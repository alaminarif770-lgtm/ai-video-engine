import asyncio
import base64
import gc
import gzip
import hashlib
import html
import io
import json
import os
import queue
import random
import re
import threading
import time
from datetime import datetime, timedelta, timezone
from stat import S_IFREG

try:
    from zoneinfo import ZoneInfo
    BD_TZ = ZoneInfo("Asia/Dhaka")
except Exception:
    BD_TZ = timezone(timedelta(hours=6))

import boto3
from botocore.config import Config
from flask import Flask, Response, jsonify, redirect, render_template, request, stream_with_context
from PIL import Image, ImageDraw, ImageFont, ImageOps
import requests
from stream_zip import ZIP_32, stream_zip

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 32 * 1024 * 1024


# ================= কনফিগারেশন =================
def _load_local_config():
    if os.path.exists("config.json"):
        try:
            with open("config.json", "r", encoding="utf-8") as f:
                data = json.load(f)
                if isinstance(data, dict):
                    return data
        except Exception as e:
            print(f"Error reading config.json: {e}")
    return {}


_LOCAL_CFG = _load_local_config()


def get_conf(key, default=""):
    env_val = os.environ.get(key)
    if env_val is not None and str(env_val).strip():
        return str(env_val).strip()
    cfg_val = _LOCAL_CFG.get(key)
    if cfg_val is not None and str(cfg_val).strip():
        return str(cfg_val).strip()
    return str(default or "").strip()


TELEGRAM_BOT_TOKEN = get_conf("TELEGRAM_BOT_TOKEN", "9286714156:AAGLSmL2HSHFcPo7ThJxTaGSBQa4mHf8aZk")
TELEGRAM_CHAT_ID = get_conf("TELEGRAM_CHAT_ID", "6322417812")

R2_ENDPOINT = get_conf("R2_ENDPOINT")
R2_ACCESS_KEY_ID = get_conf("R2_ACCESS_KEY_ID")
R2_SECRET_ACCESS_KEY = get_conf("R2_SECRET_ACCESS_KEY")
R2_BUCKET_NAME = get_conf("R2_BUCKET_NAME", "story-assets")

# Cloudflare Workers AI ক্রেডেনশিয়ালস
CF_ACCOUNT_ID = get_conf("CF_ACCOUNT_ID", "bca09c8cc7fd3d4f7e5980d9e8f84e9c")
CF_API_TOKEN = get_conf("CF_API_TOKEN", "cfat_LjDBPWtfOsQptigADDMGAOcQVeHvjmT6zokjVSKD80f57b89")

GITHUB_PAT = get_conf("GITHUB_PAT")
GITHUB_OWNER = get_conf("GITHUB_OWNER", "alaminarif770-lgtm")
GITHUB_REPO = get_conf("GITHUB_REPO", "story-video-renderer")
GITHUB_WORKFLOW = get_conf("GITHUB_WORKFLOW", "render.yml")
GITHUB_REF = get_conf("GITHUB_REF", "main")

APP_PASSWORD = get_conf("APP_PASSWORD")
APP_BASE_URL = get_conf("APP_BASE_URL").rstrip("/")

STORAGE_DIR = "/tmp/studio_assets"
REFS_DIR = "/tmp/studio_refs"
os.makedirs(STORAGE_DIR, exist_ok=True)
os.makedirs(REFS_DIR, exist_ok=True)

R2_COOKIES_KEY = "_system/cookies.json"
R2_HISTORY_KEY = "_system/history.json"
INTERNAL_PROJECT_FILES = {"meta.json", "job_state.json", "input_scenes.json", "story_bible.json"}
PRESIGN_TTL_LONG = 21600

state_lock = threading.Lock()
r2_meta_lock = threading.Lock()
boot_lock = threading.Lock()
_bootstrapped = False

cookie_pool = []
history_cache = []

worker_control = {
    "loop": None,
    "stop_event": None,
    "wakeup_event": None,
    "unpause_event": None,
}

state = {
    "is_running": False,
    "is_paused": False,
    "is_testing_cookies": False,
    "should_stop": False,
    "job_id": 0,
    "project_title": "Idle",
    "project_slug": "",
    "aspect_ratio": "16:9",
    "total_scenes": 0,
    "current_scene": 0,
    "completed_count": 0,
    "failed_count": 0,
    "percent": 0,
    "status_text": "System Ready (Cloudflare FLUX.1 Engine)",
    "active_account": "CF FLUX",
    "failed_scenes": [],
    "logs": [],
}


# ================= সময় ও লগ হেল্পার =================
def now_bd():
    return datetime.now(BD_TZ)


def now_utc_iso():
    return datetime.now(timezone.utc).isoformat()


def _detect_log_level(msg):
    if "✅" in msg or "🎉" in msg or "🎬" in msg:
        return "ok"
    if "❌" in msg or "🛑" in msg or "🚫" in msg:
        return "fail"
    if "⚠️" in msg or "⏸️" in msg:
        return "warn"
    return "info"


def add_log(message, level=None):
    dt = now_bd()
    entry = {
        "ts": dt.isoformat(),
        "ts_12h": dt.strftime("%I:%M:%S %p"),
        "level": level or _detect_log_level(message),
        "text": message,
    }
    with state_lock:
        state["logs"].append(entry)
        if len(state["logs"]) > 350:
            state["logs"] = state["logs"][-350:]


def update_state(**kwargs):
    with state_lock:
        state.update(kwargs)


def _notify_worker_wakeup():
    loop = worker_control.get("loop")
    ev = worker_control.get("wakeup_event")
    if loop and ev and not loop.is_closed():
        try:
            loop.call_soon_threadsafe(ev.set)
        except Exception:
            pass


def _notify_worker_unpause():
    loop = worker_control.get("loop")
    ev = worker_control.get("unpause_event")
    if loop and ev and not loop.is_closed():
        try:
            loop.call_soon_threadsafe(ev.set)
        except Exception:
            pass


# ================= সিকিউরিটি ও ব্যান্ডউইথ কম্প্রেসন =================
@app.before_request
def check_auth():
    if not APP_PASSWORD:
        return None
    if request.path == "/api/ping":
        return None
    auth = request.authorization
    if not auth or auth.password != APP_PASSWORD:
        return Response(
            "Authentication required",
            401,
            {"WWW-Authenticate": 'Basic realm="Story Engine"'},
        )
    return None


@app.after_request
def compress_response(response):
    if (
        response.direct_passthrough
        or response.is_streamed
        or response.status_code < 200
        or response.status_code >= 300
        or "Content-Encoding" in response.headers
        or "gzip" not in request.headers.get("Accept-Encoding", "").lower()
    ):
        return response

    ct = (response.content_type or "").lower()
    if not any(t in ct for t in ("application/json", "text/html", "text/plain", "text/css", "application/javascript")):
        return response

    data = response.get_data()
    if len(data) < 512:
        return response

    compressed = gzip.compress(data, compresslevel=6)
    if len(compressed) >= len(data):
        return response

    response.set_data(compressed)
    response.headers["Content-Encoding"] = "gzip"
    response.headers["Content-Length"] = str(len(compressed))
    vary = response.headers.get("Vary", "")
    if "Accept-Encoding" not in vary:
        response.headers["Vary"] = f"{vary}, Accept-Encoding".strip(", ")
    return response


# ================= Cloudflare R2 হেল্পার =================
def get_r2_client():
    if not all([R2_ENDPOINT, R2_ACCESS_KEY_ID, R2_SECRET_ACCESS_KEY, R2_BUCKET_NAME]):
        return None
    return boto3.client(
        "s3",
        endpoint_url=R2_ENDPOINT,
        aws_access_key_id=R2_ACCESS_KEY_ID,
        aws_secret_access_key=R2_SECRET_ACCESS_KEY,
        config=Config(
            signature_version="s3v4",
            connect_timeout=10,
            read_timeout=25,
            retries={"max_attempts": 2},
        ),
        region_name="auto",
    )


def make_project_slug(title):
    ascii_part = re.sub(r"[^a-zA-Z0-9_-]+", "_", title.strip()).strip("_").lower()
    short_hash = hashlib.md5(title.encode("utf-8")).hexdigest()[:6]
    if ascii_part:
        return f"{ascii_part[:36]}_{short_hash}"
    return f"story_{short_hash}"


def r2_upload_bytes(s3, key, data_bytes, content_type):
    s3.put_object(
        Bucket=R2_BUCKET_NAME,
        Key=key,
        Body=data_bytes,
        ContentType=content_type,
    )


def r2_download_bytes(s3, key):
    try:
        obj = s3.get_object(Bucket=R2_BUCKET_NAME, Key=key)
        body = obj["Body"]
        try:
            return body.read()
        finally:
            body.close()
    except Exception:
        return None


def r2_head_object(s3, key):
    try:
        return s3.head_object(Bucket=R2_BUCKET_NAME, Key=key)
    except Exception:
        return None


def r2_invalidate_archive_zip(s3, slug):
    if not s3 or not slug:
        return
    for key in (f"projects/{slug}/_archive/{slug}.zip", f"projects/{slug}/_archive/zip_status.json"):
        try:
            s3.delete_object(Bucket=R2_BUCKET_NAME, Key=key)
        except Exception:
            pass


def r2_read_json(s3, key, default=None):
    try:
        obj = s3.get_object(Bucket=R2_BUCKET_NAME, Key=key)
        raw = obj["Body"].read().decode("utf-8")
        return json.loads(raw)
    except Exception:
        return default


def r2_write_json(s3, key, data):
    if not s3:
        return False
    try:
        payload = json.dumps(data, ensure_ascii=False, indent=2).encode("utf-8")
        with r2_meta_lock:
            r2_upload_bytes(s3, key, payload, "application/json; charset=utf-8")
        return True
    except Exception as e:
        print(f"R2 JSON write failed ({key}): {e}")
        return False


def r2_list_existing_scenes(s3, slug):
    prefix = f"projects/{slug}/"
    existing = set()
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=prefix):
            for obj in page.get("Contents", []):
                rel = obj["Key"][len(prefix):]
                if rel and "/" not in rel:
                    existing.add(rel)
    except Exception as e:
        add_log(f"⚠️ R2 ফাইল লিস্ট চেক করতে সমস্যা: {str(e)[:60]}")
    return existing


def r2_list_refs(s3, slug):
    prefix = f"projects/{slug}/_refs/"
    refs = set()
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=prefix):
            for obj in page.get("Contents", []):
                rel = obj["Key"][len(prefix):]
                if rel and "/" not in rel:
                    refs.add(rel)
    except Exception:
        pass
    return refs


def r2_list_video_objects(s3, slug):
    prefix = f"projects/{slug}/_video/"
    items = []
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=prefix):
            for obj in page.get("Contents", []):
                rel = obj["Key"][len(prefix):]
                if rel:
                    items.append({
                        "key": obj["Key"],
                        "name": rel,
                        "size": obj.get("Size", 0),
                    })
    except Exception:
        pass
    return items


# ================= হিস্ট্রি R2 ম্যানেজার =================
def save_history_to_r2():
    s3 = get_r2_client()
    if not s3:
        return False
    with state_lock:
        data = list(history_cache[:60])
    return r2_write_json(s3, R2_HISTORY_KEY, {"history": data, "updated_at": now_utc_iso()})


def upsert_history_entry(entry_dict):
    with state_lock:
        slug = entry_dict["slug"]
        idx = next((i for i, h in enumerate(history_cache) if h.get("slug") == slug), None)
        if idx is not None:
            history_cache[idx].update(entry_dict)
            item = history_cache.pop(idx)
            history_cache.insert(0, item)
        else:
            history_cache.insert(0, entry_dict)
        if len(history_cache) > 60:
            del history_cache[60:]
    save_history_to_r2()


def bootstrap_from_r2():
    global _bootstrapped
    with boot_lock:
        if _bootstrapped:
            return
        s3 = get_r2_client()
        loaded_history = []

        if s3:
            h_doc = r2_read_json(s3, R2_HISTORY_KEY)
            if isinstance(h_doc, dict) and isinstance(h_doc.get("history"), list):
                changed = False
                for h in h_doc["history"]:
                    if h.get("status") == "running":
                        h["status"] = "interrupted"
                        h["updated_at"] = now_utc_iso()
                        changed = True
                    loaded_history.append(h)
                if changed:
                    r2_write_json(s3, R2_HISTORY_KEY, {"history": loaded_history, "updated_at": now_utc_iso()})

        # Cloudflare Workers AI ইঞ্জিনকে ডিফল্ট অ্যাক্টিভ হিসেবে সেট করা
        cf_engine_record = {
            "id": "cf_flux",
            "name": "Cloudflare Workers AI",
            "preview": "FLUX.1 [schnell]",
            "psid": "cf_official_api",
            "psidts": None,
            "enabled": True,
            "version": 1,
            "status": "active",
            "success_count": 0,
            "fail_count": 0,
            "consecutive_fails": 0,
            "cooldown_level": 0,
            "cooldown_until": 0.0,
            "cooldown_probe": False,
            "last_used_at": 0.0,
            "last_error": "",
        }

        with state_lock:
            cookie_pool.clear()
            cookie_pool.append(cf_engine_record)
            history_cache.clear()
            history_cache.extend(loaded_history)

        _bootstrapped = True


# ================= CLOUDFLARE WORKERS AI (FLUX.1) ইঞ্জিন =================
def generate_flux_image_cloudflare(prompt, aspect_ratio="16:9"):
    """Cloudflare Workers AI (@cf/black-forest-labs/flux-1-schnell) দিয়ে ২-৩ সেকেন্ডে সিনেমাটিক ইমেজ তৈরি"""
    if not CF_ACCOUNT_ID or not CF_API_TOKEN:
        raise ValueError("Cloudflare Account ID বা API Token সেট করা নেই!")

    url = f"https://api.cloudflare.com/client/v4/accounts/{CF_ACCOUNT_ID}/ai/run/@cf/black-forest-labs/flux-1-schnell"
    headers = {
        "Authorization": f"Bearer {CF_API_TOKEN}",
        "Content-Type": "application/json",
    }

    # অ্যাসপেক্ট রেশিও নির্দেশিকা
    ratio_prompt = f"{prompt}, cinematic lighting, photorealistic 8k, aspect ratio {aspect_ratio}"
    payload = {
        "prompt": ratio_prompt,
        "steps": 4,  # schnell মডেলের ৪ স্টেপেই আল্ট্রা কোয়ালিটি দেয়
    }

    res = requests.post(url, headers=headers, json=payload, timeout=40)
    if res.status_code != 200:
        try:
            err = res.json().get("errors", res.text[:120])
        except Exception:
            err = res.text[:120]
        raise RuntimeError(f"Cloudflare AI Error ({res.status_code}): {err}")

    content_type = res.headers.get("Content-Type", "").lower()
    if "application/json" in content_type:
        data = res.json()
        b64_img = data.get("result", {}).get("image")
        if not b64_img:
            raise RuntimeError("Cloudflare কোনো ইমেজ ডেটা ফেরত দেয়নি")
        return base64.b64decode(b64_img)
    else:
        # সরাসরি বাইনারি ইমেজ ফেরত আসলে
        return res.content


# ================= ইমেজ ওয়াটারমার্ক ও ভয়েসওভার টেক্সট =================
def apply_watermark(image_bytes, scene_num, mode=True):
    img = Image.open(io.BytesIO(image_bytes)).convert("RGBA")

    if mode in (False, "none", "false", None, ""):
        out = io.BytesIO()
        img.convert("RGB").save(out, format="JPEG", quality=92, optimize=True)
        return out.getvalue()

    txt_layer = Image.new("RGBA", img.size, (255, 255, 255, 0))
    draw = ImageDraw.Draw(txt_layer)

    text = f"Scene #{scene_num:03d}" if mode == "scene" else f"#{scene_num:03d}"
    font_size = max(16, int(img.height * 0.022))
    try:
        font = ImageFont.load_default(size=font_size)
    except Exception:
        font = ImageFont.load_default()

    draw.text((20, 18), text, fill=(255, 255, 255, 80), font=font)
    merged = Image.alpha_composite(img, txt_layer).convert("RGB")

    out = io.BytesIO()
    merged.save(out, format="JPEG", quality=92, optimize=True)
    return out.getvalue()


def build_clean_voiceover_text(scenes_data):
    parts = []
    for sc in scenes_data:
        if not isinstance(sc, dict):
            continue
        narr = str(sc.get("narration") or "").strip()
        if narr:
            parts.append(narr)
    return " ".join(parts)


# ================= টেলিগ্রাম কিউ ওয়ার্কার =================
tg_queue = queue.Queue(maxsize=1000)
_tg_thread_lock = threading.Lock()
_tg_thread = None


def _telegram_queue_loop():
    s3_local = None
    while True:
        item = tg_queue.get()
        try:
            kind = item[0]
            if kind == "msg":
                if TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
                    requests.post(
                        f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage",
                        data={"chat_id": TELEGRAM_CHAT_ID, "text": item[1], "parse_mode": "HTML", "disable_web_page_preview": True},
                        timeout=20,
                    )
            elif kind == "photo_r2":
                r2_key, scene_num, narration = item[1], item[2], item[3]
                if s3_local is None:
                    s3_local = get_r2_client()
                if s3_local and TELEGRAM_BOT_TOKEN and TELEGRAM_CHAT_ID:
                    photo_url = s3_local.generate_presigned_url(
                        "get_object",
                        Params={"Bucket": R2_BUCKET_NAME, "Key": r2_key},
                        ExpiresIn=900,
                    )
                    safe_narr = html.escape(str(narration or ""))[:950]
                    requests.post(
                        f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto",
                        data={"chat_id": TELEGRAM_CHAT_ID, "photo": photo_url, "caption": f'<b>Scene #{scene_num:03d}</b>\n\n"{safe_narr}"', "parse_mode": "HTML"},
                        timeout=25,
                    )
            time.sleep(1.2)
        except Exception as e:
            print(f"Telegram worker error: {e}")
        finally:
            tg_queue.task_done()


def ensure_telegram_worker():
    global _tg_thread
    with _tg_thread_lock:
        if _tg_thread is None or not _tg_thread.is_alive():
            _tg_thread = threading.Thread(target=_telegram_queue_loop, daemon=True)
            _tg_thread.start()


def send_telegram_message(text):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    ensure_telegram_worker()
    try:
        tg_queue.put_nowait(("msg", text))
    except queue.Full:
        pass


def send_telegram_photo_r2_queued(r2_key, scene_num, narration):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        return
    ensure_telegram_worker()
    try:
        tg_queue.put_nowait(("photo_r2", r2_key, scene_num, narration))
    except queue.Full:
        pass


# ================= GitHub Actions ২য় ভিডিও সার্ভার ট্রিগার =================
def trigger_github_video_render(slug, mode="video"):
    if not GITHUB_PAT:
        return False, "Render-এ GITHUB_PAT সেট করা নেই।"

    s3 = get_r2_client()
    if s3 and mode in ("video", "both"):
        r2_write_json(
            s3,
            f"projects/{slug}/_video/video_status.json",
            {
                "slug": slug,
                "status": "queued",
                "percent": 2,
                "message": "২য় সার্ভারে কমান্ড পাঠানো হয়েছে, রেন্ডার শুরু হচ্ছে...",
                "updated_at": now_utc_iso(),
            },
        )

    url = (
        f"https://api.github.com/repos/{GITHUB_OWNER}/{GITHUB_REPO}"
        f"/actions/workflows/{GITHUB_WORKFLOW}/dispatches"
    )
    headers = {
        "Authorization": f"Bearer {GITHUB_PAT}",
        "Accept": "application/vnd.github+json",
        "X-GitHub-Api-Version": "2022-11-28",
    }
    inputs_payload = {"slug": slug}
    if mode != "video":
        inputs_payload["mode"] = mode

    try:
        res = requests.post(
            url,
            headers=headers,
            json={"ref": GITHUB_REF, "inputs": inputs_payload},
            timeout=20,
        )
        if res.status_code in (201, 204):
            return True, "২য় সার্ভারে কমান্ড পাঠানো হয়েছে!"
        return False, f"GitHub HTTP {res.status_code}"
    except Exception as e:
        return False, str(e)[:150]


# ================= তাৎক্ষণিক ক্যানসেলেবল ও Pause হেল্পার =================
async def wait_if_paused(stop_event, unpause_event):
    while not stop_event.is_set():
        with state_lock:
            paused = state.get("is_paused", False)
        if not paused:
            return True

        unpause_event.clear()
        with state_lock:
            if not state.get("is_paused", False):
                return True

        update_state(status_text="Paused (User)", active_account="-")
        stop_t = asyncio.create_task(stop_event.wait())
        unp_t = asyncio.create_task(unpause_event.wait())
        try:
            await asyncio.wait({stop_t, unp_t}, return_when=asyncio.FIRST_COMPLETED)
        finally:
            for t in (stop_t, unp_t):
                if not t.done():
                    t.cancel()
    return False


async def smart_sleep(seconds, stop_event, wakeup_event=None):
    if seconds <= 0 or stop_event.is_set():
        return not stop_event.is_set()

    tasks = [asyncio.create_task(stop_event.wait())]
    if wakeup_event is not None:
        tasks.append(asyncio.create_task(wakeup_event.wait()))

    try:
        done, pending = await asyncio.wait(tasks, timeout=seconds, return_when=asyncio.FIRST_COMPLETED)
        for p in pending:
            p.cancel()
        if stop_event.is_set():
            return False
        if wakeup_event is not None and wakeup_event.is_set():
            wakeup_event.clear()
        return True
    finally:
        for t in tasks:
            if not t.done():
                t.cancel()


# ================= মূল জেনারেশন ওয়ার্কার (FLUX.1) =================
async def async_generation_worker(
    scenes_data,
    title,
    ratio,
    watermark_mode,
    target_scene_nums=None,
    story_cfg=None,
):
    bootstrap_from_r2()
    ensure_telegram_worker()
    slug = make_project_slug(title)
    total = len(scenes_data)
    story_cfg = story_cfg or {}
    auto_video = bool(story_cfg.get("auto_video", False))

    loop = asyncio.get_running_loop()
    stop_event = asyncio.Event()
    wakeup_event = asyncio.Event()
    unpause_event = asyncio.Event()
    unpause_event.set()

    with state_lock:
        new_job_id = state["job_id"] + 1
        if state["should_stop"]:
            stop_event.set()
        worker_control["loop"] = loop
        worker_control["stop_event"] = stop_event
        worker_control["wakeup_event"] = wakeup_event
        worker_control["unpause_event"] = unpause_event
        state.update({
            "is_running": True,
            "is_paused": False,
            "job_id": new_job_id,
            "project_title": title,
            "project_slug": slug,
            "aspect_ratio": ratio,
            "total_scenes": total,
            "current_scene": 0,
            "completed_count": 0,
            "failed_count": 0,
            "percent": 0,
            "status_text": "FLUX.1 Engine Connected...",
            "active_account": "FLUX.1",
            "failed_scenes": [],
            "logs": [],
        })

    add_log(f"🚀 প্রজেক্ট শুরু: {title} (মোট {total} টি সিন) — Cloudflare FLUX.1 Engine")
    add_log(f"📁 R2 ফোল্ডার: projects/{slug}/")

    failed_scenes_list = []
    completed_nums = set()

    def _sync_job_progress(s3_cli, job_status="running"):
        with state_lock:
            done_c = len(completed_nums)
            fail_c = len(failed_scenes_list)
            state["completed_count"] = done_c
            state["failed_count"] = fail_c
            state["failed_scenes"] = list(failed_scenes_list)

        summary = {
            "slug": slug,
            "title": title,
            "aspect_ratio": ratio,
            "watermark": watermark_mode,
            "auto_video": auto_video,
            "total_scenes": total,
            "completed_count": len(completed_nums),
            "failed_count": len(failed_scenes_list),
            "failed_scenes": list(failed_scenes_list),
            "status": job_status,
            "updated_at": now_utc_iso(),
        }
        if s3_cli:
            r2_write_json(s3_cli, f"projects/{slug}/job_state.json", summary)
            upsert_history_entry(summary)

    try:
        s3 = get_r2_client()
        if not s3:
            add_log("❌ Cloudflare R2 কনফিগারেশন পাওয়া যায়নি! config.json চেক করুন।")
            update_state(status_text="R2 Config Error")
            return

        voiceover_text = build_clean_voiceover_text(scenes_data)
        if voiceover_text:
            try:
                r2_upload_bytes(s3, f"projects/{slug}/story.txt", voiceover_text.encode("utf-8"), "text/plain; charset=utf-8")
            except Exception:
                pass

        existing_files = r2_list_existing_scenes(s3, slug)
        existing_jpgs = {f for f in existing_files if f.lower().endswith(".jpg")}
        if existing_jpgs:
            add_log(f"♻️ R2-তে আগে থেকেই {len(existing_jpgs)} টি ছবি আছে (অটো-রিজিউম চালু)।")

        _sync_job_progress(s3, "running")
        send_telegram_message(f"🚀 <b>{html.escape(title)}</b>\nমোট সিন: {total}\nFLUX.1 দিয়ে ইমেজ তৈরি শুরু হয়েছে!")

        # সিন জেনারেশন লুপ
        skipped_count = 0
        for idx, sc in enumerate(scenes_data):
            if stop_event.is_set():
                break
            if not await wait_if_paused(stop_event, unpause_event):
                break
            if not isinstance(sc, dict):
                continue

            raw_num = sc.get("scene_number")
            try:
                num = int(raw_num) if raw_num is not None and str(raw_num).strip() != "" else (idx + 1)
            except Exception:
                num = idx + 1

            filename = f"scene_{num:03d}.jpg"
            r2_key = f"projects/{slug}/{filename}"

            update_state(
                current_scene=num,
                percent=int(((idx + 1) / max(1, total)) * 100),
                status_text=f"Rendering #{num:03d} (FLUX.1)...",
                active_account="FLUX.1",
            )

            if filename in existing_jpgs and (target_scene_nums is None or num not in target_scene_nums):
                skipped_count += 1
                completed_nums.add(num)
                update_state(completed_count=len(completed_nums))
                continue

            if target_scene_nums is not None and num not in target_scene_nums:
                continue

            prompt = str(sc.get("image_prompt", "")).strip()
            narration = str(sc.get("narration", "")).strip()

            if not prompt:
                failed_scenes_list.append({"scene_number": num, "reason": "প্রম্পট খালি ছিল"})
                continue

            t_start = time.time()
            add_log(f"🎨 [FLUX.1] সিন #{num:03d} তৈরি হচ্ছে: {prompt[:40]}...")

            try:
                # Cloudflare FLUX API দিয়ে সেকেন্ডে ছবি তৈরি
                raw_img_bytes = await asyncio.to_thread(generate_flux_image_cloudflare, prompt, ratio)
                processed_bytes = apply_watermark(raw_img_bytes, num, watermark_mode)

                await asyncio.to_thread(r2_upload_bytes, s3, r2_key, processed_bytes, "image/jpeg")
                send_telegram_photo_r2_queued(r2_key, num, narration)

                elapsed = round(time.time() - t_start, 1)
                completed_nums.add(num)
                add_log(f"✅ [FLUX.1] সিন #{num:03d} সম্পন্ন ({elapsed}s) -> R2 & Telegram!")
                _sync_job_progress(s3, "running")
                del raw_img_bytes, processed_bytes
            except Exception as gen_err:
                err_msg = str(gen_err)[:120]
                failed_scenes_list.append({"scene_number": num, "reason": err_msg})
                add_log(f"❌ সিন #{num:03d} ব্যর্থ: {err_msg}")
                _sync_job_progress(s3, "running")

            gc.collect()

            # হালকা ২ সেকেন্ডের বিরতি
            if idx < total - 1 and not stop_event.is_set():
                await smart_sleep(1.8, stop_event, wakeup_event)

        # ফাইনাল কাজ শেষ
        was_stopped = stop_event.is_set()
        final_status = "stopped" if was_stopped else "completed"

        update_state(
            percent=100 if final_status == "completed" else int((len(completed_nums) / max(1, total)) * 100),
            status_text="Completed" if final_status == "completed" else "Stopped",
            active_account="FLUX.1",
            is_paused=False,
        )
        _sync_job_progress(s3, final_status)

        if final_status == "completed":
            add_log(f"🎉 কাজ শেষ! সফল: {len(completed_nums)}/{total}")
            send_telegram_message(f"🎉 <b>{html.escape(title)}</b> সম্পন্ন হয়েছে!\nসফল: {len(completed_nums)} / {total}\nসব ছবি Cloudflare R2-তে সেভ হয়েছে!")

            # অটো-ভিডিও ট্রিগার
            if auto_video and not failed_scenes_list:
                ok_trig, trig_msg = trigger_github_video_render(slug, mode="video")
                if ok_trig:
                    add_log("🎬 ২য় সার্ভারে অটো-ভিডিও রেন্ডার শুরু হয়েছে!")
                    send_telegram_message(f"🎬 <b>২য় সার্ভারে ভিডিও রেন্ডার শুরু হয়েছে!</b>")

    except InterruptedError:
        add_log("🛑 কাজ থামানো হয়েছে।")
        update_state(status_text="Stopped", active_account="-", is_paused=False)
    except Exception as fatal_err:
        add_log(f"❌ সার্ভার ত্রুটি: {str(fatal_err)[:120]}")
        update_state(status_text="Failed", active_account="-", is_paused=False)
    finally:
        with state_lock:
            worker_control["loop"] = None
            worker_control["stop_event"] = None
            state["is_running"] = False
            state["is_paused"] = False
            state["should_stop"] = False


def generation_worker(scenes_data, title, ratio, watermark_mode, target_scene_nums=None, story_cfg=None):
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        loop.run_until_complete(
            async_generation_worker(scenes_data, title, ratio, watermark_mode, target_scene_nums, story_cfg)
        )
    finally:
        loop.close()


# ================= Flask রুটস =================
@app.route("/")
def index():
    bootstrap_from_r2()
    return render_template("index.html")


@app.route("/api/ping", methods=["GET"])
def ping():
    return jsonify({"status": "alive", "running": state["is_running"]})


@app.route("/api/status", methods=["GET"])
def get_status():
    bootstrap_from_r2()
    with state_lock:
        snapshot = {
            "is_running": state["is_running"],
            "is_paused": state["is_paused"],
            "is_testing_cookies": False,
            "job_id": state["job_id"],
            "project_title": state["project_title"],
            "project_slug": state["project_slug"],
            "aspect_ratio": state["aspect_ratio"],
            "total_scenes": state["total_scenes"],
            "current_scene": state["current_scene"],
            "completed_count": state["completed_count"],
            "failed_count": state["failed_count"],
            "percent": state["percent"],
            "status_text": state["status_text"],
            "active_account": state["active_account"],
            "failed_scenes": list(state["failed_scenes"]),
            "logs": list(state["logs"]),
            "accounts": [
                {
                    "order_num": 1,
                    "id": "cf_flux",
                    "name": "Cloudflare Workers AI",
                    "preview": "FLUX.1 [schnell]",
                    "status": "active",
                    "enabled": True,
                    "success_count": state["completed_count"],
                    "fail_count": state["failed_count"],
                    "cooldown_remaining": 0,
                    "last_error": "",
                }
            ],
            "interrupted_job": None,
        }
    return jsonify(snapshot)


@app.route("/api/start", methods=["POST"])
def start_pipeline():
    bootstrap_from_r2()
    with state_lock:
        if state["is_running"]:
            return jsonify({"error": "একটি কাজ ইতিমধ্যেই চলছে!"}), 400
        state["should_stop"] = False
        state["is_paused"] = False

    payload = request.get_json(silent=True) or {}
    raw_json = payload.get("json_content", "")
    ratio = str(payload.get("aspect_ratio", "16:9"))
    watermark_mode = payload.get("watermark", "hash")
    auto_video = bool(payload.get("auto_video", False))

    try:
        parsed = json.loads(raw_json) if isinstance(raw_json, str) else raw_json
    except Exception as e:
        return jsonify({"error": f"Invalid JSON: {str(e)}"}), 400

    scenes = parsed.get("scenes")
    if not isinstance(scenes, list) or len(scenes) == 0:
        return jsonify({"error": "JSON-এ ভ্যালিড 'scenes' পাওয়া যায়নি।"}), 400

    title = str(parsed.get("project_title") or "Untitled Story").strip()
    story_cfg = {"auto_video": auto_video}

    threading.Thread(
        target=generation_worker,
        args=(scenes, title, ratio, watermark_mode, None, story_cfg),
        daemon=True,
    ).start()

    return jsonify({"status": "success", "total_scenes": len(scenes), "slug": make_project_slug(title)})


@app.route("/api/pause", methods=["POST"])
def pause_pipeline():
    with state_lock:
        if not state["is_running"]:
            return jsonify({"error": "কোনো কাজ চলছে না।"}), 400
        state["is_paused"] = True
        state["status_text"] = "Paused"
    _notify_worker_wakeup()
    return jsonify({"status": "paused"})


@app.route("/api/resume", methods=["POST"])
def resume_pipeline():
    with state_lock:
        if not state["is_running"]:
            return jsonify({"error": "কোনো কাজ চলছে না।"}), 400
        state["is_paused"] = False
        state["status_text"] = "Resuming..."
    _notify_worker_unpause()
    return jsonify({"status": "resumed"})


@app.route("/api/stop", methods=["POST"])
def stop_pipeline():
    with state_lock:
        if state["is_running"]:
            state["should_stop"] = True
            loop = worker_control.get("loop")
            ev = worker_control.get("stop_event")
            if loop and ev and not loop.is_closed():
                try:
                    loop.call_soon_threadsafe(ev.set)
                except Exception:
                    pass
            return jsonify({"status": "stopping"})
    return jsonify({"status": "idle"})


# ================= হিস্ট্রি ও অন্যান্য API =================
@app.route("/api/history", methods=["GET"])
def api_get_history():
    bootstrap_from_r2()
    with state_lock:
        items = list(history_cache)
    return jsonify({"history": items})


@app.route("/api/history/delete/<slug>", methods=["POST"])
def api_delete_history(slug):
    bootstrap_from_r2()
    with state_lock:
        before = len(history_cache)
        history_cache[:] = [h for h in history_cache if h.get("slug") != slug]
        removed = len(history_cache) < before
    if removed:
        save_history_to_r2()
    return jsonify({"status": "deleted"})


@app.route("/api/video/slug", methods=["POST"])
def api_video_slug():
    data = request.get_json(silent=True) or {}
    title = str(data.get("title") or "Untitled Story").strip()
    return jsonify({"slug": make_project_slug(title)})


@app.route("/api/video/presign-upload", methods=["POST"])
def api_video_presign_upload():
    data = request.get_json(silent=True) or {}
    slug = str(data.get("slug", "")).strip()
    kind = str(data.get("kind", "")).strip().lower()
    filename = str(data.get("filename", "")).strip()
    content_type = str(data.get("content_type") or "application/octet-stream").strip()

    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid slug"}), 400

    ext = os.path.splitext(filename)[1].lower()
    target_name = f"audio{ext}" if kind == "audio" else ("subtitles.srt" if kind == "srt" else f"font{ext}")
    r2_key = f"projects/{slug}/_video/{target_name}"

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    try:
        upload_url = s3.generate_presigned_url(
            "put_object",
            Params={"Bucket": R2_BUCKET_NAME, "Key": r2_key, "ContentType": content_type},
            ExpiresIn=3600,
        )
        return jsonify({"upload_url": upload_url, "key": r2_key, "content_type": content_type})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/video/project/<slug>", methods=["GET"])
def api_video_project_detail(slug):
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    objs = r2_list_video_objects(s3, slug)
    audio_file = next((o["name"] for o in objs if o["name"].lower().endswith((".mp3", ".wav", ".m4a", ".aac", ".ogg"))), None)
    srt_file = next((o["name"] for o in objs if o["name"].lower().endswith(".srt")), None)
    font_file = next((o["name"] for o in objs if o["name"].lower().endswith((".ttf", ".otf"))), None)
    mp4_obj = next((o for o in objs if o["name"] == "final_video.mp4"), None)
    cfg = r2_read_json(s3, f"projects/{slug}/_video/video_config.json", default={}) or {}
    status_doc = r2_read_json(s3, f"projects/{slug}/_video/video_status.json", default={}) or {}
    return jsonify({
        "slug": slug,
        "audio_file": audio_file,
        "srt_file": srt_file,
        "font_file": font_file,
        "has_video": bool(mp4_obj),
        "video_size": mp4_obj["size"] if mp4_obj else 0,
        "config": cfg,
        "status": status_doc,
    })


@app.route("/api/video/config/<slug>", methods=["POST"])
def api_video_save_config(slug):
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    data = request.get_json(silent=True) or {}
    if r2_write_json(s3, f"projects/{slug}/_video/video_config.json", data):
        return jsonify({"status": "saved"})
    return jsonify({"error": "Config সেভ করা যায়নি"}), 500


@app.route("/api/video/trigger/<slug>", methods=["POST"])
def api_video_trigger(slug):
    ok, msg = trigger_github_video_render(slug, mode="video")
    if ok:
        return jsonify({"status": "triggered", "message": msg})
    return jsonify({"error": msg}), 500


@app.route("/api/video/list", methods=["GET"])
def api_video_list():
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    projects = {}
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix="projects/"):
            for obj in page.get("Contents", []):
                key = obj["Key"]
                parts = key.split("/")
                if len(parts) < 3 or not parts[2]:
                    continue
                slug = parts[1]
                if slug not in projects:
                    projects[slug] = {
                        "slug": slug,
                        "title": slug,
                        "image_count": 0,
                        "has_meta": False,
                        "has_audio": False,
                        "has_srt": False,
                        "has_font": False,
                        "has_video": False,
                        "video_size": 0,
                        "last_modified": "",
                        "has_video_status": False,
                    }
                p = projects[slug]
                lm = obj["LastModified"].strftime("%Y-%m-%d %H:%M")
                if lm > p["last_modified"]:
                    p["last_modified"] = lm
                if len(parts) == 3 and parts[2].lower().endswith((".jpg", ".jpeg", ".png", ".webp")):
                    p["image_count"] += 1
                elif len(parts) == 4 and parts[2] == "_video":
                    vname = parts[3].lower()
                    if vname.endswith((".mp3", ".wav", ".m4a", ".aac", ".ogg")):
                        p["has_audio"] = True
                    elif vname == "final_video.mp4":
                        p["has_video"] = True
                        p["video_size"] = obj.get("Size", 0)

        result = list(projects.values())
        result.sort(key=lambda x: x["last_modified"], reverse=True)
        return jsonify({"videos": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/video/presign-download/<slug>", methods=["GET"])
def api_video_presign_download(slug):
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    try:
        url = s3.generate_presigned_url(
            "get_object",
            Params={"Bucket": R2_BUCKET_NAME, "Key": f"projects/{slug}/_video/final_video.mp4"},
            ExpiresIn=PRESIGN_TTL_LONG,
        )
        return jsonify({"url": url})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/r2/projects", methods=["GET"])
def r2_list_projects():
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    projects = {}
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix="projects/"):
            for obj in page.get("Contents", []):
                key = obj["Key"]
                parts = key.split("/")
                if len(parts) < 3 or not parts[2]:
                    continue
                slug = parts[1]
                filename = parts[2]
                if slug not in projects:
                    projects[slug] = {"slug": slug, "title": slug, "image_count": 0, "total_bytes": 0, "last_modified": ""}
                p = projects[slug]
                p["total_bytes"] += obj.get("Size", 0)
                lm = obj["LastModified"].strftime("%Y-%m-%d %H:%M")
                if lm > p["last_modified"]:
                    p["last_modified"] = lm
                if len(parts) == 3 and filename.lower().endswith((".jpg", ".jpeg", ".png", ".webp")):
                    p["image_count"] += 1
        result = sorted(projects.values(), key=lambda x: x["last_modified"], reverse=True)
        return jsonify({"projects": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/r2/project/<slug>/files", methods=["GET"])
def r2_list_project_files(slug):
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    files = []
    prefix = f"projects/{slug}/"
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=prefix):
            for obj in page.get("Contents", []):
                key = obj["Key"]
                name = key[len(prefix):]
                if not name or "/" in name or name in INTERNAL_PROJECT_FILES:
                    continue
                files.append({
                    "key": key,
                    "name": name,
                    "size": obj.get("Size", 0),
                    "is_image": name.lower().endswith((".jpg", ".jpeg", ".png", ".webp")),
                })
        files.sort(key=lambda x: x["name"])
        return jsonify({"slug": slug, "files": files})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/r2/file", methods=["GET"])
def r2_stream_file():
    key = request.args.get("key", "").strip()
    download = request.args.get("download", "0") == "1"
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    filename = key.split("/")[-1]
    params = {"Bucket": R2_BUCKET_NAME, "Key": key}
    if download:
        params["ResponseContentDisposition"] = f'attachment; filename="{filename}"'
    try:
        url = s3.generate_presigned_url("get_object", Params=params, ExpiresIn=PRESIGN_TTL_LONG)
        return redirect(url, code=302)
    except Exception as e:
        return jsonify({"error": str(e)}), 404


@app.route("/api/r2/download-zip/<slug>", methods=["GET"])
def r2_stream_zip(slug):
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    objects_to_zip = []
    prefix = f"projects/{slug}/"
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=prefix):
            for obj in page.get("Contents", []):
                name = obj["Key"][len(prefix):]
                if not name or "/" in name or name in INTERNAL_PROJECT_FILES:
                    continue
                objects_to_zip.append((name, obj["Key"], obj["LastModified"].replace(tzinfo=None)))
    except Exception as e:
        return jsonify({"error": str(e)}), 500

    if not objects_to_zip:
        return jsonify({"error": "No files found"}), 404

    def member_files():
        for name, key, mod_time in objects_to_zip:
            def chunk_iter(obj_key=key):
                resp = s3.get_object(Bucket=R2_BUCKET_NAME, Key=obj_key)
                body = resp["Body"]
                try:
                    for chunk in body.iter_chunks(chunk_size=65536):
                        if chunk:
                            yield chunk
                finally:
                    body.close()
            yield (name, mod_time, S_IFREG | 0o644, ZIP_32, chunk_iter())

    return Response(
        stream_with_context(stream_zip(member_files())),
        mimetype="application/zip",
        headers={"Content-Disposition": f'attachment; filename="{slug}.zip"'},
    )


@app.route("/api/r2/delete-project", methods=["POST"])
def r2_delete_project():
    data = request.get_json(silent=True) or {}
    slug = str(data.get("slug", "")).strip()
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500
    try:
        paginator = s3.get_paginator("list_objects_v2")
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=f"projects/{slug}/"):
            keys = [{"Key": obj["Key"]} for obj in page.get("Contents", [])]
            if keys:
                s3.delete_objects(Bucket=R2_BUCKET_NAME, Delete={"Objects": keys})
        return jsonify({"status": "deleted"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    bootstrap_from_r2()
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port)
