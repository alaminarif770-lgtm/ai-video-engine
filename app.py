import asyncio
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
from gemini_webapi import GeminiClient
from PIL import Image, ImageDraw, ImageFont, ImageOps
import requests
from stream_zip import ZIP_32, stream_zip

app = Flask(__name__)
app.config["MAX_CONTENT_LENGTH"] = 32 * 1024 * 1024  # ৩২ MB পর্যন্ত বড় JSON সাপোর্ট (৫০০+ সিন)


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

PROXY_URL = get_conf("PROXY")  # প্রক্সি লিংক (যদি থাকে)

GITHUB_PAT = get_conf("GITHUB_PAT")
GITHUB_OWNER = get_conf("GITHUB_OWNER", "alaminarif770-lgtm")
GITHUB_REPO = get_conf("GITHUB_REPO", "story-video-renderer")
GITHUB_WORKFLOW = get_conf("GITHUB_WORKFLOW", "render.yml")
GITHUB_REF = get_conf("GITHUB_REF", "main")

APP_PASSWORD = get_conf("APP_PASSWORD")
APP_BASE_URL = get_conf("APP_BASE_URL").rstrip("/")

STORAGE_DIR = "/tmp/studio_assets"
REFS_DIR = "/tmp/studio_refs"
GEMINI_CACHE_DIR = "/tmp/gemini_cookies"
os.makedirs(STORAGE_DIR, exist_ok=True)
os.makedirs(REFS_DIR, exist_ok=True)
os.makedirs(GEMINI_CACHE_DIR, exist_ok=True)
os.environ.setdefault("GEMINI_COOKIE_PATH", GEMINI_CACHE_DIR)

R2_COOKIES_KEY = "_system/cookies.json"
R2_HISTORY_KEY = "_system/history.json"
INTERNAL_PROJECT_FILES = {"meta.json", "job_state.json", "input_scenes.json", "story_bible.json"}
PRESIGN_TTL_LONG = 21600  # ৬ ঘণ্টা

COOLDOWN_TIERS = [180, 600, 1800]  # ৩ মিনিট -> ১০ মিনিট -> ৩০ মিনিট
MIN_ACCOUNT_INTERVAL = 18.0        # প্রতি একাউন্টের দুটি রিকোয়েস্টের মাঝে গ্যাপ

state_lock = threading.Lock()
r2_meta_lock = threading.Lock()
boot_lock = threading.Lock()
_bootstrapped = False

cookie_pool = []
rr_cursor = 0  # কঠোর সিরিয়াল রোটেশন (১ -> ২ -> ৩ -> ৪ -> ৫ -> ১...)
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
    "status_text": "System Ready",
    "active_account": "-",
    "failed_scenes": [],
    "logs": [],
}


# ================= সময় ও লগ হেল্পার (12H BDT) =================
def now_bd():
    return datetime.now(BD_TZ)


def now_utc_iso():
    return datetime.now(timezone.utc).isoformat()


def _detect_log_level(msg):
    if "✅" in msg or "🎉" in msg or "🎬" in msg:
        return "ok"
    if "❌" in msg or "🛑" in msg or "🚫" in msg or "বাতিল" in msg:
        return "fail"
    if "⚠️" in msg or "⏭️" in msg or "❄️" in msg or "⏸️" in msg:
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


def _clear_gemini_cache(psid=None):
    try:
        for fname in os.listdir(GEMINI_CACHE_DIR):
            if psid is None or psid in fname or fname.startswith(".cached_1psidts"):
                try:
                    os.remove(os.path.join(GEMINI_CACHE_DIR, fname))
                except Exception:
                    pass
    except Exception:
        pass


# ================= GZIP ব্যান্ডউইথ সাশ্রয় =================
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


# ================= কুকি পুল ও ৩-৪ ঘণ্টার অটো-সিঙ্ক মেকানিজম =================
def mask_cookie(psid):
    if len(psid) <= 12:
        return "***"
    return f"{psid[:7]}...{psid[-5:]}"


def clean_cookie_input(raw_psid, raw_psidts=""):
    cleaned = str(raw_psid or "").strip()
    quoted = re.findall(r'"([^"]*)"', cleaned)
    if quoted:
        cleaned = quoted[-1].strip()

    psidts = str(raw_psidts or "").strip() or None
    if "|" in cleaned and not psidts:
        parts = cleaned.split("|", 1)
        cleaned = parts[0].strip()
        psidts = parts[1].strip() or None

    cleaned = cleaned.replace("__Secure-1PSID=", "").rstrip(";").strip()
    if psidts:
        psidts = psidts.replace("__Secure-1PSIDTS=", "").rstrip(";").strip() or None

    return cleaned, psidts


def _make_cookie_record(psid, psidts=None, name="", enabled=True, existing_dict=None):
    cid = (existing_dict or {}).get("id") or f"ck_{hashlib.md5((psid + str(time.time())).encode('utf-8')).hexdigest()[:8]}"
    return {
        "id": cid,
        "name": name or (existing_dict or {}).get("name") or "Gmail",
        "preview": mask_cookie(psid),
        "psid": psid,
        "psidts": psidts,
        "enabled": bool(enabled),
        "version": int((existing_dict or {}).get("version", 1)),
        "status": "paused" if not enabled else (existing_dict or {}).get("status", "standby"),
        "success_count": int((existing_dict or {}).get("success_count", 0)),
        "fail_count": int((existing_dict or {}).get("fail_count", 0)),
        "consecutive_fails": int((existing_dict or {}).get("consecutive_fails", 0)),
        "cooldown_level": int((existing_dict or {}).get("cooldown_level", 0)),
        "cooldown_until": float((existing_dict or {}).get("cooldown_until", 0.0)),
        "cooldown_probe": bool((existing_dict or {}).get("cooldown_probe", False)),
        "last_used_at": float((existing_dict or {}).get("last_used_at", 0.0)),
        "last_error": str((existing_dict or {}).get("last_error", "")),
    }


def _sync_client_cookies_to_storage(cid, client):
    """৩-৪ ঘণ্টার লগআউট ফিক্স: GeminiClient এর নতুন ঘূর্ণায়মান 1PSIDTS কুকি R2 তে অটো-সিঙ্ক করে"""
    if not client or not getattr(client, "cookies", None):
        return
    try:
        cookies_dict = client.cookies
        new_psidts = cookies_dict.get("__Secure-1PSIDTS") or cookies_dict.get("Secure-1PSIDTS")
        if new_psidts:
            with state_lock:
                target = next((c for c in cookie_pool if c["id"] == cid), None)
                if target and target.get("psidts") != new_psidts:
                    target["psidts"] = new_psidts
                    target["version"] = target.get("version", 1) + 1
                    add_log(f"🔄 {target['name']}-এর ঘূর্ণায়মান কুকি স্বয়ংক্রিয়ভাবে রিনিউ ও R2-তে সিঙ্ক হয়েছে!")
                    save_cookies_to_r2()
    except Exception as e:
        print(f"Cookie auto-sync error: {e}")


def _cookie_name_exists(name, exclude_id=None):
    target = str(name or "").strip().lower()
    if not target:
        return False
    for c in cookie_pool:
        if exclude_id and c["id"] == exclude_id:
            continue
        if str(c.get("name", "")).strip().lower() == target:
            return True
    return False


def _next_unique_default_cookie_name():
    n = 1
    while True:
        cand = f"Gmail #{n}"
        if not _cookie_name_exists(cand):
            return cand
        n += 1


def _load_fallback_file_cookies():
    items = []
    raw_lines = []
    for fname in ("cookie.txt", "cookies.txt"):
        if os.path.exists(fname):
            try:
                with open(fname, "r", encoding="utf-8") as f:
                    raw_lines.extend(f.read().splitlines())
                break
            except Exception:
                pass

    if not raw_lines:
        env_single = get_conf("SECURE_1PSID")
        if env_single:
            env_1psidts = get_conf("SECURE_1PSIDTS")
            raw_lines.append(f"{env_single}|{env_1psidts}" if env_1psidts else env_single)

    idx = 1
    for line in raw_lines:
        cleaned = line.strip()
        if not cleaned or cleaned.startswith("#"):
            continue
        psid, psidts = clean_cookie_input(cleaned)
        if not psid or psid.lower() in ("my cookies", "your_cookie_here"):
            continue
        items.append(_make_cookie_record(psid, psidts, name=f"Gmail #{idx}"))
        idx += 1
    return items


def save_cookies_to_r2():
    s3 = get_r2_client()
    if not s3:
        return False
    with state_lock:
        serializable = [
            {
                "id": c["id"],
                "name": c["name"],
                "psid": c["psid"],
                "psidts": c.get("psidts"),
                "enabled": c.get("enabled", True),
                "success_count": c.get("success_count", 0),
                "fail_count": c.get("fail_count", 0),
                "last_error": c.get("last_error", ""),
            }
            for c in cookie_pool
        ]
    return r2_write_json(s3, R2_COOKIES_KEY, {"cookies": serializable, "updated_at": now_utc_iso()})


def sanitize_accounts_for_ui():
    now_ts = time.time()
    result = []
    with state_lock:
        for idx, c in enumerate(cookie_pool):
            status = c.get("status", "standby")
            cd_rem = 0
            if not c.get("enabled", True):
                status = "paused"
            elif c.get("cooldown_until", 0) > now_ts:
                status = "cooldown"
                cd_rem = int(c["cooldown_until"] - now_ts)
            elif status == "cooldown" and c.get("cooldown_until", 0) <= now_ts:
                status = "standby"

            result.append({
                "order_num": idx + 1,
                "id": c["id"],
                "name": c["name"],
                "preview": c["preview"],
                "has_psidts": bool(c.get("psidts")),
                "status": status,
                "enabled": c.get("enabled", True),
                "success_count": c.get("success_count", 0),
                "fail_count": c.get("fail_count", 0),
                "consecutive_fails": c.get("consecutive_fails", 0),
                "cooldown_level": c.get("cooldown_level", 0),
                "cooldown_remaining": cd_rem,
                "last_error": c.get("last_error", ""),
                "last_used_at": c.get("last_used_at", 0),
            })
    return result


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
        loaded_cookies = []
        loaded_history = []

        if s3:
            c_doc = r2_read_json(s3, R2_COOKIES_KEY)
            if isinstance(c_doc, dict) and isinstance(c_doc.get("cookies"), list):
                for item in c_doc["cookies"]:
                    psid = str(item.get("psid", "")).strip()
                    if psid:
                        loaded_cookies.append(
                            _make_cookie_record(
                                psid=psid,
                                psidts=item.get("psidts"),
                                name=item.get("name", "Gmail"),
                                enabled=item.get("enabled", True),
                                existing_dict=item,
                            )
                        )
            else:
                loaded_cookies = _load_fallback_file_cookies()

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
        else:
            loaded_cookies = _load_fallback_file_cookies()

        with state_lock:
            cookie_pool.clear()
            cookie_pool.extend(loaded_cookies)
            history_cache.clear()
            history_cache.extend(loaded_history)

        if s3 and loaded_cookies and r2_read_json(s3, R2_COOKIES_KEY) is None:
            save_cookies_to_r2()

        _bootstrapped = True


# ================= ইমেজ ওয়াটারমার্ক ও রেফারেন্স শিট =================
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


def _safe_key_name(key):
    cleaned = re.sub(r"[^a-zA-Z0-9_-]+", "_", str(key or "").strip()).strip("_").lower()
    return cleaned or "char"


def _build_labeled_collage(char_items, out_path):
    tile_w, tile_h = 380, 420
    label_h = 48
    gap = 14
    margin = 14
    count = len(char_items)
    total_w = margin * 2 + count * tile_w + (count - 1) * gap
    total_h = margin * 2 + tile_h + label_h

    canvas = Image.new("RGB", (total_w, total_h), (245, 247, 250))
    draw = ImageDraw.Draw(canvas)
    try:
        font = ImageFont.load_default(size=24)
    except Exception:
        font = ImageFont.load_default()

    labels = []
    for idx, (ckey, img_path) in enumerate(char_items):
        x = margin + idx * (tile_w + gap)
        y = margin
        try:
            with Image.open(img_path) as im:
                rgb = im.convert("RGB")
                fitted = ImageOps.fit(rgb, (tile_w, tile_h), method=Image.Resampling.LANCZOS)
                canvas.paste(fitted, (x, y))
        except Exception:
            draw.rectangle([x, y, x + tile_w, y + tile_h], fill=(220, 224, 230))

        draw.rectangle([x, y + tile_h, x + tile_w, y + tile_h + label_h], fill=(15, 23, 42))
        label_txt = str(ckey).upper().replace("_", " ")[:24]
        labels.append(label_txt)
        try:
            bbox = draw.textbbox((0, 0), label_txt, font=font)
            tw = bbox[2] - bbox[0]
            th = bbox[3] - bbox[1]
            tx = x + max(6, (tile_w - tw) // 2)
            ty = y + tile_h + max(4, (label_h - th) // 2) - 2
        except Exception:
            tx = x + 12
            ty = y + tile_h + 12
        draw.text((tx, ty), label_txt, fill=(255, 255, 255), font=font)

    canvas.save(out_path, format="JPEG", quality=92)
    return out_path, labels


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
_tg_last_err_log = 0.0


def _log_tg_failure(detail):
    global _tg_last_err_log
    now_t = time.time()
    if now_t - _tg_last_err_log >= 10.0:
        _tg_last_err_log = now_t
        add_log(f"⚠️ টেলিগ্রাম এরর: {detail}", level="warn")


def _handle_tg_response(res):
    if res.status_code == 200:
        return True
    try:
        desc = res.json().get("description", res.text[:120])
    except Exception:
        desc = res.text[:120]
    if res.status_code == 429:
        try:
            retry_after = int(res.json().get("parameters", {}).get("retry_after", 5))
        except Exception:
            retry_after = 5
        _log_tg_failure(f"429 Rate Limit ({retry_after}s অপেক্ষা)")
        time.sleep(min(retry_after, 30))
        return False
    _log_tg_failure(f"HTTP {res.status_code} - {desc}")
    return False


def _send_telegram_message_sync(text):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        _log_tg_failure("TELEGRAM_BOT_TOKEN বা TELEGRAM_CHAT_ID সেট করা নেই")
        return False
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendMessage"
    try:
        res = requests.post(
            url,
            data={
                "chat_id": TELEGRAM_CHAT_ID,
                "text": text,
                "parse_mode": "HTML",
                "disable_web_page_preview": True,
            },
            timeout=20,
        )
        return _handle_tg_response(res)
    except Exception as e:
        _log_tg_failure(str(e)[:120])
        return False


def _build_scene_caption(scene_num, narration):
    safe_narration = html.escape(str(narration or ""))
    caption = f'<b>Scene #{scene_num:03d}</b>\n\n"{safe_narration}"'
    if len(caption) > 1000:
        caption = caption[:997] + '..."'
    return caption


def _send_telegram_photo_sync(image_bytes, scene_num, narration):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        _log_tg_failure("TELEGRAM_BOT_TOKEN বা TELEGRAM_CHAT_ID সেট করা নেই")
        return False
    url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto"
    caption = _build_scene_caption(scene_num, narration)
    files = {"photo": (f"scene_{scene_num:03d}.jpg", image_bytes, "image/jpeg")}
    data = {
        "chat_id": TELEGRAM_CHAT_ID,
        "caption": caption,
        "parse_mode": "HTML",
    }
    try:
        res = requests.post(url, files=files, data=data, timeout=30)
        return _handle_tg_response(res)
    except Exception as e:
        _log_tg_failure(str(e)[:120])
        return False


def _send_telegram_photo_url_sync(s3_cli, r2_key, scene_num, narration):
    if not TELEGRAM_BOT_TOKEN or not TELEGRAM_CHAT_ID:
        _log_tg_failure("TELEGRAM_BOT_TOKEN বা TELEGRAM_CHAT_ID সেট করা নেই")
        return False

    try:
        photo_url = s3_cli.generate_presigned_url(
            "get_object",
            Params={"Bucket": R2_BUCKET_NAME, "Key": r2_key},
            ExpiresIn=900,
        )
        url = f"https://api.telegram.org/bot{TELEGRAM_BOT_TOKEN}/sendPhoto"
        res = requests.post(
            url,
            data={
                "chat_id": TELEGRAM_CHAT_ID,
                "photo": photo_url,
                "caption": _build_scene_caption(scene_num, narration),
                "parse_mode": "HTML",
            },
            timeout=25,
        )
        if res.status_code == 200:
            return True
        if res.status_code == 429:
            return _handle_tg_response(res)
    except Exception:
        pass

    img_bytes = r2_download_bytes(s3_cli, r2_key)
    if img_bytes:
        try:
            return _send_telegram_photo_sync(img_bytes, scene_num, narration)
        finally:
            del img_bytes
    _log_tg_failure(f"R2 থেকে ছবি লোড করা যায়নি ({r2_key})")
    return False


def _telegram_queue_loop():
    s3_local = None
    while True:
        item = tg_queue.get()
        try:
            kind = item[0]
            if kind == "msg":
                _send_telegram_message_sync(item[1])
            elif kind == "photo":
                _send_telegram_photo_sync(item[1], item[2], item[3])
            elif kind == "photo_r2":
                r2_key, scene_num, narration = item[1], item[2], item[3]
                if s3_local is None:
                    s3_local = get_r2_client()
                if s3_local:
                    _send_telegram_photo_url_sync(s3_local, r2_key, scene_num, narration)
            time.sleep(1.2)
        except Exception as e:
            _log_tg_failure(str(e)[:120])
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
        _log_tg_failure("Telegram queue full (1000+)")


def notify_cookie_issue(name, preview, reason, level="warning"):
    icon = "🚫" if level == "critical" else "⚠️"
    title = "কুকি অকার্যকর হয়েছে" if level == "critical" else "কুকি সতর্কতা"
    send_telegram_message(
        f"{icon} <b>{title} ({html.escape(name)})</b> ({html.escape(preview)})\n"
        f"সমস্যা: <code>{html.escape(str(reason)[:220])}</code>"
    )


# ================= GitHub Actions ট্রিগার হেল্পার =================
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
    if s3 and mode in ("zip", "both"):
        r2_write_json(
            s3,
            f"projects/{slug}/_archive/zip_status.json",
            {
                "slug": slug,
                "status": "queued",
                "percent": 5,
                "message": "২য় সার্ভারে ZIP তৈরির কমান্ড পাঠানো হয়েছে...",
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
        try:
            err_msg = res.json().get("message", res.text[:160])
        except Exception:
            err_msg = res.text[:160]
        if s3 and mode in ("video", "both"):
            r2_write_json(
                s3,
                f"projects/{slug}/_video/video_status.json",
                {
                    "slug": slug,
                    "status": "failed",
                    "percent": 0,
                    "message": f"GitHub ট্রিগার ব্যর্থ: {err_msg}",
                    "updated_at": now_utc_iso(),
                },
            )
        if s3 and mode in ("zip", "both"):
            r2_write_json(
                s3,
                f"projects/{slug}/_archive/zip_status.json",
                {
                    "slug": slug,
                    "status": "failed",
                    "percent": 0,
                    "message": f"GitHub ট্রিগার ব্যর্থ: {err_msg}",
                    "updated_at": now_utc_iso(),
                },
            )
        return False, f"GitHub HTTP {res.status_code}: {err_msg}"
    except Exception as e:
        return False, str(e)[:150]


# ================= কুকি টেস্ট ওয়ার্কার =================
async def _test_single_cookie_async(cookie_entry):
    cid = cookie_entry["id"]
    with state_lock:
        for c in cookie_pool:
            if c["id"] == cid:
                c["status"] = "connecting"
                c["last_error"] = ""

    add_log(f"🔍 {cookie_entry['name']} ({cookie_entry['preview']}) পরীক্ষা করা হচ্ছে...")
    client = None
    try:
        # প্রক্সি সাপোর্টসহ ইনিট
        client = GeminiClient(
            secure_1psid=cookie_entry["psid"],
            secure_1psidts=cookie_entry.get("psidts"),
            proxy=PROXY_URL if PROXY_URL else None,
        )
        await client.init(timeout=45, auto_close=False, auto_refresh=True)
        _sync_client_cookies_to_storage(cid, client)  # নতুন কুকি সেভ

        with state_lock:
            for c in cookie_pool:
                if c["id"] == cid:
                    c["status"] = "active" if c.get("enabled", True) else "paused"
                    c["consecutive_fails"] = 0
                    c["cooldown_level"] = 0
                    c["cooldown_until"] = 0.0
                    c["last_error"] = ""
        add_log(f"✅ {cookie_entry['name']} একদম সচল আছে!")
        return True
    except Exception as e:
        err = str(e)[:150]
        with state_lock:
            for c in cookie_pool:
                if c["id"] == cid:
                    c["status"] = "failed"
                    c["fail_count"] += 1
                    c["last_error"] = err
        add_log(f"❌ {cookie_entry['name']} কাজ করছে না: {err}")
        notify_cookie_issue(cookie_entry["name"], cookie_entry["preview"], f"লগইন ব্যর্থ: {err}", level="critical")
        return False
    finally:
        if client:
            try:
                await asyncio.wait_for(client.close(), timeout=4)
            except Exception:
                pass


async def async_test_cookies_worker(target_id=None):
    bootstrap_from_r2()
    update_state(is_testing_cookies=True, status_text="Testing Cookie(s)...")

    with state_lock:
        targets = [
            dict(c) for c in cookie_pool
            if (target_id is None and c.get("enabled", True)) or (c["id"] == target_id)
        ]

    if not targets:
        update_state(is_testing_cookies=False, status_text="No Cookie to Test")
        add_log("⚠️ টেস্ট করার মতো কোনো সক্রিয় কুকি পাওয়া যায়নি।")
        return

    ok_cnt = 0
    for item in targets:
        if await _test_single_cookie_async(item):
            ok_cnt += 1

    save_cookies_to_r2()
    status_txt = f"Cookies Tested ({ok_cnt}/{len(targets)} Active)"
    update_state(is_testing_cookies=False, status_text=status_txt)


def test_cookies_worker(target_id=None):
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    try:
        loop.run_until_complete(async_test_cookies_worker(target_id))
    finally:
        loop.close()


# ================= তাৎক্ষণিক ক্যানসেলেবল ও Pause হেল্পার =================
async def run_cancellable(coro, stop_event, timeout=None):
    task = asyncio.create_task(coro)
    stop_task = asyncio.create_task(stop_event.wait())
    try:
        done, _ = await asyncio.wait(
            {task, stop_task},
            timeout=timeout,
            return_when=asyncio.FIRST_COMPLETED,
        )
        if stop_task in done:
            task.cancel()
            try:
                await task
            except (asyncio.CancelledError, Exception):
                pass
            raise InterruptedError("Stopped by user")
        if not done:
            task.cancel()
            try:
                await task
            except (asyncio.CancelledError, Exception):
                pass
            raise TimeoutError(f"Timeout ({timeout}s)")
        return task.result()
    finally:
        if not stop_task.done():
            stop_task.cancel()


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
    if seconds <= 0:
        return not stop_event.is_set()
    if stop_event.is_set():
        return False

    tasks = [asyncio.create_task(stop_event.wait())]
    if wakeup_event is not None:
        tasks.append(asyncio.create_task(wakeup_event.wait()))

    try:
        done, pending = await asyncio.wait(
            tasks,
            timeout=seconds,
            return_when=asyncio.FIRST_COMPLETED,
        )
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


def _is_auth_error(err_msg):
    low = str(err_msg or "").lower()
    return any(k in low for k in (
        "autherror", "failed to initialize", "1psid", "unauthorized", "401", "forbidden", "cookie",
        "are you signed in", "signed out", "sign in", "log in", "logged in", "image creation may not"
    ))


def _is_rate_limit_error(err_msg):
    low = str(err_msg or "").lower()
    return any(k in low for k in ("429", "too many", "rate limit", "quota", "resource exhausted"))


# ================= কঠোর সিরিয়াল রোটেশন (১ -> ২ -> ৩ -> ৪ -> ৫ -> ১...) =================
def _pick_next_cookie():
    global rr_cursor
    now_ts = time.time()
    cooldowns = []

    with state_lock:
        n = len(cookie_pool)
        if n == 0:
            return None, None

        start_idx = rr_cursor % n
        for offset in range(n):
            idx = (start_idx + offset) % n
            c = cookie_pool[idx]

            if not c.get("enabled", True):
                c["status"] = "paused"
                continue
            if c.get("status") == "failed":
                continue

            cd_until = c.get("cooldown_until", 0.0)
            if cd_until > now_ts:
                c["status"] = "cooldown"
                cooldowns.append(cd_until - now_ts)
                continue

            if c.get("status") == "cooldown" and cd_until <= now_ts:
                c["status"] = "standby"
                c["cooldown_probe"] = True

            rr_cursor = (idx + 1) % n
            picked = dict(c)
            picked["order_num"] = idx + 1
            return picked, 0.0

    if cooldowns:
        return None, min(cooldowns)

    return None, None


def _mark_cookie_cooldown(cid, err_msg, force_cooldown=False):
    now_ts = time.time()
    msg_out = None
    close_client = False

    with state_lock:
        target = next((c for c in cookie_pool if c["id"] == cid), None)
        if not target:
            return None, False

        target["fail_count"] += 1
        target["consecutive_fails"] += 1
        target["last_error"] = err_msg

        if _is_auth_error(err_msg):
            target["status"] = "failed"
            target["cooldown_until"] = 0.0
            close_client = True
            _clear_gemini_cache(target["psid"])
            msg_out = ("auth", target["name"], target["preview"])
        elif force_cooldown or target.get("cooldown_probe") or _is_rate_limit_error(err_msg) or target["consecutive_fails"] >= 2:
            lvl = min(target.get("cooldown_level", 0) + 1, len(COOLDOWN_TIERS))
            dur = COOLDOWN_TIERS[lvl - 1]
            target["cooldown_level"] = lvl
            target["cooldown_until"] = now_ts + dur
            target["cooldown_probe"] = False
            target["status"] = "cooldown"
            close_client = True
            msg_out = ("cooldown", target["name"], dur, lvl)
        else:
            target["status"] = "active"

    return msg_out, close_client


def _mark_cookie_success(cid):
    with state_lock:
        target = next((c for c in cookie_pool if c["id"] == cid), None)
        if not target:
            return
        target["status"] = "active"
        target["success_count"] += 1
        target["consecutive_fails"] = 0
        target["cooldown_level"] = 0
        target["cooldown_until"] = 0.0
        target["cooldown_probe"] = False
        target["last_error"] = ""
        target["last_used_at"] = time.time()


async def _call_gemini_with_pool(
    clients_map,
    last_alert_at,
    stop_event,
    wakeup_event,
    unpause_event,
    prompt,
    files=None,
    expect_image=True,
    status_label="Rendering",
    log_prefix="",
    temp_filename="temp_gen.jpg",
    max_attempts=3,
):
    """প্রক্সি ও ডিরেক্ট-ডাউনলোড অপটিমাইজেশনসহ সিরিয়াল কুকি রোটেশন কলার"""
    last_error = "সব চেষ্টায় ব্যর্থ"

    for attempt in range(1, max_attempts + 1):
        if stop_event.is_set():
            raise InterruptedError("Stopped by user")
        if not await wait_if_paused(stop_event, unpause_event):
            raise InterruptedError("Stopped by user")

        with state_lock:
            valid_map = {
                c["id"]: c.get("version", 1)
                for c in cookie_pool
                if c.get("enabled", True) and c.get("status") != "failed"
            }

        for stale_id in list(clients_map.keys()):
            stored_cli, stored_ver = clients_map[stale_id]
            if stale_id not in valid_map or valid_map[stale_id] != stored_ver:
                clients_map.pop(stale_id)
                try:
                    await asyncio.wait_for(stored_cli.close(), timeout=3)
                except Exception:
                    pass

        chosen = None
        while not stop_event.is_set():
            if not await wait_if_paused(stop_event, unpause_event):
                raise InterruptedError("Stopped by user")
            chosen, wait_cd = _pick_next_cookie()
            if chosen is not None:
                break
            if wait_cd is None:
                add_log("🚫 কোনো সচল কুকি অবশিষ্ট নেই! নতুন কুকি অ্যাড করুন বা Pause/Failed ঠিক করুন।")
                return "NO_COOKIES", None, "কোনো সচল কুকি নেই"
            wait_chunk = min(wait_cd, 5.0)
            update_state(status_text=f"All Cookies Cooldown ({int(wait_cd)}s)...", active_account="-")
            add_log(f"❄️ সব কুকি কুলডাউনে আছে। {int(wait_cd)} সেকেন্ড অপেক্ষা চলছে...")
            await smart_sleep(wait_chunk, stop_event, wakeup_event)

        if stop_event.is_set() or not chosen:
            raise InterruptedError("Stopped by user")

        cid = chosen["id"]
        cname = chosen["name"]
        c_order = chosen.get("order_num", 1)
        c_ver = chosen.get("version", 1)
        acc_label = f"#{c_order} {cname}"

        # পার-একাউন্ট পেসিং
        elapsed_since_use = time.time() - chosen.get("last_used_at", 0.0)
        if chosen.get("last_used_at", 0.0) > 0 and elapsed_since_use < MIN_ACCOUNT_INTERVAL:
            need_wait = round((MIN_ACCOUNT_INTERVAL - elapsed_since_use) + random.uniform(0.5, 2.5), 1)
            update_state(status_text=f"Pacing {acc_label} ({need_wait}s)...", active_account=acc_label)
            if not await smart_sleep(need_wait, stop_event, wakeup_event):
                raise InterruptedError("Stopped by user")
            if not await wait_if_paused(stop_event, unpause_event):
                raise InterruptedError("Stopped by user")

        client_entry = clients_map.get(cid)
        client = client_entry[0] if (client_entry and client_entry[1] == c_ver) else None

        if client is None:
            with state_lock:
                for c in cookie_pool:
                    if c["id"] == cid:
                        c["status"] = "connecting"
            update_state(status_text=f"Connecting {acc_label}...", active_account=acc_label)
            add_log(f"🔑 {acc_label} ({chosen['preview']}) কানেক্ট হচ্ছে...")
            try:
                # প্রক্সি সাপোর্টসহ জেমিনি ক্লায়েন্ট
                client = GeminiClient(
                    secure_1psid=chosen["psid"],
                    secure_1psidts=chosen.get("psidts"),
                    proxy=PROXY_URL if PROXY_URL else None,
                )
                await run_cancellable(
                    client.init(timeout=45, auto_close=False, auto_refresh=True),
                    stop_event,
                    timeout=50,
                )
                clients_map[cid] = (client, c_ver)
                _sync_client_cookies_to_storage(cid, client)  # রিনিউ কুকি সংরক্ষণ
                add_log(f"✅ {acc_label} কানেক্ট হয়েছে!")
            except InterruptedError:
                raise
            except Exception as init_err:
                err_msg = str(init_err)[:140]
                last_error = f"{acc_label} লগইন ব্যর্থ: {err_msg}"
                add_log(f"❌ {acc_label} লগইন ব্যর্থ: {err_msg}")
                _mark_cookie_cooldown(cid, err_msg, force_cooldown=True)
                save_cookies_to_r2()
                continue

        with state_lock:
            for c in cookie_pool:
                if c["id"] == cid:
                    c["status"] = "working"

        update_state(status_text=f"{status_label} ({acc_label})...", active_account=acc_label)
        if log_prefix:
            add_log(f"🎨 [{acc_label}] {log_prefix} (চেষ্টা {attempt}/{max_attempts})...")

        temp_path = os.path.join(STORAGE_DIR, temp_filename)
        try:
            coro = client.generate_content(prompt, files=files) if files else client.generate_content(prompt)
            response = await run_cancellable(coro, stop_event, timeout=95)
            _sync_client_cookies_to_storage(cid, client)  # প্রতিটি কলের পর কুকি রিনিউ চেক

            if not expect_image:
                resp_text = (getattr(response, "text", "") or "").strip()
                if _is_auth_error(resp_text):
                    raise RuntimeError(f"AuthError: কুকি লগআউট হয়ে গেছে ({resp_text[:100]})")
                if not resp_text:
                    _mark_cookie_success(cid)
                    last_error = "Gemini টেক্সট রেসপন্স খালি ছিল"
                    if attempt < max_attempts and not await smart_sleep(2.0, stop_event, wakeup_event):
                        raise InterruptedError("Stopped by user")
                    continue
                _mark_cookie_success(cid)
                return "OK", resp_text, acc_label

            # ইমেজ রেসপন্স হ্যান্ডলিং
            if not response or not response.images:
                resp_text = (getattr(response, "text", "") or "").strip()[:140]
                if _is_auth_error(resp_text):
                    raise RuntimeError(f"AuthError: কুকি লগআউট হয়ে গেছে ({resp_text})")
                _mark_cookie_success(cid)
                last_error = f"ইমেজ আসেনি: {resp_text}" if resp_text else "Gemini ইমেজ রিটার্ন করেনি (Prompt/Filter)"
                add_log(f"⚠️ [{acc_label}] {log_prefix}: {last_error}")
                if attempt < max_attempts and not await smart_sleep(2.5, stop_event, wakeup_event):
                    raise InterruptedError("Stopped by user")
                continue

            first_image = response.images[0]
            raw_bytes = None

            # ================= ব্যান্ডউইথ সেভিং অপটিমাইজেশন =================
            # গুগলের ১ MB ছবি প্রক্সি দিয়ে না টেনে সরাসরি রেন্ডারের ফ্রি ব্যান্ডউইথ দিয়ে ডাউনলোড
            img_url = getattr(first_image, "url", None)
            if img_url:
                try:
                    r_img = await run_cancellable(
                        asyncio.to_thread(
                            requests.get,
                            img_url,
                            headers={"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)"},
                            timeout=25,
                        ),
                        stop_event,
                        timeout=30,
                    )
                    if r_img and r_img.status_code == 200 and len(r_img.content) > 1000:
                        raw_bytes = r_img.content
                except Exception:
                    raw_bytes = None

            # ফলব্যাক: ডিরেক্ট ফেচ না হলে সাধারণ save() মেথড
            if not raw_bytes:
                await run_cancellable(
                    first_image.save(path=STORAGE_DIR, filename=temp_filename),
                    stop_event,
                    timeout=30,
                )
                if not os.path.exists(temp_path):
                    raise RuntimeError("টেম্পোরারি ইমেজ সেভ হয়নি")
                with open(temp_path, "rb") as f:
                    raw_bytes = f.read()

            _mark_cookie_success(cid)
            return "OK", raw_bytes, acc_label

        except InterruptedError:
            raise
        except Exception as e:
            err_msg = str(e)[:140]
            last_error = err_msg
            add_log(f"⚠️ [{acc_label}] {log_prefix} ব্যর্থ (চেষ্টা {attempt}/{max_attempts}): {err_msg}")

            cd_info, need_close = _mark_cookie_cooldown(cid, err_msg)
            if need_close and cid in clients_map:
                bad_cli, _ = clients_map.pop(cid)
                try:
                    await asyncio.wait_for(bad_cli.close(), timeout=3)
                except Exception:
                    pass

            if cd_info:
                if cd_info[0] == "auth":
                    add_log(f"🚫 {cd_info[1]} অকার্যকর/লগআউট হয়েছে! কুকিটি Failed হিসেবে চিহ্নিত হলো।")
                    now_ts = time.time()
                    if now_ts - last_alert_at.get(cid, 0.0) > 120:
                        last_alert_at[cid] = now_ts
                        notify_cookie_issue(cd_info[1], cd_info[2], err_msg, level="critical")
                elif cd_info[0] == "cooldown":
                    mins = int(cd_info[2] // 60)
                    add_log(f"❄️ {cd_info[1]} কুলডাউনে গেল ({mins} মিনিট, লেভেল {cd_info[3]})।")

            save_cookies_to_r2()
            if attempt < max_attempts:
                if not await smart_sleep(random.uniform(2.5, 4.5), stop_event, wakeup_event):
                    raise InterruptedError("Stopped by user")
        finally:
            if os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except Exception:
                    pass

    return "FAILED", None, last_error


# ================= পুরোনো JSON অটো-অ্যানালাইজ ও স্টোরি বাইবেল হেল্পার =================
def _extract_json_block(raw_text):
    txt = str(raw_text or "").strip()
    m = re.search(r"```(?:json)?\s*(\{.*?\})\s*```", txt, flags=re.DOTALL)
    if m:
        txt = m.group(1)
    else:
        start = txt.find("{")
        end = txt.rfind("}")
        if start != -1 and end != -1 and end > start:
            txt = txt[start:end + 1]
    return json.loads(txt)


async def _auto_analyze_old_json(s3, slug, title, scenes_data, clients_map, last_alert_at, stop_event, wakeup_event, unpause_event):
    cached = r2_read_json(s3, f"projects/{slug}/story_bible.json")
    if isinstance(cached, dict) and (cached.get("style_bible") or cached.get("characters")):
        add_log("♻️ R2 থেকে আগে তৈরি করা Story Bible লোড হয়েছে।")
        return cached

    add_log("🧠 পুরোনো JSON পাওয়া গেছে — অটোমেটিক Style ও Character শনাক্ত করা হচ্ছে...")
    total = len(scenes_data)
    step = max(1, total // 40)
    samples = []
    for idx in range(0, total, step):
        sc = scenes_data[idx]
        if not isinstance(sc, dict):
            continue
        p = str(sc.get("image_prompt", ""))[:150].strip()
        n = str(sc.get("narration", ""))[:80].strip()
        if p or n:
            samples.append(f"#{idx + 1}: {p} | {n}")
        if len(samples) >= 42:
            break

    if not samples:
        return {"style_bible": "", "eras": {}, "characters": {}, "char_keywords": {}, "era_keywords": {}}

    analysis_prompt = (
        "Analyze these story scene samples and extract visual consistency rules. "
        "Return ONLY valid raw JSON (no markdown, no explanation) with this exact structure:\n"
        '{\n'
        '  "style_bible": "concise unified art style, lighting and render quality across scenes",\n'
        '  "eras": {"era_key": "short atmosphere/setting/outfit era description"},\n'
        '  "era_keywords": {"era_key": ["keyword1", "keyword2"]},\n'
        '  "characters": {"char_key": "Solo centered front-facing upper-body portrait on a plain neutral background, age, gender, face, hair, outfit"},\n'
        '  "char_keywords": {"char_key": ["name_or_phrase_1", "name_or_phrase_2"]}\n'
        '}\n'
        "Rules: Detect only recurring named or clearly distinct main characters (0 to 10 max). "
        "If no distinct recurring character can be identified, keep characters as {}.\n\n"
        f"Title: {title}\nSamples:\n" + "\n".join(samples)
    )

    status, resp_text, err = await _call_gemini_with_pool(
        clients_map=clients_map,
        last_alert_at=last_alert_at,
        stop_event=stop_event,
        wakeup_event=wakeup_event,
        unpause_event=unpause_event,
        prompt=analysis_prompt,
        files=None,
        expect_image=False,
        status_label="Analyzing Story Bible",
        log_prefix="গল্পের স্টাইল ও চরিত্র অ্যানালাইজ হচ্ছে",
        max_attempts=2,
    )

    result = {"style_bible": "", "eras": {}, "characters": {}, "char_keywords": {}, "era_keywords": {}}
    if status == "OK" and resp_text:
        try:
            parsed = _extract_json_block(resp_text)
            if isinstance(parsed, dict):
                result["style_bible"] = str(parsed.get("style_bible") or "").strip()
                if isinstance(parsed.get("eras"), dict):
                    result["eras"] = {str(k): str(v) for k, v in parsed["eras"].items() if v}
                if isinstance(parsed.get("characters"), dict):
                    result["characters"] = {str(k): str(v) for k, v in parsed["characters"].items() if v}
                if isinstance(parsed.get("char_keywords"), dict):
                    result["char_keywords"] = parsed["char_keywords"]
                if isinstance(parsed.get("era_keywords"), dict):
                    result["era_keywords"] = parsed["era_keywords"]
                add_log(
                    f"✨ Auto-Bible তৈরি: {len(result['characters'])} টি চরিত্র, "
                    f"{len(result['eras'])} টি সময়কাল শনাক্ত হয়েছে।"
                )
        except Exception as pe:
            add_log(f"⚠️ Auto-Analyze JSON পার্স হয়নি, Scene #1 Style Anchor ব্যবহার হবে ({str(pe)[:50]})")

    r2_write_json(s3, f"projects/{slug}/story_bible.json", result)
    return result


def _resolve_scene_tags(sc, bible):
    era_key = str(sc.get("era") or "").strip()
    raw_chars = sc.get("characters")
    char_list = []

    if isinstance(raw_chars, list):
        char_list = [str(x).strip() for x in raw_chars if str(x).strip()]
    elif isinstance(raw_chars, str) and raw_chars.strip():
        char_list = [raw_chars.strip()]

    haystack = (str(sc.get("image_prompt") or "") + " " + str(sc.get("narration") or "")).lower()

    if not era_key and bible.get("era_keywords"):
        for ek, kws in bible["era_keywords"].items():
            if isinstance(kws, list) and any(str(w).lower() in haystack for w in kws if str(w).strip()):
                era_key = str(ek)
                break

    if raw_chars is None and bible.get("char_keywords"):
        for ck, kws in bible["char_keywords"].items():
            if isinstance(kws, list) and any(str(w).lower() in haystack for w in kws if str(w).strip()):
                char_list.append(str(ck))

    return era_key, char_list


def _build_scene_prompt(prompt, ratio, style_bible, era_desc, char_labels, ref_mode):
    parts = []
    if ref_mode == "single":
        parts.append(
            "Use the attached image strictly as the character's exact facial identity, hairstyle, age, outfit, and art style reference. "
            "Create a completely new pose, camera angle, expression, and background for the scene below."
        )
    elif ref_mode == "collage":
        names_str = ", ".join(char_labels)
        parts.append(
            f"The attached reference sheet shows labeled character portraits side by side ({names_str}). "
            "Keep each named character's exact facial identity, age, and appearance in the new scene below."
        )
    elif ref_mode == "style_anchor":
        parts.append(
            "Use the attached image strictly as visual art style, lighting, and color grading reference "
            "(and keep consistent character identity if the same character appears). Create a completely new scene below."
        )

    if style_bible:
        parts.append(f"Art Style: {style_bible}.")
    if era_desc:
        parts.append(f"Era & Atmosphere: {era_desc}.")

    parts.append(f"Scene Description: {prompt}")
    parts.append(f"Aspect ratio {ratio}")
    return " ".join(parts)


# ================= মূল জেনারেশন ওয়ার্কার =================
async def async_generation_worker(
    scenes_data,
    title,
    ratio,
    watermark_mode,
    target_scene_nums=None,
    story_cfg=None,
):
    global rr_cursor
    bootstrap_from_r2()
    ensure_telegram_worker()
    slug = make_project_slug(title)
    total = len(scenes_data)
    story_cfg = story_cfg or {}

    consistency_mode = str(story_cfg.get("consistency_mode") or "auto").strip().lower()
    style_bible = str(story_cfg.get("style_bible") or "").strip()
    eras_map = story_cfg.get("eras") if isinstance(story_cfg.get("eras"), dict) else {}
    chars_map = story_cfg.get("characters") if isinstance(story_cfg.get("characters"), dict) else {}
    auto_video = bool(story_cfg.get("auto_video", False))

    proj_refs_dir = os.path.join(REFS_DIR, slug)
    os.makedirs(proj_refs_dir, exist_ok=True)

    loop = asyncio.get_running_loop()
    stop_event = asyncio.Event()
    wakeup_event = asyncio.Event()
    unpause_event = asyncio.Event()
    unpause_event.set()

    with state_lock:
        new_job_id = state["job_id"] + 1
        if state["should_stop"]:
            stop_event.set()
        rr_cursor = 0
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
            "status_text": "Initializing R2 & Cookie Pool...",
            "active_account": "-",
            "failed_scenes": [],
            "logs": [],
        })

    add_log(f"🚀 প্রজেক্ট শুরু: {title} (মোট {total} টি সিন)" + (" [Auto-Video ON]" if auto_video else ""))
    if target_scene_nums:
        add_log(f"♻️ রিট্রাই মোড: {len(target_scene_nums)} টি নির্দিষ্ট সিন রান হচ্ছে।")
    add_log(f"📁 R2 ফোল্ডার: projects/{slug}/")

    clients_map = {}
    last_alert_at = {}
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

        for f in os.listdir(STORAGE_DIR):
            try:
                os.remove(os.path.join(STORAGE_DIR, f))
            except Exception:
                pass

        with state_lock:
            has_any_cookie = len(cookie_pool) > 0
        if not has_any_cookie:
            add_log("❌ কোনো কুকি অ্যাড করা নেই! Cookies ট্যাব থেকে কুকি অ্যাড করুন।")
            update_state(status_text="Cookie Missing Error")
            send_telegram_message("❌ <b>প্রজেক্ট শুরু হয়নি:</b> কোনো Gemini কুকি অ্যাড করা নেই!")
            return

        voiceover_text = build_clean_voiceover_text(scenes_data)
        try:
            await run_cancellable(
                asyncio.to_thread(
                    r2_write_json,
                    s3,
                    f"projects/{slug}/input_scenes.json",
                    {
                        "project_title": title,
                        "aspect_ratio": ratio,
                        "watermark": watermark_mode,
                        "consistency_mode": consistency_mode,
                        "auto_video": auto_video,
                        "style_bible": style_bible,
                        "eras": eras_map,
                        "characters": chars_map,
                        "scenes": scenes_data,
                    },
                ),
                stop_event,
                timeout=25,
            )
            meta_bytes = json.dumps({
                "title": title,
                "slug": slug,
                "aspect_ratio": ratio,
                "total_scenes": total,
                "updated_at": now_utc_iso(),
            }, ensure_ascii=False, indent=2).encode("utf-8")
            await run_cancellable(
                asyncio.to_thread(r2_upload_bytes, s3, f"projects/{slug}/meta.json", meta_bytes, "application/json; charset=utf-8"),
                stop_event,
                timeout=20,
            )

            if voiceover_text:
                await run_cancellable(
                    asyncio.to_thread(
                        r2_upload_bytes,
                        s3,
                        f"projects/{slug}/story.txt",
                        voiceover_text.encode("utf-8"),
                        "text/plain; charset=utf-8",
                    ),
                    stop_event,
                    timeout=20,
                )
        except InterruptedError:
            raise
        except Exception as e:
            add_log(f"⚠️ ইনপুট/story.txt সেভে সতর্কতা: {str(e)[:60]}")

        existing_files = await run_cancellable(
            asyncio.to_thread(r2_list_existing_scenes, s3, slug),
            stop_event,
            timeout=25,
        )
        existing_jpgs = {f for f in existing_files if f.lower().endswith(".jpg")}
        if existing_jpgs:
            add_log(f"♻️ R2-তে আগে থেকেই {len(existing_jpgs)} টি ছবি আছে (অটো-রিজিউম চালু)।")

        _sync_job_progress(s3, "running")
        send_telegram_message(
            f"🚀 <b>{html.escape(title)}</b>\n"
            f"মোট সিন: {total}\n"
            f"কাজ শুরু হয়েছে!"
        )

        # ================= কনসিস্টেন্সি সেটআপ =================
        auto_bible = {"style_bible": style_bible, "eras": eras_map, "characters": chars_map, "char_keywords": {}, "era_keywords": {}}
        if consistency_mode == "auto" and not style_bible and not chars_map:
            auto_bible = await _auto_analyze_old_json(
                s3, slug, title, scenes_data, clients_map, last_alert_at, stop_event, wakeup_event, unpause_event
            )
            style_bible = auto_bible.get("style_bible", "")
            eras_map = auto_bible.get("eras", {})
            chars_map = auto_bible.get("characters", {})

        ref_paths = {}
        existing_refs_r2 = await run_cancellable(
            asyncio.to_thread(r2_list_refs, s3, slug),
            stop_event,
            timeout=20,
        )

        if consistency_mode == "auto" and chars_map:
            add_log(f"🎭 চরিত্র রেফারেন্স প্রস্তুত হচ্ছে ({len(chars_map)} জন)...")
            for ckey, cdesc in chars_map.items():
                if stop_event.is_set():
                    break
                if not await wait_if_paused(stop_event, unpause_event):
                    break

                safe_ckey = _safe_key_name(ckey)
                ref_fname = f"{safe_ckey}.jpg"
                local_ref = os.path.join(proj_refs_dir, ref_fname)
                r2_ref_key = f"projects/{slug}/_refs/{ref_fname}"

                if os.path.exists(local_ref):
                    ref_paths[ckey] = local_ref
                    continue
                if ref_fname in existing_refs_r2:
                    data_bytes = await run_cancellable(
                        asyncio.to_thread(r2_download_bytes, s3, r2_ref_key),
                        stop_event,
                        timeout=25,
                    )
                    if data_bytes:
                        with open(local_ref, "wb") as rf:
                            rf.write(data_bytes)
                        ref_paths[ckey] = local_ref
                        add_log(f"♻️ R2 থেকে '{ckey}' রেফারেন্স রিস্টোর হয়েছে।")
                        continue

                ref_prompt = (
                    "Generate an image of a single solo character, centered front-facing upper-body portrait "
                    "against a plain neutral studio background, clear sharp face and eyes, even studio lighting. "
                    f"{('Art Style: ' + style_bible + '. ') if style_bible else ''}"
                    f"Character details: {cdesc}, aspect ratio 1:1"
                )
                r_status, r_bytes, r_err = await _call_gemini_with_pool(
                    clients_map=clients_map,
                    last_alert_at=last_alert_at,
                    stop_event=stop_event,
                    wakeup_event=wakeup_event,
                    unpause_event=unpause_event,
                    prompt=ref_prompt,
                    files=None,
                    expect_image=True,
                    status_label=f"Creating Ref: {ckey}",
                    log_prefix=f"রেফারেন্স পোর্ট্রেট তৈরি হচ্ছে ({ckey})",
                    temp_filename=f"_ref_{ref_fname}",
                    max_attempts=3,
                )
                if r_status == "NO_COOKIES":
                    break
                if r_status == "OK" and r_bytes:
                    with open(local_ref, "wb") as rf:
                        rf.write(r_bytes)
                    await run_cancellable(
                        asyncio.to_thread(r2_upload_bytes, s3, r2_ref_key, r_bytes, "image/jpeg"),
                        stop_event,
                        timeout=25,
                    )
                    ref_paths[ckey] = local_ref
                    add_log(f"✅ '{ckey}' মাস্টার রেফারেন্স সেভ হয়েছে!")
                    del r_bytes
                else:
                    add_log(f"⚠️ '{ckey}' রেফারেন্স তৈরি করা যায়নি: {r_err}")

        style_anchor_local = os.path.join(proj_refs_dir, "_style_anchor.jpg")
        style_anchor_r2 = f"projects/{slug}/_refs/_style_anchor.jpg"
        use_style_anchor = (consistency_mode in ("auto", "style_only")) and not ref_paths

        if use_style_anchor and not os.path.exists(style_anchor_local) and "_style_anchor.jpg" in existing_refs_r2:
            sa_bytes = await run_cancellable(
                asyncio.to_thread(r2_download_bytes, s3, style_anchor_r2),
                stop_event,
                timeout=25,
            )
            if sa_bytes:
                with open(style_anchor_local, "wb") as sf:
                    sf.write(sa_bytes)
                add_log("♻️ R2 থেকে Style Anchor ইমেজ রিস্টোর হয়েছে।")

        # ================= একক সিন জেনারেশন =================
        aborted_no_cookies = False
        scene_lookup = {}
        uploaded_new_scene = False

        async def _process_single_scene(idx, sc, is_auto_retry=False):
            nonlocal aborted_no_cookies, uploaded_new_scene
            raw_num = sc.get("scene_number")
            try:
                num = int(raw_num) if raw_num is not None and str(raw_num).strip() != "" else (idx + 1)
            except (ValueError, TypeError):
                num = idx + 1

            prompt = str(sc.get("image_prompt", "")).strip()
            narration = str(sc.get("narration", "")).strip()
            filename = f"scene_{num:03d}.jpg"
            r2_key = f"projects/{slug}/{filename}"

            if not prompt:
                reason = "প্রম্পট খালি ছিল"
                failed_scenes_list.append({"scene_number": num, "reason": reason, "prompt": ""})
                _sync_job_progress(s3, "running")
                add_log(f"❌ সিন #{num:03d} বাতিল: {reason}")
                return False

            era_key, scene_chars = _resolve_scene_tags(sc, auto_bible)
            era_desc = str(eras_map.get(era_key) or "").strip() if era_key else ""

            valid_char_items = []
            for ck in scene_chars:
                if ck in ref_paths and os.path.exists(ref_paths[ck]):
                    valid_char_items.append((ck, ref_paths[ck]))
                else:
                    ck_low = ck.lower()
                    matched = next((k for k in ref_paths if k.lower() == ck_low), None)
                    if matched and os.path.exists(ref_paths[matched]):
                        valid_char_items.append((matched, ref_paths[matched]))

            valid_char_items = valid_char_items[:4]

            attach_files = None
            ref_mode = "none"
            char_labels = []
            tmp_collage_path = os.path.join(proj_refs_dir, "_tmp_collage.jpg")

            if consistency_mode != "none":
                if len(valid_char_items) == 1:
                    attach_files = [valid_char_items[0][1]]
                    ref_mode = "single"
                elif len(valid_char_items) >= 2:
                    c_path, char_labels = _build_labeled_collage(valid_char_items, tmp_collage_path)
                    attach_files = [c_path]
                    ref_mode = "collage"
                elif use_style_anchor and os.path.exists(style_anchor_local):
                    attach_files = [style_anchor_local]
                    ref_mode = "style_anchor"

            if ref_mode == "none" and not style_bible and not era_desc:
                lower_p = prompt.lower()
                if not any(lower_p.startswith(w) for w in ("generate ", "create ", "draw ", "make ", "an image", "image of")):
                    final_prompt = f"Generate an image of: {prompt}, aspect ratio {ratio}"
                else:
                    final_prompt = f"{prompt}, aspect ratio {ratio}"
            else:
                final_prompt = _build_scene_prompt(prompt, ratio, style_bible, era_desc, char_labels, ref_mode)

            t_start = time.time()
            prefix_tag = "অটো-রিট্রাই সিন" if is_auto_retry else "সিন"
            gen_status, raw_bytes, gen_info = await _call_gemini_with_pool(
                clients_map=clients_map,
                last_alert_at=last_alert_at,
                stop_event=stop_event,
                wakeup_event=wakeup_event,
                unpause_event=unpause_event,
                prompt=final_prompt,
                files=attach_files,
                expect_image=True,
                status_label=f"Rendering #{num:03d}",
                log_prefix=f"{prefix_tag} #{num:03d} তৈরি হচ্ছে" + (f" [Ref: {len(valid_char_items)}]" if valid_char_items else ""),
                temp_filename=filename,
                max_attempts=3,
            )

            if os.path.exists(tmp_collage_path):
                try:
                    os.remove(tmp_collage_path)
                except Exception:
                    pass

            if gen_status == "NO_COOKIES":
                aborted_no_cookies = True
                return False

            if gen_status == "OK" and raw_bytes:
                if use_style_anchor and not os.path.exists(style_anchor_local):
                    try:
                        with open(style_anchor_local, "wb") as sf:
                            sf.write(raw_bytes)
                        await run_cancellable(
                            asyncio.to_thread(r2_upload_bytes, s3, style_anchor_r2, raw_bytes, "image/jpeg"),
                            stop_event,
                            timeout=25,
                        )
                        add_log(f"📌 সিন #{num:03d}-কে Style Anchor হিসেবে R2-তে সেভ করা হয়েছে।")
                    except Exception:
                        pass

                processed_bytes = apply_watermark(raw_bytes, num, watermark_mode)
                await run_cancellable(
                    asyncio.to_thread(r2_upload_bytes, s3, r2_key, processed_bytes, "image/jpeg"),
                    stop_event,
                    timeout=35,
                )
                uploaded_new_scene = True
                send_telegram_photo_r2_queued(r2_key, num, narration)

                elapsed = round(time.time() - t_start, 1)
                completed_nums.add(num)
                add_log(f"✅ [{gen_info}] সিন #{num:03d} সম্পন্ন ({elapsed}s) -> R2 & Telegram কিউতে পাঠানো হয়েছে!")
                _sync_job_progress(s3, "running")
                del raw_bytes, processed_bytes
                return True
            else:
                reason = str(gen_info or "সব চেষ্টায় ব্যর্থ")
                failed_scenes_list.append({
                    "scene_number": num,
                    "reason": reason,
                    "prompt": prompt[:180],
                })
                _sync_job_progress(s3, "running")
                add_log(f"❌ সিন #{num:03d} বাতিল হয়েছে -> কারণ: {reason}")
                return False

        # ================= মূল সিন লুপ =================
        skipped_count = 0

        for idx, sc in enumerate(scenes_data):
            if stop_event.is_set() or aborted_no_cookies:
                break
            if not await wait_if_paused(stop_event, unpause_event):
                break
            if not isinstance(sc, dict):
                continue

            raw_num = sc.get("scene_number")
            try:
                num = int(raw_num) if raw_num is not None and str(raw_num).strip() != "" else (idx + 1)
            except (ValueError, TypeError):
                num = idx + 1

            scene_lookup[num] = (idx, sc)
            filename = f"scene_{num:03d}.jpg"

            update_state(
                current_scene=num,
                percent=int(((idx + 1) / max(1, total)) * 100),
            )

            if filename in existing_jpgs and (target_scene_nums is None or num not in target_scene_nums):
                skipped_count += 1
                completed_nums.add(num)
                update_state(completed_count=len(completed_nums))
                continue

            if target_scene_nums is not None and num not in target_scene_nums:
                continue

            await _process_single_scene(idx, sc, is_auto_retry=False)
            gc.collect()

            if idx < total - 1 and not stop_event.is_set() and not aborted_no_cookies:
                breather = round(random.uniform(2.5, 4.2), 1)
                update_state(status_text=f"Scene #{num:03d} Done. Next in {breather}s...")
                if not await smart_sleep(breather, stop_event, wakeup_event):
                    break
                if not await wait_if_paused(stop_event, unpause_event):
                    break

        # ================= রিট্রাই =================
        if auto_video and failed_scenes_list and not stop_event.is_set() and not aborted_no_cookies:
            retry_items = list(failed_scenes_list)
            failed_scenes_list.clear()
            add_log(f"♻️ অটো-ভিডিও চেক: ব্যর্থ হওয়া {len(retry_items)} টি সিন ১ বার অটো-রিট্রাই করা হচ্ছে...")

            for r_item in retry_items:
                if stop_event.is_set() or aborted_no_cookies:
                    failed_scenes_list.append(r_item)
                    continue
                if not await wait_if_paused(stop_event, unpause_event):
                    failed_scenes_list.append(r_item)
                    continue
                r_num = r_item["scene_number"]
                if r_num in scene_lookup:
                    r_idx, r_sc = scene_lookup[r_num]
                    await _process_single_scene(r_idx, r_sc, is_auto_retry=True)
                    gc.collect()
                else:
                    failed_scenes_list.append(r_item)

        if uploaded_new_scene and s3:
            await asyncio.to_thread(r2_invalidate_archive_zip, s3, slug)

        if voiceover_text and s3:
            try:
                await asyncio.to_thread(
                    r2_upload_bytes,
                    s3,
                    f"projects/{slug}/story.txt",
                    voiceover_text.encode("utf-8"),
                    "text/plain; charset=utf-8",
                )
            except Exception:
                pass

        was_stopped = stop_event.is_set()
        final_status = "stopped" if (was_stopped or aborted_no_cookies) else "completed"

        update_state(
            percent=100 if final_status == "completed" else int((len(completed_nums) / max(1, total)) * 100),
            status_text="Stopped" if was_stopped else ("No Active Cookies" if aborted_no_cookies else "Completed"),
            active_account="-",
            is_paused=False,
        )
        _sync_job_progress(s3, final_status)
        save_cookies_to_r2()

        if failed_scenes_list:
            failed_nums_str = ", ".join(f"#{f['scene_number']:03d}" for f in failed_scenes_list)
            add_log(f"📋 বাতিল হওয়া সিন ({len(failed_scenes_list)} টি): {failed_nums_str}", level="fail")

        if final_status == "completed":
            add_log(
                f"🎉 কাজ শেষ! সফল: {len(completed_nums)}/{total} "
                f"(আগের স্কিপ: {skipped_count}, বাতিল: {len(failed_scenes_list)})"
            )
            summary_msg = (
                f"🎉 <b>{html.escape(title)}</b> সম্পন্ন হয়েছে!\n\n"
                f"✅ সফল/মোট: {len(completed_nums)} / {total}\n"
                f"⏭️ স্কিপ (আগে ছিল): {skipped_count}\n"
                f"❌ বাতিল/ব্যর্থ: {len(failed_scenes_list)}\n"
                f"🎙️ ভয়েসওভার স্ক্রিপ্ট: <code>story.txt</code> রেডি\n"
            )
            if failed_scenes_list:
                f_nums = ", ".join(f"#{f['scene_number']:03d}" for f in failed_scenes_list[:20])
                summary_msg += f"📌 বাতিল সিন: <code>{f_nums}</code>\n"
            if APP_BASE_URL:
                summary_msg += f'\n📦 <a href="{APP_BASE_URL}/api/r2/download-zip/{slug}">১-ক্লিক ZIP ডাউনলোড করুন</a>'
            send_telegram_message(summary_msg)

            # ================= Auto-Video Trigger =================
            if auto_video:
                if failed_scenes_list:
                    add_log("🚫 অটো-ভিডিও থামানো হয়েছে: রিট্রাই করার পরও কিছু সিন ব্যর্থ থাকায় ভিডিও শুরু করা হয়নি।", level="fail")
                    send_telegram_message(
                        f"⚠️ <b>অটো-ভিডিও থামানো হয়েছে ({html.escape(title)})</b>\n"
                        f"১ বার রিট্রাই করার পরও {len(failed_scenes_list)} টি সিন ব্যর্থ রয়েছে।"
                    )
                else:
                    vid_objs = r2_list_video_objects(s3, slug)
                    has_audio = any(
                        o["name"].lower().endswith((".mp3", ".wav", ".m4a", ".aac", ".ogg"))
                        for o in vid_objs
                    )
                    if not has_audio:
                        add_log("⚠️ অটো-ভিডিও চালু করা যায়নি: প্রজেক্টে ভয়েসওভার অডিও আপলোড করা নেই।", level="warn")
                        send_telegram_message(
                            f"⚠️ <b>অটো-ভিডিও শুরু হয়নি ({html.escape(title)})</b>\n"
                            f"সব ছবি তৈরি হয়েছে, কিন্তু ভয়েসওভার অডিও আপলোড করা ছিল না।"
                        )
                    else:
                        ok_trig, trig_msg = trigger_github_video_render(slug, mode="video")
                        if ok_trig:
                            add_log("🎬 সব সিন সফল! ২য় সার্ভারে অটো-ভিডিও রেন্ডার শুরু হয়েছে!")
                            send_telegram_message(
                                f"🎬 <b>অটো-ভিডিও রেন্ডার শুরু হয়েছে!</b>\n"
                                f"প্রজেক্ট: <b>{html.escape(title)}</b>\n"
                                f"ভিডিও তৈরি হলেই টেলিগ্রামে জানানো হবে।"
                            )
                        else:
                            add_log(f"❌ অটো-ভিডিও ট্রিগার ব্যর্থ: {trig_msg}", level="fail")
                            send_telegram_message(f"❌ <b>অটো-ভিডিও ট্রিগার ব্যর্থ ({html.escape(title)}):</b> {html.escape(trig_msg)}")
        else:
            add_log(f"🛑 কাজ থামানো হয়েছে। সম্পন্ন: {len(completed_nums)}/{total}, বাতিল: {len(failed_scenes_list)}")
            send_telegram_message(
                f"🛑 <b>{html.escape(title)}</b> থামানো হয়েছে।\n"
                f"✅ সেভ আছে: {len(completed_nums)} / {total}\n"
                f"❌ বাতিল: {len(failed_scenes_list)}"
            )

    except InterruptedError:
        add_log("🛑 ইউজার নির্দেশে কাজ থামানো হয়েছে।")
        update_state(status_text="Stopped", active_account="-", is_paused=False)
        try:
            _sync_job_progress(get_r2_client(), "stopped")
        except Exception:
            pass

    except Exception as fatal_err:
        add_log(f"❌ অপ্রত্যাশিত সার্ভার ত্রুটি: {str(fatal_err)[:120]}")
        update_state(status_text="Failed", active_account="-", is_paused=False)
        try:
            _sync_job_progress(get_r2_client(), "interrupted")
        except Exception:
            pass

    finally:
        for cid, (cli, _) in list(clients_map.items()):
            try:
                await asyncio.wait_for(cli.close(), timeout=4)
            except Exception:
                pass
        clients_map.clear()

        with state_lock:
            worker_control["loop"] = None
            worker_control["stop_event"] = None
            worker_control["wakeup_event"] = None
            worker_control["unpause_event"] = None
            for c in cookie_pool:
                if c.get("status") in ("working", "connecting"):
                    c["status"] = "active" if c.get("enabled", True) else "paused"
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
    accounts_view = sanitize_accounts_for_ui()

    with state_lock:
        snapshot = {
            "is_running": state["is_running"],
            "is_paused": state["is_paused"],
            "is_testing_cookies": state["is_testing_cookies"],
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
            "accounts": accounts_view,
            "interrupted_job": None,
        }
        if not state["is_running"]:
            for h in history_cache:
                if h.get("status") == "interrupted":
                    snapshot["interrupted_job"] = {
                        "slug": h.get("slug"),
                        "title": h.get("title"),
                        "completed_count": h.get("completed_count", 0),
                        "total_scenes": h.get("total_scenes", 0),
                        "failed_count": h.get("failed_count", 0),
                        "updated_at": h.get("updated_at"),
                    }
                    break
    return jsonify(snapshot)


# ================= কুকিজ ম্যানেজমেন্ট API =================
@app.route("/api/cookies/add", methods=["POST"])
def api_add_cookie():
    bootstrap_from_r2()
    data = request.get_json(silent=True) or {}
    psid, psidts = clean_cookie_input(data.get("psid", ""), data.get("psidts", ""))
    custom_name = str(data.get("name", "")).strip()

    if not psid or len(psid) < 20:
        return jsonify({"error": "সঠিক __Secure-1PSID কুকি দিন!"}), 400

    with state_lock:
        for existing in cookie_pool:
            if existing["psid"] == psid:
                return jsonify({"error": f"এই কুকিটি আগে থেকেই '{existing['name']}' নামে অ্যাড করা আছে!"}), 400

        if custom_name and _cookie_name_exists(custom_name):
            return jsonify({"error": f"'{custom_name}' নামে আগে থেকেই একটি কুকি আছে! আলাদা নাম দিন।"}), 400

        final_name = custom_name or _next_unique_default_cookie_name()
        record = _make_cookie_record(psid=psid, psidts=psidts, name=final_name, enabled=True)
        cookie_pool.append(record)
        running_now = state["is_running"]
        testing_now = state["is_testing_cookies"]

    _clear_gemini_cache(psid)
    save_cookies_to_r2()
    _notify_worker_wakeup()

    if running_now:
        add_log(f"➕ নতুন সহযোগী কুকি অ্যাড হয়েছে: {final_name} ({record['preview']}) — সিরিয়ালে যুক্ত হয়েছে!")
    else:
        add_log(f"➕ নতুন কুকি অ্যাড হয়েছে: {final_name} ({record['preview']})")
        if not testing_now:
            threading.Thread(target=test_cookies_worker, args=(record["id"],), daemon=True).start()

    return jsonify({
        "status": "added",
        "message": f"{final_name} সফলভাবে অ্যাড হয়েছে!" + (" চলমান প্রজেক্টে পরের সিরিয়ালে কাজে নামবে।" if running_now else ""),
    })


@app.route("/api/cookies/edit/<cookie_id>", methods=["POST"])
def api_edit_cookie(cookie_id):
    bootstrap_from_r2()
    data = request.get_json(silent=True) or {}
    new_name = str(data.get("name", "")).strip()
    raw_psid = str(data.get("psid", "")).strip()
    raw_psidts = str(data.get("psidts", "")).strip()
    clear_psidts = bool(data.get("clear_psidts", False))

    if not new_name:
        return jsonify({"error": "কুকির নাম খালি রাখা যাবে না!"}), 400

    old_psid = None
    new_psid_clean = None

    with state_lock:
        target = next((c for c in cookie_pool if c["id"] == cookie_id), None)
        if not target:
            return jsonify({"error": "Cookie not found"}), 404

        if _cookie_name_exists(new_name, exclude_id=cookie_id):
            return jsonify({"error": f"'{new_name}' নামে আগে থেকেই একটি কুকি আছে! আলাদা নাম দিন।"}), 400

        old_name = target["name"]
        old_psid = target["psid"]
        target["name"] = new_name

        if raw_psid:
            cleaned_psid, cleaned_psidts = clean_cookie_input(raw_psid, raw_psidts)
            if len(cleaned_psid) < 20:
                return jsonify({"error": "নতুন __Secure-1PSID কুকিটি সঠিক নয়!"}), 400
            for other in cookie_pool:
                if other["id"] != cookie_id and other["psid"] == cleaned_psid:
                    return jsonify({"error": f"এই কুকিটি আগে থেকেই '{other['name']}' নামে আছে!"}), 400
            target["psid"] = cleaned_psid
            target["preview"] = mask_cookie(cleaned_psid)
            if cleaned_psidts:
                target["psidts"] = cleaned_psidts
            elif clear_psidts:
                target["psidts"] = None
            target["status"] = "standby" if target.get("enabled", True) else "paused"
            target["consecutive_fails"] = 0
            target["cooldown_level"] = 0
            target["cooldown_until"] = 0.0
            target["cooldown_probe"] = False
            target["last_error"] = ""
            target["version"] = target.get("version", 1) + 1
            new_psid_clean = cleaned_psid
        else:
            if clear_psidts:
                target["psidts"] = None
                target["version"] = target.get("version", 1) + 1
            elif raw_psidts:
                _, cleaned_psidts = clean_cookie_input("dummy", raw_psidts)
                target["psidts"] = cleaned_psidts
                target["version"] = target.get("version", 1) + 1

    if new_psid_clean:
        _clear_gemini_cache(old_psid)
        _clear_gemini_cache(new_psid_clean)

    save_cookies_to_r2()
    _notify_worker_wakeup()
    add_log(f"✏️ কুকি আপডেট হয়েছে: {old_name} → {new_name}")
    return jsonify({"status": "updated", "message": f"{new_name} আপডেট হয়েছে!"})


@app.route("/api/cookies/delete/<cookie_id>", methods=["POST"])
def api_delete_cookie(cookie_id):
    bootstrap_from_r2()
    removed_name = None
    removed_psid = None
    with state_lock:
        for i, c in enumerate(cookie_pool):
            if c["id"] == cookie_id:
                removed_name = c["name"]
                removed_psid = c["psid"]
                cookie_pool.pop(i)
                break
    if not removed_name:
        return jsonify({"error": "Cookie not found"}), 404

    _clear_gemini_cache(removed_psid)
    save_cookies_to_r2()
    add_log(f"🗑️ কুকি ডিলিট করা হয়েছে: {removed_name}")
    return jsonify({"status": "deleted"})


@app.route("/api/cookies/toggle/<cookie_id>", methods=["POST"])
def api_toggle_cookie(cookie_id):
    bootstrap_from_r2()
    new_enabled = None
    cname = ""
    with state_lock:
        for c in cookie_pool:
            if c["id"] == cookie_id:
                new_enabled = not c.get("enabled", True)
                c["enabled"] = new_enabled
                c["status"] = "standby" if new_enabled else "paused"
                cname = c["name"]
                break
    if new_enabled is None:
        return jsonify({"error": "Cookie not found"}), 404

    save_cookies_to_r2()
    if new_enabled:
        _notify_worker_wakeup()
        add_log(f"▶️ {cname} আবার সক্রিয় করা হয়েছে।")
    else:
        add_log(f"⏸️ {cname} সাময়িক Pause করা হয়েছে।")
    return jsonify({"status": "updated", "enabled": new_enabled})


@app.route("/api/cookies/reset/<cookie_id>", methods=["POST"])
def api_reset_cookie(cookie_id):
    bootstrap_from_r2()
    cname = None
    psid = None
    with state_lock:
        for c in cookie_pool:
            if c["id"] == cookie_id:
                c["cooldown_until"] = 0.0
                c["cooldown_level"] = 0
                c["consecutive_fails"] = 0
                c["cooldown_probe"] = False
                c["last_error"] = ""
                c["status"] = "standby" if c.get("enabled", True) else "paused"
                cname = c["name"]
                psid = c["psid"]
                break
    if not cname:
        return jsonify({"error": "Cookie not found"}), 404

    _clear_gemini_cache(psid)
    save_cookies_to_r2()
    _notify_worker_wakeup()
    add_log(f"🔄 {cname}-এর কুলডাউন/এরর রিসেট করা হয়েছে।")
    return jsonify({"status": "reset"})


@app.route("/api/cookies/test/<cookie_id>", methods=["POST"])
def api_test_single_cookie(cookie_id):
    bootstrap_from_r2()
    with state_lock:
        if state["is_running"]:
            return jsonify({"error": "কাজ চলাকালীন আলাদা টেস্ট করা যাবে না।"}), 400
        if state["is_testing_cookies"]:
            return jsonify({"error": "কুকি টেস্ট ইতিমধ্যেই চলছে..."}), 400
        exists = any(c["id"] == cookie_id for c in cookie_pool)

    if not exists:
        return jsonify({"error": "Cookie not found"}), 404

    threading.Thread(target=test_cookies_worker, args=(cookie_id,), daemon=True).start()
    return jsonify({"status": "testing"})


@app.route("/api/test-cookies", methods=["POST"])
def api_test_cookies():
    bootstrap_from_r2()
    with state_lock:
        if state["is_running"]:
            return jsonify({"error": "কাজ চলাকালীন কুকি টেস্ট করা যাবে না।"}), 400
        if state["is_testing_cookies"]:
            return jsonify({"error": "কুকি টেস্ট ইতিমধ্যেই চলছে..."}), 400

    threading.Thread(target=test_cookies_worker, daemon=True).start()
    return jsonify({"status": "testing"})


# ================= স্টার্ট / পজ / রিজিউম / স্টপ API =================
@app.route("/api/start", methods=["POST"])
def start_pipeline():
    bootstrap_from_r2()
    with state_lock:
        if state["is_running"]:
            return jsonify({"error": "একটি কাজ ইতিমধ্যেই চলছে!"}), 400
        if state["is_testing_cookies"]:
            return jsonify({"error": "কুকি টেস্ট শেষ হওয়া পর্যন্ত একটু অপেক্ষা করুন।"}), 400
        if not any(c.get("enabled", True) for c in cookie_pool):
            return jsonify({"error": "কোনো সক্রিয় কুকি নেই! Cookies ট্যাব থেকে কুকি অ্যাড বা Resume করুন।"}), 400
        state["should_stop"] = False
        state["is_paused"] = False

    payload = request.get_json(silent=True)
    if not isinstance(payload, dict):
        return jsonify({"error": "Invalid JSON request body."}), 400

    raw_json = payload.get("json_content", "")
    ratio = str(payload.get("aspect_ratio", "16:9"))
    watermark_mode = payload.get("watermark", "hash")
    consistency_mode = str(payload.get("consistency_mode", "auto")).strip().lower()
    auto_video = bool(payload.get("auto_video", False))

    try:
        parsed = json.loads(raw_json) if isinstance(raw_json, str) else raw_json
    except Exception as e:
        return jsonify({"error": f"Invalid JSON syntax: {str(e)}"}), 400

    if not isinstance(parsed, dict):
        return jsonify({"error": "JSON অবশ্যই একটি অবজেক্ট {...} হতে হবে।"}), 400

    scenes = parsed.get("scenes")
    if not isinstance(scenes, list) or len(scenes) == 0:
        return jsonify({"error": "JSON-এ ভ্যালিড 'scenes' লিস্ট পাওয়া যায়নি।"}), 400

    title = str(parsed.get("project_title") or "Untitled Story").strip()
    story_cfg = {
        "consistency_mode": consistency_mode,
        "auto_video": auto_video,
        "style_bible": str(parsed.get("style_bible") or "").strip(),
        "eras": parsed.get("eras") if isinstance(parsed.get("eras"), dict) else {},
        "characters": parsed.get("characters") if isinstance(parsed.get("characters"), dict) else {},
    }

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
        if not state["is_paused"]:
            state["is_paused"] = True
            state["status_text"] = "Pausing after current step..."
    _notify_worker_wakeup()
    add_log("⏸️ ইউজার নির্দেশে কাজ Pause করা হয়েছে।")
    return jsonify({"status": "paused"})


@app.route("/api/resume", methods=["POST"])
def resume_pipeline():
    with state_lock:
        if not state["is_running"]:
            return jsonify({"error": "কোনো কাজ চলছে না।"}), 400
        if state["is_paused"]:
            state["is_paused"] = False
            state["status_text"] = "Resuming..."
    _notify_worker_unpause()
    add_log("▶️ কাজ আবার Resume করা হয়েছে।")
    return jsonify({"status": "resumed"})


@app.route("/api/stop", methods=["POST"])
def stop_pipeline():
    with state_lock:
        if state["is_running"]:
            state["should_stop"] = True
            state["is_paused"] = False
            state["status_text"] = "Stopping..."
            loop = worker_control.get("loop")
            ev = worker_control.get("stop_event")
            if loop and ev and not loop.is_closed():
                try:
                    loop.call_soon_threadsafe(ev.set)
                except Exception:
                    pass
            return jsonify({"status": "stopping"})
    return jsonify({"status": "idle"})


# ================= হিস্ট্রি API =================
@app.route("/api/history", methods=["GET"])
def api_get_history():
    bootstrap_from_r2()
    with state_lock:
        items = list(history_cache)
    return jsonify({"history": items})


@app.route("/api/history/resume/<slug>", methods=["POST"])
def api_resume_history(slug):
    bootstrap_from_r2()
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400

    with state_lock:
        if state["is_running"]:
            return jsonify({"error": "আরেকটি কাজ ইতিমধ্যেই চলছে!"}), 400
        if state["is_testing_cookies"]:
            return jsonify({"error": "কুকি টেস্ট শেষ হওয়া পর্যন্ত অপেক্ষা করুন।"}), 400
        if not any(c.get("enabled", True) for c in cookie_pool):
            return jsonify({"error": "কোনো সক্রিয় কুকি নেই! আগে Cookies ট্যাবে কুকি দিন।"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "Cloudflare R2 কনফিগার করা নেই।"}), 500

    input_doc = r2_read_json(s3, f"projects/{slug}/input_scenes.json")
    if not input_doc or not isinstance(input_doc.get("scenes"), list):
        return jsonify({"error": "এই প্রজেক্টের ইনপুট সিন ডেটা R2-তে পাওয়া যায়নি।"}), 404

    payload = request.get_json(silent=True) or {}
    mode = payload.get("mode", "remaining")

    target_nums = None
    if mode == "failed_only":
        job_doc = r2_read_json(s3, f"projects/{slug}/job_state.json") or {}
        failed_list = job_doc.get("failed_scenes", [])
        target_nums = {int(f["scene_number"]) for f in failed_list if "scene_number" in f}
        if not target_nums:
            return jsonify({"error": "রিজিউম করার মতো কোনো বাতিল হওয়া সিন নেই!"}), 400

    with state_lock:
        state["should_stop"] = False
        state["is_paused"] = False

    title = input_doc.get("project_title") or slug
    ratio = input_doc.get("aspect_ratio") or "16:9"
    wm = input_doc.get("watermark", "hash")
    scenes = input_doc["scenes"]
    story_cfg = {
        "consistency_mode": input_doc.get("consistency_mode", "auto"),
        "auto_video": bool(input_doc.get("auto_video", False)),
        "style_bible": input_doc.get("style_bible", ""),
        "eras": input_doc.get("eras", {}),
        "characters": input_doc.get("characters", {}),
    }

    threading.Thread(
        target=generation_worker,
        args=(scenes, title, ratio, wm, target_nums, story_cfg),
        daemon=True,
    ).start()

    return jsonify({"status": "resumed", "mode": mode})


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


# ================= Phase-2: ভিডিও রেন্ডার ও ডাইরেক্ট R2 Presigned API =================
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
        return jsonify({"error": "Invalid project slug"}), 400
    if kind not in ("audio", "srt", "font"):
        return jsonify({"error": "Invalid upload kind"}), 400

    ext = os.path.splitext(filename)[1].lower()
    valid_exts = {
        "audio": {".mp3", ".wav", ".m4a", ".aac", ".ogg"},
        "srt": {".srt"},
        "font": {".ttf", ".otf"},
    }
    if ext not in valid_exts[kind]:
        return jsonify({"error": f"ভুল ফাইল ফরম্যাট ({ext})!"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 কনফিগার করা নেই।"}), 500

    existing = r2_list_video_objects(s3, slug)
    for item in existing:
        if os.path.splitext(item["name"])[1].lower() in valid_exts[kind]:
            try:
                s3.delete_object(Bucket=R2_BUCKET_NAME, Key=item["key"])
            except Exception:
                pass

    target_name = f"audio{ext}" if kind == "audio" else ("subtitles.srt" if kind == "srt" else f"font{ext}")
    r2_key = f"projects/{slug}/_video/{target_name}"

    try:
        upload_url = s3.generate_presigned_url(
            "put_object",
            Params={
                "Bucket": R2_BUCKET_NAME,
                "Key": r2_key,
                "ContentType": content_type,
            },
            ExpiresIn=3600,
        )
        return jsonify({"upload_url": upload_url, "key": r2_key, "content_type": content_type})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/video/project/<slug>", methods=["GET"])
def api_video_project_detail(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
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
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    data = request.get_json(silent=True) or {}
    cfg = {
        "auto_video": bool(data.get("auto_video", False)),
        "quality": str(data.get("quality") or "1080p"),
        "aspect_ratio": str(data.get("aspect_ratio") or ""),
        "motion_mode": str(data.get("motion_mode") or "auto"),
        "transition_type": str(data.get("transition_type") or "crossfade"),
        "transition_duration": float(data.get("transition_duration") if data.get("transition_duration") is not None else 0.45),
        "subtitle_enabled": bool(data.get("subtitle_enabled", True)),
        "font_size": int(data.get("font_size") or 50),
        "font_bold": bool(data.get("font_bold", False)),
        "text_color": str(data.get("text_color") or "#FFFFFF"),
        "plate_enabled": bool(data.get("plate_enabled", True)),
        "plate_mode": str(data.get("plate_mode") or "box"),
        "plate_color": str(data.get("plate_color") or "#000000"),
        "plate_opacity": float(data.get("plate_opacity") if data.get("plate_opacity") is not None else 0.70),
        "plate_padding": int(data.get("plate_padding") if data.get("plate_padding") is not None else 16),
        "position": str(data.get("position") or "bottom"),
        "margin_v": int(data.get("margin_v") if data.get("margin_v") is not None else 60),
        "updated_at": now_utc_iso(),
    }
    if r2_write_json(s3, f"projects/{slug}/_video/video_config.json", cfg):
        return jsonify({"status": "saved", "config": cfg})
    return jsonify({"error": "Config সেভ করা যায়নি"}), 500


@app.route("/api/video/trigger/<slug>", methods=["POST"])
def api_video_trigger(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    input_doc = r2_read_json(s3, f"projects/{slug}/input_scenes.json")
    if not input_doc or not isinstance(input_doc.get("scenes"), list):
        return jsonify({"error": "এই প্রজেক্টের সিন বা ছবি এখনো তৈরি হয়নি!"}), 400

    vid_objs = r2_list_video_objects(s3, slug)
    has_audio = any(o["name"].lower().endswith((".mp3", ".wav", ".m4a", ".aac", ".ogg")) for o in vid_objs)
    if not has_audio:
        return jsonify({"error": "আগে ভয়েসওভার অডিও (.mp3/.wav) আপলোড করুন!"}), 400

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

                if len(parts) == 3:
                    fname = parts[2]
                    if fname.lower().endswith((".jpg", ".jpeg", ".png", ".webp")):
                        p["image_count"] += 1
                    elif fname == "meta.json":
                        p["has_meta"] = True
                elif len(parts) == 4 and parts[2] == "_video":
                    vname = parts[3].lower()
                    if vname.endswith((".mp3", ".wav", ".m4a", ".aac", ".ogg")):
                        p["has_audio"] = True
                    elif vname.endswith(".srt"):
                        p["has_srt"] = True
                    elif vname.endswith((".ttf", ".otf")):
                        p["has_font"] = True
                    elif vname == "final_video.mp4":
                        p["has_video"] = True
                        p["video_size"] = obj.get("Size", 0)
                    elif vname == "video_status.json":
                        p["has_video_status"] = True

        result = []
        for slug, p in projects.items():
            if p["has_meta"]:
                meta = r2_read_json(s3, f"projects/{slug}/meta.json")
                if isinstance(meta, dict) and meta.get("title"):
                    p["title"] = meta["title"]
            if p["has_video_status"]:
                st = r2_read_json(s3, f"projects/{slug}/_video/video_status.json") or {}
                p["video_status"] = st
            else:
                p["video_status"] = {
                    "status": "completed" if p["has_video"] else "not_started",
                    "percent": 100 if p["has_video"] else 0,
                    "message": "ভিডিও তৈরি সম্পন্ন" if p["has_video"] else "এখনো ভিডিও তৈরি করা হয়নি",
                }
            result.append(p)

        result.sort(key=lambda x: x["last_modified"], reverse=True)
        return jsonify({"videos": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/video/presign-download/<slug>", methods=["GET"])
def api_video_presign_download(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    mode = request.args.get("mode", "download")
    key = f"projects/{slug}/_video/final_video.mp4"
    params = {
        "Bucket": R2_BUCKET_NAME,
        "Key": key,
    }
    if mode != "play":
        params["ResponseContentDisposition"] = f'attachment; filename="{slug}.mp4"'

    try:
        url = s3.generate_presigned_url("get_object", Params=params, ExpiresIn=PRESIGN_TTL_LONG)
        return jsonify({"url": url})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/video/delete/<slug>", methods=["POST"])
def api_video_delete(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    try:
        s3.delete_object(Bucket=R2_BUCKET_NAME, Key=f"projects/{slug}/_video/final_video.mp4")
        r2_write_json(
            s3,
            f"projects/{slug}/_video/video_status.json",
            {
                "slug": slug,
                "status": "not_started",
                "percent": 0,
                "message": "পুরোনো ভিডিও ডিলিট করা হয়েছে",
                "updated_at": now_utc_iso(),
            },
        )
        return jsonify({"status": "deleted"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


# ================= Cloudflare R2 স্টোরেজ API =================
@app.route("/api/r2/projects", methods=["GET"])
def r2_list_projects():
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "Cloudflare R2 কনফিগার করা নেই।"}), 500

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
                    projects[slug] = {
                        "slug": slug,
                        "title": slug,
                        "image_count": 0,
                        "total_bytes": 0,
                        "last_modified": "",
                        "has_meta": False,
                    }
                p = projects[slug]
                p["total_bytes"] += obj.get("Size", 0)
                lm = obj["LastModified"].strftime("%Y-%m-%d %H:%M")
                if lm > p["last_modified"]:
                    p["last_modified"] = lm
                if len(parts) == 3:
                    if filename.lower().endswith((".jpg", ".jpeg", ".png", ".webp")):
                        p["image_count"] += 1
                    elif filename == "meta.json":
                        p["has_meta"] = True

        for slug, p in projects.items():
            if p["has_meta"]:
                meta = r2_read_json(s3, f"projects/{slug}/meta.json")
                if isinstance(meta, dict) and meta.get("title"):
                    p["title"] = meta["title"]

        result = sorted(projects.values(), key=lambda x: x["last_modified"], reverse=True)
        return jsonify({"projects": result})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/r2/project/<slug>/files", methods=["GET"])
def r2_list_project_files(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
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
    if not key or not key.startswith("projects/") or ".." in key:
        return jsonify({"error": "Invalid key"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    filename = key.split("/")[-1]
    params = {
        "Bucket": R2_BUCKET_NAME,
        "Key": key,
    }
    if download:
        params["ResponseContentDisposition"] = f'attachment; filename="{filename}"'

    try:
        url = s3.generate_presigned_url("get_object", Params=params, ExpiresIn=PRESIGN_TTL_LONG)
        return redirect(url, code=302)
    except Exception as e:
        return jsonify({"error": str(e)}), 404


def _build_zip_download_url(s3, slug):
    archive_key = f"projects/{slug}/_archive/{slug}.zip"
    return s3.generate_presigned_url(
        "get_object",
        Params={
            "Bucket": R2_BUCKET_NAME,
            "Key": archive_key,
            "ResponseContentDisposition": f'attachment; filename="{slug}.zip"',
        },
        ExpiresIn=PRESIGN_TTL_LONG,
    )


@app.route("/api/r2/zip-status/<slug>", methods=["GET"])
def r2_zip_status(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400
    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    archive_key = f"projects/{slug}/_archive/{slug}.zip"
    head = r2_head_object(s3, archive_key)
    if head:
        return jsonify({
            "slug": slug,
            "status": "completed",
            "percent": 100,
            "size_bytes": head.get("ContentLength", 0),
            "download_url": _build_zip_download_url(s3, slug),
            "message": "ZIP তৈরি সম্পন্ন! ডাউনলোড শুরু হচ্ছে...",
        })

    st = r2_read_json(s3, f"projects/{slug}/_archive/zip_status.json", default=None) or {
        "slug": slug,
        "status": "not_started",
        "percent": 0,
        "message": "ZIP তৈরি হয়নি",
    }
    return jsonify(st)


@app.route("/api/r2/download-zip/<slug>", methods=["GET"])
def r2_stream_zip(slug):
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    archive_key = f"projects/{slug}/_archive/{slug}.zip"
    head = r2_head_object(s3, archive_key)
    if head:
        return redirect(_build_zip_download_url(s3, slug), code=302)

    if GITHUB_PAT:
        st = r2_read_json(s3, f"projects/{slug}/_archive/zip_status.json", default={}) or {}
        curr_status = str(st.get("status") or "").lower()
        updated_str = str(st.get("updated_at") or "")
        is_recent_active = False
        if curr_status in ("queued", "downloading", "zipping", "uploading") and updated_str:
            try:
                upd_dt = datetime.fromisoformat(updated_str.replace("Z", "+00:00"))
                if (datetime.now(timezone.utc) - upd_dt).total_seconds() < 1200:
                    is_recent_active = True
            except Exception:
                pass

        if not is_recent_active:
            ok, msg = trigger_github_video_render(slug, mode="zip")
            if not ok:
                return Response(
                    f"<html><body style='font-family:sans-serif;background:#0f172a;color:#f8fafc;padding:40px;text-align:center'>"
                    f"<h2>ZIP তৈরি শুরু করা যায়নি</h2><p>{html.escape(msg)}</p>"
                    f"<p style='color:#94a3b8'>নিশ্চিত করুন ২য় সার্ভারের <code>.github/workflows/render.yml</code> আপডেট করা আছে।</p>"
                    f"</body></html>",
                    status=500,
                    mimetype="text/html; charset=utf-8",
                )

        safe_slug = html.escape(slug)
        wait_html = f"""<!doctype html>
<html lang="bn">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>ZIP প্রস্তুত হচ্ছে — {safe_slug}</title>
<style>
  body{{margin:0;min-height:100vh;display:flex;align-items:center;justify-content:center;background:#0b1120;color:#e2e8f0;font-family:system-ui,sans-serif;padding:20px}}
  .card{{max-width:460px;width:100%;background:#111827;border:1px solid #1e293b;border-radius:16px;padding:28px;text-align:center;box-shadow:0 20px 50px rgba(0,0,0,.4)}}
  .bar-bg{{height:10px;background:#1e293b;border-radius:99px;overflow:hidden;margin:18px 0}}
  .bar{{height:100%;width:10%;background:linear-gradient(90deg,#38bdf8,#6366f1);transition:width .4s ease}}
  .muted{{color:#94a3b8;font-size:14px}}
  .btn{{display:none;margin-top:16px;padding:12px 20px;background:#2563eb;color:#fff;text-decoration:none;border-radius:10px;font-weight:600}}
</style>
</head>
<body>
  <div class="card">
    <h2>📦 Cloudflare R2-তে ZIP তৈরি হচ্ছে</h2>
    <p class="muted">Render-এর ব্যান্ডউইথ বাঁচাতে ২য় সার্ভার সরাসরি R2-তে ZIP বানাচ্ছে। তৈরি হলেই অটোমেটিক ডাউনলোড শুরু হবে।</p>
    <div class="bar-bg"><div class="bar" id="bar"></div></div>
    <div id="msg" class="muted">অপেক্ষা করুন...</div>
    <a id="dl" class="btn" href="#">ডাউনলোড শুরু না হলে এখানে ক্লিক করুন</a>
  </div>
<script>
const slug = {json.dumps(slug)};
async function poll() {{
  try {{
    const r = await fetch(`/api/r2/zip-status/${{encodeURIComponent(slug)}}`);
    const d = await r.json();
    if (d.percent !== undefined) document.getElementById('bar').style.width = Math.max(8, d.percent) + '%';
    if (d.message) document.getElementById('msg').textContent = `${{d.percent || 0}}% — ${{d.message}}`;
    if (d.status === 'completed' && d.download_url) {{
      const a = document.getElementById('dl');
      a.href = d.download_url;
      a.style.display = 'inline-block';
      window.location.href = d.download_url;
      return;
    }}
    if (d.status === 'failed') {{
      document.getElementById('msg').style.color = '#f87171';
      return;
    }}
  }} catch (e) {{}}
  setTimeout(poll, 3500);
}}
poll();
</script>
</body>
</html>"""
        return Response(wait_html, mimetype="text/html; charset=utf-8")

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
        return jsonify({"error": "No files found in this project"}), 404

    objects_to_zip.sort(key=lambda x: x[0])

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


@app.route("/api/r2/delete-file", methods=["POST"])
def r2_delete_file():
    data = request.get_json(silent=True) or {}
    key = str(data.get("key", "")).strip()
    if not key or not key.startswith("projects/") or ".." in key:
        return jsonify({"error": "Invalid key"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    try:
        s3.delete_object(Bucket=R2_BUCKET_NAME, Key=key)
        parts = key.split("/")
        if len(parts) >= 3 and parts[1]:
            r2_invalidate_archive_zip(s3, parts[1])
        return jsonify({"status": "deleted"})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route("/api/r2/delete-project", methods=["POST"])
def r2_delete_project():
    data = request.get_json(silent=True) or {}
    slug = str(data.get("slug", "")).strip()
    if not re.match(r"^[a-zA-Z0-9_-]+$", slug):
        return jsonify({"error": "Invalid project slug"}), 400

    s3 = get_r2_client()
    if not s3:
        return jsonify({"error": "R2 not configured"}), 500

    try:
        paginator = s3.get_paginator("list_objects_v2")
        deleted_count = 0
        for page in paginator.paginate(Bucket=R2_BUCKET_NAME, Prefix=f"projects/{slug}/"):
            keys = [{"Key": obj["Key"]} for obj in page.get("Contents", [])]
            if keys:
                s3.delete_objects(Bucket=R2_BUCKET_NAME, Delete={"Objects": keys})
                deleted_count += len(keys)
        return jsonify({"status": "deleted", "count": deleted_count})
    except Exception as e:
        return jsonify({"error": str(e)}), 500


if __name__ == "__main__":
    bootstrap_from_r2()
    port = int(os.environ.get("PORT", 5000))
    app.run(host="0.0.0.0", port=port)
