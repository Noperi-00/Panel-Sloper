import re
import asyncio
import hashlib
import hmac
import ipaddress
import json
import logging
import os
import shutil
import psutil
import secrets
import socket
import sys
import time
import string
from collections import defaultdict, deque
from datetime import datetime, timedelta
from pathlib import Path
from urllib.parse import quote, urlsplit
from zoneinfo import ZoneInfo

import aiofiles
import httpx
import uvicorn
from fastapi import (
    Depends,
    FastAPI,
    HTTPException,
    Request,
)
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import HTMLResponse, JSONResponse, RedirectResponse, Response

# When launched as `python main.py`, relay modules import `main`; alias the running module first.
if __name__ == "__main__":
    sys.modules.setdefault("main", sys.modules[__name__])

logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
APP_NAME = "VPN Panel"
APP_VERSION = "2.0.0"
logger = logging.getLogger("VPNPanel")

IRAN_TZ = ZoneInfo("Asia/Tehran")

app = FastAPI(title=f"{APP_NAME} v{APP_VERSION}", docs_url=None, redoc_url=None)

# ── Persistence ───────────────────────────────────────────────────────────────
def _resolve_data_dir() -> Path:
    """اولویت ۱: متغیر Railway volume. ۲: /data اگه قابل نوشتن باشه (volume سوار).
    ۳: مسیر کنار برنامه. با این ترتیب volume حتی بدون env var هم شناسایی می‌شود."""
    env_path = os.environ.get("RAILWAY_VOLUME_MOUNT_PATH") or os.environ.get("DATA_DIR")
    if env_path:
        return Path(env_path)
    for cand in ("/data", Path(os.path.dirname(os.path.abspath(__file__))) / "data"):
        try:
            p = Path(cand); p.mkdir(parents=True, exist_ok=True)
            (p / ".wprobe").write_text("1", encoding="utf-8"); (p / ".wprobe").unlink(missing_ok=True)
            return p
        except Exception:
            continue
    return Path(os.path.dirname(os.path.abspath(__file__))) / "data"

DATA_DIR = _resolve_data_dir()
DATA_FILE = DATA_DIR / "panel_state.json"
SECRET_FILE = DATA_DIR / "panel_secret.key"
HOST_FILE = DATA_DIR / "host.txt"    # persisted detected public host (survives restarts)
SAVE_LOCK = asyncio.Lock()

def _load_or_create_secret() -> str:
    """SECRET_KEY را روی دیسک ذخیره و ثابت نگه می‌دارد.
    قبلاً وقتی متغیر محیطی SECRET_KEY تنظیم نشده بود، با هر ری‌استارت سرویس
    (که روی Railway هر چند ساعت یک‌بار اتفاق می‌افتد) یک مقدار تصادفی جدید
    ساخته می‌شد. چون هش پسورد بر پایه‌ی همین secret ساخته می‌شود، تغییر آن
    باعث می‌شد پسورد درست هم دیگر قبول نشود. حالا secret یک‌بار ساخته و در
    فایل ذخیره می‌شود و در ری‌استارت‌های بعدی همان مقدار خوانده می‌شود."""
    env_secret = os.environ.get("SECRET_KEY")
    if env_secret:
        return env_secret
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        secret_path = SECRET_FILE
        if secret_path.exists():
            existing = secret_path.read_text(encoding="utf-8").strip()
            if existing:
                return existing
        new_secret = secrets.token_urlsafe(32)
        SECRET_FILE.write_text(new_secret, encoding="utf-8")
        return new_secret
    except Exception as e:
        logger.warning(f"Could not persist SECRET_KEY, sessions/password may reset on restart: {e}")
        return secrets.token_urlsafe(32)

def _load_or_init_host() -> str:
    """Public host the panel is served on. Railway injects RAILWAY_PUBLIC_DOMAIN;
    when that is missing (e.g. custom domain or unknown region), we persist the
    first real Host we see to host.txt inside the persistent volume so config
    links keep the right URL across restarts and redeployments."""
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        if HOST_FILE.exists():
            existing = HOST_FILE.read_text(encoding="utf-8").strip().lower()
            if existing:
                return existing
    except Exception as e:
        logger.warning(f"Could not read persisted host: {e}")
    return "localhost"

def persist_host(host: str):
    """Remember the public host so links stay valid across restarts/deployments."""
    host = (host or "").strip().lower()
    if not host or host in {"localhost", "127.0.0.1", "[::1]"}:
        return
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        if HOST_FILE.exists() and HOST_FILE.read_text(encoding="utf-8").strip().lower() == host:
            return
        HOST_FILE.write_text(host, encoding="utf-8")
        CONFIG["host"] = host
        logger.info(f"Public host persisted: {host}")
    except Exception as e:
        logger.warning(f"Could not persist host: {e}")

CONFIG = {
    "port": int(os.environ.get("PORT", 8000)),
    "secret": _load_or_create_secret(),
    "host": os.environ.get("RAILWAY_PUBLIC_DOMAIN") or _load_or_init_host()}

TRUST_PROXY_HEADERS = os.environ.get("TRUST_PROXY_HEADERS", "false").lower() in {"1", "true", "yes"}
ALLOWED_PUBLIC_HOSTS = {x.strip().split(":", 1)[0].lower() for x in os.environ.get("ALLOWED_PUBLIC_HOSTS", "").split(",") if x.strip()}

# ── Trusted reverse-proxy allowlist (IP spoofing defense) ────────────────────
# Client-supplied X-Forwarded-For / X-Real-IP are only honoured when the TCP peer
# that opened the connection is a proxy we explicitly trust. Empty = trust nobody,
# so the socket peer address is always the authoritative client IP.
TRUSTED_PROXIES: set[str] = {
    x.strip().lower() for x in os.environ.get("TRUSTED_PROXIES", "").split(",") if x.strip()
}

def _peer_host(client) -> str:
    """Socket peer address of the actual TCP connection (never spoofable)."""
    try:
        return (client.host if client else "") or ""
    except Exception:
        return ""

def _trusted_peer(peer: str) -> bool:
    """True only when the TCP peer is in the trusted-proxy allowlist."""
    if not peer or not TRUSTED_PROXIES:
        return False
    return peer.lower() in TRUSTED_PROXIES

def _extract_forwarded(headers) -> str:
    """Read the left-most client address from proxy headers; '' when absent/invalid."""
    fwd = (headers.get("x-forwarded-for") or "").strip()
    if fwd:
        # left-most entry is the original client; the rest are successive proxies
        candidate = fwd.split(",", 1)[0].strip()
    else:
        candidate = (headers.get("x-real-ip") or "").strip()
    if not candidate:
        return ""
    # reject obvious garbage: must parse as an IP or a valid hostname label
    if len(candidate) > 64 or " " in candidate:
        return ""
    return candidate

def resolve_client_ip(request) -> str:
    """Authoritative client IP. Proxy headers are trusted only from a trusted peer.

    Accepts a FastAPI `Request` or a Starlette `WebSocket` — both expose `.client`
    and `.headers`. Behind Railway the TCP peer is Railway's own proxy; set
    TRUSTED_PROXIES to that egress address to make forwarded headers meaningful.
    Without it, the socket peer is used, which cannot be spoofed by the client."""
    peer = _peer_host(request.client)
    if TRUST_PROXY_HEADERS or _trusted_peer(peer):
        forwarded = _extract_forwarded(request.headers)
        if forwarded:
            return forwarded
    return peer or "نامشخص"

_cors_origins = [x.strip() for x in os.environ.get("CORS_ORIGINS", "").split(",") if x.strip()]
app.add_middleware(
    CORSMiddleware,
    allow_origins=_cors_origins,
    allow_credentials=True,
    allow_methods=["GET", "POST", "PATCH", "DELETE", "OPTIONS"],
    allow_headers=["Content-Type", "X-Requested-With"],
)

async def load_state():
    global LINKS, AUTH, SUBS, CATEGORIES
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        state_path = DATA_FILE
        if state_path.exists():
            async with aiofiles.open(state_path, "r", encoding="utf-8") as f:
                raw = await f.read()
            data = json.loads(raw)
            loaded_links = data.get("links", {})
            loaded_subs = data.get("subs", {})
            # Migrate the removed stream-one alias to the supported stream-up route.
            for item in loaded_links.values():
                if item.get("protocol") == "xhttp-stream-one":
                    item["protocol"] = "xhttp-stream-up"
            LINKS.update(loaded_links)
            SUBS.update(loaded_subs)
            loaded_cats = data.get("categories", {})
            CATEGORIES.update(loaded_cats)
            if "password_hash" in data and os.environ.get("ADMIN_PASSWORD_RESET", "") != "1":
                AUTH["password_hash"] = data["password_hash"]
            if data.get("username") and os.environ.get("ADMIN_PASSWORD_RESET", "") != "1":
                AUTH["username"] = str(data["username"]).strip()
            logger.info(f"State loaded: {len(LINKS)} links, {len(SUBS)} subs")
    except Exception as e:
        logger.warning(f"Could not load state: {e}")
    # مسیر پایدار جایگزین volume: اگه state محلی نبود، از GitHub branch بخوان.
    if not LINKS and not SUBS:
        try:
            pulled = asyncio.get_event_loop_policy().new_event_loop().run_until_complete(_gh_persist_pull())
        except Exception:
            pulled = None
        if pulled:
            try:
                data = json.loads(pulled)
                for item in data.get("links", {}).values():
                    if item.get("protocol") == "xhttp-stream-one":
                        item["protocol"] = "xhttp-stream-up"
                LINKS.update(data.get("links", {}))
                SUBS.update(data.get("subs", {}))
                CATEGORIES.update(data.get("categories", {}))
                logger.info(f"restored state from GitHub: {len(LINKS)} links / {len(SUBS)} subs")
            except Exception as e:
                logger.warning(f"could not apply GitHub state: {e}")

GH_PERSIST_TOKEN = os.environ.get("GH_PERSIST_TOKEN", "").strip()
GH_PERSIST_REPO = os.environ.get("GH_PERSIST_REPO", "noperi0000-netizen/Panel-Sloper").strip()
GH_PERSIST_PATH = os.environ.get("GH_PERSIST_PATH", "state/panel_state.json").strip()
GH_PERSIST_BRANCH = os.environ.get("GH_PERSIST_BRANCH", "state").strip()
_gh_sha_cache: dict[str, str] = {}

async def _gh_persist_push(data: str) -> None:
    """state را به یک branch جداگانه در GitHub push می‌کند (جایگزین volume)."""
    if not GH_PERSIST_TOKEN:
        return
    url = f"https://api.github.com/repos/{GH_PERSIST_REPO}/contents/{GH_PERSIST_PATH}"
    async with httpx.AsyncClient(timeout=20) as cli:
        try:
            prev = await cli.get(url, headers={"Authorization": f"token {GH_PERSIST_TOKEN}", "Accept": "application/vnd.github+json"})
            if prev.status_code == 200:
                _gh_sha_cache["sha"] = prev.json().get("sha")
        except Exception:
            pass
        body = {"message": "state: auto-persist", "branch": GH_PERSIST_BRANCH,
                "content": __import__("base64").b64encode(data.encode()).decode(),
                **({"sha": _gh_sha_cache["sha"]} if "sha" in _gh_sha_cache else {})}
        try:
            r = await cli.put(url, json=body, headers={"Authorization": f"token {GH_PERSIST_TOKEN}", "Accept": "application/vnd.github+json"})
            if r.status_code in (200, 201):
                _gh_sha_cache["sha"] = r.json().get("content", {}).get("sha", _gh_sha_cache.get("sha", ""))
        except Exception as e:
            logger.warning(f"github persist push failed: {e}")

async def _gh_persist_pull() -> str | None:
    """state را از GitHub branch می‌خواند (در صورت نبود فایل محلی)."""
    if not GH_PERSIST_TOKEN:
        return None
    url = f"https://api.github.com/repos/{GH_PERSIST_REPO}/contents/{GH_PERSIST_PATH}?ref={GH_PERSIST_BRANCH}"
    async with httpx.AsyncClient(timeout=20) as cli:
        try:
            r = await cli.get(url, headers={"Authorization": f"token {GH_PERSIST_TOKEN}", "Accept": "application/vnd.github+json"})
            if r.status_code == 200:
                import base64
                return base64.b64decode(r.json()["content"]).decode()
        except Exception as e:
            logger.warning(f"github persist pull failed: {e}")
    return None

async def save_state():
    async with SAVE_LOCK:
        try:
            DATA_DIR.mkdir(parents=True, exist_ok=True)
            data = {
                "links": dict(LINKS),
                "subs": dict(SUBS),
            "categories": dict(CATEGORIES),
                "password_hash": AUTH["password_hash"],
                "username": AUTH["username"],
                "saved_at": datetime.now().isoformat()}
            tmp = DATA_FILE.with_suffix(".tmp")
            async with aiofiles.open(tmp, "w", encoding="utf-8") as f:
                await f.write(json.dumps(data, ensure_ascii=False, indent=2))
            tmp.replace(DATA_FILE)
            await _gh_persist_push(json.dumps(data, ensure_ascii=False))
        except Exception as e:
            logger.warning(f"Could not save state: {e}")

# ── In-memory state ───────────────────────────────────────────────────────────
connections: dict = {}
stats = {
    "total_bytes": 0,
    "total_requests": 0,
    "total_errors": 0,
    "start_time": time.time()}
error_logs: deque = deque(maxlen=50)
activity_logs: deque = deque(maxlen=200)
hourly_traffic: dict = defaultdict(int)
http_client: httpx.AsyncClient | None = None
LINKS: dict = {}
LINKS_LOCK = asyncio.Lock()
SUBS: dict = {}
SUBS_LOCK = asyncio.Lock()
CATEGORIES: dict = {}
CATEGORIES_LOCK = asyncio.Lock()

# پروتکل‌های پشتیبانی‌شده برای هر کانفیگ
PROTOCOLS = ("vless-ws", "xhttp-packet-up", "xhttp-stream-up")
DEFAULT_PROTOCOL = "vless-ws"

# Fingerprint (uTLS) های قابل انتخاب برای هر کانفیگ
FINGERPRINTS = ("chrome", "firefox", "safari", "ios", "android", "edge", "360", "qq", "random", "randomized")
DEFAULT_FINGERPRINT = "chrome"

# پیش‌فرض ALPN بر اساس نوع ترابرد (اگر کاربر مقدار دستی نده)
DEFAULT_ALPN_BY_PROTOCOL = {
    "vless-ws": "http/1.1",
    "xhttp-packet-up": "h2,http/1.1",
    "xhttp-stream-up": "h2,http/1.1",
    "xhttp-stream-one": "h2,http/1.1"}
DEFAULT_PORT = 443
MIN_PORT, MAX_PORT = 1, 65535

# محدودیت سرعت (0 = نامحدود). واحد ذخیره‌سازی داخلی همیشه بایت‌بر‌ثانیه است.
DEFAULT_SPEED_LIMIT = 0

def log_activity(kind: str, message: str, level: str = "info", meta: dict | None = None):
    """ثبت یک رخداد در لاگ فعالیت‌ها (ساخت/حذف/ویرایش کانفیگ، ورود، و...)."""
    activity_logs.append({
        "kind": kind,
        "level": level,
        "message": message,
        "time": datetime.now().isoformat(),
        **(meta or {})})

# ── Auth ──────────────────────────────────────────────────────────────────────
SESSION_COOKIE = "vpn_session"
# Admin sessions now expire and roll over instead of lasting a full year.
SESSION_TTL = int(os.environ.get("SESSION_TTL_SECONDS", str(60 * 60 * 24 * 30)))  # 30 days default

def hash_password(pw: str) -> str:
    """PBKDF2 password hash; legacy SHA-256 hashes remain verifiable for migration."""
    iterations = 310_000
    salt = secrets.token_hex(16)
    digest = hashlib.pbkdf2_hmac("sha256", pw.encode(), salt.encode(), iterations)
    return f"pbkdf2_sha256${iterations}${salt}${digest.hex()}"


def verify_password(pw: str, stored: str) -> bool:
    if not stored:
        return False
    if stored.startswith("pbkdf2_sha256$"):
        try:
            _, iterations, salt, expected = stored.split("$", 3)
            digest = hashlib.pbkdf2_hmac("sha256", pw.encode(), salt.encode(), int(iterations))
            return hmac.compare_digest(digest.hex(), expected)
        except (ValueError, TypeError):
            return False
    legacy = hashlib.sha256(f"{pw}{CONFIG['secret']}".encode()).hexdigest()
    return hmac.compare_digest(legacy, stored)

_env_admin_user = os.environ.get("ADMIN_USERNAME", "Noperi")
_env_admin_pw = os.environ.get("ADMIN_PASSWORD", "")
# Seed from env once. If no ADMIN_PASSWORD is provided (fresh install), the
# documented default "Noperi" is used. A persisted password in state.json
# always wins so users can change it from the panel.
AUTH = {"username": _env_admin_user, "password_hash": hash_password(_env_admin_pw) if _env_admin_pw else hash_password("Noperi")}
LOGIN_CAPTCHAS: dict[str, tuple[str, float]] = {}
SESSIONS: dict = {}
SESSIONS_LOCK = asyncio.Lock()
LOGIN_FAILURES: dict[str, list[float]] = defaultdict(list)
LOGIN_LOCK = asyncio.Lock()
LOGIN_WINDOW = 300
LOGIN_MAX_FAILURES = 8

def _login_key(ip: str, username: str | None) -> str:
    """Rate-limit key. Always keyed on the supplied username so an attacker cannot
    reset the counter by rotating a spoofable X-Forwarded-For value; the unspoofable
    peer IP is added when a username is absent."""
    u = (username or "").strip().lower()
    if u:
        return f"u:{u}"
    return f"ip:{ip}"

async def login_rate_limited(ip: str, username: str | None = None) -> bool:
    now = time.time()
    key = _login_key(ip, username)
    async with LOGIN_LOCK:
        attempts = [t for t in LOGIN_FAILURES.get(key, []) if now - t < LOGIN_WINDOW]
        LOGIN_FAILURES[key] = attempts
        return len(attempts) >= LOGIN_MAX_FAILURES

async def record_login_failure(ip: str, username: str | None = None):
    async with LOGIN_LOCK:
        LOGIN_FAILURES[_login_key(ip, username)].append(time.time())

async def create_session(ip: str | None = None, ua: str | None = None) -> str:
    token = secrets.token_urlsafe(32)
    now = time.time()
    async with SESSIONS_LOCK:
        SESSIONS[token] = {
            "expires_at": now + SESSION_TTL,
            "created_at": now,
            "ip": ip or "",
            "ua": (ua or "")[:300],
            "device": detect_device(ua or ""),
        }
    return token

async def is_valid_session(token: str | None) -> bool:
    if not token:
        return False
    async with SESSIONS_LOCK:
        sess = SESSIONS.get(token)
        if sess is None:
            return False
        exp = sess.get("expires_at", 0) if isinstance(sess, dict) else sess
        if exp < time.time():
            SESSIONS.pop(token, None)
            return False
        return True

async def destroy_session(token: str | None):
    if not token:
        return
    async with SESSIONS_LOCK:
        SESSIONS.pop(token, None)

async def require_auth(request: Request):
    token = request.cookies.get(SESSION_COOKIE)
    if not await is_valid_session(token):
        raise HTTPException(status_code=401, detail="unauthorized")
    return token

# ── Startup / Shutdown ────────────────────────────────────────────────────────
@app.on_event("startup")
async def startup():
    global http_client
    limits = httpx.Limits(max_connections=500, max_keepalive_connections=100)
    timeout = httpx.Timeout(30.0, connect=10.0)
    http_client = httpx.AsyncClient(
        limits=limits, timeout=timeout, follow_redirects=True,
    )
    await load_state()
    ensure_reaper()
    ensure_backup_scheduler()
    log_activity("system", "سرور راه‌اندازی شد", "ok")
    logger.info(f"{APP_NAME} v{APP_VERSION} started on port {CONFIG['port']}")

@app.on_event("shutdown")
async def shutdown():
    await save_state()
    if http_client:
        await http_client.aclose()

# ── Helpers ───────────────────────────────────────────────────────────────────
def get_host(request: Request | None = None) -> str:
    """Return a validated public host; proxy headers are trusted only when explicitly enabled."""
    configured = os.environ.get("RAILWAY_PUBLIC_DOMAIN") or CONFIG["host"]
    if request is not None:
        header_name = "x-forwarded-host" if TRUST_PROXY_HEADERS else "host"
        candidate = request.headers.get(header_name, "").split(",", 1)[0].strip().split(":", 1)[0].lower()
        if not candidate:
            return configured
        # Never trust an arbitrary client-supplied Host: it must match the configured
        # public domain or an explicit allowlist, otherwise link generation could be
        # poisoned with an attacker-controlled domain.
        host_is_allowed = candidate in ALLOWED_PUBLIC_HOSTS or (not ALLOWED_PUBLIC_HOSTS and (configured == "localhost" or candidate == configured.lower()))
        if host_is_allowed:
            persist_host(candidate)
            return candidate
    return configured

def generate_uuid() -> str:
    h = secrets.token_hex(16)
    return f"{h[:8]}-{h[8:12]}-{h[12:16]}-{h[16:20]}-{h[20:32]}"
    
def now_ir() -> datetime:
    return datetime.now(IRAN_TZ)

def generate_vless_link(
    uuid: str,
    host: str,
    remark: str = "",
    protocol: str = DEFAULT_PROTOCOL,
    fingerprint: str | None = None,
    alpn: str | None = None,
    port: int | None = None,
) -> str:
    """می‌سازد VLESS share-link متناسب با پروتکل انتخاب‌شده (WS کلاسیک یا یکی از مدهای XHTTP).
    fingerprint / alpn / port در صورت ندادن، از پیش‌فرض‌های خود پروتکل استفاده می‌شوند."""
    fp = (fingerprint or DEFAULT_FINGERPRINT).strip() or DEFAULT_FINGERPRINT
    if fp not in FINGERPRINTS:
        fp = DEFAULT_FINGERPRINT
    alpn_val = (alpn or "").strip() or DEFAULT_ALPN_BY_PROTOCOL.get(protocol, "http/1.1")
    port_val = port or DEFAULT_PORT
    if not (MIN_PORT <= port_val <= MAX_PORT):
        port_val = DEFAULT_PORT

    if protocol == "vless-ws":
        path = f"/ws/{uuid}"
        params = {
            "encryption": "none",
            "security": "tls",
            "type": "ws",
            "host": host,
            "path": path,
            "sni": host,
            "fp": fp,
            "alpn": alpn_val}
    else:
        # xhttp-packet-up / xhttp-stream-up / xhttp-stream-one
        mode = protocol.replace("xhttp-", "")  # packet-up | stream-up | stream-one
        path = f"/xhttp-siz10/{mode}/{uuid}"
        params = {
            "encryption": "none",
            "security": "tls",
            "type": "xhttp",
            "mode": mode,
            "host": host,
            "path": path,
            "sni": host,
            "fp": fp,
            "alpn": alpn_val}
    query = "&".join(f"{k}={quote(str(v))}" for k, v in params.items())
    return f"vless://{uuid}@{host}:{port_val}?{query}#{quote(remark)}"

def vless_link_for_link(link: dict, uid: str, host: str) -> str:
    """generate_vless_link رو با تنظیمات دستی همون کانفیگ (fingerprint/alpn/port) صدا می‌زنه."""
    proto = link.get("protocol", DEFAULT_PROTOCOL)
    return generate_vless_link(
        uid, host,
        remark=link.get('label',''),
        protocol=proto,
        fingerprint=link.get("fingerprint"),
        alpn=link.get("alpn"),
        port=link.get("port"),
    )

def uptime() -> str:
    secs = int(time.time() - stats["start_time"])
    h, m, s = secs // 3600, (secs % 3600) // 60, secs % 60
    return f"{h:02d}:{m:02d}:{s:02d}"

def parse_size_to_bytes(value: float, unit: str) -> int:
    unit = unit.upper()
    if unit == "GB": return int(value * 1024 ** 3)
    if unit == "MB": return int(value * 1024 ** 2)
    if unit == "KB": return int(value * 1024)
    return int(value)

def parse_speed_to_bytes(value: float, unit: str) -> int:
    """محدودیت سرعت رو به بایت‌بر‌ثانیه تبدیل می‌کنه.
    واحدهای پشتیبانی‌شده: MBIT (مگابیت‌بر‌ثانیه، رایج‌ترین)، KB (کیلوبایت‌بر‌ثانیه)، MB (مگابایت‌بر‌ثانیه)."""
    if value <= 0:
        return 0
    unit = (unit or "MBIT").upper()
    if unit == "MBIT":
        return int(value * 1024 * 1024 / 8)
    if unit == "KB":
        return int(value * 1024)
    if unit == "MB":
        return int(value * 1024 * 1024)
    return int(value)

# ── Inlined compact QR encoder (dependency-free) ─────────────────────────────
_QR_GF_EXP = [0] * 512
_QR_GF_LOG = [0] * 256
def _gf_init():
    x = 1
    for i in range(255):
        _QR_GF_EXP[i] = x
        _QR_GF_LOG[x] = i
        x <<= 1
        if x & 0x100:
            x ^= 0x11D
    for i in range(255, 512):
        _QR_GF_EXP[i] = _QR_GF_EXP[i - 255]
_gf_init()

def _gf_mul(a: int, b: int) -> int:
    if a == 0 or b == 0:
        return 0
    return _QR_GF_EXP[_QR_GF_LOG[a] + _QR_GF_LOG[b]]

def _rs_blocks(data: list, ec_len: int) -> list:
    g = [1] + [0] * ec_len
    for i in range(ec_len):
        for j in range(ec_len):
            g[j] ^= _gf_mul(g[j + 1], _QR_GF_EXP[i])
    res = list(data) + [0] * ec_len
    for i in range(len(data)):
        c = res[i]
        for j in range(ec_len):
            res[i + 1 + j] ^= _gf_mul(g[j + 1], c)
    return res[-ec_len:]

_QR_ALIGN = {2: (6, 18), 3: (6, 22), 4: (6, 26)}
_QR_CAP = {1: 14, 2: 26, 3: 42, 4: 78}   # byte-mode capacity (L)

def _qr_build(text: str):
    """Return (matrix, size) for a version 1-4 byte-mode QR with mask 0."""
    data = text.encode("utf-8")
    n = len(data)
    version = 1
    for v in (1, 2, 3, 4):
        if n <= _QR_CAP[v]:
            version = v
            break
    else:
        version = 4
    size = version * 4 + 17
    total_cw = {1: 26, 2: 44, 3: 70, 4: 100}[version]
    ec_len = {1: 7, 2: 10, 3: 15, 4: 16}[version]

    bits = [0, 1, 0, 0]  # byte-mode indicator
    for i in range(7, -1, -1):
        bits.append((n >> i) & 1)
    for ch in data:
        for i in range(7, -1, -1):
            bits.append((ch >> i) & 1)
    max_bits = (total_cw + ec_len) * 8
    bits = bits[:max_bits]
    while len(bits) % 8:
        bits.append(0)
    pad = [1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    pi = 0
    while len(bits) < max_bits:
        bits.append(pad[pi % 16])
        pi += 1
    codewords = []
    for b in range(0, len(bits), 8):
        v = 0
        for bit in bits[b:b + 8]:
            v = (v << 1) | bit
        codewords.append(v)
    ec = _rs_blocks(codewords, ec_len)
    codewords += ec

    M = [[-1] * size for _ in range(size)]

    finder = [[1, 1, 1, 1, 1, 1, 1], [1, 0, 0, 0, 0, 0, 1], [1, 0, 1, 1, 1, 0, 1],
              [1, 0, 1, 1, 1, 0, 1], [1, 0, 1, 1, 1, 0, 1], [1, 0, 0, 0, 0, 0, 1],
              [1, 1, 1, 1, 1, 1, 1]]
    for (r, c) in [(0, 0), (0, size - 7), (size - 7, 0)]:
        for y in range(7):
            for x in range(7):
                M[r + y][c + x] = finder[y][x]
        for i in range(8):
            for j in range(8):
                rr, cc = r + i - (1 if r else 0), c + j - (1 if c else 0)
                if 0 <= rr < size and 0 <= cc < size and M[rr][cc] == -1:
                    M[rr][cc] = 0
    M[size - 8][8] = 1  # dark module

    if version >= 2:
        centers = _QR_ALIGN[version]
        for cy in centers:
            for cx in centers:
                skip = False
                for dy in range(-2, 3):
                    for dx in range(-2, 3):
                        if 0 <= cy + dy < size and 0 <= cx + dx < size and M[cy + dy][cx + dx] != -1:
                            skip = True
                if skip:
                    continue
                for dy in range(-2, 3):
                    for dx in range(-2, 3):
                        v = 1 if (abs(dy) == 2 or abs(dx) == 2 or (dy == 0 and dx == 0)) else 0
                        M[cy + dy][cx + dx] = v

    for i in range(8, size - 8):
        if M[6][i] == -1:
            M[6][i] = 1 if i % 2 == 0 else 0
        if M[i][6] == -1:
            M[i][6] = 1 if i % 2 == 0 else 0

    # place codewords zig-zag, applying mask 0 at placement time
    # (function patterns must NOT be masked)
    bi = 0
    col = size - 1
    up = True
    while col > 0:
        if col == 6:
            col -= 1
        for k in range(size):
            r = (size - 1 - k) if up else k
            for dc in (0, -1):
                c = col + dc
                if 0 <= c < size and M[r][c] == -1:
                    bit = codewords[bi >> 3] >> (7 - (bi & 7)) & 1 if (bi >> 3) < len(codewords) else 0
                    bi += 1
                    if (r + c) % 2 == 0:
                        bit ^= 1
                    M[r][c] = bit
        col -= 2
        up = not up

    # format info: level L(01) mask 0 -> 0b101010000010010 (14 bits)
    fb = 0b101010000010010
    fbits = [(fb >> i) & 1 for i in range(13, -1, -1)]
    pos1 = [(8, 0), (8, 1), (8, 2), (8, 3), (8, 4), (8, 5), (8, 7), (8, 8),
            (7, 8), (5, 8), (4, 8), (3, 8), (2, 8), (1, 8)]
    pos2 = [(size - 1, 8), (size - 2, 8), (size - 3, 8), (size - 4, 8), (size - 5, 8),
            (size - 6, 8), (size - 7, 8), (size - 8, 8),
            (8, size - 8), (8, size - 7), (8, size - 6), (8, size - 5), (8, size - 4), (8, size - 3)]
    for i, (r, c) in enumerate(pos1):
        M[r][c] = fbits[i]
    for i, (r, c) in enumerate(pos2):
        M[r][c] = fbits[i]
    return M, size

def qr_svg(data: str, size: int = 200, dark: str = "#10B981", light: str = "#ffffff") -> str:
    """Render a scannable QR (byte mode, L) as inline SVG. No dependencies."""
    try:
        M, n = _qr_build(data)
    except Exception:
        return ""
    cell = size / n
    parts = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{size}" height="{size}" viewBox="0 0 {size} {size}" shape-rendering="crispEdges">',
             f'<rect width="{size}" height="{size}" fill="{light}"/>']
    for y in range(n):
        row = M[y]
        run_x = -1
        for x in range(n):
            if row[x] == 1:
                if run_x < 0:
                    run_x = x
            else:
                if run_x >= 0:
                    parts.append(f'<rect x="{run_x*cell:.2f}" y="{y*cell:.2f}" width="{(x-run_x)*cell:.2f}" height="{cell:.2f}" fill="{dark}"/>')
                    run_x = -1
        if run_x >= 0:
            parts.append(f'<rect x="{run_x*cell:.2f}" y="{y*cell:.2f}" width="{(n-run_x)*cell:.2f}" height="{cell:.2f}" fill="{dark}"/>')
    parts.append('</svg>')
    return ''.join(parts)


def is_link_expired(link: dict) -> bool:
    exp = link.get("expires_at")
    if not exp:
        return False
    try:
        return datetime.now() > datetime.fromisoformat(exp)
    except Exception:
        return False

def is_link_allowed(link: dict | None) -> bool:
    if link is None:
        return False
    if not link.get("active", True):
        return False
    if is_link_expired(link):
        return False
    # بررسی حجم مشترک ساب گروه
    sub_id = link.get("sub_id")
    if sub_id and sub_id in SUBS:
        sub = SUBS[sub_id]
        sub_limit = sub.get("total_limit_bytes", 0)
        sub_used = sub.get("total_used_bytes", 0)
        if sub_limit > 0 and sub_used >= sub_limit:
            return False
        # ═══ پایان روز گروه ═══
        sub_days = sub.get("total_days", 0)
        if sub_days > 0 and sub.get("created_at"):
            try:
                if datetime.fromisoformat(sub["created_at"]) + timedelta(days=sub_days) < datetime.now():
                    return False
            except Exception:
                pass
    lb = link.get("limit_bytes", 0)
    if lb > 0 and link.get("used_bytes", 0) >= lb:
        return False
    return True

def fmt_bytes(b: int) -> str:
    if b < 1024: return f"{b} B"
    if b < 1024**2: return f"{b/1024:.1f} KB"
    if b < 1024**3: return f"{b/1024**2:.2f} MB"
    return f"{b/1024**3:.2f} GB"

def unique_ips_for_uuid(uuid: str) -> set:
    """آی‌پی‌های یکتای همین لحظه متصل به یک UUID خاص (بر اساس dict اتصالات زنده)."""
    return {c.get("ip") for c in connections.values() if c.get("uuid") == uuid and c.get("ip")}

def is_ip_allowed(link: dict | None, uuid: str, ip: str) -> bool:
    """محدودیت تعداد آی‌پی/کاربر هم‌زمان برای هر کانفیگ. ip_limit=0 یعنی نامحدود.
    اگر همین آی‌پی از قبل روی این کانفیگ سشن باز داشته باشه، همیشه مجازه (برای چند اتصال
    هم‌زمان از یک دستگاه/مرورگر مشکلی پیش نمیاد)."""
    if link is None:
        return False
    limit = int(link.get("ip_limit", 0) or 0)
    if limit <= 0:
        return True
    ips = unique_ips_for_uuid(uuid)
    if ip in ips:
        return True
    return len(ips) < limit

def client_ip(request: Request) -> str:
    """آی‌پی واقعی کلاینت. فقط در صورتی هدرهای forwarded رو می‌پذیره که اتصال از
    یک reverse-proxy مورداعتماد بوده (TRUSTED_PROXIES). در غیر این صورت از peer
    address سوکت استفاده می‌شه که قابل جعل نیست."""
    return resolve_client_ip(request)

@app.get("/api/qr")
async def qr_endpoint(data: str):
    """Inline SVG QR — no third-party dependency."""
    if not data or len(data) > 300:
        raise HTTPException(status_code=400, detail="invalid data")
    svg = qr_svg(data, size=260)
    if not svg:
        raise HTTPException(status_code=500, detail="qr failed")
    return HTMLResponse(content=svg, media_type="image/svg+xml")


# ── Auto-expiry & auto-disconnect reaper ────────────────────────────────────────
REAPER_INTERVAL = int(os.environ.get("REAPER_INTERVAL", "60"))

async def _kill_link_connections(uuid: str) -> int:
    """Force-disconnect every live tunnel for one config (WS + XHTTP)."""
    killed = 0
    try:
        from relay_vless import _active_ws
        for conn_id, ws in list(_active_ws.items()):
            conn = connections.get(conn_id)
            if conn and conn.get("uuid") == uuid:
                try:
                    await ws.close(code=1008, reason="link disabled/expired")
                    killed += 1
                except Exception:
                    pass
    except Exception:
        pass
    try:
        import xhttp_siz10
        async with xhttp_siz10.XHTTP_LOCK:
            stale = [sid for sid, s in list(xhttp_siz10.xhttp_sessions.items())
                     if s.get("uuid") == uuid]
        for sid in stale:
            await xhttp_siz10._teardown(sid)
            killed += 1
    except Exception:
        pass
    for cid in [c for c, v in list(connections.items()) if v.get("uuid") == uuid]:
        connections.pop(cid, None)
    return killed

async def _expiry_reaper():
    while True:
        await asyncio.sleep(REAPER_INTERVAL)
        try:
            acted = 0
            async with LINKS_LOCK:
                snap = dict(LINKS)
            for uid, link in snap.items():
                changed = False
                if link.get("active", True) and (is_link_expired(link) or not is_link_allowed(link)):
                    link["active"] = False
                    changed = True
                    if is_link_expired(link):
                        log_activity("link", f"انقضای خودکار: کانفیگ «{link.get('label','?')}» غیرفعال شد", "warn",
                                     meta={"uuid": uid, "expired_at": link.get("expires_at")})
                    else:
                        reason = []
                        sub_id = link.get("sub_id")
                        if sub_id and sub_id in SUBS:
                            sub = SUBS[sub_id]
                            if sub.get("total_limit_bytes", 0) > 0 and sub.get("total_used_bytes", 0) >= sub.get("total_limit_bytes", 0):
                                reason.append("پایان حجم گروه")
                            if sub.get("total_days", 0) and sub.get("created_at") and datetime.fromisoformat(sub["created_at"]) + timedelta(days=sub["total_days"]) < datetime.now():
                                reason.append("پایان روز گروه")
                        if link.get("limit_bytes", 0) > 0 and link.get("used_bytes", 0) >= link.get("limit_bytes", 0):
                            reason.append("پایان حجم کانفیگ")
                        log_activity("link", f"قطع خودکار ({'، '.join(reason) or 'سقف'}): کانفیگ «{link.get('label','?')}»", "warn",
                                     meta={"uuid": uid})
                if changed:
                    acted += 1
                    await _kill_link_connections(uid)
            if acted:
                asyncio.create_task(save_state())
                logger.info(f"reaper: deactivated + disconnected {acted} link(s)")
        except Exception as e:
            logger.warning(f"reaper error: {e}")

_reaper_started = False

def ensure_reaper():
    global _reaper_started
    if not _reaper_started:
        asyncio.create_task(_expiry_reaper())
        _reaper_started = True


# ── Default link ──────────────────────────────────────────────────────────────
_default_link_created = False

async def ensure_default_link():
    global _default_link_created
    if _default_link_created:
        return
    async with LINKS_LOCK:
        if not any(l.get("is_default") for l in LINKS.values()):
            uid = hashlib.sha256(f"default{CONFIG['secret']}".encode()).hexdigest()
            uid = f"{uid[:8]}-{uid[8:12]}-{uid[12:16]}-{uid[16:20]}-{uid[20:32]}"
            if uid not in LINKS:
                LINKS[uid] = {
                    "label": "لینک پیش‌فرض",
                    "limit_bytes": 0,
                    "used_bytes": 0,
                    "created_at": datetime.now().isoformat(),
                    "active": True,
                    "expires_at": None,
                    "note": "",
                    "is_default": True,
                    "sub_id": None,
                    "protocol": DEFAULT_PROTOCOL,
                    "fingerprint": DEFAULT_FINGERPRINT,
                    "alpn": "",
                    "port": DEFAULT_PORT,
                    "ip_limit": 0,
                    "speed_limit_bytes": DEFAULT_SPEED_LIMIT}
                asyncio.create_task(save_state())
        _default_link_created = True

# ── Basic endpoints ───────────────────────────────────────────────────────────
@app.get("/")
async def root():
    return {"service": APP_NAME, "version": APP_VERSION, "status": "active"}

def persistence_status() -> dict:
    """Whether /data is a persistent Railway volume (survives redeploy) or ephemeral."""
    mounted = bool(os.environ.get("RAILWAY_VOLUME_MOUNT_PATH"))
    writable = False
    free_mb = 0
    try:
        DATA_DIR.mkdir(parents=True, exist_ok=True)
        probe = DATA_DIR / ".wprobe"
        probe.write_text("1", encoding="utf-8")
        probe.unlink(missing_ok=True)
        writable = True
        free_mb = int(shutil.disk_usage(DATA_DIR).free / (1024 * 1024))
    except Exception:
        pass
    return {"mounted": mounted, "writable": writable, "free_mb": free_mb,
            "data_dir": str(DATA_DIR)}

@app.get("/health")
async def health():
    ps = persistence_status()
    return {"status": "ok", "connections": len(connections), "uptime": uptime(),
            "version": APP_VERSION, "volume": ps,
            "auth": {"env_admin_pw_set": bool(os.environ.get("ADMIN_PASSWORD")),
                     "reset_flag": bool(os.environ.get("ADMIN_PASSWORD_RESET"))}}

def _collect_telemetry() -> dict:
    """Container-scoped stats. On a shared host, psutil.* returns HOST values which
    are misleading — so we report our own process where it matters."""
    proc = psutil.Process()
    mem = proc.memory_info()
    vm = psutil.virtual_memory()
    try:
        cpu_proc = proc.cpu_percent(interval=0.05)
    except Exception:
        cpu_proc = 0.0
    cpu_count = psutil.cpu_count(logical=True) or 1
    try:
        load = psutil.getloadavg()[0] / cpu_count * 100
    except Exception:
        load = 0.0
    net = psutil.net_io_counters()
    disk = psutil.disk_usage("/")
    return {
        "cpu": {"process_pct": round(cpu_proc, 1),
                "host_pct": round(psutil.cpu_percent(interval=None), 1),
                "load_pct": round(min(load, 100), 1),
                "cores": cpu_count},
        "mem": {"rss_mb": round(mem.rss / 1048576, 1),
                "host_total_mb": round(vm.total / 1048576, 1),
                "host_used_pct": round(vm.percent, 1)},
        "disk": {"used_gb": round(disk.used / 1073741824, 2),
                 "total_gb": round(disk.total / 1073741824, 2),
                 "free_pct": round(100 - disk.percent, 1)},
        "net": {"sent_mb": round(net.bytes_sent / 1048576, 2),
                "recv_mb": round(net.bytes_recv / 1048576, 2)},
        "fds": len(proc.connections()) if hasattr(proc, "connections") else 0,
    }

@app.get("/api/telemetry")
async def telemetry(_=Depends(require_auth)):
    try:
        return {"ok": True, **_collect_telemetry()}
    except Exception as e:
        return {"ok": False, "error": str(e)}

@app.get("/api/system")
async def system_info(_=Depends(require_auth)):
    async with LINKS_LOCK:
        links_count = len(LINKS)
        active_links = sum(1 for link in LINKS.values() if is_link_allowed(link))
    async with SUBS_LOCK:
        subs_count = len(SUBS)
    return {
        "name": APP_NAME,
        "version": APP_VERSION,
        "persistence": persistence_status(),
        "author": "Panel Sloper",
        "platform": "Railway-ready",
        "uptime": uptime(),
        "links_count": links_count,
        "active_links": active_links,
        "subs_count": subs_count,
        "active_connections": len(connections),
        "features": ["VLESS", "WebSocket", "XHTTP", "Traffic limits", "Speed limits", "IP limits", "QR codes", "Backup/export"]}

@app.get("/api/backup")
async def download_backup(_=Depends(require_auth)):
    async with LINKS_LOCK:
        links = dict(LINKS)
    async with SUBS_LOCK:
        subs = dict(SUBS)
    async with CATEGORIES_LOCK:
        cats = dict(CATEGORIES)
    payload = {
        "format": "vpn-backup",
        "version": APP_VERSION,
        "created_at": datetime.now().isoformat(),
        "links": links,
        "subs": subs,
        "categories": cats}
    return Response(
        content=json.dumps(payload, ensure_ascii=False, indent=2),
        media_type="application/json",
        headers={"Content-Disposition": "attachment; filename=vpn-backup.json"},
    )

# ── Automatic backups (6 / 3 / 1 rotation) ─────────────────────────────────────
BACKUP_DIR = DATA_DIR / "backups"
BACKUP_KEEP = {"hourly": 6, "daily": 3, "weekly": 1}

def _prune_backups(kind: str):
    try:
        files = sorted(BACKUP_DIR.glob(f"vpn-{kind}-*.json"))
        for f in files[:max(0, len(files) - BACKUP_KEEP[kind])]:
            f.unlink(missing_ok=True)
    except Exception:
        pass

async def auto_backup(kind: str):
    try:
        BACKUP_DIR.mkdir(parents=True, exist_ok=True)
        async with LINKS_LOCK:
            links = dict(LINKS)
        async with SUBS_LOCK:
            subs = dict(SUBS)
        async with CATEGORIES_LOCK:
            cats = dict(CATEGORIES)
        payload = json.dumps({
            "format": "vpn-backup", "version": APP_VERSION,
            "created_at": datetime.now().isoformat(),
            "kind": kind,
            "links": links, "subs": subs, "categories": cats},
            ensure_ascii=False, indent=2)
        (BACKUP_DIR / f"vpn-{kind}-{datetime.now().strftime('%Y%m%d-%H%M%S')}.json").write_text(payload, encoding="utf-8")
        _prune_backups(kind)
        log_activity("backup", f"بکاپ خودکار {kind} ساخته شد", "info")
    except Exception as e:
        logger.warning(f"auto backup error: {e}")

@app.get("/api/backups")
async def list_backups(_=Depends(require_auth)):
    try:
        files = sorted(BACKUP_DIR.glob("vpn-*.json"), reverse=True)
        out = []
        for f in files:
            parts = f.stem.split("-")
            out.append({"name": f.name, "kind": parts[1] if len(parts) > 2 else "?",
                        "size": f.stat().st_size, "created": datetime.fromtimestamp(f.stat().st_mtime).isoformat()})
        return {"backups": out, "count": len(out)}
    except Exception as e:
        return {"backups": [], "count": 0, "error": str(e)}

@app.post("/api/backups/restore/{name}")
async def restore_named_backup(name: str, _=Depends(require_auth)):
    f = BACKUP_DIR / name
    if not f.is_file() or f.parent != BACKUP_DIR:
        raise HTTPException(404, "بکاپ پیدا نشد")
    payload = json.loads(f.read_text(encoding="utf-8"))
    links, subs = payload.get("links"), payload.get("subs")
    if not isinstance(links, dict) or not isinstance(subs, dict):
        raise HTTPException(400, "ساختار بکاپ نامعتبر")
    async with LINKS_LOCK:
        LINKS.clear(); LINKS.update(links)
    async with SUBS_LOCK:
        SUBS.clear(); SUBS.update(subs)
    async with CATEGORIES_LOCK:
        CATEGORIES.clear(); CATEGORIES.update(payload.get("categories") or {})
    await save_state()
    log_activity("backup", f"بکاپ {name} بازگردانی شد", "ok")
    return {"ok": True, "links": len(LINKS), "subs": len(SUBS)}

@app.post("/api/backup")
async def manual_backup(_=Depends(require_auth)):
    await auto_backup("manual")
    return {"ok": True}

async def _backup_scheduler():
    """۶ بکاپ ساعتی + ۳ روزانه + ۱ هفتگی."""
    while True:
        await asyncio.sleep(3600)
        try:
            now = datetime.now()
            await auto_backup("hourly")
            if now.hour == 3:
                await auto_backup("daily")
            if now.weekday() == 6 and now.hour == 4:
                await auto_backup("weekly")
        except Exception as e:
            logger.warning(f"backup scheduler error: {e}")

_backup_started = False
def ensure_backup_scheduler():
    global _backup_started
    if not _backup_started:
        asyncio.create_task(_backup_scheduler())
        _backup_started = True

@app.post("/api/restore")
async def restore_backup(request: Request, _=Depends(require_auth)):
    body = await request.json()
    if body.get("format") not in {"vpn-backup", None}:
        raise HTTPException(status_code=400, detail="فرمت backup نامعتبر است")
    links = body.get("links")
    subs = body.get("subs")
    cats = body.get("categories") or {}
    if not isinstance(links, dict) or not isinstance(subs, dict) or len(links) > 5000 or len(subs) > 1000:
        raise HTTPException(status_code=400, detail="ساختار backup نامعتبر است")
    if not isinstance(cats, dict) or len(cats) > 500:
        cats = {}
    async with LINKS_LOCK:
        LINKS.clear()
        LINKS.update(links)
    async with SUBS_LOCK:
        SUBS.clear()
        SUBS.update(subs)
    async with CATEGORIES_LOCK:
        CATEGORIES.clear()
        CATEGORIES.update(cats)
    await save_state()
    log_activity("backup", "پشتیبان با موفقیت restore شد", "ok")
    return {"ok": True, "links": len(LINKS), "subs": len(SUBS), "categories": len(CATEGORIES)}

@app.get("/api/links/export")
async def export_links(request: Request, _=Depends(require_auth)):
    host = get_host(request)
    async with LINKS_LOCK:
        lines = [vless_link_for_link(link, uid, host) for uid, link in LINKS.items() if is_link_allowed(link)]
    return {"version": APP_VERSION, "count": len(lines), "links": lines}

@app.post("/api/links/bulk")
async def bulk_links(request: Request, _=Depends(require_auth)):
    body = await request.json()
    action = str(body.get("action", "")).lower()
    ids = [str(uid) for uid in (body.get("ids") or [])][:500]
    if action not in {"activate", "deactivate", "reset_usage"}:
        raise HTTPException(status_code=400, detail="عملیات نامعتبر است")
    changed = 0
    async with LINKS_LOCK:
        for uid in ids:
            link = LINKS.get(uid)
            if not link:
                continue
            if action == "activate":
                link["active"] = True
            elif action == "deactivate":
                link["active"] = False
            else:
                link["used_bytes"] = 0
            changed += 1
    if changed:
        await save_state()
        log_activity("bulk", f"عملیات گروهی {action} روی {changed} کانفیگ انجام شد", "ok")
    return {"ok": True, "changed": changed, "action": action}

# ── Subscription (single link) ────────────────────────────────────────────────
@app.get("/sub/{uuid}")
async def subscription_single(uuid: str, request: Request):
    import base64
    async with LINKS_LOCK:
        link = LINKS.get(uuid)
    if not link or not is_link_allowed(link):
        raise HTTPException(status_code=404, detail="not found or inactive")
    host = get_host(request)
    vless = vless_link_for_link(link, uuid, host)
    content = base64.b64encode(vless.encode()).decode()
    return Response(content=content, media_type="text/plain",
                    headers={"profile-title": quote(link["label"])})

@app.get("/sub-all")
async def subscription_all(request: Request, _=Depends(require_auth)):
    import base64
    host = get_host(request)
    async with LINKS_LOCK:
        lines = [
            vless_link_for_link(d, uid, host)
            for uid, d in LINKS.items()
            if is_link_allowed(d)
        ]
    content = base64.b64encode("\n".join(lines).encode()).decode()
    return Response(content=content, media_type="text/plain")

# ══════════════════════════════════════════════════════════════════════════════
# SUB GROUP endpoints
# ══════════════════════════════════════════════════════════════════════════════

@app.post("/api/subs")
async def create_sub(request: Request, _=Depends(require_auth)):
    body = await request.json()
    name = (body.get("name") or "گروه جدید").strip()[:60]
    desc = (body.get("desc") or "").strip()[:200]
    password = (body.get("password") or "").strip()
    sub_id = generate_uuid()
    uuid_key = secrets.token_urlsafe(16)
    async with SUBS_LOCK:
        SUBS[sub_id] = {
            "name": name,
            "desc": desc,
            "password_hash": hash_password(password) if password else None,
            "uuid_key": uuid_key,
            "created_at": datetime.now().isoformat(),
            "link_ids": [],
            "total_limit_bytes": 0,
            "total_used_bytes": 0}
    asyncio.create_task(save_state())
    log_activity("sub", f"گروه «{name}» ساخته شد", "ok")
    host = get_host(request)
    return {
        "sub_id": sub_id,
        **SUBS[sub_id],
        "public_url": f"https://{host}/p/{uuid_key}",
        "sub_url": f"https://{host}/sub-group/{uuid_key}"}


@app.post("/api/subs/{sub_id}/bandwidth")
async def set_sub_bandwidth(sub_id: str, request: Request, _=Depends(require_auth)):
    """تنظیم حجم مشترک گروه. days>0 تعداد روز گروه را هم ثبت می‌کند."""
    body = await request.json()
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(404, detail="sub not found")
        s = SUBS[sub_id]
        if "total_limit_bytes" in body:
            try: s["total_limit_bytes"] = max(0, int(body["total_limit_bytes"] or 0))
            except (TypeError, ValueError): pass
        if "total_used_bytes" in body:
            try: s["total_used_bytes"] = max(0, int(body["total_used_bytes"] or 0))
            except (TypeError, ValueError): pass
        days = int(body.get("days") or 0)
        if days > 0:
            s["total_days"] = days
        s_name = s.get("name", sub_id)
    await save_state()
    log_activity("sub", f"حجم گروه «{s_name}» به‌روزرسانی شد", "info")
    return {"ok": True, **{k: v for k, v in s.items() if k != "password_hash"}}

@app.post("/api/subs/{sub_id}/quick-create")
async def quick_create_links(sub_id: str, request: Request, _=Depends(require_auth)):
    """Batch-build the 24-config matrix for a sub group in ONE request."""
    body = await request.json()
    async with SUBS_LOCK:
        sub = SUBS.get(sub_id)
        if not sub:
            raise HTTPException(status_code=404, detail="sub not found")
        sub_name = sub.get("name", sub_id)

    days = max(0, min(3650, int(body.get("days") or 0)))
    ip_limit = max(0, min(100, int(body.get("ip_limit") or 0)))
    # ═══ reaper با اتمام روز گروه هم خاموش میکنه → total_days رو ثبت میکنیم ═══
    async with SUBS_LOCK:
        if sub_id in SUBS:
            SUBS[sub_id]["total_days"] = days
            if days > 0 and not SUBS[sub_id].get("created_at"):
                SUBS[sub_id]["created_at"] = datetime.now().isoformat()
    try:
        speed_limit_bytes = int(body.get("speed_limit_bytes") or 0)
    except (TypeError, ValueError):
        speed_limit_bytes = 0
    expires_at = (datetime.now() + timedelta(days=days)).isoformat() if days > 0 else None

    protos = ("vless-ws", "xhttp-packet-up", "xhttp-stream-up")
    fps = ("chrome", "ios")
    alpns = ("", "h2", "http/1.1", "h2,http/1.1")
    abbr_p = {"vless-ws": "VWS", "xhttp-packet-up": "XPU", "xhttp-stream-up": "XHS"}
    abbr_f = {"chrome": "CH", "ios": "IO"}
    abbr_a = {"": "DEF", "h2": "H2", "http/1.1": "11", "h2,http/1.1": "MIX"}

    # Idempotency: drop any configs already attached to this group so a
    # retry never doubles the matrix.
    async with SUBS_LOCK:
        existing = list(sub.get("link_ids", []))
    for old_uid in existing:
        if old_uid in LINKS:
            await remove_link(old_uid)
        elif old_uid in SUBS.get(sub_id, {}).get("link_ids", []):
            async with SUBS_LOCK:
                SUBS[sub_id]["link_ids"] = [x for x in SUBS[sub_id].get("link_ids", []) if x != old_uid]

    created = []
    count = 1
    for proto in protos:
        for fp in fps:
            for alpn in alpns:
                label = f"{abbr_p[proto]}-{abbr_f[fp]}-{abbr_a[alpn]}-{count:02d}"
                uid, _link = await make_link(
                    label=label, limit_bytes=0, expires_at=expires_at,
                    sub_id=sub_id, protocol=proto, fingerprint=fp, alpn=alpn,
                    port=443, ip_limit=ip_limit, speed_limit_bytes=speed_limit_bytes)
                created.append(uid)
                count += 1

    # make_link already appends to sub.link_ids and fires save_state; one final
    # consolidated save + log keeps it cheap and consistent.
    await save_state()
    log_activity("sub", f"۲۴ کانفیگ برای گروه «{sub_name}» ساخته شد", "ok")
    return {"ok": True, "count": len(created), "links": created}


@app.get("/api/subs/{sub_id}/bandwidth")
async def get_sub_bandwidth(sub_id: str, _=Depends(require_auth)):
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(404, "not found")
        sub = SUBS[sub_id]
    return {"total_limit_bytes": sub.get("total_limit_bytes", 0), "total_used_bytes": sub.get("total_used_bytes", 0)}

@app.get("/api/subs/{sub_id}")
async def get_sub_single(sub_id: str, request: Request, _=Depends(require_auth)):
    host = get_host(request)
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(404, "not found")
        s = dict(SUBS[sub_id])
    async with LINKS_LOCK:
        snap_links = dict(LINKS)
    link_ids = s.get("link_ids", [])
    active_count = sum(1 for lid in link_ids if is_link_allowed(snap_links.get(lid)))
    total_used = sum(snap_links[lid].get("used_bytes", 0) for lid in link_ids if lid in snap_links)
    return {
        "sub_id": sub_id,
        **s,
        "password_hash": None,
        "has_password": s.get("password_hash") is not None,
        "links_count": len(link_ids),
        "active_count": active_count,
        "total_used_bytes": total_used,
        "total_used_fmt": fmt_bytes(total_used),
        "public_url": f"https://{host}/p/{s['uuid_key']}",
        "sub_url": f"https://{host}/sub-group/{s['uuid_key']}"
    }

@app.get("/api/subs")
async def list_subs(request: Request, _=Depends(require_auth)):
    host = get_host(request)
    async with SUBS_LOCK:
        snap_subs = dict(SUBS)
    async with LINKS_LOCK:
        snap_links = dict(LINKS)
    result = []
    for sid, s in snap_subs.items():
        link_ids = s.get("link_ids", [])
        active_count = sum(1 for lid in link_ids if is_link_allowed(snap_links.get(lid)))
        total_used = sum(snap_links[lid].get("used_bytes", 0) for lid in link_ids if lid in snap_links)
        result.append({
            "sub_id": sid,
            **s,
            "password_hash": None,
            "has_password": s.get("password_hash") is not None,
            "links_count": len(link_ids),
            "active_count": active_count,
            "total_used_bytes": total_used,
            "total_used_fmt": fmt_bytes(total_used),
            "public_url": f"https://{host}/p/{s['uuid_key']}",
            "sub_url": f"https://{host}/sub-group/{s['uuid_key']}"})
    result.sort(key=lambda x: x["created_at"], reverse=True)
    return {"subs": result}

@app.patch("/api/subs/{sub_id}")
async def update_sub(sub_id: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        s = SUBS[sub_id]
        if "name" in body:
            s["name"] = str(body["name"])[:60]
        if "desc" in body:
            s["desc"] = str(body["desc"])[:200]
        if "password" in body:
            pw = str(body["password"]).strip()
            s["password_hash"] = hash_password(pw) if pw else None
        if "link_ids" in body:
            s["link_ids"] = list(body["link_ids"])
    asyncio.create_task(save_state())
    return {"ok": True}

@app.delete("/api/subs/{sub_id}")
async def delete_sub(sub_id: str, _=Depends(require_auth)):
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        name = SUBS[sub_id].get("name", sub_id)
        del SUBS[sub_id]
    async with LINKS_LOCK:
        for link in LINKS.values():
            if link.get("sub_id") == sub_id:
                link["sub_id"] = None
    asyncio.create_task(save_state())
    log_activity("sub", f"گروه «{name}» حذف شد", "warn")
    return {"ok": True, "deleted": sub_id}

@app.post("/api/subs/{sub_id}/links")
async def assign_link_to_sub(sub_id: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    link_id = str(body.get("link_id", ""))
    action = str(body.get("action", "add"))
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            raise HTTPException(status_code=404, detail="sub not found")
        s = SUBS[sub_id]
        ids = s.setdefault("link_ids", [])
        if action == "add":
            if link_id not in ids:
                ids.append(link_id)
        else:
            if link_id in ids:
                ids.remove(link_id)
    async with LINKS_LOCK:
        if link_id in LINKS:
            LINKS[link_id]["sub_id"] = sub_id if action == "add" else None
    asyncio.create_task(save_state())
    return {"ok": True}

# ── Public sub-group subscription file ───────────────────────────────────────
@app.get("/sub-group/{uuid_key}")
async def sub_group_subscription(uuid_key: str, request: Request):
    import base64
    async with SUBS_LOCK:
        sub = next((s for s in SUBS.values() if s.get("uuid_key") == uuid_key), None)
    if not sub:
        raise HTTPException(status_code=404, detail="not found")

    if sub.get("password_hash"):
        pw = request.query_params.get("pw", "")
        if not verify_password(pw, sub["password_hash"]):
            raise HTTPException(status_code=403, detail="wrong password")

    host = get_host(request)
    link_ids = sub.get("link_ids", [])
    async with LINKS_LOCK:
        lines = []
        for lid in link_ids:
            link = LINKS.get(lid)
            if link and is_link_allowed(link):
                lines.append(vless_link_for_link(link, lid, host))

    content = base64.b64encode("\n".join(lines).encode()).decode()
    return Response(
        content=content,
        media_type="text/plain",
        headers={
            "profile-title": quote(sub["name"]),
            "profile-update-interval": "12"}
    )

# ── Auth endpoints ────────────────────────────────────────────────────────────
@app.post("/api/login")
async def api_login(request: Request):
    body = await request.json()
    ip = client_ip(request)
    # Captcha removed - just check username/password
    username = str(body.get("username", "")).strip()
    if await login_rate_limited(ip, username):
        raise HTTPException(status_code=429, detail="تعداد تلاش‌ها زیاد است؛ چند دقیقه بعد دوباره امتحان کنید")
    username_ok = hmac.compare_digest(username, AUTH["username"]) if username else False
    if not username_ok or not verify_password(str(body.get("password", "")), AUTH["password_hash"]):
        await record_login_failure(ip, username or None)
        log_activity("auth", f"تلاش ورود ناموفق از {ip}", "err")
        raise HTTPException(status_code=401, detail="نام کاربری یا رمز عبور اشتباه است")
    if not AUTH["password_hash"].startswith("pbkdf2_sha256$"):
        AUTH["password_hash"] = hash_password(str(body.get("password", "")))
        await save_state()
    token = await create_session(ip=ip, ua=str(request.headers.get("user-agent", "")))
    log_activity("auth", f"ورود موفق به پنل از {ip}", "ok")
    resp = JSONResponse({"ok": True})
    resp.set_cookie(SESSION_COOKIE, token, max_age=SESSION_TTL, httponly=True,
                   secure=request.url.scheme == "https", samesite="lax", path="/")
    return resp

@app.post("/api/logout")
async def api_logout(request: Request):
    await destroy_session(request.cookies.get(SESSION_COOKIE))
    resp = JSONResponse({"ok": True})
    resp.delete_cookie(SESSION_COOKIE, path="/")
    return resp

@app.get("/api/me")
async def api_me(request: Request):
    return {"authenticated": await is_valid_session(request.cookies.get(SESSION_COOKIE))}

@app.post("/api/change-password")
async def api_change_password(request: Request, token=Depends(require_auth)):
    body = await request.json()
    if not verify_password(str(body.get("current_password", "")), AUTH["password_hash"]):
        raise HTTPException(status_code=400, detail="رمز فعلی اشتباه است")
    new = str(body.get("new_password", ""))
    if len(new) < 10:
        raise HTTPException(status_code=400, detail="رمز جدید باید حداقل ۱۰ کاراکتر باشد")
    AUTH["password_hash"] = hash_password(new)
    async with SESSIONS_LOCK:
        SESSIONS.clear()
        SESSIONS[token] = {"expires_at": time.time() + SESSION_TTL,
                           "created_at": time.time(), "ip": "", "ua": "", "device": ""}
    await save_state()
    log_activity("auth", "رمز عبور پنل تغییر کرد", "ok")
    return {"ok": True}

# ── Admin credential control ─────────────────────────────────────────────────
@app.post("/api/change-credentials")
async def change_credentials(request: Request, token=Depends(require_auth)):
    body = await request.json()
    if not verify_password(str(body.get("current_password", "")), AUTH["password_hash"]):
        raise HTTPException(status_code=400, detail="رمز فعلی اشتباه است")
    username = str(body.get("username", "")).strip()
    new_password = str(body.get("new_password", ""))
    if len(username) < 3 or len(username) > 64:
        raise HTTPException(status_code=400, detail="نام کاربری باید بین ۳ تا ۶۴ کاراکتر باشد")
    if new_password and len(new_password) < 10:
        raise HTTPException(status_code=400, detail="رمز جدید باید حداقل ۱۰ کاراکتر باشد")
    AUTH["username"] = username
    if new_password:
        AUTH["password_hash"] = hash_password(new_password)
    async with SESSIONS_LOCK:
        SESSIONS.clear()
        SESSIONS[token] = {"expires_at": time.time() + SESSION_TTL,
                           "created_at": time.time(), "ip": "", "ua": "", "device": ""}
    await save_state()
    log_activity("auth", "مشخصات ورود مدیر به‌روزرسانی شد", "ok")
    return {"ok": True, "username": username}

# ── Stats ─────────────────────────────────────────────────────────────────────
@app.get("/stats")
async def get_stats(_=Depends(require_auth)):
    async with LINKS_LOCK:
        snap = dict(LINKS)
    return {
        "active_connections": len(connections),
        "total_traffic_mb": round(stats["total_bytes"] / (1024 ** 2), 2),
        "total_requests": stats["total_requests"],
        "total_errors": stats["total_errors"],
        "uptime": uptime(),
        "timestamp": datetime.now().isoformat(),
        "hourly": dict(hourly_traffic),
        "recent_errors": list(error_logs)[-10:],
        "links_count": len(snap),
        "active_links": sum(1 for l in snap.values() if is_link_allowed(l)),
        "expired_links": sum(1 for l in snap.values() if is_link_expired(l)),
        "subs_count": len(SUBS)}

# ── Activity Logs ─────────────────────────────────────────────────────────────
@app.get("/api/activity")
async def get_activity(_=Depends(require_auth)):
    return {"logs": list(activity_logs)[-150:]}

# ── Live connections (with IP) ────────────────────────────────────────────────
# ── تشخیص نوع دستگاه از User-Agent ──────────────────────────────────────────
def detect_device(ua: str) -> str:
    """بر اساس User-Agent، مدل دستگاه را برمی‌گرداند."""
    if not ua:
        return "نامشخص"
    u = ua.lower()
    if "iphone" in u:
        m = re.search(r"iphone([0-9]+,[0-9]+)", u)
        return f"iPhone" + (f" {m.group(1)}" if m else "")
    if "ipad" in u: return "iPad"
    if "ipod" in u: return "iPod"
    if "mac os x" in u or "macintosh" in u:
        m = re.search(r"intel mac os x ([0-9_]+)", u)
        ver = m.group(1).replace("_", ".") if m else ""
        return f"Mac" + (f" {ver}" if ver else "")
    if "android" in u:
        m = re.search(r"android ([0-9.]+)", u)
        ver = m.group(1) if m else ""
        brand = "Samsung" if "sm-" in u or "samsung" in u else \
                "Xiaomi" if "redmi" in u or "mi " in u or "xiaomi" in u or "pocophone" in u or "m2004" in u or "2304" in u or "2305" in u or "2312" in u else \
                "Huawei" if "huawei" in u or "honor" in u else \
                "OnePlus" if "oneplus" in u else \
                "Oppo" if "oppo" in u or "cph" in u else \
                "Vivo" if "vivo" in u else \
                "Realme" if "realme" in u else \
                "Nokia" if "nokia" in u else \
                "Pixel" if "pixel" in u else "Android"
        return f"{brand}" + (f" Android {ver}" if ver else "")
    if "windows nt 10" in u: return "Windows 10/11"
    if "windows nt 6.3" in u: return "Windows 8.1"
    if "windows nt 6.1" in u: return "Windows 7"
    if "windows" in u: return "Windows PC"
    if "linux" in u and "android" not in u:
        if "ubuntu" in u: return "Ubuntu Linux"
        if "debian" in u: return "Debian Linux"
        if "fedora" in u: return "Fedora Linux"
        if "arch" in u: return "Arch Linux"
        return "Linux PC"
    if "cros" in u: return "Chromebook"
    if "playstation" in u: return "PlayStation"
    if "nintendo" in u: return "Nintendo"
    if "tv" in u or "smarttv" in u: return "Smart TV"
    if "mobile" in u: return "موبایل"
    return "نامشخص"


def ua_from_conn(c: dict) -> str:
    """User-Agent ذخیره‌شده روی یک رکورد اتصال (در صورت وجود)."""
    return c.get("user_agent", "") or c.get("ua", "")

@app.get("/api/connections")
async def get_connections(_=Depends(require_auth)):
    """
    خروجی این endpoint حالا بر اساس IP گروه‌بندی شده:
    هر آی‌پی فقط یک آیتم نمایش داده می‌شود، با جمع بایت‌های تمام سشن‌های
    باز روی همان آی‌پی و تعداد سشن‌های فعال آن آی‌پی.
    raw_count همچنان تعداد واقعی اتصالات باز (سشن‌های خام، مثلاً ۴۰ تا
    اتصال هم‌زمان یک موبایل) را برمی‌گرداند.
    """
    async with LINKS_LOCK:
        snap = dict(LINKS)

    grouped: dict[str, dict] = {}
    for conn_id, c in connections.items():
        ip = c.get("ip", "نامشخص")
        link = snap.get(c.get("uuid"))
        label = link.get("label") if link else "نامشخص"
        g = grouped.get(ip)
        if g is None:
            g = {
                "ip": ip,
                "sessions": 0,
                "bytes": 0,
                "labels": set(),
                "transports": set(),
                "first_connected_at": c.get("connected_at"),
                "last_connected_at": c.get("connected_at")}
            grouped[ip] = g
        g["sessions"] += 1
        g["bytes"] += c.get("bytes", 0)
        g["labels"].add(label)
        g["transports"].add(c.get("transport", "vless-ws"))
        ca = c.get("connected_at")
        if ca:
            if not g["first_connected_at"] or ca < g["first_connected_at"]:
                g["first_connected_at"] = ca
            if not g["last_connected_at"] or ca > g["last_connected_at"]:
                g["last_connected_at"] = ca

    # newest known destination per IP (site the client is connected to)
    dests: dict[str, str] = {}
    uas: dict[str, str] = {}
    for c in connections.values():
        d = c.get("dest")
        if d:
            dests[c.get("ip", "نامشخص")] = d
        ua = c.get("user_agent") or c.get("ua")
        if ua:
            uas[c.get("ip", "نامشخص")] = ua

    result = []
    for ip, g in grouped.items():
        result.append({
            "ip": ip,
            "sessions": g["sessions"],
            "labels": sorted(g["labels"]),
            "label": " · ".join(sorted(g["labels"])) if g["labels"] else "نامشخص",
            "transports": sorted(g["transports"]),
            "bytes": g["bytes"],
            "bytes_fmt": fmt_bytes(g["bytes"]),
            "connected_at": g["first_connected_at"],
            "last_connected_at": g["last_connected_at"],
            "dest": dests.get(ip, ""),
            "ua": uas.get(ip, ""),
            "device": detect_device(uas.get(ip, ""))})
    result.sort(key=lambda x: x.get("last_connected_at") or "", reverse=True)

    return {
        "connections": result,
        "count": len(result),          # تعداد آی‌پی‌های یکتا
        "raw_count": len(connections), # تعداد کل اتصالات باز (بدون گروه‌بندی)
    }

# ── Shared link create/delete helpers ────────────────────────────────────────
async def make_link(
    label: str = "لینک جدید",
    limit_bytes: int = 0,
    expires_at: str | None = None,
    note: str = "",
    sub_id: str | None = None,
    protocol: str = DEFAULT_PROTOCOL,
    fingerprint: str = DEFAULT_FINGERPRINT,
    alpn: str = "",
    port: int = DEFAULT_PORT,
    ip_limit: int = 0,
    speed_limit_bytes: int = 0,
    category_id: str | None = None,
) -> tuple[str, dict]:
    if protocol not in PROTOCOLS:
        protocol = DEFAULT_PROTOCOL
    fingerprint = (fingerprint or DEFAULT_FINGERPRINT).strip().lower()
    if fingerprint not in FINGERPRINTS:
        fingerprint = DEFAULT_FINGERPRINT
    if not (MIN_PORT <= port <= MAX_PORT):
        port = DEFAULT_PORT
    uid = generate_uuid()
    async with LINKS_LOCK:
        LINKS[uid] = {
            "label": (label or "لینک جدید").strip()[:60] or "لینک جدید",
            "limit_bytes": max(0, limit_bytes),
            "used_bytes": 0,
            "created_at": datetime.now().isoformat(),
            "active": True,
            "expires_at": expires_at,
            "note": (note or "").strip()[:200],
            "is_default": False,
            "sub_id": sub_id,
            "protocol": protocol,
            "fingerprint": fingerprint,
            "alpn": (alpn or "").strip()[:100],
            "port": port,
            "ip_limit": max(0, ip_limit),
            "speed_limit_bytes": max(0, speed_limit_bytes),
            "category_id": (category_id or "0").strip()[:64] or "0"}
    if sub_id:
        async with SUBS_LOCK:
            if sub_id in SUBS:
                ids = SUBS[sub_id].setdefault("link_ids", [])
                if uid not in ids:
                    ids.append(uid)
    asyncio.create_task(save_state())
    log_activity("link", f"کانفیگ «{LINKS[uid]['label']}» ساخته شد", "ok")
    return uid, LINKS[uid]

async def remove_link(uid: str) -> str | None:
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        label = LINKS[uid].get("label", uid)
        sub_id = LINKS[uid].get("sub_id")
        del LINKS[uid]
    if sub_id:
        async with SUBS_LOCK:
            if sub_id in SUBS:
                ids = SUBS[sub_id].get("link_ids", [])
                if uid in ids:
                    ids.remove(uid)
    await save_state()
    log_activity("link", f"کانفیگ «{label}» حذف شد", "err")
    return label

async def set_link_active(uid: str, active: bool) -> dict | None:
    async with LINKS_LOCK:
        if uid not in LINKS:
            return None
        LINKS[uid]["active"] = bool(active)
        label = LINKS[uid]["label"]
    log_activity("link", f"کانفیگ «{label}» {'فعال' if active else 'غیرفعال'} شد", "ok" if active else "warn")
    asyncio.create_task(save_state())
    return LINKS[uid]

# ── Sub-group helpers (shared by the web API) ───────────────────────────────
async def create_sub_group(name: str = "گروه جدید", desc: str = "", password: str = "") -> tuple[str, dict]:
    name = (name or "گروه جدید").strip()[:60]
    desc = (desc or "").strip()[:200]
    password = (password or "").strip()
    sub_id = generate_uuid()
    uuid_key = secrets.token_urlsafe(16)
    async with SUBS_LOCK:
        SUBS[sub_id] = {
            "name": name,
            "desc": desc,
            "password_hash": hash_password(password) if password else None,
            "uuid_key": uuid_key,
            "created_at": datetime.now().isoformat(),
            "link_ids": []}
    asyncio.create_task(save_state())
    log_activity("sub", f"گروه «{name}» ساخته شد", "ok")
    return sub_id, SUBS[sub_id]

async def add_sub_usage(sub_id: str, bytes_used: int) -> None:
    """افزودن مصرف به ساب گروه (حجم مشترک)."""
    if bytes_used <= 0:
        return
    async with SUBS_LOCK:
        sub = SUBS.get(sub_id)
        if sub is None:
            return
        sub["total_used_bytes"] = sub.get("total_used_bytes", 0) + bytes_used
    asyncio.create_task(save_state())

async def set_link_sub(uid: str, sub_id: str | None) -> bool:
    """یک کانفیگ رو به یک گروه ساب اضافه/منتقل می‌کنه؛ با sub_id=None از گروه فعلیش خارجش می‌کنه."""
    async with LINKS_LOCK:
        if uid not in LINKS:
            return False
        old_sub = LINKS[uid].get("sub_id")
        label = LINKS[uid].get("label", uid)
    if sub_id is not None:
        async with SUBS_LOCK:
            if sub_id not in SUBS:
                return False
    async with SUBS_LOCK:
        if old_sub and old_sub in SUBS:
            ids = SUBS[old_sub].get("link_ids", [])
            if uid in ids:
                ids.remove(uid)
        if sub_id and sub_id in SUBS:
            ids = SUBS[sub_id].setdefault("link_ids", [])
            if uid not in ids:
                ids.append(uid)
    async with LINKS_LOCK:
        if uid in LINKS:
            LINKS[uid]["sub_id"] = sub_id
    asyncio.create_task(save_state())
    log_activity("link", f"کانفیگ «{label}» {'به گروه اضافه شد' if sub_id else 'از گروه خارج شد'}", "info")
    return True

async def remove_sub_group(sub_id: str) -> str | None:
    async with SUBS_LOCK:
        if sub_id not in SUBS:
            return None
        name = SUBS[sub_id].get("name", sub_id)
        del SUBS[sub_id]
    async with LINKS_LOCK:
        for link in LINKS.values():
            if link.get("sub_id") == sub_id:
                link["sub_id"] = None
    asyncio.create_task(save_state())
    log_activity("sub", f"گروه «{name}» حذف شد", "warn")
    return name

# ── Link Management ───────────────────────────────────────────────────────────
@app.post("/api/links")
async def create_link(request: Request, _=Depends(require_auth)):
    body = await request.json()
    lv = float(body.get("limit_value") or 0)
    lu = body.get("limit_unit") or "GB"
    limit_bytes = 0 if lv <= 0 else parse_size_to_bytes(lv, lu)
    exp_days = int(body.get("expires_days") or 0)
    expires_at = (datetime.now() + timedelta(days=exp_days)).isoformat() if exp_days > 0 else None
    try:
        port = int(body.get("port") or DEFAULT_PORT)
    except (TypeError, ValueError):
        port = DEFAULT_PORT
    try:
        ip_limit = int(body.get("ip_limit") or 0)
    except (TypeError, ValueError):
        ip_limit = 0

    sv = float(body.get("speed_limit_value") or 0)
    su = body.get("speed_limit_unit") or "MBIT"
    speed_limit_bytes = 0 if sv <= 0 else parse_speed_to_bytes(sv, su)

    uid, link = await make_link(
        label=body.get("label") or "لینک جدید",
        limit_bytes=limit_bytes,
        expires_at=expires_at,
        note=body.get("note") or "",
        sub_id=body.get("sub_id") or None,
        protocol=body.get("protocol") or DEFAULT_PROTOCOL,
        fingerprint=body.get("fingerprint") or DEFAULT_FINGERPRINT,
        alpn=body.get("alpn") or "",
        port=port,
        ip_limit=ip_limit,
        speed_limit_bytes=speed_limit_bytes,
        category_id=body.get("category_id"),
    )

    host = get_host(request)
    return {
        "uuid": uid,
        **link,
        "expired": False,
        "vless_link": vless_link_for_link(link, uid, host),
        "sub_url": f"https://{host}/sub/{uid}"}

@app.get("/api/links")
async def list_links(request: Request, _=Depends(require_auth)):
    host = get_host(request)
    async with LINKS_LOCK:
        snap = dict(LINKS)
    async with CATEGORIES_LOCK:
        cats = dict(CATEGORIES)
    result = []
    for uid, d in snap.items():
        proto = d.get("protocol", DEFAULT_PROTOCOL)
        cid = str(d.get("category_id") or "0")
        cat = cats.get(cid)
        item = dict(d)
        item["category"] = {"id": cid, "name": cat.get("name") if cat else "عمومی",
                            "color": cat.get("color") if cat else "#10B981"}
        result.append({
            "uuid": uid,
            **item,
            "protocol": proto,
            "expired": is_link_expired(d),
            "vless_link": vless_link_for_link(d, uid, host),
            "sub_url": f"https://{host}/sub/{uid}",
            "connected_ips": len(unique_ips_for_uuid(uid))})
    result.sort(key=lambda x: x["created_at"], reverse=True)
    return {"links": result}

@app.patch("/api/links/{uid}")
async def update_link(uid: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    async with LINKS_LOCK:
        if uid not in LINKS:
            raise HTTPException(status_code=404, detail="link not found")
        link = LINKS[uid]
        old_sub = link.get("sub_id")
        label = link.get("label")
        if "active" in body:
            link["active"] = bool(body["active"])
            log_activity("link", f"کانفیگ «{label}» {'فعال' if link['active'] else 'غیرفعال'} شد", "ok" if link["active"] else "warn")
        if "label" in body:
            link["label"] = str(body["label"])[:60]
        if "note" in body:
            link["note"] = str(body["note"])[:200]
        if "category_id" in body:
            link["category_id"] = (str(body.get("category_id") or "0")).strip()[:64] or "0"
        if body.get("reset_usage"):
            link["used_bytes"] = 0
            log_activity("link", f"مصرف کانفیگ «{label}» ریست شد", "info")
        if "limit_value" in body:
            lv = float(body.get("limit_value") or 0)
            lu = body.get("limit_unit") or "GB"
            link["limit_bytes"] = 0 if lv <= 0 else parse_size_to_bytes(lv, lu)
        if "expires_days" in body:
            ed = int(body["expires_days"] or 0)
            link["expires_at"] = (datetime.now() + timedelta(days=ed)).isoformat() if ed > 0 else None
        if "fingerprint" in body:
            fp = str(body.get("fingerprint") or DEFAULT_FINGERPRINT).strip().lower()
            link["fingerprint"] = fp if fp in FINGERPRINTS else DEFAULT_FINGERPRINT
        if "alpn" in body:
            link["alpn"] = str(body.get("alpn") or "").strip()[:100]
        if "port" in body:
            try:
                p = int(body.get("port") or DEFAULT_PORT)
            except (TypeError, ValueError):
                p = DEFAULT_PORT
            link["port"] = p if (MIN_PORT <= p <= MAX_PORT) else DEFAULT_PORT
        if "ip_limit" in body:
            try:
                il = int(body.get("ip_limit") or 0)
            except (TypeError, ValueError):
                il = 0
            link["ip_limit"] = max(0, il)
        if "speed_limit_value" in body:
            sv = float(body.get("speed_limit_value") or 0)
            su = body.get("speed_limit_unit") or "MBIT"
            link["speed_limit_bytes"] = 0 if sv <= 0 else parse_speed_to_bytes(sv, su)
            from speed_limit import reset_bucket
            reset_bucket(uid)
        if any(k in body for k in ("label", "note", "category_id", "limit_value", "expires_days", "fingerprint", "alpn", "port", "ip_limit", "speed_limit_value")):
            log_activity("link", f"کانفیگ «{link['label']}» ویرایش شد", "info")
        new_sub = body.get("sub_id", "UNCHANGED")
        if new_sub != "UNCHANGED":
            link["sub_id"] = new_sub or None

    if new_sub != "UNCHANGED":
        async with SUBS_LOCK:
            if old_sub and old_sub in SUBS:
                ids = SUBS[old_sub].get("link_ids", [])
                if uid in ids:
                    ids.remove(uid)
            if new_sub and new_sub in SUBS:
                ids = SUBS[new_sub].setdefault("link_ids", [])
                if uid not in ids:
                    ids.append(uid)

    asyncio.create_task(save_state())
    return {"ok": True}

@app.delete("/api/links/{uid}")
async def delete_link(uid: str, _=Depends(require_auth)):
    label = await remove_link(uid)
    if label is None:
        raise HTTPException(status_code=404, detail="link not found")
    return {"ok": True, "deleted": uid}

# ══════════════════════════════════════════════════════════════════════════════
# Security — لغو نشست‌های قبلی
# ══════════════════════════════════════════════════════════════════════════════
@app.get("/api/sessions")
async def list_sessions(request: Request, _=Depends(require_auth)):
    cur = request.cookies.get(SESSION_COOKIE)
    now = time.time()
    async with SESSIONS_LOCK:
        items = []
        for t, sess in SESSIONS.items():
            if isinstance(sess, dict):
                if sess.get("expires_at", 0) <= now:
                    continue
                items.append({
                    "token": t[:10] + "…", "current": t == cur,
                    "login_at": sess.get("created_at"),
                    "ip": sess.get("ip") or "",
                    "device": sess.get("device") or "",
                    "ua": sess.get("ua") or "",
                    "expires_in_hours": round((sess.get("expires_at", now) - now) / 3600, 1)})
            else:
                if sess > now:
                    items.append({"token": t[:10] + "…", "current": t == cur,
                                  "login_at": None, "ip": "", "device": "", "ua": "",
                                  "expires_in_hours": round((sess - now) / 3600, 1)})
    items.sort(key=lambda s: (s.get("login_at") or 0), reverse=True)
    return {"sessions": items, "count": len(items)}

@app.post("/api/security/revoke-other-sessions")
async def revoke_other_sessions(request: Request, _=Depends(require_auth)):
    cur = request.cookies.get(SESSION_COOKIE)
    removed = 0
    async with SESSIONS_LOCK:
        stale = [t for t in list(SESSIONS.keys()) if t != cur]
        for t in stale:
            SESSIONS.pop(t, None)
            removed += 1
    log_activity("auth", f"نشست‌های قبلی حساب لغو شد ({removed} مورد)", "warn")
    return {"ok": True, "revoked": removed}

# ══════════════════════════════════════════════════════════════════════════════
# Categories (دسته‌بندی کانفیگ‌ها)
# ══════════════════════════════════════════════════════════════════════════════
CAT_COLORS = ("#10B981", "#3B82F6", "#F59E0B", "#EF4444", "#8B5CF6", "#EC4899", "#14B8A6", "#F97316")

@app.get("/api/categories")
async def list_categories(_=Depends(require_auth)):
    async with CATEGORIES_LOCK:
        snap = dict(CATEGORIES)
    async with LINKS_LOCK:
        link_count = {}
        for d in LINKS.values():
            cid = str(d.get("category_id") or "0")
            link_count[cid] = link_count.get(cid, 0) + 1
    out = []
    for cid, c in snap.items():
        x = dict(c); x["id"] = cid
        x["links_count"] = link_count.get(cid, 0)
        out.append(x)
    out.sort(key=lambda c: c.get("number", 0))
    return {"categories": out}

@app.post("/api/categories")
async def create_category(request: Request, _=Depends(require_auth)):
    body = await request.json()
    name = str(body.get("name") or "").strip()
    if not name:
        raise HTTPException(status_code=400, detail="نام دسته الزامی است")
    cid = generate_uuid()
    async with CATEGORIES_LOCK:
        number = max([c.get("number", 0) for c in CATEGORIES.values()], default=0) + 1
        CATEGORIES[cid] = {"name": name[:40],
                           "color": str(body.get("color") or "")[:7] or CAT_COLORS[number % len(CAT_COLORS)],
                           "number": number}
    asyncio.create_task(save_state())
    log_activity("system", f"دسته‌بندی «{name}» ساخته شد", "ok")
    return {"ok": True, "id": cid}

@app.patch("/api/categories/{cid}")
async def update_category(cid: str, request: Request, _=Depends(require_auth)):
    body = await request.json()
    async with CATEGORIES_LOCK:
        if cid not in CATEGORIES:
            raise HTTPException(status_code=404, detail="category not found")
        if "name" in body and str(body["name"]).strip():
            CATEGORIES[cid]["name"] = str(body["name"]).strip()[:40]
        if "color" in body:
            CATEGORIES[cid]["color"] = str(body["color"])[:7]
        if "number" in body:
            try:
                CATEGORIES[cid]["number"] = int(body["number"])
            except (TypeError, ValueError):
                pass
        name = CATEGORIES[cid].get("name")
    asyncio.create_task(save_state())
    log_activity("system", f"دسته‌بندی «{name}» ویرایش شد", "info")
    return {"ok": True}

@app.delete("/api/categories/{cid}")
async def delete_category(cid: str, _=Depends(require_auth)):
    async with CATEGORIES_LOCK:
        c = CATEGORIES.pop(cid, None)
    if c is None:
        raise HTTPException(status_code=404, detail="category not found")
    async with LINKS_LOCK:
        for d in LINKS.values():
            if str(d.get("category_id") or "0") == cid:
                d["category_id"] = "0"
    asyncio.create_task(save_state())
    log_activity("system", f"دسته‌بندی «{c.get('name')}» حذف شد", "warn")
    return {"ok": True}

# ══════════════════════════════════════════════════════════════════════════════
# VLESS Relay — جدا شده به relay_vless.py (دست نخورده)
# ══════════════════════════════════════════════════════════════════════════════

from relay_vless import (
    websocket_tunnel,
)

app.add_api_websocket_route("/ws/{uuid}", websocket_tunnel)

# ══════════════════════════════════════════════════════════════════════════════
# XHTTP — Siz10a XHTTP Ultra (ترابرد جدید، جدا از VLESS/WS، هر ۳ مد)
# ══════════════════════════════════════════════════════════════════════════════
from xhttp_siz10 import router as xhttp_router

app.include_router(xhttp_router)

# ══════════════════════════════════════════════════════════════════════════════
# ── HTTP Proxy ────────────────────────────────────────────────────────────────
_HOP = {"connection","keep-alive","proxy-authenticate","proxy-authorization",
        "te","trailers","transfer-encoding","upgrade","content-encoding","content-length"}
MAX_PROXY_BODY = 8 * 1024 * 1024
MAX_PROXY_RESPONSE = 32 * 1024 * 1024
ENABLE_HTTP_PROXY = os.environ.get("ENABLE_HTTP_PROXY", "true").lower() in {"1", "true", "yes"}


def _proxy_destination_allowed(target_url: str) -> bool:
    try:
        parts = urlsplit(target_url)
        if parts.scheme not in {"http", "https"} or not parts.hostname:
            return False
        host = parts.hostname
        try:
            addresses = {ipaddress.ip_address(host)}
        except ValueError:
            addresses = {ipaddress.ip_address(item[4][0]) for item in socket.getaddrinfo(host, parts.port or 443, type=socket.SOCK_STREAM)}
        return all(not (addr.is_private or addr.is_loopback or addr.is_link_local or addr.is_multicast or addr.is_reserved or addr.is_unspecified) for addr in addresses)
    except (ValueError, OSError, socket.gaierror):
        return False

@app.api_route("/proxy/{target_url:path}", methods=["GET","POST","PUT","DELETE","PATCH","HEAD","OPTIONS"])
async def http_proxy(target_url: str, request: Request, _=Depends(require_auth)):
    if not ENABLE_HTTP_PROXY:
        raise HTTPException(status_code=404, detail="proxy disabled")
    if not target_url.startswith(("http://", "https://")):
        target_url = "https://" + target_url
    if len(target_url) > 2048 or not _proxy_destination_allowed(target_url):
        raise HTTPException(status_code=403, detail="destination is not allowed")
    try:
        body = await request.body()
        if len(body) > MAX_PROXY_BODY:
            raise HTTPException(status_code=413, detail="request body is too large")
        headers = {k: v for k, v in request.headers.items() if k.lower() not in _HOP and k.lower() != "host"}
        resp = await http_client.request(method=request.method, url=target_url, headers=headers, content=body)
        content_length = int(resp.headers.get("content-length", "0") or 0)
        if content_length > MAX_PROXY_RESPONSE:
            raise HTTPException(status_code=413, detail="response is too large")
        content = resp.content
        if len(content) > MAX_PROXY_RESPONSE:
            raise HTTPException(status_code=413, detail="response is too large")
        stats["total_bytes"] += len(content)
        stats["total_requests"] += 1
        hourly_traffic[now_ir().strftime("%H:00")] += len(content)
        return Response(content=content, status_code=resp.status_code,
                        headers={k: v for k, v in resp.headers.items() if k.lower() not in _HOP})
    except HTTPException:
        raise
    except Exception as exc:
        stats["total_errors"] += 1
        error_logs.append({"error": type(exc).__name__, "time": datetime.now().isoformat()})
        raise HTTPException(status_code=502, detail="proxy request failed")

# ── Public sub page ───────────────────────────────────────────────────────────
@app.get("/p/{uuid_key}", response_class=HTMLResponse)
async def public_sub_page(uuid_key: str, request: Request):
    from pages import get_public_page_html
    async with SUBS_LOCK:
        sub = next(({"sub_id": sid, **s} for sid, s in SUBS.items() if s.get("uuid_key") == uuid_key), None)
    if not sub:
        return HTMLResponse("<h2 style='font-family:sans-serif;padding:40px'>گروه پیدا نشد</h2>", status_code=404)
    return HTMLResponse(content=get_public_page_html(uuid_key))

@app.get("/api/public/sub/{uuid_key}")
async def public_sub_data(uuid_key: str, request: Request):
    async with SUBS_LOCK:
        sub_entry = next(((sid, s) for sid, s in SUBS.items() if s.get("uuid_key") == uuid_key), None)
    if not sub_entry:
        raise HTTPException(status_code=404, detail="not found")
    sub_id, sub = sub_entry

    has_pw = sub.get("password_hash") is not None
    if has_pw:
        pw = request.query_params.get("pw", "")
        if not verify_password(pw, sub["password_hash"]):
            return JSONResponse({"locked": True, "name": sub["name"]})

    host = get_host(request)
    link_ids = sub.get("link_ids", [])
    async with LINKS_LOCK:
        snap = dict(LINKS)

    links_out = []
    active_conns = 0
    for lid in link_ids:
        link = snap.get(lid)
        if not link:
            continue
        allowed = is_link_allowed(link)
        conn_count = sum(1 for c in connections.values() if c.get("uuid") == lid)
        active_conns += conn_count
        proto = link.get("protocol", DEFAULT_PROTOCOL)
        links_out.append({
            "uuid": lid,
            "label": link["label"],
            "active": allowed,
            "protocol": proto,
            "used_bytes": link.get("used_bytes", 0),
            "used_fmt": fmt_bytes(link.get("used_bytes", 0)),
            "limit_bytes": link.get("limit_bytes", 0),
            "limit_fmt": "∞" if link.get("limit_bytes", 0) == 0 else fmt_bytes(link["limit_bytes"]),
            "expires_at": link.get("expires_at"),
            "vless_link": vless_link_for_link(link, lid, host),
            "sub_url": f"https://{host}/sub/{lid}",
            "connections": conn_count,
            "ip_limit": link.get("ip_limit", 0),
            "speed_limit_bytes": link.get("speed_limit_bytes", 0)})

    total_used = sum(l["used_bytes"] for l in links_out)
    sub_used = sub.get("total_used_bytes", total_used)
    total_limit = sub.get("total_limit_bytes", 0)
    # Expiry: the group-level total_days drives reaper/auto-expiry. Derive the exact
    # expiry date from the stored matrix so the public page shows the real deadline.
    total_days = int(sub.get("total_days") or 0)
    group_expires_at = sub.get("expires_at")
    if not group_expires_at and total_days > 0:
        created_iso = sub.get("created_at")
        if created_iso:
            try:
                group_expires_at = (datetime.fromisoformat(created_iso) + timedelta(days=total_days)).isoformat()
            except (ValueError, TypeError):
                group_expires_at = None
    days_left = None
    if group_expires_at:
        try:
            days_left = max(0, (datetime.fromisoformat(group_expires_at) - datetime.now()).days)
        except (ValueError, TypeError):
            days_left = None
    return {
        "locked": False,
        "name": sub["name"],
        "desc": sub.get("desc", ""),
        "sub_url": f"https://{host}/sub-group/{uuid_key}",
        "active_connections": active_conns,
        "total_limit_bytes": total_limit,
        "total_limit_fmt": "نامحدود" if total_limit == 0 else fmt_bytes(total_limit),
        "total_used_bytes": sub_used,
        "total_used_fmt": fmt_bytes(sub_used),
        "expires_at": group_expires_at,
        "days_left": days_left,
        "links": links_out}

# ── HTML Pages (login + dashboard) ───────────────────────────────────────────
from pages import DASHBOARD_HTML, LOGIN_HTML


@app.get("/login", response_class=HTMLResponse)
async def login_page(request: Request):
    if await is_valid_session(request.cookies.get(SESSION_COOKIE)):
        return RedirectResponse(url="/dashboard")
    captcha_id = secrets.token_urlsafe(18)
    alphabet = string.ascii_uppercase + string.digits
    captcha_code = "".join(secrets.choice(alphabet) for _ in range(5))
    LOGIN_CAPTCHAS[captcha_id] = (captcha_code, time.time() + 300)
    return HTMLResponse(content=LOGIN_HTML.replace("__CAPTCHA_ID__", captcha_id).replace("__CAPTCHA_CODE__", captcha_code))

@app.get("/dashboard", response_class=HTMLResponse)
async def dashboard(request: Request):
    if not await is_valid_session(request.cookies.get(SESSION_COOKIE)):
        return RedirectResponse(url="/login")
    await ensure_default_link()
    return HTMLResponse(content=DASHBOARD_HTML)

@app.get("/test-ws", response_class=HTMLResponse)
async def test_ws_redirect():
    return HTMLResponse(content="<script>location.href='/dashboard'</script>")

if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=CONFIG["port"], log_level="info", workers=1)
