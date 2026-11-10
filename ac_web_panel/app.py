# -*- coding: utf-8 -*-
"""AP - Alternative Assetto Corsa Hosting Panel v5.0.
Регистрация с подтверждением, профили игроков с аватарками и SteamID,
статистика (время, трассы, машины, рекорды), лидерборд, редактор сервера.
"""
import base64
import json
import os
import re
import shutil
import socket
import struct
import subprocess
import tempfile
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import time
import urllib.error
import urllib.request
import zipfile
from urllib.parse import quote
from datetime import datetime
from functools import wraps

from flask import Flask, Response, flash, jsonify, redirect, render_template, request, send_file, session, url_for
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

app = Flask(__name__)
app.secret_key = "alternative-panel-v5"
app.config["MAX_CONTENT_LENGTH"] = 10 * 1024 * 1024 * 1024  # max upload 10 GB

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
SERVER_DIR = "/root/ac_server"
CFG_PATH = os.path.join(SERVER_DIR, "cfg", "server_cfg.ini")
ENTRY_PATH = os.path.join(SERVER_DIR, "cfg", "entry_list.ini")
CONTENT_CARS = os.path.join(SERVER_DIR, "content", "cars")
CONTENT_TRACKS = os.path.join(SERVER_DIR, "content", "tracks")
RESULTS_DIR = os.path.join(SERVER_DIR, "results")
LOG_PATH = os.path.join(SERVER_DIR, "server.log")
BLACKLIST_PATH = os.path.join(SERVER_DIR, "cfg", "blacklist.txt")
WELCOME_PATHS = [os.path.join(SERVER_DIR, "cfg", "welcome.txt"),
                 os.path.join(SERVER_DIR, "welcome.txt")]
PREVIEWS_DIR = os.path.join(BASE_DIR, "previews")  # свои превью: cars/<model>[/<skin>].jpg, tracks/<id>.jpg
USERS_PATH = os.path.join(BASE_DIR, "users.json")
STATS_PATH = os.path.join(BASE_DIR, "driver_stats.json")


# ---------- несколько игровых серверов ----------
SERVER_INSTANCES = (
    {"id": "main", "label": "Главный", "suffix": "", "screen": "ac_main", "proc": "acServer_main"},
    {"id": "pub1", "label": "Паблик 1", "suffix": "_pub1", "screen": "ac_pub1", "proc": "acServer_pub1"},
    {"id": "pub2", "label": "Паблик 2", "suffix": "_pub2", "screen": "ac_pub2", "proc": "acServer_pub2"},
)
PUB_PORTS = {"pub1": {"tcp": "9601", "udp": "9601", "http": "8082"},
             "pub2": {"tcp": "9602", "udp": "9602", "http": "8083"}}


def valid_srv(srv):
    return srv if any(x["id"] == srv for x in SERVER_INSTANCES) else "main"


def get_server(srv):
    srv = valid_srv(srv)
    for x in SERVER_INSTANCES:
        if x["id"] == srv:
            return x
    return SERVER_INSTANCES[0]


def srv_dir(srv="main"):
    return SERVER_DIR + get_server(srv)["suffix"]


def srv_cfg(srv="main"):
    return os.path.join(srv_dir(srv), "cfg", "server_cfg.ini")


def srv_entry(srv="main"):
    return os.path.join(srv_dir(srv), "cfg", "entry_list.ini")


def srv_log(srv="main"):
    return os.path.join(srv_dir(srv), "server.log")


def srv_results(srv="main"):
    return os.path.join(srv_dir(srv), "results")


def srv_blacklist(srv="main"):
    return os.path.join(srv_dir(srv), "cfg", "blacklist.txt")


def srv_welcome_paths(srv="main"):
    d = srv_dir(srv)
    return [os.path.join(d, "cfg", "welcome.txt"), os.path.join(d, "welcome.txt")]


def srv_exists(srv):
    return os.path.isfile(srv_cfg(srv))


def pub_ready(srv):
    """Паблик полностью собран: конфиг, слоты, ссылки, results."""
    d = srv_dir(srv)
    return (os.path.isfile(srv_cfg(srv)) and os.path.isfile(srv_entry(srv))
            and os.path.lexists(os.path.join(d, "acServer"))
            and os.path.lexists(os.path.join(d, "content"))
            and os.path.isdir(os.path.join(d, "results")))


# ---------- CM Server Details: описания для Content Manager ----------
CM_SIDECAR_PORTS = {"main": 8091, "pub1": 8092, "pub2": 8093}
CM_SIDECAR_STATUS = {}
CM_SIDECAR_SERVERS = {}


def cm_desc_path(srv="main"):
    return os.path.join(srv_dir(srv), "cm_description.txt")


def read_cmdesc(srv="main"):
    try:
        with open(cm_desc_path(srv), "r", encoding="utf-8") as f:
            return f.read()
    except OSError:
        return ""


def cm_suffix(srv):
    return " \u2139" + str(CM_SIDECAR_PORTS.get(valid_srv(srv), 8091))


def strip_cm_suffix(name):
    return re.sub(r"\s*\u2139\d+\s*$", "", name or "")


_CM_IP_CACHE = {"ip": None}


def _cm_public_ip():
    if _CM_IP_CACHE["ip"] is None:
        try:
            sk = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            sk.connect(("8.8.8.8", 80))
            _CM_IP_CACHE["ip"] = sk.getsockname()[0]
            sk.close()
        except Exception:
            _CM_IP_CACHE["ip"] = ""
    return _CM_IP_CACHE["ip"] or ""


def _cm_num(v, default=0):
    try:
        return int(float(str(v).strip().replace(",", ".")))
    except (TypeError, ValueError, AttributeError):
        return default


_CM_GEO_CACHE = {"at": 0.0, "country": "", "code": "", "city": "", "ip": ""}
_CM_GEO_TTL = 6 * 3600.0
_CM_GEO_BUSY = {"busy": False}


def _cm_geo_parse(obj):
    """Чистая функция: нормализует ответ ip-api.com / ipinfo.io. Тестируема."""
    out = {"country": "", "code": "", "city": "", "ip": ""}
    if not isinstance(obj, dict):
        return out
    if obj.get("status") == "success" or "countryCode" in obj or "country" in obj:
        out["country"] = str(obj.get("country") or "")
        out["code"] = str(obj.get("countryCode") or obj.get("country_code") or "")
        if not out["code"] and len(out["country"]) == 2:
            out["code"] = out["country"].upper()
        out["city"] = str(obj.get("city") or "")
        out["ip"] = str(obj.get("query") or obj.get("ip") or "")
    return out


def _cm_geo_refresh():
    """Блокирующее обновление geo-кэша. Вызывать только из фонового потока."""
    data = {"country": "", "code": "", "city": "", "ip": ""}
    try:
        obj, err, _m = _http_json(
            "http://ip-api.com/json/?fields=status,country,countryCode,city,query", timeout=4)
        if err is None:
            data = _cm_geo_parse(obj)
    except Exception:
        pass
    if not data.get("code"):
        try:
            obj2, err2, _m2 = _http_json("https://ipinfo.io/json", timeout=5)
            if err2 is None:
                d2 = _cm_geo_parse(obj2)
                if d2.get("code"):
                    data = d2
        except Exception:
            pass
    if data.get("code"):
        data["at"] = time.time()
        _CM_GEO_CACHE.update(data)
    return _CM_GEO_CACHE


def _cm_geo_ensure():
    """Geo-кэш, не блокирует запросы: обновление — в фоне, чтение — мгновенно."""
    try:
        stale = time.time() - float(_CM_GEO_CACHE.get("at") or 0) > _CM_GEO_TTL
        if stale and not _CM_GEO_BUSY["busy"]:
            _CM_GEO_BUSY["busy"] = True

            def _run():
                try:
                    _cm_geo_refresh()
                finally:
                    _CM_GEO_BUSY["busy"] = False

            threading.Thread(target=_run, daemon=True, name="cm-geo-refresh").start()
    except Exception:
        pass
    return _CM_GEO_CACHE


_CM_PING_SESSION_RE = re.compile(r"ping\?session=(\d+)", re.IGNORECASE)


def _cm_session_from_text(text):
    """Чистая функция: номер сессии из последнего lobby-пинга в тексте лога."""
    try:
        ms = _CM_PING_SESSION_RE.findall(text or "")
        if ms:
            n = int(ms[-1])
            if 1 <= n <= 7:
                return n
    except (TypeError, ValueError):
        pass
    return None


def _cm_session_type(srv, live_session=0):
    """Текущая сессия 1/2/3: свежий lobby-пинг > живой /INFO > практика."""
    try:
        p = srv_log(srv)
        if os.path.exists(p):
            with open(p, "rb") as f:
                try:
                    f.seek(-40960, os.SEEK_END)
                except OSError:
                    f.seek(0)
                n = _cm_session_from_text(f.read().decode("utf-8", "ignore"))
                if n:
                    return n
    except Exception:
        pass
    try:
        n = int(live_session or 0)
        if 1 <= n <= 7:
            return n
    except (TypeError, ValueError):
        pass
    return 1


def _cm_detail_cars(srv, pickup_open=True):
    """Слоты entry_list как DetailResponseCar (как у настоящего AssettoServer)."""
    out = []
    try:
        for e in parse_entry_list(srv):
            model = (e.get("MODEL") or "").strip()
            if not model:
                continue
            out.append({
                "Model": model,
                "Skin": (e.get("SKIN") or "").strip(),
                "IsEntryList": bool(pickup_open),
                "DriverName": None,
                "DriverTeam": None,
                "DriverNation": None,
                "IsConnected": False,
                "ID": None,
            })
    except Exception:
        pass
    return out


_CM_JSON_RE = re.compile(r"^/JSON\|(\d+)$")


def _cm_route(path):
    """Маршрут сайдкара -> (route, arg). route: details|info|json|None."""
    p = (path or "").split("?")[0]
    if p.rstrip("/") == "/api/details":
        return ("details", None)
    if p.rstrip("/") == "/INFO":
        return ("info", None)
    m = _CM_JSON_RE.match(p)
    if m:
        return ("json", m.group(1))
    return (None, None)


def _http_bytes(url, timeout=5):
    """Сырой GET -> (bytes|None, status, ctype). Для прокси /JSON (байт-в-байт)."""
    try:
        with urllib.request.urlopen(url, timeout=timeout) as r:
            raw = r.read() or b""
            try:
                st = int(getattr(r, "status", 0) or 0)
            except (TypeError, ValueError):
                st = 0
            try:
                ct = (r.headers.get("Content-Type") or "")[:80]
            except Exception:
                ct = ""
            return raw, st, ct
    except Exception:
        return None, 0, ""


def build_cm_details(srv):
    srv = valid_srv(srv)
    lines = read_cfg_lines(srv)
    g = lambda k, d="": get_cfg_value(lines, "SERVER", k, d)
    gw = lambda k, d="": get_cfg_value(lines, "WEATHER_0", k, d)
    gd = lambda k, d="": get_cfg_value(lines, "DYNAMIC_TRACK", k, d)
    try:
        http_port = g("HTTP_PORT", "8081") or "8081"
        info, _err, _meta = _http_json("http://127.0.0.1:%s/INFO" % http_port)
        live = info if isinstance(info, dict) else {}
    except Exception:
        live = {}
    try:
        amb = float((gw("BASE_TEMPERATURE_AMBIENT", "20") or "20").strip().replace(",", "."))
    except ValueError:
        amb = 20.0
    try:
        off = float((gw("BASE_TEMPERATURE_ROAD", "5") or "5").strip().replace(",", "."))
    except ValueError:
        off = 5.0
    cars = [c.strip() for c in re.split(r"[;,]", g("CARS", "")) if c.strip()]
    password = g("PASSWORD", "")
    timeleft = _cm_num(live.get("timeleft", 0)) // 1000  # kunos шлёт мс, в details нужны секунды
    tod = live.get("timeofday")
    geo = _cm_geo_ensure()
    pickup_open = (live.get("pickup", g("PICKUP_MODE_ENABLED", "1") == "1") not in (0, False))
    d = {
        "cars": live.get("cars") or cars,
        "clients": _cm_num(live.get("clients", 0)),
        "cport": _cm_num(live.get("cport") or g("HTTP_PORT", "8081")),
        "durations": live.get("durations") or [],
        "extra": bool(_cm_num(live.get("extra", 0))),
        "inverted": _cm_num(live.get("inverted", 0)),
        "ip": live.get("ip") or geo.get("ip") or _cm_public_ip(),
        "maxclients": _cm_num(live.get("maxclients") or g("MAX_CLIENTS", "12")),
        "name": strip_cm_suffix(live.get("name") or g("NAME", "")),
        "pass": bool(live.get("pass", bool(password))),
        "pickup": pickup_open,
        "pit": bool(live.get("pit", False)),
        "port": _cm_num(live.get("port") or g("UDP_PORT", "9600")),
        "session": _cm_session_type(srv, live.get("session", 0)),
        "sessiontypes": live.get("sessiontypes") or [],
        "timed": bool(live.get("timed", False)),
        "timeleft": timeleft,
        "timeofday": _cm_num(tod if tod is not None else g("SUN_ANGLE", "16")),
        "timestamp": 0,
        "tport": _cm_num(live.get("tport") or g("TCP_PORT", "9600")),
        "track": live.get("track") or g("TRACK", ""),
        "players": {"Cars": _cm_detail_cars(srv, pickup_open)},
        "until": int(time.time()) + timeleft,
        "trackBase": g("TRACK", ""),
        "assists": {
            "absState": _cm_num(g("ABS_ALLOWED", "1")),
            "tcState": _cm_num(g("TC_ALLOWED", "1")),
            "fuelRate": _cm_num(g("FUEL_RATE", "100")),
            "damageMultiplier": _cm_num(g("DAMAGE_MULTIPLIER", "100")),
            "tyreWearRate": _cm_num(g("TYRE_WEAR_RATE", "100")),
            "allowedTyresOut": _cm_num(g("ALLOWED_TYRES_OUT", "-1")),
            "stabilityAllowed": g("STABILITY_ALLOWED", "0") == "1",
            "autoclutchAllowed": g("AUTOCLUTCH_ALLOWED", "0") == "1",
            "tyreBlanketsAllowed": g("TYRE_BLANKETS_ALLOWED", "0") == "1",
            "forceVirtualMirror": g("FORCE_VIRTUAL_MIRROR", "0") == "1",
        },
        "wrappedPort": CM_SIDECAR_PORTS[srv],
        "ambientTemperature": amb,
        "roadTemperature": amb + off,
        "currentWeatherId": gw("GRAPHICS", "3_clear") or "3_clear",
        "windSpeed": _cm_num(gw("WIND_BASE_SPEED_MIN", "0")),
        "windDirection": _cm_num(gw("WIND_BASE_DIRECTION", "0")),
        "description": read_cmdesc(srv),
        "grip": float(_cm_num(gd("SESSION_START", "97"))),
        "gripTransfer": 0,
        "frequency": 10,
        "content": None,
        "features": [],
        "loadingImageUrl": None,
        "extensions": {},
        "l": False,
        "json": None,
    }
    if geo.get("code"):
        d["country"] = [geo.get("country") or geo.get("code"), geo.get("code")]
    d["city"] = geo.get("city") or None
    return d


class _CMDetailsHandler(BaseHTTPRequestHandler):
    srv = "main"

    def log_message(self, *a):
        pass

    def _send_json(self, obj, status=200):
        try:
            body = json.dumps(obj, ensure_ascii=False).encode("utf-8")
        except Exception as e:
            status = 500
            body = ('{"error": %s}' % json.dumps(str(e)[:200])).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        return body

    def _proxy_json(self, guid):
        try:
            lines = read_cfg_lines(self.srv)
            http_port = get_cfg_value(lines, "SERVER", "HTTP_PORT", "8081") or "8081"
        except Exception:
            http_port = "8081"
        raw, _st, ctype = _http_bytes("http://127.0.0.1:%s/JSON|%s" % (http_port, guid), timeout=5)
        if raw is None:
            self.send_error(502)
            return None
        self.send_response(200)
        self.send_header("Content-Type", ctype or "application/json")
        self.send_header("Content-Length", str(len(raw)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.end_headers()
        return raw

    def _serve(self, head_only=False):
        route, arg = _cm_route(self.path or "")
        if route == "details":
            body = self._send_json(build_cm_details(self.srv))
        elif route == "info":
            d = build_cm_details(self.srv)
            d["name"] = (d.get("name") or "") + cm_suffix(self.srv)
            body = self._send_json(d)
        elif route == "json":
            body = self._proxy_json(arg)
            if body is None:
                return
        else:
            self.send_error(404)
            return
        if not head_only:
            self.wfile.write(body)

    def do_GET(self):
        self._serve(head_only=False)

    def do_HEAD(self):
        self._serve(head_only=True)


def start_cm_sidecars():
    try:
        _cm_geo_ensure()
    except Exception:
        pass
    for x in SERVER_INSTANCES:
        srv = x["id"]
        port = CM_SIDECAR_PORTS[srv]
        try:
            handler = type("_CMH_" + srv, (_CMDetailsHandler,), {"srv": srv})
            httpd = ThreadingHTTPServer(("0.0.0.0", port), handler)
            httpd.daemon_threads = True
            t = threading.Thread(target=httpd.serve_forever, daemon=True, name="cm-sidecar-" + srv)
            t.start()
            CM_SIDECAR_SERVERS[srv] = httpd
            CM_SIDECAR_STATUS[srv] = True
        except Exception as e:
            CM_SIDECAR_STATUS[srv] = False
            try:
                print("CM sidecar %s:%d failed: %s" % (srv, port, e), flush=True)
            except Exception:
                pass


def can_edit_server(srv, u):
    if not u or u.get("status") != "approved":
        return False
    return valid_srv(srv) == "main" or u.get("role") == "admin"


def _need_edit(srv):
    """Redirect если текущий юзер не вправе менять этот сервер, иначе None."""
    _name, u = current_user()
    if can_edit_server(srv, u or {}):
        return None
    flash("Паблики настраивает только админ.", "error")
    return redirect(url_for("index") + "?srv=" + valid_srv(srv))
AVATARS_DIR = os.path.join(BASE_DIR, "avatars")

TRACK_INTERVAL = 60  # секунд между опросами сервера трекером
UDP_LISTEN_PORT = 11000  # панель слушает здесь то, что шлёт acServer
UDP_SERVER_PORT = 11001  # acServer слушает здесь команды панели
UDP_ROSTER_TTL = 120  # секунд без пакетов — UDP мёртв, откат на HTTP

SAFE_NAME = re.compile(r"^[A-Za-z0-9_\-\.]+$")
USERNAME_RE = re.compile(r"^[A-Za-z0-9_.\-]{3,20}$")
STEAMID_RE = re.compile(r"^7656119\d{10}$")
PREVIEW_NAMES = ("preview.jpg", "preview.jpeg", "preview.png", "preview.webp")
IMG_EXTS = (".jpg", ".jpeg", ".png", ".webp")
PNG_SIG = b"\x89PNG\r\n\x1a\n"

ADMIN_SEED_USER = "branchik07"
ADMIN_SEED_HASH = "pbkdf2:sha256:1000000$C6cRf2OMQYmcBs64$0e41d7653e92b88f1b09539b63fbd3daf2e8e8128192d3217adc10ba12829e18"

# field -> (SECTION, KEY) в server_cfg.ini
SETTINGS_FIELDS = [
    ("name", "SERVER", "NAME"),
    ("password", "SERVER", "PASSWORD"),
    ("admin_password", "SERVER", "ADMIN_PASSWORD"),
    ("track", "SERVER", "TRACK"),
    ("config_track", "SERVER", "CONFIG_TRACK"),
    ("sun_angle", "SERVER", "SUN_ANGLE"),
    ("max_clients", "SERVER", "MAX_CLIENTS"),
    ("udp_port", "SERVER", "UDP_PORT"),
    ("tcp_port", "SERVER", "TCP_PORT"),
    ("http_port", "SERVER", "HTTP_PORT"),
    ("register_to_lobby", "SERVER", "REGISTER_TO_LOBBY"),
    ("pickup_mode", "SERVER", "PICKUP_MODE_ENABLED"),
    ("locked_entry_list", "SERVER", "LOCKED_ENTRY_LIST"),
    ("loop_mode", "SERVER", "LOOP_MODE"),
    ("blacklist_mode", "SERVER", "BLACKLIST_MODE"),
    ("race_over_time", "SERVER", "RACE_OVER_TIME"),
    ("fuel_rate", "SERVER", "FUEL_RATE"),
    ("damage_multiplier", "SERVER", "DAMAGE_MULTIPLIER"),
    ("tyre_wear_rate", "SERVER", "TYRE_WEAR_RATE"),
    ("abs_allowed", "SERVER", "ABS_ALLOWED"),
    ("tc_allowed", "SERVER", "TC_ALLOWED"),
    ("stability_allowed", "SERVER", "STABILITY_ALLOWED"),
    ("autoclutch_allowed", "SERVER", "AUTOCLUTCH_ALLOWED"),
    ("tyre_blankets_allowed", "SERVER", "TYRE_BLANKETS_ALLOWED"),
    ("force_virtual_mirror", "SERVER", "FORCE_VIRTUAL_MIRROR"),
    ("practice_time", "PRACTICE", "TIME"),
    ("practice_open", "PRACTICE", "IS_OPEN"),
    ("qualify_time", "QUALIFY", "TIME"),
    ("qualify_open", "QUALIFY", "IS_OPEN"),
    ("race_laps", "RACE", "LAPS"),
    ("race_time", "RACE", "TIME"),
    ("race_wait_time", "RACE", "WAIT_TIME"),
    ("race_open", "RACE", "IS_OPEN"),
    ("weather_graphics", "WEATHER_0", "GRAPHICS"),
    ("temp_ambient", "WEATHER_0", "BASE_TEMPERATURE_AMBIENT"),
    ("temp_road", "WEATHER_0", "BASE_TEMPERATURE_ROAD"),
    ("wind_min", "WEATHER_0", "WIND_BASE_SPEED_MIN"),
    ("wind_max", "WEATHER_0", "WIND_BASE_SPEED_MAX"),
    ("dyn_start", "DYNAMIC_TRACK", "SESSION_START"),
    ("dyn_randomness", "DYNAMIC_TRACK", "RANDOMNESS"),
    ("dyn_transfer", "DYNAMIC_TRACK", "SESSION_TRANSFER"),
    ("dyn_lap_gain", "DYNAMIC_TRACK", "LAP_GAIN"),
]
CHECKBOX_FIELDS = {
    "register_to_lobby", "pickup_mode", "locked_entry_list", "loop_mode",
    "practice_open", "qualify_open", "race_open", "force_virtual_mirror",
}
# поля вкладки "Гонка" (остальные — вкладка "Сервер"); каждая форма сохраняет только свои
RACE_TAB_FIELDS = {
    "track", "config_track", "sun_angle", "weather_graphics", "temp_ambient", "temp_road",
    "wind_min", "wind_max", "practice_time", "practice_open", "qualify_time", "qualify_open",
    "race_laps", "race_time", "race_wait_time", "race_open",
    "dyn_start", "dyn_randomness", "dyn_transfer", "dyn_lap_gain",
}
DEFAULTS = {
    "sun_angle": "16", "max_clients": "10", "udp_port": "9600", "tcp_port": "9600",
    "http_port": "8081", "race_over_time": "180", "fuel_rate": "100",
    "damage_multiplier": "100", "tyre_wear_rate": "100", "blacklist_mode": "0",
    "practice_time": "10", "qualify_time": "10", "race_laps": "5",
    "race_time": "0", "race_wait_time": "60",
    "weather_graphics": "3_clear", "temp_ambient": "20", "temp_road": "25",
    "wind_min": "0", "wind_max": "10",
    "dyn_start": "90", "dyn_randomness": "0", "dyn_transfer": "80", "dyn_lap_gain": "30",
}


# ---------- пользователи и доступ ----------

def _seed_admin():
    return {"pw": ADMIN_SEED_HASH, "role": "admin", "status": "approved",
            "created": datetime.now().strftime("%Y-%m-%d %H:%M")}


def load_users():
    if not os.path.exists(USERS_PATH):
        users = {ADMIN_SEED_USER: _seed_admin()}
        save_users(users)
        return users
    try:
        with open(USERS_PATH, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            if ADMIN_SEED_USER not in data:
                data[ADMIN_SEED_USER] = _seed_admin()
                save_users(data)
            return data
    except Exception:
        pass
    return {}


def save_users(users):
    tmp = USERS_PATH + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(users, f, ensure_ascii=False, indent=2)
    os.replace(tmp, USERS_PATH)


def current_user():
    name = session.get("user")
    if not name:
        return None, None
    u = load_users().get(name)
    if not u:
        session.pop("user", None)
        return None, None
    return name, u


def login_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        _name, u = current_user()
        if not u:
            return redirect(url_for("auth"))
        if u.get("status") != "approved":
            return redirect(url_for("waiting"))
        return fn(*args, **kwargs)
    return wrapper


def admin_required(fn):
    @wraps(fn)
    def wrapper(*args, **kwargs):
        _name, u = current_user()
        if not u or u.get("status") != "approved" or u.get("role") != "admin":
            return redirect(url_for("auth"))
        return fn(*args, **kwargs)
    return wrapper


def get_profile(username):
    u = load_users().get(username) or {}
    return {"nick": u.get("nick", ""), "steamid": u.get("steamid", ""),
            "has_avatar": os.path.isfile(os.path.join(AVATARS_DIR, username + ".png"))}


# ---------- server_cfg.ini (с учётом секций) ----------

def read_cfg_lines(srv="main"):
    p = srv_cfg(srv)
    if not os.path.exists(p):
        return []
    with open(p, "r", encoding="utf-8", errors="ignore") as f:
        return f.readlines()


def _cfg_clean(s):
    """Убрать невидимый мусор (BOM, zero-width, NBSP) для сравнения ключей/секций."""
    return s.replace("\ufeff", "").replace("\u200b", "").replace("\u200c", "").replace("\u200d", "").replace("\xa0", " ")


def get_cfg_value(lines, section, key, default=""):
    cur = ""
    for line in lines:
        s = line.strip()
        sc = _cfg_clean(s)
        if sc.startswith("[") and sc.endswith("]"):
            cur = sc[1:-1].strip()
            continue
        if "=" in sc and not sc.startswith(";") and not sc.startswith("#"):
            k, v = s.split("=", 1)
            if cur.upper() == section.upper() and _cfg_clean(k).strip().upper() == key.upper():
                return v.strip()
    return default


def set_cfg_values(updates, srv="main"):
    """updates: список (section, key, value). Сохраняет структуру файла и кодировку."""
    lines = read_cfg_lines(srv)
    remaining = {(s.upper(), k.upper()): (s, k, v) for s, k, v in updates}
    new_lines = []
    cur = ""
    done = set()
    for line in lines:
        s = line.strip()
        sc = _cfg_clean(s)
        if sc.startswith("[") and sc.endswith("]"):
            cur = sc[1:-1].strip()
            new_lines.append(line)
            continue
        if "=" in sc and not sc.startswith(";") and not sc.startswith("#"):
            k = _cfg_clean(s.split("=", 1)[0]).strip()
            lookup = (cur.upper(), k.upper())
            if lookup in remaining:
                if lookup in done:
                    continue  # дубль ключа — выкидываем
                _, _, v = remaining[lookup]
                new_lines.append("%s=%s\n" % (k, v))
                done.add(lookup)
                continue
        new_lines.append(line)
    # дописываем отсутствующие ключи в нужные секции
    for lookup, (s, k, v) in remaining.items():
        if lookup in done:
            continue
        found = any(l.strip().upper() == "[%s]" % s.upper() for l in new_lines)
        if not found:
            if new_lines and not new_lines[-1].endswith("\n"):
                new_lines[-1] += "\n"
            new_lines.append("\n[%s]\n" % s)
        idx = None
        for i in range(len(new_lines) - 1, -1, -1):
            if new_lines[i].strip().upper() == "[%s]" % s.upper():
                idx = i
                break
        insert_at = len(new_lines)
        if idx is not None:
            for j in range(idx + 1, len(new_lines)):
                if new_lines[j].strip().startswith("["):
                    insert_at = j
                    break
        new_lines.insert(insert_at, "%s=%s\n" % (k, v))
    p = srv_cfg(srv)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.writelines(new_lines)


# ---------- entry_list.ini ----------

ENTRY_KEYS = ["MODEL", "SKIN", "SPECTATOR_MODE", "DRIVERNAME", "TEAM", "GUID", "BALLAST", "RESTRICTOR"]


def parse_entry_list(srv="main"):
    entries = []
    p = srv_entry(srv)
    if not os.path.exists(p):
        return entries
    cur = None
    with open(p, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            s = line.strip()
            if s.upper().startswith("[CAR_"):
                if cur is not None:
                    entries.append(cur)
                cur = {k: "" for k in ENTRY_KEYS}
                cur["SPECTATOR_MODE"] = "0"
                cur["BALLAST"] = "0"
                cur["RESTRICTOR"] = "0"
                continue
            if cur is not None and "=" in s and not s.startswith(";"):
                k, v = s.split("=", 1)
                k = k.strip().upper()
                if k in cur:
                    cur[k] = v.strip()
    if cur is not None:
        entries.append(cur)
    return entries


def write_entry_list(entries, srv="main"):
    p = srv_entry(srv)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        for i, e in enumerate(entries):
            f.write("[CAR_%d]\n" % i)
            for k in ENTRY_KEYS:
                f.write("%s=%s\n" % (k, e.get(k, "")))
            f.write("\n")


# ---------- контент: машины и трассы ----------

def get_car_skins(model):
    d = os.path.join(CONTENT_CARS, model, "skins")
    if not os.path.isdir(d):
        return []
    try:
        return sorted(x for x in os.listdir(d) if os.path.isdir(os.path.join(d, x)))
    except Exception:
        return []


def get_dir_size_mb(path):
    total = 0
    try:
        for root, _dirs, files in os.walk(path):
            for fn in files:
                try:
                    total += os.path.getsize(os.path.join(root, fn))
                except OSError:
                    pass
    except OSError:
        pass
    return round(total / 1024 / 1024, 1)


def list_cars():
    cars = []
    if not os.path.isdir(CONTENT_CARS):
        return cars
    for folder in sorted(os.listdir(CONTENT_CARS)):
        p = os.path.join(CONTENT_CARS, folder)
        if not os.path.isdir(p):
            continue
        info = {"id": folder, "brand": "", "name": folder, "bhp": "",
                "weight": "", "size": get_dir_size_mb(p), "skins": get_car_skins(folder)}
        for cand in (os.path.join(p, "ui", "ui_car.json"), os.path.join(p, "ui_car.json")):
            if os.path.exists(cand):
                try:
                    with open(cand, "r", encoding="utf-8", errors="ignore") as f:
                        data = json.load(f)
                    info["brand"] = data.get("brand", "")
                    info["name"] = data.get("name", folder)
                    specs = data.get("specs", {})
                    if isinstance(specs, dict):
                        info["bhp"] = str(specs.get("bhp", ""))
                        info["weight"] = str(specs.get("weight", ""))
                except Exception:
                    pass
                break
        cars.append(info)
    return cars


def get_track_layouts(track_id):
    layouts = set()
    p = os.path.join(CONTENT_TRACKS, track_id)
    try:
        for fn in os.listdir(p):
            if fn.startswith("models_") and fn.endswith(".ini"):
                layouts.add(fn[7:-4])
        ui_path = os.path.join(p, "ui")
        if os.path.isdir(ui_path):
            for fn in os.listdir(ui_path):
                if fn.startswith("ui_track_") and fn.endswith(".json"):
                    layouts.add(fn[9:-5])
    except Exception:
        pass
    return sorted(layouts)


def list_tracks():
    tracks = []
    if not os.path.isdir(CONTENT_TRACKS):
        return tracks
    for folder in sorted(os.listdir(CONTENT_TRACKS)):
        p = os.path.join(CONTENT_TRACKS, folder)
        if not os.path.isdir(p):
            continue
        info = {"id": folder, "name": folder, "description": "", "length": "",
                "size": get_dir_size_mb(p), "layouts": get_track_layouts(folder)}
        for cand in (os.path.join(p, "ui", "ui_track.json"), os.path.join(p, "ui_track.json")):
            if os.path.exists(cand):
                try:
                    with open(cand, "r", encoding="utf-8", errors="ignore") as f:
                        data = json.load(f)
                    info["name"] = data.get("name", folder)
                    info["description"] = data.get("description", "")
                    info["length"] = str(data.get("length", ""))
                except Exception:
                    pass
                break
        tracks.append(info)
    return tracks


# ---------- приветствие и чёрный список ----------

def read_text_file(path):
    if not os.path.exists(path):
        return ""
    try:
        with open(path, "r", encoding="utf-8", errors="ignore") as f:
            return f.read()
    except Exception:
        return ""


def read_welcome(srv="main"):
    for p in srv_welcome_paths(srv):
        text = read_text_file(p)
        if text:
            return text
    return ""


def read_blacklist(srv="main"):
    return read_text_file(srv_blacklist(srv))


# ---------- управление сервером ----------

def is_server_running(srv="main"):
    s = get_server(srv)
    names = [s["screen"]] + (["ac"] if s["id"] == "main" else [])
    try:
        out = subprocess.run(["screen", "-ls"], stdout=subprocess.PIPE,
                             stderr=subprocess.DEVNULL, timeout=5).stdout.decode("utf-8", "ignore")
        for n in names:
            if (".%s\t" % n) in out or (".%s " % n) in out:
                return True
    except Exception:
        pass
    try:
        r = subprocess.run(["pgrep", "-f", s["proc"]], stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=5)
        return r.returncode == 0
    except Exception:
        return False


def start_server_proc(srv="main"):
    if is_server_running(srv):
        return False
    s = get_server(srv)
    try:
        open(srv_log(srv), "w", encoding="utf-8").write("")
    except Exception:
        pass
    subprocess.Popen(["screen", "-dmS", s["screen"], "bash", "-c",
                      "exec -a %s ./acServer > server.log 2>&1" % s["proc"]],
                     cwd=srv_dir(srv), stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    return True


def stop_server_proc(srv="main"):
    s = get_server(srv)
    names = [s["screen"]] + (["ac"] if s["id"] == "main" else [])
    for n in names:
        subprocess.run(["screen", "-S", n, "-X", "quit"],
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    subprocess.run(["pkill", "-9", "-f", s["proc"]],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)


def setup_pub_server(srv):
    """Создать паблик с нуля или дочинить недосозданный. 'created'/'repaired'/None."""
    if valid_srv(srv) != srv or srv == "main":
        return None
    d = srv_dir(srv)
    fresh = not os.path.isfile(srv_cfg(srv))
    was_ready = pub_ready(srv)
    try:
        os.makedirs(os.path.join(d, "cfg"), exist_ok=True)
        os.makedirs(os.path.join(d, "results"), exist_ok=True)
        for name in ("content", "acServer"):
            src, dst = os.path.join(SERVER_DIR, name), os.path.join(d, name)
            if os.path.exists(src) and not os.path.lexists(dst):
                try:
                    os.symlink(src, dst)
                except OSError:
                    pass
        main_lines = read_cfg_lines("main")
        if fresh:
            base = "".join(main_lines)
            with open(srv_cfg(srv), "w", encoding="utf-8") as f:
                f.write(base if base.strip() else "[SERVER]\n")
        ports = PUB_PORTS[srv]
        forced = [
            ("SERVER", "TCP_PORT", ports["tcp"]),
            ("SERVER", "UDP_PORT", ports["udp"]),
            ("SERVER", "HTTP_PORT", ports["http"]),
            ("SERVER", "REGISTER_TO_LOBBY", "1"),
            ("SERVER", "UDP_PLUGIN_ADDRESS", ""),
        ]
        if fresh:
            main_name = strip_cm_suffix(get_cfg_value(main_lines, "SERVER", "NAME", "AC Server"))
            forced += [
                ("SERVER", "NAME", "%s | %s" % (main_name, get_server(srv)["label"].upper())),
                ("SERVER", "PASSWORD", ""),
                ("SERVER", "MAX_CLIENTS", "12"),
            ]
        else:
            cur_name = get_cfg_value(read_cfg_lines(srv), "SERVER", "NAME", "")
            if not cur_name.strip():
                main_name = strip_cm_suffix(get_cfg_value(main_lines, "SERVER", "NAME", "AC Server"))
                forced.append(("SERVER", "NAME",
                               "%s | %s" % (main_name, get_server(srv)["label"].upper())))
        set_cfg_values(forced, srv)
        if not os.path.isfile(srv_entry(srv)):
            want_cars = get_cfg_value(read_cfg_lines(srv), "SERVER", "CARS", "")
            models = [c.strip() for c in re.split(r"[;,]", want_cars) if c.strip()]
            if not models:
                main_cars = get_cfg_value(main_lines, "SERVER", "CARS", "")
                models = [c.strip() for c in re.split(r"[;,]", main_cars) if c.strip()]
            if not models:
                models = ["ks_mazda_mx5_cup"]
            base_entries = parse_entry_list("main")
            entries = []
            for i in range(12):
                if i < len(base_entries) and base_entries[i].get("MODEL"):
                    entries.append(dict(base_entries[i]))
                else:
                    e = {k: "" for k in ENTRY_KEYS}
                    e.update({"MODEL": models[i % len(models)], "SPECTATOR_MODE": "0",
                              "BALLAST": "0", "RESTRICTOR": "0"})
                    entries.append(e)
            write_entry_list(entries, srv)
            used = []
            for e in entries:
                if e.get("MODEL") and e["MODEL"] not in used:
                    used.append(e["MODEL"])
            set_cfg_values([("SERVER", "CARS", ";".join(used)),
                            ("SERVER", "MAX_CLIENTS", str(len(entries)))], srv)
        bp = srv_blacklist(srv)
        if not os.path.isfile(bp) and os.path.isfile(srv_blacklist("main")):
            try:
                shutil.copy(srv_blacklist("main"), bp)
            except Exception:
                pass
        if not any(os.path.isfile(p) for p in srv_welcome_paths(srv)):
            wmain = read_welcome("main")
            if wmain:
                for p in srv_welcome_paths(srv):
                    try:
                        os.makedirs(os.path.dirname(p), exist_ok=True)
                        with open(p, "w", encoding="utf-8") as f:
                            f.write(wmain)
                    except Exception:
                        pass
        try:
            if not os.path.isfile(cm_desc_path(srv)):
                open(cm_desc_path(srv), "w", encoding="utf-8").write("")
        except OSError:
            pass
        return "created" if fresh else ("exists" if was_ready else "repaired")
    except Exception:
        return None


@app.route("/setup_pub", methods=["POST"])
@admin_required
def setup_pub():
    res = {srv: setup_pub_server(srv) for srv in ("pub1", "pub2")}
    if all(v == "created" for v in res.values()):
        flash("Паблики созданы: порты 9601/8082 и 9602/8083. Проверь названия и жми Старт.", "ok")
    elif all(v == "exists" for v in res.values()):
        flash("Паблики уже созданы и в порядке.", "ok")
    elif all(v in ("created", "repaired") for v in res.values()):
        flash("Готово: недостающее дочинено (ссылки, порты, слоты). Проверь названия и жми Старт.", "ok")
    else:
        flash("Готово частично: pub1=%s, pub2=%s." % (res["pub1"], res["pub2"]), "error")
    return redirect(url_for("index") + "?srv=pub1")


# ---------- системная статистика и онлайн ----------

def _uptime_str():
    try:
        with open("/proc/uptime") as f:
            secs = int(float(f.read().split()[0]))
    except Exception:
        return None
    d, secs = divmod(secs, 86400)
    h, secs = divmod(secs, 3600)
    m = secs // 60
    if d:
        return "%dд %dч" % (d, h)
    if h:
        return "%dч %dм" % (h, m)
    return "%dм" % m


def _http_json(url, timeout=3):
    """Возвращает (obj, err, meta). err: None | 'conn' | 'http404' | 'httpXXX' | 'badjson'.

    meta: {status, ctype, len, head} — сырой preview ответа для диагностики.
    """
    meta = {"status": 0, "ctype": "", "len": 0, "head": ""}
    try:
        with urllib.request.urlopen(url, timeout=timeout) as r:
            raw = r.read() or b""
            try:
                meta["status"] = int(getattr(r, "status", 0) or 0)
            except (TypeError, ValueError):
                pass
            try:
                meta["ctype"] = (r.headers.get("Content-Type") or "")[:80]
            except Exception:
                pass
    except urllib.error.HTTPError as e:
        try:
            raw = e.read() or b""
        except Exception:
            raw = b""
        meta["status"] = e.code
        meta["len"] = len(raw)
        meta["head"] = raw[:400].decode("utf-8", "replace")
        return None, ("http404" if e.code == 404 else "http%d" % e.code), meta
    except Exception:
        return None, "conn", meta
    meta["len"] = len(raw)
    meta["head"] = raw[:400].decode("utf-8", "replace")
    try:
        return json.loads(raw.decode("utf-8-sig")), None, meta
    except Exception:
        return None, "badjson", meta


def _fmt_lap(ms):
    try:
        ms = int(ms)
    except (TypeError, ValueError):
        return "—"
    if ms <= 0:
        return "—"
    m, rem = divmod(ms, 60000)
    s, ms = divmod(rem, 1000)
    return "%d:%02d.%03d" % (m, s, ms)


def fmt_duration(secs):
    try:
        secs = int(secs or 0)
    except (TypeError, ValueError):
        return "—"
    if secs <= 0:
        return "—"
    d, r = divmod(secs, 86400)
    h, r = divmod(r, 3600)
    m = r // 60
    if d:
        return "%dд %dч" % (d, h)
    if h:
        return "%dч %dм" % (h, m)
    if m:
        return "%dм" % m
    return "%dс" % secs


def fmt_ago(ts):
    try:
        ts = int(ts or 0)
    except (TypeError, ValueError):
        return "—"
    if ts <= 0:
        return "—"
    delta = int(time.time()) - ts
    if delta < 0:
        delta = 0
    if delta < 3600:
        m = delta // 60
        return "только что" if m < 1 else "%d мин назад" % m
    if delta < 86400:
        return "%d ч назад" % (delta // 3600)
    return "%d дн назад" % (delta // 86400)


LAST_PROBE = {"at": 0, "port": "", "info_ok": False, "info_keys": [], "info_track": "",
              "info_clients": 0, "info_status": 0, "info_ctype": "", "info_len": 0,
              "info_head": "", "info_json_field": "", "json_ok": False, "json_status": 0,
              "json_ctype": "", "json_len": 0, "json_head": "", "cars_raw": 0,
              "car_keys": [], "players": 0, "names": [], "error": ""}


def fetch_live(http_port):
    """Живые данные с игрового сервера: игроки, трасса. None если недоступен."""
    global LAST_PROBE
    port = str(http_port or "8081")
    base = "http://127.0.0.1:%s" % port
    probe = {"at": int(time.time()), "port": port, "info_ok": False, "info_keys": [],
             "info_track": "", "info_clients": 0, "info_status": 0, "info_ctype": "",
             "info_len": 0, "info_head": "", "info_json_field": "", "json_ok": False,
             "json_status": 0, "json_ctype": "", "json_len": 0, "json_head": "",
             "cars_raw": 0, "car_keys": [], "players": 0, "names": [], "error": ""}
    info, info_err, info_meta = _http_json(base + "/INFO")
    data, json_err, json_meta = _http_json(base + "/JSON")
    for k in ("status", "ctype", "len", "head"):
        probe["info_" + k] = info_meta.get(k, "")
        probe["json_" + k] = json_meta.get(k, "")
    if info is None and data is None:
        probe["error"] = "INFO:%s JSON:%s" % (info_err, json_err)
        LAST_PROBE = probe
        return None
    players = []
    if isinstance(data, dict):
        cars = data.get("Cars") or []
        if isinstance(cars, dict):
            cars = list(cars.values())
        if isinstance(cars, list):
            probe["cars_raw"] = len(cars)
            probe["json_ok"] = True
            for c in cars:
                if not isinstance(c, dict):
                    continue
                if not probe["car_keys"]:
                    try:
                        probe["car_keys"] = sorted(c.keys())[:12]
                    except Exception:
                        pass
                if c.get("IsConnected") is False:
                    continue
                name = (c.get("DriverName") or "").strip()
                if not name:
                    continue
                try:
                    speed = round(float(c.get("TopSpeedKmh") or 0))
                except (TypeError, ValueError):
                    speed = 0
                try:
                    best = int(c.get("BestLap") or 0)
                except (TypeError, ValueError):
                    best = 0
                guid = c.get("DriverGuid") or c.get("DriverGUID") or c.get("GUID") or ""
                players.append({"name": name, "car": c.get("CarModel") or "—",
                                "best": best, "speed": speed, "guid": str(guid or "")})
    track, clients = "", 0
    if isinstance(info, dict):
        probe["info_ok"] = True
        try:
            probe["info_keys"] = sorted(info.keys())[:20]
        except Exception:
            pass
        track = info.get("track") or ""
        probe["info_track"] = track
        try:
            clients = int(info.get("clients") or 0)
        except (TypeError, ValueError):
            pass
        probe["info_clients"] = clients
        try:
            probe["info_json_field"] = repr(info.get("json"))[:200]
        except Exception:
            pass
    probe["players"] = len(players)
    probe["names"] = [p["name"] for p in players[:12]]
    if info is None:
        probe["error"] = "INFO:%s" % info_err
    elif data is None:
        probe["error"] = "JSON:%s" % json_err
    LAST_PROBE = probe
    return {"players": players, "track": track, "clients": clients}


# ---------- UDP-плагин acServer: живые данные (имена, GUID, круги) ----------
# Формат по исходникам assetto-server-manager (pkg/udp): little-endian,
# первый байт датаграммы = тип, строки = u8 длина в СИМВОЛАХ + байты
# (x4 для широких UTF-32LE, x1 для обычных UTF-8).

UDP_STATUS = {"listening": False, "bind_error": "", "cfg_address": "",
              "cfg_local_port": "", "cfg_managed": False, "cfg_points_to_us": False,
              "packets": 0, "last_rx": 0, "last_type": "", "by_type": {},
              "parse_errors": 0, "last_parse_error": "", "cmd_sent": 0, "cmd_port": 0,
              "cmd_error": "",
              "session_type": "", "server_version": 0, "server_error": "",
              "end_session_file": ""}
UDP_ROSTER = {}  # car_id -> {"name":, "guid":, "car":, "skin":, "team":, "seen":}
UDP_TRACK = ""
_udp_lock = threading.Lock()

UDP_EV = {10: "collision_car", 11: "collision_env", 50: "new_session",
          51: "new_connection", 52: "conn_closed", 53: "car_update", 54: "car_info",
          55: "end_session", 56: "version", 57: "chat", 58: "client_loaded",
          59: "session_info", 60: "error", 73: "lap", 130: "client_event"}
UDP_SESSIONS = {0: "Booking", 1: "Practice", 2: "Qualifying", 3: "Race"}


class _UdpReader(object):
    def __init__(self, buf):
        self.buf = buf
        self.pos = 0

    def u8(self):
        v = self.buf[self.pos]
        self.pos += 1
        return v

    def u16(self):
        v = struct.unpack_from("<H", self.buf, self.pos)[0]
        self.pos += 2
        return v

    def u32(self):
        v = struct.unpack_from("<I", self.buf, self.pos)[0]
        self.pos += 4
        return v

    def i32(self):
        v = struct.unpack_from("<i", self.buf, self.pos)[0]
        self.pos += 4
        return v

    def raw_str(self, wide):
        n = self.u8()
        size = n * (4 if wide else 1)
        b = self.buf[self.pos:self.pos + size]
        if len(b) < size:
            raise ValueError("truncated string")
        self.pos += size
        return b.decode("utf-32-le" if wide else "utf-8", "replace")


def _udp_track_key(track, config):
    t = (track or "").strip()
    c = (config or "").strip()
    if c and not t.lower().endswith(c.lower()):
        t = (t + "_" + c) if t else c
    return t


def _udp_roster_set(car_id, name, guid, car, skin="", team=""):
    with _udp_lock:
        UDP_ROSTER[int(car_id)] = {"name": (name or "").strip(),
                                   "guid": (guid or "").strip(),
                                   "car": (car or "").strip(),
                                   "skin": (skin or "").strip(),
                                   "team": (team or "").strip(),
                                   "seen": int(time.time())}


def _udp_roster_del(car_id):
    with _udp_lock:
        return UDP_ROSTER.pop(int(car_id), None)


def udp_roster_snapshot():
    with _udp_lock:
        return [dict({"car_id": k}, **v) for k, v in sorted(UDP_ROSTER.items())]


def record_udp_lap(name, guid, track, car, ms):
    """Рекорд круга с UDP в реальном времени (только чистые, как в results)."""
    if ms <= 0 or (not name and not guid):
        return
    now = int(time.time())
    bk = (track or "?") + "|" + (car or "?")

    def _fn(data):
        data.setdefault("drivers", {})
        data.setdefault("guids", {})
        data.setdefault("guid_best", {})
        data.setdefault("meta", {})["updated"] = now
        if guid and STEAMID_RE.match(guid):
            if name:
                data["guids"][guid] = name
            gb = data["guid_best"].setdefault(guid, {})
            prev = gb.get(bk, 0)
            if not prev or ms < prev:
                gb[bk] = ms
        if name:
            d = data["drivers"].setdefault(name, {"seconds": 0, "tracks": {}, "cars": {},
                                                  "combos": {}, "best": {}, "days": [],
                                                  "last_seen": 0})
            d["last_seen"] = now
            prev = d["best"].get(bk, 0)
            if not prev or ms < prev:
                d["best"][bk] = ms

    update_stats(_fn)


def _udp_handle(buf):
    """Разобрать одну датаграмму. Возвращает имя события."""
    global UDP_TRACK
    if not buf:
        raise ValueError("empty datagram")
    r = _UdpReader(buf)
    typ = r.u8()
    if typ in (51, 52):  # NewConnection / ConnectionClosed
        name = r.raw_str(True)
        guid = r.raw_str(True)
        car_id = r.u8()
        car = r.raw_str(False)
        skin = r.raw_str(False)
        if typ == 51:
            _udp_roster_set(car_id, name, guid, car, skin)
        else:
            _udp_roster_del(car_id)
    elif typ == 54:  # CarInfo (ответ на команду 201)
        car_id = r.u8()
        connected = r.u8()
        car = r.raw_str(True)
        skin = r.raw_str(True)
        name = r.raw_str(True)
        team = r.raw_str(True)
        guid = r.raw_str(True)
        if connected and (name or "").strip():
            _udp_roster_set(car_id, name, guid, car, skin, team)
        else:
            _udp_roster_del(car_id)
    elif typ in (50, 59):  # NewSession / SessionInfo
        r.u8()
        r.u8()
        r.u8()
        r.u8()
        r.raw_str(True)  # server name
        track = r.raw_str(False)
        config = r.raw_str(False)
        r.raw_str(False)  # session name
        stype = r.u8()
        r.u16()
        r.u16()
        r.u16()
        r.u8()
        r.u8()
        r.raw_str(False)  # weather
        r.i32()  # elapsed ms
        UDP_TRACK = _udp_track_key(track, config)
        UDP_STATUS["session_type"] = UDP_SESSIONS.get(stype, "?")
    elif typ == 73:  # LapCompleted
        car_id = r.u8()
        lap = r.u32()
        cuts = r.u8()
        count = r.u8()
        for _ in range(count):
            r.u8()
            r.u32()
            r.u16()
            r.u8()
        with _udp_lock:
            ent = UDP_ROSTER.get(car_id, {})
            nm = ent.get("name", "")
            gd = ent.get("guid", "")
            cm = ent.get("car", "")
        if cuts == 0 and lap > 0:
            record_udp_lap(nm, gd, UDP_TRACK or "?", cm, lap)
    elif typ == 56:  # Version
        UDP_STATUS["server_version"] = r.u8()
    elif typ == 55:  # EndSession
        UDP_STATUS["end_session_file"] = r.raw_str(True)[:80]
    elif typ == 60:  # Error
        UDP_STATUS["server_error"] = r.raw_str(True)[:200]
    elif typ in (53, 57, 58, 130, 10, 11):
        pass  # известные, но не нужные нам
    else:
        raise ValueError("unknown msg type %d" % typ)
    return UDP_EV.get(typ, "?")


def _valid_port(s):
    return (s or "").isdigit() and 0 < int(s) < 65536


def ensure_udp_cfg():
    """Прописать UDP_PLUGIN_* в server_cfg.ini, если их нет. Чужое не трогаем.

    UDP_PLUGIN_LOCAL_PORT=0 означает «плагин-интерфейс выключен» — чиним на свой порт.
    """
    lines = read_cfg_lines()
    addr = get_cfg_value(lines, "SERVER", "UDP_PLUGIN_ADDRESS", "")
    lport = get_cfg_value(lines, "SERVER", "UDP_PLUGIN_LOCAL_PORT", "")
    managed = False
    want_addr = "127.0.0.1:%d" % UDP_LISTEN_PORT
    updates = []
    if not addr:
        addr = want_addr
        updates.append(("SERVER", "UDP_PLUGIN_ADDRESS", want_addr))
    if addr.strip() == want_addr and not _valid_port(lport):
        lport = str(UDP_SERVER_PORT)
        updates.append(("SERVER", "UDP_PLUGIN_LOCAL_PORT", lport))
    if updates:
        set_cfg_values(updates)
        managed = True
    UDP_STATUS["cfg_address"] = addr
    UDP_STATUS["cfg_local_port"] = lport
    UDP_STATUS["cfg_managed"] = managed
    UDP_STATUS["cfg_points_to_us"] = (addr.strip() == want_addr)
    return addr, lport, managed


def udp_send(cmd_byte):
    """Команда acServer'у: 201 = дай ростер, 204 = дай сессию."""
    if not UDP_STATUS.get("cfg_points_to_us"):
        return
    try:
        port = int(UDP_STATUS.get("cfg_local_port") or 0)
    except (TypeError, ValueError):
        port = 0
    if not 0 < port < 65536:
        UDP_STATUS["cmd_error"] = "плохой порт команд: %r" % (UDP_STATUS.get("cfg_local_port"),)
        return
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        try:
            sock.sendto(bytes([cmd_byte]), ("127.0.0.1", port))
        finally:
            sock.close()
        UDP_STATUS["cmd_port"] = port
        UDP_STATUS["cmd_sent"] += 1
        UDP_STATUS["cmd_error"] = ""
    except Exception as e:
        UDP_STATUS["cmd_error"] = ("%s: %s" % (type(e).__name__, e))[:160]


def _udp_loop():
    ensure_udp_cfg()
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.bind(("127.0.0.1", UDP_LISTEN_PORT))
        sock.settimeout(1.0)
    except Exception as e:
        UDP_STATUS["bind_error"] = ("%s: %s" % (type(e).__name__, e))[:200]
        return
    UDP_STATUS["listening"] = True
    udp_send(201)
    udp_send(204)
    last_poll = time.time()
    while True:
        try:
            try:
                buf, _ = sock.recvfrom(2048)
            except socket.timeout:
                buf = None
            if buf:
                try:
                    ev = _udp_handle(bytes(buf))
                    UDP_STATUS["packets"] += 1
                    UDP_STATUS["last_rx"] = int(time.time())
                    UDP_STATUS["last_type"] = ev or "?"
                    if ev:
                        bt = UDP_STATUS["by_type"]
                        bt[ev] = bt.get(ev, 0) + 1
                except Exception as e:
                    UDP_STATUS["packets"] += 1
                    UDP_STATUS["parse_errors"] += 1
                    UDP_STATUS["last_parse_error"] = ("%s: %s" % (type(e).__name__, e))[:200]
            if time.time() - last_poll >= 60:
                udp_send(201)
                udp_send(204)
                last_poll = time.time()
        except Exception:
            pass


def _live_players(lines, http_port):
    """UDP-first, HTTP fallback. Возвращает (players, track, source) или None."""
    snap = udp_roster_snapshot()
    fresh = UDP_STATUS["last_rx"] and (int(time.time()) - UDP_STATUS["last_rx"]) <= UDP_ROSTER_TTL
    if UDP_STATUS["listening"] and fresh and snap:
        players = [{"name": r["name"], "car": r["car"] or "-", "best": 0, "speed": 0,
                    "guid": r["guid"]} for r in snap if (r["name"] or "").strip()]
        if players:
            return players, UDP_TRACK or get_cfg_value(lines, "SERVER", "TRACK", ""), "udp"
    live = fetch_live(http_port)
    if live is None:
        return None
    return live["players"], live["track"] or get_cfg_value(lines, "SERVER", "TRACK", ""), "http"


# ---------- трекер статистики ----------

_stats_lock = threading.Lock()


def _read_stats_file():
    default = {"drivers": {}, "guids": {}, "guid_best": {}, "meta": {"updated": 0}}
    try:
        if os.path.exists(STATS_PATH):
            with open(STATS_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            if isinstance(data, dict):
                for k, v in default.items():
                    data.setdefault(k, v)
                return data
    except Exception:
        pass
    return {"drivers": {}, "guids": {}, "guid_best": {}, "meta": {"updated": 0}}


def load_stats():
    with _stats_lock:
        return _read_stats_file()


def update_stats(fn):
    with _stats_lock:
        data = _read_stats_file()
        fn(data)
        tmp = STATS_PATH + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False)
        os.replace(tmp, STATS_PATH)
        return data


def apply_live_sample(players, track, now=None, interval=TRACK_INTERVAL):
    """Записать один опрос онлайна в статистику."""
    now = int(now or time.time())
    day = datetime.utcfromtimestamp(now).strftime("%Y-%m-%d")

    def _fn(data):
        data.setdefault("drivers", {})
        data.setdefault("guids", {})
        data.setdefault("meta", {})["updated"] = now
        for p in players:
            name = (p.get("name") or "").strip()
            if not name:
                continue
            d = data["drivers"].setdefault(name, {"seconds": 0, "tracks": {}, "cars": {},
                                                  "combos": {}, "best": {}, "days": [], "last_seen": 0})
            d["seconds"] = d.get("seconds", 0) + interval
            d["last_seen"] = now
            if track:
                d["tracks"][track] = d["tracks"].get(track, 0) + interval
            car = (p.get("car") or "").strip()
            if car:
                d["cars"][car] = d["cars"].get(car, 0) + interval
            if track and car:
                ck = track + "|" + car
                d["combos"][ck] = d["combos"].get(ck, 0) + interval
            try:
                best = int(p.get("best") or 0)
            except (TypeError, ValueError):
                best = 0
            if best > 0 and track and car:
                bk = track + "|" + car
                prev = d["best"].get(bk, 0)
                if not prev or best < prev:
                    d["best"][bk] = best
            days = d.setdefault("days", [])
            if day not in days:
                days.append(day)
                del days[:-90]
            guid = (p.get("guid") or "").strip()
            if guid and STEAMID_RE.match(guid):
                data["guids"][guid] = name

    return update_stats(_fn)


def _walk_laps(obj, out):
    if isinstance(obj, dict):
        g = obj.get("DriverGuid") or obj.get("DriverGUID") or obj.get("GUID")
        lap = obj.get("LapTime")
        if g and lap:
            try:
                lap = int(lap)
            except (TypeError, ValueError):
                lap = 0
            if lap > 0:
                try:
                    cuts = int(obj.get("Cuts", 0))
                except (TypeError, ValueError):
                    cuts = 0
                out.append({"guid": str(g), "name": obj.get("DriverName") or "",
                            "car": obj.get("CarModel") or "", "lap": lap, "cuts": cuts})
        for v in obj.values():
            _walk_laps(v, out)
    elif isinstance(obj, list):
        for v in obj:
            _walk_laps(v, out)


def _root_track(obj):
    if isinstance(obj, dict):
        for k in ("TrackName", "Track", "TrackConfig", "track"):
            v = obj.get(k)
            if isinstance(v, str) and v:
                return v
    return ""


def scan_results():
    """Разобрать results/*.json: связки GUID->ник и рекорды кругов."""
    if not os.path.isdir(RESULTS_DIR):
        return 0
    try:
        files = sorted((os.path.join(RESULTS_DIR, f) for f in os.listdir(RESULTS_DIR)
                        if f.lower().endswith(".json")),
                       key=lambda p: os.path.getmtime(p), reverse=True)[:200]
    except OSError:
        return 0
    n = [0]

    def _fn(data):
        data.setdefault("guids", {})
        data.setdefault("guid_best", {})
        for path in files:
            try:
                if os.path.getsize(path) > 3 * 1024 * 1024:
                    continue
                with open(path, "r", encoding="utf-8", errors="ignore") as f:
                    doc = json.load(f)
            except Exception:
                continue
            track = _root_track(doc)
            laps = []
            _walk_laps(doc, laps)
            for L in laps:
                g = L["guid"]
                if not STEAMID_RE.match(g):
                    continue
                if L["name"] and g not in data["guids"]:
                    data["guids"][g] = L["name"]
                if L["cuts"] > 0:
                    continue
                gb = data["guid_best"].setdefault(g, {})
                bk = (track or "?") + "|" + (L["car"] or "?")
                prev = gb.get(bk, 0)
                if not prev or L["lap"] < prev:
                    gb[bk] = L["lap"]
                n[0] += 1

    update_stats(_fn)
    return n[0]


TRACKER_STATUS = {"started": 0, "cycle": 0, "last_run": 0, "last_ok": 0,
                  "samples": 0, "last_scan": 0, "scanned_laps": 0, "error": "",
                  "source": ""}


def _tracker_loop():
    TRACKER_STATUS["started"] = int(time.time())
    cycles = 0
    while True:
        try:
            lines = read_cfg_lines()
            port = get_cfg_value(lines, "SERVER", "HTTP_PORT", "8081") or "8081"
            res = _live_players(lines, port)
            if res:
                players, track, source = res
                TRACKER_STATUS["source"] = source
                if players:
                    apply_live_sample(players, track)
                    TRACKER_STATUS["samples"] += 1
            TRACKER_STATUS["last_ok"] = int(time.time())
            TRACKER_STATUS["error"] = ""
            cycles += 1
            TRACKER_STATUS["cycle"] = cycles
            if cycles % 10 == 0:
                try:
                    n = scan_results()
                    TRACKER_STATUS["last_scan"] = int(time.time())
                    TRACKER_STATUS["scanned_laps"] = n
                except Exception:
                    TRACKER_STATUS["last_scan"] = int(time.time())
                    TRACKER_STATUS["scanned_laps"] = -1
        except Exception as e:
            TRACKER_STATUS["error"] = ("%s: %s" % (type(e).__name__, e))[:200]
        finally:
            TRACKER_STATUS["last_run"] = int(time.time())
        time.sleep(TRACK_INTERVAL)


def start_tracker():
    t = threading.Thread(target=_tracker_loop, daemon=True, name="ac-tracker")
    t.start()
    u = threading.Thread(target=_udp_loop, daemon=True, name="ac-udp")
    u.start()


# ---------- профили и лидерборд ----------

def link_driver(profile, stats):
    """Найти имя пилота для профиля. Возвращает (name, via) или (None, None)."""
    guids = stats.get("guids", {})
    drivers = stats.get("drivers", {})
    sid = (profile.get("steamid") or "").strip()
    if sid and sid in guids:
        return guids[sid], "steamid"
    nick = (profile.get("nick") or "").strip()
    if nick:
        if nick in drivers:
            return nick, "nick"
        low = nick.lower()
        for n in drivers:
            if n.lower() == low:
                return n, "nick"
    return None, None


def build_my_stats(username, stats):
    u = load_users().get(username) or {}
    prof = {"nick": u.get("nick", ""), "steamid": u.get("steamid", "")}
    dname, via = link_driver(prof, stats)
    base = {"linked": bool(dname), "via": via, "nick": prof["nick"], "steamid": prof["steamid"]}
    if not dname:
        return base
    d = stats.get("drivers", {}).get(dname, {})
    secs = d.get("seconds", 0)
    tracks = sorted(d.get("tracks", {}).items(), key=lambda kv: kv[1], reverse=True)
    cars = sorted(d.get("cars", {}).items(), key=lambda kv: kv[1], reverse=True)
    combos = d.get("combos", {})
    fav_combo = max(combos, key=lambda k: combos[k]).split("|") if combos else ["", ""]
    bests = dict(d.get("best", {}))
    if prof["steamid"]:
        for k, v in stats.get("guid_best", {}).get(prof["steamid"], {}).items():
            if k not in bests or (v and v < bests[k]):
                bests[k] = v
    best_list = []
    for k in sorted(bests):
        t, _, c = k.partition("|")
        best_list.append({"track": t, "car": c, "time": _fmt_lap(bests[k])})
    tmax = tracks[0][1] if tracks else 1
    cmax = cars[0][1] if cars else 1
    base.update({
        "driver": dname, "seconds": secs, "has_time": secs > 0,
        "time_str": fmt_duration(secs), "days": len(d.get("days", [])),
        "last_ago": fmt_ago(d.get("last_seen", 0)),
        "fav_track": tracks[0][0] if tracks else "—",
        "fav_car": cars[0][0] if cars else "—",
        "fav_combo": ("%s + %s" % (fav_combo[0], fav_combo[1])) if combos else "—",
        "fav_combo_track": fav_combo[0] if combos else "",
        "fav_combo_car": fav_combo[1] if combos and len(fav_combo) > 1 else "",
        "tracks": [{"name": n, "str": fmt_duration(s), "pct": round(s / tmax * 100)} for n, s in tracks[:10]],
        "cars": [{"name": n, "str": fmt_duration(s), "pct": round(s / cmax * 100)} for n, s in cars[:10]],
        "bests": best_list[:15],
    })
    return base


def build_leaderboard():
    users = load_users()
    stats = load_stats()
    drivers = stats.get("drivers", {})
    rows = []
    for name, u in users.items():
        if u.get("status") != "approved":
            continue
        prof = {"nick": u.get("nick", ""), "steamid": u.get("steamid", "")}
        dname, _via = link_driver(prof, stats)
        d = drivers.get(dname, {}) if dname else {}
        secs = d.get("seconds", 0)
        cars = d.get("cars", {})
        rows.append({"username": name, "nick": prof["nick"], "steamid": prof["steamid"],
                     "seconds": secs, "time_str": fmt_duration(secs),
                     "fav_car": max(cars, key=lambda k: cars[k]) if cars else "—",
                     "last_ago": fmt_ago(d.get("last_seen", 0))})
    rows.sort(key=lambda r: r["seconds"], reverse=True)
    return rows


def _avatar_svg(letter):
    safe = (letter or "?")[:1].replace("&", "").replace("<", "").replace(">", "")
    return (
        '<svg xmlns="http://www.w3.org/2000/svg" width="256" height="256" viewBox="0 0 256 256">'
        '<defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1">'
        '<stop offset="0" stop-color="#7c3aed"/><stop offset="1" stop-color="#4c1d95"/></linearGradient></defs>'
        '<rect width="256" height="256" rx="56" fill="url(#g)"/>'
        '<text x="128" y="168" font-size="120" font-weight="bold" text-anchor="middle"'
        ' fill="#ffffff" font-family="sans-serif">%s</text></svg>' % (safe or "?")
    )


# ---------- маршруты: вход и регистрация ----------

@app.route("/auth")
def auth():
    _name, u = current_user()
    if u and u.get("status") == "approved":
        return redirect(url_for("index"))
    if u:
        return redirect(url_for("waiting"))
    return render_template("auth.html", mode=request.args.get("tab", "login"), error=None)


@app.route("/login", methods=["POST"])
def login():
    login_name = (request.form.get("username") or "").strip()
    pw = request.form.get("password") or ""
    u = load_users().get(login_name)
    if not u or not check_password_hash(u.get("pw", ""), pw):
        return render_template("auth.html", mode="login", error="Неверный логин или пароль")
    session["user"] = login_name
    if u.get("status") != "approved":
        return redirect(url_for("waiting"))
    return redirect(url_for("index"))


@app.route("/register", methods=["POST"])
def register():
    login_name = (request.form.get("username") or "").strip()
    p1 = request.form.get("password") or ""
    p2 = request.form.get("password2") or ""
    users = load_users()
    err = None
    if not USERNAME_RE.match(login_name):
        err = "Логин: 3–20 символов (буквы, цифры, _ . -)"
    elif login_name in users:
        err = "Такой логин уже занят"
    elif len(p1) < 4:
        err = "Пароль слишком короткий (минимум 4 символа)"
    elif p1 != p2:
        err = "Пароли не совпадают"
    if err:
        return render_template("auth.html", mode="register", error=err)
    users[login_name] = {"pw": generate_password_hash(p1), "role": "user",
                         "status": "pending",
                         "created": datetime.now().strftime("%Y-%m-%d %H:%M")}
    save_users(users)
    session["user"] = login_name
    return redirect(url_for("waiting"))


@app.route("/waiting")
def waiting():
    name, u = current_user()
    if not u:
        return redirect(url_for("auth"))
    if u.get("status") == "approved":
        return redirect(url_for("index"))
    return render_template("waiting.html", username=name)


@app.route("/auth_status")
def auth_status():
    _name, u = current_user()
    if not u:
        return jsonify({"logged_in": False})
    return jsonify({"logged_in": True, "status": u.get("status"), "role": u.get("role")})


@app.route("/logout")
def logout():
    session.pop("user", None)
    return redirect(url_for("auth"))


@app.route("/approve", methods=["POST"])
@admin_required
def approve():
    target = (request.form.get("username") or "").strip()
    users = load_users()
    if target in users and users[target].get("status") == "pending":
        users[target]["status"] = "approved"
        save_users(users)
        flash("Доступ выдан: %s" % target, "ok")
    else:
        flash("Заявка не найдена", "error")
    return redirect(url_for("index") + "#tab-requests")


@app.route("/reject", methods=["POST"])
@admin_required
def reject():
    target = (request.form.get("username") or "").strip()
    users = load_users()
    if target in users and users[target].get("status") == "pending":
        del users[target]
        save_users(users)
        flash("Заявка отклонена: %s" % target, "ok")
    else:
        flash("Заявка не найдена", "error")
    return redirect(url_for("index") + "#tab-requests")


@app.route("/delete_user", methods=["POST"])
@admin_required
def delete_user():
    me, _u = current_user()
    target = (request.form.get("username") or "").strip()
    users = load_users()
    if target == me:
        flash("Нельзя удалить себя", "error")
    elif target in users:
        del users[target]
        save_users(users)
        try:
            os.remove(os.path.join(AVATARS_DIR, target + ".png"))
        except OSError:
            pass
        flash("Пользователь удалён: %s" % target, "ok")
    else:
        flash("Пользователь не найден", "error")
    return redirect(url_for("index") + "#tab-requests")


@app.route("/change_admin_password", methods=["POST"])
@admin_required
def change_admin_password():
    me, u = current_user()
    cur = request.form.get("current", "")
    new = request.form.get("new", "")
    conf = request.form.get("confirm", "")
    users = load_users()
    if not check_password_hash(u.get("pw", ""), cur):
        flash("Текущий пароль неверный", "error")
    elif len(new) < 4:
        flash("Новый пароль слишком короткий (минимум 4 символа)", "error")
    elif new != conf:
        flash("Новый пароль и подтверждение не совпадают", "error")
    else:
        users[me]["pw"] = generate_password_hash(new)
        save_users(users)
        flash("Пароль изменён", "ok")
    return redirect(url_for("index") + "#tab-requests")


# ---------- маршруты: профиль и аватарки ----------

@app.route("/save_profile", methods=["POST"])
@login_required
def save_profile():
    me, _u = current_user()
    nick = (request.form.get("nick") or "").strip()[:30]
    steamid = (request.form.get("steamid") or "").strip()
    if not nick:
        flash("Укажи свой ник в игре — по нему находится статистика", "error")
        return redirect(url_for("index") + "#tab-profile")
    if not STEAMID_RE.match(steamid):
        flash("SteamID неверный: нужно 17 цифр, начинается с 7656119 (узнать можно на steamid.io)", "error")
        return redirect(url_for("index") + "#tab-profile")
    users = load_users()
    users[me]["nick"] = nick
    users[me]["steamid"] = steamid
    save_users(users)
    flash("Профиль сохранён", "ok")
    return redirect(url_for("index") + "#tab-profile")


@app.route("/upload_avatar", methods=["POST"])
@login_required
def upload_avatar():
    me, _u = current_user()
    f = request.files.get("file")
    if not f or not f.filename:
        flash("Файл не выбран", "error")
        return redirect(url_for("index") + "#tab-profile")
    if not f.filename.lower().endswith(".png"):
        flash("Только PNG! Пересохрани картинку в PNG и попробуй снова.", "error")
        return redirect(url_for("index") + "#tab-profile")
    head = f.read(8)
    f.seek(0, os.SEEK_END)
    size = f.tell()
    f.seek(0)
    if head != PNG_SIG:
        flash("Это не настоящий PNG-файл", "error")
        return redirect(url_for("index") + "#tab-profile")
    if size > 2 * 1024 * 1024:
        flash("Аватарка больше 2 МБ — сожми её и попробуй снова", "error")
        return redirect(url_for("index") + "#tab-profile")
    os.makedirs(AVATARS_DIR, exist_ok=True)
    f.save(os.path.join(AVATARS_DIR, me + ".png"))
    flash("Аватарка обновлена", "ok")
    return redirect(url_for("index") + "#tab-profile")


@app.route("/avatar/<username>")
@login_required
def avatar(username):
    if USERNAME_RE.match(username):
        p = os.path.join(AVATARS_DIR, username + ".png")
        if os.path.isfile(p):
            resp = send_file(p, mimetype="image/png", conditional=True)
            resp.headers["Cache-Control"] = "no-cache"
            return resp
        letter = username[:1].upper()
    else:
        letter = "?"
    return Response(_avatar_svg(letter), mimetype="image/svg+xml",
                    headers={"Cache-Control": "no-store"})


# ---------- маршруты: панель ----------

def build_join_link(ip, http_port, password):
    """Race invite ссылка для друзей: открывает CM и заходит на сервер. Пароль вшит в base64."""
    link = "https://acstuff.club/s/q:race/online/join?ip=%s&httpPort=%s" % (ip or "", http_port or "8081")
    if password:
        pw = base64.b64encode(password.encode("utf-8")).decode("ascii")
        link += "&password=" + quote(pw, safe="")
    return link


def _servers_ctx():
    out = []
    for x in SERVER_INSTANCES:
        name = ""
        try:
            ls = read_cfg_lines(x["id"])
            name = strip_cm_suffix(get_cfg_value(ls, "SERVER", "NAME", ""))
        except Exception:
            pass
        out.append({"id": x["id"], "label": x["label"], "running": is_server_running(x["id"]),
                    "exists": srv_exists(x["id"]), "name": name})
    return out


@app.route("/")
@login_required
def index():
    me, u = current_user()
    is_admin = (u.get("role") == "admin")
    srv = valid_srv(request.args.get("srv", "main"))
    lines = read_cfg_lines(srv)
    cfg = {}
    for field, section, key in SETTINGS_FIELDS:
        cfg[field] = get_cfg_value(lines, section, key, DEFAULTS.get(field, ""))
    try:
        _amb = float((cfg.get("temp_ambient") or "").strip().replace(",", "."))
        _off = float((cfg.get("temp_road") or "").strip().replace(",", "."))
        cfg["temp_road"] = "%g" % (_amb + _off)
    except (ValueError, AttributeError):
        pass
    cfg["name"] = strip_cm_suffix(cfg.get("name", ""))
    cars = list_cars()
    tracks = list_tracks()
    track_layouts = {t["id"]: t.get("layouts", []) for t in tracks}
    entries = parse_entry_list(srv)
    track_name = cfg.get("track", "")
    for t in tracks:
        if t["id"] == cfg.get("track"):
            track_name = t["name"]
            break
    models = []
    for e in entries:
        if e.get("MODEL") and e["MODEL"] not in models:
            models.append(e["MODEL"])
    if not models:
        server_cars = get_cfg_value(lines, "SERVER", "CARS", "")
        models = [m for m in server_cars.split(";") if m]
    cars_str = ", ".join(models) if models else "—"
    server_host = (request.host or "").rsplit(":", 1)[0]
    pending_users, all_users = [], []
    if is_admin:
        for n, d in load_users().items():
            row = {"name": n, "role": d.get("role", "user"),
                   "status": d.get("status", ""), "created": d.get("created", "")}
            all_users.append(row)
            if d.get("status") == "pending":
                pending_users.append(row)
        all_users.sort(key=lambda r: r["name"])
    stats = load_stats()
    return render_template("index.html", running=is_server_running(srv), cfg=cfg,
                           cars=cars, tracks=tracks, track_layouts=track_layouts,
                           entries=entries, welcome=read_welcome(srv),
                           blacklist=read_blacklist(srv), server_host=server_host,
                           track_name=track_name, cars_str=cars_str,
                           username=me, is_admin=is_admin,
                           srv=srv, can_edit=can_edit_server(srv, u),
                           servers=_servers_ctx(),
                           cm_description=read_cmdesc(srv), cm_port=CM_SIDECAR_PORTS[srv],
                           cm_on=bool(read_cmdesc(srv).strip()),
                           cm_live=CM_SIDECAR_STATUS.get(srv, False),
                           setup_needed=any(not pub_ready(x) for x in ("pub1", "pub2")),
                           pending_users=pending_users, all_users=all_users,
                           profile=get_profile(me),
                           my_stats=build_my_stats(me, stats),
                           leaderboard=build_leaderboard(),
                           join_link=build_join_link(server_host, cfg.get("http_port") or "8081",
                                                     cfg.get("password") or ""))


@app.route("/start", methods=["POST"])
@login_required
def start():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    ready = srv_exists(srv) if srv == "main" else pub_ready(srv)
    if not ready:
        flash("Сервер ещё не создан или недосоздан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    start_server_proc(srv)
    flash("Сервер запускается… Смотри вкладку «Логи»", "ok")
    return redirect(url_for("index") + "?srv=" + srv)


@app.route("/stop", methods=["POST"])
@login_required
def stop():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    stop_server_proc(srv)
    flash("Сервер остановлен", "ok")
    return redirect(url_for("index") + "?srv=" + srv)


@app.route("/restart", methods=["POST"])
@login_required
def restart():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    ready = srv_exists(srv) if srv == "main" else pub_ready(srv)
    if not ready:
        flash("Сервер ещё не создан или недосоздан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    stop_server_proc(srv)
    time.sleep(2)
    start_server_proc(srv)
    flash("Сервер перезапускается…", "ok")
    return redirect(url_for("index") + "?srv=" + srv)


def remove_cfg_sections(sections, srv="main"):
    """Удалить секции из server_cfg.ini целиком. Возвращает реально удалённые."""
    want = {x.upper() for x in sections}
    lines = read_cfg_lines(srv)
    new_lines, removed, skip = [], [], False
    for line in lines:
        t = line.strip()
        if t.startswith("[") and t.endswith("]"):
            name = t[1:-1].strip().upper()
            skip = name in want
            if skip:
                if name not in removed:
                    removed.append(name)
                continue
        if not skip:
            new_lines.append(line)
    if removed:
        with open(srv_cfg(srv), "w", encoding="utf-8") as f:
            f.writelines(new_lines)
    return removed


@app.route("/save", methods=["POST"])
@login_required
def save_settings():
    tab = request.form.get("form_tab", "all")
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    if srv != "main" and not srv_exists(srv):
        flash("Сервер ещё не создан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    updates = []
    for field, section, key in SETTINGS_FIELDS:
        is_race = field in RACE_TAB_FIELDS
        if tab == "race" and not is_race:
            continue
        if tab == "server" and is_race:
            continue
        if field in CHECKBOX_FIELDS:
            v = "1" if str(request.form.get(field, "0")) in ("1", "on", "true", "True") else "0"
        else:
            v = (request.form.get(field, "") or "").strip()
        updates.append((section, key, v))
    # дорога = воздух + поправка: в поле вводят ИТОГ, в конфиг пишем поправку
    try:
        _amb = float((request.form.get("temp_ambient", "") or "").strip().replace(",", "."))
        _tgt = float((request.form.get("temp_road", "") or "").strip().replace(",", "."))
        _off = "%g" % (_tgt - _amb)
        updates = [(sn, k, _off) if (sn, k) == ("WEATHER_0", "BASE_TEMPERATURE_ROAD") else (sn, k, v)
                   for sn, k, v in updates]
    except ValueError:
        pass
    _cm_on = bool(read_cmdesc(srv).strip())
    _fixed = []
    for _sn, _k, _v in updates:
        if (_sn, _k) == ("SERVER", "NAME"):
            _clean = strip_cm_suffix(_v)
            _v = _clean + cm_suffix(srv) if _cm_on else _clean
        _fixed.append((_sn, _k, _v))
    updates = _fixed
    set_cfg_values(updates, srv)
    removed = remove_cfg_sections(("WEATHER_1", "WEATHER_2"), srv)
    msg = "Настройки сохранены. Перезапусти сервер кнопкой «Перезапуск», чтобы применить."
    if removed:
        msg += " Убраны лишние секции погоды (%s) — они перебивали основную." % ", ".join(removed)
    flash(msg, "ok")
    return redirect(url_for("index") + "?srv=" + srv)


@app.route("/save_entries", methods=["POST"])
@login_required
def save_entries():
    data = request.get_json(silent=True)
    if data is None:
        try:
            data = json.loads(request.form.get("entries_json", "[]"))
        except Exception:
            data = []
    srv = "main"
    if isinstance(data, dict):
        srv = valid_srv(data.get("srv", "main"))
    else:
        srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        if request.is_json:
            return jsonify({"ok": False, "error": "admin only"}), 403
        return denied
    if srv != "main" and not srv_exists(srv):
        if request.is_json:
            return jsonify({"ok": False, "error": "not created"}), 404
    if srv != "main" and not srv_exists(srv):
        flash("Сервер ещё не создан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    entries = data if isinstance(data, list) else data.get("entries", [])
    clean = []
    for e in entries:
        model = str(e.get("MODEL", "")).strip()
        if not model:
            continue
        clean.append({
            "MODEL": model,
            "SKIN": str(e.get("SKIN", "")).strip(),
            "SPECTATOR_MODE": "1" if str(e.get("SPECTATOR_MODE", "0")) in ("1", "on", "true") else "0",
            "DRIVERNAME": str(e.get("DRIVERNAME", "")).strip(),
            "TEAM": str(e.get("TEAM", "")).strip(),
            "GUID": str(e.get("GUID", "")).strip(),
            "BALLAST": str(e.get("BALLAST", "0")).strip() or "0",
            "RESTRICTOR": str(e.get("RESTRICTOR", "0")).strip() or "0",
        })
    write_entry_list(clean, srv)
    models = []
    for c in clean:
        if c["MODEL"] not in models:
            models.append(c["MODEL"])
    updates = [("SERVER", "CARS", ";".join(models))]
    if clean:
        updates.append(("SERVER", "MAX_CLIENTS", str(len(clean))))
    set_cfg_values(updates, srv)
    if request.is_json:
        return jsonify({"ok": True, "count": len(clean)})
    flash("Слоты сохранены (%d). CARS и MAX_CLIENTS обновлены." % len(clean), "ok")
    return redirect(url_for("index") + "?srv=" + srv + "#tab-cars")


@app.route("/save_welcome", methods=["POST"])
@login_required
def save_welcome():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    if srv != "main" and not srv_exists(srv):
        flash("Сервер ещё не создан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    text = request.form.get("welcome", "")
    ok = False
    for p in srv_welcome_paths(srv):
        try:
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as f:
                f.write(text)
            ok = True
        except Exception:
            pass
    if ok:
        flash("Описание сохранено. Появится в поиске серверов после перезапуска игрового сервера (кнопка \u21bb вверху).", "ok")
    else:
        flash("Не получилось записать файл приветствия", "error")
    return redirect(url_for("index") + "?srv=" + srv + "#tab-server")


@app.route("/save_blacklist", methods=["POST"])
@login_required
def save_blacklist():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    if srv != "main" and not srv_exists(srv):
        flash("Сервер ещё не создан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    text = request.form.get("blacklist", "")
    guids = [l.strip() for l in text.replace(",", "\n").splitlines() if l.strip()]
    try:
        bp = srv_blacklist(srv)
        os.makedirs(os.path.dirname(bp), exist_ok=True)
        with open(bp, "w", encoding="utf-8") as f:
            f.write("\n".join(guids) + ("\n" if guids else ""))
        flash("Список сохранён (%d). Перезапусти сервер, чтобы применить." % len(guids), "ok")
    except Exception as e:
        flash("Ошибка записи: %s" % e, "error")
    return redirect(url_for("index") + "?srv=" + srv + "#tab-server")


def _upload_answer(want_json, msg, kind):
    """Ответ загрузки мода: JSON для XHR (с прогресс-баром) или flash+redirect для обычной формы."""
    if want_json:
        code = 200 if kind == "ok" else 400
        return jsonify(ok=(kind == "ok"), message=msg,
                       redirect=url_for("index") + "#tab-mods"), code
    flash(msg, kind)
    return redirect(url_for("index") + "#tab-mods")


def _find_rar_tool():
    for t in ("unrar", "7z", "unar", "bsdtar"):
        if shutil.which(t):
            return t
    return None


def _extract_rar(archive, destdir):
    """Распаковать .rar системной утилитой. Кидает RuntimeError с понятным текстом."""
    tool = _find_rar_tool()
    if not tool:
        raise RuntimeError("NO_BACKEND")
    if tool == "unrar":
        cmd = ["unrar", "x", "-o+", "-p-", "-y", archive, destdir + os.sep]
    elif tool == "7z":
        cmd = ["7z", "x", "-y", "-bd", "-o" + destdir, archive]
    elif tool == "unar":
        cmd = ["unar", "-f", "-q", "-o", destdir, archive]
    else:
        cmd = ["bsdtar", "-xf", archive, "-C", destdir]
    try:
        p = subprocess.run(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                           stderr=subprocess.PIPE, timeout=600)
    except subprocess.TimeoutExpired:
        raise RuntimeError("Распаковка заняла больше 10 минут — попробуй другой архив")
    if p.returncode != 0:
        out = ((p.stderr or b"") + b"\n" + (p.stdout or b"")).decode("utf-8", "ignore")
        if "password" in out.lower():
            raise RuntimeError("Архив защищён паролем — распакуй его на компьютере и упакуй заново без пароля")
        lines = out.strip().splitlines()
        detail = lines[-1][:160] if lines else ("код %d" % p.returncode)
        raise RuntimeError("Не получилось распаковать RAR (%s): %s" % (tool, detail))
    base = os.path.realpath(destdir) + os.sep
    for root, _dirs, files in os.walk(destdir):
        for n in files:
            if not os.path.realpath(os.path.join(root, n)).startswith(base):
                raise RuntimeError("Подозрительный архив: пути выходят за пределы папки")


def _is_pack_dir(path, name):
    return os.path.isdir(os.path.join(path, name)) and name.lower() in ("cars", "tracks")


def _move_one(src, dst):
    if os.path.isdir(src):
        if os.path.exists(dst):
            shutil.rmtree(dst)
        shutil.move(src, dst)
    else:
        shutil.move(src, dst)


@app.route("/upload", methods=["POST"])
@login_required
def upload_mod():
    mod_type = request.form.get("mod_type", "car")
    want_json = request.headers.get("X-Requested-With") == "XMLHttpRequest"
    f = request.files.get("file")
    if not f or not f.filename:
        return _upload_answer(want_json, "Файл не выбран", "error")
    filename = secure_filename(f.filename)
    low = filename.lower()
    is_zip, is_rar = low.endswith(".zip"), low.endswith(".rar")
    if not (is_zip or is_rar):
        return _upload_answer(want_json, "Можно загружать только .zip и .rar архивы", "error")
    target_dir = CONTENT_CARS if mod_type == "car" else CONTENT_TRACKS
    os.makedirs(target_dir, exist_ok=True)
    tmp_zip = os.path.join(tempfile.gettempdir(), "ac_" + filename)
    f.save(tmp_zip)
    try:
        tmpdir = tempfile.mkdtemp(prefix="ac_extract_")
        if is_zip:
            with zipfile.ZipFile(tmp_zip) as z:
                z.extractall(tmpdir)
        elif _find_rar_tool() is None:
            return _upload_answer(want_json, "На сервере нет распаковщика RAR. Выполни на VDS: sudo apt update && sudo apt install -y unrar — и перезапусти панель.", "error")
        else:
            try:
                _extract_rar(tmp_zip, tmpdir)
            except RuntimeError as e:
                return _upload_answer(want_json, str(e), "error")
        items = [i for i in os.listdir(tmpdir) if i != "__MACOSX"]
        if not items:
            return _upload_answer(want_json, "Архив пустой", "error")
        # паки: папки cars/ и tracks/ на верхнем уровне (или на уровень ниже под папкой-обёрткой)
        base = tmpdir
        if len(items) == 1:
            only = os.path.join(tmpdir, items[0])
            if os.path.isdir(only):
                sub = [i for i in os.listdir(only) if i != "__MACOSX"]
                if any(_is_pack_dir(only, i) for i in sub):
                    base, items = only, sub
        pack_dirs = {i for i in items if _is_pack_dir(base, i)}
        rest = [i for i in items if i not in pack_dirs]
        installed_cars, installed_tracks, installed_rest = [], [], []
        for pd in sorted(pack_dirs):
            is_cars = (pd.lower() == "cars")
            dest = CONTENT_CARS if is_cars else CONTENT_TRACKS
            os.makedirs(dest, exist_ok=True)
            bucket = installed_cars if is_cars else installed_tracks
            for child in sorted(os.listdir(os.path.join(base, pd))):
                if child == "__MACOSX":
                    continue
                _move_one(os.path.join(base, pd, child), os.path.join(dest, child))
                bucket.append(child)
        if len(rest) == 1 and os.path.isdir(os.path.join(base, rest[0])):
            _move_one(os.path.join(base, rest[0]), os.path.join(target_dir, rest[0]))
            installed_rest.append(rest[0])
        else:
            for i in rest:
                _move_one(os.path.join(base, i), os.path.join(target_dir, i))
                installed_rest.append(i)
        parts = []
        if installed_cars:
            parts.append("машины: " + ", ".join(installed_cars))
        if installed_tracks:
            parts.append("трассы: " + ", ".join(installed_tracks))
        if installed_rest:
            parts.append(", ".join(installed_rest))
        if not parts:
            return _upload_answer(want_json, "В архиве нет модов (папки cars/tracks пустые)", "error")
        shutil.rmtree(tmpdir, ignore_errors=True)
        return _upload_answer(want_json, "Установлено: %s. Перезапусти сервер." % "; ".join(parts), "ok")
    except zipfile.BadZipFile:
        return _upload_answer(want_json, "Битый ZIP-архив", "error")
    except Exception as e:
        return _upload_answer(want_json, "Ошибка распаковки: %s" % e, "error")
    finally:
        try:
            os.remove(tmp_zip)
        except Exception:
            pass


@app.route("/delete_mod", methods=["POST"])
@login_required
def delete_mod():
    mod_type = request.form.get("mod_type", "car")
    name = (request.form.get("name", "") or "").strip()
    if not name or not SAFE_NAME.match(name) or ".." in name or "/" in name:
        flash("Некорректное имя", "error")
        return redirect(url_for("index") + "#tab-mods")
    base = CONTENT_CARS if mod_type == "car" else CONTENT_TRACKS
    target = os.path.realpath(os.path.join(base, name))
    if not target.startswith(os.path.realpath(base) + os.sep) or not os.path.isdir(target):
        flash("Папка не найдена", "error")
        return redirect(url_for("index") + "#tab-mods")
    try:
        shutil.rmtree(target)
        flash("Удалено: %s" % name, "ok")
    except Exception as e:
        flash("Ошибка удаления: %s" % e, "error")
    return redirect(url_for("index") + "#tab-mods")


@app.route("/api/skins/<model>")
@login_required
def api_skins(model):
    if not SAFE_NAME.match(model):
        return jsonify({"skins": []})
    return jsonify({"skins": get_car_skins(model)})


# ---------- превью машин и трасс ----------

PLACEHOLDER_CAR_SVG = (
    '<svg xmlns="http://www.w3.org/2000/svg" width="640" height="360" viewBox="0 0 640 360">'
    '<defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1">'
    '<stop offset="0" stop-color="#150a2e"/><stop offset="1" stop-color="#2c1658"/></linearGradient></defs>'
    '<rect width="640" height="360" fill="url(#g)"/>'
    '<circle cx="540" cy="60" r="150" fill="#a855f7" opacity="0.12"/>'
    '<text x="320" y="178" font-size="92" text-anchor="middle">\U0001F3CE\uFE0F</text>'
    '<text x="320" y="255" font-size="26" fill="#a78bfa" text-anchor="middle" font-family="sans-serif">'
    'Нет превью в моде</text></svg>'
)
PLACEHOLDER_TRACK_SVG = (
    '<svg xmlns="http://www.w3.org/2000/svg" width="640" height="360" viewBox="0 0 640 360">'
    '<defs><linearGradient id="g" x1="0" y1="0" x2="1" y2="1">'
    '<stop offset="0" stop-color="#120826"/><stop offset="1" stop-color="#2c1658"/></linearGradient></defs>'
    '<rect width="640" height="360" fill="url(#g)"/>'
    '<circle cx="100" cy="300" r="150" fill="#a855f7" opacity="0.12"/>'
    '<text x="320" y="178" font-size="92" text-anchor="middle">\U0001F3C1</text>'
    '<text x="320" y="255" font-size="26" fill="#a78bfa" text-anchor="middle" font-family="sans-serif">'
    'Нет превью в моде</text></svg>'
)


def _safe_join(base, *parts):
    real_base = os.path.realpath(base)
    target = os.path.realpath(os.path.join(real_base, *parts))
    if target != real_base and not target.startswith(real_base + os.sep):
        return None
    return target


def _parts_ok(*parts):
    return all(p and "/" not in p and "\\" not in p and ".." not in p for p in parts)


def _resolve_ci(path):
    """Возвращает путь к файлу, игнорируя регистр имени (или None)."""
    if os.path.isfile(path):
        return path
    d = os.path.dirname(path)
    b = os.path.basename(path).lower()
    try:
        for e in os.listdir(d):
            if e.lower() == b:
                p = os.path.join(d, e)
                if os.path.isfile(p):
                    return p
    except OSError:
        pass
    return None


def _car_image_candidates(model, skin=None):
    if not _parts_ok(model) or (skin and not _parts_ok(skin)):
        return []
    cands = []
    if skin:
        cands += [os.path.join(PREVIEWS_DIR, "cars", model, skin + e) for e in IMG_EXTS]
    cands += [os.path.join(PREVIEWS_DIR, "cars", model + e) for e in IMG_EXTS]
    base = os.path.realpath(CONTENT_CARS)
    if skin:
        d = _safe_join(base, model, "skins", skin)
        if d:
            cands += [os.path.join(d, n) for n in PREVIEW_NAMES]
    skins_dir = _safe_join(base, model, "skins")
    if skins_dir and os.path.isdir(skins_dir):
        try:
            skins = sorted(x for x in os.listdir(skins_dir)
                           if os.path.isdir(os.path.join(skins_dir, x)))
        except OSError:
            skins = []
        for s in skins[:30]:
            cands += [os.path.join(skins_dir, s, n) for n in PREVIEW_NAMES]
    for sub in ((), ("ui",)):
        d = _safe_join(base, model, *sub)
        if d:
            cands += [os.path.join(d, n) for n in PREVIEW_NAMES]
    return cands


def _track_image_candidates(track):
    if not _parts_ok(track):
        return []
    cands = [os.path.join(PREVIEWS_DIR, "tracks", track + e) for e in IMG_EXTS]
    base = os.path.realpath(CONTENT_TRACKS)
    ui = _safe_join(base, track, "ui")
    if ui:
        cands += [os.path.join(ui, n) for n in PREVIEW_NAMES]
        try:
            layouts = sorted(x for x in os.listdir(ui)
                             if os.path.isdir(os.path.join(ui, x)))
        except OSError:
            layouts = []
        for lay in layouts[:30]:
            d = _safe_join(base, track, "ui", lay)
            if d:
                cands += [os.path.join(d, n) for n in PREVIEW_NAMES]
        cands.append(os.path.join(ui, "map.png"))
    root = _safe_join(base, track)
    if root:
        cands += [os.path.join(root, n) for n in PREVIEW_NAMES]
        cands.append(os.path.join(root, "map.png"))
    return cands


def _send_image(path):
    low = path.lower()
    if low.endswith(".png"):
        mime = "image/png"
    elif low.endswith(".webp"):
        mime = "image/webp"
    else:
        mime = "image/jpeg"
    resp = send_file(path, mimetype=mime, conditional=True)
    resp.headers["Cache-Control"] = "no-cache"
    return resp


def _placeholder(svg):
    resp = Response(svg, mimetype="image/svg+xml")
    resp.headers["Cache-Control"] = "no-store"
    return resp


def _serve_image(cands, placeholder, debug_info):
    found = None
    for c in cands:
        hit = _resolve_ci(c)
        if hit:
            found = hit
            break
    if request.args.get("debug") == "1":
        return jsonify({"query": debug_info, "found": found,
                        "checked": [{"path": c, "exists": os.path.isfile(c)} for c in cands[:200]]})
    if found:
        return _send_image(found)
    return _placeholder(placeholder)


@app.route("/img/car/<model>")
@app.route("/img/car/<model>/<skin>")
@login_required
def img_car(model, skin=None):
    return _serve_image(_car_image_candidates(model, skin), PLACEHOLDER_CAR_SVG,
                        {"model": model, "skin": skin})


@app.route("/img/track/<track>")
@login_required
def img_track(track):
    return _serve_image(_track_image_candidates(track), PLACEHOLDER_TRACK_SVG,
                        {"track": track})


@app.route("/upload_preview", methods=["POST"])
@login_required
def upload_preview():
    mod_type = request.form.get("mod_type", "car")
    name = (request.form.get("name", "") or "").strip()
    skin = (request.form.get("skin", "") or "").strip()
    f = request.files.get("file")
    if not name or "/" in name or "\\" in name or ".." in name:
        flash("Укажи точное имя папки мода (без слешей)", "error")
        return redirect(url_for("index") + "#tab-mods")
    if skin and ("/" in skin or "\\" in skin or ".." in skin):
        flash("Некорректное имя скина", "error")
        return redirect(url_for("index") + "#tab-mods")
    if not f or not f.filename:
        flash("Файл не выбран", "error")
        return redirect(url_for("index") + "#tab-mods")
    ext = os.path.splitext(f.filename)[1].lower()
    if ext not in IMG_EXTS:
        flash("Только картинки: JPG или PNG", "error")
        return redirect(url_for("index") + "#tab-mods")
    if mod_type == "car" and skin:
        dest_dir = os.path.join(PREVIEWS_DIR, "cars", name)
        dest = os.path.join(dest_dir, skin + ext)
    elif mod_type == "car":
        dest_dir = os.path.join(PREVIEWS_DIR, "cars")
        dest = os.path.join(dest_dir, name + ext)
    else:
        dest_dir = os.path.join(PREVIEWS_DIR, "tracks")
        dest = os.path.join(dest_dir, name + ext)
    os.makedirs(dest_dir, exist_ok=True)
    base = os.path.splitext(dest)[0]
    for e in IMG_EXTS:
        if base + e != dest and os.path.exists(base + e):
            os.remove(base + e)
    f.save(dest)
    flash("Превью сохранено. Обнови страницу (Ctrl+F5).", "ok")
    return redirect(url_for("index") + "#tab-mods")


@app.route("/save_cmdesc", methods=["POST"])
@login_required
def save_cmdesc():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    if srv != "main" and not srv_exists(srv):
        flash("Сервер ещё не создан (кнопка «Создать паблики» вверху).", "error")
        return redirect(url_for("index") + "?srv=" + srv)
    text = (request.form.get("cm_description", "") or "").replace("\r\n", "\n").replace("\r", "\n")
    try:
        os.makedirs(os.path.dirname(cm_desc_path(srv)), exist_ok=True)
        with open(cm_desc_path(srv), "w", encoding="utf-8") as f:
            f.write(text)
    except OSError as e:
        flash("Не получилось записать описание: %s" % e, "error")
        return redirect(url_for("index") + "?srv=" + srv + "#tab-server")
    cur = get_cfg_value(read_cfg_lines(srv), "SERVER", "NAME", "")
    clean = strip_cm_suffix(cur)
    want = clean + cm_suffix(srv) if text.strip() else clean
    if want != cur:
        set_cfg_values([("SERVER", "NAME", want)], srv)
    flash("Описание для Content Manager сохранено. Перезапусти игровой сервер кнопкой «Перезапуск», чтобы применить.", "ok")
    return redirect(url_for("index") + "?srv=" + srv + "#tab-server")


@app.route("/logs")
@login_required
def logs():
    srv = valid_srv(request.args.get("srv", "main"))
    try:
        n = int(request.args.get("lines", "200"))
    except ValueError:
        n = 200
    n = max(20, min(n, 2000))
    lines = []
    p = srv_log(srv)
    if os.path.exists(p):
        with open(p, "r", encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()[-n:]
    return jsonify({"running": is_server_running(srv), "lines": lines})


@app.route("/download_log")
@login_required
def download_log():
    srv = valid_srv(request.args.get("srv", "main"))
    p = srv_log(srv)
    if not os.path.exists(p):
        flash("Лог-файл ещё не создан (сервер не запускался)", "error")
        return redirect(url_for("index") + "?srv=" + srv + "#tab-logs")
    try:
        return send_file(p, as_attachment=True, download_name="acserver-%s.log" % srv)
    except TypeError:
        return send_file(p, as_attachment=True, attachment_filename="acserver-%s.log" % srv)


@app.route("/clear_log", methods=["POST"])
@login_required
def clear_log():
    srv = valid_srv(request.form.get("srv", "main"))
    denied = _need_edit(srv)
    if denied:
        return denied
    try:
        open(srv_log(srv), "w", encoding="utf-8").write("")
        flash("Лог очищен", "ok")
    except Exception as e:
        flash("Ошибка: %s" % e, "error")
    return redirect(url_for("index") + "?srv=" + srv + "#tab-logs")


@app.route("/stats")
@login_required
def stats():
    try:
        load1, _, _ = os.getloadavg()
        ncpu = os.cpu_count() or 1
        cpu = round(load1 / ncpu * 100)
    except Exception:
        cpu = None
    ram_used = ram_total = None
    try:
        mem = {}
        with open("/proc/meminfo") as f:
            for line in f:
                k, _, v = line.partition(":")
                mem[k.strip()] = int(v.split()[0])
        ram_total = mem.get("MemTotal", 0) // 1024
        ram_used = (mem.get("MemTotal", 0) - mem.get("MemAvailable", 0)) // 1024
    except Exception:
        pass
    disk_pct = disk_used = disk_total = None
    try:
        du = shutil.disk_usage("/")
        disk_pct = round(du.used / du.total * 100)
        disk_used = round(du.used / 1024 ** 3, 1)
        disk_total = round(du.total / 1024 ** 3, 1)
    except Exception:
        pass
    return jsonify({"cpu": cpu, "ram_used": ram_used, "ram_total": ram_total,
                    "disk_pct": disk_pct, "disk_used": disk_used, "disk_total": disk_total,
                    "uptime": _uptime_str()})


@app.route("/api/tracker")
@admin_required
def api_tracker():
    st = load_stats()
    sf = {"exists": os.path.isfile(STATS_PATH), "size": 0, "updated": 0,
          "drivers": 0, "guids": 0, "names": []}
    if sf["exists"]:
        try:
            sf["size"] = os.path.getsize(STATS_PATH)
        except OSError:
            pass
        sf["updated"] = (st.get("meta") or {}).get("updated", 0)
        dr = st.get("drivers") or {}
        sf["drivers"] = len(dr)
        sf["guids"] = len(st.get("guids") or {})
        try:
            sf["names"] = sorted(dr.keys(), key=lambda n: dr[n].get("seconds", 0),
                                 reverse=True)[:12]
        except Exception:
            sf["names"] = sorted(dr.keys())[:12]
    res_n = 0
    try:
        if os.path.isdir(RESULTS_DIR):
            res_n = sum(1 for f in os.listdir(RESULTS_DIR) if f.lower().endswith(".json"))
    except OSError:
        pass
    return jsonify({"now": int(time.time()), "interval": TRACK_INTERVAL,
                    "server_running": is_server_running(),
                    "tracker": dict(TRACKER_STATUS),
                    "probe": dict(LAST_PROBE),
                    "udp": dict(UDP_STATUS), "udp_track": UDP_TRACK,
                    "udp_roster": udp_roster_snapshot(),
                    "cfg_path": CFG_PATH,
                    "stats_file": sf,
                    "results_files": res_n})


@app.route("/pilot/<username>")
@login_required
def pilot(username):
    users = load_users()
    u = users.get(username)
    if not u or u.get("status") != "approved":
        flash("Пилот не найден.")
        return redirect(url_for("index"))
    me, meu = current_user()
    return render_template("pilot.html", username=me,
                           is_admin=(meu.get("role") == "admin"),
                           pilot_name=username, pilot_nick=u.get("nick", ""),
                           pilot_stats=build_my_stats(username, load_stats()))


@app.route("/online")
@login_required
def online():
    srv = valid_srv(request.args.get("srv", "main"))
    lines = read_cfg_lines(srv)
    http_port = get_cfg_value(lines, "SERVER", "HTTP_PORT", "8081") or "8081"
    maxc = get_cfg_value(lines, "SERVER", "MAX_CLIENTS", "")
    if srv != "main":
        info, _err, _meta = _http_json("http://127.0.0.1:%s/INFO" % http_port)
        if not isinstance(info, dict):
            return jsonify({"ok": False, "running": is_server_running(srv)})
        try:
            clients = int(info.get("clients") or 0)
        except (TypeError, ValueError):
            clients = 0
        return jsonify({"ok": True, "running": True, "count": clients, "max": maxc,
                        "track": info.get("track") or "", "players": []})
    res = _live_players(lines, http_port)
    if res is None:
        return jsonify({"ok": False, "running": is_server_running()})
    live_players, track, _source = res
    players = [{"name": p["name"], "car": p["car"], "best": _fmt_lap(p["best"]),
                "speed": ("%d км/ч" % p["speed"]) if p["speed"] > 0 else "—"}
               for p in live_players]
    count = len(players) or LAST_PROBE.get("info_clients", 0)
    return jsonify({"ok": True, "running": True, "count": count, "max": maxc,
                    "track": track, "players": players})


@app.errorhandler(413)
def too_large(_e):
    if request.headers.get("X-Requested-With") == "XMLHttpRequest":
        return jsonify(ok=False, message="Файл слишком большой (лимит 10 ГБ)",
                       redirect=url_for("index") + "#tab-mods"), 413
    flash("Файл слишком большой (лимит 10 ГБ)", "error")
    return redirect(url_for("index") + "#tab-mods")


if __name__ == "__main__":
    try:
        scan_results()
    except Exception:
        pass
    start_tracker()
    start_cm_sidecars()
    app.run(host="0.0.0.0", port=8772, threaded=True)
