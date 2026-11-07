#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Barez Tire Stock Monitor (v3)
=============================
مانیتور موجودی فروشگاه آنلاین بارز (shop.barez.org) از مسیر ویزارد خرید
دکاپست (آذربایجان شرقی / تبریز).

v3 changes:
  * تشخیص موجودی از روی جدول رندرشدهٔ HTML (ردیف‌های clickableRow) — چون
    serverMemo.data.products در این سایت همیشه خالی است و باعث می‌شد اسکریپت
    «اتمام موجودی» اشتباه اعلام کند (باگ ساعت ۱۲:۱۵).
  * زمان‌بندی فعال فقط در بازه‌های ساعت تهران: ۰۷:۰۰–۰۹:۰۰ و ۱۰:۰۰–۱۵:۰۰؛
    داخل بازه‌ها هر ۳ دقیقه یک بررسی، بیرون بازه‌ها بدون بررسی و بدون پیام.
  * ضددرخغ: اگر ساختار صفحه تغییر کند «بی‌خبری» اعلام نمی‌شود؛ پیام‌های
    ضربان بی‌خبری حداکثر ساعتی یک‌بار است.

Usage:
  python3 barez_monitor.py --check          # one manual check (outside windows too)
  python3 barez_monitor.py --loop           # ensure background worker is running
  python3 barez_monitor.py --setup-bale     # auto-discover chat_id from getUpdates
  python3 barez_monitor.py --test-notify    # send a test message to Bale
  python3 barez_monitor.py --status         # print current state
  python3 barez_monitor.py --reset-state    # clear known-stock state
"""
import argparse
import base64
import datetime
import html as htmllib
import json
import os
import random
import re
import subprocess
import sys
import time
import traceback
import urllib.parse

import requests

BASE = "https://shop.barez.org"
START_URL = f"{BASE}/start-live"
BUY_LINK = "https://shop.barez.org/start-live"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36")

# PORTABLE: all files live next to this script (works on any laptop/PC)
HERE = os.path.dirname(os.path.abspath(__file__))
CONFIG_PATH = os.path.join(HERE, "barez_monitor_config.json")
STATE_PATH = os.path.join(HERE, "barez_state.json")
LOG_PATH = os.path.join(HERE, "barez_monitor.log")
NOTIFY_PATH = os.path.join(HERE, "last_notification.txt")
LOCK_PATH = os.path.join(HERE, "barez_loop.lock")

LOOP_INTERVAL = 180      # seconds between checks inside the worker (3 min)
LOOP_CAP = 28800         # worker lifetime cap ≈ 8 h (covers both daily windows)
LOCK_FRESH = 420         # lockfile older than 7 min => stale, respawn

# active checking windows in TEHRAN local time (start, end) — end exclusive
ACTIVE_WINDOWS = [((7, 0), (9, 0)), ((10, 0), (15, 0))]
TEHRAN_TZ = datetime.timezone(datetime.timedelta(hours=3, minutes=30))

HEARTBEAT_EVERY = 3600   # max one idle heartbeat per hour (inside windows)
NUDGE_EVERY = 1800       # max one "still available" nudge per 30 min

DEFAULT_DELIVERY_NAME = "ارسال سراسری با دکاپست (انبار مرکزی بارز)"

DEFAULT_CONFIG = {
    "province_id": "1",
    "city_id": "1",
    "province_name": "آذربایجان شرقی",
    "city_name": "تبریز",
    "delivery_type": "dekapost",
    "delivery_name": DEFAULT_DELIVERY_NAME,
    "bale_token": "",
    "bale_chat_id": "",
    "relay_status": False
}


# ---------------------------------------------------------------- utilities
def log(msg):
    line = f"[{datetime.datetime.now().isoformat(timespec='seconds')}] {msg}"
    print(line)
    try:
        with open(LOG_PATH, "a", encoding="utf-8") as f:
            f.write(line + "\n")
    except OSError:
        pass


def load_json(path, default):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, data):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=1)


def load_config():
    cfg = load_json(CONFIG_PATH, dict(DEFAULT_CONFIG))
    for k, v in DEFAULT_CONFIG.items():
        cfg.setdefault(k, v)
    # GitHub Actions / cloud: token & chat_id can come from environment
    # variables (repository secrets) instead of the JSON file.
    if os.environ.get("BALE_TOKEN"):
        cfg["bale_token"] = os.environ["BALE_TOKEN"]
    if os.environ.get("BALE_CHAT_ID"):
        cfg["bale_chat_id"] = os.environ["BALE_CHAT_ID"]
    return cfg


def fa_digits(s):
    return str(s).translate(str.maketrans("0123456789", "۰۱۲۳۴۵۶۷۸۹"))


def fmt_price(p):
    try:
        return fa_digits(f"{int(p):,}")
    except (TypeError, ValueError):
        return fa_digits(p)


def tehran_now():
    return datetime.datetime.now(datetime.timezone.utc).astimezone(TEHRAN_TZ)


def in_active_window(now=None):
    """True if current TEHRAN time is inside one of the active windows."""
    t = (now or tehran_now()).time()
    for (h1, m1), (h2, m2) in ACTIVE_WINDOWS:
        if datetime.time(h1, m1) <= t < datetime.time(h2, m2):
            return True
    return False


def next_window_start(now=None):
    """Next Tehran-time window opening (datetime)."""
    t = now or tehran_now()
    tt = t.time()
    cands = []
    for (h1, m1), _e in ACTIVE_WINDOWS:
        start = datetime.time(h1, m1)
        if tt < start:
            cands.append(datetime.datetime.combine(t.date(), start,
                                                   tzinfo=TEHRAN_TZ))
        else:
            cands.append(datetime.datetime.combine(
                t.date() + datetime.timedelta(days=1), start,
                tzinfo=TEHRAN_TZ))
    return min(cands)


# ------------------------------------------------------------ livewire client
class WizardError(Exception):
    pass


class Wizard:
    """Drives the guest purchase wizard on shop.barez.org (Livewire v2)."""

    def __init__(self):
        self.s = requests.Session()
        self.s.headers.update({"User-Agent": UA,
                               "Accept-Language": "fa-IR,fa;q=0.9"})
        r = self.s.get(START_URL, timeout=40)
        r.raise_for_status()
        m = re.search(r'wire:initial-data="([^"]+)"', r.text)
        c = re.search(r'csrf-token"\s+content="([^"]+)"', r.text)
        if not m or not c:
            raise WizardError("صفحه شروع خرید ساختار مورد انتظار را ندارد "
                              "(احتمالاً تغییر کرده است)")
        self.snap = json.loads(htmllib.unescape(m.group(1)))
        self.csrf = c.group(1)
        self.name = self.snap["fingerprint"]["name"]
        self.html = ""

    # low level ---------------------------------------------------------
    def _post(self, updates):
        payload = {"fingerprint": self.snap["fingerprint"],
                   "serverMemo": self.snap["serverMemo"],
                   "updates": updates}
        r = self.s.post(f"{BASE}/livewire/message/{self.name}", json=payload,
                        headers={"X-CSRF-TOKEN": self.csrf,
                                 "X-Requested-With": "XMLHttpRequest",
                                 "Accept": "text/html, application/xhtml+xml",
                                 "Referer": START_URL,
                                 "Origin": BASE},
                        timeout=40)
        if r.status_code != 200:
            raise WizardError(f"سرورLivewire کد {r.status_code} برگرداند")
        j = r.json()
        sm = j.get("serverMemo", {})
        for key, value in sm.items():
            if key == "data":
                for dk, dv in value.items():
                    self.snap["serverMemo"]["data"][dk] = dv
            else:
                self.snap["serverMemo"][key] = value
        self.html = j.get("effects", {}).get("html") or self.html
        # surface error alerts sent by the site
        for d in (j.get("effects", {}).get("dispatches") or []):
            if d.get("event") == "alert":
                data = d.get("data") or {}
                raise WizardError(
                    f"سایت پیام خطا داد: {data.get('message', 'نامشخص')}")
        return j

    def _sig(self, method, params):
        pstr = ",".join("" if p is None else str(p) for p in params)
        return method + base64.b64encode(
            urllib.parse.quote(pstr, safe="").encode()).decode()

    def sync(self, name, value):
        return self._post([{"type": "syncInput",
                            "payload": {"id": f"s{random.randint(10**12, 10**13)}",
                                        "name": name, "value": value}}])

    def set(self, name, value):
        return self._post([{"type": "callMethod",
                            "payload": {"id": self._sig("$set", [name, value]),
                                        "method": "$set",
                                        "params": [name, value]}}])

    def call(self, method, params=None):
        params = params or []
        return self._post([{"type": "callMethod",
                            "payload": {"id": self._sig(method, params),
                                        "method": method,
                                        "params": params}}])

    # high level --------------------------------------------------------
    def reach_products(self, cfg):
        self.call("nextDeliveryType", [cfg["delivery_type"]])
        self.sync("fields.TermsAndConditions.ruleCheckButton", True)
        self.call("nextTermsAndConditions")
        self.set("fields.ProvincesCities.provinces", str(cfg["province_id"]))
        self.set("fields.ProvincesCities.city", str(cfg["city_id"]))
        self.call("nextProvincesCities")
        return self.state()

    def state(self):
        return self.snap["serverMemo"]["data"]

    def partial(self):
        return self.state().get("currentPartial")


# ------------------------------------------------------------- stock parsing
def parse_products_html(html):
    """Extract in-stock tire rows from the RENDERED products table.

    The wizard's serverMemo.data.products is always [] on this site; the
    authoritative stock list lives only in the rendered HTML:
      - each row is a <tr class="clickableRow">
      - in-stock rows contain a <select id="product-count-N"> with numeric
        <option value="M"> entries
      - sold-out rows contain the text «اتمام موجودی» and no select
    """
    rows = []
    if not html:
        return rows
    chunks = re.split(r'<tr[^>]*class="[^"]*clickableRow[^"]*"[^>]*>', html)
    for chunk in chunks[1:]:
        chunk = chunk.split("</tr>")[0]
        if "اتمام موجودی" in chunk:
            continue  # sold-out row
        options = [int(v) for v in
                   re.findall(r'<option[^>]*value="(\d+)"', chunk)]
        if not options:
            continue
        m_id = (re.search(r'data-id="(\d+)"', chunk)
                or re.search(r'showDetail\((\d+)\)', chunk)
                or re.search(r'nextProduct\((\d+)\)', chunk))
        if not m_id:
            continue
        pid = int(m_id.group(1))
        tds = re.findall(r'<td[^>]*>(.*?)</td>', chunk, flags=re.S)
        name = ""
        if len(tds) >= 2:
            name = re.sub(r"\s+", " ",
                          re.sub(r"<[^>]+>", " ", tds[1])).strip()
        m_price = re.search(r'data-price="(\d+)"', chunk)
        price = int(m_price.group(1)) if m_price else ""
        m_tp = re.search(r'data-transport_price="(\d+)"', chunk)
        transport = int(m_tp.group(1)) if m_tp else ""
        m_size = re.search(r'(\d{3}/\d{2}\s?R\s?\d{2})', name)
        size = re.sub(r"\s+", "", m_size.group(1)) if m_size else ""
        rows.append({"id": pid, "name": name, "size": size, "price": price,
                     "count": max(options), "transport": transport})
    return rows


def parse_products(data):
    """Fallback: extract in-stock rows from wizard state `products`."""
    products = data.get("products") or []
    rows = []
    if isinstance(products, dict):
        products = list(products.values())
    for p in products:
        if not isinstance(p, dict):
            continue
        rows.append({
            "id": p.get("id"),
            "name": p.get("name") or p.get("title") or p.get("pattern") or "",
            "size": p.get("size") or "",
            "price": p.get("price") or p.get("amount") or "",
            "count": p.get("count") if p.get("count") is not None
                     else p.get("inventory") if p.get("inventory") is not None
                     else p.get("stock") if p.get("stock") is not None else "",
            "transport": "",
        })
    return rows


def scan_secondary_signals(data, html):
    """Cheap extra indicators worth logging (never used to suppress stock)."""
    sig = {}
    txt = re.sub(r"<[^>]+>", " ", re.sub(r"<script.*?</script>", " ", html,
                                         flags=re.S))
    txt = re.sub(r"\s+", " ", txt)
    sig["etmam_mojoodi"] = "اتمام موجودی" in txt
    sig["current_partial"] = data.get("currentPartial")
    sig["auth_status"] = data.get("auth_status")
    return sig


# --------------------------------------------------------------- bale sender
def bale_send(cfg, text):
    token = cfg.get("bale_token") or ""
    chat_id = cfg.get("bale_chat_id") or ""
    if not token or not chat_id:
        return False, "توکن بله یا chat_id تنظیم نشده است"
    url = f"https://tapi.bale.ai/bot{token}/sendMessage"
    try:
        r = requests.post(url, json={"chat_id": chat_id, "text": text},
                          timeout=30)
        ok = r.status_code == 200
        return ok, f"HTTP {r.status_code} {r.text[:120]}"
    except requests.RequestException as e:
        return False, str(e)[:150]


def bale_get_chat_id(token):
    r = requests.get(f"https://tapi.bale.ai/bot{token}/getUpdates", timeout=30)
    if r.status_code != 200:
        return None, f"getUpdates HTTP {r.status_code}"
    j = r.json()
    for upd in j.get("result", [])[::-1]:
        msg = upd.get("message") or upd.get("edited_message") or {}
        chat = msg.get("chat") or {}
        if chat.get("id"):
            return chat["id"], f"chat type={chat.get('type')} title={chat.get('title') or chat.get('first_name')}"
    return None, "پیامی از هیچ چتی پیدا نشد؛ ابتدا به ربات /start بدهید"


# ------------------------------------------------------------- notification
def build_message(rows, cfg):
    now = tehran_now().strftime("%Y-%m-%d ساعت %H:%M")
    lines = ["🚨 تایر بارز موجود شد!", ""]
    for r in rows:
        lines.append(f"• محصول: {r['name'] or 'نامشخص'}")
        if r.get("size"):
            lines.append(f"• سایز: {r['size']}")
        if r.get("price") not in ("", None):
            lines.append(f"• قیمت: {fmt_price(r['price'])} ریال")
        if r.get("transport") not in ("", None):
            lines.append(f"• هزینه ارسال دکاپست: {fmt_price(r['transport'])} ریال")
        if r.get("count") not in ("", None):
            lines.append(f"• حداکثر تعداد قابل سفارش: {fa_digits(r['count'])}")
        lines.append("")
    lines.append(f"• مرکز فروش: {cfg.get('delivery_name') or DEFAULT_DELIVERY_NAME}")
    lines.append(f"• محل بررسی: {cfg.get('province_name', '')} / {cfg.get('city_name', '')}")
    lines.append(f"• زمان بررسی: {now}")
    lines.append("")
    lines.append(f"🔗 صفحه خرید: {BUY_LINK}")
    lines.append("")
    lines.append("⏳ توجه: موجودی بارز معمولاً خیلی زود تمام می‌شود؛ "
                 "در صورت تمایل هرچه سریع‌تر در سایت سفارش ثبت کنید.")
    return "\n".join(lines)


# ------------------------------------------------------- background loop
def _lock_fresh():
    try:
        with open(LOCK_PATH, encoding="utf-8") as f:
            d = json.load(f)
        return (time.time() - d.get("ts", 0)) < LOCK_FRESH
    except (OSError, ValueError):
        return False


def loop_worker():
    """Check every LOOP_INTERVAL seconds but ONLY inside the active windows;
    outside windows the worker stays alive and idles silently.
    The cron task acts only as a keepalive that respawns this worker."""
    start = time.time()
    log(f"loop worker started (pid={os.getpid()}, cap={LOOP_CAP}s, "
        f"interval={LOOP_INTERVAL}s)")
    idle_logged = False
    while time.time() - start < LOOP_CAP:
        with open(LOCK_PATH, "w", encoding="utf-8") as f:
            json.dump({"ts": time.time(), "pid": os.getpid()}, f)
        if in_active_window():
            idle_logged = False
            try:
                run_check(load_config())
            except Exception as e:  # never let the loop die
                log(f"loop unexpected error: {e}\n{traceback.format_exc()[-500:]}")
        else:
            if not idle_logged:
                nxt = next_window_start()
                log(f"outside active windows — idle until "
                    f"{nxt.strftime('%Y-%m-%d %H:%M')} Tehran")
                idle_logged = True
        time.sleep(LOOP_INTERVAL)
    try:
        os.remove(LOCK_PATH)
    except OSError:
        pass
    log("loop worker exit (cap reached)")


def ensure_loop():
    """Spawn a detached loop worker if none is running (fast, returns)."""
    if _lock_fresh():
        log("loop already running — keepalive ok")
        print("loop already running")
        return
    try:
        os.remove(LOCK_PATH)
    except OSError:
        pass
    with open(LOCK_PATH, "w", encoding="utf-8") as f:
        json.dump({"ts": time.time(), "pid": 0}, f)
    log("spawning loop worker")
    with open(LOG_PATH, "a", encoding="utf-8") as lf:
        subprocess.Popen([sys.executable, os.path.abspath(__file__),
                          "--loop-worker"], stdout=lf, stderr=subprocess.STDOUT,
                         start_new_session=True)
    print("loop worker spawned")


# ------------------------------------------------------------------- checks
def run_check(cfg, notify=True):
    state = load_json(STATE_PATH, {})
    log("check start")
    try:
        w = Wizard()
        data = w.reach_products(cfg)
    except (WizardError, requests.RequestException) as e:
        state["error_count"] = state.get("error_count", 0) + 1
        state["last_error"] = str(e)[:300]
        state["last_run"] = tehran_now().isoformat(timespec="seconds")
        save_json(STATE_PATH, state)
        log(f"CHECK ERROR: {e}")
        # report persistent errors to chat (every 4th consecutive error ≈ 1h)
        if state["error_count"] % 4 == 1 and notify:
            errmsg = (f"⚠️ مانیتور تایر بارز خطا خورد (بار "
                      f"{fa_digits(state['error_count'])}):\n{e}\n"
                      "اگر تکرار شد بررسی می‌کنم.")
            if cfg.get("relay_status"):
                ok, detail = bale_send(cfg, errmsg)
                log(f"bale error relay: ok={ok} {detail}")
            return ("ERROR", errmsg)
        return ("ERROR_QUIET", str(e))

    state["error_count"] = 0
    state["last_run"] = tehran_now().isoformat(timespec="seconds")
    sig = scan_secondary_signals(data, w.html)
    state["last_signals"] = sig

    # ---- stock detection: rendered HTML is authoritative ----------------
    # Three real page states (verified against live site):
    #   1. stock exists  -> products table (clickableRow rows) is rendered
    #   2. all sold out  -> NO table, only the site's global «اتمام موجودی» span
    #   3. anything else -> structure anomaly, never claim "no stock"
    txt = re.sub(r"<[^>]+>", " ", w.html or "")
    has_table = bool(w.html) and "clickableRow" in w.html
    rows = parse_products_html(w.html) if has_table else []
    if not rows:
        rows = parse_products(data)  # fallback (usually empty on this site)
    global_etmam = (not has_table) and ("اتمام موجودی" in txt)
    state["last_signals"] = {**sig, "has_table": has_table,
                             "global_etmam": global_etmam}

    if not has_table and not global_etmam and not rows:
        # page structure anomaly — never claim "no stock" from a broken page
        state["anomaly_count"] = state.get("anomaly_count", 0) + 1
        state["last_products_hash"] = ""
        state["last_products"] = []
        state["last_partial"] = sig["current_partial"]
        save_json(STATE_PATH, state)
        log("ANOMALY: rendered html has no clickableRow — no status claims")
        if (notify and cfg.get("relay_status")
                and state["anomaly_count"] % 4 == 1):
            msg = ("⚠️ ساختار صفحه فروشگاه بارز تغییر کرده و فعلاً نمی‌توانم "
                   "موجودی را بخوانم؛ پیگیری می‌شود.")
            ok, detail = bale_send(cfg, msg)
            log(f"bale anomaly relay: ok={ok} {detail}")
        return ("ANOMALY", "structure changed")
    state["anomaly_count"] = 0

    in_stock = bool(rows)
    was_in_stock = bool(state.get("last_in_stock"))
    cur_hash = ""
    if rows:
        cur_hash = str(sorted((r["id"], r["name"], r["size"], r["price"],
                               r["count"]) for r in rows))
    state["last_products_hash"] = cur_hash
    state["last_products"] = rows
    state["last_partial"] = sig["current_partial"]
    state["last_in_stock"] = in_stock
    save_json(STATE_PATH, state)

    now_ts = time.time()
    now_hm = tehran_now().strftime("%H:%M")

    # ---- in stock --------------------------------------------------------
    if in_stock:
        known = state.get("notified_hashes", [])
        if cur_hash not in known:
            msg = build_message(rows, cfg)
            state.setdefault("notified_hashes", [])
            state["notified_hashes"].append(cur_hash)
            state["notified_hashes"] = state["notified_hashes"][-20:]
            state["last_nudge_ts"] = now_ts
            save_json(STATE_PATH, state)
            log(f"IN STOCK! {len(rows)} rows -> notifying")
            if notify:
                ok, detail = bale_send(cfg, msg)
                log(f"bale send: ok={ok} {detail}")
                # also save for chat relay
                with open(NOTIFY_PATH, "w", encoding="utf-8") as f:
                    f.write(msg)
                if ok:
                    return ("NOTIFY", msg + "\n\n(✅ به بله هم ارسال شد)")
                return ("NOTIFY", msg + "\n\n(⚠️ ارسال به بله ناموفق: "
                                       f"{detail})")
            return ("NOTIFY", msg)
        log(f"in stock ({len(rows)} rows) but already notified (same hash)")
        if (notify and cfg.get("relay_status")
                and now_ts - state.get("last_nudge_ts", 0) >= NUDGE_EVERY):
            state["last_nudge_ts"] = now_ts
            save_json(STATE_PATH, state)
            hb = (f"🔁 همچنان موجود است ({cfg.get('city_name', '')}، "
                  f"ساعت {fa_digits(now_hm)}) — اگر سفارش ثبت نکرده‌اید، "
                  "عجله کنید.")
            ok, detail = bale_send(cfg, hb)
            log(f"bale nudge: ok={ok} {detail}")
        return ("OK", "موجود است (قبلاً خبر داده‌ام)")

    # ---- no stock --------------------------------------------------------
    log(f"no stock | rows=0 | partial={sig['current_partial']} | "
        f"etmam={sig['etmam_mojoodi']}")
    if was_in_stock:
        # genuine transition: previously announced stock has ended
        state["last_in_stock"] = False
        save_json(STATE_PATH, state)
        if notify and cfg.get("relay_status"):
            msg = (f"🔴 موجودی که پیش‌تر خبر داده بودم به پایان رسید "
                   f"(ساعت {fa_digits(now_hm)}).")
            ok, detail = bale_send(cfg, msg)
            log(f"bale soldout-transition: ok={ok} {detail}")
        return ("OK", "موجودی قبلی به پایان رسید")
    # idle heartbeat: rate-limited, neutral wording (no false sold-out claim)
    if (notify and cfg.get("relay_status")
            and now_ts - state.get("last_heartbeat_ts", 0) >= HEARTBEAT_EVERY):
        state["last_heartbeat_ts"] = now_ts
        save_json(STATE_PATH, state)
        hb = (f"🕐 بررسی {fa_digits(now_hm)} ({cfg.get('city_name', '')}) — "
              "موجودی جدیدی ثبت نشده است؛ به‌محض مشاهده خبر می‌دهم.")
        ok, detail = bale_send(cfg, hb)
        log(f"bale heartbeat: ok={ok} {detail}")
    return ("OK", "موجودی جدیدی ثبت نشده است")


# --------------------------------------------------------------------- CLI
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--check-in-window", action="store_true",
                    help="one check, but skipped silently outside the "
                         "active Tehran windows (for cron/scheduled runs)")
    ap.add_argument("--setup-bale", action="store_true")
    ap.add_argument("--test-notify", action="store_true")
    ap.add_argument("--status", action="store_true")
    ap.add_argument("--reset-state", action="store_true")
    ap.add_argument("--loop", action="store_true",
                    help="ensure a detached background worker is running "
                         "(checks every 3 min inside active windows)")
    ap.add_argument("--loop-worker", action="store_true")
    args = ap.parse_args()

    cfg = load_config()

    if args.loop_worker:
        loop_worker()
        sys.exit(0)

    if args.loop:
        ensure_loop()
        sys.exit(0)
    if args.setup_bale:
        token = cfg.get("bale_token") or ""
        if not token:
            print("توکن بله در فایل کانفیگ نیست. اول توکن را ذخیره کنید.")
            sys.exit(1)
        chat_id, info = bale_get_chat_id(token)
        print("getUpdates:", info)
        if chat_id:
            cfg["bale_chat_id"] = str(chat_id)
            save_json(CONFIG_PATH, cfg)
            ok, detail = bale_send(cfg, "✅ اتصال مانیتور تایر بارز برقرار شد. "
                                        "از این به بعد موجودی‌ها را همین‌جا خبر می‌دهم.")
            print("chat_id saved:", chat_id, "| test send:", ok, detail)
        sys.exit(0)

    if args.test_notify:
        ok, detail = bale_send(cfg, "🔔 پیام آزمایشی مانیتور تایر بارز — "
                                    "اتصال بله سالم است.")
        print("test notify:", ok, detail)
        sys.exit(0)

    if args.status:
        print(json.dumps(load_json(STATE_PATH, {}), ensure_ascii=False, indent=1))
        sys.exit(0)

    if args.reset_state:
        save_json(STATE_PATH, {})
        print("state cleared")
        sys.exit(0)

    if args.check_in_window:
        if not in_active_window():
            print("outside active windows — skipped")
            sys.exit(0)
        status, text = run_check(load_config())
        print(f"== {status} ==")
        print(text)
        sys.exit(0)

    # default: one check
    status, text = run_check(cfg)
    print(f"== {status} ==")
    print(text)


if __name__ == "__main__":
    main()
