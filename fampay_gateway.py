import html as _html
import imaplib
import io
import logging
import os
import re
import secrets
import socket
import sqlite3
import ssl
import threading
import time
import urllib.parse
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation
from email import message_from_bytes
from email.header import decode_header, make_header
from email.utils import parseaddr, parsedate_to_datetime
from typing import Callable, Optional

log = logging.getLogger("fampay_gateway")

# ----------------------------------------------------------------------------
# Config
# ----------------------------------------------------------------------------


@dataclass(frozen=True)
class Config:
    gmail_address: str = ""
    gmail_app_password: str = ""
    upi_id: str = ""
    store_name: str = "VISSHU HACKS STORE"

    imap_server: str = "imap.gmail.com"
    imap_port: int = 993
    imap_timeout: int = 20
    lookback_days: int = 3
    max_fetch: int = 10
    max_mail_bytes: int = 3_000_000

    sender_domains: tuple = ("famapp.in", "famapp.com", "fampay.in", "famapp.co")
    require_auth: bool = True            # Gmail ke DKIM/SPF pass ke bina mail trust nahi hoti

    order_window: int = 900              # QR 15 min valid
    late_utr_window: int = 86400         # order ke 24h tak UTR submit ho sakta hai
    clock_skew: int = 300
    max_payment_age: int = 7200
    email_max_delay: int = 3600
    verify_max_age: int = 21600          # UTR ke 6h baad bhi mail na mile -> admin review
    max_utr_tries: int = 5
    max_open_orders: int = 5
    min_amount: int = 10
    max_amount: int = 50000

    worker_interval: int = 15
    retry_fast: int = 30
    retry_slow: int = 300

    breaker_threshold: int = 3           # itne IMAP failures ke baad pause
    breaker_pause: int = 600

    @classmethod
    def from_env(cls, **overrides) -> "Config":
        base = dict(
            gmail_address=os.getenv("dhansinghthakur210@gmail.com", "").strip(),
            gmail_app_password=os.getenv("nygj hndl vrlw gjkn", "").strip(),
            upi_id=os.getenv("visshuthakur@fam", "").strip(),
            store_name=os.getenv("VISSHU HACKS STORE", "VISSHU HACKS STORE").strip(),
        )
        base.update(overrides)
        return cls(**base)

    @property
    def configured(self) -> bool:
        return bool(self.gmail_address and self.gmail_app_password and self.upi_id)


@dataclass
class Hooks:
    """Bot se judne ke points. Sab optional (get_db ko chhod kar)."""
    get_db: Callable[[], sqlite3.Connection]
    notify_user: Callable[[int, str], None] = lambda uid, text: None          # HTML text
    notify_admin: Callable[..., None] = lambda event, **kw: None              # event name + details
    on_credited: Callable[[int, int, str, str], None] = lambda uid, amt, utr, oid: None
    log_activity: Callable[[int, str, str], None] = lambda uid, action, detail: None
    send_default_success: bool = True      # False => bot apna premium success message on_credited se bhejta hai


# ----------------------------------------------------------------------------
# Small utilities
# ----------------------------------------------------------------------------
_MON_ABBR = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]
_MONTHS = {m.lower(): i for i, m in enumerate(_MON_ABBR, 1)}
OPEN_STATUSES = ("pending", "expired")        # in states me abhi bhi credit ho sakta hai


def epoch_now() -> int:
    return int(time.time())


def _fmt_ts(t) -> str:
    try:
        return datetime.fromtimestamp(int(t), tz=timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC") if t else "?"
    except Exception:
        return "?"


def esc(s) -> str:
    return _html.escape(str(s or ""))


def new_order_id() -> str:
    return "RX" + time.strftime("%y%m%d%H%M%S", time.gmtime()) + secrets.token_hex(2).upper()


# ----------------------------------------------------------------------------
# UTR helpers
# ----------------------------------------------------------------------------
_FAMPAY_ID_RX = re.compile(r"FMPIB[A-Z0-9]{4,35}|FAM[A-Z0-9]{9,35}", re.I)


def normalize_utr(raw) -> Optional[str]:
    """Canonical UTR (UPPERCASE alnum, 8-40, kam se kam ek digit) ya None.
    FamPay ka FMPIB6749353033 aur 6749353033 ek hi payment hai -> digits wala canonical."""
    if raw is None:
        return None
    s = str(raw).strip()
    s = re.sub(r"(?i)^(?:fam\s*pay|fam\s*app|fam|utr|upi\s*ref|upi\s*txn|txn|transaction|ref)"
               r"[\s\-_]*(?:transaction|txn|upi|ref)?[\s\-_]*(?:id|no|number|num)?\.?\s*[:#\-]\s*", "", s)
    s = re.sub(r"(?i)^utr\s+(?:(?:id|no|number|num)\.?\s+)?", "", s)
    s = re.sub(r"(?i)^(?:fam\s*pay\s*|fam\s*app\s*)?(?:transaction|txn|upi\s*ref(?:erence)?|ref(?:erence)?)"
               r"\s*(?:id|no|number|num)\.?\s+", "", s)
    s = re.sub(r"[\s\-_]", "", s).upper()
    s = re.sub(r"^UTR(?=\d{8,})", "", s)                    # "UTR123456789012" -> 123456789012
    if not re.fullmatch(r"[A-Z0-9]{8,40}", s) or not re.search(r"\d", s):
        return None
    m = re.fullmatch(r"FMPIB(\d{6,14})", s)
    return m.group(1) if m else s


def utr_aliases(utr) -> list:
    """Ek payment ke saare roop (duplicate check + mail search ke liye)."""
    u = str(utr or "").strip().upper()
    out = [u]
    m = re.fullmatch(r"FMPIB(\d{6,14})", u)
    if m:
        out.append(m.group(1))
    elif re.fullmatch(r"\d{6,14}", u):
        out.append("FMPIB" + u)
    return out


def looks_like_utr(raw) -> bool:
    t = str(raw or "").strip()
    if re.fullmatch(r"\d{10,12}", t):
        return True
    return bool(_FAMPAY_ID_RX.fullmatch(t)) and normalize_utr(t) is not None


# ----------------------------------------------------------------------------
# Email parsing (pure functions - easy to test)
# ----------------------------------------------------------------------------
def _decode_header_value(v) -> str:
    try:
        return str(make_header(decode_header(v or "")))
    except Exception:
        return str(v or "")


def _html_to_text(h: str) -> str:
    h = re.sub(r"(?is)<(script|style).*?</\1>", " ", h)
    h = re.sub(r"(?i)<br\s*/?>|</p>|</tr>|</div>|</li>", "\n", h)
    h = re.sub(r"(?i)</t[dh]>", " ", h)
    h = re.sub(r"<[^>]+>", " ", h)
    return _html.unescape(h)


def _email_text(msg) -> str:
    chunks = []
    for part in msg.walk():
        if part.get_content_maintype() == "multipart":
            continue
        ctype = part.get_content_type()
        if ctype not in ("text/plain", "text/html"):
            continue
        if "attachment" in str(part.get("Content-Disposition", "")).lower():
            continue
        try:
            payload = part.get_payload(decode=True)
        except Exception:
            continue
        if not payload:
            continue
        try:
            txt = payload.decode(part.get_content_charset() or "utf-8", errors="replace")
        except LookupError:
            txt = payload.decode("utf-8", errors="replace")
        chunks.append(txt if ctype == "text/plain" else _html_to_text(txt))
    out = "\n".join(chunks).replace("\xa0", " ")
    return re.sub(r"[ \t\r\f\v]+", " ", out)[:200_000]


_CUR = r"(?:₹|\brs\.?|\binr\b)"
_NUM = r"([0-9][0-9,]*(?:\.[0-9]{1,2})?)"
_AMT_KEYED = (
    re.compile(r"(?:received|credited|credit|payment\s+of|paid|deposited|amount)[^0-9₹\n]{0,40}?"
               + _CUR + r"\s*" + _NUM, re.I),
    re.compile(_CUR + r"\s*" + _NUM + r"\s*(?:has\s+been\s+|was\s+)?(?:received|credited|paid)", re.I),
)
_AMT_ANY = re.compile(_CUR + r"\s*" + _NUM, re.I)


def _to_paise(s) -> Optional[int]:
    try:
        d = Decimal(s.replace(",", "")) * 100
    except (InvalidOperation, AttributeError):
        return None
    return int(d) if d == d.to_integral_value() else None


def parse_amount_paise(text: str) -> Optional[int]:
    """Mail me likha amount (paise). Agar na mile ya confusing ho -> None (kabhi guess nahi)."""
    keyed = {p for rx in _AMT_KEYED for m in rx.finditer(text) if (p := _to_paise(m.group(1))) is not None}
    if len(keyed) == 1:
        return next(iter(keyed))
    if len(keyed) > 1:
        return None
    anyv = {p for m in _AMT_ANY.finditer(text) if (p := _to_paise(m.group(1))) is not None}
    return next(iter(anyv)) if len(anyv) == 1 else None


_UTR_LABELED = re.compile(
    r"(?:\butr\b|upi\s*ref(?:erence)?(?:\s*(?:no|id|number))?|transaction\s*(?:id|no|number|ref(?:erence)?)"
    r"|txn\s*(?:id|no|ref)|ref(?:erence)?\s*(?:id|no|number)|\brrn\b"
    r"|fam\s*(?:pay|app)?\s*(?:transaction|txn|payment)?\s*(?:id|no|number)|payment\s*id|upi\s*(?:transaction|txn)\s*id)"
    r"\s*[:#\-]?\s*(?:is\s*)?([A-Za-z0-9]{8,40})\b", re.I)
_TOKEN = re.compile(r"\b[A-Za-z0-9]{8,40}\b")


def utr_in_text(text: str, utr: str) -> bool:
    labeled = {m.group(1).upper() for m in _UTR_LABELED.finditer(text)}
    tokens = {t.upper() for t in _TOKEN.findall(text)}
    for u in utr_aliases(utr):
        if u in labeled:
            return True
        if not labeled:
            if u in tokens:
                return True
        elif u in tokens and (re.fullmatch(r"\d{10,12}", u) or _FAMPAY_ID_RX.fullmatch(u)):
            return True
    return False


_DT_PATTERNS = (
    (re.compile(r"(\d{4})-(\d{2})-(\d{2})[T ](\d{1,2}):(\d{2})(?::(\d{2}))?\s*([AaPp]\.?[Mm]\.?)?"), "ymd"),
    (re.compile(r"(\d{1,2})[/\-.](\d{1,2})[/\-.](\d{4}),?\s*(?:at\s*)?(\d{1,2}):(\d{2})(?::(\d{2}))?\s*([AaPp]\.?[Mm]\.?)?"), "dmy"),
    (re.compile(r"(\d{1,2})(?:st|nd|rd|th)?\s+([A-Za-z]{3,9})\.?,?\s+(\d{4}),?\s*(?:at\s*|-\s*)?(\d{1,2}):(\d{2})(?::(\d{2}))?\s*([AaPp]\.?[Mm]\.?)?"), "dMy"),
    (re.compile(r"([A-Za-z]{3,9})\.?\s+(\d{1,2})(?:st|nd|rd|th)?,?\s+(\d{4}),?\s*(?:at\s*|-\s*)?(\d{1,2}):(\d{2})(?::(\d{2}))?\s*([AaPp]\.?[Mm]\.?)?"), "Mdy"),
)


def _ist_to_utc_naive(y, mo, d, h, mi, s, ampm) -> datetime:
    if ampm:
        ap = ampm.lower().replace(".", "")
        if ap == "pm" and h < 12:
            h += 12
        elif ap == "am" and h == 12:
            h = 0
    return datetime(y, mo, d, h, mi, s) - timedelta(hours=5, minutes=30)


def parse_body_datetimes(text: str) -> list:
    """Body ke saare date+time (IST maan kar) -> naive UTC datetimes."""
    out = []
    for rx, kind in _DT_PATTERNS:
        for m in rx.finditer(text):
            g = m.groups()
            try:
                if kind == "ymd":
                    y, mo, d = int(g[0]), int(g[1]), int(g[2])
                elif kind == "dmy":
                    d, mo, y = int(g[0]), int(g[1]), int(g[2])
                elif kind == "dMy":
                    d, y, mo = int(g[0]), int(g[2]), _MONTHS.get(g[1][:3].lower())
                else:
                    mo, d, y = _MONTHS.get(g[0][:3].lower()), int(g[1]), int(g[2])
                if not mo:
                    continue
                h, mi, s, ap = int(g[3]), int(g[4]), int(g[5] or 0), g[6]
                if ap and not (1 <= h <= 12):
                    continue
                out.append(_ist_to_utc_naive(y, mo, d, h, mi, s, ap))
            except (ValueError, TypeError):
                continue
    return out


def _header_epoch(msg) -> Optional[int]:
    try:
        dt = parsedate_to_datetime(str(msg.get("Date", "")))
        if dt.tzinfo is None:
            dt = dt.replace(tzinfo=timezone.utc)
        return int(dt.astimezone(timezone.utc).timestamp())
    except Exception:
        return None


def _domain_allowed(cfg: Config, dom: str) -> bool:
    dom = (dom or "").lower().strip(".")
    return any(dom == d or dom.endswith("." + d) for d in cfg.sender_domains)


def _sender_domain(msg) -> str:
    addr = parseaddr(_decode_header_value(msg.get("From", "")))[1]
    return addr.rsplit("@", 1)[-1].lower() if "@" in addr else ""


def _auth_ok(cfg: Config, msg) -> bool:
    """Sirf Gmail (mx.google.com) ka Authentication-Results trust hota hai.
    Isse koi bhi fake 'payment received' mail bhej kar balance nahi badha sakta."""
    if not cfg.require_auth:
        return True
    for h in (msg.get_all("Authentication-Results") or []):
        hs = re.sub(r"\s+", " ", str(h)).lower()
        if not hs.startswith("mx.google.com"):
            continue
        for m in re.finditer(r"dkim=pass[^;]*?header\.(?:d|i)=@?([a-z0-9.\-]+)", hs):
            if _domain_allowed(cfg, m.group(1)):
                return True
        for m in re.finditer(r"spf=pass[^;]*?smtp\.mailfrom=(?:[^@\s;]*@)?([a-z0-9.\-]+)", hs):
            if _domain_allowed(cfg, m.group(1)):
                return True
        return False
    return False


_INTERNALDATE_RX = re.compile(
    r'INTERNALDATE\s+"\s*(\d{1,2})-([A-Za-z]{3})-(\d{4})\s+(\d{2}):(\d{2}):(\d{2})\s+([+-])(\d{2})(\d{2})\s*"')


def _fetch_internaldate(data) -> Optional[int]:
    """Gmail ka apna arrival time (epoch UTC). Sender isse fake nahi kar sakta."""
    try:
        for item in data or []:
            blob = item[0] if isinstance(item, tuple) else item
            if not isinstance(blob, (bytes, bytearray)):
                continue
            m = _INTERNALDATE_RX.search(blob.decode("ascii", "ignore"))
            if not m:
                continue
            d, mon, y, hh, mi, ss, sign, oh, om = m.groups()
            idx = _MONTHS[mon.lower()]
            base = int(datetime(int(y), idx, int(d), int(hh), int(mi), int(ss), tzinfo=timezone.utc).timestamp())
            return base - (1 if sign == "+" else -1) * (int(oh) * 3600 + int(om) * 60)
    except Exception as e:
        log.debug("internaldate parse fail: %s", e)
    return None


def parse_payment_email(cfg: Config, msg, utr: str, arrival_ts: Optional[int] = None) -> dict:
    """Kabhi raise nahi karta. Mail kya kehti hai wo dict me deta hai; trust ka faisla verifier karta hai.
    Body ka time tabhi maana jata hai jab Gmail arrival time se consistent ho (pehle IST, phir UTR reading)."""
    info = {"sender_domain": "", "sender_ok": False, "auth_ok": False, "utr_match": False,
            "amount_paise": None, "paid_at": None, "paid_src": "", "subject": "",
            "arrival_at": arrival_ts, "header_at": None, "time_conflict": False}
    try:
        info["subject"] = _decode_header_value(msg.get("Subject", ""))[:120]
        dom = _sender_domain(msg)
        info["sender_domain"] = dom
        info["auth_ok"] = _auth_ok(cfg, msg)
        info["sender_ok"] = bool(dom) and _domain_allowed(cfg, dom) and info["auth_ok"]
        text = _email_text(msg)
        info["utr_match"] = utr_in_text(text, utr)
        info["amount_paise"] = parse_amount_paise(text)

        hdr_ts = _header_epoch(msg)
        info["header_at"] = hdr_ts
        ref = arrival_ts if arrival_ts is not None else hdr_ts
        body_times = parse_body_datetimes(text)
        chosen, src = None, ""
        if body_times:
            if ref is not None:
                for t in body_times:
                    base = int(t.replace(tzinfo=timezone.utc).timestamp())
                    for cand in (base, base + 19800):                # IST reading, phir UTC reading
                        gap = ref - cand
                        if -cfg.clock_skew <= gap <= cfg.email_max_delay:
                            if chosen is None or abs(ref - cand) < abs(ref - chosen):
                                chosen, src = cand, "body"
            if chosen is None:
                info["time_conflict"] = True          # body time arrival se match nahi -> auto-credit nahi
        elif hdr_ts is not None:
            if ref is not None and ref - hdr_ts > cfg.email_max_delay:
                info["time_conflict"] = True
            else:
                chosen, src = hdr_ts, "header"
        elif arrival_ts is not None:
            chosen, src = arrival_ts, "arrival"
        if chosen is not None:
            info["paid_at"], info["paid_src"] = int(chosen), src
    except Exception as e:
        log.warning("parse_payment_email error: %s", e)
    return info


def check_payment_time(cfg: Config, em: dict, created: int, utr_submitted_at: Optional[int], now: int):
    """Pure time validation -> (ok, reason)."""
    ts, arr, src, skew = em.get("paid_at"), em.get("arrival_at"), em.get("paid_src"), cfg.clock_skew
    if ts is None:
        return False, ("time_inconsistent" if em.get("time_conflict") else "time_unreadable")
    if ts > now + skew or (arr is not None and (ts > arr + skew or arr > now + skew)):
        return False, "future_timestamp"
    if ts < int(created) - skew:
        return False, "payment_before_order"
    max_age = cfg.max_payment_age if src == "body" else min(cfg.max_payment_age, cfg.order_window + cfg.email_max_delay)
    if ts > int(created) + max_age:
        return False, "payment_too_late"
    if utr_submitted_at:
        tol = skew if src == "body" else cfg.email_max_delay
        if ts > int(utr_submitted_at) + tol:
            return False, "payment_after_utr_submit"        # user pay karne se pehle UTR nahi jaan sakta
    return True, ""


# ----------------------------------------------------------------------------
# Gmail IMAP client  (circuit breaker + backoff)
# ----------------------------------------------------------------------------
class ImapUnavailable(Exception):
    pass


class GmailClient:
    def __init__(self, cfg: Config, on_alert: Callable[[str], None] = lambda t: None):
        self.cfg = cfg
        self._lock = threading.Lock()
        self._fails = 0
        self._paused_until = 0.0
        self._last_alert = 0.0
        self._on_alert = on_alert

    # -- connection
    def _connect(self) -> imaplib.IMAP4_SSL:
        ctx = ssl.create_default_context()
        try:
            M = imaplib.IMAP4_SSL(self.cfg.imap_server, self.cfg.imap_port, ssl_context=ctx, timeout=self.cfg.imap_timeout)
        except TypeError:                                   # python < 3.9
            M = imaplib.IMAP4_SSL(self.cfg.imap_server, self.cfg.imap_port, ssl_context=ctx)
            try:
                M.sock.settimeout(self.cfg.imap_timeout)
            except Exception:
                pass
        M.login(self.cfg.gmail_address, self.cfg.gmail_app_password)
        return M

    def _alert(self, text: str):
        if time.time() - self._last_alert < 3600:
            return
        self._last_alert = time.time()
        try:
            self._on_alert(text)
        except Exception as e:
            log.error("imap alert failed: %s", e)

    def _record(self, ok: bool, why: str = ""):
        if ok:
            self._fails = 0
            return
        self._fails += 1
        if self._fails >= self.cfg.breaker_threshold:
            self._paused_until = time.time() + self.cfg.breaker_pause
            self._alert(f"Gmail IMAP {self._fails} baar fail ({why}). {self.cfg.breaker_pause // 60} min pause.")

    @property
    def paused(self) -> bool:
        return time.time() < self._paused_until

    def selftest(self):
        if not self.cfg.configured:
            return False, "GMAIL_ADDRESS / GMAIL_APP_PASSWORD / FAMPAY_UPI_ID missing"
        try:
            with self._lock:
                M = self._connect()
                M.logout()
            return True, "login OK"
        except imaplib.IMAP4.error as e:
            return False, f"Gmail login failed: {str(e)[:150]} | 2-Step ON, App Password sahi, IMAP enabled?"
        except Exception as e:
            return False, f"Gmail connection failed: {str(e)[:150]}"

    # -- search
    def _search_ids(self, M, utr: str) -> list:
        q = '"%s newer_than:%dd"' % (utr, self.cfg.lookback_days)
        try:
            typ, data = M.search(None, "X-GM-RAW", q)
            if typ == "OK":
                return data[0].split() if data and data[0] else []
        except Exception as e:
            log.debug("X-GM-RAW failed, fallback: %s", e)
        d = datetime.now(timezone.utc) - timedelta(days=self.cfg.lookback_days)
        since = f"{d.day:02d}-{_MON_ABBR[d.month - 1]}-{d.year}"
        typ, data = M.search(None, "SINCE", since, "TEXT", '"%s"' % utr)
        return data[0].split() if typ == "OK" and data and data[0] else []

    def search_utr(self, utr: str):
        """-> (status, emails, error).  status: 'ok' | 'error'. Kabhi raise nahi karta."""
        if not self.cfg.configured:
            return "error", [], "gmail_not_configured"
        if not re.fullmatch(r"[A-Z0-9]{8,40}", str(utr or "")):
            return "error", [], "bad_utr"
        if self.paused:
            return "error", [], "imap_paused"
        for attempt in range(2):                                  # 1 quick retry (network hiccup)
            M = None
            with self._lock:
                try:
                    M = self._connect()
                    emails = []
                    for mailbox in ("INBOX", '"[Gmail]/All Mail"'):
                        try:
                            typ, _ = M.select(mailbox, readonly=True)
                        except Exception:
                            continue
                        if typ != "OK":
                            continue
                        ids = []
                        for alias in utr_aliases(utr):
                            ids += [i for i in self._search_ids(M, alias) if i not in ids]
                        for num in ids[-self.cfg.max_fetch:]:
                            try:
                                typ, data = M.fetch(num, "(INTERNALDATE BODY.PEEK[])")
                                if typ != "OK" or not data or not isinstance(data[0], tuple):
                                    continue
                                raw = data[0][1]
                                if not raw or len(raw) > self.cfg.max_mail_bytes:
                                    continue
                                emails.append(parse_payment_email(self.cfg, message_from_bytes(raw), utr,
                                                                  _fetch_internaldate(data)))
                            except Exception as e:
                                log.warning("malformed email skipped: %s", e)
                        if emails:
                            break
                    self._record(True)
                    return "ok", emails, ""
                except imaplib.IMAP4.error as e:
                    self._record(False, "login/imap")
                    log.error("IMAP error: %s", str(e)[:200])
                    return "error", [], "imap_login_failed"       # retry se fayda nahi
                except (socket.timeout, TimeoutError, ConnectionError, ssl.SSLError, OSError) as e:
                    log.error("IMAP connection failure: %s", e)
                    err = "imap_connection_failed"
                except Exception as e:
                    log.error("IMAP unexpected: %s", e)
                    err = "imap_unexpected"
                finally:
                    if M is not None:
                        try:
                            M.logout()
                        except Exception:
                            pass
            if attempt == 0:
                time.sleep(2)
        self._record(False, err)
        return "error", [], err


# ----------------------------------------------------------------------------
# Schema
# ----------------------------------------------------------------------------
_PENDING_EXTRA_COLS = {
    "expected_amount": "INTEGER", "pay_method": "TEXT DEFAULT 'upi_gmail'", "utr": "TEXT",
    "utr_submitted_at": "INTEGER", "last_check_at": "INTEGER DEFAULT 0", "check_count": "INTEGER DEFAULT 0",
    "utr_tries": "INTEGER DEFAULT 0", "reject_reason": "TEXT", "received_amount": "REAL", "paid_at": "INTEGER",
}


def ensure_schema(conn: sqlite3.Connection) -> None:
    """Idempotent: tables + missing columns + indexes."""
    cur = conn.cursor()
    cur.execute("""CREATE TABLE IF NOT EXISTS pending_payments (
        id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INTEGER NOT NULL, order_id TEXT NOT NULL UNIQUE,
        amount INTEGER NOT NULL, status TEXT DEFAULT 'pending', created_at INTEGER NOT NULL)""")
    cur.execute("""CREATE TABLE IF NOT EXISTS payment_utrs (
        utr TEXT PRIMARY KEY, order_id TEXT NOT NULL, user_id INTEGER NOT NULL,
        amount INTEGER NOT NULL, received_amount REAL, paid_at INTEGER, credited_at INTEGER NOT NULL)""")
    have = {r[1] for r in cur.execute("PRAGMA table_info(pending_payments)")}
    for col, ddl in _PENDING_EXTRA_COLS.items():
        if col not in have:
            cur.execute(f"ALTER TABLE pending_payments ADD COLUMN {col} {ddl}")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_pp_status ON pending_payments(pay_method, status)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_pp_user ON pending_payments(user_id, status, created_at)")
    cur.execute("CREATE INDEX IF NOT EXISTS idx_payment_utrs_user ON payment_utrs(user_id)")
    conn.commit()
    cur.close()


# ----------------------------------------------------------------------------
# QR
# ----------------------------------------------------------------------------
def build_upi_uri(cfg: Config, amount: int, order_id: str = "") -> str:
    q = {"pa": cfg.upi_id, "pn": cfg.store_name, "am": f"{int(amount)}.00", "cu": "INR"}
    if order_id:
        q["tn"] = order_id                      # note me order id: user ke statement me bhi dikhega
    return "upi://pay?" + urllib.parse.urlencode(q, quote_via=urllib.parse.quote, safe="@")


def make_qr_png(uri: str) -> Optional[io.BytesIO]:
    """QR locally banta hai (external API nahi). Library na ho to None."""
    try:
        import segno
        buf = io.BytesIO()
        segno.make(uri, error="m").save(buf, kind="png", scale=10, border=4)
        buf.seek(0)
        buf.name = "upi_qr.png"
        return buf
    except ImportError:
        pass
    except Exception as e:
        log.error("segno failed: %s", e)
    try:
        import qrcode
        qr = qrcode.QRCode(error_correction=qrcode.constants.ERROR_CORRECT_M, box_size=10, border=4)
        qr.add_data(uri)
        qr.make(fit=True)
        buf = io.BytesIO()
        qr.make_image(fill_color="black", back_color="white").save(buf, format="PNG")
        buf.seek(0)
        buf.name = "upi_qr.png"
        return buf
    except ImportError:
        log.error("QR library missing: pip install segno")
    except Exception as e:
        log.error("qrcode failed: %s", e)
    return None


# ----------------------------------------------------------------------------
# Gateway
# ----------------------------------------------------------------------------
REVIEW_MSG = {
    "amount_mismatch": "Payment mili par amount order ke amount se match nahi hua.",
    "amount_unreadable": "Payment email se amount verify nahi ho paya.",
    "time_unreadable": "Payment ka time verify nahi ho paya.",
    "payment_before_order": "Yeh payment is order banne se pehle ki hai, isliye accept nahi hui.",
    "payment_too_late": "Payment order ki maximum allowed time ke baad hui hai.",
    "future_timestamp": "Payment email ka time invalid (future) hai.",
    "time_inconsistent": "Payment email ka time Gmail ke arrival time se match nahi hua.",
    "payment_after_utr_submit": "Payment time UTR submit hone ke baad ka dikh raha hai.",
    "duplicate_utr": "Yeh UTR pehle hi use ho chuka hai.",
    "email_not_found_timeout": "Is UTR ki payment email abhi tak nahi mili.",
}


class FamPayGateway:
    def __init__(self, cfg: Config, hooks: Hooks):
        self.cfg = cfg
        self.h = hooks
        self.mail = GmailClient(cfg, on_alert=lambda t: self._admin("PAYMENT_GATEWAY_ERROR", method="GMAIL IMAP",
                                                                      status="FAILED", details=t))
        self._locks: dict = {}
        self._locks_guard = threading.Lock()
        self._stop = threading.Event()
        self._thread: Optional[threading.Thread] = None

    # -- small helpers
    def _admin(self, event, **kw):
        try:
            self.h.notify_admin(event, **kw)
        except Exception as e:
            log.error("notify_admin failed: %s", e)

    def _user(self, uid, text):
        try:
            self.h.notify_user(uid, text)
        except Exception as e:
            log.warning("notify_user failed uid=%s: %s", uid, e)

    def _run(self, sql, params=()) -> int:
        conn = self.h.get_db()
        try:
            cur = conn.cursor()
            cur.execute(sql, params)
            conn.commit()
            n = cur.rowcount
            cur.close()
            return n
        finally:
            conn.close()

    def _one(self, sql, params=()):
        conn = self.h.get_db()
        try:
            cur = conn.cursor()
            cur.execute(sql, params)
            row = cur.fetchone()
            cur.close()
            return row
        finally:
            conn.close()

    def get_order(self, order_id):
        return self._one("SELECT * FROM pending_payments WHERE order_id=?", (order_id,))

    def _order_lock(self, order_id) -> threading.Lock:
        with self._locks_guard:
            if len(self._locks) > 1000:
                for k in [k for k, v in self._locks.items() if not v.locked()]:
                    self._locks.pop(k, None)
            return self._locks.setdefault(order_id, threading.Lock())

    # -- setup / health
    def init(self):
        conn = self.h.get_db()
        try:
            ensure_schema(conn)
        finally:
            conn.close()

    def health(self) -> dict:
        ok, msg = self.mail.selftest()
        return {"configured": self.cfg.configured, "gmail_ok": ok, "message": msg,
                "qr_ok": make_qr_png("upi://pay?pa=test@fam") is not None, "breaker_paused": self.mail.paused}

    # -- 1. order
    def create_order(self, user_id: int, amount: int):
        """-> (order_id | None, error_code, uri).  error: disabled | bad_amount | too_many_open | db"""
        if not self.cfg.configured:
            return None, "not_configured", ""
        amount = int(amount)
        if not (self.cfg.min_amount <= amount <= self.cfg.max_amount):
            return None, "bad_amount", ""
        now = epoch_now()
        row = self._one("SELECT COUNT(*) AS c FROM pending_payments WHERE user_id=? AND pay_method='upi_gmail' "
                        "AND status='pending' AND created_at>?", (user_id, now - 3600))
        if row and int(row[0]) >= self.cfg.max_open_orders:
            return None, "too_many_open", ""
        oid = new_order_id()
        try:
            self._run("INSERT INTO pending_payments (user_id, order_id, amount, expected_amount, status, created_at, pay_method) "
                      "VALUES (?,?,?,?, 'pending', ?, 'upi_gmail')", (user_id, oid, amount, amount, now))
        except Exception as e:
            log.error("create_order failed: %s", e)
            return None, "db", ""
        self.h.log_activity(user_id, "FAMPAY_QR_GEN", f"₹{amount} | {oid}")
        self._admin("INSTANT_PAYMENT_STARTED", user_id=user_id, amount=amount, ref=oid, status="PENDING")
        return oid, "", build_upi_uri(self.cfg, amount, oid)

    def cancel_order(self, user_id: int, order_id: str) -> bool:
        return self._run("UPDATE pending_payments SET status='cancelled' WHERE order_id=? AND user_id=? "
                         "AND status='pending' AND (utr IS NULL OR utr='')", (order_id, user_id)) == 1

    # -- 2. UTR
    def submit_utr(self, user_id: int, order_id: str, raw_utr: str, auto_verify: bool = True):
        """-> (ok, code).  auto_verify=True: verification background thread me chalu.
        auto_verify=False: caller khud verify_order() chalayega (jaise bot, feedback dikhane ke liye)."""
        utr = normalize_utr(raw_utr)
        if not utr:
            return False, "invalid_utr"
        row = self.get_order(order_id)
        if (not row or row["user_id"] != user_id or row["pay_method"] != "upi_gmail"
                or row["status"] not in OPEN_STATUSES + ("review",)):
            return False, "order_inactive"
        if epoch_now() - int(row["created_at"]) > self.cfg.late_utr_window:
            return False, "utr_window_closed"
        if int(row["utr_tries"] or 0) >= self.cfg.max_utr_tries:
            return False, "too_many_tries"
        a, b = (utr_aliases(utr) + [utr, utr])[:2]
        used = self._one("SELECT 1 FROM payment_utrs WHERE UPPER(utr) IN (?,?)", (a.upper(), b.upper()))
        if not used and self._table_exists("manual_deposits"):
            used = self._one("SELECT 1 FROM manual_deposits WHERE UPPER(utr) IN (?,?) "
                             "AND status IN ('pending','approved') LIMIT 1", (a.upper(), b.upper()))
        if used:
            self._admin("SUSPICIOUS_PAYMENT", user_id=user_id, amount=row["amount"], utr=utr, ref=order_id,
                        status="BLOCKED", details="Duplicate UTR submitted")
            return False, "duplicate_utr"
        n = self._run("UPDATE pending_payments SET utr=?, utr_submitted_at=?, status='pending', reject_reason=NULL, "
                      "last_check_at=0, check_count=0, utr_tries=COALESCE(utr_tries,0)+1 "
                      "WHERE order_id=? AND user_id=? AND status IN ('pending','expired','review')",
                      (utr, epoch_now(), order_id, user_id))
        if n != 1:
            return False, "update_failed"
        self.h.log_activity(user_id, "UPI_UTR_SUBMIT", f"₹{row['amount']} | {utr}")
        self._admin("UTR_SUBMITTED", user_id=user_id, amount=row["amount"], utr=utr, ref=order_id, status="PENDING")
        if auto_verify:
            threading.Thread(target=self.verify_order, args=(order_id, True), daemon=True).start()
        return True, utr

    def _table_exists(self, name: str) -> bool:
        return self._one("SELECT 1 FROM sqlite_master WHERE type='table' AND name=?", (name,)) is not None

    # -- 3. verify (read-only)
    def check_mail(self, order, utr) -> dict:
        status, emails, err = self.mail.search_utr(utr)
        res = {"state": "error", "reason": err, "emails": emails, "received_paise": None, "paid_at": None, "detail": ""}
        if status != "ok":
            return res
        exp = int(order["amount"]) * 100
        created = int(order["created_at"])
        utr_sub = int(order["utr_submitted_at"]) if order["utr_submitted_at"] else None
        now = epoch_now()
        matched, reject = False, ""
        for em in emails:
            if not (em["sender_ok"] and em["utr_match"]):
                continue
            matched = True
            if em["amount_paise"] is None:
                reject = reject or "amount_unreadable"
                continue
            res["received_paise"] = em["amount_paise"]
            if em["amount_paise"] != exp:
                reject = "amount_mismatch"
                continue
            ok, why = check_payment_time(self.cfg, em, created, utr_sub, now)
            res["detail"] = (f"order {_fmt_ts(created)} | payment {_fmt_ts(em['paid_at'])} ({em['paid_src'] or 'none'}) "
                             f"| arrival {_fmt_ts(em.get('arrival_at'))}")
            if not ok:
                reject = why if (not reject or reject == "time_unreadable") else reject
                res["paid_at"] = em["paid_at"]
                continue
            res.update(state="verified", reason="", paid_at=em["paid_at"], received_paise=em["amount_paise"])
            return res
        res.update(state="rejected", reason=reject or "unverified") if matched else res.update(state="not_found", reason="")
        return res

    # -- 4. atomic credit
    def credit(self, order_id, utr, received_paise, paid_at):
        """-> ('credited'|'duplicate_utr'|'not_open'|'error', row)  - sab kuch ek transaction me."""
        conn = self.h.get_db()
        cur = conn.cursor()
        try:
            cur.execute("BEGIN IMMEDIATE")
            cur.execute("SELECT * FROM pending_payments WHERE order_id=?", (order_id,))
            row = cur.fetchone()
            if not row or row["status"] not in OPEN_STATUSES:
                conn.rollback()
                return "not_open", None
            if received_paise != int(row["amount"]) * 100:
                conn.rollback()
                return "error", None
            a, b = (utr_aliases(utr) + [utr, utr])[:2]
            dup = cur.execute("SELECT 1 FROM payment_utrs WHERE UPPER(utr) IN (?,?) LIMIT 1", (a.upper(), b.upper())).fetchone()
            if not dup and cur.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='manual_deposits'").fetchone():
                dup = cur.execute("SELECT 1 FROM manual_deposits WHERE UPPER(utr) IN (?,?) AND status='approved' LIMIT 1",
                                  (a.upper(), b.upper())).fetchone()
            if dup:
                conn.rollback()
                return "duplicate_utr", row
            try:
                cur.execute("INSERT INTO payment_utrs (utr, order_id, user_id, amount, received_amount, paid_at, credited_at) "
                            "VALUES (?,?,?,?,?,?,?)",
                            (utr, order_id, row["user_id"], int(row["amount"]), received_paise / 100.0, paid_at, epoch_now()))
            except sqlite3.IntegrityError:
                conn.rollback()
                return "duplicate_utr", row
            cur.execute("UPDATE pending_payments SET status='success', utr=?, received_amount=?, paid_at=?, reject_reason=NULL "
                        "WHERE id=? AND status IN ('pending','expired')", (utr, received_paise / 100.0, paid_at, row["id"]))
            if cur.rowcount != 1:
                conn.rollback()
                return "not_open", None
            cur.execute("UPDATE users SET balance = balance + ? WHERE id=?", (int(row["amount"]), row["user_id"]))
            if cur.rowcount != 1:
                conn.rollback()
                return "error", None
            cur.execute("INSERT INTO transactions (user_id, amount, type, details, reference_id) "
                        "VALUES (?,?,'add_money','fam_pay',?)", (row["user_id"], int(row["amount"]), utr))
            conn.commit()
            return "credited", row
        except Exception as e:
            try:
                conn.rollback()
            except Exception:
                pass
            log.error("credit error: %s", e)
            return "error", None
        finally:
            cur.close()
            conn.close()

    def _mark_review(self, row, reason, received_paise=None, detail=""):
        if self._run("UPDATE pending_payments SET status='review', reject_reason=? WHERE id=? "
                     "AND status IN ('pending','expired')", (reason, row["id"])) != 1:
            return
        self._user(row["user_id"],
                   f"⚠️ <b>PAYMENT VERIFICATION FAILED</b>\n\n💰 Order amount: ₹{row['amount']}\n"
                   f"📝 UTR: <code>{esc(row['utr'])}</code>\n\n{REVIEW_MSG.get(reason, 'Payment verify nahi ho paya.')}\n"
                   f"Balance add <b>nahi</b> hua. Sahi UTR ho to dobara bhejo ya support se contact karo.\n"
                   f"🆔 <code>{esc(row['order_id'])}</code>")
        rec = f"₹{received_paise / 100:.2f}" if received_paise is not None else "?"
        self._admin("SUSPICIOUS_PAYMENT" if reason == "duplicate_utr" else "UTR_VERIFICATION_FAILED",
                    user_id=row["user_id"], amount=row["amount"], utr=row["utr"], ref=row["order_id"], status="FAILED",
                    details=f"Reason: {reason} | expected ₹{row['amount']} | email {rec}" + (f" | {detail}" if detail else ""))

    def verify_order(self, order_id: str, force: bool = False) -> str:
        """Thread-safe. Returns: credited | not_found | rejected | duplicate_utr | busy | skip | error"""
        lk = self._order_lock(order_id)
        if not lk.acquire(blocking=False):
            return "busy"
        try:
            row = self.get_order(order_id)
            if not row or row["status"] not in OPEN_STATUSES or not row["utr"]:
                return "skip"
            now = epoch_now()
            if not force and now - int(row["last_check_at"] or 0) < 10:
                return "skip"
            self._run("UPDATE pending_payments SET last_check_at=?, check_count=COALESCE(check_count,0)+1 WHERE id=?",
                      (now, row["id"]))
            res = self.check_mail(row, row["utr"])
            st = res["state"]
            if st == "verified":
                out, _ = self.credit(order_id, row["utr"], res["received_paise"], res["paid_at"])
                if out == "credited":
                    self.h.log_activity(row["user_id"], "UPI_PAYMENT_OK", f"₹{row['amount']} | {row['utr']}")
                    if self.h.send_default_success:
                        self._user(row["user_id"], f"✅ <b>PAYMENT SUCCESS</b>\n\n💰 ₹{row['amount']} balance me add ho gaya.\n"
                                                   f"📝 UTR: <code>{esc(row['utr'])}</code>")
                    try:
                        self.h.on_credited(row["user_id"], int(row["amount"]), row["utr"], order_id)
                    except Exception as e:
                        log.error("on_credited hook failed: %s", e)
                elif out == "duplicate_utr":
                    self._mark_review(row, "duplicate_utr", res["received_paise"])
                elif out == "error":
                    self._admin("PAYMENT_ERROR", user_id=row["user_id"], amount=row["amount"], utr=row["utr"], ref=order_id,
                                status="FAILED", details="credit failed - balance NOT added")
                return out
            if st == "rejected":
                self._mark_review(row, res["reason"], res["received_paise"], res.get("detail", ""))
                return "rejected"
            return st
        except Exception as e:
            log.exception("verify_order error: %s", e)
            return "error"
        finally:
            lk.release()

    # -- 5. background worker
    def _tick(self):
        now = epoch_now()
        conn = self.h.get_db()
        try:
            cur = conn.cursor()
            cur.execute("SELECT id, user_id, order_id, amount FROM pending_payments WHERE pay_method='upi_gmail' "
                        "AND status='pending' AND (utr IS NULL OR utr='') AND created_at<?", (now - self.cfg.order_window,))
            stale = cur.fetchall()
            cur.execute("SELECT order_id, utr_submitted_at, last_check_at FROM pending_payments "
                        "WHERE pay_method='upi_gmail' AND status IN ('pending','expired') AND utr IS NOT NULL AND utr<>''")
            todo = cur.fetchall()
            cur.close()
        finally:
            conn.close()
        for r in stale:
            if self._run("UPDATE pending_payments SET status='expired' WHERE id=? AND status='pending' "
                         "AND (utr IS NULL OR utr='')", (r["id"],)) == 1:
                self._admin("INSTANT_PAYMENT_EXPIRED", user_id=r["user_id"], amount=r["amount"], ref=r["order_id"], status="EXPIRED")
                self._user(r["user_id"], f"⏰ <b>ORDER EXPIRED</b>\n\n💰 ₹{r['amount']} · <code>{esc(r['order_id'])}</code>\n\n"
                                         f"Agar payment kar chuke ho to UTR bhejo — payment time check hoga.\n"
                                         f"Nahi kiya to naya QR generate karo.")
        if self.mail.paused:
            return
        for r in todo:
            since = now - int(r["utr_submitted_at"] or now)
            if since > self.cfg.verify_max_age:
                row = self.get_order(r["order_id"])
                if row and row["status"] in OPEN_STATUSES:
                    self._mark_review(row, "email_not_found_timeout")
                continue
            interval = self.cfg.retry_fast if since < 600 else self.cfg.retry_slow
            if now - int(r["last_check_at"] or 0) >= interval:
                self.verify_order(r["order_id"])

    def start_worker(self):
        if self._thread and self._thread.is_alive():
            return
        self._stop.clear()

        def loop():
            while not self._stop.is_set():
                try:
                    self._tick()
                except Exception as e:
                    log.error("worker error: %s", e)
                self._stop.wait(self.cfg.worker_interval)

        self._thread = threading.Thread(target=loop, name="fampay-worker", daemon=True)
        self._thread.start()

    def stop_worker(self, timeout: float = 5.0):
        self._stop.set()
        if self._thread:
            self._thread.join(timeout)


# ----------------------------------------------------------------------------
# Self-test:  python fampay_gateway.py --selftest
# ----------------------------------------------------------------------------
def _selftest() -> int:
    import tempfile
    from email.message import EmailMessage

    cfg = Config(gmail_address="x@gmail.com", gmail_app_password="x", upi_id="shop@fam")
    fails = []

    def ok(name, cond):
        print(("PASS " if cond else "FAIL ") + name)
        if not cond:
            fails.append(name)

    ok("normalize FMPIB -> digits", normalize_utr("FMPIB6749353033") == "6749353033")
    ok("normalize 'UTR: 123456789012'", normalize_utr("UTR: 123456789012") == "123456789012")
    ok("normalize rejects short", normalize_utr("1234") is None)
    ok("aliases", utr_aliases("6749353033") == ["6749353033", "FMPIB6749353033"])
    ok("amount keyed", parse_amount_paise("You received ₹ 1,250.50 from Rahul") == 125050)
    ok("amount ambiguous -> None", parse_amount_paise("received ₹100 and received ₹200") is None)
    ok("uri", build_upi_uri(cfg, 100, "RX1").startswith("upi://pay?pa=shop@fam&pn=ROCKY%20X%20STORE&am=100.00"))

    now = epoch_now()
    paid = datetime.fromtimestamp(now - 120, tz=timezone.utc) + timedelta(hours=5, minutes=30)
    body = f"Payment received\nAmount: ₹100.00\nUTR: 123456789012\n{paid:%d/%m/%Y %H:%M:%S}\n"
    msg = EmailMessage()
    msg["From"] = "FamApp <noreply@famapp.in>"
    msg["Subject"] = "Payment received"
    msg["Authentication-Results"] = "mx.google.com; dkim=pass header.i=@famapp.in; spf=pass smtp.mailfrom=famapp.in"
    msg.set_content(body)
    em = parse_payment_email(cfg, msg, "123456789012", now - 100)
    ok("mail sender+auth", em["sender_ok"])
    ok("mail utr match", em["utr_match"])
    ok("mail amount", em["amount_paise"] == 10000)
    ok("mail time body", em["paid_src"] == "body")
    ok("time check passes", check_payment_time(cfg, em, now - 600, now - 60, now)[0])
    ok("time before order rejected", check_payment_time(cfg, em, now + 3000, None, now)[1] == "payment_before_order")

    fake = EmailMessage()
    fake["From"] = "scam@evil.com"
    fake.set_content(body)
    ok("fake sender rejected", not parse_payment_email(cfg, fake, "123456789012", now - 100)["sender_ok"])

    # DB flow (mail layer stubbed)
    path = os.path.join(tempfile.mkdtemp(), "t.db")

    def get_db():
        c = sqlite3.connect(path, timeout=10)
        c.row_factory = sqlite3.Row
        return c

    c = get_db()
    c.executescript("CREATE TABLE users(id INTEGER PRIMARY KEY, balance INTEGER DEFAULT 0);"
                    "CREATE TABLE transactions(id INTEGER PRIMARY KEY AUTOINCREMENT, user_id INT, amount INT, type TEXT, details TEXT, reference_id TEXT);"
                    "INSERT INTO users(id,balance) VALUES (1,0);")
    c.commit()
    c.close()
    sent = []
    gw = FamPayGateway(cfg, Hooks(get_db=get_db, notify_user=lambda u, t: sent.append((u, t))))
    gw.init()
    gw.mail.search_utr = lambda utr: ("ok", [em], "")             # Gmail ko stub kiya
    oid, err, _ = gw.create_order(1, 100)
    ok("create_order", bool(oid) and not err)
    ok("bad amount blocked", gw.create_order(1, 1)[1] == "bad_amount")
    good, code = gw.submit_utr(1, oid, "123456789012")
    ok("submit_utr", good)
    time.sleep(0.5)
    out = gw.verify_order(oid, True)
    bal = get_db().execute("SELECT balance FROM users WHERE id=1").fetchone()[0]
    ok(f"credited once (balance={bal}, out={out})", bal == 100)
    gw.verify_order(oid, True)
    ok("replay does not double-credit", get_db().execute("SELECT balance FROM users WHERE id=1").fetchone()[0] == 100)
    oid2, _, _ = gw.create_order(1, 100)
    ok("same UTR on new order blocked", gw.submit_utr(1, oid2, "123456789012") == (False, "duplicate_utr"))

    print("\nALL OK" if not fails else f"\n{len(fails)} FAILED: {fails}")
    return 1 if fails else 0


if __name__ == "__main__":
    import sys
    if "--selftest" in sys.argv:
        raise SystemExit(_selftest())
    print(__doc__)


# =============================================================================
#  YAHAN SIRF YE TEEN LINES BHARNA
# =============================================================================
GMAIL_ADDRESS = "dhansinghthakur210@gmail.com"           # Gmail ID
GMAIL_APP_PASSWORD = "nygj hndl vrlw gjkn"      # Gmail App Password
FAMPAY_UPI_ID = "visshuthakur@fam"           # UPI ID
STORE_NAME = "VISSHU HACKS STORE"

UPI_ORDER_WINDOW_SECONDS = 900

FAMPAY_CFG = Config(
    gmail_address=GMAIL_ADDRESS.strip(),
    gmail_app_password=GMAIL_APP_PASSWORD.replace(" ", "").strip(),
    upi_id=FAMPAY_UPI_ID.strip(),
    store_name=STORE_NAME,
    order_window=UPI_ORDER_WINDOW_SECONDS,
    min_amount=1, max_amount=100000,
)

# Gateway instance. get_db aur baaki hooks (notify_user, notify_admin, on_credited, log_activity)
# ko apne bot ke functions se jodna hai - woh tumhare bot ke saath add karna.
# FAMPAY = FamPayGateway(FAMPAY_CFG, Hooks(get_db=get_db, notify_user=..., notify_admin=..., on_credited=..., log_activity=...))


# ============ LOADING ANIMATION (1% -> 100%) ============


_PAY_LINE = "━━━━━━━━━━━━━━━━━━"


_XL_PCTS = (1, 14, 29, 43, 58, 72, 86, 100)


def _xl_bar(p):
    n = max(0, min(10, p // 10))
    return "▰" * n + "▱" * (10 - n)


def _xl_frame(title, p, label):
    return f"{title}\n<code>{_xl_bar(p)}  {p}%</code>\n<i>{label}</i>"


def _xl_labels(labels, count):
    out = []
    for i in range(count):
        out.append(labels[min(len(labels) - 1, i * len(labels) // count)])
    return out


def _xl_play(chat_id, mid, title, labels, seconds=1.2, pcts=_XL_PCTS):
    """Animations disabled: callers can proceed directly to the final screen."""
    return True


def _pay_edit_safe(chat_id, msg_id, text, markup=None):
    """Safe edit: swallows 'message is not modified', retries ONCE after 1.2s on 'Too Many Requests'."""
    for attempt in range(2):
        try:
            bot.edit_message_text(text, chat_id, msg_id, parse_mode="HTML", reply_markup=markup)
            return True
        except Exception as e:
            low = str(e).lower()
            if "message is not modified" in low:
                return True
            if attempt == 0 and ("too many requests" in low or "429" in low):
                time.sleep(1.2)
                continue
            logger.warning(f"_pay_edit_safe failed: {e}")
            return False
    return False


def _pay_edit(chat_id, message_id, text, markup=None):
    """Edit a message for animation frames. Returns True on success (or unchanged), False otherwise."""
    return _pay_edit_safe(chat_id, message_id, text, markup)


def _pay_play_frames(chat_id, message_id, frames, delay=0.4):
    """Play short edit-animation frames on an existing message. Never raises."""
    if QUICK_UI:
        return True
    for fr in frames:
        try:
            if not _pay_edit(chat_id, message_id, fr):
                return False
            time.sleep(delay * ANIM_SPEED)
        except Exception:
            return False
    return True


def _pay_progressive(chat_id, steps, final_markup=None, delay=0.55):
    """Send first step as a new message, then reveal remaining steps by editing it.
    Falls back to sending the final text as a fresh message if editing fails."""
    if not steps:
        return None
    if QUICK_UI:
        return safe_send(chat_id, steps[-1], final_markup)
    msg = safe_send(chat_id, steps[0])
    if msg is None:
        return None
    ok = True
    for i in range(1, len(steps)):
        time.sleep(delay * ANIM_SPEED)
        last = (i == len(steps) - 1)
        if not _pay_edit(chat_id, msg.message_id, steps[i], final_markup if last else None):
            ok = False
            break
    if not ok:
        return safe_send(chat_id, steps[-1], final_markup)
    return msg


def _pay_progressive_bg(chat_id, steps, final_markup=None, delay=0.55):
    """Run _pay_progressive in a daemon thread so callers (admin clicks) never block."""
    try:
        threading.Thread(target=_pay_progressive, args=(chat_id, steps, final_markup, delay), daemon=True).start()
    except Exception as e:
        logger.warning(f"pay progressive thread fail | {e}")


# ============ CUSTOM AMOUNT KEYPAD + QR GENERATE ============


def show_keypad(call, user_id, amount):
    min_deposit = get_setting("min_deposit", 10)
    is_new = is_new_user(user_id)

    markup = InlineKeyboardMarkup(row_width=3)
    for row in (("1", "2", "3"), ("4", "5", "6"), ("7", "8", "9")):
        markup.add(*[InlineKeyboardButton(d, callback_data=f"pad_{d}", style="primary") for d in row])
    markup.add(
        InlineKeyboardButton("⌫", callback_data="pad_backspace", style="danger"),
        InlineKeyboardButton("0", callback_data="pad_0", style="primary"),
        InlineKeyboardButton("✅", callback_data="pad_enter", style="success"),
    )
    markup.add(InlineKeyboardButton("❌ Cancel", callback_data="back_main", style="danger"))

    shown = f"{int(amount):,}" if amount else "0"
    text = (
        f"<b>{esc(ap_plain('title'))}</b>\n"
        f"{_PAY_LINE}\n"
        f"{ap_text('keypad_sub')}\n\n"
        f"💳 <b>ENTER AMOUNT</b>\n"
        f"┏━━━━━━━━━━━━━━━━┓\n"
        f"      💵  <b>₹ {shown}</b> ▌\n"
        f"┗━━━━━━━━━━━━━━━━┛\n"
        f"👇 Keypad se amount daalo, phir ✅ dabao\n"
        f"{_PAY_LINE}"
    )
    if is_new:
        text += f"\n\n⚠️ Pehli baar ₹{min_deposit} minimum deposit karna padega.\n{_PAY_LINE}"
    safe_navigate(call, text, markup)


def handle_keypad(call, data, user_id):
    state = get_user_state(user_id)
    amount = state.get("keypad_amount", "") or ""

    if data == "pad_backspace":
        amount = amount[:-1]
    elif data == "pad_enter":
        if not amount:
            safe_answer(call, "❌ Amount enter karo", show_alert=True)
            return
        try:
            amt = int(amount)
        except ValueError:
            pop_user_state(user_id)
            safe_answer(call, "❌ Invalid amount", show_alert=True)
            return

        min_deposit = get_setting("min_deposit", 10)
        if is_new_user(user_id) and amt < min_deposit:
            safe_answer(call, f"❌ Minimum ₹{min_deposit} required!", show_alert=True)
            return
        if amt < 1 or amt > 100000:
            safe_answer(call, "❌ Amount ₹1 – ₹1,00,000", show_alert=True)
            return

        generate_qr(call, amt, user_id)
        return
    else:
        digit = data.replace("pad_", "")
        if digit.isdigit():
            if len(amount) < 7:
                amount += digit

    set_user_state(user_id, {"keypad_amount": amount})
    show_keypad(call, user_id, amount)


def generate_qr(call, amount, user_id):
    if is_duplicate_click(user_id, "qr_generate", window=6):
        safe_answer(call, "⏳ Please wait...", show_alert=True)
        return

    def _unavailable(title, body):
        pop_user_state(user_id)
        safe_answer(call, "❌ Auto payment unavailable", show_alert=True)
        safe_send(
            call.message.chat.id,
            f"❌ <b>{title}</b>\n\n{body}\n\n👉 <b>Manual Deposit</b> use karo.",
            InlineKeyboardMarkup(row_width=1).add(
                InlineKeyboardButton("📱 Manual Deposit", callback_data="manual_deposit", style="success"),
                InlineKeyboardButton("◀️ Back", callback_data="back_main", style="danger")))

    if not is_fampay_enabled():
        _unavailable("AUTO PAYMENT TEMPORARILY DISABLED", "UPI auto-payment abhi band hai.")
        return
    if not gmail_configured():
        logger.error("UPI QR requested but Gmail IMAP is not configured (set GMAIL_APP_PASSWORD).")
        _unavailable("PAYMENT UNAVAILABLE", "Auto payment service abhi available nahi hai.")
        return

    _lim_err = pro_deposit_limit_error(user_id, int(amount))
    if _lim_err:
        pop_user_state(user_id)
        safe_answer(call, _lim_err, show_alert=True)
        return

    _fg_remember_user(call.from_user)
    order_id, _err, upi_uri = FAMPAY.create_order(user_id, int(amount))
    if not order_id:
        pop_user_state(user_id)
        if _err == "too_many_open":
            safe_answer(call, "⛔ Pehle purane pending orders complete/cancel karo", show_alert=True)
        elif _err == "bad_amount":
            safe_answer(call, f"❌ Amount ₹{FAMPAY_CFG.min_amount} – ₹{FAMPAY_CFG.max_amount} ke beech hona chahiye", show_alert=True)
        elif _err == "not_configured":
            _unavailable("PAYMENT UNAVAILABLE", "Auto payment service abhi available nahi hai.")
        else:
            logger.error(f"create_order failed: {_err}")
            safe_answer(call, "❌ Error. Try again.", show_alert=True)
        return

    _t = esc(ap_plain("title"))
    _pay_play_frames(call.message.chat.id, call.message.message_id, [
        f"<b>{_t}</b>\n{_PAY_LINE}\n\n🔐 Secure order ban raha hai...",
        f"<b>{_t}</b>\n{_PAY_LINE}\n\n🔐 Order created ✅\n📲 QR generate ho raha hai...",
        f"<b>{_t}</b>\n{_PAY_LINE}\n\n🔐 Order created ✅\n📲 QR ready ✅\n💎 Opening payment screen...",
        f"<b>{_t}</b>\n{_PAY_LINE}\n\n🎯 <b>ORDER LOCKED — {order_id}</b>",
        f"<b>{_t}</b>\n{_PAY_LINE}\n\n🎯 <b>ORDER LOCKED — {order_id}</b>\n📲 <b>QR GENERATE HO GAYA ✅ — 15 min valid</b>",
    ], delay=0.4)
    try:
        bot.delete_message(call.message.chat.id, call.message.message_id)
    except Exception:
        pass

    _v = dict(amount=amount, upi=FAMPAY_UPI_ID, order=order_id, minutes=UPI_ORDER_WINDOW_SECONDS // 60)
    caption = (
        f"<b>{_t}</b>\n"
        f"{_PAY_LINE}\n"
        f"{ap_text('details', **_v)}\n"
        f"{_PAY_LINE}\n"
        f"{ap_text('howto', **_v)}\n"
        f"{_PAY_LINE}\n"
        f"{ap_text('footer', **_v)}"
    )
    markup = InlineKeyboardMarkup(row_width=1)
    markup.add(InlineKeyboardButton(ap_plain("btn_done"), callback_data=f"upi_utr_{order_id}", style="success"))
    markup.add(InlineKeyboardButton(ap_plain("btn_status"), callback_data="check_payment_status", style="primary"))
    markup.add(InlineKeyboardButton(ap_plain("btn_cancel"), callback_data=f"cancel_qr_{order_id}", style="danger"))
    png = make_upi_qr_png(upi_uri)
    try:
        if png is None:
            raise RuntimeError("qr_unavailable")
        if len(re.sub(r"<[^>]+>", "", caption)) > 1000:       # photo captions are limited to 1024 chars
            bot.send_photo(call.message.chat.id, png)
            safe_send(call.message.chat.id, caption, markup)
        else:
            bot.send_photo(call.message.chat.id, png, caption=caption, parse_mode="HTML", reply_markup=markup)
        safe_answer(call)
    except Exception as e:
        logger.error(f"QR send failed: {e}")
        safe_send(call.message.chat.id, caption, markup)
    finally:
        pop_user_state(user_id)
