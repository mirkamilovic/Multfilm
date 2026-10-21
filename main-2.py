# ======================================================================
# LUXOR CINEMA BOT — main.py (TO'LIQ, TUZATILGAN, YANGILANGAN VERSIYA)
# ======================================================================
# YANGILIKLAR (v3):
#   • Kanalga avto-joylash endi BOT ICHIDAN sozlanadi: /admin → 📡 Post kanallari
#     (bir nechta kanal, har biriga kino / serial / multfilm turi alohida yoqiladi)
#   • Multfilm va multserial bo'limi: /addmultfilm, /addmultserial (+ tugmalar)
#   • Egasi admin yollaydi: /addadmin, /deladmin, /admins (yoki /admin → 👑 Jamoa)
#   • Post joylanmasa sababi adminga yoziladi; /postcheck — kanal huquqlarini tekshiradi
#   • Serial posti /done dan keyin joylanadi; yangi qismlar uchun alohida post
#   • Xatolar tuzatildi (kod tekshiruvi, matnsiz xabar, videoni fayl qilib yuborish, ...)
# ======================================================================
# Bu fayl sizning eski `bot_addons_v2-1.py` va `mini_app_v2.html`
# parchalaringizni to'g'ri birlashtirib, xatolarni tuzatib va yangi
# funksiyalarni qo'shib yozilgan TO'LIQ ishlaydigan bot.
#
# ⚠️ MUHIM: sizning asl `main.py` faylingiz menga yuklanmagan edi,
# shuning uchun bu fayl NOLDAN, addon fayllaringizdagi sxema asosida
# ("users" va "movies" jadvallari) qurildi. Agar sizning eski botingizda
# boshqa qo'shimcha funksiyalar bo'lgan bo'lsa, ularni shu faylga
# qo'shishim uchun ayting.
#
# ISHGA TUSHIRISH:
#   1) Railway "Variables" bo'limiga quyidagilarni qo'shing:
#        BOT_TOKEN        - @BotFather bergan token
#        ADMIN_IDS         - masalan: 123456789,987654321
#        WEBHOOK_HOST      - masalan: https://luxor-cinema-bot-production.up.railway.app
#        (PORT ni Railway o'zi beradi, qo'lda kerak emas)
#   2) requirements.txt: aiogram>=3.4,<4  aiosqlite  aiohttp
#   3) mini_app.html shu main.py bilan bir papkada bo'lishi kerak.
# ======================================================================

import asyncio
import csv
import hashlib
import hmac
import io
import json
import logging
import os
import random
import re
import shutil
import gzip
import sqlite3
import tempfile
import time
from datetime import datetime, timedelta, timezone
import sys
from html import escape as html_escape
from urllib.parse import parse_qsl

import aiosqlite
import aiohttp
from aiohttp import web

from aiogram import Bot, Dispatcher, Router, F, BaseMiddleware
from aiogram.client.default import DefaultBotProperties, Default
from aiogram.client.session.middlewares.base import BaseRequestMiddleware
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandObject, CommandStart, StateFilter
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.exceptions import TelegramBadRequest, TelegramRetryAfter
from aiogram.types import (
    Message, CallbackQuery, PreCheckoutQuery, LabeledPrice, BufferedInputFile,
    ReplyKeyboardMarkup, KeyboardButton, WebAppInfo,
    InlineKeyboardMarkup, InlineKeyboardButton,
)
from aiogram.types import TelegramObject
from aiogram.types import ErrorEvent, BotCommand, BotCommandScopeChat
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiogram.webhook.aiohttp_server import SimpleRequestHandler, setup_application
from typing import Any, Awaitable, Callable, Union

# ----------------------------------------------------------------------
# KONFIGURATSIYA
# ----------------------------------------------------------------------
logging.basicConfig(level=logging.INFO, stream=sys.stdout)


def utcnow() -> datetime:
    """datetime.utcnow() o'rnini bosadi (u Python 3.12+ da eskirgan).
    Natija avvalgidek 'naive' UTC vaqt — bazadagi ISO satrlar bilan mos."""
    return datetime.now(timezone.utc).replace(tzinfo=None)

log = logging.getLogger("luxor-cinema-bot")

BOT_TOKEN = os.environ["BOT_TOKEN"]
ADMIN_IDS = {int(x) for x in os.environ.get("ADMIN_IDS", "").replace(" ", "").split(",") if x}
MODERATOR_IDS = {int(x) for x in os.environ.get("MODERATOR_IDS", "").replace(" ", "").split(",") if x}
STAFF_IDS = ADMIN_IDS | MODERATOR_IDS  # kontent boshqarish uchun — admin + moderator
# YANGI: OWNER_IDS — bot EGASI (Railway'dagi ADMIN_IDS). Admin yollash, zaxira/tiklash va CSV eksport faqat egasiga.
# Bot ichidan yollangan adminlar bazada (staff_members) saqlanadi va ishga tushganda ADMIN_IDS/MODERATOR_IDS ga qo'shiladi.
OWNER_IDS = frozenset(ADMIN_IDS)
ENV_MODERATOR_IDS = frozenset(MODERATOR_IDS)
DB_PATH = os.environ.get("DB_PATH", "bot.db")
# Railway'da "unable to open database file" xatosi ko'pincha DB_PATH'ning
# papkasi mavjud emasligidan kelib chiqadi (masalan DB_PATH=/data/bot.db
# lekin /data hali yaratilmagan). Shuni oldindan xavfsiz yaratib qo'yamiz.
# ⚠️ Eslatma: Railway konteyneri har safar qayta deploy qilinganda diskini
# tozalaydi — ma'lumotlar (foydalanuvchilar, kinolar) saqlanib qolishi uchun
# Railway'da Volume yarating va DB_PATH'ni o'sha volume yo'liga (masalan
# /data/bot.db) sozlang, aks holda har deploydan keyin baza bo'shab qoladi.
_db_dir = os.path.dirname(os.path.abspath(DB_PATH))
if _db_dir:
    os.makedirs(_db_dir, exist_ok=True)
PORT = int(os.environ.get("PORT", "8080"))
WEBHOOK_HOST = os.environ.get("WEBHOOK_HOST", "").rstrip("/")   # https://xxxx.up.railway.app

# ⚙️ "Do'kon: Maxsus takliflar" — "Sotib olish" tugmasi shu Telegram
# foydalanuvchisiga (sizga) avtomatik o'tadi. O'zgartirmoqchi bo'lsangiz —
# faqat shu qatorni tahrirlang (mini_app.html'da ham xuddi shu username bor,
# ikkalasini birga o'zgartiring).
SELLER_CONTACT_USERNAME = os.environ.get("SELLER_CONTACT_USERNAME", "Mirkamilovic")

# ⚙️ CLICK / PAYME — O'zbekiston to'lov tizimlari (real so'm bilan to'lov).
# Ishlashi uchun Click/Payme'da tadbirkor sifatida ro'yxatdan o'ting va
# quyidagi maydonlarni Railway'ning Environment Variables bo'limiga qo'ying.
# Kalitlar bo'sh bo'lsa, mini-app'da bu to'lov usuli avtomatik yashiriladi —
# hech narsa buzilmaydi, faqat variant ko'rinmaydi.
CLICK_MERCHANT_ID = os.environ.get("CLICK_MERCHANT_ID", "")
CLICK_SERVICE_ID = os.environ.get("CLICK_SERVICE_ID", "")
CLICK_SECRET_KEY = os.environ.get("CLICK_SECRET_KEY", "")
PAYME_MERCHANT_ID = os.environ.get("PAYME_MERCHANT_ID", "")
PAYME_SECRET_KEY = os.environ.get("PAYME_SECRET_KEY", "")
CLICK_PAYME_ENABLED = bool(CLICK_MERCHANT_ID or PAYME_MERCHANT_ID)
WEBHOOK_PATH = "/webhook"
MINI_APP_PATH = "/app"
HTML_FILE = os.path.join(os.path.dirname(__file__), "mini_app.html")

# ⚙️ YANGI: /start xabaridagi banner rasm. Telegram file_id yoki https:// rasm
# havolasi bo'lishi mumkin. Bo'sh qoldirilsa — banner rasmisiz, oddiy matn bilan
# yuboriladi (hech narsa buzilmaydi).
WELCOME_PHOTO = os.environ.get("WELCOME_PHOTO", "")

# ⚙️ YANGI: kanalga AVTOMATIK JOYLASH — /addmovie yoki /addseries orqali
# yangi kino/serial qo'shilganda, bot shu kanalga rasm + matn + "Ko'rish"
# tugmasi bilan post qiladi (skrindagi "Valor Cinema" postiga o'xshab).
# Railway "Variables" bo'limiga qo'shing:
#   POST_CHANNEL_ID  - masalan: @mychannel yoki -1001234567890
# ⭐ ENDI BU MAJBURIY EMAS: kanalni bot ichidan qo'shing — /admin → 📡 Post kanallari.
# Bu o'zgaruvchi faqat bot ichida birorta kanal qo'shilmagan bo'lsa zaxira sifatida ishlaydi.
# ⚠️ Bot shu kanalda ADMIN bo'lishi va "Postlarni joylash" huquqiga ega
# bo'lishi shart, aks holda xato chiqadi.
POST_CHANNEL_ID = os.environ.get("POST_CHANNEL_ID", "")
CHANNEL_BUTTON_TEXT = os.environ.get("CHANNEL_BUTTON_TEXT", "➕ Tomosha qilish ➕")

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp = Dispatcher(storage=MemoryStorage())

admin_router = Router(name="admin")
user_router = Router(name="user")
pay_router = Router(name="pay")

# ----------------------------------------------------------------------
# TARIFLAR / NARXLAR (Telegram Stars — XTR) — pul topish funksiyalari
# ----------------------------------------------------------------------
VIP_PLANS = {
    "vip_7":  {"days": 7,  "stars": 149, "label": "💎 VIP — 7 kun"},
    "vip_30": {"days": 30, "stars": 399, "label": "💎 VIP — 30 kun"},
}
DONATE_OPTIONS = [20, 50, 100, 300]

# ----------------------------------------------------------------------
# DB SXEMASI
# ----------------------------------------------------------------------
SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS users (
    user_id INTEGER PRIMARY KEY,
    full_name TEXT,
    username TEXT,
    vip_until TEXT,
    joined_at TEXT NOT NULL,
    referred_by INTEGER,
    referral_count INTEGER NOT NULL DEFAULT 0,
    stars_spent INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS movies (
    code TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    genre TEXT,
    description TEXT,
    file_id TEXT,
    views INTEGER NOT NULL DEFAULT 0,
    is_vip INTEGER NOT NULL DEFAULT 0,
    price_stars INTEGER NOT NULL DEFAULT 0,
    added_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS movie_ratings (
    user_id INTEGER NOT NULL,
    movie_code TEXT NOT NULL,
    rating INTEGER NOT NULL,
    PRIMARY KEY (user_id, movie_code)
);

CREATE TABLE IF NOT EXISTS movie_purchases (
    user_id INTEGER NOT NULL,
    movie_code TEXT NOT NULL,
    purchased_at TEXT NOT NULL,
    PRIMARY KEY (user_id, movie_code)
);

CREATE TABLE IF NOT EXISTS payments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    kind TEXT NOT NULL,
    ref TEXT,
    amount_stars INTEGER NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS user_favorites (
    user_id INTEGER NOT NULL,
    movie_code TEXT NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY (user_id, movie_code)
);

CREATE TABLE IF NOT EXISTS movie_requests (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    title TEXT NOT NULL,
    note TEXT,
    status TEXT NOT NULL DEFAULT 'pending',
    created_at TEXT NOT NULL,
    resolved_at TEXT
);

CREATE TABLE IF NOT EXISTS daily_checkins (
    user_id INTEGER PRIMARY KEY,
    streak INTEGER NOT NULL DEFAULT 0,
    total_checkins INTEGER NOT NULL DEFAULT 0,
    last_checkin_date TEXT
);

CREATE TABLE IF NOT EXISTS genre_subscriptions (
    user_id INTEGER NOT NULL,
    genre TEXT NOT NULL,
    PRIMARY KEY (user_id, genre)
);

CREATE TABLE IF NOT EXISTS banned_users (
    user_id INTEGER PRIMARY KEY,
    reason TEXT,
    banned_by INTEGER NOT NULL,
    banned_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS series (
    code TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    genre TEXT,
    description TEXT,
    is_vip INTEGER NOT NULL DEFAULT 0,
    price_stars INTEGER NOT NULL DEFAULT 0,
    added_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS series_episodes (
    series_code TEXT NOT NULL,
    episode_number INTEGER NOT NULL,
    file_id TEXT NOT NULL,
    views INTEGER NOT NULL DEFAULT 0,
    added_at TEXT NOT NULL,
    PRIMARY KEY (series_code, episode_number)
);

CREATE TABLE IF NOT EXISTS shop_products (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    description TEXT,
    price_stars INTEGER NOT NULL DEFAULT 0,
    emoji TEXT NOT NULL DEFAULT '🛍',
    active INTEGER NOT NULL DEFAULT 1,
    added_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS product_orders (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    product_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS movie_comments (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    code TEXT NOT NULL,
    kind TEXT NOT NULL DEFAULT 'movie',
    user_id INTEGER NOT NULL,
    username TEXT,
    text TEXT NOT NULL,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS watch_progress (
    user_id INTEGER NOT NULL,
    series_code TEXT NOT NULL,
    last_episode INTEGER NOT NULL,
    updated_at TEXT NOT NULL,
    PRIMARY KEY (user_id, series_code)
);

CREATE TABLE IF NOT EXISTS series_follows (
    user_id INTEGER NOT NULL,
    series_code TEXT NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY (user_id, series_code)
);

CREATE TABLE IF NOT EXISTS promo_codes (
    code TEXT PRIMARY KEY,
    vip_days INTEGER NOT NULL DEFAULT 0,
    max_uses INTEGER NOT NULL DEFAULT 1,
    used_count INTEGER NOT NULL DEFAULT 0,
    expires_at TEXT,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS promo_redemptions (
    code TEXT NOT NULL,
    user_id INTEGER NOT NULL,
    redeemed_at TEXT NOT NULL,
    PRIMARY KEY (code, user_id)
);

CREATE TABLE IF NOT EXISTS coming_soon (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    genre TEXT,
    poster_url TEXT,
    expected_date TEXT,
    released_code TEXT,
    created_at TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS coming_soon_waitlist (
    coming_soon_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    created_at TEXT NOT NULL,
    PRIMARY KEY (coming_soon_id, user_id)
);

CREATE TABLE IF NOT EXISTS achievements (
    id TEXT PRIMARY KEY,
    title TEXT NOT NULL,
    description TEXT NOT NULL,
    emoji TEXT NOT NULL DEFAULT '🏅'
);

CREATE TABLE IF NOT EXISTS user_achievements (
    user_id INTEGER NOT NULL,
    achievement_id TEXT NOT NULL,
    earned_at TEXT NOT NULL,
    PRIMARY KEY (user_id, achievement_id)
);

CREATE TABLE IF NOT EXISTS payment_orders (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    provider TEXT NOT NULL,
    kind TEXT NOT NULL,
    ref TEXT NOT NULL,
    amount_sum INTEGER NOT NULL,
    status TEXT NOT NULL DEFAULT 'pending',
    provider_txn_id TEXT,
    created_at TEXT NOT NULL,
    paid_at TEXT
);

CREATE TABLE IF NOT EXISTS watch_events (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    created_at TEXT NOT NULL
);

-- YANGI: Majburiy obuna kanallari — admin panel orqali qo'shiladi/o'chiriladi.
-- chat_id: @username yoki -100... ko'rinishidagi kanal ID (bot shu kanalda
-- ADMIN bo'lishi shart, aks holda obuna holatini tekshira olmaydi).
CREATE TABLE IF NOT EXISTS force_sub_channels (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    chat_id TEXT NOT NULL,
    title TEXT NOT NULL,
    url TEXT,
    added_at TEXT NOT NULL
);

-- YANGI: sozlamalar (masalan, kanal posti tugmasining matni)
CREATE TABLE IF NOT EXISTS bot_settings (
    key TEXT PRIMARY KEY,
    value TEXT
);

-- YANGI: premium emoji almashtirish (oddiy emoji -> premium emoji ID)
CREATE TABLE IF NOT EXISTS emoji_map (
    emoji TEXT PRIMARY KEY,
    custom_id TEXT NOT NULL,
    added_at TEXT NOT NULL
);

-- YANGI: bot ichidan yollangan adminlar. role: 'content' (kontent admin) | 'full' (to'liq admin)
CREATE TABLE IF NOT EXISTS staff_members (
    user_id INTEGER PRIMARY KEY,
    role TEXT NOT NULL DEFAULT 'content',
    name TEXT,
    added_by INTEGER,
    added_at TEXT NOT NULL
);

-- YANGI: postlar joylanadigan kanallar. kinds: 'movie,series,cartoon' (qaysi turlar tushishi)
CREATE TABLE IF NOT EXISTS post_channels (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    chat_id TEXT NOT NULL UNIQUE,
    title TEXT,
    kinds TEXT NOT NULL DEFAULT 'movie,series,cartoon',
    active INTEGER NOT NULL DEFAULT 1,
    added_at TEXT NOT NULL
);
"""


async def init_db() -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.executescript(SCHEMA_SQL)
        # Eski (allaqachon yaratilgan) bazalarga yangi ustunlarni xavfsiz qo'shish.
        # SQLite'da "ADD COLUMN IF NOT EXISTS" yo'q, shuning uchun har birini
        # alohida sinab, "duplicate column" xatosini e'tiborsiz qoldiramiz.
        for alter_sql in (
            "ALTER TABLE movies ADD COLUMN poster_url TEXT",
            "ALTER TABLE series ADD COLUMN poster_url TEXT",
            "ALTER TABLE movies ADD COLUMN year INTEGER",
            "ALTER TABLE movies ADD COLUMN country TEXT",
            "ALTER TABLE movies ADD COLUMN language TEXT",
            "ALTER TABLE series ADD COLUMN year INTEGER",
            "ALTER TABLE series ADD COLUMN country TEXT",
            "ALTER TABLE series ADD COLUMN language TEXT",
            "ALTER TABLE users ADD COLUMN lang TEXT DEFAULT 'uz'",
            "ALTER TABLE users ADD COLUMN vip_reminded_at TEXT",
            "ALTER TABLE movies ADD COLUMN category TEXT",          # 'movie' | 'cartoon'
            "ALTER TABLE series ADD COLUMN category TEXT",          # 'series' | 'cartoon'
            "ALTER TABLE movies ADD COLUMN file_kind TEXT",         # 'video' | 'document'
            "ALTER TABLE series_episodes ADD COLUMN file_kind TEXT",
            "ALTER TABLE movies ADD COLUMN quality TEXT",
            "ALTER TABLE series ADD COLUMN quality TEXT",
        ):
            try:
                await db.execute(alter_sql)
            except Exception:
                pass
        # Standart yutuqlar ro'yxatini bir marta ekish (mavjud bo'lsa qayta yozilmaydi)
        for a_id, title, desc, emoji in (
            ("watch_10", "Sinodef 10", "10 ta kino/qism ko'rdingiz", "🎬"),
            ("watch_50", "Kinoxo'r", "50 ta kino/qism ko'rdingiz", "🍿"),
            ("streak_7", "Bir hafta izchil", "7 kunlik kunlik bonus streak", "🔥"),
            ("streak_30", "Temir intizom", "30 kunlik kunlik bonus streak", "💎"),
            ("referral_5", "Do'stlar safari", "5 ta do'stingizni taklif qildingiz", "🤝"),
            ("first_comment", "Fikringiz muhim", "Birinchi izohingizni qoldirdingiz", "💬"),
        ):
            try:
                await db.execute(
                    "INSERT OR IGNORE INTO achievements (id, title, description, emoji) VALUES (?, ?, ?, ?)",
                    (a_id, title, desc, emoji),
                )
            except Exception:
                pass
        # Eski (qo'lda yozilgan) janrlarni tayyor ro'yxatga moslab tuzatish
        await _normalize_existing_genres(db)
        # Eski yozuvlarga tur belgilash: janri «Multfilm» bo'lsa — multfilm, aks holda kino/serial
        for tbl, normal in (("movies", "movie"), ("series", "series")):
            try:
                await db.execute(
                    f"UPDATE {tbl} SET category = CASE WHEN genre LIKE '%Multfilm%' THEN 'cartoon' ELSE '{normal}' END "
                    "WHERE category IS NULL"
                )
            except Exception:
                pass
        await db.commit()
    await load_staff_from_db()
    await load_emoji_map()


# ----------------------------------------------------------------------
# YORDAMCHI FUNKSIYALAR
# ----------------------------------------------------------------------
def now_iso() -> str:
    return utcnow().isoformat()


# ----------------------------------------------------------------------
# YANGI: POSTER — endi admin havola o'rniga to'g'ridan-to'g'ri SURAT
# yuboradi. Bazada "tg:<file_id>" ko'rinishida saqlanadi va mini-app'ga
# "/poster/<file_id>" havolasi sifatida beriladi (pastdagi serve_poster
# handleri shu file_id'ni Telegram serverlaridan olib, rasm sifatida
# qaytaradi). Eski http(s):// havolalar ham ishlashda davom etadi.
# ----------------------------------------------------------------------
def extract_poster(message: Message) -> str | None:
    """Admin poster bosqichida yuborgan narsani o'qiydi: SURAT bo'lsa uni
    'tg:<file_id>' qilib saqlaymiz (eng katta o'lchamini olamiz), eski
    http(s) havola yuborilsa uni ham qabul qilamiz, '-' bo'lsa postersiz."""
    if message.photo:
        return "tg:" + message.photo[-1].file_id
    text = (message.text or "").strip()
    if not text or text == "-":
        return None
    if text.startswith("http://") or text.startswith("https://"):
        return text
    return None


# (Kanalga avtomatik joylash funksiyalari — post_content_to_channel va boshqalar —
#  faylning pastki qismidagi "KANALGA AVTOMATIK JOYLASH" bo'limida.)

_SERIES_EP_RE = re.compile(r"^series_(.+)-ep(\d{1,4})$")


def parse_series_payload(payload: str) -> "tuple[str, int]":
    """'series_2001' → ('2001', 1);  'series_2001-ep5' → ('2001', 5)  (kanaldagi «yangi qism» posti uchun)."""
    m = _SERIES_EP_RE.match(payload or "")
    if m:
        return m.group(1), max(1, int(m.group(2)))
    return (payload or "").removeprefix("series_"), 1


def poster_col(col: str) -> str:
    """SQL ifoda: 'tg:<file_id>' ko'rinishida saqlangan posterni
    '/poster/<file_id>' havolasiga aylantiradi, http(s) havolalarni
    o'zgarishsiz qoldiradi."""
    alias = col.split(".")[-1]
    return f"CASE WHEN {col} LIKE 'tg:%' THEN '/poster/' || substr({col}, 4) ELSE {col} END AS {alias}"


# ----------------------------------------------------------------------
# YANGI: ONLAYN KO'RISH — mini-app ichida video pleer orqali tomosha
# qilish uchun qisqa muddatli, imzolangan token. Tokenni faqat shu
# foydalanuvchi, shu kino kodi va cheklangan vaqt uchun yaratamiz —
# shunday qilib to'g'ridan-to'g'ri video havolasi hech kimga oshkor
# bo'lmaydi va sizib chiqmaydi.
# ----------------------------------------------------------------------
STREAM_TOKEN_TTL = 6 * 60 * 60  # 6 soat


def make_stream_token(user_id: int, kind: str, code: str) -> str:
    expiry = int(utcnow().timestamp()) + STREAM_TOKEN_TTL
    payload = f"{kind}:{code}:{user_id}:{expiry}"
    sig = hmac.new(BOT_TOKEN.encode(), payload.encode(), hashlib.sha256).hexdigest()[:32]
    return f"{expiry}.{sig}"


def verify_stream_token(token: str, user_id: int, kind: str, code: str) -> bool:
    try:
        expiry_s, sig = token.split(".", 1)
        expiry = int(expiry_s)
    except (ValueError, AttributeError):
        return False
    if expiry < int(utcnow().timestamp()):
        return False
    payload = f"{kind}:{code}:{user_id}:{expiry}"
    expected = hmac.new(BOT_TOKEN.encode(), payload.encode(), hashlib.sha256).hexdigest()[:32]
    return hmac.compare_digest(sig, expected)


async def is_banned(user_id: int) -> bool:
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("SELECT 1 FROM banned_users WHERE user_id = ?", (user_id,))
        return (await cur.fetchone()) is not None


# ----------------------------------------------------------------------
# YANGI: MAJBURIY OBUNA (force-subscribe) — admin panel orqali qo'shilgan
# kanallarga obuna bo'lmagan foydalanuvchi botdan foydalana olmaydi.
# ----------------------------------------------------------------------
MAX_FORCE_SUB_CHANNELS = 15


async def get_force_sub_channels() -> list[dict]:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT id, chat_id, title, url FROM force_sub_channels ORDER BY id"
        )).fetchall()
    return [dict(r) for r in rows]


def _chat_ref(chat_id):
    """Bazadagi matn ko'rinishidagi kanal ID'sini Telegram API tushunadigan ko'rinishga keltiradi."""
    t = str(chat_id).strip()
    return int(t) if re.fullmatch(r"-?\d+", t) else t


_USERNAME_RE = re.compile(r"^@?([A-Za-z][A-Za-z0-9_]{3,31})$")
_TME_RE = re.compile(r"^(?:https?://)?(?:t|telegram)\.me/(.+)$", re.I)
_BUTTON_URL_RE = re.compile(r"^(?:https?://(?:t|telegram)\.me/\S+|tg://\S+)$", re.I)


def valid_button_url(url) -> bool:
    """Telegram inline-tugma uchun yaroqli havolami? (yaroqsiz havola xabarni butunlay
    yubormay qo'yardi — bot 'jim qolardi'; shuning uchun har doim tekshiramiz)."""
    return bool(_BUTTON_URL_RE.match((url or "").strip()))


def normalize_channel_ref(text) -> "str | None":
    """Admin yozgan kanal ko'rsatkichini @username yoki -100... ID ko'rinishiga keltiradi.
    Yaroqsiz bo'lsa (masalan '1', '293', 'W') None qaytaradi."""
    t = (text or "").strip()
    if not t:
        return None
    m = _TME_RE.match(t)
    if m:
        tail = m.group(1).split("?")[0].strip("/")
        if tail.startswith("+") or tail.startswith("joinchat"):
            return None  # taklif havolasidan kanal ID sini bilib bo'lmaydi
        t = tail.split("/")[0]
    if re.fullmatch(r"-100\d{5,}", t):
        return t
    m = _USERNAME_RE.match(t)
    return "@" + m.group(1) if m else None


async def resolve_channel_info(chat_id) -> dict:
    """Kanal haqida ma'lumot: nomi, havolasi, bot adminmi, xatolik matni."""
    info = {"title": None, "url": None, "is_admin": False, "error": None}
    ref = _chat_ref(chat_id)
    try:
        chat = await bot.get_chat(ref)
        info["title"] = getattr(chat, "title", None) or str(chat_id)
        username = getattr(chat, "username", None)
        if username:
            info["url"] = f"https://t.me/{username}"
        else:
            link = getattr(chat, "invite_link", None)
            if link and valid_button_url(link):
                info["url"] = link
    except Exception as e:
        info["error"] = str(e)
        return info
    try:
        me = await bot.get_me()
        member = await bot.get_chat_member(ref, me.id)
        info["is_admin"] = member.status in ("administrator", "creator")
    except Exception as e:
        info["error"] = str(e)
    if not info["url"] and info["is_admin"]:
        try:
            link = await bot.export_chat_invite_link(ref)
            if valid_button_url(link):
                info["url"] = link
        except Exception:
            pass
    return info


async def ensure_channel_url(ch: dict) -> "str | None":
    """Kanal tugmasi uchun YAROQLI havolani qaytaradi (kerak bo'lsa avtomatik topib, bazaga yozadi)."""
    url = (ch.get("url") or "").strip()
    if valid_button_url(url):
        return url
    cid = str(ch["chat_id"]).strip()
    url = None
    if cid.startswith("@") and _USERNAME_RE.match(cid):
        url = f"https://t.me/{cid[1:]}"
    else:
        url = (await resolve_channel_info(cid)).get("url")
    if url and valid_button_url(url):
        try:
            async with aiosqlite.connect(DB_PATH) as db:
                await db.execute("UPDATE force_sub_channels SET url = ? WHERE id = ?", (url, ch.get("id")))
                await db.commit()
        except Exception:
            pass
        return url
    return None


async def build_force_sub_markup(channels: list[dict]):
    """(inline klaviatura, havolasi topilmagan kanallar) — tugma har doim yaroqli havola bilan quriladi."""
    kb = InlineKeyboardBuilder()
    no_link: list[dict] = []
    for ch in channels:
        url = await ensure_channel_url(ch)
        if url:
            kb.button(text=f"📢 {str(ch['title'])[:40]}", url=url)
        else:
            no_link.append(ch)
    kb.button(text="✅ Bajardim", callback_data="fsub:check")
    kb.adjust(1)
    return kb.as_markup(), no_link


def no_link_lines(channels: list[dict]) -> str:
    if not channels:
        return ""
    lines = []
    for c in channels:
        cid = str(c["chat_id"])
        lines.append(f"• {html_escape(str(c['title']))}" + (f" — {html_escape(cid)}" if cid.startswith("@") else ""))
    return "\n\n" + "\n".join(lines)


FORCE_SUB_TEXT = (
    "🔒 <b>Botdan foydalanish uchun quyidagi kanal(lar)ga obuna bo'ling</b>,\n"
    "so'ngra pastdagi <b>\"✅ Bajardim\"</b> tugmasini bosing:"
)


async def _is_missing(ch: dict, user_id: int) -> bool:
    """True = foydalanuvchi bu kanalga obuna EMAS. Tekshirib bo'lmasa (bot admin emas va h.k.)
    kanal e'tiborga olinmaydi — foydalanuvchi bloklanib qolmasin."""
    try:
        member = await bot.get_chat_member(_chat_ref(ch["chat_id"]), user_id)
    except Exception:
        log.warning(
            "Majburiy obuna tekshiruvida xatolik (chat_id=%s) — bot shu kanalda admin emasmi?",
            ch["chat_id"],
        )
        return False
    if member.status in ("left", "kicked"):
        return True
    if member.status == "restricted" and getattr(member, "is_member", True) is False:
        return True
    return False


async def get_missing_channels(user_id: int) -> list[dict]:
    """Foydalanuvchi hali obuna bo'lmagan majburiy kanallar ro'yxati."""
    channels = await get_force_sub_channels()
    if not channels:
        return []
    flags = await asyncio.gather(*[_is_missing(ch, user_id) for ch in channels])
    return [ch for ch, missing in zip(channels, flags) if missing]


async def sanitize_force_sub_channels() -> None:
    """Bazadagi yaroqsiz havolalarni (masalan 'W') tozalaydi — ular tugmani buzardi."""
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute("SELECT id, url FROM force_sub_channels")).fetchall()
        for rid, url in rows:
            if url and not valid_button_url(url):
                await db.execute("UPDATE force_sub_channels SET url = NULL WHERE id = ?", (rid,))
        await db.commit()


class ForceSubMiddleware(BaseMiddleware):
    """user_router'dagi barcha message/callback handlerlaridan oldin ishga tushadi:
    majburiy kanallarga obuna bo'lmagan foydalanuvchini to'xtatib, obuna tugmalarini
    ko'rsatadi. Admin/moderatorlar va "fsub:" callbacklari bu tekshiruvdan chetlab o'tadi.
    MUHIM: xabar yuborishda xatolik bo'lsa ham bot JIM QOLMAYDI — zaxira variantlar bor."""

    async def __call__(
        self,
        handler: Callable[[TelegramObject, dict[str, Any]], Awaitable[Any]],
        event: Union[Message, CallbackQuery],
        data: dict[str, Any],
    ) -> Any:
        user = event.from_user
        if not user or user.id in STAFF_IDS:
            return await handler(event, data)
        if isinstance(event, CallbackQuery) and event.data and event.data.startswith("fsub:"):
            return await handler(event, data)
        if await is_banned(user.id):
            return await handler(event, data)

        missing = await get_missing_channels(user.id)
        if not missing:
            return await handler(event, data)

        # /start deep-link (movie_xxx, ref_xxx) bo'lsa, obuna tasdiqlangach davom ettirish uchun saqlaymiz.
        state: FSMContext | None = data.get("state")
        if state is not None and isinstance(event, Message) and event.text and event.text.startswith("/start"):
            parts = event.text.split(maxsplit=1)
            payload = parts[1] if len(parts) > 1 else ""
            await state.update_data(fsub_pending_payload=payload)

        target = event if isinstance(event, Message) else event.message
        if target is None:
            return await handler(event, data)

        # 1) asosiy variant: kanal tugmalari + «Bajardim»
        try:
            markup, no_link = await build_force_sub_markup(missing)
            await target.answer(FORCE_SUB_TEXT + no_link_lines(no_link), reply_markup=markup)
            if isinstance(event, CallbackQuery):
                await event.answer()
            return None
        except Exception:
            log.exception("Majburiy obuna xabarini yuborib bo'lmadi — zaxira variant sinab ko'riladi")

        # 2) zaxira: kanal havolasiz oddiy matn + faqat «Bajardim» tugmasi
        try:
            fallback_kb = InlineKeyboardMarkup(
                inline_keyboard=[[InlineKeyboardButton(text="✅ Bajardim", callback_data="fsub:check")]]
            )
            await target.answer(FORCE_SUB_TEXT + no_link_lines(missing), reply_markup=fallback_kb)
            if isinstance(event, CallbackQuery):
                await event.answer()
            return None
        except Exception:
            log.exception("Zaxira obuna xabari ham yuborilmadi — foydalanuvchi o'tkazib yuboriladi")

        # 3) hech narsa yordam bermasa — foydalanuvchini bloklamaymiz
        return await handler(event, data)


async def is_vip(user_id: int) -> bool:
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("SELECT vip_until FROM users WHERE user_id = ?", (user_id,))
        row = await cur.fetchone()
    if not row or not row[0]:
        return False
    try:
        return datetime.fromisoformat(row[0]) > utcnow()
    except ValueError:
        return False


async def extend_vip(user_id: int, days: int) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT vip_until FROM users WHERE user_id = ?", (user_id,))).fetchone()
        base = utcnow()
        if row and row["vip_until"]:
            try:
                current = datetime.fromisoformat(row["vip_until"])
                if current > base:
                    base = current
            except ValueError:
                pass
        new_until = (base + timedelta(days=days)).isoformat()
        await db.execute("UPDATE users SET vip_until = ? WHERE user_id = ?", (new_until, user_id))
        await db.commit()


async def ensure_user(user_id: int, full_name: str, username: str, referred_by: int | None = None) -> bool:
    """Foydalanuvchini bazaga qo'shadi (agar yo'q bo'lsa). True = yangi foydalanuvchi."""
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("SELECT 1 FROM users WHERE user_id = ?", (user_id,))
        exists = await cur.fetchone()
        if exists:
            await db.execute(
                "UPDATE users SET full_name = ?, username = ? WHERE user_id = ?",
                (full_name, username, user_id),
            )
            await db.commit()
            return False
        await db.execute(
            "INSERT INTO users (user_id, full_name, username, joined_at, referred_by) VALUES (?, ?, ?, ?, ?)",
            (user_id, full_name, username, now_iso(), referred_by),
        )
        if referred_by and referred_by != user_id:
            await db.execute(
                "UPDATE users SET referral_count = referral_count + 1 WHERE user_id = ?", (referred_by,)
            )
        await db.commit()
    if referred_by and referred_by != user_id:
        async with aiosqlite.connect(DB_PATH) as db:
            row = await (await db.execute(
                "SELECT referral_count FROM users WHERE user_id = ?", (referred_by,)
            )).fetchone()
        if row and row[0] % 5 == 0:
            await extend_vip(referred_by, 3)
            await grant_achievement(referred_by, "referral_5")
            try:
                await bot.send_message(
                    referred_by,
                    "🎉 Siz 5 ta do'stingizni taklif qildingiz — sovg'a sifatida 3 kunlik VIP oldingiz!",
                )
            except Exception:
                pass
    return True


def main_menu_kb(webapp_url: str) -> ReplyKeyboardMarkup:
    kb = [
        [KeyboardButton(text="🌐 Mini App", web_app=WebAppInfo(url=webapp_url))],
        [KeyboardButton(text="🔎 Nomi bo'yicha qidirish"), KeyboardButton(text="🆕 Yangi qo'shilganlar")],
        [KeyboardButton(text="🏆 TOP-10"), KeyboardButton(text="🎲 Tasodifiy kino")],
        [KeyboardButton(text="🧸 Multfilmlar"), KeyboardButton(text="📺 Seriallar")],
        [KeyboardButton(text="▶️ Davom ettirish"), KeyboardButton(text="💎 VIP olish")],
        [KeyboardButton(text="👥 Do'st taklif qilish"), KeyboardButton(text="ℹ️ Yordam")],
    ]
    return ReplyKeyboardMarkup(keyboard=kb, resize_keyboard=True)


# ----------------------------------------------------------------------
# YANGI: /start uchun zamonaviy, inline-tugmali karta (bannerli).
# Eslatma: inline tugmadagi Mini App ("🍿 Kino teatrni ochish" va h.k.)
# orqali ochilganda Telegram.WebApp.sendData() ba'zi klientlarda
# ishlamasligi mumkin edi — endi bu muammo yo'q, chunki kino/serial
# yetkazish endi tg.sendData()ga emas, /api/deliver-movie kabi to'g'ridan-
# to'g'ri HTTP so'rovlarga tayanadi (yuqoridagi izohga qarang).
# ----------------------------------------------------------------------
def welcome_inline_kb(webapp_url: str) -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="🍿 KINO TEATRNI OCHISH", web_app=WebAppInfo(url=webapp_url))
    kb.button(text="🔍 Kino qidirish", web_app=WebAppInfo(url=webapp_url + "?focus=search"))
    kb.button(text="🎲 Kino Ruletka", callback_data="quick:random")
    kb.button(text="🏆 TOP-10 kinolar", web_app=WebAppInfo(url=webapp_url + "?focus=top"))
    kb.button(text="💎 VIP / Do'kon", web_app=WebAppInfo(url=webapp_url + "?focus=shop"))
    kb.button(text="❤️ Saqlanganlar", web_app=WebAppInfo(url=webapp_url + "?focus=profile"))
    kb.button(text="👥 Do'st taklif qilish", callback_data="quick:referral")
    kb.button(text="ℹ️ Yordam", callback_data="quick:help")
    kb.adjust(1, 2, 2, 2, 1)
    return kb


async def notify_genre_subscribers(genre: str, movie_title: str, noun: str = "kino") -> None:
    if not genre:
        return
    # Kino bir nechta janrda bo'lishi mumkin ("Jangari, Triller") —
    # har bir janr obunachisiga xabar boradi, lekin bir kishiga faqat bir marta.
    names = normalize_genres(genre)[0] or split_genres(genre)
    if not names:
        return
    user_ids: set[int] = set()
    async with aiosqlite.connect(DB_PATH) as db:
        for g in names:
            cur = await db.execute("SELECT user_id FROM genre_subscriptions WHERE genre = ?", (g,))
            user_ids.update(r[0] for r in await cur.fetchall())
    label = ", ".join(names)
    for uid in user_ids:
        try:
            await bot.send_message(uid, f"🔔 Yangi {label} janridagi {noun} qo'shildi: <b>{html_escape(movie_title)}</b>")
        except Exception:
            pass
        await asyncio.sleep(0.05)


async def notify_series_followers(series_code: str, series_title: str, ep_num: int) -> None:
    """Sevimli serialining yangi qismi chiqqanda, uni oldin ko'rgan
    foydalanuvchilarga (series_follows) avtomatik xabar yuboradi."""
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute(
            "SELECT user_id FROM series_follows WHERE series_code = ?", (series_code,)
        )).fetchall()
    for (uid,) in rows:
        try:
            await bot.send_message(
                uid, f"🔔 <b>{series_title}</b> serialining {ep_num}-qismi chiqdi! Ko'rish uchun: {series_code}:{ep_num}"
            )
        except Exception:
            pass
        await asyncio.sleep(0.05)


# ----------------------------------------------------------------------
# YUTUQLAR (ACHIEVEMENTS) — kontent ko'rilganda avtomatik tekshiriladi
# ----------------------------------------------------------------------
async def grant_achievement(user_id: int, achievement_id: str) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        exists = await (await db.execute(
            "SELECT 1 FROM user_achievements WHERE user_id = ? AND achievement_id = ?",
            (user_id, achievement_id),
        )).fetchone()
        if exists:
            return
        a = await (await db.execute(
            "SELECT title, description, emoji FROM achievements WHERE id = ?", (achievement_id,)
        )).fetchone()
        if not a:
            return
        await db.execute(
            "INSERT INTO user_achievements (user_id, achievement_id, earned_at) VALUES (?, ?, ?)",
            (user_id, achievement_id, now_iso()),
        )
        await db.commit()
    try:
        await bot.send_message(
            user_id, f"🏆 Yangi yutuq! {a['emoji']} <b>{a['title']}</b>\n{a['description']}"
        )
    except Exception:
        pass


async def track_watch_event(user_id: int) -> None:
    """Har bir kino/qism ko'rishda chaqiriladi — "Sinodef 10" / "Kinoxo'r"
    yutuqlarini avtomatik tekshiradi."""
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("INSERT INTO watch_events (user_id, created_at) VALUES (?, ?)", (user_id, now_iso()))
        await db.commit()
        row = await (await db.execute(
            "SELECT COUNT(*) FROM watch_events WHERE user_id = ?", (user_id,)
        )).fetchone()
    count = row[0] if row else 0
    if count >= 10:
        await grant_achievement(user_id, "watch_10")
    if count >= 50:
        await grant_achievement(user_id, "watch_50")


# ----------------------------------------------------------------------
# KARTOCHKA DIZAYNI (kanal posti va bot yuboradigan kino xabari bir xil ko'rinadi)
#   🎬Nomi: ...📽 / 🇺🇿 O'zbek tilida ✅ / [ma'lumot bloki] / Tomosha qilish tugmasini bosing🔰
# Til, davlat, sifat, yil — kino/serial uchun /setinfo orqali o'zgartiriladi
# (kiritilmagan bo'lsa: O'zbek tilida, Uzb, 1080p, qo'shilgan yil).
# ----------------------------------------------------------------------
_LANG_FLAGS = (("o'zbek", "🇺🇿"), ("ozbek", "🇺🇿"), ("uzbek", "🇺🇿"), ("rus", "🇷🇺"), ("ingliz", "🇬🇧"),
               ("turk", "🇹🇷"), ("koreys", "🇰🇷"), ("hind", "🇮🇳"), ("yapon", "🇯🇵"), ("xitoy", "🇨🇳"))


def item_info(row) -> dict:
    keys = row.keys() if row is not None else []

    def g(k):
        return row[k] if k in keys and row[k] else None

    year = g("year")
    if not year:
        try:
            year = int(str(g("added_at") or "")[:4])
        except ValueError:
            year = utcnow().year
    return {
        "language": g("language") or "O'zbek tilida",
        "country": g("country") or "Uzb",
        "quality": g("quality") or "1080p",
        "year": year,
    }


def card_text(title: str, genre, info: dict, category, kind: str, *, code=None, price_stars: int = 0,
              head: str = "", episode_line: "str | None" = None,
              footer: str = "Tomosha qilish tugmasini bosing🔰") -> str:
    icon = "🧸" if category == "cartoon" else ("📺" if kind == "series" else "🎬")
    lang = str(info.get("language") or "O'zbek tilida")
    flag = next((f for k, f in _LANG_FLAGS if k in lang.lower()), "🌐")
    if "til" not in lang.lower():
        lang += " tilida"
    t = html_escape(title[:120])
    rows = [f"▶️📽 {t}"]
    if genre:
        rows.append(f"🎭 Janr: {html_escape(genre)}")
    if episode_line:
        rows.append(episode_line)
    rows += [
        f"🌍 Davlati: {html_escape(str(info.get('country') or 'Uzb'))}",
        f"♦️ Sifati: {html_escape(str(info.get('quality') or '1080p'))}",
        f"📆 Yili: {info.get('year')}",
    ]
    if price_stars:
        rows.append(f"⭐ Narxi: {price_stars} Stars")
    if code:
        rows.append(f"📌 Kod: <code>{html_escape(str(code))}</code>")
    return f"{head}{icon}Nomi: {t}📽\n\n{flag}{html_escape(lang)} ✅\n\n<blockquote>" + "\n".join(rows) + f"</blockquote>\n\n{footer}"


def post_markup(text: str, url: str, styled: bool = True) -> InlineKeyboardMarkup:
    """Kanal posti tugmasi. styled=True bo'lsa yashil ('success') tugma so'raladi; Telegram qabul qilmasa oddiy tugma ishlatiladi."""
    btn = None
    if styled:
        try:
            btn = InlineKeyboardButton(text=text, url=url, style="success")
        except Exception:
            btn = None
    if btn is None:
        btn = InlineKeyboardButton(text=text, url=url)
    return InlineKeyboardMarkup(inline_keyboard=[[btn]])


async def deliver_movie(chat_id: int, user_id: int, code: str, announce_missing: bool = True) -> bool:
    """Kinoni foydalanuvchiga yuboradi (VIP/narx tekshiruvi bilan).
    Qaytaradi: kod topilib yuborilgan/yuborilishga urinilgan bo'lsa True,
    bunday kodli kino umuman topilmasa False (announce_missing=False bo'lsa
    bu holatda hech qanday xabar yubormaydi — masalan, serial kodlarini ham
    tekshirib ko'rish uchun, "topilmadi" xabarini faqat ikkalasi ham
    topilmaganda bir marta ko'rsatish maqsadida)."""
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        movie = await (await db.execute("SELECT * FROM movies WHERE code = ?", (code,))).fetchone()
    if not movie:
        if announce_missing:
            await bot.send_message(
                chat_id,
                "😔 Bunday kodli kino topilmadi.\nMini App orqali kino so'rovi yuborishingiz mumkin.",
            )
        return False

    if movie["is_vip"] and not await is_vip(user_id):
        await bot.send_message(
            chat_id,
            f"💎 <b>{movie['title']}</b> — faqat VIP a'zolar uchun.\n/vip buyrug'i orqali VIP oling.",
        )
        return True

    if movie["price_stars"] and movie["price_stars"] > 0 and not await is_vip(user_id):
        async with aiosqlite.connect(DB_PATH) as db:
            bought = await (await db.execute(
                "SELECT 1 FROM movie_purchases WHERE user_id = ? AND movie_code = ?", (user_id, code)
            )).fetchone()
        if not bought:
            await bot.send_invoice(
                chat_id=chat_id,
                title=movie["title"],
                description=movie["description"] or "Eksklyuziv kino",
                payload=f"movie:{code}",
                currency="XTR",
                prices=[LabeledPrice(label=movie["title"], amount=movie["price_stars"])],
            )
            return True

    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE movies SET views = views + 1 WHERE code = ?", (code,))
        await db.commit()

    m_cat = movie["category"] if "category" in movie.keys() else None
    caption = card_text(
        movie["title"], movie["genre"], item_info(movie), m_cat, "movie",
        code=code, footer="🍿 Yoqimli tomosha!",
    )
    kb = InlineKeyboardBuilder()
    for n in range(1, 6):
        kb.button(text="⭐" * n, callback_data=f"rate:{code}:{n}")
    kb.adjust(5)
    if movie["file_id"]:
        m_kind = movie["file_kind"] if "file_kind" in movie.keys() else None
        sender = bot.send_document if m_kind == "document" else bot.send_video
        await sender(chat_id, movie["file_id"], caption=caption, reply_markup=kb.as_markup())
    else:
        await bot.send_message(chat_id, caption, reply_markup=kb.as_markup())
    await track_watch_event(user_id)
    return True


async def deliver_series_episode(
    chat_id: int, user_id: int, series_code: str, ep_num: int, announce_missing: bool = True
) -> bool:
    """Serial qismini foydalanuvchiga yuboradi (VIP/narx tekshiruvi serial darajasida).
    Qaytaradi: bunday kodli serial topilib biror amal bajarilgan (video yoki
    xabar yuborilgan) bo'lsa True, bunday kodli serial umuman topilmasa va
    announce_missing=False bo'lsa xabarsiz False qaytaradi."""
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        s = await (await db.execute("SELECT * FROM series WHERE code = ?", (series_code,))).fetchone()
        if not s:
            if announce_missing:
                await bot.send_message(chat_id, "😔 Bunday kodli serial topilmadi.")
            return False
        ep = await (await db.execute(
            "SELECT * FROM series_episodes WHERE series_code = ? AND episode_number = ?",
            (series_code, ep_num),
        )).fetchone()
        total_eps = (await (await db.execute(
            "SELECT COUNT(*) c FROM series_episodes WHERE series_code = ?", (series_code,)
        )).fetchone())["c"]

    if not ep:
        await bot.send_message(chat_id, f"😔 {ep_num}-qism hali yuklanmagan. Jami qismlar: {total_eps}")
        return True

    if s["is_vip"] and not await is_vip(user_id):
        await bot.send_message(
            chat_id, f"💎 <b>{s['title']}</b> — faqat VIP a'zolar uchun.\n/vip buyrug'i orqali VIP oling."
        )
        return True

    if s["price_stars"] and s["price_stars"] > 0 and not await is_vip(user_id):
        async with aiosqlite.connect(DB_PATH) as db:
            bought = await (await db.execute(
                "SELECT 1 FROM movie_purchases WHERE user_id = ? AND movie_code = ?",
                (user_id, series_code),
            )).fetchone()
        if not bought:
            await bot.send_invoice(
                chat_id=chat_id,
                title=s["title"],
                description=s["description"] or "Eksklyuziv serial",
                payload=f"series:{series_code}",
                currency="XTR",
                prices=[LabeledPrice(label=s["title"], amount=s["price_stars"])],
            )
            return True

    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "UPDATE series_episodes SET views = views + 1 WHERE series_code = ? AND episode_number = ?",
            (series_code, ep_num),
        )
        # "Davom ettirish" — foydalanuvchi qaysi qismda to'xtaganini eslab qolamiz
        await db.execute(
            """INSERT INTO watch_progress (user_id, series_code, last_episode, updated_at)
               VALUES (?, ?, ?, ?)
               ON CONFLICT(user_id, series_code) DO UPDATE SET last_episode=?, updated_at=?""",
            (user_id, series_code, ep_num, now_iso(), ep_num, now_iso()),
        )
        # Qism ko'rilganda avtomatik "kuzatuvchi" bo'ladi — yangi qism chiqqanda xabar oladi
        await db.execute(
            "INSERT OR IGNORE INTO series_follows (user_id, series_code, created_at) VALUES (?, ?, ?)",
            (user_id, series_code, now_iso()),
        )
        await db.commit()

    s_cat = s["category"] if "category" in s.keys() else None
    caption = card_text(
        s["title"], s["genre"], item_info(s), s_cat, "series",
        code=series_code, episode_line=f"📼 {ep_num}-qism ({total_eps} tadan)", footer="🍿 Yoqimli tomosha!",
    )
    kb = InlineKeyboardBuilder()
    if ep_num < total_eps:
        kb.button(text="▶️ Keyingi qism", callback_data=f"nextep:{series_code}:{ep_num + 1}")
    e_kind = ep["file_kind"] if "file_kind" in ep.keys() else None
    e_sender = bot.send_document if e_kind == "document" else bot.send_video
    await e_sender(chat_id, ep["file_id"], caption=caption, reply_markup=kb.as_markup() if ep_num < total_eps else None)
    await track_watch_event(user_id)
    return True


@user_router.callback_query(F.data.startswith("nextep:"))
async def cb_next_episode(callback: CallbackQuery) -> None:
    _, series_code, ep_num = callback.data.split(":")
    await callback.answer()
    if await is_banned(callback.from_user.id):
        return
    await deliver_series_episode(callback.message.chat.id, callback.from_user.id, series_code, int(ep_num))


# ----------------------------------------------------------------------
# YANGI: majburiy obuna tekshiruvini user_router'ning HAMMA message va
# callback handlerlariga qo'llash (admin/moderatorlarga taalluqli emas).
# ----------------------------------------------------------------------
user_router.message.middleware(ForceSubMiddleware())
user_router.callback_query.middleware(ForceSubMiddleware())


@user_router.callback_query(F.data == "fsub:check")
async def cb_fsub_check(callback: CallbackQuery, state: FSMContext) -> None:
    uid = callback.from_user.id
    missing = await get_missing_channels(uid)
    if missing:
        names = ", ".join(str(c["title"]) for c in missing)
        await callback.answer(f"❌ Hali obuna bo'lmagansiz: {names}"[:190], show_alert=True)
        return
    await callback.answer("✅ Obuna tasdiqlandi!")
    msg = callback.message
    chat_id = msg.chat.id if msg is not None else uid
    try:
        if msg is not None:
            await msg.delete()
    except Exception:
        pass
    try:
        data = await state.get_data()
        payload = data.get("fsub_pending_payload") or ""
        if payload:
            await state.update_data(fsub_pending_payload=None)
        referred_by = None
        if payload.startswith("ref_"):
            try:
                referred_by = int(payload.removeprefix("ref_"))
            except ValueError:
                referred_by = None
        await ensure_user(uid, callback.from_user.full_name, callback.from_user.username, referred_by)
        if payload.startswith("movie_"):
            await deliver_movie(chat_id, uid, payload.removeprefix("movie_"))
        elif payload.startswith("series_"):
            s_code, s_ep = parse_series_payload(payload)
            await deliver_series_episode(chat_id, uid, s_code, s_ep)
        else:
            await send_welcome(chat_id, uid, callback.from_user.full_name)
    except Exception:
        log.exception("fsub:check dan keyingi qadamda xatolik")
        try:
            await bot.send_message(chat_id, "✅ Obuna tasdiqlandi! Botdan foydalanish uchun /start ni bosing.")
        except Exception:
            pass


# ----------------------------------------------------------------------
# CORE: /start, /help, kino kodi orqali qidiruv
# ----------------------------------------------------------------------
@user_router.message(CommandStart(deep_link=True))
async def cmd_start_deeplink(message: Message, command: CommandObject) -> None:
    if await is_banned(message.from_user.id):
        return
    referred_by = None
    payload = command.args or ""
    if payload.startswith("ref_"):
        try:
            referred_by = int(payload.removeprefix("ref_"))
        except ValueError:
            referred_by = None
    await ensure_user(
        message.from_user.id, message.from_user.full_name, message.from_user.username, referred_by
    )
    if payload.startswith("movie_"):
        await deliver_movie(message.chat.id, message.from_user.id, payload.removeprefix("movie_"))
        return
    if payload.startswith("series_"):
        s_code, s_ep = parse_series_payload(payload)
        await deliver_series_episode(message.chat.id, message.from_user.id, s_code, s_ep)
        return
    await send_welcome(message.chat.id, message.from_user.id, message.from_user.full_name)


@user_router.message(CommandStart())
async def cmd_start(message: Message) -> None:
    if await is_banned(message.from_user.id):
        return
    await ensure_user(message.from_user.id, message.from_user.full_name, message.from_user.username)
    await send_welcome(message.chat.id, message.from_user.id, message.from_user.full_name)


async def send_welcome(chat_id: int, user_id: int, full_name: str) -> None:
    webapp_url = f"{WEBHOOK_HOST}{MINI_APP_PATH}" if WEBHOOK_HOST else "https://example.com"
    lang = await get_user_lang(user_id)
    text = (
        "👑 ───── ✦ <b>LUXOR CINEMA</b> ✦ ───── 👑\n\n"
        f"✨ Xush kelibsiz, <b>{html_escape(full_name)}</b>!\n\n"
        + UI_TEXT["welcome"].get(lang, UI_TEXT["welcome"]["uz"]) +
        "\n\n🎬 Kino kodini kiriting (masalan: 105) yoki pastdagi menyudan tanlang:"
    )
    kb = welcome_inline_kb(webapp_url).as_markup()
    sent_photo = False
    if WELCOME_PHOTO:
        try:
            await bot.send_photo(chat_id, WELCOME_PHOTO, caption=text, reply_markup=kb)
            sent_photo = True
        except Exception:
            log.exception("WELCOME_PHOTO yuborilmadi, matn bilan davom etiladi")
    if not sent_photo:
        await bot.send_message(chat_id, text, reply_markup=kb)
    # Doimiy pastki klaviatura ham qo'shiladi — bitta Telegram xabari faqat
    # bitta klaviatura turini ko'rsata oladi, shuning uchun bu qisqa
    # xizmat xabari orqali ikkalasi ham ochiq turadi.
    await bot.send_message(chat_id, "⌨️", reply_markup=main_menu_kb(webapp_url))


@user_router.message(Command("help"))
async def cmd_help(message: Message) -> None:
    await message.answer(
        "ℹ️ <b>Yordam</b>\n"
        "• Kino/serial kodini yozing — darhol keladi (serial bo'lsa 1-qism)\n"
        "/qidir <nomi> — nomi bo'yicha kino/serial qidirish\n"
        "/yangi — so'nggi qo'shilgan kino/seriallar\n"
        "/davom — to'xtagan serialingizni davom ettirish\n"
        "/top — eng ko'p ko'rilgan 10 ta kino\n"
        "/random — tasodifiy kino\n"
        "/vip — VIP a'zolik sotib olish\n"
        "/support — botni qo'llab-quvvatlash\n"
        "/referral — do'stlaringizni taklif qilib bonus oling\n"
        "/share &lt;kod&gt; — kinoni do'stingizga ulashish havolasini olish\n"
        "/promo &lt;kod&gt; — promo-kodni ishlatish\n"
        "/language — interfeys tilini o'zgartirish"
    )


# ----------------------------------------------------------------------
# YANGI: /start kartasidagi tezkor inline tugmalar (quick:*)
# ----------------------------------------------------------------------
@user_router.callback_query(F.data == "quick:random")
async def cb_quick_random(callback: CallbackQuery) -> None:
    await callback.answer()
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute("SELECT code FROM movies")).fetchall()
    if not rows:
        await callback.message.answer("Hozircha kinolar mavjud emas.")
        return
    code = random.choice(rows)[0]
    await deliver_movie(callback.message.chat.id, callback.from_user.id, code)


@user_router.callback_query(F.data == "quick:referral")
async def cb_quick_referral(callback: CallbackQuery) -> None:
    await callback.answer()
    me = await bot.get_me()
    link = f"https://t.me/{me.username}?start=ref_{callback.from_user.id}"
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT referral_count FROM users WHERE user_id = ?", (callback.from_user.id,)
        )).fetchone()
    count = row[0] if row else 0
    await callback.message.answer(
        "👥 <b>Do'stlaringizni taklif qiling!</b>\n\n"
        "Har <b>5 ta</b> taklif uchun — <b>3 kunlik VIP</b> sovg'a!\n\n"
        f"🔗 Sizning havolangiz:\n{link}\n\n"
        f"✅ Hozirgacha taklif qilinganlar: <b>{count}</b>"
    )


@user_router.callback_query(F.data == "quick:help")
async def cb_quick_help(callback: CallbackQuery) -> None:
    await callback.answer()
    await cmd_help(callback.message)


# ----------------------------------------------------------------------
# YANGI: ULASHISH (share) — do'stga yuborsa bo'ladigan havola yaratadi
# ----------------------------------------------------------------------
@user_router.message(Command("share"))
async def cmd_share(message: Message, command: CommandObject) -> None:
    if not command.args:
        await message.answer("Foydalanish: /share &lt;kino kodi&gt;")
        return
    code = command.args.strip()
    me = await bot.get_me()
    link = f"https://t.me/{me.username}?start=movie_{code}"
    kb = InlineKeyboardBuilder()
    kb.button(
        text="📤 Do'stlarga ulashish",
        url=f"https://t.me/share/url?url={link}&text=Bu kinoni ko'ring!",
    )
    await message.answer(f"🔗 Ulashish havolasi:\n{link}", reply_markup=kb.as_markup())


# ----------------------------------------------------------------------
# YANGI: KO'P TILLI INTERFEYS — asosiy menyu/salomlashuv uz/ru/en
# (to'liq bot emas, eng ko'p ishlatiladigan matnlar tarjima qilingan)
# ----------------------------------------------------------------------
UI_TEXT = {
    "welcome": {
        "uz": "🎬 <b>Luxor Cinema</b>ga xush kelibsiz!\n\nKino kodini yuboring — kino sizga darhol keladi.\nYoki pastdagi <b>Mini App</b> orqali katalogni ko'ring.",
        "ru": "🎬 Добро пожаловать в <b>Luxor Cinema</b>!\n\nОтправьте код фильма — он придёт сразу.\nИли откройте <b>Mini App</b> ниже для каталога.",
        "en": "🎬 Welcome to <b>Luxor Cinema</b>!\n\nSend a movie code — it arrives instantly.\nOr open the <b>Mini App</b> below to browse.",
    },
    "lang_set": {
        "uz": "✅ Til o'zbek tiliga o'zgartirildi.",
        "ru": "✅ Язык изменён на русский.",
        "en": "✅ Language switched to English.",
    },
}


async def get_user_lang(user_id: int) -> str:
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute("SELECT lang FROM users WHERE user_id = ?", (user_id,))).fetchone()
    return (row[0] if row and row[0] else "uz")


@user_router.message(Command("language"))
async def cmd_language(message: Message) -> None:
    kb = InlineKeyboardBuilder()
    kb.button(text="🇺🇿 O'zbek", callback_data="lang:uz")
    kb.button(text="🇷🇺 Русский", callback_data="lang:ru")
    kb.button(text="🇬🇧 English", callback_data="lang:en")
    kb.adjust(3)
    await message.answer("Tilni tanlang / Выберите язык / Choose language:", reply_markup=kb.as_markup())


@user_router.callback_query(F.data.startswith("lang:"))
async def cb_set_language(callback: CallbackQuery) -> None:
    lang = callback.data.split(":", 1)[1]
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE users SET lang = ? WHERE user_id = ?", (lang, callback.from_user.id))
        await db.commit()
    await callback.answer()
    await callback.message.answer(UI_TEXT["lang_set"].get(lang, UI_TEXT["lang_set"]["uz"]))


@user_router.message(F.web_app_data)
async def handle_webapp_data(message: Message) -> None:
    """Mini-app'dagi kino/serial kartochkasi bosilganda tg.sendData() orqali
    keladigan ma'lumotni qabul qiladi (oddiy kino kodi yoki 'KOD:QISM')."""
    if await is_banned(message.from_user.id):
        return
    data = (message.web_app_data.data or "").strip()
    if not data:
        return
    if ":" in data:
        code, _, ep = data.partition(":")
        if ep.isdigit():
            await deliver_series_episode(message.chat.id, message.from_user.id, code, int(ep))
            return
    await deliver_movie(message.chat.id, message.from_user.id, data)


@user_router.message(StateFilter(None), F.text.regexp(r"^[A-Za-z0-9_\-]{1,20}$"))
async def search_by_code(message: Message) -> None:
    """Foydalanuvchi oddiy matn (kod) yuborsa: avval kino kodlari orasidan
    qidiradi, topilmasa serial kodlari orasidan qidiradi va topilsa
    serialning 1-qismini yuboradi (YANGI: avval faqat kino kodlari
    ishlar edi, serial kodi yozilganda "topilmadi" chiqardi)."""
    if await is_banned(message.from_user.id):
        return
    code = message.text.strip()
    if await deliver_movie(message.chat.id, message.from_user.id, code, announce_missing=False):
        return
    if await deliver_series_episode(message.chat.id, message.from_user.id, code, 1, announce_missing=False):
        return
    await bot.send_message(
        message.chat.id,
        "😔 Bunday kodli kino yoki serial topilmadi.\nMini App orqali so'rov yuborishingiz mumkin.",
    )


@user_router.message(StateFilter(None), F.text.regexp(r"^[A-Za-z0-9_\-]{1,20}:\d{1,4}$"))
async def search_by_series_code(message: Message) -> None:
    """Foydalanuvchi 'KOD:QISM' formatida yuborsa (masalan 2001:3) — serial qismi."""
    if await is_banned(message.from_user.id):
        return
    code, _, ep = message.text.strip().partition(":")
    await deliver_series_episode(message.chat.id, message.from_user.id, code, int(ep))


# ----------------------------------------------------------------------
# YANGI QULAYLIK FUNKSIYASI 1/3 — NOMI BO'YICHA QIDIRISH
# Foydalanuvchi kino/serial kodini bilmasa ham, nomining bir qismini
# yozib qidira oladi (masalan "Titanik" yoki "Kelinlar qo'zg'oloni").
# ----------------------------------------------------------------------
class SearchStates(StatesGroup):
    query = State()


@user_router.message(Command("qidir"))
@user_router.message(F.text == "🔎 Nomi bo'yicha qidirish")
async def cmd_search_prompt(message: Message, state: FSMContext) -> None:
    if await is_banned(message.from_user.id):
        return
    args = message.text.split(maxsplit=1)
    if len(args) > 1:
        await run_title_search(message, args[1])
        return
    await state.set_state(SearchStates.query)
    await message.answer("🔎 Qidirmoqchi bo'lgan kino/serial nomining bir qismini yozing:")


@user_router.message(SearchStates.query)
async def cmd_search_query(message: Message, state: FSMContext) -> None:
    await state.clear()
    if not message.text:
        await message.answer("❌ Matn kiriting.")
        return
    await run_title_search(message, message.text.strip())


async def run_title_search(message: Message, query: str) -> None:
    like = f"%{query}%"
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        movies = await (await db.execute(
            "SELECT code, title FROM movies WHERE title LIKE ? ORDER BY views DESC LIMIT 10", (like,)
        )).fetchall()
        series = await (await db.execute(
            "SELECT code, title FROM series WHERE title LIKE ? ORDER BY code DESC LIMIT 10", (like,)
        )).fetchall()
    if not movies and not series:
        await message.answer(
            f"😔 \"{html_escape(query)}\" bo'yicha hech narsa topilmadi.\nMini App orqali kino so'rovi yuborishingiz mumkin."
        )
        return
    lines = [f"🔎 <b>\"{html_escape(query)}\"</b> bo'yicha natijalar:"]
    for r in movies:
        lines.append(f"🎬 {html_escape(r['title'])} — kod: <code>{html_escape(r['code'])}</code>")
    for r in series:
        lines.append(f"📺 {html_escape(r['title'])} — kod: <code>{html_escape(r['code'])}</code>")
    lines.append("\n👆 Kodni nusxalab, botga yuboring — kino/serial (1-qism) darhol keladi.")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI QULAYLIK FUNKSIYASI 2/3 — YANGI QO'SHILGAN KINO/SERIALLAR
# ----------------------------------------------------------------------
@user_router.message(Command("yangi"))
@user_router.message(F.text == "🆕 Yangi qo'shilganlar")
async def cmd_new_content(message: Message) -> None:
    if await is_banned(message.from_user.id):
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        movies = await (await db.execute(
            "SELECT code, title, added_at FROM movies ORDER BY added_at DESC LIMIT 5"
        )).fetchall()
        series = await (await db.execute(
            "SELECT code, title, added_at FROM series ORDER BY added_at DESC LIMIT 5"
        )).fetchall()
    combined = sorted(
        [("🎬", r) for r in movies] + [("📺", r) for r in series],
        key=lambda x: x[1]["added_at"], reverse=True,
    )[:10]
    if not combined:
        await message.answer("Hozircha kino/serial mavjud emas.")
        return
    lines = ["🆕 <b>So'nggi qo'shilganlar:</b>"]
    for icon, r in combined:
        lines.append(f"{icon} {html_escape(r['title'])} — kod: <code>{html_escape(r['code'])}</code>")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI QULAYLIK FUNKSIYASI 3/3 — "DAVOM ETTIRISH": foydalanuvchi
# to'xtagan seriallarini bir buyruq bilan davom ettiradi (watch_progress
# jadvali avvaldan bor edi, lekin botda buyruq/tugma orqali kirish yo'q edi
# — faqat mini-app ichida ishlar edi).
# ----------------------------------------------------------------------
@user_router.message(Command("davom"))
@user_router.message(F.text == "▶️ Davom ettirish")
async def cmd_continue_watching(message: Message) -> None:
    if await is_banned(message.from_user.id):
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            """SELECT w.series_code AS code, w.last_episode, s.title,
                      (SELECT COUNT(*) FROM series_episodes e WHERE e.series_code = w.series_code) AS total_eps
               FROM watch_progress w JOIN series s ON s.code = w.series_code
               WHERE w.user_id = ? ORDER BY w.updated_at DESC LIMIT 10""",
            (message.from_user.id,),
        )).fetchall()
    if not rows:
        await message.answer("📺 Hali birorta serialni tomosha qilishni boshlamagansiz.")
        return
    lines = ["▶️ <b>Davom ettirish:</b>"]
    kb = InlineKeyboardBuilder()
    has_buttons = False
    for r in rows:
        lines.append(f"📺 {html_escape(r['title'])} — {r['last_episode']}/{r['total_eps']}-qism ko'rilgan")
        if r["last_episode"] < r["total_eps"]:
            next_ep = r["last_episode"] + 1
            kb.button(text=f"▶️ {r['title']} ({next_ep}-qism)", callback_data=f"nextep:{r['code']}:{next_ep}")
            has_buttons = True
    kb.adjust(1)
    await message.answer("\n".join(lines), reply_markup=kb.as_markup() if has_buttons else None)


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI 1/5 — TOP-10 KINOLAR
# ----------------------------------------------------------------------
@user_router.message(Command("top"))
@user_router.message(F.text == "🏆 TOP-10")
async def cmd_top(message: Message) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT code, title, views FROM movies ORDER BY views DESC LIMIT 10"
        )).fetchall()
    if not rows:
        await message.answer("Hozircha kinolar mavjud emas.")
        return
    lines = ["🏆 <b>TOP-10 kino</b>"]
    for i, r in enumerate(rows, 1):
        lines.append(f"{i}. {r['title']} — {r['views']} ko'rish (kod: <code>{r['code']}</code>)")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI 2/5 — TASODIFIY KINO
# ----------------------------------------------------------------------
@user_router.message(Command("random"))
@user_router.message(F.text == "🎲 Tasodifiy kino")
async def cmd_random(message: Message) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute("SELECT code FROM movies")).fetchall()
    if not rows:
        await message.answer("Hozircha kinolar mavjud emas.")
        return
    code = random.choice(rows)[0]
    await deliver_movie(message.chat.id, message.from_user.id, code)


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI 3/5 — KINO BAHOLASH (reyting)
# ----------------------------------------------------------------------
@user_router.callback_query(F.data.startswith("rate:"))
async def cb_rate_movie(callback: CallbackQuery) -> None:
    _, code, n = callback.data.split(":")
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO movie_ratings (user_id, movie_code, rating) VALUES (?, ?, ?) "
            "ON CONFLICT(user_id, movie_code) DO UPDATE SET rating = excluded.rating",
            (callback.from_user.id, code, int(n)),
        )
        await db.commit()
        avg = await (await db.execute(
            "SELECT AVG(rating), COUNT(*) FROM movie_ratings WHERE movie_code = ?", (code,)
        )).fetchone()
    await callback.answer(f"Baholadingiz: {n}⭐  (o'rtacha: {avg[0]:.1f}, {avg[1]} ta baho)", show_alert=True)


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI 4/5 — REFERRAL (do'st taklif qilish)
# ----------------------------------------------------------------------
@user_router.message(Command("referral"))
@user_router.message(F.text == "👥 Do'st taklif qilish")
async def cmd_referral(message: Message) -> None:
    me = await bot.get_me()
    link = f"https://t.me/{me.username}?start=ref_{message.from_user.id}"
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT referral_count FROM users WHERE user_id = ?", (message.from_user.id,)
        )).fetchone()
    count = row[0] if row else 0
    await message.answer(
        "👥 <b>Do'stlaringizni taklif qiling!</b>\n\n"
        f"Har <b>5 ta</b> taklif uchun — <b>3 kunlik VIP</b> sovg'a!\n\n"
        f"🔗 Sizning havolangiz:\n{link}\n\n"
        f"✅ Hozirgacha taklif qilinganlar: <b>{count}</b>"
    )


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI 5/5 — ADMIN: FOYDALANUVCHILARNI CSV QILIB EKSPORT
# ----------------------------------------------------------------------
@admin_router.message(Command("export"))
async def admin_export_users(message: Message) -> None:
    if message.from_user.id not in OWNER_IDS:
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute("SELECT * FROM users")).fetchall()
    buf = io.StringIO()
    writer = csv.writer(buf)
    if rows:
        writer.writerow(rows[0].keys())
        for r in rows:
            writer.writerow(list(r))
    data = buf.getvalue().encode("utf-8")
    file = BufferedInputFile(data, filename="users_export.csv")
    await message.answer_document(file, caption=f"👤 Jami: {len(rows)} foydalanuvchi")


# ----------------------------------------------------------------------
# YANGI: TAYYOR JANRLAR RO'YXATI (xato yozilgan yoki yangi janr paydo
# bo'lib qolmasligi uchun). Admin janrni matn bilan yozmaydi — tugmalar
# orqali tanlaydi. Bitta kino/serial uchun ko'pi bilan MAX_GENRES_PER_ITEM
# ta janr tanlash mumkin. Ro'yxatni o'zgartirmoqchi bo'lsangiz — faqat
# shu GENRES ro'yxatini tahrirlang (mini-app ham shu ro'yxatni ishlatadi).
# ----------------------------------------------------------------------
GENRES: list[tuple[str, str]] = [
    ("Jangari", "💥"), ("Komediya", "😂"), ("Drama", "🎭"), ("Melodrama", "💞"),
    ("Triller", "🎯"), ("Qo'rqinchli", "👻"), ("Fantastika", "🚀"), ("Fantezi", "🧙"),
    ("Sarguzasht", "🧭"), ("Detektiv", "🕵️"), ("Kriminal", "🚔"), ("Tarixiy", "🏛"),
    ("Harbiy", "🎖"), ("Oilaviy", "👪"), ("Multfilm", "🧸"), ("Anime", "🌸"),
    ("Hujjatli", "🎞"), ("Hayotiy", "🌿"), ("Musiqiy", "🎵"), ("Sport", "⚽"),
    ("Vester", "🤠"), ("Klassika", "🎬"), ("Afsona", "📜"), ("Biografiya", "👤"), ("Dorama", "🎎"),
]
GENRE_NAMES: list[str] = [g for g, _ in GENRES]
GENRE_EMOJI: dict[str, str] = dict(GENRES)
MAX_GENRES_PER_ITEM = 3

_GENRE_APOSTROPHES = "'’‘`ʻʼ´"


def _gkey(text: str) -> str:
    """Janr nomini solishtirish uchun kalit: kichik harf, apostrofsiz, bo'shliqsiz."""
    t = (text or "").lower()
    for ch in _GENRE_APOSTROPHES:
        t = t.replace(ch, "")
    return "".join(c for c in t if c.isalnum())


_GENRE_KEYS: dict[str, str] = {_gkey(n): n for n in GENRE_NAMES}
# Eski/boshqacha yozilgan nomlar → tayyor janr
for _alias, _target in (
    ("hujjatli film", "Hujjatli"), ("dokumental", "Hujjatli"), ("korror", "Qo'rqinchli"),
    ("qorqinchli", "Qo'rqinchli"), ("multfilmlar", "Multfilm"), ("multik", "Multfilm"),
    ("romantik", "Melodrama"), ("fantasy", "Fantezi"), ("action", "Jangari"),
    ("comedy", "Komediya"), ("horror", "Qo'rqinchli"), ("thriller", "Triller"),
    ("kriminal", "Kriminal"), ("jinoyat", "Kriminal"), ("doramalar", "Dorama"), ("animelar", "Anime"), ("sarguzasht", "Sarguzasht"),
):
    _GENRE_KEYS.setdefault(_gkey(_alias), _target)


def split_genres(text) -> list[str]:
    return [p.strip() for p in re.split(r"[,;/|]+", text or "") if p.strip()]


def normalize_genres(text) -> tuple[list[str], list[str]]:
    """Matnni tayyor janrlarga moslaydi. (mos kelganlar, tanilmaganlar) qaytaradi."""
    matched: list[str] = []
    unknown: list[str] = []
    for part in split_genres(text):
        name = _GENRE_KEYS.get(_gkey(part))
        if name:
            if name not in matched:
                matched.append(name)
        else:
            unknown.append(part)
    return matched, unknown


async def _normalize_existing_genres(db) -> None:
    """Eski bazadagi janrlarni (masalan 'jangari ', 'Komediya' yoki 'Hujjatli film')
    tayyor ro'yxatdagi nomga keltiradi. Tanib bo'lmaydigan janrlarga tegmaydi."""
    for table in ("movies", "series", "coming_soon"):
        try:
            rows = await (await db.execute(
                f"SELECT DISTINCT genre FROM {table} WHERE genre IS NOT NULL AND genre != ''"
            )).fetchall()
            for (old,) in rows:
                matched, unknown = normalize_genres(old)
                if matched and not unknown:
                    new = ", ".join(matched)
                    if new != old:
                        await db.execute(f"UPDATE {table} SET genre = ? WHERE genre = ?", (new, old))
        except Exception:
            log.exception("Janrlarni tuzatishda xatolik (%s)", table)
    try:
        rows = await (await db.execute("SELECT DISTINCT genre FROM genre_subscriptions")).fetchall()
        for (old,) in rows:
            matched, unknown = normalize_genres(old)
            if len(matched) == 1 and not unknown and matched[0] != old:
                await db.execute(
                    "UPDATE OR IGNORE genre_subscriptions SET genre = ? WHERE genre = ?", (matched[0], old)
                )
                await db.execute("DELETE FROM genre_subscriptions WHERE genre = ?", (old,))
    except Exception:
        log.exception("Janr obunalarini tuzatishda xatolik")


def genre_prompt_text(selected: list[str], allow_keep: bool = False) -> str:
    text = (
        f"🎭 <b>Janrni tanlang</b> (ko'pi bilan {MAX_GENRES_PER_ITEM} ta).\n"
        "Tanlab bo'lgach «✔️ Tayyor» tugmasini bosing."
    )
    if selected:
        text += f"\n\nTanlandi: <b>{', '.join(selected)}</b>"
    if allow_keep:
        text += "\n(O'zgartirmaslik uchun ⏭ tugmasini bosing)"
    return text


def genre_picker_kb(selected: list[str], allow_keep: bool = False) -> InlineKeyboardMarkup:
    rows: list[list[InlineKeyboardButton]] = []
    row: list[InlineKeyboardButton] = []
    for i, (name, emoji) in enumerate(GENRES):
        mark = "✅" if name in selected else emoji
        row.append(InlineKeyboardButton(text=f"{mark} {name}", callback_data=f"gp:t:{i}"))
        if len(row) == 2:
            rows.append(row)
            row = []
    if row:
        rows.append(row)
    footer = [InlineKeyboardButton(text=f"✔️ Tayyor ({len(selected)})", callback_data="gp:done")]
    if selected:
        footer.insert(0, InlineKeyboardButton(text="♻️ Tozalash", callback_data="gp:clear"))
    rows.append(footer)
    if allow_keep:
        rows.append([InlineKeyboardButton(text="⏭ O'zgartirmaslik", callback_data="gp:keep")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


async def ask_genre(message: Message, state: FSMContext, flow: str, allow_keep: bool = False) -> None:
    """Admindan janrni TUGMALAR orqali tanlashni so'raydi (flow — qaysi jarayon davom etishini belgilaydi)."""
    await state.update_data(gp_flow=flow, gp_sel=[], gp_keep=allow_keep)
    await message.answer(genre_prompt_text([], allow_keep), reply_markup=genre_picker_kb([], allow_keep))


async def _genre_step_done(msg: Message, state: FSMContext) -> None:
    """Janr tanlangach — avvalgi jarayonning KEYINGI qadamiga o'tadi (oldingi tartib o'zgarmaydi)."""
    d = await state.get_data()
    flow, sel = d.get("gp_flow"), d.get("gp_sel") or []
    for k in ("gp_flow", "gp_sel", "gp_keep"):
        d.pop(k, None)
    if sel:
        d["genre"] = ", ".join(sel)
    await state.set_data(d)
    if flow == "addmovie":
        await state.set_state(AddMovieStates.video)
        await msg.answer("Endi video faylni yuboring (yoki 'yo'q' deb yozing):")
    elif flow == "addseries":
        await state.set_state(AddSeriesStates.price)
        await msg.answer("Narxini Stars da kiriting (bepul bo'lsa 0):")
    elif flow == "editmovie":
        await state.set_state(EditMovieStates.price)
        await msg.answer("Yangi narxni Stars da yuboring (o'zgartirmaslik uchun — deb yozing):")
    elif flow == "comingsoon":
        await state.set_state(AddComingSoonStates.date)
        await msg.answer("Taxminiy chiqish sanasini kiriting (masalan: 2026-10-01), yoki — deb yozing:")


async def genre_text_fallback(message: Message, state: FSMContext, flow: str, allow_keep: bool = False) -> None:
    """Admin tugma o'rniga matn yozib yuborsa: faqat tayyor ro'yxatdagi janr qabul qilinadi,
    xato yozilgan bo'lsa qayta tugmalar ko'rsatiladi."""
    text = (message.text or "").strip()
    if allow_keep and text == "-":
        await state.update_data(gp_flow=flow, gp_sel=[], gp_keep=True)
        await _genre_step_done(message, state)
        return
    matched, unknown = normalize_genres(text)
    if matched and not unknown:
        await state.update_data(gp_flow=flow, gp_sel=matched[:MAX_GENRES_PER_ITEM], gp_keep=allow_keep)
        await _genre_step_done(message, state)
        return
    note = f"❌ «{html_escape(', '.join(unknown))}» ro'yxatda yo'q.\n\n" if unknown else ""
    await state.update_data(gp_flow=flow, gp_sel=[], gp_keep=allow_keep)
    await message.answer(note + genre_prompt_text([], allow_keep), reply_markup=genre_picker_kb([], allow_keep))


@admin_router.callback_query(F.data.startswith("gp:"))
async def cb_genre_picker(callback: CallbackQuery, state: FSMContext) -> None:
    if callback.from_user.id not in STAFF_IDS:
        await callback.answer()
        return
    d = await state.get_data()
    flow = d.get("gp_flow")
    if not flow:
        await callback.answer("Bu tugma eskirgan. Amalni qaytadan boshlang.", show_alert=True)
        return
    sel = list(d.get("gp_sel") or [])
    keep = bool(d.get("gp_keep"))
    parts = callback.data.split(":")
    action = parts[1] if len(parts) > 1 else ""
    if action == "t":
        try:
            name = GENRES[int(parts[2])][0]
        except (IndexError, ValueError):
            await callback.answer()
            return
        if name in sel:
            sel.remove(name)
        elif len(sel) >= MAX_GENRES_PER_ITEM:
            await callback.answer(f"Ko'pi bilan {MAX_GENRES_PER_ITEM} ta janr tanlash mumkin", show_alert=True)
            return
        else:
            sel.append(name)
    elif action == "clear":
        sel = []
    elif action == "keep":
        if not keep:
            await callback.answer()
            return
        await state.update_data(gp_sel=[])
        try:
            await callback.message.edit_text("🎭 Janr: <b>o'zgartirilmadi</b>")
        except Exception:
            pass
        await callback.answer()
        await _genre_step_done(callback.message, state)
        return
    elif action == "done":
        if not sel:
            await callback.answer("Kamida bitta janr tanlang", show_alert=True)
            return
        try:
            await callback.message.edit_text(f"🎭 Janr: <b>{', '.join(sel)}</b>")
        except Exception:
            pass
        await callback.answer()
        await _genre_step_done(callback.message, state)
        return
    await state.update_data(gp_sel=sel)
    try:
        await callback.message.edit_text(genre_prompt_text(sel, keep), reply_markup=genre_picker_kb(sel, keep))
    except Exception:
        pass
    await callback.answer()


@admin_router.message(Command("genrecheck"))
async def admin_genrecheck(message: Message) -> None:
    """Bazada tayyor ro'yxatda yo'q (xato yozilgan) janrlari bor kino/seriallarni ko'rsatadi."""
    if message.from_user.id not in STAFF_IDS:
        return
    lines: list[str] = []
    async with aiosqlite.connect(DB_PATH) as db:
        for table, icon in (("movies", "🎬"), ("series", "📺")):
            rows = await (await db.execute(f"SELECT code, title, genre FROM {table}")).fetchall()
            for code, title, genre in rows:
                if not (genre or "").strip():
                    lines.append(f"{icon} <code>{html_escape(str(code))}</code> — {html_escape(str(title))}: <i>janr yo'q</i>")
                    continue
                _, unknown = normalize_genres(genre)
                if unknown:
                    lines.append(
                        f"{icon} <code>{html_escape(str(code))}</code> — {html_escape(str(title))}: «{html_escape(genre)}»"
                    )
    if not lines:
        await message.answer("✅ Hamma kino va seriallarning janri tayyor ro'yxatga mos.")
        return
    head = (
        f"⚠️ Janri tekshirilishi kerak: <b>{len(lines)}</b> ta\n"
        "Kino uchun: <code>/editmovie &lt;kod&gt;</code> — janr tugmalar bilan tanlanadi.\n"
        "Serial uchun: <code>/addseries</code> ni shu kod bilan qayta boshlang (qismlar saqlanib qoladi).\n\n"
    )
    chunk = head
    for line in lines:
        if len(chunk) + len(line) + 1 > 3800:
            await message.answer(chunk)
            chunk = ""
        chunk += line + "\n"
    if chunk:
        await message.answer(chunk)


# ----------------------------------------------------------------------
# YANGI QULAYLIKLAR (admin): keyingi bo'sh kodni taklif qilish, band kodni
# ogohlantirish va /cancel (jarayonni bekor qilish)
# ----------------------------------------------------------------------
async def next_free_code(kind: str) -> str:
    """Kino ('addmovie') yoki serial ('addseries') uchun keyingi bo'sh raqamli kod."""
    table, base = ("movies", 1001) if kind == "addmovie" else ("series", 2001)
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute(f"SELECT code FROM {table}")).fetchall()
    nums = [int(r[0]) for r in rows if str(r[0]).isdigit()]
    return str(max(nums) + 1) if nums else str(base)


async def code_hint(kind: str) -> str:
    code = await next_free_code(kind)
    return f"\n💡 Keyingi bo'sh kod: <code>{code}</code> — shuni ishlatish uchun <b>+</b> deb yozing."


async def resolve_code(message: Message, kind: str) -> str:
    """Admin yozgan kodni o'qiydi: '+' bo'lsa — keyingi bo'sh kod; band bo'lsa — ogohlantiradi (davom etadi)."""
    text = (message.text or "").strip()
    if text == "+":
        text = await next_free_code(kind)
        await message.answer(f"✅ Kod: <code>{text}</code>")
    table = "movies" if kind == "addmovie" else "series"
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(f"SELECT title FROM {table} WHERE code = ?", (text,))).fetchone()
    if row:
        await message.answer(
            f"⚠️ <code>{html_escape(text)}</code> kodi band: «{html_escape(str(row[0]))}». "
            "Davom etsangiz, eskisining o'rniga yangisi yoziladi. To'xtatish uchun /cancel yozing."
        )
    return text


@admin_router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    """Har qanday ko'p bosqichli jarayonni (kino qo'shish, tahrirlash va h.k.) to'xtatadi."""
    if await state.get_state() is None:
        await message.answer("Bekor qilinadigan amal yo'q.")
        return
    await state.clear()
    await message.answer("❌ Amal bekor qilindi.")


# ----------------------------------------------------------------------
# YANGI: BAZANI "ESLAB QOLISH" — zaxira (backup) va tiklash (restore)
#   • Bot bazani (kinolar, foydalanuvchilar, VIP, kanallar...) vaqti-vaqti bilan
#     Telegram'ga fayl qilib yuboradi va PIN qiladi (Railway diski tozalansa ham
#     nusxa Telegram'da qoladi).
#   • Baza butunlay bo'sh bo'lib ishga tushsa (masalan, Volume'siz deploydan keyin),
#     bot o'zi oxirgi pin qilingan zaxiradan tiklaydi.
#   • Qo'lda: /backup — hozir zaxira olish, /restore — faylni yuborib tiklash.
# Ixtiyoriy Railway o'zgaruvchilari:
#   BACKUP_CHAT_ID     — zaxira yuboriladigan yopiq kanal/guruh ID (bot admin bo'lsin).
#                        Bo'sh bo'lsa — ADMIN_IDS ning shaxsiy chatiga yuboriladi.
#   BACKUP_EVERY_HOURS — avtomatik zaxira oralig'i, soat (standart: 6)
#   AUTO_RESTORE       — 0 bo'lsa avtomatik tiklash o'chadi (standart: 1)
# ----------------------------------------------------------------------
BACKUP_CHAT_ID = os.environ.get("BACKUP_CHAT_ID", "").strip()
try:
    BACKUP_EVERY_HOURS = max(1, int(os.environ.get("BACKUP_EVERY_HOURS", "6")))
except ValueError:
    BACKUP_EVERY_HOURS = 6
AUTO_RESTORE = os.environ.get("AUTO_RESTORE", "1").strip() != "0"
BACKUP_GZIP_ABOVE = 15 * 1024 * 1024      # shundan katta bo'lsa siqib yuboriladi
BACKUP_DOWNLOAD_LIMIT = 20 * 1024 * 1024  # Telegram bot faylni ko'pi bilan 20 MB yuklab oladi

_backup_lock: "asyncio.Lock | None" = None
_backup_task: "asyncio.Task | None" = None
_last_backup_fp: "str | None" = None
_last_pin: dict = {}


def _get_backup_lock() -> asyncio.Lock:
    global _backup_lock
    if _backup_lock is None:
        _backup_lock = asyncio.Lock()
    return _backup_lock


def _backup_targets() -> list:
    if BACKUP_CHAT_ID:
        return [_chat_ref(BACKUP_CHAT_ID)]
    return sorted(OWNER_IDS)


def _snapshot_sync(src_path: str) -> bytes:
    """SQLite'ning xavfsiz 'online backup' usuli bilan izchil nusxa oladi."""
    fd, tmp = tempfile.mkstemp(suffix=".db")
    os.close(fd)
    try:
        src = sqlite3.connect(src_path)
        dst = sqlite3.connect(tmp)
        try:
            src.backup(dst)
        finally:
            dst.close()
            src.close()
        with open(tmp, "rb") as f:
            return f.read()
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass


async def db_counts() -> dict:
    out = {"movies": 0, "series": 0, "users": 0, "episodes": 0}
    async with aiosqlite.connect(DB_PATH) as db:
        for key, table in (("movies", "movies"), ("series", "series"),
                           ("users", "users"), ("episodes", "series_episodes")):
            try:
                row = await (await db.execute(f"SELECT COUNT(*) FROM {table}")).fetchone()
                out[key] = row[0]
            except Exception:
                out[key] = 0
    return out


def counts_line(c: dict) -> str:
    return f"🎬 {c['movies']} kino · 📺 {c['series']} serial ({c['episodes']} qism) · 👤 {c['users']} foydalanuvchi"


async def content_fingerprint() -> str:
    """Kontent (kino, serial, qism, do'kon, kanal, promo...) o'zgarganini bilish uchun."""
    h = hashlib.md5()
    async with aiosqlite.connect(DB_PATH) as db:
        for q in (
            "SELECT code,title,genre,price_stars,is_vip,file_id FROM movies ORDER BY code",
            "SELECT code,title,genre,price_stars,is_vip FROM series ORDER BY code",
            "SELECT series_code,episode_number,file_id FROM series_episodes ORDER BY series_code,episode_number",
            "SELECT id,title,price_stars,active FROM shop_products ORDER BY id",
            "SELECT id,chat_id,url FROM force_sub_channels ORDER BY id",
            "SELECT code,vip_days,max_uses FROM promo_codes ORDER BY code",
            "SELECT id,title,released_code FROM coming_soon ORDER BY id",
        ):
            try:
                rows = await (await db.execute(q)).fetchall()
            except Exception:
                rows = []
            h.update(repr(rows).encode("utf-8", "ignore"))
    return h.hexdigest()


async def send_backup(reason: str = "avto", targets: "list | None" = None, pin: bool = True, force: bool = False) -> int:
    """Bazaning nusxasini Telegram'ga yuboradi. Nechta joyga yuborilganini qaytaradi."""
    global _last_backup_fp
    counts = await db_counts()
    if not force and counts["movies"] + counts["series"] + counts["users"] == 0:
        log.info("Baza bo'sh — zaxira yuborilmadi (eski zaxira ustidan yozib yubormaslik uchun)")
        return 0
    fp = await content_fingerprint()
    async with _get_backup_lock():
        data = await asyncio.to_thread(_snapshot_sync, DB_PATH)
    stamp = utcnow().strftime("%Y%m%d_%H%M")
    name = f"luxor_backup_{stamp}.db"
    if len(data) > BACKUP_GZIP_ABOVE:
        data = gzip.compress(data)
        name += ".gz"
    caption = (
        f"💾 Zaxira ({reason})\n{counts_line(counts)}\n🕒 {stamp} UTC\n\n"
        "Tiklash: /restore — shu faylni yuborasiz."
    )
    can_pin = pin and (counts["movies"] + counts["series"] > 0)
    sent = 0
    for chat in (targets or _backup_targets()):
        try:
            m = await bot.send_document(chat, BufferedInputFile(data, filename=name), caption=caption)
            sent += 1
            if can_pin:
                try:
                    await bot.pin_chat_message(chat, m.message_id, disable_notification=True)
                    prev = _last_pin.get(str(chat))
                    if prev:
                        try:
                            await bot.unpin_chat_message(chat, prev)
                        except Exception:
                            pass
                    _last_pin[str(chat)] = m.message_id
                except Exception:
                    log.info("Zaxira xabarini pin qilib bo'lmadi (chat=%s)", chat)
        except Exception:
            log.exception("Zaxirani yuborib bo'lmadi (chat=%s)", chat)
    if sent:
        _last_backup_fp = fp
    return sent


def request_backup(delay: int = 60) -> None:
    """Admin kontentni o'zgartirgach, 1 daqiqadan keyin (o'zgarishlar yig'ilib) zaxira yuboradi."""
    global _backup_task
    if _backup_task is not None and not _backup_task.done():
        return

    async def _job() -> None:
        await asyncio.sleep(delay)
        try:
            await send_backup("o'zgarishdan keyin")
        except Exception:
            log.exception("Avto-zaxira xatosi")

    _backup_task = asyncio.create_task(_job())


class AdminBackupMiddleware(BaseMiddleware):
    """Admin/moderator handleri ishlab bo'lgach, kontent o'zgargan bo'lsa zaxirani rejalashtiradi."""

    async def __call__(self, handler, event, data):
        result = await handler(event, data)
        try:
            if await content_fingerprint() != _last_backup_fp:
                request_backup()
        except Exception:
            log.exception("AdminBackupMiddleware xatosi")
        return result


# (O'zgarishdan keyingi avto-zaxira o'chirildi: endi zaxira faqat kuniga bir marta, 07:00 da keladi.)


BACKUP_HOUR = int(os.environ.get("BACKUP_HOUR", "7"))                  # soat (mahalliy vaqt)
BACKUP_TZ_OFFSET = int(os.environ.get("BACKUP_TZ_OFFSET_HOURS", "5"))  # Toshkent = UTC+5


def seconds_until_backup() -> float:
    tz = timezone(timedelta(hours=BACKUP_TZ_OFFSET))
    now = datetime.now(tz)
    target = now.replace(hour=BACKUP_HOUR, minute=0, second=0, microsecond=0)
    if target <= now:
        target += timedelta(days=1)
    return (target - now).total_seconds()


async def backup_loop() -> None:
    """Har kuni bir marta, mahalliy vaqt bilan 07:00 da zaxira yuboradi."""
    while True:
        await asyncio.sleep(seconds_until_backup())
        try:
            await send_backup(f"kunlik — {BACKUP_HOUR:02d}:00")
        except Exception:
            log.exception("backup_loop xatosi")
        await asyncio.sleep(90)


async def _final_backup(app=None) -> None:
    """Bot to'xtaganda (deploy/restart) oxirgi nusxani yuboradi."""
    try:
        await asyncio.wait_for(send_backup("bot to'xtatilmoqda — deploy/restart"), timeout=8)
    except Exception:
        log.warning("Yakuniy zaxira yuborilmadi")


# ---- Faylni tekshirish / tiklash -------------------------------------------------
def _inspect_sync(path: str) -> dict:
    with open(path, "rb") as f:
        if f.read(16) != b"SQLite format 3\x00":
            raise ValueError("bu SQLite baza fayli emas")
    con = sqlite3.connect(path)
    try:
        if con.execute("PRAGMA integrity_check").fetchone()[0] != "ok":
            raise ValueError("fayl shikastlangan")
        tables = {r[0] for r in con.execute("SELECT name FROM sqlite_master WHERE type='table'")}
        if not {"movies", "users"} <= tables:
            raise ValueError("bu Luxor Cinema bazasi emas (movies/users jadvallari yo'q)")

        def cnt(t: str) -> int:
            return con.execute(f"SELECT COUNT(*) FROM {t}").fetchone()[0] if t in tables else 0

        return {"movies": cnt("movies"), "series": cnt("series"),
                "users": cnt("users"), "episodes": cnt("series_episodes")}
    finally:
        con.close()


async def _download_backup_file(doc) -> str:
    """Telegram hujjatini DB yoniga vaqtincha fayl qilib yuklaydi (.gz bo'lsa ochadi)."""
    if (getattr(doc, "file_size", None) or 0) > BACKUP_DOWNLOAD_LIMIT:
        raise ValueError("fayl 20 MB dan katta — Telegram bot uni yuklab ololmaydi")
    folder = os.path.dirname(os.path.abspath(DB_PATH)) or "."
    os.makedirs(folder, exist_ok=True)
    fd, tmp = tempfile.mkstemp(suffix=".incoming", dir=folder)
    os.close(fd)
    try:
        await bot.download(doc, destination=tmp)
        with open(tmp, "rb") as f:
            magic = f.read(2)
        if magic == b"\x1f\x8b":
            with gzip.open(tmp, "rb") as g:
                raw = g.read()
            with open(tmp, "wb") as f:
                f.write(raw)
        return tmp
    except Exception:
        try:
            os.remove(tmp)
        except OSError:
            pass
        raise


def _apply_restore_sync(incoming: str) -> None:
    if os.path.exists(DB_PATH):
        try:
            shutil.copy2(DB_PATH, DB_PATH + ".before_restore")
        except Exception:
            pass
    for suffix in ("-wal", "-shm"):
        p = DB_PATH + suffix
        if os.path.exists(p):
            try:
                os.remove(p)
            except OSError:
                pass
    os.replace(incoming, DB_PATH)


async def auto_restore_if_empty() -> "str | None":
    """Baza butunlay bo'sh bo'lsa — oxirgi PIN qilingan zaxiradan tiklaydi."""
    if not AUTO_RESTORE:
        return None
    c = await db_counts()
    if c["movies"] + c["series"] + c["users"] > 0:
        return None
    for chat in _backup_targets():
        try:
            chat_obj = await bot.get_chat(chat)
            pinned = getattr(chat_obj, "pinned_message", None)
            doc = getattr(pinned, "document", None) if pinned else None
            if not doc:
                continue
            path = await _download_backup_file(doc)
            try:
                info = await asyncio.to_thread(_inspect_sync, path)
                if info["movies"] + info["series"] + info["users"] == 0:
                    raise ValueError("zaxira ham bo'sh")
                await asyncio.to_thread(_apply_restore_sync, path)
            except Exception:
                try:
                    os.remove(path)
                except OSError:
                    pass
                raise
            await init_db()
            log.info("Baza zaxiradan avtomatik tiklandi: %s", counts_line(info))
            return counts_line(info)
        except Exception:
            log.exception("Avtomatik tiklash muvaffaqiyatsiz (chat=%s)", chat)
    return None


class RestoreStates(StatesGroup):
    file = State()


RESTORE_PROMPT = (
    "♻️ <b>Bazani tiklash</b>\n\n"
    "Bot yuborgan zaxira faylini (<code>.db</code> yoki <code>.db.gz</code>) shu yerga yuboring.\n"
    "Yoki fayl ostida /restore deb <b>javob (reply)</b> yozing.\n\n"
    "Tasdiqlashdan oldin fayl ichidagi kino/foydalanuvchi soni ko'rsatiladi.\n"
    "Bekor qilish: /cancel"
)


def _admin_backup_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="💾 Hozir zaxira olish", callback_data="admin_act:backupnow")
    kb.button(text="♻️ Zaxiradan tiklash", callback_data="admin_act:restore")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 1, 1)
    return kb


@admin_router.message(Command("backup"))
async def cmd_backup(message) -> None:
    if message.from_user.id not in OWNER_IDS:
        await message.answer("⛔ Bu buyruq faqat bot egasi uchun.")
        return
    await message.answer("⏳ Zaxira tayyorlanmoqda...")
    sent = await send_backup("qo'lda", targets=[message.from_user.id], force=True)
    if not sent:
        await message.answer("❌ Zaxirani yuborib bo'lmadi. Railway loglarini tekshiring.")


@admin_router.message(Command("restore"))
async def cmd_restore(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in OWNER_IDS:
        await message.answer("⛔ Bu buyruq faqat bot egasi uchun.")
        return
    reply = message.reply_to_message
    if reply is not None and reply.document is not None:
        await _restore_from_document(message, state, reply.document)
        return
    await state.set_state(RestoreStates.file)
    await message.answer(RESTORE_PROMPT)


@admin_router.message(RestoreStates.file, F.document)
async def restore_got_file(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in OWNER_IDS:
        return
    await _restore_from_document(message, state, message.document)


@admin_router.message(RestoreStates.file, F.text, ~F.text.startswith("/"))
async def restore_need_file(message: Message) -> None:
    if message.from_user.id not in OWNER_IDS:
        return
    await message.answer("❌ Zaxira faylini (hujjat) yuboring. Bekor qilish: /cancel")


async def _restore_from_document(message: Message, state: FSMContext, doc) -> None:
    name = (getattr(doc, "file_name", "") or "").lower()
    if not name.endswith((".db", ".gz", ".sqlite", ".sqlite3")):
        await message.answer("❌ Fayl <code>.db</code> yoki <code>.db.gz</code> bo'lishi kerak.")
        return
    await message.answer("⏳ Fayl tekshirilmoqda...")
    try:
        path = await _download_backup_file(doc)
        try:
            info = await asyncio.to_thread(_inspect_sync, path)
        except Exception:
            try:
                os.remove(path)
            except OSError:
                pass
            raise
    except Exception as e:
        await state.clear()
        await message.answer(f"❌ Fayl yaroqsiz: {html_escape(str(e)[:250])}")
        return
    cur = await db_counts()
    await state.clear()
    await state.update_data(restore_path=path)
    kb = InlineKeyboardBuilder()
    kb.button(text="✅ Tiklash", callback_data="restore:go")
    kb.button(text="❌ Bekor qilish", callback_data="restore:no")
    kb.adjust(2)
    await message.answer(
        "♻️ <b>Fayl to'g'ri.</b>\n\n"
        f"📦 Zaxirada: {counts_line(info)}\n"
        f"🗄 Hozirgi baza: {counts_line(cur)}\n\n"
        "⚠️ Hozirgi baza shu fayl bilan <b>almashtiriladi</b>. Tasdiqlaysizmi?",
        reply_markup=kb.as_markup(),
    )


@admin_router.callback_query(F.data.in_({"restore:go", "restore:no"}))
async def cb_restore(callback: CallbackQuery, state: FSMContext) -> None:
    if callback.from_user.id not in OWNER_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    await callback.answer()
    data = await state.get_data()
    path = data.get("restore_path")
    await state.update_data(restore_path=None)
    if callback.data == "restore:no" or not path or not os.path.exists(path):
        if path and os.path.exists(path):
            try:
                os.remove(path)
            except OSError:
                pass
        await callback.message.answer(
            "❌ Bekor qilindi." if callback.data == "restore:no"
            else "⚠️ Fayl topilmadi. /restore ni qaytadan boshlang."
        )
        return
    try:
        await asyncio.to_thread(_apply_restore_sync, path)
        await init_db()
        c = await db_counts()
    except Exception as e:
        log.exception("Tiklashda xatolik")
        await callback.message.answer(f"❌ Tiklashda xatolik: {html_escape(str(e)[:250])}")
        return
    await callback.message.answer(
        f"✅ <b>Baza tiklandi!</b>\n{counts_line(c)}\n\n"
        "Eski baza xavfsizlik uchun serverda <code>.before_restore</code> nomi bilan saqlandi."
    )


# ---- Admin buyruqlari ro'yxati (/adminhelp) va "/" menyusi ------------------------
STAFF_COMMANDS = [
    ("admin", "Admin panel (tugmalar)"),
    ("adminhelp", "Barcha admin buyruqlari"),
    ("addmovie", "Kino qo'shish"),
    ("addmultfilm", "Multfilm qo'shish"),
    ("editmovie", "Kino/multfilmni tahrirlash"),
    ("delmovie", "Kino/multfilmni o'chirish"),
    ("addseries", "Serial qo'shish"),
    ("addmultserial", "Multserial qo'shish"),
    ("addepisode", "Serialga qism qo'shish"),
    ("delseries", "Serialni o'chirish"),
    ("repost", "Postni kanalga qayta joylash"),
    ("setinfo", "Til, davlat, sifat, yil o'zgartirish"),
    ("addcomingsoon", "Tez orada ro'yxatiga qo'shish"),
    ("releasecoming", "Chiqarilgan deb belgilash"),
    ("movie_requests", "Kino so'rovlari"),
    ("delcomment", "Izohni o'chirish"),
    ("genrecheck", "Janri xato kinolar"),
    ("addfsub", "Majburiy kanal qo'shish"),
    ("fsublist", "Majburiy kanallar ro'yxati"),
    ("fsubtest", "Obuna xabarini ko'rish"),
    ("cancel", "Jarayonni bekor qilish"),
]
# To'liq admin va egasi uchun
ADMIN_ONLY_COMMANDS = [
    ("stats", "Umumiy statistika"),
    ("lowviews", "Kam ko'rilgan kinolar"),
    ("searchuser", "Foydalanuvchi qidirish"),
    ("user_info", "Foydalanuvchi ma'lumoti"),
    ("ban", "Bloklash"),
    ("unban", "Blokdan chiqarish"),
    ("givevip", "VIP berish"),
    ("removevip", "VIP olib tashlash"),
    ("broadcast", "Hammaga xabar"),
    ("broadcastvip", "VIP'larga xabar"),
    ("addpromo", "Promo-kod yaratish"),
    ("addproduct", "Do'kon taklifi qo'shish"),
    ("setemoji", "Premium emoji almashtirish"),
    ("emojis", "Almashtirilgan emojilar"),
    ("emojitoggle", "Premium emojini yoqish/o'chirish"),
    ("products", "Do'kon takliflari"),
    ("delproduct", "Do'kon taklifini o'chirish"),
]
CHANNEL_COMMANDS = [
    ("channels", "Post kanallari paneli"),
    ("setchannel", "Post kanali qo'shish"),
    ("postcheck", "Post kanallarini tekshirish"),
    ("setbtn", "Kanal posti tugmasi matni"),
]
# Faqat bot EGASI uchun
OWNER_COMMANDS = [
    ("addadmin", "Admin yollash"),
    ("deladmin", "Adminni olib tashlash"),
    ("admins", "Adminlar ro'yxati"),
    ("status", "Tizim holati"),
    ("export", "Foydalanuvchilar CSV"),
    ("backup", "Bazani zaxiralash"),
    ("restore", "Zaxiradan tiklash"),
]

ADMIN_HELP_STAFF = (
    "🛠 <b>ADMIN BUYRUQLARI</b>\n\n"
    "🎬 <b>Kontent</b> (barcha adminlar)\n"
    "/admin — tugmali panel (hammasi tugmalar bilan ham qilinadi)\n"
    "/addmovie — kino: kod → nom → janr → video → narx → poster → tavsif\n"
    "     <i>kod so'ralganda <code>+</code> yozsangiz — keyingi bo'sh kod olinadi</i>\n"
    "/addmultfilm — multfilm (xuddi shunday, «Multfilm» janri o'zi qo'shiladi)\n"
    "/addseries — serial · /addmultserial — multserial\n"
    "     <i>qismlarni birma-bir yuboring, tugagach /done — shunda kanalga post tushadi</i>\n"
    "/addepisode &lt;kod&gt; — mavjud serialga qism qo'shish\n"
    "/editmovie &lt;kod&gt; — nom, janr, narxni o'zgartirish\n"
    "/delmovie &lt;kod&gt; · /delseries &lt;kod&gt; — o'chirish\n"
    "/repost &lt;kod&gt; — postni kanalga qayta joylash\n"
    "/setinfo &lt;kod&gt; til | davlat | sifat | yil — kartochka ma'lumoti (masalan: <code>/setinfo 1001 Rus tilida | USA | 720p | 2024</code>; o'tkazish uchun -)\n"
    "/addcomingsoon · /releasecoming &lt;id&gt; &lt;kod&gt; — «Tez orada»\n"
    "/movie_requests — kino so'rovlari · /delcomment &lt;id&gt; — izoh o'chirish\n"
    "/genrecheck — janri xato kontent · /cancel — jarayonni bekor qilish\n\n"
    "📢 <b>Majburiy obuna</b>\n"
    "/addfsub · /fsublist · /fsubtest\n"
)
ADMIN_HELP_ADMIN = (
    "\n👨‍💼 <b>To'liq admin</b>\n"
    "/stats — statistika · /lowviews — kam ko'rilganlar\n"
    "/searchuser &lt;ism&gt; · /user_info &lt;id&gt;\n"
    "/ban &lt;id&gt; [sabab] · /unban &lt;id&gt;\n"
    "/givevip &lt;id&gt; &lt;kun&gt; · /removevip &lt;id&gt;\n"
    "/broadcast — hammaga · /broadcastvip — VIP'larga\n"
    "/addproduct · /products · /delproduct &lt;id&gt;\n"
    "✨ /setemoji — premium emoji almashtirish · /emojis — ro'yxat · /emojitoggle — yoqish/o'chirish\n"
    "/addpromo &lt;KOD&gt; &lt;vip_kun&gt; &lt;max&gt; [amal_kun]\n\n"
    "📡 <b>Post kanallari</b> (kanalga avto-joylash)\n"
    "/channels — kanallar paneli (turlarni yoqish/o'chirish, test post)\n"
    "/setchannel — kanal qo'shish (forward yoki @username)\n"
    "/postcheck — kanal va bot huquqlarini tekshirish\n"
    "/setbtn &lt;matn&gt; — post tugmasi yozuvi\n"
)
ADMIN_HELP_OWNER = (
    "\n👑 <b>Bot egasi</b>\n"
    "/addadmin &lt;id|@username&gt; [full] — admin yollash (full = to'liq admin)\n"
    "/deladmin &lt;id|@username&gt; — olib tashlash · /admins — ro'yxat\n"
    "/status — tizim holati (baza, kanallar, adminlar)\n"
    "/export — foydalanuvchilar CSV\n"
    "/backup · /restore — zaxira va tiklash\n"
    "<i>Bot zaxirani har kuni soat 07:00 da bir marta yuboradi. Hozir olish: /backup</i>\n"
)


async def cmd_adminhelp(message) -> None:
    uid = message.from_user.id
    if uid not in STAFF_IDS:
        return
    text = ADMIN_HELP_STAFF
    if uid in ADMIN_IDS:
        text += ADMIN_HELP_ADMIN
    if uid in OWNER_IDS:
        text += ADMIN_HELP_OWNER.replace("{hours}", str(BACKUP_EVERY_HOURS))
    await message.answer(text)


@admin_router.message(Command("adminhelp"))
async def _adminhelp_cmd(message: Message) -> None:
    await cmd_adminhelp(message)


async def register_admin_commands() -> None:
    """Har kimning Telegram "/" menyusiga FAQAT o'z darajasiga mos buyruqlar yoziladi (kontent admin / to'liq admin / ega)."""
    for uid in list(STAFF_IDS):
        await refresh_commands_for(uid)


async def notify_startup(restored: "str | None") -> None:
    c = await db_counts()
    db_dir = os.path.dirname(os.path.abspath(DB_PATH))
    on_volume = os.path.ismount(db_dir)
    lines = [
        "🟢 <b>Bot ishga tushdi</b>",
        f"🗄 Baza: <code>{html_escape(DB_PATH)}</code> — "
        + ("Volume ✅" if on_volume else "Volume EMAS ⚠️ (deploydan keyin baza tozalanishi mumkin)"),
        counts_line(c),
        f"🌐 Rejim: {'webhook' if WEBHOOK_HOST else 'polling'}",
    ]
    if restored:
        lines.append(f"♻️ Baza zaxiradan avtomatik tiklandi: {restored}")
    elif c["movies"] + c["series"] + c["users"] == 0:
        lines.append("ℹ️ Baza bo'sh. Zaxira fayli bo'lsa /restore bilan tiklang.")
    lines.append("📖 Barcha buyruqlar: /adminhelp")
    for uid in OWNER_IDS:
        try:
            await bot.send_message(uid, "\n".join(lines))
        except Exception:
            pass


async def post_startup(restored: "str | None") -> None:
    try:
        await sanitize_force_sub_channels()
    except Exception:
        log.exception("Majburiy kanal havolalarini tozalashda xatolik")
    await register_admin_commands()
    await notify_startup(restored)
    await check_post_channels_on_startup()
    asyncio.create_task(backup_loop())


_last_err_notice: dict = {}


async def on_unhandled_error(event: ErrorEvent) -> bool:
    """Handlerlardagi kutilmagan xatolar: foydalanuvchi JIM qolmaydi, adminga esa sabab yuboriladi."""
    exc = event.exception
    log.error("Handlerda xatolik: %r", exc, exc_info=exc)
    upd = event.update
    uid = None
    try:
        cq = getattr(upd, "callback_query", None)
        msg = getattr(upd, "message", None)
        if cq is not None:
            uid = cq.from_user.id
            await cq.answer("⚠️ Xatolik yuz berdi. Birozdan so'ng qayta urinib ko'ring.", show_alert=True)
        elif msg is not None:
            uid = msg.from_user.id if msg.from_user else None
            await msg.answer("⚠️ Xatolik yuz berdi. Birozdan so'ng qayta urinib ko'ring.")
    except Exception:
        pass
    key = f"{type(exc).__name__}:{str(exc)[:60]}"
    now = time.monotonic()
    if now - _last_err_notice.get(key, -1e9) > 900:
        _last_err_notice[key] = now
        for admin_id in OWNER_IDS:
            try:
                await bot.send_message(
                    admin_id,
                    "⚠️ <b>Bot xatosi</b>\n"
                    f"<code>{html_escape(type(exc).__name__)}: {html_escape(str(exc)[:300])}</code>\n"
                    f"Foydalanuvchi: <code>{uid}</code>",
                )
            except Exception:
                pass
    return True


# ======================================================================
# PREMIUM EMOJI — bot yuboradigan HAMMA xabarlardagi oddiy emojilarni premium emojiga almashtiradi.
#   1) /setemoji → premium emoji (yoki «oddiy emoji + premium emoji» juftligi) yuborasiz
#   2) shundan keyin bot yozadigan har bir shu emoji (kanal posti, kino xabari, menyu matnlari) premium bo'lib chiqadi
# Eslatma: Telegram faqat Premium foydalanuvchi premium emojini yubora oladi (admin Premium bo'lishi kerak) va
# botlar custom emojini ishlatishi uchun bot Fragment'da qo'shimcha username sotib olgan bo'lishi kerak.
# Agar Telegram qabul qilmasa — xabar oddiy emoji bilan ketaveradi, hech narsa buzilmaydi.
# ======================================================================
_EMOJI_MAP: "dict[str, str]" = {}
_EMOJI_ON = True
_emoji_re = None
_TAG_RE = re.compile(r"<tg-emoji\b[^>]*>.*?</tg-emoji>|<[^>]*>", re.S)
_EMOJI_CHAR = "[\U0001F000-\U0001FAFF☀-➿⬀-⯿←-⇿⌀-⏿■-◿⤀-⥿〰〽㊗㊙©®‼⁉™ℹⓂ]"
_EMOJI_SEQ = re.compile(
    "(?:" + _EMOJI_CHAR + "(?:️|‍" + _EMOJI_CHAR + "️?|[\U0001F3FB-\U0001F3FF])*)+"
)
_EMOJI_METHODS = {
    "SendMessage", "EditMessageText", "SendPhoto", "SendVideo", "SendDocument", "SendAnimation",
    "SendAudio", "EditMessageCaption", "CopyMessage",
}


def _ekey(e: str) -> str:
    return e.replace("️", "")


def _rebuild_emoji_re() -> None:
    global _emoji_re
    keys = sorted(_EMOJI_MAP, key=len, reverse=True)
    _emoji_re = re.compile("|".join(re.escape(k) + "️?" for k in keys)) if keys else None


async def load_emoji_map() -> None:
    global _EMOJI_ON
    try:
        async with aiosqlite.connect(DB_PATH) as db:
            rows = await (await db.execute("SELECT emoji, custom_id FROM emoji_map")).fetchall()
        _EMOJI_MAP.clear()
        _EMOJI_MAP.update({r[0]: r[1] for r in rows})
        _rebuild_emoji_re()
        _EMOJI_ON = (await get_setting("premium_emoji", "1")) != "0"
    except Exception:
        log.exception("Premium emoji ro'yxatini o'qib bo'lmadi")


def apply_premium_emoji(text: str) -> str:
    """HTML matndagi (teglardan tashqaridagi) oddiy emojilarni <tg-emoji> ga o'raydi."""
    if not text or not _EMOJI_ON or _emoji_re is None:
        return text

    def _sub(chunk: str) -> str:
        return _emoji_re.sub(
            lambda m: f'<tg-emoji emoji-id="{_EMOJI_MAP[_ekey(m.group(0))]}">{m.group(0)}</tg-emoji>', chunk
        )

    out, pos = [], 0
    for m in _TAG_RE.finditer(text):
        out.append(_sub(text[pos:m.start()]))
        out.append(m.group(0))
        pos = m.end()
    out.append(_sub(text[pos:]))
    return "".join(out)


class PremiumEmojiMiddleware(BaseRequestMiddleware):
    async def __call__(self, make_request, bot, method):
        if _EMOJI_ON and _emoji_re is not None and type(method).__name__ in _EMOJI_METHODS:
            pm = getattr(method, "parse_mode", None)
            if isinstance(pm, Default) or (pm is not None and str(getattr(pm, "value", pm)).upper() == "HTML"):
                upd = {}
                for f in ("text", "caption"):
                    v = getattr(method, f, None)
                    if isinstance(v, str):
                        nv = apply_premium_emoji(v)
                        if nv != v:
                            upd[f] = nv
                if upd:
                    try:
                        return await make_request(bot, method.model_copy(update=upd))
                    except TelegramBadRequest as e:
                        low = str(e).lower()
                        if "emoji" not in low and "entit" not in low:
                            raise
                        log.warning("Premium emoji qabul qilinmadi, oddiy emoji bilan yuboriladi: %s", e)
        return await make_request(bot, method)


try:
    bot.session.middleware(PremiumEmojiMiddleware())
except Exception:
    log.exception("Premium emoji middleware'ni ulab bo'lmadi (aiogram versiyasi eski bo'lishi mumkin)")


class EmojiStates(StatesGroup):
    wait = State()


EMOJI_HELP = (
    "✨ <b>Premium emoji almashtirish</b>\n\n"
    "Premium emoji(lar)ni shu yerga yuboring. Ikki usul:\n"
    "1️⃣ Faqat premium emoji — u qaysi oddiy emojiga mos bo'lsa, o'shaning o'rniga ishlatiladi.\n"
    "2️⃣ <b>Oddiy emoji + premium emoji</b> juftligi, masalan: <code>🎬 [premium]  📺 [premium]</code> — "
    "oddiy 🎬 o'rniga birinchi premium, 📺 o'rniga ikkinchisi chiqadi. Bir xabarda bir nechtasini yuborsa bo'ladi.\n\n"
    "⚠️ Premium emojini faqat Telegram Premium egasi yubora oladi.\n"
    "Ro'yxat: /emojis · yoqish/o'chirish: /emojitoggle · bekor qilish: /cancel"
)


def _u16(text: str) -> bytes:
    return text.encode("utf-16-le")


async def _answer_safe(message, text: str, **kw) -> None:
    try:
        await message.answer(text, **kw)
    except Exception:
        plain = re.sub(r"</?tg-emoji[^>]*>", "", text)
        await message.answer(plain, **kw)


@admin_router.message(Command("setemoji"))
async def cmd_setemoji(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    await state.clear()
    await state.set_state(EmojiStates.wait)
    await message.answer(EMOJI_HELP)


@admin_router.message(EmojiStates.wait)
async def emoji_wait(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    text = message.text or message.caption or ""
    ents = [e for e in (message.entities or message.caption_entities or [])
            if e.type == "custom_emoji" and e.custom_emoji_id]
    if not ents:
        await message.answer(
            "❌ Premium emoji topilmadi. Premium emojini (yoki «🎬 + premium emoji» juftligini) yuboring.\n"
            "Bekor qilish: /cancel"
        )
        return
    raw = _u16(text)
    ents.sort(key=lambda e: e.offset)
    saved: "list[tuple[str, str, str]]" = []
    prev_end = 0
    async with aiosqlite.connect(DB_PATH) as db:
        for e in ents:
            fallback = raw[e.offset * 2:(e.offset + e.length) * 2].decode("utf-16-le", "ignore")
            gap = raw[prev_end * 2:e.offset * 2].decode("utf-16-le", "ignore").strip()
            target = gap if gap and _EMOJI_SEQ.fullmatch(gap) else fallback
            prev_end = e.offset + e.length
            key = _ekey(target)
            if not key:
                continue
            await db.execute(
                "INSERT OR REPLACE INTO emoji_map (emoji, custom_id, added_at) VALUES (?, ?, ?)",
                (key, e.custom_emoji_id, now_iso()),
            )
            saved.append((key, e.custom_emoji_id, fallback))
        await db.commit()
    await load_emoji_map()
    await state.clear()
    lines = ["✅ <b>Saqlandi:</b>"] + [
        f'{html_escape(k)} → <tg-emoji emoji-id="{cid}">{html_escape(fb)}</tg-emoji>' for k, cid, fb in saved
    ]
    lines.append(f"\nEndi bot yuboradigan xabarlardagi shu emojilar premium bo'lib chiqadi" +
                 ("" if _EMOJI_ON else " (⚠️ hozir o'chiq — /emojitoggle bilan yoqing)") + ".\nYana qo'shish: /setemoji")
    await _answer_safe(message, "\n".join(lines))


async def _emoji_list_payload() -> "tuple[str, InlineKeyboardMarkup | None]":
    if not _EMOJI_MAP:
        return "📭 Hali premium emoji almashtirilmagan. Boshlash: /setemoji", None
    lines = [f"✨ <b>Premium emojilar</b> ({len(_EMOJI_MAP)} ta) — holati: " + ("🟢 yoqilgan" if _EMOJI_ON else "🔴 o'chirilgan")]
    kb = InlineKeyboardBuilder()
    for k, cid in list(_EMOJI_MAP.items())[:60]:
        lines.append(f'{html_escape(k)} → <tg-emoji emoji-id="{cid}">{html_escape(k)}</tg-emoji>')
        if len(("emoji_del:" + k).encode()) <= 64:
            kb.button(text=f"🗑 {k}", callback_data="emoji_del:" + k)
    kb.adjust(4)
    return "\n".join(lines) + "\n\nO'chirish uchun emojini bosing.", kb.as_markup()


@admin_router.message(Command("emojis"))
async def cmd_emojis(message: Message) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    text, kb = await _emoji_list_payload()
    await _answer_safe(message, text, reply_markup=kb)


@admin_router.callback_query(F.data.startswith("emoji_del:"))
async def cb_emoji_del(callback: CallbackQuery) -> None:
    if callback.from_user.id not in ADMIN_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    key = callback.data.split(":", 1)[1]
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM emoji_map WHERE emoji = ?", (key,))
        await db.commit()
    await load_emoji_map()
    await callback.answer("O'chirildi")
    text, kb = await _emoji_list_payload()
    try:
        await callback.message.edit_text(text, reply_markup=kb)
    except Exception:
        await callback.message.answer(re.sub(r"</?tg-emoji[^>]*>", "", text), reply_markup=kb)


@admin_router.message(Command("emojitoggle"))
async def cmd_emojitoggle(message: Message) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    await set_setting("premium_emoji", "0" if _EMOJI_ON else "1")
    await load_emoji_map()
    await message.answer("🟢 Premium emoji YOQILDI." if _EMOJI_ON else "🔴 Premium emoji o'chirildi (oddiy emojilar chiqadi).")


# ----------------------------------------------------------------------
# ADMIN: KINO / MULTFILM QO'SHISH / O'CHIRISH
#   /addmovie      — kino          /addmultfilm   — multfilm (bitta fayl)
# Hammasi bir xil bosqichlar: kod → nom → janr → video → narx → poster → tavsif.
# Saqlangach bot kanal(lar)ga avtomatik post joylaydi va natijani adminga yozadi.
# ----------------------------------------------------------------------
CODE_RE = re.compile(r"^[A-Za-z0-9_\-]{1,20}$")   # deep-link va qidiruv bilan mos
CODE_RULE_TEXT = (
    "❌ Kod faqat lotin harf, raqam, <code>_</code> yoki <code>-</code> bo'lishi va "
    "20 belgidan oshmasligi kerak (bo'sh joy bo'lmasin). Masalan: <code>1001</code>\n"
    "Qayta kiriting yoki <b>+</b> yozing (keyingi bo'sh kod)."
)


def msg_text(message: Message) -> str:
    """Matn yoki izohni xavfsiz o'qiydi (rasm/video yuborilsa None.strip() xatosi chiqmasin)."""
    return (message.text or message.caption or "").strip()


def parse_price(text: str) -> "int | None":
    t = (text or "").strip().replace(" ", "").replace(",", "")
    if not t.isdigit():
        return None
    return int(t)


def extract_video(message: Message) -> "tuple[str, str] | None":
    """(file_id, 'video' | 'document') — oddiy video ham, 'fayl' sifatida yuborilgan video ham qabul qilinadi."""
    if message.video:
        return message.video.file_id, "video"
    doc = message.document
    if doc and (doc.mime_type or "").lower().startswith("video/"):
        return doc.file_id, "document"
    return None


def poster_input(message: Message) -> "tuple[bool, str | None]":
    """(to'g'rimi, poster). '-' yoki 'yo'q' = postersiz. Noto'g'ri narsa kelsa — qayta so'raladi."""
    if message.photo:
        return True, "tg:" + message.photo[-1].file_id
    text = (message.text or "").strip()
    if text.startswith(("http://", "https://")):
        return True, text
    if text.lower() in ("-", "yo'q", "yoq", "yo‘q", "yo`q"):
        return True, None
    return False, None


POSTER_PROMPT = (
    "🖼 Poster <b>suratini</b> yuboring (rasm sifatida, «fayl» emas) yoki http(s) havola.\n"
    "O'tkazib yuborish uchun — deb yozing:"
)
DESC_PROMPT = (
    "📝 Qisqa <b>tavsif</b> yozing (kanal postida va kino ostida ko'rinadi).\n"
    "O'tkazib yuborish uchun — deb yozing:"
)


def ensure_cartoon_genre(genre: "str | None", category: str) -> "str | None":
    """Multfilm bo'limiga qo'shilgan narsaga «Multfilm» janri avtomatik qo'shiladi."""
    if category != "cartoon":
        return genre
    names = split_genres(genre)
    if "Multfilm" not in names:
        names.insert(0, "Multfilm")
    return ", ".join(names[:MAX_GENRES_PER_ITEM])


class AddMovieStates(StatesGroup):
    code = State()
    title = State()
    genre = State()
    video = State()
    price = State()
    poster = State()
    desc = State()


async def _begin_movie_flow(message: Message, state: FSMContext, category: str) -> None:
    await state.clear()
    await state.update_data(category=category)
    await state.set_state(AddMovieStates.code)
    what = "Multfilm" if category == "cartoon" else "Kino"
    icon = "🧸" if category == "cartoon" else "🆕"
    await message.answer(f"{icon} {what} kodini kiriting (masalan: 1001):" + await code_hint("addmovie"))


@admin_router.message(Command("addmovie"))
async def admin_addmovie_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await _begin_movie_flow(message, state, "movie")


@admin_router.message(Command("addmultfilm"))
async def admin_addmultfilm_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await _begin_movie_flow(message, state, "cartoon")


async def read_code(message: Message, kind: str) -> "str | None":
    """Kodni o'qib tekshiradi; yaroqsiz bo'lsa sababini yozib None qaytaradi."""
    text = (message.text or "").strip()
    if text != "+" and not CODE_RE.match(text):
        await message.answer(CODE_RULE_TEXT)
        return None
    return await resolve_code(message, kind)


@admin_router.message(AddMovieStates.code)
async def admin_addmovie_code(message: Message, state: FSMContext) -> None:
    code = await read_code(message, "addmovie")
    if code is None:
        return
    await state.update_data(code=code)
    await state.set_state(AddMovieStates.title)
    await message.answer("Nomini kiriting:")


@admin_router.message(AddMovieStates.title)
async def admin_addmovie_title(message: Message, state: FSMContext) -> None:
    title = (message.text or "").strip()
    if not title:
        await message.answer("❌ Nomni matn ko'rinishida yozing:")
        return
    await state.update_data(title=title[:200])
    await state.set_state(AddMovieStates.genre)
    await ask_genre(message, state, "addmovie")


@admin_router.message(AddMovieStates.genre)
async def admin_addmovie_genre(message: Message, state: FSMContext) -> None:
    await genre_text_fallback(message, state, "addmovie")


_NO_VIDEO_WORDS = ("yo'q", "yoq", "yo‘q", "yo`q", "-")


@admin_router.message(AddMovieStates.video)
async def admin_addmovie_video(message: Message, state: FSMContext) -> None:
    vid = extract_video(message)
    if vid:
        await state.update_data(file_id=vid[0], file_kind=vid[1])
    elif (message.text or "").strip().lower() in _NO_VIDEO_WORDS:
        await state.update_data(file_id=None, file_kind=None)
    else:
        await message.answer(
            "❌ Bu video emas. Video faylni yuboring (oddiy video yoki «fayl» sifatida), "
            "yoki videosiz saqlash uchun <b>yo'q</b> deb yozing:"
        )
        return
    await state.set_state(AddMovieStates.price)
    await message.answer("Narxini Stars da kiriting (bepul bo'lsa 0 deb yozing):")


@admin_router.message(AddMovieStates.price)
async def admin_addmovie_price(message: Message, state: FSMContext) -> None:
    price = parse_price(message.text or "")
    if price is None:
        await message.answer("❌ Faqat musbat raqam yozing (bepul bo'lsa 0):")
        return
    await state.update_data(price=price)
    await state.set_state(AddMovieStates.poster)
    await message.answer(POSTER_PROMPT)


@admin_router.message(AddMovieStates.poster)
async def admin_addmovie_poster(message: Message, state: FSMContext) -> None:
    ok, poster = poster_input(message)
    if not ok:
        await message.answer("❌ Rasm yoki havola yuboring (yoki o'tkazib yuborish uchun — deb yozing).\n" + POSTER_PROMPT)
        return
    await state.update_data(poster_url=poster)
    await state.set_state(AddMovieStates.desc)
    await message.answer(DESC_PROMPT)


@admin_router.message(AddMovieStates.desc)
async def admin_addmovie_desc(message: Message, state: FSMContext) -> None:
    raw = (message.text or "").strip()
    description = None if raw in ("", "-") else raw[:600]
    data = await state.get_data()
    await state.clear()
    category = data.get("category") or "movie"
    genre = ensure_cartoon_genre(data.get("genre"), category)
    poster_url = data.get("poster_url")
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            """INSERT INTO movies (code, title, genre, description, file_id, file_kind, price_stars,
                                   poster_url, added_at, views, is_vip, category)
               VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, 0, 0, ?)
               ON CONFLICT(code) DO UPDATE SET
                 title = excluded.title, genre = excluded.genre,
                 description = COALESCE(excluded.description, movies.description),
                 file_id = COALESCE(excluded.file_id, movies.file_id),
                 file_kind = CASE WHEN excluded.file_id IS NOT NULL THEN excluded.file_kind ELSE movies.file_kind END,
                 price_stars = excluded.price_stars,
                 poster_url = COALESCE(excluded.poster_url, movies.poster_url),
                 category = excluded.category""",
            (data["code"], data["title"], genre, description, data.get("file_id"), data.get("file_kind"),
             data["price"], poster_url, now_iso(), category),
        )
        await db.commit()
    label = "Multfilm" if category == "cartoon" else "Kino"
    warn = "" if data.get("file_id") else "\n⚠️ Video biriktirilmadi — keyin /addmultfilm yoki /addmovie bilan shu kodni qayta yuboring."
    await message.answer(f"✅ {label} qo'shildi: <b>{html_escape(data['title'])}</b> (kod: <code>{html_escape(data['code'])}</code>){warn}")
    await notify_genre_subscribers(genre, data["title"], "multfilm" if category == "cartoon" else "kino")
    res = await post_content_to_channel(
        "movie", data["code"], data["title"], genre, data["price"], poster_url,
        category=category, description=description, notify_user_id=message.from_user.id,
    )
    await message.answer(format_post_report(res))


@admin_router.message(Command("delmovie"))
async def admin_delmovie(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /delmovie &lt;kod&gt;")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("DELETE FROM movies WHERE code = ?", (command.args.strip(),))
        await db.commit()
    await message.answer("🗑 O'chirildi." if cur.rowcount else "Bunday kodli kino/multfilm topilmadi.")


# ----------------------------------------------------------------------
# ADMIN: SERIAL / MULTSERIAL — QISM-QISM (bo'lib-bo'lib) YUKLASH
#   /addseries — serial     /addmultserial — multserial
# Kanalga post serial TUGATILGANDA (/done) joylanadi — shunda post ichida qismlar soni
# to'g'ri bo'ladi va havola bo'sh serialga olib bormaydi.
# ----------------------------------------------------------------------
class AddSeriesStates(StatesGroup):
    code = State()
    title = State()
    genre = State()
    price = State()
    poster = State()
    desc = State()
    episodes = State()   # shu holatda: video kelsa -> keyingi qism, "/done" -> tugatish


async def _series_episode_count(code: str) -> int:
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT COUNT(*) FROM series_episodes WHERE series_code = ?", (code,)
        )).fetchone()
    return row[0] if row else 0


async def _series_last_episode(code: str) -> int:
    """Eng katta qism raqami (qism o'chirilgan bo'lsa ham raqamlar to'qnashmasin)."""
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT COALESCE(MAX(episode_number), 0) FROM series_episodes WHERE series_code = ?", (code,)
        )).fetchone()
    return row[0] if row else 0


async def _begin_series_flow(message: Message, state: FSMContext, category: str) -> None:
    await state.clear()
    await state.update_data(category=category, is_new=True, added=[])
    await state.set_state(AddSeriesStates.code)
    what = "Multserial" if category == "cartoon" else "Serial"
    icon = "🧸" if category == "cartoon" else "📺"
    await message.answer(f"{icon} Yangi {what.lower()} kodini kiriting (masalan: 2001):" + await code_hint("addseries"))


@admin_router.message(Command("addseries"))
async def admin_addseries_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await _begin_series_flow(message, state, "series")


@admin_router.message(Command("addmultserial"))
async def admin_addmultserial_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await _begin_series_flow(message, state, "cartoon")


@admin_router.message(AddSeriesStates.code)
async def admin_addseries_code(message: Message, state: FSMContext) -> None:
    code = await read_code(message, "addseries")
    if code is None:
        return
    await state.update_data(code=code)
    await state.set_state(AddSeriesStates.title)
    await message.answer("Nomini kiriting:")


@admin_router.message(AddSeriesStates.title)
async def admin_addseries_title(message: Message, state: FSMContext) -> None:
    title = (message.text or "").strip()
    if not title:
        await message.answer("❌ Nomni matn ko'rinishida yozing:")
        return
    await state.update_data(title=title[:200])
    await state.set_state(AddSeriesStates.genre)
    await ask_genre(message, state, "addseries")


@admin_router.message(AddSeriesStates.genre)
async def admin_addseries_genre(message: Message, state: FSMContext) -> None:
    await genre_text_fallback(message, state, "addseries")


@admin_router.message(AddSeriesStates.price)
async def admin_addseries_price(message: Message, state: FSMContext) -> None:
    price = parse_price(message.text or "")
    if price is None:
        await message.answer("❌ Faqat musbat raqam yozing (bepul bo'lsa 0):")
        return
    await state.update_data(price=price)
    await state.set_state(AddSeriesStates.poster)
    await message.answer(POSTER_PROMPT)


@admin_router.message(AddSeriesStates.poster)
async def admin_addseries_poster(message: Message, state: FSMContext) -> None:
    ok, poster = poster_input(message)
    if not ok:
        await message.answer("❌ Rasm yoki havola yuboring (yoki o'tkazib yuborish uchun — deb yozing).\n" + POSTER_PROMPT)
        return
    await state.update_data(poster_url=poster)
    await state.set_state(AddSeriesStates.desc)
    await message.answer(DESC_PROMPT)


@admin_router.message(AddSeriesStates.desc)
async def admin_addseries_desc(message: Message, state: FSMContext) -> None:
    raw = (message.text or "").strip()
    description = None if raw in ("", "-") else raw[:600]
    data = await state.get_data()
    category = data.get("category") or "series"
    genre = ensure_cartoon_genre(data.get("genre"), category)
    await state.update_data(description=description, genre=genre)
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            """INSERT INTO series (code, title, genre, description, price_stars, poster_url, added_at, is_vip, category)
               VALUES (?, ?, ?, ?, ?, ?, ?, 0, ?)
               ON CONFLICT(code) DO UPDATE SET
                 title = excluded.title, genre = excluded.genre,
                 description = COALESCE(excluded.description, series.description),
                 price_stars = excluded.price_stars,
                 poster_url = COALESCE(excluded.poster_url, series.poster_url),
                 category = excluded.category""",
            (data["code"], data["title"], genre, description, data["price"],
             data.get("poster_url"), now_iso(), category),
        )
        await db.commit()
    await state.set_state(AddSeriesStates.episodes)
    label = "Multserial" if category == "cartoon" else "Serial"
    await message.answer(
        f"✅ {label} yaratildi: <b>{html_escape(data['title'])}</b> (kod: <code>{html_escape(data['code'])}</code>)\n\n"
        "🎬 Endi qismlarni birma-bir yuboring (video yoki «fayl» sifatida) — "
        "har biri navbatdagi qism bo'lib qo'shiladi.\n"
        "Tugatgach <b>/done</b> deb yozing — shunda kanalga post joylanadi."
    )
    await notify_genre_subscribers(genre, data["title"], "multserial" if category == "cartoon" else "serial")


async def _start_add_episodes(message: Message, state: FSMContext, code: str) -> bool:
    """Mavjud serialga qism qo'shish rejimini yoqadi (buyruq ham, tugma ham shuni ishlatadi)."""
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute("SELECT title FROM series WHERE code = ?", (code,))).fetchone()
    if not row:
        await message.answer("Bunday kodli serial topilmadi. Avval /addseries yoki /addmultserial bilan yarating.")
        return False
    await state.clear()
    await state.update_data(code=code, is_new=False, added=[])
    await state.set_state(AddSeriesStates.episodes)
    count = await _series_episode_count(code)
    await message.answer(
        f"🎬 <b>{html_escape(row[0])}</b> (<code>{html_escape(code)}</code>) uchun yangi qism(lar)ni yuboring "
        f"(hozircha {count} ta qism bor).\nTugatgach <b>/done</b> deb yozing."
    )
    return True


@admin_router.message(Command("addepisode"))
async def admin_addepisode_start(message: Message, state: FSMContext, command: CommandObject) -> None:
    """Mavjud serialga keyinroq (istalgan vaqtda) yangi qismlar qo'shish uchun."""
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /addepisode &lt;serial_kodi&gt;\nYoki /admin → 🎬 Kontent → «📼 Qism qo'shish» (tugmalar bilan).")
        return
    await _start_add_episodes(message, state, command.args.strip())


@admin_router.message(AddSeriesStates.episodes, Command("done"))
async def admin_addseries_done(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    code = data.get("code", "")
    added = data.get("added") or []
    await state.clear()
    total = await _series_episode_count(code)
    await message.answer(f"🎉 Tayyor! <b>{html_escape(code)}</b> da jami {total} ta qism bor.")
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        s = await (await db.execute("SELECT * FROM series WHERE code = ?", (code,))).fetchone()
    if not s:
        return
    if data.get("is_new"):
        if total == 0:
            await message.answer("ℹ️ Hali birorta qism yo'q — kanalga post joylanmadi. Qism qo'shgach /repost " + html_escape(code))
            return
        res = await post_content_to_channel(
            "series", code, s["title"], s["genre"], s["price_stars"], s["poster_url"],
            category=s["category"] or "series", description=s["description"], ep_count=total,
            notify_user_id=message.from_user.id,
        )
    elif added:
        res = await post_content_to_channel(
            "series", code, s["title"], s["genre"], s["price_stars"], s["poster_url"],
            category=s["category"] or "series", description=s["description"], ep_count=total,
            new_eps=(min(added), max(added)), notify_user_id=message.from_user.id,
        )
    else:
        return
    await message.answer(format_post_report(res))


@admin_router.message(AddSeriesStates.episodes)
async def admin_addseries_episode_video(message: Message, state: FSMContext) -> None:
    vid = extract_video(message)
    if not vid:
        await message.answer("Iltimos video fayl yuboring, yoki tugatish uchun /done deb yozing.")
        return
    data = await state.get_data()
    code = data["code"]
    next_num = await _series_last_episode(code) + 1
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO series_episodes (series_code, episode_number, file_id, file_kind, added_at) VALUES (?, ?, ?, ?, ?)",
            (code, next_num, vid[0], vid[1], now_iso()),
        )
        await db.commit()
        db.row_factory = aiosqlite.Row
        s = await (await db.execute("SELECT title FROM series WHERE code = ?", (code,))).fetchone()
    added = list(data.get("added") or []) + [next_num]
    await state.update_data(added=added)
    if next_num > 1 and s:  # 1-qism uchun emas (hali kuzatuvchi yo'q) — 2-qismdan boshlab bildirishnoma
        await notify_series_followers(code, s["title"], next_num)
    await message.answer(f"✅ {next_num}-qism qo'shildi. Davom eting yoki /done deb yozing.")


@admin_router.message(Command("setinfo"))
async def admin_setinfo(message: Message, command: CommandObject) -> None:
    """/setinfo <kod> til | davlat | sifat | yil — post va kino kartochkasidagi ma'lumotlar."""
    if message.from_user.id not in STAFF_IDS:
        return
    parts = (command.args or "").split(maxsplit=1)
    if len(parts) < 2:
        await message.answer(
            "Foydalanish: <code>/setinfo &lt;kod&gt; til | davlat | sifat | yil</code>\n"
            "Masalan: <code>/setinfo 1001 O'zbek tilida | Uzb | 1080p | 2026</code>\n"
            "Biror qismni o'zgartirmaslik uchun <b>-</b> yozing: <code>/setinfo 1001 - | Koreya | - | 2025</code>"
        )
        return
    code, rest = parts[0], parts[1]
    vals = [v.strip() for v in re.split(r"[|;]", rest)]
    sets: dict = {}
    for col, v in zip(("language", "country", "quality", "year"), vals):
        if not v or v == "-":
            continue
        if col == "year":
            m = re.search(r"\d{4}", v)
            if m:
                sets[col] = int(m.group())
        else:
            sets[col] = v[:40]
    if not sets:
        await message.answer("❌ Hech narsa o'zgartirilmadi — qiymatlarni tekshiring.")
        return
    updated = []
    async with aiosqlite.connect(DB_PATH) as db:
        for tbl in ("movies", "series"):
            cur = await db.execute(
                f"UPDATE {tbl} SET " + ", ".join(f"{c} = ?" for c in sets) + " WHERE code = ?",
                list(sets.values()) + [code],
            )
            if cur.rowcount:
                updated.append(tbl)
        await db.commit()
    if not updated:
        await message.answer("😔 Bunday kodli kino/serial topilmadi.")
        return
    await message.answer(f"✅ <code>{html_escape(code)}</code> yangilandi. Postni yangilash uchun: /repost {html_escape(code)}")


@admin_router.message(Command("repost"))
async def admin_repost(message: Message, command: CommandObject) -> None:
    """Kino/serial postini kanal(lar)ga qayta joylash: /repost &lt;kod&gt;"""
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /repost &lt;kod&gt;\nYoki /admin → 🎬 Kontent → «📣 Qayta joylash».")
        return
    await message.answer(await repost_by_code(command.args.strip(), message.from_user.id))


async def repost_by_code(code: str, notify_user_id: "int | None" = None, only: "str | None" = None) -> str:
    """Kodi bo'yicha kino yoki serialni topib, kanalga qayta joylaydi. Tayyor xabar matnini qaytaradi."""
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        m = None if only == "series" else await (await db.execute("SELECT * FROM movies WHERE code = ?", (code,))).fetchone()
        s = None if (m or only == "movie") else await (await db.execute("SELECT * FROM series WHERE code = ?", (code,))).fetchone()
    if m:
        res = await post_content_to_channel(
            "movie", m["code"], m["title"], m["genre"], m["price_stars"], m["poster_url"],
            category=m["category"] or "movie", description=m["description"], notify_user_id=notify_user_id,
        )
        return format_post_report(res)
    if s:
        total = await _series_episode_count(code)
        res = await post_content_to_channel(
            "series", s["code"], s["title"], s["genre"], s["price_stars"], s["poster_url"],
            category=s["category"] or "series", description=s["description"], ep_count=total,
            notify_user_id=notify_user_id,
        )
        return format_post_report(res)
    return "😔 Bunday kodli kino/serial topilmadi."


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (ADMIN) — /editmovie: video qayta yuklamasdan
# mavjud kino nomi/janri/narxini tahrirlash
# ----------------------------------------------------------------------
class EditMovieStates(StatesGroup):
    title = State()
    genre = State()
    price = State()


@admin_router.message(Command("editmovie"))
async def admin_editmovie_start(message: Message, state: FSMContext, command: CommandObject) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /editmovie &lt;kod&gt;")
        return
    code = command.args.strip()
    async with aiosqlite.connect(DB_PATH) as db:
        exists = await (await db.execute("SELECT 1 FROM movies WHERE code = ?", (code,))).fetchone()
    if not exists:
        await message.answer("Bunday kodli kino topilmadi.")
        return
    await state.update_data(code=code)
    await state.set_state(EditMovieStates.title)
    await message.answer("Yangi nomni yuboring (o'zgartirmaslik uchun — deb yozing):")


@admin_router.message(EditMovieStates.title)
async def admin_editmovie_title(message: Message, state: FSMContext) -> None:
    t = msg_text(message)
    if t and t != "-":
        await state.update_data(title=t[:200])
    await state.set_state(EditMovieStates.genre)
    await ask_genre(message, state, "editmovie", allow_keep=True)


@admin_router.message(EditMovieStates.genre)
async def admin_editmovie_genre(message: Message, state: FSMContext) -> None:
    await genre_text_fallback(message, state, "editmovie", allow_keep=True)


@admin_router.message(EditMovieStates.price)
async def admin_editmovie_price(message: Message, state: FSMContext) -> None:
    t = msg_text(message)
    if t and t != "-":
        p = parse_price(t)
        if p is None:
            await message.answer("❌ Faqat raqam yozing (o'zgartirmaslik uchun — deb yozing):")
            return
        await state.update_data(price_stars=p)
    data = await state.get_data()
    await state.clear()
    code = data.pop("code")
    if not data:
        await message.answer("Hech narsa o'zgarmadi.")
        return
    set_parts, params = [], []
    for col in ("title", "genre", "price_stars"):
        if col in data:
            set_parts.append(f"{col} = ?")
            params.append(data[col])
    params.append(code)
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(f"UPDATE movies SET {', '.join(set_parts)} WHERE code = ?", params)
        await db.commit()
    await message.answer(f"✅ {code} yangilandi.")


# ----------------------------------------------------------------------
# ADMIN: "DO'KON — MAXSUS TAKLIFLAR" (narxni o'zingiz belgilaysiz;
# "Sotib olish" tugmasi mini-appda avtomatik SELLER_CONTACT_USERNAME'ga
# olib boradi, siz bilan to'g'ridan-to'g'ri kelishib to'lov qilinadi)
# ----------------------------------------------------------------------
class AddProductStates(StatesGroup):
    title = State()
    description = State()
    price = State()
    emoji = State()


@admin_router.message(Command("addproduct"))
async def admin_addproduct_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    await state.set_state(AddProductStates.title)
    await message.answer("🛍 Yangi taklif nomini kiriting (masalan: Shaxsiy VIP dizayn):")


@admin_router.message(AddProductStates.title)
async def admin_addproduct_title(message: Message, state: FSMContext) -> None:
    await state.update_data(title=message.text.strip())
    await state.set_state(AddProductStates.description)
    await message.answer("Qisqacha tavsif yozing (o'tkazib yuborish uchun — deb yozing):")


@admin_router.message(AddProductStates.description)
async def admin_addproduct_description(message: Message, state: FSMContext) -> None:
    text = message.text.strip()
    await state.update_data(description=None if text == "-" else text)
    await state.set_state(AddProductStates.price)
    await message.answer("Narxini Stars da kiriting (siz o'zingiz belgilaysiz, masalan: 250):")


@admin_router.message(AddProductStates.price)
async def admin_addproduct_price(message: Message, state: FSMContext) -> None:
    try:
        price = int(message.text.strip())
    except ValueError:
        price = 0
    await state.update_data(price=price)
    await state.set_state(AddProductStates.emoji)
    await message.answer("Bitta emoji tanlang (masalan: 🎁, 🖼, ⚡, 📣):")


@admin_router.message(AddProductStates.emoji)
async def admin_addproduct_emoji(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    emoji = message.text.strip()[:4] or "🛍"
    await state.clear()
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO shop_products (title, description, price_stars, emoji, added_at) VALUES (?, ?, ?, ?, ?)",
            (data["title"], data.get("description"), data["price"], emoji, now_iso()),
        )
        await db.commit()
    await message.answer(
        f"✅ Yangi taklif qo'shildi: {emoji} <b>{data['title']}</b> — {data['price']} ⭐\n"
        "Mini-app 'Do'kon' bo'limida darhol ko'rinadi."
    )


@admin_router.message(Command("products"))
async def admin_products_list(message: Message) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT * FROM shop_products WHERE active = 1 ORDER BY id DESC"
        )).fetchall()
    if not rows:
        await message.answer("Hozircha takliflar yo'q. /addproduct bilan qo'shing.")
        return
    lines = ["🛍 <b>Faol takliflar:</b>"]
    for r in rows:
        lines.append(f"#{r['id']} {r['emoji']} {r['title']} — {r['price_stars']} ⭐")
    lines.append("\nO'chirish: /delproduct &lt;id&gt;")
    await message.answer("\n".join(lines))


@admin_router.message(Command("delproduct"))
async def admin_delproduct(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    if not command.args or not command.args.strip().isdigit():
        await message.answer("Foydalanish: /delproduct &lt;id&gt;")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE shop_products SET active = 0 WHERE id = ?", (int(command.args.strip()),))
        await db.commit()
    await message.answer("🗑 Taklif do'kondan olib tashlandi.")


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (ADMIN) 1/2 — /searchuser: foydalanuvchini ism yoki
# username bo'yicha qidirish (ID bilmasangiz ham topa olasiz)
# ----------------------------------------------------------------------
@admin_router.message(Command("searchuser"))
async def admin_searchuser(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /searchuser &lt;ism yoki username&gt;")
        return
    q = f"%{command.args.strip()}%"
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT user_id, full_name, username, vip_until FROM users "
            "WHERE full_name LIKE ? OR username LIKE ? LIMIT 15",
            (q, q),
        )).fetchall()
    if not rows:
        await message.answer("Hech kim topilmadi.")
        return
    lines = ["🔎 <b>Topilgan foydalanuvchilar:</b>"]
    for r in rows:
        vip = f", VIP: {r['vip_until']}" if r["vip_until"] else ""
        lines.append(f"🆔 {r['user_id']} — {r['full_name']} (@{r['username'] or '—'}){vip}")
    lines.append("\nBatafsil: /user_info &lt;id&gt;")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (ADMIN) 2/2 — /broadcastvip: xabarni faqat VIP
# a'zolarga yuborish (barchaga emas)
# ----------------------------------------------------------------------
class BroadcastVipStates(StatesGroup):
    content = State()


@admin_router.message(Command("broadcastvip"))
async def admin_broadcastvip_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    await state.set_state(BroadcastVipStates.content)
    await message.answer("💎 Faqat VIP a'zolarga yuboriladigan xabarni yuboring:")


@admin_router.message(BroadcastVipStates.content)
async def admin_broadcastvip_send(message: Message, state: FSMContext) -> None:
    await state.clear()
    text = message.html_text or message.caption or ""
    photo = message.photo[-1].file_id if message.photo else None
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute(
            "SELECT user_id FROM users WHERE vip_until IS NOT NULL AND vip_until > ?", (now_iso(),)
        )).fetchall()
    sent, failed = 0, 0
    for (uid,) in rows:
        try:
            if photo:
                await bot.send_photo(uid, photo, caption=text)
            else:
                await bot.send_message(uid, text)
            sent += 1
        except Exception:
            failed += 1
        await asyncio.sleep(0.05)
    await message.answer(f"✅ VIP a'zolarga yuborildi: {sent} ta\n⚠️ Yetib bormadi: {failed} ta")


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (USER) 1/2 — /leaderboard: eng ko'p do'st taklif
# qilganlar reytingi (bot ichida, mini-app'dagi bilan bir xil ma'lumot)
# ----------------------------------------------------------------------
@user_router.message(Command("leaderboard"))
async def cmd_leaderboard(message: Message) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT full_name, username, referral_count FROM users "
            "WHERE referral_count > 0 ORDER BY referral_count DESC LIMIT 10"
        )).fetchall()
    if not rows:
        await message.answer("Hali hech kim do'st taklif qilmagan. Birinchi bo'ling! /referral")
        return
    medals = ["🥇", "🥈", "🥉"]
    lines = ["🏆 <b>Referral liderbordi:</b>"]
    for i, r in enumerate(rows):
        rank = medals[i] if i < 3 else f"{i + 1}."
        lines.append(f"{rank} {r['full_name']} (@{r['username'] or '—'}) — {r['referral_count']} ta")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (USER) 2/2 — /feedback: foydalanuvchi fikr-mulohaza
# yoki xatolik haqida to'g'ridan-to'g'ri adminlarga yozib yuboradi
# ----------------------------------------------------------------------
class FeedbackStates(StatesGroup):
    text = State()


@user_router.message(Command("feedback"))
async def cmd_feedback_start(message: Message, state: FSMContext) -> None:
    await state.set_state(FeedbackStates.text)
    await message.answer("✍️ Fikr-mulohaza yoki xatolik haqida yozing (admin ko'radi):")


@user_router.message(FeedbackStates.text)
async def cmd_feedback_send(message: Message, state: FSMContext) -> None:
    await state.clear()
    text = message.text.strip()
    uid = message.from_user.id
    uname = f"@{message.from_user.username}" if message.from_user.username else message.from_user.full_name
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(admin_id, f"📩 <b>Fikr-mulohaza</b>\n👤 {uname} (ID: {uid})\n\n{text}")
        except Exception:
            pass
    await message.answer("✅ Rahmat! Fikringiz adminlarga yetkazildi.")


# ----------------------------------------------------------------------
# PROMO-KOD TIZIMI — admin yaratadi, foydalanuvchi qo'llaydi (bepul VIP kun)
# ----------------------------------------------------------------------
@admin_router.message(Command("addpromo"))
async def admin_addpromo(message: Message, command: CommandObject) -> None:
    """Foydalanish: /addpromo &lt;KOD&gt; &lt;vip_kun&gt; &lt;max_ishlatish&gt; [amal_kun]"""
    if message.from_user.id not in ADMIN_IDS:
        return
    parts = (command.args or "").split()
    if len(parts) < 3:
        await message.answer("Foydalanish: /addpromo &lt;KOD&gt; &lt;vip_kun&gt; &lt;max_ishlatish&gt; [amal_kun]")
        return
    code = parts[0].upper()
    try:
        vip_days = int(parts[1])
        max_uses = int(parts[2])
        expires_at = (utcnow() + timedelta(days=int(parts[3]))).isoformat() if len(parts) > 3 else None
    except ValueError:
        await message.answer("Raqamlar noto'g'ri kiritildi.")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT OR REPLACE INTO promo_codes (code, vip_days, max_uses, used_count, expires_at, created_at) "
            "VALUES (?, ?, ?, 0, ?, ?)",
            (code, vip_days, max_uses, expires_at, now_iso()),
        )
        await db.commit()
    await message.answer(f"✅ Promo-kod yaratildi: <b>{code}</b> — {vip_days} kun VIP, {max_uses} marta ishlatiladi.")


@user_router.message(Command("promo"))
async def cmd_promo(message: Message, command: CommandObject) -> None:
    if not command.args:
        await message.answer("Foydalanish: /promo &lt;KOD&gt;")
        return
    code = command.args.strip().upper()
    uid = message.from_user.id
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        promo = await (await db.execute("SELECT * FROM promo_codes WHERE code = ?", (code,))).fetchone()
        if not promo:
            await message.answer("❌ Bunday promo-kod topilmadi.")
            return
        if promo["expires_at"] and promo["expires_at"] < now_iso():
            await message.answer("⏰ Bu promo-kodning muddati tugagan.")
            return
        if promo["used_count"] >= promo["max_uses"]:
            await message.answer("😔 Bu promo-kod limitiga yetgan.")
            return
        already = await (await db.execute(
            "SELECT 1 FROM promo_redemptions WHERE code = ? AND user_id = ?", (code, uid)
        )).fetchone()
        if already:
            await message.answer("Siz bu promo-kodni allaqachon ishlatgansiz.")
            return
        await db.execute("UPDATE promo_codes SET used_count = used_count + 1 WHERE code = ?", (code,))
        await db.execute(
            "INSERT INTO promo_redemptions (code, user_id, redeemed_at) VALUES (?, ?, ?)",
            (code, uid, now_iso()),
        )
        await db.commit()
    await extend_vip(uid, promo["vip_days"])
    await message.answer(f"🎉 Promo-kod qabul qilindi! Sizga {promo['vip_days']} kunlik VIP berildi.")


# ----------------------------------------------------------------------
# "TEZ ORADA" (COMING SOON) — kuting ro'yxati, chiqqanda avtomatik xabar
# ----------------------------------------------------------------------
class AddComingSoonStates(StatesGroup):
    title = State()
    genre = State()
    date = State()
    poster = State()


@admin_router.message(Command("addcomingsoon"))
async def admin_addcomingsoon_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await state.set_state(AddComingSoonStates.title)
    await message.answer("🔜 Tez orada chiqadigan kino/serial nomini kiriting:")


@admin_router.message(AddComingSoonStates.title)
async def admin_addcomingsoon_title(message: Message, state: FSMContext) -> None:
    await state.update_data(title=message.text.strip())
    await state.set_state(AddComingSoonStates.genre)
    await ask_genre(message, state, "comingsoon")


@admin_router.message(AddComingSoonStates.genre)
async def admin_addcomingsoon_genre(message: Message, state: FSMContext) -> None:
    await genre_text_fallback(message, state, "comingsoon")


@admin_router.message(AddComingSoonStates.date)
async def admin_addcomingsoon_date(message: Message, state: FSMContext) -> None:
    text = message.text.strip()
    await state.update_data(expected_date=None if text == "-" else text)
    await state.set_state(AddComingSoonStates.poster)
    await message.answer("🖼 Poster <b>suratni</b> yuboring, yoki — deb yozing:")


@admin_router.message(AddComingSoonStates.poster)
async def admin_addcomingsoon_poster(message: Message, state: FSMContext) -> None:
    poster_url = extract_poster(message)
    data = await state.get_data()
    await state.clear()
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO coming_soon (title, genre, poster_url, expected_date, created_at) VALUES (?, ?, ?, ?, ?)",
            (data["title"], data["genre"], poster_url, data.get("expected_date"), now_iso()),
        )
        await db.commit()
    await message.answer(f"✅ '{data['title']}' \"Tez orada\" bo'limiga qo'shildi.")


@admin_router.message(Command("releasecoming"))
async def admin_releasecoming(message: Message, command: CommandObject) -> None:
    """Foydalanish: /releasecoming &lt;coming_soon_id&gt; &lt;kino_kodi&gt; — kuting
    ro'yxatidagilarga avtomatik xabar beradi va kino chiqqanini belgilaydi."""
    if message.from_user.id not in STAFF_IDS:
        return
    parts = (command.args or "").split()
    if len(parts) < 2:
        await message.answer("Foydalanish: /releasecoming &lt;id&gt; &lt;kino_kodi&gt;")
        return
    cs_id, movie_code = parts[0], parts[1]
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        cs = await (await db.execute("SELECT * FROM coming_soon WHERE id = ?", (cs_id,))).fetchone()
        if not cs:
            await message.answer("Topilmadi.")
            return
        await db.execute("UPDATE coming_soon SET released_code = ? WHERE id = ?", (movie_code, cs_id))
        waiters = await (await db.execute(
            "SELECT user_id FROM coming_soon_waitlist WHERE coming_soon_id = ?", (cs_id,)
        )).fetchall()
        await db.commit()
    for (uid,) in waiters:
        try:
            await bot.send_message(uid, f"🎉 Kutgan kinongiz chiqdi: <b>{cs['title']}</b>! Kodi: {movie_code}")
        except Exception:
            pass
        await asyncio.sleep(0.05)
    await message.answer(f"✅ {len(waiters)} kishiga xabar yuborildi.")


# ----------------------------------------------------------------------
# ADMIN: kam ko'rilgan kontentni tozalash tavsiyasi
# ----------------------------------------------------------------------
@admin_router.message(Command("delcomment"))
async def admin_delcomment(message: Message, command: CommandObject) -> None:
    """Izohlarni boshqarish — moderator ham foydalana oladi."""
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args or not command.args.strip().isdigit():
        await message.answer("Foydalanish: /delcomment &lt;id&gt;")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM movie_comments WHERE id = ?", (int(command.args.strip()),))
        await db.commit()
    await message.answer("🗑 Izoh o'chirildi.")


@admin_router.message(Command("lowviews"))
async def admin_lowviews(message: Message) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT code, title, views FROM movies ORDER BY views ASC LIMIT 15"
        )).fetchall()
    if not rows:
        await message.answer("Kinolar yo'q.")
        return
    lines = ["🧹 <b>Eng kam ko'rilgan 15 ta kino</b> (tozalash uchun ko'rib chiqing):"]
    for r in rows:
        lines.append(f"#{r['code']} {r['title']} — {r['views']} ko'rish")
    lines.append("\nO'chirish: /delmovie &lt;kod&gt;")
    await message.answer("\n".join(lines))


# ----------------------------------------------------------------------
# YANGI BOT FUNKSIYASI (USER) — /genres: janrlarga tez obuna bo'lish
# (mavjud genre_subscriptions jadvaliga bot ichidan ham kirish imkoni)
# ----------------------------------------------------------------------
@user_router.message(Command("genres"))
async def cmd_genres(message: Message) -> None:
    uid = message.from_user.id
    async with aiosqlite.connect(DB_PATH) as db:
        sub_rows = await (await db.execute(
            "SELECT genre FROM genre_subscriptions WHERE user_id = ?", (uid,)
        )).fetchall()
    subscribed = {r[0] for r in sub_rows}
    genres = list(GENRE_NAMES)
    kb = InlineKeyboardBuilder()
    for g in genres:
        mark = "🔔" if g in subscribed else "🔕"
        kb.button(text=f"{mark} {g}", callback_data=f"gsub:{g}")
    kb.adjust(2)
    await message.answer(
        "🔔 Yoqtirgan janrlaringizga obuna bo'ling — yangi kino/serial qo'shilganda xabar beramiz:",
        reply_markup=kb.as_markup(),
    )


@user_router.callback_query(F.data.startswith("gsub:"))
async def cb_toggle_genre_sub(callback: CallbackQuery) -> None:
    genre = callback.data.split(":", 1)[1]
    uid = callback.from_user.id
    async with aiosqlite.connect(DB_PATH) as db:
        exists = await (await db.execute(
            "SELECT 1 FROM genre_subscriptions WHERE user_id = ? AND genre = ?", (uid, genre)
        )).fetchone()
        if exists:
            await db.execute(
                "DELETE FROM genre_subscriptions WHERE user_id = ? AND genre = ?", (uid, genre)
            )
            subscribed_now = False
        else:
            await db.execute(
                "INSERT INTO genre_subscriptions (user_id, genre) VALUES (?, ?)", (uid, genre)
            )
            subscribed_now = True
        await db.commit()
    await callback.answer("🔔 Obuna bo'lindi" if subscribed_now else "🔕 Obuna bekor qilindi")
    mark = "🔔" if subscribed_now else "🔕"
    for row in callback.message.reply_markup.inline_keyboard:
        for btn in row:
            if btn.callback_data == callback.data:
                btn.text = f"{mark} {genre}"
    await callback.message.edit_reply_markup(reply_markup=callback.message.reply_markup)


@admin_router.message(Command("delseries"))
async def admin_delseries(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /delseries &lt;kod&gt;")
        return
    code = command.args.strip()
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM series WHERE code = ?", (code,))
        await db.execute("DELETE FROM series_episodes WHERE series_code = ?", (code,))
        await db.commit()
    await message.answer("🗑 Serial va barcha qismlari o'chirildi.")


# ========================================================================
# ADMIN PANEL — /admin: barcha admin funksiyalarga tugmalar orqali kirish
# ========================================================================

def _admin_main_menu_kb(uid: int = 0) -> "InlineKeyboardBuilder":
    """Tugmalar foydalanuvchi darajasiga qarab chiqadi: kontent admin / to'liq admin / ega."""
    kb = InlineKeyboardBuilder()
    full = uid in ADMIN_IDS
    owner = uid in OWNER_IDS
    kb.button(text="🎬 Kontent (kino, serial, multfilm)", callback_data="admin_menu:content")
    if full:
        kb.button(text="📡 Post kanallari", callback_data="adm2:channels")
        kb.button(text="📊 Statistika", callback_data="admin_act:stats")
        kb.button(text="👥 Foydalanuvchilar", callback_data="admin_menu:users")
        kb.button(text="📢 Xabar yuborish", callback_data="admin_menu:broadcast")
        kb.button(text="🛍 Do'kon", callback_data="admin_menu:shop")
        kb.button(text="✨ Premium emoji", callback_data="admin_act:emoji_start")
    kb.button(text="🎟 Promo & Tez orada", callback_data="admin_menu:promo")
    kb.button(text="💬 Izohlar", callback_data="admin_act:comments_info")
    kb.button(text="📢 Majburiy obuna", callback_data="admin_menu:fsub")
    if owner:
        kb.button(text="👑 Jamoa (adminlar)", callback_data="adm2:team")
        kb.button(text="🩺 Tizim holati", callback_data="adm2:status")
        kb.button(text="💾 Zaxira / tiklash", callback_data="admin_menu:backup")
    kb.button(text="📖 Buyruqlar ro'yxati", callback_data="admin_act:adminhelp")
    kb.adjust(1, 2)
    return kb


def _admin_fsub_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Kanal qo'shish", callback_data="admin_act:addfsub")
    kb.button(text="📃 Kanallar ro'yxati / o'chirish", callback_data="admin_act:fsublist")
    kb.button(text="👁 Foydalanuvchi ko'radigan xabar", callback_data="admin_act:fsubtest")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 1, 1, 1)
    return kb


def _admin_content_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="➕ Kino qo'shish", callback_data="admin_act:addmovie")
    kb.button(text="🧸 Multfilm qo'shish", callback_data="adm2:addcartoon")
    kb.button(text="➕ Serial qo'shish", callback_data="admin_act:addseries")
    kb.button(text="🧸 Multserial qo'shish", callback_data="adm2:addcartoonseries")
    kb.button(text="📼 Qism qo'shish", callback_data="adm2:pick:ep:0")
    kb.button(text="✏️ Kino/multfilm tahrirlash", callback_data="adm2:pick:edit:0")
    kb.button(text="🗑 Kino/multfilm o'chirish", callback_data="adm2:pick:delm:0")
    kb.button(text="🗑 Serial o'chirish", callback_data="adm2:pick:dels:0")
    kb.button(text="📣 Kino postini qayta joylash", callback_data="adm2:pick:repm:0")
    kb.button(text="📣 Serial postini qayta joylash", callback_data="adm2:pick:reps:0")
    kb.button(text="🧹 Kam ko'rilganlar", callback_data="admin_act:lowviews")
    kb.button(text="📝 Kino so'rovlari", callback_data="admin_act:requests")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(2, 2, 1, 1, 2, 2, 2, 1)
    return kb


def _admin_users_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="🔎 Qidirish", callback_data="admin_act:searchuser_info")
    kb.button(text="ℹ️ Foydalanuvchi ma'lumoti", callback_data="admin_act:userinfo_info")
    kb.button(text="🚫 Bloklash", callback_data="admin_act:ban_info")
    kb.button(text="✅ Blokdan chiqarish", callback_data="admin_act:unban_info")
    kb.button(text="💎 VIP/Premium berish", callback_data="admin_act:givevip_info")
    kb.button(text="⛔ VIP/Premium olib tashlash", callback_data="admin_act:removevip_info")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 2, 2, 1)
    return kb


def _admin_broadcast_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="📢 Barchaga xabar", callback_data="admin_act:broadcast")
    kb.button(text="💎 Faqat VIP'larga", callback_data="admin_act:broadcastvip")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 1, 1)
    return kb


def _admin_shop_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="📃 Mahsulotlar ro'yxati", callback_data="admin_act:products")
    kb.button(text="➕ Mahsulot qo'shish", callback_data="admin_act:addproduct")
    kb.button(text="🗑 Mahsulot o'chirish", callback_data="admin_act:delproduct_info")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 1, 1, 1)
    return kb


def _admin_promo_menu_kb() -> "InlineKeyboardBuilder":
    kb = InlineKeyboardBuilder()
    kb.button(text="🎟 Promo-kod yaratish", callback_data="admin_act:addpromo_info")
    kb.button(text="🔜 \"Tez orada\" qo'shish", callback_data="admin_act:addcomingsoon")
    kb.button(text="🚀 Chiqarilganini belgilash", callback_data="admin_act:releasecoming_info")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(1, 1, 1, 1)
    return kb


@admin_router.message(Command("admin"))
async def admin_panel(message: Message) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await message.answer("🛠 <b>Admin panel</b>\nKerakli bo'limni tanlang:", reply_markup=_admin_main_menu_kb(message.from_user.id).as_markup())


@admin_router.callback_query(F.data.startswith("admin_menu:"))
async def cb_admin_menu_nav(callback: CallbackQuery) -> None:
    if callback.from_user.id not in STAFF_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    target = callback.data.split(":", 1)[1]
    menus = {
        "main": ("🛠 <b>Admin panel</b>\nKerakli bo'limni tanlang:", _admin_main_menu_kb(callback.from_user.id)),
        "content": ("🎬 <b>Kontent boshqaruvi</b>", _admin_content_menu_kb()),
        "users": ("👥 <b>Foydalanuvchilar</b>", _admin_users_menu_kb()),
        "broadcast": ("📢 <b>Xabar yuborish</b>", _admin_broadcast_menu_kb()),
        "shop": ("🛍 <b>Do'kon boshqaruvi</b>", _admin_shop_menu_kb()),
        "promo": ("🎟 <b>Promo & Tez orada</b>", _admin_promo_menu_kb()),
        "fsub": ("📢 <b>Majburiy obuna kanallari</b>\nBot bu kanallarda ADMIN bo'lishi shart!", _admin_fsub_menu_kb()),
        "backup": ("💾 <b>Zaxira va tiklash</b>\nBaza Telegram'ga fayl qilib yuboriladi va kerak bo'lganda tiklanadi.", _admin_backup_menu_kb()),
    }
    text, kb = menus.get(target, menus["main"])
    await callback.message.edit_text(text, reply_markup=kb.as_markup())
    await callback.answer()


# Faqat argumentsiz/to'g'ridan-to'g'ri bajariladigan amallar (natija darhol chatga yuboriladi)
_ADMIN_DIRECT_ACTIONS = {"stats", "products", "lowviews", "requests", "fsublist"}
# Argument talab qiladigan amallar — tugma bosilganda aniq buyruq namunasi ko'rsatiladi
_ADMIN_USAGE_HINTS = {
    "addepisode_info": "📼 Serialga qism qo'shish:\n<code>/addepisode &lt;serial_kodi&gt;</code>\nMasalan: <code>/addepisode 2001</code>",
    "editmovie_info": "✏️ Kino tahrirlash:\n<code>/editmovie &lt;kod&gt;</code>\nMasalan: <code>/editmovie 1001</code>",
    "delmovie_info": "🗑 Kino o'chirish:\n<code>/delmovie &lt;kod&gt;</code>",
    "delseries_info": "🗑 Serial o'chirish:\n<code>/delseries &lt;kod&gt;</code>",
    "searchuser_info": "🔎 Foydalanuvchi qidirish:\n<code>/searchuser &lt;ism yoki username&gt;</code>",
    "userinfo_info": "ℹ️ Foydalanuvchi ma'lumoti:\n<code>/user_info &lt;id&gt;</code>",
    "ban_info": "🚫 Bloklash:\n<code>/ban &lt;user_id&gt; [sabab]</code>",
    "unban_info": "✅ Blokdan chiqarish:\n<code>/unban &lt;user_id&gt;</code>",
    "givevip_info": "💎 VIP/Premium berish (to'lovsiz, qo'lda):\n<code>/givevip &lt;user_id&gt; &lt;kun_soni&gt;</code>\nMasalan: <code>/givevip 123456789 30</code>\n(Botda alohida \"Premium\" darajasi yo'q — VIP va Premium bitta a'zolik.)",
    "removevip_info": "⛔ VIP/Premium olib tashlash:\n<code>/removevip &lt;user_id&gt;</code>",
    "delproduct_info": "🗑 Mahsulot o'chirish:\n<code>/delproduct &lt;id&gt;</code>\n(ID'larni ko'rish uchun \"📃 Mahsulotlar ro'yxati\"ni bosing)",
    "addpromo_info": "🎟 Promo-kod yaratish:\n<code>/addpromo &lt;KOD&gt; &lt;vip_kun&gt; &lt;max_ishlatish&gt; [amal_kun]</code>\nMasalan: <code>/addpromo SALE10 7 100 30</code>",
    "releasecoming_info": "🚀 \"Tez orada\"ni chiqarilgan deb belgilash:\n<code>/releasecoming &lt;id&gt; &lt;kino_kodi&gt;</code>\nID'larni ko'rish uchun /addcomingsoon orqali qo'shilganlar ro'yxatini eslang.",
    "comments_info": "💬 Izohni o'chirish:\n<code>/delcomment &lt;id&gt;</code>\n(ID mini-app'dagi izohlar ro'yxatida ko'rinadi)",
}


@admin_router.callback_query(F.data.startswith("admin_act:"))
async def cb_admin_action(callback: CallbackQuery, state: FSMContext) -> None:
    if callback.from_user.id not in STAFF_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    action = callback.data.split(":", 1)[1]
    await callback.answer()

    if action == "emoji_start":
        if callback.from_user.id not in ADMIN_IDS:
            await callback.message.answer("⛔ Bu bo'lim faqat to'liq admin va egasi uchun.")
            return
        await state.clear()
        await state.set_state(EmojiStates.wait)
        await callback.message.answer(EMOJI_HELP)
        return

    if action in _ADMIN_USAGE_HINTS:
        await callback.message.answer(_ADMIN_USAGE_HINTS[action])
        return

    if action == "addfsub":
        current = await get_force_sub_channels()
        if len(current) >= MAX_FORCE_SUB_CHANNELS:
            await callback.message.answer(
                f"⚠️ Limitga yetdingiz: maksimum {MAX_FORCE_SUB_CHANNELS} ta majburiy kanal qo'shish mumkin.\n"
                "Yangi kanal qo'shish uchun avval eskilaridan birini o'chiring "
                "(\"📃 Kanallar ro'yxati / o'chirish\")."
            )
            return

    # Ko'p bosqichli (FSM) amallar — shu funksiya chaqirilganda quriladi (lazy),
    # shunda State klasslari faylning istalgan joyida e'lon qilingan bo'lsa ham
    # muammo bo'lmaydi (modul yuklanish vaqtida emas, chaqiruv vaqtida o'qiladi).
    fsm_actions = {
        "addmovie": (AddMovieStates.code, "🆕 Kino kodini kiriting (masalan: 1001):"),
        "addseries": (AddSeriesStates.code, "📺 Yangi serial kodini kiriting (masalan: 2001):"),
        "addproduct": (AddProductStates.title, "🛍 Yangi taklif nomini kiriting (masalan: Shaxsiy VIP dizayn):"),
        "addcomingsoon": (AddComingSoonStates.title, "🔜 Tez orada chiqadigan kino/serial nomini kiriting:"),
        "broadcast": (BroadcastStates.content, "📢 Barcha foydalanuvchilarga yuboriladigan xabarni yuboring (matn/rasm):"),
        "broadcastvip": (BroadcastVipStates.content, "💎 Faqat VIP a'zolarga yuboriladigan xabarni yuboring:"),
        "addfsub": (AddForceSubStates.chat_id, ADDFSUB_PROMPT),
    }
    if action in fsm_actions:
        target_state, prompt = fsm_actions[action]
        if action in ("addmovie", "addseries"):
            prompt += await code_hint(action)
            await state.clear()
            await state.update_data(category="movie" if action == "addmovie" else "series", is_new=True, added=[])
        await state.set_state(target_state)
        await callback.message.answer(prompt)
        return

    if action == "restore":
        if callback.from_user.id not in OWNER_IDS:
            await callback.message.answer("⛔ Bu amal faqat admin uchun.")
            return
        await state.set_state(RestoreStates.file)
        await callback.message.answer(RESTORE_PROMPT)
        return
    if action == "backupnow":
        await cmd_backup(_AdminMsgProxy(callback))
        return
    if action == "adminhelp":
        await cmd_adminhelp(_AdminMsgProxy(callback))
        return
    if action == "fsubtest":
        await admin_fsub_test(_AdminMsgProxy(callback))
        return
    if action == "stats":
        await admin_stats(_AdminMsgProxy(callback))
        return
    if action == "products":
        await admin_products_list(_AdminMsgProxy(callback))
        return
    if action == "lowviews":
        await admin_lowviews(_AdminMsgProxy(callback))
        return
    if action == "requests":
        await admin_movie_requests(_AdminMsgProxy(callback))
        return
    if action == "fsublist":
        await admin_fsub_list(_AdminMsgProxy(callback))
        return


class _AdminMsgProxy:
    """Admin-panel tugmalari orqali mavjud /stats, /products, /lowviews,
    /movie_requests handlerlarini QAYTA YOZMASDAN chaqirish uchun ingichka
    moslashtiruvchi: callback.message o'rniga chaqiruvchi (bosgan admin)ning
    from_user'ini almashtirib beradi, javob esa xuddi shu chatga ketadi."""

    def __init__(self, callback: CallbackQuery):
        self._callback = callback
        self.from_user = callback.from_user

    def answer(self, *args, **kwargs):
        return self._callback.message.answer(*args, **kwargs)


# ========================================================================
# YANGI: MAJBURIY OBUNA — kanal qo'shish / ro'yxat / o'chirish (admin panel)
# ========================================================================

class AddForceSubStates(StatesGroup):
    chat_id = State()
    title = State()
    url = State()


def _extract_forwarded_chat(message: Message):
    """Forward qilingan xabardan manba kanalni topadi. aiogram/Bot API
    versiyasiga qarab ma'lumot 'forward_origin' (yangi) yoki
    'forward_from_chat' (eski, deprecated) maydonida kelishi mumkin —
    ikkalasini ham sinab ko'ramiz."""
    origin = getattr(message, "forward_origin", None)
    if origin is not None and getattr(origin, "chat", None) is not None:
        return origin.chat
    fwd_chat = getattr(message, "forward_from_chat", None)
    if fwd_chat is not None:
        return fwd_chat
    return None


ADDFSUB_PROMPT = (
    "📢 <b>Kanal qo'shish</b> — ikki xil usul:\n\n"
    "1️⃣ Kanaldagi istalgan postni shu yerga <b>forward</b> qiling — "
    "bot kanal ID, nom va havolani o'zi aniqlaydi.\n\n"
    "2️⃣ Yoki yozing: <code>@mychannel</code> yoki <code>-1001234567890</code>\n\n"
    "⚠️ Bot shu kanalda <b>ADMIN</b> bo'lishi shart.\n"
    "Bekor qilish: /cancel"
)


async def _finalize_add_force_sub(message: Message, state: FSMContext, chat_id: str, title: str, url: "str | None") -> None:
    """Kanalni qo'shadi: bot kanalda adminligini TEKSHIRADI, havolani avtomatik topadi va
    natijani adminga ANIQ ko'rsatadi."""
    await state.clear()
    current = await get_force_sub_channels()
    if len(current) >= MAX_FORCE_SUB_CHANNELS:
        await message.answer(
            f"⚠️ Limitga yetdingiz: maksimum {MAX_FORCE_SUB_CHANNELS} ta majburiy kanal qo'shish mumkin. "
            "Kanal qo'shilmadi."
        )
        return
    if any(str(c["chat_id"]) == str(chat_id) for c in current):
        await message.answer(f"ℹ️ <b>{html_escape(str(title))}</b> allaqachon ro'yxatda.")
        return

    info = await resolve_channel_info(chat_id)
    if not valid_button_url(url):
        url = None
    url = url or info.get("url")
    title = title or info.get("title") or str(chat_id)

    if info["is_admin"]:
        status_line = "✅ Bot shu kanalda ADMIN — obuna tekshiruvi ishlaydi."
    elif info["error"]:
        status_line = (
            f"❌ DIQQAT: bot kanalga kira olmadi ({html_escape(str(info['error'])[:200])}). "
            "Botni kanalga qo'shib, ADMIN qiling — aks holda bu kanal tekshiruvda e'tiborga olinmaydi!"
        )
    else:
        status_line = (
            "❌ DIQQAT: bot bu kanalda ADMIN EMAS. Kanalga o'tib, botni ADMIN qiling — "
            "aks holda obuna tekshiruvi bu kanal uchun ishlamaydi!"
        )

    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO force_sub_channels (chat_id, title, url, added_at) VALUES (?, ?, ?, ?)",
            (str(chat_id), str(title), url or None, now_iso()),
        )
        await db.commit()
    link_line = (
        f"🔗 Havola: {html_escape(url)}" if url
        else "⚠️ Havola aniqlanmadi — botni kanalda ADMIN qiling, taklif havolasi o'zi yaratiladi."
    )
    await message.answer(
        f"✅ Kanal qo'shildi: <b>{html_escape(str(title))}</b> (<code>{html_escape(str(chat_id))}</code>)\n"
        f"📊 Jami: {len(current) + 1}/{MAX_FORCE_SUB_CHANNELS} ta kanal\n"
        f"{link_line}\n\n{status_line}\n\n"
        "👁 Foydalanuvchi ko'radigan xabarni ko'rish: /fsubtest"
    )


@admin_router.message(AddForceSubStates.chat_id)
async def admin_addfsub_chat_id(message: Message, state: FSMContext) -> None:
    # 1) Kanaldan post FORWARD qilingan bo'lsa — hammasini avtomatik olamiz
    fwd_chat = _extract_forwarded_chat(message)
    if fwd_chat is not None:
        chat_id = str(fwd_chat.id)
        title = getattr(fwd_chat, "title", None) or chat_id
        username = getattr(fwd_chat, "username", None)
        url = f"https://t.me/{username}" if username else None
        await _finalize_add_force_sub(message, state, chat_id, title, url)
        return

    # 2) Qo'lda yozilgan: faqat @username yoki -100... ID qabul qilinadi
    ref = normalize_channel_ref(message.text or "")
    if not ref:
        await message.answer(
            "❌ Bu kanal ko'rsatkichi yaroqsiz.\n\n"
            "Quyidagilardan birini yuboring:\n"
            "• <code>@kanal_username</code>\n"
            "• <code>-1001234567890</code> (kanal ID)\n"
            "• yoki kanaldan bitta postni <b>forward</b> qiling\n\n"
            "Bekor qilish: /cancel"
        )
        return
    info = await resolve_channel_info(ref)
    if info["title"] is None:
        await message.answer(
            f"❌ Bot bu kanalni topa olmadi: <code>{html_escape(str(info['error'])[:200])}</code>\n\n"
            "Botni kanalga qo'shib ADMIN qiling, so'ng qayta yuboring. Bekor qilish: /cancel"
        )
        return
    await _finalize_add_force_sub(message, state, ref, info["title"], info["url"])


@admin_router.message(Command("addfsub"))
async def cmd_addfsub(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    current = await get_force_sub_channels()
    if len(current) >= MAX_FORCE_SUB_CHANNELS:
        await message.answer(f"⚠️ Limitga yetdingiz: maksimum {MAX_FORCE_SUB_CHANNELS} ta kanal.")
        return
    await state.set_state(AddForceSubStates.chat_id)
    await message.answer(ADDFSUB_PROMPT)


@admin_router.message(Command("fsublist"))
async def cmd_fsublist(message: Message) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    await admin_fsub_list(message)


async def admin_fsub_test(message) -> None:
    """Foydalanuvchi obuna xabarini AYNAN qanday ko'rishini adminga ko'rsatadi."""
    if message.from_user.id not in STAFF_IDS:
        return
    channels = await get_force_sub_channels()
    if not channels:
        await message.answer("📭 Majburiy obuna kanallari yo'q. Qo'shish: /addfsub")
        return
    markup, no_link = await build_force_sub_markup(channels)
    try:
        await message.answer(
            "👁 <b>Foydalanuvchi shunday ko'radi:</b>\n\n" + FORCE_SUB_TEXT + no_link_lines(no_link),
            reply_markup=markup,
        )
    except Exception as e:
        await message.answer(
            f"❌ Xabarni yuborib bo'lmadi: <code>{html_escape(str(e)[:250])}</code>\n"
            "Kanallarni /fsublist orqali tekshiring."
        )
        return
    if no_link:
        await message.answer(
            "⚠️ Havolasi topilmagan kanallar tugmasiz ko'rinadi. Botni shu kanallarda ADMIN qiling."
        )


@admin_router.message(Command("fsubtest"))
async def cmd_fsubtest(message: Message) -> None:
    await admin_fsub_test(message)


@admin_router.message(AddForceSubStates.title)
async def admin_addfsub_title(message: Message, state: FSMContext) -> None:
    title = (message.text or "").strip()
    if not title:
        await message.answer("❌ Bo'sh bo'lmasin. Qayta kiriting:")
        return
    await state.update_data(title=title)
    await state.set_state(AddForceSubStates.url)
    await message.answer(
        "🔗 Kanal havolasini kiriting (masalan <code>https://t.me/mychannel</code> yoki "
        "yopiq kanal uchun taklif havolasi <code>https://t.me/+xxxxx</code>).\n"
        "Agar kanal @username bo'lsa va havola shundan avtomatik yasalishini xohlasangiz — \"-\" yozing:"
    )


@admin_router.message(AddForceSubStates.url)
async def admin_addfsub_url(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    chat_id = data["chat_id"]
    title = data["title"]
    url_input = (message.text or "").strip()
    if url_input == "-":
        url = f"https://t.me/{chat_id.lstrip('@')}" if chat_id.startswith("@") else ""
    else:
        url = url_input
    await _finalize_add_force_sub(message, state, chat_id, title, url or None)


async def admin_fsub_list(message) -> None:
    channels = await get_force_sub_channels()
    if not channels:
        await message.answer(f"📭 Hozircha majburiy obuna kanallari yo'q. (0/{MAX_FORCE_SUB_CHANNELS})")
        return
    lines = [f"📢 <b>Majburiy obuna kanallari</b> ({len(channels)}/{MAX_FORCE_SUB_CHANNELS}):\n(o'chirish uchun tugmani bosing)"]
    kb = InlineKeyboardBuilder()
    me = await bot.get_me()
    for ch in channels:
        status_icon = "✅"
        try:
            member = await bot.get_chat_member(_chat_ref(ch["chat_id"]), me.id)
            if member.status != "administrator":
                status_icon = "⚠️"
        except Exception:
            status_icon = "❌"
        lines.append(f"{status_icon} {html_escape(ch['title'])} — <code>{html_escape(str(ch['chat_id']))}</code>")
        kb.button(text=f"🗑 {ch['title']}", callback_data=f"fsub_del:{ch['id']}")
    lines.append("\n✅ — bot admin | ⚠️ — bot admin emas | ❌ — kanal topilmadi/bot a'zo emas")
    kb.adjust(1)
    await message.answer("\n".join(lines), reply_markup=kb.as_markup())


@admin_router.callback_query(F.data.startswith("fsub_del:"))
async def cb_fsub_delete(callback: CallbackQuery) -> None:
    if callback.from_user.id not in STAFF_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    fsub_id = int(callback.data.split(":", 1)[1])
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM force_sub_channels WHERE id = ?", (fsub_id,))
        await db.commit()
    await callback.answer("🗑 O'chirildi")
    await admin_fsub_list(_AdminMsgProxy(callback))


# ========================================================================
# ADMIN (asl 5 ta funksiya — tuzatilgan)
# ========================================================================

@admin_router.message(Command("stats"))
async def admin_stats(message: Message) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        total_users = (await (await db.execute("SELECT COUNT(*) c FROM users")).fetchone())["c"]
        vip_count = (await (await db.execute(
            "SELECT COUNT(*) c FROM users WHERE vip_until IS NOT NULL AND vip_until > ?",
            (now_iso(),),
        )).fetchone())["c"]
        pending_requests = (await (await db.execute(
            "SELECT COUNT(*) c FROM movie_requests WHERE status='pending'"
        )).fetchone())["c"]
        total_favorites = (await (await db.execute("SELECT COUNT(*) c FROM user_favorites")).fetchone())["c"]
        total_stars = (await (await db.execute(
            "SELECT COALESCE(SUM(amount_stars),0) s FROM payments"
        )).fetchone())["s"]
        top_movies = await (await db.execute(
            "SELECT title, views FROM movies ORDER BY views DESC LIMIT 5"
        )).fetchall()
    lines = [
        "📊 <b>Umumiy statistika</b>",
        f"👤 Foydalanuvchilar: {total_users}",
        f"💎 VIP: {vip_count}",
        f"❤️ Sevimlilarga qo'shilgan: {total_favorites}",
        f"📝 Kutilayotgan kino so'rovlari: {pending_requests}",
        f"⭐ Jami tushum: {total_stars} Stars",
    ]
    if top_movies:
        lines.append("\n🏆 <b>Top 5 kino:</b>")
        for i, m in enumerate(top_movies, 1):
            lines.append(f"{i}. {m['title']} — {m['views']} ko'rish")
    await message.answer("\n".join(lines))


class BroadcastStates(StatesGroup):
    content = State()
    confirm = State()


@admin_router.message(Command("broadcast"))
async def admin_broadcast_start(message: Message, state: FSMContext) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    await state.set_state(BroadcastStates.content)
    await message.answer("📢 Barcha foydalanuvchilarga yuboriladigan xabarni yuboring (matn/rasm):")


@admin_router.message(BroadcastStates.content)
async def admin_broadcast_content(message: Message, state: FSMContext) -> None:
    await state.update_data(
        text=message.html_text or message.caption or "",
        photo=message.photo[-1].file_id if message.photo else None,
    )
    await state.set_state(BroadcastStates.confirm)
    kb = InlineKeyboardBuilder()
    kb.button(text="✅ Yuborish", callback_data="bc_confirm")
    kb.button(text="❌ Bekor qilish", callback_data="bc_cancel")
    await message.answer("Shu xabarni barchaga yuborishni tasdiqlaysizmi?", reply_markup=kb.as_markup())


@admin_router.callback_query(F.data == "bc_confirm")
async def admin_broadcast_confirm(callback: CallbackQuery, state: FSMContext) -> None:
    data = await state.get_data()
    await state.clear()
    await callback.message.edit_text("⏳ Yuborilmoqda...")
    sent, failed = 0, 0
    async with aiosqlite.connect(DB_PATH) as db:
        rows = await (await db.execute("SELECT user_id FROM users")).fetchall()
    for (uid,) in rows:
        try:
            if data.get("photo"):
                await bot.send_photo(uid, data["photo"], caption=data.get("text") or "")
            else:
                await bot.send_message(uid, data.get("text") or "")
            sent += 1
        except Exception:
            failed += 1
        await asyncio.sleep(0.05)
    await callback.message.edit_text(f"✅ Yuborildi: {sent} ta\n⚠️ Yetib bormadi: {failed} ta")


@admin_router.callback_query(F.data == "bc_cancel")
async def admin_broadcast_cancel(callback: CallbackQuery, state: FSMContext) -> None:
    await state.clear()
    await callback.message.edit_text("❌ Bekor qilindi.")


@admin_router.message(Command("ban"))
async def admin_ban(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    parts = (command.args or "").split(maxsplit=1)
    if not parts:
        await message.answer("Foydalanish: /ban &lt;user_id&gt; [sabab]")
        return
    try:
        uid = int(parts[0])
    except ValueError:
        await message.answer("user_id son bo'lishi kerak.")
        return
    reason = parts[1] if len(parts) > 1 else None
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT OR REPLACE INTO banned_users (user_id, reason, banned_by, banned_at) VALUES (?, ?, ?, ?)",
            (uid, reason, message.from_user.id, now_iso()),
        )
        await db.commit()
    await message.answer(f"🚫 {uid} bloklandi." + (f" Sabab: {reason}" if reason else ""))


@admin_router.message(Command("unban"))
async def admin_unban(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /unban &lt;user_id&gt;")
        return
    try:
        uid = int(command.args.strip())
    except ValueError:
        await message.answer("user_id son bo'lishi kerak.")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("DELETE FROM banned_users WHERE user_id = ?", (uid,))
        await db.commit()
    await message.answer(f"✅ {uid} blokdan chiqarildi.")


# ----------------------------------------------------------------------
# YANGI: ADMIN QO'LDA VIP BERISH / OLIB TASHLASH
# Eslatma: botda alohida "Premium" darajasi yo'q — "VIP" va "Premium"
# bitta xil a'zolik (users.vip_until). Ekrandagi "💎 Premium" tugmasi ham
# aslida shu VIP/Do'kon bo'limiga olib boradi. Pastdagi buyruqlar orqali
# xohlagan foydalanuvchiga to'lovsiz, qo'lda VIP/Premium bera olasiz.
# ----------------------------------------------------------------------
@admin_router.message(Command("givevip"))
async def admin_give_vip(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    parts = (command.args or "").split()
    if len(parts) != 2:
        await message.answer("Foydalanish: /givevip &lt;user_id&gt; &lt;kun_soni&gt;\nMasalan: /givevip 123456789 30")
        return
    try:
        uid, days = int(parts[0]), int(parts[1])
    except ValueError:
        await message.answer("user_id va kun soni son bo'lishi kerak.")
        return
    if days <= 0:
        await message.answer("Kun soni musbat bo'lishi kerak.")
        return
    await extend_vip(uid, days)
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT vip_until FROM users WHERE user_id = ?", (uid,))).fetchone()
    until = row["vip_until"][:10] if row and row["vip_until"] else "?"
    await message.answer(f"✅ {uid} ga {days} kunlik VIP/Premium berildi.\nAmal qilish muddati: {until} gacha.")
    try:
        await bot.send_message(
            uid, f"💎 Sizga admin tomonidan <b>{days} kunlik VIP/Premium</b> a'zolik berildi!\nMuddati: {until} gacha."
        )
    except Exception:
        pass


@admin_router.message(Command("removevip"))
async def admin_remove_vip(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /removevip &lt;user_id&gt;")
        return
    try:
        uid = int(command.args.strip())
    except ValueError:
        await message.answer("user_id son bo'lishi kerak.")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute("UPDATE users SET vip_until = NULL WHERE user_id = ?", (uid,))
        await db.commit()
    await message.answer(f"✅ {uid} ning VIP/Premium a'zoligi bekor qilindi.")


@admin_router.message(Command("user_info"))
async def admin_user_info(message: Message, command: CommandObject) -> None:
    if message.from_user.id not in ADMIN_IDS:
        return
    if not command.args:
        await message.answer("Foydalanish: /user_info &lt;user_id&gt;")
        return
    try:
        uid = int(command.args.strip())
    except ValueError:
        await message.answer("user_id son bo'lishi kerak.")
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        user = await (await db.execute("SELECT * FROM users WHERE user_id = ?", (uid,))).fetchone()
        if not user:
            await message.answer("Foydalanuvchi topilmadi.")
            return
        fav_count = (await (await db.execute(
            "SELECT COUNT(*) c FROM user_favorites WHERE user_id = ?", (uid,)
        )).fetchone())["c"]
        checkin = await (await db.execute(
            "SELECT streak, total_checkins FROM daily_checkins WHERE user_id = ?", (uid,)
        )).fetchone()
        banned = await (await db.execute("SELECT reason FROM banned_users WHERE user_id = ?", (uid,))).fetchone()
    u = dict(user)
    vip_display = u.get("vip_until") or "yo'q"
    banned_display = ("Ha — " + (banned["reason"] or "—")) if banned else "Yo'q"
    lines = [
        f"👤 <b>{u.get('full_name', '—')}</b> (@{u.get('username') or '—'})",
        f"🆔 {uid}",
        f"💎 VIP: {vip_display}",
        f"❤️ Sevimlilar: {fav_count}",
        f"🔥 Kunlik streak: {checkin['streak'] if checkin else 0} ({checkin['total_checkins'] if checkin else 0} marta)",
        f"⭐ Sarflagan Stars: {u.get('stars_spent', 0)}",
        f"👥 Taklif qilganlar: {u.get('referral_count', 0)}",
        f"🚫 Bloklangan: {banned_display}",
    ]
    await message.answer("\n".join(lines))


@admin_router.message(Command("movie_requests"))
async def admin_movie_requests(message: Message) -> None:
    if message.from_user.id not in STAFF_IDS:
        return
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT * FROM movie_requests WHERE status='pending' ORDER BY created_at DESC LIMIT 10"
        )).fetchall()
    if not rows:
        await message.answer("📭 Kutilayotgan so'rovlar yo'q.")
        return
    for r in rows:
        kb = InlineKeyboardBuilder()
        kb.button(text="✅ Bajarildi", callback_data=f"req_done_{r['id']}")
        kb.button(text="❌ Rad etish", callback_data=f"req_reject_{r['id']}")
        await message.answer(
            f"📝 <b>{r['title']}</b>\n💬 {r['note'] or '—'}\n👤 {r['user_id']}",
            reply_markup=kb.as_markup(),
        )


@admin_router.callback_query(F.data.startswith("req_done_") | F.data.startswith("req_reject_"))
async def admin_movie_request_resolve(callback: CallbackQuery) -> None:
    ok = callback.data.startswith("req_done_")
    req_id = int(callback.data.split("_")[-1])
    status = "done" if ok else "rejected"
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT user_id, title FROM movie_requests WHERE id = ?", (req_id,))).fetchone()
        await db.execute(
            "UPDATE movie_requests SET status = ?, resolved_at = ? WHERE id = ?", (status, now_iso(), req_id)
        )
        await db.commit()
    await callback.message.edit_text(callback.message.text + f"\n\n{'✅ Bajarildi' if ok else '❌ Rad etildi'}")
    if row:
        try:
            if ok:
                await bot.send_message(row["user_id"], f"🎬 So'ragan kinongiz qo'shildi: {row['title']}")
            else:
                await bot.send_message(row["user_id"], f"😔 \"{row['title']}\" so'rovingiz bajarilmadi.")
        except Exception:
            pass
    await callback.answer()


# ========================================================================
# USER (asl 5 ta funksiya — mini-app API, endi xavfsiz initData bilan)
# ========================================================================

@user_router.message(Command("checkin"))
@user_router.message(F.text == "🎁 Kunlik bonus")
async def cmd_checkin_hint(message: Message) -> None:
    await message.answer("🎁 Kunlik bonusni Mini App > Profil bo'limidan belgilashingiz mumkin.")


# ========================================================================
# PUL TOPISH FUNKSIYASI 1/3 — VIP OBUNA (Telegram Stars)
# ========================================================================
@user_router.message(Command("vip"))
@user_router.message(F.text == "💎 VIP olish")
async def cmd_vip(message: Message) -> None:
    kb = InlineKeyboardBuilder()
    for plan_id, plan in VIP_PLANS.items():
        kb.button(text=f"{plan['label']} — {plan['stars']}⭐", callback_data=f"buy_vip:{plan_id}")
    kb.adjust(1)
    await message.answer(
        "💎 <b>VIP a'zolik afzalliklari:</b>\n"
        "• Reklamasiz foydalanish\n"
        "• Barcha eksklyuziv kinolar bepul\n"
        "• Kunlik bonus 2x tezroq to'planadi\n\n"
        "Tarifni tanlang:",
        reply_markup=kb.as_markup(),
    )


@user_router.callback_query(F.data.startswith("buy_vip:"))
async def cb_buy_vip(callback: CallbackQuery) -> None:
    plan_id = callback.data.split(":", 1)[1]
    plan = VIP_PLANS.get(plan_id)
    if plan is None or callback.message is None:
        await callback.answer("⚠️ Bu tugma eskirgan. /vip ni qaytadan bosing.", show_alert=True)
        return
    await callback.message.answer_invoice(
        title=plan["label"],
        description=f"{plan['days']} kunlik VIP a'zolik",
        payload=f"vip:{plan_id}",
        currency="XTR",
        prices=[LabeledPrice(label=plan["label"], amount=plan["stars"])],
    )
    await callback.answer()


# ========================================================================
# PUL TOPISH FUNKSIYASI 2/3 — EKSKLYUZIV KINO SOTIB OLISH
# ========================================================================
# (deliver_movie() funksiyasi ichida amalga oshirilgan: agar kino narxi
#  bo'lsa va foydalanuvchi VIP bo'lmasa — avtomatik invoice yuboriladi)


# ========================================================================
# PUL TOPISH FUNKSIYASI 3/3 — HOMIYLIK / SUPPORT (donation)
# ========================================================================
@user_router.message(Command("support"))
@user_router.message(F.text == "❤️ Botni qo'llab-quvvatlash")
async def cmd_support(message: Message) -> None:
    kb = InlineKeyboardBuilder()
    for amount in DONATE_OPTIONS:
        kb.button(text=f"{amount}⭐", callback_data=f"donate:{amount}")
    kb.adjust(4)
    await message.answer(
        "❤️ Botimiz yoqsa, uni qo'llab-quvvatlashingiz mumkin.\n"
        "Har qanday miqdordagi Stars katta yordam bo'ladi!",
        reply_markup=kb.as_markup(),
    )


@user_router.callback_query(F.data.startswith("donate:"))
async def cb_donate(callback: CallbackQuery) -> None:
    amount = int(callback.data.split(":")[1])
    await callback.message.answer_invoice(
        title="Homiylik",
        description=f"Botni qo'llab-quvvatlash — {amount} Stars",
        payload=f"donate:{amount}",
        currency="XTR",
        prices=[LabeledPrice(label="Homiylik", amount=amount)],
    )
    await callback.answer()


# ----------------------------------------------------------------------
# TO'LOVLARNI QAYTA ISHLASH (Telegram Stars)
# ----------------------------------------------------------------------
@pay_router.pre_checkout_query()
async def process_pre_checkout(pre_checkout_query: PreCheckoutQuery) -> None:
    await pre_checkout_query.answer(ok=True)


@pay_router.message(F.successful_payment)
async def process_successful_payment(message: Message) -> None:
    payload = message.successful_payment.invoice_payload
    amount = message.successful_payment.total_amount
    uid = message.from_user.id
    kind, _, ref = payload.partition(":")

    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO payments (user_id, kind, ref, amount_stars, created_at) VALUES (?, ?, ?, ?, ?)",
            (uid, kind, ref, amount, now_iso()),
        )
        await db.execute(
            "UPDATE users SET stars_spent = stars_spent + ? WHERE user_id = ?", (amount, uid)
        )
        await db.commit()

    if kind == "vip":
        plan = VIP_PLANS.get(ref)
        if plan:
            await extend_vip(uid, plan["days"])
            await message.answer(f"✅ Rahmat! Sizga {plan['days']} kunlik VIP faollashtirildi 💎")
    elif kind == "movie":
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR IGNORE INTO movie_purchases (user_id, movie_code, purchased_at) VALUES (?, ?, ?)",
                (uid, ref, now_iso()),
            )
            await db.commit()
        await message.answer("✅ To'lov qabul qilindi! Kino yuborilmoqda...")
        await deliver_movie(message.chat.id, uid, ref)
    elif kind == "series":
        async with aiosqlite.connect(DB_PATH) as db:
            await db.execute(
                "INSERT OR IGNORE INTO movie_purchases (user_id, movie_code, purchased_at) VALUES (?, ?, ?)",
                (uid, ref, now_iso()),
            )
            await db.commit()
        await message.answer("✅ To'lov qabul qilindi! Serial ochildi, 1-qismni yuborilmoqda...")
        await deliver_series_episode(message.chat.id, uid, ref, 1)
    elif kind == "donate":
        await message.answer(f"❤️ Rahmat! Siz {amount}⭐ homiylik qildingiz. Bu biz uchun juda muhim!")
        for admin_id in ADMIN_IDS:
            try:
                await bot.send_message(admin_id, f"❤️ Yangi homiylik: {amount}⭐ — @{message.from_user.username or uid}")
            except Exception:
                pass


# ========================================================================
# MINI-APP UCHUN WEB API (aiohttp)
# ========================================================================

def verify_init_data(init_data: str) -> dict | None:
    """Telegram WebApp initData'ni xavfsiz tekshiradi (hash orqali)."""
    if not init_data:
        return None
    try:
        parsed = dict(parse_qsl(init_data, strict_parsing=True))
    except ValueError:
        return None
    received_hash = parsed.pop("hash", None)
    if not received_hash:
        return None
    data_check_string = "\n".join(f"{k}={v}" for k, v in sorted(parsed.items()))
    secret_key = hmac.new(b"WebAppData", BOT_TOKEN.encode(), hashlib.sha256).digest()
    calc_hash = hmac.new(secret_key, data_check_string.encode(), hashlib.sha256).hexdigest()
    if not hmac.compare_digest(calc_hash, received_hash):
        return None
    return parsed


async def get_request_user_id(request: web.Request) -> int | None:
    init_data = request.headers.get("X-Init-Data", "")
    parsed = verify_init_data(init_data)
    if not parsed:
        return None
    try:
        user = json.loads(parsed.get("user", "{}"))
        return int(user.get("id"))
    except Exception:
        return None


def api_route(handler):
    async def wrapper(request: web.Request) -> web.Response:
        user_id = await get_request_user_id(request)
        if not user_id:
            return web.json_response({"ok": False, "message": "unauthorized"}, status=401)
        if await is_banned(user_id):
            return web.json_response({"ok": False, "message": "banned"}, status=403)
        return await handler(request, user_id)
    return wrapper


# ---- 1) Sevimlilar ----
@api_route
async def api_favorite_toggle(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = data.get("code")
    async with aiosqlite.connect(DB_PATH) as db:
        exists = await (await db.execute(
            "SELECT 1 FROM user_favorites WHERE user_id = ? AND movie_code = ?", (user_id, code)
        )).fetchone()
        if exists:
            await db.execute("DELETE FROM user_favorites WHERE user_id = ? AND movie_code = ?", (user_id, code))
            added = False
        else:
            await db.execute(
                "INSERT INTO user_favorites (user_id, movie_code, created_at) VALUES (?, ?, ?)",
                (user_id, code, now_iso()),
            )
            added = True
        await db.commit()
    return web.json_response({"ok": True, "added": added})


@api_route
async def api_favorites_list(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"""SELECT m.code, m.title, m.genre, m.views, m.is_vip, m.price_stars, m.added_at,
                      {poster_col('m.poster_url')}
               FROM user_favorites f
               JOIN movies m ON m.code = f.movie_code
               WHERE f.user_id = ? ORDER BY f.created_at DESC""",
            (user_id,),
        )).fetchall()
    return web.json_response({"ok": True, "favorites": [dict(r) for r in rows]})


# ---- 2) Kino so'rash ----
@api_route
async def api_movie_request_add(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    title = (data.get("title") or "").strip()
    note = data.get("note")
    if not title:
        return web.json_response({"ok": False, "message": "Kino nomini kiriting"})
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO movie_requests (user_id, title, note, status, created_at) VALUES (?, ?, ?, 'pending', ?)",
            (user_id, title, note, now_iso()),
        )
        await db.commit()
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(admin_id, f"📝 Yangi kino so'rovi: <b>{title}</b>\n👤 {user_id}")
        except Exception:
            pass
    return web.json_response({"ok": True})


# ---- 3) Kunlik bonus ----
@api_route
async def api_checkin(request: web.Request, user_id: int) -> web.Response:
    today = utcnow().date().isoformat()
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT * FROM daily_checkins WHERE user_id = ?", (user_id,))).fetchone()
        if row and row["last_checkin_date"] == today:
            return web.json_response({"ok": True, "already": True, "streak": row["streak"]})
        yesterday = (utcnow() - timedelta(days=1)).date().isoformat()
        streak = (row["streak"] + 1) if (row and row["last_checkin_date"] == yesterday) else 1
        total = (row["total_checkins"] + 1) if row else 1
        await db.execute(
            """INSERT INTO daily_checkins (user_id, streak, total_checkins, last_checkin_date)
               VALUES (?, ?, ?, ?)
               ON CONFLICT(user_id) DO UPDATE SET streak=?, total_checkins=?, last_checkin_date=?""",
            (user_id, streak, total, today, streak, total, today),
        )
        await db.commit()
    reward_days = 0
    if streak % 7 == 0:
        reward_days = 1
        await extend_vip(user_id, 1)
    if streak >= 7:
        await grant_achievement(user_id, "streak_7")
    if streak >= 30:
        await grant_achievement(user_id, "streak_30")
    return web.json_response({"ok": True, "already": False, "streak": streak, "reward_days": reward_days})


# ---- 4) Janr obunasi ----
@api_route
async def api_genre_sub_toggle(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    genre = data.get("genre")
    async with aiosqlite.connect(DB_PATH) as db:
        exists = await (await db.execute(
            "SELECT 1 FROM genre_subscriptions WHERE user_id = ? AND genre = ?", (user_id, genre)
        )).fetchone()
        if exists:
            await db.execute("DELETE FROM genre_subscriptions WHERE user_id = ? AND genre = ?", (user_id, genre))
            subscribed = False
        else:
            await db.execute(
                "INSERT INTO genre_subscriptions (user_id, genre) VALUES (?, ?)", (user_id, genre)
            )
            subscribed = True
        await db.commit()
    return web.json_response({"ok": True, "subscribed": subscribed})


# ---- 5) Mening statistikam ----
@api_route
async def api_user_stats(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        fav_count = (await (await db.execute(
            "SELECT COUNT(*) c FROM user_favorites WHERE user_id = ?", (user_id,)
        )).fetchone())["c"]
        checkin = await (await db.execute(
            "SELECT streak, total_checkins FROM daily_checkins WHERE user_id = ?", (user_id,)
        )).fetchone()
        req_count = (await (await db.execute(
            "SELECT COUNT(*) c FROM movie_requests WHERE user_id = ?", (user_id,)
        )).fetchone())["c"]
        u = await (await db.execute(
            "SELECT vip_until, referral_count FROM users WHERE user_id = ?", (user_id,)
        )).fetchone()
    return web.json_response({
        "ok": True,
        "favorites": fav_count,
        "streak": checkin["streak"] if checkin else 0,
        "total_checkins": checkin["total_checkins"] if checkin else 0,
        "requests": req_count,
        "vip_until": u["vip_until"] if u else None,
        "referral_count": u["referral_count"] if u else 0,
        "is_admin": user_id in ADMIN_IDS,
    })


# ---- YANGI MINI-APP API 1/5 — Kino reytingi (baholash) ----
@api_route
async def api_rate_movie(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code, rating = data.get("code"), int(data.get("rating", 0))
    if not (1 <= rating <= 5):
        return web.json_response({"ok": False, "message": "1-5 oralig'ida bo'lishi kerak"})
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO movie_ratings (user_id, movie_code, rating) VALUES (?, ?, ?) "
            "ON CONFLICT(user_id, movie_code) DO UPDATE SET rating = excluded.rating",
            (user_id, code, rating),
        )
        await db.commit()
        avg = await (await db.execute(
            "SELECT AVG(rating), COUNT(*) FROM movie_ratings WHERE movie_code = ?", (code,)
        )).fetchone()
    return web.json_response({"ok": True, "avg": round(avg[0] or 0, 1), "count": avg[1]})


# ---- Kino katalogi (mini-app bosh sahifasi uchun) ----
@api_route
async def api_movies_list(request: web.Request, user_id: int) -> web.Response:
    data = {}
    try:
        data = await request.json()
    except Exception:
        pass
    q = (data.get("q") or "").strip()
    genre = (data.get("genre") or "").strip()
    code = str(data.get("code") or "").strip()
    sort = (data.get("sort") or "new").strip()
    try:
        limit = max(1, min(int(data.get("limit", 60)), 300))
    except (TypeError, ValueError):
        limit = 60
    try:
        offset = max(0, int(data.get("offset", 0)))
    except (TypeError, ValueError):
        offset = 0
    where: list[str] = []
    params: list = []
    if code:
        where.append("m.code = ?")
        params.append(code)
    else:
        if q:
            where.append("(m.title LIKE ? OR m.genre LIKE ?)")
            params += [f"%{q}%", f"%{q}%"]
        if genre:
            # janr bo'yicha ANIQ moslik ("Drama" qidirilganda "Melodrama" chiqib ketmaydi)
            where.append("(',' || REPLACE(COALESCE(m.genre, ''), ', ', ',') || ',') LIKE ?")
            params.append(f"%,{genre},%")
    order = {
        "views": "m.views DESC, m.added_at DESC",
        "rating": "avg_rating DESC, rating_count DESC, m.added_at DESC",
    }.get(sort, "m.added_at DESC")
    category = str(data.get("category") or "").strip()
    if not code and category in ("movie", "cartoon"):
        where.append("COALESCE(m.category, 'movie') = ?")
        params.append(category)
    where_sql = ("WHERE " + " AND ".join(where)) if where else ""
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"""SELECT m.code, m.title, m.genre, m.description, m.views, m.is_vip, m.price_stars,
                      m.added_at, COALESCE(m.category, 'movie') AS category, {poster_col('m.poster_url')},
                      (SELECT ROUND(AVG(rating), 1) FROM movie_ratings WHERE movie_code = m.code) AS avg_rating,
                      (SELECT COUNT(*) FROM movie_ratings WHERE movie_code = m.code) AS rating_count
               FROM movies m {where_sql} ORDER BY {order} LIMIT ? OFFSET ?""",
            params + [limit + 1, offset],
        )).fetchall()
    return web.json_response({
        "ok": True,
        "movies": [dict(r) for r in rows[:limit]],
        "has_more": len(rows) > limit,
    })


# ---- YANGI MINI-APP API 2/5 — TOP-10 ----
@api_route
async def api_top_movies(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"SELECT code, title, genre, views, is_vip, price_stars, {poster_col('poster_url')} "
            "FROM movies ORDER BY views DESC LIMIT 10"
        )).fetchall()
    return web.json_response({"ok": True, "movies": [dict(r) for r in rows]})


# ---- YANGI MINI-APP API 3/5 — Tasodifiy kino ----
@api_route
async def api_random_movie(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute(
            "SELECT code, title, genre FROM movies ORDER BY RANDOM() LIMIT 1"
        )).fetchone()
    return web.json_response({"ok": True, "movie": dict(row) if row else None})


# ---- YANGI MINI-APP API 4/5 — Referral ma'lumoti ----
@api_route
async def api_referral_info(request: web.Request, user_id: int) -> web.Response:
    me = await bot.get_me()
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT referral_count FROM users WHERE user_id = ?", (user_id,)
        )).fetchone()
    return web.json_response({
        "ok": True,
        "link": f"https://t.me/{me.username}?start=ref_{user_id}",
        "count": row[0] if row else 0,
    })


# ---- YANGI MINI-APP API — Janrlar ro'yxati (filtr chiplar + obuna uchun) ----
@api_route
async def api_genres_list(request: web.Request, user_id: int) -> web.Response:
    """Endi doim TAYYOR janrlar ro'yxatini qaytaradi (GENRES) + har biridagi kino/serial soni."""
    async def _counts(db, table: str) -> dict:
        rows = await (await db.execute(
            f"SELECT genre FROM {table} WHERE genre IS NOT NULL AND genre != ''"
        )).fetchall()
        counts: dict[str, int] = {}
        for (g,) in rows:
            for name in normalize_genres(g)[0]:
                counts[name] = counts.get(name, 0) + 1
        return counts

    async with aiosqlite.connect(DB_PATH) as db:
        movie_counts = await _counts(db, "movies")
        series_counts = await _counts(db, "series")
        sub_rows = await (await db.execute(
            "SELECT genre FROM genre_subscriptions WHERE user_id = ?", (user_id,)
        )).fetchall()
    return web.json_response({
        "ok": True,
        "genres": GENRE_NAMES,
        "icons": GENRE_EMOJI,
        "counts": movie_counts,
        "series_counts": series_counts,
        "subscribed": [r[0] for r in sub_rows],
    })


# ---- MINI-APP API — Seriallar (bitta bo'lim, qismlarga bo'lingan) ----
@api_route
async def api_series_list(request: web.Request, user_id: int) -> web.Response:
    data = {}
    try:
        data = await request.json()
    except Exception:
        pass
    q = (data.get("q") or "").strip()
    genre = (data.get("genre") or "").strip()
    code = str(data.get("code") or "").strip()
    try:
        limit = max(1, min(int(data.get("limit", 60)), 300))
    except (TypeError, ValueError):
        limit = 60
    try:
        offset = max(0, int(data.get("offset", 0)))
    except (TypeError, ValueError):
        offset = 0
    where: list[str] = []
    params: list = []
    if code:
        where.append("s.code = ?")
        params.append(code)
    else:
        if q:
            where.append("(s.title LIKE ? OR s.genre LIKE ?)")
            params += [f"%{q}%", f"%{q}%"]
        if genre:
            where.append("(',' || REPLACE(COALESCE(s.genre, ''), ', ', ',') || ',') LIKE ?")
            params.append(f"%,{genre},%")
    category = str(data.get("category") or "").strip()
    if not code and category in ("series", "cartoon"):
        where.append("COALESCE(s.category, 'series') = ?")
        params.append(category)
    where_sql = ("WHERE " + " AND ".join(where)) if where else ""
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"""SELECT s.code, s.title, s.genre, s.description, s.is_vip, s.price_stars, s.added_at, COALESCE(s.category, 'series') AS category,
                      {poster_col('s.poster_url')},
                      (SELECT COUNT(*) FROM series_episodes e WHERE e.series_code = s.code) AS episode_count
               FROM series s {where_sql}
               ORDER BY s.added_at DESC LIMIT ? OFFSET ?""",
            params + [limit + 1, offset],
        )).fetchall()
    return web.json_response({
        "ok": True,
        "series": [dict(r) for r in rows[:limit]],
        "has_more": len(rows) > limit,
    })


@api_route
async def api_series_episodes(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = data.get("code")
    async with aiosqlite.connect(DB_PATH) as db:
        row = await (await db.execute(
            "SELECT COUNT(*) FROM series_episodes WHERE series_code = ?", (code,)
        )).fetchone()
    return web.json_response({"ok": True, "code": code, "episode_count": row[0] if row else 0})


# ---- YANGI: "Davom ettirish" — foydalanuvchi qaysi serialda, qaysi qismda to'xtagani ----
@api_route
async def api_continue_watching(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"""SELECT w.series_code AS code, w.last_episode, w.updated_at, s.title, {poster_col('s.poster_url')},
                      (SELECT COUNT(*) FROM series_episodes e WHERE e.series_code = w.series_code) AS episode_count
               FROM watch_progress w JOIN series s ON s.code = w.series_code
               WHERE w.user_id = ? ORDER BY w.updated_at DESC LIMIT 10""",
            (user_id,),
        )).fetchall()
    return web.json_response({"ok": True, "items": [dict(r) for r in rows]})


# ---- YANGI: Izoh/sharh qoldirish (kino va serial uchun) ----
@api_route
async def api_comments_list(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code, kind = data.get("code"), data.get("kind", "movie")
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            """SELECT id, username, text, created_at FROM movie_comments
               WHERE code = ? AND kind = ? ORDER BY created_at DESC LIMIT 50""",
            (code, kind),
        )).fetchall()
    return web.json_response({"ok": True, "comments": [dict(r) for r in rows]})


@api_route
async def api_comment_add(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code, kind, text = data.get("code"), data.get("kind", "movie"), (data.get("text") or "").strip()
    if not code or not text:
        return web.json_response({"ok": False, "message": "Izoh matnini kiriting"})
    text = text[:300]
    async with aiosqlite.connect(DB_PATH) as db:
        u = await (await db.execute("SELECT username, full_name FROM users WHERE user_id = ?", (user_id,))).fetchone()
        display = (u[0] if u and u[0] else (u[1] if u else None)) or "Foydalanuvchi"
        await db.execute(
            "INSERT INTO movie_comments (code, kind, user_id, username, text, created_at) VALUES (?, ?, ?, ?, ?, ?)",
            (code, kind, user_id, display, text, now_iso()),
        )
        await db.commit()
    await grant_achievement(user_id, "first_comment")
    return web.json_response({"ok": True})


# ---- YANGI: Referral liderbordi ----
@api_route
async def api_referral_leaderboard(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            """SELECT full_name, username, referral_count FROM users
               WHERE referral_count > 0 ORDER BY referral_count DESC LIMIT 10"""
        )).fetchall()
    return web.json_response({"ok": True, "leaders": [dict(r) for r in rows]})


# ---- YANGI: Admin statistikasi mini-appda (faqat Telegram orqali tasdiqlangan admin ko'radi) ----
@api_route
async def api_admin_stats(request: web.Request, user_id: int) -> web.Response:
    if user_id not in ADMIN_IDS:
        return web.json_response({"ok": False, "message": "Ruxsat yo'q"}, status=403)
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        total_users = (await (await db.execute("SELECT COUNT(*) c FROM users")).fetchone())["c"]
        try:
            vip_count = (await (await db.execute(
                "SELECT COUNT(*) c FROM users WHERE vip_until IS NOT NULL AND vip_until > ?",
                (now_iso(),),
            )).fetchone())["c"]
        except Exception:
            vip_count = 0
        total_movies = (await (await db.execute("SELECT COUNT(*) c FROM movies")).fetchone())["c"]
        total_series = (await (await db.execute("SELECT COUNT(*) c FROM series")).fetchone())["c"]
        pending_requests = (await (await db.execute(
            "SELECT COUNT(*) c FROM movie_requests WHERE status='pending'"
        )).fetchone())["c"]
        top_movies = await (await db.execute(
            "SELECT title, views FROM movies ORDER BY views DESC LIMIT 5"
        )).fetchall()
    return web.json_response({
        "ok": True,
        "total_users": total_users,
        "vip_count": vip_count,
        "total_movies": total_movies,
        "total_series": total_series,
        "pending_requests": pending_requests,
        "top_movies": [dict(r) for r in top_movies],
    })


# ---- YANGI: Promo-kod (mini-app'dan ham qo'llash mumkin) ----
@api_route
async def api_promo_redeem(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = (data.get("code") or "").strip().upper()
    if not code:
        return web.json_response({"ok": False, "message": "Kod kiritilmadi"})
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        promo = await (await db.execute("SELECT * FROM promo_codes WHERE code = ?", (code,))).fetchone()
        if not promo:
            return web.json_response({"ok": False, "message": "Bunday promo-kod topilmadi"})
        if promo["expires_at"] and promo["expires_at"] < now_iso():
            return web.json_response({"ok": False, "message": "Promo-kod muddati tugagan"})
        if promo["used_count"] >= promo["max_uses"]:
            return web.json_response({"ok": False, "message": "Promo-kod limitiga yetgan"})
        already = await (await db.execute(
            "SELECT 1 FROM promo_redemptions WHERE code = ? AND user_id = ?", (code, user_id)
        )).fetchone()
        if already:
            return web.json_response({"ok": False, "message": "Siz bu kodni allaqachon ishlatgansiz"})
        await db.execute("UPDATE promo_codes SET used_count = used_count + 1 WHERE code = ?", (code,))
        await db.execute(
            "INSERT INTO promo_redemptions (code, user_id, redeemed_at) VALUES (?, ?, ?)",
            (code, user_id, now_iso()),
        )
        await db.commit()
    await extend_vip(user_id, promo["vip_days"])
    return web.json_response({"ok": True, "vip_days": promo["vip_days"]})


# ---- YANGI: "Tez orada" bo'limi ----
@api_route
async def api_coming_soon_list(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"SELECT id, title, genre, {poster_col('poster_url')}, expected_date FROM coming_soon "
            "WHERE released_code IS NULL ORDER BY id DESC"
        )).fetchall()
        waiting = await (await db.execute(
            "SELECT coming_soon_id FROM coming_soon_waitlist WHERE user_id = ?", (user_id,)
        )).fetchall()
    return web.json_response({
        "ok": True,
        "items": [dict(r) for r in rows],
        "waiting_ids": [w[0] for w in waiting],
    })


@api_route
async def api_coming_soon_wait(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    cs_id = data.get("id")
    async with aiosqlite.connect(DB_PATH) as db:
        exists = await (await db.execute(
            "SELECT 1 FROM coming_soon_waitlist WHERE coming_soon_id = ? AND user_id = ?", (cs_id, user_id)
        )).fetchone()
        if exists:
            await db.execute(
                "DELETE FROM coming_soon_waitlist WHERE coming_soon_id = ? AND user_id = ?", (cs_id, user_id)
            )
            waiting = False
        else:
            await db.execute(
                "INSERT INTO coming_soon_waitlist (coming_soon_id, user_id, created_at) VALUES (?, ?, ?)",
                (cs_id, user_id, now_iso()),
            )
            waiting = True
        await db.commit()
    return web.json_response({"ok": True, "waiting": waiting})


# ---- YANGI: Yutuqlar (achievements) ----
@api_route
async def api_achievements_list(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        all_ach = await (await db.execute("SELECT * FROM achievements")).fetchall()
        earned = await (await db.execute(
            "SELECT achievement_id FROM user_achievements WHERE user_id = ?", (user_id,)
        )).fetchall()
    earned_ids = {e[0] for e in earned}
    items = [dict(a, earned=(a["id"] in earned_ids)) for a in all_ach]
    return web.json_response({"ok": True, "achievements": items})


# ---- MINI-APP API — Do'kon: Maxsus takliflar (narxi admin tomonidan belgilanadi) ----
@api_route
async def api_products_list(request: web.Request, user_id: int) -> web.Response:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT id, title, description, price_stars, emoji FROM shop_products "
            "WHERE active = 1 ORDER BY id DESC"
        )).fetchall()
    return web.json_response({
        "ok": True,
        "products": [dict(r) for r in rows],
        "seller_username": SELLER_CONTACT_USERNAME,
    })


@api_route
async def api_product_order(request: web.Request, user_id: int) -> web.Response:
    """Foydalanuvchi 'Sotib olish' bosganda: buyurtmani yozib qo'yamiz va
    adminga darhol xabar beramiz, keyin front-end SELLER_CONTACT_USERNAME
    havolasini ochadi — to'lov to'g'ridan-to'g'ri o'sha yerda kelishiladi."""
    data = await request.json()
    product_id = data.get("product_id")
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        product = await (await db.execute(
            "SELECT * FROM shop_products WHERE id = ?", (product_id,)
        )).fetchone()
        if not product:
            return web.json_response({"ok": False, "message": "Taklif topilmadi"})
        await db.execute(
            "INSERT INTO product_orders (product_id, user_id, created_at) VALUES (?, ?, ?)",
            (product_id, user_id, now_iso()),
        )
        await db.commit()
        u = await (await db.execute("SELECT full_name, username FROM users WHERE user_id = ?", (user_id,))).fetchone()
    bot_ref: Bot = request.app["bot"]
    buyer = f"@{u['username']}" if (u and u["username"]) else (u["full_name"] if u else str(user_id))
    for admin_id in ADMIN_IDS:
        try:
            await bot_ref.send_message(
                admin_id,
                f"🛒 <b>Yangi buyurtma!</b>\n{product['emoji']} {product['title']} — {product['price_stars']} ⭐\n"
                f"👤 {buyer} (ID: {user_id})",
            )
        except Exception:
            pass
    return web.json_response({"ok": True, "seller_username": SELLER_CONTACT_USERNAME})


# ---- YANGI MINI-APP API 5/5 — Do'kon: VIP/kino uchun invoice yaratish ----
@api_route
async def api_create_invoice(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    kind = data.get("kind")  # "vip" | "movie" | "donate"
    ref = str(data.get("ref", ""))

    if kind == "vip":
        plan = VIP_PLANS.get(ref)
        if not plan:
            return web.json_response({"ok": False, "message": "Noto'g'ri tarif"})
        title, desc, amount, payload = plan["label"], f"{plan['days']} kunlik VIP", plan["stars"], f"vip:{ref}"
    elif kind == "movie":
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            movie = await (await db.execute("SELECT * FROM movies WHERE code = ?", (ref,))).fetchone()
        if not movie or not movie["price_stars"]:
            return web.json_response({"ok": False, "message": "Kino topilmadi"})
        title, desc, amount, payload = movie["title"], "Eksklyuziv kino", movie["price_stars"], f"movie:{ref}"
    elif kind == "series":
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            s = await (await db.execute("SELECT * FROM series WHERE code = ?", (ref,))).fetchone()
        if not s or not s["price_stars"]:
            return web.json_response({"ok": False, "message": "Serial topilmadi"})
        title, desc, amount, payload = s["title"], "Eksklyuziv serial", s["price_stars"], f"series:{ref}"
    elif kind == "donate":
        amount = int(ref) if ref.isdigit() else 0
        if amount <= 0:
            return web.json_response({"ok": False, "message": "Noto'g'ri summa"})
        title, desc, payload = "Homiylik", "Botni qo'llab-quvvatlash", f"donate:{amount}"
    else:
        return web.json_response({"ok": False, "message": "Noto'g'ri turi"})

    link = await bot.create_invoice_link(
        title=title, description=desc, payload=payload,
        currency="XTR", prices=[LabeledPrice(label=title, amount=amount)],
    )
    return web.json_response({"ok": True, "link": link})


# ----------------------------------------------------------------------
# YANGI: KINO/SERIALNI ISHONCHLI YETKAZISH
# Ilgari mini-app kartochka bosilganda faqat Telegram.WebApp.sendData()ga
# tayanardi. Bu usul FAQAT reply-klaviatura yoki menyu tugmasi orqali
# ochilgan Mini App'larda kafolatlangan ishlaydi; ba'zi klientlarda
# (masalan o'zgartirilgan/mod Telegram ilovalari) sendData jim-jit
# ishlamay qoladi — natijada "so'rov yuborildi" degan xabar chiqadi-yu,
# lekin kino botdan kelmaydi. Shuning uchun endi mini-app to'g'ridan-to'g'ri
# shu API orqali (initData bilan tasdiqlangan) botga "yubor" buyrug'ini
# beradi — bu klient turi va ochilish usulidan qat'iy nazar ishlaydi.
# ----------------------------------------------------------------------
@api_route
async def api_deliver_movie(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = (data.get("code") or "").strip()
    if not code:
        return web.json_response({"ok": False, "message": "Kod ko'rsatilmagan"})
    try:
        await deliver_movie(user_id, user_id, code)
    except Exception:
        log.exception("api_deliver_movie xatolik")
        return web.json_response({"ok": False, "message": "Yuborishda xatolik. Botda /start bosing va qayta urinib ko'ring."})
    return web.json_response({"ok": True})


@api_route
async def api_deliver_episode(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = (data.get("code") or "").strip()
    try:
        ep = int(data.get("episode"))
    except (TypeError, ValueError):
        return web.json_response({"ok": False, "message": "Noto'g'ri qism raqami"})
    if not code:
        return web.json_response({"ok": False, "message": "Kod ko'rsatilmagan"})
    try:
        await deliver_series_episode(user_id, user_id, code, ep)
    except Exception:
        log.exception("api_deliver_episode xatolik")
        return web.json_response({"ok": False, "message": "Yuborishda xatolik. Botda /start bosing va qayta urinib ko'ring."})
    return web.json_response({"ok": True})


# ----------------------------------------------------------------------
# YANGI: ONLAYN KO'RISH — mini-app ichida to'g'ridan-to'g'ri video pleer.
# Xavfsizlik uchun kino fayliga bevosita havola hech qachon frontendga
# berilmaydi — faqat shu foydalanuvchi/kino/vaqt uchun imzolangan,
# muddati cheklangan token beriladi (make_stream_token/verify_stream_token).
# Kino (movies) va serial qismlari (series_episodes) uchun ham ishlaydi.
# ----------------------------------------------------------------------
@api_route
async def api_stream_token(request: web.Request, user_id: int) -> web.Response:
    data = await request.json()
    code = (data.get("code") or "").strip()
    if not code:
        return web.json_response({"ok": False, "message": "Kod ko'rsatilmagan"})

    ep_raw = data.get("episode")
    episode: int | None = None
    if ep_raw not in (None, ""):
        try:
            episode = int(ep_raw)
        except (TypeError, ValueError):
            return web.json_response({"ok": False, "message": "Noto'g'ri qism raqami"})

    if episode is not None:
        # ---- SERIAL QISMI ----
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            srow = await (await db.execute("SELECT * FROM series WHERE code = ?", (code,))).fetchone()
            erow = await (await db.execute(
                "SELECT file_id FROM series_episodes WHERE series_code = ? AND episode_number = ?",
                (code, episode),
            )).fetchone()
        if not srow or not erow or not erow["file_id"]:
            return web.json_response({"ok": False, "message": "Video topilmadi"})
        if srow["is_vip"] and not await is_vip(user_id):
            return web.json_response({"ok": False, "message": "💎 Faqat VIP a'zolar uchun onlayn ko'rish mavjud"})
        if srow["price_stars"] and srow["price_stars"] > 0 and not await is_vip(user_id):
            async with aiosqlite.connect(DB_PATH) as db:
                bought = await (await db.execute(
                    "SELECT 1 FROM movie_purchases WHERE user_id = ? AND movie_code = ?", (user_id, code)
                )).fetchone()
            if not bought:
                return web.json_response({"ok": False, "message": "⭐ Avval sotib oling", "need_purchase": True})
        token = make_stream_token(user_id, "episode", f"{code}:{episode}")
        return web.json_response(
            {"ok": True, "url": f"/stream/episode/{code}/{episode}?uid={user_id}&token={token}"}
        )

    # ---- KINO ----
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT * FROM movies WHERE code = ?", (code,))).fetchone()
    if not row or not row["file_id"]:
        return web.json_response({"ok": False, "message": "Video topilmadi"})
    if row["is_vip"] and not await is_vip(user_id):
        return web.json_response({"ok": False, "message": "💎 Faqat VIP a'zolar uchun onlayn ko'rish mavjud"})
    if row["price_stars"] and row["price_stars"] > 0 and not await is_vip(user_id):
        async with aiosqlite.connect(DB_PATH) as db:
            bought = await (await db.execute(
                "SELECT 1 FROM movie_purchases WHERE user_id = ? AND movie_code = ?", (user_id, code)
            )).fetchone()
        if not bought:
            return web.json_response({"ok": False, "message": "⭐ Avval sotib oling", "need_purchase": True})
    token = make_stream_token(user_id, "movie", code)
    return web.json_response({"ok": True, "url": f"/stream/movie/{code}?uid={user_id}&token={token}"})


async def serve_poster(request: web.Request) -> web.Response:
    """'tg:<file_id>' ko'rinishida saqlangan posterlarni Telegram
    serverlaridan olib, oddiy rasm sifatida qaytaradi."""
    file_id = request.match_info.get("file_id", "")
    try:
        file = await bot.get_file(file_id)
        buf = await bot.download_file(file.file_path)
        return web.Response(
            body=buf.read(), content_type="image/jpeg",
            headers={"Cache-Control": "public, max-age=604800"},
        )
    except Exception:
        return web.Response(status=404)


async def _proxy_telegram_file(request: web.Request, file_id: str) -> web.Response:
    """Berilgan Telegram file_id'ni <video> pleeriga Range so'rovlarini
    qo'llab-quvvatlab uzatadi (shu orqali videoda oldinga/orqaga surish
    ham ishlaydi). Kino va serial qismlari uchun umumiy yordamchi."""
    tg_file = await bot.get_file(file_id)
    file_url = f"https://api.telegram.org/file/bot{BOT_TOKEN}/{tg_file.file_path}"
    fwd_headers = {}
    range_header = request.headers.get("Range")
    if range_header:
        fwd_headers["Range"] = range_header
    async with aiohttp.ClientSession() as session:
        async with session.get(file_url, headers=fwd_headers) as upstream:
            resp = web.StreamResponse(status=upstream.status)
            for h in ("Content-Type", "Content-Length", "Content-Range"):
                if h in upstream.headers:
                    resp.headers[h] = upstream.headers[h]
            resp.headers.setdefault("Content-Type", "video/mp4")
            resp.headers["Accept-Ranges"] = "bytes"
            await resp.prepare(request)
            async for chunk in upstream.content.iter_chunked(256 * 1024):
                await resp.write(chunk)
            return resp


async def serve_stream(request: web.Request) -> web.Response:
    """Kino faylini Telegram serveridan olib, mini-app'dagi <video>
    pleeriga uzatadi."""
    code = request.match_info.get("code", "")
    try:
        uid = int(request.query.get("uid", "0"))
    except ValueError:
        return web.Response(status=403)
    token = request.query.get("token", "")
    if not verify_stream_token(token, uid, "movie", code):
        return web.Response(status=403, text="Token yaroqsiz yoki muddati o'tgan")
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute("SELECT file_id FROM movies WHERE code = ?", (code,))).fetchone()
    if not row or not row["file_id"]:
        return web.Response(status=404)
    return await _proxy_telegram_file(request, row["file_id"])


async def serve_stream_episode(request: web.Request) -> web.Response:
    """Serial qismini Telegram serveridan olib, mini-app'dagi <video>
    pleeriga uzatadi (kino uchun ishlagan onlayn ko'rish endi serial
    qismlari uchun ham xuddi shunday ishlaydi)."""
    code = request.match_info.get("code", "")
    try:
        ep = int(request.match_info.get("ep", "0"))
        uid = int(request.query.get("uid", "0"))
    except ValueError:
        return web.Response(status=403)
    token = request.query.get("token", "")
    if not verify_stream_token(token, uid, "episode", f"{code}:{ep}"):
        return web.Response(status=403, text="Token yaroqsiz yoki muddati o'tgan")
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        row = await (await db.execute(
            "SELECT file_id FROM series_episodes WHERE series_code = ? AND episode_number = ?", (code, ep)
        )).fetchone()
    if not row or not row["file_id"]:
        return web.Response(status=404)
    return await _proxy_telegram_file(request, row["file_id"])


# ----------------------------------------------------------------------
# WEB APP QURISH (aiohttp) — mini app + webhook + API'lar
# ----------------------------------------------------------------------
async def serve_mini_app(request: web.Request) -> web.Response:
    try:
        with open(HTML_FILE, "r", encoding="utf-8") as f:
            html = f.read()
    except FileNotFoundError:
        return web.Response(text="mini_app.html topilmadi", status=500)
    return web.Response(text=html, content_type="text/html")


async def health(request: web.Request) -> web.Response:
    return web.Response(text="ok")


# ======================================================================
# YANGI: KANALGA AVTOMATIK JOYLASH — endi BOT ICHIDAN sozlanadi
#   • Bir nechta kanal, har biriga qaysi turlar (kino / serial / multfilm) ketishi tanlanadi
#   • Post joylanmasa — sababi adminga aniq yoziladi (jim qolmaydi)
#   • /channels, /setchannel, /postcheck — tugmalar: /admin → 📡 Post kanallari
# ======================================================================
START_TIME = time.time()

POST_KIND_KEYS = ("movie", "series", "cartoon")
POST_KIND_LABELS = {"movie": "🎬 Kino", "series": "📺 Serial", "cartoon": "🧸 Multfilm"}


def kinds_set(raw) -> "set[str]":
    raw = (raw or "").strip().lower()
    if not raw or raw == "all":
        return set(POST_KIND_KEYS)
    return {k for k in raw.split(",") if k in POST_KIND_KEYS}


def kinds_text(kinds: "set[str]") -> str:
    return ",".join(k for k in POST_KIND_KEYS if k in kinds)


def kinds_pretty(kinds: "set[str]") -> str:
    if kinds == set(POST_KIND_KEYS):
        return "hammasi"
    return ", ".join(POST_KIND_LABELS[k] for k in POST_KIND_KEYS if k in kinds) or "hech narsa"


async def get_setting(key: str, default: "str | None" = None) -> "str | None":
    try:
        async with aiosqlite.connect(DB_PATH) as db:
            row = await (await db.execute("SELECT value FROM bot_settings WHERE key = ?", (key,))).fetchone()
        return row[0] if row and row[0] is not None else default
    except Exception:
        return default


async def set_setting(key: str, value: str) -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            "INSERT INTO bot_settings (key, value) VALUES (?, ?) ON CONFLICT(key) DO UPDATE SET value = excluded.value",
            (key, value),
        )
        await db.commit()


async def get_post_channels(active_only: bool = False) -> "list[dict]":
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            "SELECT id, chat_id, title, kinds, active FROM post_channels"
            + (" WHERE active = 1" if active_only else "") + " ORDER BY id"
        )).fetchall()
    return [dict(r) for r in rows]


async def get_post_targets(cat_key: str) -> "list[dict]":
    """Shu turdagi post qaysi kanallarga ketishi. Bazada kanal bo'lmasa — eski POST_CHANNEL_ID (env) ishlatiladi."""
    all_rows = await get_post_channels()
    if not all_rows:
        return [{"id": None, "chat_id": POST_CHANNEL_ID, "title": POST_CHANNEL_ID, "kinds": "all"}] if POST_CHANNEL_ID else []
    return [r for r in all_rows if r["active"] and cat_key in kinds_set(r["kinds"])]


def explain_tg_error(e: Exception) -> str:
    s = str(e).lower()
    if "chat not found" in s:
        return "kanal topilmadi — ID/username noto'g'ri yoki bot kanalga qo'shilmagan"
    if "bot is not a member" in s or "bot was kicked" in s or "bot was blocked" in s:
        return "bot bu kanalda yo'q (a'zo emas yoki chiqarib yuborilgan)"
    if ("not enough rights" in s or "administrator rights" in s or "have no rights" in s
            or "need to be" in s or "can't post" in s or "not allowed" in s):
        return "botda «Xabar joylash» (Post messages) huquqi yo'q — kanalda botni admin qiling"
    if "wrong file identifier" in s or "wrong remote file" in s or "failed to get http url" in s:
        return "poster rasmi yaroqsiz"
    if "can't parse entities" in s:
        return "matnda noto'g'ri belgilar bor"
    if "too many requests" in s or "retry after" in s:
        return "Telegram vaqtincha cheklov qo'ydi (keyinroq /repost qiling)"
    return str(e)[:160]


async def get_post_button_text() -> str:
    return (await get_setting("post_button_text")) or CHANNEL_BUTTON_TEXT


def _post_caption(kind: str, code: str, title: str, genre, price_stars: int, category: str,
                  description, ep_count, new_eps, bot_username: str, info: "dict | None" = None) -> str:
    head = ""
    episode_line = None
    if new_eps:
        x, y = new_eps
        head = "🆕 <b>Yangi qism qo'shildi!</b>\n\n" if x == y else "🆕 <b>Yangi qismlar qo'shildi!</b>\n\n"
    if kind == "series" and ep_count:
        if new_eps:
            x, y = new_eps
            episode_line = f"📼 Qism: {x}" if x == y else f"📼 Qismlar: {x}–{y} (jami {ep_count} ta)"
        else:
            episode_line = f"📼 Qismlar: {ep_count} ta"
    info = info or {"language": "O'zbek tilida", "country": "Uzb", "quality": "1080p", "year": utcnow().year}
    return card_text(title, genre, info, category, kind, code=code, price_stars=price_stars,
                     head=head, episode_line=episode_line)


async def _send_one_post(chat_ref, caption: str, poster_url, markup, fallback_markup=None) -> "int | None":
    """Bitta kanalga yuboradi; poster ishlamasa — rasmsiz matn bilan qayta urinadi. message_id qaytaradi."""
    async def _go(mk):
        if poster_url and poster_url.startswith("tg:"):
            try:
                return await bot.send_photo(chat_ref, poster_url.removeprefix("tg:"), caption=caption, reply_markup=mk)
            except TelegramBadRequest as e:
                if "file" not in str(e).lower() and "photo" not in str(e).lower():
                    raise
        elif poster_url and poster_url.startswith(("http://", "https://")):
            try:
                return await bot.send_photo(chat_ref, poster_url, caption=caption, reply_markup=mk)
            except TelegramBadRequest as e:
                if "file" not in str(e).lower() and "photo" not in str(e).lower() and "url" not in str(e).lower():
                    raise
        return await bot.send_message(chat_ref, caption, reply_markup=mk)

    async def _try(mk):
        try:
            return await _go(mk)
        except TelegramBadRequest as e:
            low = str(e).lower()
            if fallback_markup is not None and mk is not fallback_markup and ("button" in low or "style" in low or "reply markup" in low):
                return await _go(fallback_markup)   # yashil tugma qabul qilinmasa — oddiy tugma
            raise

    try:
        msg = await _try(markup)
    except TelegramRetryAfter as e:
        await asyncio.sleep(min(int(e.retry_after) + 1, 30))
        msg = await _try(markup)
    return getattr(msg, "message_id", None)


async def post_content_to_channel(
    kind: str, code: str, title: str, genre, price_stars: int, poster_url,
    *, category: "str | None" = None, description: "str | None" = None,
    ep_count: "int | None" = None, new_eps: "tuple[int, int] | None" = None,
    notify_user_id: "int | None" = None,
) -> dict:
    """kind: 'movie' | 'series'; category: 'movie' | 'series' | 'cartoon'.
    Qaytaradi: {'sent': [kanal nomlari], 'failed': [(kanal, sabab)], 'none_configured': bool, 'filtered_out': bool}"""
    category = category or ("series" if kind == "series" else "movie")
    cat_key = "cartoon" if category == "cartoon" else ("series" if kind == "series" else "movie")
    res: dict = {"sent": [], "failed": [], "none_configured": False, "filtered_out": False, "cat_key": cat_key}
    targets = await get_post_targets(cat_key)
    if not targets:
        configured = await get_post_channels(active_only=True)
        res["none_configured"] = not configured
        res["filtered_out"] = bool(configured)
        return res
    try:
        me = await bot.get_me()
    except Exception as e:
        res["failed"].append(("bot", explain_tg_error(e)))
        return res
    payload = f"series_{code}-ep{new_eps[0]}" if (kind == "series" and new_eps) else f"{'series' if kind == 'series' else 'movie'}_{code}"
    link = f"https://t.me/{me.username}?start={payload}"
    info = None
    try:
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            row = await (await db.execute(
                f"SELECT * FROM {'series' if kind == 'series' else 'movies'} WHERE code = ?", (code,)
            )).fetchone()
        if row:
            info = item_info(row)
    except Exception:
        log.exception("Post uchun kino ma'lumotini o'qib bo'lmadi")
    caption = _post_caption(kind, code, title, genre, price_stars, category, description, ep_count, new_eps, me.username, info)
    btn_text = await get_post_button_text()
    markup = post_markup(btn_text, link, styled=True)
    plain_markup = post_markup(btn_text, link, styled=False)
    for ch in targets:
        name = str(ch.get("title") or ch["chat_id"])
        try:
            await _send_one_post(_chat_ref(ch["chat_id"]), caption, poster_url, markup, plain_markup)
            res["sent"].append(name)
        except Exception as e:
            log.exception("Kanalga joylashda xatolik (%s: %s → %s)", kind, code, ch["chat_id"])
            res["failed"].append((name, explain_tg_error(e)))
        await asyncio.sleep(0.3)
    return res


def format_post_report(res: dict) -> str:
    if res.get("none_configured"):
        return (
            "📡 Kanalga post joylanmadi: post kanali sozlanmagan.\n"
            "Sozlash: /admin → 📡 Post kanallari (yoki /setchannel)."
        )
    if res.get("filtered_out"):
        return (
            f"📡 Kanalga post joylanmadi: hech bir kanalda «{POST_KIND_LABELS.get(res.get('cat_key'), '')}» turi yoqilmagan.\n"
            "Yoqish: /channels"
        )
    lines = []
    if res["sent"]:
        lines.append("📡 Kanalga joylandi: " + ", ".join(f"<b>{html_escape(n)}</b>" for n in res["sent"]))
    for name, why in res["failed"]:
        lines.append(f"❌ <b>{html_escape(name)}</b> — joylanmadi: {html_escape(why)}")
    if res["failed"]:
        lines.append("🔧 Tekshirish va tuzatish: /postcheck — keyin /repost &lt;kod&gt;")
    return "\n".join(lines) or "📡 Joylanadigan kanal topilmadi."


# ---- Kanal huquqlarini tekshirish ------------------------------------------------
async def check_post_channel(chat_id) -> dict:
    """{'ok': bool, 'title': str|None, 'problem': str|None, 'fix': str|None}"""
    out = {"ok": False, "title": None, "problem": None, "fix": None}
    ref = _chat_ref(chat_id)
    try:
        chat = await bot.get_chat(ref)
    except Exception as e:
        out["problem"] = explain_tg_error(e)
        out["fix"] = "Botni kanalga qo'shing, ADMIN qiling va kanal ID/@username to'g'riligini tekshiring."
        return out
    out["title"] = getattr(chat, "title", None) or str(chat_id)
    try:
        me = await bot.get_me()
        member = await bot.get_chat_member(ref, me.id)
    except Exception as e:
        out["problem"] = explain_tg_error(e)
        out["fix"] = "Botni kanalga ADMIN qilib qo'shing."
        return out
    status = getattr(member, "status", "")
    if status == "creator":
        out["ok"] = True
    elif status == "administrator":
        if getattr(chat, "type", "") == "channel" and getattr(member, "can_post_messages", None) is False:
            out["problem"] = "bot admin, lekin «Post messages» huquqi o'chiq"
            out["fix"] = "Kanal → Administratorlar → bot → «Xabar joylash» ni yoqing."
        else:
            out["ok"] = True
    else:
        out["problem"] = "bot bu kanalda ADMIN emas"
        out["fix"] = "Kanal → Administratorlar → botni qo'shing va «Xabar joylash» huquqini bering."
    return out


async def verify_post_channels_report(only_problems: bool = False) -> "tuple[str, bool]":
    """(matn, hammasi_joyidami). Kanal yo'q bo'lsa ham matn qaytaradi."""
    channels = await get_post_channels()
    if not channels:
        if POST_CHANNEL_ID:
            channels = [{"id": None, "chat_id": POST_CHANNEL_ID, "title": POST_CHANNEL_ID, "kinds": "all", "active": 1}]
        else:
            return "📡 Post kanali sozlanmagan. /admin → 📡 Post kanallari.", False
    lines, all_ok = [], True
    for ch in channels:
        r = await check_post_channel(ch["chat_id"])
        all_ok = all_ok and r["ok"] or not ch["active"]
        name = html_escape(str(r["title"] or ch.get("title") or ch["chat_id"]))
        if r["ok"]:
            if not only_problems:
                lines.append(f"✅ <b>{name}</b> — tayyor ({kinds_pretty(kinds_set(ch['kinds']))})" + ("" if ch["active"] else " · 🔕 o'chiq"))
        else:
            lines.append(f"❌ <b>{name}</b> — {html_escape(r['problem'] or '?')}\n   🔧 {html_escape(r['fix'] or '')}")
    return "\n".join(lines), all_ok


# ---- Kanal qo'shish (forward yoki @username / ID) ----------------------------------
class AddPostChannelStates(StatesGroup):
    chat = State()


ADDPOST_PROMPT = (
    "📡 <b>Post kanali qo'shish</b> — kino/serial/multfilm postlari shu kanalga tushadi.\n\n"
    "1️⃣ Kanaldan istalgan postni shu yerga <b>forward</b> qiling, yoki\n"
    "2️⃣ yozing: <code>@mychannel</code> / <code>-1001234567890</code>\n\n"
    "⚠️ Avval botni kanalga <b>ADMIN</b> qiling va «Xabar joylash» huquqini bering.\n"
    "Bekor qilish: /cancel"
)


def can_manage_channels(uid: int) -> bool:
    return uid in ADMIN_IDS  # egasi + to'liq adminlar


async def _channels_panel() -> "tuple[str, InlineKeyboardMarkup]":
    channels = await get_post_channels()
    kb = InlineKeyboardBuilder()
    if not channels:
        text = "📡 <b>Post kanallari</b>\n\nHali kanal qo'shilmagan" + (
            f" (hozir env POST_CHANNEL_ID ishlayapti: <code>{html_escape(POST_CHANNEL_ID)}</code>)." if POST_CHANNEL_ID else "."
        )
    else:
        lines = ["📡 <b>Post kanallari</b>", "Har kanal uchun qaysi turlar tushishini tugmalar bilan tanlang:\n"]
        for ch in channels:
            ks = kinds_set(ch["kinds"])
            lines.append(
                f"{'🔔' if ch['active'] else '🔕'} <b>{html_escape(str(ch['title']))}</b> "
                f"(<code>{html_escape(str(ch['chat_id']))}</code>) — {kinds_pretty(ks)}"
            )
            cid = ch["id"]
            for k in POST_KIND_KEYS:
                kb.button(text=("✅ " if k in ks else "▫️ ") + POST_KIND_LABELS[k], callback_data=f"adm2:chk:{cid}:{k}")
            kb.button(text="🔕 O'chirish" if ch["active"] else "🔔 Yoqish", callback_data=f"adm2:chon:{cid}")
            kb.button(text="🧪 Test post", callback_data=f"adm2:chtest:{cid}")
            kb.button(text="🗑 Olib tashlash", callback_data=f"adm2:chdel:{cid}")
        text = "\n".join(lines)
    kb.button(text="➕ Kanal qo'shish", callback_data="adm2:chadd")
    kb.button(text="🩺 Tekshirish", callback_data="adm2:chcheck")
    kb.button(text="✏️ Tugma matni", callback_data="adm2:chbtn")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    rows = [3, 3] * len(channels) + [1, 2, 1]
    kb.adjust(*rows)
    return text, kb.as_markup()


@admin_router.message(Command("channels"))
async def cmd_channels(message: Message) -> None:
    if not can_manage_channels(message.from_user.id):
        return
    text, kb = await _channels_panel()
    await message.answer(text, reply_markup=kb)


@admin_router.message(Command("setchannel"))
async def cmd_setchannel(message: Message, state: FSMContext) -> None:
    if not can_manage_channels(message.from_user.id):
        return
    await state.clear()
    await state.set_state(AddPostChannelStates.chat)
    await message.answer(ADDPOST_PROMPT)


@admin_router.message(Command("postcheck"))
async def cmd_postcheck(message: Message) -> None:
    if not can_manage_channels(message.from_user.id):
        return
    await message.answer("🩺 Tekshirilmoqda...")
    text, ok = await verify_post_channels_report()
    await message.answer(text + ("\n\n✅ Hammasi joyida — postlar avtomatik joylanadi." if ok else ""))


@admin_router.message(Command("setbtn"))
async def cmd_setbtn(message: Message, command: CommandObject) -> None:
    """/setbtn <matn> — kanal postidagi tugma yozuvini o'zgartirish (faqat egasi/to'liq admin)."""
    if not can_manage_channels(message.from_user.id):
        return
    if not command.args:
        await message.answer(f"Hozirgi tugma: <b>{html_escape(await get_post_button_text())}</b>\nO'zgartirish: <code>/setbtn 🎬 Tomosha qilish</code>")
        return
    await set_setting("post_button_text", command.args.strip()[:40])
    await message.answer(f"✅ Tugma matni: <b>{html_escape(command.args.strip()[:40])}</b>")


async def _add_post_channel(message: Message, state: FSMContext, chat_id: str, title: str) -> None:
    await state.clear()
    r = await check_post_channel(chat_id)
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute(
            "INSERT OR IGNORE INTO post_channels (chat_id, title, kinds, active, added_at) VALUES (?, ?, 'movie,series,cartoon', 1, ?)",
            (str(chat_id), str(r["title"] or title), now_iso()),
        )
        await db.commit()
        added = cur.rowcount > 0
    head = (
        f"✅ Kanal qo'shildi: <b>{html_escape(str(r['title'] or title))}</b>" if added
        else f"ℹ️ <b>{html_escape(str(r['title'] or title))}</b> allaqachon ro'yxatda."
    )
    status = "✅ Bot kanalda ishlay oladi — post joylash tayyor." if r["ok"] else (
        f"❌ Muammo: {html_escape(r['problem'] or '?')}\n🔧 {html_escape(r['fix'] or '')}"
    )
    kb = InlineKeyboardBuilder()
    kb.button(text="📡 Kanallar paneli", callback_data="adm2:channels")
    await message.answer(f"{head}\n{status}\n\nTurlarni sozlash va test post: /channels", reply_markup=kb.as_markup())


@admin_router.message(AddPostChannelStates.chat)
async def admin_addpostchannel_chat(message: Message, state: FSMContext) -> None:
    fwd = _extract_forwarded_chat(message)
    if fwd is not None:
        await _add_post_channel(message, state, str(fwd.id), getattr(fwd, "title", None) or str(fwd.id))
        return
    ref = normalize_channel_ref(message.text or "")
    if not ref:
        await message.answer(
            "❌ Yaroqsiz. <code>@kanal_username</code>, <code>-1001234567890</code> yuboring yoki kanaldan post forward qiling.\n"
            "Bekor qilish: /cancel"
        )
        return
    r = await check_post_channel(ref)
    if r["title"] is None:
        await message.answer(
            f"❌ Bot bu kanalni topa olmadi: {html_escape(r['problem'] or '?')}\n"
            "Botni kanalga ADMIN qilib qo'shing va qayta yuboring. Bekor qilish: /cancel"
        )
        return
    await _add_post_channel(message, state, ref, r["title"])


class PostBtnStates(StatesGroup):
    text = State()


@admin_router.message(PostBtnStates.text)
async def admin_postbtn_text(message: Message, state: FSMContext) -> None:
    t = (message.text or "").strip()
    if not t:
        await message.answer("❌ Matn yuboring (masalan: 🎬 Tomosha qilish) yoki /cancel")
        return
    await state.clear()
    await set_setting("post_button_text", t[:40])
    await message.answer(f"✅ Tugma matni: <b>{html_escape(t[:40])}</b>")


# ======================================================================
# YANGI: ADMIN YOLLASH (faqat EGASI) — bot ichidan admin qo'shish/olib tashlash
#   Rollar:  🛠 kontent admin — kino/serial/multfilm/qism, kanalga post, so'rovlar, majburiy obuna
#            👨‍💼 to'liq admin — yuqoridagilar + statistika, ban/VIP, xabar yuborish, do'kon, promo, post kanallari
#   Egasi — Railway'dagi ADMIN_IDS: yuqoridagilar + admin yollash, zaxira/tiklash, CSV eksport
# ======================================================================
ROLE_LABELS = {"content": "🛠 Kontent admin", "full": "👨‍💼 To'liq admin"}


def is_owner(uid: int) -> bool:
    return uid in OWNER_IDS


def _apply_staff_role(uid: int, role: "str | None") -> None:
    """Xotiradagi to'plamlarni yangilaydi (barcha tekshiruvlar shularga tayanadi)."""
    if uid in OWNER_IDS:
        return
    ADMIN_IDS.discard(uid)
    MODERATOR_IDS.discard(uid)
    if role == "full":
        ADMIN_IDS.add(uid)
    elif role == "content":
        MODERATOR_IDS.add(uid)
    STAFF_IDS.clear()
    STAFF_IDS.update(ADMIN_IDS | MODERATOR_IDS)


async def load_staff_from_db() -> None:
    """Bazadagi yollangan adminlarni xotiraga yuklaydi (har ishga tushishda va tiklashdan keyin)."""
    try:
        async with aiosqlite.connect(DB_PATH) as db:
            rows = await (await db.execute("SELECT user_id, role FROM staff_members")).fetchall()
    except Exception:
        log.exception("Adminlar ro'yxatini bazadan o'qib bo'lmadi")
        return
    ADMIN_IDS.clear()
    ADMIN_IDS.update(OWNER_IDS)
    MODERATOR_IDS.clear()
    MODERATOR_IDS.update(ENV_MODERATOR_IDS)
    STAFF_IDS.clear()
    STAFF_IDS.update(ADMIN_IDS | MODERATOR_IDS)
    for uid, role in rows:
        _apply_staff_role(int(uid), role)


async def resolve_user_ref(text: str) -> "tuple[int | None, str]":
    """'123456', '@username' → (user_id, ko'rinadigan nom). Username bo'yicha faqat botga /start bosganlar topiladi."""
    t = (text or "").strip()
    if re.fullmatch(r"\d{4,15}", t):
        uid = int(t)
        name = str(uid)
        async with aiosqlite.connect(DB_PATH) as db:
            row = await (await db.execute("SELECT full_name, username FROM users WHERE user_id = ?", (uid,))).fetchone()
        if row:
            name = row[0] or (f"@{row[1]}" if row[1] else str(uid))
        return uid, name
    m = re.fullmatch(r"@?([A-Za-z][A-Za-z0-9_]{3,31})", t)
    if m:
        async with aiosqlite.connect(DB_PATH) as db:
            row = await (await db.execute(
                "SELECT user_id, full_name FROM users WHERE LOWER(username) = LOWER(?)", (m.group(1),)
            )).fetchone()
        if row:
            return int(row[0]), row[1] or f"@{m.group(1)}"
    return None, ""


def _extract_forwarded_user(message: Message):
    origin = getattr(message, "forward_origin", None)
    u = getattr(origin, "sender_user", None) if origin is not None else None
    return u or getattr(message, "forward_from", None)


async def hire_staff(uid: int, name: str, role: str, by: int) -> str:
    if uid in OWNER_IDS:
        return "ℹ️ Bu foydalanuvchi — bot egasi, uni o'zgartirib bo'lmaydi."
    async with aiosqlite.connect(DB_PATH) as db:
        await db.execute(
            """INSERT INTO staff_members (user_id, role, name, added_by, added_at) VALUES (?, ?, ?, ?, ?)
               ON CONFLICT(user_id) DO UPDATE SET role = excluded.role, name = excluded.name""",
            (uid, role, name, by, now_iso()),
        )
        await db.commit()
    _apply_staff_role(uid, role)
    await refresh_commands_for(uid)
    notified = True
    try:
        await bot.send_message(
            uid,
            f"🎉 Siz <b>Luxor Cinema</b> botida <b>{ROLE_LABELS[role]}</b> etib tayinlandingiz!\n\n"
            "🛠 /admin — tugmali panel (kino, serial, multfilm qo'shish va boshqalar)\n"
            "📖 /adminhelp — barcha buyruqlar",
        )
    except Exception:
        notified = False
    return (
        f"✅ <b>{html_escape(name)}</b> (<code>{uid}</code>) — {ROLE_LABELS[role]} qilindi."
        + ("" if notified else "\n⚠️ Unga xabar yuborib bo'lmadi: u botga avval /start bosishi kerak. Bosgach /admin ishlaydi.")
    )


async def fire_staff(uid: int) -> str:
    if uid in OWNER_IDS:
        return "ℹ️ Bot egasini olib tashlab bo'lmaydi."
    async with aiosqlite.connect(DB_PATH) as db:
        cur = await db.execute("DELETE FROM staff_members WHERE user_id = ?", (uid,))
        await db.commit()
    was_env_mod = uid in ENV_MODERATOR_IDS
    _apply_staff_role(uid, "content" if was_env_mod else None)
    await refresh_commands_for(uid, remove=not was_env_mod)
    if not cur.rowcount:
        return "ℹ️ Bu foydalanuvchi yollangan adminlar ro'yxatida yo'q." + (
            "\n(U Railway'dagi MODERATOR_IDS orqali berilgan — o'sha yerdan olib tashlang.)" if was_env_mod else ""
        )
    try:
        await bot.send_message(uid, "ℹ️ Sizning admin huquqlaringiz olib tashlandi.")
    except Exception:
        pass
    return f"🗑 <code>{uid}</code> admin lavozimidan olib tashlandi."


async def list_staff() -> "list[dict]":
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute("SELECT user_id, role, name FROM staff_members ORDER BY added_at")).fetchall()
    return [dict(r) for r in rows]


async def _team_panel() -> "tuple[str, InlineKeyboardMarkup]":
    staff = await list_staff()
    lines = ["👑 <b>Jamoa (adminlar)</b>", "", "👑 Egalar: " + ", ".join(f"<code>{i}</code>" for i in sorted(OWNER_IDS))]
    env_mods = sorted(ENV_MODERATOR_IDS - OWNER_IDS)
    if env_mods:
        lines.append("🛠 Env moderatorlar: " + ", ".join(f"<code>{i}</code>" for i in env_mods))
    kb = InlineKeyboardBuilder()
    if staff:
        lines.append("")
        for s in staff:
            lines.append(f"{ROLE_LABELS.get(s['role'], s['role'])} — {html_escape(s['name'] or '')} (<code>{s['user_id']}</code>)")
            other = "full" if s["role"] == "content" else "content"
            kb.button(text=f"🔁 {(s['name'] or str(s['user_id']))[:14]} → {ROLE_LABELS[other].split(' ', 1)[1]}", callback_data=f"adm2:role:{s['user_id']}")
            kb.button(text="🗑 Olib tashlash", callback_data=f"adm2:fire:{s['user_id']}")
    else:
        lines.append("\nHali yollangan admin yo'q.")
    kb.button(text="➕ Kontent admin yollash", callback_data="adm2:hire:content")
    kb.button(text="➕ To'liq admin yollash", callback_data="adm2:hire:full")
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:main")
    kb.adjust(*([2] * len(staff) + [1, 1, 1]))
    return "\n".join(lines), kb.as_markup()


class HireStates(StatesGroup):
    who = State()


HIRE_PROMPT = (
    "➕ <b>{role}</b> yollash.\n\n"
    "Quyidagilardan birini yuboring:\n"
    "• foydalanuvchi <b>ID</b> raqami (masalan <code>123456789</code>)\n"
    "• <code>@username</code> (u botga /start bosgan bo'lsa)\n"
    "• yoki uning biror xabarini shu yerga <b>forward</b> qiling\n\n"
    "💡 ID bilish: u @userinfobot ga /start yozsin.\nBekor qilish: /cancel"
)


@admin_router.message(Command("addadmin"))
async def cmd_addadmin(message: Message, command: CommandObject) -> None:
    """/addadmin <id|@username> [full|content]  — faqat bot egasi."""
    if not is_owner(message.from_user.id):
        return
    parts = (command.args or "").split()
    if not parts:
        await message.answer(
            "Foydalanish:\n<code>/addadmin 123456789</code> — kontent admin\n"
            "<code>/addadmin 123456789 full</code> — to'liq admin\n"
            "<code>/addadmin @username</code>\n\nYoki tugmalar bilan: /admin → 👑 Jamoa"
        )
        return
    role = "full" if len(parts) > 1 and parts[1].lower() in ("full", "toliq", "to'liq") else "content"
    uid, name = await resolve_user_ref(parts[0])
    if uid is None:
        await message.answer("❌ Foydalanuvchi topilmadi. ID raqamini yuboring (yoki u botga /start bosgan bo'lsin).")
        return
    await message.answer(await hire_staff(uid, name, role, message.from_user.id))


@admin_router.message(Command("deladmin"))
async def cmd_deladmin(message: Message, command: CommandObject) -> None:
    if not is_owner(message.from_user.id):
        return
    if not command.args:
        await message.answer("Foydalanish: <code>/deladmin 123456789</code> yoki <code>/deladmin @username</code>")
        return
    uid, _ = await resolve_user_ref(command.args.strip().split()[0])
    if uid is None:
        await message.answer("❌ Foydalanuvchi topilmadi.")
        return
    await message.answer(await fire_staff(uid))


@admin_router.message(Command("admins"))
async def cmd_admins(message: Message) -> None:
    if not is_owner(message.from_user.id):
        return
    text, kb = await _team_panel()
    await message.answer(text, reply_markup=kb)


@admin_router.message(HireStates.who)
async def admin_hire_who(message: Message, state: FSMContext) -> None:
    data = await state.get_data()
    role = data.get("role") or "content"
    fu = _extract_forwarded_user(message)
    if fu is not None:
        uid, name = fu.id, fu.full_name
    else:
        uid, name = await resolve_user_ref(message.text or "")
        if uid is None:
            await message.answer("❌ Topilmadi. ID raqami, @username yuboring yoki uning xabarini forward qiling. Bekor qilish: /cancel")
            return
    await state.clear()
    await message.answer(await hire_staff(uid, name, role, message.from_user.id))


# ---- "/" menyusi: har kim o'z darajasiga mos buyruqlarni ko'radi ---------------------
def commands_for(uid: int) -> "list[BotCommand]":
    cmds = list(STAFF_COMMANDS)
    if uid in ADMIN_IDS:
        cmds += ADMIN_ONLY_COMMANDS + CHANNEL_COMMANDS
    if uid in OWNER_IDS:
        cmds += OWNER_COMMANDS
    return [BotCommand(command=c, description=d) for c, d in cmds]


async def refresh_commands_for(uid: int, remove: bool = False) -> None:
    try:
        if remove:
            await bot.delete_my_commands(scope=BotCommandScopeChat(chat_id=uid))
        else:
            await bot.set_my_commands(commands_for(uid), scope=BotCommandScopeChat(chat_id=uid))
    except Exception:
        log.info("Buyruqlar menyusini yangilab bo'lmadi (user=%s)", uid)


# ---- Tizim holati (egasi) --------------------------------------------------------------
async def build_status_text() -> str:
    c = await db_counts()
    up = int(time.time() - START_TIME)
    d, rem = divmod(up, 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    db_dir = os.path.dirname(os.path.abspath(DB_PATH))
    chans, ok = await verify_post_channels_report()
    configured = bool(await get_post_channels()) or bool(POST_CHANNEL_ID)
    chan_state = ("✅ hammasi joyida" if ok else "⚠️ muammo bor") if configured else "⚠️ sozlanmagan"
    fs = await get_force_sub_channels()
    staff = await list_staff()
    return (
        "🩺 <b>Tizim holati</b>\n\n"
        f"⏱ Ishlayapti: {d} kun {h} soat {m} daqiqa\n"
        f"🌐 Rejim: {'webhook' if WEBHOOK_HOST else 'polling'}\n"
        f"🗄 Baza: <code>{html_escape(DB_PATH)}</code> — " + ("Volume ✅" if os.path.ismount(db_dir) else "Volume EMAS ⚠️") + "\n"
        f"{counts_line(c)}\n"
        f"👥 Adminlar: {len(OWNER_IDS)} ega, {len(staff)} yollangan\n"
        f"🔒 Majburiy obuna kanallari: {len(fs)} ta\n\n"
        f"📡 <b>Post kanallari</b> ({chan_state}):\n{chans}"
    )


@admin_router.message(Command("status"))
async def cmd_status(message: Message) -> None:
    if not is_owner(message.from_user.id):
        return
    await message.answer(await build_status_text())


# ======================================================================
# YANGI ADMIN-PANEL TUGMALARI (callback prefiksi: adm2:)
# ======================================================================
def _icon_for(category: "str | None", table: str) -> str:
    if category == "cartoon":
        return "🧸"
    return "📺" if table == "series" else "🎬"


_PICK_ACTIONS = {
    # amal: (jadval, sarlavha)
    "ep":   ("series", "📼 Qaysi serial/multserialga qism qo'shamiz?"),
    "edit": ("movies", "✏️ Qaysi kino/multfilmni tahrirlaymiz?"),
    "delm": ("movies", "🗑 Qaysi kino/multfilmni o'chiramiz?"),
    "dels": ("series", "🗑 Qaysi serial/multserialni o'chiramiz?"),
    "repm": ("movies", "📣 Qaysi kino/multfilmni kanalga qayta joylaymiz?"),
    "reps": ("series", "📣 Qaysi serial/multserialni kanalga qayta joylaymiz?"),
}
_PICK_PAGE = 8


async def _pick_list(action: str, page: int) -> "tuple[str, InlineKeyboardMarkup]":
    table, title = _PICK_ACTIONS[action]
    page = max(0, page)
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            f"SELECT code, title, category FROM {table} ORDER BY added_at DESC LIMIT ? OFFSET ?",
            (_PICK_PAGE + 1, page * _PICK_PAGE),
        )).fetchall()
    kb = InlineKeyboardBuilder()
    shown = rows[:_PICK_PAGE]
    for r in shown:
        data = f"adm2:do:{action}:{r['code']}"
        if len(data.encode()) > 64:
            continue
        kb.button(text=f"{_icon_for(r['category'], table)} {str(r['title'])[:26]} · {r['code']}", callback_data=data)
    nav = 0
    if page > 0:
        kb.button(text="◀️", callback_data=f"adm2:pick:{action}:{page - 1}")
        nav += 1
    if len(rows) > _PICK_PAGE:
        kb.button(text="▶️", callback_data=f"adm2:pick:{action}:{page + 1}")
        nav += 1
    kb.button(text="⬅️ Orqaga", callback_data="admin_menu:content")
    kb.adjust(*([1] * len(shown) + ([nav] if nav else []) + [1]))
    text = title if shown else "Hali hech narsa qo'shilmagan."
    return text + "\n<i>(oxirgi qo'shilganlar birinchi)</i>", kb.as_markup()


def _is_content_staff(uid: int) -> bool:
    return uid in STAFF_IDS


@admin_router.callback_query(F.data.startswith("adm2:"))
async def cb_admin2(callback: CallbackQuery, state: FSMContext) -> None:
    uid = callback.from_user.id
    if uid not in STAFF_IDS:
        await callback.answer("Ruxsat yo'q", show_alert=True)
        return
    parts = callback.data.split(":")
    act = parts[1] if len(parts) > 1 else ""
    msg = callback.message

    async def edit_or_send(text: str, markup=None) -> None:
        try:
            await msg.edit_text(text, reply_markup=markup)
        except Exception:
            await msg.answer(text, reply_markup=markup)

    # --- kontent: turlar bo'yicha qo'shish ---
    if act in ("addcartoon", "addcartoonseries"):
        await callback.answer()
        if act == "addcartoon":
            await _begin_movie_flow(msg, state, "cartoon")
        else:
            await _begin_series_flow(msg, state, "cartoon")
        return

    # --- ro'yxatdan tanlash ---
    if act == "pick" and len(parts) >= 4 and parts[2] in _PICK_ACTIONS:
        await callback.answer()
        text, kb = await _pick_list(parts[2], int(parts[3]) if parts[3].isdigit() else 0)
        await edit_or_send(text, kb)
        return

    if act == "do" and len(parts) >= 4 and parts[2] in _PICK_ACTIONS:
        action, code = parts[2], ":".join(parts[3:])
        await callback.answer()
        if action == "ep":
            await _start_add_episodes(msg, state, code)
        elif action == "edit":
            async with aiosqlite.connect(DB_PATH) as db:
                ok = await (await db.execute("SELECT 1 FROM movies WHERE code = ?", (code,))).fetchone()
            if not ok:
                await msg.answer("Bunday kodli kino topilmadi.")
                return
            await state.clear()
            await state.update_data(code=code)
            await state.set_state(EditMovieStates.title)
            await msg.answer("Yangi nomni yuboring (o'zgartirmaslik uchun — deb yozing):")
        elif action in ("delm", "dels"):
            kb = InlineKeyboardBuilder()
            kb.button(text="✅ Ha, o'chirilsin", callback_data=f"adm2:yes:{action}:{code}"[:64])
            kb.button(text="❌ Yo'q", callback_data="admin_menu:content")
            kb.adjust(2)
            await edit_or_send(f"⚠️ <code>{html_escape(code)}</code> o'chirilsinmi? Bu amalni qaytarib bo'lmaydi.", kb.as_markup())
        elif action in ("repm", "reps"):
            await msg.answer("⏳ Joylanmoqda...")
            await msg.answer(await repost_by_code(code, uid, only="movie" if action == "repm" else "series"))
        return

    if act == "yes" and len(parts) >= 4 and parts[2] in ("delm", "dels"):
        code = ":".join(parts[3:])
        await callback.answer()
        async with aiosqlite.connect(DB_PATH) as db:
            if parts[2] == "delm":
                cur = await db.execute("DELETE FROM movies WHERE code = ?", (code,))
            else:
                cur = await db.execute("DELETE FROM series WHERE code = ?", (code,))
                await db.execute("DELETE FROM series_episodes WHERE series_code = ?", (code,))
            await db.commit()
        await edit_or_send("🗑 O'chirildi." if cur.rowcount else "Bunday kod topilmadi.")
        return

    # --- post kanallari (egasi + to'liq adminlar) ---
    if act in ("channels", "chk", "chon", "chtest", "chdel", "chadd", "chcheck", "chbtn"):
        if not can_manage_channels(uid):
            await callback.answer("Bu bo'lim faqat to'liq admin va egasi uchun", show_alert=True)
            return
        if act == "channels":
            await callback.answer()
            text, kb = await _channels_panel()
            await edit_or_send(text, kb)
            return
        if act == "chadd":
            await callback.answer()
            await state.clear()
            await state.set_state(AddPostChannelStates.chat)
            await msg.answer(ADDPOST_PROMPT)
            return
        if act == "chbtn":
            await callback.answer()
            await state.clear()
            await state.set_state(PostBtnStates.text)
            await msg.answer(
                f"✏️ Hozirgi tugma matni: <b>{html_escape(await get_post_button_text())}</b>\n"
                "Yangi matnni yuboring (masalan: 🎬 Tomosha qilish). Bekor qilish: /cancel"
            )
            return
        if act == "chcheck":
            await callback.answer("Tekshirilmoqda...")
            text, ok = await verify_post_channels_report()
            await msg.answer(text + ("\n\n✅ Hammasi joyida." if ok else ""))
            return
        # quyidagilar kanal ID (jadvaldagi) talab qiladi
        try:
            cid = int(parts[2])
        except (IndexError, ValueError):
            await callback.answer()
            return
        async with aiosqlite.connect(DB_PATH) as db:
            db.row_factory = aiosqlite.Row
            ch = await (await db.execute("SELECT * FROM post_channels WHERE id = ?", (cid,))).fetchone()
            if not ch:
                await callback.answer("Kanal topilmadi", show_alert=True)
                return
            if act == "chk":
                k = parts[3] if len(parts) > 3 else ""
                ks = kinds_set(ch["kinds"])
                if k in POST_KIND_KEYS:
                    ks.symmetric_difference_update({k})
                    await db.execute("UPDATE post_channels SET kinds = ? WHERE id = ?", (kinds_text(ks), cid))
                    await db.commit()
                await callback.answer("Saqlandi" if ks else "⚠️ Hech bir tur tanlanmadi — post tushmaydi", show_alert=not ks)
            elif act == "chon":
                await db.execute("UPDATE post_channels SET active = 1 - active WHERE id = ?", (cid,))
                await db.commit()
                await callback.answer("Saqlandi")
            elif act == "chdel":
                await db.execute("DELETE FROM post_channels WHERE id = ?", (cid,))
                await db.commit()
                await callback.answer("Olib tashlandi")
            elif act == "chtest":
                await callback.answer("Test post yuborilmoqda...")
                try:
                    me = await bot.get_me()
                    kb = InlineKeyboardBuilder()
                    kb.button(text=await get_post_button_text(), url=f"https://t.me/{me.username}")
                    await _send_one_post(
                        _chat_ref(ch["chat_id"]),
                        "🧪 <b>Test post</b>\n\nBot shu kanalga post joylay oladi ✅\n(Bu xabarni o'chirib tashlashingiz mumkin.)",
                        None, kb.as_markup(),
                    )
                    await msg.answer(f"✅ Test post <b>{html_escape(str(ch['title']))}</b> kanaliga yuborildi.")
                except Exception as e:
                    await msg.answer(f"❌ <b>{html_escape(str(ch['title']))}</b>: {html_escape(explain_tg_error(e))}")
                return
        text, kb = await _channels_panel()
        await edit_or_send(text, kb)
        return

    # --- jamoa (faqat egasi) ---
    if act in ("team", "hire", "fire", "role", "status"):
        if not is_owner(uid):
            await callback.answer("Bu bo'lim faqat bot egasi uchun", show_alert=True)
            return
        if act == "team":
            await callback.answer()
            text, kb = await _team_panel()
            await edit_or_send(text, kb)
            return
        if act == "status":
            await callback.answer("Tekshirilmoqda...")
            await msg.answer(await build_status_text())
            return
        if act == "hire":
            role = parts[2] if len(parts) > 2 and parts[2] in ROLE_LABELS else "content"
            await callback.answer()
            await state.clear()
            await state.update_data(role=role)
            await state.set_state(HireStates.who)
            await msg.answer(HIRE_PROMPT.replace("{role}", ROLE_LABELS[role]))
            return
        try:
            target = int(parts[2])
        except (IndexError, ValueError):
            await callback.answer()
            return
        if act == "fire":
            await callback.answer()
            await msg.answer(await fire_staff(target))
        elif act == "role":
            async with aiosqlite.connect(DB_PATH) as db:
                row = await (await db.execute("SELECT role, name FROM staff_members WHERE user_id = ?", (target,))).fetchone()
            if not row:
                await callback.answer("Topilmadi", show_alert=True)
                return
            await callback.answer()
            new_role = "full" if row[0] == "content" else "content"
            await msg.answer(await hire_staff(target, row[1] or str(target), new_role, uid))
        text, kb = await _team_panel()
        await edit_or_send(text, kb)
        return

    await callback.answer()


# ======================================================================
# FOYDALANUVCHILAR UCHUN: 🧸 Multfilmlar va 📺 Seriallar ro'yxati (tugmalar bilan)
# ======================================================================
_BROWSE_PAGE = 8


async def _browse_page(kind: str, page: int) -> "tuple[str, InlineKeyboardMarkup | None]":
    """kind: 'cartoon' | 'series' | 'movie'."""
    page = max(0, page)
    items: list[tuple[str, str, str]] = []   # (belgi, nom, callback)
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        if kind == "cartoon":
            ms = await (await db.execute(
                "SELECT code, title, added_at FROM movies WHERE category = 'cartoon' ORDER BY added_at DESC")).fetchall()
            ss = await (await db.execute(
                "SELECT code, title, added_at FROM series WHERE category = 'cartoon' ORDER BY added_at DESC")).fetchall()
            merged = sorted([("🧸", r, "m") for r in ms] + [("🧸", r, "s") for r in ss], key=lambda x: x[1]["added_at"], reverse=True)
        else:
            ss = await (await db.execute(
                "SELECT code, title, added_at FROM series WHERE COALESCE(category, 'series') != 'cartoon' ORDER BY added_at DESC")).fetchall()
            merged = [("📺", r, "s") for r in ss]
    chunk = merged[page * _BROWSE_PAGE:(page + 1) * _BROWSE_PAGE]
    for icon, r, t in chunk:
        items.append((icon, str(r["title"]), f"pl:{t}:{r['code']}"))
    title = "🧸 <b>Multfilmlar</b>" if kind == "cartoon" else "📺 <b>Seriallar</b>"
    if not items:
        return f"{title}\n\nHozircha hech narsa yo'q.", None
    kb = InlineKeyboardBuilder()
    for icon, name, data in items:
        if len(data.encode()) <= 64:
            kb.button(text=f"{icon} {name[:40]}", callback_data=data)
    nav = 0
    if page > 0:
        kb.button(text="◀️ Oldingi", callback_data=f"br:{kind}:{page - 1}")
        nav += 1
    if len(merged) > (page + 1) * _BROWSE_PAGE:
        kb.button(text="Keyingi ▶️", callback_data=f"br:{kind}:{page + 1}")
        nav += 1
    kb.adjust(*([1] * len(items) + ([nav] if nav else [])))
    return f"{title}\nBirini tanlang — darhol keladi:", kb.as_markup()


@user_router.message(Command("multfilmlar"))
@user_router.message(F.text == "🧸 Multfilmlar")
async def cmd_cartoons(message: Message) -> None:
    if await is_banned(message.from_user.id):
        return
    text, kb = await _browse_page("cartoon", 0)
    await message.answer(text, reply_markup=kb)


@user_router.message(Command("seriallar"))
@user_router.message(F.text == "📺 Seriallar")
async def cmd_series_browse(message: Message) -> None:
    if await is_banned(message.from_user.id):
        return
    text, kb = await _browse_page("series", 0)
    await message.answer(text, reply_markup=kb)


@user_router.callback_query(F.data.startswith("br:"))
async def cb_browse(callback: CallbackQuery) -> None:
    parts = callback.data.split(":")
    if len(parts) < 3 or parts[1] not in ("cartoon", "series") or not parts[2].isdigit():
        await callback.answer()
        return
    text, kb = await _browse_page(parts[1], int(parts[2]))
    try:
        await callback.message.edit_text(text, reply_markup=kb)
    except Exception:
        pass
    await callback.answer()


@user_router.callback_query(F.data.startswith("pl:"))
async def cb_play(callback: CallbackQuery) -> None:
    _, t, code = (callback.data.split(":", 2) + ["", ""])[:3]
    await callback.answer()
    if await is_banned(callback.from_user.id) or not code:
        return
    if t == "m":
        await deliver_movie(callback.message.chat.id, callback.from_user.id, code)
    elif t == "s":
        await deliver_series_episode(callback.message.chat.id, callback.from_user.id, code, 1)




async def check_post_channels_on_startup() -> None:
    """Bot ishga tushganda post kanallarini jimgina tekshiradi; muammo bo'lsa EGASIGA xabar beradi."""
    try:
        if not (await get_post_channels()) and not POST_CHANNEL_ID:
            return
        text, ok = await verify_post_channels_report(only_problems=True)
        if ok:
            return
        for uid in OWNER_IDS:
            try:
                await bot.send_message(uid, "⚠️ <b>Post kanalida muammo</b> — postlar joylanmasligi mumkin:\n\n" + text + "\n\nTekshirish: /postcheck")
            except Exception:
                pass
    except Exception:
        log.exception("Post kanallarini ishga tushishda tekshirib bo'lmadi")


def create_webapp() -> web.Application:
    app = web.Application()
    app["bot"] = bot

    app.router.add_get(MINI_APP_PATH, serve_mini_app)
    app.router.add_get("/", health)
    app.router.add_get("/health", health)
    app.router.add_get("/poster/{file_id}", serve_poster)
    app.router.add_get("/stream/movie/{code}", serve_stream)
    app.router.add_get("/stream/episode/{code}/{ep}", serve_stream_episode)

    app.router.add_post("/api/deliver-movie", api_deliver_movie)
    app.router.add_post("/api/deliver-episode", api_deliver_episode)
    app.router.add_post("/api/stream-token", api_stream_token)

    app.router.add_post("/api/favorite-toggle", api_favorite_toggle)
    app.router.add_post("/api/favorites-list", api_favorites_list)
    app.router.add_post("/api/movie-request-add", api_movie_request_add)
    app.router.add_post("/api/checkin", api_checkin)
    app.router.add_post("/api/genre-sub-toggle", api_genre_sub_toggle)
    app.router.add_post("/api/user-stats", api_user_stats)
    app.router.add_post("/api/movies-list", api_movies_list)

    app.router.add_post("/api/rate-movie", api_rate_movie)
    app.router.add_post("/api/top-movies", api_top_movies)
    app.router.add_post("/api/random-movie", api_random_movie)
    app.router.add_post("/api/referral-info", api_referral_info)
    app.router.add_post("/api/create-invoice", api_create_invoice)
    app.router.add_post("/api/genres-list", api_genres_list)
    app.router.add_post("/api/series-list", api_series_list)
    app.router.add_post("/api/series-episodes", api_series_episodes)
    app.router.add_post("/api/continue-watching", api_continue_watching)
    app.router.add_post("/api/comments-list", api_comments_list)
    app.router.add_post("/api/comment-add", api_comment_add)
    app.router.add_post("/api/referral-leaderboard", api_referral_leaderboard)
    app.router.add_post("/api/admin-stats", api_admin_stats)
    app.router.add_post("/api/promo-redeem", api_promo_redeem)
    app.router.add_post("/api/coming-soon-list", api_coming_soon_list)
    app.router.add_post("/api/coming-soon-wait", api_coming_soon_wait)
    app.router.add_post("/api/achievements-list", api_achievements_list)
    app.router.add_post("/api/products-list", api_products_list)
    app.router.add_post("/api/product-order", api_product_order)

    SimpleRequestHandler(dispatcher=dp, bot=bot).register(app, path=WEBHOOK_PATH)
    setup_application(app, dp, bot=bot)
    return app


async def on_startup() -> None:
    await init_db()
    restored = await auto_restore_if_empty()
    if WEBHOOK_HOST:
        await bot.set_webhook(f"{WEBHOOK_HOST}{WEBHOOK_PATH}", drop_pending_updates=True)
        log.info("Webhook o'rnatildi: %s%s", WEBHOOK_HOST, WEBHOOK_PATH)
    else:
        log.warning("WEBHOOK_HOST berilmagan — polling rejimida ishga tushmoqda.")
    asyncio.create_task(background_jobs_loop())
    asyncio.create_task(post_startup(restored))


# ----------------------------------------------------------------------
# FON VAZIFALARI: VIP muddati tugashi haqida eslatma (kuniga bir marta) +
# haftalik avtomatik statistik hisobot adminlarga
# ----------------------------------------------------------------------
async def send_vip_expiry_reminders() -> None:
    soon = (utcnow() + timedelta(days=2)).isoformat()
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        rows = await (await db.execute(
            """SELECT user_id, vip_until FROM users
               WHERE vip_until IS NOT NULL AND vip_until > ? AND vip_until < ?
                 AND (vip_reminded_at IS NULL OR vip_reminded_at < ?)""",
            (now_iso(), soon, (utcnow() - timedelta(days=1)).isoformat()),
        )).fetchall()
        for r in rows:
            try:
                await bot.send_message(
                    r["user_id"],
                    "⏰ Sizning VIP a'zoligingiz muddati tez orada tugaydi!\n"
                    "Uzaytirish uchun mini-app'dagi 💎 Do'kon bo'limiga o'ting.",
                )
            except Exception:
                pass
            await db.execute("UPDATE users SET vip_reminded_at = ? WHERE user_id = ?", (now_iso(), r["user_id"]))
        await db.commit()


async def send_weekly_report() -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        db.row_factory = aiosqlite.Row
        total_users = (await (await db.execute("SELECT COUNT(*) c FROM users")).fetchone())["c"]
        week_ago = (utcnow() - timedelta(days=7)).isoformat()
        new_users = (await (await db.execute(
            "SELECT COUNT(*) c FROM users WHERE joined_at > ?", (week_ago,)
        )).fetchone())["c"]
        new_watches = (await (await db.execute(
            "SELECT COUNT(*) c FROM watch_events WHERE created_at > ?", (week_ago,)
        )).fetchone())["c"]
        top = await (await db.execute("SELECT title, views FROM movies ORDER BY views DESC LIMIT 3")).fetchall()
    lines = [
        "📊 <b>Haftalik hisobot</b>",
        f"👤 Jami foydalanuvchilar: {total_users} (+{new_users} shu hafta)",
        f"🎬 Shu hafta ko'rishlar: {new_watches}",
    ]
    if top:
        lines.append("🏆 Top: " + ", ".join(f"{t['title']} ({t['views']})" for t in top))
    text = "\n".join(lines)
    for admin_id in ADMIN_IDS:
        try:
            await bot.send_message(admin_id, text)
        except Exception:
            pass


async def background_jobs_loop() -> None:
    """Bot ishga tushgandan keyin fonda aylanadi: har 24 soatda VIP
    eslatmalarini va har 7 kunda haftalik hisobotni yuboradi."""
    cycles = 0
    while True:
        try:
            await send_vip_expiry_reminders()
            if cycles % 7 == 0:
                await send_weekly_report()
        except Exception:
            log.exception("background_jobs_loop xatolik")
        cycles += 1
        await asyncio.sleep(24 * 60 * 60)


def main() -> None:
    dp.errors.register(on_unhandled_error)
    dp.include_router(admin_router)
    dp.include_router(pay_router)
    dp.include_router(user_router)

    if WEBHOOK_HOST:
        app = create_webapp()

        async def _startup(app: web.Application) -> None:
            await on_startup()

        app.on_startup.append(_startup)
        web.run_app(app, host="0.0.0.0", port=PORT)
    else:
        async def _run_polling() -> None:
            await init_db()
            restored = await auto_restore_if_empty()
            await bot.delete_webhook(drop_pending_updates=True)
            asyncio.create_task(background_jobs_loop())
            asyncio.create_task(post_startup(restored))
            await dp.start_polling(bot)

        asyncio.run(_run_polling())


if __name__ == "__main__":
    main()
