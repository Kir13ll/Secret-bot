"""
Telegram-бот для шифрования и расшифровки файлов по паролю.

ЛИЧНЫЙ ЧАТ (как раньше):
    файл -> бот определяет режим по маркеру CRYPTv1\\0 -> пароль -> результат.

ГРУППА (бот — администратор с правом удаления сообщений):
    0. Админ группы заранее пишет боту в личку /setcode, выбирает группу
       и вводит кодовое слово этой группы (хранится в SQLite).
    1. Участник присылает НЕзашифрованный документ.
    2. Бот читает файл, удаляет оригинал, шифрует его кодовым словом группы,
       присылает в группу зашифрованный .enc и ссылку.
    3. Человек открывает ссылку, вводит кодовое слово — бот берёт
       зашифрованный файл из Telegram по file_id, расшифровывает
       и отдаёт на скачивание прямо со страницы.
    Уже зашифрованные файлы (с маркером) в группе бот не трогает.

Формат зашифрованного файла:
    [8 байт "CRYPTv1\\0"][16 байт соли][12 байт nonce][шифртекст + тег GCM]

Настройки — переменные окружения (или константы ниже):
    BOT_TOKEN  — токен от @BotFather
    BASE_URL   — публичный адрес сайта БЕЗ слеша на конце, https://files.example.com
    WEB_HOST / WEB_PORT — где слушает встроенный веб-сервер (по умолчанию 0.0.0.0:8080)
    DB_PATH    — файл SQLite со ссылками (по умолчанию links.db)

Запуск: python crypt_bot.py
"""

import asyncio
import html
import io
import logging
import os
import re
import secrets
import sqlite3
import threading
import time
from urllib.parse import quote

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
# Для продакшена замените MemoryStorage на RedisStorage:
#   from aiogram.fsm.storage.redis import RedisStorage
#   storage = RedisStorage.from_url("redis://localhost:6379/0")
# MemoryStorage теряет состояния (и файлы в них) при перезапуске бота.
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.types import (
    BufferedInputFile,
    CallbackQuery,
    ChatMemberUpdated,
    Message,
)
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiohttp import web
from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

# ----------------------------- Настройки ------------------------------------

BOT_TOKEN = os.getenv("BOT_TOKEN", "")
BASE_URL = os.getenv("BASE_URL", "http://localhost:8080").rstrip("/")
# Сайт расшифровки: по умолчанию выключен (ENABLE_WEB=1 — включить).
# Ссылки в группе генерируются и сохраняются в базу независимо от этого флага.
ENABLE_WEB = os.getenv("ENABLE_WEB", "0") == "1"
WEB_HOST = os.getenv("WEB_HOST", "0.0.0.0")
WEB_PORT = int(os.getenv("WEB_PORT", "8080"))
DB_PATH = os.getenv("DB_PATH", "links.db")

MAGIC = b"CRYPTv1\x00"          # магический маркер (8 байт)
SALT_SIZE = 16                   # размер соли
NONCE_SIZE = 12                  # размер nonce для AES-GCM
TAG_SIZE = 16                    # размер тега GCM
KDF_ITERATIONS = 600_000         # число итераций PBKDF2
HEADER_SIZE = len(MAGIC) + SALT_SIZE + NONCE_SIZE
ENC_SUFFIX = ".enc"
MIN_CODEWORD_LEN = 8             # минимальная длина кодового слова группы

# Лимиты облачного Telegram Bot API: скачивание ботом — 20 МБ, отправка — 50 МБ.
MAX_DOWNLOAD_SIZE = 20 * 1024 * 1024
# В группе зашифрованный файл потом скачивается обратно (getFile, лимит 20 МБ),
# а он больше оригинала на HEADER_SIZE + TAG_SIZE байт — оставляем запас.
GROUP_MAX_SIZE = MAX_DOWNLOAD_SIZE - 1024

# Защита страницы от перебора кодового слова
MAX_FAILS = 5                    # неудачных попыток на ссылку...
FAIL_WINDOW = 15 * 60            # ...за это число секунд

ERR_WRONG_PASSWORD = "❌ Неверный пароль или файл повреждён"

logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
)
logger = logging.getLogger("crypt_bot")

# Роутеры: личные чаты и группы обрабатываются раздельно
private_router = Router()
private_router.message.filter(F.chat.type == "private")
group_router = Router()
group_router.message.filter(F.chat.type.in_({"group", "supergroup"}))
# Служебные события (добавление/удаление бота в группе)
events_router = Router()

# PBKDF2 тяжёлый: ограничиваем число одновременных операций
CRYPTO_SEM = asyncio.Semaphore(2)


# ----------------------------- Состояния ------------------------------------

class CryptStates(StatesGroup):
    """Единственное состояние: ожидание пароля от пользователя."""
    waiting_for_password = State()


class SetCodeStates(StatesGroup):
    """Ожидание кодового слова группы (команда /setcode)."""
    waiting_for_codeword = State()


# ------------------------- Криптографические функции ------------------------

def is_encrypted(data: bytes) -> bool:
    """Проверяет, начинается ли файл с магического маркера CRYPTv1\\0."""
    return data[: len(MAGIC)] == MAGIC


def make_key(password: str, salt: bytes) -> bytes:
    """Выводит 32-байтный ключ из пароля через PBKDF2-HMAC-SHA256."""
    kdf = PBKDF2HMAC(
        algorithm=hashes.SHA256(),
        length=32,
        salt=salt,
        iterations=KDF_ITERATIONS,
    )
    return kdf.derive(password.encode("utf-8"))


def encrypt_file(data: bytes, password: str) -> bytes:
    """
    Шифрует данные AES-256-GCM.
    Возвращает: MAGIC + соль + nonce + (шифртекст + тег GCM).
    """
    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    key = make_key(password, salt)
    ciphertext = AESGCM(key).encrypt(nonce, data, None)
    return MAGIC + salt + nonce + ciphertext


def decrypt_file(data: bytes, password: str) -> bytes:
    """
    Расшифровывает данные формата CRYPTv1.
    Бросает InvalidTag при неверном пароле или повреждённых данных,
    ValueError — если файл слишком короткий или без маркера.
    """
    if not is_encrypted(data) or len(data) < HEADER_SIZE + TAG_SIZE:
        raise ValueError("Некорректный формат зашифрованного файла")

    salt = data[len(MAGIC): len(MAGIC) + SALT_SIZE]
    nonce = data[len(MAGIC) + SALT_SIZE: HEADER_SIZE]
    ciphertext = data[HEADER_SIZE:]
    key = make_key(password, salt)
    return AESGCM(key).decrypt(nonce, ciphertext, None)


async def run_crypto(func, *args):
    """Запускает тяжёлую криптооперацию в потоке, не более 2 одновременно."""
    async with CRYPTO_SEM:
        return await asyncio.to_thread(func, *args)


# ------------------------------ База ссылок ---------------------------------

_db = sqlite3.connect(DB_PATH, check_same_thread=False)
_db_lock = threading.Lock()
with _db_lock:
    _db.execute(
        "CREATE TABLE IF NOT EXISTS links ("
        "token TEXT PRIMARY KEY, file_id TEXT NOT NULL, "
        "file_name TEXT NOT NULL, created REAL NOT NULL)"
    )
    _db.commit()


def _db_add(token: str, file_id: str, file_name: str) -> None:
    with _db_lock:
        _db.execute(
            "INSERT INTO links (token, file_id, file_name, created) VALUES (?, ?, ?, ?)",
            (token, file_id, file_name, time.time()),
        )
        _db.commit()


def _db_get(token: str) -> tuple[str, str] | None:
    with _db_lock:
        row = _db.execute(
            "SELECT file_id, file_name FROM links WHERE token = ?", (token,)
        ).fetchone()
    return (row[0], row[1]) if row else None


async def db_add(token: str, file_id: str, file_name: str) -> None:
    await asyncio.to_thread(_db_add, token, file_id, file_name)


async def db_get(token: str) -> tuple[str, str] | None:
    return await asyncio.to_thread(_db_get, token)


# Группы, куда добавлен бот, и кодовое слово каждой группы
with _db_lock:
    _db.execute(
        "CREATE TABLE IF NOT EXISTS groups ("
        "chat_id INTEGER PRIMARY KEY, title TEXT NOT NULL, codeword TEXT)"
    )
    _db.commit()


def _group_upsert(chat_id: int, title: str) -> None:
    with _db_lock:
        _db.execute(
            "INSERT INTO groups (chat_id, title) VALUES (?, ?) "
            "ON CONFLICT(chat_id) DO UPDATE SET title = excluded.title",
            (chat_id, title),
        )
        _db.commit()


def _group_remove(chat_id: int) -> None:
    with _db_lock:
        _db.execute("DELETE FROM groups WHERE chat_id = ?", (chat_id,))
        _db.commit()


def _group_list() -> list[tuple[int, str]]:
    with _db_lock:
        rows = _db.execute("SELECT chat_id, title FROM groups").fetchall()
    return [(r[0], r[1]) for r in rows]


def _codeword_set(chat_id: int, codeword: str) -> None:
    with _db_lock:
        _db.execute("UPDATE groups SET codeword = ? WHERE chat_id = ?", (codeword, chat_id))
        _db.commit()


def _codeword_get(chat_id: int) -> str | None:
    with _db_lock:
        row = _db.execute(
            "SELECT codeword FROM groups WHERE chat_id = ?", (chat_id,)
        ).fetchone()
    return row[0] if row and row[0] else None


# ----------------------------- Вспомогательное ------------------------------

def _result_name(file_name: str, mode: str) -> str:
    """Подбирает имя итогового файла."""
    if mode == "encrypt":
        return file_name + ENC_SUFFIX
    if file_name.lower().endswith(ENC_SUFFIX) and len(file_name) > len(ENC_SUFFIX):
        return file_name[: -len(ENC_SUFFIX)]
    return file_name + ".dec"


async def is_group_admin(bot: Bot, chat_id: int, user_id: int) -> bool:
    """Проверяет, что пользователь — создатель или администратор группы."""
    try:
        member = await bot.get_chat_member(chat_id, user_id)
    except Exception:
        return False
    return member.status in ("creator", "administrator")


async def safe_delete(bot: Bot, chat_id: int, message_id: int | None) -> bool:
    """
    Пытается удалить сообщение, возвращает True при успехе.
    Ошибки не критичны: сообщение могло быть удалено ранее, быть старше
    48 часов или у бота нет прав (в группах).
    """
    if message_id is None:
        return False
    try:
        await bot.delete_message(chat_id=chat_id, message_id=message_id)
        return True
    except Exception:
        logger.warning("Не удалось удалить сообщение %s", message_id)
        return False


# ============================== ЛИЧНЫЙ ЧАТ ==================================

@private_router.message(Command("start"))
async def cmd_start(message: Message, state: FSMContext) -> None:
    """Краткая инструкция."""
    await state.clear()
    await message.answer(
        "🔐 Я шифрую и расшифровываю файлы по паролю.\n\n"
        "1. Отправьте мне файл (как документ).\n"
        "2. Я сам пойму, что делать: обычный файл — зашифрую "
        "(и сразу удалю оригинал из чата), зашифрованный мной — расшифрую.\n"
        "3. Напишите пароль — получите результат. "
        "Сообщение с паролем я тоже удалю.\n\n"
        "Алгоритм: AES-256-GCM + PBKDF2-SHA256.\n"
        "Лимит размера файла: 20 МБ.\n"
        "/cancel — отменить текущую операцию.\n\n"
        "👥 Группы: добавьте меня в группу администратором (право «Удаление "
        "сообщений»), затем администратор пишет мне здесь /setcode, выбирает "
        "группу и задаёт кодовое слово. После этого все файлы, присланные "
        "в группу, я шифрую этим словом и выдаю ссылку для скачивания."
    )


@private_router.message(Command("cancel"))
async def cmd_cancel(message: Message, state: FSMContext) -> None:
    """Сбрасывает состояние."""
    await state.clear()
    await message.answer("Операция отменена. Отправьте новый файл.")


@private_router.message(Command("setcode"))
async def cmd_setcode(message: Message, state: FSMContext, bot: Bot) -> None:
    """Показывает группы, где пользователь админ и где есть бот."""
    await state.clear()
    mine = []
    for chat_id, title in await asyncio.to_thread(_group_list):
        if await is_group_admin(bot, chat_id, message.from_user.id):
            mine.append((chat_id, title))
    if not mine:
        await message.answer(
            "Не нашёл групп, где вы администратор, а я добавлен. "
            "Добавьте меня в группу админом (право «Удаление сообщений») "
            "и повторите /setcode."
        )
        return
    kb = InlineKeyboardBuilder()
    for chat_id, title in mine:
        kb.button(text=title[:60], callback_data=f"grp:{chat_id}")
    kb.adjust(1)
    await message.answer(
        "Для какой группы задать кодовое слово?", reply_markup=kb.as_markup()
    )


@private_router.callback_query(F.data.startswith("grp:"))
async def on_group_chosen(call: CallbackQuery, state: FSMContext, bot: Bot) -> None:
    """Группа выбрана — ждём кодовое слово."""
    chat_id = int(call.data.split(":", 1)[1])
    if not await is_group_admin(bot, chat_id, call.from_user.id):
        await call.answer("Вы не администратор этой группы", show_alert=True)
        return
    title = dict(await asyncio.to_thread(_group_list)).get(chat_id)
    if title is None:
        await call.answer("Группа не найдена", show_alert=True)
        return
    await state.set_state(SetCodeStates.waiting_for_codeword)
    await state.update_data(chat_id=chat_id, title=title)
    await bot.send_message(
        call.from_user.id,
        f"Введите кодовое слово для «{html.escape(title)}» "
        f"(не короче {MIN_CODEWORD_LEN} символов). Сообщение я удалю.\n"
        "Файлы, зашифрованные раньше, останутся со старым словом.\n"
        "/cancel — отмена.",
    )
    await call.answer()


@private_router.message(
    SetCodeStates.waiting_for_codeword, F.text, ~F.text.startswith("/")
)
async def on_codeword(message: Message, state: FSMContext, bot: Bot) -> None:
    """Сохраняет кодовое слово группы."""
    codeword = message.text.strip()
    await safe_delete(bot, message.chat.id, message.message_id)

    if len(codeword) < MIN_CODEWORD_LEN:
        await message.answer(
            f"❌ Слишком короткое слово (минимум {MIN_CODEWORD_LEN} символов). "
            "Введите другое или /cancel."
        )
        return

    data = await state.get_data()
    chat_id: int = data["chat_id"]
    title: str = data["title"]
    await state.clear()

    if not await is_group_admin(bot, chat_id, message.from_user.id):
        await message.answer("❌ Вы больше не администратор этой группы.")
        return

    await asyncio.to_thread(_codeword_set, chat_id, codeword)
    await message.answer(
        f"✅ Кодовое слово для «{html.escape(title)}» сохранено. "
        "Теперь файлы, присланные в группу, будут шифроваться им."
    )


@private_router.message(F.document)
async def on_document(message: Message, state: FSMContext, bot: Bot) -> None:
    """
    Принимает документ, определяет режим по магическому маркеру
    и запрашивает пароль. Незашифрованный файл сразу удаляется из чата.
    """
    doc = message.document

    if doc.file_size and doc.file_size > MAX_DOWNLOAD_SIZE:
        await message.answer("❌ Файл слишком большой: бот может скачать не более 20 МБ.")
        return

    try:
        buffer = io.BytesIO()
        await bot.download(doc, destination=buffer)
        file_bytes = buffer.getvalue()
    except Exception:
        logger.exception("Не удалось скачать файл")
        await message.answer("❌ Не удалось скачать файл. Попробуйте ещё раз.")
        return

    # Режим определяется ТОЛЬКО по магическому маркеру, не по имени файла
    mode = "decrypt" if is_encrypted(file_bytes) else "encrypt"

    # Сразу удаляем незашифрованный файл из чата: данные уже в памяти бота.
    if mode == "encrypt":
        await safe_delete(bot, message.chat.id, message.message_id)

    await state.set_state(CryptStates.waiting_for_password)
    await state.update_data(
        file_bytes=file_bytes,
        file_name=doc.file_name or "file",
        mode=mode,
    )

    if mode == "decrypt":
        await message.answer("🔓 Файл зашифрован. Введите пароль для расшифровки:")
    else:
        await message.answer(
            "🔒 Файл получен и удалён из чата. Введите пароль для шифрования:"
        )


@private_router.message(CryptStates.waiting_for_password, F.text)
async def on_password(message: Message, state: FSMContext, bot: Bot) -> None:
    """Принимает пароль, выполняет операцию и отправляет результат."""
    password = message.text
    data = await state.get_data()
    file_bytes: bytes = data["file_bytes"]
    file_name: str = data["file_name"]
    mode: str = data["mode"]

    await safe_delete(bot, message.chat.id, message.message_id)

    try:
        if mode == "encrypt":
            result = await run_crypto(encrypt_file, file_bytes, password)
            caption = "✅ Файл зашифрован"
        else:
            result = await run_crypto(decrypt_file, file_bytes, password)
            caption = "✅ Файл расшифрован"

        await message.answer_document(
            BufferedInputFile(result, filename=_result_name(file_name, mode)),
            caption=caption,
        )
    except InvalidTag:
        await message.answer(ERR_WRONG_PASSWORD)
    except ValueError:
        logger.warning("Некорректный формат зашифрованного файла")
        await message.answer(ERR_WRONG_PASSWORD)
    except Exception:
        logger.exception("Ошибка при обработке файла")
        await message.answer("❌ Произошла внутренняя ошибка. Попробуйте позже.")
    finally:
        await state.clear()


# ================================= ГРУППА ===================================

_warned: dict[int, float] = {}   # chat_id -> когда последний раз предупреждали


@events_router.my_chat_member()
async def on_bot_membership(event: ChatMemberUpdated) -> None:
    """Запоминает группы, куда добавили бота, и забывает те, откуда убрали."""
    if event.chat.type not in ("group", "supergroup"):
        return
    status = event.new_chat_member.status
    if status in ("member", "administrator"):
        await asyncio.to_thread(_group_upsert, event.chat.id, event.chat.title or str(event.chat.id))
    elif status in ("left", "kicked"):
        await asyncio.to_thread(_group_remove, event.chat.id)


@group_router.message(F.document)
async def on_group_document(message: Message, bot: Bot) -> None:
    """
    Файл в группе: читаем -> удаляем оригинал -> шифруем кодовым словом группы
    -> отправляем .enc со ссылкой. Уже зашифрованные файлы игнорируются.
    Если у группы нет кодового слова, файл не трогаем.
    """
    doc = message.document
    chat = message.chat
    await asyncio.to_thread(_group_upsert, chat.id, chat.title or str(chat.id))

    codeword = await asyncio.to_thread(_codeword_get, chat.id)
    if not codeword:
        # Предупреждаем не чаще раза в 10 минут, чтобы не спамить
        if time.time() - _warned.get(chat.id, 0) > 600:
            _warned[chat.id] = time.time()
            await message.answer(
                "⚠️ Для этой группы не задано кодовое слово, файлы не шифруются. "
                "Администратор: напишите мне в личку /setcode."
            )
        return

    if doc.file_size and doc.file_size > GROUP_MAX_SIZE:
        await message.answer(
            "❌ Файл слишком большой: бот может обработать не более ~20 МБ."
        )
        return

    try:
        buffer = io.BytesIO()
        await bot.download(doc, destination=buffer)
        file_bytes = buffer.getvalue()
    except Exception:
        logger.exception("Не удалось скачать файл из группы")
        await message.answer("❌ Не удалось скачать файл. Отправьте его ещё раз.")
        return

    # Зашифрованные файлы (в т.ч. наши же .enc) не трогаем
    if is_encrypted(file_bytes):
        return

    # Оригинал удаляем сразу. Если не получилось — файл НЕ обрабатываем.
    if not await safe_delete(bot, chat.id, message.message_id):
        await message.answer(
            "⚠️ Не могу удалить файл. Сделайте меня администратором "
            "с правом «Удаление сообщений». Файл не обработан."
        )
        return

    file_name = doc.file_name or "file"
    user = message.from_user
    sender = html.escape(user.full_name) if user else "участника"

    try:
        encrypted = await run_crypto(encrypt_file, file_bytes, codeword)
        token = secrets.token_urlsafe(16)
        link = f"{BASE_URL}/d/{token}"

        sent = await message.answer_document(
            BufferedInputFile(encrypted, filename=_result_name(file_name, "encrypt")),
            caption=(
                f"🔒 Файл <b>{html.escape(file_name)}</b> от {sender} зашифрован.\n\n"
                f"🔗 {link}\n\n"
                "Откройте ссылку и введите кодовое слово группы, чтобы скачать файл."
            ),
        )
        # file_id именно зашифрованного файла, отправленного ботом
        await db_add(token, sent.document.file_id, file_name)
    except Exception:
        logger.exception("Ошибка при шифровании файла в группе")
        await message.answer(
            "❌ Не удалось обработать файл. Оригинал уже удалён — "
            "отправьте его ещё раз."
        )


# ================================== САЙТ ====================================

PAGE = """<!doctype html>
<html lang="ru"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<meta name="robots" content="noindex">
<title>Расшифровка файла</title>
<style>
:root{color-scheme:light dark}
body{font-family:system-ui,-apple-system,sans-serif;max-width:420px;margin:12vh auto;padding:0 16px}
h1{font-size:1.4rem}
input,button{width:100%;box-sizing:border-box;padding:12px;font-size:1rem;margin-top:10px;border-radius:8px;border:1px solid #8886}
button{background:#2a7ae4;color:#fff;border:0;cursor:pointer}
.err{color:#d33;margin-top:12px}
</style></head><body>
<h1>🔐 Расшифровка файла</h1>
<p>Файл: <b>%NAME%</b></p>
<form method="post" autocomplete="off">
<input type="password" name="password" placeholder="Кодовое слово" required autofocus>
<button type="submit">Расшифровать и скачать</button>
</form>
%ERROR%
</body></html>"""

# token -> (число неудач, время первой неудачи)
_fails: dict[str, tuple[int, float]] = {}


def _is_locked(token: str) -> bool:
    entry = _fails.get(token)
    if not entry:
        return False
    count, first = entry
    if time.time() - first > FAIL_WINDOW:
        _fails.pop(token, None)
        return False
    return count >= MAX_FAILS


def _register_fail(token: str) -> None:
    count, first = _fails.get(token, (0, time.time()))
    if time.time() - first > FAIL_WINDOW:
        count, first = 0, time.time()
    _fails[token] = (count + 1, first)


def render_page(name: str, error: str = "", status: int = 200) -> web.Response:
    err_html = f'<div class="err">{html.escape(error)}</div>' if error else ""
    body = PAGE.replace("%NAME%", html.escape(name)).replace("%ERROR%", err_html)
    return web.Response(text=body, content_type="text/html", status=status)


def content_disposition(name: str) -> str:
    """Заголовок Content-Disposition с поддержкой юникода в имени."""
    ascii_name = re.sub(r'[^A-Za-z0-9._ -]', "_", name.encode("ascii", "ignore").decode()) or "file"
    return f"attachment; filename=\"{ascii_name}\"; filename*=UTF-8''{quote(name)}"


async def web_form(request: web.Request) -> web.Response:
    """GET /d/{token} — страница ввода кодового слова."""
    rec = await db_get(request.match_info["token"])
    if not rec:
        return web.Response(status=404, text="Ссылка недействительна")
    return render_page(rec[1])


async def web_download(request: web.Request) -> web.Response:
    """POST /d/{token} — проверка кодового слова и выдача расшифрованного файла."""
    token = request.match_info["token"]
    rec = await db_get(token)
    if not rec:
        return web.Response(status=404, text="Ссылка недействительна")
    file_id, file_name = rec

    if _is_locked(token):
        return render_page(
            file_name, "Слишком много неверных попыток. Попробуйте позже.", 429
        )

    form = await request.post()
    password = form.get("password", "")
    if not isinstance(password, str) or not password.strip():
        return render_page(file_name, "Введите кодовое слово.", 400)
    password = password.strip()  # так же, как при шифровании (подпись .strip())

    bot: Bot = request.app["bot"]
    try:
        buf = io.BytesIO()
        await bot.download(file_id, destination=buf)
    except Exception:
        logger.exception("Не удалось получить файл из Telegram")
        return render_page(file_name, "Не удалось получить файл из Telegram.", 502)

    try:
        data = await run_crypto(decrypt_file, buf.getvalue(), password)
    except (InvalidTag, ValueError):
        _register_fail(token)
        return render_page(file_name, "Неверное кодовое слово.", 403)
    except Exception:
        logger.exception("Ошибка расшифровки на сайте")
        return render_page(file_name, "Внутренняя ошибка.", 500)

    _fails.pop(token, None)
    return web.Response(
        body=data,
        content_type="application/octet-stream",
        headers={
            "Content-Disposition": content_disposition(file_name),
            "Cache-Control": "no-store",
        },
    )


def build_web_app(bot: Bot) -> web.Application:
    app = web.Application(client_max_size=64 * 1024)
    app["bot"] = bot
    app.router.add_get("/d/{token}", web_form)
    app.router.add_post("/d/{token}", web_download)
    return app


# -------------------------------- Запуск ------------------------------------

async def main() -> None:
    """Точка входа: запускает веб-сервер и long polling."""
    bot = Bot(
        token=BOT_TOKEN,
        default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    )
    dp = Dispatcher(storage=MemoryStorage())
    dp.include_router(private_router)
    dp.include_router(group_router)
    dp.include_router(events_router)

    runner = None
    if ENABLE_WEB:
        runner = web.AppRunner(build_web_app(bot))
        await runner.setup()
        await web.TCPSite(runner, WEB_HOST, WEB_PORT).start()
        logger.info("Сайт запущен на %s:%s, ссылки вида %s/d/<token>", WEB_HOST, WEB_PORT, BASE_URL)
    else:
        logger.info("Сайт выключен (ENABLE_WEB=0): бот только шифрует и выдаёт ссылки")

    try:
        logger.info("Бот запущен")
        await dp.start_polling(bot)
    finally:
        if runner:
            await runner.cleanup()
        await bot.session.close()


if __name__ == "__main__":
    asyncio.run(main())
