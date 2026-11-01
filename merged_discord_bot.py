#!/usr/bin/env python3
"""
Merged Discord Bot
==================
Combines features from:
  • Server template copier (pull / apply / backup / compare / manage)
  • APK announcer + full moderation suite
  • TikTok lookup / download / search tools
  • Snipe + utility commands
  • Music player (YouTube / search / Spotify → YouTube) with default playlist

Requirements (Python 3.9+):
    pip install -U "discord.py[voice]>=2.3" aiohttp yt-dlp aiosqlite python-dotenv requests PyNaCl
    Optional (better Spotify playlist loading):  pip install spotipy

System:
    FFmpeg must be installed and on PATH
    (Windows: ffmpeg.org  |  macOS: brew install ffmpeg  |  Linux: apt install ffmpeg)

Token:
    Set DISCORD_TOKEN in environment or create a .env file:
        DISCORD_TOKEN=your_bot_token

    Optional Spotify API (playlist tracks → YouTube matches):
        SPOTIFY_CLIENT_ID=...
        SPOTIFY_CLIENT_SECRET=...
        Free app: https://developer.spotify.com/dashboard

    NEVER hard-code tokens in source.

Invite the bot with:
    scopes: bot + applications.commands
    permissions: Administrator (or Manage Server/Channels/Roles, Ban/Kick,
                 Moderate Members, Manage Messages, Connect + Speak)

Privileged Gateway Intents (Developer Portal → Bot):
    • Server Members Intent
    • Message Content Intent
"""

from __future__ import annotations

import asyncio
import json
import os
import random
import re
import sys
import tempfile
import traceback
from collections import defaultdict
from datetime import date, datetime, timedelta, timezone
from io import BytesIO
from typing import Optional

# ---------------------------------------------------------------------------
# Dependencies
# ---------------------------------------------------------------------------
try:
    import aiohttp
    import aiosqlite
    import discord
    import requests
    import yt_dlp
    from discord import app_commands
    from discord.ext import commands
    from discord.http import Route
    from dotenv import load_dotenv
except ImportError as e:
    print(f"[!] Missing dependency: {e}")
    print("    Install with:")
    print(
        '    python -m pip install -U "discord.py[voice]>=2.3" aiohttp yt-dlp '
        "aiosqlite python-dotenv requests PyNaCl"
    )
    print("    Optional for Spotify playlists:  pip install spotipy")
    sys.exit(1)

try:
    import spotipy
    from spotipy.oauth2 import SpotifyClientCredentials

    _HAS_SPOTIPY = True
except ImportError:
    spotipy = None  # type: ignore
    SpotifyClientCredentials = None  # type: ignore
    _HAS_SPOTIPY = False

load_dotenv()

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
TOKEN = os.getenv("DISCORD_TOKEN", "").strip()
if not TOKEN:
    # Fallback to bot_token.txt next to the script (optional convenience)
    _token_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "bot_token.txt")
    if os.path.isfile(_token_file):
        with open(_token_file, encoding="utf-8") as f:
            TOKEN = f.read().strip()
        if TOKEN.lower().startswith("bot "):
            TOKEN = TOKEN[4:]

if not TOKEN:
    print("[!] No token found. Set DISCORD_TOKEN env var or create bot_token.txt")
    sys.exit(1)

CONFIG_FILE = "config.json"
HISTORY_DB = "history.db"
PREFIX = ","
REASON = "Merged bot"
SNIPE_TIMEOUT = 3600  # seconds
API = "https://discord.com/api/v10"

# Web dashboard (http://HOST:PORT/) — default localhost only
DASHBOARD_HOST = os.getenv("DASHBOARD_HOST", "127.0.0.1").strip() or "127.0.0.1"
DASHBOARD_PORT = int(os.getenv("DASHBOARD_PORT", "8765") or "8765")
DASHBOARD_PASSWORD = os.getenv("DASHBOARD_PASSWORD", "").strip()  # empty = no login

_bot_started_at: Optional[datetime] = None

# Default Spotify playlist — used when /play or .play is run with no query
DEFAULT_PLAYLIST = (
    "https://open.spotify.com/playlist/4J8GeAjHYKavwnH1oxd9qM?si=c945feba9aff4409"
)

SPOTIFY_CLIENT_ID = os.getenv("SPOTIFY_CLIENT_ID", "").strip()
SPOTIFY_CLIENT_SECRET = os.getenv("SPOTIFY_CLIENT_SECRET", "").strip()

FFMPEG_OPTIONS = {
    "before_options": "-reconnect 1 -reconnect_streamed 1 -reconnect_delay_max 5",
    "options": "-vn",
}
YDL_OPTS = {
    "format": "bestaudio/best",
    "quiet": True,
    "no_warnings": True,
    "default_search": "ytsearch1",
    "nocheckcertificate": True,
    "ignoreerrors": False,
    "noplaylist": True,  # single tracks; playlists handled separately
    "extract_flat": False,
    # YouTube needs a JS runtime to solve signature challenges (Node in Docker image)
    "js_runtimes": {"node": {}},
    "remote_components": ["ejs:github"],
}

def _youtube_cookiefile() -> Optional[str]:
    """YouTube blocks datacenter IPs ("Sign in to confirm you're not a bot").
    Pass cookies via YOUTUBE_COOKIES (Netscape cookies.txt contents) or
    YOUTUBE_COOKIES_FILE (path)."""
    path = os.getenv("YOUTUBE_COOKIES_FILE", "").strip()
    if path and os.path.exists(path):
        return path
    raw = os.getenv("YOUTUBE_COOKIES", "").strip()
    if raw:
        raw = raw.replace("\\n", "\n")
        out = os.path.join(tempfile.gettempdir(), "yt_cookies.txt")
        with open(out, "w") as f:
            f.write(raw + "\n")
        return out
    return None


_YT_COOKIES = _youtube_cookiefile()
if _YT_COOKIES:
    YDL_OPTS["cookiefile"] = _YT_COOKIES

YDL_PLAYLIST_OPTS = {
    **YDL_OPTS,
    "noplaylist": False,
    "extract_flat": "in_playlist",
    "playlistend": 50,  # cap size for safety
}

# ---------------------------------------------------------------------------
# Config helpers
# ---------------------------------------------------------------------------
def load_config() -> dict:
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except (json.JSONDecodeError, OSError):
            print("Warning: couldn't read config.json, starting fresh.")
    return {}


def save_config(cfg: dict) -> None:
    with open(CONFIG_FILE, "w", encoding="utf-8") as f:
        json.dump(cfg, f, indent=4)


config = load_config()

# ---------------------------------------------------------------------------
# Bot setup
# ---------------------------------------------------------------------------
intents = discord.Intents.default()
intents.message_content = True
intents.members = True


class MergedBot(commands.Bot):
    def __init__(self):
        super().__init__(
            command_prefix=PREFIX,
            intents=intents,
            help_command=None,
        )
        self.job_lock = asyncio.Lock()
        self.snipe_cache: dict[int, dict] = {}

    async def setup_hook(self):
        # Global sync (can take up to ~1 h to appear everywhere)
        # For instant appearance, also do per-guild sync on join / ready.
        try:
            synced = await self.tree.sync()
            print(f"Synced {len(synced)} global slash command(s).")
        except Exception as e:
            print(f"Slash sync warning: {e}")


bot = MergedBot()

# ---------------------------------------------------------------------------
# Small utilities
# ---------------------------------------------------------------------------
def as_int(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return None


def safe_filename(s: str) -> str:
    return re.sub(r'[<>:"/\\|?*]+', "_", s).strip() or "server"


def humanize_seconds(seconds: int) -> str:
    if seconds <= 0:
        return "off"
    minutes, secs = divmod(seconds, 60)
    hours, minutes = divmod(minutes, 60)
    days, hours = divmod(hours, 24)
    out = []
    for value, unit in ((days, "day"), (hours, "hour"), (minutes, "minute"), (secs, "second")):
        if value:
            out.append(f"{value} {unit}{'s' if value != 1 else ''}")
    return ", ".join(out) or "0 seconds"


def format_number(n) -> str:
    if n is None:
        return "N/A"
    try:
        n = int(n)
    except Exception:
        return str(n)
    if n >= 1_000_000:
        return f"{n / 1_000_000:.1f}M"
    if n >= 1_000:
        return f"{n / 1_000:.1f}K"
    return str(n)


def log(msg: str):
    print(f"[{datetime.now().strftime('%H:%M:%S')}] {msg}")


def flags_from_value(cls, value):
    try:
        return cls(value)
    except TypeError:
        pass
    try:
        obj = cls.__new__(cls)
        obj.value = int(value)
        return obj
    except Exception:
        return None


def perm_summary(perms: int) -> str:
    if perms & (1 << 3):
        return "Administrator"
    return f"{perms:,} perms"


def describe_channel(ch: dict) -> str:
    t = as_int(ch.get("type")) or 0
    name = ch.get("name", "?")
    return {
        0: f"#{name}",
        5: f"#{name} (announcement)",
        15: f"#{name} (forum)",
        2: f"🔊 {name}",
        13: f"🎙 {name}",
    }.get(t, f"{name} (type {t})")


def describe_real_channel(c: discord.abc.GuildChannel) -> str:
    if isinstance(c, discord.CategoryChannel):
        return f"📁 {c.name}"
    if c.type in (discord.ChannelType.voice, discord.ChannelType.stage_voice):
        return f"🔊 {c.name}"
    return f"#{c.name}"


async def try_edit(channel, *attempt_kwargs):
    for kwargs in attempt_kwargs:
        try:
            await channel.edit(**kwargs)
            return True
        except (TypeError, discord.HTTPException):
            continue
    return False


async def download_image(url: str) -> Optional[bytes]:
    try:
        async with aiohttp.ClientSession() as sess:
            async with sess.get(url) as resp:
                if resp.status == 200:
                    return await resp.read()
    except aiohttp.ClientError:
        pass
    return None


async def safe_reply(interaction: discord.Interaction, content: str, *, ephemeral: bool = True):
    if interaction.response.is_done():
        await interaction.followup.send(content, ephemeral=ephemeral)
    else:
        await interaction.response.send_message(content, ephemeral=ephemeral)


def hierarchy_error(source, target: discord.Member) -> Optional[str]:
    guild = source.guild
    moderator = source.user if isinstance(source, discord.Interaction) else source.author
    me = guild.me
    if target.id == me.id:
        return "❌ Nice try."
    if target.id == moderator.id:
        return "❌ You can't moderate yourself."
    if target.id == guild.owner_id:
        return "❌ You can't moderate the server owner."
    if moderator.id != guild.owner_id and target.top_role >= moderator.top_role:
        return "❌ You can't moderate someone with an equal or higher role."
    if target.top_role >= me.top_role:
        return "❌ That member's top role is ≥ mine — raise my role and try again."
    return None


def get_warns(guild_id: int, user_id: int) -> list:
    guild_cfg = config.setdefault(str(guild_id), {})
    return guild_cfg.setdefault("warnings", {}).setdefault(str(user_id), [])


def iso_to_ts(iso: str) -> int:
    try:
        return int(datetime.fromisoformat(iso).timestamp())
    except (ValueError, TypeError):
        return 0


async def modlog(source, action: str, target, reason: Optional[str], extra: str = "") -> None:
    if isinstance(source, discord.Interaction):
        guild, moderator = source.guild, source.user
    else:
        guild, moderator = source.guild, source.author
    channel_id = config.get(str(guild.id), {}).get("modlog_channel")
    if not channel_id:
        return
    channel = guild.get_channel(channel_id)
    if not isinstance(channel, discord.TextChannel):
        return
    embed = discord.Embed(
        title=f"🛡️ {action}",
        color=discord.Color.dark_red(),
        timestamp=discord.utils.utcnow(),
    )
    embed.add_field(name="User", value=f"{target.mention} (`{target.id}`)", inline=True)
    embed.add_field(name="Moderator", value=f"{moderator.mention} (`{moderator.id}`)", inline=True)
    if extra:
        embed.add_field(name="Details", value=extra, inline=False)
    embed.add_field(name="Reason", value=reason or "*No reason given*", inline=False)
    try:
        await channel.send(embed=embed)
    except discord.Forbidden:
        pass


# ---------------------------------------------------------------------------
# Database (TikTok history)
# ---------------------------------------------------------------------------
async def init_db():
    async with aiosqlite.connect(HISTORY_DB) as db:
        # Existing TikTok history
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                command TEXT,
                query TEXT,
                result_summary TEXT,
                timestamp TEXT
            )
            """
        )
        # Greed-style: economy (cash + bank, daily/work cooldowns)
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS economy (
                guild_id INTEGER NOT NULL,
                user_id  INTEGER NOT NULL,
                balance  INTEGER NOT NULL DEFAULT 0,
                bank     INTEGER NOT NULL DEFAULT 0,
                last_daily TEXT,
                last_work  TEXT,
                PRIMARY KEY (guild_id, user_id)
            )
            """
        )
        # Greed-style: leveling
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS levels (
                guild_id INTEGER NOT NULL,
                user_id  INTEGER NOT NULL,
                xp       INTEGER NOT NULL DEFAULT 0,
                messages INTEGER NOT NULL DEFAULT 0,
                PRIMARY KEY (guild_id, user_id)
            )
            """
        )
        # Greed-style: reminders
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS reminders (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL,
                guild_id INTEGER,
                channel_id INTEGER NOT NULL,
                remind_at TEXT NOT NULL,
                message TEXT,
                created_at TEXT
            )
            """
        )
        # Greed-style: birthdays
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS birthdays (
                guild_id INTEGER NOT NULL,
                user_id  INTEGER NOT NULL,
                month    INTEGER NOT NULL,
                day      INTEGER NOT NULL,
                PRIMARY KEY (guild_id, user_id)
            )
            """
        )
        # Greed-style: giveaways
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS giveaways (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                guild_id INTEGER NOT NULL,
                channel_id INTEGER NOT NULL,
                message_id INTEGER NOT NULL,
                prize TEXT,
                host_id INTEGER,
                ends_at TEXT NOT NULL,
                winners INTEGER DEFAULT 1,
                ended INTEGER DEFAULT 0
            )
            """
        )
        # Greed-style: AFK
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS afk (
                guild_id INTEGER NOT NULL,
                user_id  INTEGER NOT NULL,
                message  TEXT,
                since     TEXT,
                PRIMARY KEY (guild_id, user_id)
            )
            """
        )
        # Greed-style: starboard (so we don't repost the same message)
        await db.execute(
            """
            CREATE TABLE IF NOT EXISTS starboard_cache (
                guild_id INTEGER NOT NULL,
                source_message_id INTEGER NOT NULL,
                starboard_message_id INTEGER NOT NULL,
                stars INTEGER DEFAULT 0,
                PRIMARY KEY (guild_id, source_message_id)
            )
            """
        )
        await db.commit()


async def save_history(user_id: int, command: str, query: str, summary: str):
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO history (user_id, command, query, result_summary, timestamp) VALUES (?, ?, ?, ?, ?)",
            (user_id, command, query, summary, datetime.now(timezone.utc).isoformat()),
        )
        await db.commit()


# ===========================================================================
# EVENTS
# ===========================================================================
@bot.event
async def on_ready():
    global _bot_started_at
    await init_db()
    if _bot_started_at is None:
        _bot_started_at = datetime.now(timezone.utc)
    # Start Greed-style background loops (idempotent — skips if already running)
    for name, coro in (
        ("_reminder_loop", _reminder_loop),
        ("_birthday_loop", _birthday_loop),
        ("_giveaway_loop", _giveaway_loop),
    ):
        if not getattr(bot, name, None):
            setattr(bot, name, asyncio.create_task(coro()))
    print(f"Logged in as {bot.user} (ID: {bot.user.id})")
    print(f"Prefix: {PREFIX}  |  Slash commands registered globally")
    print(f"Dashboard → http://{DASHBOARD_HOST}:{DASHBOARD_PORT}/")
    try:
        await bot.change_presence(
            activity=discord.Activity(type=discord.ActivityType.watching, name=f"{PREFIX}help · {len(bot.guilds)} servers")
        )
    except Exception:
        pass

    # Instant per-guild sync so commands appear immediately
    for guild in bot.guilds:
        try:
            bot.tree.copy_global_to(guild=guild)
            await bot.tree.sync(guild=guild)
        except discord.HTTPException:
            pass
    print(f"Ready in {len(bot.guilds)} guild(s).")


@bot.event
async def on_guild_join(guild: discord.Guild):
    try:
        bot.tree.copy_global_to(guild=guild)
        await bot.tree.sync(guild=guild)
        print(f"Commands registered in '{guild.name}'.")
    except discord.HTTPException:
        pass


@bot.event
async def on_message_delete(message: discord.Message):
    if message.author.bot or not message.guild:
        return
    bot.snipe_cache[message.channel.id] = {
        "content": message.content or "*[no text content]*",
        "author": message.author,
        "created_at": message.created_at,
        "deleted_at": datetime.now(timezone.utc),
        "attachments": [a.url for a in message.attachments],
        "embeds": len(message.embeds),
    }


@bot.event
async def on_message(message: discord.Message):
    if message.author.bot:
        return
    content = message.content.lower()
    if "tiktok.com" in content or "vm.tiktok.com" in content:
        try:
            await message.add_reaction("📥")
        except Exception:
            pass

    if message.guild is not None:
        # Greed-style: gain XP per message (+ chance of level-up role)
        await _add_xp(message.guild.id, message.author.id, message.channel, message.author)
        # Greed-style: clear author's AFK on activity + reply to mentions of AFK users
        await _handle_afk_on_message(message)

    await bot.process_commands(message)


@bot.event
async def on_thread_create(thread: discord.Thread):
    """APK release announcer."""
    if thread.guild is None:
        return
    settings = config.get(str(thread.guild.id), {})
    apk_channel_id = settings.get("apk_channel")
    announce_channel_id = settings.get("announce_channel")
    if not apk_channel_id or not announce_channel_id:
        return
    if thread.parent_id != apk_channel_id:
        return
    announce_channel = thread.guild.get_channel(announce_channel_id)
    if not isinstance(announce_channel, discord.TextChannel):
        return
    role_id = settings.get("ping_role")
    role_mention = f"<@&{role_id}>" if role_id else ""
    content = f"{role_mention} 😍 APK released in {thread.mention}!"
    try:
        await announce_channel.send(
            content,
            allowed_mentions=discord.AllowedMentions(roles=True, everyone=False, users=False),
        )
    except discord.Forbidden:
        print(f"No permission to send in #{announce_channel.name}.")


# Greed-style: welcome new members + apply autorole
@bot.event
async def on_member_join(member: discord.Member):
    if member.bot or member.guild is None:
        return
    settings = config.get(str(member.guild.id), {})
    # Autorole
    role_id = settings.get("autorole")
    if role_id:
        role = member.guild.get_role(role_id)
        if role and role < member.guild.me.top_role and not role.managed:
            try:
                await member.add_roles(role, reason="Autorole")
            except discord.HTTPException:
                pass
    # Welcome message
    welcome_channel_id = settings.get("welcome_channel")
    welcome_msg = settings.get("welcome_message")
    if welcome_channel_id and welcome_msg:
        channel = member.guild.get_channel(welcome_channel_id)
        if isinstance(channel, discord.TextChannel):
            text = (
                welcome_msg
                .replace("{user}", member.mention)
                .replace("{server}", member.guild.name)
                .replace("{name}", member.display_name)
            )
            try:
                await channel.send(text)
            except discord.HTTPException:
                pass


# Greed-style: starboard (repost messages when they hit a star threshold)
@bot.event
async def on_raw_reaction_add(payload: discord.RawReactionActionEvent):
    if payload.user_id == bot.user.id or payload.guild_id is None:
        return
    if str(payload.emoji) != STAR_EMOJI:
        return
    guild = bot.get_guild(payload.guild_id)
    if guild is None:
        return
    settings = config.get(str(guild.id), {})
    sb_channel_id = settings.get("starboard_channel")
    if not sb_channel_id or payload.channel_id == sb_channel_id:
        return
    sb_channel = guild.get_channel(sb_channel_id)
    if not isinstance(sb_channel, discord.TextChannel):
        return
    threshold = int(settings.get("starboard_threshold", STAR_THRESHOLD) or STAR_THRESHOLD)
    channel = guild.get_channel(payload.channel_id)
    if not isinstance(channel, discord.TextChannel):
        return
    try:
        message = await channel.fetch_message(payload.message_id)
    except discord.HTTPException:
        return
    if message.author.id == payload.user_id:
        return  # don't count self-stars

    star_count = 0
    for r in message.reactions:
        if str(r.emoji) == STAR_EMOJI:
            async for u in r.users():
                if u.id != message.author.id and not u.bot:
                    star_count += 1
            break
    if star_count < threshold:
        return

    sb_msg_id = None
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT starboard_message_id FROM starboard_cache WHERE guild_id=? AND source_message_id=?",
            (guild.id, message.id),
        )
        row = await cur.fetchone()
        sb_msg_id = row[0] if row else None

    embed = discord.Embed(
        description=message.content or "*[media only]*",
        color=discord.Color.gold(),
        url=message.jump_url,
        timestamp=message.created_at,
    )
    embed.set_author(name=str(message.author), icon_url=message.author.display_avatar.url)
    embed.add_field(name="Source", value=f"[Jump]({message.jump_url})", inline=False)
    embed.add_field(name="Stars", value=f"⭐ {star_count}", inline=True)
    if message.attachments:
        a0 = message.attachments[0]
        if str(a0.url).lower().endswith((".png", ".jpg", ".jpeg", ".gif", ".webp")):
            embed.set_image(url=a0.url)

    if sb_msg_id:
        try:
            sb_msg = await sb_channel.fetch_message(sb_msg_id)
            await sb_msg.edit(content=f"⭐ {star_count} | {channel.mention}", embed=embed)
        except discord.HTTPException:
            sb_msg_id = None
    if not sb_msg_id:
        try:
            sb_msg = await sb_channel.send(content=f"⭐ {star_count} | {channel.mention}", embed=embed)
            async with aiosqlite.connect(HISTORY_DB) as db:
                await db.execute(
                    "INSERT OR REPLACE INTO starboard_cache (guild_id, source_message_id, starboard_message_id, stars) VALUES (?,?,?,?)",
                    (guild.id, message.id, sb_msg.id, star_count),
                )
                await db.commit()
        except discord.HTTPException:
            pass


# ===========================================================================
# ERROR HANDLERS
# ===========================================================================
@bot.tree.error
async def on_app_command_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.MissingPermissions):
        missing = ", ".join(p.replace("_", " ") for p in error.missing_permissions)
        msg = f"❌ You need **{missing}** permission."
    elif isinstance(error, app_commands.BotMissingPermissions):
        missing = ", ".join(p.replace("_", " ") for p in error.missing_permissions)
        msg = f"❌ I'm missing **{missing}** permission."
    elif isinstance(error, app_commands.NoPrivateMessage):
        msg = "❌ That command only works inside a server."
    elif isinstance(error, app_commands.CommandInvokeError) and isinstance(error.__cause__, discord.Forbidden):
        msg = "❌ Discord refused that action (role hierarchy or channel perms)."
    elif isinstance(error, app_commands.CommandInvokeError) and isinstance(error.__cause__, discord.HTTPException):
        msg = "⚠️ Discord API error — try again shortly."
    elif isinstance(error, app_commands.CheckFailure):
        msg = "❌ You can't use this command here."
    else:
        traceback.print_exc()
        msg = f"❌ Unexpected error: {type(error).__name__}"
    try:
        await safe_reply(interaction, msg)
    except discord.HTTPException:
        pass


@bot.event
async def on_command_error(ctx: commands.Context, error: commands.CommandError):
    if isinstance(error, commands.CommandNotFound):
        return
    if isinstance(error, commands.CommandOnCooldown):
        await ctx.reply(f"Slow down — try again in `{error.retry_after:.1f}s`.", mention_author=False, delete_after=5)
    elif isinstance(error, commands.MissingPermissions):
        missing = ", ".join(p.replace("_", " ") for p in error.missing_permissions)
        await ctx.reply(f"❌ You need **{missing}** permission.", mention_author=False)
    elif isinstance(error, commands.BotMissingPermissions):
        missing = ", ".join(p.replace("_", " ") for p in error.missing_permissions)
        await ctx.reply(f"❌ I'm missing **{missing}** permission.", mention_author=False)
    elif isinstance(error, (commands.MemberNotFound, commands.UserNotFound)):
        await ctx.reply("❌ Couldn't find that user.", mention_author=False)
    elif isinstance(error, commands.MissingRequiredArgument):
        await ctx.reply(
            f"❌ Missing `{error.param.name}` — usage: `{PREFIX}{ctx.command.name} {ctx.command.signature}`",
            mention_author=False,
        )
    elif isinstance(error, commands.CommandInvokeError) and isinstance(error.original, discord.Forbidden):
        await ctx.reply("❌ Discord refused that action (role hierarchy / channel perms).", mention_author=False)
    elif isinstance(error, commands.CheckFailure):
        await ctx.reply("❌ You can't use that command here.", mention_author=False)
    else:
        traceback.print_exc()


# ===========================================================================
# /set  — APK announcer + mod-log configuration
# ===========================================================================
@bot.tree.command(name="set", description="Configure APK announcer and mod log")
@app_commands.guild_only()
@app_commands.describe(
    apk_channel="Forum channel where APK releases are posted",
    ping_role="Role to ping when a new APK drops",
    announce_channel="Channel the announcement is sent to",
    modlog_channel="Channel where moderation actions are logged",
)
@app_commands.checks.has_permissions(administrator=True)
async def set_cmd(
    interaction: discord.Interaction,
    apk_channel: Optional[discord.ForumChannel] = None,
    ping_role: Optional[discord.Role] = None,
    announce_channel: Optional[discord.TextChannel] = None,
    modlog_channel: Optional[discord.TextChannel] = None,
):
    settings = config.setdefault(str(interaction.guild_id), {})
    if apk_channel is not None:
        settings["apk_channel"] = apk_channel.id
    if ping_role is not None:
        settings["ping_role"] = ping_role.id
    if announce_channel is not None:
        settings["announce_channel"] = announce_channel.id
    if modlog_channel is not None:
        settings["modlog_channel"] = modlog_channel.id
    save_config(config)

    def ch(cid):
        return f"<#{cid}>" if cid else "*Not set*"

    def role_str(rid):
        return f"<@&{rid}>" if rid else "*None*"

    embed = discord.Embed(title="⚙️ Settings", color=discord.Color.blurple())
    embed.add_field(name="APK forum", value=ch(settings.get("apk_channel")), inline=True)
    embed.add_field(name="Ping role", value=role_str(settings.get("ping_role")), inline=True)
    embed.add_field(name="Announce channel", value=ch(settings.get("announce_channel")), inline=True)
    embed.add_field(name="Mod log", value=ch(settings.get("modlog_channel")), inline=True)
    embed.set_footer(text="Leave an option out to keep its current value.")
    await interaction.response.send_message(embed=embed, ephemeral=True)


# ===========================================================================
# /roleall
# ===========================================================================
@bot.tree.command(name="roleall", description="Give (or remove) a role to/from every member")
@app_commands.guild_only()
@app_commands.describe(role="The role", remove="True = remove instead of give")
@app_commands.checks.has_permissions(administrator=True)
async def roleall_cmd(interaction: discord.Interaction, role: discord.Role, remove: bool = False):
    guild = interaction.guild
    me = guild.me
    if role.is_default():
        await interaction.response.send_message("❌ Can't mass-assign @everyone.", ephemeral=True)
        return
    if role.managed:
        await interaction.response.send_message("❌ That role is managed and can't be assigned manually.", ephemeral=True)
        return
    if role >= me.top_role:
        await interaction.response.send_message(
            f"❌ My top role must be **above** {role.mention}.", ephemeral=True
        )
        return

    await interaction.response.defer(ephemeral=True, thinking=True)
    verb = "Removing" if remove else "Giving"
    count, failed = 0, 0
    try:
        async for member in guild.fetch_members(limit=None):
            if member.bot:
                continue
            has_role = role in member.roles
            if (remove and has_role) or (not remove and not has_role):
                try:
                    if remove:
                        await member.remove_roles(role, reason=f"/roleall by {interaction.user}")
                    else:
                        await member.add_roles(role, reason=f"/roleall by {interaction.user}")
                    count += 1
                    if count % 25 == 0:
                        await interaction.edit_original_response(
                            content=f"{verb} **{role.name}** — {count} done…"
                        )
                    await asyncio.sleep(0.4)
                except discord.HTTPException:
                    failed += 1
    except discord.ClientException:
        await interaction.followup.send(
            "❌ **Server Members Intent** is off. Enable it in the Developer Portal.",
            ephemeral=True,
        )
        return

    done_verb = "removed from" if remove else "given to"
    result = f"✅ **{role.name}** {done_verb} **{count}** member(s)."
    if failed:
        result += f" ⚠️ {failed} failed."
    await interaction.followup.send(result, ephemeral=True)


# ===========================================================================
# Moderation — bans / kicks / timeouts / warnings (slash)
# ===========================================================================
@bot.tree.command(name="ban", description="Ban a user (works even if they already left)")
@app_commands.guild_only()
@app_commands.describe(
    user="User to ban (or paste raw ID)",
    reason="Reason",
    delete_messages="How much recent message history to delete",
    silent="Don't try to DM the user",
)
@app_commands.choices(
    delete_messages=[
        app_commands.Choice(name="Nothing", value=0),
        app_commands.Choice(name="Last hour", value=3600),
        app_commands.Choice(name="Last 6 hours", value=21600),
        app_commands.Choice(name="Last 24 hours", value=86400),
        app_commands.Choice(name="Last 7 days", value=604800),
    ]
)
@app_commands.checks.has_permissions(ban_members=True)
@app_commands.checks.bot_has_permissions(ban_members=True)
async def ban_cmd(
    interaction: discord.Interaction,
    user: discord.User,
    reason: Optional[str] = None,
    delete_messages: Optional[app_commands.Choice[int]] = None,
    silent: bool = False,
):
    guild = interaction.guild
    if user.id in (interaction.user.id, bot.user.id):
        await interaction.response.send_message("❌ Can't ban yourself / the bot.", ephemeral=True)
        return
    member = guild.get_member(user.id)
    if member is not None:
        err = hierarchy_error(interaction, member)
        if err:
            await interaction.response.send_message(err, ephemeral=True)
            return
    if not silent:
        try:
            await user.send(f"🚫 You were **banned** from **{guild.name}**.\nReason: {reason or 'No reason given'}")
        except (discord.Forbidden, discord.HTTPException):
            pass
    seconds = delete_messages.value if delete_messages else 0
    await guild.ban(user, reason=reason or f"/ban by {interaction.user}", delete_message_seconds=seconds)
    note = "" if member is not None else " *(user wasn't in the server)*"
    await interaction.response.send_message(f"🚫 Banned **{user}** (`{user.id}`).{note}", ephemeral=True)
    await modlog(
        interaction,
        "Ban",
        user,
        reason,
        extra=f"Deleted message history from the last {humanize_seconds(seconds)}." if seconds else "",
    )


@bot.tree.command(name="unban", description="Unban a user by ID")
@app_commands.guild_only()
@app_commands.describe(user_id="Banned user's ID", reason="Reason")
@app_commands.checks.has_permissions(ban_members=True)
@app_commands.checks.bot_has_permissions(ban_members=True)
async def unban_cmd(interaction: discord.Interaction, user_id: str, reason: Optional[str] = None):
    if not user_id.strip().isdigit():
        await interaction.response.send_message("❌ Paste numbers only.", ephemeral=True)
        return
    try:
        user = await bot.fetch_user(int(user_id.strip()))
    except discord.NotFound:
        await interaction.response.send_message("❌ No Discord user with that ID.", ephemeral=True)
        return
    try:
        await interaction.guild.unban(user, reason=reason or f"/unban by {interaction.user}")
    except discord.NotFound:
        await interaction.response.send_message(f"❌ **{user}** isn't banned here.", ephemeral=True)
        return
    await interaction.response.send_message(f"✅ Unbanned **{user}** (`{user.id}`).", ephemeral=True)
    await modlog(interaction, "Unban", user, reason)


@bot.tree.command(name="kick", description="Kick a member")
@app_commands.guild_only()
@app_commands.describe(member="Member to kick", reason="Reason", silent="Don't DM first")
@app_commands.checks.has_permissions(kick_members=True)
@app_commands.checks.bot_has_permissions(kick_members=True)
async def kick_cmd(
    interaction: discord.Interaction,
    member: discord.Member,
    reason: Optional[str] = None,
    silent: bool = False,
):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    if not silent:
        try:
            await member.send(
                f"👢 You were **kicked** from **{interaction.guild.name}**.\nReason: {reason or 'No reason given'}"
            )
        except (discord.Forbidden, discord.HTTPException):
            pass
    await member.kick(reason=reason or f"/kick by {interaction.user}")
    await interaction.response.send_message(f"👢 Kicked **{member}** (`{member.id}`).", ephemeral=True)
    await modlog(interaction, "Kick", member, reason)


TIMEOUT_CHOICES = [
    app_commands.Choice(name="5 minutes", value=5),
    app_commands.Choice(name="10 minutes", value=10),
    app_commands.Choice(name="30 minutes", value=30),
    app_commands.Choice(name="1 hour", value=60),
    app_commands.Choice(name="8 hours", value=480),
    app_commands.Choice(name="1 day", value=1440),
    app_commands.Choice(name="3 days", value=4320),
    app_commands.Choice(name="1 week", value=10080),
    app_commands.Choice(name="4 weeks (max)", value=40320),
]


@bot.tree.command(name="timeout", description="Timeout a member")
@app_commands.guild_only()
@app_commands.describe(member="Member", duration="How long", reason="Reason")
@app_commands.choices(duration=TIMEOUT_CHOICES)
@app_commands.checks.has_permissions(moderate_members=True)
@app_commands.checks.bot_has_permissions(moderate_members=True)
async def timeout_cmd(
    interaction: discord.Interaction,
    member: discord.Member,
    duration: app_commands.Choice[int],
    reason: Optional[str] = None,
):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    if member.guild_permissions.administrator:
        await interaction.response.send_message(
            "❌ Can't timeout members with Administrator permission.", ephemeral=True
        )
        return
    expires = discord.utils.utcnow() + timedelta(minutes=duration.value)
    await member.timeout(timedelta(minutes=duration.value), reason=reason or f"/timeout by {interaction.user}")
    ts = int(expires.timestamp())
    await interaction.response.send_message(
        f"🔇 Timed out **{member}** until <t:{ts}:f> (<t:{ts}:R>).", ephemeral=True
    )
    await modlog(interaction, "Timeout", member, reason, extra=f"Expires <t:{ts}:f> (<t:{ts}:R>)")


@bot.tree.command(name="untimeout", description="Remove a timeout early")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="Reason")
@app_commands.checks.has_permissions(moderate_members=True)
@app_commands.checks.bot_has_permissions(moderate_members=True)
async def untimeout_cmd(interaction: discord.Interaction, member: discord.Member, reason: Optional[str] = None):
    if not member.is_timed_out():
        await interaction.response.send_message(f"❌ **{member}** isn't timed out.", ephemeral=True)
        return
    await member.timeout(None, reason=reason or f"/untimeout by {interaction.user}")
    await interaction.response.send_message(f"🔊 Removed timeout from **{member}**.", ephemeral=True)
    await modlog(interaction, "Untimeout", member, reason)


@bot.tree.command(name="warn", description="Issue a warning")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="What they did")
@app_commands.checks.has_permissions(moderate_members=True)
async def warn_cmd(interaction: discord.Interaction, member: discord.Member, reason: str):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    warns = get_warns(interaction.guild_id, member.id)
    warns.append(
        {
            "reason": reason,
            "mod": interaction.user.id,
            "time": discord.utils.utcnow().isoformat(),
        }
    )
    save_config(config)
    try:
        await member.send(f"⚠️ You were warned in **{interaction.guild.name}**.\nReason: {reason}")
    except (discord.Forbidden, discord.HTTPException):
        pass
    await interaction.response.send_message(
        f"⚠️ Warned **{member}** — they now have **{len(warns)}** warning(s).", ephemeral=True
    )
    await modlog(interaction, f"Warning #{len(warns)}", member, reason)


@bot.tree.command(name="warnings", description="Show a member's warnings")
@app_commands.guild_only()
@app_commands.describe(member="Whose warnings")
@app_commands.checks.has_permissions(moderate_members=True)
async def warnings_cmd(interaction: discord.Interaction, member: discord.Member):
    warns = config.get(str(interaction.guild_id), {}).get("warnings", {}).get(str(member.id), [])
    if not warns:
        await interaction.response.send_message(f"✅ **{member}** has a clean record.", ephemeral=True)
        return
    shown = warns[-10:]
    start = len(warns) - len(shown) + 1
    lines = []
    for i, w in enumerate(shown, start=start):
        ts = iso_to_ts(w.get("time", ""))
        when = f"<t:{ts}:R>" if ts else "unknown time"
        lines.append(f"`#{i}` • {when} • {w.get('reason', '*no reason*')} — <@{w.get('mod', '?')}>")
    embed = discord.Embed(
        title=f"⚠️ Warnings — {member} ({len(warns)} total)",
        description="\n".join(lines),
        color=discord.Color.orange(),
    )
    if len(warns) > len(shown):
        embed.set_footer(text="Only showing the 10 most recent.")
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="clearwarnings", description="Remove one or all warnings")
@app_commands.guild_only()
@app_commands.describe(member="Member", warning="Warning number (empty = clear all)")
@app_commands.checks.has_permissions(moderate_members=True)
async def clearwarnings_cmd(
    interaction: discord.Interaction,
    member: discord.Member,
    warning: Optional[app_commands.Range[int, 1]] = None,
):
    warns = get_warns(interaction.guild_id, member.id)
    if not warns:
        await interaction.response.send_message(f"✅ **{member}** has no warnings.", ephemeral=True)
        return
    if warning is None:
        count = len(warns)
        warns.clear()
        msg = f"🗑️ Cleared all **{count}** warning(s) from **{member}**."
    elif warning <= len(warns):
        removed = warns.pop(warning - 1)
        msg = f"🗑️ Removed warning **#{warning}** ({removed.get('reason', '?')}) from **{member}**."
    else:
        await interaction.response.send_message(
            f"❌ Warning number must be between 1 and {len(warns)}.", ephemeral=True
        )
        return
    save_config(config)
    await interaction.response.send_message(msg, ephemeral=True)


# ===========================================================================
# Channel tools
# ===========================================================================
@bot.tree.command(name="purge", description="Bulk-delete messages")
@app_commands.guild_only()
@app_commands.describe(
    amount="How many (1–100)",
    member="Only this member's messages",
    bots_only="Only bot/webhook messages",
)
@app_commands.checks.has_permissions(manage_messages=True)
@app_commands.checks.bot_has_permissions(manage_messages=True, read_message_history=True)
async def purge_cmd(
    interaction: discord.Interaction,
    amount: app_commands.Range[int, 1, 100],
    member: Optional[discord.Member] = None,
    bots_only: bool = False,
):
    await interaction.response.defer(ephemeral=True)
    channel = interaction.channel
    filtering = member is not None or bots_only
    remaining = amount

    def check(m: discord.Message) -> bool:
        nonlocal remaining
        if remaining <= 0:
            return False
        ok = True
        if member is not None:
            ok = m.author.id == member.id
        if ok and bots_only:
            ok = m.author.bot or m.webhook_id is not None
        if ok:
            remaining -= 1
        return ok

    try:
        deleted = await channel.purge(limit=1000 if filtering else amount, check=check)
    except discord.Forbidden:
        await interaction.followup.send("❌ Missing permissions to delete messages here.", ephemeral=True)
        return
    except discord.HTTPException:
        await interaction.followup.send(
            "⚠️ Some messages couldn't be deleted (older than 14 days can't be bulk-deleted).",
            ephemeral=True,
        )
        return
    await interaction.followup.send(f"🧹 Deleted **{len(deleted)}** message(s).", ephemeral=True)
    await modlog(interaction, "Purge", interaction.user, None, extra=f"Deleted {len(deleted)} in {channel.mention}")


@bot.tree.command(name="slowmode", description="Set channel slowmode")
@app_commands.guild_only()
@app_commands.describe(seconds="0 = off, max 21600 (6 h)", channel="Channel (default: this one)")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def slowmode_cmd(
    interaction: discord.Interaction,
    seconds: app_commands.Range[int, 0, 21600],
    channel: Optional[discord.TextChannel] = None,
):
    target = channel or interaction.channel
    if not isinstance(target, discord.TextChannel):
        await interaction.response.send_message("❌ Only works on text channels.", ephemeral=True)
        return
    await target.edit(slowmode_delay=seconds, reason=f"/slowmode by {interaction.user}")
    await interaction.response.send_message(
        f"🐢 Slowmode in {target.mention} → **{humanize_seconds(seconds)}**.", ephemeral=True
    )
    await modlog(interaction, "Slowmode", interaction.user, None, extra=f"{target.mention} → {humanize_seconds(seconds)}")


@bot.tree.command(name="lock", description="Lock a channel (@everyone can't send)")
@app_commands.guild_only()
@app_commands.describe(channel="Channel (default: this one)", reason="Reason")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def lock_cmd(
    interaction: discord.Interaction,
    channel: Optional[discord.TextChannel] = None,
    reason: Optional[str] = None,
):
    target = channel or interaction.channel
    if not isinstance(target, discord.TextChannel):
        await interaction.response.send_message("❌ Only text channels.", ephemeral=True)
        return
    overwrite = target.overwrites_for(interaction.guild.default_role)
    if overwrite.send_messages is False:
        await interaction.response.send_message(f"ℹ️ {target.mention} is already locked.", ephemeral=True)
        return
    overwrite.send_messages = False
    await target.set_permissions(
        interaction.guild.default_role, overwrite=overwrite, reason=reason or f"/lock by {interaction.user}"
    )
    await interaction.response.send_message(f"🔒 Locked {target.mention}.", ephemeral=True)
    await modlog(interaction, "Channel lock", interaction.user, reason, extra=target.mention)


@bot.tree.command(name="unlock", description="Unlock a channel")
@app_commands.guild_only()
@app_commands.describe(channel="Channel (default: this one)", reason="Reason")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def unlock_cmd(
    interaction: discord.Interaction,
    channel: Optional[discord.TextChannel] = None,
    reason: Optional[str] = None,
):
    target = channel or interaction.channel
    if not isinstance(target, discord.TextChannel):
        await interaction.response.send_message("❌ Only text channels.", ephemeral=True)
        return
    overwrite = target.overwrites_for(interaction.guild.default_role)
    if overwrite.send_messages is not False:
        await interaction.response.send_message(f"ℹ️ {target.mention} isn't locked.", ephemeral=True)
        return
    overwrite.send_messages = None
    await target.set_permissions(
        interaction.guild.default_role, overwrite=overwrite, reason=reason or f"/unlock by {interaction.user}"
    )
    await interaction.response.send_message(f"✅ Unlocked {target.mention}.", ephemeral=True)
    await modlog(interaction, "Channel unlock", interaction.user, reason, extra=target.mention)


@bot.command(name="lock")
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def lock_prefix(ctx: commands.Context, *, reason: Optional[str] = None):
    """.lock [reason] — @everyone can't send here (admins still can)."""
    target = ctx.channel
    if not isinstance(target, discord.TextChannel):
        await ctx.reply("❌ Only text channels.", mention_author=False)
        return
    overwrite = target.overwrites_for(ctx.guild.default_role)
    if overwrite.send_messages is False:
        await ctx.reply(f"ℹ️ {target.mention} is already locked.", mention_author=False)
        return
    overwrite.send_messages = False
    await target.set_permissions(
        ctx.guild.default_role, overwrite=overwrite, reason=reason or f".lock by {ctx.author}"
    )
    await ctx.send(f"🔒 {target.mention} is locked. Only admins can send messages.")
    await modlog(ctx, "Channel lock", ctx.author, reason, extra=target.mention)


@bot.command(name="unlock")
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def unlock_prefix(ctx: commands.Context, *, reason: Optional[str] = None):
    """.unlock [reason] — restore @everyone's ability to send here."""
    target = ctx.channel
    if not isinstance(target, discord.TextChannel):
        await ctx.reply("❌ Only text channels.", mention_author=False)
        return
    overwrite = target.overwrites_for(ctx.guild.default_role)
    if overwrite.send_messages is not False:
        await ctx.reply(f"ℹ️ {target.mention} isn't locked.", mention_author=False)
        return
    overwrite.send_messages = None
    await target.set_permissions(
        ctx.guild.default_role, overwrite=overwrite, reason=reason or f".unlock by {ctx.author}"
    )
    await ctx.send(f"🔓 {target.mention} is unlocked.")
    await modlog(ctx, "Channel unlock", ctx.author, reason, extra=target.mention)


# ===========================================================================
# Prefix moderation (.kick / .to / .ban)
# ===========================================================================
DURATION_UNITS = {"s": 1, "m": 60, "h": 3600, "d": 86400, "w": 604800}


def parse_duration(text: str) -> Optional[timedelta]:
    matches = re.findall(r"(\d+)\s*([smhdw])", text.lower().strip())
    if not matches:
        return None
    total = sum(int(value) * DURATION_UNITS[unit] for value, unit in matches)
    if total <= 0:
        return None
    return timedelta(seconds=total)


@bot.command(name="kick")
@commands.guild_only()
@commands.has_permissions(kick_members=True)
@commands.bot_has_permissions(kick_members=True)
async def kick_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    try:
        await member.send(f"👢 You were **kicked** from **{ctx.guild.name}**.\nReason: {reason or 'No reason given'}")
    except (discord.Forbidden, discord.HTTPException):
        pass
    await member.kick(reason=reason or f".kick by {ctx.author}")
    await ctx.reply(f"👢 Kicked **{member}** (`{member.id}`).", mention_author=False)
    await modlog(ctx, "Kick", member, reason)


@bot.command(name="to")
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(moderate_members=True)
async def timeout_prefix(
    ctx: commands.Context, member: discord.Member, duration: str, *, reason: Optional[str] = None
):
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    if member.guild_permissions.administrator:
        await ctx.reply("❌ Can't timeout members with Administrator.", mention_author=False)
        return
    delta = parse_duration(duration)
    if delta is None or delta < timedelta(seconds=60) or delta > timedelta(days=28):
        await ctx.reply(
            "❌ Invalid duration. Use `30s`, `10m`, `1h`, `2d`, `1w` (or combos). Min 1 min, max 28 days.",
            mention_author=False,
        )
        return
    expires = discord.utils.utcnow() + delta
    await member.timeout(delta, reason=reason or f".to by {ctx.author}")
    ts = int(expires.timestamp())
    await ctx.reply(f"🔇 Timed out **{member}** until <t:{ts}:f> (<t:{ts}:R>).", mention_author=False)
    await modlog(ctx, "Timeout", member, reason, extra=f"Expires <t:{ts}:f> (<t:{ts}:R>)")


@bot.command(name="ban")
@commands.guild_only()
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def ban_prefix(ctx: commands.Context, user: discord.User, *, reason: Optional[str] = None):
    if user.id in (ctx.author.id, bot.user.id):
        await ctx.reply("❌ Can't ban yourself / the bot.", mention_author=False)
        return
    member = ctx.guild.get_member(user.id)
    if member is not None:
        err = hierarchy_error(ctx, member)
        if err:
            await ctx.reply(err, mention_author=False)
            return
    try:
        await user.send(f"🚫 You were **banned** from **{ctx.guild.name}**.\nReason: {reason or 'No reason given'}")
    except (discord.Forbidden, discord.HTTPException):
        pass
    await ctx.guild.ban(user, reason=reason or f"{PREFIX}ban by {ctx.author}")
    note = "" if member is not None else " *(user wasn't in the server)*"
    await ctx.reply(f"🚫 Banned **{user}** (`{user.id}`).{note}", mention_author=False)
    await modlog(ctx, "Ban", user, reason)


# ===========================================================================
# EXTRA MODERATION (slash + prefix)
#  • mute / unmute      — role-based mute (separate from Discord timeout)
#  • softban            — ban + unban to wipe messages then kick
#  • nuke               — clone + delete a channel (clears ALL history)
#  • hide / unhide      — toggle @everyone view on a channel
#  • lockdown / unlockdown — lock / unlock every text channel
#  • addrole / removerole — give / take a role from a member
#  • voicekick          — disconnect a member from voice
#  • move               — move a member between voice channels
#  • nick / clearnick   — set / reset a member's nickname
#  • roleinfo / channelinfo / serverinfo(slash) / userinfo(slash)
#  • prefix versions of: purge, slowmode, unban, untimeout, warn,
#    warnings, clearwarnings, set
# ===========================================================================

# ---- helpers shared by slash + prefix ----
def _get_mute_role(guild: discord.Guild) -> Optional[discord.Role]:
    """Return the configured mute role (or None)."""
    rid = config.get(str(guild.id), {}).get("mute_role")
    if rid:
        r = guild.get_role(rid)
        if r is not None:
            return r
    # Fallback: look for a role named 'muted' (case-insensitive)
    for r in guild.roles:
        if r.name.lower() == "muted":
            return r
    return None


async def _ensure_mute_role(guild: discord.Guild) -> Optional[discord.Role]:
    """Create + configure a Muted role if none exists."""
    role = _get_mute_role(guild)
    if role is not None:
        return role
    try:
        role = await guild.create_role(
            name="Muted",
            permissions=discord.Permissions(send_messages=False, send_messages_in_threads=False,
                                            add_reactions=False, speak=False, stream=False),
            reason=f"Mute role auto-created by {guild.me}",
        )
    except discord.Forbidden:
        return None
    config.setdefault(str(guild.id), {})["mute_role"] = role.id
    save_config(config)
    # Apply "Muted can't speak" to every text + voice channel
    for ch in guild.channels:
        try:
            if isinstance(ch, discord.TextChannel):
                ow = ch.overwrites_for(role)
                ow.send_messages = False
                ow.add_reactions = False
                await ch.set_permissions(role, overwrite=ow, reason="Auto-mute setup")
            elif isinstance(ch, (discord.VoiceChannel, discord.StageChannel)):
                ow = ch.overwrites_for(role)
                ow.speak = False
                ow.stream = False
                await ch.set_permissions(role, overwrite=ow, reason="Auto-mute setup")
        except discord.HTTPException:
            pass
    return role


# ----------------------- SLASH -----------------------

@bot.tree.command(name="mute", description="Role-mute a member (lasts until /unmute)")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="Reason")
@app_commands.checks.has_permissions(moderate_members=True)
@app_commands.checks.bot_has_permissions(manage_roles=True)
async def mute_cmd(interaction: discord.Interaction,
                  member: discord.Member,
                  reason: Optional[str] = None):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    role = await _ensure_mute_role(interaction.guild)
    if role is None:
        await interaction.response.send_message("❌ I can't create the Muted role (need Manage Roles).", ephemeral=True)
        return
    if role >= interaction.guild.me.top_role:
        await interaction.response.send_message("❌ My top role must be above the Muted role.", ephemeral=True)
        return
    if role in member.roles:
        await interaction.response.send_message(f"🔇 {member.mention} is already muted.", ephemeral=True)
        return
    try:
        await member.add_roles(role, reason=reason or f"/mute by {interaction.user}")
    except discord.HTTPException:
        await interaction.response.send_message("❌ Couldn't add the Muted role.", ephemeral=True)
        return
    await interaction.response.send_message(f"🔇 Muted **{member}**.", ephemeral=True)
    try:
        await member.send(f"🔇 You were **muted** in **{interaction.guild.name}**.\nReason: {reason or 'No reason given'}")
    except discord.HTTPException:
        pass
    await modlog(interaction, "Mute", member, reason)


@bot.tree.command(name="unmute", description="Remove role mute")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="Reason")
@app_commands.checks.has_permissions(moderate_members=True)
@app_commands.checks.bot_has_permissions(manage_roles=True)
async def unmute_cmd(interaction: discord.Interaction,
                    member: discord.Member,
                    reason: Optional[str] = None):
    role = _get_mute_role(interaction.guild)
    if role is None or role not in member.roles:
        await interaction.response.send_message(f"❌ **{member}** isn't muted.", ephemeral=True)
        return
    try:
        await member.remove_roles(role, reason=reason or f"/unmute by {interaction.user}")
    except discord.HTTPException:
        await interaction.response.send_message("❌ Couldn't remove the Muted role.", ephemeral=True)
        return
    await interaction.response.send_message(f"🔊 Unmuted **{member}**.", ephemeral=True)
    await modlog(interaction, "Unmute", member, reason)


@bot.tree.command(name="softban", description="Ban + unban to wipe messages and kick the user")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="Reason")
@app_commands.checks.has_permissions(ban_members=True)
@app_commands.checks.bot_has_permissions(ban_members=True)
async def softban_cmd(interaction: discord.Interaction,
                     member: discord.Member,
                     reason: Optional[str] = None):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    await interaction.guild.ban(member, reason=reason or f"/softban by {interaction.user}", delete_message_days=1)
    await interaction.guild.unban(member, reason=f"/softban unban by {interaction.user}")
    await interaction.response.send_message(f"💨 Soft-banned **{member}** (messages wiped).", ephemeral=True)
    try:
        await member.send(f"💨 You were **soft-banned** (kicked + messages wiped) from **{interaction.guild.name}**.\nReason: {reason or 'No reason given'}")
    except discord.HTTPException:
        pass
    await modlog(interaction, "Softban", member, reason)


@bot.tree.command(name="nuke", description="Clone this channel and delete the old one (wipes ALL history)")
@app_commands.guild_only()
@app_commands.describe(channel="Channel to nuke (default: this one)")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def nuke_cmd(interaction: discord.Interaction,
                  channel: Optional[discord.TextChannel] = None):
    target = channel or interaction.channel
    if not isinstance(target, discord.TextChannel):
        await interaction.response.send_message("❌ Only text channels.", ephemeral=True)
        return
    await interaction.response.defer(ephemeral=True)
    pos = target.position
    try:
        new_ch = await target.clone(reason=f"/nuke by {interaction.user}")
        await new_ch.edit(position=pos)
        await target.delete(reason=f"/nuke by {interaction.user}")
    except discord.HTTPException as e:
        await interaction.followup.send(f"❌ Nuke failed: {e}", ephemeral=True)
        return
    await new_ch.send(f"💥 Channel nuked by {interaction.user.mention}.", delete_after=10)
    await modlog(interaction, "Nuke", interaction.user, None, extra=new_ch.mention)


@bot.tree.command(name="hide", description="Hide a channel from @everyone")
@app_commands.guild_only()
@app_commands.describe(channel="Channel (default: this one)", reason="Reason")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def hide_cmd(interaction: discord.Interaction,
                  channel: Optional[discord.TextChannel] = None,
                  reason: Optional[str] = None):
    target = channel or interaction.channel
    ow = target.overwrites_for(interaction.guild.default_role)
    if ow.view_channel is False:
        await interaction.response.send_message(f"ℹ️ {target.mention} is already hidden.", ephemeral=True)
        return
    ow.view_channel = False
    await target.set_permissions(interaction.guild.default_role, overwrite=ow, reason=reason or f"/hide by {interaction.user}")
    await interaction.response.send_message(f"👁️‍🗨️ Hid {target.mention}.", ephemeral=True)
    await modlog(interaction, "Channel hide", interaction.user, reason, extra=target.mention)


@bot.tree.command(name="unhide", description="Show a hidden channel to @everyone")
@app_commands.guild_only()
@app_commands.describe(channel="Channel (default: this one)", reason="Reason")
@app_commands.checks.has_permissions(manage_channels=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def unhide_cmd(interaction: discord.Interaction,
                    channel: Optional[discord.TextChannel] = None,
                    reason: Optional[str] = None):
    target = channel or interaction.channel
    ow = target.overwrites_for(interaction.guild.default_role)
    if ow.view_channel is not False:
        await interaction.response.send_message(f"ℹ️ {target.mention} isn't hidden.", ephemeral=True)
        return
    ow.view_channel = None
    await target.set_permissions(interaction.guild.default_role, overwrite=ow, reason=reason or f"/unhide by {interaction.user}")
    await interaction.response.send_message(f"👁️ Unhid {target.mention}.", ephemeral=True)
    await modlog(interaction, "Channel unhide", interaction.user, reason, extra=target.mention)


@bot.tree.command(name="lockdown", description="Lock every text channel (emergency)")
@app_commands.guild_only()
@app_commands.checks.has_permissions(administrator=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def lockdown_cmd(interaction: discord.Interaction, reason: Optional[str] = None):
    await interaction.response.defer(ephemeral=True)
    count = 0
    for ch in interaction.guild.text_channels:
        ow = ch.overwrites_for(interaction.guild.default_role)
        if ow.send_messages is not False:
            ow.send_messages = False
            try:
                await ch.set_permissions(interaction.guild.default_role, overwrite=ow, reason=reason or f"/lockdown by {interaction.user}")
                count += 1
            except discord.HTTPException:
                pass
    await interaction.followup.send(f"🔒 Locked **{count}** text channel(s).", ephemeral=True)
    await modlog(interaction, "Lockdown", interaction.user, reason, extra=f"{count} channels")


@bot.tree.command(name="unlockdown", description="Undo a /lockdown")
@app_commands.guild_only()
@app_commands.checks.has_permissions(administrator=True)
@app_commands.checks.bot_has_permissions(manage_channels=True)
async def unlockdown_cmd(interaction: discord.Interaction, reason: Optional[str] = None):
    await interaction.response.defer(ephemeral=True)
    count = 0
    for ch in interaction.guild.text_channels:
        ow = ch.overwrites_for(interaction.guild.default_role)
        if ow.send_messages is False:
            ow.send_messages = None
            try:
                await ch.set_permissions(interaction.guild.default_role, overwrite=ow, reason=reason or f"/unlockdown by {interaction.user}")
                count += 1
            except discord.HTTPException:
                pass
    await interaction.followup.send(f"🔓 Unlocked **{count}** text channel(s).", ephemeral=True)
    await modlog(interaction, "Unlockdown", interaction.user, reason, extra=f"{count} channels")


@bot.tree.command(name="addrole", description="Give a role to a member")
@app_commands.guild_only()
@app_commands.describe(member="Member", role="Role to give", reason="Reason")
@app_commands.checks.has_permissions(manage_roles=True)
@app_commands.checks.bot_has_permissions(manage_roles=True)
async def addrole_cmd(interaction: discord.Interaction,
                     member: discord.Member,
                     role: discord.Role,
                     reason: Optional[str] = None):
    if role.is_default() or role.managed:
        await interaction.response.send_message("❌ Can't use @everyone or a managed role.", ephemeral=True)
        return
    if role >= interaction.guild.me.top_role:
        await interaction.response.send_message(f"❌ My top role must be above {role.mention}.", ephemeral=True)
        return
    if role in member.roles:
        await interaction.response.send_message(f"ℹ️ {member.mention} already has {role.mention}.", ephemeral=True)
        return
    await member.add_roles(role, reason=reason or f"/addrole by {interaction.user}")
    await interaction.response.send_message(f"✅ Added {role.mention} to {member.mention}.", ephemeral=True)
    await modlog(interaction, "Addrole", member, reason, extra=role.mention)


@bot.tree.command(name="removerole", description="Remove a role from a member")
@app_commands.guild_only()
@app_commands.describe(member="Member", role="Role to remove", reason="Reason")
@app_commands.checks.has_permissions(manage_roles=True)
@app_commands.checks.bot_has_permissions(manage_roles=True)
async def removerole_cmd(interaction: discord.Interaction,
                        member: discord.Member,
                        role: discord.Role,
                        reason: Optional[str] = None):
    if role not in member.roles:
        await interaction.response.send_message(f"ℹ️ {member.mention} doesn't have {role.mention}.", ephemeral=True)
        return
    await member.remove_roles(role, reason=reason or f"/removerole by {interaction.user}")
    await interaction.response.send_message(f"✅ Removed {role.mention} from {member.mention}.", ephemeral=True)
    await modlog(interaction, "Removerole", member, reason, extra=role.mention)


@bot.tree.command(name="voicekick", description="Disconnect a member from voice")
@app_commands.guild_only()
@app_commands.describe(member="Member", reason="Reason")
@app_commands.checks.has_permissions(mute_members=True)
async def voicekick_cmd(interaction: discord.Interaction,
                       member: discord.Member,
                       reason: Optional[str] = None):
    if member.voice is None or member.voice.channel is None:
        await interaction.response.send_message(f"❌ {member.mention} isn't in a voice channel.", ephemeral=True)
        return
    try:
        await member.move_to(None, reason=reason or f"/voicekick by {interaction.user}")
    except discord.HTTPException:
        await interaction.response.send_message("❌ Couldn't disconnect them.", ephemeral=True)
        return
    await interaction.response.send_message(f"🔊 Disconnected **{member}** from voice.", ephemeral=True)
    await modlog(interaction, "Voicekick", member, reason)


@bot.tree.command(name="move", description="Move a member to another voice channel")
@app_commands.guild_only()
@app_commands.describe(member="Member", channel="Destination voice channel", reason="Reason")
@app_commands.checks.has_permissions(move_members=True)
@app_commands.checks.bot_has_permissions(move_members=True)
async def move_cmd(interaction: discord.Interaction,
                  member: discord.Member,
                  channel: discord.VoiceChannel,
                  reason: Optional[str] = None):
    if member.voice is None or member.voice.channel is None:
        await interaction.response.send_message(f"❌ {member.mention} isn't in a voice channel.", ephemeral=True)
        return
    if member.voice.channel.id == channel.id:
        await interaction.response.send_message("ℹ️ They're already in that channel.", ephemeral=True)
        return
    try:
        await member.move_to(channel, reason=reason or f"/move by {interaction.user}")
    except discord.HTTPException:
        await interaction.response.send_message("❌ Couldn't move them.", ephemeral=True)
        return
    await interaction.response.send_message(f"➡️ Moved **{member}** to {channel.mention}.", ephemeral=True)
    await modlog(interaction, "Move", member, reason, extra=channel.mention)


@bot.tree.command(name="nick", description="Change a member's nickname")
@app_commands.guild_only()
@app_commands.describe(member="Member", nickname="New nickname (leave empty to clear)", reason="Reason")
@app_commands.checks.has_permissions(manage_nicknames=True)
@app_commands.checks.bot_has_permissions(manage_nicknames=True)
async def nick_cmd(interaction: discord.Interaction,
                   member: discord.Member,
                   nickname: Optional[str] = None,
                   reason: Optional[str] = None):
    err = hierarchy_error(interaction, member)
    if err:
        await interaction.response.send_message(err, ephemeral=True)
        return
    new_nick = (nickname or None) if nickname else None
    try:
        await member.edit(nick=new_nick, reason=reason or f"/nick by {interaction.user}")
    except discord.HTTPException:
        await interaction.response.send_message("❌ Couldn't change nickname.", ephemeral=True)
        return
    if new_nick:
        await interaction.response.send_message(f"✏️ {member.mention} is now **{new_nick}**.", ephemeral=True)
    else:
        await interaction.response.send_message(f"✏️ Reset {member.mention}'s nickname.", ephemeral=True)
    await modlog(interaction, "Nickname", member, reason, extra=new_nick or "(cleared)")


@bot.tree.command(name="roleinfo", description="Show information about a role")
@app_commands.guild_only()
@app_commands.describe(role="Role")
async def roleinfo_cmd(interaction: discord.Interaction, role: discord.Role):
    embed = discord.Embed(title=f"🎭 {role.name}", color=role.color or 0x2F3136)
    embed.add_field(name="ID", value=role.id, inline=True)
    embed.add_field(name="Members", value=len(role.members), inline=True)
    embed.add_field(name="Color", value=str(role.color), inline=True)
    embed.add_field(name="Hoisted", value="Yes" if role.hoist else "No", inline=True)
    embed.add_field(name="Mentionable", value="Yes" if role.mentionable else "No", inline=True)
    embed.add_field(name="Position", value=role.position, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(role.created_at, "R"), inline=False)
    perms = ", ".join(p.replace("_", " ").title() for p, v in role.permissions if v) or "—"
    embed.add_field(name="Permissions", value=perms[:1024], inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="channelinfo", description="Show information about a channel")
@app_commands.guild_only()
@app_commands.describe(channel="Channel (default: this one)")
async def channelinfo_cmd(interaction: discord.Interaction,
                          channel: Optional[discord.abc.GuildChannel] = None):
    ch = channel or interaction.channel
    embed = discord.Embed(title=f"# {ch.name}", color=0x5865F2)
    embed.add_field(name="ID", value=ch.id, inline=True)
    embed.add_field(name="Type", value=str(ch.type).replace("ChannelType.", ""), inline=True)
    embed.add_field(name="Position", value=ch.position, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(ch.created_at, "R"), inline=False)
    if isinstance(ch, discord.TextChannel):
        embed.add_field(name="Topic", value=ch.topic or "—", inline=False)
        embed.add_field(name="Slowmode", value=humanize_seconds(ch.slowmode_delay), inline=True)
        embed.add_field(name="NSFW", value="Yes" if ch.nsfw else "No", inline=True)
    if ch.category:
        embed.add_field(name="Category", value=ch.category.name, inline=True)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="serverinfo", description="Show server info (slash)")
@app_commands.guild_only()
async def serverinfo_cmd(interaction: discord.Interaction):
    guild = interaction.guild
    embed = discord.Embed(title=guild.name, color=0x5865F2)
    if guild.icon:
        embed.set_thumbnail(url=guild.icon.url)
    embed.add_field(name="Owner", value=guild.owner.mention if guild.owner else "Unknown", inline=True)
    embed.add_field(name="Members", value=guild.member_count, inline=True)
    embed.add_field(name="Boost Level", value=guild.premium_tier, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(guild.created_at, "R"), inline=True)
    embed.add_field(name="Channels", value=len(guild.channels), inline=True)
    embed.add_field(name="Roles", value=len(guild.roles), inline=True)
    embed.add_field(name="Emojis", value=len(guild.emojis), inline=True)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="userinfo", description="Show user info (slash)")
@app_commands.guild_only()
@app_commands.describe(member="Member (default: you)")
async def userinfo_cmd(interaction: discord.Interaction, member: Optional[discord.Member] = None):
    member = member or interaction.user
    embed = discord.Embed(color=member.color or 0x2F3136)
    embed.set_author(name=str(member), icon_url=member.display_avatar.url)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="ID", value=member.id, inline=True)
    embed.add_field(name="Nickname", value=member.nick or "None", inline=True)
    embed.add_field(name="Bot?", value="Yes" if member.bot else "No", inline=True)
    embed.add_field(name="Account Created", value=discord.utils.format_dt(member.created_at, "R"), inline=True)
    embed.add_field(name="Joined Server", value=discord.utils.format_dt(member.joined_at, "R") if member.joined_at else "Unknown", inline=True)
    roles = [r.mention for r in member.roles if r != interaction.guild.default_role]
    embed.add_field(name=f"Roles [{len(roles)}]", value=" ".join(roles) if roles else "None", inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="muterole", description="Set which role /mute uses (admins)")
@app_commands.guild_only()
@app_commands.describe(role="Role to use as the mute role")
@app_commands.checks.has_permissions(manage_guild=True)
async def muterole_cmd(interaction: discord.Interaction, role: discord.Role):
    config.setdefault(str(interaction.guild_id), {})["mute_role"] = role.id
    save_config(config)
    await interaction.response.send_message(f"🔇 Mute role set to {role.mention}.", ephemeral=True)


# ----------------------- PREFIX -----------------------

@bot.command(name="unban")
@commands.guild_only()
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def unban_prefix(ctx: commands.Context, user_id: str, *, reason: Optional[str] = None):
    """`,unban <user_id> [reason]`"""
    if not user_id.strip().isdigit():
        await ctx.reply("❌ Paste numbers only.", mention_author=False)
        return
    try:
        user = await bot.fetch_user(int(user_id.strip()))
    except discord.NotFound:
        await ctx.reply("❌ No Discord user with that ID.", mention_author=False)
        return
    try:
        await ctx.guild.unban(user, reason=reason or f"{PREFIX}unban by {ctx.author}")
    except discord.NotFound:
        await ctx.reply(f"❌ **{user}** isn't banned here.", mention_author=False)
        return
    await ctx.reply(f"✅ Unbanned **{user}** (`{user.id}`).", mention_author=False)
    await modlog(ctx, "Unban", user, reason)


@bot.command(name="untimeout")
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(moderate_members=True)
async def untimeout_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    """`,untimeout @member [reason]`"""
    if not member.is_timed_out():
        await ctx.reply(f"❌ **{member}** isn't timed out.", mention_author=False)
        return
    await member.timeout(None, reason=reason or f"{PREFIX}untimeout by {ctx.author}")
    await ctx.reply(f"🔊 Removed timeout from **{member}**.", mention_author=False)
    await modlog(ctx, "Untimeout", member, reason)


@bot.command(name="warn")
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
async def warn_prefix(ctx: commands.Context, member: discord.Member, *, reason: str):
    """`,warn @member <reason>`"""
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    warns = get_warns(ctx.guild.id, member.id)
    warns.append({"reason": reason, "mod": ctx.author.id, "time": discord.utils.utcnow().isoformat()})
    save_config(config)
    try:
        await member.send(f"⚠️ You were warned in **{ctx.guild.name}**.\nReason: {reason}")
    except discord.HTTPException:
        pass
    await ctx.reply(f"⚠️ Warned **{member}** — they now have **{len(warns)}** warning(s).", mention_author=False)
    await modlog(ctx, f"Warning #{len(warns)}", member, reason)


@bot.command(name="warnings", aliases=["warns"])
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
async def warnings_prefix(ctx: commands.Context, member: discord.Member):
    """`,warnings @member`"""
    warns = config.get(str(ctx.guild.id), {}).get("warnings", {}).get(str(member.id), [])
    if not warns:
        await ctx.reply(f"✅ **{member}** has a clean record.", mention_author=False)
        return
    lines = []
    for i, w in enumerate(warns[-10:], start=max(1, len(warns) - 9)):
        ts = iso_to_ts(w.get("time", ""))
        when = f"<t:{ts}:R>" if ts else "unknown"
        lines.append(f"`#{i}` • {when} • {w.get('reason', '*no reason*')} — <@{w.get('mod', '?')}>")
    embed = discord.Embed(title=f"⚠️ Warnings — {member} ({len(warns)} total)",
                          description="\n".join(lines), color=discord.Color.orange())
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="clearwarnings", aliases=["clearwarns"])
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
async def clearwarnings_prefix(ctx: commands.Context, member: discord.Member, warning: Optional[int] = None):
    """`,clearwarnings @member [#]`"""
    warns = get_warns(ctx.guild.id, member.id)
    if not warns:
        await ctx.reply(f"✅ **{member}** has no warnings.", mention_author=False)
        return
    if warning is None:
        count = len(warns)
        warns.clear()
        msg = f"🗑️ Cleared all **{count}** warning(s) from **{member}**."
    elif 1 <= warning <= len(warns):
        removed = warns.pop(warning - 1)
        msg = f"🗑️ Removed warning **#{warning}** ({removed.get('reason', '?')}) from **{member}**."
    else:
        await ctx.reply(f"❌ Warning number must be between 1 and {len(warns)}.", mention_author=False)
        return
    save_config(config)
    await ctx.reply(msg, mention_author=False)


@bot.command(name="purge", aliases=["clear", "clean"])
@commands.guild_only()
@commands.has_permissions(manage_messages=True)
@commands.bot_has_permissions(manage_messages=True, read_message_history=True)
async def purge_prefix(ctx: commands.Context, amount: int, member: Optional[discord.Member] = None, *, bots_only: Optional[str] = None):
    """`,purge <amount> [@member|bots]`"""
    if amount < 1 or amount > 100:
        await ctx.reply("❌ Use a number between 1 and 100.", mention_author=False)
        return
    await ctx.message.delete()
    bots_flag = (bots_only or "").lower() == "bots"
    remaining = amount

    def check(m: discord.Message) -> bool:
        nonlocal remaining
        if remaining <= 0:
            return False
        ok = True
        if member is not None:
            ok = m.author.id == member.id
        if ok and bots_flag:
            ok = m.author.bot or m.webhook_id is not None
        if ok:
            remaining -= 1
        return ok

    try:
        deleted = await ctx.channel.purge(limit=1000 if (member or bots_flag) else amount, check=check)
    except discord.HTTPException:
        await ctx.reply("⚠️ Some messages older than 14 days couldn't be deleted.", mention_author=False, delete_after=8)
        return
    await ctx.send(f"🧹 Deleted **{len(deleted)}** message(s).", delete_after=8)
    await modlog(ctx, "Purge", ctx.author, None, extra=f"Deleted {len(deleted)} in {ctx.channel.mention}")


@bot.command(name="slowmode", aliases=["sm"])
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def slowmode_prefix(ctx: commands.Context, seconds: int, channel: Optional[discord.TextChannel] = None):
    """`,slowmode <seconds|0> [#channel]`"""
    if seconds < 0 or seconds > 21600:
        await ctx.reply("❌ Use 0–21600 seconds.", mention_author=False)
        return
    target = channel or ctx.channel
    if not isinstance(target, discord.TextChannel):
        await ctx.reply("❌ Only text channels.", mention_author=False)
        return
    await target.edit(slowmode_delay=seconds, reason=f"{PREFIX}slowmode by {ctx.author}")
    await ctx.reply(f"🐢 Slowmode in {target.mention} → **{humanize_seconds(seconds)}**.", mention_author=False)
    await modlog(ctx, "Slowmode", ctx.author, None, extra=f"{target.mention} → {humanize_seconds(seconds)}")


@bot.command(name="mute")
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(manage_roles=True)
async def mute_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    """`,mute @member [reason]`"""
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    role = await _ensure_mute_role(ctx.guild)
    if role is None:
        await ctx.reply("❌ I can't create the Muted role (need Manage Roles).", mention_author=False)
        return
    if role >= ctx.guild.me.top_role:
        await ctx.reply("❌ My top role must be above the Muted role.", mention_author=False)
        return
    if role in member.roles:
        await ctx.reply(f"🔇 {member.mention} is already muted.", mention_author=False)
        return
    await member.add_roles(role, reason=reason or f"{PREFIX}mute by {ctx.author}")
    await ctx.reply(f"🔇 Muted **{member}**.", mention_author=False)
    try:
        await member.send(f"🔇 You were **muted** in **{ctx.guild.name}**.\nReason: {reason or 'No reason given'}")
    except discord.HTTPException:
        pass
    await modlog(ctx, "Mute", member, reason)


@bot.command(name="unmute")
@commands.guild_only()
@commands.has_permissions(moderate_members=True)
@commands.bot_has_permissions(manage_roles=True)
async def unmute_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    """`,unmute @member [reason]`"""
    role = _get_mute_role(ctx.guild)
    if role is None or role not in member.roles:
        await ctx.reply(f"❌ **{member}** isn't muted.", mention_author=False)
        return
    await member.remove_roles(role, reason=reason or f"{PREFIX}unmute by {ctx.author}")
    await ctx.reply(f"🔊 Unmuted **{member}**.", mention_author=False)
    await modlog(ctx, "Unmute", member, reason)


@bot.command(name="softban", aliases=["sb"])
@commands.guild_only()
@commands.has_permissions(ban_members=True)
@commands.bot_has_permissions(ban_members=True)
async def softban_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    """`,softban @member [reason]`"""
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    await ctx.guild.ban(member, reason=reason or f"{PREFIX}softban by {ctx.author}", delete_message_days=1)
    await ctx.guild.unban(member, reason=f"{PREFIX}softban unban by {ctx.author}")
    await ctx.reply(f"💨 Soft-banned **{member}** (messages wiped).", mention_author=False)
    try:
        await member.send(f"💨 You were **soft-banned** (kicked + messages wiped) from **{ctx.guild.name}**.\nReason: {reason or 'No reason given'}")
    except discord.HTTPException:
        pass
    await modlog(ctx, "Softban", member, reason)


@bot.command(name="nuke")
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def nuke_prefix(ctx: commands.Context, channel: Optional[discord.TextChannel] = None):
    """`,nuke [#channel]`"""
    target = channel or ctx.channel
    if not isinstance(target, discord.TextChannel):
        await ctx.reply("❌ Only text channels.", mention_author=False)
        return
    pos = target.position
    try:
        new_ch = await target.clone(reason=f"{PREFIX}nuke by {ctx.author}")
        await new_ch.edit(position=pos)
        await target.delete(reason=f"{PREFIX}nuke by {ctx.author}")
    except discord.HTTPException as e:
        await ctx.reply(f"❌ Nuke failed: {e}", mention_author=False)
        return
    await new_ch.send(f"💥 Channel nuked by {ctx.author.mention}.", delete_after=10)
    await modlog(ctx, "Nuke", ctx.author, None, extra=new_ch.mention)


@bot.command(name="hide")
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def hide_prefix(ctx: commands.Context, channel: Optional[discord.TextChannel] = None, *, reason: Optional[str] = None):
    """`,hide [#channel] [reason]`"""
    target = channel or ctx.channel
    ow = target.overwrites_for(ctx.guild.default_role)
    if ow.view_channel is False:
        await ctx.reply(f"ℹ️ {target.mention} is already hidden.", mention_author=False)
        return
    ow.view_channel = False
    await target.set_permissions(ctx.guild.default_role, overwrite=ow, reason=reason or f"{PREFIX}hide by {ctx.author}")
    await ctx.reply(f"👁️‍🗨️ Hid {target.mention}.", mention_author=False)
    await modlog(ctx, "Channel hide", ctx.author, reason, extra=target.mention)


@bot.command(name="unhide")
@commands.guild_only()
@commands.has_permissions(manage_channels=True)
@commands.bot_has_permissions(manage_channels=True)
async def unhide_prefix(ctx: commands.Context, channel: Optional[discord.TextChannel] = None, *, reason: Optional[str] = None):
    """`,unhide [#channel] [reason]`"""
    target = channel or ctx.channel
    ow = target.overwrites_for(ctx.guild.default_role)
    if ow.view_channel is not False:
        await ctx.reply(f"ℹ️ {target.mention} isn't hidden.", mention_author=False)
        return
    ow.view_channel = None
    await target.set_permissions(ctx.guild.default_role, overwrite=ow, reason=reason or f"{PREFIX}unhide by {ctx.author}")
    await ctx.reply(f"👁️ Unhid {target.mention}.", mention_author=False)
    await modlog(ctx, "Channel unhide", ctx.author, reason, extra=target.mention)


@bot.command(name="lockdown")
@commands.guild_only()
@commands.has_permissions(administrator=True)
@commands.bot_has_permissions(manage_channels=True)
async def lockdown_prefix(ctx: commands.Context, *, reason: Optional[str] = None):
    """`,lockdown [reason] — lock every text channel"""
    msg = await ctx.reply("🔒 Locking down…")
    count = 0
    for ch in ctx.guild.text_channels:
        ow = ch.overwrites_for(ctx.guild.default_role)
        if ow.send_messages is not False:
            ow.send_messages = False
            try:
                await ch.set_permissions(ctx.guild.default_role, overwrite=ow, reason=reason or f"{PREFIX}lockdown by {ctx.author}")
                count += 1
            except discord.HTTPException:
                pass
    await msg.edit(content=f"🔒 Locked **{count}** text channel(s).")
    await modlog(ctx, "Lockdown", ctx.author, reason, extra=f"{count} channels")


@bot.command(name="unlockdown")
@commands.guild_only()
@commands.has_permissions(administrator=True)
@commands.bot_has_permissions(manage_channels=True)
async def unlockdown_prefix(ctx: commands.Context, *, reason: Optional[str] = None):
    """`,unlockdown [reason]"""
    msg = await ctx.reply("🔓 Unlocking…")
    count = 0
    for ch in ctx.guild.text_channels:
        ow = ch.overwrites_for(ctx.guild.default_role)
        if ow.send_messages is False:
            ow.send_messages = None
            try:
                await ch.set_permissions(ctx.guild.default_role, overwrite=ow, reason=reason or f"{PREFIX}unlockdown by {ctx.author}")
                count += 1
            except discord.HTTPException:
                pass
    await msg.edit(content=f"🔓 Unlocked **{count}** text channel(s).")
    await modlog(ctx, "Unlockdown", ctx.author, reason, extra=f"{count} channels")


@bot.command(name="addrole", aliases=["roleadd"])
@commands.guild_only()
@commands.has_permissions(manage_roles=True)
@commands.bot_has_permissions(manage_roles=True)
async def addrole_prefix(ctx: commands.Context, member: discord.Member, role: discord.Role, *, reason: Optional[str] = None):
    """`,addrole @member @role [reason]`"""
    if role.is_default() or role.managed:
        await ctx.reply("❌ Can't use @everyone or a managed role.", mention_author=False)
        return
    if role >= ctx.guild.me.top_role:
        await ctx.reply(f"❌ My top role must be above {role.mention}.", mention_author=False)
        return
    if role in member.roles:
        await ctx.reply(f"ℹ️ {member.mention} already has {role.mention}.", mention_author=False)
        return
    await member.add_roles(role, reason=reason or f"{PREFIX}addrole by {ctx.author}")
    await ctx.reply(f"✅ Added {role.mention} to {member.mention}.", mention_author=False)
    await modlog(ctx, "Addrole", member, reason, extra=role.mention)


@bot.command(name="removerole", aliases=["roleremove"])
@commands.guild_only()
@commands.has_permissions(manage_roles=True)
@commands.bot_has_permissions(manage_roles=True)
async def removerole_prefix(ctx: commands.Context, member: discord.Member, role: discord.Role, *, reason: Optional[str] = None):
    """`,removerole @member @role [reason]`"""
    if role not in member.roles:
        await ctx.reply(f"ℹ️ {member.mention} doesn't have {role.mention}.", mention_author=False)
        return
    await member.remove_roles(role, reason=reason or f"{PREFIX}removerole by {ctx.author}")
    await ctx.reply(f"✅ Removed {role.mention} from {member.mention}.", mention_author=False)
    await modlog(ctx, "Removerole", member, reason, extra=role.mention)


@bot.command(name="voicekick", aliases=["vckick"])
@commands.guild_only()
@commands.has_permissions(mute_members=True)
async def voicekick_prefix(ctx: commands.Context, member: discord.Member, *, reason: Optional[str] = None):
    """`,voicekick @member [reason]"""
    if member.voice is None or member.voice.channel is None:
        await ctx.reply(f"❌ {member.mention} isn't in a voice channel.", mention_author=False)
        return
    try:
        await member.move_to(None, reason=reason or f"{PREFIX}voicekick by {ctx.author}")
    except discord.HTTPException:
        await ctx.reply("❌ Couldn't disconnect them.", mention_author=False)
        return
    await ctx.reply(f"🔊 Disconnected **{member}** from voice.", mention_author=False)
    await modlog(ctx, "Voicekick", member, reason)


@bot.command(name="move", aliases=["vcmove"])
@commands.guild_only()
@commands.has_permissions(move_members=True)
@commands.bot_has_permissions(move_members=True)
async def move_prefix(ctx: commands.Context, member: discord.Member, channel: discord.VoiceChannel, *, reason: Optional[str] = None):
    """`,move @member #voicechannel [reason]`"""
    if member.voice is None or member.voice.channel is None:
        await ctx.reply(f"❌ {member.mention} isn't in a voice channel.", mention_author=False)
        return
    if member.voice.channel.id == channel.id:
        await ctx.reply("ℹ️ They're already in that channel.", mention_author=False)
        return
    try:
        await member.move_to(channel, reason=reason or f"{PREFIX}move by {ctx.author}")
    except discord.HTTPException:
        await ctx.reply("❌ Couldn't move them.", mention_author=False)
        return
    await ctx.reply(f"➡️ Moved **{member}** to {channel.mention}.", mention_author=False)
    await modlog(ctx, "Move", member, reason, extra=channel.mention)


@bot.command(name="nick", aliases=["nickname", "setnick"])
@commands.guild_only()
@commands.has_permissions(manage_nicknames=True)
@commands.bot_has_permissions(manage_nicknames=True)
async def nick_prefix(ctx: commands.Context, member: discord.Member, *, nickname: Optional[str] = None):
    """`,nick @member [new nickname]`"""
    err = hierarchy_error(ctx, member)
    if err:
        await ctx.reply(err, mention_author=False)
        return
    new_nick = nickname.strip() if nickname else None
    try:
        await member.edit(nick=new_nick or None, reason=f"{PREFIX}nick by {ctx.author}")
    except discord.HTTPException:
        await ctx.reply("❌ Couldn't change nickname.", mention_author=False)
        return
    if new_nick:
        await ctx.reply(f"✏️ {member.mention} is now **{new_nick}**.", mention_author=False)
    else:
        await ctx.reply(f"✏️ Reset {member.mention}'s nickname.", mention_author=False)
    await modlog(ctx, "Nickname", member, None, extra=new_nick or "(cleared)")


@bot.command(name="roleinfo", aliases=["role"])
@commands.guild_only()
async def roleinfo_prefix(ctx: commands.Context, role: discord.Role):
    """`,roleinfo @role`"""
    embed = discord.Embed(title=f"🎭 {role.name}", color=role.color or 0x2F3136)
    embed.add_field(name="ID", value=role.id, inline=True)
    embed.add_field(name="Members", value=len(role.members), inline=True)
    embed.add_field(name="Color", value=str(role.color), inline=True)
    embed.add_field(name="Hoisted", value="Yes" if role.hoist else "No", inline=True)
    embed.add_field(name="Mentionable", value="Yes" if role.mentionable else "No", inline=True)
    embed.add_field(name="Position", value=role.position, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(role.created_at, "R"), inline=False)
    perms = ", ".join(p.replace("_", " ").title() for p, v in role.permissions if v) or "—"
    embed.add_field(name="Permissions", value=perms[:1024], inline=False)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="channelinfo", aliases=["cinfo"])
@commands.guild_only()
async def channelinfo_prefix(ctx: commands.Context, channel: Optional[discord.abc.GuildChannel] = None):
    """`,channelinfo [#channel]`"""
    ch = channel or ctx.channel
    embed = discord.Embed(title=f"# {ch.name}", color=0x5865F2)
    embed.add_field(name="ID", value=ch.id, inline=True)
    embed.add_field(name="Type", value=str(ch.type).replace("ChannelType.", ""), inline=True)
    embed.add_field(name="Position", value=ch.position, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(ch.created_at, "R"), inline=False)
    if isinstance(ch, discord.TextChannel):
        embed.add_field(name="Topic", value=ch.topic or "—", inline=False)
        embed.add_field(name="Slowmode", value=humanize_seconds(ch.slowmode_delay), inline=True)
        embed.add_field(name="NSFW", value="Yes" if ch.nsfw else "No", inline=True)
    if ch.category:
        embed.add_field(name="Category", value=ch.category.name, inline=True)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="muterole")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def muterole_prefix(ctx: commands.Context, role: discord.Role):
    """`,muterole @role`"""
    config.setdefault(str(ctx.guild.id), {})["mute_role"] = role.id
    save_config(config)
    await ctx.reply(f"🔇 Mute role set to {role.mention}.", mention_author=False)


# ===========================================================================
# Snipe + utility prefix commands
# ===========================================================================
@bot.command(name="snipe", aliases=["s"])
@commands.cooldown(1, 4, commands.BucketType.channel)
async def snipe(ctx: commands.Context):
    data = bot.snipe_cache.get(ctx.channel.id)
    if not data:
        return await ctx.send("There's nothing to snipe here.")
    age = datetime.now(timezone.utc) - data["deleted_at"]
    if age > timedelta(seconds=SNIPE_TIMEOUT):
        del bot.snipe_cache[ctx.channel.id]
        return await ctx.send("That message is too old to snipe.")
    embed = discord.Embed(description=data["content"], color=0x2F3136, timestamp=data["created_at"])
    embed.set_author(name=str(data["author"]), icon_url=data["author"].display_avatar.url)
    embed.set_footer(text=f"Deleted {discord.utils.format_dt(data['deleted_at'], 'R')}")
    if data["attachments"]:
        embed.add_field(name="Attachments", value="\n".join(data["attachments"][:5]), inline=False)
        first = data["attachments"][0].lower()
        if first.endswith((".png", ".jpg", ".jpeg", ".gif", ".webp")):
            embed.set_image(url=data["attachments"][0])
    if data["embeds"]:
        embed.add_field(name="Embeds", value=str(data["embeds"]), inline=True)
    await ctx.send(embed=embed)


@bot.command(name="clearsnipe", aliases=["cs"])
@commands.has_permissions(manage_messages=True)
async def clearsnipe(ctx: commands.Context):
    if ctx.channel.id in bot.snipe_cache:
        del bot.snipe_cache[ctx.channel.id]
        await ctx.send("Snipe cache cleared.")
    else:
        await ctx.send("Nothing to clear.")


@bot.command(name="ping")
async def ping(ctx: commands.Context):
    latency = round(bot.latency * 1000)
    await ctx.send(f"Pong! `{latency}ms`")


@bot.command(name="userinfo", aliases=["ui", "whois"])
async def userinfo(ctx: commands.Context, member: discord.Member = None):
    member = member or ctx.author
    embed = discord.Embed(color=member.color or 0x2F3136)
    embed.set_author(name=str(member), icon_url=member.display_avatar.url)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="ID", value=member.id, inline=True)
    embed.add_field(name="Nickname", value=member.nick or "None", inline=True)
    embed.add_field(name="Bot?", value="Yes" if member.bot else "No", inline=True)
    embed.add_field(name="Account Created", value=discord.utils.format_dt(member.created_at, "R"), inline=True)
    embed.add_field(
        name="Joined Server",
        value=discord.utils.format_dt(member.joined_at, "R") if member.joined_at else "Unknown",
        inline=True,
    )
    roles = [r.mention for r in member.roles if r != ctx.guild.default_role]
    embed.add_field(name=f"Roles [{len(roles)}]", value=" ".join(roles) if roles else "None", inline=False)
    await ctx.send(embed=embed)


@bot.command(name="avatar", aliases=["av", "pfp"])
async def avatar(ctx: commands.Context, member: discord.Member = None):
    member = member or ctx.author
    embed = discord.Embed(title=f"{member}'s Avatar", color=member.color or 0x2F3136)
    embed.set_image(url=member.display_avatar.url)
    await ctx.send(embed=embed)


@bot.command(name="serverinfo", aliases=["si", "guildinfo"])
async def serverinfo(ctx: commands.Context):
    guild = ctx.guild
    embed = discord.Embed(title=guild.name, color=0x5865F2)
    if guild.icon:
        embed.set_thumbnail(url=guild.icon.url)
    embed.add_field(name="Owner", value=guild.owner.mention if guild.owner else "Unknown", inline=True)
    embed.add_field(name="Members", value=guild.member_count, inline=True)
    embed.add_field(name="Boost Level", value=guild.premium_tier, inline=True)
    embed.add_field(name="Created", value=discord.utils.format_dt(guild.created_at, "R"), inline=True)
    embed.add_field(name="Channels", value=len(guild.channels), inline=True)
    embed.add_field(name="Roles", value=len(guild.roles), inline=True)
    await ctx.send(embed=embed)


@bot.command(name="help", aliases=["h", "commands"])
async def help_command(ctx: commands.Context):
    embed = discord.Embed(
        title="Merged Bot — Commands",
        description=f"Prefix: `{PREFIX}`  ·  All slash commands also have a `{PREFIX}` prefix version",
        color=0x5865F2,
    )
    embed.add_field(
        name="🛡️ Moderation",
        value=(
            f"`{PREFIX}ban /unban /kick /softban`\n"
            f"`{PREFIX}timeout /untimeout /mute /unmute`\n"
            f"`{PREFIX}warn /warnings /clearwarnings`\n"
            f"`{PREFIX}purge /slowmode /lock /unlock /hide /unhide`\n"
            f"`{PREFIX}nuke /lockdown /unlockdown`\n"
            f"`{PREFIX}addrole /removerole /muterole`\n"
            f"`{PREFIX}voicekick /move /nick`\n"
            f"`{PREFIX}roleall /roleinfo /channelinfo`\n"
            f"`{PREFIX}userinfo /serverinfo`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🎵 Music",
        value=(
            f"`{PREFIX}play` (empty = default Spotify playlist)\n"
            f"`{PREFIX}skip /pause /resume /stop`\n"
            f"`{PREFIX}queue /np /volume /loop /leave`"
        ),
        inline=False,
    )
    embed.add_field(
        name="💰 Economy & gamble",
        value=(
            f"`{PREFIX}balance /daily /work`\n"
            f"`{PREFIX}pay /deposit /withdraw`\n"
            f"`{PREFIX}coinflip /dice /slots /scratch /blackjack`\n"
            f"`{PREFIX}leaderboard`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📈 Levels / AFK / Fun",
        value=(
            f"`{PREFIX}rank /levels /levelconfig`\n"
            f"`{PREFIX}afk`\n"
            f"`{PREFIX}rps /8ball /roll /poll`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🎁 Engagement",
        value=(
            f"`{PREFIX}giveaway start|end|reroll`\n"
            f"`{PREFIX}remind /reminders /cancelreminder`\n"
            f"`{PREFIX}bday set|list|channel`\n"
            f"`{PREFIX}starboard /welcome /autorole`"
        ),
        inline=False,
    )
    embed.add_field(
        name="📱 TikTok",
        value=(
            f"`{PREFIX}lookup /reversevid /search /uservideos /download /sound /history`"
        ),
        inline=False,
    )
    embed.add_field(
        name="🛠️ Templates & misc",
        value=(
            f"`{PREFIX}pull /apply` — server templates (e.g. `{PREFIX}apply ABC123 confirm=true`)\n"
            f"`{PREFIX}set apk_channel=#ch ping_role=@role announce_channel=#ch modlog_channel=#ch`\n"
            f"`{PREFIX}roleall @role [remove=true]`\n"
            f"`{PREFIX}snipe /clearsnipe /ping`\n"
            f"`{PREFIX}help` — this message"
        ),
        inline=False,
    )
    embed.set_footer(text="Most commands also work as slash commands (e.g. /ban, /play, /daily).")
    await ctx.send(embed=embed)


# ===========================================================================
# SERVER TEMPLATE TOOLS (core of server_copier, as slash commands)
# ===========================================================================
def parse_template_code(text: str) -> str:
    text = text.strip().rstrip("/").split("?")[0].split("#")[0]
    if "/" in text:
        text = text.rsplit("/", 1)[-1]
    if not re.fullmatch(r"[A-Za-z0-9]+", text):
        raise ValueError(f"That doesn't look like a template link/code: {text!r}")
    return text


async def fetch_template_by_code(code: str) -> dict:
    ua = {"User-Agent": "merged-bot/1.0"}
    attempts = [
        (f"{API}/guilds/templates/{code}", {**ua, "Authorization": f"Bot {TOKEN}"}),
        (f"{API}/guilds/templates/{code}", ua),
        (f"{API}/templates/{code}", {**ua, "Authorization": f"Bot {TOKEN}"}),
        (f"{API}/templates/{code}", ua),
    ]
    async with aiohttp.ClientSession() as session:
        for url, headers in attempts:
            async with session.get(url, headers=headers) as resp:
                if resp.status == 200:
                    return await resp.json()
    raise RuntimeError(
        f"Couldn't fetch template '{code}'. Check the link/code and that the template still exists."
    )


async def load_template(ref: str) -> dict:
    ref = ref.strip().strip('"').strip("'")
    if os.path.isfile(ref):
        with open(ref, encoding="utf-8") as f:
            data = json.load(f)
        if "serialized_source_guild" in data:
            return data
        if "channels" in data or "roles" in data:
            return {"name": f"(from {os.path.basename(ref)})", "serialized_source_guild": data}
        raise RuntimeError(f"{ref} doesn't look like a saved template file.")
    code = parse_template_code(ref)
    return await fetch_template_by_code(code)


def compare_data(guild: discord.Guild, template: dict) -> dict:
    src = template["serialized_source_guild"]
    tmpl_roles = [r for r in src.get("roles", []) if r.get("name") != "@everyone"]
    tmpl_role_names = {(r.get("name") or "").lower() for r in tmpl_roles}
    roles_create, roles_update = [], []
    for r in tmpl_roles:
        name = r.get("name") or "?"
        found = discord.utils.get(guild.roles, name=name)
        (roles_update if found else roles_create).append(name)
    roles_extra = [
        r.name
        for r in guild.roles
        if r.name.lower() not in tmpl_role_names and r != guild.default_role and not r.managed
    ]

    tmpl_chans = src.get("channels", [])
    chan_create, chan_update = [], []
    tmpl_chan_keys = set()
    for ch in tmpl_chans:
        t = as_int(ch.get("type")) or 0
        name = ch.get("name") or "?"
        tmpl_chan_keys.add((name.lower(), t))
        if t == 4:
            found = discord.utils.find(
                lambda c: isinstance(c, discord.CategoryChannel) and c.name.lower() == name.lower(),
                guild.channels,
            )
        else:
            found = discord.utils.find(
                lambda c: c.name.lower() == name.lower() and c.type.value == t, guild.channels
            )
        (chan_update if found else chan_create).append(describe_channel(ch))
    chans_extra = [
        describe_real_channel(c)
        for c in guild.channels
        if (c.name.lower(), c.type.value) not in tmpl_chan_keys
    ]

    name_change = None
    if src.get("name") and src["name"] != guild.name:
        name_change = (guild.name, src["name"])

    return {
        "roles_create": roles_create,
        "roles_update": roles_update,
        "roles_extra": roles_extra,
        "chan_create": chan_create,
        "chan_update": chan_update,
        "chans_extra": chans_extra,
        "name_change": name_change,
    }


def _bullet_list(items, limit=12):
    if not items:
        return "—"
    shown = [f"• {i}" for i in items[:limit]]
    if len(items) > limit:
        shown.append(f"…and {len(items) - limit} more")
    return "\n".join(shown)


async def apply_roles(guild: discord.Guild, src: dict, stats: dict) -> dict:
    role_map = {}
    for r in src.get("roles", []):
        name = r.get("name") or ""
        rid = as_int(r.get("id"))
        perms = discord.Permissions(as_int(r.get("permissions")) or 0)
        if name == "@everyone":
            if rid is not None:
                role_map[rid] = guild.default_role
            try:
                await guild.default_role.edit(permissions=perms, reason=REASON)
            except Exception:
                pass
            continue
        fields = dict(
            name=name,
            permissions=perms,
            colour=discord.Colour(as_int(r.get("color")) or 0),
            hoist=bool(r.get("hoist", False)),
            mentionable=bool(r.get("mentionable", False)),
        )
        existing = discord.utils.get(guild.roles, name=name)
        try:
            if existing is None:
                existing = await guild.create_role(reason=REASON, **fields)
                stats["roles_created"] += 1
            else:
                await existing.edit(reason=REASON, **fields)
                stats["roles_updated"] += 1
        except Exception:
            if existing is None:
                continue
        if rid is not None:
            role_map[rid] = existing
    return role_map


async def apply_role_order(guild: discord.Guild, src: dict, role_map: dict):
    positions, pos = {}, 1
    for r in src.get("roles", []):
        if r.get("name") == "@everyone":
            continue
        real = role_map.get(as_int(r.get("id")))
        if real is not None and real != guild.default_role:
            positions[real] = pos
            pos += 1
    if positions:
        try:
            await guild.edit_role_positions(positions, reason=REASON)
        except Exception:
            pass


async def resolve_overwrites(guild: discord.Guild, ch: dict, role_map: dict):
    pairs = []
    for o in ch.get("permission_overwrites") or []:
        otype = as_int(o.get("type")) or 0
        tid = as_int(o.get("id"))
        allow = discord.Permissions(as_int(o.get("allow")) or 0)
        deny = discord.Permissions(as_int(o.get("deny")) or 0)
        if otype == 0:
            target = role_map.get(tid)
        else:
            target = guild.get_member(tid)
            if target is None:
                try:
                    target = await guild.fetch_member(tid)
                except Exception:
                    target = None
        if target is not None:
            pairs.append((target, allow, deny))
    return pairs


def overwrite_map(pairs):
    return {t: discord.PermissionOverwrite.from_pair(a, d) for t, a, d in pairs}


def raw_overwrites(pairs):
    return [
        {
            "id": str(t.id),
            "type": "0" if isinstance(t, discord.Role) else "1",
            "allow": str(a.value),
            "deny": str(d.value),
        }
        for t, a, d in pairs
    ]


async def create_channel_via_api(client, guild, ch, parent, pairs):
    t = as_int(ch.get("type")) or 0
    payload = {
        "name": ch.get("name") or "channel",
        "type": t,
        "permission_overwrites": raw_overwrites(pairs),
    }
    if parent is not None:
        payload["parent_id"] = parent.id
    for key in ("topic", "nsfw", "rate_limit_per_user", "position"):
        if ch.get(key) is not None:
            payload[key] = ch[key]
    try:
        data = await client.http.request(
            Route("POST", "/guilds/{guild_id}/channels", guild_id=guild.id), json=payload
        )
        return await client.fetch_channel(as_int(data["id"]))
    except discord.HTTPException:
        return await guild.create_text_channel(
            ch.get("name") or "channel", category=parent, overwrites=overwrite_map(pairs), reason=REASON
        )


async def apply_channels(client, guild, src, role_map, stats):
    chan_map = {}

    def find_existing(name, ctype):
        return discord.utils.find(
            lambda c: c.name.lower() == name.lower() and c.type.value == ctype, guild.channels
        )

    async def upsert(ch):
        t = as_int(ch.get("type")) or 0
        name = ch.get("name") or "channel"
        tid = as_int(ch.get("id"))
        position = as_int(ch.get("position"))
        pairs = await resolve_overwrites(guild, ch, role_map)
        ow = overwrite_map(pairs)

        if t == 4:  # category
            existing = discord.utils.find(
                lambda c: isinstance(c, discord.CategoryChannel) and c.name.lower() == name.lower(),
                guild.channels,
            )
            if existing is None:
                try:
                    existing = await guild.create_category(name, overwrites=ow, reason=REASON)
                    stats["channels_created"] += 1
                    if position is not None:
                        await try_edit(existing, dict(position=position))
                except Exception:
                    await asyncio.sleep(0.3)
                    return
            else:
                kw = dict(name=name, overwrites=ow, reason=REASON)
                if position is not None:
                    kw["position"] = position
                if await try_edit(existing, kw):
                    stats["channels_updated"] += 1
            if tid is not None and existing is not None:
                chan_map[tid] = existing
            await asyncio.sleep(0.3)
            return

        parent = chan_map.get(as_int(ch.get("parent_id")))
        edit_kwargs = {}
        if position is not None:
            edit_kwargs["position"] = position
        if t in (0, 5, 13, 15) and ch.get("topic") is not None:
            edit_kwargs["topic"] = ch["topic"]
        if t in (0, 5):
            if ch.get("nsfw") is not None:
                edit_kwargs["nsfw"] = bool(ch["nsfw"])
            if ch.get("rate_limit_per_user") is not None:
                edit_kwargs["slowmode_delay"] = ch["rate_limit_per_user"]
        if t == 0 and ch.get("default_auto_archive_duration") is not None:
            edit_kwargs["default_auto_archive_duration"] = ch["default_auto_archive_duration"]
        if t in (2, 13):
            if ch.get("bitrate") is not None:
                edit_kwargs["bitrate"] = ch["bitrate"]
            if ch.get("user_limit"):
                edit_kwargs["user_limit"] = ch["user_limit"]

        existing = find_existing(name, t)
        if existing is not None:
            basic = dict(name=name, category=parent, overwrites=ow, reason=REASON)
            safe = {k: v for k, v in edit_kwargs.items() if k not in ("bitrate", "user_limit")}
            ok = await try_edit(existing, {**basic, **edit_kwargs}, {**basic, **safe}, dict(name=name, overwrites=ow))
            if tid is not None:
                chan_map[tid] = existing
            if ok:
                stats["channels_updated"] += 1
            await asyncio.sleep(0.3)
            return

        try:
            if t in (5, 15):
                new = await create_channel_via_api(client, guild, ch, parent, pairs)
            elif t == 0:
                new = await guild.create_text_channel(name, category=parent, overwrites=ow, reason=REASON)
            elif t == 2:
                new = await guild.create_voice_channel(name, category=parent, overwrites=ow, reason=REASON)
            elif t == 13:
                new = await guild.create_stage_channel(name, category=parent, overwrites=ow, reason=REASON)
            else:
                await asyncio.sleep(0.3)
                return
        except Exception:
            await asyncio.sleep(0.3)
            return

        if edit_kwargs:
            await try_edit(new, dict(edit_kwargs))
        stats["channels_created"] += 1
        if tid is not None:
            chan_map[tid] = new
        await asyncio.sleep(0.3)

    ordered = sorted(src.get("channels", []), key=lambda c: (as_int(c.get("type")) or 0) != 4)
    for ch in ordered:
        try:
            await upsert(ch)
        except Exception:
            pass
    return chan_map


async def delete_extras(guild, role_map, chan_map, opts):
    if opts.get("delete_extra_roles"):
        keep = {r.id for r in role_map.values()} | {guild.default_role.id}
        for r in list(guild.roles):
            if r.id in keep or r.managed or r == guild.default_role:
                continue
            try:
                await r.delete(reason=REASON)
            except Exception:
                pass
    if opts.get("delete_extra_channels"):
        keep = {c.id for c in chan_map.values()}
        for c in sorted(guild.channels, key=lambda c: isinstance(c, discord.CategoryChannel)):
            if c.id in keep:
                continue
            try:
                await c.delete(reason=REASON)
            except Exception:
                pass


async def apply_settings(guild, template, chan_map):
    src = template["serialized_source_guild"]
    fields = {}
    if src.get("name"):
        fields["name"] = src["name"]
    if as_int(src.get("verification_level")) is not None:
        fields["verification_level"] = discord.VerificationLevel(src["verification_level"])
    if as_int(src.get("default_message_notifications")) is not None:
        fields["default_notifications"] = discord.NotificationLevel(src["default_message_notifications"])
    if as_int(src.get("explicit_content_filter")) is not None:
        fields["explicit_content_filter"] = discord.ContentFilter(src["explicit_content_filter"])
    if src.get("preferred_locale"):
        fields["preferred_locale"] = src["preferred_locale"]
    if as_int(src.get("afk_timeout")):
        fields["afk_timeout"] = src["afk_timeout"]
    afk = chan_map.get(as_int(src.get("afk_channel_id")))
    if afk is not None:
        fields["afk_channel"] = afk
    sysc = chan_map.get(as_int(src.get("system_channel_id")))
    if sysc is not None:
        fields["system_channel"] = sysc
    if as_int(src.get("system_channel_flags")) is not None:
        flags = flags_from_value(discord.SystemChannelFlags, src["system_channel_flags"])
        if flags is not None:
            fields["system_channel_flags"] = flags
    if fields:
        try:
            await guild.edit(reason=REASON, **fields)
        except Exception:
            pass


async def apply_appearance(client, guild, template):
    src = template.get("serialized_source_guild") or {}
    source_id = template.get("source_guild_id")
    if not source_id:
        return
    icon_hash = src.get("icon_hash")
    banner_hash = None
    try:
        raw = await client.http.request(Route("GET", "/guilds/{guild_id}", guild_id=source_id))
        icon_hash = raw.get("icon") or icon_hash
        banner_hash = raw.get("banner")
    except discord.HTTPException:
        pass
    if icon_hash:
        ext = "gif" if icon_hash.startswith("a_") else "png"
        data = await download_image(f"https://cdn.discordapp.com/icons/{source_id}/{icon_hash}.{ext}?size=1024")
        if data:
            try:
                await guild.edit(icon=data, reason=REASON)
            except Exception:
                pass
    if banner_hash:
        ext = "gif" if banner_hash.startswith("a_") else "png"
        data = await download_image(f"https://cdn.discordapp.com/banners/{source_id}/{banner_hash}.{ext}?size=2048")
        if data:
            try:
                await guild.edit(banner=data, reason=REASON)
            except Exception:
                pass


async def do_apply(client, guild, template, opts):
    stats = {"roles_created": 0, "roles_updated": 0, "channels_created": 0, "channels_updated": 0}
    src = template["serialized_source_guild"]
    role_map = await apply_roles(guild, src, stats)
    await apply_role_order(guild, src, role_map)
    chan_map = await apply_channels(client, guild, src, role_map, stats)
    await delete_extras(guild, role_map, chan_map, opts)
    if opts.get("apply_guild_settings", True):
        await apply_settings(guild, template, chan_map)
        await apply_appearance(client, guild, template)
    return stats


async def do_backup(client, guild, purpose="undo point"):
    stamp = datetime.now().strftime("%Y-%m-%d_%H-%M-%S")
    try:
        template = await client.http.request(
            Route("POST", "/guilds/{guild_id}/templates", guild_id=guild.id),
            json={"name": f"Backup {stamp}"},
        )
    except discord.HTTPException as e:
        return False, str(e)
    fname = f"backup-{safe_filename(guild.name)}-{stamp}.json"
    try:
        with open(fname, "w", encoding="utf-8") as f:
            json.dump(template, f, indent=2, ensure_ascii=False)
    except OSError:
        pass
    return True, fname


# --- Slash: /pull ---
@bot.tree.command(name="pull", description="List this server's saved templates + discord.new links")
@app_commands.guild_only()
@app_commands.checks.has_permissions(manage_guild=True)
async def cmd_pull(interaction: discord.Interaction):
    await interaction.response.defer()
    guild = interaction.guild
    try:
        templates = await bot.http.request(Route("GET", "/guilds/{guild_id}/templates", guild_id=guild.id))
    except discord.Forbidden:
        await interaction.edit_original_response(content="❌ I need **Manage Server** permission.")
        return
    except discord.HTTPException as e:
        await interaction.edit_original_response(content=f"❌ Couldn't load templates ({e.status}): {e.text}")
        return

    if not templates:
        await interaction.edit_original_response(
            embed=discord.Embed(
                title=f"📋 Templates on {guild.name}",
                description="No saved templates yet. Create one with the menu-style tools or Discord UI.",
                color=discord.Colour.gold(),
            )
        )
        return

    templates.sort(key=lambda t: t.get("updated_at") or t.get("created_at") or "", reverse=True)
    embed = discord.Embed(title=f"📋 Templates on {guild.name} ({len(templates)})", color=discord.Colour.green())
    for t in templates[:15]:
        src = t.get("serialized_source_guild") or {}
        roles = len([r for r in src.get("roles", []) if r.get("name") != "@everyone"])
        chans = len(src.get("channels", []))
        updated = (t.get("updated_at") or t.get("created_at") or "")[:10]
        dirty = " · **out of date**" if t.get("is_dirty") else ""
        value = (
            f"https://discord.new/{t.get('code', '?')}\n"
            f"{roles} roles · {chans} channels · used {t.get('usage_count', 0)}×"
            + (f" · updated {updated}" if updated else "")
            + dirty
        )
        if t.get("description"):
            value = f"{t['description']}\n{value}"
        embed.add_field(name=t.get("name") or "(unnamed)", value=value, inline=False)
    if len(templates) > 15:
        embed.set_footer(text=f"…and {len(templates) - 15} more not shown.")
    await interaction.edit_original_response(embed=embed)


# --- Slash: /apply ---
@bot.tree.command(name="apply", description="Reshape THIS server to match a template")
@app_commands.guild_only()
@app_commands.describe(
    template="discord.new link/code OR path to a .json template file",
    backup="Back up this server first (default True)",
    delete_channels="Delete channels NOT in the template (messages lost forever)",
    delete_roles="Delete roles NOT in the template (members stay)",
    copy_settings="Copy name, settings, icon & banner (default True)",
    confirm="True = apply for real. Without it you only get a PREVIEW.",
)
@app_commands.checks.has_permissions(manage_guild=True)
async def cmd_apply(
    interaction: discord.Interaction,
    template: str,
    backup: bool = True,
    delete_channels: bool = False,
    delete_roles: bool = False,
    copy_settings: bool = True,
    confirm: bool = False,
):
    await interaction.response.defer(ephemeral=not confirm)
    guild = interaction.guild

    try:
        tmpl = await load_template(template)
    except Exception as e:
        await interaction.edit_original_response(content=f"❌ {e}")
        return
    if not tmpl.get("serialized_source_guild"):
        await interaction.edit_original_response(content="❌ That template has no server data.")
        return

    if not confirm:
        data = compare_data(guild, tmpl)
        embed = discord.Embed(
            title=f"📋 Dry run: '{tmpl.get('name', '?')}' → '{guild.name}'",
            description="Nothing was changed. Re-run with **confirm: True** to apply.",
            color=discord.Colour.blurple(),
        )
        embed.add_field(name=f"Roles created ({len(data['roles_create'])})", value=_bullet_list(data["roles_create"]))
        embed.add_field(name=f"Roles updated ({len(data['roles_update'])})", value=_bullet_list(data["roles_update"]))
        embed.add_field(
            name=f"Roles deleted IF delete_roles ({len(data['roles_extra'])})",
            value=_bullet_list(data["roles_extra"]),
        )
        embed.add_field(name=f"Channels created ({len(data['chan_create'])})", value=_bullet_list(data["chan_create"]))
        embed.add_field(name=f"Channels updated ({len(data['chan_update'])})", value=_bullet_list(data["chan_update"]))
        embed.add_field(
            name=f"Channels deleted IF delete_channels ({len(data['chans_extra'])})",
            value=_bullet_list(data["chans_extra"]),
        )
        if data["name_change"]:
            embed.add_field(
                name="Server name",
                value=f"'{data['name_change'][0]}' → '{data['name_change'][1]}'",
                inline=False,
            )
        await interaction.edit_original_response(embed=embed)
        return

    async with bot.job_lock:
        if backup:
            ok, info = await do_backup(bot, guild, purpose="before /apply")
            if not ok:
                await interaction.edit_original_response(
                    content=f"⚠ Pre-apply backup failed ({info}). Continuing anyway…"
                )
        opts = {
            "delete_extra_channels": delete_channels,
            "delete_extra_roles": delete_roles,
            "apply_guild_settings": copy_settings,
        }
        try:
            stats = await do_apply(bot, guild, tmpl, opts)
        except discord.Forbidden:
            await interaction.edit_original_response(
                content="❌ Discord said 403 — give me **Administrator** and try again."
            )
            return
        except Exception as e:
            traceback.print_exc()
            await interaction.edit_original_response(
                content=f"❌ Something went wrong ({type(e).__name__}: {e}) — changes may be partial."
            )
            return

    embed = discord.Embed(title=f"✅ Applied template: {tmpl.get('name', '?')}", color=discord.Colour.green())
    if tmpl.get("code"):
        embed.description = f"https://discord.new/{tmpl['code']}"
    embed.add_field(
        name="Roles",
        value=f"+{stats['roles_created']} created · ~{stats['roles_updated']} updated",
    )
    embed.add_field(
        name="Channels",
        value=f"+{stats['channels_created']} created · ~{stats['channels_updated']} updated",
    )
    embed.set_footer(text="Nobody was kicked — every member is still in the server.")
    await interaction.edit_original_response(embed=embed)


# ---- prefix versions of admin/slash commands ----

@bot.command(name="pull")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def pull_prefix(ctx: commands.Context):
    """`,pull — list this server's saved templates"""
    try:
        templates = await bot.http.request(
            Route("GET", "/guilds/{guild_id}/templates", guild_id=ctx.guild.id)
        )
    except discord.HTTPException as e:
        await ctx.reply(f"❌ Couldn't load templates ({e.status}): {e.text}", mention_author=False)
        return
    if not templates:
        await ctx.reply(embed=discord.Embed(
            title=f"📋 Templates on {ctx.guild.name}",
            description="No saved templates yet.",
            color=discord.Colour.gold(),
        ), mention_author=False)
        return
    templates.sort(key=lambda t: t.get("updated_at") or t.get("created_at") or "", reverse=True)
    embed = discord.Embed(title=f"📋 Templates on {ctx.guild.name} ({len(templates)})", color=discord.Colour.green())
    for t in templates[:15]:
        src = t.get("serialized_source_guild") or {}
        roles = len([r for r in src.get("roles", []) if r.get("name") != "@everyone"])
        chans = len(src.get("channels", []))
        updated = (t.get("updated_at") or t.get("created_at") or "")[:10]
        dirty = " · **out of date**" if t.get("is_dirty") else ""
        value = (f"https://discord.new/{t.get('code', '?')}\n"
                 f"{roles} roles · {chans} channels · used {t.get('usage_count', 0)}×"
                 + (f" · updated {updated}" if updated else "") + dirty)
        if t.get("description"):
            value = f"{t['description']}\n{value}"
        embed.add_field(name=t.get("name") or "(unnamed)", value=value, inline=False)
    if len(templates) > 15:
        embed.set_footer(text=f"…and {len(templates) - 15} more not shown.")
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="apply")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def apply_prefix(ctx: commands.Context, template: str, *, flags: str = ""):
    """`,apply <template> [confirm backup delete_channels delete_roles copy_settings]

    Each flag is a key=value pair, e.g. `,apply ABC123 confirm=true backup=true`
    Anything not specified uses defaults (confirm=false, backup=true, etc.)."""
    try:
        tmpl = await load_template(template)
    except Exception as e:
        await ctx.reply(f"❌ {e}", mention_author=False)
        return
    if not tmpl.get("serialized_source_guild"):
        await ctx.reply("❌ That template has no server data.", mention_author=False)
        return

    flag_map = {}
    for pair in (flags or "").split():
        if "=" in pair:
            k, v = pair.split("=", 1)
            flag_map[k.strip().lower()] = v.strip().lower() in ("1", "true", "yes", "on")
    confirm = flag_map.get("confirm", False)
    backup = flag_map.get("backup", True)
    delete_channels = flag_map.get("delete_channels", False)
    delete_roles = flag_map.get("delete_roles", False)
    copy_settings = flag_map.get("copy_settings", True)

    if not confirm:
        data = compare_data(ctx.guild, tmpl)
        embed = discord.Embed(
            title=f"📋 Dry run: '{tmpl.get('name', '?')}' → '{ctx.guild.name}'",
            description="Nothing was changed. Re-run with `confirm=true` to apply.",
            color=discord.Colour.blurple(),
        )
        embed.add_field(name=f"Roles created ({len(data['roles_create'])})", value=_bullet_list(data["roles_create"]))
        embed.add_field(name=f"Roles updated ({len(data['roles_update'])})", value=_bullet_list(data["roles_update"]))
        embed.add_field(name=f"Channels created ({len(data['chan_create'])})", value=_bullet_list(data["chan_create"]))
        embed.add_field(name=f"Channels updated ({len(data['chan_update'])})", value=_bullet_list(data["chan_update"]))
        if data["name_change"]:
            embed.add_field(name="Server name",
                            value=f"'{data['name_change'][0]}' → '{data['name_change'][1]}'", inline=False)
        await ctx.reply(embed=embed, mention_author=False)
        return

    async with bot.job_lock:
        if backup:
            ok, info = await do_backup(bot, ctx.guild, purpose="before ,apply")
            if not ok:
                await ctx.reply(f"⚠ Pre-apply backup failed ({info}). Continuing anyway…", mention_author=False)
        opts = {
            "delete_extra_channels": delete_channels,
            "delete_extra_roles": delete_roles,
            "apply_guild_settings": copy_settings,
        }
        try:
            stats = await do_apply(bot, ctx.guild, tmpl, opts)
        except discord.Forbidden:
            await ctx.reply("❌ Discord said 403 — give me **Administrator** and try again.", mention_author=False)
            return
        except Exception as e:
            traceback.print_exc()
            await ctx.reply(f"❌ Something went wrong ({type(e).__name__}: {e}) — changes may be partial.", mention_author=False)
            return

    embed = discord.Embed(title=f"✅ Applied template: {tmpl.get('name', '?')}", color=discord.Colour.green())
    if tmpl.get("code"):
        embed.description = f"https://discord.new/{tmpl['code']}"
    embed.add_field(name="Roles", value=f"+{stats['roles_created']} created · ~{stats['roles_updated']} updated")
    embed.add_field(name="Channels", value=f"+{stats['channels_created']} created · ~{stats['channels_updated']} updated")
    embed.set_footer(text="Nobody was kicked — every member is still in the server.")
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="set")
@commands.guild_only()
@commands.has_permissions(administrator=True)
async def set_prefix(ctx: commands.Context, *, settings: str = ""):
    """`,set key=value key=value... — configure APK announcer + mod log

    Keys: apk_channel=#channel · ping_role=@role · announce_channel=#channel · modlog_channel=#channel

    Example: `,set apk_channel=#releases ping_role=@Subs announce_channel=#general`"""
    s = config.setdefault(str(ctx.guild.id), {})
    parsed_any = False
    for pair in (settings or "").split():
        if "=" not in pair:
            continue
        key, val = pair.split("=", 1)
        key = key.strip().lower()
        val = val.strip()
        m_id = None
        ch_match = re.match(r"<#(\d+)>", val)
        role_match = re.match(r"<@&(\d+)>", val)
        if ch_match:
            m_id = int(ch_match.group(1))
        elif role_match:
            m_id = int(role_match.group(1))
        elif val.isdigit():
            m_id = int(val)
        if key == "apk_channel" and m_id:
            ch = ctx.guild.get_channel(m_id)
            if isinstance(ch, discord.ForumChannel):
                s["apk_channel"] = m_id
                parsed_any = True
        elif key == "announce_channel" and m_id:
            ch = ctx.guild.get_channel(m_id)
            if isinstance(ch, discord.TextChannel):
                s["announce_channel"] = m_id
                parsed_any = True
        elif key == "modlog_channel" and m_id:
            ch = ctx.guild.get_channel(m_id)
            if isinstance(ch, discord.TextChannel):
                s["modlog_channel"] = m_id
                parsed_any = True
        elif key == "ping_role" and m_id:
            r = ctx.guild.get_role(m_id)
            if r:
                s["ping_role"] = m_id
                parsed_any = True
    if parsed_any:
        save_config(config)

    def ch(cid):
        return f"<#{cid}>" if cid else "*Not set*"

    def role_str(rid):
        return f"<@&{rid}>" if rid else "*None*"

    embed = discord.Embed(title="⚙️ Settings", color=discord.Color.blurple())
    embed.add_field(name="APK forum", value=ch(s.get("apk_channel")), inline=True)
    embed.add_field(name="Ping role", value=role_str(s.get("ping_role")), inline=True)
    embed.add_field(name="Announce channel", value=ch(s.get("announce_channel")), inline=True)
    embed.add_field(name="Mod log", value=ch(s.get("modlog_channel")), inline=True)
    embed.set_footer(text="Use `,set key=value key=value` to update.  Keys: apk_channel, ping_role, announce_channel, modlog_channel")
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="roleall")
@commands.guild_only()
@commands.has_permissions(administrator=True)
async def roleall_prefix(ctx: commands.Context, role: discord.Role, remove: Optional[str] = None):
    """`,roleall @role [remove=true]"""
    guild = ctx.guild
    me = guild.me
    if role.is_default():
        await ctx.reply("❌ Can't mass-assign @everyone.", mention_author=False)
        return
    if role.managed:
        await ctx.reply("❌ That role is managed and can't be assigned manually.", mention_author=False)
        return
    if role >= me.top_role:
        await ctx.reply(f"❌ My top role must be **above** {role.mention}.", mention_author=False)
        return
    remove_flag = (remove or "").lower() in ("true", "1", "yes", "remove")
    status_msg = await ctx.reply(f"⏳ Working on **{role.name}**…")
    verb = "Removing" if remove_flag else "Giving"
    count, failed = 0, 0
    try:
        async for member in guild.fetch_members(limit=None):
            if member.bot:
                continue
            has_role = role in member.roles
            if (remove_flag and has_role) or (not remove_flag and not has_role):
                try:
                    if remove_flag:
                        await member.remove_roles(role, reason=f",roleall by {ctx.author}")
                    else:
                        await member.add_roles(role, reason=f",roleall by {ctx.author}")
                    count += 1
                    if count % 25 == 0:
                        await status_msg.edit(content=f"{verb} **{role.name}** — {count} done…")
                    await asyncio.sleep(0.4)
                except discord.HTTPException:
                    failed += 1
    except discord.ClientException:
        await status_msg.edit(content="❌ **Server Members Intent** is off. Enable it in the Developer Portal.")
        return
    done_verb = "removed from" if remove_flag else "given to"
    result = f"✅ **{role.name}** {done_verb} **{count}** member(s)."
    if failed:
        result += f" ⚠️ {failed} failed."
    await status_msg.edit(content=result)


# ===========================================================================
# TikTok tools
# ===========================================================================
def get_user_info_ytdlp(username: str):
    url = f"https://www.tiktok.com/@{username}"
    ydl_opts = {
        "quiet": True,
        "no_warnings": True,
        "extract_flat": False,
        "playlistend": 8,
        "ignoreerrors": True,
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        return ydl.extract_info(url, download=False)


def get_user_info(username: str):
    url = f"https://www.tiktok.com/@{username}"
    headers = {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
        "Accept-Language": "en-US,en;q=0.9",
    }
    try:
        r = requests.get(url, headers=headers, timeout=12)
        r.raise_for_status()
        html = r.text
        match = re.search(
            r'<script id="__UNIVERSAL_DATA_FOR_REHYDRATION__" type="application/json">(.*?)</script>', html
        )
        if not match:
            match = re.search(r'<script id="SIGI_STATE" type="application/json">(.*?)</script>', html)
        if match:
            data = json.loads(match.group(1))
            try:
                user_detail = data["__DEFAULT_SCOPE__"]["webapp.user-detail"]["userInfo"]
                user = user_detail.get("user", {})
                stats = user_detail.get("stats", {})
                return {
                    "uploader": user.get("nickname"),
                    "uploader_id": user.get("uniqueId"),
                    "description": user.get("signature") or "No bio",
                    "channel_follower_count": stats.get("followerCount"),
                    "view_count": stats.get("heartCount"),
                    "thumbnail": user.get("avatarLarger") or user.get("avatarMedium"),
                    "entries": [],
                }
            except Exception:
                pass
        return get_user_info_ytdlp(username)
    except Exception:
        return get_user_info_ytdlp(username)


def get_video_info(url: str):
    ydl_opts = {"quiet": True, "no_warnings": True, "skip_download": True}
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        return ydl.extract_info(url, download=False)


def download_video_bytes(url: str):
    with tempfile.TemporaryDirectory() as tmpdir:
        ydl_opts = {
            "quiet": True,
            "no_warnings": True,
            "format": "mp4/best",
            "outtmpl": os.path.join(tmpdir, "video.%(ext)s"),
        }
        with yt_dlp.YoutubeDL(ydl_opts) as ydl:
            info = ydl.extract_info(url, download=True)
            filename = ydl.prepare_filename(info)
            with open(filename, "rb") as f:
                return f.read(), info


def search_tiktok(query: str, limit: int = 6):
    ydl_opts = {
        "quiet": True,
        "no_warnings": True,
        "extract_flat": True,
        "playlistend": limit,
    }
    with yt_dlp.YoutubeDL(ydl_opts) as ydl:
        result = ydl.extract_info(f"ytsearch{limit}:{query} site:tiktok.com", download=False)
        return result.get("entries", [])


@bot.tree.command(name="lookup", description="Lookup a TikTok user")
@app_commands.describe(username="TikTok username (without @)")
async def lookup(interaction: discord.Interaction, username: str):
    await interaction.response.defer()
    username = username.lstrip("@").strip()
    log(f"LOOKUP by {interaction.user} → @{username}")
    try:
        info = await asyncio.to_thread(get_user_info, username)
        uploader = info.get("uploader") or info.get("channel") or username
        uploader_id = info.get("uploader_id") or info.get("channel_id") or username
        description = info.get("description") or "No bio"
        follower_count = info.get("channel_follower_count") or info.get("follower_count")
        view_count = info.get("view_count")
        embed = discord.Embed(
            title=f"@{uploader_id}",
            description=str(description)[:1500],
            color=0x00F2EA,
            url=f"https://www.tiktok.com/@{uploader_id}",
        )
        thumb = info.get("thumbnail")
        if thumb:
            embed.set_thumbnail(url=thumb)
        embed.add_field(name="Display Name", value=str(uploader)[:256], inline=True)
        embed.add_field(name="Followers", value=format_number(follower_count), inline=True)
        embed.add_field(name="Total Likes", value=format_number(view_count), inline=True)
        entries = info.get("entries") or []
        recent_lines = []
        for entry in entries[:4]:
            title = (entry.get("title") or "No title")[:40]
            url = entry.get("url") or entry.get("webpage_url")
            views = format_number(entry.get("view_count"))
            if url:
                recent_lines.append(f"• [{title}...]({url}) — {views}")
        recent_text = "\n".join(recent_lines) if recent_lines else "No recent videos found"
        if len(recent_text) > 1000:
            recent_text = recent_text[:997] + "..."
        embed.add_field(name="Recent Videos", value=recent_text, inline=False)
        embed.set_footer(text="TikTok Lookup")
        embed.timestamp = datetime.now(timezone.utc)
        await interaction.followup.send(embed=embed)
        await save_history(
            interaction.user.id, "lookup", username, f"{uploader} | {format_number(follower_count)} followers"
        )
    except Exception as e:
        log(f"LOOKUP FAILED → {e}")
        traceback.print_exc()
        await interaction.followup.send(f"❌ Failed to lookup `@{username}`\n```{str(e)[:400]}```")


@bot.tree.command(name="reversevid", description="Get TikTok video info + embed")
@app_commands.describe(url="TikTok video URL")
async def reversevid(interaction: discord.Interaction, url: str):
    await interaction.response.defer()
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await interaction.followup.send("❌ Please provide a valid TikTok URL.")
        return
    try:
        info = await asyncio.to_thread(get_video_info, url)
        title = info.get("title") or info.get("description") or "No caption"
        uploader_id = info.get("uploader_id") or info.get("uploader") or "unknown"
        view_count = info.get("view_count")
        like_count = info.get("like_count")
        comment_count = info.get("comment_count")
        duration = info.get("duration")
        thumbnail = info.get("thumbnail")
        webpage_url = info.get("webpage_url") or url
        embed = discord.Embed(title="TikTok Video", description=str(title)[:2000], color=0xFE2C55, url=webpage_url)
        if thumbnail:
            embed.set_image(url=thumbnail)
        embed.add_field(name="Author", value=f"[@{uploader_id}](https://www.tiktok.com/@{uploader_id})", inline=True)
        embed.add_field(name="Views", value=format_number(view_count), inline=True)
        embed.add_field(name="Likes", value=format_number(like_count), inline=True)
        embed.add_field(name="Comments", value=format_number(comment_count), inline=True)
        embed.add_field(name="Duration", value=f"{duration}s" if duration else "N/A", inline=True)
        embed.set_footer(text="Reverse Video")
        embed.timestamp = datetime.now(timezone.utc)
        try:
            video_bytes, _ = await asyncio.to_thread(download_video_bytes, url)
            if len(video_bytes) < 24 * 1024 * 1024:
                file = discord.File(fp=BytesIO(video_bytes), filename="tiktok.mp4")
                await interaction.followup.send(embed=embed, file=file)
            else:
                await interaction.followup.send(embed=embed)
        except Exception:
            await interaction.followup.send(embed=embed)
        await save_history(
            interaction.user.id, "reversevid", url, f"@{uploader_id} | {format_number(view_count)} views"
        )
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Failed\n```{str(e)[:500]}```")


@bot.tree.command(name="search", description="Search TikTok videos")
@app_commands.describe(query="What to search for", limit="How many results (1-10)")
async def search(interaction: discord.Interaction, query: str, limit: app_commands.Range[int, 1, 10] = 6):
    await interaction.response.defer()
    try:
        results = await asyncio.to_thread(search_tiktok, query, limit)
        if not results:
            await interaction.followup.send("No results found.")
            return
        embed = discord.Embed(title=f"Search: {query}", color=0xFE2C55)
        for i, video in enumerate(results[:limit], 1):
            title = (video.get("title") or "No title")[:55]
            url = video.get("url") or video.get("webpage_url")
            uploader = video.get("uploader") or "unknown"
            views = format_number(video.get("view_count"))
            if url:
                embed.add_field(
                    name=f"{i}. {title}",
                    value=f"@{uploader} • {views} views\n[Watch]({url})",
                    inline=False,
                )
        embed.set_footer(text="TikTok Search")
        embed.timestamp = datetime.now(timezone.utc)
        await interaction.followup.send(embed=embed)
        await save_history(interaction.user.id, "search", query, f"{len(results)} results")
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Search failed\n```{str(e)[:400]}```")


@bot.tree.command(name="uservideos", description="Get recent videos from a TikTok user")
@app_commands.describe(username="TikTok username", limit="How many videos (1-12)")
async def uservideos(
    interaction: discord.Interaction, username: str, limit: app_commands.Range[int, 1, 12] = 6
):
    await interaction.response.defer()
    username = username.lstrip("@").strip()
    try:
        info = await asyncio.to_thread(get_user_info_ytdlp, username)
        entries = info.get("entries") or []
        if not entries:
            await interaction.followup.send("No videos found.")
            return
        embed = discord.Embed(
            title=f"Videos from @{username}",
            color=0x00F2EA,
            url=f"https://www.tiktok.com/@{username}",
        )
        for i, entry in enumerate(entries[:limit], 1):
            title = (entry.get("title") or "No title")[:50]
            url = entry.get("url") or entry.get("webpage_url")
            views = format_number(entry.get("view_count"))
            if url:
                embed.add_field(name=f"{i}. {title}", value=f"{views} views • [Watch]({url})", inline=False)
        embed.set_footer(text="User Videos")
        embed.timestamp = datetime.now(timezone.utc)
        await interaction.followup.send(embed=embed)
        await save_history(interaction.user.id, "uservideos", username, f"{len(entries[:limit])} videos")
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Failed\n```{str(e)[:400]}```")


@bot.tree.command(name="download", description="Download a TikTok video")
@app_commands.describe(url="TikTok video URL")
async def download(interaction: discord.Interaction, url: str):
    await interaction.response.defer()
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await interaction.followup.send("❌ Invalid TikTok URL.")
        return
    try:
        video_bytes, info = await asyncio.to_thread(download_video_bytes, url)
        title = (info.get("title") or "tiktok")[:40]
        filename = re.sub(r'[\\/*?:"<>|]', "", title) + ".mp4"
        if len(video_bytes) > 24 * 1024 * 1024:
            await interaction.followup.send("⚠️ Video too large (over 24 MB).")
            return
        file = discord.File(fp=BytesIO(video_bytes), filename=filename)
        await interaction.followup.send(content=f"**Downloaded:** {title}", file=file)
        await save_history(interaction.user.id, "download", url, title)
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Download failed\n```{str(e)[:400]}```")


@bot.tree.command(name="sound", description="Lookup a TikTok sound/music")
@app_commands.describe(url="TikTok video URL that uses the sound")
async def sound(interaction: discord.Interaction, url: str):
    await interaction.response.defer()
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await interaction.followup.send("❌ Please provide a valid TikTok video URL.")
        return
    try:
        info = await asyncio.to_thread(get_video_info, url)
        track = info.get("track") or "Unknown"
        artist = info.get("artist") or info.get("creator") or "Unknown"
        duration = info.get("duration")
        view_count = info.get("view_count")
        webpage_url = info.get("webpage_url") or url
        sound_title = info.get("track") or info.get("title") or "Unknown Sound"
        embed = discord.Embed(
            title="TikTok Sound / Music",
            description=f"**{sound_title}**",
            color=0x9B59B6,
            url=webpage_url,
        )
        embed.add_field(name="Track", value=str(track)[:256], inline=True)
        embed.add_field(name="Artist", value=str(artist)[:256], inline=True)
        embed.add_field(name="Duration", value=f"{duration}s" if duration else "N/A", inline=True)
        embed.add_field(name="Video Views", value=format_number(view_count), inline=True)
        thumb = info.get("thumbnail")
        if thumb:
            embed.set_thumbnail(url=thumb)
        embed.set_footer(text="Sound Lookup")
        embed.timestamp = datetime.now(timezone.utc)
        await interaction.followup.send(embed=embed)
        await save_history(interaction.user.id, "sound", url, sound_title)
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Failed to get sound info\n```{str(e)[:400]}```")


@bot.tree.command(name="history", description="Show your recent TikTok searches")
async def history(interaction: discord.Interaction, limit: app_commands.Range[int, 1, 15] = 8):
    await interaction.response.defer(ephemeral=True)
    async with aiosqlite.connect(HISTORY_DB) as db:
        cursor = await db.execute(
            "SELECT command, query, result_summary, timestamp FROM history WHERE user_id = ? ORDER BY id DESC LIMIT ?",
            (interaction.user.id, limit),
        )
        rows = await cursor.fetchall()
    if not rows:
        await interaction.followup.send("No history yet.", ephemeral=True)
        return
    embed = discord.Embed(title="Your Search History", color=0x5865F2)
    for cmd, query, summary, ts in rows:
        embed.add_field(
            name=f"`/{cmd}` — {query[:40]}",
            value=f"{summary}\n<t:{int(datetime.fromisoformat(ts).timestamp())}:R>",
            inline=False,
        )
    await interaction.followup.send(embed=embed, ephemeral=True)


# ===========================================================================
# TikTok PREFIX commands  (mirror the slash ones)
# ===========================================================================
@bot.command(name="lookup")
async def lookup_prefix(ctx: commands.Context, username: str):
    """`,lookup <username>` — TikTok user info"""
    await ctx.typing()
    username = username.lstrip("@").strip()
    log(f"LOOKUP(prefix) by {ctx.author} → @{username}")
    try:
        info = await asyncio.to_thread(get_user_info, username)
        uploader = info.get("uploader") or info.get("channel") or username
        uploader_id = info.get("uploader_id") or info.get("channel_id") or username
        description = info.get("description") or "No bio"
        follower_count = info.get("channel_follower_count") or info.get("follower_count")
        view_count = info.get("view_count")
        embed = discord.Embed(
            title=f"@{uploader_id}",
            description=str(description)[:1500],
            color=0x00F2EA,
            url=f"https://www.tiktok.com/@{uploader_id}",
        )
        thumb = info.get("thumbnail")
        if thumb:
            embed.set_thumbnail(url=thumb)
        embed.add_field(name="Display Name", value=str(uploader)[:256], inline=True)
        embed.add_field(name="Followers", value=format_number(follower_count), inline=True)
        embed.add_field(name="Total Likes", value=format_number(view_count), inline=True)
        entries = info.get("entries") or []
        recent_lines = []
        for entry in entries[:4]:
            title = (entry.get("title") or "No title")[:40]
            url = entry.get("url") or entry.get("webpage_url")
            views = format_number(entry.get("view_count"))
            if url:
                recent_lines.append(f"• [{title}...]({url}) — {views}")
        recent_text = "\n".join(recent_lines) if recent_lines else "No recent videos found"
        if len(recent_text) > 1000:
            recent_text = recent_text[:997] + "..."
        embed.add_field(name="Recent Videos", value=recent_text, inline=False)
        embed.set_footer(text="TikTok Lookup")
        embed.timestamp = datetime.now(timezone.utc)
        await ctx.reply(embed=embed, mention_author=False)
        await save_history(ctx.author.id, "lookup", username, f"{uploader} | {format_number(follower_count)} followers")
    except Exception as e:
        log(f"LOOKUP(prefix) FAILED → {e}")
        await ctx.reply(f"❌ Failed to lookup `@{username}`\n```{str(e)[:400]}```", mention_author=False)


@bot.command(name="reversevid", aliases=["rev"])
async def reversevid_prefix(ctx: commands.Context, url: str):
    """`,reversevid <tiktok_url>`"""
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await ctx.reply("❌ Please provide a valid TikTok URL.", mention_author=False)
        return
    await ctx.typing()
    try:
        info = await asyncio.to_thread(get_video_info, url)
        title = info.get("title") or info.get("description") or "No caption"
        uploader_id = info.get("uploader_id") or info.get("uploader") or "unknown"
        view_count = info.get("view_count")
        like_count = info.get("like_count")
        comment_count = info.get("comment_count")
        duration = info.get("duration")
        thumbnail = info.get("thumbnail")
        webpage_url = info.get("webpage_url") or url
        embed = discord.Embed(title="TikTok Video", description=str(title)[:2000], color=0xFE2C55, url=webpage_url)
        if thumbnail:
            embed.set_image(url=thumbnail)
        embed.add_field(name="Author", value=f"[@{uploader_id}](https://www.tiktok.com/@{uploader_id})", inline=True)
        embed.add_field(name="Views", value=format_number(view_count), inline=True)
        embed.add_field(name="Likes", value=format_number(like_count), inline=True)
        embed.add_field(name="Comments", value=format_number(comment_count), inline=True)
        embed.add_field(name="Duration", value=f"{duration}s" if duration else "N/A", inline=True)
        embed.set_footer(text="Reverse Video")
        embed.timestamp = datetime.now(timezone.utc)
        try:
            video_bytes, _ = await asyncio.to_thread(download_video_bytes, url)
            if len(video_bytes) < 24 * 1024 * 1024:
                file = discord.File(fp=BytesIO(video_bytes), filename="tiktok.mp4")
                await ctx.reply(embed=embed, file=file, mention_author=False)
            else:
                await ctx.reply(embed=embed, mention_author=False)
        except Exception:
            await ctx.reply(embed=embed, mention_author=False)
        await save_history(ctx.author.id, "reversevid", url, f"@{uploader_id} | {format_number(view_count)} views")
    except Exception as e:
        await ctx.reply(f"❌ Failed\n```{str(e)[:500]}```", mention_author=False)


@bot.command(name="search")
async def search_prefix(ctx: commands.Context, *, query: str):
    """`,search <query>`"""
    await ctx.typing()
    try:
        results = await asyncio.to_thread(search_tiktok, query, 6)
        if not results:
            await ctx.reply("No results found.", mention_author=False)
            return
        embed = discord.Embed(title=f"Search: {query}", color=0xFE2C55)
        for i, video in enumerate(results[:6], 1):
            title = (video.get("title") or "No title")[:55]
            url = video.get("url") or video.get("webpage_url")
            uploader = video.get("uploader") or "unknown"
            views = format_number(video.get("view_count"))
            if url:
                embed.add_field(name=f"{i}. {title}", value=f"@{uploader} • {views} views\n[Watch]({url})", inline=False)
        embed.set_footer(text="TikTok Search")
        embed.timestamp = datetime.now(timezone.utc)
        await ctx.reply(embed=embed, mention_author=False)
        await save_history(ctx.author.id, "search", query, f"{len(results)} results")
    except Exception as e:
        await ctx.reply(f"❌ Search failed\n```{str(e)[:400]}```", mention_author=False)


@bot.command(name="uservideos", aliases=["uv"])
async def uservideos_prefix(ctx: commands.Context, username: str, limit: int = 6):
    """`,uservideos <username> [limit]`"""
    await ctx.typing()
    username = username.lstrip("@").strip()
    limit = max(1, min(12, limit))
    try:
        info = await asyncio.to_thread(get_user_info_ytdlp, username)
        entries = info.get("entries") or []
        if not entries:
            await ctx.reply("No videos found.", mention_author=False)
            return
        embed = discord.Embed(title=f"Videos from @{username}", color=0x00F2EA,
                              url=f"https://www.tiktok.com/@{username}")
        for i, entry in enumerate(entries[:limit], 1):
            title = (entry.get("title") or "No title")[:50]
            url = entry.get("url") or entry.get("webpage_url")
            views = format_number(entry.get("view_count"))
            if url:
                embed.add_field(name=f"{i}. {title}", value=f"{views} views • [Watch]({url})", inline=False)
        embed.set_footer(text="User Videos")
        embed.timestamp = datetime.now(timezone.utc)
        await ctx.reply(embed=embed, mention_author=False)
        await save_history(ctx.author.id, "uservideos", username, f"{len(entries[:limit])} videos")
    except Exception as e:
        await ctx.reply(f"❌ Failed\n```{str(e)[:400]}```", mention_author=False)


@bot.command(name="download", aliases=["dl"])
async def download_prefix(ctx: commands.Context, url: str):
    """`,download <tiktok_url>`"""
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await ctx.reply("❌ Invalid TikTok URL.", mention_author=False)
        return
    status = await ctx.reply("⬇️ Downloading…", mention_author=False)
    try:
        video_bytes, info = await asyncio.to_thread(download_video_bytes, url)
        title = (info.get("title") or "tiktok")[:40]
        filename = re.sub(r'[\\/*?:"<>|]', "", title) + ".mp4"
        if len(video_bytes) > 24 * 1024 * 1024:
            await status.edit(content="⚠️ Video too large (over 24 MB).")
            return
        file = discord.File(fp=BytesIO(video_bytes), filename=filename)
        await status.edit(content=f"**Downloaded:** {title}", attachments=[file])
        await save_history(ctx.author.id, "download", url, title)
    except Exception as e:
        await status.edit(content=f"❌ Download failed\n```{str(e)[:400]}```")


@bot.command(name="sound")
async def sound_prefix(ctx: commands.Context, url: str):
    """`,sound <tiktok_url>`"""
    if "tiktok.com" not in url.lower() and "vm.tiktok.com" not in url.lower():
        await ctx.reply("❌ Please provide a valid TikTok video URL.", mention_author=False)
        return
    await ctx.typing()
    try:
        info = await asyncio.to_thread(get_video_info, url)
        track = info.get("track") or "Unknown"
        artist = info.get("artist") or info.get("creator") or "Unknown"
        duration = info.get("duration")
        view_count = info.get("view_count")
        webpage_url = info.get("webpage_url") or url
        sound_title = info.get("track") or info.get("title") or "Unknown Sound"
        embed = discord.Embed(title="TikTok Sound / Music", description=f"**{sound_title}**",
                              color=0x9B59B6, url=webpage_url)
        embed.add_field(name="Track", value=str(track)[:256], inline=True)
        embed.add_field(name="Artist", value=str(artist)[:256], inline=True)
        embed.add_field(name="Duration", value=f"{duration}s" if duration else "N/A", inline=True)
        embed.add_field(name="Video Views", value=format_number(view_count), inline=True)
        thumb = info.get("thumbnail")
        if thumb:
            embed.set_thumbnail(url=thumb)
        embed.set_footer(text="Sound Lookup")
        embed.timestamp = datetime.now(timezone.utc)
        await ctx.reply(embed=embed, mention_author=False)
        await save_history(ctx.author.id, "sound", url, sound_title)
    except Exception as e:
        await ctx.reply(f"❌ Failed to get sound info\n```{str(e)[:400]}```", mention_author=False)


@bot.command(name="history")
async def history_prefix(ctx: commands.Context, limit: int = 8):
    """`,history [limit]`"""
    limit = max(1, min(15, limit))
    async with aiosqlite.connect(HISTORY_DB) as db:
        cursor = await db.execute(
            "SELECT command, query, result_summary, timestamp FROM history WHERE user_id = ? ORDER BY id DESC LIMIT ?",
            (ctx.author.id, limit),
        )
        rows = await cursor.fetchall()
    if not rows:
        await ctx.reply("No history yet.", mention_author=False)
        return
    embed = discord.Embed(title="Your Search History", color=0x5865F2)
    for cmd, query, summary, ts in rows:
        embed.add_field(
            name=f"`{PREFIX}{cmd}` — {query[:40]}",
            value=f"{summary}\n<t:{int(datetime.fromisoformat(ts).timestamp())}:R>",
            inline=False,
        )
    await ctx.reply(embed=embed, mention_author=False)


# ===========================================================================
# GREED-STYLE COMMANDS  (economy / afk / levels / giveaways / reminders /
#                        birthdays / starboard / welcome / fun)
# Data lives in history.db (sqlite). Per-guild config in config.json.
# ===========================================================================
STAR_EMOJI = "⭐"
STAR_THRESHOLD = 5  # default stars to qualify for starboard
GIVEAWAY_EMOJI = "🎉"
EMOJIS_SLOT = ["🍒", "🍋", "🍉", "🍇", "🔔", "⭐", "7️⃣"]

# Economy tunables
DAILY_REWARD = 250
DAILY_COOLDOWN_HOURS = 22
WORK_MIN, WORK_MAX = 50, 200
WORK_COOLDOWN_HOURS = 1


# --- Economy helpers --------------------------------------------------------

async def _get_balance(guild_id: int, user_id: int) -> tuple[int, int]:
    """Return (cash, bank)."""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT balance, bank FROM economy WHERE guild_id=? AND user_id=?",
            (guild_id, user_id),
        )
        row = await cur.fetchone()
    if row is None:
        return 0, 0
    return int(row[0] or 0), int(row[1] or 0)


async def _set_balance(guild_id: int, user_id: int, cash: int, bank: int) -> None:
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO economy (guild_id, user_id, balance, bank) VALUES (?,?,?,?) "
            "ON CONFLICT(guild_id, user_id) DO UPDATE SET balance=?, bank=?",
            (guild_id, user_id, cash, bank, cash, bank),
        )
        await db.commit()


async def _add_balance(guild_id: int, user_id: int, amount: int) -> int:
    """Add (or subtract, if amount < 0) cash. Returns new cash balance (>= 0)."""
    cash, bank = await _get_balance(guild_id, user_id)
    cash = max(0, cash + amount)
    await _set_balance(guild_id, user_id, cash, bank)
    return cash


# --- Leveling helpers -------------------------------------------------------

def _xp_for_level(level: int) -> int:
    """Cumulative XP required to reach `level`."""
    return 100 + 50 * level + 5 * level * level


async def _add_xp(guild_id: int, user_id: int,
                  channel: Optional[discord.TextChannel],
                  member: discord.Member) -> None:
    settings = config.get(str(guild_id), {})
    if not settings.get("leveling_enabled", True):
        return
    gain = random.randint(15, 25)
    try:
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute(
                "INSERT INTO levels (guild_id, user_id, xp, messages) VALUES (?,?,?,1) "
                "ON CONFLICT(guild_id, user_id) DO UPDATE SET xp=xp+?, messages=messages+1",
                (guild_id, user_id, gain, gain),
            )
            cur = await db.execute(
                "SELECT xp, messages FROM levels WHERE guild_id=? AND user_id=?",
                (guild_id, user_id),
            )
            row = await cur.fetchone()
            await db.commit()
    except Exception as e:
        log(f"xp insert failed: {e}")
        return
    if not row:
        return
    xp = int(row[0] or 0)
    msgs = int(row[1] or 0)
    level = 0
    while xp >= _xp_for_level(level + 1):
        level += 1
    # Did this message push us over into a new level?
    if level > 0 and (xp - gain) < _xp_for_level(level) <= xp:
        if channel is not None:
            try:
                await channel.send(
                    f"🎉 {member.mention} leveled up to **level {level}**!",
                    delete_after=10,
                )
            except discord.HTTPException:
                pass
        # Auto-role reward (configured via /levelconfig)
        rewards = settings.get("level_roles") or {}
        role_id = rewards.get(str(level))
        if role_id:
            role = member.guild.get_role(role_id)
            if role and role < member.guild.me.top_role and not role.managed:
                try:
                    await member.add_roles(role, reason=f"Level {level} reward")
                except discord.HTTPException:
                    pass


async def _get_level_data(guild_id: int, user_id: int) -> tuple[int, int, int]:
    """Return (xp, messages, level)."""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT xp, messages FROM levels WHERE guild_id=? AND user_id=?",
            (guild_id, user_id),
        )
        row = await cur.fetchone()
    xp = int(row[0] or 0) if row else 0
    msgs = int(row[1] or 0) if row else 0
    level = 0
    while xp >= _xp_for_level(level + 1):
        level += 1
    return xp, msgs, level


# --- AFK helper -------------------------------------------------------------

async def _handle_afk_on_message(message: discord.Message) -> None:
    """If author is AFK, clear it. If they mentioned AFK users, notify."""
    guild = message.guild
    if guild is None:
        return
    try:
        async with aiosqlite.connect(HISTORY_DB) as db:
            cur = await db.execute(
                "SELECT message, since FROM afk WHERE guild_id=? AND user_id=?",
                (guild.id, message.author.id),
            )
            row = await cur.fetchone()
            if row:
                await db.execute(
                    "DELETE FROM afk WHERE guild_id=? AND user_id=?",
                    (guild.id, message.author.id),
                )
                await db.commit()
                try:
                    await message.reply(
                        f"👋 Welcome back, {message.author.mention}! AFK cleared.",
                        mention_author=False, delete_after=10,
                    )
                except discord.HTTPException:
                    pass
    except Exception as e:
        log(f"afk clear failed: {e}")

    if not message.mentions:
        return
    try:
        ids = [m.id for m in message.mentions]
        placeholders = ",".join("?" * len(ids))
        async with aiosqlite.connect(HISTORY_DB) as db:
            cur = await db.execute(
                f"SELECT user_id, message, since FROM afk WHERE guild_id=? AND user_id IN ({placeholders})",
                (guild.id, *ids),
            )
            rows = await cur.fetchall()
    except Exception as e:
        log(f"afk lookup failed: {e}")
        return
    for uid, afk_msg, since in rows:
        if uid == message.author.id:
            continue
        member = guild.get_member(uid)
        name = member.display_name if member else f"<@{uid}>"
        since_ts = iso_to_ts(since or "")
        ago = f" (since <t:{since_ts}:R>)" if since_ts else ""
        try:
            await message.reply(
                f"💤 **{name}** is AFK{ago}: {afk_msg or 'AFK'}",
                mention_author=False, delete_after=15,
            )
        except discord.HTTPException:
            pass


# --- Background loops -------------------------------------------------------

async def _reminder_loop():
    """Fire due reminders every 30 seconds."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            now_iso = datetime.now(timezone.utc).isoformat()
            rows: list[tuple] = []
            async with aiosqlite.connect(HISTORY_DB) as db:
                cur = await db.execute(
                    "SELECT id, user_id, channel_id, message FROM reminders WHERE remind_at <= ?",
                    (now_iso,),
                )
                rows = await cur.fetchall()
                if rows:
                    ids = tuple(r[0] for r in rows)
                    placeholders = ",".join("?" * len(ids))
                    await db.execute(
                        f"DELETE FROM reminders WHERE id IN ({placeholders})", ids
                    )
                    await db.commit()
            for _rid, uid, cid, msg in rows:
                channel = bot.get_channel(cid)
                if channel is None:
                    try:
                        channel = await bot.fetch_channel(cid)
                    except discord.HTTPException:
                        continue
                if channel is None:
                    continue
                try:
                    await channel.send(
                        f"⏰ <@{uid}> reminder: {msg or 'no message'}",
                        allowed_mentions=discord.AllowedMentions(users=True),
                    )
                except discord.HTTPException:
                    pass
        except Exception as e:
            log(f"reminder loop error: {e}")
        await asyncio.sleep(30)


async def _birthday_loop():
    """Once an hour, post birthday wishes in configured channels."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            now = datetime.now()
            today = now.date()
            key = (today.month, today.day, now.hour)
            if getattr(_birthday_loop, "_ran", None) == key:
                await asyncio.sleep(900)
                continue
            _birthday_loop._ran = key  # type: ignore[attr-defined]
            async with aiosqlite.connect(HISTORY_DB) as db:
                cur = await db.execute(
                    "SELECT guild_id, user_id FROM birthdays WHERE month=? AND day=?",
                    (today.month, today.day),
                )
                rows = await cur.fetchall()
            for gid, uid in rows:
                settings = config.get(str(gid), {})
                bc_id = settings.get("birthday_channel")
                if not bc_id:
                    continue
                guild = bot.get_guild(gid)
                if guild is None:
                    continue
                bc = guild.get_channel(bc_id)
                if not isinstance(bc, discord.TextChannel):
                    continue
                try:
                    await bc.send(
                        f"🎉 Happy birthday, <@{uid}>! 🎂",
                        allowed_mentions=discord.AllowedMentions(users=True),
                    )
                except discord.HTTPException:
                    pass
        except Exception as e:
            log(f"birthday loop error: {e}")
        await asyncio.sleep(900)


async def _giveaway_loop():
    """End giveaways whose time is up."""
    await bot.wait_until_ready()
    while not bot.is_closed():
        try:
            now_iso = datetime.now(timezone.utc).isoformat()
            rows: list[tuple] = []
            async with aiosqlite.connect(HISTORY_DB) as db:
                cur = await db.execute(
                    "SELECT id, guild_id, channel_id, message_id, prize, host_id, winners "
                    "FROM giveaways WHERE ended=0 AND ends_at <= ?",
                    (now_iso,),
                )
                rows = await cur.fetchall()
                if rows:
                    ids = tuple(r[0] for r in rows)
                    placeholders = ",".join("?" * len(ids))
                    await db.execute(
                        f"UPDATE giveaways SET ended=1 WHERE id IN ({placeholders})", ids
                    )
                    await db.commit()
            for row in rows:
                _gid, gid, ch_id, msg_id, prize, host_id, winners = row
                guild = bot.get_guild(gid)
                if guild is None:
                    continue
                ch = guild.get_channel(ch_id)
                if not isinstance(ch, discord.TextChannel):
                    continue
                try:
                    msg = await ch.fetch_message(msg_id)
                except discord.HTTPException:
                    continue
                users: list[discord.User] = []
                for r in msg.reactions:
                    if str(r.emoji) == GIVEAWAY_EMOJI:
                        async for u in r.users():
                            if not u.bot:
                                users.append(u)
                        break
                if not users:
                    try:
                        await msg.edit(
                            content="🎉 **Giveaway ended** — no entrants. 😢",
                            allowed_mentions=discord.AllowedMentions.none(),
                        )
                    except discord.HTTPException:
                        pass
                    continue
                win_n = max(1, min(int(winners or 1), len(users)))
                picked = random.sample(users, win_n)
                mention_str = " ".join(u.mention for u in picked)
                try:
                    await msg.edit(content=f"🎉 **Giveaway ended!** Winners: {mention_str}")
                    await ch.send(
                        f"🎉 Congrats {mention_str}! You won **{prize or 'a prize'}** "
                        f"(host: <@{host_id}>)"
                    )
                except discord.HTTPException:
                    pass
        except Exception as e:
            log(f"giveaway loop error: {e}")
        await asyncio.sleep(45)


# ===========================================================================
# Economy slash commands
# ===========================================================================

@bot.tree.command(name="balance", description="Show your cash + bank balance")
@app_commands.guild_only()
async def balance_cmd(interaction: discord.Interaction, member: Optional[discord.Member] = None):
    member = member or interaction.user
    cash, bank = await _get_balance(interaction.guild_id, member.id)
    embed = discord.Embed(title=f"💰 {member.display_name}'s balance", color=0x2ECC71)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="💵 Cash", value=f"{cash:,} bucks", inline=True)
    embed.add_field(name="🏦 Bank", value=f"{bank:,} bucks", inline=True)
    embed.add_field(name="📊 Net worth", value=f"{cash + bank:,} bucks", inline=True)
    embed.set_footer(text="Use /daily and /work to earn")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="daily", description="Claim your daily bucks")
@app_commands.guild_only()
@app_commands.checks.cooldown(1, DAILY_COOLDOWN_HOURS * 3600,
                              key=lambda i: (i.guild_id, i.user_id))
async def daily_cmd(interaction: discord.Interaction):
    now = datetime.now(timezone.utc)
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT last_daily FROM economy WHERE guild_id=? AND user_id=?",
            (interaction.guild_id, interaction.user.id),
        )
        row = await cur.fetchone()
        last = row[0] if row else None
    if last:
        try:
            last_dt = datetime.fromisoformat(last)
            if now - last_dt < timedelta(hours=DAILY_COOLDOWN_HOURS):
                remaining = timedelta(hours=DAILY_COOLDOWN_HOURS) - (now - last_dt)
                mins = int(remaining.total_seconds() // 60)
                await interaction.response.send_message(
                    f"⏳ You already claimed. Come back in **{mins} min**.",
                    ephemeral=True,
                )
                return
        except ValueError:
            pass
    cash = await _add_balance(interaction.guild_id, interaction.user.id, DAILY_REWARD)
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "UPDATE economy SET last_daily=? WHERE guild_id=? AND user_id=?",
            (now.isoformat(), interaction.guild_id, interaction.user.id),
        )
        await db.commit()
    await interaction.response.send_message(
        f"💵 You claimed **{DAILY_REWARD}** bucks! New balance: **{cash:,}**."
    )


@daily_cmd.error
async def daily_cmd_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CommandOnCooldown):
        mins = int(error.retry_after // 60)
        await interaction.response.send_message(
            f"⏳ Come back in **{mins} min** to claim again.", ephemeral=True
        )


@bot.tree.command(name="work", description="Work a quick job for some bucks")
@app_commands.guild_only()
@app_commands.checks.cooldown(1, WORK_COOLDOWN_HOURS * 3600,
                              key=lambda i: (i.guild_id, i.user_id))
async def work_cmd(interaction: discord.Interaction):
    jobs = [
        "wrote some code", "delivered pizzas", "walked dogs", "mowed lawns",
        "fixed a router", "bartended", "drove a taxi", "made coffee",
        "tutored math", "painted a fence", "stocked shelves",
        "walked an elderly neighbor's cat", "fixed a leaky faucet",
        "sang for tips", "data entry for a startup",
    ]
    earned = random.randint(WORK_MIN, WORK_MAX)
    cash = await _add_balance(interaction.guild_id, interaction.user.id, earned)
    await interaction.response.send_message(
        f"🛠️ You {random.choice(jobs)} and earned **{earned}** bucks! Balance: **{cash:,}**."
    )


@work_cmd.error
async def work_cmd_error(interaction: discord.Interaction, error: app_commands.AppCommandError):
    if isinstance(error, app_commands.CommandOnCooldown):
        mins = int(error.retry_after // 60)
        await interaction.response.send_message(
            f"⏳ You're tired — rest **{mins} min** before working again.",
            ephemeral=True,
        )


@bot.tree.command(name="deposit", description="Deposit cash into your bank (safe from robbery)")
@app_commands.guild_only()
@app_commands.describe(amount="How much (or 'all')")
async def deposit_cmd(interaction: discord.Interaction, amount: str):
    cash, bank = await _get_balance(interaction.guild_id, interaction.user.id)
    amt = cash if amount.lower() == "all" else as_int(amount)
    if amt is None or amt <= 0:
        await interaction.response.send_message("❌ Enter a positive number or 'all'.", ephemeral=True)
        return
    if amt > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return
    await _set_balance(interaction.guild_id, interaction.user.id, cash - amt, bank + amt)
    await interaction.response.send_message(
        f"🏦 Deposited **{amt:,}** bucks. Cash: **{cash - amt:,}** · Bank: **{bank + amt:,}**."
    )


@bot.tree.command(name="withdraw", description="Withdraw bucks from your bank")
@app_commands.guild_only()
@app_commands.describe(amount="How much (or 'all')")
async def withdraw_cmd(interaction: discord.Interaction, amount: str):
    cash, bank = await _get_balance(interaction.guild_id, interaction.user.id)
    amt = bank if amount.lower() == "all" else as_int(amount)
    if amt is None or amt <= 0:
        await interaction.response.send_message("❌ Enter a positive number or 'all'.", ephemeral=True)
        return
    if amt > bank:
        await interaction.response.send_message(f"❌ You only have **{bank:,}** in the bank.", ephemeral=True)
        return
    await _set_balance(interaction.guild_id, interaction.user.id, cash + amt, bank - amt)
    await interaction.response.send_message(
        f"💸 Withdrew **{amt:,}** bucks. Cash: **{cash + amt:,}** · Bank: **{bank - amt:,}**."
    )


@bot.tree.command(name="pay", description="Send bucks to another member")
@app_commands.guild_only()
@app_commands.describe(member="Recipient", amount="How much")
async def pay_cmd(interaction: discord.Interaction,
                 member: discord.Member,
                 amount: app_commands.Range[int, 1]):
    if member.id == interaction.user.id or member.bot:
        await interaction.response.send_message("❌ Pick someone else.", ephemeral=True)
        return
    cash, _bank = await _get_balance(interaction.guild_id, interaction.user.id)
    if amount > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return
    await _add_balance(interaction.guild_id, interaction.user.id, -amount)
    await _add_balance(interaction.guild_id, member.id, amount)
    await interaction.response.send_message(f"💸 Sent **{amount:,}** bucks to {member.mention}.")


# ===========================================================================
# Gambling slash commands
# ===========================================================================

@bot.tree.command(name="coinflip", description="Bet bucks on heads or tails")
@app_commands.guild_only()
@app_commands.choices(choice=[
    app_commands.Choice(name="Heads", value="heads"),
    app_commands.Choice(name="Tails", value="tails"),
])
@app_commands.describe(choice="Heads or tails", bet="How much to bet")
async def coinflip_cmd(interaction: discord.Interaction,
                       choice: app_commands.Choice[str],
                       bet: app_commands.Range[int, 1]):
    cash, _ = await _get_balance(interaction.guild_id, interaction.user.id)
    if bet > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return
    result = random.choice(["heads", "tails"])
    if choice.value == result:
        await _add_balance(interaction.guild_id, interaction.user.id, bet)
        await interaction.response.send_message(
            f"🪙 It was **{result}**! You won **{bet:,}** bucks! 🎉"
        )
    else:
        await _add_balance(interaction.guild_id, interaction.user.id, -bet)
        await interaction.response.send_message(
            f"🪙 It was **{result}**. You lost **{bet:,}** bucks. 😢"
        )


@bot.tree.command(name="dice", description="Roll a die and bet on the outcome (1-6)")
@app_commands.guild_only()
@app_commands.describe(guess="Your guess 1-6", bet="How much to bet")
async def dice_cmd(interaction: discord.Interaction,
                   guess: app_commands.Range[int, 1, 6],
                   bet: app_commands.Range[int, 1]):
    cash, _ = await _get_balance(interaction.guild_id, interaction.user.id)
    if bet > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return
    roll = random.randint(1, 6)
    if roll == guess:
        winnings = bet * 5
        await _add_balance(interaction.guild_id, interaction.user.id, winnings)
        await interaction.response.send_message(
            f"🎲 Rolled **{roll}** — exact match! You won **{winnings:,}** bucks! 🎉"
        )
    else:
        await _add_balance(interaction.guild_id, interaction.user.id, -bet)
        await interaction.response.send_message(
            f"🎲 Rolled **{roll}**. You guessed **{guess}**. Lost **{bet:,}** bucks."
        )


@bot.tree.command(name="slots", description="Spin the slot machine")
@app_commands.guild_only()
@app_commands.describe(bet="How much to bet")
async def slots_cmd(interaction: discord.Interaction, bet: app_commands.Range[int, 1]):
    cash, _ = await _get_balance(interaction.guild_id, interaction.user.id)
    if bet > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return
    reels = [random.choice(EMOJIS_SLOT) for _ in range(3)]
    if reels[0] == reels[1] == reels[2]:
        mult = 10 if "7" in reels[0] else 5
        winnings = bet * mult
        await _add_balance(interaction.guild_id, interaction.user.id, winnings - bet)
        await interaction.response.send_message(
            f"🎰 {' | '.join(reels)}\n🎉 Three of a kind! You won **{winnings:,}** bucks (x{mult})!"
        )
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]:
        winnings = max(1, int(bet * 1.5))
        await _add_balance(interaction.guild_id, interaction.user.id, winnings - bet)
        await interaction.response.send_message(
            f"🎰 {' | '.join(reels)}\n✨ Pair! You won **{winnings:,}** bucks (x1.5)."
        )
    else:
        await _add_balance(interaction.guild_id, interaction.user.id, -bet)
        await interaction.response.send_message(
            f"🎰 {' | '.join(reels)}\n😢 No match. Lost **{bet:,}** bucks."
        )


@bot.tree.command(name="scratch", description="Buy a scratch card (50 bucks)")
@app_commands.guild_only()
async def scratch_cmd(interaction: discord.Interaction):
    cost = 50
    cash, _ = await _get_balance(interaction.guild_id, interaction.user.id)
    if cash < cost:
        await interaction.response.send_message(
            f"❌ A scratch card costs {cost} bucks. You have {cash:,}.", ephemeral=True
        )
        return
    await _add_balance(interaction.guild_id, interaction.user.id, -cost)
    roll = random.random()
    if roll < 0.05:
        win = 1000
    elif roll < 0.15:
        win = 250
    elif roll < 0.35:
        win = 100
    elif roll < 0.55:
        win = 50
    else:
        win = 0
    if win:
        await _add_balance(interaction.guild_id, interaction.user.id, win)
        await interaction.response.send_message(
            f"🎫 You scratched the card... and won **{win:,}** bucks! 🎉"
        )
    else:
        await interaction.response.send_message(
            "🎫 You scratched the card... nothing. Better luck next time!"
        )


@bot.tree.command(name="blackjack", description="Play a quick hand of blackjack vs the dealer")
@app_commands.guild_only()
@app_commands.describe(bet="How much to bet")
async def blackjack_cmd(interaction: discord.Interaction, bet: app_commands.Range[int, 1]):
    cash, _ = await _get_balance(interaction.guild_id, interaction.user.id)
    if bet > cash:
        await interaction.response.send_message(f"❌ You only have **{cash:,}** cash.", ephemeral=True)
        return

    def card():
        return random.randint(1, 11)

    def hand_value(cards):
        v = sum(cards)
        if 1 in cards and v + 10 <= 21:
            v += 10
        return v

    player = [card(), card()]
    dealer = [card(), card()]
    pv = hand_value(player)
    dv = hand_value(dealer)
    # Auto-hit player to 17
    while pv < 17:
        player.append(card())
        pv = hand_value(player)
    # Dealer hits to 17
    while dv < 17:
        dealer.append(card())
        dv = hand_value(dealer)

    if pv > 21:
        result = "bust"
    elif dv > 21:
        result = "win"
    elif pv > dv:
        result = "win"
    elif pv < dv:
        result = "lose"
    else:
        result = "push"

    msg = (
        f"🃏 Your hand: {player} ({pv})\n"
        f"🃏 Dealer: {dealer} ({dv})\n"
    )
    if result == "win":
        await _add_balance(interaction.guild_id, interaction.user.id, bet)
        await interaction.response.send_message(msg + f"\n🎉 You won **{bet:,}** bucks!")
    elif result == "push":
        await interaction.response.send_message(msg + "\n🤝 Push — bet returned.")
    else:
        await _add_balance(interaction.guild_id, interaction.user.id, -bet)
        await interaction.response.send_message(msg + f"\n😢 You lost **{bet:,}** bucks.")


@bot.tree.command(name="leaderboard", description="Show the top earners in this server")
@app_commands.guild_only()
async def leaderboard_cmd(interaction: discord.Interaction):
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT user_id, balance, bank FROM economy WHERE guild_id=? "
            "ORDER BY (balance+bank) DESC LIMIT 10",
            (interaction.guild_id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await interaction.response.send_message("No economy data yet. Try `/daily` first!")
        return
    embed = discord.Embed(title="🏆 Economy Leaderboard", color=0xF1C40F)
    medals = ["🥇", "🥈", "🥉"] + ["•"] * 7
    lines = []
    for i, (uid, bal, bank) in enumerate(rows):
        member = interaction.guild.get_member(uid)
        name = member.display_name if member else f"<@{uid}>"
        net = int(bal or 0) + int(bank or 0)
        lines.append(f"{medals[i]} **{name}** — {net:,} bucks")
    embed.description = "\n".join(lines)
    await interaction.response.send_message(embed=embed)


# ===========================================================================
# AFK
# ===========================================================================

@bot.tree.command(name="afk", description="Set yourself AFK so the bot tells people who mention you")
@app_commands.guild_only()
@app_commands.describe(message="Why you're away (default: AFK)")
async def afk_cmd(interaction: discord.Interaction, message: str = "AFK"):
    now_iso = datetime.now(timezone.utc).isoformat()
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO afk (guild_id, user_id, message, since) VALUES (?,?,?,?) "
            "ON CONFLICT(guild_id, user_id) DO UPDATE SET message=excluded.message, since=excluded.since",
            (interaction.guild_id, interaction.user.id, message[:500], now_iso),
        )
        await db.commit()
    await interaction.response.send_message(
        f"💤 You're now AFK: **{message}**. I'll let people know when they mention you."
    )


# ===========================================================================
# Leveling
# ===========================================================================

@bot.tree.command(name="rank", description="Show your level, XP, and rank in this server")
@app_commands.guild_only()
async def rank_cmd(interaction: discord.Interaction, member: Optional[discord.Member] = None):
    member = member or interaction.user
    xp, msgs, level = await _get_level_data(interaction.guild_id, member.id)
    next_xp = _xp_for_level(level + 1)
    cur_level_xp = _xp_for_level(level)
    pct = int(((xp - cur_level_xp) / max(1, next_xp - cur_level_xp)) * 100) if next_xp > cur_level_xp else 0
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT COUNT(*)+1 FROM levels WHERE guild_id=? AND xp > ?",
            (interaction.guild_id, xp),
        )
        rank_n = (await cur.fetchone())[0]
    embed = discord.Embed(title=f"📈 {member.display_name}", color=member.color or 0x2ECC71)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="Level", value=str(level), inline=True)
    embed.add_field(name="XP", value=f"{xp:,} / {next_xp:,}", inline=True)
    embed.add_field(name="Rank", value=f"#{rank_n}", inline=True)
    embed.add_field(name="Messages", value=str(msgs), inline=True)
    bar_len = 20
    filled = int(pct / 100 * bar_len)
    bar = "█" * filled + "░" * (bar_len - filled)
    embed.add_field(name=f"Progress to L{level+1}", value=f"`{bar}` {pct}%", inline=False)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="levels", description="Show the top levelers in this server")
@app_commands.guild_only()
async def levels_cmd(interaction: discord.Interaction):
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT user_id, xp FROM levels WHERE guild_id=? ORDER BY xp DESC LIMIT 10",
            (interaction.guild_id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await interaction.response.send_message("No XP yet. Send some messages!")
        return
    embed = discord.Embed(title="📈 Levels Leaderboard", color=0xF1C40F)
    medals = ["🥇", "🥈", "🥉"] + ["•"] * 7
    lines = []
    for i, (uid, xp) in enumerate(rows):
        m = interaction.guild.get_member(uid)
        name = m.display_name if m else f"<@{uid}>"
        lvl = 0
        x = int(xp or 0)
        while x >= _xp_for_level(lvl + 1):
            lvl += 1
        lines.append(f"{medals[i]} **{name}** — L{lvl} · {x:,} XP")
    embed.description = "\n".join(lines)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="levelconfig", description="Configure leveling (admins)")
@app_commands.guild_only()
@app_commands.describe(
    enabled="Turn leveling on/off",
    reward_role="Role to give when reaching a level",
    level="Which level this role is for",
)
@app_commands.checks.has_permissions(manage_guild=True)
async def levelconfig_cmd(interaction: discord.Interaction,
                          enabled: Optional[bool] = None,
                          reward_role: Optional[discord.Role] = None,
                          level: Optional[app_commands.Range[int, 1, 200]] = None):
    settings = config.setdefault(str(interaction.guild_id), {})
    if enabled is not None:
        settings["leveling_enabled"] = enabled
    if reward_role is not None and level is not None:
        rewards = settings.setdefault("level_roles", {})
        rewards[str(level)] = reward_role.id
    save_config(config)
    msg_parts = [f"Leveling: **{'on' if settings.get('leveling_enabled', True) else 'off'}**"]
    rewards = settings.get("level_roles") or {}
    if rewards:
        msg_parts.append("Rewards: " + ", ".join(f"L{k} → <@&{v}>" for k, v in rewards.items()))
    await interaction.response.send_message("\n".join(msg_parts), ephemeral=True)


# ===========================================================================
# Giveaways
# ===========================================================================

@bot.tree.command(name="giveaway", description="Run a giveaway")
@app_commands.guild_only()
@app_commands.choices(action=[
    app_commands.Choice(name="Start", value="start"),
    app_commands.Choice(name="End", value="end"),
    app_commands.Choice(name="Reroll", value="reroll"),
])
@app_commands.describe(
    action="start / end / reroll",
    prize="Prize name (for start)",
    duration="How long (e.g. 1h, 30m, 2d) — for start",
    winners="Number of winners (default 1)",
    message_id="Giveaway message ID — for end/reroll",
)
@app_commands.checks.has_permissions(manage_messages=True)
async def giveaway_cmd(interaction: discord.Interaction,
                       action: app_commands.Choice[str],
                       prize: Optional[str] = None,
                       duration: Optional[str] = None,
                       winners: Optional[app_commands.Range[int, 1, 20]] = None,
                       message_id: Optional[str] = None):
    if action.value == "start":
        if not prize:
            await interaction.response.send_message("❌ Provide a `prize`.", ephemeral=True)
            return
        delta = parse_duration(duration or "1h")
        if delta is None or delta < timedelta(minutes=1) or delta > timedelta(days=14):
            await interaction.response.send_message(
                "❌ Use a `duration` like `30m`, `1h`, `2d`. Min 1m, max 14d.",
                ephemeral=True,
            )
            return
        ends_at = datetime.now(timezone.utc) + delta
        win_n = winners or 1
        embed = discord.Embed(
            title="🎉 Giveaway!",
            description=(
                f"**Prize:** {prize}\n"
                f"**Winners:** {win_n}\n"
                f"**Ends:** <t:{int(ends_at.timestamp())}:R> "
                f"(<t:{int(ends_at.timestamp())}:f>)\n\n"
                f"React with {GIVEAWAY_EMOJI} to enter!"
            ),
            color=discord.Color.pink(),
            timestamp=ends_at,
        )
        embed.set_footer(text=f"Hosted by {interaction.user}")
        await interaction.response.send_message(embed=embed)
        msg = await interaction.original_response()
        await msg.add_reaction(GIVEAWAY_EMOJI)
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute(
                "INSERT INTO giveaways (guild_id, channel_id, message_id, prize, host_id, ends_at, winners, ended) "
                "VALUES (?,?,?,?,?,?,?,0)",
                (interaction.guild_id, interaction.channel_id, msg.id, prize,
                 interaction.user.id, ends_at.isoformat(), win_n),
            )
            await db.commit()
    elif action.value == "end":
        if not message_id or not message_id.isdigit():
            await interaction.response.send_message("❌ Provide a valid `message_id`.", ephemeral=True)
            return
        mid = int(message_id)
        try:
            msg = await interaction.channel.fetch_message(mid)
        except discord.HTTPException:
            await interaction.response.send_message("❌ Couldn't find that message in this channel.", ephemeral=True)
            return
        users = []
        for r in msg.reactions:
            if str(r.emoji) == GIVEAWAY_EMOJI:
                async for u in r.users():
                    if not u.bot:
                        users.append(u)
                break
        if not users:
            await interaction.response.send_message("❌ No entrants.", ephemeral=True)
            return
        win_n = winners or 1
        picked = random.sample(users, min(win_n, len(users)))
        mention_str = " ".join(u.mention for u in picked)
        try:
            await msg.edit(content=f"🎉 **Giveaway ended!** Winners: {mention_str}")
        except discord.HTTPException:
            pass
        await interaction.response.send_message(f"🎉 Winners: {mention_str}")
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute("UPDATE giveaways SET ended=1 WHERE message_id=?", (mid,))
            await db.commit()
    elif action.value == "reroll":
        if not message_id or not message_id.isdigit():
            await interaction.response.send_message("❌ Provide a valid `message_id`.", ephemeral=True)
            return
        mid = int(message_id)
        try:
            msg = await interaction.channel.fetch_message(mid)
        except discord.HTTPException:
            await interaction.response.send_message("❌ Couldn't find that message.", ephemeral=True)
            return
        users = []
        for r in msg.reactions:
            if str(r.emoji) == GIVEAWAY_EMOJI:
                async for u in r.users():
                    if not u.bot:
                        users.append(u)
                break
        if not users:
            await interaction.response.send_message("❌ No entrants.", ephemeral=True)
            return
        winner = random.choice(users)
        await interaction.response.send_message(f"🎉 New winner: {winner.mention}!")


# ===========================================================================
# Reminders
# ===========================================================================

@bot.tree.command(name="remind", description="Set a reminder")
@app_commands.guild_only()
@app_commands.describe(time="When (e.g. 10m, 2h, 1d)", message="What to remind you")
async def remind_cmd(interaction: discord.Interaction, time: str, message: str):
    delta = parse_duration(time)
    if delta is None or delta < timedelta(seconds=10) or delta > timedelta(days=30):
        await interaction.response.send_message(
            "❌ Use a `time` like `10m`, `2h`, `1d`. Min 10s, max 30d.",
            ephemeral=True,
        )
        return
    remind_at = datetime.now(timezone.utc) + delta
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO reminders (user_id, guild_id, channel_id, remind_at, message, created_at) "
            "VALUES (?,?,?,?,?,?)",
            (interaction.user.id, interaction.guild_id, interaction.channel_id,
             remind_at.isoformat(), message[:500], datetime.now(timezone.utc).isoformat()),
        )
        await db.commit()
    ts = int(remind_at.timestamp())
    await interaction.response.send_message(
        f"⏰ Got it — I'll remind you <t:{ts}:R> (<t:{ts}:f>): {message}"
    )


@bot.tree.command(name="reminders", description="List your pending reminders")
@app_commands.guild_only()
async def reminders_cmd(interaction: discord.Interaction):
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT id, remind_at, message FROM reminders WHERE user_id=? ORDER BY remind_at",
            (interaction.user.id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await interaction.response.send_message("You have no pending reminders.", ephemeral=True)
        return
    lines = []
    for rid, when, msg in rows[:15]:
        ts = iso_to_ts(when)
        lines.append(f"`#{rid}` <t:{ts}:R> — {msg[:60]}")
    embed = discord.Embed(title="⏰ Your reminders", description="\n".join(lines), color=0x5865F2)
    await interaction.response.send_message(embed=embed, ephemeral=True)


@bot.tree.command(name="cancelreminder", description="Cancel a reminder by ID")
@app_commands.guild_only()
@app_commands.describe(reminder_id="Reminder # (from /reminders)")
async def cancelreminder_cmd(interaction: discord.Interaction, reminder_id: int):
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute("SELECT user_id FROM reminders WHERE id=?", (reminder_id,))
        row = await cur.fetchone()
        if not row or row[0] != interaction.user.id:
            await interaction.response.send_message("❌ No such reminder of yours.", ephemeral=True)
            return
        await db.execute("DELETE FROM reminders WHERE id=?", (reminder_id,))
        await db.commit()
    await interaction.response.send_message(f"🗑️ Cancelled reminder #{reminder_id}.")


# ===========================================================================
# Birthdays
# ===========================================================================

@bot.tree.command(name="bday", description="Set or list birthdays")
@app_commands.guild_only()
@app_commands.choices(action=[
    app_commands.Choice(name="Set mine", value="set"),
    app_commands.Choice(name="List", value="list"),
    app_commands.Choice(name="Set announce channel", value="channel"),
])
@app_commands.describe(
    month="Month (1-12) — for set",
    day="Day (1-31) — for set",
    channel="Announce channel — for channel",
)
async def bday_cmd(interaction: discord.Interaction,
                   action: app_commands.Choice[str],
                   month: Optional[app_commands.Range[int, 1, 12]] = None,
                   day: Optional[app_commands.Range[int, 1, 31]] = None,
                   channel: Optional[discord.TextChannel] = None):
    if action.value == "set":
        if not month or not day:
            await interaction.response.send_message("❌ Provide `month` and `day`.", ephemeral=True)
            return
        try:
            date(2024, month, day)  # 2024 is a leap year, covers Feb 29
        except ValueError:
            await interaction.response.send_message("❌ That date doesn't exist.", ephemeral=True)
            return
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute(
                "INSERT INTO birthdays (guild_id, user_id, month, day) VALUES (?,?,?,?) "
                "ON CONFLICT(guild_id, user_id) DO UPDATE SET month=excluded.month, day=excluded.day",
                (interaction.guild_id, interaction.user.id, month, day),
            )
            await db.commit()
        await interaction.response.send_message(f"🎂 Saved your birthday: **{month}/{day}**.")
    elif action.value == "list":
        async with aiosqlite.connect(HISTORY_DB) as db:
            cur = await db.execute(
                "SELECT user_id, month, day FROM birthdays WHERE guild_id=? ORDER BY month, day",
                (interaction.guild_id,),
            )
            rows = await cur.fetchall()
        if not rows:
            await interaction.response.send_message("No birthdays saved yet.", ephemeral=True)
            return
        lines = []
        for uid, m, d in rows:
            member = interaction.guild.get_member(uid)
            name = member.display_name if member else f"<@{uid}>"
            lines.append(f"🎂 {name} — {m}/{d}")
        embed = discord.Embed(title="🎂 Birthdays", description="\n".join(lines), color=0xE91E63)
        await interaction.response.send_message(embed=embed, ephemeral=True)
    elif action.value == "channel":
        if not interaction.user.guild_permissions.manage_guild:
            await interaction.response.send_message("❌ You need Manage Server.", ephemeral=True)
            return
        if not channel:
            await interaction.response.send_message("❌ Provide a `channel`.", ephemeral=True)
            return
        settings = config.setdefault(str(interaction.guild_id), {})
        settings["birthday_channel"] = channel.id
        save_config(config)
        await interaction.response.send_message(f"🎂 Birthday announcements → {channel.mention}.")


# ===========================================================================
# Starboard config
# ===========================================================================

@bot.tree.command(name="starboard", description="Configure the starboard")
@app_commands.guild_only()
@app_commands.describe(
    channel="Channel to post starred messages to",
    threshold="Min stars to qualify (default 5)",
)
@app_commands.checks.has_permissions(manage_guild=True)
async def starboard_cmd(interaction: discord.Interaction,
                        channel: Optional[discord.TextChannel] = None,
                        threshold: Optional[app_commands.Range[int, 1, 50]] = None):
    settings = config.setdefault(str(interaction.guild_id), {})
    if channel is not None:
        settings["starboard_channel"] = channel.id
    if threshold is not None:
        settings["starboard_threshold"] = threshold
    save_config(config)
    sb = settings.get("starboard_channel")
    th = settings.get("starboard_threshold", STAR_THRESHOLD)
    await interaction.response.send_message(
        f"⭐ Starboard: {f'<#{sb}>' if sb else '*not set*'} · threshold: **{th}**",
        ephemeral=True,
    )


# ===========================================================================
# Welcome + Autorole
# ===========================================================================

@bot.tree.command(name="welcome", description="Configure welcome messages")
@app_commands.guild_only()
@app_commands.describe(
    channel="Channel for welcome messages",
    message="Welcome text (use {user}, {server}, {name})",
)
@app_commands.checks.has_permissions(manage_guild=True)
async def welcome_cmd(interaction: discord.Interaction,
                      channel: Optional[discord.TextChannel] = None,
                      message: Optional[str] = None):
    settings = config.setdefault(str(interaction.guild_id), {})
    if channel is not None:
        settings["welcome_channel"] = channel.id
    if message is not None:
        settings["welcome_message"] = message[:1000]
    save_config(config)
    ch = settings.get("welcome_channel")
    msg = settings.get("welcome_message") or "*not set*"
    await interaction.response.send_message(
        f"👋 Welcome channel: {f'<#{ch}>' if ch else '*not set*'}\nMessage: {msg}",
        ephemeral=True,
    )


@bot.tree.command(name="autorole", description="Set the role auto-assigned to new members")
@app_commands.guild_only()
@app_commands.describe(role="Role (leave empty to clear)")
@app_commands.checks.has_permissions(manage_guild=True)
async def autorole_cmd(interaction: discord.Interaction, role: Optional[discord.Role] = None):
    settings = config.setdefault(str(interaction.guild_id), {})
    if role is None:
        settings.pop("autorole", None)
        save_config(config)
        await interaction.response.send_message("🚫 Autorole cleared.", ephemeral=True)
        return
    if role.is_default() or role.managed:
        await interaction.response.send_message("❌ Can't use @everyone or a managed role.", ephemeral=True)
        return
    if role >= interaction.guild.me.top_role:
        await interaction.response.send_message(
            f"❌ My top role must be above {role.mention}.", ephemeral=True
        )
        return
    settings["autorole"] = role.id
    save_config(config)
    await interaction.response.send_message(f"✅ New members will get {role.mention}.", ephemeral=True)


# ===========================================================================
# Fun: RPS, 8ball, roll, poll
# ===========================================================================

@bot.tree.command(name="rps", description="Rock paper scissors vs the bot")
@app_commands.guild_only()
@app_commands.choices(choice=[
    app_commands.Choice(name="Rock", value="rock"),
    app_commands.Choice(name="Paper", value="paper"),
    app_commands.Choice(name="Scissors", value="scissors"),
])
@app_commands.describe(choice="Rock / paper / scissors")
async def rps_cmd(interaction: discord.Interaction, choice: app_commands.Choice[str]):
    bot_choice = random.choice(["rock", "paper", "scissors"])
    emoji_map = {"rock": "🪨", "paper": "📄", "scissors": "✂️"}
    you = choice.value
    if you == bot_choice:
        result = "It's a tie!"
    elif (you == "rock" and bot_choice == "scissors") or \
         (you == "paper" and bot_choice == "rock") or \
         (you == "scissors" and bot_choice == "paper"):
        result = "You win! 🎉"
    else:
        result = "You lose! 😢"
    await interaction.response.send_message(
        f"{emoji_map[you]} vs {emoji_map[bot_choice]} — **{result}**"
    )


@bot.tree.command(name="8ball", description="Ask the magic 8-ball")
@app_commands.describe(question="Your yes/no question")
async def eightball_cmd(interaction: discord.Interaction, question: str):
    answers = [
        "It is certain.", "It is decidedly so.", "Without a doubt.", "Yes definitely.",
        "You may rely on it.", "As I see it, yes.", "Most likely.", "Outlook good.",
        "Yes.", "Signs point to yes.",
        "Reply hazy, try again.", "Ask again later.", "Better not tell you now.",
        "Cannot predict now.", "Concentrate and ask again.",
        "Don't count on it.", "My reply is no.", "My sources say no.",
        "Outlook not so good.", "Very doubtful.",
    ]
    await interaction.response.send_message(f"🎱 **{question}**\n→ _{random.choice(answers)}_")


@bot.tree.command(name="roll", description="Roll dice (e.g. 2d6, 1d20)")
@app_commands.describe(spec="NdM format, e.g. 2d6 (default 1d6)")
async def roll_cmd(interaction: discord.Interaction, spec: str = "1d6"):
    m = re.fullmatch(r"(\d{1,3})d(\d{1,4})", spec.lower().strip())
    if not m:
        await interaction.response.send_message(
            "❌ Use NdM format, e.g. `2d6`, `1d20`, `4d8`.", ephemeral=True
        )
        return
    n, sides = int(m.group(1)), int(m.group(2))
    if n < 1 or n > 100 or sides < 2 or sides > 1000:
        await interaction.response.send_message("❌ 1-100 dice, 2-1000 sides.", ephemeral=True)
        return
    rolls = [random.randint(1, sides) for _ in range(n)]
    total = sum(rolls)
    if n == 1:
        await interaction.response.send_message(f"🎲 d{sides} → **{total}**")
    else:
        await interaction.response.send_message(
            f"🎲 {n}d{sides} → {rolls} = **{total}**"
        )


@bot.tree.command(name="poll", description="Create a quick reaction poll")
@app_commands.guild_only()
@app_commands.describe(question="Poll question",
                       option1="Option 1", option2="Option 2",
                       option3="Option 3 (optional)", option4="Option 4 (optional)",
                       option5="Option 5 (optional)")
async def poll_cmd(interaction: discord.Interaction,
                   question: str,
                   option1: str,
                   option2: str,
                   option3: Optional[str] = None,
                   option4: Optional[str] = None,
                   option5: Optional[str] = None):
    options = [o for o in (option1, option2, option3, option4, option5) if o]
    if len(options) < 2:
        await interaction.response.send_message("❌ Need at least 2 options.", ephemeral=True)
        return
    if len(options) > 10:
        await interaction.response.send_message("❌ Max 10 options.", ephemeral=True)
        return
    letters = ["🇦", "🇧", "🇨", "🇩", "🇪", "🇫", "🇬", "🇭", "🇮", "🇯"]
    desc = "\n".join(f"{letters[i]} {o}" for i, o in enumerate(options))
    embed = discord.Embed(title=f"📊 {question}", description=desc, color=0x5865F2)
    embed.set_footer(text=f"Poll by {interaction.user}")
    await interaction.response.send_message(embed=embed)
    msg = await interaction.original_response()
    for i in range(len(options)):
        try:
            await msg.add_reaction(letters[i])
        except discord.HTTPException:
            pass


# ===========================================================================
# Greed-style PREFIX commands (mirror the slash versions)
# ===========================================================================

@bot.command(name="balance", aliases=["bal"])
@commands.guild_only()
async def balance_prefix(ctx: commands.Context, member: discord.Member = None):
    """`,balance [@member]`"""
    member = member or ctx.author
    cash, bank = await _get_balance(ctx.guild.id, member.id)
    embed = discord.Embed(title=f"💰 {member.display_name}'s balance", color=0x2ECC71)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="💵 Cash", value=f"{cash:,} bucks", inline=True)
    embed.add_field(name="🏦 Bank", value=f"{bank:,} bucks", inline=True)
    embed.add_field(name="📊 Net worth", value=f"{cash + bank:,} bucks", inline=True)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="daily")
@commands.guild_only()
async def daily_prefix(ctx: commands.Context):
    """`,daily — claim your daily bucks`"""
    now = datetime.now(timezone.utc)
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT last_daily FROM economy WHERE guild_id=? AND user_id=?",
            (ctx.guild.id, ctx.author.id),
        )
        row = await cur.fetchone()
        last = row[0] if row else None
    if last:
        try:
            last_dt = datetime.fromisoformat(last)
            if now - last_dt < timedelta(hours=DAILY_COOLDOWN_HOURS):
                remaining = timedelta(hours=DAILY_COOLDOWN_HOURS) - (now - last_dt)
                mins = int(remaining.total_seconds() // 60)
                await ctx.reply(f"⏳ You already claimed. Come back in **{mins} min**.", mention_author=False)
                return
        except ValueError:
            pass
    cash = await _add_balance(ctx.guild.id, ctx.author.id, DAILY_REWARD)
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "UPDATE economy SET last_daily=? WHERE guild_id=? AND user_id=?",
            (now.isoformat(), ctx.guild.id, ctx.author.id),
        )
        await db.commit()
    await ctx.reply(f"💵 You claimed **{DAILY_REWARD}** bucks! New balance: **{cash:,}**.", mention_author=False)


@bot.command(name="work")
@commands.guild_only()
async def work_prefix(ctx: commands.Context):
    """`,work — quick job for bucks`"""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT last_work FROM economy WHERE guild_id=? AND user_id=?",
            (ctx.guild.id, ctx.author.id),
        )
        row = await cur.fetchone()
        last = row[0] if row else None
    if last:
        try:
            last_dt = datetime.fromisoformat(last)
            if datetime.now(timezone.utc) - last_dt < timedelta(hours=WORK_COOLDOWN_HOURS):
                mins = int((timedelta(hours=WORK_COOLDOWN_HOURS) - (datetime.now(timezone.utc) - last_dt)).total_seconds() // 60)
                await ctx.reply(f"⏳ You're tired — rest **{mins} min** before working again.", mention_author=False)
                return
        except ValueError:
            pass
    jobs = [
        "wrote some code", "delivered pizzas", "walked dogs", "mowed lawns",
        "fixed a router", "bartended", "drove a taxi", "made coffee",
        "tutored math", "painted a fence", "stocked shelves",
    ]
    earned = random.randint(WORK_MIN, WORK_MAX)
    cash = await _add_balance(ctx.guild.id, ctx.author.id, earned)
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "UPDATE economy SET last_work=? WHERE guild_id=? AND user_id=?",
            (datetime.now(timezone.utc).isoformat(), ctx.guild.id, ctx.author.id),
        )
        await db.commit()
    await ctx.reply(f"🛠️ You {random.choice(jobs)} and earned **{earned}** bucks! Balance: **{cash:,}**.", mention_author=False)


@bot.command(name="deposit", aliases=["dep"])
@commands.guild_only()
async def deposit_prefix(ctx: commands.Context, amount: str):
    """`,deposit <amount|all>`"""
    cash, bank = await _get_balance(ctx.guild.id, ctx.author.id)
    amt = cash if amount.lower() == "all" else as_int(amount)
    if amt is None or amt <= 0:
        await ctx.reply("❌ Enter a positive number or 'all'.", mention_author=False)
        return
    if amt > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return
    await _set_balance(ctx.guild.id, ctx.author.id, cash - amt, bank + amt)
    await ctx.reply(f"🏦 Deposited **{amt:,}** bucks. Cash: **{cash - amt:,}** · Bank: **{bank + amt:,}**.", mention_author=False)


@bot.command(name="withdraw", aliases=["wd"])
@commands.guild_only()
async def withdraw_prefix(ctx: commands.Context, amount: str):
    """`,withdraw <amount|all>`"""
    cash, bank = await _get_balance(ctx.guild.id, ctx.author.id)
    amt = bank if amount.lower() == "all" else as_int(amount)
    if amt is None or amt <= 0:
        await ctx.reply("❌ Enter a positive number or 'all'.", mention_author=False)
        return
    if amt > bank:
        await ctx.reply(f"❌ You only have **{bank:,}** in the bank.", mention_author=False)
        return
    await _set_balance(ctx.guild.id, ctx.author.id, cash + amt, bank - amt)
    await ctx.reply(f"💸 Withdrew **{amt:,}** bucks. Cash: **{cash + amt:,}** · Bank: **{bank - amt:,}**.", mention_author=False)


@bot.command(name="pay")
@commands.guild_only()
async def pay_prefix(ctx: commands.Context, member: discord.Member, amount: int):
    """`,pay @member <amount>`"""
    if amount <= 0 or member.id == ctx.author.id or member.bot:
        await ctx.reply("❌ Pick someone else and a positive amount.", mention_author=False)
        return
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if amount > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return
    await _add_balance(ctx.guild.id, ctx.author.id, -amount)
    await _add_balance(ctx.guild.id, member.id, amount)
    await ctx.reply(f"💸 Sent **{amount:,}** bucks to {member.mention}.", mention_author=False)


@bot.command(name="coinflip", aliases=["cf"])
@commands.guild_only()
async def coinflip_prefix(ctx: commands.Context, choice: str, bet: int):
    """`,coinflip <heads|tails> <bet>`"""
    choice = choice.lower()
    if choice not in ("heads", "tails"):
        await ctx.reply("❌ Choose `heads` or `tails`.", mention_author=False)
        return
    if bet <= 0:
        await ctx.reply("❌ Bet must be positive.", mention_author=False)
        return
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if bet > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return
    result = random.choice(["heads", "tails"])
    if choice == result:
        await _add_balance(ctx.guild.id, ctx.author.id, bet)
        await ctx.reply(f"🪙 It was **{result}**! You won **{bet:,}** bucks! 🎉", mention_author=False)
    else:
        await _add_balance(ctx.guild.id, ctx.author.id, -bet)
        await ctx.reply(f"🪙 It was **{result}**. You lost **{bet:,}** bucks. 😢", mention_author=False)


@bot.command(name="dice")
@commands.guild_only()
async def dice_prefix(ctx: commands.Context, guess: int, bet: int):
    """`,dice <1-6> <bet>`"""
    if not 1 <= guess <= 6 or bet <= 0:
        await ctx.reply("❌ Pick 1-6 and a positive bet.", mention_author=False)
        return
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if bet > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return
    roll = random.randint(1, 6)
    if roll == guess:
        winnings = bet * 5
        await _add_balance(ctx.guild.id, ctx.author.id, winnings)
        await ctx.reply(f"🎲 Rolled **{roll}** — exact match! You won **{winnings:,}** bucks! 🎉", mention_author=False)
    else:
        await _add_balance(ctx.guild.id, ctx.author.id, -bet)
        await ctx.reply(f"🎲 Rolled **{roll}**. You guessed **{guess}**. Lost **{bet:,}** bucks.", mention_author=False)


@bot.command(name="slots", aliases=["slot"])
@commands.guild_only()
async def slots_prefix(ctx: commands.Context, bet: int):
    """`,slots <bet>`"""
    if bet <= 0:
        await ctx.reply("❌ Bet must be positive.", mention_author=False)
        return
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if bet > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return
    reels = [random.choice(EMOJIS_SLOT) for _ in range(3)]
    if reels[0] == reels[1] == reels[2]:
        mult = 10 if "7" in reels[0] else 5
        winnings = bet * mult
        await _add_balance(ctx.guild.id, ctx.author.id, winnings - bet)
        await ctx.reply(f"🎰 {' | '.join(reels)}\n🎉 Three of a kind! You won **{winnings:,}** bucks (x{mult})!", mention_author=False)
    elif reels[0] == reels[1] or reels[1] == reels[2] or reels[0] == reels[2]:
        winnings = max(1, int(bet * 1.5))
        await _add_balance(ctx.guild.id, ctx.author.id, winnings - bet)
        await ctx.reply(f"🎰 {' | '.join(reels)}\n✨ Pair! You won **{winnings:,}** bucks (x1.5).", mention_author=False)
    else:
        await _add_balance(ctx.guild.id, ctx.author.id, -bet)
        await ctx.reply(f"🎰 {' | '.join(reels)}\n😢 No match. Lost **{bet:,}** bucks.", mention_author=False)


@bot.command(name="scratch")
@commands.guild_only()
async def scratch_prefix(ctx: commands.Context):
    """`,scratch — buy a scratch card for 50 bucks`"""
    cost = 50
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if cash < cost:
        await ctx.reply(f"❌ A scratch card costs {cost} bucks. You have {cash:,}.", mention_author=False)
        return
    await _add_balance(ctx.guild.id, ctx.author.id, -cost)
    roll = random.random()
    if roll < 0.05:
        win = 1000
    elif roll < 0.15:
        win = 250
    elif roll < 0.35:
        win = 100
    elif roll < 0.55:
        win = 50
    else:
        win = 0
    if win:
        await _add_balance(ctx.guild.id, ctx.author.id, win)
        await ctx.reply(f"🎫 You scratched the card... and won **{win:,}** bucks! 🎉", mention_author=False)
    else:
        await ctx.reply("🎫 You scratched the card... nothing. Better luck next time!", mention_author=False)


@bot.command(name="blackjack", aliases=["bj"])
@commands.guild_only()
async def blackjack_prefix(ctx: commands.Context, bet: int):
    """`,blackjack <bet>`"""
    if bet <= 0:
        await ctx.reply("❌ Bet must be positive.", mention_author=False)
        return
    cash, _ = await _get_balance(ctx.guild.id, ctx.author.id)
    if bet > cash:
        await ctx.reply(f"❌ You only have **{cash:,}** cash.", mention_author=False)
        return

    def card():
        return random.randint(1, 11)

    def hand_value(cards):
        v = sum(cards)
        if 1 in cards and v + 10 <= 21:
            v += 10
        return v

    player = [card(), card()]
    dealer = [card(), card()]
    pv = hand_value(player)
    dv = hand_value(dealer)
    while pv < 17:
        player.append(card())
        pv = hand_value(player)
    while dv < 17:
        dealer.append(card())
        dv = hand_value(dealer)
    if pv > 21:
        result = "bust"
    elif dv > 21:
        result = "win"
    elif pv > dv:
        result = "win"
    elif pv < dv:
        result = "lose"
    else:
        result = "push"
    msg = f"🃏 Your hand: {player} ({pv})\n🃏 Dealer: {dealer} ({dv})\n"
    if result == "win":
        await _add_balance(ctx.guild.id, ctx.author.id, bet)
        await ctx.reply(msg + f"\n🎉 You won **{bet:,}** bucks!", mention_author=False)
    elif result == "push":
        await ctx.reply(msg + "\n🤝 Push — bet returned.", mention_author=False)
    else:
        await _add_balance(ctx.guild.id, ctx.author.id, -bet)
        await ctx.reply(msg + f"\n😢 You lost **{bet:,}** bucks.", mention_author=False)


@bot.command(name="leaderboard", aliases=["lb"])
@commands.guild_only()
async def leaderboard_prefix(ctx: commands.Context):
    """`,leaderboard — top earners`"""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT user_id, balance, bank FROM economy WHERE guild_id=? ORDER BY (balance+bank) DESC LIMIT 10",
            (ctx.guild.id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await ctx.reply("No economy data yet. Try `,daily` first!", mention_author=False)
        return
    embed = discord.Embed(title="🏆 Economy Leaderboard", color=0xF1C40F)
    medals = ["🥇", "🥈", "🥉"] + ["•"] * 7
    lines = []
    for i, (uid, bal, bank) in enumerate(rows):
        member = ctx.guild.get_member(uid)
        name = member.display_name if member else f"<@{uid}>"
        net = int(bal or 0) + int(bank or 0)
        lines.append(f"{medals[i]} **{name}** — {net:,} bucks")
    embed.description = "\n".join(lines)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="afk")
@commands.guild_only()
async def afk_prefix(ctx: commands.Context, *, message: str = "AFK"):
    """`,afk [message]`"""
    now_iso = datetime.now(timezone.utc).isoformat()
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO afk (guild_id, user_id, message, since) VALUES (?,?,?,?) "
            "ON CONFLICT(guild_id, user_id) DO UPDATE SET message=excluded.message, since=excluded.since",
            (ctx.guild.id, ctx.author.id, message[:500], now_iso),
        )
        await db.commit()
    await ctx.reply(f"💤 You're now AFK: **{message}**. I'll let people know when they mention you.", mention_author=False)


@bot.command(name="rank")
@commands.guild_only()
async def rank_prefix(ctx: commands.Context, member: discord.Member = None):
    """`,rank [@member]`"""
    member = member or ctx.author
    xp, msgs, level = await _get_level_data(ctx.guild.id, member.id)
    next_xp = _xp_for_level(level + 1)
    cur_level_xp = _xp_for_level(level)
    pct = int(((xp - cur_level_xp) / max(1, next_xp - cur_level_xp)) * 100) if next_xp > cur_level_xp else 0
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT COUNT(*)+1 FROM levels WHERE guild_id=? AND xp > ?",
            (ctx.guild.id, xp),
        )
        rank_n = (await cur.fetchone())[0]
    embed = discord.Embed(title=f"📈 {member.display_name}", color=member.color or 0x2ECC71)
    embed.set_thumbnail(url=member.display_avatar.url)
    embed.add_field(name="Level", value=str(level), inline=True)
    embed.add_field(name="XP", value=f"{xp:,} / {next_xp:,}", inline=True)
    embed.add_field(name="Rank", value=f"#{rank_n}", inline=True)
    embed.add_field(name="Messages", value=str(msgs), inline=True)
    bar_len = 20
    filled = int(pct / 100 * bar_len)
    bar = "█" * filled + "░" * (bar_len - filled)
    embed.add_field(name=f"Progress to L{level+1}", value=f"`{bar}` {pct}%", inline=False)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="levels", aliases=["xplb"])
@commands.guild_only()
async def levels_prefix(ctx: commands.Context):
    """`,levels — top levelers`"""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT user_id, xp FROM levels WHERE guild_id=? ORDER BY xp DESC LIMIT 10",
            (ctx.guild.id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await ctx.reply("No XP yet. Send some messages!", mention_author=False)
        return
    embed = discord.Embed(title="📈 Levels Leaderboard", color=0xF1C40F)
    medals = ["🥇", "🥈", "🥉"] + ["•"] * 7
    lines = []
    for i, (uid, xp) in enumerate(rows):
        m = ctx.guild.get_member(uid)
        name = m.display_name if m else f"<@{uid}>"
        lvl = 0
        x = int(xp or 0)
        while x >= _xp_for_level(lvl + 1):
            lvl += 1
        lines.append(f"{medals[i]} **{name}** — L{lvl} · {x:,} XP")
    embed.description = "\n".join(lines)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="levelconfig")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def levelconfig_prefix(ctx: commands.Context, key: str, value: str):
    """`,levelconfig <enabled|reward> <on|off|@role L<n>>`"""
    settings = config.setdefault(str(ctx.guild.id), {})
    if key.lower() == "enabled":
        settings["leveling_enabled"] = value.lower() in ("on", "true", "yes", "1")
        save_config(config)
        await ctx.reply(f"Leveling: **{'on' if settings.get('leveling_enabled', True) else 'off'}**.", mention_author=False)
        return
    if key.lower() == "reward":
        # expect "@role L5" → store role id at level 5
        m = re.match(r"<@&?(\d+)>\s*L?(\d+)", value)
        if not m:
            await ctx.reply("❌ Use `,levelconfig reward @role L5`.", mention_author=False)
            return
        rid, lvl = int(m.group(1)), int(m.group(2))
        rewards = settings.setdefault("level_roles", {})
        rewards[str(lvl)] = rid
        save_config(config)
        await ctx.reply(f"✅ Level {lvl} reward → <@&{rid}>.", mention_author=False)


@bot.command(name="giveaway")
@commands.guild_only()
@commands.has_permissions(manage_messages=True)
async def giveaway_prefix(ctx: commands.Context, action: str, *, rest: str = ""):
    """`,giveaway start <duration> <winners> <prize>` or `,giveaway end|reroll <message_id>`"""
    action = action.lower()
    if action == "start":
        parts = rest.split(maxsplit=2)
        if len(parts) < 3:
            await ctx.reply("Usage: `,giveaway start <1h|30m|2d> <winners> <prize>`", mention_author=False)
            return
        duration_str, winners_str, prize = parts
        delta = parse_duration(duration_str)
        if delta is None or delta < timedelta(minutes=1) or delta > timedelta(days=14):
            await ctx.reply("❌ Use a duration like `30m`, `1h`, `2d`. Min 1m, max 14d.", mention_author=False)
            return
        try:
            win_n = max(1, int(winners_str))
        except ValueError:
            await ctx.reply("❌ Winners must be a number.", mention_author=False)
            return
        ends_at = datetime.now(timezone.utc) + delta
        embed = discord.Embed(
            title="🎉 Giveaway!",
            description=(f"**Prize:** {prize}\n**Winners:** {win_n}\n"
                        f"**Ends:** <t:{int(ends_at.timestamp())}:R> (<t:{int(ends_at.timestamp())}:f>)\n\n"
                        f"React with {GIVEAWAY_EMOJI} to enter!"),
            color=discord.Color.pink(),
            timestamp=ends_at,
        )
        embed.set_footer(text=f"Hosted by {ctx.author}")
        msg = await ctx.send(embed=embed)
        await msg.add_reaction(GIVEAWAY_EMOJI)
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute(
                "INSERT INTO giveaways (guild_id, channel_id, message_id, prize, host_id, ends_at, winners, ended) "
                "VALUES (?,?,?,?,?,?,?,0)",
                (ctx.guild.id, ctx.channel.id, msg.id, prize, ctx.author.id, ends_at.isoformat(), win_n),
            )
            await db.commit()
        return
    if action in ("end", "reroll"):
        mid_str = rest.strip().split()[0] if rest.strip() else ""
        if not mid_str.isdigit():
            await ctx.reply(f"Usage: `,giveaway {action} <message_id>`", mention_author=False)
            return
        mid = int(mid_str)
        try:
            msg = await ctx.channel.fetch_message(mid)
        except discord.HTTPException:
            await ctx.reply("❌ Couldn't find that message in this channel.", mention_author=False)
            return
        users = []
        for r in msg.reactions:
            if str(r.emoji) == GIVEAWAY_EMOJI:
                async for u in r.users():
                    if not u.bot:
                        users.append(u)
                break
        if not users:
            await ctx.reply("❌ No entrants.", mention_author=False)
            return
        if action == "end":
            winner = random.choice(users)
            try:
                await msg.edit(content=f"🎉 **Giveaway ended!** Winner: {winner.mention}")
            except discord.HTTPException:
                pass
            await ctx.reply(f"🎉 Winner: {winner.mention}!")
            async with aiosqlite.connect(HISTORY_DB) as db:
                await db.execute("UPDATE giveaways SET ended=1 WHERE message_id=?", (mid,))
                await db.commit()
        else:
            winner = random.choice(users)
            await ctx.reply(f"🎉 New winner: {winner.mention}!")
        return
    await ctx.reply("Usage: `,giveaway start|end|reroll ...`", mention_author=False)


@bot.command(name="remind", aliases=["remindme"])
@commands.guild_only()
async def remind_prefix(ctx: commands.Context, time: str, *, message: str):
    """`,remind <time> <message>`"""
    delta = parse_duration(time)
    if delta is None or delta < timedelta(seconds=10) or delta > timedelta(days=30):
        await ctx.reply("❌ Use a time like `10m`, `2h`, `1d`. Min 10s, max 30d.", mention_author=False)
        return
    remind_at = datetime.now(timezone.utc) + delta
    async with aiosqlite.connect(HISTORY_DB) as db:
        await db.execute(
            "INSERT INTO reminders (user_id, guild_id, channel_id, remind_at, message, created_at) "
            "VALUES (?,?,?,?,?,?)",
            (ctx.author.id, ctx.guild.id, ctx.channel.id,
             remind_at.isoformat(), message[:500], datetime.now(timezone.utc).isoformat()),
        )
        await db.commit()
    ts = int(remind_at.timestamp())
    await ctx.reply(f"⏰ Got it — I'll remind you <t:{ts}:R> (<t:{ts}:f>): {message}", mention_author=False)


@bot.command(name="reminders")
async def reminders_prefix(ctx: commands.Context):
    """`,reminders — list yours"""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute(
            "SELECT id, remind_at, message FROM reminders WHERE user_id=? ORDER BY remind_at",
            (ctx.author.id,),
        )
        rows = await cur.fetchall()
    if not rows:
        await ctx.reply("You have no pending reminders.", mention_author=False)
        return
    lines = []
    for rid, when, msg in rows[:15]:
        ts = iso_to_ts(when)
        lines.append(f"`#{rid}` <t:{ts}:R> — {msg[:60]}")
    embed = discord.Embed(title="⏰ Your reminders", description="\n".join(lines), color=0x5865F2)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="cancelreminder", aliases=["delreminder"])
async def cancelreminder_prefix(ctx: commands.Context, reminder_id: int):
    """`,cancelreminder <id>`"""
    async with aiosqlite.connect(HISTORY_DB) as db:
        cur = await db.execute("SELECT user_id FROM reminders WHERE id=?", (reminder_id,))
        row = await cur.fetchone()
        if not row or row[0] != ctx.author.id:
            await ctx.reply("❌ No such reminder of yours.", mention_author=False)
            return
        await db.execute("DELETE FROM reminders WHERE id=?", (reminder_id,))
        await db.commit()
    await ctx.reply(f"🗑️ Cancelled reminder #{reminder_id}.", mention_author=False)


@bot.command(name="bday", aliases=["birthday"])
@commands.guild_only()
async def bday_prefix(ctx: commands.Context, action: str, *, rest: str = ""):
    """`,bday set <MM/DD>` · `,bday list` · `,bday channel #channel`"""
    action = action.lower()
    if action == "set":
        m = re.match(r"(\d{1,2})[/-](\d{1,2})", rest.strip())
        if not m:
            await ctx.reply("Usage: `,bday set MM/DD`", mention_author=False)
            return
        month, day = int(m.group(1)), int(m.group(2))
        try:
            date(2024, month, day)
        except ValueError:
            await ctx.reply("❌ That date doesn't exist.", mention_author=False)
            return
        async with aiosqlite.connect(HISTORY_DB) as db:
            await db.execute(
                "INSERT INTO birthdays (guild_id, user_id, month, day) VALUES (?,?,?,?) "
                "ON CONFLICT(guild_id, user_id) DO UPDATE SET month=excluded.month, day=excluded.day",
                (ctx.guild.id, ctx.author.id, month, day),
            )
            await db.commit()
        await ctx.reply(f"🎂 Saved your birthday: **{month}/{day}**.", mention_author=False)
    elif action == "list":
        async with aiosqlite.connect(HISTORY_DB) as db:
            cur = await db.execute(
                "SELECT user_id, month, day FROM birthdays WHERE guild_id=? ORDER BY month, day",
                (ctx.guild.id,),
            )
            rows = await cur.fetchall()
        if not rows:
            await ctx.reply("No birthdays saved yet.", mention_author=False)
            return
        lines = []
        for uid, m, d in rows:
            member = ctx.guild.get_member(uid)
            name = member.display_name if member else f"<@{uid}>"
            lines.append(f"🎂 {name} — {m}/{d}")
        embed = discord.Embed(title="🎂 Birthdays", description="\n".join(lines), color=0xE91E63)
        await ctx.reply(embed=embed, mention_author=False)
    elif action == "channel":
        if not ctx.author.guild_permissions.manage_guild:
            await ctx.reply("❌ You need Manage Server.", mention_author=False)
            return
        # Allow "#channel" mention or channel ID
        m = re.match(r"<#(\d+)>", rest.strip())
        if m:
            ch_id = int(m.group(1))
            channel = ctx.guild.get_channel(ch_id)
        else:
            try:
                ch_id = int(rest.strip())
                channel = ctx.guild.get_channel(ch_id)
            except ValueError:
                channel = None
        if not isinstance(channel, discord.TextChannel):
            await ctx.reply("❌ Provide a `#channel`.", mention_author=False)
            return
        settings = config.setdefault(str(ctx.guild.id), {})
        settings["birthday_channel"] = channel.id
        save_config(config)
        await ctx.reply(f"🎂 Birthday announcements → {channel.mention}.", mention_author=False)
    else:
        await ctx.reply("Usage: `,bday set|list|channel ...`", mention_author=False)


@bot.command(name="starboard")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def starboard_prefix(ctx: commands.Context, channel: Optional[discord.TextChannel] = None, threshold: Optional[int] = None):
    """`,starboard [#channel] [threshold]`"""
    settings = config.setdefault(str(ctx.guild.id), {})
    if channel is not None:
        settings["starboard_channel"] = channel.id
    if threshold is not None:
        settings["starboard_threshold"] = max(1, threshold)
    save_config(config)
    sb = settings.get("starboard_channel")
    th = settings.get("starboard_threshold", STAR_THRESHOLD)
    await ctx.reply(f"⭐ Starboard: {f'<#{sb}>' if sb else '*not set*'} · threshold: **{th}**", mention_author=False)


@bot.command(name="welcome")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def welcome_prefix(ctx: commands.Context, channel: Optional[discord.TextChannel] = None, *, message: Optional[str] = None):
    """`,welcome [#channel] [message with {user} {server} {name}]`"""
    settings = config.setdefault(str(ctx.guild.id), {})
    if channel is not None:
        settings["welcome_channel"] = channel.id
    if message is not None:
        settings["welcome_message"] = message[:1000]
    save_config(config)
    ch = settings.get("welcome_channel")
    msg = settings.get("welcome_message") or "*not set*"
    await ctx.reply(f"👋 Welcome channel: {f'<#{ch}>' if ch else '*not set*'}\nMessage: {msg}", mention_author=False)


@bot.command(name="autorole")
@commands.guild_only()
@commands.has_permissions(manage_guild=True)
async def autorole_prefix(ctx: commands.Context, role: Optional[discord.Role] = None):
    """`,autorole [@role] — leave empty to clear`"""
    settings = config.setdefault(str(ctx.guild.id), {})
    if role is None:
        settings.pop("autorole", None)
        save_config(config)
        await ctx.reply("🚫 Autorole cleared.", mention_author=False)
        return
    if role.is_default() or role.managed:
        await ctx.reply("❌ Can't use @everyone or a managed role.", mention_author=False)
        return
    if role >= ctx.guild.me.top_role:
        await ctx.reply(f"❌ My top role must be above {role.mention}.", mention_author=False)
        return
    settings["autorole"] = role.id
    save_config(config)
    await ctx.reply(f"✅ New members will get {role.mention}.", mention_author=False)


@bot.command(name="rps")
async def rps_prefix(ctx: commands.Context, choice: str):
    """`,rps <rock|paper|scissors>`"""
    choice = choice.lower()
    if choice not in ("rock", "paper", "scissors"):
        await ctx.reply("❌ Choose `rock`, `paper`, or `scissors`.", mention_author=False)
        return
    bot_choice = random.choice(["rock", "paper", "scissors"])
    emoji_map = {"rock": "🪨", "paper": "📄", "scissors": "✂️"}
    if choice == bot_choice:
        result = "It's a tie!"
    elif (choice == "rock" and bot_choice == "scissors") or \
         (choice == "paper" and bot_choice == "rock") or \
         (choice == "scissors" and bot_choice == "paper"):
        result = "You win! 🎉"
    else:
        result = "You lose! 😢"
    await ctx.reply(f"{emoji_map[choice]} vs {emoji_map[bot_choice]} — **{result}**", mention_author=False)


@bot.command(name="8ball", aliases=["eightball"])
async def eightball_prefix(ctx: commands.Context, *, question: str):
    """`,8ball <question>`"""
    answers = [
        "It is certain.", "It is decidedly so.", "Without a doubt.", "Yes definitely.",
        "You may rely on it.", "As I see it, yes.", "Most likely.", "Outlook good.",
        "Yes.", "Signs point to yes.",
        "Reply hazy, try again.", "Ask again later.", "Better not tell you now.",
        "Cannot predict now.", "Concentrate and ask again.",
        "Don't count on it.", "My reply is no.", "My sources say no.",
        "Outlook not so good.", "Very doubtful.",
    ]
    await ctx.reply(f"🎱 **{question}**\n→ _{random.choice(answers)}_", mention_author=False)


@bot.command(name="roll", aliases=["dice_roll"])
async def roll_prefix(ctx: commands.Context, spec: str = "1d6"):
    """`,roll [NdM]` (e.g. ,roll 2d6)"""
    m = re.fullmatch(r"(\d{1,3})d(\d{1,4})", spec.lower().strip())
    if not m:
        await ctx.reply("❌ Use NdM format, e.g. `2d6`, `1d20`, `4d8`.", mention_author=False)
        return
    n, sides = int(m.group(1)), int(m.group(2))
    if n < 1 or n > 100 or sides < 2 or sides > 1000:
        await ctx.reply("❌ 1-100 dice, 2-1000 sides.", mention_author=False)
        return
    rolls = [random.randint(1, sides) for _ in range(n)]
    total = sum(rolls)
    if n == 1:
        await ctx.reply(f"🎲 d{sides} → **{total}**", mention_author=False)
    else:
        await ctx.reply(f"🎲 {n}d{sides} → {rolls} = **{total}**", mention_author=False)


@bot.command(name="poll")
@commands.guild_only()
async def poll_prefix(ctx: commands.Context, question: str, *options: str):
    """`,poll "Question" option1 option2 [option3 ...]`"""
    if len(options) < 2:
        await ctx.reply("❌ Need at least 2 options. Example: `,poll \"Pizza or Burger?\" Pizza Burger`", mention_author=False)
        return
    if len(options) > 10:
        await ctx.reply("❌ Max 10 options.", mention_author=False)
        return
    letters = ["🇦", "🇧", "🇨", "🇩", "🇪", "🇫", "🇬", "🇭", "🇮", "🇯"]
    desc = "\n".join(f"{letters[i]} {o}" for i, o in enumerate(options))
    embed = discord.Embed(title=f"📊 {question}", description=desc, color=0x5865F2)
    embed.set_footer(text=f"Poll by {ctx.author}")
    msg = await ctx.send(embed=embed)
    for i in range(len(options)):
        try:
            await msg.add_reaction(letters[i])
        except discord.HTTPException:
            pass


# ===========================================================================
# MUSIC PLAYER  (YouTube / search / Spotify → YouTube match)
# Default playlist: DEFAULT_PLAYLIST (Spotify)
# ===========================================================================
class Song:
    __slots__ = ("title", "url", "webpage_url", "duration", "requester", "thumbnail")

    def __init__(
        self,
        title: str,
        url: str,
        webpage_url: str = "",
        duration: Optional[int] = None,
        requester: str = "",
        thumbnail: str = "",
    ):
        self.title = title
        self.url = url  # streamable audio URL
        self.webpage_url = webpage_url or url
        self.duration = duration
        self.requester = requester
        self.thumbnail = thumbnail

    def duration_str(self) -> str:
        if not self.duration:
            return "?:??"
        m, s = divmod(int(self.duration), 60)
        h, m = divmod(m, 60)
        return f"{h}:{m:02d}:{s:02d}" if h else f"{m}:{s:02d}"


class GuildMusic:
    """Per-guild queue + playback state."""

    def __init__(self, guild_id: int):
        self.guild_id = guild_id
        self.queue: list[Song] = []
        self.now: Optional[Song] = None
        self.volume = 0.5
        self.loop_track = False
        self._lock = asyncio.Lock()

    def clear(self):
        self.queue.clear()
        self.now = None


# guild_id → GuildMusic
_music: dict[int, GuildMusic] = {}


def get_music(guild_id: int) -> GuildMusic:
    if guild_id not in _music:
        _music[guild_id] = GuildMusic(guild_id)
    return _music[guild_id]


def _spotify_client():
    if not _HAS_SPOTIPY or not SPOTIFY_CLIENT_ID or not SPOTIFY_CLIENT_SECRET:
        return None
    try:
        return spotipy.Spotify(
            auth_manager=SpotifyClientCredentials(
                client_id=SPOTIFY_CLIENT_ID,
                client_secret=SPOTIFY_CLIENT_SECRET,
            )
        )
    except Exception as e:
        log(f"Spotify client failed: {e}")
        return None


def _spotify_id_from_url(url: str) -> tuple[Optional[str], Optional[str]]:
    """Return (kind, id) where kind is track|playlist|album|None."""
    m = re.search(
        r"open\.spotify\.com/(?:intl-[a-z]+/)?(track|playlist|album)/([A-Za-z0-9]+)",
        url,
    )
    if m:
        return m.group(1), m.group(2)
    return None, None


def _ytdlp_extract(query: str, playlist: bool = False) -> list[dict]:
    opts = YDL_PLAYLIST_OPTS if playlist else YDL_OPTS
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(query, download=False)
    if info is None:
        return []
    if "entries" in info:
        return [e for e in info["entries"] if e]
    return [info]


def _entry_to_song(entry: dict, requester: str = "") -> Optional[Song]:
    if not entry:
        return None
    # Prefer direct stream URL; for flat playlist entries search by title later
    url = entry.get("url") or entry.get("webpage_url")
    title = entry.get("title") or entry.get("id") or "Unknown"
    webpage = entry.get("webpage_url") or entry.get("original_url") or url or ""
    duration = entry.get("duration")
    thumb = ""
    if entry.get("thumbnail"):
        thumb = entry["thumbnail"]
    elif entry.get("thumbnails"):
        thumb = entry["thumbnails"][-1].get("url", "")
    if not url:
        return None
    return Song(
        title=title[:200],
        url=url,
        webpage_url=webpage,
        duration=int(duration) if duration else None,
        requester=requester,
        thumbnail=thumb,
    )


def _resolve_youtube_search(query: str, requester: str = "") -> list[Song]:
    """Search YouTube (or extract URL) and return Song list with stream URLs."""
    # If it looks like a bare search, force ytsearch
    if not re.match(r"https?://", query):
        query = f"ytsearch1:{query}"
    entries = _ytdlp_extract(query, playlist=False)
    songs = []
    for e in entries:
        # Re-extract if we only got flat metadata without a playable URL
        if e.get("ie_key") or (e.get("url") and not e.get("formats") and "youtube.com" in (e.get("url") or "")):
            try:
                full = _ytdlp_extract(e.get("url") or e.get("webpage_url") or e.get("id"), playlist=False)
                if full:
                    e = full[0]
            except Exception:
                pass
        s = _entry_to_song(e, requester)
        if s:
            # Ensure we have a real stream URL
            if not s.url or s.url.startswith("http") is False:
                continue
            songs.append(s)
    return songs


def _spotify_embed_queries(kind: str, sid: str) -> list[str]:
    """No-auth fallback: read track list from the public Spotify embed page.

    Spotify's API now rejects client-credentials access to playlist items (401),
    so scrape open.spotify.com/embed instead (first ~100 tracks).
    """
    import json as _json
    r = requests.get(
        f"https://open.spotify.com/embed/{kind}/{sid}",
        headers={"User-Agent": "Mozilla/5.0"},
        timeout=15,
    )
    r.raise_for_status()
    m = re.search(r'<script id="__NEXT_DATA__" type="application/json">(.*?)</script>', r.text, re.S)
    if not m:
        return []
    entity = _json.loads(m.group(1))["props"]["pageProps"]["state"]["data"]["entity"]
    out = []
    for t in entity.get("trackList") or []:
        title, artist = t.get("title"), (t.get("subtitle") or "").replace("\xa0", " ")
        if title:
            out.append(f"{artist} - {title}" if artist else title)
    return out[:50]


def _resolve_spotify_to_songs(url: str, requester: str = "") -> list[Song]:
    """Map Spotify track/playlist/album → YouTube Songs via search."""
    kind, sid = _spotify_id_from_url(url)
    if not kind or not sid:
        return []

    sp = _spotify_client()
    queries: list[str] = []

    if sp is None:
        # No API keys: best-effort single search on the URL title won't work well.
        # Fall back to searching the Spotify URL text itself is useless — tell caller.
        raise RuntimeError(
            "Spotify playlist/track needs SPOTIFY_CLIENT_ID + SPOTIFY_CLIENT_SECRET "
            "(and `pip install spotipy`). Free app: https://developer.spotify.com/dashboard"
        )

    if kind == "track":
        t = sp.track(sid)
        artists = ", ".join(a["name"] for a in t.get("artists", []))
        queries.append(f"{artists} - {t['name']}")
    elif kind == "playlist":
        try:
            results = sp.playlist_items(sid, additional_types=("track",))
        except Exception as e:
            log(f"Spotify API playlist failed ({e}); using embed fallback")
            results = None
            queries.extend(_spotify_embed_queries("playlist", sid))
        while results:
            for item in results["items"]:
                track = item.get("track") or {}
                if not track or track.get("is_local"):
                    continue
                artists = ", ".join(a["name"] for a in track.get("artists", []))
                name = track.get("name") or ""
                if name:
                    queries.append(f"{artists} - {name}")
            if results.get("next"):
                results = sp.next(results)
            else:
                break
            if len(queries) >= 50:
                break
    elif kind == "album":
        results = sp.album_tracks(sid)
        album = sp.album(sid)
        album_artists = ", ".join(a["name"] for a in album.get("artists", []))
        while results:
            for track in results["items"]:
                artists = ", ".join(a["name"] for a in track.get("artists", [])) or album_artists
                name = track.get("name") or ""
                if name:
                    queries.append(f"{artists} - {name}")
            if results.get("next"):
                results = sp.next(results)
            else:
                break
            if len(queries) >= 50:
                break

    songs: list[Song] = []
    for q in queries:
        try:
            found = _resolve_youtube_search(q, requester)
            if found:
                songs.append(found[0])
        except Exception as e:
            log(f"YT match failed for '{q}': {e}")
    return songs


def resolve_query(query: str, requester: str = "") -> list[Song]:
    """Resolve a user query (URL or text) into playable Song objects."""
    query = query.strip()
    if "open.spotify.com" in query or "spotify:" in query:
        return _resolve_spotify_to_songs(query, requester)

    # YouTube / SoundCloud / direct / search
    is_playlist = any(
        x in query
        for x in ("list=", "playlist", "album", "sets/")
    ) and re.match(r"https?://", query)
    if is_playlist:
        entries = _ytdlp_extract(query, playlist=True)
        songs = []
        for e in entries[:50]:
            # Flat entries need a second extract for stream URL
            page = e.get("url") or e.get("webpage_url")
            if page and not e.get("formats"):
                try:
                    full = _ytdlp_extract(page, playlist=False)
                    if full:
                        e = full[0]
                except Exception:
                    continue
            s = _entry_to_song(e, requester)
            if s:
                songs.append(s)
        return songs

    return _resolve_youtube_search(query, requester)


async def ensure_voice(interaction_or_ctx) -> Optional[discord.VoiceClient]:
    """Join the caller's voice channel if needed. Returns voice client or None."""
    if isinstance(interaction_or_ctx, discord.Interaction):
        guild = interaction_or_ctx.guild
        user = interaction_or_ctx.user
        respond = interaction_or_ctx.followup.send if interaction_or_ctx.response.is_done() else interaction_or_ctx.response.send_message
    else:
        guild = interaction_or_ctx.guild
        user = interaction_or_ctx.author
        respond = interaction_or_ctx.reply

    if not guild:
        return None
    member = guild.get_member(user.id) or user
    if not getattr(member, "voice", None) or member.voice is None or member.voice.channel is None:
        await respond("❌ Join a voice channel first.", ephemeral=True)
        return None

    channel = member.voice.channel
    vc = guild.voice_client
    if vc is None:
        try:
            vc = await channel.connect()
        except Exception as e:
            await respond(f"❌ Couldn't join voice: {e}", ephemeral=True)
            return None
    elif vc.channel != channel:
        await vc.move_to(channel)
    return vc


def _play_next(guild: discord.Guild):
    """After a track ends, play the next one (or loop). Called from the voice thread."""
    gm = get_music(guild.id)
    vc = guild.voice_client
    if vc is None:
        return

    if gm.loop_track and gm.now is not None:
        song = gm.now
    elif gm.queue:
        song = gm.queue.pop(0)
        gm.now = song
    else:
        gm.now = None
        return

    def after_play(error):
        if error:
            log(f"Player error in {guild.name}: {error}")
        # Schedule next track on the bot loop
        fut = asyncio.run_coroutine_threadsafe(_async_after(guild), bot.loop)
        try:
            fut.result(timeout=30)
        except Exception as e:
            log(f"after_play schedule failed: {e}")

    try:
        source = discord.FFmpegPCMAudio(song.url, **FFMPEG_OPTIONS)
        source = discord.PCMVolumeTransformer(source, volume=gm.volume)
        vc.play(source, after=after_play)
    except Exception as e:
        log(f"Failed to start track '{song.title}': {e}")
        # Skip to next
        asyncio.run_coroutine_threadsafe(_async_after(guild), bot.loop)


async def _async_after(guild: discord.Guild):
    await asyncio.sleep(0.3)
    if guild.voice_client and not guild.voice_client.is_playing():
        _play_next(guild)


async def start_or_enqueue(guild: discord.Guild, songs: list[Song], announce_channel=None):
    """Enqueue songs and start playback if idle."""
    if not songs:
        return "❌ Nothing found to play."
    gm = get_music(guild.id)
    gm.queue.extend(songs)
    vc = guild.voice_client
    started = False
    if vc and not vc.is_playing() and not vc.is_paused():
        _play_next(guild)
        started = True
    elif vc is None:
        return "❌ Not connected to voice."

    if len(songs) == 1:
        s = songs[0]
        if started or gm.now is s or (gm.now is None):
            return f"▶ **Now playing:** [{s.title}]({s.webpage_url}) `{s.duration_str()}`"
        pos = len(gm.queue)
        return f"➕ Queued **{s.title}** (`{s.duration_str()}`) — position {pos}"
    return f"➕ Queued **{len(songs)}** tracks from playlist / search."


# --- Slash music commands ---

@bot.tree.command(name="play", description="Play a song/URL/playlist — empty = default Spotify playlist")
@app_commands.guild_only()
@app_commands.describe(query="YouTube/Spotify URL or search text (leave empty for the default playlist)")
async def music_play(interaction: discord.Interaction, query: Optional[str] = None):
    await interaction.response.defer()
    vc = await ensure_voice(interaction)
    if vc is None:
        return
    q = (query or "").strip() or DEFAULT_PLAYLIST
    using_default = not (query or "").strip()
    try:
        songs = await asyncio.to_thread(resolve_query, q, str(interaction.user))
    except RuntimeError as e:
        await interaction.followup.send(f"❌ {e}")
        return
    except Exception as e:
        traceback.print_exc()
        await interaction.followup.send(f"❌ Couldn't resolve that: `{e}`")
        return
    if not songs:
        await interaction.followup.send("❌ No results.")
        return
    msg = await start_or_enqueue(interaction.guild, songs)
    prefix = "🎵 **Default playlist loaded.**\n" if using_default else ""
    await interaction.followup.send(prefix + msg)


@bot.tree.command(name="skip", description="Skip the current track")
@app_commands.guild_only()
async def music_skip(interaction: discord.Interaction):
    vc = interaction.guild.voice_client if interaction.guild else None
    if not vc or not (vc.is_playing() or vc.is_paused()):
        await interaction.response.send_message("❌ Nothing is playing.", ephemeral=True)
        return
    gm = get_music(interaction.guild.id)
    gm.loop_track = False
    vc.stop()  # triggers after → next
    await interaction.response.send_message("⏭ Skipped.")


@bot.tree.command(name="pause", description="Pause playback")
@app_commands.guild_only()
async def music_pause(interaction: discord.Interaction):
    vc = interaction.guild.voice_client if interaction.guild else None
    if not vc or not vc.is_playing():
        await interaction.response.send_message("❌ Nothing is playing.", ephemeral=True)
        return
    vc.pause()
    await interaction.response.send_message("⏸ Paused.")


@bot.tree.command(name="resume", description="Resume playback")
@app_commands.guild_only()
async def music_resume(interaction: discord.Interaction):
    vc = interaction.guild.voice_client if interaction.guild else None
    if not vc or not vc.is_paused():
        await interaction.response.send_message("❌ Nothing is paused.", ephemeral=True)
        return
    vc.resume()
    await interaction.response.send_message("▶ Resumed.")


@bot.tree.command(name="stop", description="Stop and clear the queue")
@app_commands.guild_only()
async def music_stop(interaction: discord.Interaction):
    if not interaction.guild:
        return
    gm = get_music(interaction.guild.id)
    gm.clear()
    vc = interaction.guild.voice_client
    if vc:
        vc.stop()
        await vc.disconnect()
    await interaction.response.send_message("⏹ Stopped and left the channel.")


@bot.tree.command(name="queue", description="Show the music queue")
@app_commands.guild_only()
async def music_queue(interaction: discord.Interaction):
    gm = get_music(interaction.guild.id)
    lines = []
    if gm.now:
        lines.append(f"**Now:** [{gm.now.title}]({gm.now.webpage_url}) `{gm.now.duration_str()}`")
    for i, s in enumerate(gm.queue[:15], 1):
        lines.append(f"`{i}.` [{s.title}]({s.webpage_url}) `{s.duration_str()}`")
    if len(gm.queue) > 15:
        lines.append(f"…and {len(gm.queue) - 15} more")
    if not lines:
        await interaction.response.send_message("Queue is empty. Use `/play` (empty = default playlist).")
        return
    embed = discord.Embed(
        title="🎵 Queue",
        description="\n".join(lines),
        color=0x1DB954,
    )
    embed.set_footer(text=f"Volume {int(gm.volume * 100)}% · Loop track: {'on' if gm.loop_track else 'off'}")
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="nowplaying", description="Show the current track")
@app_commands.guild_only()
async def music_np(interaction: discord.Interaction):
    gm = get_music(interaction.guild.id)
    if not gm.now:
        await interaction.response.send_message("Nothing is playing.", ephemeral=True)
        return
    s = gm.now
    embed = discord.Embed(
        title="🎵 Now playing",
        description=f"[{s.title}]({s.webpage_url})",
        color=0x1DB954,
    )
    embed.add_field(name="Duration", value=s.duration_str(), inline=True)
    embed.add_field(name="Requested by", value=s.requester or "—", inline=True)
    if s.thumbnail:
        embed.set_thumbnail(url=s.thumbnail)
    await interaction.response.send_message(embed=embed)


@bot.tree.command(name="volume", description="Set playback volume (0–150)")
@app_commands.guild_only()
@app_commands.describe(level="Volume percent (0–150)")
async def music_volume(interaction: discord.Interaction, level: app_commands.Range[int, 0, 150]):
    gm = get_music(interaction.guild.id)
    gm.volume = level / 100.0
    vc = interaction.guild.voice_client if interaction.guild else None
    if vc and vc.source and isinstance(vc.source, discord.PCMVolumeTransformer):
        vc.source.volume = gm.volume
    await interaction.response.send_message(f"🔊 Volume set to **{level}%**.")


@bot.tree.command(name="loop", description="Toggle looping the current track")
@app_commands.guild_only()
async def music_loop(interaction: discord.Interaction):
    gm = get_music(interaction.guild.id)
    gm.loop_track = not gm.loop_track
    await interaction.response.send_message(
        f"🔁 Track loop **{'on' if gm.loop_track else 'off'}**."
    )


@bot.tree.command(name="leave", description="Disconnect the bot from voice")
@app_commands.guild_only()
async def music_leave(interaction: discord.Interaction):
    if not interaction.guild or not interaction.guild.voice_client:
        await interaction.response.send_message("I'm not in a voice channel.", ephemeral=True)
        return
    get_music(interaction.guild.id).clear()
    await interaction.guild.voice_client.disconnect()
    await interaction.response.send_message("👋 Left the voice channel.")


# Prefix music commands
@bot.command(name="play", aliases=["p"])
@commands.guild_only()
async def play_prefix(ctx: commands.Context, *, query: Optional[str] = None):
    vc = await ensure_voice(ctx)
    if vc is None:
        return
    q = (query or "").strip() or DEFAULT_PLAYLIST
    using_default = not (query or "").strip()
    status = await ctx.reply("🔎 Looking that up…", mention_author=False)
    try:
        songs = await asyncio.to_thread(resolve_query, q, str(ctx.author))
    except RuntimeError as e:
        await status.edit(content=f"❌ {e}")
        return
    except Exception as e:
        traceback.print_exc()
        await status.edit(content=f"❌ Couldn't resolve that: `{e}`")
        return
    if not songs:
        await status.edit(content="❌ No results.")
        return
    msg = await start_or_enqueue(ctx.guild, songs)
    prefix = "🎵 **Default playlist loaded.**\n" if using_default else ""
    await status.edit(content=prefix + msg)


@bot.command(name="skip", aliases=["fs", "next"])
@commands.guild_only()
async def skip_prefix(ctx: commands.Context):
    vc = ctx.guild.voice_client
    if not vc or not (vc.is_playing() or vc.is_paused()):
        await ctx.reply("❌ Nothing is playing.", mention_author=False)
        return
    get_music(ctx.guild.id).loop_track = False
    vc.stop()
    await ctx.reply("⏭ Skipped.", mention_author=False)


@bot.command(name="pause")
@commands.guild_only()
async def pause_prefix(ctx: commands.Context):
    vc = ctx.guild.voice_client
    if not vc or not vc.is_playing():
        await ctx.reply("❌ Nothing is playing.", mention_author=False)
        return
    vc.pause()
    await ctx.reply("⏸ Paused.", mention_author=False)


@bot.command(name="resume")
@commands.guild_only()
async def resume_prefix(ctx: commands.Context):
    vc = ctx.guild.voice_client
    if not vc or not vc.is_paused():
        await ctx.reply("❌ Nothing is paused.", mention_author=False)
        return
    vc.resume()
    await ctx.reply("▶ Resumed.", mention_author=False)


@bot.command(name="stop")
@commands.guild_only()
async def stop_prefix(ctx: commands.Context):
    get_music(ctx.guild.id).clear()
    if ctx.guild.voice_client:
        ctx.guild.voice_client.stop()
        await ctx.guild.voice_client.disconnect()
    await ctx.reply("⏹ Stopped.", mention_author=False)


@bot.command(name="queue", aliases=["q"])
@commands.guild_only()
async def queue_prefix(ctx: commands.Context):
    gm = get_music(ctx.guild.id)
    lines = []
    if gm.now:
        lines.append(f"**Now:** {gm.now.title} `{gm.now.duration_str()}`")
    for i, s in enumerate(gm.queue[:15], 1):
        lines.append(f"`{i}.` {s.title} `{s.duration_str()}`")
    if not lines:
        await ctx.reply("Queue empty. `.play` with no args loads the default playlist.", mention_author=False)
        return
    await ctx.reply("\n".join(lines), mention_author=False)


@bot.command(name="np", aliases=["nowplaying"])
@commands.guild_only()
async def np_prefix(ctx: commands.Context):
    gm = get_music(ctx.guild.id)
    if not gm.now:
        await ctx.reply("Nothing is playing.", mention_author=False)
        return
    s = gm.now
    embed = discord.Embed(
        title="🎵 Now playing",
        description=f"[{s.title}]({s.webpage_url})",
        color=0x1DB954,
    )
    embed.add_field(name="Duration", value=s.duration_str(), inline=True)
    embed.add_field(name="Requested by", value=s.requester or "—", inline=True)
    if s.thumbnail:
        embed.set_thumbnail(url=s.thumbnail)
    await ctx.reply(embed=embed, mention_author=False)


@bot.command(name="volume", aliases=["vol"])
@commands.guild_only()
async def volume_prefix(ctx: commands.Context, level: int):
    """`,volume <0-150>`"""
    if not 0 <= level <= 150:
        await ctx.reply("❌ Use 0–150.", mention_author=False)
        return
    gm = get_music(ctx.guild.id)
    gm.volume = level / 100.0
    vc = ctx.guild.voice_client
    if vc and vc.source and isinstance(vc.source, discord.PCMVolumeTransformer):
        vc.source.volume = gm.volume
    await ctx.reply(f"🔊 Volume set to **{level}%**.", mention_author=False)


@bot.command(name="loop", aliases=["repeat"])
@commands.guild_only()
async def loop_prefix(ctx: commands.Context):
    """`,loop — toggle track loop"""
    gm = get_music(ctx.guild.id)
    gm.loop_track = not gm.loop_track
    await ctx.reply(f"🔁 Track loop **{'on' if gm.loop_track else 'off'}**.", mention_author=False)


@bot.command(name="leave", aliases=["dc", "disconnect"])
@commands.guild_only()
async def leave_prefix(ctx: commands.Context):
    if not ctx.guild.voice_client:
        await ctx.reply("Not in voice.", mention_author=False)
        return
    get_music(ctx.guild.id).clear()
    await ctx.guild.voice_client.disconnect()
    await ctx.reply("👋 Left.", mention_author=False)


# ===========================================================================
# Console commands (type while the bot is online)
# ===========================================================================
def _console_help():
    print(
        """
   Console commands (type while the bot is online):
     say <channel_id> <message>   — post a message in that channel
     dm  <user_id> <message>      — DM a user (they must share a server)
     guilds                       — list servers the bot is in
     help                         — show this list
     quit / exit                  — take the bot offline and exit
"""
    )


async def _console_say(channel_id: int, message: str):
    channel = bot.get_channel(channel_id)
    if channel is None:
        try:
            channel = await bot.fetch_channel(channel_id)
        except (discord.NotFound, discord.Forbidden):
            print("   [!] No channel with that ID that the bot can see.")
            return
    try:
        await channel.send(message)
        name = getattr(channel, "name", str(channel_id))
        print(f"   ✔ sent to #{name}")
    except discord.Forbidden:
        print("   [!] 403 — bot needs View Channel + Send Messages there.")
    except Exception as e:
        print(f"   [!] Couldn't send: {e}")


async def _console_dm(user_id: int, message: str):
    user = bot.get_user(user_id)
    if user is None:
        try:
            user = await bot.fetch_user(user_id)
        except (discord.NotFound, discord.Forbidden):
            print("   [!] No user with that ID.")
            return
    try:
        await user.send(message)
        print(f"   ✔ DM sent to {user}")
    except discord.Forbidden:
        print("   [!] 403 — they don't share a server with the bot, or DMs are closed.")
    except Exception as e:
        print(f"   [!] Couldn't send: {e}")


def _console_loop():
    """Blocking input loop that runs on a background thread."""
    import time

    # Wait until the bot is ready
    while not bot.is_ready():
        if bot.is_closed():
            return
        time.sleep(0.3)

    print("\n   Console is ready. Type 'help' for commands, or 'quit' to exit.")
    _console_help()

    while not bot.is_closed():
        try:
            raw = input("console> ").strip()
        except (EOFError, KeyboardInterrupt):
            print()
            break
        if not raw:
            continue

        parts = raw.split(None, 2)
        cmd = parts[0].lower()

        if cmd in ("quit", "exit", "q"):
            print("   Taking the bot offline…")
            asyncio.run_coroutine_threadsafe(bot.close(), bot.loop)
            break

        if cmd in ("help", "?"):
            _console_help()
            continue

        if cmd == "guilds":
            if not bot.guilds:
                print("   (bot is in no servers yet)")
            else:
                for g in bot.guilds:
                    print(f"   {g.name}  (ID {g.id})  ~{g.member_count or '?'} members")
            continue

        if cmd == "say":
            if len(parts) < 3:
                print("   Usage: say <channel_id> <message>")
                continue
            cid = as_int(parts[1])
            if cid is None:
                print("   [!] Channel ID must be a number (Developer Mode → right-click channel → Copy Channel ID).")
                continue
            msg = parts[2]
            fut = asyncio.run_coroutine_threadsafe(_console_say(cid, msg), bot.loop)
            try:
                fut.result(timeout=15)
            except Exception as e:
                print(f"   [!] {e}")
            continue

        if cmd == "dm":
            if len(parts) < 3:
                print("   Usage: dm <user_id> <message>")
                continue
            uid = as_int(parts[1])
            if uid is None:
                print("   [!] User ID must be a number (Developer Mode → right-click user → Copy User ID).")
                continue
            msg = parts[2]
            fut = asyncio.run_coroutine_threadsafe(_console_dm(uid, msg), bot.loop)
            try:
                fut.result(timeout=15)
            except Exception as e:
                print(f"   [!] {e}")
            continue

        print(f"   [!] Unknown command '{cmd}'. Type 'help' for the list.")


# ===========================================================================
# WEB DASHBOARD  (aiohttp — http://HOST:PORT/)
# ===========================================================================
_DASH_CSS = """
:root {
  --bg: #0f1117; --panel: #171b24; --border: #2a3140; --text: #e8eaed;
  --muted: #9aa0a6; --accent: #5865F2; --green: #3ba55d; --red: #ed4245;
  --spotify: #1DB954; --warn: #faa61a;
}
* { box-sizing: border-box; }
body {
  margin: 0; font-family: ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, sans-serif;
  background: var(--bg); color: var(--text); line-height: 1.5;
}
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
.wrap { max-width: 1100px; margin: 0 auto; padding: 24px 20px 60px; }
header {
  display: flex; flex-wrap: wrap; align-items: center; justify-content: space-between;
  gap: 12px; margin-bottom: 28px; padding-bottom: 16px; border-bottom: 1px solid var(--border);
}
header h1 { margin: 0; font-size: 1.35rem; font-weight: 700; letter-spacing: -0.02em; }
header h1 span { color: var(--accent); }
.nav { display: flex; flex-wrap: wrap; gap: 8px; }
.nav a {
  padding: 6px 12px; border-radius: 8px; background: var(--panel);
  border: 1px solid var(--border); color: var(--text); font-size: 0.9rem;
}
.nav a:hover, .nav a.active { background: var(--accent); border-color: var(--accent); text-decoration: none; }
.grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 14px; margin-bottom: 24px; }
.card {
  background: var(--panel); border: 1px solid var(--border); border-radius: 12px;
  padding: 16px 18px;
}
.card h3 { margin: 0 0 6px; font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.06em; color: var(--muted); font-weight: 600; }
.card .val { font-size: 1.6rem; font-weight: 700; }
.card .sub { color: var(--muted); font-size: 0.85rem; margin-top: 4px; }
.badge {
  display: inline-block; padding: 2px 8px; border-radius: 999px; font-size: 0.75rem; font-weight: 600;
}
.badge.on { background: rgba(59,165,93,.2); color: var(--green); }
.badge.off { background: rgba(237,66,69,.2); color: var(--red); }
table { width: 100%; border-collapse: collapse; font-size: 0.92rem; }
th, td { text-align: left; padding: 10px 12px; border-bottom: 1px solid var(--border); }
th { color: var(--muted); font-weight: 600; font-size: 0.75rem; text-transform: uppercase; letter-spacing: 0.04em; }
tr:hover td { background: rgba(255,255,255,.02); }
.btn {
  display: inline-block; padding: 8px 14px; border-radius: 8px; border: none;
  background: var(--accent); color: #fff; font-weight: 600; cursor: pointer; font-size: 0.9rem;
}
.btn:hover { filter: brightness(1.1); }
.btn.danger { background: var(--red); }
.btn.spotify { background: var(--spotify); color: #000; }
.btn.ghost { background: transparent; border: 1px solid var(--border); color: var(--text); }
input, select, textarea {
  width: 100%; padding: 10px 12px; border-radius: 8px; border: 1px solid var(--border);
  background: var(--bg); color: var(--text); font-size: 0.95rem; margin-bottom: 10px;
}
label { display: block; font-size: 0.8rem; color: var(--muted); margin-bottom: 4px; }
.form-row { margin-bottom: 12px; }
.flash { padding: 12px 14px; border-radius: 8px; margin-bottom: 16px; background: rgba(88,101,242,.15); border: 1px solid var(--accent); }
.muted { color: var(--muted); }
.mono { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: 0.85rem; }
footer { margin-top: 40px; color: var(--muted); font-size: 0.8rem; text-align: center; }
.login-box { max-width: 360px; margin: 80px auto; }
"""

_DASH_LAYOUT = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title} · Bot Dashboard</title>
<style>{css}</style>
</head>
<body>
<div class="wrap">
<header>
  <h1><span>●</span> Merged Bot Dashboard</h1>
  <nav class="nav">
    <a href="/" class="{a_home}">Overview</a>
    <a href="/guilds" class="{a_guilds}">Servers</a>
    <a href="/music" class="{a_music}">Music</a>
    <a href="/config" class="{a_config}">Config</a>
    <a href="/tools" class="{a_tools}">Tools</a>
  </nav>
</header>
{flash}
{body}
<footer>Bound to {host}:{port} · Prefix <span class="mono">{prefix}</span> · Default playlist is the configured Spotify list</footer>
</div>
</body>
</html>
"""


def _dash_auth_ok(request: "aiohttp.web.Request") -> bool:
    if not DASHBOARD_PASSWORD:
        return True
    cookie = request.cookies.get("dash_auth")
    if cookie == DASHBOARD_PASSWORD:
        return True
    auth = request.headers.get("Authorization", "")
    if auth.startswith("Bearer ") and auth[7:] == DASHBOARD_PASSWORD:
        return True
    return False


def _dash_html(title: str, body: str, active: str = "home", flash: str = "") -> str:
    flash_html = f'<div class="flash">{flash}</div>' if flash else ""
    return _DASH_LAYOUT.format(
        title=title,
        css=_DASH_CSS,
        body=body,
        flash=flash_html,
        host=DASHBOARD_HOST,
        port=DASHBOARD_PORT,
        prefix=PREFIX,
        a_home="active" if active == "home" else "",
        a_guilds="active" if active == "guilds" else "",
        a_music="active" if active == "music" else "",
        a_config="active" if active == "config" else "",
        a_tools="active" if active == "tools" else "",
    )


def _uptime_str() -> str:
    if _bot_started_at is None:
        return "—"
    delta = datetime.now(timezone.utc) - _bot_started_at
    secs = int(delta.total_seconds())
    h, rem = divmod(secs, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{h}h {m}m"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


async def _dash_login(request: "aiohttp.web.Request"):
    from aiohttp import web

    if request.method == "POST":
        data = await request.post()
        pw = (data.get("password") or "").strip()
        if pw == DASHBOARD_PASSWORD:
            resp = web.HTTPFound("/")
            resp.set_cookie("dash_auth", DASHBOARD_PASSWORD, max_age=86400 * 7, httponly=True)
            return resp
        body = """
        <div class="login-box card">
          <h2>Login</h2>
          <p class="muted">Wrong password.</p>
          <form method="post">
            <label>Password</label>
            <input type="password" name="password" autofocus>
            <button class="btn" type="submit">Sign in</button>
          </form>
        </div>"""
        return web.Response(text=_dash_html("Login", body), content_type="text/html")

    body = """
    <div class="login-box card">
      <h2>Dashboard login</h2>
      <p class="muted">Set via <span class="mono">DASHBOARD_PASSWORD</span>.</p>
      <form method="post">
        <label>Password</label>
        <input type="password" name="password" autofocus>
        <button class="btn" type="submit">Sign in</button>
      </form>
    </div>"""
    return web.Response(text=_dash_html("Login", body), content_type="text/html")


async def _dash_index(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")

    ready = bot.is_ready() and bot.user is not None
    name = str(bot.user) if ready else "Connecting…"
    uid = bot.user.id if ready else "—"
    latency = f"{round(bot.latency * 1000)} ms" if ready else "—"
    guilds = len(bot.guilds) if ready else 0
    members = sum(g.member_count or 0 for g in bot.guilds) if ready else 0
    voice_n = sum(1 for g in bot.guilds if g.voice_client) if ready else 0
    queued = sum(len(get_music(g.id).queue) + (1 if get_music(g.id).now else 0) for g in bot.guilds) if ready else 0
    warn_total = 0
    for gid, gcfg in config.items():
        warns = gcfg.get("warnings") or {}
        for lst in warns.values():
            warn_total += len(lst)

    body = f"""
    <div class="grid">
      <div class="card"><h3>Status</h3>
        <div class="val"><span class="badge {'on' if ready else 'off'}">{'Online' if ready else 'Offline'}</span></div>
        <div class="sub">{name}</div></div>
      <div class="card"><h3>Latency</h3><div class="val">{latency}</div><div class="sub">gateway heartbeat</div></div>
      <div class="card"><h3>Uptime</h3><div class="val">{_uptime_str()}</div><div class="sub">since last start</div></div>
      <div class="card"><h3>Servers</h3><div class="val">{guilds}</div><div class="sub">~{members:,} members</div></div>
      <div class="card"><h3>Voice</h3><div class="val">{voice_n}</div><div class="sub">active connections</div></div>
      <div class="card"><h3>Music queue</h3><div class="val">{queued}</div><div class="sub">tracks across guilds</div></div>
      <div class="card"><h3>Warnings stored</h3><div class="val">{warn_total}</div><div class="sub">all guilds</div></div>
      <div class="card"><h3>Bot ID</h3><div class="val" style="font-size:1rem" class="mono">{uid}</div>
        <div class="sub">prefix <span class="mono">{PREFIX}</span></div></div>
    </div>
    <div class="card">
      <h3>Default music playlist</h3>
      <p><a href="{DEFAULT_PLAYLIST}" target="_blank" rel="noopener">{DEFAULT_PLAYLIST}</a></p>
      <p class="muted">Empty <span class="mono">/play</span> or <span class="mono">{PREFIX}play</span> loads this Spotify list (needs Spotify API keys for full resolve).</p>
    </div>
    """
    return web.Response(text=_dash_html("Overview", body, "home"), content_type="text/html")


async def _dash_guilds(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")

    rows = []
    for g in sorted(bot.guilds, key=lambda x: (x.name or "").lower()):
        gm = get_music(g.id)
        now = gm.now.title[:40] if gm.now else "—"
        vc = "Yes" if g.voice_client else "No"
        gcfg = config.get(str(g.id), {})
        warns = sum(len(v) for v in (gcfg.get("warnings") or {}).values())
        rows.append(
            f"<tr><td><strong>{_html_esc(g.name)}</strong><br><span class='mono muted'>{g.id}</span></td>"
            f"<td>{g.member_count or '?'}</td><td>{len(g.channels)}</td><td>{len(g.roles)}</td>"
            f"<td>{vc}</td><td>{_html_esc(now)}</td><td>{len(gm.queue)}</td><td>{warns}</td></tr>"
        )
    table = (
        "<table><thead><tr><th>Server</th><th>Members</th><th>Channels</th><th>Roles</th>"
        "<th>Voice</th><th>Now playing</th><th>Queue</th><th>Warns</th></tr></thead>"
        f"<tbody>{''.join(rows) or '<tr><td colspan=8 class=muted>No servers yet.</td></tr>'}</tbody></table>"
    )
    body = f'<div class="card">{table}</div>'
    return web.Response(text=_dash_html("Servers", body, "guilds"), content_type="text/html")


async def _dash_music(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")

    blocks = []
    for g in bot.guilds:
        gm = get_music(g.id)
        if not gm.now and not gm.queue and not g.voice_client:
            continue
        now = f"<strong>{_html_esc(gm.now.title)}</strong> <span class='muted'>{gm.now.duration_str()}</span>" if gm.now else "—"
        qlines = "".join(
            f"<li>{_html_esc(s.title)} <span class='muted'>{s.duration_str()}</span></li>"
            for s in gm.queue[:20]
        ) or "<li class='muted'>Empty</li>"
        blocks.append(
            f"""<div class="card" style="margin-bottom:14px">
            <h3>{_html_esc(g.name)}</h3>
            <p>Now: {now}</p>
            <p class="muted">Volume {int(gm.volume*100)}% · Loop {'on' if gm.loop_track else 'off'} ·
            Voice: {'connected' if g.voice_client else 'not connected'}</p>
            <ol>{qlines}</ol>
            <form method="post" action="/music/skip" style="display:inline">
              <input type="hidden" name="guild_id" value="{g.id}">
              <button class="btn ghost" type="submit">Skip</button>
            </form>
            <form method="post" action="/music/stop" style="display:inline">
              <input type="hidden" name="guild_id" value="{g.id}">
              <button class="btn danger" type="submit">Stop & leave</button>
            </form>
            </div>"""
        )
    if not blocks:
        blocks.append('<div class="card"><p class="muted">No active music sessions. Use /play in Discord (empty query = default playlist).</p></div>')

    body = f"""
    <div class="card" style="margin-bottom:16px">
      <h3>Play default playlist in a server</h3>
      <form method="post" action="/music/play_default">
        <label>Server</label>
        <select name="guild_id">
          {''.join(f'<option value="{g.id}">{_html_esc(g.name)}</option>' for g in bot.guilds)}
        </select>
        <p class="muted">Bot must already be in a voice channel in that server (join via Discord first).</p>
        <button class="btn spotify" type="submit">▶ Load default Spotify playlist</button>
      </form>
    </div>
    {''.join(blocks)}
    """
    return web.Response(text=_dash_html("Music", body, "music"), content_type="text/html")


async def _dash_music_skip(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    gid = as_int(data.get("guild_id"))
    guild = bot.get_guild(gid) if gid else None
    if guild and guild.voice_client:
        get_music(guild.id).loop_track = False
        guild.voice_client.stop()
    raise web.HTTPFound("/music")


async def _dash_music_stop(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    gid = as_int(data.get("guild_id"))
    guild = bot.get_guild(gid) if gid else None
    if guild:
        get_music(guild.id).clear()
        if guild.voice_client:
            guild.voice_client.stop()
            await guild.voice_client.disconnect()
    raise web.HTTPFound("/music")


async def _dash_music_play_default(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    gid = as_int(data.get("guild_id"))
    guild = bot.get_guild(gid) if gid else None
    flash = "Server not found."
    if guild and guild.voice_client:
        try:
            songs = await asyncio.to_thread(resolve_query, DEFAULT_PLAYLIST, "dashboard")
            msg = await start_or_enqueue(guild, songs)
            flash = msg
        except Exception as e:
            flash = f"Failed: {e}"
    elif guild:
        flash = "Bot is not in a voice channel there — join one in Discord first."
    # Re-render music page with flash
    request["flash"] = flash
    body_resp = await _dash_music(request)
    # inject flash by re-building — simpler redirect with query
    raise web.HTTPFound("/music")


async def _dash_config(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")

    rows = []
    for gid, settings in sorted(config.items(), key=lambda x: x[0]):
        guild = bot.get_guild(as_int(gid) or 0)
        name = guild.name if guild else f"ID {gid}"
        apk = settings.get("apk_channel", "—")
        ann = settings.get("announce_channel", "—")
        mod = settings.get("modlog_channel", "—")
        ping = settings.get("ping_role", "—")
        warn_n = sum(len(v) for v in (settings.get("warnings") or {}).values())
        rows.append(
            f"<tr><td>{_html_esc(name)}<br><span class='mono muted'>{gid}</span></td>"
            f"<td class='mono'>{apk}</td><td class='mono'>{ann}</td>"
            f"<td class='mono'>{mod}</td><td class='mono'>{ping}</td><td>{warn_n}</td></tr>"
        )

    body = f"""
    <div class="card" style="margin-bottom:16px">
      <h3>Runtime</h3>
      <p>Dashboard bind: <span class="mono">{DASHBOARD_HOST}:{DASHBOARD_PORT}</span></p>
      <p>Password protection: <span class="badge {'on' if DASHBOARD_PASSWORD else 'off'}">{'On' if DASHBOARD_PASSWORD else 'Off'}</span></p>
      <p>Spotify API: <span class="badge {'on' if (SPOTIFY_CLIENT_ID and SPOTIFY_CLIENT_SECRET) else 'off'}">{
        'Configured' if (SPOTIFY_CLIENT_ID and SPOTIFY_CLIENT_SECRET) else 'Missing'}</span></p>
      <p class="muted">Guild settings are edited in Discord with <span class="mono">/set</span>.</p>
    </div>
    <div class="card">
      <h3>Per-server config (config.json)</h3>
      <table>
        <thead><tr><th>Server</th><th>APK forum</th><th>Announce</th><th>Mod log</th><th>Ping role</th><th>Warns</th></tr></thead>
        <tbody>{''.join(rows) or '<tr><td colspan=6 class=muted>No config yet.</td></tr>'}</tbody>
      </table>
    </div>
    """
    return web.Response(text=_dash_html("Config", body, "config"), content_type="text/html")


async def _dash_tools(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")

    msg = request.query.get("msg", "")
    flash = f'<div class="card" style="margin-bottom:14px">{_html_esc(msg)}</div>' if msg else ""
    body = flash + """
    <div class="grid">
      <div class="card">
        <h3>Join VC</h3>
        <form method="post" action="/tools/joinvc">
          <label>Voice channel ID</label>
          <input name="channel_id" placeholder="123456789012345678" required>
          <button class="btn" type="submit">Join</button>
        </form>
        <form method="post" action="/tools/leavevc" style="margin-top:8px">
          <label>Leave VC in server (channel ID of the VC to leave)</label>
          <input name="channel_id" placeholder="123456789012345678" required>
          <button class="btn danger" type="submit">Leave</button>
        </form>
      </div>
      <div class="card">
        <h3>Say (post as bot)</h3>
        <form method="post" action="/tools/say">
          <label>Channel ID</label>
          <input name="channel_id" placeholder="123456789012345678" required>
          <label>Message</label>
          <textarea name="message" rows="3" required></textarea>
          <button class="btn" type="submit">Send</button>
        </form>
      </div>
      <div class="card">
        <h3>DM a user</h3>
        <form method="post" action="/tools/dm">
          <label>User ID</label>
          <input name="user_id" placeholder="123456789012345678" required>
          <label>Message</label>
          <textarea name="message" rows="3" required></textarea>
          <button class="btn" type="submit">Send DM</button>
        </form>
      </div>
    </div>
    <div class="card" style="margin-top:14px">
      <h3>Command cheat sheet</h3>
      <p class="muted">Prefix: <span class="mono">,</span>  ·  all slash commands also have a <span class="mono">,</span> prefix version</p>
      <p class="muted">Music: <span class="mono">,play</span> (empty = default playlist) ·
      <span class="mono">,skip ,pause ,queue ,np ,volume ,loop ,leave</span></p>
      <p class="muted">Mod: <span class="mono">,ban ,kick ,timeout ,mute ,warn ,purge ,slowmode</span> ·
      <span class="mono">,lock ,unlock ,hide ,unhide ,nuke ,lockdown ,unlockdown ,softban ,voicekick ,move ,nick ,addrole ,removerole ,roleinfo ,channelinfo</span></p>
      <p class="muted">Economy: <span class="mono">,balance ,daily ,work ,pay ,deposit ,withdraw</span> ·
      Gamble: <span class="mono">,coinflip ,dice ,slots ,scratch ,blackjack ,leaderboard</span></p>
      <p class="muted">Levels: <span class="mono">,rank ,levels ,levelconfig</span> ·
      Fun: <span class="mono">,rps ,8ball ,roll ,poll ,afk</span></p>
      <p class="muted">Engagement: <span class="mono">,giveaway ,remind ,reminders ,bday ,starboard ,welcome ,autorole</span></p>
      <p class="muted">TikTok: <span class="mono">,lookup ,reversevid ,search ,uservideos ,download ,sound ,history</span></p>
      <p class="muted">Templates: <span class="mono">,pull ,apply</span> ·
      Misc: <span class="mono">,snipe ,clearsnipe ,ping ,userinfo ,serverinfo ,help</span></p>
      <p class="muted">Console: <span class="mono">say</span> · <span class="mono">dm</span> · <span class="mono">guilds</span> · <span class="mono">quit</span></p>
    </div>
    """
    return web.Response(text=_dash_html("Tools", body, "tools"), content_type="text/html")


async def _dash_tools_say(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    cid = as_int(data.get("channel_id"))
    msg = (data.get("message") or "").strip()
    if cid and msg:
        await _console_say(cid, msg)
    raise web.HTTPFound("/tools")


async def _dash_tools_joinvc(request: "aiohttp.web.Request"):
    from aiohttp import web
    from urllib.parse import quote

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    cid = as_int(data.get("channel_id"))
    ch = bot.get_channel(cid) if cid else None
    if ch is None and cid:
        try:
            ch = await bot.fetch_channel(cid)
        except Exception:
            ch = None
    if not isinstance(ch, (discord.VoiceChannel, discord.StageChannel)):
        out = "Not a voice channel the bot can see."
    else:
        try:
            vc = ch.guild.voice_client
            if vc is None:
                await ch.connect()
            elif vc.channel.id != ch.id:
                await vc.move_to(ch)
            out = f"Joined {ch.name} in {ch.guild.name}."
        except Exception as e:
            out = f"Couldn't join: {e}"
    raise web.HTTPFound("/tools?msg=" + quote(out))


async def _dash_tools_leavevc(request: "aiohttp.web.Request"):
    from aiohttp import web
    from urllib.parse import quote

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    cid = as_int(data.get("channel_id"))
    ch = bot.get_channel(cid) if cid else None
    vc = ch.guild.voice_client if ch is not None else None
    if vc is None:
        out = "Bot isn't in voice in that server."
    else:
        await vc.disconnect()
        out = f"Left voice in {ch.guild.name}."
    raise web.HTTPFound("/tools?msg=" + quote(out))


async def _dash_tools_dm(request: "aiohttp.web.Request"):
    from aiohttp import web

    if not _dash_auth_ok(request):
        raise web.HTTPFound("/login")
    data = await request.post()
    uid = as_int(data.get("user_id"))
    msg = (data.get("message") or "").strip()
    if uid and msg:
        await _console_dm(uid, msg)
    raise web.HTTPFound("/tools")


def _html_esc(s) -> str:
    return (
        str(s)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


async def start_dashboard():
    """Start the aiohttp dashboard on the bot's event loop."""
    from aiohttp import web

    app = web.Application()
    app.router.add_get("/", _dash_index)
    app.router.add_get("/login", _dash_login)
    app.router.add_post("/login", _dash_login)
    app.router.add_get("/guilds", _dash_guilds)
    app.router.add_get("/music", _dash_music)
    app.router.add_post("/music/skip", _dash_music_skip)
    app.router.add_post("/music/stop", _dash_music_stop)
    app.router.add_post("/music/play_default", _dash_music_play_default)
    app.router.add_get("/config", _dash_config)
    app.router.add_get("/tools", _dash_tools)
    app.router.add_post("/tools/say", _dash_tools_say)
    app.router.add_post("/tools/dm", _dash_tools_dm)
    app.router.add_post("/tools/joinvc", _dash_tools_joinvc)
    app.router.add_post("/tools/leavevc", _dash_tools_leavevc)

    runner = web.AppRunner(app)
    await runner.setup()
    site = web.TCPSite(runner, DASHBOARD_HOST, DASHBOARD_PORT)
    try:
        await site.start()
        log(f"Dashboard listening on http://{DASHBOARD_HOST}:{DASHBOARD_PORT}/")
    except OSError as e:
        log(f"Dashboard failed to bind {DASHBOARD_HOST}:{DASHBOARD_PORT}: {e}")


# Hook dashboard start into setup_hook
_original_setup_hook = MergedBot.setup_hook


async def _setup_hook_with_dash(self):
    await _original_setup_hook(self)
    self.loop.create_task(start_dashboard())


MergedBot.setup_hook = _setup_hook_with_dash  # type: ignore


# ===========================================================================
# Entry point
# ===========================================================================
if __name__ == "__main__":
    import threading

    print("Starting merged Discord bot…")
    print("Make sure DISCORD_TOKEN is set (env or bot_token.txt).")
    print(f"Dashboard will be at http://{DASHBOARD_HOST}:{DASHBOARD_PORT}/")
    if DASHBOARD_PASSWORD:
        print("Dashboard password is set (DASHBOARD_PASSWORD).")
    else:
        print("Dashboard has no password — only bind to localhost or set DASHBOARD_PASSWORD.")

    # Console input runs on its own thread so it doesn't block the bot's event loop
    console_thread = threading.Thread(target=_console_loop, name="console", daemon=True)
    console_thread.start()

    try:
        bot.run(TOKEN)
    except discord.LoginFailure:
        print("[!] Token rejected. Reset it in the Developer Portal and update DISCORD_TOKEN / bot_token.txt")
    except Exception:
        traceback.print_exc()
        try:
            input("\nPress Enter to exit…")
        except EOFError:
            pass