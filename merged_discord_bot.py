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
PREFIX = "."
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
    print(f"Logged in as {bot.user} (ID: {bot.user.id})")
    print(f"Prefix: {PREFIX}  |  Slash commands registered globally")
    print(f"Dashboard → http://{DASHBOARD_HOST}:{DASHBOARD_PORT}/")
    try:
        await bot.change_presence(
            activity=discord.Activity(type=discord.ActivityType.watching, name="servers • templates • music")
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
    await ctx.guild.ban(user, reason=reason or f".ban by {ctx.author}")
    note = "" if member is not None else " *(user wasn't in the server)*"
    await ctx.reply(f"🚫 Banned **{user}** (`{user.id}`).{note}", mention_author=False)
    await modlog(ctx, "Ban", user, reason)


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


@bot.command(name="help")
async def help_command(ctx: commands.Context):
    embed = discord.Embed(title="Merged Bot — Commands", description=f"Prefix: `{PREFIX}`", color=0x5865F2)
    embed.add_field(
        name="Utility (prefix)",
        value=(
            f"`{PREFIX}snipe` / `s` — last deleted message\n"
            f"`{PREFIX}clearsnipe` / `cs` — clear snipe cache\n"
            f"`{PREFIX}ping` — latency\n"
            f"`{PREFIX}userinfo [user]` — user info\n"
            f"`{PREFIX}avatar [user]` — avatar\n"
            f"`{PREFIX}serverinfo` — server info\n"
            f"`{PREFIX}kick` / `{PREFIX}to` / `{PREFIX}ban` — moderation"
        ),
        inline=False,
    )
    embed.add_field(
        name="Music",
        value=(
            f"`/play` or `{PREFIX}play` — empty = **default Spotify playlist**\n"
            f"`/skip /pause /resume /stop /queue /nowplaying /volume /loop /leave`\n"
            f"Also: `{PREFIX}skip` `{PREFIX}pause` `{PREFIX}queue` `{PREFIX}np` `{PREFIX}leave`"
        ),
        inline=False,
    )
    embed.add_field(
        name="Slash commands",
        value=(
            "**/set** — APK announcer + mod-log config\n"
            "**/roleall** — mass role give/remove\n"
            "**/ban / unban / kick / timeout / untimeout**\n"
            "**/warn / warnings / clearwarnings**\n"
            "**/purge / slowmode / lock / unlock**\n"
            "**/pull / apply** — server templates\n"
            "**/lookup / reversevid / search / uservideos / download / sound / history** — TikTok"
        ),
        inline=False,
    )
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
    await ctx.reply(f"🎵 **{gm.now.title}** `{gm.now.duration_str()}`", mention_author=False)


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
      <p class="muted">Music: <span class="mono">/play</span> (empty = default playlist) ·
      <span class="mono">/skip /pause /queue /leave</span></p>
      <p class="muted">Mod: <span class="mono">/ban /kick /timeout /warn /purge</span></p>
      <p class="muted">Templates: <span class="mono">/pull /apply</span></p>
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
