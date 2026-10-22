# Discord bot + web dashboard (Railway / Docker)
FROM python:3.12-slim

# FFmpeg required for music playback
RUN apt-get update \
    && apt-get install -y --no-install-recommends ffmpeg nodejs \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

COPY merged_discord_bot.py .

# Railway sets PORT; bot maps it to the dashboard when DASHBOARD_PORT is unset
ENV DASHBOARD_HOST=0.0.0.0
ENV PYTHONUNBUFFERED=1

# No interactive console on Railway (stdin is not a TTY)
CMD ["python", "-u", "merged_discord_bot.py"]
