#!/usr/bin/env sh
set -eu
export PORT="${PORT:-8080}"
export DATA_DIR="${DATA_DIR:-/data}"
export DB_PATH="${DB_PATH:-$DATA_DIR/omtogel_staff.db}"
mkdir -p "$DATA_DIR"
exec gunicorn --workers 1 --threads 8 --timeout 120 --bind "0.0.0.0:$PORT" app:app
