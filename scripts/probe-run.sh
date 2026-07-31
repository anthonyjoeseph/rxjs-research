#!/usr/bin/env bash
set -u
export PATH="$PATH:/root/.cabal/bin" LC_ALL=C.UTF-8 LANG=C.UTF-8
cd "$(dirname "$0")/../agda"
LOG="$2"; : > "$LOG"
agda -i src -i probe "$1" >> "$LOG" 2>&1
echo "EXIT=$?" >> "$LOG"
