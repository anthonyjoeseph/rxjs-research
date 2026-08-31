#!/bin/bash
# SessionStart hook (Claude Code on the web): rebuild the Agda toolchain and
# TypeScript deps on a fresh container, and re-enable the swapfile a cold
# `make gate-heavy` needs to survive its peak-RSS module without OOMing.
# Idempotent — safe to re-run every session, including a warm one.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

REPO="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"
cd "$REPO"

echo "=== Agda toolchain (scripts/install-agda.sh) ==="
bash scripts/install-agda.sh

# Make the toolchain visible for the rest of this session, and to future
# hook runs in the same shell family.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  {
    echo 'export PATH="$HOME/.cabal/bin:$PATH"'
    echo 'export LC_ALL=C.UTF-8 LANG=C.UTF-8'
  } >> "$CLAUDE_ENV_FILE"
fi

echo "=== TypeScript deps (typescript/npm install) ==="
if [ -f typescript/package.json ]; then
  (cd typescript && npm install)
fi

echo "=== Swapfile ==="
# A cold `make gate-heavy` tower check has peaked near this container's
# ~15GB memcg ceiling on one deeply-nested-mutual-block module and been
# OOM-killed; 12GB of swap gave enough headroom for a retry to go green.
# The file's bytes can survive a container rebuild but `swapon` state is
# kernel/runtime state and does not, so this always re-checks it.
SWAPFILE=/swapfile
SWAP_SIZE_KB=12582912 # 12GiB, matches what was validated to work
if command -v swapon >/dev/null 2>&1 && [ "$(id -u)" = "0" ]; then
  if ! swapon --show=NAME --noheadings 2>/dev/null | grep -qx "$SWAPFILE"; then
    if [ ! -f "$SWAPFILE" ]; then
      fallocate -l "${SWAP_SIZE_KB}K" "$SWAPFILE" 2>/dev/null \
        || dd if=/dev/zero of="$SWAPFILE" bs=1M count=$((SWAP_SIZE_KB / 1024)) status=none
      chmod 600 "$SWAPFILE"
      mkswap "$SWAPFILE" >/dev/null
    fi
    swapon "$SWAPFILE"
    echo "swapon $SWAPFILE: $(swapon --show=NAME,SIZE --noheadings | grep "$SWAPFILE")"
  else
    echo "$SWAPFILE already active"
  fi
else
  echo "not root or no swapon — skipping swapfile setup"
fi

echo "=== session-start hook done ==="
