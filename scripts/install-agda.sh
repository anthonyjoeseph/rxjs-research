#!/usr/bin/env bash
# Install the Agda toolchain this repo needs on a fresh box, in seconds.
# Idempotent: re-running skips whatever is already in place.
#
#   Agda 2.8.0  — the OFFICIAL prebuilt binary from the agda/agda GitHub
#                 release: statically linked, its data files embedded (written
#                 to $XDG_DATA_HOME/agda on first run).  Building it with cabal
#                 took the better part of an hour, every fresh container.
#   GHC         — from apt, only for `--compile` (MAlonzo); the typechecker
#                 does not need it.  The GHCup domain is proxy-blocked here.
#   agda-stdlib 2.3  (registered in ~/.agda so `agda` finds it by default)
#
# Installs to ~/.cabal/bin, where the cabal build used to land, so every PATH
# line that already names it keeps working.
#
# After this, from repo root:
#   export PATH="$HOME/.cabal/bin:$PATH"
#   export LC_ALL=C.UTF-8 LANG=C.UTF-8      # the CLI emits em-dashes; avoid a
#                                            # locale crash at runtime
#   make agda
#
# NEW AGENT, START HERE: run this script, then read CLAUDE.md.
set -euo pipefail

AGDA_VERSION=2.8.0
STDLIB_VERSION=2.3
STDLIB_DIR="$HOME/agda-stdlib-${STDLIB_VERSION}"
BIN_DIR="$HOME/.cabal/bin"
AGDA_URL="https://github.com/agda/agda/releases/download/v${AGDA_VERSION}/Agda-v${AGDA_VERSION}-linux.tar.xz"

log() { printf '\n=== %s ===\n' "$1"; }

log "GHC (apt, for --compile only)"
if ! command -v ghc >/dev/null 2>&1; then
  sudo apt-get update -y 2>&1 | grep -v "^Err:\|403\|Forbidden\|no longer signed" || true
  sudo apt-get install -y ghc
else
  echo "ghc $(ghc --numeric-version) already present"
fi

export PATH="$BIN_DIR:$PATH"

log "Agda ${AGDA_VERSION} (prebuilt release binary)"
if command -v agda >/dev/null 2>&1 && [ "$(agda --numeric-version 2>/dev/null)" = "$AGDA_VERSION" ]; then
  echo "Agda ${AGDA_VERSION} already installed at $(command -v agda)"
else
  mkdir -p "$BIN_DIR"
  tmp="$(mktemp -d)"
  trap 'rm -rf "$tmp"' EXIT
  curl -fsSL --retry 4 --max-time 300 -o "$tmp/agda.tar.xz" "$AGDA_URL"
  tar -xJf "$tmp/agda.tar.xz" -C "$tmp"
  install -m 755 "$tmp/agda" "$BIN_DIR/agda"
  echo "installed $(agda --version | head -1) at $BIN_DIR/agda"
fi

log "agda-stdlib ${STDLIB_VERSION}"
if [ ! -d "$STDLIB_DIR" ]; then
  git clone --depth 1 --branch v${STDLIB_VERSION} \
    https://github.com/agda/agda-stdlib.git "$STDLIB_DIR"
else
  echo "stdlib already unpacked at ${STDLIB_DIR}"
fi

log "register stdlib in ~/.agda"
mkdir -p "$HOME/.agda"
echo "${STDLIB_DIR}/standard-library.agda-lib" > "$HOME/.agda/libraries"
echo "standard-library-${STDLIB_VERSION}" > "$HOME/.agda/defaults"

log "done"
cat <<EOF
Agda:   $(command -v agda)  ($(agda --numeric-version))
stdlib: ${STDLIB_DIR}

Add to your shell for this session:
  export PATH="\$HOME/.cabal/bin:\$PATH"
  export LC_ALL=C.UTF-8 LANG=C.UTF-8
EOF
