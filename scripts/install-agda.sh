#!/usr/bin/env bash
# Install the Agda toolchain this repo needs, from scratch, on a fresh
# cloud box. Idempotent: re-running skips whatever is already in place.
#
#   Agda 2.7.0.1  (built with GHC's MAlonzo backend, so we need GHC)
#   GHC 9.4.7 + cabal 3.8  (from apt — the GHCup domain is proxy-blocked here)
#   agda-stdlib 2.2  (registered in ~/.agda so `agda` finds it by default)
#
# After this, from repo root:
#   export PATH="$HOME/.cabal/bin:$PATH"
#   export LC_ALL=C.UTF-8 LANG=C.UTF-8      # the CLI emits em-dashes; avoid a
#                                            # locale crash at runtime
#   cd agda && agda src/Main.agda                       # typecheck everything
#   agda --compile --compile-dir=_cli src/CLI/Main.agda # build the batch CLI
#   agda --compile --compile-dir=_cli src/QuickCheck.agda
#
# NEW AGENT, START HERE: run this script, then read CLAUDE.md for the
# working methodology. The TS side lives in typescript/ (npm install; the
# oracle is `npm run oracle`, the all-Agda QuickCheck is `npm run agda:qc`).
set -euo pipefail

AGDA_VERSION=2.7.0.1
STDLIB_VERSION=2.2
STDLIB_DIR="$HOME/agda-stdlib-${STDLIB_VERSION}"

log() { printf '\n=== %s ===\n' "$1"; }

log "GHC + cabal (apt)"
if ! command -v ghc >/dev/null 2>&1 || ! command -v cabal >/dev/null 2>&1; then
  # Some PPA repos may be inaccessible in this cloud environment; allow the update to
  # proceed despite them by suppressing the error exit code. The standard Ubuntu repos
  # should be available.
  sudo apt-get update -y 2>&1 | grep -v "^Err:\|403\|Forbidden\|no longer signed" || true
  sudo apt-get install -y ghc cabal-install
else
  echo "ghc $(ghc --numeric-version), cabal $(cabal --numeric-version) already present"
fi

export PATH="$HOME/.cabal/bin:$PATH"

log "Agda ${AGDA_VERSION} (cabal)"
if command -v agda >/dev/null 2>&1 && [ "$(agda --numeric-version 2>/dev/null)" = "$AGDA_VERSION" ]; then
  echo "Agda ${AGDA_VERSION} already installed at $(command -v agda)"
else
  cabal update
  cabal install "Agda-${AGDA_VERSION}" --overwrite-policy=always
fi

log "agda-stdlib ${STDLIB_VERSION}"
if [ ! -d "$STDLIB_DIR" ]; then
  tarball="/tmp/agda-stdlib-${STDLIB_VERSION}.tar.gz"
  curl -fsSL \
    "https://github.com/agda/agda-stdlib/archive/refs/tags/v${STDLIB_VERSION}.tar.gz" \
    -o "$tarball"
  tar -xzf "$tarball" -C "$HOME"
  rm -f "$tarball"
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
