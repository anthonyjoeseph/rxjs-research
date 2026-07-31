#!/usr/bin/env bash
# Build and run the JOINT PROBE (agda/probe/Joint-Probe.agda).
#
#   scripts/joint-probe.sh FIRST [LAST]     rows FIRST..LAST, one per process
#
# The probe needs an evaluator that logs every subscribeE entry's
# (pathLen κ , sizeᵉ b), and the verified evaluator must stay byte-identical
# (Verify-Well-Formed reduces its clauses).  So: copy agda/src to a scratch
# Agda project, instrument the COPY, drop the probe and the shapes it imports
# in beside it, compile, run.  agda/src is never written.
#
# The build is CACHED in $JOINT_PROBE_DIR (default a fixed scratch path) so a
# sweep does not pay the compile per row; delete that directory to rebuild.
set -euo pipefail

export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"
export PATH="$PATH:$HOME/.cabal/bin:/root/.cabal/bin"

FIRST="${1:-0}"
LAST="${2:-$FIRST}"

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD="${JOINT_PROBE_DIR:-${TMPDIR:-/tmp}/joint-probe}"

if [ ! -x "$BUILD/_out/Joint-Probe" ]; then
  rm -rf "$BUILD"
  mkdir -p "$BUILD/src"
  cp -R "$REPO/agda/src/." "$BUILD/src/"
  cp "$REPO/agda/probe/Mint-Loop-Shapes.agda" "$BUILD/src/Mint-Loop-Shapes.agda"
  cp "$REPO/agda/probe/Joint-Probe.agda" "$BUILD/src/Joint-Probe.agda"
  cat > "$BUILD/rxjs-probe.agda-lib" <<'LIB'
name: rxjs-joint-probe
include: src
depend: standard-library-2.2
LIB

  python3 "$REPO/scripts/joint-probe-instrument.py" "$BUILD/src/Rx/Evaluator.agda"

  # Behaviour-neutrality: jointLog is WRITTEN and NEVER READ inside the
  # evaluator, so it cannot influence a burst, a registry or a schedule.  The
  # only three places allowed to mention it are the field declaration, st-init
  # and logJoint's own body.
  stray="$(grep -n 'jointLog' "$BUILD/src/Rx/Evaluator.agda" \
           | grep -v -e 'jointLog        : List (ℕ × ℕ)  -- JOINT PROBE (write-only)' \
                     -e 'st-init e = record { jointLog = \[\] ;' \
                     -e 'record st { jointLog = (probePathLen κ , sizeᵉ b) ∷ EvalSt.jointLog st }' \
           || true)"
  if [ -n "$stray" ]; then
    echo "joint-probe: the instrumented evaluator READS jointLog — not neutral:" >&2
    echo "$stray" >&2
    exit 1
  fi

  cd "$BUILD"
  set +e
  agda --compile --compile-dir=_out src/Joint-Probe.agda 2>&1 \
    | grep -v -e '^ *Checking ' -e '^Compiling ' \
              -e '^\[ *[0-9]* of *[0-9]*\] Compiling ' -e '^Linking ' -e '^Calling: '
  rc="${PIPESTATUS[0]}"
  set -e
  if [ "$rc" -ne 0 ]; then
    echo "joint-probe: agda failed (exit $rc)" >&2
    exit "$rc"
  fi
fi

cd "$BUILD"
for n in $(seq "$FIRST" "$LAST"); do
  echo "$n" | ./_out/Joint-Probe
done
