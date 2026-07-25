#!/usr/bin/env bash
# Build and run the BURST PROBE (agda/probe/Burst-Probe.agda).
#
#   scripts/burst-probe.sh [FIRST] [LAST] [RUNS] [DEPTH]   (defaults 1 1 200 4)
#
# Seeds FIRST..LAST, RUNS generated programs per seed per corpus, DEPTH capping
# program nesting — the same knobs as scripts/gen-unit-tests.sh.
#
# The probe needs an evaluator that records every subscription burst, and the
# verified evaluator must stay byte-identical (Verify-Well-Formed reduces its
# clauses).  So: copy agda/src to a scratch Agda project, instrument the COPY,
# drop the probe module in beside it, compile, run.  agda/src is never written.
#
# The probe replays its own drain against the real `evaluate` on every program,
# so an instrumentation that perturbed behaviour shows up as selfcheck failures
# rather than as plausible-looking numbers.
set -euo pipefail

# the report is UTF-8 (em-dashes, ∷ in rendered programs)
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

FIRST="${1:-1}"
LAST="${2:-$FIRST}"
RUNS="${3:-200}"
DEPTH="${4:-4}"

REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BUILD="${BURST_PROBE_DIR:-$(mktemp -d "${TMPDIR:-/tmp}/burst-probe.XXXXXX")}"

mkdir -p "$BUILD/src"
cp -R "$REPO/agda/src/." "$BUILD/src/"
cp "$REPO/agda/probe/Burst-Probe.agda" "$BUILD/src/Burst-Probe.agda"
cat > "$BUILD/rxjs-probe.agda-lib" <<'LIB'
name: rxjs-probe
include: src
depend: standard-library-2.2
LIB

python3 "$REPO/scripts/burst-probe-instrument.py" "$BUILD/src/Rx/Evaluator.agda"

cd "$BUILD"
# agda reports errors on stdout, so keep stdout and drop only progress chatter;
# grep must not decide the exit status (it exits 1 on a clean, silent build)
set +e
agda --compile --compile-dir=_out src/Burst-Probe.agda 2>&1 \
  | grep -v -e '^ *Checking ' -e '^Compiling '
rc="${PIPESTATUS[0]}"
set -e
if [ "$rc" -ne 0 ]; then
  echo "burst-probe: agda failed (exit $rc)" >&2
  exit "$rc"
fi

echo "$FIRST $LAST $RUNS $DEPTH" | ./_out/Burst-Probe
