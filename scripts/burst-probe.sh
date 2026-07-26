#!/usr/bin/env bash
# Build and run the BURST PROBE (agda/probe/Burst-Probe.agda).
#
#   scripts/burst-probe.sh [FIRST] [LAST] [RUNS] [DEPTH] [CORPUS]  (1 1 200 4 0)
#
# Seeds FIRST..LAST, RUNS generated programs per seed per corpus, DEPTH capping
# program nesting — the same knobs as scripts/gen-unit-tests.sh.  CORPUS picks one
# corpus (0 all, 1 A, 2 B, 3 C, 4 C₃); with the report arriving in one block at
# the end, that is how a long run that wedged or got reaped is bisected — seed
# range narrows the seed, CORPUS the corpus, halving RUNS the program.
#
# The probe needs an evaluator that records every subscription burst, and the
# verified evaluator must stay byte-identical (Verify-Well-Formed reduces its
# clauses).  So: copy agda/src to a scratch Agda project, instrument the COPY,
# drop the probe module in beside it, compile, run.  agda/src is never written.
#
# Two guards keep the numbers honest, and they cover different things:
#   • the probe replays its own drain against `evaluate` on every program, so a
#     probe drain that drifted from the real one is a loud failure;
#   • this script greps the instrumented copy to confirm the log is written and
#     never read, which is what makes the instrumentation behaviour-neutral (the
#     in-Agda check cannot see that — both sides of it run instrumented).
set -euo pipefail

# the report is UTF-8 (em-dashes, ∷ in rendered programs)
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

FIRST="${1:-1}"
LAST="${2:-$FIRST}"
RUNS="${3:-200}"
DEPTH="${4:-4}"
CORPUS="${5:-0}"

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

# Behaviour-neutrality.  The probe's in-Agda selfcheck compares probeDrain
# against `evaluate` INSIDE the instrumented build, so it catches a drifted
# drain but not an instrumentation that moved the evaluator.  What makes the
# instrumentation neutral is that burstLog is written and NEVER READ: the log
# cannot influence a burst, a registry or a schedule.  Enforce exactly that —
# the only three places allowed to mention it are the field declaration, st-init
# and logBurst's own body.
stray="$(grep -n 'burstLog' "$BUILD/src/Rx/Evaluator.agda" \
         | grep -v -e 'burstLog        : List (List (InstEmit ⊤))' \
                   -e 'st-init e = record { burstLog = \[\] ;' \
                   -e 'logBurst b st = record st { burstLog = map probeEmit b ∷ EvalSt.burstLog st }' \
         || true)"
if [ -n "$stray" ]; then
  echo "burst-probe: the instrumented evaluator READS burstLog — not neutral:" >&2
  echo "$stray" >&2
  exit 1
fi

cd "$BUILD"
# agda reports errors on stdout, so keep stdout and drop only progress chatter;
# grep must not decide the exit status (it exits 1 on a clean, silent build)
set +e
agda --compile --compile-dir=_out src/Burst-Probe.agda 2>&1 \
  | grep -v -e '^ *Checking ' -e '^Compiling ' \
            -e '^\[ *[0-9]* of *[0-9]*\] Compiling ' -e '^Linking ' -e '^Calling: '
rc="${PIPESTATUS[0]}"
set -e
if [ "$rc" -ne 0 ]; then
  echo "burst-probe: agda failed (exit $rc)" >&2
  exit "$rc"
fi

echo "$FIRST $LAST $RUNS $DEPTH $CORPUS" | ./_out/Burst-Probe
