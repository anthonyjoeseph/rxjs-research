#!/usr/bin/env bash
# Run the all-Agda QuickCheck over a FIXED seed range and fail on any
# counterexample.  Writes nothing.
#
#   scripts/quickcheck-sweep.sh [FIRST] [LAST] [RUNS] [DEPTH]
#
# WHY THIS IS NOT `make quickcheck`.  That target exists to GROW the bug
# cache: it appends a case module per new counterexample and then tells you
# the gate is expected to fail.  A check that edits the tree it is checking
# cannot be a gate step — a green run and a red run leave different trees,
# and the second one has already written the finding it was supposed to
# report.  So the sweep shares the binary and nothing else: same seeds every
# run, no dedup state, no append, and the verdict is the exit code.
#
# WHAT A FAILURE MEANS.  The binary compares `impl-batchSimultaneous`
# against `spec-batchSimultaneous` on generated programs, and the spec is
# gospel — so a failing case is an IMPLEMENTATION bug, never a spec one.
# The sweep prints the failing seed and the block the binary emitted; run
# `make quickcheck ARGS='<seed> <seed>'` to cache it as a type-level unit
# test, then fix the implementation.
set -euo pipefail

FIRST=${1:-1}
LAST=${2:-60}
RUNS=${3:-200}
DEPTH=${4:-4}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QC="$ROOT/agda/_cli/QuickCheck"

[ -x "$QC" ] || { echo "quickcheck-sweep: no $QC — run 'make qc-build' first" >&2; exit 1; }

# the binary prints em-dashes and Agda's unicode identifiers; a C locale
# turns both into a commitBuffer crash
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

cases=0
bad=0
for seed in $(seq "$FIRST" "$LAST"); do
  # stdin is: SEED RUNS DEPTH (QuickCheck.agda's main reads runs before depth)
  printf '%s %s %s\n' "$seed" "$RUNS" "$DEPTH" | "$QC" > "$tmp"
  line="$(head -1 "$tmp")"

  # "seed N depth D — ran R cases, F failures; μ A var B defer C"
  fails="$(printf '%s\n' "$line" | sed -n 's/.*cases, \([0-9][0-9]*\) failures.*/\1/p')"
  if [ -z "$fails" ]; then
    echo "quickcheck-sweep: seed $seed printed no summary line:" >&2
    cat "$tmp" >&2
    exit 1
  fi

  cases=$((cases + RUNS))
  if [ "$fails" -ne 0 ]; then
    bad=$((bad + fails))
    echo "quickcheck-sweep: RED — $line"
    cat "$tmp"
  fi
done

if [ "$bad" -ne 0 ]; then
  echo "quickcheck-sweep: $bad counterexample(s) over seeds $FIRST..$LAST" >&2
  echo "  the spec is gospel — this is an implementation bug.  Cache it with" >&2
  echo "  'make quickcheck ARGS=\"<seed> <seed>\"' and fix the implementation." >&2
  exit 1
fi

echo "quickcheck-sweep: clean — $cases case(s) over seeds $FIRST..$LAST at depth $DEPTH"
