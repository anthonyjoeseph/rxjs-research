#!/usr/bin/env bash
# Append newly-discovered counterexamples to Implementation/Unit-Test.agda.
# APPEND-ONLY: for each seed in the range, runs ./_cli/QuickCheck and, if it
# reports a failure, extracts the paste-ready Agda block (between the
# -- <<<PASTE / -- PASTE>>> markers) and appends it — UNLESS that exact program
# already appears in the file. Nothing is ever deleted or overwritten; a fixed
# bug simply becomes a passing guard that stays. The file fully typechecks iff
# no known counterexample remains.
#
# Usage:  scripts/gen-unit-tests.sh [FIRST] [LAST]     (defaults 1 300)
# Requires: ./_cli/QuickCheck already built.
set -euo pipefail
cd "$(dirname "$0")/.."

FIRST="${1:-1}"
LAST="${2:-300}"
QC=./_cli/QuickCheck
OUT=src/Implementation/Unit-Test.agda

if [[ ! -x "$QC" ]]; then echo "build $QC first" >&2; exit 1; fi

added=0
for s in $(seq "$FIRST" "$LAST"); do
  out="$(echo "$s" | "$QC" 2>/dev/null)" || { printf '\r  seed %s (blowup/err, skipped) ' "$s" >&2; continue; }
  echo "$out" | grep -q '<<<PASTE' || { printf '\r  seed %s ok            ' "$s" >&2; continue; }
  block="$(echo "$out" | sed -n '/<<<PASTE/,/PASTE>>>/p' | sed '1d;$d')"
  prog="$(echo "$block" | sed -n '2p')"          # the program line is the dedup key
  if grep -qF "$prog" "$OUT"; then
    printf '\r  seed %s FAIL (already cached) ' "$s" >&2; continue
  fi
  { echo; echo "-- seed $s"; echo "$block"; } >> "$OUT"
  added=$((added+1))
  printf '\r  seed %s FAIL — appended (#%s)  \n' "$s" "$added" >&2
done
printf '\r%*s\r' 40 '' >&2
echo "appended $added new distinct failing programs to $OUT" >&2
