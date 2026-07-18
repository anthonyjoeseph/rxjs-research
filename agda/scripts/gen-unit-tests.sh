#!/usr/bin/env bash
# Append newly-discovered counterexamples to Implementation/Unit-Test.agda.
# APPEND-ONLY: for each seed in the range, runs ./_cli/QuickCheck and, if it
# reports a failure, extracts the paste-ready Agda block (between the
# -- <<<PASTE / -- PASTE>>> markers) and appends it — UNLESS that exact
# program already appears in the file. Nothing is ever deleted or
# overwritten; a fixed bug simply becomes a passing guard that stays. The
# file fully typechecks iff no known counterexample remains.
#
# Usage:  scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH]
#         (defaults: 1 300 200 4)
# Requires: ./_cli/QuickCheck already built (npm run agda:qc).
set -euo pipefail
cd "$(dirname "$0")/.."

FIRST="${1:-1}"
LAST="${2:-300}"
RUNS="${3:-200}"
DEPTH="${4:-4}"
QC=./_cli/QuickCheck
OUT=src/Implementation/Unit-Test.agda
export LC_ALL=C.UTF-8 LANG=C.UTF-8   # the report uses non-ASCII glyphs

if [[ ! -x "$QC" ]]; then echo "build $QC first (npm run agda:qc)" >&2; exit 1; fi

added=0
for s in $(seq "$FIRST" "$LAST"); do
  out="$(echo "$s $RUNS $DEPTH" | "$QC" 2>/dev/null)" \
    || { printf '\r  seed %s (err, skipped) ' "$s" >&2; continue; }
  echo "$out" | grep -q '<<<PASTE' \
    || { printf '\r  seed %s ok            ' "$s" >&2; continue; }
  echo "$out"                                     # surface every mismatch on stdout

  # a run may report MANY failing programs; carve out each PASTE block
  # (lines strictly between the markers) into its own temp file
  tmpd="$(mktemp -d)"
  echo "$out" | awk -v d="$tmpd" '
    /<<<PASTE/  { n++; inblk=1; fn=sprintf("%s/blk%04d", d, n); next }
    /PASTE>>>/  { inblk=0; next }
    inblk       { print > fn }
  '
  for f in "$tmpd"/blk*; do
    [ -e "$f" ] || continue
    prog="$(sed -n '2p' "$f")"                   # the program line is the dedup key
    if grep -qF "$prog" "$OUT"; then continue; fi # skip cached (or just-appended) dupes
    { echo; echo "-- seed $s"; cat "$f"; } >> "$OUT"
    added=$((added+1))
    printf '\r  seed %s FAIL — appended (#%s)  \n' "$s" "$added" >&2
  done
  rm -rf "$tmpd"
done
printf '\r%*s\r' 40 '' >&2
echo "appended $added new distinct failing programs to $OUT" >&2
