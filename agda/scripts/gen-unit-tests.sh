#!/usr/bin/env bash
# Regenerate the OPEN section of Implementation/Unit-Test.agda from QuickCheck
# counterexamples. For each seed in the range, runs ./_cli/QuickCheck and, if it
# reports a failure, extracts the paste-ready Agda block (emitted between the
# -- <<<PASTE / -- PASTE>>> markers). Deduplicates by program text so a bug that
# recurs across seeds is pinned once.
#
# Usage:  scripts/gen-unit-tests.sh [FIRST] [LAST]     (defaults 1 200)
# Requires: ./_cli/QuickCheck already built.
set -euo pipefail
cd "$(dirname "$0")/.."

FIRST="${1:-1}"
LAST="${2:-200}"
QC=./_cli/QuickCheck
OUT=src/Implementation/Unit-Test.agda
TMP="$(mktemp)"
SEEN="$(mktemp)"

if [[ ! -x "$QC" ]]; then echo "build $QC first" >&2; exit 1; fi

echo "-- Generated $(printf '%s..%s' "$FIRST" "$LAST") by scripts/gen-unit-tests.sh — do not hand-edit." >> "$TMP"

count=0
for s in $(seq "$FIRST" "$LAST"); do
  out="$(echo "$s" | "$QC" 2>/dev/null)"
  # skip seeds with no failure
  echo "$out" | grep -q '<<<PASTE' || { printf '\r  seed %s (clean)      ' "$s" >&2; continue; }
  block="$(echo "$out" | sed -n '/<<<PASTE/,/PASTE>>>/p' | sed '1d;$d')"
  prog="$(echo "$block" | sed -n '2p')"          # the program line dedupes cases
  if grep -qxF "$prog" "$SEEN"; then continue; fi
  echo "$prog" >> "$SEEN"
  count=$((count+1))
  { echo "-- seed $s"; echo "$block"; echo; } >> "$TMP"
  printf '\r  seed %s FAIL (#%s)    \n' "$s" "$count" >&2
done
printf '\r%*s\r' 40 '' >&2
echo "$count distinct failing programs" >&2

# splice into the OUT file between the markers
awk -v tmp="$TMP" '
  /-- BEGIN GENERATED/ { print; while ((getline l < tmp) > 0) print l; skip=1; next }
  /-- END GENERATED/   { skip=0 }
  !skip { print }
' "$OUT" > "$OUT.new" && mv "$OUT.new" "$OUT"
rm -f "$TMP" "$SEEN"
echo "wrote $OUT" >&2
