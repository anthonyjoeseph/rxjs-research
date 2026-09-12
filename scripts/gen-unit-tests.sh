#!/usr/bin/env bash
# Append newly-discovered QuickCheck counterexamples to the bug cache's
# corpus, agda/src/Implementation/Unit-Test.agda.
#
#   scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH]
#
# Defaults: seeds 1..300, 200 runs each, depth 4 — what `make quickcheck`
# runs with no ARGS.
#
# APPEND-ONLY.  QuickCheck emits each failing case as a self-delimited
# `-- <<<PASTE` / `-- PASTE>>>` block; we dedup on the block's PROGRAM line,
# so a seed that rediscovers a cached program adds nothing, and a bug that
# has since been fixed simply stays on as a passing guard.  Nothing here
# ever deletes or rewrites an existing entry.
#
# THE BLOCK IS ALREADY A ROW, trailing `∷` included — QuickCheck prints the
# corpus's own syntax, so this script never builds or parses Agda.  All it
# does is name the row (the binary writes `"?"`, since a hand-pasted block
# has to typecheck as it stands) and splice it in above the list's `[]`.
#
# Invariant the cache exists to enforce: every row holds <=> no known
# counterexample remains.  So after this appends anything, `make bug-cache`
# is expected to FAIL until the implementation is fixed.
set -euo pipefail

FIRST=${1:-1}
LAST=${2:-300}
RUNS=${3:-200}
DEPTH=${4:-4}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QC="$ROOT/agda/_cli/QuickCheck"
CORPUS="$ROOT/agda/src/Implementation/Unit-Test.agda"

[ -x "$QC" ]     || { echo "gen-unit-tests: no $QC — run 'make qc-build' first" >&2; exit 1; }
[ -f "$CORPUS" ] || { echo "gen-unit-tests: no $CORPUS" >&2; exit 1; }
grep -qx '  \[\]' "$CORPUS" || {
  echo "gen-unit-tests: $CORPUS does not end its list with a bare '  []'" >&2; exit 1; }
grep -qx -- '-- <<<IMPORTS' "$CORPUS" || {
  echo "gen-unit-tests: $CORPUS carries no '-- <<<IMPORTS' marker" >&2; exit 1; }

# THE WIDE IMPORT BLOCK, a superset of what any generated program can mention.
# `make imports-fix` prunes it to what the corpus actually uses, which is what
# makes the pruned file unable to accept the NEXT row — so the wide form is
# restored here, before anything is appended, and pruned again at the end.
read -r -d '' WIDE_IMPORTS <<'AGDA' || true
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (after_,_; hot; cold)
open import Rx.Exp using (input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
  nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add; mul)
open import Rx.Slots using (scripted; shared)

open import Implementation.Unit-Test.Prelude using (Case; cached)
AGDA

widen () {
  local t; t="$(mktemp)"
  awk -v block="$WIDE_IMPORTS" '
    /^-- <<<IMPORTS$/ { print; print block; skip = 1; next }
    /^-- IMPORTS>>>$/ { skip = 0 }
    !skip             { print }
  ' "$CORPUS" > "$t"
  mv "$t" "$CORPUS"
}

# the binary prints em-dashes, and the pasted blocks are full of Agda's
# unicode identifiers — a C locale turns both into a commitBuffer crash
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

tmp="$(mktemp)"
row="$(mktemp)"
spl="$(mktemp)"
trap 'rm -f "$tmp" "$row" "$spl"' EXIT

widen

added=0
for seed in $(seq "$FIRST" "$LAST"); do
  # stdin is: SEED RUNS DEPTH  (QuickCheck.agda's main: parseNat, numAt 1,
  # numAt 2 — runs before depth)
  printf '%s %s %s\n' "$seed" "$RUNS" "$DEPTH" | "$QC" > "$tmp"
  head -1 "$tmp"

  nblocks="$(grep -c '^-- <<<PASTE$' "$tmp" || true)"
  [ "${nblocks:-0}" -eq 0 ] && continue

  for k in $(seq 1 "$nblocks"); do
    awk -v want="$k" '
      /^-- <<<PASTE$/ { n++; if (n == want) inb = 1; next }
      /^-- PASTE>>>$/ { if (inb) exit; next }
      inb             { print }
    ' "$tmp" > "$row"

    # line 2 is the program, and it is the whole key: every row is held to
    # BOTH properties, so a program that fails agreement and well-formedness
    # at once dedups to one row rather than being cached twice
    key="$(sed -n '2p' "$row")"
    if grep -Fqx -- "$key" "$CORPUS"; then
      continue
    fi

    # one seed can yield several blocks, and two seeds can find the same
    # shape, so the label is disambiguated rather than assumed unique
    label="$seed"; n=1
    while grep -Fq -- "\"$label\" 30" "$CORPUS"; do
      n=$((n + 1)); label="$seed-$n"
    done
    sed -i "1s/\"?\"/\"$label\"/" "$row"

    # splice above the list's terminator, which is the corpus's last line
    sed '$d' "$CORPUS" > "$spl"
    cat "$row" >> "$spl"
    printf '  []\n' >> "$spl"
    cp "$spl" "$CORPUS"

    added=$((added + 1))
    echo "  + cached a new counterexample (seed $seed) as \"$label\""
  done
done

echo "gen-unit-tests: appended $added new row(s) to ${CORPUS#"$ROOT"/}"

# UNCONDITIONAL, because `widen` ran unconditionally: a dead import is an
# `imports-check` failure, so leaving the wide form behind on a run that found
# nothing would break the gate for having found nothing.
( cd "$ROOT" && make --no-print-directory imports-fix >/dev/null )
echo "gen-unit-tests: pruned the corpus's imports"

if [ "$added" -gt 0 ]; then
  echo "gen-unit-tests: now run 'make bug-cache' — it is green iff no known"
  echo "                counterexample remains, so it should fail until the"
  echo "                implementation is fixed."
fi
