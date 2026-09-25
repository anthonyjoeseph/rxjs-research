#!/usr/bin/env bash
# Append newly-discovered QuickCheck counterexamples to the bug cache's
# corpus, agda/src/Implementation/Unit-Test.agda.
#
#   scripts/gen-unit-tests.sh [FIRST] [LAST] [RUNS] [DEPTH] [SECS]
#
# Defaults: seeds 1..300, 200 runs each, depth 4 — what `make quickcheck`
# runs with no ARGS — and 60 seconds per seed, ten times what a seed costs.
#
# A SEED IS BOUNDED IN WALL CLOCK, BECAUSE ONE CASE CAN COST MORE THAN THE
# WHOLE SWEEP.  A guarded fixpoint whose step hands back more elements than
# it was given, with no `takeᵉ` above it, has a run exponential in the
# fuel; the corpus contains such programs and the generator has no reason
# not to draw one.  The cost is INSIDE `evaluate↓` rather than in the list
# it returns — the drain forces each cascade whole — so a budget on the
# stream's length buys nothing, and wall clock is what actually measures
# the thing.  Measured: one case of seed 3 outruns the other 199 by more
# than two orders of magnitude and does not finish.
#
# THE SEED IS THEN REPORTED AS TIMED OUT, NOT AS AGREEING.  It contributes
# no census and no rows, so the sweep says which part of its corpus it
# could not run rather than reporting the remainder as a clean sweep —
# and the exit status stays what it was, since the verdict this script
# reports is the CORPUS.  The bound is a BACKSTOP rather than the fix: the
# generator caps every tree it draws with a root `takeᵉ`, which unsubscribes
# the fixpoint once the cap is reached and is what actually keeps such a
# program finite.
#
# `timeout` DOES NOT EXIST ON macOS, so it is used when present (`gtimeout`
# from coreutils counts) and skipped with a warning when it is not.  A
# local run then behaves as it always did.
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
SECS=${5:-60}

# a seed that ran out of time leaves the binary killed mid-write, so the
# capture is treated as absent rather than parsed
TIMEOUT=""
if command -v timeout >/dev/null 2>&1; then TIMEOUT="timeout $SECS"
elif command -v gtimeout >/dev/null 2>&1; then TIMEOUT="gtimeout $SECS"
else
  echo "gen-unit-tests: no timeout(1) on PATH — a pathological seed will" >&2
  echo "                run until it is killed by hand" >&2
fi

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QC="$ROOT/agda/_oracle/_cli/QuickCheck"
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
#
# AND IT COVERS WHAT THE CORPUS ALREADY SPENDS, NOT ONLY WHAT THE GENERATOR
# CAN EMIT TODAY.  The corpus is APPEND-ONLY and the pruner reads the WHOLE
# file, so a name dropped from this block because the generator stopped
# emitting it is deleted from the import list of rows that still use it, and
# the corpus goes unscopeable on the next run of this script.  So the list
# is WIDER than the generator's palette on purpose, and a name leaves it
# only when the language it names has stopped having that former.
read -r -d '' WIDE_IMPORTS <<'AGDA' || true
open import Data.Bool using (true; false)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import Rx.SExp using (inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; mergeAllˢ;
  switchAllˢ; exhaustAllˢ; μˢ; varˢ; deferˢ;
  varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; inlˢ; inrˢ; caseˢ; ifˢ;
  primˢ; nilˢ; consˢ; foldˢ; strmˢ)

open import Rx.Prim using (hot; cold; after_,_)
open import Implementation.Unit-Test.Prelude using (Case; cached; mkSlots)
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
cen="$(mktemp)"
trap 'rm -f "$tmp" "$row" "$spl" "$cen"' EXIT

widen

added=0
timedout=""
for seed in $(seq "$FIRST" "$LAST"); do
  # stdin is: SEED RUNS DEPTH  (QuickCheck.agda's main: parseNat, numAt 1,
  # numAt 2 — runs before depth)
  if printf '%s %s %s\n' "$seed" "$RUNS" "$DEPTH" | $TIMEOUT "$QC" > "$tmp"
  then :; else
    rc=$?
    if [ "$rc" -eq 124 ]; then
      echo "seed $seed depth $DEPTH — TIMED OUT after ${SECS}s; not checked"
      timedout="$timedout $seed"
      continue
    fi
    echo "gen-unit-tests: seed $seed exited $rc" >&2
    exit "$rc"
  fi
  head -1 "$tmp"
  # one census line per run, banked for the aggregate below rather than
  # printed: per-seed counts are noise at 300 seeds, and the question the
  # census answers is about the SWEEP
  grep '^census ' "$tmp" >> "$cen" || true

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

# THE CENSUS, AGGREGATED ACROSS THE SWEEP.  The pairing check proves a former
# is GENERABLE -- every surface spells it and the generator has a lane -- and
# says nothing about whether any run generated one.  A former totalling ZERO
# here is the pairing's own silence one layer in: all four surfaces agree
# about it, the map is green, and no program carrying it has been run on
# either side.
#
# WRITTEN TO A FILE AND NOT MERELY PRINTED, because the verdict this script
# reports is the CORPUS and its exit status is 0 either way.  A second verdict
# read off scrollback is a verdict nothing reads, so the totals go somewhere a
# caller can fail on -- which is what the workflow's own step does.
CENSUS="$ROOT/agda/_cli/census.txt"
awk '{ for (i = 2; i < NF; i += 2) t[$i] += $(i + 1) }
     END { for (k in t) print k, t[k] }' "$cen" | sort > "$CENSUS"
echo "gen-unit-tests: census over seeds $FIRST..$LAST -> ${CENSUS#"$ROOT"/}"
awk '{ printf "  %-12s %s\n", $1, $2 }' "$CENSUS"

if [ -n "$timedout" ]; then
  echo "gen-unit-tests: TIMED OUT:$timedout"
  echo "                each of these seeds drew a program whose run does not"
  echo "                finish in ${SECS}s, so its whole batch is unchecked —"
  echo "                the census and the corpus below cover the rest."
fi

unreached="$(awk '$2 == 0 { printf "%s ", $1 }' "$CENSUS")"
if [ -n "$unreached" ]; then
  echo "gen-unit-tests: NEVER GENERATED: $unreached"
  echo "                the pairing proves these are generable; this sweep"
  echo "                shows nothing produced one, so no program carrying"
  echo "                them has been checked on either side."
fi

# UNCONDITIONAL, because `widen` ran unconditionally: a dead import is an
# `imports-check` failure, so leaving the wide form behind on a run that found
# nothing would break the gate for having found nothing.
( cd "$ROOT" && make --no-print-directory imports-fix >/dev/null )
echo "gen-unit-tests: pruned the corpus's imports"

# THE COUNT GOES TO A FILE, FOR THE REASON THE CENSUS DOES: a caller has to
# be able to fail on "the corpus grew", and this script's exit status is 0
# whether or not it found anything.
#
# AND A CALLER MUST NOT READ IT OFF `git diff`, WHICH IS WHAT THE WORKFLOW
# DID.  `widen` rewrites the import block from this script's own list and the
# prune above puts back only the live names -- in the WIDE list's order, not
# the committed file's.  So a sweep that found nothing still left the corpus
# textually changed, and the job went red reporting new rows under a diff
# that was one import list reordered.  A check whose subject is whether the
# corpus GREW reads the number this script computed, not a diff of a file it
# rewrites unconditionally.
printf '%s\n' "$added" > "$ROOT/agda/_cli/added.txt"
echo "gen-unit-tests: appended count -> agda/_cli/added.txt"

if [ "$added" -gt 0 ]; then
  echo "gen-unit-tests: now run 'make bug-cache' — it is green iff no known"
  echo "                counterexample remains, so it should fail until the"
  echo "                implementation is fixed."
fi
