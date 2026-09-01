#!/usr/bin/env bash
# Append newly-discovered QuickCheck counterexamples to the type-level bug
# cache under agda/src/Implementation/Unit-Test/.
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
# ONE MODULE PER CASE, which is what keeps the cache's cost flat.  A pin is a
# `refl` over a whole `evaluate` run and costs minutes; in one file every case
# is re-checked whenever any case is appended, so the gate's bill grows with
# the cache.  Agda's interface cache is per module, so a case in its own
# module is checked once and never again.  Unit-Test.agda is then the LEDGER:
# one import-and-pin block per case, and the anonymous pin is what gives the
# case module its reachability, since a MODULE_ROOTS file seeds from those.
#
# Invariant the cache exists to enforce: the cache fully typechecks
# <=> no known counterexample remains.  So after this appends anything,
# `make gate-heavy` is expected to FAIL until the implementation is fixed.
set -euo pipefail

FIRST=${1:-1}
LAST=${2:-300}
RUNS=${3:-200}
DEPTH=${4:-4}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QC="$ROOT/agda/_cli/QuickCheck"
LEDGER="$ROOT/agda/src/Implementation/Unit-Test.agda"
CASEDIR="$ROOT/agda/src/Implementation/Unit-Test"

[ -x "$QC" ]     || { echo "gen-unit-tests: no $QC — run 'make qc-build' first" >&2; exit 1; }
[ -f "$LEDGER" ] || { echo "gen-unit-tests: no $LEDGER" >&2; exit 1; }
[ -d "$CASEDIR" ] || { echo "gen-unit-tests: no $CASEDIR" >&2; exit 1; }

# THE IMPORT BLOCK EVERY CASE MODULE GETS, a superset of what any generated
# program can mention: nothing here knows which constructors a given program
# uses, so the block is written wide and `make imports-fix` prunes it at the
# end.  A dead import is an imports-check failure, so the prune is not
# optional and this script runs it rather than leaving it to be remembered.
read -r -d '' CASE_IMPORTS <<'AGDA' || true
open import Data.List using ([]; _∷_)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (after_,_; hot; cold)
open import Rx.Exp using (input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ;
  switchAllᵉ; exhaustAllᵉ; nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add; mul)
open import Rx.Slots using (scripted)
AGDA

# the binary prints em-dashes, and the pasted blocks are full of Agda's
# unicode identifiers — a C locale turns both into a commitBuffer crash
export LC_ALL="${LC_ALL:-C.UTF-8}"
export LANG="${LANG:-C.UTF-8}"

tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT

added=0
for seed in $(seq "$FIRST" "$LAST"); do
  # stdin is: SEED RUNS DEPTH  (QuickCheck.agda's main: parseNat, numAt 1,
  # numAt 2 — runs before depth)
  printf '%s %s %s\n' "$seed" "$RUNS" "$DEPTH" | "$QC" > "$tmp"
  head -1 "$tmp"

  nblocks="$(grep -c '^-- <<<PASTE$' "$tmp" || true)"
  [ "${nblocks:-0}" -eq 0 ] && continue

  for k in $(seq 1 "$nblocks"); do
    block="$(awk -v want="$k" '
      /^-- <<<PASTE$/ { n++; if (n == want) inb = 1; next }
      /^-- PASTE>>>$/ { if (inb) exit; next }
      inb             { print }
    ' "$tmp")"

    # line 2 is the program; for a WellFormedOutput block it carries the
    # {- WF -} prefix, which keeps its key distinct from the Agree block
    # of the very same program
    key="$(printf '%s\n' "$block" | sed -n '2p')"
    if grep -Fqxr -- "$key" "$CASEDIR"; then
      continue
    fi

    # WHICH OF THE TWO SHAPES this is, read off the block's own statement
    # rather than guessed: both live in Unit-Test/Prelude.agda, and the pin's
    # name is what the ledger will claim.
    case "$(printf '%s\n' "$block" | sed -n '1p')" in
      *Agree*)             stmt=Agree;             pfx=agree ;;
      *WellFormedOutput*)  stmt=WellFormedOutput;  pfx=wf ;;
      *) echo "gen-unit-tests: seed $seed block $k names no known statement" >&2; exit 1 ;;
    esac

    # one seed can yield several blocks, and two seeds can find the same
    # shape, so the module name is disambiguated rather than assumed unique
    suffix="$seed"; n=1
    while [ -e "$CASEDIR/Case-$suffix.agda" ]; do
      n=$((n + 1)); suffix="$seed-$n"
    done
    mod="Case-$suffix"; pin="$pfx-$suffix"

    {
      printf -- '-- One cached counterexample, seed %s.  Appended by\n' "$seed"
      printf -- '-- `scripts/gen-unit-tests.sh`; the pin is what makes it a guard.\n'
      printf -- 'module Implementation.Unit-Test.%s where\n\n' "$mod"
      printf '%s\n\n' "$CASE_IMPORTS"
      printf -- 'open import Implementation.Unit-Test.Prelude using (%s)\n\n' "$stmt"
      printf '%s\n' "$block" \
        | sed "1s/^_ :/$pin :/; \$s/^_ = refl/$pin = refl/"
    } > "$CASEDIR/$mod.agda"

    {
      printf -- '\nopen import Implementation.Unit-Test.%s using (%s)\n' "$mod" "$pin"
      printf -- '_ : _\n_ = %s\n' "$pin"
    } >> "$LEDGER"

    added=$((added + 1))
    echo "  + cached a new counterexample (seed $seed) as $mod"
  done
done

echo "gen-unit-tests: appended $added new case module(s) to ${CASEDIR#"$ROOT"/}"
if [ "$added" -gt 0 ]; then
  # the import block above is deliberately wide, so pruning is owed
  ( cd "$ROOT" && make --no-print-directory imports-fix >/dev/null )
  echo "gen-unit-tests: pruned the new modules' imports"
  echo "gen-unit-tests: now run 'make gate-heavy' — the cache is green iff no"
  echo "                known counterexample remains, so it should fail"
  echo "                until the implementation is fixed."
fi
