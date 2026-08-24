#!/usr/bin/env bash
# Append newly-discovered QuickCheck counterexamples to the type-level bug
# cache, agda/src/Implementation/Unit-Test.agda.
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
# Invariant the cache exists to enforce: Unit-Test.agda fully typechecks
# <=> no known counterexample remains.  So after this appends anything,
# `make gate-heavy` is expected to FAIL until the implementation is fixed.
set -euo pipefail

FIRST=${1:-1}
LAST=${2:-300}
RUNS=${3:-200}
DEPTH=${4:-4}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QC="$ROOT/agda/_cli/QuickCheck"
CACHE="$ROOT/agda/src/Implementation/Unit-Test.agda"

[ -x "$QC" ]    || { echo "gen-unit-tests: no $QC — run 'make qc-build' first" >&2; exit 1; }
[ -f "$CACHE" ] || { echo "gen-unit-tests: no $CACHE" >&2; exit 1; }

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
    if grep -Fqx "$key" "$CACHE"; then
      continue
    fi

    { printf '\n-- seed %s\n' "$seed"; printf '%s\n' "$block"; } >> "$CACHE"
    added=$((added + 1))
    echo "  + cached a new counterexample (seed $seed)"
  done
done

echo "gen-unit-tests: appended $added new case(s) to ${CACHE#"$ROOT"/}"
if [ "$added" -gt 0 ]; then
  echo "gen-unit-tests: now run 'make gate-heavy' — the cache is green iff no"
  echo "                known counterexample remains, so it should fail"
  echo "                until the implementation is fixed."
fi
