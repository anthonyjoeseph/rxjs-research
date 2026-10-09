#!/bin/bash
# THE WALK SWEEP OVER A SEED RANGE: `make walk`'s body.  Runs the walk binary
# once per seed under its own time budget, so a seed whose draw is slow costs
# that seed (reported OVER BUDGET, its tallies lost) and not the sweep, and
# sums the per-tag tallies.  Exits 1 on any failure outside `control`, and
# also when `control` failed nowhere: a sweep whose control holds reached
# nothing.
#   walk-sweep.sh BIN "SEED RUNS DEPTH [FUEL]" SEEDS BUDGET DRAW
set -u
BIN=$1; set -- $2 "${@:3}"
SEED=$1; RUNS=$2; DEPTH=$3
if [ $# -ge 7 ]; then FUEL=$4; shift 4; else FUEL=0; shift 3; fi
SEEDS=$1; BUDGET=$2; DRAW=$3
for ((s = SEED; s < SEED + SEEDS; s++)); do
  printf '%s %s %s %s\n%s\n' "$s" "$RUNS" "$DEPTH" "$FUEL" "$DRAW" | timeout "$BUDGET" "$BIN" \
    || echo "seed $s OVER BUDGET"
done | awk '
/^[a-z]+ checked/ { k[$1] += $3; c[$1] += $5; f[$1] += $7; seen[$1] = 1 }
/first failure/ && !/control/ { print; show = 1; next }
show && /^      / { print; next }
{ show = 0 }
/OVER BUDGET/ { print; over++ }
/^restriction/ { print; exit 2 }
END {
  for (t in seen) printf "%s checked %d counted %d failed %d\n", t, k[t], c[t], f[t]
  if (over) printf "over budget: %d seed(s)\n", over
  bad = 0; for (t in seen) if (t != "control" && f[t] > 0) bad = 1
  if (bad) { print "walk: RED"; exit 1 }
  if (!f["control"]) { print "walk: control never failed -- the sweep reached nothing"; exit 1 }
  print "walk: GREEN"
}'
