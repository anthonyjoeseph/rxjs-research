.PHONY: all help agda bug-cache burst-probe cut-caches-probe hop-descent-probe frame-work-probe state-blowup-probe j-budget-probe fold-count-probe mint-loop-probe joint-probe eval-growth-probe ts-check cli-build oracle qc-build quickcheck

# UTF-8 locale for em-dashes and special characters in Agda output
export LC_ALL := C.UTF-8
export LANG := C.UTF-8

all: help

# ─────────────────────────────────────────────────────────────────────────
# The two differential-test workflows:
#
#   make oracle       rxjs (TS) vs the Agda oracle, per generated program
#   make quickcheck   impl- vs spec-batchSimultaneous, all in Agda
#
# Both accept arguments after ARGS=. See each target below for the exact syntax
# and seed examples. `make help` shows the descriptions.
# ─────────────────────────────────────────────────────────────────────────

help:
	@echo "Available targets:"
	@echo "  agda          typecheck the Agda source (src/Main.agda)"
	@echo "  bug-cache     typecheck the type-level bug cache (NOT reached by"
	@echo "                  src/Main.agda, so 'make agda' does not cover it —"
	@echo "                  green here <=> no known counterexample remains)"
	@echo "  burst-probe   measure the subscription bursts the evaluator mints:"
	@echo "                  frameFresh? on every burst, cross-emit opens, and"
	@echo "                  acc-matched closes (see agda/probe/Burst-Probe.agda)"
	@echo "                  make burst-probe                      (seed 1, 200, depth 4)"
	@echo "                  make burst-probe ARGS='1 25 200 4'    (seeds 1..25)"
	@echo "                  make burst-probe ARGS='1 1 20 4 4'    (corpus C₃ only)"
	@echo "                  NOTE: corpus B depth ≤ 4 only.  Depth 5 corpus B draws gas"
	@echo "                  proportional to def sizes (budgetAt = syncBudget sizeᵉ),"
	@echo "                  making each program ≫ 90 min per seed.  Corpora A, C,"
	@echo "                  and C₃ can be run at depth 5 without issue."
	@echo "  cut-caches-probe  the counterexample that cachesValid is not a burst"
	@echo "                  invariant: it fails BOTH ways across a merge inner's"
	@echo "                  subscribe (see agda/probe/Cut-Caches-Probe.agda)"
	@echo "  hop-descent-probe  the refutation that a burst's observable value"
	@echo "                  measures below its carrier — false at all three"
	@echo "                  sites (see agda/probe/Hop-Descent-Probe.agda)"
	@echo "  frame-work-probe  is a subscribe frame's work entry-determined?"
	@echo "                  refl-checked payload counts for the deepening scan"
	@echo "                  (see agda/probe/Frame-Work-Probe.agda).  SLOW (~30 min)"
	@echo "  state-blowup-probe  what does ONE instant do to the STORE?  reads"
	@echo "                  capsOK?'s own three quantities off a real run"
	@echo "                  (see agda/probe/State-Blowup-Probe.agda)"
	@echo "  j-budget-probe  is cWid * cReg enough ITERATIONS?  NO — and no count"
	@echo "                  of the Caps triple is, because chain length moves"
	@echo "                  while the triple stands still"
	@echo "                  (see agda/probe/J-Budget-Probe.agda)"
	@echo "  fold-count-probe  does one cascade's FOLD COUNT fit that count?  NO —"
	@echo "                  nested shares make deliveries exponential in the"
	@echo "                  number of shared slots while every Caps component"
	@echo "                  stays linear.  Then GATES the replacement,"
	@echo "                  2 ^ cReg * cSize, over four share shapes plus the"
	@echo "                  standing regression suite"
	@echo "                  (see agda/probe/Fold-Count-Probe.agda)"
	@echo "  mint-loop-probe  does the MINTING FEEDBACK LOOP close?  a scan under"
	@echo "                  a share whose step re-subscribes that share, nested"
	@echo "                  k deep, so a minted chain can itself mint.  NO — the"
	@echo "                  deliveries saturate in k on three ladders of four,"
	@echo "                  while 2 ^ cReg * cSize grows.  The fourth is still"
	@echo "                  climbing where it stops computing.  ~18 min, two files"
	@echo "  joint-probe   is subscribeE-caps's joint hypothesis, pathLen + size"
	@echo "                  <= cSize, true at the TIGHT admissible cSize?  NO — it"
	@echo "                  fails on every one of seventeen families, and the"
	@echo "                  half-cap chain watermark fails on the simplest of them"
	@echo "                  (see agda/probe/Joint-Probe.agda)"
	@echo "                  make joint-probe ARGS='0 80'   (the whole sweep)"
	@echo "  eval-growth-probe  what does ONE application cost?  refutes the"
	@echo "                  AFFINE reading of the five evaluation obligations"
	@echo "                  on all three axes — a closed term of size 6k+1"
	@echo "                  whose value has size 2^(k+1)-1, the same ladder as"
	@echo "                  a step function, and a mu whose unfolding's parked"
	@echo "                  width doubles per rung.  Then measures what DOES"
	@echo "                  pay: two or three j (see agda/probe/"
	@echo "                  Eval-Growth-Probe.agda).  Fast, ~1 min"
	@echo "  ts-check      typecheck the TypeScript source"
	@echo "  cli-build     compile the Agda differential-test CLI (agda/_cli/Main)"
	@echo "  oracle        generate programs, evaluate in rxjs and Agda, report diffs"
	@echo "                  make oracle                   (full seed sweep)"
	@echo "                  make oracle ARGS='--seed 1'   (ONE seed only)"
	@echo "                  make oracle ARGS='--operator mergeAll'"
	@echo "  qc-build      compile the all-Agda QuickCheck binary (agda/_cli/QuickCheck)"
	@echo "  quickcheck    all-Agda QuickCheck: impl- vs spec-batchSimultaneous"
	@echo "                  make quickcheck              (seeds 1..300, 200 runs each)"
	@echo "                  make quickcheck ARGS='42 42' (ONE seed, 200 runs, depth 4)"
	@echo "                  make quickcheck ARGS='1 500 300 5' (seeds 1..500, 300 runs, depth 5)"

agda:
	cd agda && agda src/Main.agda

# Implementation/Unit-Test.agda is deliberately not imported by Main (it is a
# throwaway performance cache, deleted once Formal-Verification is discharged),
# so nothing else in the build would ever notice it rotting.  This target is
# what makes its invariant enforceable rather than remembered.
bug-cache:
	cd agda && agda src/Implementation/Unit-Test.agda

# The probe needs an evaluator that records every subscription burst, and
# Verify-Well-Formed reduces the evaluator's clauses — so instrumenting it in
# place would break the proofs.  burst-probe.sh therefore instruments a COPY in
# a scratch project; agda/src is never written.  Not part of `make agda`: this
# measures the evaluator, it does not check it.
burst-probe:
	scripts/burst-probe.sh $(ARGS)

# Four refl-checked computations pinning down why BurstInv cannot carry
# cachesValid.  Standalone (it only computes on hand-built configurations), so
# it is not reached by src/Main.agda and needs its own target to stay honest.
cut-caches-probe:
	cd agda && agda -i src -i probe probe/Cut-Caches-Probe.agda

# The three absurd-pattern refutations of hop descent: an observable value
# carried by a burst does NOT measure below its carrier, because a template
# with two uses of its bound variable copies the plugged value's shells twice.
# Standalone (hand-built expressions only), so src/Main.agda never reaches it —
# and it must not rot, because it is the reason dBound's `r` is still open.
hop-descent-probe:
	cd agda && agda -i src -i probe probe/Hop-Descent-Probe.agda

# Is a subscribe frame's work entry-determined?  refl-checked payload counts
# for the deepening scan (an obs-typed accumulator that re-wraps itself), which
# is what licenses re-indexing hopD's scan clause off the store anchor.
# Standalone, so src/Main.agda never reaches it.  SLOW — prog₂ delivers 126
# payloads in one frame and the defer loop another 62; those numbers ARE the
# finding, so they are not shrunk.  ~30 min.
frame-work-probe:
	cd agda && agda -i src -i probe probe/Frame-Work-Probe.agda

# The gate for sizeBlowup and regBlowup — and, as it turned out, three
# refutations of round 4's other components.  It reads capsOK?'s own
# conjuncts (sizeᵛ, outWᵛ, the registry's length) off a real run, which
# needs the evaluator's STATE, so it re-runs the drain loop keeping
# Sched/EvalSt.  Standalone, so src/Main.agda never reaches it.
state-blowup-probe:
	cd agda && agda -i src -i probe probe/State-Blowup-Probe.agda

# The gate for frameBlowup's ITERATION COUNT, the one component round 4
# left unmeasured.  It refutes `cWid * cReg` — and, via a family whose
# caps triple is constant while its chain length grows, refutes every
# count computed from the triple alone.  Standalone, so src/Main.agda
# never reaches it.  The family stops at k = 4: every gate re-runs the
# evaluator, and k = 6 (a 4371-node store) OOMs a 16 GB box for no extra
# content — 15, 51, 159, 483 against a fixed (7, 1, 1) already says it.
j-budget-probe:
	cd agda && agda -i src -i probe probe/J-Budget-Probe.agda

# The gate for frameBlowup's ITERATION COUNT itself — the receipt
# cascadeGo-caps hands back, read off the evaluator's own `delivered`
# ledger.  It refutes `cWid * cReg * cSize` (nested shares deliver
# exponentially in the shared-slot count) and then gates the
# replacement, `2 ^ cReg * cSize`, against four share shapes and the
# standing regression suite.  Standalone, so src/Main.agda never reaches
# it.  SLOW — every assertion re-runs the evaluator, ~40 min.
fold-count-probe:
	cd agda && agda -i src -i probe probe/Fold-Count-Probe.agda

# The gate for the one crude spot in `2 ^ cReg * cSize`: shareAdmit reads the
# registry as of the dispatch, so a mid-cascade mint widens the branching of
# the cascade that minted it.  Fold-Count-Probe's family G sampled one rung of
# that loop; this closes it, and finds the deliveries SATURATE in the nesting
# depth while the budget keeps growing through cSize — on three ladders of
# four.  Standalone, so src/Main.agda never reaches it.  SLOW — every fold
# count re-runs the evaluator through a real cascade — and split in two
# because ONE wall over these families does not finish: it ran past fifty
# minutes and was killed.  Split, it is ~10 min plus ~8 min.
mint-loop-probe:
	cd agda && agda -i src -i probe probe/Mint-Loop-Shapes.agda
	cd agda && agda -i src -i probe probe/Mint-Loop-Probe.agda
	cd agda && agda -i src -i probe probe/Mint-Loop-Frames.agda

# The gate on repairing the caps tree's two blocked companions.
# subscribeE-caps hypothesises `pathLen κ + sizeᵉ b ≤ cSize` and the
# delivery side carries the two bounds SEPARATELY; before the ℓ ledger is
# threaded through four ground clauses and a state predicate, this
# measures whether the joint form is true at the tight admissible cSize.
# It is not — see the reading at the head of agda/probe/Joint-Probe.agda.
# Instruments a COPY of the evaluator (agda/src is never written).
#   make joint-probe                 (row 0)
#   make joint-probe ARGS='0 80'     (the whole sweep)
joint-probe:
	scripts/joint-probe.sh $(ARGS)

# The gate on the AFFINE-FIRST reading of the eval cluster — the probe
# that had to run before any of evalTms-caps / evalSeed-caps /
# unfoldμ-caps / mapFrame-caps / scanFrame-caps was ground.  It refutes
# affine on every axis the ruling named, and then measures the receipt
# that does pay (two or three j).  Hand-built syntax only, no evaluator
# state, so src/Main.agda never reaches it — and it must not rot, since
# it is the evidence behind whatever shape those five end up with.
eval-growth-probe:
	cd agda && agda -i src -i probe probe/Eval-Growth-Probe.agda

ts-check:
	cd typescript && npm run typecheck

cli-build:
	cd agda && agda --compile --compile-dir=_cli src/CLI/Main.agda

oracle: cli-build
	cd typescript && npm run oracle -- $(ARGS)

qc-build:
	cd agda && agda --compile --compile-dir=_cli src/QuickCheck.agda

quickcheck: qc-build
	scripts/gen-unit-tests.sh $(ARGS)
