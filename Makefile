.PHONY: all help agda bug-cache entry-caps-refuted level-walk-probe sub-charge-probe nest-budget-probe refresh-probe frame-mint-probe nest-count-probe instant-height-probe visited-width-probe mult-width-probe burst-probe cut-caches-probe hop-descent-probe frame-work-probe state-blowup-probe j-budget-probe fold-count-probe mint-loop-probe joint-probe eval-growth-probe width-count-probe charge-probe chain-half-probe share-count-probe ts-check cli-build oracle qc-build quickcheck

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
	@echo "  entry-caps-refuted  the refutation of stepFrame-entry-caps: one"
	@echo "                  map-f frame whose OUTPUT payload breaches the entry"
	@echo "                  cap it was charged at, so cascadeGo-deliveries is"
	@echo "                  not a theorem.  Carries the Leg-0 width lemma too"
	@echo "                  (see agda/probe/Entry-Caps-Refuted.agda).  seconds"
	@echo "  level-walk-probe  the EVOLVING-CAPS delivery walk, before it is"
	@echo "                  landed: the walk carries the level and reads the"
	@echo "                  registry off it, so nothing is charged at the"
	@echo "                  refuted entry caps.  Termination, the front"
	@echo "                  decomposition, monotonicity, and the gate — the"
	@echo "                  level walk is POINTWISE ABOVE the registry walk it"
	@echo "                  replaces (see agda/probe/Level-Walk-Probe.agda)"
	@echo "  sub-charge-probe  what does ONE SUBSCRIBE cost?  the clause table off"
	@echo "                  the ground companion tree, and the finding that the"
	@echo "                  subscribe charge is MUTUALLY RECURSIVE with the frame"
	@echo "                  charge (a frame subscribes one inner per payload; that"
	@echo "                  subscribe runs frames of its own), so no closed form in"
	@echo "                  (S,W,J) closes it.  Carries the nesting-indexed hierarchy"
	@echo "                  Rx.Evaluator now runs on: termination, inflation,"
	@echo "                  monotonicity in all five arguments, domination of the old"
	@echo "                  fLvl — and the COMPOSITION GATE, one lemma per clause"
	@echo "                  shape, which is what fixed the shape (the first draft"
	@echo "                  admitted none of the four)"
	@echo "                  (see agda/probe/Sub-Charge-Probe.agda).  Seconds"
	@echo "  nest-budget-probe  may the SUBSCRIBE-NESTING budget k be read off"
	@echo "                  the SIZE CAP?  NO.  Carries the lemma the signature"
	@echo "                  pass owes (nest <= size, proven, on values and both"
	@echo "                  syntactic halves) and the (b)-conjunct arithmetic the"
	@echo "                  two *All faces wait on (n^2 <= 2^n + 1, tight at 3)."
	@echo "                  Then refutes the descent the budget was ruled on: a"
	@echo "                  scan under an *All MINTS a payload per fold and the"
	@echo "                  k-th mint nests k deep, from syntax whose own nesting"
	@echo "                  stands still at 2 — so the budget is charged at the"
	@echo "                  frame's ENTRY level while its payloads are bounded at"
	@echo "                  the level it CLIMBED TO (3 against 43690)"
	@echo "                  (see agda/probe/Nest-Budget-Probe.agda).  Seconds"
	@echo "  refresh-probe   does the PER-FRAME BUDGET REFRESH close it?  HALF."
	@echo "                  The soundness side passes as a THEOREM (a frame"
	@echo "                  subscribes only its own arriving values and a concat"
	@echo "                  queue filled at a LOWER level, so nest <= size <= what"
	@echo "                  that frame itself admits — no row can breach it).  The"
	@echo "                  TERMINATION side fails: the refresh regenerates the"
	@echo "                  one descending argument LARGER and Agda"
	@echo "                  rejects the block.  Carries the repair — the refresh"
	@echo "                  with a DEPTH FUEL the frame entry spends — inflation,"
	@echo "                  monotonicity, fLvl <= it, the old family <= it, and"
	@echo "                  the four composition-gate steps re-proven; then names"
	@echo "                  the one number still unruled: what the fuel is set to"
	@echo "                  (see agda/probe/Refresh-Probe.agda).  Seconds"
	@echo "  frame-mint-probe  what does ONE stepFrame mint, and how wide is the"
	@echo "                  burst it is handed?  the per-FRAME maxima the two"
	@echo "                  entry axioms bound.  Mints are 1 on every row of the"
	@echo "                  amplifier family (against a cSize floor of 3-18); the"
	@echo "                  frame WIDTH climbs across arrivals, 6 to 120"
	@echo "                  (see agda/probe/Frame-Mint-Probe.agda).  ~4 min"
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
	@echo "  nest-count-probe  is the WIDTH count a SYNTACTIC constant?  per"
	@echo "                  APPLICATION yes, exactly — per INSTANT no: the"
	@echo "                  same node folds once per DELIVERY and each fold"
	@echo "                  pays the nesting again, so the stories are"
	@echo "                  deliveries x nesting and the fan-out family"
	@echo "                  breaches at four deliveries"
	@echo "                  (see agda/probe/Nest-Count-Probe.agda).  Fast"
	@echo "  width-count-probe  the refutation that the COUNT may read cWid:""
	@echo "                  one fold exponentiates a width, so j folds put it"
	@echo "                  under a tower of height j — a count with a cWid"
	@echo "                  summand iterates the tower per instant and"
	@echo "                  capsAt-tower's linear height is gone.  Also gates"
	@echo "                  the 2-tower delivery bound against every measured"
	@echo "                  ladder and prices the root margin against the"
	@echo "                  slope (see agda/probe/Width-Count-Probe.agda)"
	@echo "  mult-width-probe  prices the MULTIPLICATIVE width engine before"
	@echo "                  it is built: the joint tower slope of a count that"
	@echo "                  READS cWid (four stories, so budgetAt does not"
	@echo "                  move), the exchange rate against the exponential"
	@echo "                  step (one exponential fold IS suc w multiplicative"
	@echo "                  ones), and the BASE, where the whole root-fuel"
	@echo "                  margin goes (see agda/probe/Mult-Width-Probe.agda)"
	@echo "                  Fast, ~15 s"
	@echo "  visited-width-probe  the ruling off slot-fuel-probe, measured:"
	@echo "                  the slot descent drops VISITED slots instead of"
	@echo "                  spending fuel, so a revisit contributes zero."
	@echo "                  The 2-cycle's four tower stories collapse to a"
	@echo "                  fixed point; acyclic telescopes agree by refl;"
	@echo "                  the base height fits 3 + 2*sz (16 against 689"
	@echo "                  where the fuel form demanded 792)"
	@echo "                  (see agda/probe/Visited-Width-Probe.agda).  Fast"
	@echo "  charge-probe  does one cascade's j fit D * cSize?  NO - the"
	@echo "                  receipt-weighted j breaches it on the deepening"
	@echo "                  scan, and twice over when a second scan sits"
	@echo "                  DOWNSTREAM of the amplifier (47 against 20).  The"
	@echo "                  mint ladders all fit: the corner that breaks it"
	@echo "                  has FEW deliveries and WIDE payloads"
	@echo "                  (see agda/probe/Charge-Probe.agda).  ~2 min"
	@echo "  instant-height-probe  how fast do the STORE's two axes climb"
	@echo "                  ACROSS INSTANTS, and does the receipt's payload"
	@echo "                  width V stay under what the PREVIOUS instant"
	@echo "                  stored?  Nine families, four instants each where"
	@echo "                  the container reaches them.  REAL WIDTH CLIMBS"
	@echo "                  MORE THAN ONE STORY PER INSTANT (932 digits"
	@echo "                  against 926 on the deepening scan), and V exceeds"
	@echo "                  the stored width once (2 against 1).  The"
	@echo "                  receipt-dictated charge fits every measured row"
	@echo "                  (see agda/probe/Instant-Height-Probe.agda).  ~2.5 min"
	@echo "  chain-half-probe  the counterexample that a FIXED cap cannot"
	@echo "                  survive a subscribe: at C = 5, a tight chain and a"
	@echo "                  two-shell expression register a chain of length"
	@echo "                  six.  This is why regsSz?-subscribeE is not in the"
	@echo "                  tree (see agda/probe/Chain-Half-Probe.agda)"
	@echo "  share-count-probe  the refutation of an ENTRY-LEVEL bound on a"
	@echo "                  subscribe burst's EMIT COUNT: sharedConnect"
	@echo "                  prepends one envelope per connect, so a k-deep"
	@echo "                  share ladder is k+1 emits while every entry"
	@echo "                  hypothesis stays fixed.  The count has to ride"
	@echo "                  subscribeE-caps's EXISTENTIAL, at the exit level"
	@echo "                  (see agda/probe/Share-Count-Probe.agda).  ~10 s"
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

# The REFUTATION of those two frame-local axioms: a machine-checked
# Entry-Caps -> bottom on one map-f frame, plus the Leg-0 width lemma
# (cWid at cascade (suc id)'s entry is at least a two-rung tower, 1024,
# against the measured per-frame payload count of 120).  Seconds.
entry-caps-refuted:
	cd agda && agda -i src -i probe probe/Entry-Caps-Refuted.agda

# The EVOLVING-CAPS delivery walk, probed before it is landed: the walk
# carries the caps record and grows it per delivery, so the registry a
# dispatch sees is read off the LEVEL (capsOK?'s own fifth conjunct)
# rather than off a per-delivery mint budget charged at the refuted
# entry caps.  Termination, the front decomposition, monotonicity, and
# the GATE — the level walk is POINTWISE ABOVE the registry walk it
# replaces, so no measured D row has to be re-run.  Self-contained
# arithmetic, so src/Main.agda never reaches it.  Seconds.
level-walk-probe:
	cd agda && agda -i src -i probe probe/Level-Walk-Probe.agda

# What does ONE SUBSCRIBE cost?  The two remaining *All frame faces and
# .Wet's GAP (a) all wait on `subscribeE-caps`'s j′, which is an unbounded
# existential.  This reads the clause table off the ground companion tree and
# finds the shape the receipts compose in: the subscribe charge is MUTUALLY
# RECURSIVE with the frame charge, so the ruled candidate (~2·sizeAt, one
# receipt per operator) is too small and no closed form in (S,W,J) closes the
# loop.  Carries the nesting-indexed hierarchy Rx.Evaluator now runs on —
# termination, inflation, monotonicity in all five arguments, and the gate that
# it dominates the old `fLvl` pointwise at every nesting budget, which is what
# makes the rewiring cost no re-derivation above the frame — plus the
# COMPOSITION GATE (§ 5), one lemma per clause SHAPE of the ground tree, proven
# against the receipts as abstract numbers.  That gate is what fixed the shape:
# the first draft terminated and was monotone and admitted none of the four.
# Self-contained arithmetic on top of Level-Walk-Probe's copies, so
# src/Main.agda never reaches it.  Seconds.
sub-charge-probe:
	cd agda && agda -i src -i probe probe/Sub-Charge-Probe.agda

# May the SUBSCRIBE-NESTING budget `k` be read off the SIZE CAP, as the
# standing ruling instantiates it (fLvl′ S W J = fLvlK S W (suc (sizeAt S J)) J)?
# NO.  The probe carries the one non-arithmetic lemma the signature pass owes —
# nestᵛ ≤ sizeᵛ, proven, beside the other value measures — and the (b)-conjunct
# arithmetic the two *All faces wait on, and then refutes the DESCENT the budget
# was ruled on: a `scanᵉ` under an *All mints a payload per fold, the k-th mint
# nests k deep (real `applyFn`, refl-checked), and the carrier's own nesting
# stands still at 2.  So the budget is charged at the frame's ENTRY level while
# the values its payload subscribes are handed are bounded only at the level the
# frame has CLIMBED TO — the Entry-Caps-Refuted distinction, one stratum in.
# Standalone, so src/Main.agda never reaches it.  Seconds
nest-budget-probe:
	cd agda && agda -i src -i probe probe/Nest-Budget-Probe.agda

# Does the PER-FRAME BUDGET REFRESH close the hole Nest-Budget-Probe opened?
# HALF.  The SOUNDNESS side passes as a theorem — a frame subscribes only its
# own arriving values and the values a concat frame queued at a LOWER level, so
# nestᵛ ≤ sizeᵛ ≤ the frame's own size admission, no row can breach it.  The
# TERMINATION side fails: taken literally the refresh regenerates the family's
# only descending argument LARGER, and Agda rejects the whole mutual block.  So
# the probe carries the repair — the refresh with an explicit DEPTH FUEL the
# frame entry spends — proven inflationary, monotone in all five arguments,
# above `fLvl` and above the family it replaces, with the four composition-gate
# steps re-proven, and names the one number still unruled: what that fuel is
# instantiated at.  Standalone, so src/Main.agda never reaches it.  Seconds
refresh-probe:
	cd agda && agda -i src -i probe probe/Refresh-Probe.agda

# The gate on the two frame-local axioms cascadeGo-deliveries WAS proven
# from.  Mint-Loop-Frames reports mints and frames per CASCADE; these are
# the per-FRAME MAXIMA, which is what stepFrame-entry-mint and
# stepFrame-entry-caps bounded before Entry-Caps-Refuted killed them.
# Same mirror walk, same real stepFrame, ~4 min.
frame-mint-probe:
	cd agda && agda -i src -i probe probe/Frame-Mint-Probe.agda

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

# The refutation of a count that READS cWid.  One fold exponentiates a
# width, so j folds put the width under a TOWER OF HEIGHT j — hence a
# count with a cWid summand iterates the tower function once per
# instant and capsAt-tower's linear height is gone, taking
# caps-fuel-root with it.  Also gates the 2-tower delivery bound
# `2 ^ (2 ^ cReg)` against every measured ladder, and prices the root
# margin as a function of the per-instant slope.  Arithmetic on the
# recurrence alone, so src/Main.agda never reaches it.  Fast, ~10 s
width-count-probe:
	cd agda && agda -i src -i probe probe/Width-Count-Probe.agda

# Is the WIDTH count a SYNTACTIC constant?  The split-count ruling gives the
# width axis `suc (nestᵉ + slotsNest)` foldStep passes per instant, on
# Mult-Width-Probe §7's price for ONE applyFn.  Per APPLICATION that holds
# exactly (the fn2 ticker climbs two stories an instant, four instants).  Per
# INSTANT it fails: the same node folds once per DELIVERY and each fold pays
# the nesting again, so the stories are deliveries × nesting and the fan-out
# family breaches at four deliveries.  Standalone, so src/Main.agda never
# reaches it
nest-count-probe:
	cd agda && agda -i src -i probe probe/Nest-Count-Probe.agda

# The refutation of `cascadeGo-charge` as stated.  It mirrors foldPath /
# dispatchShare / shareGo / cascadeGo with the RECEIPT stepFrame-caps
# reports at each frame threaded in place of the emit stream, so the
# number it returns is a LOWER BOUND on the conjunct's own j — and it
# breaks `j <= D * cSize` on the deepening scan.  Standalone, so
# src/Main.agda never reaches it.  ~2 min
charge-probe:
	cd agda && agda -i src -i probe probe/Charge-Probe.agda

# The price of the MULTIPLICATIVE width engine, paid before the engine is
# built.  Arithmetic on the recurrence alone: the joint tower slope with a
# count that READS cWid (four stories on all three axes, so budgetAt's
# (7+sz)(id+2) does not move), the exchange rate against the exponential
# foldStep, and the base-height accounting — which is where the root fuel's
# whole margin turns out to go.  Standalone, so src/Main.agda never reaches
# it.  Fast, ~15 s
mult-width-probe:
	cd agda && agda -i src -i probe probe/Mult-Width-Probe.agda

# The ruling Slot-Fuel-Probe prices out, measured before it is ground in:
# the slot descent stops spending generic fuel and starts DROPPING
# VISITED SLOTS, so a revisit contributes ZERO (share-connect-no-replay).
# On that probe's own 2-cycle the fuel measure's four tower stories
# collapse to a FIXED POINT after two shared entries, and on any ACYCLIC
# telescope the two descents are equal by refl — which confines the
# soundness question to telescopes with a slot cycle.  The base-height
# row that refuted `3 + 2 * sz` is re-run and fits: 16 against 689 where
# the fuel form demanded 792.  Standalone, so src/Main.agda never
# reaches it.  Fast.
visited-width-probe:
	cd agda && agda -i src -i probe probe/Visited-Width-Probe.agda

# The instant sweep the charge form's V-coverage turns on: VMAX, WSTORE,
# SSTORE and the receipt-weighted j at instants 0 … 3 on nine families.
# It re-runs the evaluator once per instant per column, so the DEEP cells
# are read off the compiled harness (probe/Instant-Height-Main.agda) and
# recorded in the tables as measured-not-rechecked; this target checks the
# `refl` pins and the numeral gates written on them.  Standalone, so
# src/Main.agda never reaches it.  ~2.5 min
instant-height-probe:
	cd agda && agda -i src -i probe probe/Instant-Height-Probe.agda

# The counterexample that killed regsSz?-subscribeE: a FIXED cap cannot
# survive a subscribe, because subscribeE pushes one frame per shell of
# what it walks and the hypothesis buys room for exactly one.  One
# hand-built configuration, run through the real subscribeE, so
# src/Main.agda never reaches it — and it must not rot, because it is
# the whole reason that postulate is not in the tree.
chain-half-probe:
	cd agda && agda -i src -i probe probe/Chain-Half-Probe.agda

# At WHICH LEVEL is a subscribe burst's EMIT COUNT bounded?  Not the entry
# level: every subscribeE clause is emit-for-emit except sharedConnect,
# which PREPENDS its own init envelope onto the def's whole burst, so a
# ladder of k shares hands back k+1 emits — and nothing in the entry
# hypotheses bounds k, since slotsCaps? reads each def POINTWISE and a
# ladder keeps every pointwise number at 1.  Two rows, three shares and
# four, every hypothesis by refl at the same caps 2 1 1, both yielding ⊥.
# The exit level is fine and is the repair: sharedConnect-caps reports one
# fold PER CONNECT, so the count belongs in subscribeE-caps's existential.
share-count-probe:
	cd agda && agda -i src -i probe probe/Share-Count-Probe.agda

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
