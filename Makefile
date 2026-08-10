.PHONY: all help agda bug-cache unsafe-check wiring level-walk-probe nest-budget-probe nest-count-probe instant-height-probe joint-probe ts-check cli-build oracle qc-build quickcheck

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
	@echo "  agda          typecheck the Agda source (src/Main.agda) — this is"
	@echo "                  the CLAIM GRAPH: Main names individual claims, so"
	@echo "                  green here means every claim's support compiles"
	@echo "  bug-cache     typecheck the type-level bug cache (NOT reached by"
	@echo "                  src/Main.agda, so 'make agda' does not cover it —"
	@echo "                  green here <=> no known counterexample remains)"
	@echo "  unsafe-check  SOUNDNESS GUARD: the build is NOT --safe (it cannot be,"
	@echo "                  while postulates exist), so nothing stops an unsafe"
	@echo "                  pragma reaching the proof path.  This greps for them."
	@echo "                  Retires at the finish line, when 'agda --safe"
	@echo "                  src/Main.agda' checks postulates and pragmas at once"
	@echo "  wiring        the wiring-law report ('a comment is not a wire'):"
	@echo "                  every top-level definition/postulate in agda/src,"
	@echo "                  its consumer count, and the ledger of postulates"
	@echo "                  with vs without a real consumer.  A report for a"
	@echo "                  human to rule on, not a build gate — always exits"
	@echo "                  0 and deletes nothing (see scripts/check-wiring.py)"
	@echo "  wiring-gate   the same check, but EXITS 1 on a violation"
	@echo "  gate          the acceptance test: wiring-gate + unsafe-check +"
	@echo "                  agda + bug-cache, cheap checks first so"
	@echo "                  a 2-second failure never waits on a 40-minute one"
	@echo "  level-walk-probe  the EVOLVING-CAPS delivery walk, before it is"
	@echo "                  landed: the walk carries the level and reads the"
	@echo "                  registry off it, so nothing is charged at the"
	@echo "                  refuted entry caps.  Termination, the front"
	@echo "                  decomposition, monotonicity, and the gate — the"
	@echo "                  level walk is POINTWISE ABOVE the registry walk it"
	@echo "                  replaces (see agda/probe/Level-Walk-Probe.agda)"
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
	@echo "  joint-probe   is subscribeE-caps's joint hypothesis, pathLen + size"
	@echo "                  <= cSize, true at the TIGHT admissible cSize?  NO — it"
	@echo "                  fails on every one of seventeen families, and the"
	@echo "                  half-cap chain watermark fails on the simplest of them"
	@echo "                  (see agda/probe/Joint-Probe.agda)"
	@echo "                  make joint-probe ARGS='0 80'   (the whole sweep)"
	@echo "  nest-count-probe  is the WIDTH count a SYNTACTIC constant?  per"
	@echo "                  APPLICATION yes, exactly — per INSTANT no: the"
	@echo "                  same node folds once per DELIVERY and each fold"
	@echo "                  pays the nesting again, so the stories are"
	@echo "                  deliveries x nesting and the fan-out family"
	@echo "                  breaches at four deliveries"
	@echo "                  (see agda/probe/Nest-Count-Probe.agda).  Fast"
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

# SOUNDNESS GUARD.  The build is NOT `--safe` — `make agda` runs a plain
# `agda src/Main.agda`, there is no OPTIONS pragma in src/ and no flags in the
# .agda-lib — so nothing mechanically stops an unsafe pragma landing on the
# proof path.  `--safe` cannot be switched on while postulates exist (it rejects
# `postulate` as well as the pragmas), so until the endgame this grep IS the
# guard.  EXEMPT: src/QuickCheck.agda, a test harness Main does not import.
#
# At the finish line this target retires: once The-Proof.agda carries no
# postulates, `agda --safe src/Main.agda` checks both halves at once.
unsafe-check:
	@cd agda && hits=$$(grep -rn -E '\{-# *(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|REWRITE)' src/ \
	    --include='*.agda' | grep -v '^src/QuickCheck.agda:' || true); \
	  opts=$$(grep -rn -E '\{-# *OPTIONS.*(--type-in-type|--no-termination-check|--no-positivity-check|--rewriting)' src/ \
	    --include='*.agda' || true); \
	  if [ -n "$$hits$$opts" ]; then \
	    echo "UNSAFE PRAGMA ON THE PROOF PATH — this is a soundness hole, not a shortcut:"; \
	    echo "$$hits"; echo "$$opts"; exit 1; \
	  else \
	    echo "unsafe-check: clean (0 unsafe pragmas outside the documented QuickCheck.agda exemption)"; \
	  fi

# The wiring law's mechanised check (see CLAUDE.md, "the wiring law: a
# comment is not a wire").  Pure textual analysis of agda/src, no Agda
# invocation — always exits 0, this is a report for a human to rule on.
wiring:
	scripts/check-wiring.py

# The same check AS A GATE: exits 1 on a wiring-law violation (an orphan
# outside the exempt families, or a ⊤-typed postulate that asserts nothing).
wiring-gate:
	scripts/check-wiring.py --gate

# THE ACCEPTANCE TEST, cheap checks FIRST.  Ordering is the point: an orphan
# or an unsafe pragma is decidable in seconds by grep, while `agda` costs
# ~40 minutes — so there is no reason to spend the 40 minutes only to fail on
# something a textual pass already knew.  Fail fast, then typecheck.
gate:
	@$(MAKE) --no-print-directory wiring-gate
	@$(MAKE) --no-print-directory unsafe-check
	@$(MAKE) --no-print-directory agda
	@$(MAKE) --no-print-directory bug-cache
	@echo "gate: ALL GREEN"










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



# The instant sweep the charge form's V-coverage turns on: VMAX, WSTORE,
# SSTORE and the receipt-weighted j at instants 0 … 3 on nine families.
# It re-runs the evaluator once per instant per column, so the DEEP cells
# are read off the compiled harness (probe/Instant-Height-Main.agda) and
# recorded in the tables as measured-not-rechecked; this target checks the
# `refl` pins and the numeral gates written on them.  Standalone, so
# src/Main.agda never reaches it.  ~2.5 min
instant-height-probe:
	cd agda && agda -i src -i probe probe/Instant-Height-Probe.agda






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


# WHY A CONSTANT DEMAND LEDGER CANNOT BE WALKED.  The Delivery-Walk threads
# its ledger through every frame, so a `Vb` constant in the walk level asserts
# that EVERY frame preserves a fixed size bound.  `stepFrame` on `map-f fn` is
# `map (applyFn fn) vals`, and a duplicating `fn` roughly doubles `sizeᵛ`: at
# Dm = 1 a value of size 1 comes back at size 3.  All five hypotheses are met
# at `st-init` of a concrete program, so the refutation is not vacuous.  This
# is why the burst walk's ledger is CAPS-INDEXED (see caps-burst-walk-probe).
# Seconds.
demand-sfstep-absurd:
	cd agda && agda -i src -i probe probe/Demand-SfStep-Absurd.agda


# THE CORRECTED BURST WALK, rehearsed: a Walk-Hyps instantiation whose burst
# and event ledgers are CAPS-INDEXED (`burstCaps?`/`eventCaps?` at
# `frameStep J c`) rather than constant.  Vb/Pb/OK are `walkH`'s verbatim and
# every closure fact is proven; exactly one postulate is new, and only its
# events half is genuinely open — `FrameFace` bounds a frame's output VALUES
# and says nothing about its emitted EVENTS.  Seconds.
caps-burst-walk-probe:
	cd agda && agda -i src -i probe probe/Caps-Burst-Walk-Probe.agda
