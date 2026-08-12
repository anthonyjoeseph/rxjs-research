.PHONY: all help agda agda-dev agda-dev-selftest bug-cache unsafe-check wiring ts-check cli-build oracle qc-build quickcheck

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
	@echo "  agda-dev      THE FAST DEV LOOP: check one mutual-block member at a"
	@echo "                  time against its siblings POSTULATED at their exact"
	@echo "                  signatures.  Subscribe-Face 11s, Wet 17s, one member"
	@echo "                  ~6s — against 927s and 908s for the real modules."
	@echo "                  DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF"
	@echo "                  IS VALID: the real recursion's TERMINATION is not"
	@echo "                  checked, and postulates do not reduce.  'make agda'"
	@echo "                  stays the merge gate"
	@echo "                  make agda-dev                    (all dirty modules)"
	@echo "                  make agda-dev ARGS='Verify-Budget-Sufficient/Wet.agda'"
	@echo "                  make agda-dev ARGS='<file> <member>'   (the grind loop)"
	@echo "                  make agda-dev ARGS='--list <file>'    (block structure)"
	@echo "                  SCOPE=1 scope-check only; HOLES=1 tolerate ? holes"
	@echo "  agda-dev-selftest  falsification test for agda-dev: corrupt a real"
	@echo "                  body in src, demand the fast check goes RED, restore."
	@echo "                  Run whenever the stubbing logic changes"
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

# THE FAST DEV LOOP.  86-91% of `make agda` is Agda's occurrence/polarity pass
# over two big mutual blocks, and no flag or pragma touches it (three routes
# measured and closed; the record is scripts/agda-dev.py's docstring).  What it IS
# sensitive to is mutual-block MEMBERSHIP, steeply: one real body in
# Subscribe-Face's block costs 63ms of Positivity, fifteen cost 300s.  So this
# checks ONE body at a time, against its siblings POSTULATED at their exact
# existing signatures.  agda/src is never written to.
#
#   make agda-dev                     every module dirtier than its interface
#   make agda-dev ARGS='<file>'       one module, every member
#   make agda-dev ARGS='<file> <member>'   one member — the actual grind loop
#   make agda-dev ARGS='--list <file>'     its mutual-block structure
#
# Measured warm: Subscribe-Face 11.3s (against 927s), Wet 17.0s (against 908s),
# one member ~6s.  OPT-IN flags: SCOPE=1 (names and syntax only, no
# typechecking), HOLES=1 (tolerate ? holes and missing clauses).
#
# DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID.  Two things
# are given up and the first is not minor: TERMINATION of the real mutual
# recursion is not checked (and in this proof the mutual recursion IS the
# induction), and postulates do not REDUCE.  `make agda` stays the merge gate.
# BUDGETS ARE ENFORCED, NOT DOCUMENTED (Anthony, 2026-08-11): 30s for one file,
# 180s for the whole project.  A loop that quietly drifts to two minutes has
# stopped being a loop, and a number that lives only in a comment is a number
# nobody maintains.  Exceeding the budget FAILS, with the usual causes printed.
# Override deliberately with BUDGET=<seconds> when the work has genuinely grown.
AGDA_DEV_BUDGET ?= $(if $(ARGS),30,180)
agda-dev:
	scripts/agda-dev.py --budget $(if $(BUDGET),$(BUDGET),$(AGDA_DEV_BUDGET)) \
	  $(if $(SCOPE),--scope) $(if $(HOLES),--holes) $(ARGS)

# Is the fast loop load-bearing, or green by construction?  Corrupts one token
# in a real body in src, demands the dev check go RED, and restores the file
# byte-for-byte.  RUN THIS WHENEVER THE STUBBING LOGIC CHANGES: a generator bug
# that silently dropped the focus body would otherwise read as a very fast pass.
agda-dev-selftest:
	scripts/agda-dev.py --falsify $(ARGS)

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

