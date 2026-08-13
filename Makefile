.PHONY: all help agda agda-dev agda-dev-selftest bg bg-check bug-cache unsafe-check wiring ts-check cli-build oracle qc-build quickcheck harness harness-build

# UTF-8 locale for em-dashes and special characters in Agda output
export LC_ALL := C.UTF-8
export LANG := C.UTF-8

# ─────────────────────────────────────────────────────────────────────────
# THE AGDA INVOCATION — ONE DEFINITION, USED BY EVERY TARGET, AND BY
# scripts/agda-dev.py.  NEVER call bare `agda` in this file.
#
# `-W error` PROMOTES EVERY WARNING TO AN ERROR, and it is here because a
# warning that costs nothing gets ignored: a `RewritesNothing` sat on every
# single build for weeks, printed twice per run, and nobody stopped, because
# the build was green and the warning was free.  A dead `rewrite` is a proof
# step doing nothing — cheap to fix, and exactly the kind of rot that hides a
# real one later.  Agda exits 42 on a promoted warning; green now means
# warning-free.
#
# ⚠ THE FLAG MUST MATCH scripts/agda-dev.py's `agda_flags()` EXACTLY.  Agda
# records the WARNING MODE in an interface's validity key, so a target running
# with a different -W than the dev loop invalidates the whole cone on EVERY
# alternation — measured 2026-08-11 at 120 modules rebuilt per switch, with
# the cost landing on whatever module happened to be next and each tool
# blaming the other.  Change one, change both, in the same commit.
# ─────────────────────────────────────────────────────────────────────────
AGDA := agda -W error

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
	@echo "                  signatures.  ONE MEMBER AT A TIME — the grind loop"
	@echo "                  DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF"
	@echo "                  IS VALID, wherever a block was stubbed: the real"
	@echo "                  recursion's TERMINATION is not checked and postulates"
	@echo "                  do not reduce.  Modules with no multi-member block"
	@echo "                  are checked verbatim.  'make agda' is the merge gate"
	@echo "                  NO whole-project sweep: measured out as costlier"
	@echo "                  than 'make gate' at lower fidelity"
	@echo "                  make agda-dev ARGS='Verify-Budget-Sufficient/Wet/Part2.agda'"
	@echo "                  make agda-dev ARGS='<file> <member>'   (the grind loop)"
	@echo "                  make agda-dev ARGS='--list <file>'    (block structure)"
	@echo "                  SCOPE=1 scope-check only; HOLES=1 tolerate ? holes"
	@echo "  agda-dev-selftest  falsification test for agda-dev: corrupt a real"
	@echo "                  body in src, demand the fast check goes RED, restore."
	@echo "                  Run whenever the stubbing logic changes"
	@echo "  bug-cache     typecheck the type-level bug cache + the demand-probe rows"
	@echo "                  (NOT reached by src/Main.agda, so 'make agda' does not"
	@echo "                  cover them — green here <=> no known counterexample remains)"
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
	@echo "                  a 2-second failure never waits on the 13-minute one"
	@echo "  bg            RUN EVERY LONG BUILD THROUGH THIS.  ALWAYS EXITS 7,"
	@echo "                  green or red — a launcher status that is right most"
	@echo "                  of the time gets believed, so this one is never"
	@echo "                  right.  It cannot report a false green because it"
	@echo "                  cannot report anything.  Ask bg-check instead"
	@echo "                  make bg T=agda   /   make bg T=gate LOG=/tmp/g.log"
	@echo "  bg-check      THE VERDICT of a detached run: GREEN, RED + failing"
	@echo "                  tail, or STILL RUNNING (exit 3 — not a pass)"
	@echo "                  make bg-check T=agda"
	@echo "  ts-check      typecheck the TypeScript source"
	@echo "  cli-build     compile the Agda differential-test CLI (agda/_cli/Main)"
	@echo "  oracle        generate programs, evaluate in rxjs and Agda, report diffs"
	@echo "                  make oracle                   (full seed sweep)"
	@echo "                  make oracle ARGS='--seed 1'   (ONE seed only)"
	@echo "                  make oracle ARGS='--operator mergeAll'"
	@echo "  harness       THE COMPILED MEASUREMENT HARNESS: read a number off"
	@echo "                  the machine's own arithmetic via the GHC backend,"
	@echo "                  which runs the same definitions and IGNORES"
	@echo "                  'abstract' (opacity is a typechecking contract,"
	@echo "                  not a runtime one).  For rungs the checker cannot"
	@echo "                  normalise -- but NOT for the caps counting family,"
	@echo "                  measured DIVERGENT here too (see the quarantine in"
	@echo "                  src/Harness/Main.agda: that blowup is arithmetic,"
	@echo "                  not opacity, so no backend reaches it)"
	@echo "                  ANYTHING READ OFF IT IS measured-not-rechecked: it"
	@echo "                  is NOT a refl pin, cannot discharge a postulate,"
	@echo "                  and exists to AIM the grind and to REFUTE.  Row 0"
	@echo "                  is a refl-pinned CALIBRATION and a mismatch there"
	@echo "                  VOIDS every other row (the run stops)"
	@echo "                  make harness             (the terminating rows)"
	@echo "                  make harness ARGS='10'   (one row, incl. quarantine)"
	@echo "  qc-build      compile the all-Agda QuickCheck binary (agda/_cli/QuickCheck)"
	@echo "  quickcheck    all-Agda QuickCheck: impl- vs spec-batchSimultaneous"
	@echo "                  make quickcheck              (seeds 1..300, 200 runs each)"
	@echo "                  make quickcheck ARGS='42 42' (ONE seed, 200 runs, depth 4)"
	@echo "                  make quickcheck ARGS='1 500 300 5' (seeds 1..500, 300 runs, depth 5)"

# Times itself and records the result in typecheck-performance-numbers.md, so that
# file stays current for free.  Only a GREEN run is recorded (`&&`), because a
# timing from a failed build measures how long it took to fail.  The recorder
# leaves the file byte-identical unless a number actually moved, so a normal build
# does not dirty the tree.
agda:
	@t0=$$(date +%s); log=$$(mktemp); rc=$$(mktemp); \
	 { (cd agda && $(AGDA) src/Main.agda); echo $$? > $$rc; } 2>&1 | tee $$log; \
	 st=$$(cat $$rc); el=$$(( $$(date +%s) - t0 )); \
	 n=$$(grep -c '^[[:space:]]*Checking ' $$log || true); \
	 if [ "$$st" -eq 0 ] && [ "$$n" -gt 0 ]; then \
	   scripts/perf_record.py "make agda (full gate, $$n modules)" $$el; \
	 fi; \
	 rm -f $$log $$rc; exit $$st

# THE FAST DEV LOOP.  Checks one mutual-block member at a time against its
# siblings POSTULATED at their exact signatures.  agda/src is never written to.
# Rationale, measurements and the closed performance experiments live in
# scripts/agda-dev.py's docstring -- read that before re-opening any of it.
#
# THERE IS NO WHOLE-PROJECT SWEEP.  One was built and measured against `make
# gate`; it cost more and checked less, so it is not supported and the bare
# command asks for a file.  It was not a cache-warming play either.  The cheap
# pre-gate is `make wiring-gate` plus `make unsafe-check`, both textual and
# seconds-long.  Figures: typecheck-performance-numbers.md.
#
#   make agda-dev ARGS='<file>'       one module, every member
#   make agda-dev ARGS='<file> <member>'   one member — the actual grind loop
#   make agda-dev ARGS='--list <file>'     its mutual-block structure
#
# OPT-IN flags: SCOPE=1 (names and syntax only; buys no time, so not a speedup),
# HOLES=1 (tolerate ? holes and missing clauses).
#
# DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID -- but only
# where something was STUBBED.  A module with no multi-member block has nothing
# stubbed and is checked verbatim, so the sweep is a real check there.  Where a
# block IS stubbed, TERMINATION of the real mutual recursion goes unchecked (in
# this proof the mutual recursion IS the induction) and postulates do not
# REDUCE.  `make agda` stays the merge gate.
#
# THE BUDGET IS ENFORCED, NOT DOCUMENTED.  It is set from a full cold scan of
# every module, and sits in the GAP in that distribution rather than just above
# the worst case -- a budget set to the worst observed time fails about half the
# time, since that time is a distribution and not a constant.  RE-SCAN BEFORE
# MOVING IT; the scan and the reasoning are in typecheck-performance-numbers.md.
# A cold DEPENDENCY CHAIN still blows it (edit Wet/Part1, check Wet/Part4, and
# you pay for Part2 and Part3 too); pass BUDGET= for that case, which is what it
# is for.
#
# A BUDGET THAT FAILS ON NORMAL WORK IS WORSE THAN NO BUDGET: it trains everyone
# to pass BUDGET= reflexively, and then a real regression sails through.
# Exceeding it FAILS, with the usual causes printed.  Override deliberately with
# BUDGET=<seconds> when the work has genuinely grown -- and move these numbers
# when it has, rather than overriding twice.
AGDA_DEV_BUDGET ?= 45
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
	cd agda && $(AGDA) src/Implementation/Unit-Test.agda
	cd agda && $(AGDA) src/Verify-Budget-Sufficient/Demand-Probe.agda

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
# ~13 minutes — so there is no reason to spend the 13 minutes only to fail on
# something a textual pass already knew.  Fail fast, then typecheck.
gate:
	@$(MAKE) --no-print-directory wiring-gate
	@$(MAKE) --no-print-directory unsafe-check
	@$(MAKE) --no-print-directory agda
	@$(MAKE) --no-print-directory bug-cache
	@echo "gate: ALL GREEN"

# ─────────────────────────────────────────────────────────────────────────
# DETACHED BUILDS — always launch a long target through `make bg`.
#
# `make agda` costs tens of minutes and the agent harness's foreground ceiling
# is ~600s, so long builds get detached and polled.  THE BUG THIS TARGET
# EXISTS TO CLOSE (hit 2026-08-11, and not for the first time) is the obvious
# hand-rolled wrapper:
#
#     (make agda > /tmp/x.log 2>&1; echo EXIT=$$? >> /tmp/x.log)
#
# The subshell exits with ECHO's status, which is ALWAYS 0.  So the launcher
# reports success no matter what happened, and a RED build is indistinguishable
# from a green one unless someone remembers to read the log — which is exactly
# the thing that did not happen.  Same family as the `timeout … | tail` trap
# and the `make agda` run from the wrong directory: a green-looking lie.
#
# SO `make bg` ALWAYS EXITS 7, GREEN OR RED (Anthony, 2026-08-11).  Not a
# propagated status — a deliberately USELESS one.  A launcher status that is
# right most of the time is worse than one that is never right: the reliable
# one gets read and believed, and every rare false green slips through.  An
# invariant 7 carries no information at all, so it cannot carry a wrong answer,
# and the only way to learn anything is `make bg-check` — which reads the log.
# Never make this "smarter" by propagating the code; that is the bug, restored.
#
#     make bg T=agda                  detach this under run_in_background
#     make bg T=gate LOG=/tmp/g.log   explicit log path
#     make bg-check T=agda            THE VERDICT: green, red + tail, or running
#
LOG ?= /tmp/rxjs-bg-$(T).log
bg:
	@test -n "$(T)" || { echo "usage: make bg T=<target> [LOG=<path>] [ARGS=...]" >&2; exit 2; }
	@rm -f $(LOG)
	@echo "bg: $(T) -> $(LOG)"
	@$(MAKE) --no-print-directory $(T) ARGS='$(ARGS)' > $(LOG) 2>&1; ec=$$?; \
	  echo "EXIT=$$ec" >> $(LOG); \
	  if [ $$ec -eq 0 ]; then \
	    echo "bg: $(T) looks GREEN ($(LOG))"; \
	  else \
	    echo "bg: $(T) RED — exit $$ec ($(LOG)).  Last 25 lines:"; \
	    tail -25 $(LOG); \
	  fi; \
	  echo "bg: exiting 7 BY DESIGN — this status is not a verdict."; \
	  echo "bg: run \`make bg-check T=$(T)\` for the real result."; \
	  exit 7

# The verdict of a detached run, without having to remember the log path or
# recognise what a green Agda log looks like.  Three distinct answers, and the
# distinctions are the whole point:
#
#   * STILL RUNNING (exit 3) — no EXIT= line yet.  Not a pass; not finished.
#   * RED (the real exit code) — plus the failing tail, so the reason is here.
#   * GREEN — and it PRINTS THE LOG'S OWN LAST WORD alongside, because exit 0
#     does not distinguish "checked everything, all passed" from "checked
#     NOTHING".  A vacuous pass wearing a real pass's clothes is the same
#     failure as the exit-code bug this file exists to prevent, one layer up.
#     Never summarise a log to one word when its own last line is the answer.
bg-check:
	@test -n "$(T)" || { echo "usage: make bg-check T=<target> [LOG=<path>]" >&2; exit 2; }
	@test -f $(LOG) || { echo "bg-check: no log at $(LOG) — never launched?"; exit 2; }
	@if grep -q '^EXIT=' $(LOG); then \
	  ec=$$(grep '^EXIT=' $(LOG) | tail -1 | cut -d= -f2); \
	  last=$$(grep -v '^EXIT=' $(LOG) | grep -v '^[[:space:]]*$$' | tail -1); \
	  if [ "$$ec" = 0 ]; then \
	    echo "bg-check: $(T) GREEN ($(LOG))"; \
	    echo "  log's last word: $$last"; \
	    echo "  ^ READ IT.  Exit 0 can also mean 'did no work' — check that the"; \
	    echo "    run actually checked what you think it checked."; \
	  else echo "bg-check: $(T) RED — exit $$ec ($(LOG)).  Last 25 lines:"; \
	       tail -25 $(LOG); exit $$ec; fi; \
	else \
	  echo "bg-check: $(T) STILL RUNNING ($$(wc -l < $(LOG) | tr -d ' ') lines so far)"; \
	  tail -2 $(LOG); exit 3; \
	fi

ts-check:
	cd typescript && npm run typecheck

cli-build:
	cd agda && $(AGDA) --compile --compile-dir=_cli src/CLI/Main.agda

oracle: cli-build
	cd typescript && npm run oracle -- $(ARGS)

# THE MEASUREMENT HARNESS — a COMPILED calculator for the machine's own
# arithmetic.  THE GHC BACKEND RUNS THE SAME DEFINITIONS AND IGNORES
# `abstract`, because opacity is a TYPECHECKING contract and not a runtime one
# — so a number sealed away from `refl` is readable here, and rungs that
# exhaust the checker (one was killed at 12.6 GB after 20 minutes) are cheap.
#
# WHAT IT IS *NOT* FOR, measured 2026-08-12: the CAPS COUNTING FAMILY
# (`poolCount`, `blowH`, `capsHgo`) is DIVERGENT under the compiled backend
# too — `poolCount 1 0` and `blowH 0`, the smallest possible arguments, each
# still running at 45 s with row 0 calibrating correctly in the same binary.
# That blowup is ARITHMETIC (`blowH` feeds `poolCount` a tower), not opacity,
# so no backend and no hardware reaches it.  Those rows are QUARANTINED at
# 10+ and excluded from the default sweep; see src/Harness/Main.agda.
#
# ⚠ ANYTHING READ OFF THIS IS `measured-not-rechecked` BY CONSTRUCTION.  A
# compiled number is NOT a `refl` pin: no proof may depend on it and it cannot
# discharge a postulate.  It exists to AIM the grind and to REFUTE.
#
# ROW 0 IS THE CALIBRATION and it is not decoration.  It prints a value the
# harness module ALSO pins by `refl`, so the typechecker fixes the expected
# number and the binary prints the computed one.  IF ROW 0 IS NOT 65536 THE
# BACKEND HAS DIVERGED AND EVERY OTHER ROW IS VOID — that is why `make harness`
# runs row 0 first and stops on mismatch rather than reporting on.
#
# ONE PROCESS PER ROW, deliberately: one process computing several deep rungs
# retains all of them and dies of memory; a fresh process per row does not.
#
#   make harness-build        compile it
#   make harness              every row, one process each (calibrated first)
#   make harness ARGS='5'     just row 5
HARNESS_ROWS ?= 2
harness-build:
	cd agda && $(AGDA) --compile --compile-dir=_harness src/Harness/Main.agda

harness: harness-build
	@cd agda && cal=$$(echo 0 | ./_harness/Main); \
	 case "$$cal" in \
	   *65536*) echo "harness: $$cal  [calibrated]";; \
	   *) echo "harness: CALIBRATION FAILED — every other row is VOID."; \
	      echo "  row 0 printed: $$cal"; \
	      echo "  expected 65536, the value Harness/Main.agda pins by refl."; \
	      echo "  the GHC backend has diverged from the typechecker; do not read on."; \
	      exit 1;; \
	 esac; \
	 if [ -n "$(ARGS)" ]; then echo "$(ARGS)" | ./_harness/Main; \
	 else for n in $$(seq 1 $(HARNESS_ROWS)); do echo $$n | ./_harness/Main; done; fi

qc-build:
	cd agda && $(AGDA) --compile --compile-dir=_cli src/QuickCheck.agda

quickcheck: qc-build
	scripts/gen-unit-tests.sh $(ARGS)

