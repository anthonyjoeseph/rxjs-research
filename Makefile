.PHONY: all help agda agda-dev agda-dev-selftest bg bg-check bug-cache unsafe-check wiring ts-check cli-build oracle qc-build quickcheck

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
	@echo "                  signatures.  ONE MEMBER ~6s — the grind loop.  Whole"
	@echo "                  modules, cold: Wet 55s, Subscribe-Face 21s, Caps-Face"
	@echo "                  part 8s; whole project 159s (2026-08-12)"
	@echo "                  DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF"
	@echo "                  IS VALID: the real recursion's TERMINATION is not"
	@echo "                  checked, and postulates do not reduce.  'make agda'"
	@echo "                  stays the merge gate"
	@echo "                  make agda-dev                    (EVERY module)"
	@echo "                  make agda-dev DIRTY=1            (only what you edited)"
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
#   make agda-dev                     EVERY dev-checkable module (DIRTY=1 to
#                                     restrict to what you edited -- dirty is
#                                     OPT-IN, because you run the bare command
#                                     precisely when you do not know what is
#                                     dirty, and "checked nothing" must never
#                                     be the silent answer to that question)
#   make agda-dev ARGS='<file>'       one module, every member
#   make agda-dev ARGS='<file> <member>'   one member — the actual grind loop
#   make agda-dev ARGS='--list <file>'     its mutual-block structure
#
# Measured 2026-08-12, COLD AND ON A COHERENT CACHE -- i.e. the real edit-one-
# file case: append a line to the file, then check it, with every DEPENDENCY
# already built.  Both halves matter.  Cold-but-incoherent (a dependency also
# rebuilding) inflates a module by 50x and has produced three phantom
# "slow module" diagnoses; see CLAUDE.md's "MEASURE ON A COHERENT CACHE".
#   Wet/Part2 35.0s (rest of Wet 6-12s; was 55.1s before the split)
#   Subscribe-Face 21.2s   Evaluator 9.4s   Caps.agda 15.7s
#   Caps-Face (split into Part1..Part7) worst part 8.3s, was 72.6s whole
#   Verify-Well-Formed/Part1 6.3s  <- measured 357s while Caps-Face rebuilt
# Whole project 12 modules, 158.6s of module time, all GREEN, under the 300s
# budget.  Only modules WITH a multi-member block are checked.
#
# THESE ARE DEV NUMBERS AND THEY ARE NOT THE COST OF AN EDIT.  agda-dev
# postulates the block's siblings, so POSITIVITY OVER THE REAL BLOCK NEVER RUNS
# -- that is the whole reason it is fast.  Wet/Part2 is 35.0s here and 254.7s
# under real agda, 88% of it Positivity.  Compare dev to dev and gate to gate,
# and always say which one a number is.
# ONE MEMBER ~6s, and that is the number the grind loop actually runs at.
# OPT-IN flags: SCOPE=1 (names and syntax only, no typechecking), HOLES=1
# (tolerate ? holes and missing clauses).
#
# DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID.  Two things
# are given up and the first is not minor: TERMINATION of the real mutual
# recursion is not checked (and in this proof the mutual recursion IS the
# induction), and postulates do not REDUCE.  `make agda` stays the merge gate.
# BUDGETS ARE ENFORCED, NOT DOCUMENTED (Anthony, 2026-08-11): 90s for one file,
# 300s for the whole project.  A loop that quietly drifts has stopped being a
# loop, and a number that lives only in a comment is a number nobody maintains.
#
# SET FROM THE **COLD** NUMBERS, re-measured 2026-08-12 (Anthony: "wouldn't the
# cold numbers be the relevant ones?  The use case would be that we're running
# this after modifying the file").  Cold IS the normal case -- you edit a file,
# so its generated module has new content and nothing is cached for it; warm
# only happens when you re-run having changed nothing, which is not the loop.
# Measured cold worst cases (2026-08-12): one file 35.0s (Wet/Part2, the
# 36-member wet walk -- a genuine 14-cycle plus a genuine 3-cycle, so it cannot
# be dissolved the way Caps-Face's spurious block was; hoisting around it and
# disabling positivity were both measured and both rejected, see CLAUDE.md).
# Whole project 158.6s of module time.  Both sit under 90s/300s with headroom.
# NOTE the 90s budget was set when one file could cost 55.1s; it now has more
# headroom than intended, which is fine -- do not tighten it to fit today's
# numbers, since a cold dependency chain legitimately costs more (Part4 took
# 271.8s the first time, building Part1..Part3 underneath it).  The
# earlier 30s/180s were warm figures, and 30s failed on every heavyweight
# module the moment you actually edited one.
#
# A BUDGET THAT FAILS ON NORMAL WORK IS WORSE THAN NO BUDGET: it trains everyone
# to pass BUDGET= reflexively, and then a real regression sails through.
# Exceeding it FAILS, with the usual causes printed.  Override deliberately with
# BUDGET=<seconds> when the work has genuinely grown -- and move these numbers
# when it has, rather than overriding twice.
AGDA_DEV_BUDGET ?= $(if $(ARGS),90,300)
agda-dev:
	scripts/agda-dev.py --budget $(if $(BUDGET),$(BUDGET),$(AGDA_DEV_BUDGET)) \
	  $(if $(SCOPE),--scope) $(if $(HOLES),--holes) $(if $(DIRTY),--dirty) $(ARGS)

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
#     does not distinguish "checked twelve modules, all passed" from "checked
#     NOTHING".  Hit 2026-08-11: `make agda-dev` on a freshly built tree found
#     nothing dirty, did no work, and exited 0; agda-dev said so plainly
#     ("nothing dirty — the tree matches its interfaces") and bg-check
#     flattened it to GREEN, which then got read as a project-wide pass.
#     A vacuous pass wearing a real pass's clothes is the same failure as the
#     exit-code bug this file exists to prevent, one layer up.  So: never
#     summarise a log to one word when the log's own last line is the answer.
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
	cd agda && agda --compile --compile-dir=_cli src/CLI/Main.agda

oracle: cli-build
	cd typescript && npm run oracle -- $(ARGS)

qc-build:
	cd agda && agda --compile --compile-dir=_cli src/QuickCheck.agda

quickcheck: qc-build
	scripts/gen-unit-tests.sh $(ARGS)

