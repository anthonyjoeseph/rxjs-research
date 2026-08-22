.PHONY: gate gate-heavy gate-cheap gate-light dev-changed dev-changed-selftest stripped strip-selftest postulates dup-check dup-selftest imports-check imports-fix imports-selftest find all help agda agda-dev agda-dev-selftest bg bg-check bg-wait bug-cache unsafe-check wiring wiring-selftest comments-check comments-selftest refuted ts-check cli-build oracle qc-build quickcheck harness harness-build

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
# ⚠ AND SO IS THE BINARY.  `AGDA_BIN` names it in ONE place so an A/B is
# `make agda AGDA_BIN=/path/to/other/agda` instead of a PATH edit nobody can
# see afterwards.  It is EXPORTED, so scripts/agda-dev.py picks up the same
# one; two tools on two binaries is the same cache war as two tools on two
# warning modes, one layer lower down.  Which binary a bare `agda` resolves
# to is a property of PATH, and on Apple silicon it is worth checking that it
# is not an x86_64 build under Rosetta -- see docs/agda-build.md.
#
# ⚠ THE FLAG MUST MATCH scripts/agda-dev.py's `agda_flags()` EXACTLY.  Agda
# records the WARNING MODE in an interface's validity key, so a target running
# with a different -W than the dev loop invalidates the whole cone on EVERY
# alternation — measured 2026-08-11 at 120 modules rebuilt per switch, with
# the cost landing on whatever module happened to be next and each tool
# blaming the other.  Change one, change both, in the same commit.
# ─────────────────────────────────────────────────────────────────────────
AGDA_BIN ?= agda
export AGDA_BIN
AGDA := $(AGDA_BIN) -W error

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
	@echo "                  HOLES=1 tolerate ? holes"
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
	@echo "  wiring        the wiring-law report ('never leave a proof hanging'):"
	@echo "                  R1 every definition and postulate in agda/src must"
	@echo "                  be REACHABLE from Main's claims; R2 a name passed"
	@echo "                  as a bare argument to a postulate earns nothing"
	@echo "                  from that site, so a postulate can never be the"
	@echo "                  only tissue holding a proof to Main.  A report for"
	@echo "                  a human to rule on — always exits 0, deletes"
	@echo "                  nothing (see scripts/check-wiring.py)"
	@echo "  wiring-gate   the same check, but EXITS 1 on a violation"
	@echo "  gate-light    THE DEFAULT GATE: every cheap check, plus a real dev"
	@echo "                  check of each module this tree touched.  Refuses to"
	@echo "                  pass when the full build is still owed — a touched"
	@echo "                  multi-member block, a file outside agda/src, or too"
	@echo "                  many commits of drift.  See docs/gate.md"
	@echo "                  DRIFT=n  raise/lower the commit limit (default 10)"
	@echo "                  ARGS='--max-files n'  the changed-set ceiling"
	@echo "                  DEPS=1   dev-check the consumer cone too — never"
	@echo "                             the claim roots, whose dev check IS the"
	@echo "                             tower; auto-on past a wide cone"
	@echo "  gate          WHAT YOU TYPE.  Routes: takes the light path when the"
	@echo "                  changed set is light-checkable, the full one when it"
	@echo "                  is not, and prints which and why"
	@echo "  gate-heavy     the tower, forced: gate-light's cheap half plus every"
	@echo "                  module, the refutations and the bug cache.  Many"
	@echo "                  minutes; stamps the commit the drift check counts from"
	@echo "  postulates    every postulate in agda/src by name — the work ledger"
	@echo "  find          SEARCH FIRST, made cheap: search the declared TYPE of"
	@echo "                  every statement in agda/src.  Always the whole tree —"
	@echo "                  the failure this prevents was a search scoped to two"
	@echo "                  files.  Run it BEFORE proving anything"
	@echo "                  make find Q='≤ slotsSize'"
	@echo "  dup-check     no fact proven twice: compares declared TYPES up to"
	@echo "                  renaming of bound variables, binder spelling"
	@echo "                  (bare/annotated, explicit/implicit) and atomic type"
	@echo "                  synonyms.  A finding is two SITES, not two names —"
	@echo "                  Agda does NOT catch a same-name copy when either is"
	@echo "                  private.  EXITS 1 on a violation"
	@echo "  dup-selftest  proves dup-check load-bearing against a fixture outside"
	@echo "                  agda/src: fires on each duplicate shape, and not on"
	@echo "                  record fields, where-locals, -go aliases or operators"
	@echo "  stripped      regenerate agda/_stripped-comments/, the comment-free"
	@echo "                  mirror agda ACTUALLY checks — so a comment-only edit"
	@echo "                  leaves it byte-identical and rebuilds nothing.  Runs"
	@echo "                  automatically before every agda target (~50 ms)"
	@echo "  strip-selftest  proves the stripper safe: the lexical traps (-->, x--y,"
	@echo "                  {-# #-}) and comment-insert invariance"
	@echo "  refuted       typecheck agda/evidence/refuted/ — the machine-checked '-> bottom'"
	@echo "                  witnesses.  Separate include root: 'make agda' never"
	@echo "                  pays for it and 'make wiring' never sees it.  ~5 s"
	@echo "                  after 'make agda' (it imports src, so the cache is"
	@echo "                  warm by then).  See EVIDENCE.md"
	@echo "  gate          the acceptance test: wiring-selftest + wiring-gate +"
	@echo "                  unsafe-check + dup-selftest + dup-check + agda +"
	@echo "                  refuted + bug-cache.  Cheap"
	@echo "                  checks FIRST so a 2-second failure never waits on"
	@echo "                  the 13-minute one; 'refuted' comes AFTER 'agda'"
	@echo "                  because it imports src and wants that cache warm"
	@echo "  bg            RUN EVERY LONG BUILD THROUGH THIS.  ALWAYS EXITS 7,"
	@echo "                  green or red — a launcher status that is right most"
	@echo "                  of the time gets believed, so this one is never"
	@echo "                  right.  It cannot report a false green because it"
	@echo "                  cannot report anything.  Ask bg-check instead"
	@echo "                  make bg T=agda   /   make bg T=gate LOG=/tmp/g.log"
	@echo "  bg-check      THE VERDICT of a detached run: GREEN, RED + failing"
	@echo "                  tail, or STILL RUNNING (exit 3 — not a pass)"
	@echo "                  make bg-check T=agda"
	@echo "                  ⚠ DO NOT BRANCH ON make's EXIT CODE HERE: make"
	@echo "                  collapses BOTH 3 and 1 to its own 2, so running"
	@echo "                  and RED are indistinguishable.  Match the text,"
	@echo "                  or use bg-wait, which cannot return while"
	@echo "                  running, so its nonzero means RED and only RED"
	@echo "  bg-wait       block until a detached run is TERMINAL, then report"
	@echo "                  it — exit 0 green, NONZERO red.  This is the one"
	@echo "                  to poll: it cannot return while still running"
	@echo "                  make bg-wait T=gate   /   make bg-wait T=agda I=90"
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
agda: stripped
	@t0=$$(date +%s); log=$$(mktemp); rc=$$(mktemp); \
	 { (cd agda/_stripped-comments && $(AGDA) src/Main.agda); echo $$? > $$rc; } 2>&1 \
	   | scripts/unmap-positions.py | tee $$log; \
	 st=$$(cat $$rc); el=$$(( $$(date +%s) - t0 )); \
	 n=$$(grep -c '^[[:space:]]*Checking ' $$log || true); \
	 if [ "$$st" -eq 0 ] && [ "$$n" -gt 0 ]; then \
	   scripts/perf_record.py "make agda (full gate, $$n modules)" $$el; \
	 fi; \
	 rm -f $$log $$rc; exit $$st

# THE FAST DEV LOOP.  Checks one mutual-block member at a time against its
# siblings POSTULATED at their exact signatures; agda/src is never written to.
#
#   make agda-dev ARGS='<file>'             one module, every member
#   make agda-dev ARGS='<file> <member>'    one member -- the actual grind loop
#   make agda-dev ARGS='--list <file>'      its mutual-block structure
#
# HOLES=1 tolerates ? holes and missing clauses (opt-in).  BUDGET=<seconds>
# overrides the enforced per-file budget below, and is for a cold dependency
# chain only.  DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID
# -- `make agda` stays the merge gate.  There is deliberately no whole-project
# sweep.  All of it, with the measurements: docs/agda-dev.md.
AGDA_DEV_BUDGET ?= 45
agda-dev:
	scripts/agda-dev.py --budget $(if $(BUDGET),$(BUDGET),$(AGDA_DEV_BUDGET)) \
	  $(if $(HOLES),--holes) $(ARGS)

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
bug-cache: stripped
	@$(call AGDA_RUN,src/Implementation/Unit-Test.agda)

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
	@cd agda && hits=$$(grep -rn -E '\{-# *(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|REWRITE)' src/ evidence/ \
	    --include='*.agda' | grep -v '^src/QuickCheck.agda:' || true); \
	  opts=$$(grep -rn -E '\{-# *OPTIONS.*(--type-in-type|--no-termination-check|--no-positivity-check|--rewriting)' src/ evidence/ \
	    --include='*.agda' || true); \
	  if [ -n "$$hits$$opts" ]; then \
	    echo "UNSAFE PRAGMA ON THE PROOF PATH OR IN THE EVIDENCE — a soundness hole, not a shortcut:"; \
	    echo "$$hits"; echo "$$opts"; exit 1; \
	  else \
	    echo "unsafe-check: clean in src and evidence (0 unsafe pragmas outside the documented QuickCheck.agda exemption)"; \
	  fi

# THE COMMENT-STRIPPED MIRROR -- what Agda actually checks, and why a
# comment-only edit rebuilds nothing.  NEVER run agda against agda/src
# directly: that is a second interface cache.  See docs/agda-build.md.
stripped:
	@scripts/strip-comments.py >/dev/null

strip-selftest:
	@scripts/strip-comments.py --selftest

# Run agda against the mirror and map its positions back onto agda/src, WITHOUT
# letting the pipe swallow agda's exit status — `$$?` is stashed before the pipe,
# exactly as the `agda` recipe does.
define AGDA_RUN
rc=$$(mktemp); \
	 { (cd agda/_stripped-comments && $(AGDA) $(1)); echo $$? > $$rc; } 2>&1 \
	   | scripts/unmap-positions.py; \
	 st=$$(cat $$rc); rm -f $$rc; exit $$st
endef

# THE SAME, FROM THE EVIDENCE ROOT.  The working directory is the whole
# src/evidence boundary: Agda reads the .agda-lib of the directory it starts in,
# so starting here picks up `include: refuted probed ../src` and starting one
# level up picks up `include: src`.  That is why an evidence import in src does
# not resolve (EVIDENCE.md, E1) -- and it costs no second interface cache,
# because Agda derives a file's build directory from the nearest .agda-lib ABOVE
# THE FILE, not from the invocation, so every src module still lands in the one
# shared _build.
define AGDA_RUN_EV
rc=$$(mktemp); \
	 { (cd agda/_stripped-comments/evidence && $(AGDA) $(1)); echo $$? > $$rc; } 2>&1 \
	   | scripts/unmap-positions.py; \
	 st=$$(cat $$rc); rm -f $$rc; exit $$st
endef

# The wiring law's mechanised check (see CLAUDE.md, "the wiring law: NEVER
# LEAVE A PROOF HANGING").  Pure textual analysis of agda/src, no Agda
# invocation — always exits 0, this is a report for a human to rule on.
wiring:
	scripts/check-wiring.py

# The same check AS A GATE: exits 1 when something in agda/src has no route
# to Main, when a module is unreachable, or on a ⊤-typed postulate.
wiring-gate:
	scripts/check-wiring.py --gate

# THE SAME LAW, APPLIED TO EACH EVIDENCE TREE (Anthony).  Rooted at that tree's
# own claim root, no MODULE_ROOTS -- every witness and every probe must be
# claimed there.  `wiring-probed` is what REPLACED the probes' MODULE_ROOTS
# entries, each of which was a reachability seed inside the PROOF's own scan and
# so let a probe read as wired to Main while Main could not reach it.  See
# EVIDENCE.md.
wiring-refuted:
	scripts/check-wiring.py --src agda/evidence/refuted --root Refuted/Main.agda --gate

wiring-probed:
	scripts/check-wiring.py --src agda/evidence/probed --root Probed/Main.agda --gate

# E1 (nothing in src imports evidence) and E2 (every probe names a LIVE
# postulate).  Textual, sub-second, and in the cheap block.  See EVIDENCE.md.
evidence-check:
	@scripts/check-evidence.py --gate

evidence-selftest:
	@scripts/check-evidence.py --selftest

# NO FACT IS PROVEN TWICE.  Compares the DECLARED TYPE of every definition and
# postulate, up to renaming of bound variables — `sizeᵉ-pos` and `1≤sizeᵉ`, the
# same statement 170 lines apart in ONE file, unnoticed for months.  CLAUDE.md
# has carried a SEARCH FIRST section throughout; prose lost, as it did for
# wiring and for unsafe pragmas, so this is the machine.
#
# A finding is two SITES, not two names.  Do NOT re-introduce the assumption
# that Agda's ClashingDefinition covers same-name copies: it does not when
# either copy is `private`, or when the two modules are never in scope
# together, and both escapees were exactly that shape.  It also matches up to
# BINDER SPELLING (bare/annotated, explicit/implicit) and expands atomic type
# synonyms (Id = ℕ), because those are three ways one fact wears two types.
# `make dup-selftest` pins every one of those rows.
dup-check:
	@scripts/check-duplicates.py --gate

# ─────────────────────────────────────────────────────────────────────────
# AN IMPORT NOTHING USES IS A MODULE EDGE NOTHING PAYS FOR.  Agda has no
# unused-import warning, so this is the one dependency in the tree that can be
# asserted and never spent -- and an edge decides both what `make agda` must
# build BEFORE a file and what an edit to the imported module INVALIDATES.
# Mechanics, and the twelve-edge instance that paid for the checker:
# docs/imports-check.md
# ─────────────────────────────────────────────────────────────────────────
imports-check:
	@scripts/check-imports.py

imports-fix:
	@scripts/check-imports.py --fix

imports-selftest:
	@out=$$(scripts/check-imports.py --src scripts/imports-selftest 2>&1); \
	  fail=0; \
	  for n in Fixture.Plain Fixture.Doc Fixture.Wide Fixture.Token dead-beside-live Dead-Mod; do \
	    echo "$$out" | grep -q "$$n" \
	      || { echo "SELFTEST FAIL: $$n not reported — a real dead import stopped firing"; fail=1; }; \
	  done; \
	  for n in Fixture.Precise Fixture.Mixfix Fixture.Renamed Fixture.Qualified Fixture.Solver Fixture.Section live-used; do \
	    echo "$$out" | grep -q "$$n" \
	      && { echo "SELFTEST FAIL: $$n reported, but it is used or undecidable"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q 'found 4 dead import(s) and 2 dead name' \
	    || { echo "SELFTEST FAIL: expected exactly 4 dead imports + 2 dead names"; fail=1; }; \
	  echo "$$out" | grep -q 'live-mod' \
	    && { echo "SELFTEST FAIL: live-mod reported, but it is used"; fail=1; }; \
	  echo "$$out" | grep -qE 'Main.agda:.*(DEAD IMPORT|dead name)' \
	    && { echo "SELFTEST FAIL: the CLAIM ROOT was use-audited — its imports are claims, not uses"; fail=1; }; \
	  echo "$$out" | grep -q 'Guard-Root.agda:.*WIRING' \
	    || { echo "SELFTEST FAIL: the orphan guard did not fire on the sole route to Guard-Leaf"; fail=1; }; \
	  echo "$$out" | grep -q 'Guard-Root.agda:.*DEAD' \
	    && { echo "SELFTEST FAIL: a sole-route edge was reported DEAD — --fix would orphan a module"; fail=1; }; \
	  for n in Guard-Two-A Guard-Two-B; do \
	    echo "$$out" | grep -q "$$n.agda:.*WIRING" \
	      || { echo "SELFTEST FAIL: the guard tested $$n edge-at-a-time — jointly these two are the only routes to Guard-Shared"; fail=1; }; \
	    echo "$$out" | grep -q "$$n.agda:.*DEAD" \
	      && { echo "SELFTEST FAIL: $$n reported DEAD — deleting BOTH orphans Guard-Shared"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q '3 unused import(s) HELD BACK' \
	    || { echo "SELFTEST FAIL: expected exactly 3 held-back edges"; fail=1; }; \
	  for n in Fixture.Bare Fixture.BareRenaming; do \
	    echo "$$out" | grep -q "BLANKET IMPORT  $$n" \
	      || { echo "SELFTEST FAIL: $$n has no \`using\` list and was not reported BLANKET"; fail=1; }; \
	    echo "$$out" | grep -q "DEAD IMPORT  $$n" \
	      && { echo "SELFTEST FAIL: $$n reported DEAD — the use check cannot decide a blanket import"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q 'No-Header.agda:1: NO MODULE DECLARATION' \
	    || { echo "SELFTEST FAIL: a file with no module declaration was not reported — every import of one crashes Agda with __IMPOSSIBLE__, and agda-dev cannot see it"; fail=1; }; \
	  echo "$$out" | grep -q 'Bad-Name.agda:1: MODULE NAME MISMATCH' \
	    || { echo "SELFTEST FAIL: a module declaration disagreeing with its path was not reported"; fail=1; }; \
	  echo "$$out" | grep -q '2 file(s) whose module DECLARATION' \
	    || { echo "SELFTEST FAIL: expected exactly 2 module-declaration findings"; fail=1; }; \
	  for n in gone hidden absent; do \
	    echo "$$out" | grep -q "PHANTOM NAME  $$n" \
	      || { echo "SELFTEST FAIL: $$n is imported from a module of this tree that does not contain it — Agda finds that only as a ModuleDoesntExport warning, many minutes down the tower"; fail=1; }; \
	  done; \
	  for n in real-thing Sub-Mod r2; do \
	    echo "$$out" | grep -q "PHANTOM NAME  $$n" \
	      && { echo "SELFTEST FAIL: $$n reported PHANTOM, but Phantom-Src does export it ($$n tests, in order: a plain definition; a \`module M\` item whose keyword must come off; and the SOURCE side of a renaming, since \`x to y\` binds y and the module must export x)"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q '3 PHANTOM name(s)' \
	    || { echo "SELFTEST FAIL: expected exactly 3 phantom names — a count over 3 means the check guessed at a module it cannot read, and every Fixture.* name in this tree names no file"; fail=1; }; \
	  echo "$$out" | grep -qE 'Phantom.agda:.*(DEAD IMPORT|dead name)' \
	    && { echo "SELFTEST FAIL: a phantom row also fired as dead — a phantom is a name that does not EXIST, not one that goes unused, and a row that fires both ways cannot tell them apart"; fail=1; }; \
	  echo "$$out" | grep -q 'Main.agda:.*BLANKET IMPORT  Fixture.Root-Blanket' \
	    || { echo "SELFTEST FAIL: the blanket rule skipped the CLAIM ROOT — it binds every file (Anthony)"; fail=1; }; \
	  echo "$$out" | grep -q 'BLANKET IMPORT  Fixture.Precise' \
	    && { echo "SELFTEST FAIL: \`using () renaming (…)\` reported BLANKET — it is the most precise form there is"; fail=1; }; \
	  echo "$$out" | grep -q 'BLANKET IMPORT  Fixture.Qualified' \
	    && { echo "SELFTEST FAIL: a qualified \`import M as Q\` reported BLANKET — it puts nothing in unqualified scope"; fail=1; }; \
	  for n in Fixture.Reexport Fixture.BarePublic; do \
	    echo "$$out" | grep -q "RE-EXPORT  $$n" \
	      || { echo "SELFTEST FAIL: $$n is a \`public\` re-export and was not reported — they are illegal (Anthony)"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q '2 \`public\` re-export(s)' \
	    || { echo "SELFTEST FAIL: expected exactly 2 public re-exports"; fail=1; }; \
	  echo "$$out" | grep -q '4 BLANKET import(s)' \
	    || { echo "SELFTEST FAIL: expected exactly 4 blanket imports"; fail=1; }; \
	  echo "$$out" | grep -q 'held back' \
	    || echo "$$out" | grep -q 'HELD BACK' \
	    || { echo "SELFTEST FAIL: the held-back count went missing from the summary"; fail=1; }; \
	  tmp=$$(mktemp -d); cp -a scripts/imports-selftest/. $$tmp/; \
	  scripts/check-imports.py --src $$tmp --fix >/dev/null 2>&1; \
	  after=$$(scripts/check-imports.py --src $$tmp 2>&1); \
	  echo "$$after" | grep -q 'found 0 dead import(s) and 0 dead name(s)' \
	    || { echo "SELFTEST FAIL: --fix left dead findings behind (not idempotent).  BOTH counts are asserted: a prefix match on the import count alone passes against '0 dead import(s) and 18 dead name(s)', which is the state that shipped"; fail=1; }; \
	  echo "$$after" | grep -q 'HELD BACK' \
	    || { echo "SELFTEST FAIL: the wiring finding vanished after --fix"; fail=1; }; \
	  for n in Guard-Root Guard-Two-A Guard-Two-B; do \
	    diff -q scripts/imports-selftest/$$n.agda $$tmp/$$n.agda >/dev/null \
	      || { echo "SELFTEST FAIL: --fix deleted a held-back edge in $$n and orphaned a module"; fail=1; }; \
	  done; \
	  for n in Fixture.Bare Fixture.BareRenaming Fixture.Reexport Fixture.BarePublic; do \
	    grep -q "$$n" $$tmp/Fires.agda \
	      || { echo "SELFTEST FAIL: --fix deleted $$n — a blanket import or a re-export is repaired by a human, not by the fixer"; fail=1; }; \
	  done; \
	  echo "$$after" | grep -q '4 BLANKET import(s)' \
	    || { echo "SELFTEST FAIL: the blanket findings vanished after --fix"; fail=1; }; \
	  echo "$$after" | grep -q '3 PHANTOM name(s)' \
	    || { echo "SELFTEST FAIL: --fix deleted a phantom name — the repair is the RIGHT module, which the fixer cannot know, and deleting the item trades a scope-check warning for an unbound name"; fail=1; }; \
	  diff -q scripts/imports-selftest/Main.agda $$tmp/Main.agda >/dev/null \
	    || { echo "SELFTEST FAIL: --fix rewrote the CLAIM ROOT"; fail=1; }; \
	  grep -q 'live-used' $$tmp/Fires.agda \
	    || { echo "SELFTEST FAIL: --fix deleted a LIVE name"; fail=1; }; \
	  grep -q 'dead-beside-live' $$tmp/Fires.agda \
	    && { echo "SELFTEST FAIL: --fix left a dead name in a surviving clause"; fail=1; }; \
	  grep -q 'live-mod' $$tmp/Fires.agda \
	    || { echo "SELFTEST FAIL: --fix deleted a LIVE name from the clause holding a dead \`module\` item"; fail=1; }; \
	  grep -q 'module Dead-Mod' $$tmp/Fires.agda \
	    && { echo "SELFTEST FAIL: --fix left a dead \`module M\` item — it must compare the BOUND name, keyword off, exactly as the report does"; fail=1; }; \
	  grep -q 'Fixture.Plain' $$tmp/Fires.agda \
	    && { echo "SELFTEST FAIL: --fix left a dead import declaration"; fail=1; }; \
	  diff -q scripts/imports-selftest/Quiet.agda $$tmp/Quiet.agda >/dev/null \
	    || { echo "SELFTEST FAIL: --fix rewrote the file it must not touch"; fail=1; }; \
	  rm -rf $$tmp; \
	  if [ $$fail -eq 0 ]; then echo "imports-selftest: PASS (fires on a comment-only mention, a multi-line clause, a token near-miss and a dead name beside a live one; not on an infix mixfix, a MIXFIX SECTION (one or many holes), a renaming, a qualified import or a \`module M\` entry whose use is an \`open M\`; --fix is idempotent on BOTH counts and spares the live names, a dead \`module M\` item included; the claim root is exempt from the USE check but not from the blanket rule; a sole-route edge is held back as a WIRING finding rather than deleted, jointly as well as one at a time; and an import with no \`using\` list is BLANKET, while \`using ()\` and a qualified import are not; and a \`public\` re-export is illegal outright, named or bare; and a file with no module declaration, or one disagreeing with its path, is reported before any finding about its imports; and a name no module of this tree contains is PHANTOM, read on the source side of a renaming and with a \`module\` keyword off, surviving --fix because only a human knows the right module)"; \
	  else echo "$$out"; exit 1; fi

# PROVES dup-check IS LOAD-BEARING, against a fixture outside agda/src.  It
# earns its keep: three separate bugs shipped in this checker and each was
# found by hand, not by the check failing.  The MUST-NOT rows are the
# regressions — an operator pair the binder regex used to rename away, record
# fields that a multi-line record header spilled into the scan, where-locals,
# and the mandated -go alias.  The MUST-FIRE rows cover every way one fact
# wears two types: differing names, ONE name in two modules (which Agda does
# not catch when either copy is private), binder spelling, and an UNANNOTATED
# IMPLICIT binder's letter -- the last of which escaped the check itself, in
# the `∀ {n} {Γ : Ctx n}` opening that most statements in this tree share.
dup-selftest:
	@out=$$(scripts/check-duplicates.py --src scripts/dup-selftest 2>&1); \
	  fail=0; \
	  echo "$$out" | grep -q "4 exact + 2 up-to-binder" \
	    || { echo "SELFTEST FAIL: expected 4 exact + 2 up-to-binder groups"; fail=1; }; \
	  for n in twin-different-name shared-name annotated-binder implicit-binder synonym-rhs implicit-unannotated-a implicit-unannotated-b; do \
	    echo "$$out" | grep -q "$$n" || { echo "SELFTEST FAIL: $$n not reported — a real duplicate stopped firing"; fail=1; }; \
	  done; \
	  for n in op-and op-or sealed fld-a fld-b helper outer; do \
	    echo "$$out" | grep -q "$$n" && { echo "SELFTEST FAIL: $$n reported, but it is not a duplicate"; fail=1; }; \
	  done; \
	  if [ $$fail -eq 0 ]; then echo "dup-selftest: PASS (fires on differing names, on one name in two modules, on binder spelling and on an unannotated implicit's letter; not on operators, record fields, where-locals or the -go alias)"; \
	  else echo "$$out"; exit 1; fi

# SEARCH FIRST, made cheap and impossible to scope wrong: search the declared
# TYPE of every statement in the tree.  dup-check catches a duplicate only once
# both copies exist; this is the same law applied BEFORE the writing.  It walks
# all of agda/src always — the 2026-08-19 failure was a search scoped to two
# files, so there is deliberately no argument that narrows it.
# Q is matched as ONE PHRASE against the type text, so `Q='≤ slotsSize'` means
# what it looks like.  Search for the OPERATOR and the RELATION, not the name
# you imagine — names here are idiosyncratic and a name-guess reliably misses.
#   make find Q='≤ slotsSize'      make find Q='1 ≤ sizeᵉ'
find:
	@scripts/find-lemma.py "$(Q)"

# THE REMAINING-WORK LEDGER: every postulate in agda/src, by name.  A grep for
# `^postulate` finds the 32 BLOCK HEADERS, not the 110 names inside them, so it
# is not the ledger and never was.  PROOF-STATE must carry a row for each of
# these, in exactly one tier.
postulates:
	@scripts/check-wiring.py --postulates

# PROVES THE WIRING CHECK IS LOAD-BEARING, against a fixture outside agda/src.
# R2 fires on nothing in the real tree today, so without the fixture it would
# rot untested.  See docs/wiring.md.
refuted: stripped
	@$(call AGDA_RUN_EV,refuted/Refuted/Main.agda)

# THE PROBES.  Same tree, same law, opposite decay: see EVIDENCE.md.
probed: stripped
	@$(call AGDA_RUN_EV,probed/Probed/Main.agda)

wiring-selftest:
	@out=$$(scripts/check-wiring.py --src scripts/wiring-selftest 2>&1); \
	  fail=0; \
	  echo "$$out" | grep -q "bad-lemma" || { echo "SELFTEST FAIL: bad-lemma not reported — R2 has stopped firing"; fail=1; }; \
	  echo "$$out" | grep -q "eta-lemma" || { echo "SELFTEST FAIL: eta-lemma not reported — R2 no longer sees through the mandated eta-expansion"; fail=1; }; \
	  for n in good-lemma nested computed other top-line via-top via-mod both-mods run \
	           consume with-only via-with nested-with-only via-nested-with; do \
	    echo "$$out" | grep -q "    $$n$$" && { echo "SELFTEST FAIL: $$n reported, but it is legitimately wired"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q "^    \.\.\." && { echo "SELFTEST FAIL: a bare \`...\` node surfaced as a definition — with-arm owners must be per-site and exempt"; fail=1; }; \
	  if [ $$fail -eq 0 ]; then echo "wiring-selftest: PASS (R2 fires on the passed-only lemma and on its eta-expansion, and on nothing else; module applications conduct; \`with\` arms conduct at both scopes)"; \
	  else echo "$$out"; exit 1; fi

# THE ACCEPTANCE TEST, cheap checks FIRST.  Ordering is the point: an orphan
# or an unsafe pragma is decidable in seconds by grep, while `agda` costs
# ~13 minutes — so there is no reason to spend the 13 minutes only to fail on
# something a textual pass already knew.  Fail fast, then typecheck.
roadmap-check:
	@scripts/check-roadmap.py

# PROVES roadmap-check IS LOAD-BEARING, against fixtures outside PROOF-STATE.md.
# Same reason dup-selftest exists: the real file is (and should stay) SORTED, so
# the failing path never runs on it and would rot untested.  The MUST-NOT row is
# the one that matters — a row whose prose MENTIONS a better class later must
# still be read at its declared class, or every "the FALSITY raise is WITHDRAWN,
# this is DIFFICULTY" row in the real file would be misclassified.
roadmap-selftest:
	@fail=0; \
	  scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	      --ledger scripts/roadmap-selftest/ledger.txt --src-names scripts/roadmap-selftest/src-names.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a correctly sorted, fully covered roadmap was rejected"; fail=1; }; \
	  out=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/unsorted.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/unsorted.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: an out-of-order roadmap PASSED — the sort check is dead"; fail=1; \
	  fi; \
	  for n in b-falsity d-shape; do \
	    echo "$$out" | grep -q "$$n" \
	      || { echo "SELFTEST FAIL: $$n not reported — a real sort violation stopped firing"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q "a-grindable is" \
	    && { echo "SELFTEST FAIL: the row a violation sits below was itself reported"; fail=1; }; \
	  gap=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	           --ledger scripts/roadmap-selftest/ledger-gap.txt --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	       --ledger scripts/roadmap-selftest/ledger-gap.txt --src-names scripts/roadmap-selftest/src-names.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: an unscheduled postulate PASSED — the coverage check is dead"; fail=1; \
	  fi; \
	  echo "$$gap" | grep -q never-scheduled \
	    || { echo "SELFTEST FAIL: never-scheduled not reported by the coverage check"; fail=1; }; \
	  for n in fam-alpha fam-beta glob-one glob-two suf-nodry-nestRec; do \
	    echo "$$gap" | grep -q "^  $$n$$" \
	      && { echo "SELFTEST FAIL: $$n reported — roadmap shorthand stopped counting as naming"; fail=1; }; \
	  done; \
	  long=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/overlong.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/overlong.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a leaked-header row PASSED — the length check is dead"; fail=1; \
	  fi; \
	  echo "$$long" | grep -q leaked-header \
	    || { echo "SELFTEST FAIL: leaked-header not reported by the length check"; fail=1; }; \
	  echo "$$long" | grep -q short-row \
	    && { echo "SELFTEST FAIL: a within-budget row was reported over budget"; fail=1; }; \
	  echo "$$out" | grep -q "OVER BUDGET" \
	    && { echo "SELFTEST FAIL: the length check fired on the sort fixture"; fail=1; }; \
	  pre=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/fatpre.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/fatpre.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a tier whose PREAMBLE holds a leaked header PASSED — the preamble budget is dead"; fail=1; \
	  fi; \
	  echo "$$pre" | grep -q "TIER PREAMBLES OVER BUDGET" \
	    || { echo "SELFTEST FAIL: the fat preamble was not reported"; fail=1; }; \
	  echo "$$pre" | grep -q "^  Tier 0  fatpre.md" \
	    || { echo "SELFTEST FAIL: the over-budget tier was not NAMED with its first preamble line"; fail=1; }; \
	  echo "$$pre" | grep -q "^  Tier 1  fatpre.md" \
	    && { echo "SELFTEST FAIL: a within-budget preamble was reported — three near-budget WRAPPED rows are being charged to their section, which is the bug this fixture exists for"; fail=1; }; \
	  echo "$$pre" | grep -q "ROWS OVER BUDGET" \
	    && { echo "SELFTEST FAIL: the row budget fired on fatpre.md, so it does not prove the preamble check catches what the row check cannot"; fail=1; }; \
	  echo "$$out" | grep -q "TIER PREAMBLES" \
	    && { echo "SELFTEST FAIL: the preamble check fired on the sort fixture"; fail=1; }; \
	  scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	      --ledger scripts/roadmap-selftest/ledger.txt --src-names scripts/roadmap-selftest/src-names.txt 2>&1 \
	    | grep -q names-are-free \
	    && { echo "SELFTEST FAIL: a nine-name row was charged for its names — shortening a row would mean dropping a name"; fail=1; }; \
	  dat=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/dated.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/dated.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a roadmap naming calendar dates PASSED — the date check is dead"; fail=1; \
	  fi; \
	  for d in "2026-08-20" "2026-07-31" "Aug 18 2026"; do \
	    echo "$$dat" | grep -q "$$d" \
	      || { echo "SELFTEST FAIL: $$d not reported — the date check missed an attribution, a receipt or a spelled-out date"; fail=1; }; \
	  done; \
	  echo "$$dat" | grep -q "3 line(s) naming" \
	    || { echo "SELFTEST FAIL: the date check did not report exactly the 3 dated lines — a bare year, a bare month-day or a version number was counted as a date"; fail=1; }; \
	  echo "$$out" | grep -q "DATED NARRATIVE" \
	    && { echo "SELFTEST FAIL: the date check fired on the sort fixture"; fail=1; }; \
	  rul=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	           --ledger scripts/roadmap-selftest/ledger.txt --src-names scripts/roadmap-selftest/src-names.txt \
	           --dates-only scripts/roadmap-selftest/dated-rules.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	       --ledger scripts/roadmap-selftest/ledger.txt --src-names scripts/roadmap-selftest/src-names.txt \
	       --dates-only scripts/roadmap-selftest/dated-rules.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a dated RULES file PASSED beside a clean roadmap — the CLAUDE.md half of the date check is dead"; fail=1; \
	  fi; \
	  echo "$$rul" | grep -q "dated-rules.md:" \
	    || { echo "SELFTEST FAIL: the rules file was not named in the date report — a rowless file is being skipped"; fail=1; }; \
	  scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	      --ledger scripts/roadmap-selftest/ledger.txt --src-names scripts/roadmap-selftest/src-names.txt \
	      --dates-only /dev/null > /dev/null 2>&1 \
	    || { echo "SELFTEST FAIL: a dateless extra file was rejected"; fail=1; }; \
	  stl=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/stale.md \
	           --ledger scripts/roadmap-selftest/ledger-stale.txt \
	           --src-names scripts/roadmap-selftest/src-names-stale.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/stale.md \
	       --ledger scripts/roadmap-selftest/ledger-stale.txt \
	       --src-names scripts/roadmap-selftest/src-names-stale.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a roadmap naming discharged postulates PASSED — the staleness check is dead"; fail=1; \
	  fi; \
	  for n in b-discharged c-vanished d-gone-parent; do \
	    echo "$$stl" | grep -q "$$n" \
	      || { echo "SELFTEST FAIL: $$n not reported — one arm of the staleness check stopped firing"; fail=1; }; \
	  done; \
	  echo "$$stl" | grep -q "a-live" \
	    && { echo "SELFTEST FAIL: a still-live postulate was reported stale"; fail=1; }; \
	  cln=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	           --ledger scripts/roadmap-selftest/ledger.txt \
	           --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  echo "$$cln" | grep -q "STALE ROWS" \
	    && { echo "SELFTEST FAIL: the staleness check fired on a clean roadmap — a CITED precedent or a descriptive head is being read as a claim, and earning GRINDABLE requires naming a proven precedent"; fail=1; }; \
	  if [ $$fail -eq 0 ]; then echo "roadmap-selftest: OK"; else exit 1; fi

# `imports-check` JOINS THIS LIST IN THE COMMIT THAT MAKES THE TREE PASS IT, and
# not before -- its dead-import half is clean, but the blanket and no-`public`
# halves have 89 + 66 open findings whose repair is one refactor (3231 names
# become explicit across 91 modules).  Wiring it now would land a knowingly-red
# gate, which is the one thing that teaches everyone to ignore red.  The check is
# NOT suppressed meanwhile: `make imports-check` runs it in full, and
# `imports-selftest` below still holds the checker itself to firing.
#
# `comments-check` IS THE SAME SITUATION AND IS OWED: the tree carries 351 dated
# comments, 19 historical markers, 31 blocks whose evidence is buried mid-prose and
# 39 over-budget explanations, all predating the law.  Wiring it before the sweep
# would land a knowingly-red gate, which is the one thing that teaches everyone to
# ignore red.  `make comments-check` runs it in full meanwhile, and
# `comments-selftest` above IS wired, so the checker itself cannot rot untested.
#
# AND A `#` COMMENT AT COLUMN 0 CANNOT GO INSIDE A RECIPE -- it ENDS the recipe,
# and the tab-indented lines after it become orphans ("recipe commences before
# first target").  That is why this note sits here rather than beside the line it
# is about; a recipe-internal comment must itself be tab-indented to be one.
# THE SOURCE-COMMENT LAW.  A source header is where the roadmap's own character
# budget SENDS research, which is what rules out the obvious design: a flat
# per-block ceiling budgets the DESTINATION, and then a finding with nowhere to
# go does not move, it gets deleted.  So this charges EXPLAINING and leaves
# EVIDENCE free -- the same split the roadmap's row budget uses for names.
comments-check:
	@scripts/check-comments.py

# PROVES comments-check IS LOAD-BEARING, one fixture per check, each firing
# exactly one.  `clean` is the fixture that matters most: it is the MUST-NOT
# direction, and it passes only if all four precision properties hold at once --
# an INDENTED `ASSEMBLED`/`MEASURED` is a continuation and not a marker, an
# UNDATED `SEALED:` is durable rationale and not history (the census found the
# marker word does not separate the two -- the date does), an indented line
# after `PROBED` is not stranded prose, and a `git show` pointer is not an
# explanation.  `sha` pins that last one as load-bearing rather than decorative:
# its raw comment total is well OVER budget and its charged total well under, so
# dropping the exemption turns it red.
comments-selftest:
	@fail=0; \
	  for d in clean sha; do \
	    scripts/check-comments.py --dir scripts/comments-selftest/$$d > /dev/null 2>&1 \
	      || { echo "SELFTEST FAIL: the $$d fixture was REJECTED — a precision property of the checker has died"; fail=1; }; \
	  done; \
	  for d in dated history shape order fat; do \
	    if scripts/check-comments.py --dir scripts/comments-selftest/$$d > /dev/null 2>&1; then \
	      echo "SELFTEST FAIL: the $$d fixture PASSED — that check is dead"; fail=1; \
	    fi; \
	  done; \
	  scripts/check-comments.py --dir scripts/comments-selftest/dated 2>&1 \
	    | grep -q 'DATED COMMENTS' \
	    || { echo "SELFTEST FAIL: a dated comment was not reported as one"; fail=1; }; \
	  scripts/check-comments.py --dir scripts/comments-selftest/history 2>&1 \
	    | grep -q 'HISTORICAL MARKERS' \
	    || { echo "SELFTEST FAIL: an UNDATED historical marker was not reported — only the name check can see one"; fail=1; }; \
	  scripts/check-comments.py --dir scripts/comments-selftest/shape 2>&1 \
	    | grep -q 'prose line(s) after the evidence' \
	    || { echo "SELFTEST FAIL: prose stranded behind the evidence was not reported"; fail=1; }; \
	  scripts/check-comments.py --dir scripts/comments-selftest/order 2>&1 \
	    | grep -q 'evidence out of order' \
	    || { echo "SELFTEST FAIL: PROBED before REFUTED was not reported — the order half is dead"; fail=1; }; \
	  scripts/check-comments.py --dir scripts/comments-selftest/fat 2>&1 \
	    | grep -q 'EXPLANATIONS OVER BUDGET' \
	    || { echo "SELFTEST FAIL: an over-budget explanation was not reported"; fail=1; }; \
	  if [ $$fail -eq 0 ]; then echo "comments-selftest: PASS (all four checks fire; an indented marker, an undated SEALED and a sha pointer do not)"; \
	  else exit 1; fi

# Everything decidable without Agda: seconds, and deliberately FIRST, so a
# textual violation never costs a full build to discover.  Both gates run it.
GATE_CHEAP = wiring-selftest wiring-gate wiring-refuted wiring-probed \
             unsafe-check dup-selftest dup-check \
             imports-selftest imports-check \
             evidence-selftest evidence-check \
             roadmap-selftest roadmap-check \
             comments-selftest dev-changed-selftest

gate-cheap:
	@for t in $(GATE_CHEAP); do \
	  $(MAKE) --no-print-directory $$t || exit $$?; \
	done

# THE LIGHT GATE.  The cheap checks, plus a real dev check of every module this
# tree has touched — and `dev-changed` FAILS if the full build is still owed,
# so this target cannot be used where it is not valid.  See docs/gate.md.
gate-light:
	@$(MAKE) --no-print-directory gate-cheap
	@$(MAKE) --no-print-directory dev-changed
	@echo "gate-light: ALL GREEN"

# THE GATE YOU TYPE, and it ROUTES.  `gate` is the name every session reaches
# for, so it must not be the expensive one by default -- otherwise the habit is
# the full tower every time, whatever a doc says.  It asks dev-changed for the
# verdict (free: a --list pass and a git query, no typecheck) and takes the
# light path when the light path is valid, the full one when it is not.
gate:
	@if scripts/dev-changed.py --verdict-only --drift $(or $(DRIFT),10) \
	     >/dev/null 2>&1; then \
	  echo "gate: the changed set is light-checkable — taking the LIGHT path"; \
	  echo "gate: (\`make gate-heavy\` forces the tower)"; \
	  $(MAKE) --no-print-directory gate-light; \
	else \
	  echo "gate: the heavy path is owed — taking it:"; \
	  scripts/dev-changed.py --verdict-only --drift $(or $(DRIFT),10) \
	    2>&1 | sed -n 's/^dev-changed: ESCALATE/gate:  reason:/p'; \
	  $(MAKE) --no-print-directory gate-heavy; \
	fi

# THE MERGE GATE, forced.  Everything, including the full tower.  Stamps the
# commit on the way out, which is what dev-changed's drift trigger counts from.
gate-heavy:
	@$(MAKE) --no-print-directory gate-cheap
	@$(MAKE) --no-print-directory agda
	@$(MAKE) --no-print-directory refuted
	@$(MAKE) --no-print-directory probed
	@$(MAKE) --no-print-directory bug-cache
	@scripts/dev-changed.py --stamp
	@echo "gate-heavy: ALL GREEN"

# The one way this driver can lie is by checking NOTHING and exiting 0 — an
# empty changed set, or a multi-member block it failed to notice.  Both
# directions are pinned, against real modules whose block structure is a fact
# rather than a fixture, and via --verdict-only so it costs no typecheck.
dev-changed-selftest:
	@fail=0; \
	  m=agda/src/Verify-Budget-Sufficient/Walk-Level.agda; \
	  n=agda/src/Verify-Budget-Sufficient/Walk-Level/Arms.agda; \
	  out=$$(scripts/dev-changed.py --verdict-only --files $$m 2>&1); ec=$$?; \
	  echo "$$out" | grep -q 'FULL GATE REQUIRED' \
	    || { echo "SELFTEST FAIL: a multi-member block did not escalate — agda-dev stubs those, so a light gate there is not a check"; fail=1; }; \
	  [ $$ec -eq 2 ] \
	    || { echo "SELFTEST FAIL: escalation exited $$ec, not 2 — make must go red"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --verdict-only --files $$n 2>&1); ec=$$?; \
	  echo "$$out" | grep -q 'light gate sufficient' \
	    || { echo "SELFTEST FAIL: a module with NO multi-member block escalated — the light gate would never be usable"; fail=1; }; \
	  [ $$ec -eq 0 ] \
	    || { echo "SELFTEST FAIL: the no-block case exited $$ec, not 0"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --verdict-only --max-files 2 --files $$n $$m $$n $$m 2>&1); \
	  echo "$$out" | grep -q 'ESCALATE  4 changed modules' \
	    || { echo "SELFTEST FAIL: a changed set over the ceiling did not escalate — N dev checks cost more than the one full build they replace"; fail=1; }; \
	  w=agda/src/Verify-Budget-Sufficient/Caps-Face/Part5.agda; \
	  scripts/dev-changed.py --verdict-only --files $$w >/dev/null 2>&1 \
	    || { echo "SELFTEST FAIL: a wide consumer cone escalated to the tower — a wide cone is the one thing the light path leaves unchecked, so the answer is to CHECK the cone (a few dev passes), never to buy the whole build"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --verdict-only --drift -1 --files $$n 2>&1); \
	  echo "$$out" | grep -q 'ESCALATE.*commits since' \
	    || { echo "SELFTEST FAIL: drift is invisible to --verdict-only — \`make gate\` routes on that verdict, so it would take the light path with the consumers long unchecked"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --verdict-only --files agda/evidence/refuted/Refuted/Main.agda 2>&1); \
	  echo "$$out" | grep -q 'ESCALATE' \
	    || { echo "SELFTEST FAIL: a file outside agda/src did not escalate — nothing would have checked it"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --plan --deps --files $$n 2>&1); \
	  echo "$$out" | grep -q 'NOT the .* claim root(s) in the cone' \
	    || { echo "SELFTEST FAIL: the cone sweep did not hold back the claim roots — EVERY cone contains them by the wiring law, so a sweep that checks them IS the tower it claims to be cheaper than"; fail=1; }; \
	  echo "$$out" | grep -q 'plan  cone  agda/src/Main.agda' \
	    && { echo "SELFTEST FAIL: Main.agda is in the sweep plan — a claim root's dev check is the whole build"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --deps --budget 1 --files agda/src/Verify-Well-Formed/Part13.agda 2>&1); \
	  echo "$$out" | grep -q 'skip  agda/src/Verify-Batch-Simultaneous/The-Proof.agda' \
	    || { echo "SELFTEST FAIL: a CONE member over budget was not reported as skipped — a timeout there is only the bet the light path already makes, and calling it RED makes every wide-cone run fail"; fail=1; }; \
	  echo "$$out" | grep -q 'FAIL  agda/src/Verify-Well-Formed/Part13.agda' \
	    || { echo "SELFTEST FAIL: a CHANGED module over budget was not a FAIL — that module is the one thing this run exists to check"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --deps --budget 2 --cone-budget 0 --files agda/src/Verify-Budget-Sufficient/Caps-Bridge.agda 2>&1); \
	  echo "$$out" | grep -q 'unchecked: ' \
	    || { echo "SELFTEST FAIL: the cone sweep spent past its TOTAL budget — the per-module budget bounds one check and nothing bounded the sum, so a changed set low in the tower outspends the one build that checks all of it"; fail=1; }; \
	  if [ -f .gate-heavy-stamp ]; then \
	    python3 -c 'import importlib.util,sys; sp=importlib.util.spec_from_file_location("dc","scripts/dev-changed.py"); m=importlib.util.module_from_spec(sp); sp.loader.exec_module(m); sys.exit(0 if m.gate_base() != "HEAD" else 1)' \
	      || { echo "SELFTEST FAIL: the changed set is measured against HEAD while a heavy-gate stamp exists — a session that COMMITS then gates has a clean tree, so nothing gets checked and the gate reports ALL GREEN about a commit it never looked at"; fail=1; }; \
	  fi; \
	  out=$$(scripts/dev-changed.py --plan --deps --files $$n 2>&1); \
	  echo "$$out" | grep -q 'skip  agda/src/Verify-Budget-Sufficient/Walk-Level.agda  — has a multi-member mutual block' \
	    || { echo "SELFTEST FAIL: a cone member with a multi-member block was dropped in SILENCE — agda-dev stubs a block's siblings, so a dev check there is not a check, and the consumer that validates a new arm's FIT is exactly such a module"; fail=1; }; \
	  out=$$(scripts/dev-changed.py --verdict-only --files 2>&1); \
	  echo "$$out" | grep -q '0 changed .agda file(s)' \
	    || { echo "SELFTEST FAIL: an empty changed set was not reported as empty — checking nothing must never read as a pass"; fail=1; }; \
	  if [ $$fail -eq 0 ]; then echo "dev-changed-selftest: PASS (a multi-member block escalates and exits 2; a module without one does not; a changed set over --max-files escalates because N dev checks cost more than the full build; drift is visible to the verdict \`make gate\` routes on; a wide cone does NOT escalate, because checking the cone MINUS THE CLAIM ROOTS is cheaper than the tower, and a cone member over budget is skipped while a changed one over budget is red; the cone sweep stops at its TOTAL budget and names what it left; the changed set is measured from the last green heavy gate, not from HEAD, so committing before gating does not empty it; a file outside agda/src escalates because no dev check can reach it; a cone member whose dev check would be STUBBED is named rather than silently dropped; and an empty changed set says so rather than passing quietly)"; \
	  else exit 1; fi

# Only the modules THIS TREE has touched since the last commit — a dev check is
# cheap singly and stops being cheap in bulk, so the driver has a ceiling.
dev-changed:
	@scripts/dev-changed.py --budget $(AGDA_DEV_BUDGET) \
	  $(if $(DRIFT),--drift $(DRIFT)) $(if $(DEPS),--deps) $(ARGS)

# ─────────────────────────────────────────────────────────────────────────
# DETACHED BUILDS -- always launch a long target through `make bg`.
#
#     make bg T=agda                  detach this under run_in_background
#     make bg T=gate LOG=/tmp/g.log   explicit log path
#     make bg-check T=agda            THE VERDICT: green, red + tail, running
#     make bg-wait  T=agda            blocks until terminal
#
# `make bg` ALWAYS EXITS 7, GREEN OR RED (Anthony) -- a deliberately useless
# status, because one that is right most of the time gets believed and the
# rare false green slips through.  Never make it "smarter" by propagating
# the code; that is the bug, restored.  The signal trap below is equally
# load-bearing: without it a killed build leaves no terminal marker and
# `bg-wait` blocks forever.  Full reasoning and both constraints on the
# trap's output format: docs/bg.md.
LOG ?= /tmp/rxjs-bg-$(T).log

# bg-wait's poll interval, seconds.  Override with I=<n>.
I ?= 60
bg:
	@test -n "$(T)" || { echo "usage: make bg T=<target> [LOG=<path>] [ARGS=...]" >&2; exit 2; }
	@rm -f $(LOG)
	@echo "bg: $(T) -> $(LOG)"
	@trap 'echo "bg: TERMINATED BY SIGNAL (the build did NOT finish — this is not an Agda failure)" >> $(LOG); echo "EXIT=143" >> $(LOG); exit 7' TERM INT HUP; \
	  $(MAKE) --no-print-directory $(T) ARGS='$(ARGS)' > $(LOG) 2>&1; ec=$$?; \
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

# The verdict of a detached run, without having to remember the log path.
# See docs/bg.md.
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

cli-build: stripped
	@$(call AGDA_RUN,--compile --compile-dir=../_cli src/CLI/Main.agda)

oracle: cli-build
	cd typescript && npm run oracle -- $(ARGS)

# THE MEASUREMENT HARNESS -- a COMPILED calculator for numbers the typechecker
# cannot reach.  Every row it prints is measured-not-rechecked and can
# discharge nothing.  Row 0 is a calibration and `make harness` stops on a
# mismatch.  See docs/harness.md.
HARNESS_ROWS ?= 2
harness-build: stripped
	@$(call AGDA_RUN,--compile --compile-dir=../_harness src/Harness/Main.agda)

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

qc-build: stripped
	@$(call AGDA_RUN,--compile --compile-dir=../_cli src/QuickCheck.agda)

quickcheck: qc-build
	scripts/gen-unit-tests.sh $(ARGS)


# THE ONE TO POLL.  Exits 3 while running, 1 when red -- but never loop on it
# through make, which collapses both to exit 2.  See docs/bg.md.
bg-wait:
	@test -n "$(T)" || { echo "usage: make bg-wait T=<target> [LOG=<path>] [I=<secs>]" >&2; exit 2; }
	@while :; do \
	  test -f $(LOG) || { echo "bg-wait: no log at $(LOG) — never launched?" >&2; exit 2; }; \
	  if grep -q '^EXIT=' $(LOG); then break; fi; \
	  sleep $(I); \
	done; \
	ec=$$(grep '^EXIT=' $(LOG) | tail -1 | cut -d= -f2); \
	if [ "$$ec" = 0 ]; then \
	  echo "bg-wait: $(T) GREEN ($(LOG))"; \
	  echo "  log's last word: $$(grep -v '^EXIT=' $(LOG) | grep -v '^[[:space:]]*$$' | tail -1)"; \
	  echo "  ^ READ IT.  Exit 0 can also mean 'did no work'."; \
	else \
	  echo "bg-wait: $(T) RED — exit $$ec ($(LOG)).  Last 25 lines:"; \
	  tail -25 $(LOG); exit 1; \
	fi
