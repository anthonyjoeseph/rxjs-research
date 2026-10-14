.PHONY: all help agda gate gate-cheap bug-cache oracle oracle-build chain ghosts placing bg bg-check bg-wait \
        wiring wiring-gate wiring-selftest unsafe-check dup-check dup-selftest \
        imports-check imports-fix imports-selftest comments-check comments-selftest \
        roadmap-check roadmap-selftest roadmap-evidence roadmap-moved roadmap-moved-selftest \
        roadmap-order roadmap-order-selftest find find-prose postulates notify \
        ts-check ts-lint ts-format-check ts-gate

# UTF-8 locale for em-dashes and special characters in Agda output
export LC_ALL := C.UTF-8
export LANG := C.UTF-8

# THE PROOF TREE.  `agda/` is the previous design, kept for reference only:
# nothing here reads it.
SRC := agda-impl
AGDA_SRC := $(shell find $(SRC) -name '*.agda' -not -path '*/_build/*' -not -path '*/_cli/*')

# ─────────────────────────────────────────────────────────────────────────
# THE AGDA INVOCATION — ONE DEFINITION, USED BY EVERY TARGET.  NEVER call
# bare `agda` in this file.
#
# `-W error` PROMOTES EVERY WARNING TO AN ERROR: a warning that costs
# nothing gets ignored, and a dead `rewrite` is a proof step doing nothing.
# Agda exits 42 on a promoted warning; green means warning-free.  Agda
# records the warning mode in an interface's validity key, so every run on
# one cache must use the same flags.
# ─────────────────────────────────────────────────────────────────────────
AGDA_BIN ?= agda
export AGDA_BIN
AGDA := $(AGDA_BIN) -W error

all: help

help:
	@echo "  gate          WHAT YOU TYPE: every cheap check, then Agda on Main"
	@echo "  gate-cheap    the textual checks alone (seconds, no Agda)"
	@echo "  agda          typecheck $(SRC)/Main.agda — everything Main reaches"
	@echo "  bug-cache     compile the bug cache's runner and run every row"
	@echo "  oracle        the three Agda engines against real rxjs (typescript/ drives it)"
	@echo "  chain         the denotation's approximants form a chain (ARGS=\"FROM COUNT\")"
	@echo "  placing       the machine's trace is placed against the root's events (ARGS=\"FROM COUNT\")"
	@echo "  ghosts        every observer in the run is shown what its subtree denotes (ARGS=\"FROM COUNT\")"
	@echo "  postulates    every postulate in $(SRC) by name — the work ledger"
	@echo "  find          search the declared TYPE of every statement:  make find Q='⊑ lub'"
	@echo "  find-prose    search comment blocks and docs for a finding:  make find-prose Q='dead route'"
	@echo "  wiring        the wiring report (wiring-gate: the same, exiting 1)"
	@echo "  imports-fix   delete unused imports and names"
	@echo "  roadmap-evidence  rewrite PROOF-STATE's derived evidence fields"
	@echo "  bg / bg-check / bg-wait   run a long target detached; read its verdict"
	@echo "  ts-gate       tsc, eslint, prettier over typescript/"

# ─────────────────────────────────────────────────────────────────────────
# THE GATE.  Cheap checks FIRST: an orphan or an unsafe pragma is decidable
# in seconds by grep, so no build is spent discovering one.  Then Agda on
# Main, which is the claim graph: anything Main does not reach is not
# checked, which is what `wiring-gate` guarantees cannot happen silently.
# ─────────────────────────────────────────────────────────────────────────
GATE_CHEAP = wiring-selftest wiring-gate \
             unsafe-check dup-selftest dup-check \
             imports-selftest imports-check \
             roadmap-selftest roadmap-check \
             roadmap-moved-selftest roadmap-moved \
             roadmap-order-selftest roadmap-order \
             comments-selftest comments-check \
             ts-gate

gate-cheap:
	@for t in $(GATE_CHEAP); do \
	  $(MAKE) --no-print-directory $$t || exit $$?; \
	done

agda:
	@cd $(SRC) && $(AGDA) Main.agda

gate:
	@$(MAKE) --no-print-directory gate-cheap || { scripts/notify.py "RED (cheap checks)"; exit 1; }
	@$(MAKE) --no-print-directory agda || { scripts/notify.py "RED (agda)"; exit 1; }
	@echo "gate: ALL GREEN"
	@scripts/notify.py "GREEN"

# ─────────────────────────────────────────────────────────────────────────
# THE BUG CACHE: every program that ever made the semantics disagree,
# checked by a compiled runner rather than the typechecker, since the
# corpus only grows.  Green exactly when no known counterexample remains.
# THE ORACLE: the compiled CLI prints each generated program with the
# three engines' traces, and typescript/src/oracle.ts replays it in rxjs.
# `make oracle ARGS="COUNT FROM"`.
# ─────────────────────────────────────────────────────────────────────────
ORACLE_CLI := $(SRC)/quickcheck/Oracle-CLI.agda
ORACLE_BIN := $(SRC)/_cli/Oracle-CLI

oracle-build:
	@test -f $(ORACLE_CLI) || { echo "oracle: RED — $(ORACLE_CLI) does not exist yet"; exit 1; }
	@cd $(SRC) && $(AGDA) --compile --compile-dir=_cli quickcheck/Oracle-CLI.agda

oracle: oracle-build
	@cd typescript && AGDA_CLI_BIN=$(CURDIR)/$(ORACLE_BIN) npm run --silent oracle -- $(ARGS)

# The denotation's approximants as a chain, on ARGS="FROM COUNT" seeds:
# green when the run reaches its `done` line and no seed FAILs.
chain: oracle-build
	@out=$$($(ORACLE_BIN) chain $(ARGS)); echo "$$out"; \
	  echo "$$out" | grep -q '^chain: done ' || { echo "chain: RED — the run never finished"; exit 1; }; \
	  if echo "$$out" | grep -q '^chain: FAIL '; then echo "chain: RED"; exit 1; fi; \
	  echo "chain: GREEN"

# The machine's trace placed against the meaning, positions included, on
# ARGS="FROM COUNT" seeds.
placing: oracle-build
	@out=$$($(ORACLE_BIN) placing $(ARGS)); echo "$$out"; \
	  echo "$$out" | grep -q '^placing: done ' || { echo "placing: RED — the run never finished"; exit 1; }; \
	  if echo "$$out" | grep -q '^placing: FAIL '; then echo "placing: RED"; exit 1; fi; \
	  echo "placing: GREEN"

# Every observer inside the run against its subtree's denotation, on
# ARGS="FROM COUNT" seeds: green when the run reaches its `done` line and no
# seed FAILs.
ghosts: oracle-build
	@out=$$($(ORACLE_BIN) ghosts $(ARGS)); echo "$$out"; \
	  echo "$$out" | grep -q '^ghosts: done ' || { echo "ghosts: RED — the run never finished"; exit 1; }; \
	  if echo "$$out" | grep -q '^ghosts: FAIL '; then echo "ghosts: RED"; exit 1; fi; \
	  echo "ghosts: GREEN"

# The runner prints a FAIL line per failing row and a closing `done` line;
# a run without the `done` line died part-way and is red.  See
# docs/bug-cache.md.
#
# A FILE TARGET, so one build serves every run after it: any source edit is
# newer than the binary and rebuilds it, and the `touch` is owed because a
# compile that found nothing stale leaves the old mtime behind.
# ─────────────────────────────────────────────────────────────────────────
BUG_CACHE_BIN := $(SRC)/_cli/Bug-Cache-Runner

$(BUG_CACHE_BIN): $(AGDA_SRC)
	@cd $(SRC) && $(AGDA) --compile --compile-dir=_cli quickcheck/Bug-Cache-Runner.agda
	@touch $@

bug-cache: $(BUG_CACHE_BIN)
	@out=$$($(BUG_CACHE_BIN)); echo "$$out"; \
	  echo "$$out" | grep -q '^bug-cache: done ' \
	    || { echo "bug-cache: RED — the runner never reached its closing line"; exit 1; }; \
	  if echo "$$out" | grep -q '^bug-cache: FAIL '; then \
	    echo "bug-cache: RED — a known counterexample still fails"; exit 1; fi; \
	  echo "bug-cache: GREEN"

# The wiring law's mechanised check (see CLAUDE.md, "the wiring law: NEVER
# LEAVE A PROOF HANGING").  Pure textual analysis of the tree, no Agda
# invocation — always exits 0, this is a report for a human to rule on.
wiring:
	scripts/check-wiring.py

# The same check AS A GATE: exits 1 when something in the tree has no route
# to Main, when a module is unreachable, or on a ⊤-typed postulate.
wiring-gate:
	scripts/check-wiring.py --gate

wiring-selftest:
	@out=$$(scripts/check-wiring.py --src scripts/wiring-selftest 2>&1); \
	  fail=0; \
	  echo "$$out" | grep -q "bad-lemma" || { echo "SELFTEST FAIL: bad-lemma not reported — R2 has stopped firing"; fail=1; }; \
	  echo "$$out" | grep -q "eta-lemma" || { echo "SELFTEST FAIL: eta-lemma not reported — R2 no longer sees through the mandated eta-expansion"; fail=1; }; \
	  echo "$$out" | grep -q "    deep-dead$$" || { echo "SELFTEST FAIL: deep-dead not reported — a module nested in a module is invisible again"; fail=1; }; \
	  for n in good-lemma nested computed other top-line via-top via-mod both-mods run deep-live \
	           consume with-only via-with nested-with-only via-nested-with \
	           import-arg via-import-arg apply; do \
	    echo "$$out" | grep -q "    $$n$$" && { echo "SELFTEST FAIL: $$n reported, but it is legitimately wired"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q "^    \.\.\." && { echo "SELFTEST FAIL: a bare \`...\` node surfaced as a definition — with-arm owners must be per-site and exempt"; fail=1; }; \
	  echo "$$out" | grep -q "^    #-}$$" && { echo "SELFTEST FAIL: a nested pragma's outer \`#-}\` surfaced as a definition — block comments must nest"; fail=1; }; \
	  led=$$(scripts/check-wiring.py --postulates --src scripts/wiring-selftest 2>&1); \
	  echo "$$led" | grep -q "^sealed-gap " || { echo "SELFTEST FAIL: sealed-gap missing from the ledger — a nested block opener is being sliced off the RAW line, so members of a postulate block inside a seal are invisible"; fail=1; }; \
	  echo "$$led" | grep -qE "^(te|ct|al|te) " && { echo "SELFTEST FAIL: a keyword tail registered as a postulate — the nested opener is sliced off the RAW line"; fail=1; }; \
	  echo "$$led" | grep -q "^ffi-bound " && { echo "SELFTEST FAIL: ffi-bound on the ledger — a CLI postulate with a COMPILE GHC body is not remaining work"; fail=1; }; \
	  echo "$$led" | grep -q "^ffi-unbound " || { echo "SELFTEST FAIL: ffi-unbound missing from the ledger — the FFI exemption swallowed a CLI postulate with no binding"; fail=1; }; \
	  echo "$$led" | grep -q "^ffi-outside " || { echo "SELFTEST FAIL: ffi-outside missing from the ledger — a binding outside CLI/ must earn nothing"; fail=1; }; \
	  if [ $$fail -eq 0 ]; then echo "wiring-selftest: PASS (R2 fires on the passed-only lemma and on its eta-expansion, and on nothing else; module applications conduct; \`with\` arms conduct at both scopes; a postulate block nested in a seal reaches the ledger; a pragma nested in a pragma closes on its own close; a CLI postulate with a COMPILE GHC body leaves it, an unbound one or one outside CLI/ stays)"; \
	  else echo "$$out"; exit 1; fi

# SOUNDNESS GUARD.  The build is not `--safe` — it cannot be while
# postulates exist, since `--safe` rejects `postulate` as well as the unsafe
# pragmas — so nothing mechanically stops an unsafe pragma reaching the
# proof.  Until the endgame this grep IS the guard.  `--guardedness` is
# allowed: `--safe` accepts it.  At the finish line this target retires:
# once Main reaches no postulate, `agda --safe Main.agda` checks both halves.
unsafe-check:
	@hits=$$(grep -rn -E '\{-# *(TERMINATING|NON_TERMINATING|NO_POSITIVITY_CHECK|NO_UNIVERSE_CHECK|REWRITE)' $(SRC) \
	    --include='*.agda' || true); \
	  opts=$$(grep -rn -E '\{-# *OPTIONS.*(--type-in-type|--no-termination-check|--no-positivity-check|--rewriting)' $(SRC) \
	    --include='*.agda' || true); \
	  if [ -n "$$hits$$opts" ]; then \
	    echo "UNSAFE PRAGMA ON THE PROOF PATH — a soundness hole, not a shortcut:"; \
	    echo "$$hits"; echo "$$opts"; exit 1; \
	  else \
	    echo "unsafe-check: clean (0 unsafe pragmas in $(SRC))"; \
	  fi

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

# PROVES dup-check IS LOAD-BEARING, against a fixture outside the tree.  It
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
	  echo "$$out" | grep -q "5 exact + 2 up-to-binder" \
	    || { echo "SELFTEST FAIL: expected 5 exact + 2 up-to-binder groups"; fail=1; }; \
	  for n in twin-different-name shared-name annotated-binder implicit-binder synonym-rhs implicit-unannotated-a implicit-unannotated-b nested-mul-comm; do \
	    echo "$$out" | grep -q "$$n" || { echo "SELFTEST FAIL: $$n not reported — a real duplicate stopped firing"; fail=1; }; \
	  done; \
	  for n in op-and op-or sealed fld-a fld-b helper outer; do \
	    echo "$$out" | grep -q "$$n" && { echo "SELFTEST FAIL: $$n reported, but it is not a duplicate"; fail=1; }; \
	  done; \
	  if [ $$fail -eq 0 ]; then echo "dup-selftest: PASS (fires on differing names, on one name in two modules, on binder spelling, on an unannotated implicit's letter and inside a parameterised module; not on operators, record fields, where-locals or the -go alias)"; \
	  else echo "$$out"; exit 1; fi

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
	    || { echo "SELFTEST FAIL: a file with no module declaration was not reported — every import of one crashes Agda with __IMPOSSIBLE__, and only a full check would see it"; fail=1; }; \
	  echo "$$out" | grep -q 'Bad-Name.agda:1: MODULE NAME MISMATCH' \
	    || { echo "SELFTEST FAIL: a module declaration disagreeing with its path was not reported"; fail=1; }; \
	  echo "$$out" | grep -q '2 file(s) whose module DECLARATION' \
	    || { echo "SELFTEST FAIL: expected exactly 2 module-declaration findings"; fail=1; }; \
	  for n in gone hidden absent borrowed; do \
	    echo "$$out" | grep -q "PHANTOM NAME  $$n" \
	      || { echo "SELFTEST FAIL: $$n is imported from a module of this tree that does not declare it — Agda finds that only as a ModuleDoesntExport warning"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q "PHANTOM NAME  borrowed .*IMPORTS" \
	    || { echo "SELFTEST FAIL: a name the source module SPENDS after importing it was not caught as borrowed — its use is a body token, so the token reading calls it exported and only the import reading is left; this is the shape that reached CI"; fail=1; }; \
	  echo "$$out" | grep -q "PHANTOM NAME  gone .*IMPORTS" \
	    && { echo "SELFTEST FAIL: a name the source module holds NOWHERE was reported as borrowed — the two arms have different repairs, and only the borrowed one can name where the name actually lives"; fail=1; }; \
	  for n in real-thing Sub-Mod r2; do \
	    echo "$$out" | grep -q "PHANTOM NAME  $$n" \
	      && { echo "SELFTEST FAIL: $$n reported PHANTOM, but Phantom-Src does export it ($$n tests, in order: a plain definition; a \`module M\` item whose keyword must come off; and the SOURCE side of a renaming, since \`x to y\` binds y and the module must export x)"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q '4 PHANTOM name(s)' \
	    || { echo "SELFTEST FAIL: expected exactly 4 phantom names — a count over 4 means the check guessed at a module it cannot read, and every Fixture.* name in this tree names no file"; fail=1; }; \
	  echo "$$out" | grep -q 'PHANTOM MODULE  Phantom-Src.Nowhere' \
	    || { echo "SELFTEST FAIL: an import of a module of this tree that has NO FILE went unreported — Agda meets that as a hard FileNotFound, and a split is what leaves them"; fail=1; }; \
	  echo "$$out" | grep -q '1 PHANTOM module(s)' \
	    || { echo "SELFTEST FAIL: expected exactly 1 phantom module — every Fixture.* module named here also has no file, and firing on those would mean the check is reading a namespace it cannot see the root of"; fail=1; }; \
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
	  echo "$$out" | grep -q '2 `public` re-export(s)' \
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
	  echo "$$after" | grep -q '4 PHANTOM name(s)' \
	    || { echo "SELFTEST FAIL: --fix deleted a phantom name — the repair is the RIGHT module, which the fixer cannot know, and deleting the item trades a scope-check warning for an unbound name"; fail=1; }; \
	  echo "$$after" | grep -q '1 PHANTOM module(s)' \
	    || { echo "SELFTEST FAIL: --fix deleted a phantom module — same reason as a phantom name, one level up: only a human knows which module the definition moved to"; fail=1; }; \
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
	  if [ $$fail -eq 0 ]; then echo "imports-selftest: PASS (fires on a comment-only mention, a multi-line clause, a token near-miss and a dead name beside a live one; not on an infix mixfix, a MIXFIX SECTION (one or many holes), a renaming, a qualified import or a \`module M\` entry whose use is an \`open M\`; --fix is idempotent on BOTH counts and spares the live names, a dead \`module M\` item included; the claim root is exempt from the USE check but not from the blanket rule; a sole-route edge is held back as a WIRING finding rather than deleted, jointly as well as one at a time; and an import with no \`using\` list is BLANKET, while \`using ()\` and a qualified import are not; and a \`public\` re-export is illegal outright, named or bare; and a file with no module declaration, or one disagreeing with its path, is reported before any finding about its imports; and a name no module of this tree contains is PHANTOM, read on the source side of a renaming and with a \`module\` keyword off, surviving --fix because only a human knows the right module; and so is a name the source module merely BORROWED and then spent, which its body tokens cannot tell from one it declares, reported against the module it was borrowed from, unless the module ALSO declares it as a constructor, which Agda overloads silently; and a MODULE of this tree that has no file is PHANTOM too, while an out-of-tree namespace is not)"; \
	  else echo "$$out"; exit 1; fi

# `imports-check` JOINS THIS LIST IN THE COMMIT THAT MAKES THE TREE PASS IT, and
# not before -- its dead-import half is clean, but the blanket and no-`public`
# halves have 89 + 66 open findings whose repair is one refactor (3231 names
# become explicit across 91 modules).  Wiring it now would land a knowingly-red
# gate, which is the one thing that teaches everyone to ignore red.  The check is
# NOT suppressed meanwhile: `make imports-check` runs it in full, and
# `imports-selftest` below still holds the checker itself to firing.
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
# exactly one.  The six structural fixtures run with --no-refs so that each
# tests ONE thing; ref-ok and ref-bad are the two that resolve references.
#
# `clean` is the fixture that matters most: it is the MUST-NOT direction, and it
# passes only if three precision properties hold at once -- an INDENTED
# `ASSEMBLED`/`MEASURED` is a continuation and not a marker, an UNDATED
# `SEALED:` is durable rationale and not history (the census found the marker
# word does not separate the two -- the date does), and a `git show` pointer
# is not an explanation.  `sha` pins that last one as load-bearing rather than
# decorative: its raw comment total is well OVER budget and its charged total
# well under, so dropping the exemption turns it red.
#
# THE POSTULATE-TWIN ASSERTION IS GENERATED, and deliberately: the highest-value
# thing this checker does is refuse a `TWIN` naming a statement that is ITSELF
# STILL A POSTULATE, because that is a row whose GRINDABLE class was never
# earned.  A fixture naming a postulate by hand would go stale the day that
# postulate is discharged -- and it WOULD be discharged, since the whole point
# of the campaign is to discharge them -- and it would then pass while reporting
# the check as dead.  So the name is read from the live ledger at run time.
comments-selftest:
	@fail=0; \
	  for d in clean sha echo-ok; do \
	    scripts/check-comments.py --no-refs --dir scripts/comments-selftest/$$d > /dev/null 2>&1 \
	      || { echo "SELFTEST FAIL: the $$d fixture was REJECTED — a precision property of the checker has died"; fail=1; }; \
	  done; \
	  for d in dated history shape order fat echo lineref obscured; do \
	    if scripts/check-comments.py --no-refs --dir scripts/comments-selftest/$$d > /dev/null 2>&1; then \
	      echo "SELFTEST FAIL: the $$d fixture PASSED — that check is dead"; fail=1; \
	    fi; \
	  done; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/dated 2>&1 \
	    | grep -q 'DATED COMMENTS' \
	    || { echo "SELFTEST FAIL: a dated comment was not reported as one"; fail=1; }; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/history 2>&1 \
	    | grep -q 'HISTORICAL MARKERS' \
	    || { echo "SELFTEST FAIL: an UNDATED historical marker was not reported — only the name check can see one"; fail=1; }; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/shape 2>&1 \
	    | grep -q 'prose line(s) after the evidence' \
	    || { echo "SELFTEST FAIL: prose stranded behind the evidence was not reported"; fail=1; }; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/order 2>&1 \
	    | grep -q 'evidence out of order' \
	    || { echo "SELFTEST FAIL: RECOVERY before REFUTED was not reported — the order half is dead"; fail=1; }; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/fat 2>&1 \
	    | grep -q 'EXPLANATIONS OVER BUDGET' \
	    || { echo "SELFTEST FAIL: an over-budget explanation was not reported"; fail=1; }; \
	  scripts/check-comments.py --no-refs --dir scripts/comments-selftest/echo 2>&1 \
	    | grep -q 'ECHOES ITS OWN LEDGER' \
	    || { echo "SELFTEST FAIL: prose naming its own ledger's subject was not reported"; fail=1; }; \
	  lr=$$(scripts/check-comments.py --no-refs --dir scripts/comments-selftest/lineref 2>&1); \
	  echo "$$lr" | grep -q 'LINE-NUMBER CITATIONS' \
	    || { echo "SELFTEST FAIL: a line-number citation was not reported"; fail=1; }; \
	  echo "$$lr" | grep -q 'Wet.agda:4125' \
	    || { echo "SELFTEST FAIL: the path-and-colon citation form was missed"; fail=1; }; \
	  echo "$$lr" | grep -q 'line 1920' \
	    || { echo "SELFTEST FAIL: the prose citation form was missed -- only the path form fires"; fail=1; }; \
	  ms=$$(basename $$(ls $(SRC)/operation/*.agda | head -1) .agda); \
	  md=$$(mktemp -d); \
	  printf 'module GenRef where\n\n-- WHAT THIS LEAF OWES.  The arithmetic rides %s:514.\npostulate leaf : Set\n' "$$ms" > $$md/GenRef.agda; \
	  mr=$$(scripts/check-comments.py --no-refs --dir $$md 2>&1); \
	  echo "$$mr" | grep -q "$$ms:514" \
	    || { echo "SELFTEST FAIL: the extensionless Module:NN form was missed -- the form this tree writes most often"; fail=1; }; \
	  rm -rf $$md; \
	  echo "$$lr" | grep -q '(~882)' \
	    || { echo "SELFTEST FAIL: a tilde-number alone in its parentheses was missed -- the approximate citation names no module and carries no 'line', so the other three forms walk past it"; fail=1; }; \
	  echo "$$lr" | grep -q 'see below, ~6307' \
	    || { echo "SELFTEST FAIL: a reader sent to an approximate position was missed -- the form that was copy-pasted into nine module headers"; fail=1; }; \
	  echo "$$lr" | grep -q '~1200 lines' \
	    || { echo "SELFTEST FAIL: an approximate count of lines was missed"; fail=1; }; \
	  ob=$$(scripts/check-comments.py --no-refs --dir scripts/comments-selftest/obscured 2>&1); \
	  echo "$$ob" | grep -q 'OBSCURED MARKERS' \
	    || { echo "SELFTEST FAIL: a marker doubled into the comment text was not reported -- the form no other check in this repo can see"; fail=1; }; \
	  echo "$$ob" | grep -q 'RECOVERY' \
	    || { echo "SELFTEST FAIL: the obscured marker was reported without naming which marker it was"; fail=1; }; \
	  tn=$$(scripts/check-comments.py --sample-proven 2>/dev/null); \
	  if [ -z "$$tn" ]; then \
	    echo "SELFTEST FAIL: no proven definition to build the passing fixture from — the reference assertion cannot run"; fail=1; \
	  else \
	    rd=$$(mktemp -d); \
	    { echo 'module RefOk where'; echo; \
	      echo '-- WHAT THIS LEAF OWES.  Every reference below resolves, and each is'; \
	      echo '-- written BACKTICKED or DOTTED, which is what makes it read as a'; \
	      echo '-- reference at all.'; \
	      echo '--'; \
	      echo '-- REFUTED: the unconditional form is killed at git show 919f115 — the'; \
	      echo '--   sha form, which is what a marker carries once `src` can no longer'; \
	      echo '--   STATE the route and the witness has correctly been deleted.'; \
	      printf -- '-- TWIN: `%s` is the proven counterpart whose clauses correspond.\n' "$$tn"; \
	      echo '-- RECOVERY: git show 2984f1e575d8699e8ce78975e23c530d803fc911 restores the predecessor and its whole cone.'; \
	      echo 'postulate leaf : Set'; } > $$rd/RefOk.agda; \
	    scripts/check-comments.py --dir $$rd > /dev/null 2>&1 \
	      || { echo "SELFTEST FAIL: a TWIN naming the PROVEN definition $$tn, a REFUTED naming a real refutation and a RECOVERY carrying a real sha were REJECTED"; fail=1; }; \
	    rm -rf $$rd; \
	  fi; \
	  out=$$(scripts/check-comments.py --dir scripts/comments-selftest/ref-bad 2>&1); \
	  if scripts/check-comments.py --dir scripts/comments-selftest/ref-bad > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: references naming nothing PASSED — the resolution check is dead"; fail=1; \
	  fi; \
	  echo "$$out" | grep -q 'TWIN names nothing' \
	    || { echo "SELFTEST FAIL: an unresolvable TWIN was not reported"; fail=1; }; \
	  echo "$$out" | grep -q 'RECOVERY carries no sha' \
	    || { echo "SELFTEST FAIL: a bogus sha was not reported"; fail=1; }; \
	  pn=$$(scripts/check-wiring.py --postulates 2>/dev/null | grep '\.agda:' | head -1 | awk '{print $$1}'); \
	  if [ -z "$$pn" ]; then \
	    echo "SELFTEST FAIL: the postulate ledger is unreadable — the postulate-TWIN assertion cannot run"; fail=1; \
	  else \
	    d=$$(mktemp -d); printf 'module Gen where\n\n-- WHAT THIS LEAF OWES.\n-- TWIN: `%s` is claimed as the proven counterpart.\npostulate leaf : Set\n' "$$pn" > $$d/Gen.agda; \
	    g=$$(scripts/check-comments.py --dir $$d 2>&1); \
	    if scripts/check-comments.py --dir $$d > /dev/null 2>&1; then \
	      echo "SELFTEST FAIL: a TWIN naming the live postulate $$pn PASSED — an unearned GRINDABLE class would go unnoticed"; fail=1; \
	    fi; \
	    echo "$$g" | grep -q 'STILL A POSTULATE' \
	      || { echo "SELFTEST FAIL: a TWIN naming live postulate $$pn was not reported as one"; fail=1; }; \
	    rm -rf $$d; \
	  fi; \
	  if [ $$fail -eq 0 ]; then echo "comments-selftest: PASS (all checks fire, including a TWIN naming a live postulate read from the ledger and a marker doubled into the comment text; an indented marker, an undated SEALED, a sha pointer, a bare numeral, an approximate QUANTITY carrying its unit and a resolving reference do not)"; \
	  else exit 1; fi

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
	      --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a correctly sorted, fully covered roadmap was rejected"; fail=1; }; \
	  out=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/unsorted.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/unsorted.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: an out-of-order roadmap PASSED — the sort check is dead"; fail=1; \
	  fi; \
	  for n in b-falsity d-falsity; do \
	    echo "$$out" | grep -q "$$n" \
	      || { echo "SELFTEST FAIL: $$n not reported — a real sort violation stopped firing"; fail=1; }; \
	  done; \
	  echo "$$out" | grep -q "a-grindable is" \
	    && { echo "SELFTEST FAIL: the row a violation sits below was itself reported"; fail=1; }; \
	  gap=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	           --ledger scripts/roadmap-selftest/ledger-gap.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	       --ledger scripts/roadmap-selftest/ledger-gap.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt > /dev/null 2>&1; then \
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
	  lgc=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-count.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-count.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a tier planning TWO legs where it has rows for three PASSED — the leg count is dead"; fail=1; \
	  fi; \
	  echo "$$lgc" | grep -q "^  Tier 0  legs-count.md  names 2 leg(s), wants at least 3" \
	    || { echo "SELFTEST FAIL: the short-count tier was not NAMED with its found and wanted counts"; fail=1; }; \
	  echo "$$lgc" | grep -q "^  Tier 1  legs-count.md  names" \
	    && { echo "SELFTEST FAIL: a correctly-planned tier was reported — the count is not being read per tier"; fail=1; }; \
	  echo "$$lgc" | grep -q "OVER BUDGET" \
	    && { echo "SELFTEST FAIL: a budget check fired on legs-count.md, so it does not isolate the COUNT"; fail=1; }; \
	  lgm=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-many.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-many.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a tier planning EIGHT legs PASSED — the leg ceiling is dead"; fail=1; \
	  fi; \
	  echo "$$lgm" | grep -q "^  Tier 0  legs-many.md  names 8 leg(s), wants at most 7" \
	    || { echo "SELFTEST FAIL: the over-count tier was not NAMED with its found and wanted counts"; fail=1; }; \
	  echo "$$lgm" | grep -q "^  Tier 1  legs-many.md  names" \
	    && { echo "SELFTEST FAIL: a tier planning SEVEN legs was reported — the ceiling is off by one"; fail=1; }; \
	  lgf=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-fat.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/legs-fat.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a leg carrying its own proof PASSED — the leg budget is dead"; fail=1; \
	  fi; \
	  echo "$$lgf" | grep -q "ROADMAP LEGS OVER BUDGET" \
	    || { echo "SELFTEST FAIL: the over-budget leg was not reported"; fail=1; }; \
	  echo "$$lgf" | grep -q "ROWS OVER BUDGET" \
	    && { echo "SELFTEST FAIL: the ROW budget fired on legs-fat.md, so it does not prove a leg is charged on its own budget"; fail=1; }; \
	  echo "$$lgf" | grep -q "BIG PICTURE TIER ROADMAP" \
	    && { echo "SELFTEST FAIL: the leg COUNT fired on legs-fat.md, so it does not isolate the budget"; fail=1; }; \
	  echo "$$out" | grep -q "BIG PICTURE TIER ROADMAP" \
	    && { echo "SELFTEST FAIL: the leg count fired on the sort fixture"; fail=1; }; \
	  echo "$$out" | grep -q "ROADMAP LEGS OVER BUDGET" \
	    && { echo "SELFTEST FAIL: the leg budget fired on the sort fixture"; fail=1; }; \
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
	      --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt 2>&1 \
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
	           --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt \
	           --dates-only scripts/roadmap-selftest/dated-rules.md 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	       --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt \
	       --dates-only scripts/roadmap-selftest/dated-rules.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a dated RULES file PASSED beside a clean roadmap — the CLAUDE.md half of the date check is dead"; fail=1; \
	  fi; \
	  echo "$$rul" | grep -q "dated-rules.md:" \
	    || { echo "SELFTEST FAIL: the rules file was not named in the date report — a rowless file is being skipped"; fail=1; }; \
	  scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	      --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt --src-names scripts/roadmap-selftest/src-names.txt \
	      --dates-only /dev/null > /dev/null 2>&1 \
	    || { echo "SELFTEST FAIL: a dateless extra file was rejected"; fail=1; }; \
	  stl=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/stale.md \
	           --ledger scripts/roadmap-selftest/ledger-stale.txt --census scripts/roadmap-selftest/census.txt \
	           --src-names scripts/roadmap-selftest/src-names-stale.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/stale.md \
	       --ledger scripts/roadmap-selftest/ledger-stale.txt --census scripts/roadmap-selftest/census.txt \
	       --src-names scripts/roadmap-selftest/src-names-stale.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a roadmap naming discharged postulates PASSED — the staleness check is dead"; fail=1; \
	  fi; \
	  for n in b-discharged c-vanished d-gone-parent; do \
	    echo "$$stl" | grep -q "$$n" \
	      || { echo "SELFTEST FAIL: $$n not reported — one arm of the staleness check stopped firing"; fail=1; }; \
	  done; \
	  echo "$$stl" | grep -q "  a-live$$" \
	    && { echo "SELFTEST FAIL: a still-live postulate was reported stale"; fail=1; }; \
	  cln=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/sorted.md \
	           --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt \
	           --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  echo "$$cln" | grep -q "STALE ROWS" \
	    && { echo "SELFTEST FAIL: the staleness check fired on a clean roadmap — a CITED precedent or a descriptive head is being read as a claim, and earning GRINDABLE requires naming a proven precedent"; fail=1; }; \
	  mis=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-missing.md \
	           --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt \
	           --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-missing.md \
	       --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt \
	       --src-names scripts/roadmap-selftest/src-names.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a row with NO evidence field PASSED — the field is optional again, which is the one thing it must not be"; fail=1; \
	  else \
	    echo "$$mis" | grep -q "NO EVIDENCE FIELD" \
	      || { echo "SELFTEST FAIL: a missing evidence field was rejected for the wrong reason"; fail=1; }; \
	  fi; \
	  stl2=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-stale.md \
	            --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt \
	            --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-stale.md \
	       --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census.txt \
	       --src-names scripts/roadmap-selftest/src-names.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: an evidence field disagreeing with the headers PASSED — the field can rot, which is the whole reason it is derived"; fail=1; \
	  else \
	    echo "$$stl2" | grep -q "EVIDENCE FIELD IS STALE" \
	      || { echo "SELFTEST FAIL: a stale evidence field was rejected for the wrong reason"; fail=1; }; \
	  fi; \
	  une=$$(scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-unearned.md \
	           --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census-notwin.txt \
	           --src-names scripts/roadmap-selftest/src-names.txt 2>&1); \
	  if scripts/check-roadmap.py --file scripts/roadmap-selftest/evid-unearned.md \
	       --ledger scripts/roadmap-selftest/ledger.txt --census scripts/roadmap-selftest/census-notwin.txt \
	       --src-names scripts/roadmap-selftest/src-names.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a GRINDABLE row naming no proven twin PASSED — the class is a parking space again"; fail=1; \
	  else \
	    echo "$$une" | grep -q "NAME NO PROVEN TWIN" \
	      || { echo "SELFTEST FAIL: an unearned GRINDABLE was rejected for the wrong reason"; fail=1; }; \
	  fi; \
	  if [ $$fail -eq 0 ]; then echo "roadmap-selftest: OK"; else exit 1; fi

# WRITES the evidence field on every classed row, from the postulates' own
# headers.  The field is DERIVED -- which is the whole reason it may be
# mandatory without producing filler.  A hand-typed census is the failure this
# repo already paid for once: true when written, silently wrong later, read by
# nobody who could tell.  `roadmap-check` recomputes it and fails on a
# mismatch, so the roadmap cannot drift from the headers it summarises.
roadmap-evidence:
	@scripts/check-roadmap.py --fix-evidence

# THE ROADMAP MUST MOVE IN EVERY COMMIT, BECAUSE A LEG IS ONE COMMIT.  Either the
# leg landed -- retire it, promote the other two, write a new third -- or the
# session could not finish it, in which case the FIRST leg is rewritten as the
# work that remains.  Neither leaves the file untouched.  The check is
# deliberately dumb (did it change against HEAD) because what it defends cannot
# be resolved by a machine: `roadmap-check` verifies that a row's NAME exists,
# and nothing can verify that the plan a leg describes is still the plan.
# See docs/roadmap-check.md.
roadmap-moved:
	@scripts/check-roadmap-moved.py

# PROVES roadmap-moved IS LOAD-BEARING, in BOTH directions -- and the third
# fixture is the one that matters: a trailing-whitespace edit is the cheapest
# way to satisfy a did-it-change check, so it must NOT satisfy this one.
roadmap-moved-selftest:
	@fail=0; \
	  scripts/check-roadmap-moved.py --file scripts/roadmap-selftest/moved-diff.md \
	      --baseline-file scripts/roadmap-selftest/moved-same.md > /dev/null \
	    || { echo "SELFTEST FAIL: a genuinely changed roadmap was rejected"; fail=1; }; \
	  if scripts/check-roadmap-moved.py --file scripts/roadmap-selftest/moved-same.md \
	       --baseline-file scripts/roadmap-selftest/moved-same.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: an UNCHANGED roadmap PASSED — the check is dead"; fail=1; \
	  fi; \
	  if scripts/check-roadmap-moved.py --file scripts/roadmap-selftest/moved-space.md \
	       --baseline-file scripts/roadmap-selftest/moved-same.md > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a trailing-whitespace edit PASSED as movement — the check can be satisfied by saying nothing"; fail=1; \
	  fi; \
	  if [ $$fail -eq 0 ]; then echo "roadmap-moved-selftest: OK"; else exit 1; fi
	@scripts/roadmap-moved-git-selftest

# SETTLE RISK NEAR THE TRUNK: while a tier holds an open FALSITY row,
# a commit may not BANK a GRINDABLE row of that tier.  The pull
# it resists is structural rather than careless -- a risky leg often ends in a
# finding, a finding-only commit reads as unfinished, and a mechanical row gets
# closed alongside it to make the commit whole.  See docs/roadmap-check.md.
roadmap-order:
	@scripts/check-roadmap-order.py

# PROVES roadmap-order IS LOAD-BEARING, and -- the harder half -- that it stays
# QUIET on the four shapes the proof must remain free to take.  A check that
# fired on a deletion or a reclassification would stop the proof changing shape,
# which is a worse failure than the one it prevents.
roadmap-order-selftest:
	@fail=0; S=scripts/roadmap-selftest; \
	  if scripts/check-roadmap-order.py --file $$S/order-banked.md \
	       --baseline-file $$S/sorted.md --ledger $$S/order-ledger-banked.txt \
	       --src-names $$S/order-src-names.txt --headers $$S/order-headers-none.txt \
	       > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a GRINDABLE row banked under an open FALSITY PASSED — the check is dead"; fail=1; \
	  fi; \
	  scripts/check-roadmap-order.py --file $$S/sorted.md --baseline-file $$S/sorted.md \
	      --ledger $$S/ledger.txt --src-names $$S/src-names.txt \
	      --headers $$S/order-headers-none.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a roadmap that banked nothing was rejected"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-banked.md --baseline-file $$S/sorted.md \
	      --ledger $$S/order-ledger-banked.txt --src-names $$S/src-names.txt \
	      --headers $$S/order-headers-none.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a row DELETED from the tree was read as discharged — the proof cannot drop a statement"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-reclass.md --baseline-file $$S/sorted.md \
	      --ledger $$S/ledger.txt --src-names $$S/order-src-names.txt \
	      --headers $$S/order-headers-none.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a RECLASSIFIED row was read as discharged — the proof cannot re-rank its own risk"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-banked-t1.md --baseline-file $$S/sorted.md \
	      --ledger $$S/order-ledger-t1.txt --src-names $$S/order-src-t1.txt \
	      --headers $$S/order-headers-none.txt > /dev/null \
	    || { echo "SELFTEST FAIL: ANOTHER tier's open FALSITY blocked a discharge — the law is per-tier"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-renumbered.md --baseline-file $$S/sorted.md \
	      --ledger $$S/order-ledger-retired.txt --src-names $$S/order-src-names.txt \
	      --headers $$S/order-headers-none.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a RETIRED tier's discharge was charged to the tier that took its number — a tier is its rows"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-banked.md --baseline-file $$S/sorted.md \
	      --ledger $$S/order-ledger-banked.txt --src-names $$S/order-src-names.txt \
	      --headers $$S/order-headers-prereq.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a NAMED prerequisite was refused — the carve-out is dead"; fail=1; }; \
	  scripts/check-roadmap-order.py --file $$S/order-banked.md --baseline-file $$S/sorted.md \
	      --ledger $$S/order-ledger-banked.txt --src-names $$S/order-src-names.txt \
	      --headers $$S/order-headers-none.txt \
	      --definitions $$S/order-defs-conversion.txt > /dev/null \
	    || { echo "SELFTEST FAIL: a CONVERSION was read as a discharge — the repo's central move cannot be held"; fail=1; }; \
	  if scripts/check-roadmap-order.py --file $$S/order-banked.md --baseline-file $$S/sorted.md \
	       --ledger $$S/order-ledger-banked.txt --src-names $$S/order-src-names.txt \
	       --headers $$S/order-headers-none.txt \
	       --definitions $$S/order-defs-none.txt > /dev/null 2>&1; then \
	    echo "SELFTEST FAIL: a body standing on NOTHING open was excused as a conversion — the exemption is blanket"; fail=1; \
	  fi; \
	  if [ $$fail -eq 0 ]; then echo "roadmap-order-selftest: PASS (banking fires, and so does a body standing on nothing open; deleting, reclassifying, another tier's risk, a retired tier's number, a named prerequisite and a conversion do not)"; else exit 1; fi

# SEARCH FIRST, made cheap and impossible to scope wrong: search the declared
# TYPE of every statement in the tree.  dup-check catches a duplicate only once
# both copies exist; this is the same law applied BEFORE the writing.  It walks
# all of the tree always — a search scoped to two files once missed what was
# there — so there is deliberately no argument that narrows it.
# Q's words are ANDed against the type text and the name, so `Q='⊑ lub'`
# finds the statements mentioning both, in either order.  Search for the
# OPERATOR and the RELATION, not the name you imagine — names here are
# idiosyncratic and a name-guess reliably misses.
#   make find Q='⊑ lub'      make find Q='Rel connectᴷ'
find:
	@scripts/find-lemma.py "$(Q)"

# THE SAME SEARCH OVER PROSE, because a FINDING is not a type.  `find` cannot
# see a dead route, a coverage boundary, a ruling or a measured trap -- those
# live in comment blocks and in the documents -- and plain grep returns one
# line out of a forty-line header, which is a hit and not an answer.  This
# returns the BLOCK, which is the unit a finding is written in, and for an
# agda hit the declaration the block sits above.  Q is a REGEX, case-blind.
# THE ATTIC TOO, and it matters more here than it does for `find`: a deleted
# STATEMENT is still findable by name with `git log -S`, while a dead route
# names nothing and a coverage boundary names a probe that went with it — so
# this is the only search that can surface either at all.
#   make find-prose Q='phantom'   make find-prose Q='never parks|unbounded'
find-prose:
	@scripts/find-prose.py "$(Q)"

# THE REMAINING-WORK LEDGER: every postulate in the tree, by name.  A grep for
# `^postulate` finds the BLOCK HEADERS, not the names inside them, so it is
# not the ledger and never was.  PROOF-STATE must carry a row for each of
# these, in exactly one tier.
postulates:
	@scripts/check-wiring.py --postulates

# THE LEDGER'S SHAPE, PUSHED TO A PHONE.  A gate is the one moment the tree is
# known-good and a commit is next, so the gate targets call this on the way out
# -- green and red alike.  Typed by hand it prints the same census locally.  No
# number here is stored anywhere: all of it is derived at send time, which is
# why the roadmap can go on carrying no aggregates.  See docs/notify.md.
notify:
	@scripts/notify.py "$(or $(V),manual)"

# THE TYPESCRIPT HALF OF THE GATE, AND IT IS CHEAP BY CONSTRUCTION.  The TS
# side is the oracle's other half, so a TS tree that does not compile leaves
# the oracle nothing to compare against.  All three run in seconds and need
# no Agda, so they sit with the other textual checks.
ts-check:
	@cd $(CURDIR)/typescript && npm run typecheck

ts-lint:
	@cd $(CURDIR)/typescript && npm run lint

ts-format-check:
	@cd $(CURDIR)/typescript && npm run format:check

ts-gate: ts-check ts-lint ts-format-check
	@echo "ts-gate: GREEN (tsc, eslint, prettier)"

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

# ─────────────────────────────────────────────────────────────────────────
# DETACHED BUILDS -- always launch a long target through `make bg`.
#
#     make bg T=gate                        detach this under run_in_background
#     make bg T=gate LOG=/tmp/g.log   explicit log path
#     make bg-check T=gate                  THE VERDICT: green, red + tail, running
#     make bg-wait  T=gate                  blocks until terminal
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
