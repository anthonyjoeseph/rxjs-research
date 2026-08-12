#!/usr/bin/env python3
"""The FAST DEV LOOP: typecheck mutual-block members against POSTULATED siblings.

THIS DOCSTRING IS THE ARCHIVE for the 2026-08-11 performance investigation.
Every number is measured on this machine (24 GB, 14 cores) under Agda 2.8.0.

WHY THIS EXISTS.  86-91% of `make agda` is Agda's occurrence/polarity
("Positivity") pass over two big mutual blocks, and THAT PASS CANNOT BE SWITCHED
OFF.  Three routes were measured and all three failed -- do not re-attempt:
  * NO_POSITIVITY_CHECK on the block is a NO-OP: Agda accepts it only before a
    data/record definition or a mutual block containing one, and these blocks
    declare neither (InvalidNoPositivityCheckPragma).
  * --no-positivity-check on the command line is REJECTED, because agda-stdlib
    is --safe (EXIT=42 in 267ms, at Data/Unit/Base.agda).
  * as a per-module OPTIONS pragma it is ACCEPTED AND BUYS NOTHING: 805s
    Positivity against 779s without it.  The pass computes the occurrence graph;
    the option only suppresses the strict-positivity VERDICT on datatypes.
MEMBER COUNT DOES NOT PREDICT COST -- TERM SIZE DOES.  Measured @2.8: Caps-Face's
83-member block costs 15.2s of Positivity; Subscribe-Face's 15-member block
costs 300s.  So "split the big block up" is not the lever it looks like, and
two refactors were measured and REJECTED on that basis:
  * Caps-Face's 83-member block is 100% SPURIOUS -- zero cycles, held open by
    three gratuitous forward declarations sweeping in 80 unrelated definitions.
    Dissolving it saves nothing: the whole module is 63.9s.
  * Wet's 36-member block contains a genuine 14-member SCC.  Hoisting the other
    22 into their own module is worth 255s -> 220s of Positivity, i.e. ~35s of a
    ~17-minute build, for a large refactor with real meta-coupling risk.  No.
Use `--list` to see which members are in a genuine cycle before considering it.
Also closed: +RTS -A128m is noise (944s solo vs 927s baseline -- not GC-bound),
and telescope width is not the cost (all 19 clique signatures as bare postulates
cost 9.0s with Positivity absent).  Upgrading 2.7.0.1 -> 2.8.0 was the ONE lever
that moved it: 927s -> 384s total, 779s -> 300s Positivity (2.6x).

What the pass IS sensitive to is mutual-block MEMBERSHIP, steeply and
superlinearly: in Subscribe-Face ONE real body costs 63ms of Positivity and
FIFTEEN cost 300s.  Its 904-line prelude of 45 independent lemmas costs 7.8s.
So module SIZE is nearly irrelevant and BLOCK size is everything, and the loop
is not "disable a check", it is "check a few bodies at a time".

HOW IT WORKS.  Generated modules land in agda/_dev/ (gitignored) holding the
file VERBATIM except that block members become `postulate`s at their exact
existing signatures -- all but the FOCUS batch, which keeps its real bodies.
agda/src is NEVER written to, and the generated names cannot collide with real
interfaces in _build.  Mutual blocks are recovered exactly by reproducing Agda's
own rule (a block runs from the first forward signature until every pending
signature has a definition), because both heavy modules use IMPLICIT blocks --
Subscribe-Face declares subscribeE-caps at line 936 and defines it at 2751, and
there is no `mutual` keyword anywhere to grep for.

MEASURED 2026-08-12, on a COHERENT cache (i.e. after the -W flag mismatch that
used to make `make agda` and this tool invalidate each other was fixed -- every
number recorded before that date is suspect, and suspect in the SLOW direction).
Two regimes, and quoting the wrong one is how the old figures misled:

  COLD is the one the BUDGETS are set from, because cold is the normal case:
  you edit a file, so its generated module has new content and nothing is
  cached for it.  Warm only happens when you re-run having changed nothing,
  which is not the loop.  (Anthony, 2026-08-12.)

  WARM (src unchanged since the last dev run) -- 12 modules, 122.4s
    Caps-Face 24.1  Wet 18.4  Caps 15.5  Subscribe-Face 11.8  Keeps-Ring 9.6
    Caps-Sadd 9.2  Evaluator 8.5  Caps-Depth 8.2  Exp 3.8  Provenance 3.7
    Frame-Width 3.6  VWF/Part1 6.0
  COLD, everything (after a `make agda`, or a pull) -- 12 modules, 242.5s
    Caps-Face 72.6  Wet 55.8  Subscribe-Face 31.0  Caps 21.0  (rest ~unchanged)
  COLD, one file (the real loop: you edited ONE module, the other 11 stay warm)
    that module's cold cost + ~122s; worst case ~171s if it is Caps-Face

  one member    ~6s      <- the grind loop, and the only number that matters
                            for iteration speed
  make agda     802s (13m22s) for the full gate, 41 modules rebuilt, @2.8

The steady-state figures match the pre-2.8 warm claims (Subscribe-Face 11.3s,
Wet 17.0s), which were accurate all along -- the cache bug just made them
unreachable in practice, because any gate run destroyed the warm state.

THE MEASUREMENT THAT DECIDED THE DESIGN.  Profiling one focus run: 5.6s total,
of which 4.9s is DESERIALIZATION and 63ms is Positivity (Typing 370ms).  Once
the block is broken, the proof work is not the cost either -- loading imported
interfaces is, and that is a per-PROCESS toll.  Three consequences:
  * MAXIMUM PARALLELISM IS WRONG.  One process per member, 12-way: runs that
    cost 5.6s solo took 13-24s each, 2.5 min wall.  Deserialization is
    memory-bandwidth bound and does not scale with cores.
  * BATCHING is the lever.  Whole-file wall by --batch: 1->42.3s 2->18.5s
    3->18.6s 4->17.2s 5->23.6s 8->45.7s.  The U is the two costs crossing: too
    small pays the toll too often, too large rebuilds the block.  Default 4.
  * A SHARED CONTEXT module, checked once, carries the prelude and every other
    non-mutual body, so focus runs import it instead of re-checking it apiece.
Batches are balanced by body size (LPT): wall is `context + SLOWEST batch`, and
file order put the three biggest bodies in one batch (16.1s against 8.0s).

WHAT A GREEN RUN DOES NOT MEAN.  Two things are given up, and the first is not
minor:
  1. TERMINATION OF THE REAL MUTUAL RECURSION IS NOT CHECKED.  In this proof the
     mutual recursion IS the induction, so a body recursing on a non-decreasing
     measure passes here and fails `make agda` -- a proof-SHAPE failure, not a
     typo.  Partially recovered: SELF-recursion is real, and so is recursion
     WITHIN a batch (the batch's signatures are forward-declared, so Agda puts
     them in one mutual block).  Only recursion crossing out of the batch is lost.
  2. POSTULATES DO NOT REDUCE.  A clause needing a sibling to unfold under
     conversion can pass here and fail for real; witness arithmetic (j + j'
     versus suc (j + j')) is where it bites.  Caps-Face is the module where this
     is fatal -- see NOT_DEV_CHECKABLE.
Everything else is checked in full: types, implicits, metas, and coverage.  So:
DEV-GREEN MEANS THE TYPES LINE UP, NOT THAT THE PROOF IS VALID.  `make agda`
stays the merge gate.  `make agda-dev-selftest` (--falsify) proves the loop is
load-bearing: it flips one proj1/proj2 in a real body in src, demands RED, and
restores the file byte-for-byte.  RUN IT WHENEVER THE STUBBING LOGIC CHANGES --
a generator bug that dropped the focus body would otherwise read as a fast pass.

TWO BEHAVIOURS THE CODE NEEDED THAT THE DESIGN DID NOT ANTICIPATE:
  * A SIGNATURE'S METAS CAN BE SOLVED BY A SIBLING'S BODY -- meta solving is a
    whole-mutual-block affair.  Wet's connectWrap-wet has a `let ... if c ...`
    in its type, pinned by sharedConnect-wet's body; alone as a postulate it
    fails with UnsolvedMetaVariables.  Rather than weaken the run with
    --allow-unsolved-metas, such members and their callers are KEPT REAL (which
    checks strictly more), and the set is cached by source mtime because
    rediscovering it costs a failed context run (Wet: 35.9s cold, 17.0s warm).
  * THE FAILURE DUMP MUST BE THE TAIL, NOT THE HEAD.  Agda prints warnings first
    and dies last, and Measures.agda emits a standing RewritesNothing warning
    that buried the real error under a head-limited dump.

  scripts/agda-dev.py                      EVERY dev-checkable module
  scripts/agda-dev.py --dirty              only modules you have edited
  scripts/agda-dev.py <file>               one module, every member
  scripts/agda-dev.py <file> <member>      one member -- the actual grind loop
  scripts/agda-dev.py --list <file>        its block structure, no typechecking
  scripts/agda-dev.py --falsify            the self-test

Flags (both OPT-IN, and they stay that way on purpose):
  --scope   --only-scope-checking.  MEASURED TO BUY NOTHING HERE (11.1s against
            11.3s): the run is 4.9s of deserialization and skipping the ~0.5s of
            typing is invisible.  Kept as a fail-fast for syntax and naming
            errors, not as a speedup.  Hazard: with a DIRTY dependency it would
            write a scope-only interface and cost a rebuild.
  --holes   --allow-unsolved-metas + --allow-incomplete-matches.  Off by default
            because a silently passing ? would break "the types line up".
"""
from __future__ import annotations

import argparse
import copy
import resource
import hashlib
import os
import re
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass, field

# MODULES THIS TOOL CANNOT DEV-CHECK, with the reason and the exact error it
# produces, so nobody rediscovers them by running into a red wall.  They are
# skipped by whole-project mode and still runnable by name, which is how a fix
# gets re-tested.  Measured 2026-08-11 over the whole claim graph.
#
# The first entry is an INHERENT limit of the approach, not a bug: the other
# four are parser gaps and are fixable.
# Modules this tool cannot accelerate, with the reason, so nobody rediscovers
# them by running into a red wall.  Skipped by whole-project mode, still
# runnable by name.  Empty is the goal, and as of 2026-08-11 it is empty:
# Verify-Well-Formed was the last entry and it was SPLIT instead (5,816 lines,
# 276 members, zero cycles -- nothing to break, so the file itself was the
# problem).  Add an entry only after measuring, and say what the fix would be.
NOT_DEV_CHECKABLE: dict[str, str] = {}

# CONCURRENCY IS A MEMORY BUDGET, NOT A CONSTANT.  CLAUDE.md's standing ceiling
# ("at most TWO heavyweight checks at once") is about REAL checks of the big
# modules, which peak ~5.2 GB.  A stubbed dev run is nothing like that: measured
# 2026-08-11, a self-contained Caps-Face batch peaks 0.6-0.7 GB, so a flat cap of
# 2 left it running 22 batches two at a time for no reason.
#
# So the cap is computed from the FIRST run's actual peak RSS rather than
# guessed: fast, small runs get wide concurrency and genuinely heavy ones get
# the two-at-a-time ceiling automatically.  Ignoring memory entirely is what
# OOM'd this machine, so the budget stays conservative -- half of physical RAM.
MEM_FRACTION = 0.5


def total_ram() -> int:
    try:
        return int(subprocess.run(["sysctl", "-n", "hw.memsize"], capture_output=True,
                                  text=True).stdout.strip())
    except Exception:
        return 8 << 30


def child_peak_bytes() -> int:
    """Peak RSS of the largest child so far.  macOS reports bytes, Linux KB."""
    m = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    return m if sys.platform == "darwin" else m * 1024


def jobs_for(peak: int, ceiling: int) -> int:
    if peak <= 0:
        return 1
    return max(1, min(ceiling, int(total_ram() * MEM_FRACTION // peak)))

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
AGDA = os.path.join(REPO, "agda")
SRC = os.path.join(AGDA, "src")
DEV = os.path.join(AGDA, "_dev")

# A top-level line opening a construct we keep VERBATIM and never stub.  Its
# indented body comes along with it.  `mutual`/`private`/`abstract` blocks are
# deliberately opaque: stubbing inside one would need the nested block
# structure, and neither heavy module uses them (both use implicit top-level
# mutual blocks, which is what this tool understands).
OPAQUE = re.compile(r"^(private|abstract|mutual|postulate|instance)\b|^(data|record)\s")
# Lines that are neither declarations nor bodies: they pass through in place.
PASSTHRU = re.compile(r"^(open|import|module|infix\w*|syntax|pattern|variable)\b|^\{-#")
# `name : type`.  The name may be any Agda operator-ish token; what disqualifies
# a line is a colon that belongs to a binder instead, which cannot happen at
# indent 0 before the name's own colon.
SIG = re.compile(r"^([^\s(){};]+)\s+:(\s|$)")
# `name args = ...`, `name args with ...`, or a with-continuation `... | p = e`.
CLAUSE = re.compile(r"^([^\s(){};]+)(\s|$)")


@dataclass
class Item:
    kind: str  # 'sig' | 'clauses' | 'pass' | 'opaque' | 'comment'
    name: str | None
    start: int  # 0-based, inclusive
    end: int  # 0-based, exclusive
    block: int | None = None  # index into Parsed.blocks, for sig/clauses


@dataclass
class Block:
    members: list[str] = field(default_factory=list)
    first_item: int = 0


@dataclass
class Parsed:
    lines: list[str]
    items: list[Item]
    blocks: list[Block]
    options: list[int]  # line indices of leading OPTIONS pragmas
    module_line: int | None


def open_clause(items: list[Item], name: str | None) -> int | None:
    """Index of the clause group this line continues, or None.

    Only comments and blanks may separate a clause from its group; anything
    else closes it.
    """
    for k in range(len(items) - 1, -1, -1):
        if items[k].kind == "comment":
            continue
        if items[k].kind == "clauses" and (name is None or items[k].name == name):
            return k
        return None
    return None


def absorb(items: list[Item], k: int) -> None:
    """Drop the comment items after `items[k]`; its span now covers them."""
    del items[k + 1 :]


def parse(path: str) -> Parsed:
    lines = open(path, encoding="utf-8").read().split("\n")
    items: list[Item] = []
    module_line = None
    options: list[int] = []

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        # Blank lines and comments attach to whatever declaration follows, so a
        # stubbed-out body does not strand its own header comment above an
        # unrelated definition.
        if not line.strip() or line.lstrip().startswith("--") or line[0].isspace():
            if line and not line[0].isspace():
                pass  # a top-level comment; fall through to the comment item
            elif line.strip():
                # An indented line with no open item: only possible in a
                # malformed file.  Keep it verbatim rather than dropping it.
                items.append(Item("comment", None, i, i + 1))
                i += 1
                continue
            j = i
            while j < n and (not lines[j].strip() or lines[j].lstrip().startswith("--")):
                j += 1
            items.append(Item("comment", None, i, j))
            i = j
            continue

        # A top-level construct: consume it plus every following indented line.
        def body_end(k: int) -> int:
            k += 1
            while k < n:
                if lines[k].strip() and not lines[k][0].isspace():
                    break
                k += 1
            # Trailing blanks/comments belong to the NEXT item, not this one.
            while k - 1 > i and not lines[k - 1].strip():
                k -= 1
            return k

        end = body_end(i)
        if line.startswith("{-#") and "OPTIONS" in line:
            options.append(i)
            items.append(Item("pass", None, i, end))
        elif line.startswith("module ") and module_line is None:
            module_line = i
            items.append(Item("pass", None, i, end))
        elif PASSTHRU.match(line):
            items.append(Item("pass", None, i, end))
        elif OPAQUE.match(line):
            items.append(Item("opaque", None, i, end))
        elif line.startswith("..."):
            # A with-continuation: part of the clause group above it.
            if (k := open_clause(items, None)) is not None:
                items[k].end = end
                absorb(items, k)
            else:
                items.append(Item("comment", None, i, end))
        elif m := SIG.match(line):
            items.append(Item("sig", m.group(1), i, end))
        elif m := CLAUSE.match(line):
            name = m.group(1)
            # Clauses of one function are contiguous up to comments and blanks,
            # so a same-name group after a comment is the SAME definition -- not
            # a second one.  Getting this wrong split subscribeE-caps's body
            # into eleven phantom "blocks".
            if (k := open_clause(items, name)) is not None:
                items[k].end = end
                absorb(items, k)
            else:
                items.append(Item("clauses", name, i, end))
        else:
            items.append(Item("comment", None, i, end))
        i = end

    # IMPLICIT MUTUAL BLOCKS.  Agda groups declarations into one mutual block
    # from the first forward type signature until every pending signature has a
    # definition.  That rule is exact, and it is why this file has no `mutual`
    # keyword to look for: Subscribe-Face declares subscribeE-caps at line 936
    # and defines it at 2751, and everything between is one block.
    blocks: list[Block] = []
    pending: list[str] = []
    cur: Block | None = None
    for idx, it in enumerate(items):
        if it.kind == "sig":
            if cur is None:
                cur = Block(first_item=idx)
            pending.append(it.name)
            it.block = len(blocks)
            if it.name not in cur.members:
                cur.members.append(it.name)
        elif it.kind == "clauses":
            if cur is None:
                # A definition with no signature of its own: its own block.
                cur = Block(first_item=idx)
                cur.members.append(it.name)
                it.block = len(blocks)
                blocks.append(cur)
                cur = None
                continue
            it.block = len(blocks)
            if it.name in pending:
                pending.remove(it.name)
            if not pending:
                blocks.append(cur)
                cur = None
    if cur is not None:
        blocks.append(cur)  # unfinished (a file mid-edit); treat as a block

    return Parsed(lines, items, blocks, options, module_line)


def heavy_blocks(p: Parsed) -> list[int]:
    """Blocks worth stubbing: 2+ members.  A 1-member block costs ~nothing."""
    return [i for i, b in enumerate(p.blocks) if len(b.members) > 1]


def sig_text(p: Parsed, name: str) -> list[str] | None:
    for it in p.items:
        if it.kind == "sig" and it.name == name:
            return p.lines[it.start : it.end]
    return None


def render_ctx(p: Parsed, mod: str, foci: list[str] = [],
               stub_lines: dict[str, tuple[int, int]] | None = None,
               hoist: list[str] = [], force_stub: list[str] = [],
               real_lines: dict[str, tuple[int, int]] | None = None) -> str:
    """The SHARED CONTEXT: the file with every heavy-block member postulated.

    Checked ONCE per dev run.  Every non-mutual body in the file is real here,
    so this run is what actually verifies the prelude -- and the focus runs then
    import it instead of re-checking those 900 lines apiece.  Skipping that
    sharing was measured at >2.5 min for one file; with it, ~25 s.
    """
    heavy = set(heavy_blocks(p))
    out: list[str] = []
    emitted: set[int] = set()

    for it in p.items:
        if it.kind == "pass" and it.start == p.module_line:
            out.append(f"module {mod} where")
            continue
        if it.kind == "pass":
            out.extend(publicize(p.lines[it.start : it.end]))
            continue
        if it.block is not None and it.block in heavy:
            if it.block not in emitted:
                emitted.add(it.block)
                b = p.blocks[it.block]
                # TYPE-LEVEL members come FIRST: the stub signatures below
                # mention them (walkOK, NodeCaps, FrameFace), so a postulate
                # block placed above their definitions is 19 NotInScope errors.
                for m in hoist:
                    if m in b.members:
                        for kind in ("sig", "clauses"):
                            for jt in p.items:
                                if jt.kind == kind and jt.name == m:
                                    out.extend(p.lines[jt.start : jt.end])
                        out.append("")
                # Remember where the block starts: if nothing turns out to need
                # stubbing (every member is a focus, hoisted, or acyclic), the
                # header must be REMOVED rather than left standing.  An empty
                # `postulate` is an EmptyPostulate warning on every run, and
                # spurious warnings in this tool's output are precisely what it
                # exists to prevent -- a loop nobody reads the output of is not
                # a loop.
                hdr = len(out)
                out += ["", f"-- agda-dev: mutual block of {len(b.members)} members,",
                        "-- POSTULATED at their exact existing signatures.", "postulate"]
                body_at = len(out)
                cyc = scc_of(p, b.members)
                for m in b.members:
                    if m in foci or m in hoist or (m not in cyc and m not in force_stub):
                        continue
                    first = len(out) + 1
                    for ln in sig_text(p, m) or []:
                        out.append(("  " + ln) if ln.strip() else "")
                    if stub_lines is not None:
                        stub_lines[m] = (first, len(out))
                if len(out) == body_at:
                    del out[hdr:]
                else:
                    out.append("")
            # A KEPT-REAL member stays EXACTLY WHERE IT WAS.  Relocating these
            # to the head of the block was one bug producing all 22 of
            # Caps-Face's NotInScope errors: a body originally at line 7500 got
            # emitted at 4259, ahead of the `abstract` block defining what it
            # calls.  Position carries scope; only the stubs may move.
            # Acyclic members are NEVER stubbed -- stubbing exists to break a
            # cycle, and a postulate that replaces a perfectly orderable
            # definition only costs reduction (the SplitError class) while
            # saving nothing.  They, and the foci, stay exactly where they are.
            cyc = scc_of(p, p.blocks[it.block].members)
            if ((it.name in foci or it.name not in cyc)
                    and it.name not in hoist and it.name not in force_stub):
                first = len(out) + 1
                out.extend(p.lines[it.start : it.end])
                if real_lines is not None and it.kind == "clauses":
                    real_lines[it.name] = (first, len(out))
                out.append("")
            continue
        out.extend(p.lines[it.start : it.end])

    return "\n".join(out).rstrip() + "\n"


def render_focus(p: Parsed, mod: str, ctx: str, foci: list[str],
                 keep: list[str] = []) -> str:
    """A BATCH of real bodies, against the shared context's postulated siblings.

    `hiding (…)` is what lets the real definitions replace their stubs.  Two
    consequences worth having: a body's SELF-recursion still resolves to the
    real definition, so self-recursive termination IS checked; and within a
    batch, mutual recursion is checked too, because the batch's signatures are
    forward-declared and Agda therefore puts them in one mutual block.  Only
    recursion that crosses OUT of the batch is lost.

    Why batch at all: a focus run costs 5.6 s of which 4.9 s is deserializing
    imported interfaces -- a per-PROCESS toll, paid whether the process checks
    one body or ten.  Batching trades that toll against a bigger mutual block,
    and the block cost is negligible until the batch gets large.
    """
    out: list[str] = []
    for i in p.options:
        out.append(p.lines[i])
    out.append(f"module {mod} where")
    out.append("")
    # Qualified-only imports do not re-export through the context, so they are
    # repeated here.  `open import` lines are not: the context re-exports them
    # publicly, and importing the same name twice invites an ambiguity error.
    # Repeat the original imports, not just qualified ones.  INSTANCE arguments
    # are resolved from what is OPENED, and re-export through the context does
    # not carry them: Caps.agda's `NonZero 2` had no candidate.  Importing the
    # same definition twice is fine -- Agda only complains when two routes
    # disagree, which they cannot here.
    for it in p.items:
        if it.kind == "pass" and p.lines[it.start].startswith(("import ", "open import ")):
            out.extend(p.lines[it.start : it.end])
    shown = list(dict.fromkeys(keep + foci))
    out.append(f"open import {ctx} hiding ({'; '.join(shown)})")
    out.append("")
    if keep:
        out.append("-- agda-dev: kept REAL because the focus reduces them and a")
        out.append("-- postulate would not: " + ", ".join(keep))
    out.append("-- agda-dev: THE FOCUS BODIES, verbatim from the real module.")
    out.append("-- Signatures first so a call between them resolves: that makes")
    out.append("-- the batch one mutual block, which is checked for real.")
    for kind in ("sig", "clauses"):
        for it in p.items:
            if it.kind == kind and it.name in shown:
                out.extend(p.lines[it.start : it.end])
                out.append("")
    return "\n".join(out).rstrip() + "\n"


def publicize(block: list[str]) -> list[str]:
    """Make an `open import` re-export, so focus modules see it through the ctx.

    `public` goes at the END of the statement, after any using/hiding/renaming,
    so it is appended to the last line of the (possibly multi-line) block.
    """
    if not block or not block[0].startswith("open"):
        return block
    if any(re.search(r"\bpublic\b", ln) for ln in block):
        return block
    out = list(block)
    for k in range(len(out) - 1, -1, -1):
        if out[k].strip():
            out[k] = out[k].rstrip() + " public"
            break
    return out


def scc_of(p: Parsed, members: list[str]) -> dict[str, int]:
    """Which members are in a genuine CYCLE, and which are only along for the ride.

    Agda opens a mutual block at the first forward signature and closes it when
    every pending signature has a body, so a block's SIZE reflects declaration
    ORDER, not recursion.  Measured 2026-08-11: Caps-Face's 83-member block has
    ZERO cycles in it -- three gratuitous forward declarations swept in 80
    unrelated definitions.  Wet's 36 contain a real 14 and a real 3.
    Edges are textual (bodies and signatures, comments stripped), so a missed
    edge under-reports a cycle -- which is the safe direction for a diagnostic.
    """
    S = set(members)
    g = {m: set() for m in members}
    for it in p.items:
        if it.name in S and it.kind in ("sig", "clauses"):
            txt = "\n".join(l.split("--")[0] for l in p.lines[it.start : it.end])
            for o in members:
                if o != it.name and re.search(
                        r"(?<![\w\-])" + re.escape(o) + r"(?![\w\-])", txt):
                    g[it.name].add(o)
    index: dict[str, int] = {}
    low: dict[str, int] = {}
    stack: list[str] = []
    on: set[str] = set()
    out: dict[str, int] = {}
    counter = [0, 0]

    def strong(v: str) -> None:
        # iterative Tarjan: these blocks reach 83 members and recursion depth
        # is not worth risking on a diagnostic
        work = [(v, iter(g[v]))]
        index[v] = low[v] = counter[0]; counter[0] += 1
        stack.append(v); on.add(v)
        while work:
            u, it2 = work[-1]
            for w in it2:
                if w not in index:
                    index[w] = low[w] = counter[0]; counter[0] += 1
                    stack.append(w); on.add(w)
                    work.append((w, iter(g[w])))
                    break
                if w in on:
                    low[u] = min(low[u], index[w])
            else:
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[u])
                if low[u] == index[u]:
                    comp = []
                    while True:
                        w = stack.pop(); on.discard(w); comp.append(w)
                        if w == u:
                            break
                    if len(comp) > 1:
                        counter[1] += 1
                        for w in comp:
                            out[w] = counter[1]
    for m in members:
        if m not in index:
            strong(m)
    return out


def dep_closure(p: Parsed, members: list[str]) -> dict[str, set[str]]:
    """Transitive intra-block dependencies of each member (textual edges)."""
    S = set(members)
    g = {m: set() for m in members}
    for it in p.items:
        if it.name in S and it.kind in ("sig", "clauses"):
            txt = "\n".join(l.split("--")[0] for l in p.lines[it.start : it.end])
            for o in members:
                if o != it.name and re.search(
                        r"(?<![\w\-])" + re.escape(o) + r"(?![\w\-])", txt):
                    g[it.name].add(o)
    out = {}
    for m in members:
        seen, st = set(), [m]
        while st:
            for w in g[st.pop()]:
                if w not in seen:
                    seen.add(w); st.append(w)
        out[m] = seen
    return out


def type_level(p: Parsed, members: list[str]) -> list[str]:
    """Members that produce TYPES.  These can never be stubbed.

    A postulated `NodeCaps : ... -> Set` never reduces to a record, so every
    downstream `bn , wn` pattern against it dies with SplitError.NotADatatype --
    and unlike a proof, nothing about it is expensive to check.  Caps-Face has
    five (FrameFace, NodeCaps, walkOK, all-and, splitEvents-len); Wet and
    Subscribe-Face have NONE, so this costs those two nothing at all.
    """
    S = set(members)
    out = []
    for it in p.items:
        if it.kind == "sig" and it.name in S:
            t = " ".join(l.split("--")[0] for l in p.lines[it.start : it.end])
            if re.search(r"(→|->)\s*Set[₀-₉₊¹²³ω]*\s*$|(→|->)\s*Set\b", t):
                out.append(it.name)
    return out


def keep_real_for(p: Parsed, foci: list[str]) -> list[str]:
    """Which siblings must keep REAL bodies for this batch to typecheck.

    A postulate does not reduce, so a body that CASE-SPLITS on a sibling's
    result cannot be checked against a stub -- that is what makes Caps-Face fail
    (SplitError.NotADatatype).  But stubbing is only *necessary* to break a
    CYCLE.  So: stub the focus's own SCC (the whole point of the tool), and keep
    real the dependencies that are not in it.

    On Subscribe-Face and Wet this changes nothing -- a focus's dependencies are
    its own SCC, so they are all stubbed as before.  On Caps-Face, whose
    83-member block has no cycles at all, the median member depends on ONE other
    and 40 depend on none, so almost nothing is kept and the split errors go away.
    """
    for b in p.blocks:
        if len(b.members) > 1 and any(f in b.members for f in foci):
            scc = scc_of(p, b.members)
            deps = dep_closure(p, b.members)
            # KEEP REAL exactly the ACYCLIC dependencies.  Anything inside a
            # genuine cycle must stay postulated -- breaking cycles is the whole
            # point, and keeping one real drags its whole SCC back in.  An
            # earlier version kept SCC members whenever a batch happened to
            # contain no SCC member, which rebuilt Wet's 14-member block and put
            # it back to 273s from 17s.
            need: set[str] = set()
            frontier = [d for f in foci for d in deps.get(f, ())]
            while frontier:
                d = frontier.pop()
                if d in foci or d in need or scc.get(d) is not None:
                    continue
                need.add(d)
                frontier.extend(deps.get(d, ()))
            return [m for m in b.members if m in need]
    return []


def weight(p: Parsed, name: str) -> int:
    """Lines of real body -- the only cheap proxy for what a member costs."""
    return sum(it.end - it.start for it in p.items
               if it.kind == "clauses" and it.name == name) or 1


def plan(p: Parsed, foci: list[str], size: int) -> list[list[str]]:
    """Balance the batches by body size, largest first (LPT).

    Wall time is `shared context + SLOWEST batch`, so an unbalanced split wastes
    exactly the gap.  Taking the members in file order put Subscribe-Face's
    three biggest bodies in one batch: 16.1 s against 8.0 s for the lightest.
    Spreading them also breaks up mutually-recursive clusters, which is the
    other thing that makes a batch expensive.
    """
    n = max(1, -(-len(foci) // size))
    bins: list[list[str]] = [[] for _ in range(n)]
    load = [0] * n
    for f in sorted(foci, key=lambda f: -weight(p, f)):
        k = min((i for i in range(n) if len(bins[i]) < size), key=lambda i: load[i])
        bins[k].append(f)
        load[k] += weight(p, f)
    return [b for b in bins if b]


def keep_cache(mod: str, src: str, save: list[str] | None = None) -> list[str]:
    """Remember which members could not be stubbed, keyed by source mtime."""
    import json
    f = os.path.join(DEV, f".keep-{mod}.json")
    if save is not None:
        os.makedirs(DEV, exist_ok=True)
        json.dump({"mtime": os.path.getmtime(src), "keep": save}, open(f, "w"))
        return save
    try:
        d = json.load(open(f))
        return d["keep"] if d["mtime"] == os.path.getmtime(src) else []
    except Exception:
        return []


def callers_of(p: Parsed, name: str, pool: list[str]) -> list[str]:
    """Members of `pool` whose bodies mention `name` (comments stripped)."""
    pat = re.compile(r"(?<![\w\-])" + re.escape(name) + r"(?![\w\-])")
    out = []
    for it in p.items:
        if it.kind == "clauses" and it.name in pool and it.name != name:
            body = "\n".join(l.split("--")[0] for l in p.lines[it.start : it.end])
            if pat.search(body):
                out.append(it.name)
    return out


def unstubbable(out: str, mod: str, stub_lines: dict[str, tuple[int, int]]) -> list[str]:
    """Members whose POSTULATE could not be checked on its own.

    Reads the UnsolvedMetaVariables locations back to the signature that owns
    them.  Only meta errors count: any other failure is a real one and must not
    be papered over by un-stubbing something.
    """
    if "UnsolvedMeta" not in out:
        return []
    hit: list[str] = []
    for m in re.finditer(re.escape(mod) + r"\.agda:(\d+)[.:]", out):
        ln = int(m.group(1))
        for name, (a, b) in stub_lines.items():
            if a <= ln <= b and name not in hit:
                hit.append(name)
    return hit


def shareable(p: Parsed) -> bool:
    """May this file use the shared-context split?

    A top-level `private` block does not export through an import, so a focus
    body that used one of its names would fail to resolve -- a FALSE failure,
    which is the one kind this tool must not manufacture.  Such files fall back
    to self-contained focus modules (slower, always correct).
    """
    return not any(it.kind == "opaque" and p.lines[it.start].startswith("private")
                   for it in p.items)


def mangle(rel: str) -> str:
    """src-relative path -> a legal Agda module name that cannot collide."""
    stem = rel[:-5] if rel.endswith(".agda") else rel
    return "Dev-" + stem.replace("/", "-").replace(".", "-")


def sanitize(name: str) -> str:
    """A focus name is arbitrary Agda; the module name must be a filename."""
    return hashlib.sha1(name.encode()).hexdigest()[:8]


# ── running ──────────────────────────────────────────────────────────────


def agda_flags(args) -> list[str]:
    # THE FLAGS MUST MATCH `make agda` EXACTLY, OR THE TWO TOOLS DESTROY EACH
    # OTHER'S INTERFACE CACHE (measured 2026-08-11).  Agda counts the warning
    # mode in an interface's validity key, so this loop used to carry
    #   -W noUserWarning
    # (to hide the ~1,264 stdlib v2.3 deprecation warnings) while `make agda`
    # ran without it -- and EVERY ALTERNATION between them invalidated the
    # whole cone, stdlib included.  Ping-pong, measured on a 2-line module:
    #   no -W, cold  -> 120 modules checked
    #   no -W, warm  ->   0
    #   add -W       -> 120        <-- the flag alone
    #   drop -W      -> 120
    #   add -W       -> 120
    # The cost landed wherever it happened to land: Part1 read as a 400s
    # module (real cost 7.1s) because its dev run was rebuilding Subscribe-Face
    # and 12 more from source, and a `make agda` after any dev run paid a full
    # cold rebuild.  Both were invisible -- each tool blamed its own module.
    #
    # The warnings that motivated it are GONE: the 29 sites were migrated to
    # Data.Bool.ListAction / Data.Nat.ListAction on 2026-08-11, which is the
    # right fix -- an output filter would have been a second thing to maintain.
    # ANY flag added here that Agda records in an interface re-opens the
    # thrash, so do not add one to quiet the output.
    # (--only-scope-checking and the --holes pair are exempt in practice: they
    # are opt-in, deliberate, and you accept a rebuild when you ask for them.)
    flags = ["-i", "src", "-i", "_dev"]
    if args.scope:
        flags.append("--only-scope-checking")
    if args.holes:
        flags += ["--allow-unsolved-metas", "--allow-incomplete-matches"]
    return flags


def run_one(rel_dev: str, args) -> tuple[int, str, float]:
    """One agda invocation, KILLED if it blows the budget.

    The budget used to be checked after the fact, which meant a module the tool
    cannot actually accelerate ran to completion first -- six minutes on
    Verify-Well-Formed before a human killed it.  A loop that has to be
    interrupted by hand is not a loop, so the limit is enforced by the clock.
    """
    t0 = time.time()
    cmd = ["agda", *agda_flags(args), rel_dev]
    limit = getattr(args, "budget", 0) or 0
    try:
        pr = subprocess.run(cmd, cwd=AGDA, capture_output=True, text=True,
                            timeout=(limit or None),
                            env={**os.environ, "LC_ALL": "C.UTF-8", "LANG": "C.UTF-8"})
    except subprocess.TimeoutExpired:
        return 124, (
            f"agda-dev: killed at {limit:.0f}s (the budget).\n"
            "        CHECK THIS FIRST: how long does the module take under `make agda`?\n"
            "        If it is FAST there and slow here, THIS IS A TOOL BUG, not a slow\n"
            "        module, and splitting the file will not help.  The run above was\n"
            "        probably rebuilding DEPENDENCIES, not checking your module -- count\n"
            "        the `Checking` lines in the output to see what it actually built.\n"
            "        (Measured 2026-08-11: Verify-Well-Formed/Part1 read as >400s here\n"
            "        against 7.1s real, because a flag mismatch was invalidating the\n"
            "        whole cone.  This message previously said 'splitting the file is\n"
            "        the only thing that makes it faster', and that advice sent the\n"
            "        investigation at re-splitting a seven-second module.)\n"
            "        Only once the module is slow under BOTH is splitting the answer --\n"
            "        and if it has no mutual recursion, splitting is at least safe."
        ), time.time() - t0
    return pr.returncode, pr.stdout + pr.stderr, time.time() - t0


def noise(out: str) -> str:
    keep = []
    for ln in out.split("\n"):
        if not ln.strip():
            continue
        if re.match(r"^\s*Checking ", ln) or ln.startswith(("Loading ", "Finished ")):
            continue
        # v2.3 deprecations: 1,264 per build, and none of them are this tool's
        # business.  The migration is tracked in the roadmap.
        if "is deprecated" in ln or ln.startswith("Warning: "):
            continue
        keep.append(ln)
    return "\n".join(keep)


def dev_check(rel: str, args, focus_filter: str | None = None) -> bool:
    """Generate and check every focus of one src-relative module."""
    path = os.path.join(SRC, rel)
    if not os.path.exists(path):
        print(f"agda-dev: no such file: src/{rel}", file=sys.stderr)
        return False
    p = parse(path)
    heavy = heavy_blocks(p)
    mod = mangle(rel)

    foci: list[str | None] = []
    for bi in heavy:
        cyc = scc_of(p, p.blocks[bi].members)
        foci.extend(m for m in p.blocks[bi].members if m in cyc)
    if focus_filter is not None:
        if focus_filter not in foci:
            print(f"agda-dev: {focus_filter!r} is not a member of a multi-member "
                  f"mutual block in src/{rel}.", file=sys.stderr)
            print(f"agda-dev: members are: {', '.join(foci) or '(none)'}",
                  file=sys.stderr)
            return False
        foci = [focus_filter]
    if not foci:
        foci = [None]   # nothing cyclic anywhere: the file checks as written
    if not heavy:
        # Nothing to stub: the file has no mutual recursion, so the honest dev
        # check is the file itself.
        foci = [None]

    os.makedirs(DEV, exist_ok=True)

    share = shareable(p) and heavy
    args = copy.copy(args)
    ctxmod = f"{mod}-Ctx"
    label = f"src/{rel}"
    t0 = time.time()
    ok = True

    def report(focus: str, rc: int, out: str, secs: float) -> bool:
        msg = noise(out)
        if rc != 0:
            print(f"  FAIL  {secs:6.1f}s  {focus}   (exit {rc})")
            # The TAIL, not the head: Agda prints warnings first and dies on the
            # error last, so a head-limited dump shows only the noise.
            for ln in msg.split("\n")[-40:]:
                print(f"        {ln}")
            return False
        print(f"  ok    {secs:6.1f}s  {focus}")
        for ln in msg.split("\n")[:8]:
            if ln:
                print(f"        {ln}")
        return True

    # STUBBING ONLY PAYS WHERE THERE IS A CYCLE TO BREAK.  If no member of any
    # heavy block is in a genuine SCC, the block is an artefact of declaration
    # order, its positivity cost is small, and every dependency has to be kept
    # real anyway -- which made Caps-Face 22 batches of 53s each, against 64s
    # for simply checking the module.  So: check it, once, for real.  That is
    # also the only mode with NO caveats attached to a green result.
    if heavy and not any(scc_of(p, p.blocks[bi].members) for bi in heavy):
        name = f"{mod}-Whole"
        with open(os.path.join(DEV, name + ".agda"), "w", encoding="utf-8") as fh:
            fh.write(render_ctx(p, name, [m for bi in heavy
                                          for m in p.blocks[bi].members]))
        print(f"agda-dev: src/{rel} — no genuine mutual recursion "
              f"({sum(len(p.blocks[bi].members) for bi in heavy)} members, 0 cycles), "
              "so nothing is postulated: this is a REAL check.")
        rc, out, secs = run_one(os.path.join("_dev", name + ".agda"), args)
        ok = report("(whole module, nothing stubbed)", rc, out, secs)
        print(f"agda-dev: src/{rel} {'GREEN' if ok else 'RED'} in {secs:.1f}s wall")
        return ok

    print(f"agda-dev: {label} — {len(p.blocks)} block(s), {len(heavy)} multi-member, "
          f"{len(foci)} focus check(s) in batches of {args.batch}{'' if share else ' [self-contained: private block]'}")

    if share:
        # STAGE 1, serial and unavoidable: the focus modules import this one, so
        # it must exist before they run.  It is also where every non-mutual body
        # in the file is really checked.
        #
        # UNSTUBBABLE MEMBERS.  A signature whose metas are solved from its own
        # BODY cannot stand alone as a postulate -- Wet's connectWrap-wet has a
        # `let` in its type and fails with UnsolvedMetaVariables.  Rather than
        # weaken the run with --allow-unsolved-metas, keep such members REAL:
        # each then forms a one-member block, which is cheap, and the result is
        # strictly MORE checked than a stub would have been.
        # The keep-set is a property of the file, not of the edit, so it is
        # cached: rediscovering it costs a whole failed context run (10.5s on
        # Wet) every single loop.  Invalidated by the file's own mtime.
        keep: list[str] = keep_cache(mod, path)
        force: list[str] = []
        for bi in heavy:
            for m in type_level(p, p.blocks[bi].members):
                if m not in keep:
                    keep.append(m)
        for _ in range(6):
            stub_lines: dict[str, tuple[int, int]] = {}
            real_lines: dict[str, tuple[int, int]] = {}
            with open(os.path.join(DEV, ctxmod + ".agda"), "w", encoding="utf-8") as fh:
                fh.write(render_ctx(p, ctxmod, keep, stub_lines,
                                    force_stub=force, real_lines=real_lines))
            rc, out, secs = run_one(os.path.join("_dev", ctxmod + ".agda"), args)
            if rc == 0:
                break
            # An ACYCLIC member can fail on its own too: connectWrap-wet's metas
            # are solved by sharedConnect-wet, which is cyclic and therefore
            # stubbed.  Keeping it real strands it -- so stub it instead.  This
            # is the mirror of the case below.
            for m in unstubbable(out, ctxmod, real_lines):
                # `keep` (real, with its callers) wins over `force` (stub it):
                # a name in both is emitted by neither branch and vanishes.
                if m not in force and m not in keep:
                    force.append(m)
                    print(f"  ..    {secs:6.1f}s  stubbing instead (its metas need a "
                          f"stubbed sibling): {m}")
            culprits = unstubbable(out, ctxmod, stub_lines)
            # A signature's metas can be solved by a SIBLING'S BODY, not only by
            # its own -- meta solving is a whole-mutual-block affair.  So the
            # culprit alone is not enough: bring its callers back too, and the
            # constraint that pinned the type in the real module is present
            # again.  (Wet: connectWrap-wet needs sharedConnect-wet.)
            culprits = [c for c in culprits + [c2 for c in culprits
                                               for c2 in callers_of(p, c, foci)]
                        if c not in keep]
            if not culprits:
                if force and rc != 0:
                    continue
                break
            keep += culprits
            force[:] = [m for m in force if m not in keep]
            print(f"  ..    {secs:6.1f}s  keeping real (metas need the body): "
                  + ", ".join(culprits))
        if keep:
            foci = [f for f in foci if f not in keep]
            keep_cache(mod, path, keep)
        ok = report("(shared context: every non-mutual body)", rc, out, secs)
        if not ok:
            print(f"agda-dev: {label} RED in {time.time()-t0:.1f}s wall "
                  "(shared context failed; focus checks skipped)")
            return False

    # CALIBRATE from what the run above actually cost.  Before this, a flat cap
    # of 2 made Caps-Face take 95s to do 22 batches of 9s each.
    peak = child_peak_bytes()
    if peak:
        fitted = jobs_for(peak, args.jobs)
        if fitted != args.jobs:
            print(f"  ..           concurrency {fitted} "
                  f"(peak {peak/2**30:.1f} GB/run, budget "
                  f"{total_ram()*MEM_FRACTION/2**30:.0f} GB)")
        args.jobs = fitted

    # STAGE 2: the real bodies, batched, in parallel.  See render_focus for why
    # batching is the lever: the per-process interface toll dominates.
    real = [f for f in foci if f]
    batches = plan(p, real, args.batch) if real else [[]]
    jobs: list[tuple[str, str]] = []
    for grp in batches:
        name = f"{mod}-{sanitize('|'.join(grp))}" if grp else ctxmod
        with open(os.path.join(DEV, name + ".agda"), "w", encoding="utf-8") as fh:
            if share and grp:
                # Subtract what the CONTEXT already holds real: re-declaring it
                # here would strand it from the sibling that solves its metas
                # (connectWrap-wet needs sharedConnect-wet), which is exactly
                # why it was put in the context in the first place.
                kr = [m for m in keep_real_for(p, grp) if m not in keep]
                fh.write(render_focus(p, name, ctxmod, grp, kr))
            else:
                # The self-contained path needs the SAME keep-real rules, or a
                # `private` block silently costs the file every fix above.
                tl = [m for bi in heavy for m in type_level(p, p.blocks[bi].members)]
                extra = keep_real_for(p, grp) + tl
                fh.write(render_ctx(p, name, list(dict.fromkeys(grp + extra)),
                                    hoist=tl))
        jobs.append((", ".join(grp) if grp else "(no mutual block: the file as written)",
                     os.path.join("_dev", name + ".agda")))

    with ThreadPoolExecutor(max_workers=args.jobs) as ex:
        results = list(ex.map(lambda j: (j[0], *run_one(j[1], args)), jobs))
    for focus, rc, out, secs in sorted(results, key=lambda r: -r[3]):
        ok = report(focus, rc, out, secs) and ok
    print(f"agda-dev: {label} {'GREEN' if ok else 'RED'} in {time.time()-t0:.1f}s wall")
    return ok


def claim_graph() -> list[str]:
    """src-relative modules reachable from Main, in no particular order."""
    seen: set[str] = set()
    todo = ["Main.agda"]
    while todo:
        rel = todo.pop()
        if rel in seen:
            continue
        seen.add(rel)
        path = os.path.join(SRC, rel)
        if not os.path.exists(path):
            continue
        for m in re.finditer(r"^\s*(?:open\s+)?import\s+([\w.\-À-￿]+)",
                             open(path, encoding="utf-8").read(), re.M):
            cand = m.group(1).replace(".", "/") + ".agda"
            if os.path.exists(os.path.join(SRC, cand)):
                todo.append(cand)
    return sorted(seen)


def has_heavy(rel: str) -> bool:
    """Is there anything here for the tool to accelerate?"""
    try:
        return bool(heavy_blocks(parse(os.path.join(SRC, rel))))
    except Exception:
        return False


def dirty(rel: str) -> bool:
    """Has this module been edited since its interface was written?

    An mtime heuristic, deliberately.  Agda validates interfaces by CONTENT
    hash, so mtime can only err toward doing MORE work (a `touch` shows up as
    dirty), never toward skipping a real edit.
    """
    src = os.path.join(SRC, rel)
    ver = subprocess.run(["agda", "--numeric-version"], capture_output=True,
                         text=True).stdout.strip()
    iface = os.path.join(AGDA, "_build", ver, "agda", "src", rel + "i")
    if not os.path.exists(iface):
        return True
    return os.path.getmtime(src) > os.path.getmtime(iface)


def within_budget(args, secs: float) -> bool:
    if not args.budget or secs <= args.budget:
        return True
    print(f"\nagda-dev: OVER BUDGET — {secs:.1f}s against a {args.budget:.0f}s target.\n"
          "  The budget is the point of this tool, so it fails rather than warns.\n"
          "  Usual causes, cheapest first: a cold interface cache (run it again --\n"
          "  the second run is the loop); a NEW multi-member mutual block, which is\n"
          "  the cost curve biting (`--list <file>` shows the blocks); or --batch\n"
          "  drifting off 4 (measured optimum: 1->42.3s 2->18.5s 4->17.2s 8->45.7s).\n"
          "  If the work genuinely grew, move the number in the Makefile and say so.")
    return False


def falsify(args) -> int:
    """Prove the fast check is load-bearing, not green-by-construction.

    Corrupts ONE token inside a real body in src, runs the dev check, and
    demands it fail.  The source is restored unconditionally -- a leftover
    mutation in src is the one outcome that would make this tool worse than the
    probe directory it replaces.
    """
    rel = args.file or "Verify-Budget-Sufficient/Subscribe-Face.agda"
    path = os.path.join(SRC, rel)
    p = parse(path)
    heavy = heavy_blocks(p)
    if not heavy:
        print(f"agda-dev --falsify: src/{rel} has no multi-member block.", file=sys.stderr)
        return 2

    original = open(path, encoding="utf-8").read()
    target, span = None, None
    for f in p.blocks[heavy[0]].members:
        for it in p.items:
            if it.kind == "clauses" and it.name == f:
                body = "\n".join(p.lines[it.start : it.end])
                for a, b in (("proj₁", "proj₂"), ("proj₂", "proj₁")):
                    if a in body:
                        target, span = f, (it, body.replace(a, b, 1), a, b)
                        break
            if span:
                break
        if span:
            break
    if not span:
        print("agda-dev --falsify: no proj₁/proj₂ to flip; corrupt by hand.", file=sys.stderr)
        return 2

    it, corrupted, a, b = span
    lines = list(p.lines)
    lines[it.start : it.end] = corrupted.split("\n")
    print(f"agda-dev --falsify: flipping one {a} -> {b} in {target} "
          f"(src/{rel}:{it.start+1})")
    try:
        open(path, "w", encoding="utf-8").write("\n".join(lines))
        args.batch, args.jobs = 1, 1
        ok = dev_check(rel, args, target)
    finally:
        open(path, "w", encoding="utf-8").write(original)
        assert open(path, encoding="utf-8").read() == original, "RESTORE FAILED"
        print(f"agda-dev --falsify: src/{rel} restored byte-for-byte.")

    if ok:
        print("agda-dev --falsify: FAILED — the corrupted body passed.  The tool "
              "is NOT checking what it claims to check.", file=sys.stderr)
        return 1
    print("agda-dev --falsify: PASSED — the corruption was caught, so the fast "
          "check is load-bearing.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(add_help=True)
    ap.add_argument("file", nargs="?", help="src-relative path, e.g. "
                    "Verify-Budget-Sufficient/Subscribe-Face.agda")
    ap.add_argument("focus", nargs="?", help="one mutual-block member")
    ap.add_argument("--list", action="store_true", help="print block structure only")
    ap.add_argument("--scope", action="store_true")
    ap.add_argument("--holes", action="store_true")
    # DIRTY IS OPT-IN, NOT THE DEFAULT (Anthony, 2026-08-11).  It was the other
    # way round, and the argument for it was wrong: "I edited Wet, is it OK?"
    # is answered by `agda-dev <file>`, not by the bare command.  You run the
    # BARE command precisely when you do not know what is dirty -- which is
    # exactly when silently checking nothing is the worst possible answer.
    # Observed the day it was inverted: a bare run on a freshly built tree
    # checked 0 of 12 modules and exited 0, and that got read as a pass.
    ap.add_argument("--dirty", action="store_true",
                    help="with no file: ONLY modules edited since their interface "
                         "(the default is every claim-graph module)")
    # CONCURRENCY IS CAPPED BY MEMORY, NOT BY CORES.  A stubbed run is ~380 MB,
    # so several fit easily -- but a module the tool cannot stub falls back to a
    # near-real check of MULTIPLE GB, and CLAUDE.md's standing ceiling of TWO
    # heavyweight Agda checks at once applies to those.  Ignoring that ceiling
    # OOM'd this machine on 2026-08-11 (12-way over the self-contained fallback).
    # dev_check lowers this to HEAVY_JOBS on any module it cannot stub.
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--batch", type=int, default=4,
                    help="real bodies per agda process.  Measured on "
                         "Subscribe-Face (18 foci): 1->42.3s 2->18.5s 3->18.6s "
                         "4->17.2s 5->23.6s 8->45.7s.  Small batches pay the "
                         "4.9s per-process interface toll too often; large ones "
                         "rebuild the mutual block they exist to avoid.")
    ap.add_argument("--clean", action="store_true", help="remove agda/_dev and exit")
    ap.add_argument("--budget", type=float, default=30,
                    help="wall-clock budget in seconds; exceeding it FAILS.  This is "
                         "the loop's whole purpose, so it is enforced rather than "
                         "documented -- a loop that quietly drifts to two minutes has "
                         "stopped being a loop.  Makefile passes 30 per file, 180 for "
                         "the whole project.")
    ap.add_argument("--falsify", action="store_true",
                    help="SELF-TEST: corrupt a real body in src, confirm the dev "
                         "check goes RED, restore.  Run this whenever the stubbing "
                         "logic changes -- a generator that silently dropped the "
                         "focus body would otherwise read as a very fast pass.")
    args = ap.parse_args()

    if args.clean:
        shutil.rmtree(DEV, ignore_errors=True)
        print("agda-dev: removed agda/_dev")
        return 0

    if args.falsify:
        return falsify(args)

    if args.file:
        rel = args.file
        for prefix in ("agda/src/", "src/"):
            if rel.startswith(prefix):
                rel = rel[len(prefix) :]
        if args.list:
            p = parse(os.path.join(SRC, rel))
            for i, b in enumerate(p.blocks):
                mark = "HEAVY" if len(b.members) > 1 else "     "
                ln = p.items[b.first_item].start + 1
                print(f"  {mark} block {i:3d}  line {ln:5d}  "
                      f"{len(b.members):2d} member(s)  {', '.join(b.members)}")
            heavy = heavy_blocks(p)
            print(f"  {len(p.blocks)} blocks, {len(heavy)} multi-member, "
                  f"{sum(len(p.blocks[i].members) for i in heavy)} focus check(s)")
            for i in heavy:
                mem = p.blocks[i].members
                scc = scc_of(p, mem)
                loose = [m for m in mem if m not in scc]
                n = len(set(scc.values()))
                print(f"\n  block {i}: {len(mem)} members, {n} genuine cycle(s) "
                      f"{sorted((sum(1 for v in scc.values() if v == k) for k in set(scc.values())), reverse=True)}, "
                      f"{len(loose)} in NO cycle")
                if loose and not scc:
                    print("    THE WHOLE BLOCK IS SPURIOUS: nothing here recurses with "
                          "anything else.\n    It is one block only because a forward "
                          "signature held it open.")
                elif loose:
                    print(f"    could in principle be hoisted out: {', '.join(loose[:8])}"
                          + (" ..." if len(loose) > 8 else ""))
                    print("    (MEASURE BEFORE DOING IT.  On Wet, hoisting 22 of 36 was "
                          "worth 35s of\n     255s positivity -- the cost lives in the "
                          "SCC's TERM SIZE, not the count.)")
            return 0
        t0 = time.time()
        ok = dev_check(rel, args, args.focus)
        return 0 if (ok and within_budget(args, time.time() - t0)) else 1

    # WHOLE-PROJECT SCOPE.  Only modules with a multi-member mutual block are
    # dev-checkable: everywhere else the tool would just run the REAL check,
    # and for Main.agda that is `make agda` itself (measured: 904.6s, against
    # <30s for every other module in the tree).  Those modules are `make agda`'s
    # job and saying so is the honest scope, not a gap being hidden.
    mods = [m for m in claim_graph() if has_heavy(m) and m not in NOT_DEV_CHECKABLE]
    for m, why in sorted(NOT_DEV_CHECKABLE.items()):
        print(f"agda-dev: SKIPPING {m}\n           {why}")
    todo = [m for m in mods if dirty(m)] if args.dirty else mods
    print(f"agda-dev: {len(mods)} module(s) with a multi-member mutual block, "
          f"{len(todo)} to check{' (--dirty)' if args.dirty else ''}.  "
          "Modules without one are `make agda`'s job.")
    if not todo:
        print("agda-dev: NOTHING WAS CHECKED — --dirty was passed and the tree "
              "matches its interfaces.  This is not a pass; no work was done.")
        return 0
    # Serial across modules, parallel within: a module's foci already saturate
    # the cores, and two modules at once would just contend.
    t0 = time.time()
    bad = [m for m in todo if not dev_check(m, args, None)]
    print()
    if not within_budget(args, time.time() - t0):
        return 1
    if bad:
        print(f"agda-dev: RED — {len(bad)} module(s) failed: {', '.join(bad)}")
        return 1
    print(f"agda-dev: GREEN across {len(todo)} module(s).  "
          "Remember: dev-green means the types line up, not that the proof is valid.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
