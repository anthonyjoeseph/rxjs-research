#!/usr/bin/env python3
"""The wiring-law checker: "a comment is not a wire" (see CLAUDE.md).

Scans agda/src/**/*.agda and reports:

  (A) ORPHANS       top-level definitions (proven code) with zero consumers
                     anywhere in agda/src.
  (B) THE LEDGER     every `postulate` member, split into "with consumers"
                     (real remaining work) and "zero consumers" (dead-weight
                     deletion candidates).
  (C) SUMMARY        counts.

This is a TEXTUAL heuristic, not a semantic one — see the "limitations"
footer this script prints, and read it before trusting a borderline case.

Usage:
    scripts/check-wiring.py [--src DIR]

Exit code is always 0: this is a report for a human to rule on, not a
build gate.
"""

import argparse
import os
import sys
from bisect import bisect_right
from collections import defaultdict

# ---------------------------------------------------------------------------
# ALLOWLIST — top-level exports CLAUDE.md exempts from "every definition
# must be used somewhere" ("the only exceptions are the top-level,
# most-important exports").  Kept intentionally SHORT and SPECIFIC: this is
# not a place to park anything that merely *looks* important — a name goes
# here only when there is a concrete, textual reason it is the campaign's
# outward-facing finish line rather than internal plumbing.  Everything else
# that turns up with zero consumers is reported, not hidden, so a human
# rules on it (see DELIVERABLE 2 in the task this script was written for).
# ---------------------------------------------------------------------------
ALLOWLIST = {
    "formal-verification-batchSimultaneous": (
        "The ultimate goal named explicitly by CLAUDE.md: "
        "'agda/src/Verify-Batch-Simultaneous/The-Proof.agda fully discharged' "
        "IS this theorem.  It is the outermost consumer of the whole proof "
        "tree beneath it; nothing consumes IT because it is the finish line."
    ),
    "evaluate-well-formed": (
        "CLAUDE.md's other named half of 'the sandwich' (Rx.Evaluator-"
        "Theorems.agda's header: 'evaluate-well-formed ... now lives in "
        "Verify-Well-Formed as a real proof').  It happens to already have "
        "one real consumer (The-Proof.agda calls it directly), so it would "
        "not currently be flagged as an orphan even without this entry —  "
        "it is listed anyway because it is named, by CLAUDE.md, as a "
        "top-line export that is not REQUIRED to have one."
    ),
    "main": (
        "Two compiled-binary entry points share this name: CLI/Main.agda "
        "(built by `make cli-build`, run by `make oracle`) and "
        "QuickCheck.agda (built by `make qc-build`, run by `make "
        "quickcheck`). Each is `agda --compile`d and then run as an OS "
        "process — its consumer is the shell, not other Agda source, so "
        "textual search will never find one."
    ),
    # --- design-session rulings, 2026-08-05 (see PROOF-STATE.md "Wiring
    # --- rulings"). Two FAMILIES are exempt, matched by pattern below rather
    # --- than listed name by name.
    #
    # (1) `*-absurd` REFUTATION WITNESSES.  A machine-checked `… → ⊥` is the
    # only durable form of "this route is dead, do not retry it", and it is
    # load-bearing for the DESIGN process rather than for another term.
    # Tested twice on 2026-08-05: `caps-frame-boundary-absurd` and
    # `round3b-ledger-reset-absurd` are exactly what proved the anchor problem
    # real rather than a wiring gap, saving a long wasted grind. A worker
    # classified them "archive, not live infrastructure" and was overruled.
    # Deleting one costs a future session the whole refutation.
    #
    # (2) THE TOP-LINE SEMANTIC POSTULATES in `*-Theorems.agda`
    # (`readme-*`, `fuel-coherent`, `causality`, `μ-unfold`, `μ-guarded`,
    # `defer-shift`, `id-inheritance`, `locality`, `non-interference`,
    # `timing-invariance`, `batch-online`, `_≈ˢ_`, `_≈ᵍ_`).  These are
    # deliberately-stated outward-facing claims, imported by Main.agda; nothing
    # consumes them because they ARE the claims.  They are NOT dead weight —
    # but they ARE unproven, so they form a SECOND ledger, distinct from the
    # critical path to formal-verification-batchSimultaneous.  Exempt from the
    # orphan report; still counted as postulates.
    #
    # "anything Main.agda invokes": Main.agda (agda/src/Main.agda) has no
    # body beyond a wall of `open import` statements — no function
    # application, no `main = ...` term.  There is therefore nothing else
    # to add on that basis; the instruction to "inspect Main.agda rather
    # than guess" is satisfied by the fact that inspection turns up nothing
    # more.  (Everything Main.agda transitively imports is NOT thereby
    # allowlisted — subscribeE-walk is transitively imported too, via
    # Verify-Budget-Sufficient, and known-true fact #1 requires it to be
    # reported as an orphan regardless.)
}

# Characters that can NEVER be part of an Agda identifier in this codebase's
# style, i.e. token boundaries.  Deliberately does NOT try to enumerate
# identifier characters — this repo's names are heavy with Unicode (≤, ᵉ, ⊔,
# ′, ?, -, _) and enumerating "identifier chars" would be an unwinnable
# whack-a-mole.  Instead we enumerate the much smaller, stable set of
# characters Agda reserves and this codebase actually uses as separators:
# whitespace and ASCII structural punctuation.  Anything NOT in this set
# (including all the Unicode math/sub/superscript characters, '-', '_', '?',
# '′') is treated as a potential identifier character, so e.g. "capsOK?" and
# "capsOK?-parts" are correctly recognised as two different tokens: the
# character right after a "capsOK?" match inside "capsOK?-parts" is '-',
# which is NOT a boundary character, so the match is rejected.
BOUNDARY_CHARS = set(" \t\n\r\f\v(){}[];.,@\"'`=:\\|")


def is_boundary(ch):
    return ch is None or ch in BOUNDARY_CHARS


SKIP_HEAD_TOKENS = {
    "module", "open", "import", "infix", "infixl", "infixr",
    # `opaque` blocks may open with `unfolding <names> [in]`, naming
    # ALREADY-defined opaque definitions to unfold locally — not a new
    # definition of something called "unfolding". (Verify-Budget-
    # Sufficient/Measures.agda:1575,1938: "unfolding szB".)
    "unfolding",
}


def strip_block_comments(raw_lines):
    """Blank out {- ... -} spans (including pragmas {-# ... #-}), across
    line boundaries, preserving line count and non-comment characters'
    positions so indentation/columns stay meaningful."""
    out = []
    in_block = False
    for line in raw_lines:
        buf = []
        i, n = 0, len(line)
        while i < n:
            if in_block:
                if line[i : i + 2] == "-}":
                    buf.append("  ")
                    i += 2
                    in_block = False
                else:
                    buf.append(" ")
                    i += 1
            else:
                if line[i : i + 2] == "{-":
                    buf.append("  ")
                    i += 2
                    in_block = True
                else:
                    buf.append(line[i])
                    i += 1
        out.append("".join(buf))
    return out


def mask_full_comment_lines(visible_lines):
    """A line whose first non-space characters are `--` is excluded
    entirely (both from definition-scanning and consumer-counting).
    Inline trailing `-- ...` on an otherwise-code line is left alone —
    that is a textual-honesty limitation, documented in the footer."""
    out = []
    for line in visible_lines:
        if line.lstrip().startswith("--"):
            out.append("")
        else:
            out.append(line)
    return out


def leading_spaces(line):
    return len(line) - len(line.lstrip(" "))


class Def:
    __slots__ = ("name", "file", "line", "kind")

    def __init__(self, name, file, line, kind):
        self.name = name
        self.file = file
        self.line = line
        self.kind = kind  # 'def' | 'data/record' | 'postulate'


def find_agda_files(src_dir):
    files = []
    for root, _dirs, filenames in os.walk(src_dir):
        for fn in filenames:
            if fn.endswith(".agda"):
                files.append(os.path.relpath(os.path.join(root, fn), src_dir))
    files.sort()
    return files


def load_file(src_dir, relpath):
    with open(os.path.join(src_dir, relpath), encoding="utf-8") as f:
        raw_lines = f.readlines()
    visible = strip_block_comments(raw_lines)
    visible = mask_full_comment_lines(visible)
    return raw_lines, visible


def extract_definitions(src_dir, files):
    """Stage 1: find every top-level (column-0) definition, data/record
    declaration, and postulate member.  Returns:
        defs           name -> Def (first-seen site)
        def_lines       name -> set of (file, lineno) that are the name's
                         OWN defining lines (signature line(s) / clause LHS
                         lines / the postulate member's own line) — these
                         are excluded when counting NAME's consumers.
        postulate_names  set of names that are postulate members
        order            list of names in first-seen order (stable output)
    """
    defs = {}
    def_lines = defaultdict(set)
    postulate_names = set()
    order = []
    # Mixfix cores: an operator declared `_foo_ : ...` is DEFINED with tok0
    # == "_foo_", but its pattern-matching clauses are written INFIX —
    # `unitᵗ ≟ᵗ natᵗ = ...` for `_≟ᵗ_`, `cs is s = ...` for `_is_` — so the
    # operator's own name is NOT tok0 on those lines; some middle/other
    # token ("≟ᵗ", "is") is.  Naively taking tok0 on such a line invents a
    # bogus definition (e.g. "cs" or a data constructor like "unitᵗ") and
    # loses the clause as one of the OPERATOR's defining lines.  So: once a
    # mixfix name `_core_` is registered, remember `core -> name`, and on
    # every later definition line, prefer a token (other than tok0) that
    # matches a known core over treating tok0 as a fresh name.
    mixfix_cores = {}

    def note_mixfix(name):
        if len(name) > 2 and name.startswith("_") and name.endswith("_"):
            core = name[1:-1]
            if core and not (core.startswith("_") or core.endswith("_")):
                mixfix_cores[core] = name

    def lhs_slice(tokens):
        """Tokens strictly between tok0 and the clause's own '=' / 'with' /
        'rewrite' — i.e. the LEFT-HAND SIDE pattern only.  An operator
        mentioned in the RHS body (e.g. `main = getContents >>= ...` really
        uses `_>>=_`, but that is not a CLAUSE of `_>>=_`) must never be
        mistaken for an infix clause head, so callers only search this
        slice, never the whole line.  Returns None when no boundary is
        found (e.g. a bare continuation) — callers must then skip the
        mixfix check rather than guess."""
        for terminator in ("=", "with", "rewrite"):
            if terminator in tokens:
                return tokens[1 : tokens.index(terminator)]
        return None

    def find_mixfix_owner(tokens):
        lhs = lhs_slice(tokens)
        if lhs is None:
            return None
        for tok in lhs:
            owner = mixfix_cores.get(tok)
            if owner is not None:
                return owner
        return None

    # Block-opener keywords that appear BARE on their own line at some
    # indentation level and open an indented body whose members sit at one
    # shared "base indent".  `postulate` is the one the task spells out
    # explicitly; but by the exact same textual shape, this codebase also
    # uses `mutual`, `abstract`, `opaque`, `private`, `instance` — and
    # unlike `where` blocks (genuinely local to one parent clause, so they
    # can have at most one possible consumer and checking them is
    # uninformative), a `mutual`/`abstract`/`opaque`/`private` block holds
    # ordinary module-wide definitions that just happen to be wrapped in a
    # modifier — CLAUDE.md's own "cut at mutual-SCC boundaries" rule treats
    # `mutual` blocks as the primary structural unit of this proof, so
    # silently skipping their contents (as a strict "column 0 only" reading
    # would) would blind the checker to a large fraction of the codebase.
    # So: recurse into these exactly as into `postulate`, just without
    # marking their members as postulates.
    BLOCK_OPENERS = {"postulate", "mutual", "abstract", "opaque", "private", "instance"}

    def register(name, relpath, lineno, kind):
        def_lines[name].add((relpath, lineno))
        if name not in defs:
            defs[name] = Def(name, relpath, lineno, kind)
            order.append(name)
            note_mixfix(name)

    def scan_block(raw_lines, visible, start, end, indent_level, relpath):
        """Scan lines [start, end) that belong to one indentation scope
        (indent_level — 0 for a file's true top level, or a block's base
        indent for the body of postulate/mutual/abstract/opaque/private).
        Returns the index of the first line NOT consumed by this block."""
        i = start
        while i < end:
            vline = visible[i]
            if vline.strip() == "":
                i += 1
                continue
            indent = leading_spaces(raw_lines[i])
            if indent < indent_level:
                break  # dedent — this block (or the whole file) is done
            if indent > indent_level:
                i += 1  # a continuation line of the previous member/clause
                continue

            tokens = vline.split()
            if not tokens:
                i += 1
                continue
            tok0 = tokens[0]

            if tok0 in SKIP_HEAD_TOKENS:
                i += 1
                continue

            if tok0 in ("data", "record"):
                if len(tokens) > 1:
                    register(tokens[1].rstrip(":"), relpath, i + 1, "data/record")
                i += 1
                continue

            if tok0 in BLOCK_OPENERS:
                rest = vline[len(tok0) :].strip()
                if rest == "":
                    # Block form: find the body's base indent off the first
                    # non-blank line that follows, then recurse at that
                    # indent level until it dedents back to (or below)
                    # indent_level.
                    j = i + 1
                    base_indent = None
                    while j < end:
                        if visible[j].strip() != "":
                            base_indent = leading_spaces(raw_lines[j])
                            break
                        j += 1
                    if base_indent is None or base_indent <= indent_level:
                        i += 1  # empty/malformed block — nothing to recurse into
                        continue
                    kind = "postulate" if tok0 == "postulate" else "def"
                    j2 = scan_sub_block(
                        raw_lines, visible, j, end, base_indent, relpath, kind
                    )
                    i = j2
                    continue
                else:
                    # single-line form, e.g. "postulate randFold : ...ℕ"
                    mtoks = rest.split()
                    if mtoks:
                        kind = "postulate" if tok0 == "postulate" else "def"
                        mname = mtoks[0].rstrip(":")
                        if kind == "postulate":
                            postulate_names.add(mname)
                        register(mname, relpath, i + 1, kind)
                    i += 1
                    continue

            # A regular definition line at this scope: a type signature
            # ("name : ...") or a clause left-hand side ("name args = ...",
            # "... with ...", "... rewrite ..."). Every line at this exact
            # indent whose leading token equals `name` is one of that
            # name's OWN defining lines — signature and every clause alike.
            #
            # Exception 1: an INFIX operator's clause does not have the
            # operator at tok0 (`unitᵗ ≟ᵗ natᵗ = ...` is a clause of
            # `_≟ᵗ_`) — check tokens[1:] for a known mixfix core first.
            # Exception 2: bare `_` is Agda's anonymous top-level check
            # (`_ : impl prog ≡ expected` in the append-only bug cache,
            # Implementation/Unit-Test.agda) — it can never have a
            # consumer BY DESIGN, so it is not a definition worth tracking
            # at all, let alone flagging as an orphan.
            if tok0 == "_":
                i += 1
                continue
            # Only clause-shaped lines are candidates for infix
            # reattribution — a TYPE SIGNATURE (recognisable by a
            # standalone ':' token) may legitimately MENTION an operator
            # inside its type (e.g. "hasAtLeast-pad : ... -> gasPad m g
            # hasAtLeast n") without being one of that operator's own
            # clauses; reattributing it would wrongly hand hasAtLeast-pad's
            # own signature line to `_hasAtLeast_` and, worse, leave it
            # unmasked when counting hasAtLeast-pad's OWN consumers.
            owner = None if ":" in tokens else find_mixfix_owner(tokens)
            if owner is not None:
                def_lines[owner].add((relpath, i + 1))
            else:
                name = tok0.rstrip(":")
                register(name, relpath, i + 1, "def")
            i += 1
        return i

    def scan_sub_block(raw_lines, visible, start, end, base_indent, relpath, kind):
        """Like scan_block, but every plain-definition member found is
        tagged `kind` (used to mark postulate-block members as postulates;
        mutual/abstract/opaque/private members stay ordinary 'def's)."""
        i = start
        while i < end:
            vline = visible[i]
            if vline.strip() == "":
                i += 1
                continue
            indent = leading_spaces(raw_lines[i])
            if indent < base_indent:
                break
            if indent > base_indent:
                i += 1
                continue

            tokens = vline.split()
            if not tokens:
                i += 1
                continue
            tok0 = tokens[0]

            if tok0 in SKIP_HEAD_TOKENS:
                i += 1
                continue
            if tok0 in ("data", "record"):
                if len(tokens) > 1:
                    register(tokens[1].rstrip(":"), relpath, i + 1, "data/record")
                i += 1
                continue
            if tok0 in BLOCK_OPENERS:
                # nested block opener (e.g. a postulate/mutual inside a
                # private block) — recurse the same way scan_block does.
                rest = vline[len(tok0) :].strip()
                if rest == "":
                    j = i + 1
                    inner_base = None
                    while j < end:
                        if visible[j].strip() != "":
                            inner_base = leading_spaces(raw_lines[j])
                            break
                        j += 1
                    if inner_base is None or inner_base <= base_indent:
                        i += 1
                        continue
                    inner_kind = "postulate" if tok0 == "postulate" else kind
                    i = scan_sub_block(
                        raw_lines, visible, j, end, inner_base, relpath, inner_kind
                    )
                    continue
                else:
                    mtoks = rest.split()
                    if mtoks:
                        mname = mtoks[0].rstrip(":")
                        inner_kind = "postulate" if tok0 == "postulate" else kind
                        if inner_kind == "postulate":
                            postulate_names.add(mname)
                        register(mname, relpath, i + 1, inner_kind)
                    i += 1
                    continue

            if tok0 == "_":
                i += 1
                continue
            # Only clause-shaped lines are candidates for infix
            # reattribution — a TYPE SIGNATURE (recognisable by a
            # standalone ':' token) may legitimately MENTION an operator
            # inside its type (e.g. "hasAtLeast-pad : ... -> gasPad m g
            # hasAtLeast n") without being one of that operator's own
            # clauses; reattributing it would wrongly hand hasAtLeast-pad's
            # own signature line to `_hasAtLeast_` and, worse, leave it
            # unmasked when counting hasAtLeast-pad's OWN consumers.
            owner = None if ":" in tokens else find_mixfix_owner(tokens)
            if owner is not None:
                def_lines[owner].add((relpath, i + 1))
                i += 1
                continue
            mname = tok0.rstrip(":")
            if kind == "postulate":
                postulate_names.add(mname)
            register(mname, relpath, i + 1, kind)
            i += 1
        return i

    for relpath in files:
        raw_lines, visible = load_file(src_dir, relpath)
        n = len(raw_lines)
        scan_block(raw_lines, visible, 0, n, 0, relpath)

    return defs, def_lines, postulate_names, order


def build_corpus(src_dir, files):
    """Per-file (joined visible text, sorted line-start-offsets) for fast
    substring search + offset -> line-number lookup."""
    corpus = {}
    for relpath in files:
        _raw, visible = load_file(src_dir, relpath)
        offsets = []
        pos = 0
        for line in visible:
            offsets.append(pos)
            pos += len(line)
        text = "".join(visible)
        corpus[relpath] = (text, offsets)
    return corpus


def mixfix_core_of(name):
    """The bare operator word/symbol of a `_foo_`-shaped name — Agda
    DEFINES a mixfix operator with its underscores (`_hasAtLeast_`), but
    every USE of it is written INFIX, without them (`g hasAtLeast n`).  A
    plain substring search for the underscored form therefore finds real
    uses in ~nothing but the operator's own declaration; searching for the
    core too is what makes such an operator's real infix uses count."""
    if len(name) > 2 and name.startswith("_") and name.endswith("_"):
        core = name[1:-1]
        if core and not core.startswith("_") and not core.endswith("_"):
            return core
    return None


def count_consumers(name, files, corpus, def_lines, extra_terms=()):
    """Count boundary-matched occurrences of `name` (and any `extra_terms`
    — e.g. a mixfix operator's bare core) across all files, excluding
    name's own defining lines in its home file(s)."""
    own_lines = def_lines.get(name, ())
    total = 0
    locations = []
    terms = [name] + [t for t in extra_terms if t]
    for relpath in files:
        text, offsets = corpus[relpath]
        if not text:
            continue
        for term in terms:
            start = 0
            L = len(term)
            while True:
                idx = text.find(term, start)
                if idx == -1:
                    break
                end = idx + L
                before = text[idx - 1] if idx > 0 else None
                after = text[end] if end < len(text) else None
                if is_boundary(before) and is_boundary(after):
                    lineno = bisect_right(offsets, idx)
                    if (relpath, lineno) not in own_lines:
                        total += 1
                        if len(locations) < 3:
                            locations.append((relpath, lineno))
                start = idx + 1
    return total, locations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--src",
        default=None,
        help="path to agda/src (default: <repo-root>/agda/src, inferred from "
        "this script's own location)",
    )
    args = parser.parse_args()

    if args.src:
        src_dir = args.src
    else:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        src_dir = os.path.join(script_dir, "..", "agda", "src")
    src_dir = os.path.abspath(src_dir)

    if not os.path.isdir(src_dir):
        print(f"error: no such directory: {src_dir}", file=sys.stderr)
        sys.exit(0)  # still exit 0 — this is a report, not a gate

    files = find_agda_files(src_dir)
    defs, def_lines, postulate_names, order = extract_definitions(src_dir, files)
    corpus = build_corpus(src_dir, files)

    orphans = []  # proven defs / data-record, zero consumers, not allowlisted
    allowlisted_unused = []
    ledger_with = []  # postulates with >=1 consumer
    ledger_without = []  # postulates with 0 consumers
    toplines = []  # top-line semantic postulates in *-Theorems.agda

    results = {}
    for name in order:
        core = mixfix_core_of(name)
        count, locs = count_consumers(
            name, files, corpus, def_lines, extra_terms=(core,) if core else ()
        )
        results[name] = (count, locs)

    for name in order:
        d = defs[name]
        count, locs = results[name]
        is_postulate = name in postulate_names
        if is_postulate:
            if count > 0:
                ledger_with.append((name, d, count, locs))
            elif d.file.endswith("-Theorems.agda"):
                # Exempt family (2): a top-line semantic claim, not dead
                # weight. Unproven, so still counted as a postulate — but it
                # belongs to the SECOND ledger, off the critical path.
                toplines.append((name, d))
            else:
                ledger_without.append((name, d, count, locs))
        else:
            if count == 0:
                if name in ALLOWLIST or name.endswith("-absurd"):
                    # Exempt family (1): refutation witnesses. Their consumer
                    # is the design record, not another term.
                    allowlisted_unused.append((name, d))
                else:
                    orphans.append((name, d))
            # count > 0, not a postulate: nothing to report, it is wired.

    # Also: allowlisted names that DO have consumers are unremarkable —
    # only report allowlist entries that never even appear in ALLOWLIST at
    # all is a no-op; nothing to do here beyond allowlisted_unused above.
    # But an allowlist entry that isn't a known def at all (typo, renamed)
    # is worth a nudge:
    stale_allowlist = [n for n in ALLOWLIST if n not in defs]

    # Top-line claims are EXEMPT from the orphan report but are still
    # unproven assumptions, so they count here. Excluding them would make the
    # headline number lie in the reassuring direction.
    total_postulates = len(ledger_with) + len(ledger_without) + len(toplines)

    # ------------------------------------------------------------------
    # REPORT
    # ------------------------------------------------------------------
    print("=" * 78)
    print("WIRING CHECK — agda/src")
    print("=" * 78)
    print(f"files scanned: {len(files)}    top-level names found: {len(order)}")
    print()

    print("-" * 78)
    print("(A) ORPHANS — proven top-level definitions with ZERO consumers")
    print("-" * 78)
    if not orphans:
        print("  (none)")
    for name, d in sorted(orphans, key=lambda x: (x[1].file, x[1].line)):
        print(f"  {name}")
        print(f"      {d.file}:{d.line}  [{d.kind}]")
    print()

    print("-" * 78)
    print("(B) THE LEDGER — postulate members")
    print("-" * 78)
    print(f"  -- WITH consumers ({len(ledger_with)}) — real remaining work --")
    if not ledger_with:
        print("    (none)")
    for name, d, count, locs in sorted(ledger_with, key=lambda x: (x[1].file, x[1].line)):
        loc_str = "; ".join(f"{f}:{ln}" for f, ln in locs)
        print(f"    {name}  ({count} consumer{'s' if count != 1 else ''}: {loc_str})")
        print(f"        {d.file}:{d.line}")
    print()
    print(
        f"  -- ZERO consumers ({len(ledger_without)}) — dead-weight deletion "
        "candidates --"
    )
    if not ledger_without:
        print("    (none)")
    for name, d, _count, _locs in sorted(
        ledger_without, key=lambda x: (x[1].file, x[1].line)
    ):
        print(f"    {name}")
        print(f"        {d.file}:{d.line}")
    print()

    print(
        f"  -- TOP-LINE semantic claims ({len(toplines)}) — the SECOND ledger, "
        "off the critical path --"
    )
    if not toplines:
        print("    (none)")
    for name, d in sorted(toplines, key=lambda x: (x[1].file, x[1].line)):
        print(f"    {name}")
        print(f"        {d.file}:{d.line}")
    print()

    print("-" * 78)
    print("ALLOWLISTED (expected to have no in-repo consumer) — non-alarming")
    print("-" * 78)
    if not allowlisted_unused:
        print("  (none currently zero-consumer)")
    for name, d in allowlisted_unused:
        print(f"  {name}  -- {d.file}:{d.line}")
    if stale_allowlist:
        print("  NOTE — allowlist entries not found as any top-level name")
        print("  (typo, or the name was renamed/removed — worth a look):")
        for name in stale_allowlist:
            print(f"    {name}")
    print()

    print("-" * 78)
    print("(C) SUMMARY")
    print("-" * 78)
    print(f"  total postulates:              {total_postulates}")
    print(f"  orphaned postulates:            {len(ledger_without)}")
    print(f"  orphaned proven definitions:    {len(orphans)}")
    print()

    print("-" * 78)
    print("--- limitations ---")
    print("-" * 78)
    print(
        "  * TEXTUAL matching, not semantic. A name mentioned only inside a\n"
        "    `where` block, or only inside an inline trailing `-- comment` on\n"
        "    an otherwise-live code line, still counts as a 'consumer' here —\n"
        "    neither is a real use.\n"
        "  * Record FIELD names can shadow unrelated top-level names of the\n"
        "    same spelling; this script does not disambiguate by type or\n"
        "    scope, only by text.\n"
        "  * Only whole-line `--` comments and `{- ... -}` block comments are\n"
        "    stripped; nested block comments are not specially handled (none\n"
        "    are known to exist in agda/src today).\n"
        "  * A postulate member's OWN defining line is excluded from its own\n"
        "    consumer count, but its (possibly multi-line) TYPE is not masked\n"
        "    beyond that first line — this matches the task's literal\n"
        "    definition of 'defining line' (the line starting with the name\n"
        "    at column 0 / at the postulate block's base indent), not the\n"
        "    whole signature.\n"
        "  * Two DIFFERENT top-level definitions that happen to share a name\n"
        "    (e.g. `main` in both CLI/Main.agda and QuickCheck.agda — two\n"
        "    distinct compiled entry points) are treated as ONE name: their\n"
        "    defining lines and consumer counts merge.  Only `main` is known\n"
        "    to collide like this today.\n"
        "  * A mixfix operator `_op_` is searched for BOTH underscored\n"
        "    (its declaration form) and bare (`op`, its real infix use\n"
        "    form) — but only the LHS half of a clause line (before its own\n"
        "    `=`/`with`/`rewrite`) is checked when deciding whether a line\n"
        "    DEFINES that operator, so a line whose RHS merely USES the\n"
        "    operator is never mistaken for one of its clauses.\n"
        "  * This is a report for a human to rule on, not a build gate — it\n"
        "    always exits 0, and it deletes nothing."
    )


if __name__ == "__main__":
    main()
