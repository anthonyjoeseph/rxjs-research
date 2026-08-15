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
    scripts/check-wiring.py [--src DIR] [--gate]

Without --gate the exit code is always 0: a report for a human to rule
on.  With --gate it exits 1 on a wiring-law violation (an orphan outside
the exempt families, or a postulate that asserts nothing), which is what
makes the law enforceable next to the typechecker instead of merely
documented.
"""

import argparse
import io
import os
import re
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
    # --- design-session rulings, 2026-08-05 (see CLAUDE.md § "The wiring law"). Two FAMILIES are exempt, matched by pattern below rather
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
    # `timing-invariance`, `batch-online`).  These are
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


def read_main_claims(src_dir):
    """The names Main.agda lists in its `using (...)` clauses.

    MAIN IS THE TOP-LINE PROOF (Anthony, 2026-08-05): whatever Main imports
    sticks around, Main names individual definitions rather than bulk-opening
    modules, and Main is never edited without his approval.  So the exempt set
    is not a heuristic this script gets to invent — it is read from Main.

    This replaces an earlier guess, `d.file.endswith("-Theorems.agda")`, which
    was wrong in both directions: it exempted every postulate in a Theorems
    file including internal helpers (`truncateIn`, `emittedBefore`, `Node`,
    `δ`, `_≈ˢ_`), and it would have missed a claim stated anywhere else.  A
    filename is not a claim; being named in Main is.

    Returns (claims, ok).  `ok` is False when Main could not be parsed or has
    a bare `open import` with no `using` clause — a violation of rule 2, and
    the caller must say so loudly rather than silently reporting fewer claims.
    """
    path = os.path.join(src_dir, "Main.agda")
    try:
        with open(path, encoding="utf-8") as fh:
            raw = fh.read().split("\n")
    except OSError:
        return set(), False

    visible = [l for l in raw if not l.lstrip().startswith("--")]
    text = "\n".join(visible)

    claims = set()
    bare = []
    # Each `open import M` optionally followed by `using ( a ; b ; c )`, where
    # the clause may span lines (this file wraps them one name per line).
    for m in re.finditer(r"open\s+import\s+(\S+)([^\n]*(?:\n(?!\s*(?:open|module)\b)[^\n]*)*)",
                         text):
        module, tail = m.group(1), m.group(2)
        u = re.search(r"using\s*\((.*?)\)", tail, re.DOTALL)
        if not u:
            bare.append(module)
            continue
        for piece in u.group(1).replace("\n", " ").split(";"):
            nm = piece.strip()
            if nm:
                claims.add(nm)
    return claims, (not bare)


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
    """Remove comment text so that "a comment is not a wire" holds.

    Two cases, and the second one used to be a hole:
      * a line whose first non-space characters are `--` is dropped whole;
      * an INLINE trailing ` -- ...` on an otherwise-code line is now cut
        at the comment marker.  It used to be left alone, which meant a
        name mentioned only in a trailing comment counted as a real
        consumer — i.e. a genuinely orphaned definition could read as
        WIRED.  That is a false negative in the safety-critical
        direction, so it is closed here rather than documented.

    The marker is ` -- ` (or ` --` at end of line): leading space required,
    so a mixfix operator whose name embeds `--` is never cut.  Column
    positions are not preserved, but nothing downstream reads columns —
    only line numbers.
    """
    out = []
    for line in visible_lines:
        if line.lstrip().startswith("--"):
            out.append("")
            continue
        idx = line.find(" --")
        if idx >= 0:
            rest = line[idx + 3 :]
            # ` --` starts a comment unless it continues into an operator
            # character (Agda's own rule); `-` continues it (`---` is still
            # a comment), so only a symbol like `>` in ` -->` protects it.
            if rest == "" or rest[0] in " -\t":
                out.append(line[:idx])
                continue
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


def import_span_lines(visible):
    """1-based line numbers occupied by `open import` / `import` statements,
    INCLUDING the continuation lines of a multi-line `using (...)` clause.

    Why this exists: a name mentioned in another module's `using` clause is
    IMPORTED, not CONSUMED, and the whole point of this script is that those
    are different.  Counting them let an unused import launder an orphan into
    looking wired — `depth-capped` (Depth-Bound.agda) vanished from the orphan
    report on 2026-08-05 the moment Caps-Bridge added
    `open import ... using (depth-capped)` without calling it even once.  That
    is exactly the "compiled, not needed" loophole the wiring law exists to
    close, reproduced inside the law's own acceptance test.

    A statement runs from its `import` head until the first later line whose
    indentation returns to column 0 with a non-continuation token, so the
    hanging-indent `using (a; b;\n  c; d)` style used throughout this repo is
    absorbed correctly."""
    spans = set()
    i = 0
    n = len(visible)
    while i < n:
        stripped = visible[i].lstrip()
        if stripped.startswith("open import") or stripped.startswith("import "):
            spans.add(i + 1)
            j = i + 1
            while j < n:
                nxt = visible[j]
                if nxt.strip() == "":
                    break
                # a continuation line is INDENTED; a new column-0 statement ends the span
                if len(nxt) - len(nxt.lstrip(" ")) == 0:
                    break
                spans.add(j + 1)
                j += 1
            i = j
            continue
        i += 1
    return spans


def build_corpus(src_dir, files):
    """Per-file (joined visible text, sorted line-start-offsets) for fast
    substring search + offset -> line-number lookup, plus the set of line
    numbers belonging to import statements (never consumers — see
    `import_span_lines`)."""
    corpus = {}
    for relpath in files:
        _raw, visible = load_file(src_dir, relpath)
        offsets = []
        pos = 0
        for line in visible:
            offsets.append(pos)
            pos += len(line)
        text = "".join(visible)
        corpus[relpath] = (text, offsets, import_span_lines(visible))
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


def count_consumers(name, files, corpus, def_lines, extra_terms=(), cone=None):
    """Count boundary-matched occurrences of `name` (and any `extra_terms`
    — e.g. a mixfix operator's bare core) across all files, excluding
    name's own defining lines in its home file(s).

    Main.agda is EXCLUDED as a consumer.  It is the ROOT of the consumption
    graph, not a participant in it: since it names individual claims (rule 2),
    every claim would otherwise score a consumer purely from its own
    `using (...)` mention and land in the critical-path ledger.  That would
    erase the distinction between "postulate some other proof depends on" and
    "top-line claim we assert", which is the whole point of the two ledgers.
    """
    own_lines = def_lines.get(name, ())
    total = 0
    in_cone = 0
    locations = []
    terms = [name] + [t for t in extra_terms if t]
    for relpath in files:
        # EXACTLY src/Main.agda — NOT CLI/Main.agda, which is an unrelated
        # compiled entry point whose six helpers (process, nl, splitLines,
        # nonEmpty, parseJSON, decodeCase) really are consumed, by it. An
        # `endswith("/Main.agda")` here orphaned all six.
        if relpath == "Main.agda":
            continue
        text, offsets, import_lines = corpus[relpath]
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
                    # an `import ... using (name)` mention is IMPORTED, not
                    # CONSUMED — see import_span_lines
                    if (relpath, lineno) not in own_lines and lineno not in import_lines:
                        total += 1
                        if cone is None or relpath in cone:
                            in_cone += 1
                        if len(locations) < 3:
                            locations.append((relpath, lineno))
                start = idx + 1
    return total, locations, in_cone


def signature_text(src_dir, relpath, name, line):
    """The declared TYPE of `name`, as source text: everything after
    `name :` on its declaration line, plus every following line indented
    strictly deeper.  Returns None if the line does not declare `name`."""
    path = os.path.join(src_dir, relpath)
    try:
        with io.open(path, encoding="utf-8") as fh:
            src = fh.read().split("\n")
    except OSError:
        return None
    if line - 1 >= len(src):
        return None
    head = src[line - 1]
    m = re.match(r"^(\s*)" + re.escape(name) + r"\s*:(.*)$", head)
    if not m:
        return None
    indent, rest = m.group(1), m.group(2)
    out = [rest.strip()]
    j = line
    while j < len(src):
        cur = src[j]
        if cur.strip() == "":
            break
        if len(cur) - len(cur.lstrip()) <= len(indent):
            break
        out.append(cur.strip())
        j += 1
    return "\n".join(out)


def final_conclusion(sig):
    """The conclusion of a (possibly dependent) function type: the text
    after the LAST top-level `→`.  Parens/braces are tracked so that an
    arrow inside a hypothesis does not split the type."""
    flat = []
    for ln in sig.split("\n"):
        i = ln.find("--")
        flat.append(ln[:i] if i >= 0 else ln)
    s = " ".join(x.strip() for x in flat)
    depth, last = 0, -1
    i = 0
    while i < len(s):
        c = s[i]
        if c in "({":
            depth += 1
        elif c in ")}":
            depth -= 1
        elif depth == 0 and (c == "→" or s[i : i + 2] == "->"):
            last = i + (1 if c == "→" else 2)
        i += 1
    return s[last:].strip() if last >= 0 else s.strip()


# ---------------------------------------------------------------------------
# VACUITY EXEMPTIONS.  A `⊤`-typed postulate normally means the real claim is
# hiding in a comment (CLAUDE.md: "fix on sight").  The exception is a gap
# that is DELIBERATELY and VISIBLY not a claim — where the source itself says
# so, rather than implying content it does not have.  Same discipline as
# ALLOWLIST above: short, specific, and a reviewable diff to extend.
# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# (A3) GATE-ONLY EXEMPTIONS.  A definition whose only consumers sit outside
# `make agda`'s cone is normally dead proof code propped up by a probe.  Two
# kinds are legitimate, and each is listed with its reason so extending this
# is a reviewable diff:
#   * it serves a compiled TOOL (the CLI, QuickCheck, the bug cache, the
#     harness) — those have their own make targets and are not the proof;
#   * it is PROVEN and waiting for a consumer that is still a postulate.
# The second kind is real debt and every line of it should name what has to
# be ground before the line can go.
# ---------------------------------------------------------------------------
GATE_ONLY_ALLOWLIST = {
    "Grouped": (
        "the oracle's wire format, consumed by CLI/Encode and compiled by "
        "`make cli-build`.  Not proof code; it has no business in Main's cone "
        "beyond living in Rx/Evaluator beside the evaluator it describes."
    ),
    "wellFormed?": (
        "the protocol predicate QuickCheck and the type-level bug cache assert "
        "against (`make quickcheck`, `make bug-cache`).  A tool's oracle, not "
        "a proof obligation."
    ),
    "slotHop-fix": (
        "PROVEN and genuinely waiting: it is the equation the walk face's "
        "input clause spends, and that clause (input-wet-shared) is still a "
        "postulate, so nothing in the gate's cone can spend it yet.  The "
        "Demand-Probe rows are receipts, not consumers.  DELETE THIS LINE the "
        "moment input-wet-shared is ground — if it survives that, the proof "
        "found another route and this lemma is dead."
    ),
}


VACUOUS_ALLOWLIST = {
    "defer-shift": (
        "Rx/Evaluator-Theorems.agda states this ⊤ on purpose and says so in "
        "the declaration's own comment: 'Left as ⊤ on purpose: an honest gap, "
        "not a claim.'  Stating it for real needs a defined tick-trace and a "
        "defined (not postulated) renaming equivalence — borrowing the one "
        "relation of that shape, Rx.Time-Theorems._≈ˢ_, would relocate the "
        "vacuity rather than fix it.  That is a design call on a top-line "
        "semantic claim, not a leaf-module repair, so it is exempted "
        "EXPLICITLY here instead of being silently fabricated or silently "
        "ignored.  A NEW ⊤ postulate still fails the gate."
    ),
}


# ---------------------------------------------------------------------------
# MODULE ROOTS.  Reachability is computed from Main plus these — each is a
# SEPARATE compiled entry point with its own make target, so it is legitimately
# unreachable from Main but is NOT dead.  Listing ROOTS rather than individual
# modules means anything they import is covered automatically; only a module
# nothing reaches at all is reported.
# ---------------------------------------------------------------------------
MODULE_ROOTS = {
    "CLI.Main": "the oracle CLI — compiled by `make cli-build`, run by `make oracle`",
    "QuickCheck": "the all-Agda QuickCheck — `make qc-build` / `make quickcheck`",
    "Implementation.Unit-Test": "the type-level bug cache — `make bug-cache`",
    "Harness.Main": "the compiled measurement harness — `make harness-build` / `make harness`",
    "Verify-Budget-Sufficient.Demand-Probe": "the gas-demand measurement rows — checked by `make bug-cache`",
}

_IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([^\s;()]+)")


def arrow_slots(sig):
    """Count `→` at brace/paren depth 0 in a signature — an UPPER BOUND on
    the number of premises (it also counts the binder arrow of a leading
    `∀ … →` telescope).  Used only to size the deferred-obligation ledger,
    never to gate."""
    if not sig:
        return 0
    depth = 0
    n = 0
    for ch in sig:
        if ch in "({[":
            depth += 1
        elif ch in ")}]":
            depth -= 1
        elif ch in "→" and depth == 0:
            n += 1
    return n


def find_deferred_obligations(src_dir, defs, def_lines, postulate_names,
                              files, corpus):
    """Section B4 — PASSED-ONLY LEMMAS, i.e. DEFERRED OBLIGATIONS.

    THE BLIND SPOT THIS CLOSES.  The wiring law tracks NAMES: every
    definition must have a consumer.  It does not track OBLIGATIONS INSIDE
    TYPES.  A PROVEN lemma with its own premises can be handed as a bare
    value into a POSTULATE's hypothesis slot — `subscribeE-wet-core` takes
    22 such lemmas — and that counts as a consumer, so the lemma reads as
    fully wired and the gate stays green.  But a postulate never runs, so
    it never APPLIES what it was given: nobody has supplied that lemma's
    premises, and nobody will until the postulate is proven.

    Those premises are real remaining work that appears NOWHERE in the
    postulate ledger.  `hop-edge` (Wet.agda:4052) is the worked example:
    proven, wired, consumed — and all three of its premises unpaid, one of
    which (`hopDᵛ Ŝ o < r`) went unexamined for the whole campaign because
    nothing in the repo forced anyone to look at it.

    So: report every proven definition whose consumers are ONLY assembly
    argument positions — passed, never applied.

    THE LEAF-ONLY RULE (Anthony, 2026-08-15).  This set is FROZEN and may
    only SHRINK.  Passed-only is no longer "normal while the parent is
    postulated" — it is the state the rule exists to prevent, because a
    lemma in it has never had its FIT tested: nothing reduces it, so
    nothing checks that its type is the one the parent actually needs.
    Two `-core` discharges shed seven-plus leading hypotheses apiece for
    exactly that reason.

    The remedy for a NEW passed-only lemma is never "add a ledger line".
    It is to write the parent as a REAL BODY over POSTULATED LEAVES:

        postulate l₁ : L₁                 -- gap, a true leaf
        P : T
        P = <real body applying l₁>       -- CHECKED composition

    rather than as a postulate over proven pieces (`P = P-core l₁ …`),
    where the composition is asserted and checked by nobody.  When the
    body cannot be written yet, postulate P BARE and mint no leaves — an
    unwritten route is a header comment, not a type nobody verifies.
    """
    # 1. Assembly spans: for each `-core` postulate, the expression(s) that
    #    feed it.  An assembly is `Parent = Parent-core arg₁ … argₖ`, whose
    #    RHS may continue across more-indented lines.
    assemblies = []          # (parent, core, relpath, first_line, [arg tokens])
    arg_sites = {}           # (relpath, lineno) -> core name
    cores = sorted(n for n in postulate_names if n.endswith("-core"))
    for core in cores:
        for relpath in files:
            text, offsets, _imports = corpus[relpath]
            _raw, visible = load_file(src_dir, relpath)
            for i, line in enumerate(visible, start=1):
                if (relpath, i) in def_lines.get(core, ()):
                    continue
                if re.search(r"(?<![\w'-])" + re.escape(core) + r"(?![\w'-])", line) is None:
                    continue
                if line.lstrip().startswith("--"):
                    continue
                # collect this line plus its more-indented continuations
                span = [(i, line)]
                base = len(line) - len(line.lstrip())
                j = i + 1
                while j <= len(visible):
                    nxt = visible[j - 1]
                    if not nxt.strip():
                        break
                    ind = len(nxt) - len(nxt.lstrip())
                    if ind <= base:
                        break
                    span.append((j, nxt))
                    j += 1
                toks = set()
                for ln, txt in span:
                    body = txt.split("--", 1)[0]
                    for t in re.findall(r"[A-Za-z_][\w'ᵉᵛᶜᵍᵗˢ≤≡?′-]*|[^\s()\\{}]+", body):
                        toks.add(t)
                    arg_sites[(relpath, ln)] = core
                parent = visible[i - 1].split("=", 1)[0].strip().split()
                parent = parent[0] if parent else "?"
                passed = sorted(
                    t for t in toks
                    if t in defs and t != core and t not in postulate_names
                    and defs[t].kind == "def"
                )
                if passed:
                    assemblies.append((parent, core, relpath, i, passed))

    # 2. A lemma is PASSED-ONLY when every consumer site of it is an
    #    assembly argument position.
    passed_lemmas = {}
    for _parent, core, _rp, _ln, passed in assemblies:
        for lem in passed:
            passed_lemmas.setdefault(lem, set()).add(core)

    rows = []
    for lem, parents in sorted(passed_lemmas.items()):
        _n, locs, _c = count_consumers(lem, files, corpus, def_lines,
                                   extra_terms=(mixfix_core_of(lem),))
        elsewhere = [(f, l) for (f, l) in locs if (f, l) not in arg_sites]
        if elsewhere:
            continue                      # genuinely applied somewhere
        d = defs[lem]
        sig = signature_text(src_dir, d.file, lem, d.line)
        rows.append((lem, d, sorted(parents), arrow_slots(sig)))
    return rows, assemblies


def find_unreachable_modules(src_dir, files):
    """Modules under src/ that NOTHING reaches — not Main, not any entry point.

    THE BLIND SPOT THIS CLOSES: the orphan report scans DEFINITIONS for
    consumers, so a module holding only `open import … public` re-exports has
    nothing to orphan and reads as clean no matter how dead it is.  A module can
    therefore be entirely unused while every report above says zero.  Module
    reachability is a different question from definition reachability, and it
    needs asking separately.
    """
    mods = {}
    for rel in files:
        mods[rel[:-5].replace(os.sep, ".")] = rel

    seen = set()
    stack = ["Main"] + [m for m in MODULE_ROOTS if m in mods]
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        try:
            with io.open(os.path.join(src_dir, mods[m]), encoding="utf-8") as fh:
                body = fh.read().split("\n")
        except OSError:
            continue
        for line in body:
            if line.lstrip().startswith("--"):
                continue
            g = _IMPORT_RE.match(line)
            if g and g.group(1) in mods:
                stack.append(g.group(1))

    return sorted((m, mods[m]) for m in set(mods) - seen)


def gate_cone(src_dir, files):
    """The modules `make agda` actually compiles: everything reachable from
    Main, and NOTHING else.

    THIS IS NOT find_unreachable_modules' set.  That one seeds from Main PLUS
    every MODULE_ROOTS entry, because a separately-compiled binary is not dead.
    But those roots are compiled by their OWN make targets, not by the gate —
    so a definition whose only consumers live in a root (a probe file, the
    harness, the CLI) is never touched by `make agda`.  Counting such a
    definition as WIRED is the loophole this closes: a probe could keep dead
    proof code alive indefinitely, and the report would read clean.
    """
    mods = {}
    for rel in files:
        mods[rel[:-5].replace(os.sep, ".")] = rel
    seen, stack = set(), ["Main"]
    while stack:
        m = stack.pop()
        if m in seen or m not in mods:
            continue
        seen.add(m)
        try:
            with io.open(os.path.join(src_dir, mods[m]), encoding="utf-8") as fh:
                body = fh.read().split("\n")
        except OSError:
            continue
        for line in body:
            if line.lstrip().startswith("--"):
                continue
            g = _IMPORT_RE.match(line)
            if g and g.group(1) in mods:
                stack.append(g.group(1))
    return {mods[m] for m in seen}


def find_vacuous(src_dir, defs, postulate_names):
    """Postulates whose CONCLUSION is `⊤`.  CLAUDE.md names this as a live
    trap: such a postulate asserts nothing, its real claim sitting in a
    trailing comment, yet it reads as discharged work.  Cheap to detect,
    so it is detected rather than merely documented."""
    bad = []
    for name in sorted(postulate_names):
        d = defs.get(name)
        if d is None:
            continue
        sig = signature_text(src_dir, d.file, name, d.line)
        if sig is None:
            continue
        if final_conclusion(sig) in ("⊤", "Unit"):
            bad.append((name, d, name in VACUOUS_ALLOWLIST))
    return sorted(bad, key=lambda x: (x[1].file, x[1].line))


def unreachable_parents(orphans, defs, postulate_names):
    """Orphans that NO postulate in their own file could ever consume,
    because every such postulate is declared ABOVE them.

    This is the ordering hazard that costs the most time in practice: a
    parent postulate cannot reference a definition that follows it, so an
    orphan sitting below its intended parent cannot be wired where it
    stands — either the definition moves up, or the assembly's body moves
    down.  Discovering that from a failed 40-minute typecheck is the
    expensive way; it is decidable from line numbers alone."""
    by_file = {}
    for name in postulate_names:
        d = defs.get(name)
        if d is not None:
            by_file.setdefault(d.file, []).append(d.line)
    out = []
    for name, d in orphans:
        later = [ln for ln in by_file.get(d.file, []) if ln > d.line]
        if by_file.get(d.file) and not later:
            out.append((name, d, len(by_file[d.file])))
    return sorted(out, key=lambda x: (x[1].file, x[1].line))


def read_deferred_ledger(path):
    """Read agda/DEFERRED.txt and return (names, missing).

    `names` is a frozenset of lemma names recorded as passed-only.
    `missing` is True when the file does not exist (the gate treats a missing
    ledger the same as an empty one: every measured lemma becomes a NEW
    DEFERRAL).

    Format: each non-comment, non-blank line is:
        LEMMA | DEFERRED-BY | ≤SLOTS | REASON: ...
    Only field 0 (the lemma name, before the first ' | ') is used for the
    ratchet comparison.  The rest is informational and not parsed.
    """
    try:
        with open(path, encoding="utf-8") as fh:
            lines = fh.readlines()
    except OSError:
        return frozenset(), True
    names = set()
    for line in lines:
        line = line.rstrip("\n")
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        name = line.split(" | ")[0].strip()
        if name:
            names.add(name)
    return frozenset(names), False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--src",
        default=None,
        help="path to agda/src (default: <repo-root>/agda/src, inferred from "
        "this script's own location)",
    )
    parser.add_argument(
        "--gate",
        action="store_true",
        help="exit 1 when the wiring law is violated (orphans outside the "
        "exempt families, a ⊤-typed postulate, or a B4 ratchet mismatch). "
        "Without this the script is a report and always exits 0.",
    )
    parser.add_argument(
        "--ledger",
        default=None,
        help="path to agda/DEFERRED.txt (default: <repo-root>/agda/DEFERRED.txt, "
        "inferred from this script's own location)",
    )
    args = parser.parse_args()

    if args.src:
        src_dir = args.src
    else:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        src_dir = os.path.join(script_dir, "..", "agda", "src")
    src_dir = os.path.abspath(src_dir)

    if args.ledger:
        ledger_path = args.ledger
    else:
        script_dir = os.path.dirname(os.path.abspath(__file__))
        ledger_path = os.path.join(script_dir, "..", "agda", "DEFERRED.txt")
    ledger_path = os.path.abspath(ledger_path)

    if not os.path.isdir(src_dir):
        print(f"error: no such directory: {src_dir}", file=sys.stderr)
        sys.exit(0)  # still exit 0 — this is a report, not a gate

    files = find_agda_files(src_dir)
    defs, def_lines, postulate_names, order = extract_definitions(src_dir, files)
    corpus = build_corpus(src_dir, files)
    cone_files = gate_cone(src_dir, files)
    main_claims, main_ok = read_main_claims(src_dir)

    orphans = []  # proven defs / data-record, zero consumers, not allowlisted
    allowlisted_unused = []
    gate_only = []  # consumed, but never by anything `make agda` compiles
    ledger_with = []  # postulates with >=1 consumer
    ledger_without = []  # postulates with 0 consumers
    toplines = []  # top-line semantic postulates in *-Theorems.agda

    results = {}
    for name in order:
        core = mixfix_core_of(name)
        count, locs, cone_count = count_consumers(
            name, files, corpus, def_lines, extra_terms=(core,) if core else (),
            cone=cone_files,
        )
        results[name] = (count, locs, cone_count)

    for name in order:
        d = defs[name]
        count, locs, cone_count = results[name]
        # (A3) WIRED ONLY OUTSIDE THE GATE.  It lives in a module `make agda`
        # compiles, something references it, and yet nothing the gate compiles
        # does — so its only consumers are probe/harness/CLI roots, which run
        # under their own targets.  That is dead proof code held up by a probe.
        if (count > 0 and cone_count == 0
                and d.file in cone_files
                and name not in main_claims):
            gate_only.append((name, d, count, locs))
        is_postulate = name in postulate_names
        if is_postulate:
            if count > 0:
                ledger_with.append((name, d, count, locs))
            elif name in main_claims:
                # Exempt family (2): a top-line semantic claim, because MAIN
                # NAMES IT. Unproven, so still counted as a postulate — but it
                # belongs to the SECOND ledger, off the critical path.
                toplines.append((name, d))
            else:
                ledger_without.append((name, d, count, locs))
        else:
            if count == 0:
                if name in main_claims or name in ALLOWLIST or name.endswith("-absurd"):
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

    # A name Main claims that no longer exists in src is a BROKEN CLAIM — Main
    # would not compile, so this should be impossible; report it rather than
    # skip it, because a silent skip is how a claim goes missing.
    missing_claims = sorted(n for n in main_claims if n not in defs)

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
    print(f"Main.agda claims: {len(main_claims)}  (the exempt set — Main IS the top-line proof)")
    if not main_ok:
        print()
        print("  !! RULE 2 VIOLATION: Main.agda has a bare `open import` with no")
        print("     `using (...)` clause. Main must name individual definitions, so")
        print("     that 'imported' means 'claimed' and not merely 'compiled'.")
        print("     Until it does, the exempt set below is INCOMPLETE and every")
        print("     number in this report is unreliable.")
    if missing_claims:
        print()
        print("  !! BROKEN CLAIMS: Main.agda names these, but no definition was")
        print("     found in agda/src. Main could not compile in this state:")
        for n in missing_claims:
            print(f"       {n}")
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
    vacuous = find_vacuous(src_dir, defs, postulate_names)
    dead_modules = find_unreachable_modules(src_dir, files)
    stranded = unreachable_parents(orphans, defs, postulate_names)

    print("-" * 78)
    print("(A3) WIRED ONLY OUTSIDE THE GATE — consumers exist, but none compile")
    print("-" * 78)
    if not gate_only:
        print("  (none)")
    else:
        print("  These live in modules `make agda` compiles, and something does")
        print("  reference them — but nothing the GATE compiles does.  Their only")
        print("  consumers are MODULE_ROOTS (probe rows, the harness, the CLI),")
        print("  which run under their own make targets.  A consumer that the")
        print("  proof never reaches is not a wire: a probe file can otherwise")
        print("  hold dead proof code alive forever and every count reads clean.")
        for name, d, count, locs in gate_only:
            where = ", ".join(f"{r}:{l}" for r, l in locs)
            tag = "  [allowed]" if name in GATE_ONLY_ALLOWLIST else "  ** NEW **"
            print(f"    {name}  ({d.file}:{d.line}) — {count} consumer(s), all outside: {where}{tag}")
        stale_gate_only = sorted(set(GATE_ONLY_ALLOWLIST) - {n for n, _d, _c, _l in gate_only})
        if stale_gate_only:
            print()
            print("  IN THE ALLOWLIST BUT NO LONGER MEASURED — the win case: these")
            print("  gained a real consumer inside the gate (or were deleted), so")
            print("  their exemption lines must go:")
            for name in stale_gate_only:
                print(f"    {name}")
    print()

    print("-" * 78)
    print("(A2) UNREACHABLE MODULES — dead files, invisible to the orphan report")
    print("-" * 78)
    if not dead_modules:
        print("  (none)")
    else:
        print("  Nothing reaches these — not Main, not any compiled entry point.")
        print("  A module of pure `open import … public` re-exports has NO")
        print("  definitions to orphan, so section (A) cannot see it however")
        print("  dead it is.  Module reachability is a separate question from")
        print("  definition reachability; this is where it gets asked.")
    for mod, rel in dead_modules:
        print(f"    {mod}")
        print(f"        {rel}")
    print()

    print("-" * 78)
    print("(B2) VACUOUS POSTULATES — assert nothing, but read as discharged")
    print("-" * 78)
    if not vacuous:
        print("  (none)")
    else:
        print("  A `⊤`-typed postulate is inhabited by `tt`, so it carries no")
        print("  content at all — its real claim is sitting in a comment, where")
        print("  neither the typechecker nor grep can see it.  State the claim.")
    for name, d, exempt in vacuous:
        tag = "  [EXEMPT — deliberate, see VACUOUS_ALLOWLIST]" if exempt else ""
        print(f"    {name}{tag}")
        print(f"        {d.file}:{d.line}")
    print()

    print("-" * 78)
    deferred_rows, assemblies = find_deferred_obligations(
        src_dir, defs, def_lines, postulate_names, files, corpus)

    print("(B3) ORDERING HAZARD — orphans no same-file postulate can consume")
    print("-" * 78)
    if not stranded:
        print("  (none)")
    else:
        print("  A postulate cannot reference a definition declared BELOW it.")
        print("  For each of these, every postulate in its own file precedes")
        print("  it, so its parent must live in an IMPORTING module — or the")
        print("  definition has to move up / the assembly body move down.")
        print("  Decidable from line numbers; do not learn it from a failed")
        print("  40-minute typecheck.")
    for name, d, n_post in stranded:
        print(f"    {name}")
        print(f"        {d.file}:{d.line}  (all {n_post} postulate(s) in this file are above it)")
    print()

    print("-" * 78)
    print("(B4) DEFERRED OBLIGATIONS — proven lemmas PASSED to a postulate,")
    print("     never APPLIED, so their own premises are unpaid")
    print("-" * 78)
    print("  The wiring law tracks NAMES, not OBLIGATIONS INSIDE TYPES.  A")
    print("  proven lemma handed as a bare value into a postulate's hypothesis")
    print("  slot HAS a consumer, so it reads as fully wired and the gate stays")
    print("  green — but a postulate never runs, so it never APPLIES what it was")
    print("  given.  Nobody has supplied these lemmas' premises, and nobody will")
    print("  until the parent postulate is proven.  That is real remaining work")
    print("  appearing NOWHERE in the postulate ledger.")
    print("  NOT A DELETION LIST.  These lemmas are proven and load-bearing.")
    print("  But under the LEAF-ONLY RULE this set is FROZEN and may only")
    print("  SHRINK: a passed-only lemma has never had its FIT tested, since")
    print("  nothing reduces it.  New ones are a gate FAILURE, not a ledger")
    print("  entry — write the parent as a real body over postulated leaves.")
    print()
    if not deferred_rows:
        print("  (none)")
    else:
        for name, d, parents, slots in deferred_rows:
            print(f"    {name}   (≤{slots} →-slots deferred)")
            print(f"        {d.file}:{d.line}")
            print(f"        passed to: {', '.join(parents)}")
    print()
    print(f"  assemblies feeding a -core postulate: {len(assemblies)}")
    print(f"  passed-only lemmas:                   {len(deferred_rows)}")
    print(f"  →-slots deferred (upper bound):       {sum(r[3] for r in deferred_rows)}")
    print()

    print("-" * 78)
    print("(C) SUMMARY")
    print("-" * 78)
    print(f"  total postulates:              {total_postulates}")
    print(f"  orphaned postulates:            {len(ledger_without)}")
    print(f"  orphaned proven definitions:    {len(orphans)}")
    print(f"  unreachable modules:            {len(dead_modules)}")
    print(f"  passed-only lemmas (B4):        {len(deferred_rows)}")
    print(f"  vacuous (⊤-typed) postulates:   {len(vacuous)}"
          f"  ({sum(1 for v in vacuous if v[2])} exempt)")
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
        "  * (B4)'s →-slot count is an UPPER BOUND on premises: it counts\n"
        "    every depth-0 `→`, including the binder arrow of a leading\n"
        "    `∀ … →` telescope.  It sizes the ledger, it is not an exact\n"
        "    obligation count.  (B4) is TEXTUAL too — a lemma used only\n"
        "    inside a `where` block can be misreported as passed-only.\n"
        "  * Without --gate this is a report for a human to rule on rather\n"
        "    than a build gate; it deletes nothing either way."
    )

    if args.gate:
        problems = []
        if orphans:
            problems.append(f"{len(orphans)} orphaned proven definition(s)")
        if dead_modules:
            problems.append(f"{len(dead_modules)} unreachable module(s)")
        # The law is "every DEFINITION *and every POSTULATE* is consumed".
        # Enforcing only the definition half let three unconsumed postulates
        # sit green indefinitely, so the postulate half gates too.
        if ledger_without:
            problems.append(f"{len(ledger_without)} unconsumed postulate(s)")
        unexcused = [v for v in vacuous if not v[2]]
        if unexcused:
            problems.append(f"{len(unexcused)} vacuous (⊤-typed) postulate(s)")
        if not main_ok:
            problems.append("Main.agda has a bare `open import`")

        # A3 RATCHET — a definition inside `make agda`'s cone whose only
        # consumers are OUTSIDE it.  Reporting alone was not enough: the whole
        # failure mode is that every count reads clean, so this has to gate.
        # Exempt entries carry a reason in GATE_ONLY_ALLOWLIST; a NEW one is a
        # new piece of dead proof code held up by a probe or a tool.
        gate_only_new = sorted(
            n for n, _d, _c, _l in gate_only if n not in GATE_ONLY_ALLOWLIST
        )
        gate_only_stale = sorted(
            set(GATE_ONLY_ALLOWLIST) - {n for n, _d, _c, _l in gate_only}
        )
        if gate_only_new:
            problems.append(
                f"{len(gate_only_new)} definition(s) wired ONLY outside the gate"
            )
        if gate_only_stale:
            problems.append(
                f"{len(gate_only_stale)} GATE_ONLY_ALLOWLIST entry/entries no longer "
                "measured (gained a real consumer, or deleted — remove the entry)"
            )

        # B4 RATCHET — the passed-only set must equal agda/DEFERRED.txt.
        # A new passed-only lemma (measured but not in the ledger) is a NEW
        # DEFERRAL: deferral must be an explicit, reviewed act.  A lemma in
        # the ledger but not measured means its premises are discharged or it
        # was deleted — the win case, but the ledger line must be removed so
        # the numbers stay honest.
        measured_names = frozenset(r[0] for r in deferred_rows)
        ledger_names, ledger_missing = read_deferred_ledger(ledger_path)
        new_deferrals = sorted(measured_names - ledger_names)
        stale_entries = sorted(ledger_names - measured_names)
        if ledger_missing:
            problems.append(
                f"agda/DEFERRED.txt not found at {ledger_path} — "
                "create it (run `make wiring` and add all (B4) entries)"
            )
        else:
            if new_deferrals:
                problems.append(
                    f"{len(new_deferrals)} LEAF-ONLY VIOLATION(s) — proven lemma "
                    "passed to a postulate, never applied"
                )
            if stale_entries:
                problems.append(
                    f"{len(stale_entries)} ledger entry/entries no longer measured "
                    "(premises discharged or lemma deleted — remove from agda/DEFERRED.txt)"
                )

        if problems:
            print()
            print("=" * 78)
            print("WIRING GATE: FAIL — " + "; ".join(problems))
            print("=" * 78)
            if new_deferrals:
                print()
                print("LEAF-ONLY VIOLATION — these proven lemmas are PASSED to a")
                print("postulate and never APPLIED, so nothing checks that their")
                print("types are the ones the parent actually needs.  The remedy is")
                print("NOT to add a ledger line.  For each, write the parent as a")
                print("REAL BODY over POSTULATED LEAVES:")
                print()
                print("    postulate l : L        -- the gap, a true leaf")
                print("    P : T")
                print("    P = <body applying l>  -- composition now CHECKED")
                print()
                print("If the body cannot be written yet, postulate the parent BARE")
                print("and mint no leaves at all.  agda/DEFERRED.txt is a frozen")
                print("grandfather list that may only SHRINK; growing it needs an")
                print("explicit ruling from Anthony and increases tracked debt.")
                # Build a lookup from deferred_rows for slot counts and parents
                row_map = {r[0]: r for r in deferred_rows}
                for name in new_deferrals:
                    row = row_map.get(name)
                    if row:
                        _lem, _d, parents, slots = row
                        print(
                            f"  {name}  — passed to {', '.join(parents)}, "
                            f"≤{slots} premises unpaid"
                        )
                    else:
                        print(f"  {name}  — parent unknown")
            if gate_only_new:
                print()
                print("WIRED ONLY OUTSIDE THE GATE — nothing `make agda` compiles")
                print("uses these.  Either give each a real consumer on the proof")
                print("path, delete it, or add it to GATE_ONLY_ALLOWLIST with the")
                print("reason it legitimately serves a tool or awaits a postulate:")
                for name in gate_only_new:
                    print(f"  {name}")
            if gate_only_stale:
                print()
                print("GATE_ONLY_ALLOWLIST entries no longer measured — a WIN:")
                print("each gained a consumer inside the gate (or was deleted).")
                print("Remove the entry from scripts/check-wiring.py:")
                for name in gate_only_stale:
                    print(f"  {name}")
            if stale_entries:
                print()
                print(
                    "STALE ENTRIES — remove these lines from agda/DEFERRED.txt."
                )
                print(
                    "Their premises are now discharged (or the lemma was deleted)."
                )
                print("This is a WIN; the gate fails only until the ledger is tidied:")
                for name in stale_entries:
                    print(f"  {name}")
            sys.exit(1)
        print()
        print("=" * 78)
        print("WIRING GATE: PASS — every definition AND every postulate")
        print("traces to a top-level claim, every module is reached,")
        print("and the (B4) passed-only set matches agda/DEFERRED.txt")
        print("=" * 78)


if __name__ == "__main__":
    main()
