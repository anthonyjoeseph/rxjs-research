#!/usr/bin/env python3
"""The wiring law, mechanised: NEVER LEAVE A PROOF HANGING (see CLAUDE.md).

Two rules, and the second is a special case of the first.

  R1  REACHABILITY.  Every top-level definition and every postulate must be
      reachable from `Main.agda`'s claims (or from a MODULE_ROOTS entry
      point), following the edge relation below.  One route suffices: a
      name used in ten places needs only one of them to trace home.

  R2  A POSTULATE IS A LEAF.  A name passed as a bare argument TO a
      postulate earns NO reachability from that site.  Passing is allowed —
      what is forbidden is a postulate being the ONLY connective tissue
      between a proven definition and Main.  Such a lemma has never had its
      FIT tested: nothing reduces it, so nothing checks that its type is
      the one the parent actually needs.

THE EDGE RELATION.  Two kinds of edge, and they differ only under R2:

                          | counts for reachability
    ----------------------+------------------------
    type edge  (a name    | YES — a postulate's statement legitimately
    in a statement)       | needs vocabulary, and Main claims the statement
    ----------------------+------------------------
    application edge (a   | NO when the callee is a POSTULATE.  Yes when it
    name passed as a bare | is a definition: a real body APPLIES what it is
    argument at a call)   | given, so the composition is checked.

WHY THIS SHAPE IS ROBUST TO ITS OWN IMPRECISION.  Deciding "lemma passed as
a proof" vs "function applied to compute a value" is a TYPE question and
this script only has text.  It errs by over-suppressing.  But a suppressed
edge can only produce a FAILURE when it was that name's ONLY route home —
and a name whose only route is into a postulate is exactly what R2 exists
to report.  A misread edge on a name with any other consumer is invisible.
Contrast the earlier standalone leaf check, which gated on the classifier
directly and measured 40 false positives out of 110 postulates.

WHAT THIS REPLACES.  `agda/DEFERRED.txt` and its ratchet are GONE: R2 is
absolute, so there is nothing to grandfather.  The `-core`-suffix heuristic
is gone with it — R2 is structural and sees every postulate.  The A3
gate-cone check and the B3 ordering hazard are gone too, both subsumed by
R1 (a definition wired only by a probe no longer traces to Main, so it
fails R1 on its own).

TWO CHECKS BEYOND R1/R2, kept because R1 structurally cannot see them:
  * UNREACHABLE MODULES — a file of pure `open import … public` re-exports
    has no definitions to orphan, so definition-level reachability is blind
    to it however dead it is.
  * VACUOUS POSTULATES — R2 is perfectly happy with a `⊤`-typed leaf, but a
    postulate that asserts nothing reads as discharged.  CLAUDE.md: "A
    POSTULATE MUST ASSERT SOMETHING."

This is a TEXTUAL heuristic, not a semantic one — see the limitations
footer, and read it before trusting a borderline case.

Usage:
    scripts/check-wiring.py [--src DIR] [--gate]
"""

import argparse
import functools
import io
import os
import re
import sys
from bisect import bisect_right
from collections import defaultdict

# ---------------------------------------------------------------------------
# EXEMPT FAMILY — `*-absurd` REFUTATION WITNESSES (design-session ruling,
# 2026-08-05).  A machine-checked `… → ⊥` is the only durable form of "this
# route is dead, do not retry it", and it is load-bearing for the DESIGN
# process rather than for another term.  Tested twice: `caps-frame-boundary-
# absurd` and `round3b-ledger-reset-absurd` are what proved the anchor
# problem real rather than a wiring gap, saving a long wasted grind.  A
# worker classified them "archive, not live infrastructure" and was
# overruled; deleting one costs a future session the whole refutation.
#
# Everything else that used to sit in an ALLOWLIST here is now handled
# STRUCTURALLY and needs no entry: the top-line theorems and the semantic
# claims are Main's own `using (...)` names, so they are reachability SEEDS;
# and `main` in CLI/Main.agda and QuickCheck.agda is a definition of a
# MODULE_ROOTS file, seeded the same way.  A name earns exemption by being
# claimed, never by being listed.
# ---------------------------------------------------------------------------
EXEMPT_SUFFIXES = ("-absurd",)


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


@functools.lru_cache(maxsize=None)   # 110 postulates × 75 files of
def load_file(src_dir, relpath):     # re-reads was the whole runtime
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

            # `module … where` OPENS AN INDENTED SCOPE OF ORDINARY
            # DEFINITIONS.  Anonymous parameterised modules (`module _ (S
            # M : ℕ) … where`) are used across Caps-Face / Measures /
            # Burst-Walk to share a telescope, and `module` sitting in
            # SKIP_HEAD_TOKENS meant every definition inside one was never
            # registered at all — not orphan-checked, not reachability-
            # checked, invisible.  Measured 2026-08-18: 7 such blocks in
            # four of the heaviest modules in the tree.  Recurse exactly as
            # into `mutual`; never register the module's OWN name, because
            # a module is a scope and not a definition.
            if tok0 == "module":
                k, limit = i, min(end, i + 12)
                while k < limit and visible[k].split("--", 1)[0].split()[-1:] != ["where"]:
                    k += 1
                if k >= limit:
                    i += 1          # not a `… where` header after all
                    continue
                j = k + 1
                base_indent = None
                while j < end:
                    if visible[j].strip() != "":
                        base_indent = leading_spaces(raw_lines[j])
                        break
                    j += 1
                if base_indent is None or base_indent <= indent_level:
                    i = k + 1   # a FILE-level `module Foo where`: its body
                    continue    # sits at this same indent, so do not recurse
                i = scan_sub_block(
                    raw_lines, visible, j, end, base_indent, relpath, "def"
                )
                continue

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
                # AN ANONYMOUS PIN OWNS ITS SPAN.  `_ : T` / `_ = …` (the
                # bug-cache idiom, and the `refl` pins through the proof) can
                # never HAVE a consumer, so it is not a name worth orphan-
                # checking — but it is a real body that CONSUMES, and the
                # typechecker checks it, so whatever it uses IS used.
                # Skipping it entirely mis-attributed its whole body to the
                # definition ABOVE it: measured 2026-08-18, `sucW≰W`'s only
                # real use sits inside the anonymous pin following it and was
                # dropped as a self-reference.  Register it under a synthetic
                # per-site name — never reported, always a reachability seed.
                register(f"_#{relpath}:{i + 1}", relpath, i + 1, "anon")
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
                # AN ANONYMOUS PIN OWNS ITS SPAN.  `_ : T` / `_ = …` (the
                # bug-cache idiom, and the `refl` pins through the proof) can
                # never HAVE a consumer, so it is not a name worth orphan-
                # checking — but it is a real body that CONSUMES, and the
                # typechecker checks it, so whatever it uses IS used.
                # Skipping it entirely mis-attributed its whole body to the
                # definition ABOVE it: measured 2026-08-18, `sucW≰W`'s only
                # real use sits inside the anonymous pin following it and was
                # dropped as a self-reference.  Register it under a synthetic
                # per-site name — never reported, always a reachability seed.
                register(f"_#{relpath}:{i + 1}", relpath, i + 1, "anon")
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


# ---------------------------------------------------------------------------
# THE GRAPH
# ---------------------------------------------------------------------------

def owner_index(def_lines):
    """file -> sorted [(line, name)] of every definition head, so any line can
    be attributed to the definition whose body it belongs to."""
    by_file = defaultdict(list)
    for name, sites in def_lines.items():
        for (f, ln) in sites:
            by_file[f].append((ln, name))
    for f in by_file:
        by_file[f].sort()
    return by_file


def owner_of(by_file, relpath, lineno):
    lst = by_file.get(relpath)
    if not lst:
        return None
    i = bisect_right(lst, (lineno, "\uffff")) - 1
    return lst[i][1] if i >= 0 else None


_BND = r"[\w\'\u1d49\u1d5b\u1d9c\u1d4d\u1d57\u02e2\u2264\u2261?\u2032-]"


def postulate_arg_sites(src_dir, files, defs, def_lines, postulate_names):
    """R2's suppression set: (file, line) -> {names passed as BARE arguments
    to an applied postulate}.

    Only a BARE identifier at the application's top level counts as passed.
    A name nested inside parentheses with its own arguments is a VALUE being
    COMPUTED — `INV?-install \u03a8 (Caps.cSize (frameStep j c)) \u2026` applies
    `frameStep` to build a Caps, it does not hand `frameStep` over as a
    proof.  Measured 2026-08-18: without this restriction the classifier
    reported 40 of 110 postulates as non-leaves, every one a false positive.

    A mention left of the clause's `=` is in a TYPE, not an application, so
    it is never suppressed: that is the type edge, and R2 does not touch it.
    """
    suppressed = defaultdict(set)
    for P in sorted(postulate_names):
        own = def_lines.get(P, ())
        pat = re.compile(r"(?<!" + _BND + r")" + re.escape(P) + r"(?!" + _BND + r")")
        for relpath in files:
            if relpath == "Main.agda":
                continue
            _raw, visible = load_file(src_dir, relpath)
            for i, line in enumerate(visible, start=1):
                if (relpath, i) in own or not pat.search(line):
                    continue
                base = len(line) - len(line.lstrip())
                span, j = [(i, line)], i
                while j < len(visible):
                    nxt = visible[j]
                    if not nxt.strip() or len(nxt) - len(nxt.lstrip()) <= base:
                        break
                    span.append((j + 1, nxt))
                    j += 1
                expr = " ".join(t.strip() for _l, t in span)
                eq = expr.find("=")
                for m in pat.finditer(expr):
                    if eq == -1 or m.start() < eq:
                        continue                      # a TYPE mention
                    k, n = m.end(), len(expr)
                    while k < n:
                        ch = expr[k]
                        if ch == " ":
                            k += 1
                            continue
                        if ch in ")}],;=":
                            break                     # application ends
                        if ch in "({":                # nested: a computation
                            d, k2 = 1, k + 1
                            while k2 < n and d:
                                if expr[k2] in "({":
                                    d += 1
                                elif expr[k2] in ")}":
                                    d -= 1
                                k2 += 1
                            k = k2
                            continue
                        mm = re.match(r"[^\s(){}\[\],;]+", expr[k:])
                        if not mm:
                            break
                        for (ln, _t) in span:
                            suppressed[(relpath, ln)].add(mm.group(0))
                        k += mm.end()
    return suppressed


def build_graph(src_dir, files, defs, def_lines, postulate_names, order,
                corpus, main_claims, suppressed):
    """edges: name -> names it reaches.  consumers: name -> names reaching it.
    seed: the reachability roots (Main's claims + everything a MODULE_ROOTS
    file defines or mentions — those are separately compiled binaries whose
    consumer is the shell, so no textual search will ever find one)."""
    by_file = owner_index(def_lines)
    mods = {rel[:-5].replace(os.sep, "."): rel for rel in files}
    root_files = {mods[m] for m in MODULE_ROOTS if m in mods}
    edges, consumers = defaultdict(set), defaultdict(set)
    seed = {c for c in main_claims if c in defs}
    for name in order:
        if defs[name].file in root_files or defs[name].kind == "anon":
            seed.add(name)
        terms = [name]
        core = mixfix_core_of(name)
        if core:
            terms.append(core)
        own = def_lines.get(name, ())
        for relpath in files:
            if relpath == "Main.agda":
                continue
            text, offsets, import_lines = corpus[relpath]
            if not text:
                continue
            for term in terms:
                idx = text.find(term)
                while idx != -1:
                    end = idx + len(term)
                    before = text[idx - 1] if idx > 0 else None
                    after = text[end] if end < len(text) else None
                    if is_boundary(before) and is_boundary(after):
                        lineno = bisect_right(offsets, idx)
                        if ((relpath, lineno) not in own
                                and lineno not in import_lines):
                            if relpath in root_files:
                                seed.add(name)
                            o = owner_of(by_file, relpath, lineno)
                            # R2: a bare argument handed to a postulate earns
                            # nothing from this site.
                            if (o is not None and o != name
                                    and name not in suppressed.get((relpath, lineno), ())):
                                edges[o].add(name)
                                consumers[name].add(o)
                    idx = text.find(term, idx + 1)
    return edges, consumers, seed


def reachable_from(seed, edges):
    R, stack = set(seed), list(seed)
    while stack:
        n = stack.pop()
        for m in edges.get(n, ()):
            if m not in R:
                R.add(m)
                stack.append(m)
    return R


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", default=None,
                        help="path to agda/src (default: inferred from this "
                             "script's location)")
    parser.add_argument("--gate", action="store_true",
                        help="exit 1 when the wiring law is violated. Without "
                             "this the script is a report and always exits 0.")
    args = parser.parse_args()

    if args.src:
        src_dir = args.src
    else:
        here = os.path.dirname(os.path.abspath(__file__))
        src_dir = os.path.join(here, "..", "agda", "src")
    src_dir = os.path.abspath(src_dir)
    if not os.path.isdir(src_dir):
        print(f"error: no such directory: {src_dir}", file=sys.stderr)
        sys.exit(2)

    files = find_agda_files(src_dir)
    defs, def_lines, postulate_names, order = extract_definitions(src_dir, files)
    corpus = build_corpus(src_dir, files)
    main_claims, main_ok = read_main_claims(src_dir)
    suppressed = postulate_arg_sites(src_dir, files, defs, def_lines,
                                     postulate_names)
    edges, consumers, seed = build_graph(
        src_dir, files, defs, def_lines, postulate_names, order, corpus,
        main_claims, suppressed)
    R = reachable_from(seed, edges)

    exempt = lambda n: n.endswith(EXEMPT_SUFFIXES) or defs[n].kind == "anon"
    unreached = [n for n in order if n not in R and not exempt(n)]
    exempted = [n for n in order if n not in R and exempt(n)]
    dead_post = [n for n in unreached if n in postulate_names]
    dead_defs = [n for n in unreached if n not in postulate_names]
    dead_modules = find_unreachable_modules(src_dir, files)
    vacuous = find_vacuous(src_dir, defs, postulate_names)
    missing_claims = sorted(n for n in main_claims if n not in defs)

    print("=" * 78)
    print("WIRING CHECK \u2014 agda/src")
    print("=" * 78)
    print(f"files {len(files)}   top-level names {len(order)}   "
          f"postulates {len(postulate_names)}")
    print(f"reachability seeds {len(seed)}  (Main's claims + MODULE_ROOTS)")
    print(f"REACHABLE {len(R)}   unreachable {len(unreached)}   "
          f"exempt (*-absurd) {len(exempted)}")
    if not main_ok:
        print()
        print("  !! Main.agda has a bare `open import` with no `using (...)`.")
        print("     Main must NAME individual definitions, so that 'imported'")
        print("     means 'claimed' and not merely 'compiled'.  Until it does,")
        print("     the seed set is INCOMPLETE and every number here is soft.")
    if missing_claims:
        print()
        print("  !! BROKEN CLAIMS \u2014 Main.agda names these, no definition found:")
        for n in missing_claims:
            print(f"       {n}")
    print()

    print("-" * 78)
    print("(R1) UNREACHABLE \u2014 no route from Main to these")
    print("-" * 78)
    if not unreached:
        print("  (none)")
    else:
        print("  Nothing that Main claims reaches these, so `make agda` proves")
        print("  nothing about them.  Each is EITHER a missing wire (its")
        print("  consumer exists but is itself unreachable, or the assembly")
        print("  that should call it was never written) OR dead weight.  Both")
        print("  are findings; leaving it undecided is not an option.")
        print()
        print(f"  -- POSTULATES ({len(dead_post)}) --")
        if not dead_post:
            print("    (none)")
        for n in dead_post:
            d = defs[n]
            print(f"    {n}")
            print(f"        {d.file}:{d.line}   named by {len(consumers.get(n, ()))} "
                  f"other definition(s), none reachable")
        print()
        print(f"  -- PROVEN DEFINITIONS ({len(dead_defs)}) --")
        if not dead_defs:
            print("    (none)")
        for n in dead_defs:
            d = defs[n]
            c = len(consumers.get(n, ()))
            tag = "  <- ZERO consumers anywhere" if c == 0 else f"  ({c} consumer(s), all unreachable)"
            print(f"    {n}")
            print(f"        {d.file}:{d.line}{tag}")
    print()

    print("-" * 78)
    print("UNREACHABLE MODULES \u2014 dead files, invisible to R1")
    print("-" * 78)
    if not dead_modules:
        print("  (none)")
    else:
        print("  Nothing reaches these \u2014 not Main, not any entry point.  A")
        print("  module of pure `open import \u2026 public` re-exports has NO")
        print("  definitions to orphan, so R1 cannot see it however dead it is.")
    for mod, rel in dead_modules:
        print(f"    {mod}")
        print(f"        {rel}")
    print()

    print("-" * 78)
    print("VACUOUS POSTULATES \u2014 assert nothing, but read as discharged")
    print("-" * 78)
    if not vacuous:
        print("  (none)")
    else:
        print("  A `\u22a4`-typed postulate is inhabited by `tt`, so it carries no")
        print("  content \u2014 its real claim sits in a comment, where neither the")
        print("  typechecker nor grep can see it.  State the claim.")
    for name, d, is_exempt in vacuous:
        tag = "  [EXEMPT \u2014 see VACUOUS_ALLOWLIST]" if is_exempt else ""
        print(f"    {name}{tag}")
        print(f"        {d.file}:{d.line}")
    print()

    print("-" * 78)
    print("--- limitations ---")
    print("-" * 78)
    print(
        "  * TEXTUAL matching, not semantic.  A name mentioned only inside an\n"
        "    inline trailing `-- comment` on an otherwise-live code line still\n"
        "    counts as an edge.  Whole-line `--` and `{- -}` comments ARE\n"
        "    stripped; nested block comments are not specially handled.\n"
        "  * Record FIELD names can shadow unrelated top-level names of the\n"
        "    same spelling, and a short name (`S`, `G`) is usually a local\n"
        "    binder rather than the top-level definition it collides with.\n"
        "    This script disambiguates by text alone, never by type or scope.\n"
        "  * R2's suppression errs toward over-suppressing (see the module\n"
        "    docstring).  That is deliberate and self-limiting: it can only\n"
        "    fail a name whose ONLY route home was the suppressed edge.\n"
        "  * Two DIFFERENT definitions sharing a name (`main` in both\n"
        "    CLI/Main.agda and QuickCheck.agda) merge into one node.\n"
        "  * Reachability answers 'no consumer TODAY', never 'no consumer\n"
        "    EVER'.  A definition needed by work not yet written reads as\n"
        "    unreachable; prefer WIRING to deleting whenever a plausible\n"
        "    consumer is nameable (CLAUDE.md, DELETION).\n"
        "  * Without --gate this is a report for a human to rule on."
    )

    if args.gate:
        problems = []
        if dead_defs:
            problems.append(f"{len(dead_defs)} unreachable definition(s)")
        if dead_post:
            problems.append(f"{len(dead_post)} unreachable postulate(s)")
        if dead_modules:
            problems.append(f"{len(dead_modules)} unreachable module(s)")
        unexcused = [v for v in vacuous if not v[2]]
        if unexcused:
            problems.append(f"{len(unexcused)} vacuous (\u22a4-typed) postulate(s)")
        if not main_ok:
            problems.append("Main.agda has a bare `open import`")
        if missing_claims:
            problems.append(f"{len(missing_claims)} broken Main claim(s)")
        if problems:
            print()
            print("=" * 78)
            print("WIRING GATE: FAIL \u2014 " + "; ".join(problems))
            print("=" * 78)
            sys.exit(1)
        print()
        print("=" * 78)
        print("WIRING GATE: PASS \u2014 every definition and every postulate")
        print("traces to a top-level claim through real bodies; no postulate")
        print("is the only tissue holding a proof to Main")
        print("=" * 78)


if __name__ == "__main__":
    main()
