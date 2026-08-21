#!/usr/bin/env python3
"""An import nothing uses is a DAG edge nothing pays for — find them, fix them.

Agda has no unused-import warning, so a `using (…)` clause is the one place in
this tree where a dependency can be asserted and never spent.  That is not a
tidiness matter: an import is an edge in the module graph, and an edge decides
(a) what a full `make agda` must build before this file, and (b) what an edit to
the imported module INVALIDATES.  A name nobody reads still moves both.

The instance that motivated this checker: all thirteen `Verify-Well-Formed/Part*`
imported `budget-sufficient` from `Verify-Budget-Sufficient.Caps-Bridge`, and
exactly ONE of them used it.  Those twelve dead edges stacked the whole 13-level
VWF ladder on top of the whole 25-level budget-sufficient tower — 41 critical-path
levels where 29 were owed, and twelve extra modules rebuilt by every edit in the
budget-sufficient grind lane.  Numbers in typecheck-performance-numbers.md.

WHAT IT WILL NOT DO, and each omission is deliberate: it never reads a bare
`open import M` (no `using` clause imports every name M has, so "unused" is not
decidable from this file), and it never touches an `open import M public` (a
re-export is FOR its consumers, so locally-unused is the normal case).  Both are
silently skipped, and `--stats` counts them so the blind spot has a size.

TWO THINGS PROTECT THE CLAIM GRAPH, and the first one alone was not enough.

THE CLAIM ROOT OF A TREE IS SKIPPED WHOLESALE, AND IT IS THE ONLY EXCEPTION
THERE IS (Anthony).  A claim root exists to NAME definitions, never to apply
them -- "individual definitions only, so that `imported` means `claimed`" -- so
every one of its imports is unused BY DESIGN, and `make wiring` reads exactly
those `using` clauses to seed reachability.  A use-based checker pointed at one
reports the claim graph as dead weight; caught in simulation, deleting what it
reported orphaned 84 of 86 modules.

It is ONE rule and not a list of blessed filenames, which is the part that
matters: the claim root is DERIVED from the include root being scanned, so the
exception cannot grow without adding a whole tree, and no ordinary module can
ever acquire it.  There are two include roots and the law is the same over both
-- the refuted tree's root says of itself that a refutation not listed is not
checked, "exactly as in src/Main.agda".  Every other file in either tree earns
its imports by spending them.

And then, for every file including the claim roots: AN EDGE WHOSE DELETION WOULD
ORPHAN A MODULE IS NOT REPORTED AS DEAD -- it is reported as a WIRING finding and
`--fix` leaves it alone.  Such an edge is the only surviving route to that
module, so removing it does not tidy the graph, it hides a subtree from `make
agda` and trips `wiring-gate` one step later.  Either the module is dead (delete
it on its merits) or a real consumer is missing (wire it).  Both are findings a
human decides, which is why the guard refuses rather than picks.  Its seeds are
`check-wiring.py`'s own MODULE_ROOTS, IMPORTED rather than retyped: a compiled
binary or a probe module is reachable only as a root, so a guard that did not
know about them would happily orphan their subtrees.

The parse is deliberately conservative in ONE direction: every uncertainty
resolves to "used".  A false negative costs a build second; a false positive
deletes a name the proof needs and the tool that did it stops being trusted.
"""
from __future__ import annotations

import argparse
import os
import re
import sys

# Agda identifiers admit nearly all of unicode; what they may NOT contain is
# whitespace and these.  Splitting a file on this set is therefore an
# over-approximation of its tokens, which is the safe direction: a qualified use
# `M.name` yields `name`, so it counts.
SEP = re.compile(r"[\s.;(){}@\"]+")

# THE CLAIM ROOT of each include root -- the one file per tree whose imports ARE
# the claim, so "unused" is its normal state.  Keyed by tree so the exemption is
# derived rather than enumerated; `check-wiring.py` parameterises the same fact as
# ROOT_REL.  CLAUDE.md also forbids touching src/Main.agda without approval.
CLAIM_ROOT = {
    os.path.join("agda", "src"): "Main.agda",
    os.path.join("agda", "evidence", "refuted"): os.path.join("Refuted", "Main.agda"),
    os.path.join("agda", "evidence", "probed"): os.path.join("Probed", "Main.agda"),
}
DEFAULT_CLAIM_ROOT = "Main.agda"

# The trees in play, set once by main() and read by the two functions below --
# the same shape as `check-wiring.py`'s ROOT_REL, and for the same reason: the
# law is a property of the TREE, so a second tree gets it by being a tree and
# not by being added to a list.  It is what lets the selftest fixture own a
# claim root and so exercise a rule the real trees cannot be used to test.
TREES = list(CLAIM_ROOT)


def claim_roots() -> set:
    """The claim roots in play, as MODULE names, e.g. {"Main", "Refuted.Main"}."""
    out = set()
    for t in TREES:
        rel = CLAIM_ROOT.get(t, DEFAULT_CLAIM_ROOT)
        if os.path.isfile(os.path.join(t, rel)):
            out.add(os.path.splitext(rel)[0].replace(os.sep, "."))
    return out


def wiring_module_roots() -> set:
    """`check-wiring.py`'s MODULE_ROOTS, imported so the two cannot drift.

    A compiled binary or a type-level probe is reachable ONLY as a root, so a
    guard seeded from the claim roots alone would cheerfully orphan its subtree.
    """
    import importlib.util
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "check-wiring.py")
    spec = importlib.util.spec_from_file_location("_check_wiring", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return set(mod.MODULE_ROOTS)

DECL = re.compile(r"^([ \t]*)(open[ \t]+import|import)[ \t]+([^\s;(){}]+)", re.M)
CLAUSE = re.compile(r"\A[ \t\n]*(using|hiding|renaming)[ \t\n]*\(")
PUBLIC = re.compile(r"\A[ \t\n]*public\b")


def strip_comments(text: str) -> str:
    """Blank out `--` line comments and `{- -}` blocks, PRESERVING LENGTH.

    Every character is replaced, never removed, so an offset into the stripped
    text is the same offset into the raw text and `--fix` can edit the raw file
    from positions found in the stripped one.  Truncating instead of padding is
    the bug this docstring exists to prevent: the first version of `--fix`
    spliced a using-clause into the middle of the file's opening comment,
    because every line comment above it had shortened the text under it.

    `--` opens a comment when it stands at a token boundary and is followed by
    whitespace, another dash, or end of line.  Anything else is left alone: a
    missed comment makes a name look USED, which is the harmless direction.
    """
    text = re.sub(r"\{-(?!#).*?-\}",
                  lambda m: re.sub(r"[^\n]", " ", m.group(0)), text, flags=re.S)
    out = []
    for line in text.split("\n"):
        m = re.search(r"(?:^|[\s(){}])--(?=[\s\-]|$)", line)
        out.append(line[: m.start()] + " " * (len(line) - m.start()) if m else line)
    return "\n".join(out)


def strip_comments_checked(text: str) -> str:
    out = strip_comments(text)
    assert len(out) == len(text), "strip_comments must preserve length"
    return out


def balanced_end(text: str, i: int) -> int:
    """Index just past the `(` at text[i]'s matching `)`."""
    depth = 0
    while i < len(text):
        if text[i] == "(":
            depth += 1
        elif text[i] == ")":
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    return len(text)


class Decl:
    __slots__ = ("mod", "line", "start", "end", "public", "clauses", "names",
                 "src", "opened")

    def __init__(self, mod, line, start, end, public, clauses, names, src, opened):
        self.mod, self.line, self.start, self.end = mod, line, start, end
        self.public, self.clauses, self.names, self.src = public, clauses, names, src
        # `open import M` brings names into scope unqualified; plain `import M`
        # does not, so only the former can blanket a file.
        self.opened = opened


def split_list(inner: str) -> list[str]:
    """Names in a `using`/`renaming` list.  `x to y` binds the LOCAL name y.

    A MODULE is imported as `module M`, and the name it binds is `M` -- the
    keyword is syntax, not part of the name.  Keeping it produced the one
    false-positive class this checker has had: no token can ever equal
    `module M`, so every such import read as dead, and the use that pays for
    it (`open M ...`, a module application) is not an import declaration and
    so was never even looked at.  It deleted 18 real imports and broke the
    build.
    """
    out = []
    for part in inner.split(";"):
        part = part.strip()
        part = re.sub(r"\Amodule[ \t\n]+", "", part)
        if not part:
            continue
        m = re.match(r"\A(\S+)[ \t\n]+to[ \t\n]+(\S+)\Z", part)
        out.append(m.group(2) if m else part)
    return out


def parse(stripped: str) -> list[Decl]:
    """Every import declaration, with its clause spans.  Multi-line safe."""
    decls = []
    for m in DECL.finditer(stripped):
        mod = m.group(3)
        pos = m.end()
        clauses: dict[str, tuple[int, int]] = {}
        public = False
        while True:
            c = CLAUSE.match(stripped[pos:])
            p = PUBLIC.match(stripped[pos:])
            if c:
                open_at = pos + c.end() - 1
                close = balanced_end(stripped, open_at)
                clauses[c.group(1)] = (open_at, close)
                pos = close
            elif p:
                public = True
                pos += p.end()
            else:
                break
        names = []
        if "using" in clauses:
            a, b = clauses["using"]
            names = split_list(stripped[a + 1: b - 1])
        decls.append(Decl(mod, stripped.count("\n", 0, m.start()) + 1,
                          m.start(), pos, public, clauses, names,
                          stripped[m.start():pos],
                          " ".join(m.group(2).split()).startswith("open")))
    return decls


def atoms(name: str) -> list[str]:
    """The searchable pieces of a name.  `_∷_` is written `x ∷ xs`, so the
    mixfix holes come out and only the parts remain."""
    return [p for p in name.split("_") if p]


def body_tokens(stripped: str, decls) -> set:
    """Every token of a file with its import DECLARATIONS excised.

    Serves two questions that want the same alphabet: what this file spends
    (the use check) and what it could possibly export (the phantom check).
    Excising the declarations is what makes it answer the second -- a name a
    module merely IMPORTS is not a name it exports, `public` being illegal.
    """
    body = stripped
    for d in sorted(decls, key=lambda d: -d.start):
        body = body[: d.start] + body[d.end:]
    tokens = set(SEP.split(body))
    tokens.discard("")
    # AND EVERY TOKEN'S OWN NAME-PARTS, because `_` does not separate tokens.
    # A mixfix operator is spent as a SECTION at least as often as fully
    # applied -- `(x ⊔_) *_`, `(_∷ xs)`, `(x at_from_as_)` -- and a section is
    # ONE token carrying the underscores: `*_`, not `*`.  So an atom-equality
    # test over raw tokens calls `_*_` unused while the file multiplies three
    # times, which is the checker's worst failure mode, a false positive that
    # deletes a live import.  Splitting the tokens the same way the NAMES are
    # split puts both sides in one alphabet.
    return tokens | {q for tok in tokens for q in tok.split("_") if q}


def mentions(name: str, tokens: set) -> bool:
    if name in tokens:
        return True
    parts = atoms(name)
    # ANY part, not all: looser on purpose, so an operator whose pieces are
    # everywhere is never called unused.
    return any(q in tokens for q in parts) if parts else True


def imported_sources(d, stripped: str) -> list[str]:
    """Every name the IMPORTED module must export for this declaration to
    scope-check: the `using` items, plus the LEFT side of every `renaming`
    item.

    `split_list` cannot serve this, and that is the trap: it deliberately
    returns the name an item BINDS -- `y` of `x to y` -- because every other
    question in this file is about local scope, and a use search must look for
    what the file calls the thing.  This one question is the opposite.  Asking
    the module for `y` reports a phantom on the one item that is CORRECT and
    stays silent on the one that is not, so it fires and misses in the same
    breath.  A `using` item has no such side (Agda takes no `to` there), so
    those pass straight through.
    """
    out = list(d.names)
    if "renaming" in d.clauses:
        a, b = d.clauses["renaming"]
        for part in stripped[a + 1: b - 1].split(";"):
            part = re.sub(r"\Amodule[ \t\n]+", "", part.strip())
            if not part:
                continue
            m = re.match(r"\A(\S+)[ \t\n]+to[ \t\n]+(\S+)\Z", part)
            out.append(m.group(1) if m else part)
    return out


MODDECL = re.compile(r"^module[ \t]+([\w.\-]+)", re.M)


def module_decl(stripped: str):
    """The file's own top-level module name, or None if it declares none.

    A file with NO declaration is not a syntax error -- Agda infers the name
    from the path and will happily check the file as a TARGET.  It crashes
    only when something IMPORTS it, and then with

        __IMPOSSIBLE__, called at src/full/Agda/Interaction/Imports.hs

    naming neither the file nor the import.  Worse, the dev loop cannot see
    it: agda-dev checks a GENERATED copy that carries its own header, so the
    missing one is supplied by the generator and the module reports green
    while the gate dies on it.  Three full gate runs were spent on one such
    file, whose header had been deleted along with a duplicated comment block.
    A `grep` decides it in milliseconds, so it is checked here rather than
    discovered there.
    """
    m = MODDECL.search(stripped)
    return m.group(1) if m else None


def module_of(path: str) -> str:
    """`agda/src/A/B.agda` -> `A.B`, relative to whichever tree holds it."""
    p = os.path.normpath(path)
    for base in sorted((os.path.normpath(t) for t in TREES), key=len, reverse=True):
        if p.startswith(base + os.sep):
            p = os.path.relpath(p, base)
            break
    return p[:-5].replace(os.sep, ".") if p.endswith(".agda") else p


def import_graph(files: list[str]) -> dict[str, set[str]]:
    g = {}
    for path in files:
        stripped = strip_comments_checked(open(path, encoding="utf-8").read())
        g[module_of(path)] = {d.mod for d in parse(stripped)}
    return {m: {d for d in ds if d in g} for m, ds in g.items()}


def reachable(graph: dict[str, set[str]], roots) -> set[str]:
    seen, stack = set(), [r for r in roots if r in graph]
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack += list(graph[m])
    return seen


def audit(path: str):
    raw = open(path, encoding="utf-8").read()
    stripped = strip_comments_checked(raw)
    decls = parse(stripped)
    tokens = body_tokens(stripped, decls)

    def used(name: str) -> bool:
        return mentions(name, tokens)

    dead_decls, dead_names, skipped, blanket, reexport = [], [], [], [], []
    declared = module_decl(stripped)
    for d in decls:
        # NO `public` RE-EXPORTS (Anthony).  A re-export makes a name reachable
        # from a module that did not define it, and every consumer downstream
        # then depends on a fact written down nowhere in its own file: `grep`
        # cannot find where the name came from, `make find` reports the wrong
        # home, and this checker's use analysis has to skip the declaration
        # entirely because "locally unused" is the normal case for a re-export.
        # Importing from the DEFINING module instead makes every edge explicit.
        #
        # It does not shorten the build's critical path -- the ladder's
        # dependencies are genuine at the name level, so the depth is real --
        # but it does shrink interface files, and deserialization is this
        # build's floor.  Measured cost of the migration: 3231 names across 91
        # modules become explicit, against 14564 already explicit today.
        if d.public:
            reexport.append(d)
        # THE BLANKET RULE, and it is a policy question rather than a use one:
        # an import with no `using` list takes every name the module has, so what
        # this file depends on is not written down anywhere.  Applies to the claim
        # roots too (Anthony) -- src/Main.agda's own header has demanded it in
        # prose since long before anything checked.
        #
        # `using () renaming (x to y)` is NOT blanket and must never fire: it is
        # the most precise form there is, taking nothing and naming exactly what
        # it renames.  A bare `renaming` with no `using` IS blanket -- it takes
        # everything and respells some of it.
        #
        # A QUALIFIED `import M as Q` is exempt.  It puts nothing in unqualified
        # scope, so it cannot blanket the file, and every use is spelled
        # `Q.name` -- the dependency is written down at every use site rather
        # than once at the top.
        #
        if d.opened and "using" not in d.clauses:
            blanket.append(d)
        if d.public or "using" not in d.clauses or "renaming" in d.clauses:
            skipped.append(d)
            continue
        unused = [n for n in d.names if not used(n)]
        if unused and len(unused) == len(d.names):
            dead_decls.append(d)
        elif unused:
            dead_names.append((d, unused))
    return (raw, stripped, decls, dead_decls, dead_names, skipped, blanket,
            reexport, declared)


def rewrite(raw: str, stripped: str, dead_decls, dead_names) -> str:
    """Apply the fixes, back to front so earlier offsets stay valid.

    Offsets come from the comment-STRIPPED text, which has the same length and
    the same line breaks as the raw text, so they index both.
    """
    edits = []
    for d in dead_decls:
        s = d.start
        while s > 0 and raw[s - 1] in " \t":
            s -= 1
        e = d.end
        while e < len(raw) and raw[e] in " \t":
            e += 1
        if e < len(raw) and raw[e] == "\n":
            e += 1
        edits.append((s, e, ""))
    for d, unused in dead_names:
        a, b = d.clauses["using"]
        keep = []
        for part in stripped[a + 1: b - 1].split(";"):
            nm = part.strip()
            if not nm:
                continue
            # The BOUND name, by the same reading `split_list` gives the
            # report -- `module M` binds `M`, and `x to y` binds `y`.  A
            # rewrite that compares the raw item text instead can never match
            # a `module` item, so the fix silently keeps what the report calls
            # dead: no error, just a checker that never reaches a fixpoint,
            # which is the one failure a --fix run cannot show you.
            item = re.sub(r"\Amodule[ \t\n]+", "", nm)
            local = re.match(r"\A(\S+)[ \t\n]+to[ \t\n]+(\S+)\Z", item)
            if (local.group(2) if local else item) not in unused:
                keep.append(nm)
        indent = " " * (len(re.match(r"[ \t]*", raw[raw.rfind("\n", 0, d.start) + 1:]).group(0)) + 2)
        lines, cur = [], ""
        for nm in keep:
            piece = nm + "; "
            if cur and len(indent) + len(cur) + len(piece) > 96:
                lines.append(cur.rstrip())
                cur = ""
            cur += piece
        if cur:
            lines.append(cur.rstrip().rstrip(";"))
        edits.append((a, b, "(" + ("\n" + indent).join(lines) + ")"))
    for s, e, new in sorted(edits, key=lambda t: -t[0]):
        raw = raw[:s] + new + raw[e:]
    return raw


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--src", action="append", default=None,
                    help="tree to walk (repeatable); default agda/src + agda/evidence/refuted")
    ap.add_argument("--keep-names", action="store_true",
                    help="report only whole DEAD imports, skipping unused names "
                         "inside a surviving `using` clause.  Not what the gate "
                         "runs (Anthony: \"no unused imports, either\") -- for "
                         "isolating a module-edge question from a name one.")
    ap.add_argument("--fix", action="store_true",
                    help="delete in place whatever this run reports")
    ap.add_argument("--stats", action="store_true",
                    help="also report how many declarations were skipped, and why")
    args = ap.parse_args()

    roots = args.src or list(CLAIM_ROOT)
    TREES[:] = list(dict.fromkeys(
        list(CLAIM_ROOT) + [os.path.normpath(r) for r in roots if os.path.isdir(r)]))
    files = []
    for r in roots:
        if os.path.isfile(r):
            files.append(r)
            continue
        for dp, _, fn in os.walk(r):
            files += [os.path.join(dp, f) for f in sorted(fn) if f.endswith(".agda")]
    files.sort()

    # THE ORPHAN GUARD, and it asks the question `--fix` actually poses.
    #
    # An earlier cut tested each edge ALONE -- "would deleting this one orphan
    # anything?" -- which is a different and weaker question than the fixer asks,
    # because the fixer deletes the whole set at once.  Two dead edges into the
    # same module are each individually redundant (the other still reaches it)
    # and jointly its only routes, so a per-edge guard waves both through and the
    # module vanishes.  So the set is trimmed JOINTLY and grown back to a
    # fixpoint: whatever is still needed to keep every module reachable is held
    # back as a WIRING finding.  Terminates because `held` only grows, and in the
    # worst case holding everything restores the original graph exactly.
    graph = import_graph(files)
    seeds = claim_roots() | wiring_module_roots()
    live = reachable(graph, seeds)

    candidates = {}          # module -> {dead destination, ...}
    per_file = {}
    for path in files:
        if module_of(path) in claim_roots():
            per_file[path] = ("skip", audit(path))
            continue
        res = audit(path)
        per_file[path] = ("audit", res)
        if res[3]:
            candidates[module_of(path)] = {d.mod for d in res[3]}

    # WHAT EVERY MODULE IN THE TREE COULD POSSIBLY EXPORT -- its own tokens,
    # its import declarations excised.  A necessary condition, not a sufficient
    # one: it cannot tell a definition from a mention, so it under-reports and
    # never invents.  That is the point -- the finding it does make is certain.
    exports = {module_of(path): body_tokens(res[1], res[2])
               for path, (_, res) in per_file.items()}

    held_edges = set()
    while True:
        trimmed = {m: (ds - (candidates.get(m, set()) - {d for (sm, d) in held_edges if sm == m}))
                   for m, ds in graph.items()}
        lost = live - reachable(trimmed, seeds)
        if not lost:
            break
        newly = {(m, d) for m, ds in candidates.items() for d in ds
                 if d in lost and (m, d) not in held_edges}
        if not newly:
            break
        held_edges |= newly

    # What the fix WOULD have cost, computed once with every candidate removed.
    # Reporting must not re-ask the per-edge question -- that is the very test the
    # joint fixpoint replaced, and asking it again here silently undoes it: each
    # of a pair of sole-route edges looks individually redundant against the other
    # and both get waved through.  So a held edge simply reports the at-risk
    # modules it helps hold.
    bare = {m: (ds - candidates.get(m, set())) for m, ds in graph.items()}
    at_risk = live - reachable(bare, seeds)

    def orphans(src: str, dst: str) -> set:
        if (src, dst) not in held_edges:
            return set()
        return at_risk & (reachable(graph, [dst]) | {dst})

    n_decl = n_dead = n_name = n_skip = n_file = n_wire = n_blanket = n_reex = 0
    n_mod = n_phantom = 0
    wiring, blankets, reexports, misnamed, phantoms = [], [], [], [], []
    for path in files:
        kind, res = per_file[path]
        (raw, stripped, decls, dead_decls, dead_names, skipped, blanket,
         reexport, declared) = res
        # THE FILE'S OWN NAME, checked before anything about its imports: a
        # missing or mismatched header is what makes every IMPORT of this file
        # crash, so it outranks every finding below.  Claim roots included --
        # nothing about being a claim exempts a file from being named.
        want = module_of(path)
        if declared != want:
            misnamed.append((path, declared, want))
        # A NAME THE SOURCE MODULE HAS NOWHERE IN IT, checked for every
        # declaration and every file -- a claim root's imports are claims
        # rather than uses, but a claim on a name that does not exist is the
        # same crash as anyone else's.  Only INTRA-TREE modules can be asked:
        # a stdlib module is not a file here, and stdlib re-exports freely.
        for d in decls:
            if d.mod not in exports or not ("using" in d.clauses
                                            or "renaming" in d.clauses):
                continue
            for nm in imported_sources(d, stripped):
                if not mentions(nm, exports[d.mod]):
                    phantoms.append((path, d, nm))
        # Collected before the claim-root skip on purpose: the blanket rule binds
        # every file in the tree, roots included.
        blankets += [(path, d) for d in blanket]
        reexports += [(path, d) for d in reexport]
        if kind == "skip":
            n_skip += len(decls)
            n_decl += len(decls)
            continue
        held = []
        for d in dead_decls:
            lost = orphans(module_of(path), d.mod)
            if lost:
                wiring.append((path, d, sorted(lost)))
            else:
                held.append(d)
        dead_decls = held
        if args.keep_names:
            dead_names = []
        n_decl += len(decls)
        n_skip += len(skipped)
        if not dead_decls and not dead_names:
            continue
        n_file += 1
        for d in dead_decls:
            n_dead += 1
            print(f"{path}:{d.line}: DEAD IMPORT  {d.mod}  "
                  f"(none of its {len(d.names)} name(s) used: {'; '.join(d.names[:6])}"
                  f"{' …' if len(d.names) > 6 else ''})")
        for d, unused in dead_names:
            n_name += len(unused)
            print(f"{path}:{d.line}: dead name(s) from {d.mod}: {'; '.join(unused)}")
        if args.fix:
            open(path, "w", encoding="utf-8").write(
                rewrite(raw, stripped, dead_decls, dead_names))

    for path, declared, want in misnamed:
        n_mod += 1
        if declared is None:
            print(f"{path}:1: NO MODULE DECLARATION — expected "
                  f"`module {want} where`.  Agda infers the name from the path "
                  f"and checks this file happily as a TARGET; it crashes with "
                  f"`__IMPOSSIBLE__ ... Imports.hs` the moment anything IMPORTS "
                  f"it, naming neither this file nor the import.  agda-dev "
                  f"cannot see it either — it checks a generated copy carrying "
                  f"its own header.")
        else:
            print(f"{path}:1: MODULE NAME MISMATCH — declares `{declared}`, "
                  f"but its path says `{want}`.")

    for path, d, nm in phantoms:
        n_phantom += 1
        print(f"{path}:{d.line}: PHANTOM NAME  {nm}  — {d.mod} does not "
              f"mention `{nm}` anywhere, so it cannot be exporting it.  Import "
              f"it from where it is defined, or delete it.")

    for path, d in reexports:
        n_reex += 1
        print(f"{path}:{d.line}: RE-EXPORT  {d.mod}  — `public` makes these names "
              f"reachable from a module that did not define them, so every "
              f"consumer downstream depends on a fact written down nowhere in its "
              f"own file.  Import from the defining module instead.")

    for path, d in blankets:
        n_blanket += 1
        why = "re-exports" if d.public else "takes"
        print(f"{path}:{d.line}: BLANKET IMPORT  {d.mod}  — an import with no "
              f"`using` list {why} every name the module has, so what this file "
              f"depends on is written down nowhere.  Name them.")

    for path, d, lost in wiring:
        n_wire += 1
        print(f"{path}:{d.line}: WIRING — {d.mod} is imported and unused here, but "
              f"deleting every unused import would leave nothing reaching "
              f"{', '.join(lost)}.  Held back, not deleted: either that module is "
              f"dead (delete it on its merits) or a real consumer is missing "
              f"(wire it).")

    if args.stats:
        print(f"\nscanned {len(files)} files, {n_decl} import declarations, "
              f"{n_blanket} blanket, "
              f"{n_skip} skipped for the USE check (public re-export, "
              f"or no `using` clause, "
              f"or a `renaming` that leaves the rest imported, or a claim root: "
          f"{', '.join(sorted(claim_roots()))})")
    verb = "fixed" if args.fix else "found"
    tail = "" if args.keep_names else f" and {n_name} dead name(s)"
    print(f"imports-check: {verb} {n_dead} dead import(s){tail} "
          f"across {n_file} file(s)")
    if n_mod:
        print(f"imports-check: and {n_mod} file(s) whose module DECLARATION is "
              f"missing or does not match the path — every import of one of "
              f"those crashes Agda")
    if n_phantom:
        print(f"imports-check: and {n_phantom} PHANTOM name(s) — imported from a "
              f"module of this tree that does not contain the name at all.  Agda "
              f"reports it as a ModuleDoesntExport WARNING, which `-W error` "
              f"turns into exit 42 many minutes down the tower, in a module that "
              f"is itself correct.  Not auto-fixable: the repair is the right "
              f"module, and only a human knows which that is")
    if n_blanket:
        print(f"imports-check: and {n_blanket} BLANKET import(s) — an import with "
              f"no `using` list.  Not auto-fixable: naming them needs the module's "
              f"export list, which only Agda has")
    if n_reex:
        print(f"imports-check: and {n_reex} `public` re-export(s) — illegal: a name "
              f"must be imported from where it is defined")
    if n_wire:
        print(f"imports-check: and {n_wire} unused import(s) HELD BACK by the "
              f"orphan guard — those are wiring findings, not dead weight")
    if (n_dead or n_name) and not args.fix:
        print("imports-check: run `make imports-fix` to delete them")
    if args.fix:
        return 1 if (n_wire or n_blanket or n_reex or n_mod or n_phantom) else 0
    return 1 if (n_dead or n_name or n_wire or n_blanket or n_reex
                 or n_mod or n_phantom) else 0


if __name__ == "__main__":
    sys.exit(main())
