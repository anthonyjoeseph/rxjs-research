#!/usr/bin/env python3
"""The postulates a definition rests on: `make cone NAME=<name>`.

Walks the reference graph DOWN from one definition and prints every
postulate it reaches, each with one chain of names from the root to it,
so "what does this proof still owe?" is one command.  `make postulates`
is the whole ledger; this is the slice of it under one name.

Nodes are (name, file), not bare names: `scripts/check-wiring.py` merges
every `bounded` in the tree into one node, which is right for "is this
name used anywhere" and useless for "what does this name use".  An
occurrence of `n` in file F resolves only to a definition of `n` that F
can see: one in F itself, or in a module F imports whose `using` list
names `n` (or that F imports without a list, or reaches qualified, as
`M.n`).

Still textual, so it OVER-approximates, never under: two definitions of
one name in one file are one candidate pair, record fields resolve to
every same-named definition in scope, and a name in a comment-free
string of code counts wherever it appears in the owner's body.  An entry
here is a lead to check; an ABSENT postulate is not reached.
"""
import argparse
import importlib.util
import os
import re
import sys
from bisect import bisect_right
from collections import defaultdict, deque

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("cw", os.path.join(HERE, "check-wiring.py"))
cw = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(cw)

_IMPORT_RE = re.compile(r"^\s*(open\s+)?import\s+([^\s(]+)(.*)$", re.S)


def imports_of(visible):
    """-> list of (module, names or None).  None: no `using` list, every
    name of the module is in reach (blanket, or qualified access)."""
    out = []
    spans = sorted(cw.import_span_lines(visible))
    groups, cur = [], []
    for ln in spans:
        if cur and ln != cur[-1] + 1:
            groups.append(cur)
            cur = []
        cur.append(ln)
    if cur:
        groups.append(cur)
    for g in groups:
        # one span may hold one statement; split on statement heads
        text = "".join(visible[i - 1] for i in g)
        for stmt in re.split(r"\n(?=\S)", text):
            m = _IMPORT_RE.match(stmt)
            if not m:
                continue
            opened, mod, rest = m.group(1), m.group(2), m.group(3)
            um = re.search(r"\busing\s*\((.*?)\)", rest, re.S)
            if not opened or not um:
                out.append((mod, None))
                continue
            names = set()
            for item in um.group(1).split(";"):
                item = item.strip()
                if item.startswith("module "):
                    # an `open` of the module reaches every name it holds
                    names = None
                    break
                if item:
                    names.add(item)
            out.append((mod, names))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("name", help="the definition to walk down from")
    ap.add_argument("--file", default=None, help="the file defining it, when the name has several (relative to agda-impl)")
    ap.add_argument("--paths", action="store_true", help="print the chain of names to each postulate")
    args = ap.parse_args()

    src = os.path.abspath(os.path.join(HERE, "..", "agda-impl"))
    files = cw.find_agda_files(src)
    defs, def_lines, pnames, order, psites = cw.extract_definitions(src, files)
    corpus = cw.build_corpus(src, files)
    by_file = cw.owner_index(def_lines)
    mod_file = {rel[:-5].replace(os.sep, "."): rel for rel in files}

    # name -> files defining it
    def_files = defaultdict(set)
    for n, sites in def_lines.items():
        for (f, _ln) in sites:
            def_files[n].add(f)

    # file -> {visible file -> names or None}
    reach = {}
    for rel in files:
        _raw, visible = cw.load_file(src, rel)
        r = {rel: None}
        for mod, names in imports_of(visible):
            g = mod_file.get(mod)
            if g is None:
                continue
            if g in r and r[g] is None:
                continue
            if names is None or r.get(g, set()) is None:
                r[g] = None
            else:
                r[g] = (r.get(g) or set()) | names
        reach[rel] = r

    def is_postulate(n, f):
        return n in pnames and psites[n][0] == f

    # edges: (owner, file) -> {(name, deffile)}
    edges = defaultdict(set)
    for n in order:
        terms = [n]
        core = cw.mixfix_core_of(n)
        if core:
            terms.append(core)
        own = def_lines.get(n, ())
        homes = def_files.get(n, set())
        for rel in files:
            text, offsets, import_lines, _ = corpus[rel]
            if not text:
                continue
            vis = reach[rel]
            targets = [g for g in homes if g in vis]
            if not targets:
                continue
            for term in terms:
                idx = text.find(term)
                while idx != -1:
                    end = idx + len(term)
                    before = text[idx - 1] if idx > 0 else None
                    after = text[end] if end < len(text) else None
                    if cw.is_boundary(before) and cw.is_boundary(after):
                        ln = bisect_right(offsets, idx)
                        if (rel, ln) not in own and ln not in import_lines:
                            o = cw.owner_of(by_file, rel, ln)
                            if o is not None and o != n:
                                qualified = before == "."
                                for g in targets:
                                    names = vis[g]
                                    if g == rel or names is None or qualified or n in names:
                                        edges[(o, rel)].add((n, g))
                    idx = text.find(term, idx + 1)

    # A `with` continuation (`... | pat = body`) is registered per site as its
    # own node, so it continues the clause above it: hang it under the
    # nearest owner above it that is not itself a continuation.
    for (o, rel) in list(edges):
        if not o.startswith("...#"):
            continue
        ln = int(o.rsplit(":", 1)[1]) - 1
        p = cw.owner_of(by_file, rel, ln)
        while p is not None and p.startswith("...#"):
            ln = int(p.rsplit(":", 1)[1]) - 1
            p = cw.owner_of(by_file, rel, ln)
        if p is not None:
            edges[(p, rel)].add((o, rel))

    roots = [(args.name, f) for f in sorted(def_files.get(args.name, ()))
             if args.file is None or f == args.file]
    if not roots:
        print(f"cone: no definition named {args.name!r}" + (f" in {args.file}" if args.file else ""), file=sys.stderr)
        sys.exit(2)
    if len(roots) > 1:
        print("cone: " + args.name + " is defined in " + ", ".join(f for _, f in roots)
              + "; walking from all (pass --file to pick one)", file=sys.stderr)

    parent = {r: None for r in roots}
    q = deque(roots)
    while q:
        node = q.popleft()
        if is_postulate(*node):
            continue  # a postulate is a leaf: its type's names are not owed
        for nxt in sorted(edges.get(node, ())):
            if nxt not in parent:
                parent[nxt] = node
                q.append(nxt)

    found = sorted((n, f) for (n, f) in parent if is_postulate(n, f))
    for (n, f) in found:
        line = f"{n}  {f}:{psites[n][1]}"
        if args.paths:
            chain, cur = [], (n, f)
            while cur is not None:
                chain.append(cur[0])
                cur = parent[cur]
            line += "    via " + " ← ".join(chain)
        print(line)
    print(f"-- {len(found)} postulate(s) under {args.name}")


if __name__ == "__main__":
    main()
