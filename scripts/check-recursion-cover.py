#!/usr/bin/env python3
"""Every cycle in the evaluator's recursion is covered by a DECLARED descent.

WHAT THIS DEFENDS.  The evaluator terminates because a counter is peeled at a
few named edges and every other re-entry stays inside one nesting level,
descending on an argument it already has.  That reading is what the
stratification rests on: an order with one constructor per peel edge covers
the whole recursion exactly when no OTHER cycle survives the peels.  Nothing
checked it.  A clause added to the burst walk, a new operator routing back
through `subscribeE`, a share hop that re-enters a frame -- each would open a
cycle the order does not name, and the tower would go on compiling, because
Agda's own termination checker is happy with the counter and says nothing
about which edges carry it.

WHAT IT DOES.  It reads the evaluator's call graph, cuts the edges the source
DECLARES as peels, and requires every multi-member cycle left standing to be
one the source DECLARES as structural.  Both directions are held: a declared
peel naming an edge that no longer exists is a finding, and so is a declared
structural cycle that is no longer a cycle -- either means the declaration has
aged past the code, which is the failure that makes a comment worse than
nothing.

THE DECLARATIONS LIVE IN THE SOURCE, one per line, anywhere in the file:

    -- PEEL: <caller> -> <callee>
    -- STRUCTURAL SCC: <name> <name> ...

A PEEL says the callee is entered at a strictly smaller counter, so the edge
cannot carry a cycle.  A STRUCTURAL SCC says the members descend on an
argument of their own, and it is the one thing here taken on the source's word
-- so it says so out loud rather than by being unlisted, and the check fails
the moment it stops naming a real cycle.

THE CALL GRAPH IS OVER-APPROXIMATED, deliberately.  A name occurring anywhere
in a body counts as a call, `where` blocks and type annotations included.  The
error is one-sided: a spurious edge can only invent a cycle, so the check is
conservative in the direction that matters and cannot pass a recursion it has
not seen.
"""
import argparse
import re
import sys

WORD = r"[A-Za-z][A-Za-z0-9'´ᵃ-ᵪ₀-₟′-]*"
SIG = re.compile(r"^(" + WORD + r")\s*:\s")
HEAD = re.compile(r"^(" + WORD + r")\s")
TOK = re.compile(WORD)
PEEL = re.compile(r"--\s*PEEL:\s*(" + WORD + r")\s*->\s*(" + WORD + r")\s*$")
SCC = re.compile(r"--\s*STRUCTURAL SCC:\s*(.+?)\s*$")


def strip_block_comments(lines):
    out, depth = [], 0
    for ln in lines:
        buf, i = [], 0
        while i < len(ln):
            if depth == 0 and ln.startswith("{-", i):
                depth += 1
                i += 2
            elif depth > 0 and ln.startswith("-}", i):
                depth -= 1
                i += 2
            elif depth > 0:
                i += 1
            else:
                buf.append(ln[i])
                i += 1
        out.append("".join(buf))
    return out


def parse(path):
    raw = open(path, encoding="utf-8").read().split("\n")
    peels, sccs = set(), []
    for ln in raw:
        m = PEEL.search(ln)
        if m:
            peels.add((m.group(1), m.group(2)))
            continue
        m = SCC.search(ln)
        if m:
            sccs.append(frozenset(m.group(1).split()))

    lines = strip_block_comments(raw)
    names = {m.group(1) for ln in lines if (m := SIG.match(ln))}

    edges = {}
    cur = None
    for ln in lines:
        m = HEAD.match(ln)
        if m and m.group(1) in names:
            cur = None if re.match(r"^\s*:\s", ln[m.end(1):]) else m.group(1)
        elif ln and not ln[0].isspace() and not ln.startswith("--") \
                and not ln.startswith("...") and not ln.startswith("|"):
            cur = None
        if cur is None:
            continue
        code = ln.split("--")[0]
        for t in TOK.finditer(code):
            if t.group(0) in names:
                edges.setdefault(cur, set()).add(t.group(0))
    return names, edges, peels, sccs


def multi_sccs(edges, nodes):
    """Tarjan, iterative.  Returns the components with more than one member."""
    index, low, onstack, stack, out = {}, {}, set(), [], []
    counter = [0]
    for root in sorted(nodes):
        if root in index:
            continue
        work = [(root, iter(sorted(edges.get(root, ()))))]
        index[root] = low[root] = counter[0]
        counter[0] += 1
        stack.append(root)
        onstack.add(root)
        while work:
            u, it = work[-1]
            descended = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = counter[0]
                    counter[0] += 1
                    stack.append(w)
                    onstack.add(w)
                    work.append((w, iter(sorted(edges.get(w, ())))))
                    descended = True
                    break
                if w in onstack:
                    low[u] = min(low[u], index[w])
            if descended:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[u])
            if low[u] == index[u]:
                comp = []
                while True:
                    x = stack.pop()
                    onstack.discard(x)
                    comp.append(x)
                    if x == u:
                        break
                if len(comp) > 1:
                    out.append(frozenset(comp))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", default="agda/src/Rx/Evaluator.agda")
    args = ap.parse_args()

    names, edges, peels, declared = parse(args.file)
    findings = []

    for caller, callee in sorted(peels):
        if callee not in edges.get(caller, ()):
            findings.append(
                f"declared PEEL {caller} -> {callee} is not a call in {args.file}")

    cut = {a: {b for b in bs if (a, b) not in peels} for a, bs in edges.items()}
    surviving = multi_sccs(cut, names)

    for comp in surviving:
        if comp not in declared:
            findings.append(
                "cycle covered by no declared descent: "
                + " ".join(sorted(comp)))
    for comp in declared:
        if comp not in surviving:
            findings.append(
                "declared STRUCTURAL SCC is no longer a cycle: "
                + " ".join(sorted(comp)))

    if findings:
        print("recursion-cover: " + str(len(findings)) + " finding(s):")
        for f in findings:
            print("  " + f)
        print()
        print("Every cycle the peels do not cut has to descend on an argument")
        print("the members already carry, and say so.  A cycle named by")
        print("neither is a re-entry the stratification's order does not")
        print("cover -- and a declaration naming nothing has aged past the")
        print("code, which is what makes it worse than no declaration.")
        return 1

    print(f"recursion-cover: {args.file} — {len(names)} declaration(s), "
          f"{len(peels)} declared peel(s) cut, "
          f"{len(declared)} structural cycle(s) left standing and named, "
          f"no cycle uncovered")
    return 0


if __name__ == "__main__":
    sys.exit(main())
