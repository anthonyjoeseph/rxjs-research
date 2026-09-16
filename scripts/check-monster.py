#!/usr/bin/env python3
"""THE MONSTER: EVERY TIER NAMES THE ONE THING IT IS TRYING TO KILL.

A tier's rows are its ledger and its legs are its schedule.  The MONSTER is
what the schedule is FOR: the single declaration the session currently judges
most likely to be FALSE, chosen for BLAST RADIUS rather than for being a leaf
-- if it falls, its siblings and its parents go with it.

It is a NAME rather than prose, because a name is the part a machine can hold:
a tier's risk stated in a paragraph is read by whoever happens to read it, and
a tier's risk stated as a declaration is read by the gate on every commit.

WHAT IS HELD, and it is deliberately not a prose requirement: every line ADDED
to `agda/src` must belong to a declaration inside the lowest open tier's
monster's own DEPENDENCY CONE.  Not its blast radius -- its cone: the things
the monster's statement and body reach, which is exactly the set whose truth
decides the monster's.

THE CONE IS COMPUTED ON THE POST-EDIT TREE, WHICH IS WHAT MAKES THE RULE
SATISFIABLE.  A monster that is a postulate has a cone of vocabulary only, so
read against the OLD tree this check would forbid the one move that kills a
postulate -- converting it into a real body over smaller leaves.  Read against
the tree as it now stands, that body names the new leaves, so they are in the
cone and the commit passes.  The same reading is what lets a new lemma land:
add it AND wire it into the monster in one commit, which is the wiring law's
own workflow, and nothing further is owed.

AND IT MAY NEVER BE THE TIER'S OWN SUBJECT.  A tier is dedicated to a single
definition, named in its heading, so naming that definition the monster makes
the cone the whole tier and the check stops deciding anything.  The monster is
the deepest thing UNDER the subject that could genuinely be false; a sibling
whose cone the choice excludes is admitted by an `also:` line, which says out
loud what a monster at the top would admit silently.

AND THE MONSTER NEED NOT BE A POSTULATE.  The riskiest object in a tier is
routinely a DEFINITION -- a relation every leaf is stated in, an evaluator
clause every claim reads through -- and such a thing can be wrong in a way no
postulate ledger records.  A postulate monster is the special case.

THE ESCAPE HATCH IS IN THE FILE OF RECORD, NEVER IN THE ENVIRONMENT.  A tier's
monster section may carry an `also:` line naming further roots whose cones are
admitted, which is how a deliberately off-monster leg -- a rehearsal claim, a
tooling face, apparatus a whole tier is unreachable without -- is declared.
Written there it is reviewed with the roadmap; passed as a flag it would be
invisible the moment it was used.

Deletions are never held, and neither is a comment: what is charged is code
ARRIVING, since that is the only thing that can be off-monster work.
"""

import argparse
import importlib.util
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load_wiring():
    spec = importlib.util.spec_from_file_location(
        "check_wiring", os.path.join(HERE, "check-wiring.py"))
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


TIER_RE = re.compile(r"^##\s+Tier\s+(\d+)\b")
MONSTER_HEAD_RE = re.compile(r"^###\s+The monster\b", re.I)
NAME_RE = re.compile(r"`([^`]+)`")


NO_MONSTER_RE = re.compile(r"\(no monster\)", re.I)


def parse_monsters(path):
    """tier number -> (monster, [also…], line, subject).  One backticked name
    in the section's first non-blank prose line; `also:` lines add admitted
    roots.  The SUBJECT is the backticked name in the tier's own heading, or
    None where the tier names no single definition.

    A MONSTER IS NULL WHERE THE TIER WRITES `(no monster)`, and the monster is
    then None rather than absent.  A tier whose work is REFACTORING has no
    statement that could be false: the type it threads either checks or does
    not, and the cone of a thing that cannot be wrong decides nothing while
    still forbidding the threading, which touches every module by design.  The
    opt-out is written in the section rather than passed as a flag for the same
    reason an `also:` line is — it is reviewed with the roadmap."""
    out = {}
    subjects = {}
    tier = None
    in_section = False
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            m = TIER_RE.match(line)
            if m:
                tier, in_section = int(m.group(1)), False
                head = NAME_RE.findall(line)
                subjects[tier] = head[0] if head else None
                continue
            if line.startswith("###"):
                in_section = bool(MONSTER_HEAD_RE.match(line))
                continue
            if not in_section or tier is None or not line.strip():
                continue
            names = NAME_RE.findall(line)
            if line.strip().lower().startswith("also:"):
                if tier in out:
                    out[tier][1].extend(names)
                continue
            if tier not in out and NO_MONSTER_RE.search(line):
                out[tier] = (None, [], lineno)
                continue
            if tier not in out and names:
                out[tier] = (names[0], [], lineno)
    return {t: (mon, also, ln, subjects.get(t))
            for t, (mon, also, ln) in out.items()}


def enclosing_index(defs, def_lines):
    """anon/module-app node -> the named declaration it continues."""
    starts = {}
    for name, sites in def_lines.items():
        for relpath, ln in sites:
            cur = starts.get(name)
            if cur is None or ln < cur[1]:
                starts[name] = (relpath, ln)
    named, anon = {}, {}
    for name, (relpath, ln) in starts.items():
        (anon if defs[name].kind in ("anon", "module-app") else named) \
            .setdefault(relpath, []).append((ln, name))
    for rows in named.values():
        rows.sort()
    out = {}
    for relpath, rows in anon.items():
        pool = named.get(relpath, [])
        for ln, name in rows:
            best = None
            for start, cand in pool:
                if start < ln:
                    best = cand
                else:
                    break
            if best is not None:
                out[name] = best
    return out


PROSE_BUDGET = 700


def section_cost(path, tier_lineno):
    """the monster section's prose, `also:` lines free — they are a LEDGER of
    admitted exceptions, and charging a ledger buys exceptions left undeclared
    rather than exceptions not taken."""
    total, started = 0, False
    with open(path, encoding="utf-8") as fh:
        for lineno, line in enumerate(fh, 1):
            if lineno < tier_lineno:
                continue
            if line.startswith("###") or line.startswith("##"):
                if started:
                    break
                continue
            started = True
            if line.strip().lower().startswith("also:"):
                continue
            total += len(line.strip())
    return total


def selftest():
    import tempfile
    fails = []

    def check(cond, what):
        if not cond:
            fails.append(what)

    doc = """## Tier 1 — a
### The monster
`alpha` — because it would take the tier with it.
also: `beta` — declared exception.
### The ledger
- **`x`** — FALSITY
## Tier 2 — b
### The monster
`gamma` — the other one.
"""
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(doc)
        tmp = fh.name
    got = parse_monsters(tmp)
    check(got.get(1, (None,))[0] == "alpha", "tier 1's monster is read")
    check(got.get(1, (None, []))[1] == ["beta"], "an `also:` line is collected")
    check(got.get(2, (None,))[0] == "gamma", "a second tier carries its own")
    check(min(got) == 1, "the LOWEST tier is the one that binds")
    check(section_cost(tmp, 2) > 0, "the section's prose is charged")
    check(section_cost(tmp, 2) < PROSE_BUDGET, "an `also:` line is not charged")
    check(got.get(1, (None, [], 0, None))[3] is None,
          "a tier heading naming no definition has no subject")

    # THE SUBJECT RULE.  A tier dedicated to one definition may not name that
    # definition as its monster -- the cone would be the whole tier.
    doc2 = """## Tier 1 — `alpha`
### The monster
`alpha` — the tier's own subject.
## Tier 2 — `delta`
### The monster
`epsilon` — below the subject, which is what is wanted.
"""
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(doc2)
        tmp2 = fh.name
    g2 = parse_monsters(tmp2)
    check(g2[1][3] == "alpha" and g2[1][0] == "alpha",
          "a monster equal to its tier's subject is visible to the check")
    check(g2[2][3] == "delta" and g2[2][0] == "epsilon",
          "and a monster BELOW its tier's subject reads as distinct")
    os.unlink(tmp2)

    # THE OPT-OUT.  A refactoring tier declares none, and it must turn the
    # check OFF rather than fall through to the tier below -- which would hold
    # the threading to a cone drawn for work nobody is doing.
    doc3 = """## Tier 1 — a
### The monster
(no monster) — a refactoring tier.
## Tier 2 — b
### The monster
`gamma` — a real one, one tier down.
"""
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(doc3)
        tmp3 = fh.name
    g3 = parse_monsters(tmp3)
    check(1 in g3 and g3[1][0] is None,
          "`(no monster)` reads as a tier PRESENT with a null monster")
    check(min(g3) == 1,
          "and it still binds at the lowest tier, so the check goes quiet "
          "rather than falling through to tier 2's cone")
    check(g3.get(2, (None,))[0] == "gamma",
          "while a lower tier's real monster is still parsed")
    os.unlink(tmp3)

    # AND THE OPT-OUT IS NOT A BACKTICK-FREE LINE.  A monster section whose
    # prose simply names nothing is a tier that FORGOT, and it must not read
    # as having opted out.
    doc4 = """## Tier 1 — a
### The monster
the thing we are trying to kill, written without backticks.
"""
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as fh:
        fh.write(doc4)
        tmp4 = fh.name
    check(1 not in parse_monsters(tmp4),
          "a monster section naming nothing is NOT an opt-out")
    os.unlink(tmp4)

    # the splice: an anonymous `with` continuation must not break the cone.
    class D:
        def __init__(self, kind, file):
            self.kind, self.file = kind, file
    defs = {"asm": D("def", "A.agda"), "...#A:9": D("anon", "A.agda"),
            "leaf": D("postulate", "B.agda")}
    dl = {"asm": {("A.agda", 5)}, "...#A:9": {("A.agda", 9)},
          "leaf": {("B.agda", 3)}}
    enc = enclosing_index(defs, dl)
    check(enc.get("...#A:9") == "asm",
          "an anonymous continuation is spliced into what it continues")
    edges = {"...#A:9": {"leaf"}}
    check("leaf" not in reach({"asm"}, edges),
          "and without the splice the leaf is OFF the cone")
    edges.setdefault("asm", set()).update(edges["...#A:9"])
    check("leaf" in reach({"asm"}, edges),
          "and with it the leaf is inside")

    os.unlink(tmp)
    if fails:
        for f in fails:
            print(f"monster-selftest: FAILED — {f}")
        sys.exit(1)
    print("monster-selftest: PASS (the lowest tier's monster is the one that "
          "binds, a monster may not be its tier's own subject, a `(no "
          "monster)` tier turns the check OFF rather than falling through to "
          "the cone below it while a section that merely names nothing is a "
          "tier that forgot, an `also:` "
          "exception is collected and is not charged against "
          "the section's prose budget, and an anonymous `with` continuation is "
          "spliced into the declaration it continues -- without which an "
          "assembly applying its leaves in a `with` arm reaches none of them, "
          "which is the shape that made the first run of this check report "
          "nine offenders that were all its own body)")


def reach(seed, edges):
    R, stack = set(seed), list(seed)
    while stack:
        n = stack.pop()
        for m in edges.get(n, ()):
            if m not in R:
                R.add(m)
                stack.append(m)
    return R


def merge_base():
    for ref in ("origin/main", "main"):
        p = subprocess.run(["git", "merge-base", ref, "HEAD"],
                           capture_output=True, text=True)
        if p.returncode == 0 and p.stdout.strip():
            return p.stdout.strip()
    return None


def added_lines(base, src_rel):
    """(relpath-within-src, new lineno) for every ADDED line under agda/src."""
    p = subprocess.run(
        ["git", "diff", "-U0", base, "--", src_rel],
        capture_output=True, text=True)
    if p.returncode != 0:
        return None
    hits, cur, n = [], None, 0
    for line in p.stdout.splitlines():
        if line.startswith("+++ b/"):
            path = line[6:]
            cur = os.path.relpath(path, src_rel) if path.startswith(src_rel) else None
            continue
        m = re.match(r"^@@ -\S+ \+(\d+)(?:,(\d+))? @@", line)
        if m:
            n = int(m.group(1))
            continue
        if line.startswith("+") and not line.startswith("+++"):
            if cur:
                hits.append((cur, n))
            n += 1
        elif line.startswith(" "):
            n += 1
    return hits


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--roadmap", default=os.path.join(HERE, "..", "PROOF-STATE.md"))
    ap.add_argument("--src", default=os.path.join(HERE, "..", "agda", "src"))
    ap.add_argument("--selftest", action="store_true",
                    help="check that this check still fires, and exit")
    ap.add_argument("--gate", action="store_true",
                    help="exit 1 on a finding; without it this is a report")
    args = ap.parse_args()
    if args.selftest:
        selftest()
        return

    roadmap = os.path.abspath(args.roadmap)
    src_dir = os.path.abspath(args.src)
    repo = os.path.abspath(os.path.join(HERE, ".."))
    src_rel = os.path.relpath(src_dir, repo)

    monsters = parse_monsters(roadmap)
    if not monsters:
        print("check-monster: no tier names a monster — every tier owes a "
              "`### The monster` section naming one declaration in backticks.")
        sys.exit(1 if args.gate else 0)

    tier = min(monsters)
    monster, also, lineno, subject = monsters[tier]

    # THE OPT-OUT BINDS AT THE LOWEST TIER AND NOWHERE ELSE.  Falling through
    # to the next tier's monster would be worse than holding nothing: it would
    # hold this tier's work to a cone drawn for work nobody is doing.
    if monster is None:
        print(f"check-monster: tier {tier} declares `(no monster)` — it is a "
              f"refactoring tier, with no statement under it that could be "
              f"false, so no cone is held and every line added to agda/src is "
              f"admitted.")
        return

    roots = [monster] + also

    if subject is not None and monster == subject:
        print(f"check-monster: {os.path.basename(roadmap)}:{lineno}: tier "
              f"{tier} is dedicated to `{subject}` and names it as its own "
              f"monster. A MONSTER MAY NEVER BE ITS TIER'S OWN SUBJECT: the "
              f"subject's cone is the whole tier, so every line added "
              f"anywhere in the tier is inside it by construction and the "
              f"check stops deciding anything. Take the DEEPEST thing under "
              f"it that could genuinely be false and that still takes its "
              f"parents with it. The temptation is sharpest where the "
              f"subject is a body over leaves whose cones exclude each "
              f"other, and climbing to the parent looks like the only way to "
              f"keep both grinds licensed — it is not, and the FLOOR "
              f"argument does not license it: that argument says a monster "
              f"may not go so deep that the work which would KILL it falls "
              f"off-tree, and the answer to a SIBLING falling off-tree is an "
              f"`also:` line, which is reviewed with the roadmap and says "
              f"out loud which second cone is admitted. A monster at the top "
              f"says nothing out loud and admits everything.")
        sys.exit(1 if args.gate else 0)

    cost = section_cost(roadmap, lineno)
    if cost > PROSE_BUDGET:
        print(f"check-monster: {os.path.basename(roadmap)}:{lineno}: tier "
              f"{tier}'s monster section spends {cost} prose characters "
              f"({cost - PROSE_BUDGET} over). It says WHY this is the thing "
              f"most worth killing and what goes with it; the research behind "
              f"that belongs in the declaration's own header, where a finding "
              f"has somewhere to go. `also:` lines are free.")
        sys.exit(1 if args.gate else 0)

    w = load_wiring()
    w.ROOT_REL = "Main.agda"
    files = w.find_agda_files(src_dir)
    defs, def_lines, postulate_names, order, _sites = \
        w.extract_definitions(src_dir, files)

    missing = [r for r in roots if r not in defs]
    if missing:
        for r in missing:
            print(f"check-monster: {os.path.basename(roadmap)}:{lineno}: "
                  f"tier {tier}'s monster root `{r}` is not declared in "
                  f"agda/src — a monster is a NAME, and a name that resolves "
                  f"to nothing holds nothing.")
        sys.exit(1 if args.gate else 0)

    corpus = w.build_corpus(src_dir, files)
    main_claims, _ = w.read_main_claims(src_dir)
    suppressed = w.postulate_arg_sites(src_dir, files, defs, def_lines,
                                       postulate_names)
    edges, _consumers, _seed = w.build_graph(
        src_dir, files, defs, def_lines, postulate_names, order, corpus,
        main_claims, suppressed)

    # A column-0 `...` continuation — a `with` arm, a `rewrite` clause — is
    # its OWN node in the wiring graph, seeded directly so that a name used
    # only inside one still reads as reached.  That exemption is right there
    # and wrong here: it breaks the chain, so an assembly whose body applies
    # its leaves in a `with` arm reaches none of them.  Splice each anonymous
    # node into the declaration it lexically continues.
    enclosing = enclosing_index(defs, def_lines)
    for anon, owner in enclosing.items():
        edges[owner] |= edges.get(anon, set())
    cone = w.reachable_from(set(roots), edges)

    base = merge_base()
    if base is None:
        print("check-monster: no merge-base with main — nothing to hold.")
        return
    hits = added_lines(base, src_rel)
    if hits is None:
        print("check-monster: git diff failed — not holding anything.")
        return

    by_file = w.owner_index(def_lines)
    offenders = {}
    for relpath, ln in hits:
        owner = w.owner_of(by_file, relpath, ln)
        if owner is None or owner in cone:
            continue
        if defs[owner].kind in ("anon", "module-app"):
            owner = enclosing.get(owner)
            if owner is None or owner in cone:
                continue
        offenders.setdefault(owner, (relpath, ln))

    # THE TWO FAILURE DIRECTIONS EACH HAVE A SIGNAL, WHICH IS WHY THE RULE OF
    # THUMB IS MECHANISABLE AT ALL.  TOO HIGH shows here: a cone that is very
    # nearly the whole tree is a monster that licenses everything, which is
    # what naming a tier's top line always produces.  TOO DEEP shows below, as
    # offenders — a monster whose cone excludes the work that would kill it
    # reports the same declarations every commit until they are `also:`-ed in.
    print(f"check-monster: tier {tier}'s monster is `{monster}`"
          + (f" (also: {', '.join(also)})" if also else "")
          + f" — {len(cone)} of {len(defs)} declaration(s) in agda/src are in "
            f"its cone ({100 * len(cone) // max(len(defs), 1)}%)")
    if not offenders:
        print("check-monster: every line added to agda/src since the "
              "merge-base with main lands inside that cone")
        return

    for owner, (relpath, ln) in sorted(offenders.items()):
        print(f"  {os.path.join(src_rel, relpath)}:{ln}: `{owner}` is OFF "
              f"MONSTER — nothing the monster's statement or body reaches "
              f"depends on it")
    print(f"check-monster: {len(offenders)} declaration(s) added off the "
          f"monster's tree.  Either wire them into `{monster}` in this "
          f"commit, MOVE the monster to the thing this work is actually "
          f"aimed at, or declare the exception with an `also:` line in the "
          f"tier's monster section — where it is reviewed with the roadmap.")
    sys.exit(1 if args.gate else 0)


if __name__ == "__main__":
    main()
