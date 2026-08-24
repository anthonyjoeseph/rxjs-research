#!/usr/bin/env python3
"""The CHANGED-SET dev sweep, and the decision of whether the full gate is owed.

`make gate-heavy` costs many minutes and re-proves the whole tower.  Most edits
cannot possibly need it: `make agda-dev` emits a module with no multi-member
mutual block VERBATIM, so for such a module the dev check IS a real check, and
the only thing the full build adds is the consumers.

So this script does two jobs, and the SECOND is the one that matters:

  1. dev-check every .agda this working tree has changed under `agda/src`.
  2. decide, mechanically, whether `make gate-heavy` is still owed — and FAIL if it
     is, so `make gate-light` cannot be used where it is not valid.

THE ESCALATION TRIGGERS, all three mechanical:

  · a changed module HAS a multi-member mutual block.  There, agda-dev stubs
    the block, termination of the real mutual recursion is not checked, and
    postulates do not reduce — a bad measure passes dev and fails the gate.
    This is the case the dev loop is documented to lie about, and it is the
    only case the user's rule cares about.
  · a changed file is NOT dev-checkable at all — anything under
    `agda/evidence/refuted`, which has its own root and its own target.
  · DRIFT: too many commits since the last green heavy gate.  A light gate is
    a bet that the consumers still typecheck, and a long run of unchecked bets
    is exactly how a tree gets far down a wrong road cheaply.

WHAT THE LIGHT GATE DOES NOT CHECK, stated because a silent gap is worse than
a slow build: the changed module's CONSUMERS.  A signature edit that its own
file accepts can break every importer, and only the full build sees that.  The
reverse-dependency cone is REPORTED here by name and count so the size of the
bet is visible; pass --deps to dev-check it too.
"""
import argparse
import importlib.util
import os
import re
import subprocess
import time
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join("agda", "src")
STAMP = os.path.join(REPO, ".gate-heavy-stamp")
MULTI = re.compile(r"^\s*\d+ blocks?, (\d+) multi-member", re.M)


# WHY A CEILING ON THE CHANGED SET: the light gate wins by checking ONE module
# instead of the tower.  It stops winning when the changed set grows -- N dev
# checks run sequentially, each rebuilding its own cone, and the full build
# buys the whole tower for roughly the same money.  `--max-files` is where that
# crossover is drawn, and past it the tool escalates rather than grinding.
def _load(name: str):
    """Import a sibling script, so the two tools cannot drift apart."""
    path = os.path.join(REPO, "scripts", name + ".py")
    spec = importlib.util.spec_from_file_location(name.replace("-", "_"), path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def git(*args) -> str:
    return subprocess.run(("git",) + args, cwd=REPO, capture_output=True,
                          text=True).stdout


def gate_base() -> str:
    """The commit the last green heavy gate covered, or HEAD.

    THE CHANGED SET IS NOT "DIFF AGAINST HEAD", AND MEASURING IT THAT WAY IS A
    FALSE GREEN.  A session that commits and then runs `make gate` has a clean
    tree, so a HEAD diff is empty, so nothing is checked, and the gate says ALL
    GREEN about a commit it never looked at.  That is the flow every leg of
    this campaign uses -- land the work, then gate it.

    What the light gate actually owes is everything the last green HEAVY gate
    did not cover, which the stamp already records.  With no stamp there is
    nothing to diff from, and the drift trigger escalates anyway.
    """
    if not os.path.exists(STAMP):
        return "HEAD"
    sha = open(STAMP, encoding="utf-8").read().strip().split()[0]
    ok = subprocess.run(("git", "cat-file", "-e", sha + "^{commit}"),
                        cwd=REPO, capture_output=True).returncode == 0
    return sha if ok else "HEAD"


def changed_files() -> list[str]:
    """Every .agda uncovered by the last green heavy gate, tracked or not."""
    out = set()
    for line in git("diff", "--name-only", gate_base(), "--",
                    "agda").split("\n"):
        if line.strip().endswith(".agda"):
            out.add(line.strip())
    for line in git("status", "--porcelain", "--", "agda").split("\n"):
        if line.startswith("?? "):
            p = line[3:].strip()
            if p.endswith(".agda"):
                out.add(p)
            elif p.endswith(os.sep):
                for root, _, fs in os.walk(os.path.join(REPO, p)):
                    for f in fs:
                        if f.endswith(".agda"):
                            out.add(os.path.relpath(
                                os.path.join(root, f), REPO))
    return sorted(out)


def multi_member(rel_src: str) -> int | None:
    """How many multi-member mutual blocks, via the free --list pass."""
    pr = subprocess.run([sys.executable,
                         os.path.join(REPO, "scripts", "agda-dev.py"),
                         "--list", rel_src],
                        cwd=REPO, capture_output=True, text=True)
    m = MULTI.search(pr.stdout + pr.stderr)
    return int(m.group(1)) if m else None


def dev_check(rel_src: str, budget: str) -> tuple[int, str]:
    pr = subprocess.run([sys.executable,
                         os.path.join(REPO, "scripts", "agda-dev.py"),
                         "--budget", budget, rel_src],
                        cwd=REPO, capture_output=True, text=True)
    return pr.returncode, pr.stdout + pr.stderr


def consumers(mods: set[str]) -> set[str]:
    """Every module that transitively imports one of `mods` — the unchecked bet."""
    ci = _load("check-imports")
    ci.TREES = list(ci.CLAIM_ROOT)
    files = []
    for tree in ci.TREES:
        for root, _, fs in os.walk(os.path.join(REPO, tree)):
            for f in fs:
                if f.endswith(".agda"):
                    files.append(os.path.relpath(
                        os.path.join(root, f), REPO))
    graph = ci.import_graph(files)
    rev: dict = {}
    for src, dsts in graph.items():
        for d in dsts:
            rev.setdefault(d, set()).add(src)
    seen, stack = set(), list(mods)
    while stack:
        m = stack.pop()
        for up in rev.get(m, ()):
            if up not in seen:
                seen.add(up)
                stack.append(up)
    return seen - mods


def commits_since_full() -> int | None:
    if not os.path.exists(STAMP):
        return None
    sha = open(STAMP, encoding="utf-8").read().strip().split()[0]
    out = git("rev-list", "--count", sha + "..HEAD").strip()
    return int(out) if out.isdigit() else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--files", nargs="*", default=None,
                    help="override the changed set (selftest / manual use)")
    ap.add_argument("--budget", default="45")
    ap.add_argument("--max-files", type=int, default=6,
                    help="above this many changed modules, escalate: N "
                         "sequential dev checks cost more than one full "
                         "build, which checks the whole tower for the price")
    ap.add_argument("--drift", type=int, default=10,
                    help="commits since the last green heavy gate before the "
                         "full build is owed regardless of what changed")
    ap.add_argument("--deps-over", type=int, default=8,
                    help="dev-check the consumer cone automatically once it "
                         "exceeds this many modules.  A wide cone is the one "
                         "thing that used to justify reaching for the tower by "
                         "hand; checking the cone answers it directly, and for "
                         "a few dev passes rather than the whole build")
    ap.add_argument("--deps", action="store_true",
                    help="also dev-check the reverse-dependency cone")
    ap.add_argument("--cone-budget", type=int, default=300,
                    help="total wall-clock seconds the CONE sweep may spend. "
                         "The per-module budget bounds one check; nothing "
                         "bounded the sum, so a changed set low in the tower "
                         "(48-module cone) could outspend the one build that "
                         "checks all of it. Past this the remainder is "
                         "reported unchecked, never silently dropped.")
    ap.add_argument("--plan", action="store_true",
                    help="print the sweep PLAN — which modules would be dev "
                         "checked and which cone members are held back — then "
                         "stop.  Free: it runs no agda, which is what makes "
                         "the claim-root exclusion testable at gate-cheap "
                         "speed.")
    ap.add_argument("--verdict-only", action="store_true",
                    help="decide escalation from the free --list pass; run no "
                         "real check")
    ap.add_argument("--stamp", action="store_true",
                    help="record HEAD as the last green full gate, and exit")
    a = ap.parse_args()

    if a.stamp:
        with open(STAMP, "w", encoding="utf-8") as fh:
            fh.write(git("rev-parse", "HEAD").strip() + "\n")
        print("dev-changed: stamped this commit as the last green full gate")
        return 0

    files = a.files if a.files is not None else changed_files()
    src_files = [f for f in files if f.startswith(SRC + os.sep)]
    other = [f for f in files if not f.startswith(SRC + os.sep)]

    print(f"dev-changed: {len(files)} changed .agda file(s)"
          f" — {len(src_files)} in {SRC}, {len(other)} elsewhere")
    if not files:
        print("dev-changed: nothing changed under agda/ — no Agda was checked, "
              "and this is a REPORT rather than a pass")

    escalate = []
    # A dev check is only cheap SINGLY.  Each one pays its own startup and
    # rechecks the changed module's dependency cone; past a handful, the full
    # build is the better buy -- it costs about the same and checks EVERYTHING,
    # consumers included, which the light gate explicitly does not.
    if len(src_files) > a.max_files:
        escalate.append(f"{len(src_files)} changed modules in {SRC} (limit "
                        f"{a.max_files}) — that many dev checks costs more "
                        f"than one full build, which checks the consumers too")
    for f in other:
        escalate.append(f"{f}: not dev-checkable (its tree has its own root) "
                        f"— `make refuted` / `make gate` owns it")

    fail = 0
    multi = {}
    for f in src_files:
        rel = os.path.relpath(f, SRC)
        k = multi_member(rel)
        multi[f] = k
        if k is None:
            escalate.append(f"{f}: --list could not be read, so the block "
                            f"structure is UNKNOWN — assume the worst")
        elif k > 0:
            escalate.append(f"{f}: {k} multi-member mutual block(s) — agda-dev "
                            f"stubs them, so a dev pass here is not a check")

    n = commits_since_full()
    if n is None:
        escalate.append("no record of a green `make gate` in this working copy "
                        "— the stamp is written by the heavy gate and wiped by a "
                        "clean, so this is the cold-cache case")
    elif n > a.drift:
        escalate.append(f"{n} commits since the last green heavy gate "
                        f"(limit {a.drift}) — the consumers have gone "
                        f"unchecked for too long")
    else:
        print(f"dev-changed: {n} commit(s) since the last green full gate "
              f"(limit {a.drift})")

    if a.verdict_only:
        for line in escalate:
            print("dev-changed: ESCALATE  " + line)
        if escalate:
            print("dev-changed: FULL GATE REQUIRED")
        else:
            print("dev-changed: light gate sufficient for this changed set — "
                  "no changed module has a multi-member block, so NOTHING was "
                  "stubbed and the termination question is not asked, not "
                  "merely likely to pass.  Overriding this verdict by hand is "
                  "a claim that this tool is broken, which is a finding.")
        return 2 if escalate else 0

    # A CLAIM ROOT IS EXCLUDED WHEN IT IS *CHANGED*, FOR THE REASON THE CONE
    # SWEEP ALREADY EXCLUDES IT: a root's dev check IS the tower, so it times
    # out at the per-module budget and reports RED for a module with nothing
    # wrong with it.  The cone half of this was written first and read as the
    # whole rule; it is not, because a root is a FILE and files get edited --
    # a one-word comment in Main is enough to put it in the changed set, and
    # then the light path fails on the one module it can never check.
    _cir = _load("check-imports")
    _cir.TREES = list(_cir.CLAIM_ROOT)
    root_paths = {os.path.join(t, r) for t, r in _cir.CLAIM_ROOT.items()}
    changed_roots = sorted(f for f in src_files if f in root_paths)
    if changed_roots:
        print(f"dev-changed: NOT the {len(changed_roots)} CHANGED claim "
              f"root(s) — a root's dev check is the tower, which is the heavy "
              f"gate's job: " + ", ".join(changed_roots))
    checkable = [f for f in src_files
                 if multi.get(f) == 0 and f not in root_paths]
    # A WIDE CONE IS NOT A REASON TO REACH FOR THE TOWER, and it used to be
    # taken as one.  The cone is the only thing the light path leaves unchecked,
    # so when it is wide the answer is to CHECK IT -- a few dev passes -- not to
    # buy the whole build.  Escalating instead pays half an hour to cover a risk
    # a cheap pass covers, and it never announces itself as the wrong call.
    deps = a.deps
    if not deps and src_files:
        ci0 = _load("check-imports")
        ci0.TREES = list(ci0.CLAIM_ROOT)
        if len(consumers({ci0.module_of(f) for f in src_files})) > a.deps_over:
            print(f"dev-changed: the cone is wider than {a.deps_over} — "
                  f"checking it rather than escalating to the tower")
            deps = True
    cone_only = set()
    cone_stubbed = []
    if deps:
        ci = _load("check-imports")
        ci.TREES = list(ci.CLAIM_ROOT)
        mods = {ci.module_of(f) for f in src_files}
        cone = consumers(mods)
        # A CLAIM ROOT'S DEV CHECK *IS* THE TOWER, so it is never part of a
        # cone sweep.  Every module in `src` has a route to Main by the wiring
        # law, so EVERY cone contains the roots -- which is why the cone sweep
        # read as "cheaper than the tower" and then ran the tower.  Measured:
        # the roots timed out at 45s and Main alone took minutes at 560s, while
        # every non-root consumer in the same run came in under 12s.  What
        # covers the roots is the DRIFT counter and the heavy gate, not this.
        roots = {ci.module_of(os.path.join(t, r))
                 for t, r in ci.CLAIM_ROOT.items()}
        skipped_roots = sorted(cone & roots)
        cone = cone - roots
        print(f"dev-changed: --deps: adding {len(cone)} consumer module(s)")
        if skipped_roots:
            print(f"dev-changed: --deps: NOT the {len(skipped_roots)} claim "
                  f"root(s) in the cone — a root's dev check is the tower, "
                  f"which is the heavy gate's job: "
                  + ", ".join(skipped_roots))
        by_mod = {ci.module_of(f): f for f in src_files}
        # A CONE MEMBER WITH A MULTI-MEMBER BLOCK IS NOT SWEEPABLE, and
        # dropping it in SILENCE is how the light path came to read as
        # reassurance while the one consumer that validates a new arm's FIT
        # went unchecked: agda-dev stubs a block's siblings, so a dev check
        # there is not a check.  Say so and count it unchecked.
        for m in sorted(cone):
            p = os.path.join(SRC, m.replace(".", os.sep) + ".agda")
            if os.path.exists(os.path.join(REPO, p)) and p not in by_mod:
                k = multi_member(os.path.relpath(p, SRC))
                if k == 0:
                    checkable.append(p)
                    cone_only.add(p)
                else:
                    cone_stubbed.append(p)
        for m in cone_stubbed:
            print(f"dev-changed: skip  {m}  — has a multi-member mutual block, "
                  f"where agda-dev stubs the siblings; only `make gate-heavy` "
                  f"checks it")

    if a.plan:
        for f in checkable:
            print(f"dev-changed: plan  {'cone' if f in cone_only else 'chgd'}"
                  f"  {f}")
        return 0

    # A BUDGET TIMEOUT IS NOT A RED, AND CONFLATING THEM MAKES A CONE SWEEP
    # LIE.  For a module the commit actually CHANGED, an unfinished check is a
    # failure -- that module has to be checked.  For a cone module it is only
    # the bet the light path was making anyway, so it is reported as still
    # unchecked and the sweep goes on.
    unchecked = list(cone_stubbed)
    cone_spent = 0.0
    for f in checkable:
        if f in cone_only and cone_spent > a.cone_budget:
            unchecked.append(f)
            continue
        t0 = time.time()
        rc, out = dev_check(os.path.relpath(f, SRC), a.budget)
        if f in cone_only:
            cone_spent += time.time() - t0
        tail = [l for l in out.split("\n") if l.strip()][-1:] or [""]
        # agda-dev's PROCESS exit is 1 for any red; the budget kill is
        # distinguishable only by the per-member `(exit 124)` it reports.  A
        # cone member has no multi-member block by construction, so it runs
        # exactly ONE focus check and that marker cannot be another member's.
        if "(exit 124)" in out and f in cone_only:
            unchecked.append(f)
            print(f"dev-changed: skip  {f}  — over the {a.budget}s budget; "
                  f"still an unchecked consumer")
            continue
        print(f"dev-changed: {'ok  ' if rc == 0 else 'FAIL'}  {f}"
              f"  — {tail[0].strip()}")
        if rc != 0:
            fail = 1
            print(out.rstrip())

    if src_files and not checkable and not escalate:
        print("dev-changed: every changed module was skipped — nothing was "
              "actually checked")
        fail = 1

    mods = {_load("check-imports").module_of(f) for f in src_files} \
        if src_files else set()
    if mods:
        cone = consumers(mods)
        if deps:
            print(f"dev-changed: the cone was CHECKED — {len(cone)} consumer "
                  f"module(s) in {cone_spent:.0f}s, minus the claim roots and "
                  f"{len(unchecked)} left unchecked (per-module budget or the "
                  f"{a.cone_budget}s sweep budget)")
            for m in unchecked[:12]:
                print(f"                unchecked: {m}")
            if len(unchecked) > 12:
                print(f"                … and {len(unchecked) - 12} more")
        else:
            print(f"dev-changed: NOT CHECKED — {len(cone)} consumer module(s) "
                  f"of the changed set; the light gate bets these still "
                  f"typecheck")
            for m in sorted(cone)[:12]:
                print(f"                {m}")
            if len(cone) > 12:
                print(f"                … and {len(cone) - 12} more")

    for line in escalate:
        print("dev-changed: ESCALATE  " + line)
    if fail:
        print("dev-changed: RED — a dev check failed above")
        return 1
    if escalate:
        print("dev-changed: FULL GATE REQUIRED — run `make gate`")
        return 2
    print(f"dev-changed: {len(checkable)} module(s) dev-green; no multi-member "
          f"block touched, so `make gate-heavy` adds only the consumers"
          + (f" — {len(unchecked)} of which stayed UNCHECKED, named above"
             if unchecked else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
