#!/usr/bin/env python3
"""The EVIDENCE trees' two laws — agda/evidence/refuted and agda/evidence/probed.

Evidence is what is CHECKED but never CLAIMED: a refutation is conclusive
negative evidence (a ⊥ for a route), a probe is inconclusive positive evidence
(a `refl` receipt at concrete inputs).  Neither is part of the proof, and the
whole point of the tree is that neither can become part of it.

  E1  THE ONE-WAY BOUNDARY.  Nothing in agda/src may import from an evidence
      tree.  The library layout already makes such an import UNRESOLVABLE —
      agda/rxjs-research.agda-lib does not include the evidence roots, so the
      name does not exist from src's side — and that, not this check, is the
      mechanism.  What this adds is a fast, legible failure: a grep-level
      report in a second instead of an Agda scope error minutes into a build,
      and a check that survives someone "fixing" the include path.

  E2  A PROBE NAMES A LIVE TARGET.  Every file under probed/ carries at least
      one `-- TARGET: <postulate>` line, and every name it declares is a LIVE
      postulate.  A probe whose target has been discharged or deleted has
      nothing left to be evidence FOR.

      E2 exists because probes and refutations decay differently, and only one
      of them announces it.  A refutation dies when src can no longer STATE
      it, and `make refuted` goes red the moment that happens.  A probe dies
      when its TARGET dies — and nothing happens at all: the rows still
      compute, the `refl`s still hold, and the file stays green forever while
      being evidence for a question nobody is asking.  E2 is that
      announcement.

      A probe that has outlived its target is either deleted or retargeted.
      If what it actually pins is the EVALUATOR rather than a statement, it is
      not a probe at all — it is a unit test, and its home is the bug cache.

  E4  A HARNESS SERIES EXPIRES LIKE A PROBE.  Every `-- SERIES` block in the
      harness declares a `-- TARGET: <postulate>` naming a live postulate, on
      exactly the reasoning E2 rests on — a harness row is a probe that ran
      natively instead of in the typechecker, and it decays the same silent
      way.  It decays WORSE, in fact: the harness is a MODULE_ROOT the gate
      never builds, so its rows keep printing numbers about a statement that
      has been proven for months and nothing anywhere goes red.  Measured on
      the sweep that added this check, twenty-four series carried zero target
      declarations and TWELVE of them were evidence about statements that were
      by then proven definitions or had been deleted outright — half the file.

      A series is deleted or retargeted the moment its target dies.  Its
      FINDINGS do not die with it: a coverage boundary, a blocked verdict or a
      dead route belongs in the header of the statement it constrains, which
      is where it should have been written in the first place.
"""

import argparse
import os
import re
import subprocess
import sys

SRC = "agda/src"
HARNESS = "agda/src/Harness"
EVIDENCE = "agda/evidence"
# The module namespace each evidence root owns.  A `src` file naming one of
# these is an E1 violation whatever path it uses to say it.
NAMESPACES = {"refuted": "Refuted", "probed": "Probed"}

SERIES = re.compile(r"^--\s*SERIES\b\s*(.*?)\s*$")

IMPORT = re.compile(r"^\s*(?:open\s+import|import)\s+([\w.\-]+)")
TARGET = re.compile(r"^\s*--\s*TARGET:\s*(.+?)\s*$")


def agda_files(root):
    for dirpath, _dirs, names in os.walk(root):
        for n in sorted(names):
            if n.endswith(".agda"):
                yield os.path.join(dirpath, n)


def live_postulates(src):
    """Names of every live postulate, from the wiring checker's own ledger."""
    here = os.path.dirname(os.path.abspath(__file__))
    out = subprocess.run(
        [os.path.join(here, "check-wiring.py"), "--postulates", "--src", src],
        capture_output=True, text=True)
    names = set()
    for line in out.stdout.split("\n"):
        line = line.strip()
        if not line or line.startswith("--"):
            continue
        names.add(line.split()[0])
    return names


def check_e1(src, namespaces):
    """No src file may import an evidence namespace."""
    bad = []
    if not os.path.isdir(src):
        return bad
    for p in agda_files(src):
        for i, line in enumerate(open(p, encoding="utf-8"), 1):
            m = IMPORT.match(line)
            if not m:
                continue
            head = m.group(1).split(".")[0]
            if head in set(namespaces.values()):
                bad.append((p, i, m.group(1)))
    return bad


def check_e2(evidence, postulates):
    """Every probe declares at least one target, and every target is live."""
    missing, dead = [], []
    root = os.path.join(evidence, "probed")
    if not os.path.isdir(root):
        return missing, dead, 0
    n = 0
    for p in agda_files(root):
        base = os.path.basename(p)
        if base == "Main.agda":          # the claim root states no rows
            continue
        n += 1
        targets = []
        for i, line in enumerate(open(p, encoding="utf-8"), 1):
            m = TARGET.match(line)
            if m:
                for t in re.split(r"[,\s]+", m.group(1)):
                    if t:
                        targets.append((i, t))
        if not targets:
            missing.append(p)
            continue
        for i, t in targets:
            if t not in postulates:
                dead.append((p, i, t))
    return missing, dead, n


# A RECEIPT, in the marker form CLAUDE.md specifies: the marker opens a comment
# line and a COLON closes it.  The colon is what separates a receipt from the
# several files that discuss the word "PROBED" in prose, and it replaced a
# requirement that the marker carry a DATE -- which had quietly become
# unsatisfiable, since `make comments-check` forbids a date anywhere in
# `agda/src` or `agda/evidence`.  Two gate checks cannot both be obeyed, so this
# half of E3 was matching NOTHING while reporting itself clean, and the tree's
# six real receipts were invisible to the check written to expire them.  A
# discriminator one sibling check forbids is worse than no discriminator: it
# fails silent and it reports a total, and a total of zero reads as tidy.
#
# EVERY NEAR MISS IS A FINDING RATHER THAN A SKIP, which is the whole design and
# the reason this check has a MATCH regex and a CANDIDATE one.  Three ways a
# receipt slips past a strict pattern, all of them live in this tree at the time
# of writing: an invented SUFFIX (two were spelled `PROBED-GREEN`, a marker
# someone coined for exactly the distinction E3 enforces); a marker with no
# colon at all, trailing a parenthetical instead; and an OBSCURED one, written
# `-- -- PROBED:` so that the marker sits inside the comment TEXT -- which also
# walks it past `make comments-check`'s ordering rule, since a doubled dash is
# prose to every checker in the repo.  A pattern admitting only the legal
# spelling would have reported all three as absent.
#
# LEADING WHITESPACE IS ALLOWED, because a receipt on a block member is
# indented and an anchor at column 0 made it a SILENT SKIP -- not reported, not
# counted, not a subject.  That is the one outcome this check exists to prevent,
# and it went unnoticed until a real receipt was written inside a `postulate`
# block and the receipt total did not move.
RECEIPT = re.compile(r"^\s*--\s*PROBED(?P<suffix>-[A-Z-]+)?\s*:")
# the CANDIDATE form: any run of comment dashes, then the bare marker word.
# Anything matching this and not `RECEIPT` is reported, never dropped.
CANDIDATE = re.compile(r"^\s*(?:--\s*)+(?=PROBED\b)")
# ONE LEGAL SPELLING, AND NO HISTORICAL VARIANT.  A receipt whose statement has
# been PROVEN is deleted, not re-marked: the theorem says more than the probe
# ever did, so the coverage claim is superseded rather than dated, and what is
# worth keeping (a harness, a sha) is a `RECOVERY:` pointer and not a receipt.
# That is E2's law arriving from the header's side -- a probe expires with its
# target -- and it is what removes a standing CONTRADICTION between two gate
# checks: `make comments-check` blacklists `PROBED-HISTORICAL` as a historical
# marker, so the one spelling this check used to demand at the moment of
# discharge was a spelling its sibling refused to let anyone write.
LEGAL_SUFFIX = (None,)
# The subject line: a top-level declaration, which is what a header sits above.
DECL = re.compile(r"^(?!--)(?P<name>[^\s:(){}]+)\s*:")
POSTBLOCK = re.compile(r"^\s*postulate\b")
INDENTED = re.compile(r"^\s+(?P<name>[^\s:(){}]+)\s*:")


def check_e3(src, postulates):
    """E3.  Every `-- PROBED` receipt names a subject, and its MARKER says
    whether that subject is still a postulate.

    Receipts are the only surviving trace of most of this campaign's probes --
    the probe files expire and are deleted by E2, the receipt stays -- so their
    integrity outlives the apparatus they describe.  Nothing checked them.

    Two findings.  An ORPHANED receipt sits above no declaration at all, so no
    reader and no check can tell what it is evidence ABOUT.  A STALE one sits
    above a statement that is no longer a postulate, and it is DELETED --
    a receipt has exactly one legal tense.

    The second is the one worth having, and the moment it fires is the point of
    it: discharging a statement turns every receipt above it into a claim about
    something that is no longer open, which is exactly when a live risk class
    left standing in prose becomes a lying comment -- a FORBIDDEN STATE that
    until now was enforced by nobody.  Failing at the discharge forces the
    author to re-read the receipt while the discharge is still in their hands,
    rather than leaving it to decay into confident, wrong background.
    """
    orphaned, mismarked = [], []
    if not os.path.isdir(src):
        return orphaned, mismarked, 0
    n = 0
    for p in agda_files(src):
        lines = open(p, encoding="utf-8").read().split("\n")
        for i, line in enumerate(lines):
            m = RECEIPT.match(line)
            if not m:
                c = CANDIDATE.match(line)
                if c:
                    n += 1
                    mismarked.append((
                        p, i + 1, "-", "PROBED",
                        "unreadable as a receipt -- the marker must OPEN the "
                        "comment (one `--`, no doubling) and END in a colon"))
                continue
            n += 1
            # the subject is the first declaration below the comment block.
            # AN INDENTED RECEIPT IS ALREADY INSIDE A BLOCK: its `postulate`
            # keyword sits ABOVE it, so waiting to meet one below would never
            # enter block mode and the indented sibling declaration would not
            # match `DECL`.  The indentation of the marker itself is the signal.
            subject = None
            in_block = line[:1].isspace()
            for j in range(i + 1, len(lines)):
                nxt = lines[j]
                if not nxt.strip() or nxt.lstrip().startswith("--"):
                    continue
                if POSTBLOCK.match(nxt):
                    in_block = True
                    continue
                d = DECL.match(nxt) or (INDENTED.match(nxt) if in_block else None)
                if d:
                    subject = d.group("name")
                    break
                if not nxt.startswith((" ", "\t")):
                    in_block = False
            suffix = m.group("suffix")
            if suffix not in LEGAL_SUFFIX:
                mismarked.append((p, i + 1, "-", "PROBED" + suffix,
                                  "not a receipt marker this check knows "
                                  "(a receipt is `PROBED`, and it has exactly "
                                  "one legal tense)"))
                continue
            if subject is None:
                orphaned.append((p, i + 1))
                continue
            if subject not in postulates:
                mismarked.append((p, i + 1, subject, "PROBED",
                                  "no longer a postulate"))
    return orphaned, mismarked, n


def check_e4(harness, postulates):
    """Every `-- SERIES` block names a live postulate.

    A block is the run of comment lines the SERIES marker opens; it ends at
    the first line that is not a comment.  Two series whose headers abut with
    no code between them are ONE run, and the second one's marker is what the
    scan sees next -- so a target is credited to the marker it follows, and a
    run holding two markers needs two targets.
    """
    missing, dead, n = [], [], 0
    for path in agda_files(harness):
        lines = open(path, encoding="utf-8").read().split("\n")
        open_at = None          # a SERIES marker still owed a target
        for i, line in enumerate(lines, 1):
            m = SERIES.match(line)
            if m:
                if open_at is not None:
                    missing.append((path, open_at[0], open_at[1]))
                open_at = (i, m.group(1)[:40])
                n += 1
                continue
            t = TARGET.match(line)
            if t and open_at is not None:
                if t.group(1) not in postulates:
                    dead.append((path, i, t.group(1), open_at[1]))
                open_at = None
                continue
            if not line.startswith("--") and open_at is not None:
                missing.append((path, open_at[0], open_at[1]))
                open_at = None
        if open_at is not None:
            missing.append((path, open_at[0], open_at[1]))
    return missing, dead, n


def report(src, evidence, namespaces, postulates, gate, harness=HARNESS):
    e1 = check_e1(src, namespaces)
    missing, dead, nprobes = check_e2(evidence, postulates)
    orphaned, mismarked, nreceipts = check_e3(src, postulates)
    smissing, sdead, nseries = check_e4(harness, postulates)

    for p, i, mod in e1:
        print(f"{p}:{i}: E1 — src imports the evidence tree: {mod}")
        print("    Evidence is CHECKED but never CLAIMED.  A proof that "
              "depends on a probe")
        print("    depends on a `refl` at three inputs; one that depends on a "
              "refutation")
        print("    depends on an obituary.  Move the fact into src and prove "
              "it there.")
    for p in missing:
        print(f"{p}: E2 — probe declares no `-- TARGET: <postulate>`")
        print("    A probe with no target cannot be shown to have expired, "
              "which is the")
        print("    one thing a probe needs (see this file's header).")
    for p, i, t in dead:
        print(f"{p}:{i}: E2 — target {t!r} is not a live postulate")
        print("    It has been discharged, renamed or deleted.  DELETE the "
              "probe, or")
        print("    retarget it at the statement it now tests.  If what it "
              "pins is the")
        print("    EVALUATOR and not a statement, it is a unit test — its "
              "home is the")
        print("    bug cache.")

    for p, i, name in smissing:
        print(f"{p}:{i}: E4 — series {name!r} declares no `-- TARGET: "
              f"<postulate>`")
        print("    A harness row is a probe that ran natively.  Without a "
              "target nothing")
        print("    can say when it stopped being evidence, and the gate never "
              "builds this")
        print("    tree, so nothing else will notice either.")
    for p, i, t, name in sdead:
        print(f"{p}:{i}: E4 — series {name!r} targets {t!r}, which is not a "
              f"live postulate")
        print("    DELETE the series, or retarget it.  Its FINDINGS are not "
              "deleted with")
        print("    it: a coverage boundary or a blocked verdict belongs in the "
              "header of")
        print("    the statement it constrains.")

    for p, i in orphaned:
        print(f"{p}:{i}: E3 — receipt sits above no declaration")
        print("    A receipt is evidence ABOUT a statement, and this one names "
              "none, so")
        print("    neither a reader nor a check can say what it is evidence "
              "for.  Move it")
        print("    into the header of its subject, or delete it.")
    for p, i, subj, marker, why in mismarked:
        if subj == "-":
            print(f"{p}:{i}: E3 — `{marker}` is not a receipt marker: {why}")
            print("    A marker this check does not know is a receipt it cannot "
                  "audit, so an")
            print("    invented spelling is worse than a wrong one -- it reads "
                  "as evidence and")
            print("    is enforced as nothing.")
            continue
        print(f"{p}:{i}: E3 — receipt on {subj!r} is marked `{marker}`, but "
              f"{subj!r} is {why}")
        print("    DELETE the receipt, and re-read it while you are here.  A "
              "receipt written")
        print("    against an open statement keeps asserting a live risk after "
              "that statement")
        print("    is proven, and a live risk class standing in the header of a "
              "proven")
        print("    definition is a lying comment.  The theorem says more than "
              "the probe ever")
        print("    did, so the coverage claim is superseded rather than dated; "
              "if the probe")
        print("    left a harness worth recovering, that is a `RECOVERY:` "
              "pointer.")

    n = (len(e1) + len(missing) + len(dead) + len(orphaned) + len(mismarked)
         + len(smissing) + len(sdead))
    if n == 0:
        print(f"check-evidence: clean — {nprobes} probe(s), every one naming a "
              f"live postulate; {nreceipts} receipt(s), every one above its "
              f"subject and marked for that subject's state; no src file "
              f"imports the evidence tree; {nseries} harness series, every "
              f"one naming a live postulate")
    if gate and n:
        print(f"check-evidence: {n} finding(s) — see above")
        return 1
    return 0


def selftest():
    """Fires on each law, and stays quiet on the shapes that are legal."""
    here = os.path.dirname(os.path.abspath(__file__))
    fx = os.path.join(here, "evidence-selftest")
    fails = []

    def run(src, ev, posts, want, label, harness=None):
        import io
        import contextlib
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = report(src, ev, NAMESPACES, posts, True,
                        harness if harness else os.path.join(fx, "empty"))
        got = buf.getvalue()
        if want and want not in got:
            fails.append(f"{label}: expected {want!r}, got:\n{got}")
        if not want and rc != 0:
            fails.append(f"{label}: expected clean, got:\n{got}")
        return got

    run(os.path.join(fx, "bad-src"), os.path.join(fx, "empty"),
        set(), "E1 — src imports the evidence tree", "E1 fires")
    run(os.path.join(fx, "good-src"), os.path.join(fx, "empty"),
        set(), None, "E1 quiet on a src that imports only src")
    run(os.path.join(fx, "empty"), os.path.join(fx, "no-target"),
        {"live-one"}, "E2 — probe declares no", "E2 fires on a missing target")
    run(os.path.join(fx, "empty"), os.path.join(fx, "dead-target"),
        {"live-one"}, "is not a live postulate", "E2 fires on a dead target")
    run(os.path.join(fx, "empty"), os.path.join(fx, "live-target"),
        {"live-one"}, None, "E2 quiet on a live target")
    run(os.path.join(fx, "empty"), os.path.join(fx, "live-target"),
        set(), "is not a live postulate",
        "E2 fires when the target is discharged out from under the probe")

    empty = os.path.join(fx, "empty")
    run(empty, empty, {"live-one"}, "E4 — series 'A —",
        "E4 fires on a series with no target",
        harness=os.path.join(fx, "harness-no-target"))
    run(empty, empty, {"live-one"}, "which is not a live postulate",
        "E4 fires on a series whose target is discharged",
        harness=os.path.join(fx, "harness-dead-target"))
    run(empty, empty, {"live-one"}, None,
        "E4 quiet on a series naming a live postulate",
        harness=os.path.join(fx, "harness-live-target"))
    run(empty, empty, {"live-one"}, "E4 — series 'A —",
        "E4 charges each of two ABUTTING series its own target, rather than "
        "letting the second one's cover both",
        harness=os.path.join(fx, "harness-abutting"))

    run(os.path.join(fx, "receipt-live"), os.path.join(fx, "empty"),
        {"live-one"}, None, "E3 quiet on a receipt above a live postulate")
    run(os.path.join(fx, "receipt-hist"), os.path.join(fx, "empty"),
        {"live-one"}, "is no longer a postulate",
        "E3 fires on a `PROBED` receipt whose statement is now a definition")
    run(os.path.join(fx, "receipt-live"), os.path.join(fx, "empty"),
        set(), "is no longer a postulate",
        "E3 fires the moment the statement is discharged out from under the "
        "receipt")
    run(os.path.join(fx, "receipt-orphan"), os.path.join(fx, "empty"),
        {"live-one"}, "sits above no declaration",
        "E3 fires on a receipt with no subject")
    run(os.path.join(fx, "receipt-unknown"), os.path.join(fx, "empty"),
        {"live-one"}, "is not a receipt marker",
        "E3 fires on an invented marker rather than skipping it")
    run(os.path.join(fx, "receipt-prose"), os.path.join(fx, "empty"),
        {"live-one"}, None,
        "E3 quiet on prose where the marker does not open the comment")
    run(os.path.join(fx, "receipt-nearmiss"), os.path.join(fx, "empty"),
        {"live-one", "live-two"}, "unreadable as a receipt",
        "E3 fires on a marker doubled into the comment text, and on one with "
        "no colon -- rather than counting zero receipts and reporting clean")
    run(os.path.join(fx, "receipt-indented"), os.path.join(fx, "empty"),
        {"live-one"}, "is no longer a postulate",
        "E3 reads an INDENTED receipt on a `postulate` block member, rather "
        "than skipping it silently")

    if fails:
        for f in fails:
            print("SELFTEST FAIL:", f)
        return 1
    print("evidence-selftest: PASS (E1 fires on a src file importing the "
          "evidence tree and not on a src-only import; E2 fires on a probe "
          "with no target, on a target that was never live, and on a live "
          "target the moment it leaves the postulate ledger; and a probe "
          "naming a live postulate is clean.  E3 fires on a `PROBED` receipt "
          "whose statement is now a definition -- including the moment it is "
          "discharged out from under the receipt -- on a receipt above no "
          "declaration at all, and on an invented marker rather than skipping "
          "it; and stays quiet on a receipt above a live postulate and on "
          "prose where the marker does not open the comment.  A receipt "
          "INDENTED inside a `postulate` block is read and attributed to its "
          "own block member, not skipped and not credited to the member above "
          "it -- and a NEAR MISS is a finding rather than a skip, so a marker "
          "doubled into the comment text or written with no colon is reported "
          "instead of dropping the receipt total to a tidy-looking zero.  "
          "E4 fires on a harness series with no target and on one whose "
          "target has been discharged, charges each of two ABUTTING series "
          "its own target, and is quiet on a series naming a live "
          "postulate)")
    return 0


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gate", action="store_true")
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--src", default=SRC)
    ap.add_argument("--evidence", default=EVIDENCE)
    a = ap.parse_args()
    if a.selftest:
        sys.exit(selftest())
    sys.exit(report(a.src, a.evidence, NAMESPACES,
                    live_postulates(a.src), a.gate))


if __name__ == "__main__":
    main()
