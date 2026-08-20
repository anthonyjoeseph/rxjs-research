#!/usr/bin/env python3
"""PROOF-STATE.md's tiers must be sorted riskiest-class-first.

WHY THIS IS A GATE AND NOT A CONVENTION.  The roadmap's order is the only
thing in the repo that says what to work on next, so a stale sort silently
re-aims the next session — and it re-aims toward the SAFE end, because
grinding is what looks like progress.  Measured 2026-08-20: tier 0's sole
SHAPE row sat in the NINTH slot behind four DIFFICULTY rows, and the session
read the tier top-down, picked DIFFICULTY, and was about to fan the rest out
as GRINDABLE — the riskiest row on the anchor tier going untouched precisely
because the list said it was ninth.  A rule you can satisfy while still
failing is a rule that needs a machine (the same argument as `make find`).

WHAT IS CHECKED, and it is deliberately only this: the sequence of risk
classes down a tier never improves and then worsens.  Order WITHIN a class is
a judgement call about what unblocks more, and no machine should pretend to
know it.

A row whose text names no class is not a work item (the FFI row, "carried,
not counted").  Those are skipped for ordering but REPORTED, so an item
cannot dodge the check by omitting its class.

SECOND CHECK — COVERAGE: every live postulate in agda/src is named by some
row.  PROOF-STATE.md has always asserted this ("every one of them appears in
exactly one tier below"), and nothing enforced it, so a postulate could be
added and never scheduled — invisible debt of exactly the kind the wiring law
exists to prevent, one level up.  `make postulates` is the authority for what
exists; this check is the join.

The roadmap's own shorthand is honoured, because forbidding it would make the
file worse to read: `{a,b}` brace expansion, `*` globs, and a leading-dash
suffix (`-nestRec` after `concatDrain-nodry-loop` in the same row) all count
as naming.  Anything else must appear verbatim in backticks.
"""

import argparse
import re
import sys
import pathlib

# worst first — CLAUDE.md's ordering, and the index is the sort key
CLASSES = ["FALSITY", "SHAPE", "VACUITY", "DIFFICULTY", "GRINDABLE"]
CLASS_RE = re.compile(r"\b(" + "|".join(CLASSES) + r")\b")
TIER_RE = re.compile(r"^##\s+Tier\s+(\S+)")
ROW_RE = re.compile(r"^-\s+\*\*(.+?)\*\*")


def parse(path):
    """-> [(tier_name, [(row_label, class_or_None, line_no)])]"""
    tiers = []
    cur = None
    rows = None
    row = None  # (label, lineno, [text chunks])

    def flush_row():
        if row is not None:
            label, lineno, chunks = row
            text = " ".join(chunks)
            m = CLASS_RE.search(text)
            rows.append((label, m.group(1) if m else None, lineno))

    for i, line in enumerate(path.read_text().splitlines(), 1):
        mt = TIER_RE.match(line)
        if mt:
            flush_row()
            row = None
            cur = mt.group(1)
            rows = []
            tiers.append((cur, rows))
            continue
        if cur is None:
            continue
        mr = ROW_RE.match(line)
        if mr:
            flush_row()
            row = (mr.group(1), i, [line])
        elif row is not None:
            if line.startswith("  ") or line.startswith("\t"):
                row[2].append(line)
            elif not line.strip():
                pass  # blank line does not end a row; a new bullet or tier does
            else:
                flush_row()
                row = None
    flush_row()
    return tiers


BACKTICK_RE = re.compile(r"`([^`]+)`")


def roadmap_tokens(path):
    """Every name a row claims, with the roadmap's shorthand expanded."""
    claimed = set()
    for line in path.read_text().splitlines():
        toks = BACKTICK_RE.findall(line)
        full = [t for t in toks if not t.startswith("-")]
        for t in toks:
            if t.startswith("-") and full:
                # suffix shorthand: `-nestRec` after `concatDrain-nodry-loop`
                # means concatDrain-nodry-nestRec
                for f in full:
                    if "-" in f:
                        claimed.add(f.rsplit("-", 1)[0] + t)
                continue
            claimed.add(t)
            # brace expansion: subscribeE-{merge,concat}All-wf
            mb = re.match(r"^(.*)\{([^}]*)\}(.*)$", t)
            if mb:
                for alt in mb.group(2).split(","):
                    claimed.add(mb.group(1) + alt.strip() + mb.group(3))
    return claimed


def covered(name, claimed):
    if name in claimed:
        return True
    # a glob token in the roadmap covers the family it names
    for c in claimed:
        if "*" in c and re.fullmatch(re.escape(c).replace(r"\*", ".*"), name):
            return True
    return False


def check_coverage(path, root, ledger=None):
    """-> list of postulates no row names, or None if the ledger is unavailable."""
    if ledger:
        text = pathlib.Path(ledger).read_text()
    else:
        import subprocess
        try:
            r = subprocess.run(["scripts/check-wiring.py", "--postulates"],
                               cwd=root, capture_output=True, text=True, timeout=180)
        except Exception:
            return None
        if r.returncode != 0:
            return None
        text = r.stdout
    names = [ln.split()[0] for ln in text.splitlines()
             if ".agda:" in ln and not ln.startswith("--")]
    if not names:
        return None
    claimed = roadmap_tokens(path)
    return sorted(n for n in names if not covered(n, claimed))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="roadmap to check (default: PROOF-STATE.md); "
                                  "used by make roadmap-selftest against fixtures")
    ap.add_argument("--ledger", help="file of postulate names to require coverage of, "
                                     "one 'name path.agda:N' per line; selftest only")
    args = ap.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    path = pathlib.Path(args.file) if args.file else root / "PROOF-STATE.md"
    if not path.exists():
        print(f"check-roadmap: {path} not found", file=sys.stderr)
        return 2

    tiers = parse(path)
    if not tiers:
        print("check-roadmap: no '## Tier' sections found — parser or file is wrong",
              file=sys.stderr)
        return 2

    failures = []
    unclassified = []
    for tier, rows in tiers:
        worst = -1  # highest class index seen so far
        worst_label = None
        for label, cls, lineno in rows:
            if cls is None:
                unclassified.append((tier, label, lineno))
                continue
            idx = CLASSES.index(cls)
            if idx < worst:
                failures.append((tier, label, cls, worst_label, CLASSES[worst], lineno))
            else:
                worst, worst_label = idx, label

    for tier, rows in tiers:
        shown = [f"{c or '-'}" for _, c, _ in rows]
        print(f"  Tier {tier}: {' → '.join(shown) if shown else '(no rows)'}")

    if unclassified:
        print("\ncheck-roadmap: rows naming no risk class (skipped for ordering):")
        for tier, label, lineno in unclassified:
            print(f"  Tier {tier}  {path.name}:{lineno}  {label}")

    unscheduled = (check_coverage(path, root, args.ledger)
                   if (args.ledger or not args.file) else None)
    if unscheduled is None and not args.file:
        print("\ncheck-roadmap: WARNING — could not read the postulate ledger, "
              "coverage NOT checked")
    elif unscheduled:
        print(f"\nPOSTULATES NOT ON THE ROADMAP — {len(unscheduled)} live "
              "postulate(s) that no row names:")
        for n in unscheduled:
            print(f"  {n}")
        print("\nEvery live postulate appears in exactly one tier, by name. Add a row,")
        print("or name it in an existing family row. The roadmap's shorthand counts:")
        print("  `{a,b}` brace expansion, `readme-*` globs, and `-suffix` after a")
        print("  sibling in the same row. Anything else must appear verbatim in backticks.")
        failures.append(None)

    order_failures = [f for f in failures if f is not None]
    if order_failures:
        print("\nROADMAP OUT OF ORDER — every tier is sorted riskiest-class-first.")
        print("Classes, worst first: " + ", ".join(CLASSES))
        for tier, label, cls, prev_label, prev_cls, lineno in order_failures:
            print(f"\n  Tier {tier}  {path.name}:{lineno}")
            print(f"    {label} is {cls}")
            print(f"    but it sits BELOW {prev_label}, which is {prev_cls}")
            print(f"    → move it above the first {prev_cls} row in this tier")
        print("\nOrder WITHIN a class is a judgement call and is not checked.")

    if failures:
        return 1

    print("\ncheck-roadmap: every tier sorted riskiest-class-first"
          + ("" if unscheduled is None else "; every live postulate is on the roadmap"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
