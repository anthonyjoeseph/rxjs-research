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

THIRD CHECK — LENGTH: a row is name + risk class + hook, and nothing more.
PROOF-STATE.md has always said "one line per item"; the failure mode is not
sloppiness but a HEADER LEAKING UPWARD, one clause at a time.  A finding gets
written here because here is where it is being discussed, and it then sits far
from the postulate someone picks up six weeks later — which is the locality
argument `-- DEAD ROUTE` exists for, running backwards.  Measured 2026-08-20:
rows ranged 128 to 627 characters, and every row over ~250 held mechanism,
receipts, or dated audit narrative that the file's own rules forbid.

The budget is a CHARACTER count, not a line count — a line count is gamed by
rewrapping.  It charges the row's PROSE ONLY: everything in backticks is
subtracted first, because the names are mandatory.  A row must name every
postulate it schedules (a collective phrase is invisible to the coverage check
above, which is how nine abstractions once sat unnamed behind the words "nine
postulated abstractions"), so charging for names would put the two checks in
direct conflict and the length one would win by deleting names.  Under this
rule a family row listing eight leaves costs the same as a single-name row,
and only the explaining costs.

A row naming no risk class is not a work item and is skipped, as it is for
ordering.

FOURTH CHECK — DATES: the file names no calendar date, anywhere.  Its first
hygiene rule is "stay current: this file describes the repo's present state
and the work ahead, never its history", and a date is the one violation of it
that a machine can see with no judgement at all.  Every other form of history
here arrives WITH a date attached — a ruling's attribution, a "measured
<date>" receipt, an audit note, a "retired <date>" — because the writer knows
the reader will want to know when, so banning the timestamp bans the genre.
Prose that has gone stale without one still has to be caught by eye; that is
not a reason to catch none of it.

Where the dated thing belongs instead: a receipt or a dead route goes in the
source header of the postulate it is about, and that is the ONLY place a date is
wanted anywhere in this repo — such a receipt is only as good as the code being
unmoved since, so its age is a signal about the evidence.  A ruling goes in
CLAUDE.md with its attribution and WITHOUT its timestamp (a rule in the file of
record is in force whatever its age); a timing figure goes in
typecheck-performance-numbers.md; the rationale for a gate goes in the gate,
which is this file.
"""

import argparse
import re
import sys
import pathlib

# worst first — CLAUDE.md's ordering, and the index is the sort key
CLASSES = ["FALSITY", "SHAPE", "VACUITY", "DIFFICULTY", "GRINDABLE"]
CLASS_RE = re.compile(r"\b(" + "|".join(CLASSES) + r")\b")
TIER_RE = re.compile(r"^##\s+Tier\s+(\S+)")
# A row STARTS at a bulleted bold open; the label is closed in the JOINED text,
# not on the opening line.  A name list long enough to wrap is exactly the shape
# the tier-3 abstraction rows have, and requiring the close on line one made
# every such row invisible to the sort and length checks while still counting
# for coverage — a row that dodges the check by wrapping.
ROW_START_RE = re.compile(r"^-\s+\*\*")
LABEL_RE = re.compile(r"\*\*(.+?)\*\*")

# Prose characters per row, names free.  Set from a full scan of the file:
# the post-cleanup rows cluster at 77-260 with a clear gap to the next
# inhabitant, and this sits in that gap.  Re-scan before moving it — the GAP
# is what makes a budget safe, not the margin (same rule as AGDA_DEV_BUDGET).
ROW_BUDGET = 280

BACKTICK_SPAN_RE = re.compile(r"`[^`]*`")

# Any ISO-ish or spelled date.  The roadmap has no legitimate use for one.
DATE_RE = re.compile(
    r"\b(?:\d{4}-\d{2}-\d{2}"
    r"|(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{1,2},?\s+\d{4}"
    r"|\d{1,2}\s+(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{4})\b")


def dated_lines(path):
    """-> [(line_no, the matched date, the line)] — history the machine can see."""
    out = []
    for i, line in enumerate(path.read_text().splitlines(), 1):
        m = DATE_RE.search(line)
        if m:
            out.append((i, m.group(0), line.strip()))
    return out


def prose_cost(chunks):
    """Characters a row spends EXPLAINING — every backticked name is free."""
    text = " ".join(c.strip() for c in chunks)
    text = re.sub(r"^-\s+", "", text).replace("**", "")
    return len(re.sub(r"\s+", " ", BACKTICK_SPAN_RE.sub("", text)).strip())


def parse(path):
    """-> [(tier_name, [(row_label, class_or_None, line_no, prose_cost)])]"""
    tiers = []
    cur = None
    rows = None
    row = None  # (lineno, [text chunks])

    def flush_row():
        if row is not None:
            lineno, chunks = row
            text = " ".join(chunks)
            ml = LABEL_RE.search(text)
            label = ml.group(1) if ml else text.strip()[:60]
            m = CLASS_RE.search(text)
            rows.append((label, m.group(1) if m else None, lineno,
                         prose_cost(chunks)))

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
        if ROW_START_RE.match(line):
            flush_row()
            row = (i, [line])
        elif row is not None:
            if line.startswith("  ") or line.startswith("\t"):
                row[1].append(line)
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
    overlong = []
    for tier, rows in tiers:
        worst = -1  # highest class index seen so far
        worst_label = None
        for label, cls, lineno, cost in rows:
            if cls is None:
                unclassified.append((tier, label, lineno))
                continue
            if cost > ROW_BUDGET:
                overlong.append((tier, label, lineno, cost))
            idx = CLASSES.index(cls)
            if idx < worst:
                failures.append((tier, label, cls, worst_label, CLASSES[worst], lineno))
            else:
                worst, worst_label = idx, label

    for tier, rows in tiers:
        shown = [f"{c or '-'}" for _, c, _, _ in rows]
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

    dated = dated_lines(path)
    if dated:
        print(f"\nDATED NARRATIVE — {len(dated)} line(s) naming a calendar date:")
        for lineno, date, line in dated:
            print(f"  {path.name}:{lineno}  {date}")
            print(f"    {line[:100]}")
        print("\nThis file describes the repo's PRESENT state and the work ahead,")
        print("never its history — that is its first hygiene rule, and a date is the")
        print("one violation of it a machine can see. Move the dated thing to where it")
        print("belongs: a probe receipt or a dead route goes in the source header of")
        print("the postulate it is about; a ruling goes in CLAUDE.md, the file of")
        print("record for directives; a gate's rationale goes in the gate. Then delete")
        print("the line here. Git history is the archive.")
        failures.append(None)

    if overlong:
        print(f"\nROWS OVER BUDGET — {len(overlong)} row(s) spend more than "
              f"{ROW_BUDGET} prose characters:")
        for tier, label, lineno, cost in overlong:
            print(f"  Tier {tier}  {path.name}:{lineno}  {cost} chars "
                  f"(+{cost - ROW_BUDGET})  {label}")
        print("\nA row is a NAME, a RISK CLASS, and a HOOK saying where the risk")
        print("lives and which source header holds the full story. Over budget means")
        print("a header leaked upward: mechanism, a per-conjunct inventory, a probe")
        print("receipt, a dead route, an audit note, or dated narrative. Move it into")
        print("the postulate's own header, where the next person to pick that")
        print("postulate up will actually stand, and cut the row back to its line.")
        print("Backticked names are FREE, so shortening is never done by dropping a")
        print("name — every postulate a row schedules must stay named.")
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

    print(f"\ncheck-roadmap: every tier sorted riskiest-class-first; every row "
          f"within its {ROW_BUDGET}-char hook budget; no dated narrative"
          + ("" if unscheduled is None else "; every live postulate is on the roadmap"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
