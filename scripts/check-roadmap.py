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

FOURTH CHECK — DATES: no calendar date appears anywhere, in the roadmap OR
in CLAUDE.md.  The roadmap's first hygiene rule is "stay current: this file
describes the repo's present state and the work ahead, never its history",
and a date is the one violation of it that a machine can see with no
judgement at all.

CLAUDE.md is held to the same rule for a DIFFERENT reason, and it is worth
stating because the two files are not alike.  The roadmap must be current;
CLAUDE.md must be TIMELESS.  A ruling in the file of record is in force
whatever its age — that is what "file of record" means — so a timestamp
beside it adds nothing to its authority, and two rulings that genuinely
conflict get MERGED rather than ordered by date.  Same for the evidence under
a rule: that three of four workers died polling a build is the argument; when
it happened is decoration.  Timing figures have exactly one home and it is
neither of these files.  Every other form of history
here arrives WITH a date attached — a ruling's attribution, a "measured
<date>" receipt, an audit note, a "retired <date>" — because the writer knows
the reader will want to know when, so banning the timestamp bans the genre.
Prose that has gone stale without one still has to be caught by eye; that is
not a reason to catch none of it.

FIFTH CHECK — STALENESS, the coverage check run BACKWARDS: a row may not name
a postulate that is no longer live.  Coverage alone is one-directional, and the
direction it leaves open is the one that has actually bitten: a postulate gets
discharged, its row stays, and the file every session reads FIRST now points at
a real definition.  Two rows once did exactly that.  "Completed items are
DELETED, not marked complete" is the roadmap's own second hygiene rule, and it
was the one rule here that no machine could see.

What makes the reverse direction hard is that the roadmap CITES far more names
than it CLAIMS: a GRINDABLE row earns its class by naming the proven twin that
makes it mechanical, so a row's prose is full of definitions, record fields and
module names, every one of them legitimately not a postulate.  A reverse check
over every backticked token would fire on all of them.

So the reverse direction is checked over ROW HEADS only, and the head's own
syntax says which kind it is.  A head that is NOTHING BUT names — backticks and
separators, `a` / `b`, `c` — is a CLAIM head, and every name in it must be a
live postulate.  A head carrying prose — "`X`'s residue", "`HotLive`'s
preservation leaves", "the `glob-*` family" — names a PARENT rather than a work
item, so its names need only still EXIST in agda/src; that catches the parent
being deleted, which is the failure a descriptive head can have.

The boundary, stated plainly because it is a real gap: a family row schedules
its siblings in the HOOK, and a sibling discharged out from under such a row is
NOT caught.  It cannot be, without marking claims apart from citations in the
prose, and the coverage check needs those hook names to keep counting — narrowing
the forward token set to heads would leave 49 live postulates unscheduled.  The
way to bring a name under this check is to give it a head of its own.

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


# Files whose dates are build failures, checked with the same scan.  The
# roadmap gets all four checks; these get the date check only.  The reasons
# differ by one word and both are in docs/roadmap-check.md: the roadmap must be
# CURRENT, the rules and the tool docs must be TIMELESS.  Globs are expanded at
# use, so a new docs/ page is covered the moment it lands.
DATE_ONLY_FILES = ["CLAUDE.md"]
DATE_ONLY_GLOBS = ["docs/*.md"]


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


def expand(toks):
    """The roadmap's shorthand, expanded over one line's (or head's) tokens.

    Shared by the coverage check and the staleness check on purpose: two copies
    of this would drift, and a drift here reads as a stale row that is not one.
    """
    out = set()
    full = [t for t in toks if not t.startswith("-")]
    for t in toks:
        if t.startswith("-") and full:
            # suffix shorthand: `-nestRec` after `concatDrain-nodry-loop`
            # means concatDrain-nodry-nestRec
            for f in full:
                if "-" in f:
                    out.add(f.rsplit("-", 1)[0] + t)
            continue
        out.add(t)
        # brace expansion: subscribeE-{merge,concat}All-wf
        mb = re.match(r"^(.*)\{([^}]*)\}(.*)$", t)
        if mb:
            for alt in mb.group(2).split(","):
                out.add(mb.group(1) + alt.strip() + mb.group(3))
    return out


def roadmap_tokens(path):
    """Every name a row claims, with the roadmap's shorthand expanded."""
    claimed = set()
    for line in path.read_text().splitlines():
        claimed |= expand(BACKTICK_RE.findall(line))
    return claimed


def covered(name, claimed):
    if name in claimed:
        return True
    # a glob token in the roadmap covers the family it names
    for c in claimed:
        if "*" in c and re.fullmatch(re.escape(c).replace(r"\*", ".*"), name):
            return True
    return False


def live_postulates(root, ledger=None):
    """-> the live-postulate names, or None if the ledger cannot be read."""
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
    return names or None


def check_coverage(path, names):
    """-> list of live postulates no row names."""
    claimed = roadmap_tokens(path)
    return sorted(n for n in names if not covered(n, claimed))


# A declaration in agda/src: a type signature at any indentation, or a data /
# record / module head.  Deliberately generous — its only job is to tell a
# DELETED name from one that is merely no longer a postulate, and being
# generous errs toward silence rather than toward a false stale report.
DECL_RE = re.compile(r"^\s*([^\s:(){}@]+)\s*:(?:\s|$)")
DECL_KW_RE = re.compile(r"\b(?:data|record|module)\s+([^\s({]+)")


def src_decl_names(root):
    names = set()
    for f in sorted((root / "agda" / "src").rglob("*.agda")):
        for line in f.read_text().splitlines():
            line = re.sub(r"--.*$", "", line)
            m = DECL_RE.match(line)
            if m:
                names.add(m.group(1))
            for m in DECL_KW_RE.finditer(line):
                names.add(m.group(1))
    return names


# A head that is nothing but names and separators CLAIMS them; a head carrying
# prose ("`X`'s residue") names a PARENT.  See the docstring's FIFTH CHECK.
HEAD_SEP_RE = re.compile(r"[/,;]|\band\b|\s+")


def is_claim_head(label):
    return HEAD_SEP_RE.sub("", BACKTICK_SPAN_RE.sub("", label)) == ""


def head_groups(label):
    """A head's names as ALTERNATIVE GROUPS: satisfied if ANY member is live.

    Two shorthands make a group larger than one name.  A brace form contributes
    one group per alternative — all of them must be live, since the row is
    claiming the whole family.  A leading-dash SUFFIX is the opposite: the
    roadmap means it against a sibling in the same head, and which sibling is
    left to the reader, so every reading is offered and one live reading
    satisfies it.  The nearest preceding sibling is the one reported when none
    does, because that is the reading the roadmap's own shorthand documents.
    """
    toks = BACKTICK_RE.findall(label)
    groups = []
    seen_full = []
    for t in toks:
        if t.startswith("-") and seen_full:
            cands = [f.rsplit("-", 1)[0] + t for f in reversed(seen_full) if "-" in f]
            if cands:
                groups.append(cands)
            continue
        seen_full.append(t)
        mb = re.match(r"^(.*)\{([^}]*)\}(.*)$", t)
        if mb:
            for alt in mb.group(2).split(","):
                groups.append([mb.group(1) + alt.strip() + mb.group(3)])
            continue
        groups.append([t])
    return groups


def check_stale(tiers, live, srcnames):
    """-> (discharged, vanished, gone_parents) — rows naming what is no longer live.

    `discharged` and `vanished` split a CLAIM head's dead names by what became of
    them, because the two want different repairs and the message should say which:
    a name still declared in agda/src was DISCHARGED (delete the row), a name gone
    from agda/src entirely was DELETED (delete the row, and the work it named is
    not owed).  `gone_parents` is the descriptive-head case.
    """
    discharged, vanished, gone_parents = [], [], []
    for tier, rows in tiers:
        for label, _cls, lineno, _cost in rows:
            if not BACKTICK_RE.search(label):
                continue
            claim = is_claim_head(label)
            for group in head_groups(label):
                if any(any(covered(l, {g}) for l in live) for g in group):
                    continue
                name = group[0]
                if claim:
                    (discharged if any(g in srcnames for g in group)
                     else vanished).append((tier, lineno, label, name))
                elif not any(g in srcnames for g in group):
                    gone_parents.append((tier, lineno, label, name))
    return discharged, vanished, gone_parents


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="roadmap to check (default: PROOF-STATE.md); "
                                  "used by make roadmap-selftest against fixtures")
    ap.add_argument("--ledger", help="file of postulate names to require coverage of, "
                                     "one 'name path.agda:N' per line; selftest only")
    ap.add_argument("--src-names", help="file of names declared in agda/src, one "
                                       "per line, standing in for a scan of the "
                                       "tree; selftest only")
    ap.add_argument("--dates-only", action="append", default=None, metavar="PATH",
                    help="also refuse dates in PATH (date check only, no rows). "
                         "Defaults to CLAUDE.md; repeatable; selftest passes fixtures.")
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

    live = (live_postulates(root, args.ledger)
            if (args.ledger or not args.file) else None)
    unscheduled = None if live is None else check_coverage(path, live)
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

    stale = None
    if live is not None:
        srcnames = (set(pathlib.Path(args.src_names).read_text().split())
                    if args.src_names else src_decl_names(root))
        discharged, vanished, gone_parents = check_stale(tiers, set(live), srcnames)
        stale = discharged + vanished + gone_parents
        if discharged:
            print(f"\nSTALE ROWS — {len(discharged)} row head(s) naming a postulate "
                  "that has been DISCHARGED:")
            for tier, lineno, label, name in discharged:
                print(f"  Tier {tier}  {path.name}:{lineno}  {name}")
                print(f"    in **{label}**  — still declared in agda/src, "
                      "but no longer a postulate")
            print("\nCompleted items are DELETED, not marked complete — the roadmap's")
            print("own second hygiene rule. Delete the row. If the discharge left a")
            print("residue worth scheduling, give the residue its own row under its")
            print("own name; do not keep the parent's row pointing at a real")
            print("definition, which is what re-aims the next session.")
        if vanished:
            print(f"\nSTALE ROWS — {len(vanished)} row head(s) naming something that "
                  "is NOT IN agda/src at all:")
            for tier, lineno, label, name in vanished:
                print(f"  Tier {tier}  {path.name}:{lineno}  {name}")
                print(f"    in **{label}**")
            print("\nNeither a live postulate nor a declaration: deleted, renamed, or")
            print("misspelled. Delete the row, or fix the name to the one in agda/src.")
        if gone_parents:
            print(f"\nSTALE ROWS — {len(gone_parents)} descriptive head(s) naming a "
                  "parent that no longer exists:")
            for tier, lineno, label, name in gone_parents:
                print(f"  Tier {tier}  {path.name}:{lineno}  {name}")
                print(f"    in **{label}**")
            print("\nA head carrying prose names a PARENT, so it is held only to still")
            print("existing in agda/src. This one does not. Delete the row or rename it.")
        if stale:
            failures.append(None)

    date_targets = [path]
    if args.dates_only is not None:
        date_targets += [pathlib.Path(f) for f in args.dates_only]
    elif not args.file:
        date_targets += [root / f for f in DATE_ONLY_FILES]
        for g in DATE_ONLY_GLOBS:
            date_targets += sorted(root.glob(g))

    dated = [(f, lineno, date, line)
             for f in date_targets if f.exists()
             for lineno, date, line in dated_lines(f)]
    if dated:
        print(f"\nDATED NARRATIVE — {len(dated)} line(s) naming a calendar date:")
        for f, lineno, date, line in dated:
            print(f"  {f.name}:{lineno}  {date}")
            print(f"    {line[:100]}")
        print("\nThe roadmap describes the repo's PRESENT state and the work ahead,")
        print("never its history; CLAUDE.md states rules that are TIMELESS, in force")
        print("whatever their age. A date is the one violation of either a machine can")
        print("see. Move the dated thing to where it belongs: a receipt or a dead")
        print("route goes in the source header of")
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
          f"within its {ROW_BUDGET}-char hook budget; no dated narrative in "
          # named individually up to a handful, then counted -- a report line
          # that grows with docs/ stops being read
          + (" or ".join(f.name for f in date_targets) if len(date_targets) <= 4
             else f"{len(date_targets)} file(s): "
                  + ", ".join(f.name for f in date_targets[:2])
                  + f" and {len(date_targets) - 2} more")
          + ("" if unscheduled is None
             else "; every live postulate is on the roadmap, and every row head "
                  "names one"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
