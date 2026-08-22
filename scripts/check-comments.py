#!/usr/bin/env python3
"""Hold every comment in `agda/src` and `agda/evidence` to the source-comment law.

A source header is where the roadmap's character budget SENDS research: the
hygiene rule "research lives in source comments" makes this file the
destination for everything evicted from PROOF-STATE.  That is the whole reason
the four checks below are shaped the way they are, and it rules out the obvious
design.  A flat per-block ceiling would budget the destination, and then a
finding with nowhere to go does not move — it gets deleted.  Deleting a real
finding to satisfy a length check is strictly worse than the verbosity it cures.

So the law charges EXPLAINING and leaves EVIDENCE free, which is the same split
the roadmap's row budget already uses for names.  Four checks:

FIRST CHECK — DATES: no calendar date appears in any comment, anywhere in
either tree.  Same ruling as CLAUDE.md, PROOF-STATE.md and `docs/`, arrived at
from the other side: a receipt's content is its COVERAGE STATEMENT — which
shapes were reached and which were not — and that statement is re-runnable.
The date was supposed to say "as good as the code being unmoved since", and
nobody has ever checked one; meanwhile it goes stale in silence, which is the
precise failure CLAUDE.md bans line numbers for.

What the date really buys is enforcement of the check below it.  Purely
historical prose arrives WITH a timestamp attached, because the writer knows
they are recording a change rather than a fact — "corrected <date>", "ANSWERED
<date>", "landed <date>", "moved here from the walk face when …".  A date is
therefore the cheapest machine-visible tell for history, and banning it finds
most of the history for free.

SECOND CHECK — HISTORY: a fixed list of markers is refused by name.  The
distinction that decides the list is not importance, it is SUBJECT.  A durable
marker states something true about the STATEMENT — `PROBED` (coverage),
`DEAD ROUTE` (a route that cannot work), `REFUTED` (a machine-checked witness),
`RECOVERY` (where deleted apparatus went).  A historical marker states what
HAPPENED TO THIS DECLARATION — it was split, restated, sealed, discharged,
measured at some wall-clock.  That is git's subject, and git is better at it:
`git log -S<name>` finds it, and it cannot rot, because it is not maintained.
`PROBED-HISTORICAL` is on the list and indicts itself.

The markers are only refused in MARKER POSITION — flush left, optionally after
a warning glyph.  An INDENTED line is a continuation and exempt, and ordinary
prose saying a postulate was discharged is prose; this check must not reach
into either.

AND THE LIST IS SHORT ON PURPOSE, because the census that built it found the
marker WORD does not separate history from fact — the DATE does.  `SEALED
<date>.  This was a POSTULATE the wet spine consumed …` is history; `SEALED,
and this is not optional: … is the ONLY …` is the load-bearing reason the seal
may not be removed.  Same word, and every dated instance was history while
every undated one was a durable rationale or a section header (`SPLIT LEMMAS`,
`FRESHNESS OF THE NODE TABLE`, `ASSEMBLY (…)`).  So the ambiguous words are
left off this list entirely and the check above catches their historical uses
for free, which is the sharpest evidence there is that these two checks are one
check wearing two hats.  What survives here is the markers that are historical
BY DEFINITION, whatever follows them: a statement was restated, a `-core` was
converted, apparatus was deleted, a wall-clock was measured.

THIRD CHECK — SHAPE: the evidence sections of a block sit at its END, in the
order REFUTED / DEAD ROUTE, then PROBED, then RECOVERY.  This is the check that
actually makes a long header readable, and it is nearly free — measured at the
sweep that introduced it, 31 blocks of 2357 violated it, and they were the same
blocks the rule exists for: the 480-, 241- and 163-line essays.  A reader
skimming for "is this route dead?" gets a landmark instead of a search.

It also DEFINES the explanation, which is what makes the fourth check possible
at all: everything before the first evidence marker.  Without a fixed place for
the evidence there is no principled way to say which characters are being
charged, and a budget nobody can predict gets satisfied by deleting whatever is
nearest the bottom.

A consequence worth stating, because it changes how one sentence gets written:
a marker is a LEDGER ENTRY, not a way of emphasising a paragraph.  Prose that
wants to mention a refutation in passing names the module in backticks; the
`REFUTED:` marker is reserved for the ledger at the foot of the block.

FOURTH CHECK — EXPLANATION BUDGET: the prose before the first evidence marker
is held to a character budget, with any line carrying a git sha free.  The
distribution says this is a scalpel rather than a hammer: the median
explanation is under 200 characters and the p90 is under a thousand, so the
budget touches under two percent of blocks and every one of them is an essay
that grew a paragraph at a time.  Nothing evidential is ever what has
to give, because none of it is charged.
"""

import argparse
import pathlib
import re
import sys

# The two trees the law covers.  Both are claimed and gated; `evidence` is
# included because a probe's header is a receipt like any other and decays the
# same way.
DEFAULT_DIRS = ["agda/src", "agda/evidence"]

# Any ISO-ish or spelled date.  Kept deliberately identical in spirit to the
# roadmap checker's: one scan, one law, two jurisdictions.
DATE_RE = re.compile(
    r"\b(?:"
    r"20[0-9]{2}-[0-9]{2}-[0-9]{2}"
    r"|[0-9]{1,2}/[0-9]{1,2}/20[0-9]{2}"
    r"|(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)[a-z]*"
    r"\.?\s+[0-9]{1,2},?\s+20[0-9]{2}"
    r"|[0-9]{1,2}\s+(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Sept|Oct|Nov|Dec)"
    r"[a-z]*\.?\s+20[0-9]{2}"
    r")\b"
)

# The four markers whose subject is the STATEMENT.  Order here IS the mandated
# order in a block's tail; `DEAD ROUTE` shares a rank with `REFUTED` because
# both answer "what has been ruled out".
DURABLE = [("REFUTED", 0), ("DEAD ROUTE", 0), ("PROBED", 1), ("RECOVERY", 2)]
DURABLE_RE = re.compile(
    r"^(?:⚠\s*)?(REFUTED|DEAD ROUTE|PROBED|RECOVERY)\b(?!-)"
)

# Markers whose subject is what HAPPENED TO THIS DECLARATION.  Refused in
# marker position only.  `ROUTE` is here bare and absent above as `DEAD ROUTE`,
# so the negative lookbehind keeps the durable one out of this list.
HISTORY = [
    # Historical by definition — each says what happened to the DECLARATION.
    "PROBED-HISTORICAL", "RESTATED", "LEAF-ONLY", "DELETED", "DISCHARGED",
    "ASSEMBLED", "LANDED", "RETIRED", "SUPERSEDED", "PREMISE WEAKENED",
    # Receipts whose home is `typecheck-performance-numbers.md`, or the harness,
    # whose every row is `measured-not-rechecked` and may not read as verified.
    "TIMING RECEIPT", "MEASURED", "VERIFIED",
]
# Deliberately NOT here: SEALED, SPLIT, RESOLVED, SETTLED, FRESHNESS, ASSEMBLY.
# Each is used BOTH as history and as a durable section header or rationale, so
# a name-level ban would evict real findings; their dated uses are exactly their
# historical ones, and the date check already has them.
HISTORY_RE = re.compile(
    r"^(?:⚠\s*)?(" + "|".join(re.escape(h) for h in HISTORY) + r")\b"
)

SHA_RE = re.compile(r"\b[0-9a-f]{7,40}\b")

# Set at the measured p99, deliberately, and the percentile is the argument: the
# budget's job is to declare a block OVER-EXPLAINED, not to trim writing.  At
# this figure the check fires on blocks of 80 to 480 lines and leaves a 40-line
# module's front matter — which explains the module rather than a declaration,
# and legitimately runs to a couple of thousand characters — untouched.  Tighten
# it and the first thing to break is that front matter, which is the one kind of
# long comment nobody has ever complained about.
EXPL_BUDGET = 3000


def blocks(path):
    """-> [(first_line_no, [comment text, ...])] — maximal runs of `--` lines.

    Line comments only.  The two trees carry four `{- … -}` openers between
    them and every one is an inline `{- WF -}` tag inside a term, so there is
    no prose to find in one; scanning for them would only add false positives
    from Agda code.
    """
    out, cur, start = [], [], 0
    for n, line in enumerate(path.read_text().splitlines() + [""], 1):
        if line.strip().startswith("--"):
            if not cur:
                start = n
            cur.append(re.sub(r"^\s*--\s?", "", line))
        else:
            if cur:
                out.append((start, cur))
            cur = []
    return out


def first_marker(body):
    """-> index of the block's first evidence marker, or len(body) if none."""
    for i, line in enumerate(body):
        if DURABLE_RE.match(line):
            return i
    return len(body)


def rank(line):
    for name, r in DURABLE:
        if re.match(r"^(?:⚠\s*)?" + re.escape(name) + r"\b(?!-)", line):
            return r
    return None


def audit(files, budget):
    dated, hist, shape, fat = [], [], [], []
    for f in files:
        for start, body in blocks(f):
            for off, line in enumerate(body):
                m = DATE_RE.search(line)
                if m:
                    dated.append((f, start + off, m.group(0)))
                m = HISTORY_RE.match(line)
                if m:
                    hist.append((f, start + off, m.group(1)))

            cut = first_marker(body)

            # THIRD CHECK.  Past the first marker a line may be another
            # marker, a blank, or an INDENTED continuation of one.  Flush-left
            # prose down there is an explanation that has been stranded behind
            # the evidence, which is the shape this check exists to find.
            seen = -1
            stray = 0
            for line in body[cut:]:
                r = rank(line)
                if r is not None:
                    if r < seen:
                        shape.append((f, start, "evidence out of order"))
                        break
                    seen = r
                elif line.strip() and not line.startswith(" "):
                    stray += 1
            else:
                if stray:
                    shape.append((f, start, f"{stray} prose line(s) after the evidence"))

            # FOURTH CHECK.  Charge the explanation; sha-bearing lines are a
            # pointer rather than an explanation, so they are free.
            cost = sum(len(line) for line in body[:cut] if not SHA_RE.search(line))
            if cost > budget:
                fat.append((f, start, cost, len(body)))
    return dated, hist, shape, fat


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", action="append", default=None, metavar="PATH",
                    help="tree to check (repeatable); defaults to "
                         + " and ".join(DEFAULT_DIRS))
    ap.add_argument("--budget", type=int, default=EXPL_BUDGET,
                    help="explanation budget in characters")
    args = ap.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    dirs = [pathlib.Path(d) for d in (args.dir or [root / d for d in DEFAULT_DIRS])]
    files = sorted(p for d in dirs for p in pathlib.Path(d).rglob("*.agda"))
    if not files:
        print(f"comments-check: no .agda files under {', '.join(str(d) for d in dirs)}")
        return 1

    dated, hist, shape, fat = audit(files, args.budget)

    if dated:
        print(f"\nDATED COMMENTS — {len(dated)} line(s) naming a calendar date:")
        for f, lineno, d in dated[:40]:
            print(f"  {f}:{lineno}  {d}")
        if len(dated) > 40:
            print(f"  … and {len(dated) - 40} more")
        print("\nA receipt's content is its COVERAGE — which shapes were reached and")
        print("which were not — and that is re-runnable.  A date beside it is checked")
        print("by nobody and goes stale in silence as the code moves.  Delete it; if")
        print("the line said nothing but when something happened, delete the line.")

    if hist:
        print(f"\nHISTORICAL MARKERS — {len(hist)} line(s) recording what happened:")
        for f, lineno, m in hist[:40]:
            print(f"  {f}:{lineno}  {m}")
        if len(hist) > 40:
            print(f"  … and {len(hist) - 40} more")
        print("\nThese state what happened to the DECLARATION, not what is true of the")
        print("STATEMENT.  That is git's subject: `git log -S<name> --all` finds it and")
        print("it cannot rot there.  Keep PROBED / DEAD ROUTE / REFUTED / RECOVERY,")
        print("which say what was ruled out and what was covered; delete the rest.")

    if shape:
        print(f"\nEVIDENCE OUT OF PLACE — {len(shape)} block(s):")
        for f, lineno, why in shape:
            print(f"  {f}:{lineno}  {why}")
        print("\nA block reads: explanation, then REFUTED / DEAD ROUTE, then PROBED,")
        print("then RECOVERY.  Prose stranded behind the evidence has no landmark in")
        print("front of it, which is what makes a long header unskimmable.  And a")
        print("marker is a LEDGER ENTRY — to mention a refutation mid-paragraph, name")
        print("its module in backticks instead of opening a `REFUTED:` section.")

    if fat:
        print(f"\nEXPLANATIONS OVER BUDGET — {len(fat)} block(s) over {args.budget} chars:")
        for f, lineno, cost, lines in sorted(fat, key=lambda x: -x[2]):
            print(f"  {f}:{lineno}  {cost} chars of prose ({lines}-line block)")
        print("\nOnly the prose BEFORE the first evidence marker is charged, and lines")
        print("carrying a git sha are free — so nothing evidential is ever what has to")
        print("give.  What is over budget is explanation that grew a paragraph at a")
        print("time.  Cut the superseded framing and the corrections-to-corrections;")
        print("what survives is the finding, which is usually a fifth of the words.")

    if dated or hist or shape or fat:
        return 1

    n = len(files)
    print(f"comments-check: {n} file(s), no dated comment, no historical marker, "
          f"evidence last and in order, every explanation within its "
          f"{args.budget}-char budget")
    return 0


if __name__ == "__main__":
    sys.exit(main())
