#!/usr/bin/env python3
"""PROOF-STATE.md's tiers must be sorted riskiest-class-first.

WHY THIS IS A GATE AND NOT A CONVENTION.  The roadmap's order is the only
thing in the repo that says what to work on next, so a stale sort silently
re-aims the next session — and it re-aims toward the SAFE end, because
grinding is what looks like progress.  Measured 2026-08-20: the anchor
tier's sole SHAPE row sat in the NINTH slot behind four DIFFICULTY rows, and
the session read the tier top-down, picked DIFFICULTY, and was about to fan
the rest out as GRINDABLE — its riskiest row going untouched precisely
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

THIRD CHECK — LENGTH, in two places: a row is name + risk class + hook, and a
tier's PREAMBLE says what the tier IS and what orders it.  The preamble half
exists because the row half has an escape hatch and it was used — see
TIER_BUDGET.  Both are charged the same way, and everything below about the
charge applies to both.

A row is name + risk class + hook, and nothing more.
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
source header of the postulate it is about, and WITHOUT a date — `make
comments-check` refuses one there too, since a receipt's content is its
coverage statement and coverage is re-runnable.  A ruling goes in
CLAUDE.md with its attribution and WITHOUT its timestamp (a rule in the file of
record is in force whatever its age); a timing figure goes in
typecheck-performance-numbers.md; the rationale for a gate goes in the gate,
which is this file.

SIXTH CHECK — THE EVIDENCE FIELD: every classed row carries, directly after its
risk class, a backticked field naming the durable markers its postulates' own
headers carry — `REFUTED, PROBED`, `TWIN`, `REFUTED×2` — or `NO EVIDENCE`.

WHY IT IS MANDATORY WHEN THE HEADER SECTIONS IT SUMMARISES ARE NOT.  A source
header's `TWIN:` is optional-when-absent on purpose: requiring one would produce
filler, and a filler `TWIN:` is worse than none because it earns a class the row
has not earned.  That argument turns on the section being AUTHORED.  This field
is DERIVED — recomputed from the headers on every run — so a mandatory field
cannot be filled with anything, and the blank is the point rather than a defect.
A row reading `DIFFICULTY, NO EVIDENCE` says nobody has instantiated this
statement, refuted a route through it, or found it a twin: the cheapest
unmanaged risk in the repo, and previously invisible, because absence had no
marker to be absent.

AND IT CANNOT ROT, WHICH IS THE ONLY REASON IT MAY LIVE HERE AT ALL.  Moving the
receipts THEMSELVES into the roadmap would duplicate content, and duplicated
content drifts — the failure that emptied this repo's memory directory, where
three of six notes had aged silently past the change that invalidated them.  A
count is not a copy: it is a function of the headers, so the check recomputes it
and fails on any disagreement.  `make roadmap-evidence` writes it, and nobody
types it.

THE FIELD IS BACKTICKED, AND THAT IS LOAD-BEARING TWICE.  `prose_cost` subtracts
backticked spans, so a mandatory field on every row costs two charged characters
— the comma and the space — instead of pushing six rows past ROW_BUDGET, where
the budget would win by eating the hooks.  And it is what separates the field
from an ordinary qualifier: a row already reads `— GRINDABLE, large:`, and
`large` is bare, so it is never read as evidence and never overwritten.

NO AGGREGATES.  A per-tier or whole-file total was considered and rejected: the
per-row blank carries the whole signal, and a total is a number someone has to
keep true for no decision it changes.

SEVENTH CHECK — AN UNEARNED GRINDABLE: a GRINDABLE row whose postulates carry no
`TWIN` fails.  This mechanises a rule that was already stated and already being
broken -- GRINDABLE means "here is the worked instance", and absent one the row
is DIFFICULTY.  Ten of twelve GRINDABLE rows named no twin when this was
written, several of them naming a precedent in ROW PROSE, which resolves
nowhere and is exactly the unchecked claim the class exists to prevent.  `TWIN`
is the marker `make comments-check` refuses when its referent is itself still a
postulate, so requiring it is what makes the precedent a WALKED route rather
than a believed one.  It is checkable only now, because it needs the field
above.

EIGHTH CHECK — AN UNEVIDENCED DIFFICULTY: a DIFFICULTY row whose postulates
carry no durable marker at all fails.  Same mechanisation one class up
(Anthony: "mechanically outlaw a 'difficulty' or 'grindable' row with no
evidence"): "true and correctly stated" is a claim about receipts exactly as
GRINDABLE's is, and CLAUDE.md already rules that absent one the row is SHAPE
if the gap is written down and FALSITY if nothing is.  DIFFICULTY is the class
with no floor under it and the one that reads as safe, so it is where an
unexamined row lands by gravity -- which is why the blank fires here and stays
legal on FALSITY, SHAPE and VACUITY, the classes that CLAIM nothing.
"""

import argparse
import importlib.util
import textwrap
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

# Prose characters per TIER PREAMBLE, names free — the same charge as a row,
# applied to the section text a row is not.  A per-row budget alone leaves the
# obvious escape open, and it was taken: with rows held to a line, one tier's
# preamble reached 4387 characters while its four rows were all inside 280,
# holding a deleted face's refutation history, a superseded predecessor's
# deletion story, and the research for a currency swap that was already
# written into the source header it belongs in.  Both hygiene rules it broke
# are the file's own — "stay current" and "research lives in source comments"
# — and neither is visible to a check that only ever looks at bullets.
#
# Set from a scan after that cleanup: the three preambles sit at 86, 477 and
# 620, and this sits in the open space above them.  Re-scan before moving it;
# the GAP is what makes a budget safe, not the margin.
TIER_BUDGET = 900

# THE TIER'S BIG-PICTURE ROADMAP — the section that says what to work on.
# Rows are the LEDGER, sorted by class so nothing hides; the roadmap is the
# SCHEDULE, and the two answer different questions.  A ledger sorted
# riskiest-first names the next row but not the next PIECE OF WORK: risk is a
# property of one statement, while the work is usually a GROUP of them that
# stand or fall together, and taking the top row over and over walks the group
# in an order nobody chose.  So a tier carries exactly three legs, ranked
# riskiest-first, each free to cut across the classes where a group is the
# better unit and to fall back on the classes where it is not.
#
# EXACTLY THREE, and the bound is what makes it a plan rather than a wish
# list: three is short enough that writing a fourth forces a judgement about
# which of the three it displaces.  The one exemption is arithmetic — a tier
# with fewer than three live postulates cannot name three legs, so it names
# one per postulate.
ROADMAP_RE = re.compile(r"^###\s+Big picture tier roadmap\s*$")
SUBHEAD_RE = re.compile(r"^###\s+\S")
LEGS_WANTED = 3

# Prose per LEG, names free.  Deliberately far above ROW_BUDGET: a row says
# WHERE the risk lives and defers the story to a header, while a leg has to
# carry its own reasoning -- which postulates it groups and why they are one
# piece of work -- and there is no header for a group.
LEG_BUDGET = 700

BACKTICK_SPAN_RE = re.compile(r"`[^`]*`")

# Any ISO-ish or spelled date.  The roadmap has no legitimate use for one.
DATE_RE = re.compile(
    r"\b(?:\d{4}-\d{2}-\d{2}"
    r"|(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{1,2},?\s+\d{4}"
    r"|\d{1,2}\s+(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)[a-z]*\s+\d{4})\b")


# Files whose dates are build failures, checked with the same scan.  The
# roadmap gets all four checks; these get the date check only.  The reasons
# differ by one word and both are in docs/roadmap-check.md: the roadmap must be
# CURRENT, the rules and the tool docs must be TIMELESS.  EVIDENCE.md is here
# for the same reason as CLAUDE.md and not as an afterthought: it STATES RULES,
# and it spent its previous life as REFUTATION.md carrying two timestamps that
# nothing checked -- which is the failure this scan is about.  Globs are expanded at
# use, so a new docs/ page is covered the moment it lands.
DATE_ONLY_FILES = ["CLAUDE.md", "EVIDENCE.md"]
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
    """-> [(tier_name, [(row_label, class_or_None, line_no, prose_cost)], pre, legs)]

    `legs` is [(label, line_no, prose_cost)] for the tier's BIG PICTURE
    ROADMAP -- the bullets under that heading, which are legs and not rows and
    so are held to their own budget and their own count.

    `pre` is (first_lineno, prose_cost) for the tier's PREAMBLE — every line in
    the section that is not row text.  It is collected HERE, rather than by a
    separate scan, because only this loop knows which lines are row
    continuations: a wrapped row's second line is indented and carries no
    bullet, so any independent scan reads it as preamble and reports a number
    several times the truth.
    """
    tiers = []
    cur = None
    rows = None
    pre = None  # [lineno_or_None, [text chunks]]
    row = None  # (lineno, [text chunks])
    legs = None      # [(lineno, [text chunks])] for the roadmap subsection
    in_roadmap = False

    def flush_pre():
        if pre is not None and pre[1]:
            return (pre[0], prose_cost(pre[1]))
        return (None, 0)

    def flush_row():
        if row is not None:
            lineno, chunks = row
            text = " ".join(chunks)
            ml = LABEL_RE.search(text)
            label = ml.group(1) if ml else text.strip()[:60]
            if in_roadmap:
                legs.append((label, lineno, prose_cost(chunks)))
                return
            m = CLASS_RE.search(text)
            rows.append((label, m.group(1) if m else None, lineno,
                         prose_cost(chunks)))

    for i, line in enumerate(path.read_text().splitlines(), 1):
        mt = TIER_RE.match(line)
        if mt:
            flush_row()
            if cur is not None:
                tiers[-1] = (tiers[-1][0], tiers[-1][1], flush_pre(), legs)
            row = None
            in_roadmap = False
            cur = mt.group(1)
            rows = []
            legs = []
            pre = [None, []]
            tiers.append((cur, rows, (None, 0), legs))
            continue
        if cur is None:
            continue
        if SUBHEAD_RE.match(line):
            # a subheading OPENS a subsection and is not preamble.  Bullets
            # under the roadmap heading are LEGS; bullets under any other
            # subheading -- and under none -- are ROWS, so the ledger closes the
            # roadmap by starting, and the roadmap may sit at the top of the
            # tier where a schedule belongs.
            flush_row()
            row = None
            in_roadmap = bool(ROADMAP_RE.match(line))
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
                if line.strip():
                    if pre[0] is None:
                        pre[0] = i
                    pre[1].append(line)
        elif line.strip():
            if pre[0] is None:
                pre[0] = i
            pre[1].append(line)
    flush_row()
    if cur is not None:
        tiers[-1] = (tiers[-1][0], tiers[-1][1], flush_pre(), legs)
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
    for tier, rows, _pre, _legs in tiers:
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


# ── THE EVIDENCE FIELD ────────────────────────────────────────────────
# The five durable markers, in the order a header must carry them.  This
# list is the SAME vocabulary `make comments-check` validates, and the
# order is that check's rank order, so a row reads in the order its
# header does.
DURABLE_KINDS = ["REFUTED", "DEAD ROUTE", "TWIN", "PROBED", "RECOVERY"]
DURABLE_MARK_RE = re.compile(
    r"^(?:⚠\s*)?(REFUTED|DEAD ROUTE|TWIN|PROBED|RECOVERY)\b(?!-)"
)
NO_EVIDENCE = "NO EVIDENCE"


def receipt_cap():
    """The receipt cap, read from the checker that owns it.

    `make evidence-check` caps receipts on one POSTULATE.  What stays open is
    a ROW, and a row naming both arms of one statement carries both names'
    receipts — so a pair can gather fourteen while neither name ever reaches
    the per-name cap, and the reading that says the row is over-evidenced is
    the one nothing was holding.  Same number, second unit; importing it is
    what stops the two from drifting apart.
    """
    path = pathlib.Path(__file__).with_name("check-evidence.py")
    spec = importlib.util.spec_from_file_location("check_evidence", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod.RECEIPT_CAP

# The field as it appears in a row: a backticked span directly after the
# risk class.  BACKTICKED IS LOAD-BEARING TWICE.  It makes the field free
# under `prose_cost`, so a mandatory field on every row costs two charged
# characters (the comma and the space) instead of thirty; and it is what
# distinguishes the field from an ordinary qualifier -- a row already
# reads `— GRINDABLE, large:`, and `large` is not backticked, so it is
# never mistaken for evidence and never overwritten.
EVID_RE = re.compile(r"—\s*(?:" + "|".join(CLASSES) + r")\b")
FIELD_RE = re.compile(r"\s*,\s*`([^`]*)`")
EVID_TOKEN_RE = re.compile(
    r"^(?:" + NO_EVIDENCE + r"|(?:REFUTED|DEAD ROUTE|TWIN|PROBED|RECOVERY)"
    r"(?:×\d+)?(?:,\s*(?:REFUTED|DEAD ROUTE|TWIN|PROBED|RECOVERY)(?:×\d+)?)*)$"
)


def census(root, names, fixture=None):
    """-> {postulate name: {marker kind: count}} read from agda/src headers.

    A block is associated with EVERY declaration that follows it until the
    next comment run or a line that is neither a declaration nor a block
    keyword.  That is how a reader reads a shared `postulate` block, and it
    is why splitting a refuted postulate into its own block is what gives it
    its own markers -- the same locality the `-- REFUTED` convention rests
    on, now with something reading it.
    """
    if fixture:
        out = {n: {} for n in names}
        for ln in pathlib.Path(fixture).read_text().splitlines():
            if not ln.strip() or ln.startswith("#"):
                continue
            name, _, rest = ln.partition(":")
            out[name.strip()] = {
                k.strip().split("×")[0].strip():
                    int(k.split("×")[1]) if "×" in k else 1
                for k in rest.split(",") if k.strip()
            }
        return out

    want = set(names)
    out = {n: {} for n in names}
    src = root / "agda" / "src"
    for path in sorted(src.rglob("*.agda")) if src.exists() else []:
        block, prev_comment = [], False
        for line in path.read_text().splitlines():
            stripped = line.strip()
            if stripped.startswith("--"):
                if not prev_comment:
                    block = []
                block.append(re.sub(r"^\s*--\s?", "", line))
                prev_comment = True
                continue
            prev_comment = False
            md = DECL_RE.match(line)
            if md and md.group(1) in want:
                for b in block:
                    mk = DURABLE_MARK_RE.match(b)
                    if mk:
                        c = out[md.group(1)]
                        c[mk.group(1)] = c.get(mk.group(1), 0) + 1
                continue
            # An INDENTED line is inside the block the header opened -- a
            # sibling declaration, a continuation of one's telescope, a body.
            # Only a construct at column 0 ends the header's reach, which is
            # why splitting a refuted postulate into its own column-0
            # `postulate` block is what gives it its own markers.
            if md or line[:1].isspace() or stripped in (
                    "postulate", "abstract", "private", "mutual", ""):
                continue
            block = []
    return out


def evidence_token(counts):
    """-> the field's text for one row's merged marker counts."""
    parts = []
    for k in DURABLE_KINDS:
        n = counts.get(k, 0)
        if n == 1:
            parts.append(k)
        elif n > 1:
            parts.append(f"{k}×{n}")
    return ", ".join(parts) if parts else NO_EVIDENCE


def row_evidence(label, cen):
    """-> merged counts for every live postulate a row head names."""
    merged = {}

    def add(counts):
        for k, v in counts.items():
            merged[k] = merged.get(k, 0) + v

    for group in head_groups(label):
        for name in group:
            # the roadmap's glob shorthand names a FAMILY, and the coverage
            # check already reads it that way -- so must this, or a family row
            # can never carry evidence however marked its members are
            if "*" in name:
                hit = [n for n in cen if re.fullmatch(
                    re.escape(name).replace(r"\*", ".*"), n)]
                if hit:
                    for n in hit:
                        add(cen[n])
                    break
            elif name in cen:
                add(cen[name])
                break
    return merged


def row_span(lines, lineno):
    """-> (start, end) physical line range of the row beginning at `lineno`."""
    start = lineno - 1
    i = start + 1
    while i < len(lines):
        if ROW_START_RE.match(lines[i]) or TIER_RE.match(lines[i]):
            break
        if not lines[i].strip():
            break
        if not (lines[i].startswith("  ") or lines[i].startswith("\t")):
            break
        i += 1
    return start, i


def unwrap(chunks):
    """Physical row lines joined back into one string.

    A trailing single hyphen is a manual word break (`machine-` / `refuted`),
    so it closes up rather than taking a space -- joining on whitespace alone
    turns every hand-wrapped word in the file into two.
    """
    out = ""
    for c in chunks:
        c = c.strip()
        if not c:
            continue
        if out.endswith("-") and not out.endswith("--") and c[:1].islower():
            out += c
        else:
            out = (out + " " + c) if out else c
    return out


NBSP = "\u00a0"


def rewrap(text, keep=None, width=79):
    """Re-flow one row, continuations indented two.

    `keep` is a span the wrap may not break -- the evidence field contains a
    space (`DEAD ROUTE`) and the field is read back by regex from a single
    string, so a field split across two physical lines reads as ABSENT and the
    check reports a row that is in fact correct.
    """
    if keep and keep in text:
        text = text.replace(keep, keep.replace(" ", NBSP))
    out = textwrap.wrap(text, width=width, subsequent_indent="  ",
                        break_long_words=False, break_on_hyphens=False)
    return [l.replace(NBSP, " ") for l in out]


def evidence_edit(line, want):
    """-> (line with the field set to `want`, field found or None).

    THE ANCHOR IS NOT ALWAYS THE CLASS.  Some heads carry the class INSIDE the
    bold label (`**Real, probed, awaiting proof — DIFFICULTY**`); writing the
    field there would put it inside the row's NAME, where the coverage and
    staleness checks read it as a claimed postulate.  So a class inside the
    label anchors the field after the label's closing `**`.
    """
    mc = EVID_RE.search(line)
    if mc is None:
        return line, None
    ml = LABEL_RE.search(line)
    anchor = ml.end() if (ml and ml.start() < mc.start() < ml.end()) else mc.end()
    mf = FIELD_RE.match(line, anchor)
    have = mf.group(1) if mf else None
    if have is not None and not EVID_TOKEN_RE.match(have.strip()):
        have, end = None, anchor  # an ordinary qualifier, not the field
    else:
        end = mf.end() if mf else anchor
    return line[:anchor] + f", `{want}`" + line[end:], have


def check_evidence(path, tiers, cen):
    """-> ([(tier,label,lineno,have,want)], [(tier,label,lineno)]) — mismatched, missing."""
    lines = path.read_text().splitlines()
    bad, missing = [], []
    for tier, rows, _pre, _legs in tiers:
        for label, cls, lineno, _cost in rows:
            if cls is None:
                continue
            start, end = row_span(lines, lineno)
            want = evidence_token(row_evidence(label, cen))
            _, have = evidence_edit(unwrap(lines[start:end]), want)
            if have is None:
                missing.append((tier, label, lineno))
            elif have.strip() != want:
                bad.append((tier, label, lineno, have.strip(), want))
    return bad, missing


def unearned_grindable(path, tiers, cen):
    """-> [(tier, label, lineno)] — GRINDABLE rows naming no proven twin.

    CLAUDE.md already rules that a row without a named worked instance IS
    DIFFICULTY; until the evidence field existed there was nothing to check it
    against, and the class drifted into the place everything nobody wants to
    think about gets parked -- ten of twelve GRINDABLE rows had no `TWIN:`
    anywhere in their postulates\' headers when this check was written, several
    naming a precedent in ROW PROSE, which no machine resolves.  `TWIN:` is the
    one marker `make comments-check` refuses when its referent is itself still a
    postulate, so requiring it here is what makes "name the precedent" mean a
    walked route rather than a believed one.
    """
    out = []
    for tier, rows, _pre, _legs in tiers:
        for label, cls, lineno, _cost in rows:
            if cls == "GRINDABLE" and "TWIN" not in row_evidence(label, cen):
                out.append((tier, label, lineno))
    return out


def unevidenced_difficulty(path, tiers, cen):
    """-> [(tier, label, lineno)] — DIFFICULTY rows whose postulates carry
    no durable marker at all.

    "True and correctly stated" is earned exactly as GRINDABLE's class is —
    a probe that reached the risky region, a refutation pinning this form, a
    proven mirror — and CLAUDE.md already rules that absent one the row is
    SHAPE if the gap is written down and FALSITY if nothing is.  The blank
    stays legal on the three classes that claim nothing.
    """
    out = []
    for tier, rows, _pre, _legs in tiers:
        for label, cls, lineno, _cost in rows:
            if cls == "DIFFICULTY" and not row_evidence(label, cen):
                out.append((tier, label, lineno))
    return out


def over_probed(path, tiers, cen, cap):
    """-> [(tier, label, lineno, n)] — rows carrying more than `cap` receipts.

    A probe AIMS a grind or REFUTES a statement, and past the cap the receipts
    have stopped deciding anything while the row stays open — so what more
    evidence buys is more evidence to delete on discharge.  The repair is to
    DEFINE something, or to delete the receipts that no longer earn their
    place; splitting the row in two satisfies the count and changes nothing,
    which is the same laundering as merging probe files under the per-name cap.
    Only PROBED is counted: a refutation KILLS a statement rather than
    accumulating against a live one, and the other three markers name a route
    rather than buy coverage.
    """
    out = []
    for tier, rows, _pre, _legs in tiers:
        for label, cls, lineno, _cost in rows:
            if cls is None:
                continue
            n = row_evidence(label, cen).get("PROBED", 0)
            if n > cap:
                out.append((tier, label, lineno, n))
    return out


def fix_evidence(path, tiers, cen):
    """Rewrite every classed row's evidence field from the headers. -> n changed."""
    lines = path.read_text().splitlines()
    changed = 0
    # BOTTOM-UP, because a rewrap changes how many lines a row occupies and
    # every row below it would shift under a top-down pass.
    spans = []
    for _tier, rows, _pre, _legs in tiers:
        for label, cls, lineno, _cost in rows:
            if cls is not None:
                spans.append((lineno, label))
    for lineno, label in sorted(spans, reverse=True):
        start, end = row_span(lines, lineno)
        want = evidence_token(row_evidence(label, cen))
        text, _have = evidence_edit(unwrap(lines[start:end]), want)
        new = rewrap(text, keep=f"`{want}`")
        if new != lines[start:end]:
            lines[start:end] = new
            changed += 1
    if changed:
        path.write_text("\n".join(lines) + "\n")
    return changed



def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", help="roadmap to check (default: PROOF-STATE.md); "
                                  "used by make roadmap-selftest against fixtures")
    ap.add_argument("--ledger", help="file of postulate names to require coverage of, "
                                     "one 'name path.agda:N' per line; selftest only")
    ap.add_argument("--src-names", help="file of names declared in agda/src, one "
                                       "per line, standing in for a scan of the "
                                       "tree; selftest only")
    ap.add_argument("--census", help="file of 'name: MARKER, MARKER×2' lines "
                                     "standing in for a scan of agda/src headers; "
                                     "selftest only")
    ap.add_argument("--fix-evidence", action="store_true",
                    help="rewrite every classed row's evidence field from the "
                         "source headers, then exit (make roadmap-evidence)")
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

    if args.fix_evidence:
        live = live_postulates(root, args.ledger)
        if live is None and not args.census:
            print("check-roadmap: cannot read the postulate ledger — "
                  "the evidence field is DERIVED and cannot be written without it",
                  file=sys.stderr)
            return 2
        cen = census(root, live or [], args.census)
        n = fix_evidence(path, tiers, cen)
        print(f"roadmap-evidence: {n} row(s) rewritten in {path.name}")
        return 0

    failures = []
    unclassified = []
    overlong = []
    fat_tiers = []
    bad_legs = []      # (tier, found, wanted) — the count is wrong
    fat_legs = []      # (tier, label, lineno, cost) — one leg over budget
    for tier, rows, (pre_line, pre_cost), legs in tiers:
        if pre_cost > TIER_BUDGET:
            fat_tiers.append((tier, pre_line, pre_cost))
        # THE COUNT.  Three, unless the tier has fewer postulates than that to
        # plan over -- in which case naming three would mean inventing work.
        want = min(LEGS_WANTED, len(rows))
        if len(legs) != want:
            bad_legs.append((tier, len(legs), want))
        for leg_label, leg_line, leg_cost in legs:
            if leg_cost > LEG_BUDGET:
                fat_legs.append((tier, leg_label, leg_line, leg_cost))
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

    for tier, rows, _pre, _legs in tiers:
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

    if live is not None:
        cen = census(root, live, args.census)
        bad, missing = check_evidence(path, tiers, cen)
        if missing:
            print(f"\nROWS WITH NO EVIDENCE FIELD — {len(missing)}:")
            for tier, label, lineno in missing:
                print(f"  Tier {tier}  {path.name}:{lineno}  {label}")
            print("\nEvery classed row carries a backticked evidence field directly")
            print("after its risk class, naming the durable markers its postulates'")
            print("own headers carry — or `NO EVIDENCE` when they carry none. The")
            print("field is DERIVED, so do not type it: run")
            print("  make roadmap-evidence")
        if bad:
            print(f"\nROWS WHOSE EVIDENCE FIELD IS STALE — {len(bad)}:")
            for tier, label, lineno, have, want in bad:
                print(f"  Tier {tier}  {path.name}:{lineno}  {label}")
                print(f"    row says   `{have}`")
                print(f"    headers say `{want}`")
            print("\nThe headers are the authority — a marker was added, deleted or")
            print("retargeted and the row did not follow. Run  make roadmap-evidence")
        unearned = unearned_grindable(path, tiers, cen)
        if unearned:
            print(f"\nGRINDABLE ROWS THAT NAME NO PROVEN TWIN — {len(unearned)}:")
            for tier, label, lineno in unearned:
                print(f"  Tier {tier}  {path.name}:{lineno}  {label}")
            print("\nGRINDABLE is not 'feels easy', it is 'here is the worked")
            print("instance' — and absent one the row is DIFFICULTY. A precedent")
            print("named in this row's PROSE does not count: it resolves nowhere.")
            print("Put a `TWIN:` section in the postulate's own header naming a")
            print("PROVEN counterpart (comments-check refuses a twin that is itself")
            print("still a postulate), then run  make roadmap-evidence . Or demote")
            print("the row to DIFFICULTY, which is what it is until then.")
        unev = unevidenced_difficulty(path, tiers, cen)
        if unev:
            print(f"\nDIFFICULTY ROWS WITH NO EVIDENCE — {len(unev)}:")
            for tier, label, lineno in unev:
                print(f"  Tier {tier}  {path.name}:{lineno}  {label}")
            print("\n'True and correctly stated' is a claim about EVIDENCE — a")
            print("probe that reached the risky region, a refutation pinning this")
            print("form, or a proven mirror in a `TWIN:` section. Absent one, the")
            print("row is SHAPE if the statement's gap is written down and FALSITY")
            print("if nothing is — that is CLAUDE.md's own rule, mechanised. Put")
            print("the evidence in the postulate's header as a durable marker and")
            print("run  make roadmap-evidence , or raise the class.")
        cap = receipt_cap()
        fat = over_probed(path, tiers, cen, cap)
        if fat:
            print(f"\nROWS OVER THE RECEIPT CAP OF {cap} — {len(fat)}:")
            for tier, label, lineno, n in fat:
                print(f"  Tier {tier}  {path.name}:{lineno}  {label}")
                print(f"    {n} receipts on one open row")
            print("\nA probe AIMS a grind or REFUTES a statement. Past the cap the")
            print("receipts have stopped deciding anything and the row is still")
            print("open, so what more evidence buys is more evidence to delete when")
            print("the statement is discharged. Take the leap: DEFINE something, or")
            print("delete the receipts that no longer earn their place — and never")
            print("split the row, which satisfies the count and changes nothing.")
            print("evidence-check caps one POSTULATE; this caps the open ITEM, which")
            print("is what a row naming two arms of one statement gets past.")
        if missing or bad or unearned or unev or fat:
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

    if bad_legs:
        print(f"\nBIG PICTURE TIER ROADMAP — {len(bad_legs)} tier(s) do not name "
              f"the right number of legs:")
        for tier, found, want in bad_legs:
            print(f"  Tier {tier}  {path.name}  names {found} leg(s), wants {want}")
        print("\nThe roadmap is the SCHEDULE and the rows are the LEDGER. A tier's")
        print("next three legs are what the session actually works, grouped across")
        print("the whole ledger rather than read off the top of it — so the count is")
        print("fixed at three, and drops below three only when the tier has fewer")
        print("live postulates than that to plan over. Fewer than three is a tier")
        print("planning one leg ahead; more is a backlog, and a backlog is what the")
        print("rows already are. Write each leg as  - **<name>** — <reasoning>  under")
        print("a  ### Big picture tier roadmap  heading, riskiest leg first.")
        failures.append(None)

    if fat_legs:
        print(f"\nROADMAP LEGS OVER BUDGET — {len(fat_legs)} leg(s) spend more "
              f"than {LEG_BUDGET} prose characters:")
        for tier, label, lineno, cost in fat_legs:
            print(f"  Tier {tier}  {path.name}:{lineno}  {cost} chars "
                  f"(+{cost - LEG_BUDGET})  {label}")
        print("\nA leg carries its own reasoning, which is why its budget is several")
        print("times a row's: there is no postulate header to send the research to,")
        print("because the subject is a GROUP. But the budget still ends somewhere,")
        print("and past it the leg has stopped saying why this group is next and")
        print("started proving it. Move the argument into the header of the")
        print("postulate it is about, and leave the leg naming the group, the risk")
        print("it retires, and what makes it one unit of work.")
        failures.append(None)

    if fat_tiers:
        print(f"\nTIER PREAMBLES OVER BUDGET — {len(fat_tiers)} preamble(s) spend "
              f"more than {TIER_BUDGET} prose characters:")
        for tier, pre_line, cost in fat_tiers:
            print(f"  Tier {tier}  {path.name}:{pre_line}  {cost} chars "
                  f"(+{cost - TIER_BUDGET})")
        print("\nA tier preamble says what the tier IS — the one statement it")
        print("exports, the doors in and out, and what orders the rows. It is not")
        print("where findings go. Over budget means the same leak the row budget")
        print("catches, arriving in the section text instead of a bullet: refutation")
        print("history, a deletion story, the research behind a design change. Move")
        print("each finding into the header of the postulate or definition it is")
        print("about, and delete what is purely historical — this file describes the")
        print("repo's present state, and git history is the archive.")
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
          f"within its {ROW_BUDGET}-char hook budget; every tier preamble "
          f"within its {TIER_BUDGET}-char budget; every tier's big picture "
          f"roadmap naming its next legs, each within {LEG_BUDGET} chars; "
          f"no dated narrative in "
          # named individually up to a handful, then counted -- a report line
          # that grows with docs/ stops being read
          + (" or ".join(f.name for f in date_targets) if len(date_targets) <= 4
             else f"{len(date_targets)} file(s): "
                  + ", ".join(f.name for f in date_targets[:2])
                  + f" and {len(date_targets) - 2} more")
          + ("" if unscheduled is None
             else "; every live postulate is on the roadmap, and every row head "
                  "names one; every classed row's evidence field matches its "
                  "postulates' own headers, every GRINDABLE row names a "
                  "proven twin, and no DIFFICULTY row stands on none"))
    return 0


if __name__ == "__main__":
    sys.exit(main())
