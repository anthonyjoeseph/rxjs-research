#!/usr/bin/env python3
"""Hold every comment in `agda/src` and `agda/evidence` to the source-comment law.

A source header is where the roadmap's character budget SENDS research: the
hygiene rule "research lives in source comments" makes this file the
destination for everything evicted from PROOF-STATE.  That is the whole reason
the six checks below are shaped the way they are, and it rules out the obvious
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
# Rank 0 answers "what is ruled out, and what is the route" — a refutation, a
# route that cannot work, a proven counterpart whose clauses correspond.  Rank 1
# is coverage.  Rank 2 is where deleted apparatus went.
DURABLE = [("REFUTED", 0), ("DEAD ROUTE", 0), ("TWIN", 0),
           ("PROBED", 1), ("RECOVERY", 2)]
DURABLE_RE = re.compile(
    r"^(?:⚠\s*)?(REFUTED|DEAD ROUTE|TWIN|PROBED|RECOVERY)\b(?!-)"
)

# The markers whose text names something that can STOP EXISTING.  `DEAD ROUTE`
# is deliberately absent and unvalidated: it has no referent by construction --
# it records that a way of proving something cannot work, and there is no object
# to resolve.  That is exactly why it got a prose convention instead of a check.
VALIDATED = ("TWIN", "REFUTED", "PROBED", "RECOVERY")

# A reference is BACKTICKED or DOTTED, never a bare word, and that is a rule
# about how the line is written rather than a parsing convenience: English prose
# is full of words that happen to be declared names in this tree (`all`, `map`,
# `init`), so a scan over bare words would resolve by accident and report a
# healthy reference where there is none.  Both forms are already how the repo
# writes them.
BACKTICKED = re.compile(r"`([^`]+)`")
DOTTED = re.compile(r"\b((?:[A-Z][A-Za-z0-9-]*\.)+[A-Za-z][A-Za-z0-9'_-]*)")
SHA_TOKEN = re.compile(r"\b[0-9a-f]{7,40}\b")

# A rule line is STRUCTURE, not prose: it separates, it says nothing, and it
# closes a block from the left margin.  Charging it to the explanation would
# tax punctuation, and reading it as prose stranded behind the evidence would
# report every banner-closed block in the tree.
RULE_LINE = re.compile(r"^[-=─━═_*+#.·]{3,}\s*$")
GITLOG = re.compile(r"git log[^`\n]*agda/")


# FIFTH CHECK's vocabulary.  A structured section is a machine-checked
# reference a few lines below, so prose that ALSO names its subject is paying
# charged characters to say what the free part says -- and says it worse, since
# the prose copy is the one nothing resolves and the one that drifts.  Each
# entry fires only when the block ALREADY HAS that section, which is what keeps
# the check free of false positives: the duplication is then structural, not a
# judgement about the writing.
ECHO = {
    "PROBED":     re.compile(r"\bprobe(?:s|d|es)?\b", re.I),
    "REFUTED":    re.compile(r"\brefut(?:ed|es|ation|ations)\b", re.I),
    "DEAD ROUTE": re.compile(r"\bdead (?:route|end)s?\b", re.I),
    "TWIN":       re.compile(r"\btwins?\b", re.I),
    "RECOVERY":   re.compile(r"\bgit show\b", re.I),
}


def ref_tokens(text):
    """-> the names a section REFERS to: backticked spans and dotted paths."""
    out = set()
    for m in BACKTICKED.finditer(text):
        inner = m.group(1).strip()
        out.add(inner)
        out.add(inner.split(".")[-1])
        for w in re.findall(r"[A-Za-z][^\s,;:()]*", inner):
            out.add(w)
            out.add(w.split(".")[-1])
    for m in DOTTED.finditer(text):
        out.add(m.group(1))
        out.add(m.group(1).split(".")[-1])
    return {t for t in out if len(t) > 2}

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


# Deliberately generous, and copied in spirit from the roadmap checker's: its
# only job is to tell a name that EXISTS from one that does not, so erring
# toward finding a declaration errs toward silence rather than a false report.
DECL_RE = re.compile(r"^\s*([^\s:(){}@]+)\s*:(?:\s|$)")
DECL_KW_RE = re.compile(r"\b(?:data|record|module)\s+([^\s({]+)")


def declared_names(tree):
    """-> every name `tree` declares, plus every module path it defines."""
    out = set()
    for f in pathlib.Path(tree).rglob("*.agda"):
        rel = f.relative_to(tree).with_suffix("")
        out.add(str(rel).replace("/", "."))
        for line in f.read_text().splitlines():
            if line.strip().startswith("--"):
                continue
            m = DECL_RE.match(line)
            if m:
                out.add(m.group(1))
            m = DECL_KW_RE.search(line)
            if m:
                out.add(m.group(1).split(".")[-1])
                out.add(m.group(1))
    return out


def live_postulates(root):
    """-> the live-postulate names, or None if the ledger cannot be read."""
    import subprocess
    try:
        r = subprocess.run(["scripts/check-wiring.py", "--postulates"],
                           cwd=root, capture_output=True, text=True, timeout=180)
    except Exception:
        return None
    if r.returncode != 0:
        return None
    names = [ln.split()[0] for ln in r.stdout.splitlines() if ".agda:" in ln]
    return set(names) or None


def real_shas(root, candidates):
    """-> the subset of `candidates` git can actually resolve to an object."""
    import subprocess
    if not candidates:
        return set()
    try:
        r = subprocess.run(["git", "cat-file", "--batch-check"], cwd=root,
                           input="\n".join(sorted(candidates)) + "\n",
                           capture_output=True, text=True, timeout=120)
    except Exception:
        return set(candidates)          # git unavailable: do not invent failures
    good = set()
    for want, line in zip(sorted(candidates), r.stdout.splitlines()):
        if " missing" not in line and " ambiguous" not in line:
            good.add(want)
    return good


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


def sections(body):
    """-> [(offset, kind, text)] — each evidence marker with its continuations."""
    marks = [i for i, l in enumerate(body) if DURABLE_RE.match(l)]
    out = []
    for j, i in enumerate(marks):
        end = marks[j + 1] if j + 1 < len(marks) else len(body)
        kind = DURABLE_RE.match(body[i]).group(1)
        out.append((i, kind, " ".join(body[i:end])))
    return out


def check_refs(refs, root):
    """-> [(file, lineno, kind, why)] for every reference that resolves to
    nothing.  A marker naming something that can STOP EXISTING is only worth
    the line it costs if its disappearance is a build failure -- the same law
    `make evidence-check` already applies to a probe's `-- TARGET:`, arriving
    here from the header's side."""
    src = declared_names(root / "agda/src")
    ref = declared_names(root / "agda/evidence/refuted")
    prb = declared_names(root / "agda/evidence/probed")
    post = live_postulates(root) or set()
    shas = real_shas(root, {t for _, _, _, text in refs
                            for t in SHA_TOKEN.findall(text)})

    bad = []
    for f, lineno, kind, text in refs:
        toks = ref_tokens(text)
        if kind == "TWIN":
            hits = toks & src
            still = hits & post
            if not hits:
                bad.append((f, lineno, kind, "names nothing declared in `agda/src`"))
            elif hits <= still:
                bad.append((f, lineno, kind,
                            "names `" + sorted(still)[0] + "`, which is STILL A "
                            "POSTULATE — a twin that is not proven earns no class"))
        elif kind == "REFUTED":
            # A sha counts here for the same reason it counts for PROBED: a
            # refutation dies when `src` can no longer STATE it, and deleting
            # it then is CORRECT -- `src` must not keep machinery alive whose
            # only purpose is making a dead route expressible.  The receipt is
            # all that survives, so demanding a live declaration would demand
            # that the tree keep the very thing the deletion rule removes.
            if not (toks & ref) and not (set(SHA_TOKEN.findall(text)) & shas):
                bad.append((f, lineno, kind,
                            "names neither a declaration in "
                            "`agda/evidence/refuted` nor the sha holding a "
                            "refutation `src` can no longer state"))
        elif kind == "PROBED":
            if not (toks & prb) and not (set(SHA_TOKEN.findall(text)) & shas):
                bad.append((f, lineno, kind,
                            "names neither a live probe nor the sha holding a "
                            "deleted one"))
        elif kind == "RECOVERY":
            if not (set(SHA_TOKEN.findall(text)) & shas) and not GITLOG.search(text):
                bad.append((f, lineno, kind, "carries no sha git can resolve"))
    return bad


def audit(files, budget):
    dated, hist, shape, fat, refs, echo = [], [], [], [], [], []
    for f in files:
        for start, body in blocks(f):
            for off, line in enumerate(body):
                m = DATE_RE.search(line)
                if m:
                    dated.append((f, start + off, m.group(0)))
                m = HISTORY_RE.match(line)
                if m:
                    hist.append((f, start + off, m.group(1)))

            secs = sections(body)
            for off, kind, text in secs:
                if kind in VALIDATED:
                    refs.append((f, start + off, kind, text))

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
                elif (line.strip() and not line.startswith(" ")
                      and not RULE_LINE.match(line.strip())):
                    stray += 1
            else:
                if stray:
                    shape.append((f, start, f"{stray} prose line(s) after the evidence"))

            # FOURTH CHECK.  Charge the explanation; sha-bearing lines are a
            # pointer rather than an explanation, so they are free.
            cost = sum(len(line) for line in body[:cut]
                       if not SHA_RE.search(line)
                       and not RULE_LINE.match(line.strip()))
            if cost > budget:
                fat.append((f, start, cost, len(body)))

            # FIFTH CHECK.  Say it once.
            expl = " ".join(body[:cut])
            for kind in {k for _, k, _ in secs}:
                pat = ECHO.get(kind)
                if pat is not None:
                    m = pat.search(expl)
                    if m:
                        echo.append((f, start, kind, m.group(0)))
    return dated, hist, shape, fat, refs, echo


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", action="append", default=None, metavar="PATH",
                    help="tree to check (repeatable); defaults to "
                         + " and ".join(DEFAULT_DIRS))
    ap.add_argument("--budget", type=int, default=EXPL_BUDGET,
                    help="explanation budget in characters")
    ap.add_argument("--no-refs", action="store_true",
                    help="skip reference resolution (it reads the real trees, so "
                         "a fixture outside them cannot be judged by it)")
    args = ap.parse_args()

    root = pathlib.Path(__file__).resolve().parent.parent
    dirs = [pathlib.Path(d) for d in (args.dir or [root / d for d in DEFAULT_DIRS])]
    files = sorted(p for d in dirs for p in pathlib.Path(d).rglob("*.agda"))
    if not files:
        print(f"comments-check: no .agda files under {', '.join(str(d) for d in dirs)}")
        return 1

    dated, hist, shape, fat, refs, echo = audit(files, args.budget)
    dangling = [] if args.no_refs else check_refs(refs, root)

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

    if dangling:
        print(f"\nDANGLING REFERENCES — {len(dangling)} marker(s) naming "
              f"something that is not there:")
        for f, lineno, kind, why in dangling:
            print(f"  {f}:{lineno}  {kind} {why}")
        print("\nA marker naming something that can STOP EXISTING is only worth its")
        print("line if the disappearance is a build failure — the same law")
        print("`make evidence-check` puts on a probe's `-- TARGET:`, arriving here")
        print("from the header's side, and closing the loop between them: that check")
        print("expires a probe when its target is discharged, and this one catches")
        print("the receipt left pointing at the probe it just deleted.")
        print("\nWrite the reference BACKTICKED or DOTTED — a bare word is not read as")
        print("one, because English is full of words this tree happens to declare. A")
        print("`TWIN` names a PROVEN definition, which is what earns a GRINDABLE row")
        print("its class; if the twin is still a postulate the class is wrong. A")
        print("`PROBED` receipt for a DELETED probe names the sha holding it — that")
        print("is what makes the `git log -S` recovery rule actually work.")

    if echo:
        print(f"\nEXPLANATION ECHOES ITS OWN LEDGER — {len(echo)} block(s):")
        for f, lineno, kind, word in echo:
            print(f"  {f}:{lineno}  says \"{word}\" above its own {kind} section")
        print("\nThe section is a machine-checked reference a few lines down, so prose")
        print("that also names its subject spends CHARGED characters saying what the")
        print("FREE part already says — and says it worse, since the prose copy is the")
        print("one nothing resolves. It is also how the two halves drift: the paragraph")
        print("ages while the section stays live, and then nothing says which sentence")
        print("is current. Delete the mention and let the ledger carry it.")

    if dated or hist or shape or fat or dangling or echo:
        return 1

    n = len(files)
    print(f"comments-check: {n} file(s), no dated comment, no historical marker, "
          f"evidence last and in order, every reference resolving, no "
          f"explanation echoing its own ledger, every explanation within its "
          f"{args.budget}-char budget")
    return 0


if __name__ == "__main__":
    sys.exit(main())
