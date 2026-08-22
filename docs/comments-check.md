# `make comments-check` — the source-comment law

Holds every line comment in `agda/src` and `agda/evidence` to four checks. Run
by both gate paths, in the cheap block, so a violation never costs a build.

```
make comments-check                          the two trees
scripts/check-comments.py --dir <path>       one tree (repeatable)
scripts/check-comments.py --budget <n>       try a different ceiling
make comments-selftest                       prove the checker still fires
```

## Why it charges what it charges

The hygiene rule "research lives in source comments" makes a source header the
**destination** for everything the roadmap's own character budget evicts. That
one fact rules out the design everybody reaches for first. A flat per-block
ceiling budgets the destination — and then a finding with nowhere left to go
does not move, it gets **deleted**. Deleting a real finding to satisfy a length
check is strictly worse than the verbosity it was meant to cure.

So the law charges **explaining** and leaves **evidence** free, which is the
same split the roadmap's row budget already uses for names. Everything below
follows from that.

## The four checks

**1 — Dates.** No calendar date in any comment. A receipt's content is its
*coverage statement* — which shapes were reached, which were not — and coverage
is re-runnable, so the date adds nothing actionable; and since nobody checks
one, it is a stale line number in prose form.

**2 — Historical markers.** A short list refused by name, in marker position
only: flush left, optionally after a warning glyph. Indented lines are
continuations and exempt, and prose that happens to say a postulate was
discharged is prose.

The list is short **because the census that built it found the marker word does
not separate history from fact — the date does.** `SEALED <date>. This was a
POSTULATE the wet spine consumed …` is history; `SEALED, and this is not
optional: … is the ONLY …` is the load-bearing reason the seal may not come
off. Same word. Every dated instance of the ambiguous markers was historical
and every undated one was a durable rationale or a section header (`SPLIT
LEMMAS`, `FRESHNESS OF THE NODE TABLE`, `ASSEMBLY (…)`). So the ambiguous words
are left off the list entirely and check 1 catches their historical uses for
free — which is the sharpest evidence available that these are one check
wearing two hats.

What survives on the list is historical **by definition**, whatever follows:
`PROBED-HISTORICAL`, `RESTATED`, `LEAF-ONLY`, `DELETED`, `DISCHARGED`,
`ASSEMBLED`, `LANDED`, `RETIRED`, `SUPERSEDED`, `PREMISE WEAKENED`, plus the
receipts whose home is elsewhere — `TIMING RECEIPT` and `MEASURED` belong in
`typecheck-performance-numbers.md`, and `VERIFIED` is the false-green word a
harness row may never claim.

Deliberately **not** on it: `SEALED`, `SPLIT`, `RESOLVED`, `SETTLED`,
`FRESHNESS`, `ASSEMBLY`.

**3 — Shape.** A block's evidence sits at its end, in the order `REFUTED` /
`DEAD ROUTE`, then `PROBED`, then `RECOVERY`. Past the first marker a line may
be another marker, a blank, or an indented continuation; flush-left prose down
there is an explanation stranded behind the ledger with no landmark in front of
it.

This is the check that actually makes a long header readable, and it is nearly
free — at the sweep that introduced it, 31 blocks of 2357 violated it, and they
were the same blocks the rule exists for: the 480-, 241- and 163-line essays.

It also **defines the explanation**, which is what makes check 4 possible.
Without a fixed place for the evidence there is no principled way to say which
characters are charged, and an unpredictable budget gets satisfied by deleting
whatever sits nearest the bottom.

Consequence worth knowing before you write the sentence: a marker is a **ledger
entry**, not emphasis. To mention a refutation mid-paragraph, name its module in
backticks; reserve `REFUTED:` for the ledger at the foot of the block.

**4 — Explanation budget.** The prose before the first evidence marker, with
sha-bearing lines free. Nothing evidential is ever what has to give.

## Where the budget comes from, and why it is not tighter

Measured over `agda/src`: 2357 comment blocks, ~1.08M comment characters;
explanation length median **187**, p90 **906**, p99 **3418**, max **13345**.

The ceiling sits at the p99 **deliberately** — its job is to declare a block
*over-explained*, not to trim writing. At that figure it fires on blocks of 80
to 480 lines and leaves a 40-line module's front matter alone. Front matter
explains the module rather than a declaration and legitimately runs to a couple
of thousand characters; tighten the budget and it is the first thing to break,
and it is the one kind of long comment nobody has ever complained about.

For calibration, the count it fires on at each ceiling: 2000 → 73 blocks,
2500 → 52, 3000 → 39, 3500 → 34, 4000 → 26. The flat stretch above 3000 is why
3000 rather than 3500: the blocks between are a cluster, not a boundary.

## What to do when each one fires

| Check | The repair |
| --- | --- |
| dates | delete the date. If the line said nothing but *when*, delete the line. |
| markers | delete the line — `git log -S<name> --all` holds it, unrotting. |
| shape | move the evidence to the foot of the block, in order. If the stranded prose is superseded framing, it goes rather than moves. |
| budget | cut the superseded framing and the corrections-to-corrections. What survives is the finding, usually a fifth of the words. |

## The fixtures

`scripts/comments-selftest/<name>/*.agda`, one directory per check, each firing
exactly one.

The two that matter most are the **must-not** direction. `clean` passes only if
all four precision properties hold at once — an indented `ASSEMBLED`/`MEASURED`
is a continuation and not a marker, an undated `SEALED:` is rationale and not
history, an indented line after `PROBED` is not stranded prose, and a `git show`
pointer is not an explanation. `sha` pins that last one as load-bearing rather
than decorative: its raw comment total is well over budget and its charged total
well under, so dropping the exemption turns it red.

Fixtures live under `scripts/`, not `agda/`, so they are never compiled and need
not be valid Agda — and no claim root reaches them, so `make wiring` is not
owed one.

## Only line comments

Both trees carry four `{- … -}` openers between them and every one is an inline
`{- WF -}` tag inside a term. There is no prose to find in one, and scanning for
them would only add false positives from Agda code.
