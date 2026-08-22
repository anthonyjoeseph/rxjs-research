# `make comments-check` — the source-comment law

Holds every line comment in `agda/src` and `agda/evidence` to six checks. Run
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

## The eight checks

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

`PROBED-HISTORICAL` on that list once CONTRADICTED `make evidence-check`,
which demanded exactly that spelling on a receipt whose statement had been
proven — so the one marker E3 required at the moment of discharge was one this
check refused to let anyone write. It was resolved in E3's favour of deleting
rather than dating: a receipt has one legal tense, and on discharge it goes,
its recoverable apparatus becoming a `RECOVERY:` pointer. Do not re-admit the
spelling to make a stale receipt legal; delete the receipt.

**3 — Shape.** A block's evidence sits at its end, in the order `REFUTED` /
`DEAD ROUTE` / `TWIN`, then `PROBED`, then `RECOVERY`. Rank one is *what is
ruled out and what the route is*, rank two *what was covered*, rank three
*where deleted apparatus went*. Past the first marker a line may
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

**4 — References resolve.** Every section except `DEAD ROUTE` names an object
that can be deleted, so its disappearance is a build failure. This is the same
law `make evidence-check` puts on a probe's `-- TARGET:`, arriving from the
header's side — and the two close a loop: E2 expires a probe when its target is
discharged, and this catches the receipt left pointing at the probe it just
deleted. That gap is one CLAUDE.md already names, at ten surviving receipts
against ninety-eight deleted probe files.

| section | referent | resolved against |
| --- | --- | --- |
| `TWIN:` | a **proven** definition | declared in `agda/src` **and not in the postulate ledger** |
| `REFUTED:` | a refutation, live or spent | declared in `agda/evidence/refuted`, **or a git sha** |
| `PROBED:` | a probe, live or spent | a module under `agda/evidence/probed`, **or a git sha** |
| `RECOVERY:` | a commit | `git cat-file`, or a `git log … agda/…` form |
| `DEAD ROUTE:` | *nothing* | not validated |

**A reference is BACKTICKED or DOTTED, and that is a rule about writing the
line rather than a parsing convenience.** English prose is full of words this
tree happens to declare — `all`, `map`, `init` — so a scan over bare words
resolves by accident and reports a healthy reference where there is none.

`TWIN:` is the sharp one. CLAUDE.md's *"EARNING THE CLASS: NAME THE
PRECEDENT"* demanded a GRINDABLE row name its worked instance, and nothing
checked it. **A twin that is itself still a postulate means the class is
wrong** — the route has not been walked, so the row is DIFFICULTY. That is a
mis-classification caught mechanically.

`REFUTED:` takes a sha for the same reason, and the reason is a rule rather
than a convenience: a refutation dies when `src` can no longer STATE it, and
deleting it then is *correct* — `src` must not keep machinery alive whose only
purpose is making a dead route expressible, measured once at seven live
definitions held up by six refutations. Demanding a live declaration would
therefore demand the tree keep exactly what the deletion rule removes.

`PROBED:` cannot demand a *live* probe, because a probe expiring with its
target is correct and expected; "the probe is deleted" is a normal state and
the receipt is all that survives. So the sha is the whole recovery route, and
requiring it is what makes CLAUDE.md's `git log -S` rule work rather than
aspire to.

`--no-refs` skips this pass. Fixtures outside the real trees cannot be judged
by it.

**5 — Say it once.** An explanation may not name the subject of a section the
same block already carries: no "probe" above a `PROBED`, no "refutation" above
a `REFUTED`, no "dead end" above a `DEAD ROUTE`, no `git show` above a
`RECOVERY`. The prose copy is spending charged characters on what the free part
says, and saying it worse — the section resolves and the sentence does not.

The reason it is a *check* and not a style note is **drift**: the paragraph ages
while the section stays live, so a block ends up carrying a refutation it no
longer has beside a receipt that contradicts it, and nothing marks which
sentence is current.

**It fires only when the block ACTUALLY HAS that section**, which is what keeps
it free of false positives — the duplication is then structural rather than a
judgement about the writing, and prose naming a probe in a block with no
`PROBED` section is the only place that fact could live. Marker lines and their
indented continuations are not explanation, so a section whose own text names
its own subject cannot fire against itself. At the sweep that introduced it,
2 blocks of 2357.

**6 — Explanation budget.** The prose before the first evidence marker, with
sha-bearing lines free. Nothing evidential is ever what has to give.

**7 — Line numbers.** No comment cites a line, in any of three forms:
`Module.agda:414`, the extensionless `Wet:514`, or the prose `line 1920`. The
rule is CLAUDE.md's own, arriving in the source tree: a stale *name* fails a
`grep` loudly, while a stale line number **resolves**, points at unrelated
code, and is believed.

The census that added the check measured how far gone it already was. Of the
36 `file:line` citations, **ten pointed past the end of the file they named** —
`Wet.agda:4125` in a 188-line file, because the module had been split — and the
in-range ones had drifted onto whatever was under them, `Subscribe-Face.agda:1760`
being cited eight times and landing on `(proj₁ (proj₂ CD)))`. A further 91 used
the extensionless form. Not one of the surrounding findings had stopped being
true, which is the whole argument: the citation is the only part that rotted,
and deleting it cost nothing, because **every one of those sites already named
the declaration in backticks beside the number.**

The check is deliberately blind to whether a number happens to be right today.
A correct line number is a decay clock that has not gone off; policing
correctness would mean re-validating every citation on every edit to every
cited file, which is the maintenance burden that produced the rot.

**The extensionless form is why the prefix must be a real module basename.** A
blanket `Word:digits` pattern cannot have this form, because `Killed:9` is a
signal and `V = 4` is a numeral — and a check that calls those line numbers is
a check people learn to route around. So the pattern is built from the `.agda`
stems in the two trees at run time: it fires on `Wet` because `Wet.agda` is
there, and stays silent on anything that is not a module. That also makes it
self-maintaining, the same way the postulate-twin fixture is.

**8 — Obscured markers.** A marker doubled into the comment text —
`-- -- RECOVERY:` — is a finding, and it is the one check here that exists
because of the *other* checks. `blocks` strips exactly one `--` from a comment
line, which is correct, so a second one leaves the marker word inside the text:
the ordering rule reads it as prose and lets it stand mid-block, and the
reference pass never validates the sha it names. It is a marker that is
invisible to every checker in this repo while reading, to a human, exactly like
one that is not.

Three were live in `agda/src` when the check was written, every one a
`RECOVERY` naming a sha nothing resolved, and two of them in the file whose
header the campaign was actively working in. `make evidence-check` had two more
of its own, in the `PROBED` spelling, plus a third that trailed a parenthetical
instead of ending in a colon.

**The doubled form is reported rather than admitted, and that is the design.**
Loosening the marker pattern to accept it would make it *legal*, and a marker's
whole job is to be the one shape a reader and a machine agree on. The same
reasoning runs through E3's near-miss half in `make evidence-check`: report the
spelling, keep the canon narrow.

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
| echoes | delete the mention; the ledger below already carries it, resolvably. |
| shape | move the evidence to the foot of the block, in order. If the stranded prose is superseded framing, it goes rather than moves. |
| references | resolve it, or demote the section to `DEAD ROUTE:`, which names nothing and is not validated. A `REFUTED:` used as *emphasis* rather than as a ledger entry is the common case — reword it to name the module in backticks mid-prose. |
| line numbers | delete the number and keep the name. Every site the census found already had one in backticks; where a module is worth naming, `.Sibling` or `Rx.Module` is the form, and `make find Q='…'` takes names rather than positions. |
| obscured | write ONE `--`. The marker then becomes real evidence, so it must also sit at the foot of its block and its reference must resolve — which is the point: un-doubling it hands the line to two checks that had never seen it. |
| budget | **usually SPLIT, not cut.** A blank line separates blocks, so the ceiling caps one unstructured explanation rather than what a declaration may carry: an essay holding ten findings becomes ten blocks, each with its own heading and ledger, and nothing is deleted. Cut only when one block holds ONE finding and still runs long — then it is superseded framing, and what survives is usually a fifth of the words. |

## The fixtures

`scripts/comments-selftest/<name>/*.agda`, one directory per check, each firing
exactly one.

The two that matter most are the **must-not** direction. `clean` passes only if
six precision properties hold at once — an indented `ASSEMBLED`/`MEASURED` is a
continuation and not a marker, an undated `SEALED:` is rationale and not
history, an indented line after `PROBED` is not stranded prose, a `git show`
pointer is not an explanation, a bare numeral (`V = 4`, `21 against 20`) is not
a citation, and neither is a signal (`Killed:9`) or a non-module prefix. `sha` pins that last one as load-bearing rather
than decorative: its raw comment total is well over budget and its charged total
well under, so dropping the exemption turns it red.

**The postulate-twin assertion is generated at run time**, from the live
ledger, and deliberately: a fixture naming a postulate by hand would go stale
the day that postulate is discharged — and it *would* be, since discharging
them is the point of the campaign — and would then pass while reporting the
check as dead.

`lineref` carries all three citation forms, and asserts each by name — the
path-and-colon one, the prose one, and the extensionless one — so a pattern
narrowed to two of the three cannot pass. `obscured` asserts the marker's NAME
in the output as well as the heading, so a check that fires without saying which
marker it found does not pass.

The eight structural fixtures run with `--no-refs`, so each tests one thing;
`ref-ok` and `ref-bad` are the two that resolve references. `ref-bad` names
something no edit can accidentally make valid: an undeclared name, and a sha of
all `f`s.

Fixtures live under `scripts/`, not `agda/`, so they are never compiled and need
not be valid Agda — and no claim root reaches them, so `make wiring` is not
owed one.

## Only line comments

Both trees carry four `{- … -}` openers between them and every one is an inline
`{- WF -}` tag inside a term. There is no prose to find in one, and scanning for
them would only add false positives from Agda code.
