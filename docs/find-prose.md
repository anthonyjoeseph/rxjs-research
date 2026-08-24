# `make find-prose` — searching FINDINGS, which are not types

```
make find-prose Q='phantom'            every prose block mentioning it
make find-prose Q='never.parks'        Q is a REGEX, and case-blind
make find-prose Q='DEAD ROUTE.*drain'  markers are ordinary text to it
```

`make find` searches the declared TYPE of every statement, which is the right
search when you are about to state a lemma. It is the wrong search, and a
silent one, when the thing you need is a **finding**: a dead route, a coverage
boundary, a ruling and its rationale, a measured trap, a recovery pointer.
Those are prose by construction — a dead route has no `⊥` to state and a
coverage claim has no type — so they live in comment blocks and in the
documents, where `find` cannot reach and `dup-check` cannot police.

## Why not plain grep

Grep finds the line. A finding is a **block** — the forty-line header the line
sits in, whose first half is the argument and whose last is the evidence
ledger. One line out of it is a hit and not an answer, and the reader who gets
a hit without the argument reliably concludes the hit was about something else.

So the unit here is the block, and it is the *same* block
`scripts/check-comments.py` charges a budget to: the parser is imported from
that script rather than copied, so the searcher and the checker cannot drift
about what a block is.

## What it searches, and what it prints

Every comment block in `agda/src` and `agda/evidence`, every paragraph, bullet
and heading of `CLAUDE.md`, `PROOF-STATE.md`, `EVIDENCE.md`,
`typecheck-performance-numbers.md`, and every file in `docs/`.

An agda hit prints the **declaration the block sits above** as a `▸` line. That
is usually the whole answer: a finding is about the thing beneath it, and the
name is what you take back to `make find`.

Documents split on blank lines **and** on top-level bullets and headings, which
is not fussiness — PROOF-STATE is one unbroken run of bullets per tier, so
blank lines alone would return a whole tier for a hit on one row.

## It never fails

A zero-hit search exits 0. The rule this serves says a miss is weak evidence
and two misses on different phrasings are strong, so both outcomes are results
and neither is a build error. Phrase it twice before believing a miss —
this tree's prose is as idiosyncratic as its names.
