# `make notify` — the gate's push notification

`scripts/notify.py` posts a census of the proof's remaining work to
[ntfy.sh](https://ntfy.sh) whenever a gate finishes. A gate is the one moment
the tree is known-good and a commit is next, so it is the only point where the
numbers describe something stable.

## Setting the topic

The topic is an **address, not a configuration value**: anyone who knows it can
subscribe and read every notification. It is therefore kept out of the tree —
`.ntfy-topic` is gitignored — and read from, in order:

1. `$NTFY_TOPIC`
2. `.ntfy-topic` at the repo root

With neither set the script prints the census locally and sends nothing. It
never fails a gate: a network error, a bad topic and a missing topic all exit
zero with a line saying so.

To subscribe, open `https://ntfy.sh/<topic>` in a browser, or install the ntfy
app and add the topic there.

## What it sends

```
Title:  gate GREEN (heavy) - about to commit

Tier 1 is the lowest open — 2 falsity, 14 difficulty, 2 grindable
next up: `subscribeE-nest` (FALSITY)

  tier 1: 2 falsity, 14 difficulty, 2 grindable
  tier 2: 2 falsity, 4 shape, 19 difficulty
  tier 3: 2 vacuity, 1 difficulty

89 live postulate(s) across the tree — … on the roadmap
8 file(s) uncommitted on main
HEAD <sha> <subject>
```

The lowest open tier and its next row are the two figures that decide what gets
worked next, so they lead; the per-tier breakdown says how far the tier has to
go. A red gate sends the same body at high priority with the failing stage in
the title (`RED (the tower)`, `RED (cheap checks)`, `RED (light)`), so a build
that dies while nobody is watching still reports.

## Why it computes rather than reads

PROOF-STATE.md deliberately carries **no aggregates** — a hand-typed total is
true when written and silently wrong later, with nothing checking it, which is
the failure `roadmap-check` exists to prevent. Every number here is derived at
send time from the roadmap and the postulate ledger, and nothing is written
back, so the notification can carry counts without the roadmap acquiring any.

The parse is `check-roadmap.py`'s own, imported rather than re-implemented: a
second reader of the roadmap's row syntax would drift from the checker's, and
then the notification and the gate would disagree about what a row is.

## Where it is wired

The `gate-light` and `gate-heavy` recipes call it on both exits. `make notify`
sends the same thing by hand; `make notify V=<label>` sets the title's verdict.
