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

Tier 1 is the lowest open — 2 falsity, 21 difficulty
across 2 falsity, 16 difficulty on the roadmap
standing on 11 refutations, 4 dead routes, 3 twins, 21 probes, 3 recoveries

- **the first leg** — … the tier's big picture roadmap, verbatim,
  all three legs and the prose under each.
- **the second leg** — …
- **the third leg** — …

  tier 1: 14 difficulty, 2 grindable
    evidence: 10 refutations, 1 dead route, 3 twins, 7 probes, 1 recovery
  tier 2: 2 falsity, 4 shape, 19 difficulty
    evidence: 1 refutation, 1 dead route, 1 probe
  tier 3: 2 vacuity, 1 difficulty
    evidence: no evidence

87 live postulate(s) across the tree — … on the roadmap
evidence standing under them: 11 refutations, 2 dead routes, 3 twins, 8 probes, 1 recovery
3 file(s) uncommitted on main
HEAD <sha> <subject>
```

The lowest open tier leads, and it leads with the whole of what a session
would open the roadmap to read: the tier's POSTULATE census by risk class, and
then its big picture roadmap in full.

**The postulate count and the row count are different censuses, and both are
printed.** One row routinely heads a family, so counting rows reads the tier as
smaller than the ledger it stands for; counting postulates says how much is
actually open. The class is the ROW's, since a class is declared on a row, and
a name is counted once however many rows reach it.

**The roadmap goes out verbatim rather than as three titles.** The titles say
which groups are next and none of why, and the why is the part that decides
whether the plan still fits what the last run found. The per-tier breakdown
below it says how far each tier has to go.

**The evidence line is the other half of a risk class, and it is why the two
are printed together.** A tier of fourteen DIFFICULTY rows standing on ten
refutations and seven probes is a tier whose statements have been tested; the
same fourteen rows with `no evidence` under them is a tier whose classes are
opinions. Markers count with multiplicity — a row carrying `REFUTED×4`
contributes four — because four refutations pinning one statement's shape is
four findings, not one.

**They are summed from the postulates' own headers, not from the roadmap's
evidence fields**, by the same reader `make roadmap-check` uses. The two agree
today only because that check fails when they do not, and reading the headers
is what makes the agreement a fact rather than an assumption. A red gate sends the same body at high priority with the failing stage in
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
