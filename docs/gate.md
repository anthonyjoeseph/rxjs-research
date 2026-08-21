# `make gate` — it routes, and the machine picks light or heavy

`make gate` typechecks the whole tower and takes many minutes. Almost none of
that work is ever implicated by a given edit: most modules in `agda/src` contain
no multi-member mutual block, and **a module with no such block is emitted
VERBATIM by `agda-dev`**, so a dev pass over it is a *real* check and not a
stubbed one. Where that holds, the full build is buying a recheck of code
nothing touched.

So there are three targets, and **`gate` is the one you type** — it routes:

| Target | What it runs | Cost |
| --- | --- | --- |
| `gate` | asks for the verdict, then takes the light path or the heavy one, and says which and why | either of the below |
| `gate-light` | every cheap check, plus a real dev check of each module this tree has touched. Red when the heavy path is owed | seconds, plus one dev pass per changed module |
| `gate-heavy` | the cheap checks, the full tower, the refutations, the bug cache — and stamps the commit | many minutes |

**`gate` routing is the whole point.** If the expensive target kept the
plainest name, every session would reach for the tower by default, whatever a
doc said. So `gate` asks `dev-changed --verdict-only` — free, a `--list` pass
and a `git` query, no typecheck — and takes the cheap road when the cheap road
is valid. `gate-heavy` forces the tower when you want it regardless.

Because `gate` routes on that verdict, **every escalation trigger must be
visible to `--verdict-only`**, drift included. It was not, once: the drift check
sat after the early return, so a routing caller would have been told the light
path was fine with the consumers long unchecked. The selftest pins it.

**The cheap half is identical.** `GATE_CHEAP` is one list, shared: wiring,
`unsafe-check`, `dup-check`, the import checker's selftest, `roadmap-check`,
and every selftest that keeps those honest. Nothing about running the light gate
loosens the wiring law or lets PROOF-STATE go stale.

## You do not choose — `dev-changed` refuses

`gate-light` calls `scripts/dev-changed.py`, which **exits 2 when the full build
is still owed**, and make goes red. That is deliberate: the criterion is
mechanical, so it does not belong in anyone's head. Four triggers, any one of
which escalates:

- **A changed module has ≥1 multi-member mutual block.** `agda-dev` stubs the
  other members, so termination of the real mutual recursion is not checked and
  postulates do not reduce — and in this proof the mutual recursion IS the
  induction. This is the trigger the whole split exists for.
- **A changed file is outside `agda/src`.** `agda/refuted` has its own include
  root and its own target; no dev check reaches it.
- **The changed set exceeds `--max-files` (default 6).** A dev check is cheap
  *singly*: run N of them sequentially, each rebuilding its own cone, and the
  full build buys the entire tower for about the same money — and checks the
  consumers, which the light gate does not.
- **DRIFT: more than `--drift` commits (default 10) since the last green full
  gate.** The stamp is `.gate-heavy-stamp`, written by the heavy path, ignored by
  git, and wiped by a clean checkout — so a fresh working copy escalates, which
  is the right default for a cold cache.

## Why the trigger is "multi-member block", not "contains `mutual`"

The obvious cheap version of this rule is to grep the changed files for a
`mutual` keyword. It is wrong in **both** directions, and measured over the 90
modules of `agda/src`:

| rule | escalates | needlessly heavy | **wrongly LIGHT** |
| --- | --- | --- | --- |
| a literal `mutual` keyword appears | 14 | 9 | **17** |
| ≥1 multi-member block (implemented) | 22 | — | — |

The 17 are the finding, and `scripts/agda-dev.py`'s own header had already
said why: **an Agda mutual block is not the `mutual` keyword.** A block runs
from the first forward signature until every pending signature has a
definition, so a pair of forward-declared functions that call each other is a
two-member block with no keyword anywhere -- and this repo's heavy modules are
written exactly that way. A keyword grep misses them — among them `Rx/Evaluator.agda`, `Verify-Budget-Sufficient/
Burst-Walk.agda` and `Subscribe-Face.agda`, which are exactly the modules where
a stubbed sibling makes dev-green and gate-green come apart. The grep would
wave those onto the light path: a false green, the one failure direction that
costs something.

The 9 in the other column are the smaller half of the same point — a
single-member `mutual` block has no siblings to stub, so it is emitted verbatim
and its dev check is real.

The block is the right unit because it is the unit of TWO things at once: it
is what Agda's termination checker examines (one decreasing measure across
every call in the block), and it is what `agda-dev` stubs. Those coincide, and
that coincidence is the whole basis of the split -- in a multi-member block the
dev run loses precisely the check the heavy path uniquely buys.

So the trigger **asks the generator what it will actually stub** (`agda-dev
--list`, free) rather than grepping for a proxy. A criterion derived from the
same code that does the stubbing cannot drift from the tool it exists to guard
against; a grep can, and does.

## A WIDE CONSUMER CONE IS NOT A REASON TO ESCALATE

It reads like one — a deep module with 22 consumers feels like it wants the
tower — and reaching for the tower on that feeling is how the light gate gets
abandoned in practice. It is the wrong move. The cone is the ONLY thing the
light path leaves unchecked, so a wide cone is an argument for **checking the
cone**, which is a few dev passes, not for buying the whole build.

`dev-changed` therefore turns `--deps` on by itself once the cone exceeds
`--deps-over` (default 8), and the selftest pins that a wide cone does **not**
escalate — the regression being guarded against is a future session
"tightening" this into an escalation trigger.

### …but a CLAIM ROOT is never part of the sweep, or the sweep IS the tower

The first version of the auto-`--deps` path checked the cone as computed, and
that is wrong in a way the phrase "cheaper than the tower" hides: **every
module in `agda/src` has a route to Main by the wiring law, so EVERY cone
contains the claim roots**, and a dev check on `Main.agda` is `make agda` with
a comment-stripping round trip in front of it. Measured on the run that found
this: the roots and `The-Proof.agda` each hit the 45 s budget and were reported
`FAIL`, then at 560 s `Main.agda` took minutes and `The-Proof.agda` had still
not finished — while **every non-root consumer in the same run came in under
12 s.** The cheap part was real; the roots were the whole cost.

So the sweep subtracts the claim roots and says which ones it held back. What
covers a root is the DRIFT counter and the heavy gate, which is what they are
for.

### AND A CONE MEMBER WHOSE DEV CHECK WOULD BE STUBBED IS NAMED, NOT DROPPED

`agda-dev` stubs a multi-member mutual block's siblings, so a dev check on such
a module is not a check. The sweep therefore cannot run it — and its first
version dealt with that by **skipping it in silence**, which is worse than
running it: the summary line said the changed modules were dev-green and `make
agda` would add only the consumers, while the consumers most worth checking had
never been looked at.

The shape that makes it expensive: a new clause body lands in a leaf module, and
the module that validates its **fit** — the dispatch it plugs into — is the one
with the mutual block. Measured on the leg that found this, a sweep of 50
consumers silently dropped exactly the two modules that consume the new arms.

So the sweep names each stubbed member, counts it in the unchecked list, and the
final line says how many stayed unchecked. `make agda` is what covers them.

### A BUDGET TIMEOUT IS NOT A RED, and conflating them made the sweep lie

`agda-dev` exits non-zero for a budget kill exactly as it does for a type
error, so the sweep called both `FAIL`. For a module the commit **changed**
that is right — that module is the one thing the run exists to check. For a
**cone** module it is not: an unfinished consumer check is precisely the bet
the light path was already making, so it is reported `skip` and the sweep goes
on. Both halves are selftest rows, because collapsing either direction is a
one-character edit: red on a cone timeout fails every wide-cone run, and skip
on a changed timeout passes a module nothing checked.

The budget kill is distinguishable only by the per-member `(exit 124)` in
`agda-dev`'s own report, never by the process status. A cone member has no
multi-member block by construction, so it runs exactly one focus check and the
marker cannot belong to a sibling.

`--plan` prints the sweep plan — what would be checked, what was held back —
and runs no agda, which is what makes the root exclusion testable at
`gate-cheap` speed.

### The sweep has a TOTAL budget, not just a per-module one

`--budget` bounds one check; nothing bounded the sum. A changed set of five
modules low in the tower has a 48-module cone, and 48 per-module budgets is
more wall clock than the one build that checks all of them — so
`--cone-budget` (default 300 s) stops the sweep and NAMES what it left. Cone
coverage is partial by design; what is forbidden is partial coverage that
reads as complete.

## THE CHANGED SET IS MEASURED FROM THE LAST GREEN HEAVY GATE, NOT FROM HEAD

This one produced a false green in the flow it matters most in. `make gate`
after a commit sees a clean tree; a HEAD diff is empty; nothing is checked;
`gate-light: ALL GREEN`. The gate had not looked at the commit at all — and
land-then-gate is the flow every leg of this campaign uses.

What the light gate owes is everything the last green HEAVY gate did not
cover, and the stamp already records that commit. So `dev-changed` diffs from
the stamp, and the changed set survives committing. With no stamp there is
nothing to diff from and the drift trigger escalates anyway, which is the
cold-cache case handled correctly for a different reason.

Ask for the verdict alone, at no typecheck cost:

```
scripts/dev-changed.py --verdict-only
```

## What the light gate does NOT check, stated plainly

**It does not check the changed module's CONSUMERS.** A signature edit its own
file accepts happily can break every importer, and only the full build sees
that. This is the bet the light gate makes, and it is the reason the drift
trigger exists at all.

The bet is made *visible* rather than hidden: `dev-changed` prints the reverse
dependency cone by name and count, so the report says exactly which modules were
not checked. `DEPS=1` dev-checks the cone too, where its members have no
multi-member block. (Cross-checked on one module: the tool reported 10 consumer
modules and the subsequent full gate spent its time on 11.)

The second thing it does not check: `refuted` and `bug-cache` both depend on
`agda/src`, so running them would rebuild the cone the light gate is avoiding.
They belong to the merge gate.

## Flags and knobs

```
make gate                       WHAT YOU TYPE — routes, and says which and why
make gate-light                 force the light path (red if heavy is owed)
make gate-heavy                 force the tower
make gate DRIFT=20              raise the commit limit
make gate-light DEPS=1          dev-check the consumer cone as well
make gate-light ARGS='--max-files 12'
make dev-changed                the dev half alone
make dev-changed-selftest       verdict flips both ways, and nothing passes quietly
```

`dev-changed` exit codes: **0** green, **1** a dev check FAILED, **2** the full
gate is required. It also exits 1 when the changed set is non-empty but nothing
was actually checked — checking nothing must never read as a pass.

## Related

- [agda-dev.md](agda-dev.md) — the dev loop itself, its budget, and the
  fidelity boundary the escalation rule is derived from.
- [agda-build.md](agda-build.md) — `-W error`, and the comment-stripped mirror
  both gates actually check.
- [bg.md](bg.md) — `make gate` outlives a tool call; this is how you launch it.
