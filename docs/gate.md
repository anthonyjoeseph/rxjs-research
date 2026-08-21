# `make gate-light` and `make gate` — two gates, and the machine decides which

`make gate` typechecks the whole tower and takes many minutes. Almost none of
that work is ever implicated by a given edit: most modules in `agda/src` contain
no multi-member mutual block, and **a module with no such block is emitted
VERBATIM by `agda-dev`**, so a dev pass over it is a *real* check and not a
stubbed one. Where that holds, the full build is buying a recheck of code
nothing touched.

So there are two gates:

| Target | What it runs | Cost |
| --- | --- | --- |
| `gate-light` | every cheap check, plus a real dev check of each module this tree has touched | seconds, plus one dev pass per changed module |
| `gate` | the cheap checks, the full tower, the refutations, the bug cache — and stamps the commit | many minutes |

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
  gate.** The stamp is `.gate-full-stamp`, written by `make gate`, ignored by
  git, and wiped by a clean checkout — so a fresh working copy escalates, which
  is the right default for a cold cache.

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
make gate-light                 the default gate
make gate-light DRIFT=20        raise the commit limit
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
