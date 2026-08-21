# `agda/evidence/` — mechanics

The laws are in [EVIDENCE.md](../EVIDENCE.md); this page is how the machinery
works and what bites.

## Layout, and why the boundary is real

```
agda/
  rxjs-research.agda-lib            include: src
  src/…
  evidence/
    rxjs-evidence.agda-lib          include: refuted probed ../src
    refuted/Refuted/…               module Refuted.X
    probed/Probed/…                 module Probed.X
```

The two trees stay separate include ROOTS inside the evidence library, which
is what keeps `make wiring-refuted` and `make wiring-probed` working as plain
per-tree invocations of the same checker: each names its own tree root and its
own claim root, so one tree's files are never the other tree's orphans.

**Agda picks up the `.agda-lib` in the directory it is invoked from**, and
nothing scans subdirectories for further ones. So the include path depends
entirely on where the build starts:

| invoked from | include path | can it see `Refuted.*` / `Probed.*`? |
| --- | --- | --- |
| `agda/` (what `make agda` does) | `src` | **no — the name does not exist** |
| `agda/evidence/` (`make refuted`, `make probed`) | `refuted`, `probed`, `../src` | yes, and it sees `src` too |

That is the whole mechanism. `make agda` starts at the `src` root, so an
evidence import in `src` is an unresolved module, not a policy violation.
`make evidence-check`'s E1 exists on top of it for speed and legibility — a
grep in a second beats a scope error eight minutes in — and to survive someone
"repairing" the include path.

**Two include roots inside ONE library, which is what this replaced, gives no
boundary at all.** `include: src refuted` made both trees roots of the same
library, so `src` importing `Refuted.X` resolved fine; the one-way rule was
convention plus review, and it held only because nobody tried.

## The targets

```
make refuted              typecheck the refutations   (Refuted/Main.agda)
make probed               typecheck the probes        (Probed/Main.agda)
make wiring-refuted       reachability, rooted at Refuted/Main
make wiring-probed        reachability, rooted at Probed/Main
make evidence-check       E1 + E2
make evidence-selftest    proves E1 and E2 still fire
```

`evidence-check` and `evidence-selftest` are in `GATE_CHEAP` — both are pure
textual passes over a few hundred files and cost under a second. `refuted` and
`probed` run in `gate-heavy` beside `make agda`, on the same warm interface
cache.

## Adding a probe

1. Write it at `agda/evidence/probed/Probed/<Name>.agda`, module
   `Probed.<Name>` — the tree name and the module namespace are separate
   directory levels, and the `.agda-lib` includes `probed`, not its parent.
   Import from `src` freely — that direction is the point.
2. Give it a `-- TARGET: <postulate>` line naming what it is evidence for, one
   name per line, bare (no module prefix). E2 checks each against
   `make postulates`.
3. Name it in `Probed/Main.agda`'s `using (…)`, or `wiring-probed` will call
   it unreachable.
4. Put the RECEIPT — which shapes were covered — in the target postulate's own
   header in `src`, as `-- PROBED <date>:`. The probe is apparatus; the
   receipt is the finding, and it belongs next to the statement. A receipt on a
   `postulate` BLOCK MEMBER is indented, and E3 reads it there and attributes
   it to that member rather than to the member above — but only since the day
   a real one was written that way and the receipt total did not move. Two
   receipts had been invisible, one of them for days, so if you are auditing
   coverage against a count taken before that, take it again.

## What bites

- **`make agda` never sees this tree, and never did.** Before the move the
  probes were `MODULE_ROOTS` entries in `check-wiring.py` typechecked by
  `make bug-cache`; `make agda` compiles `src/Main.agda`'s cone and nothing
  else. If you are wondering why a probe's error never showed up in the gate
  log, that is why.
- **E2 fires the moment a target is discharged, and that is the point.** It
  will look like the gate breaking on a success. The repair is to DELETE the
  probe (or retarget it), never to relax E2 — an expired probe is exactly what
  this check exists to surface.
- **A probe that pins the EVALUATOR is not a probe.** If its rows survive
  their target because what they really test is that some composite reduces,
  it is a unit test: move it to `Implementation/Unit-Test.agda`, which is
  append-only and has its own end-of-life.
- **The comment-stripped mirror covers the evidence tree too**, so a
  comment-only edit out here is free in the same way — but **`make refuted` and
  `make probed` map the PATH back and not the LINE.** An error reports the
  `agda/evidence/…` path with the STRIPPED file's line number, which resolves
  in your editor and points at unrelated code, usually an import. Read the line
  out of `agda/_stripped-comments/evidence/…`, or match on the statement text
  rather than the number. This is the stale-line-number failure the repo's
  rules are written against, arriving from the tooling instead of a comment.
- **`make unsafe-check` covers the evidence trees as well as `src`.** A
  refutation proven with `NO_POSITIVITY_CHECK`, or a probe row that `refl`s
  because of `--type-in-type`, is worse than no evidence: it is evidence
  pointing the wrong way. Nothing about being outside the claim graph makes an
  unsound pragma harmless here.
- **`dup-check` does NOT span the boundary.** It runs per tree, so a fact
  proven both in `src` and in a refutation is not reported. That is deliberate
  — a refutation restating a `src` definition's type in order to contradict it
  is normal — but it means the SEARCH FIRST rule is on you out here.
