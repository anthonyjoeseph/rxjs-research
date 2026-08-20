# `make wiring-gate` — the reachability checker

The LAW this enforces is in CLAUDE.md ("The wiring law", "A POSTULATE MUST BE A
LEAF"). This file is the checker: what it exits 1 on, how it computes reachability,
and the four mechanics that bite when you write an assembly.

## `make wiring-gate` exits 1 on exactly these, and on nothing else

- **An unreachable definition or postulate** — R1.
- **An unreachable MODULE.** A different question from definition reachability, and a
  blind spot a per-definition check cannot see: a module holding only
  `open import … public` re-exports has no definitions to report and reads as clean
  however dead it is.
- **A `⊤`-typed postulate** that asserts nothing. `VACUOUS_ALLOWLIST` carries the one
  deliberate exception, `defer-shift`, whose own comment says it is "an honest gap,
  not a claim". A NEW one fails.
- **A bare `open import` in Main**, or a Main claim whose name no longer exists.

## How reachability is computed

From Main plus each `MODULE_ROOTS` module's declared ENTRY POINTS — `main` for a
compiled binary (the shell is its consumer, and no textual search finds that edge),
and NOTHING for a type-level cache or probe module, which is held up entirely by its
anonymous `_ : T` pins.

**It is the entries, not the module.** Seeding a root module wholesale exempted every
internal helper in it, so a probe module or a binary could accumulate dead code
forever while the gate read `unreachable 0` — measured with a canary in Root-Probe
that went unreported. Anything those entries reach is covered automatically.

`make wiring` reads Main's `using` clauses to get its seeds, so a filename never earns
an exemption and a claim cannot self-certify.

## R2: a name PASSED to a postulate gets no reachability credit

That is how "a postulate must be a leaf" is enforced — as a corollary of
reachability, needing no ledger of its own. Passing is not itself forbidden; what is
forbidden is a postulate being the ONLY connective tissue between a proven definition
and Main. A lemma that is also genuinely applied somewhere stays green; one whose only
use is being handed to a postulate has no route home and fails R1. There is no
grandfather list and no name-based heuristic: the rule sees EVERY postulate, not the
ones that happen to be named `-core`.

### "Passed" covers the eta form and the continuation line

It had to, because together they are how the rule's own worked example escaped it.
`merge-cert` was an ingredient of nothing for months and read as wired, by this shape:

```agda
root-caches =
  root-caches-core (λ {n} {Γ} {t} → merge-cert {n} {Γ} {t})
```

Each half hid it independently. The application sits BELOW its clause's `=`, so the
checker read the whole line as a type mention and never examined the arguments; and
the argument is PARENTHESISED, so it read as a nested value being computed rather
than a proof handed over. The eta form is not exotic — CLAUDE.md MANDATES it
(mechanic 1 below), so the one shape R2 most needs to see was the one shape it could
not. Both are pinned in `scripts/wiring-selftest` (`bad-lemma`, `eta-lemma`); neither
costs the real tree a name.

The check errs toward over-suppressing edges, which is safe by construction: a misread
edge can only fail a name whose ONLY route home was that edge, and such a name is
exactly what the rule exists to report.

## `make wiring-selftest`

Proves the check is load-bearing, against a fixture outside `agda/src`: R2 must fire
on a lemma passed bare to a postulate and on nothing else, and a module application
must still conduct reachability. **R2 fires on nothing in `agda/src` today, so without
the fixture it would rot untested.**

## `make wiring-refuted`

`agda/refuted/` is under the wiring law by its own root: the same checker with
`--src agda/refuted --root Refuted/Main.agda`, so every witness and every helper out
there must trace to a name `Refuted.Main` claims. It has no MODULE_ROOTS — no compiled
binaries, just witnesses — so the whole tree hangs off that claim list, and
"Refuted.Main names every witness" is enforced rather than merely stated. A refutation
cannot self-exempt by choosing its name, which is what the old `*-absurd` suffix match
allowed. Nothing in `src` may import it. The rules for that tree are in
`REFUTATION.md`.

## The four mechanics of writing an assembly

Each otherwise costs a full build.

1. **Pass every lemma ETA-EXPANDED with explicit implicits** — `(λ {n} {Γ} → f {n} {Γ})`.
   When a statement reduces away its own implicit, bare arguments give
   `Unsolved metas`; the eta form always works.
2. **A *function*-valued piece is wired by its DEFINING EQUATION**, not by its type
   (`ΩAt` in `.Measures` is the worked example) — passing the type quantifies over
   every inhabitant and makes the statement strictly STRONGER.
3. **EXTRACT types from source; never retype them.** `scripts/check-wiring.py`'s
   `signature_text` does it exactly. Copied signatures drag in VOCABULARY the parent
   module does not import — collect the names in one pass, since Agda stops at the
   FIRST scope error.
4. **ORDERING: a postulate cannot reference a definition below it.** Leaves sit above
   the body that consumes them. This is Agda scoping, not a checker rule — nothing
   reports it, so get it right rather than learning it from a failed typecheck.

## Counting the ledger

**`make postulates`** — every postulate by name — **is** the complete remaining-work
ledger. Do NOT substitute `grep '^postulate'`: that finds the block HEADERS, a third
of the count, and a branch hidden inside a block is exactly how eight well-formedness
postulates once went uncounted while the index claimed the campaign reduced to two.
