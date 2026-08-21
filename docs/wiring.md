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
forever while the gate read `unreachable 0` — measured with a canary in a probe module
that went unreported. Anything those entries reach is covered automatically.

The probes have since left this table altogether, which is the stronger fix: an entry
here is a seed inside the PROOF's own scan, so a probe listed here counted as wired
while nothing in the proof consumed it — and `make agda`, which compiles Main's cone
and nothing else, never saw the file at all. They live in `agda/evidence/probed/` now,
claimed by `Probed.Main` and held to this same law by `make wiring-probed`.

`make wiring` reads Main's `using` clauses to get its seeds, so a filename never earns
an exemption and a claim cannot self-certify.

**Two kinds of line own their span under a synthetic PER-SITE name, and both are
seeds.** An anonymous `_ : T` pin, and a column-0 `... | p = body` `with` arm. Neither
can ever HAVE a consumer, but both are real bodies the typechecker checks, so whatever
they use IS used. The per-site part is what makes them safe: attribute such a line to
the definition ABOVE it instead and a name used there becomes a self-reference and is
dropped (measured: 115 live names orphaned when the `with` arm's own head was removed,
and one pin's only real consumer lost the same way). Giving every `with` arm ONE shared
owner is the other failure — that node has no route home, so a helper consumed only
inside `with` arms reads as dead. Both are pinned by the selftest.

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
on a lemma passed bare to a postulate and on nothing else, a module application must
still conduct reachability, and a helper used only inside a `with` arm must not be
reported — at the file scope and one scope down, since two scanners register heads and
only one of them was ever exercised by the real tree. No bare `...` may surface as a
definition. **R2 fires on nothing in `agda/src` today, so without the fixture it would
rot untested**, and the `with`-arm case was invisible there for a sharper reason: the
token `...` appears in nearly every file in `agda/src`, so the shared owner rode along
accidentally reachable and the bug only surfaced in `agda/evidence/refuted`.

## `make wiring-refuted`

`agda/evidence/refuted/` is under the wiring law by its own root: the same checker with
`--src agda/evidence/refuted --root Refuted/Main.agda`, so every witness and every helper out
there must trace to a name `Refuted.Main` claims. It has no MODULE_ROOTS — no compiled
binaries, just witnesses — so the whole tree hangs off that claim list, and
"Refuted.Main names every witness" is enforced rather than merely stated. A refutation
cannot self-exempt by choosing its name, which is what the old `*-absurd` suffix match
allowed. Nothing in `src` may import it. The rules for that tree are in
`EVIDENCE.md`.

## `make wiring-probed`

The same again for `agda/evidence/probed/`, rooted at `Probed/Main.agda`. It reads
oddly at first — a probe's content is anonymous `_ : T` pins, which are seeded
everywhere anyway, so what is there to be unreachable? The answer is the HELPERS: the
program corpora, the abbreviations, the little decision procedures a probe accretes to
state its rows. Those are ordinary definitions and they rot exactly like any other.
And `Probed.Main` naming every probe module is what makes `make probed` a claim rather
than a directory listing — the same reason `Main.agda` names definitions instead of
carrying a bare `open import`.

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
