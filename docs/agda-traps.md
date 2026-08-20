# Agda language and stdlib traps — each diagnosed the expensive way

Traps **inside the language**, as opposed to the build- and tooling-level ones in
[agda-build.md](agda-build.md). Every one below cost real time at least once, and they
share a shape worth naming: **Agda reports these against the WRONG thing**, so the
error message actively misdirects. Read the entry before reasoning from the error.

- **A SHORT LOWERCASE BINDER MAY COLLIDE WITH AN IN-SCOPE CONSTRUCTOR, AND THE ERROR
  NAMES THE WRONG TYPE.** Agda then reads your intended *variable* as a *pattern*. The
  stdlib instance is `acc`, `Induction.WellFounded`'s constructor, whose shadowing
  yields the useless "cannot split on non-datatype". The costly ones are REPO-LOCAL — a
  two-letter constructor of one of this development's own small relations — and there
  the message reports the type you were matching on rather than the clash, e.g. "hs is
  not a constructor of the datatype `_≤_`". **When an error says "X is not a constructor
  of T" for something you meant as a variable, grep for `X :` before touching the
  proof.** Cost one 40-minute gate.

- **The termination checker rejects `where`-bound abbreviations of the recursion
  pattern.** Inline it — write `suc (suc j)`, not a bound alias.

- **As-patterns break the termination checker** in nested-`Acc` `where`-helpers. Keep
  the plain `go` shape.

- **Implicits sitting under `_+_` are not inferred from `≤-refl`.** Agda refuses to
  invert `_+_` (it hits inversion depth 50) and reports the failure as an *unsolved
  constraint* rather than as an inference failure. Pass the implicit explicitly.

- **`suc m ≤ᵇ n` unfolds to `m <ᵇ n`.** State Bool-false helpers over `<ᵇ` or they will
  not reduce. The same asymmetry bites in reverse when a conjunct needs a cons DROPPED
  from a `length`: a Bool-level widening lemma's bound is recoverable only *after*
  `suc … ≤ᵇ suc …` reduces, and Agda will not run that reduction backwards to solve for
  it. Go through the `≤` side instead — `≤ᵇ⇒≤`, `≤-trans`, `≤⇒≤ᵇ`.

- **`∧-true`'s Bool arguments must be EXPLICIT, not `_`,** wherever the statement
  reduces its own conjunction away — otherwise the metas are unsolvable, because there
  is nothing left in the goal to recover them from. Same family as the eta-expansion
  mandate for lemmas passed to postulates.

- **`+-monoˡ-≤` with `s≤s z≤n`** needs the implicit pinned (`z≤n {k}`), else it leaves
  unsolved metas.

- **`Data.Nat.Solver` works, but suc-headed sums must be written `3 + V`, not `V + 3`.**

- **`rewrite *-identityʳ` twice for `suc sz * 1`** — it unfolds to `suc (sz * 1)`, so
  the inner product needs its own rewrite.

- **A `with` scrutinee can be named without adding a pattern position**: `with X in eq`
  binds the equation and adds no `with` nesting level. Where the proof and the lookup
  can share ONE `with`, prefer that — refining the lookup then refines the proof's type
  and the equation is not needed at all.
