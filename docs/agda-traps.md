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

- **A CONTEXT-INDEXED CONSTRUCTOR ALIAS IN A `where` TYPE LEAVES `Γ` UNSOLVABLE, AND
  THE META IS REPORTED AT ITS CONSUMER.** `inputᶜ : ∀ {n} {Γ : Ctx n} (i : Fin n) →
  Exp Γ … (lookup Γ i)` mentions `Γ` only in its RESULT, so `hopDᵉ V (slotHop V sl)
  (inputᶜ i)` cannot solve it: `Fin n` does not carry `Γ`, and `slotHop`'s result type
  (`Fin n → ℕ`) has already forgotten it. In the enclosing STATEMENT the same term is
  fine, because a telescope variable of type `Closed Γ …` pins it — so the trap only
  appears when a `where` binding re-spells the statement's own term. Agda blames the
  outer application (`hopDᵉ`, `syncSizeᵉ`), never the alias, and the clause head that
  would supply `Γ` typically binds `{n = n}` and stops. Bind `{Γ = Γ}` in the clause
  head and write `inputᶜ {Γ = Γ} i`. The general form: **when an unsolved meta is
  reported at a function whose own arguments look fully determined, look for an argument
  whose type variable appears in ITS result only.**

- **INSIDE `abstract`, EVERY `where` BINDING NEEDS AN EXPLICIT TYPE SIGNATURE, AND THE
  ERROR IS A WARNING WITH NO POSITION YOU CAN USE.** A sealed lemma whose proof is
  staged through `where`-bound steps fails with
  `MissingTypeSignatureForOpaque: Missing type signature for abstract definition S` —
  because Agda never infers the type of an abstract definition, and a `where` binding
  under an `abstract` block is one. The message then prints the whole clause back
  desugared, as `mutual / abstract / syntax S ... / postulate S : _`, which reads like a
  tool generating broken code and is in fact Agda's own rendering. Two consequences: the
  fix is one signature per binding, and the desugared dump is NOT evidence that anything
  mangled your source. Since the tower runs `-W error`, the warning is a build failure.
  This bites specifically on the `budget-sufficient` spine, where the seal is mandatory
  and staging a bound through named steps is the natural way to write it.

- **A CLOSED NUMERAL LARGE ENOUGH TO EXCEED WORD ARITHMETIC IS FINE UNTIL IT MEETS A
  FREE VARIABLE, AND THEN THE CHECKER PEELS IT ONE SUCCESSOR AT A TIME.** `_+_` and
  `_*_` on `ℕ` are GMP-backed only when BOTH operands close; with one operand stuck on a
  bound variable, Agda falls back on the defining clauses, and `suc n * m = m + n * m`
  turns a forty-five digit factor into a forty-five digit recursion. It surfaces three
  ways, all of which read as "Agda hung on a two-line lemma": an implicit left for the
  unifier to solve against `1 + U` where `U` is such a numeral, which inverts a builtin
  addition; two DIFFERENT SPELLINGS of the same product compared under a stuck sum, which
  defeats the syntactic-equality short circuit and reduces instead; and `with` on a `Σ`
  whose type carries such a product, which reduces the abstracted type.
  Three repairs, and all of them are about keeping the numeral away from the variable
  rather than about making it smaller — shrinking it does not help, since the peel is
  linear in the value: supply the implicits explicitly; state the step that introduces
  the free variable **over variables**, in its own lemma, and apply it at the
  obligation's own spellings so every comparison is syntactic; and take a `Σ` apart with
  `proj₁`/`proj₂` rather than `with`. Measured on one refutation: seven minutes and
  thirteen gigabytes down to thirteen seconds, with no change to what it proves.
