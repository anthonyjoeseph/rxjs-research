-- FIXTURE for `make dup-selftest`.  NOT Agda that typechecks and not
-- meant to: check-duplicates.py is purely textual and never runs Agda,
-- so these are declarations without bodies.  It lives outside agda/src
-- so the real gate and the wiring law never see it — same arrangement
-- as scripts/wiring-selftest.
--
-- Every entry is labelled MUST-FIRE or MUST-NOT-FIRE.  The MUST-NOT
-- ones are the regressions: each corresponds to a bug that shipped.
module A where

Id : Set
Id = ℕ

-- MUST FIRE (exact, two names): twin of B.twin-different-name
plus-comm-ish : ∀ (a b : ℕ) → a + b ≡ b + a

-- MUST FIRE (exact, ONE name in two modules).  Agda does not catch this
-- when either copy is private or the modules never meet; the real
-- escapees were dbl-suc and 2*suc≤2^suc.
shared-name : ∀ (w : ℕ) → suc w + suc w ≡ 2 * suc w

-- MUST FIRE (up-to-binder): bare here, annotated in B
bare-binder : ∀ X → 3 * X ≡ X + X + X

-- MUST FIRE (up-to-binder): explicit here, implicit in B
explicit-binder : ∀ (m n : ℕ) → m ≤ n → (m ≤ᵇ n) ≡ true

-- MUST FIRE (exact): the binder is an UNANNOTATED IMPLICIT —
-- `{n}` here against B's `{m}`, with nothing else different.  This is
-- the shape that escaped for real: `sum-tabulate-lb` (.Caps-Face/Part1)
-- and `fᵢ≤sum-tab` (.Measures) were the same fact with the same proof,
-- in two modules of ONE public import chain, and neither Agda nor this
-- check said a word.  `∀ {n} {Γ : Ctx n}` opens most statements here,
-- so the blind spot covered nearly every pair in the tree.
implicit-unannotated-a : ∀ {n} (f : Fin n → ℕ) (i : Fin n) → f i ≤ sum (tabulate f)

-- MUST FIRE (exact, after synonym expansion): Id here, ℕ in B
synonym-lhs : ∀ (i : Id) → i + 0 ≡ i

-- MUST NOT FIRE against B.op-or.  These differ ONLY in the operators,
-- and the binder-name regex used to match `[A-Za-zÀ-￿]`, a class that
-- contains → ≡ ∧ ≤ and every other operator here — so both normalised
-- to the same key and two unrelated lemmas were reported as one fact.
op-and : ∀ a b → a ∧ b ≡ true → (a ≡ true) × (b ≡ true)

-- MUST NOT FIRE: the mandated private-impl + abstract-alias idiom.
-- Its type is distinct from every other entry here on purpose — the
-- alias exemption only applies to a group of exactly two names, so a
-- third declaration sharing the type would silently disarm this row.
sealed-go : ∀ (n : ℕ) → n * 2 ≡ n + n
sealed : ∀ (n : ℕ) → n * 2 ≡ n + n

-- MUST NOT FIRE against B's identical field.  Record fields are not
-- standalone facts and repeat across records by design (Inv and
-- BurstInv both carry reg-typed).
-- The header is MULTI-LINE on both sides on purpose.  A single-line
-- `record … where` is already caught by the where-filter, so a fixture
-- with one would pass even with the field-filter deleted.
record R1 (n : ℕ)
          (m : ℕ) : Set where
  field
    fld-a : suc n + 0 ≡ suc n
    fld-b : suc n * 1 ≡ suc n

-- MUST NOT FIRE against B.outer's local.  where-block locals are
-- hypothesis names inside one proof.
outer : ∀ (n : ℕ) → n + 1 ≡ suc n
outer n = helper
  where
  helper : n + 3 ≡ suc (suc (suc n))
