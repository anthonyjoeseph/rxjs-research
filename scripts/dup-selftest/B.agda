-- The other half of the dup-selftest fixture; see A.agda for the rules.
module B where

-- MUST FIRE (exact, two names): twin of A.plus-comm-ish
twin-different-name : ∀ (x y : ℕ) → x + y ≡ y + x

-- MUST FIRE (exact, ONE name in two modules): twin of A.shared-name
shared-name : ∀ (w : ℕ) → suc w + suc w ≡ 2 * suc w

-- MUST FIRE (up-to-binder): annotated here, bare in A
annotated-binder : ∀ (X : ℕ) → 3 * X ≡ X + X + X

-- MUST FIRE (up-to-binder): implicit here, explicit in A
implicit-binder : ∀ {m n : ℕ} → m ≤ n → (m ≤ᵇ n) ≡ true

-- MUST FIRE (exact, after synonym expansion): ℕ here, Id in A
synonym-rhs : ∀ (i : ℕ) → i + 0 ≡ i

-- MUST NOT FIRE against A.op-and — same shape, different operators.
op-or : ∀ a b → a ∨ b ≡ false → (a ≡ false) × (b ≡ false)

-- MUST NOT FIRE against A.R1's fields.  The header is deliberately
-- MULTI-LINE: that puts `where` at the indent of the last continuation
-- line while `field` sits far left, which closed the where-block early
-- and spilled all 44 of the tree's record fields into the scan.
record R2 (n : ℕ)
          (m : ℕ) : Set where
  field
    fld-a : suc n + 0 ≡ suc n
    fld-b : suc n * 1 ≡ suc n

-- MUST NOT FIRE against A.outer's local.  The two `helper`s share a
-- type deliberately: if the where-filter broke they would collide, and
-- the top-level `outer`s differ so only the locals can produce a group.
outer : ∀ (n : ℕ) → n * 1 ≡ n
outer n = helper
  where
  helper : n + 3 ≡ suc (suc (suc n))
