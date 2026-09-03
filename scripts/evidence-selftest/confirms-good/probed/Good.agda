-- The legal shapes: the target applied at a point; a conjunct projected out;
-- a ∀ applied at a point; a field of a record conclusion; a Σ given its
-- witness; a ≤ through the stdlib converter; and a row over several clauses.
-- TARGET: live-one @b6f6f3
-- TARGET: live-two @000000
module Good where
row : Confirms (live-one 3)
row = refl
conj : Confirms (proj₁ (live-two prog 0))
conj = tt
point : Confirms (proj₂ (proj₂ (live-two prog 0)) 4)
point = ≤ᵇ⇒≤ _ _ tt
field-row : Confirms (Fit.grant (live-two prog 1))
field-row = 2 , refl
rungs : (d : Fin 2) → Confirms (live-one (toℕ d))
rungs fzero        = refl
rungs (fsuc fzero) =
  refl
