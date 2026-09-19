-- fixture: the two datatypes the checker reads, with a shared-signature
-- constructor pair, a comment line and a `mutual` sibling beside the block
mutual
  data Exp {n} (Γ : Ctx n) : Ty → Set where
    liftᵉ : Fn → Exp Γ t
    -- a comment, which is not a constructor
    deferᵉ sharedSigᵉ : Exp Γ t

  Fn : Set
  Fn = Tm

  data Tm (Γ : Ctx n) : Ty → Set where
    nat̂ : ℕ → Tm Γ natᵗ

data PrimOp : Ty → Ty → Set where
  add : PrimOp (natᵗ ×ᵗ natᵗ) natᵗ
  notᵖ : PrimOp boolᵗ boolᵗ
