------------------------------------------------------------------
-- THE SPINE MEASURE: size along the hop-deepest path.
--
-- WHY IT EXISTS.  `hopDᵉ`'s scanᵉ clause pays `(2 + pmᵗ V 0 f) ^ V`,
-- and Rx.Hop-Depth's header justifies that exponent by "a fold that
-- deepens the accumulator adds at least one constructor, so
-- k ≤ sizeᵛ accₖ ≤ V".  The second half of that sentence is FALSE:
-- `Refuted.Hop-Drag` exhibits a fold step that DEEPENS the accumulator
-- while its `sizeᵛ` drops from 36 to 9.  A `caseᵗ` branch binds the
-- scrutinee's EVALUATED payload, so the branch's `strmᵗ` drags a copy
-- of that payload alone and a large shallow sibling is discarded free.
--
-- The claim is repaired, not abandoned, by measuring the right thing.
-- What the refuting step discards is a sibling that was never carrying
-- the depth; the deep component goes on being copied.  So count size
-- along the hop-deepest path only:
--
--   spn is sizeᵉ/sizeᵗ/sizeᵛ with `⊔` at exactly the positions where
--   hopD takes `⊔` — pairs, sums, `ofᵉ` lists, caseᵗ/ifᵗ branches —
--   and `+`/`suc` everywhere hopD concatenates or scales.
--
-- Two consequences, and they are the whole point:
--   · `spn≤size` (below) — so the store bound `sizeᵛ ≤ V` still caps it,
--     and the exponent's justification survives at V unchanged;
--   · on `Refuted.Hop-Drag`'s own run the spine is 4 ↦ 7 ↦ … , strictly
--     monotone across the very step that drops 27 units of total size.
--     Pinned there, beside the counterexample.
--
-- NOT A REPLACEMENT FOR sizeᵛ.  spn is an ⊔-of-branches, so it says
-- nothing about total syntax and must never be used where a size cap is
-- meant.  Its one job is to be the exponent that a fold cannot decrease.
------------------------------------------------------------------
module Rx.Hop-Spine where

open import Data.Nat  using (ℕ; suc; _+_; _⊔_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; +-mono-≤;
                                       +-assoc; ⊔-lub; m≤m+n; m≤n+m)
open import Relation.Binary.PropositionalEquality using (sym)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Val;
                          unitᵗ; boolᵗ; natᵗ; obs; _×ᵗ_; _+ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          flattenᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ)

mutual
  spnᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Exp Γ Δᵍ Δ Θ t → ℕ
  spnᵉ (input i)        = 1
  spnᵉ (ofᵉ ts)         = suc (spnᵗˢ ts)
  spnᵉ emptyᵉ           = 1
  spnᵉ (mapᵉ f e)       = suc (spnᵗ f + spnᵉ e)
  spnᵉ (takeᵉ c e)      = suc (spnᵗ c + spnᵉ e)
  spnᵉ (scanᵉ f z e)    = suc (spnᵗ f + spnᵗ z + spnᵉ e)
  spnᵉ (flattenᵉ lim e)    = suc (spnᵉ e)
  spnᵉ (switchAllᵉ e)   = suc (spnᵉ e)
  spnᵉ (exhaustAllᵉ e)  = suc (spnᵉ e)
  spnᵉ (μᵉ e)           = suc (spnᵉ e)
  spnᵉ (varᵉ x)         = 1
  spnᵉ (deferᵉ e)       = suc (spnᵉ e)

  -- the ⊔ clauses are pairᵗ, ifᵗ's branches and caseᵗ's branches —
  -- exactly hopDᵗ's ⊔ positions.  caseᵗ keeps `+` on the SCRUTINEE
  -- because hopDᵗ scales the scrutinee's depth into the branch.
  spnᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ Δᵍ Δ Θ t → ℕ
  spnᵗ (varᵗ x)      = 1
  spnᵗ unit̂          = 1
  spnᵗ (bool̂ _)      = 1
  spnᵗ (nat̂ _)       = 1
  spnᵗ (pairᵗ a b)   = suc (spnᵗ a ⊔ spnᵗ b)
  spnᵗ (fstᵗ p)      = suc (spnᵗ p)
  spnᵗ (sndᵗ p)      = suc (spnᵗ p)
  spnᵗ (inlᵗ a)      = suc (spnᵗ a)
  spnᵗ (inrᵗ a)      = suc (spnᵗ a)
  spnᵗ (caseᵗ s l r) = suc (spnᵗ s + (spnᵗ l ⊔ spnᵗ r))
  spnᵗ (ifᵗ c a b)   = suc (spnᵗ c + (spnᵗ a ⊔ spnᵗ b))
  spnᵗ (primᵗ _ a)   = suc (spnᵗ a)
  spnᵗ (strmᵗ e)     = suc (spnᵉ e)

  spnᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → List (Tm Γ Δᵍ Δ Θ t) → ℕ
  spnᵗˢ []       = 1
  spnᵗˢ (y ∷ ys) = spnᵗ y ⊔ spnᵗˢ ys

spnᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → ℕ
spnᵛ unitᵗ    _        = 1
spnᵛ boolᵗ    _        = 1
spnᵛ natᵗ     _        = 1
spnᵛ (s ×ᵗ t) (a , b)  = suc (spnᵛ s a ⊔ spnᵛ t b)
spnᵛ (s +ᵗ t) (inj₁ a) = suc (spnᵛ s a)
spnᵛ (s +ᵗ t) (inj₂ b) = suc (spnᵛ t b)
spnᵛ (obs t)  e        = spnᵉ e

------------------------------------------------------------------
-- THE TRANSFER.  Every ⊔ sits where size has a `+`, and every other
-- clause is size's verbatim — so the store bound caps the spine too,
-- and nothing downstream needs a second cap.
------------------------------------------------------------------

mutual
  spn≤sizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) →
    spnᵉ e ≤ sizeᵉ e
  spn≤sizeᵉ (input i)       = ≤-refl
  spn≤sizeᵉ (ofᵉ ts)        = s≤s (spn≤sizeᵗˢ ts)
  spn≤sizeᵉ emptyᵉ          = ≤-refl
  spn≤sizeᵉ (mapᵉ f e)      = s≤s (+-mono-≤ (spn≤sizeᵗ f) (spn≤sizeᵉ e))
  spn≤sizeᵉ (takeᵉ c e)     = s≤s (+-mono-≤ (spn≤sizeᵗ c) (spn≤sizeᵉ e))
  spn≤sizeᵉ (scanᵉ f z e)   =
    s≤s (+-mono-≤ (+-mono-≤ (spn≤sizeᵗ f) (spn≤sizeᵗ z)) (spn≤sizeᵉ e))
  spn≤sizeᵉ (flattenᵉ lim e)   = s≤s (spn≤sizeᵉ e)
  spn≤sizeᵉ (switchAllᵉ e)  = s≤s (spn≤sizeᵉ e)
  spn≤sizeᵉ (exhaustAllᵉ e) = s≤s (spn≤sizeᵉ e)
  spn≤sizeᵉ (μᵉ e)          = s≤s (spn≤sizeᵉ e)
  spn≤sizeᵉ (varᵉ x)        = ≤-refl
  spn≤sizeᵉ (deferᵉ e)      = s≤s (spn≤sizeᵉ e)

  spn≤sizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) →
    spnᵗ tm ≤ sizeᵗ tm
  spn≤sizeᵗ (varᵗ x)      = ≤-refl
  spn≤sizeᵗ unit̂          = ≤-refl
  spn≤sizeᵗ (bool̂ _)      = ≤-refl
  spn≤sizeᵗ (nat̂ _)       = ≤-refl
  spn≤sizeᵗ (pairᵗ a b)   =
    s≤s (⊔-lub (≤-trans (spn≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                (≤-trans (spn≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
  spn≤sizeᵗ (fstᵗ p)      = s≤s (spn≤sizeᵗ p)
  spn≤sizeᵗ (sndᵗ p)      = s≤s (spn≤sizeᵗ p)
  spn≤sizeᵗ (inlᵗ a)      = s≤s (spn≤sizeᵗ a)
  spn≤sizeᵗ (inrᵗ a)      = s≤s (spn≤sizeᵗ a)
  spn≤sizeᵗ (caseᵗ s l r) =
    s≤s (≤-trans (+-mono-≤ (spn≤sizeᵗ s)
                   (⊔-lub (≤-trans (spn≤sizeᵗ l) (m≤m+n (sizeᵗ l) (sizeᵗ r)))
                           (≤-trans (spn≤sizeᵗ r) (m≤n+m (sizeᵗ r) (sizeᵗ l)))))
                 (≤-reflexive (sym (+-assoc (sizeᵗ s) (sizeᵗ l) (sizeᵗ r)))))
  spn≤sizeᵗ (ifᵗ c a b)   =
    s≤s (≤-trans (+-mono-≤ (spn≤sizeᵗ c)
                   (⊔-lub (≤-trans (spn≤sizeᵗ a) (m≤m+n (sizeᵗ a) (sizeᵗ b)))
                           (≤-trans (spn≤sizeᵗ b) (m≤n+m (sizeᵗ b) (sizeᵗ a)))))
                 (≤-reflexive (sym (+-assoc (sizeᵗ c) (sizeᵗ a) (sizeᵗ b)))))
  spn≤sizeᵗ (primᵗ _ a)   = s≤s (spn≤sizeᵗ a)
  spn≤sizeᵗ (strmᵗ e)     = s≤s (spn≤sizeᵉ e)

  spn≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    spnᵗˢ ts ≤ sizeᵗˢ ts
  spn≤sizeᵗˢ []       = ≤-refl
  spn≤sizeᵗˢ (y ∷ ys) =
    ⊔-lub (≤-trans (spn≤sizeᵗ y) (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
           (≤-trans (spn≤sizeᵗˢ ys) (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))

spn≤sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → spnᵛ t v ≤ sizeᵛ t v
spn≤sizeᵛ unitᵗ    _        = ≤-refl
spn≤sizeᵛ boolᵗ    _        = ≤-refl
spn≤sizeᵛ natᵗ     _        = ≤-refl
spn≤sizeᵛ (s ×ᵗ t) (a , b)  =
  s≤s (⊔-lub (≤-trans (spn≤sizeᵛ s a) (m≤m+n (sizeᵛ s a) (sizeᵛ t b)))
              (≤-trans (spn≤sizeᵛ t b) (m≤n+m (sizeᵛ t b) (sizeᵛ s a))))
spn≤sizeᵛ (s +ᵗ t) (inj₁ a) = s≤s (spn≤sizeᵛ s a)
spn≤sizeᵛ (s +ᵗ t) (inj₂ b) = s≤s (spn≤sizeᵛ t b)
spn≤sizeᵛ (obs t)  e        = spn≤sizeᵉ e
