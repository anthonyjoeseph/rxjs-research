-- ══════════════════════════════════════════════════════════════════
-- THE DRAG ARGUMENT DOES NOT COVER A BINDER.
--
-- `walk-scan-hop` (.Walk-Level) carries the accumulator invariant
-- `hopDᵛ accᵢ ≤ (1 + P) ^ sizeᵛ accᵢ * B` along scanVals' fold.  Against
-- hopD-applyFn that splits on the step's effect on the SIZE: the
-- size-increasing arm closes on one binomial step, and the whole residue
-- is the size-PRESERVING arm, which needs "a step that does not grow the
-- accumulator cannot deepen it either".
--
-- Demand-Probe series Y made that look safe.  A step can only mention the
-- accumulator inside a `strmᵗ` by substitution, and `subΘ` substitutes the
-- whole reified argument syntactically — projections are not reduced away
-- — so a wrapper that deepens the accumulator drags a full copy of it and
-- pays in size.  Series Y ran the sharpest attack available on that (wrap
-- one component of a pair, discard a large shallow sibling) and the refund
-- was never collected: 34 ↦ 51 ↦ 68 monotone.
--
-- THE DRAG HAS A HOLE, AND IT IS `caseᵗ`.  A caseᵗ branch binds the
-- SCRUTINEE'S PAYLOAD, and evalWith has already EVALUATED the scrutinee
-- before the branch is substituted — so the branch's `strmᵗ` drags a copy
-- of that payload alone, not of the argument it was projected out of.
-- Scrutinising the small deep component therefore wraps it while the large
-- shallow sibling is discarded for free, which is exactly the trade series
-- Y could not make.  `fᶻ` below does it, and the arm is NOT empty:
--
--     step   0     1     2     3
--     size   36 ↦  9  ↦ 13  ↦ 17          hopDᵗ fᶻ ≡ 1
--     hopD    1 ↦  2  ↦  3  ↦  4
--
-- The first step SHRINKS the accumulator by 27 and DEEPENS it — so the
-- statement below, the size-preserving arm's whole content, is false.
--
-- WHAT SURVIVES, and it is why the theorem is not in doubt: the refund is
-- ONE-SHOT.  The sibling slot is spent by the step that discards it, and
-- from there the deep chain can only grow — a flat +4 of size per +1 of
-- depth.  So the pool a shrinking step draws on is bounded by the
-- accumulator's INITIAL size, which the store invariant caps at V.  The
-- repair is therefore a bound in terms of the value's OWN size rather
-- than a per-step comparison; see walk-scan-hop's header.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Hop-Drag where

open import Data.Empty using (⊥)
open import Data.Nat   using (ℕ; suc; _≤_; _⊔_; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Unit  using (tt)
open import Data.List  using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec   using () renaming ([] to []ⱽ)
open import Data.Product using (_,_)
open import Data.Sum   using (inj₁)
open import Data.Fin   using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ty; Ctx; natᵗ; obs; _×ᵗ_; _+ᵗ_;
                          ofᵉ; emptyᵉ; mergeAllᵉ;
                          strmᵗ; fstᵗ; varᵗ; nat̂; inlᵗ; caseᵗ; pairᵗ;
                          sizeᵛ; Tm; Fn; Val; applyFn)
open import Rx.Hop-Depth using (hopDᵗ; hopDᵛ)

Γᶻ : Ctx 0
Γᶻ = []ⱽ

-- THE STATEMENT.  Read it as the size-preserving arm asks for it: the
-- hypothesis compares the NEW accumulator against the OLD one (not
-- against the step's whole argument), which is the strongest form —
-- anything weaker is refuted a fortiori.
NoDeepenWithoutGrowth : Set
NoDeepenWithoutGrowth =
  ∀ {n} {Γ : Ctx n} {s u} (V : ℕ) (η : Fin n → ℕ)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (a : Val Γ u) (x : Val Γ s) →
    sizeᵛ u (applyFn f (a , x)) ≤ sizeᵛ u a →
    hopDᵛ V η u (applyFn f (a , x))
      ≤ hopDᵗ V η f ⊔ hopDᵛ V η u a ⊔ hopDᵛ V η s x

-- depth 1, size 2 — the small deep component the step will wrap
dᶻ : Val Γᶻ (obs natᵗ)
dᶻ = mergeAllᵉ emptyᵉ

-- a sum in the first slot so the step can SCRUTINISE it; a plain shallow
-- payload in the second, which is what the step throws away
Uᶻ : Ty
Uᶻ = (obs natᵗ +ᵗ obs natᵗ) ×ᵗ obs natᵗ

bigᶻ : Val Γᶻ (obs natᵗ)
bigᶻ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
            nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
            nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷
            nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

-- THE STEP.  Both branches are the same wrapper; what matters is that the
-- payload reaches `strmᵗ` through the caseᵗ BINDER, so subΘ copies the
-- payload and nothing else.  The sibling slot is refilled from the
-- template, at size 1.
fᶻ : Fn Γᶻ [] [] [] (Uᶻ ×ᵗ natᵗ) Uᶻ
fᶻ = pairᵗ (caseᵗ (fstᵗ (fstᵗ (varᵗ (here refl))))
             (inlᵗ (strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ [])))))
             (inlᵗ (strmᵗ (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))))
           (strmᵗ emptyᵉ)

-- reached by iterating the step, not hand-built
accᶻ : ℕ → Val Γᶻ Uᶻ
accᶻ 0       = inj₁ dᶻ , bigᶻ
accᶻ (suc k) = applyFn fᶻ (accᶻ k , 0)

-- THE TRADE.  LOAD-BEARING both ways: the size row must SHRINK (else the
-- step is in the already-closed arm) and the depth row must GROW (else
-- there is nothing to refute).
_ : sizeᵛ Uᶻ (accᶻ 0) ≡ 36
_ = refl
_ : sizeᵛ Uᶻ (accᶻ 1) ≡ 9
_ = refl
_ : ∀ (V : ℕ) → hopDᵛ V (λ _ → 0) Uᶻ (accᶻ 0) ≡ 1
_ = λ _ → refl
_ : ∀ (V : ℕ) → hopDᵛ V (λ _ → 0) Uᶻ (accᶻ 1) ≡ 2
_ = λ _ → refl
_ : ∀ (V : ℕ) → hopDᵗ V (λ _ → 0) fᶻ ≡ 1
_ = λ _ → refl

-- THE REFUND IS ONE-SHOT — this is what keeps the theorem alive, and it
-- is the row that says the repair is a bound on the value's own size.
-- After the sibling is spent the trade is unavailable and the chain pays
-- a flat +4 of size for each +1 of depth.
_ : sizeᵛ Uᶻ (accᶻ 2) ≡ 13
_ = refl
_ : sizeᵛ Uᶻ (accᶻ 3) ≡ 17
_ = refl
_ : ∀ (V : ℕ) → hopDᵛ V (λ _ → 0) Uᶻ (accᶻ 3) ≡ 4
_ = λ _ → refl

hop-drag-absurd : NoDeepenWithoutGrowth → ⊥
hop-drag-absurd h with h 0 (λ _ → 0) fᶻ (accᶻ 0) 0 (≤ᵇ⇒≤ 9 36 tt)
... | s≤s ()
