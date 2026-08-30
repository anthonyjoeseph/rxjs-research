-- ══════════════════════════════════════════════════════════════════
-- THE NEST CONE CANNOT PAY THE CAPS FACE'S SIZE PREMISE, so the
-- CONVERSION both descent rows say they are owed is not available.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  The nest walk's two remaining descent rows are
-- stated over a WEAKER state predicate than the proven caps face, and
-- their headers name the repair as a conversion: discharge each from
-- the proven face rather than proving it again.  The proven face takes
-- `sizeᵉ b ≤ Caps.cSize c` on the subscribed source, so the conversion
-- is exactly the claim that the nest cone's own premises supply it.
--
-- WHERE IT BREAKS, AND IT IS A CURRENCY AND NOT A LEVEL.  The only two
-- premises in that cone mentioning the source read it on the SYNC
-- spine and through the slot closure, and both are LEAVES at `deferᵉ`
-- while the caps face's `sizeᵉ` recurses through it.  So a source that
-- is a stack of defers over a one-shot holds both keys at a constant
-- while its size grows without bound, and the witness below is built
-- by recursion on whatever cap is offered -- no level, no widening and
-- no larger cap moves it, because the level device acts on the cap and
-- the gap is on the other side.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing against the rows
-- themselves, which may well be true; it kills the ROUTE.  Nor does it
-- argue for re-keying the nest walk to `sizeᵛ`: the sync spine is
-- deliberate -- what a defer gates is not subscribed in the instant --
-- so the two faces are in different currencies for a reason, and what
-- the rows need is a state-side descent proven in the nest currency.
-- The WIDTH half of the caps face's entry keys is NOT part of this
-- finding: `expWid-fromSize` derives it from the size at a level, so
-- once a size is in hand the width costs nothing.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Size-Currency where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤; 1+n≰n; m≤m+n)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import Rx.Exp using (Closed; natᵗ; obs; ofᵉ; nat̂; strmᵗ; deferᵉ; mergeAllᵉ; sizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; nestClosOK?)
open import Verify-Budget-Sufficient.Nest-Walk using (FaceOK; faceOK)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

cap : Caps
cap = caps 256 2 1

face : FaceOK cap slots
face = faceOK (≤ᵇ⇒≤ 2 256 tt) ≤-refl refl
              (≤ᵇ⇒≤ (slotsSize slots) 256 tt)

----------------------------------------------------------------------
-- THE WITNESS.  A one-shot behind a stack of defers.  The stack is a
-- free parameter and only `sizeᵉ` can see it.
----------------------------------------------------------------------

base : Closed Γ₂ (obs natᵗ)
base = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

defers : ℕ → Closed Γ₂ (obs natᵗ) → Closed Γ₂ (obs natᵗ)
defers zero    b = b
defers (suc k) b = deferᵉ (defers k b)

size-defers : ∀ k b → sizeᵉ (defers k b) ≡ k + sizeᵉ b
size-defers zero    b = refl
size-defers (suc k) b = cong suc (size-defers k b)

-- the two keys the cone carries, at EVERY stack height: both read the
-- outermost defer as a leaf, so neither is a function of k
valKey : ∀ k → nestValOK? cap (obs natᵗ) (mergeAllᵉ nothing (defers (suc k) base)) ≡ true
valKey k = refl

closKey : ∀ k → nestClosOK? cap slots (mergeAllᵉ nothing (defers (suc k) base)) ≡ true
closKey k = refl

----------------------------------------------------------------------
-- THE STATEMENT THE CONVERSION NEEDS, and its refutation.
----------------------------------------------------------------------

SizeFromNest : Set
SizeFromNest = (b : Closed Γ₂ (obs natᵗ)) (lim : Maybe ℕ) →
  nestValOK? cap (obs natᵗ) (mergeAllᵉ lim b) ≡ true →
  nestClosOK? cap slots (mergeAllᵉ lim b) ≡ true →
  FaceOK cap slots →
  sizeᵉ b ≤ Caps.cSize cap

size-from-nest-absurd : SizeFromNest → ⊥
size-from-nest-absurd pr =
  1+n≰n (≤-trans (m≤m+n (suc K) (sizeᵉ base))
                 (subst (_≤ K) (size-defers (suc K) base)
                        (pr (defers (suc K) base) nothing
                            (valKey K) (closKey K) face)))
  where
  K = Caps.cSize cap
