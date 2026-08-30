-- ══════════════════════════════════════════════════════════════════
-- THE CAPS PREMISE DOES NOT SURVIVE THE ONE HEAD THAT INSTALLS AN
-- EVALUATED VALUE, so the nest walk cannot recurse through a `scanᵉ`
-- at the cap it was entered at.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  The shared statement the nest walk instantiates
-- at every head carries `capsOK? c` on the state it is handed, and each
-- head re-establishes it for its child.  Four heads install nothing, the
-- filter head installs a COUNTER -- which `boundedNode` reads as bounded
-- at every cap -- and the *All heads install their own empty state.  The
-- scan head is the only one that installs a VALUE, and the obvious
-- reading is that its `valCaps?` premise pays for it: the premise caps
-- the head's syntax, and the seed is a subterm of the head.
--
-- WHERE IT BREAKS.  The seed is installed EVALUATED, and evaluation
-- grows size -- a `caseᵗ` binds its scrutinee's value and an arm naming
-- that binder twice returns two copies of it.  `boundedNode` reads the
-- installed node at `sizeᵛ`, so what has to fit under the cap is the
-- VALUE's size and what the premise bounds is the TERM's.  At the
-- witness below the head's syntax is thirty-nine nodes and the seed
-- evaluates to forty-five, so the smallest cap the `valCaps?` premise
-- admits is already too small by six.
--
-- WHAT DIES AND WHAT DOES NOT.  The scan head's own bound is untouched:
-- the DEPTH of an evaluated seed is what `evalTm-nest-sync` bounds, and
-- the grant has room for it.  What dies is recursing at a
-- FIXED cap.  The caps face reached the same wall and answered it by
-- STEPPING the cap -- a scan reports `frameStep (j + j′)` and charges
-- `j′` -- and a stepped cap is the wrong direction for a grant keyed on
-- `cSize`, since a bigger key is a bigger grant and the parent owes the
-- smaller one.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Seed-Caps where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Fn; Tm; Ctx; Ty; natᵗ; obs; _×ᵗ_; ofᵉ; emptyᵉ; scanᵉ; varᵗ; nat̂; pairᵗ; fstᵗ; inlᵗ;
  caseᵗ; strmᵗ; evalTm; sizeᵉ; sizeᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; mintNode; installNode; scan-st; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Refuted.Demand-Programs using (Γ₂; insT)

----------------------------------------------------------------------
-- THE WITNESS.  A scan whose seed is a `caseᵗ` returning two copies of
-- what it bound.  Nothing about the scan itself matters -- the step
-- function is a projection and the source is one nat -- so the whole of
-- the finding is in the seed.
----------------------------------------------------------------------

slots : Slots Γ₂
slots = insT 0 0 0

Two : Ty
Two = obs natᵗ ×ᵗ obs natᵗ

big : Closed Γ₂ natᵗ
big = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ nat̂ 7 ∷
           nat̂ 8 ∷ nat̂ 9 ∷ nat̂ 10 ∷ nat̂ 11 ∷ nat̂ 12 ∷ nat̂ 13 ∷ nat̂ 14 ∷
           nat̂ 15 ∷ nat̂ 16 ∷ nat̂ 17 ∷ nat̂ 18 ∷ nat̂ 19 ∷ [])

seed : Tm Γ₂ [] [] [] Two
seed = caseᵗ {s = obs natᵗ} {t = natᵗ} (inlᵗ (strmᵗ big))
         (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))
         (pairᵗ (strmᵗ emptyᵉ) (strmᵗ emptyᵉ))

step : Fn Γ₂ [] [] [] (Two ×ᵗ natᵗ) Two
step = fstᵗ (varᵗ (here refl))

src : Closed Γ₂ natᵗ
src = ofᵉ (nat̂ 0 ∷ [])

prog : Closed Γ₂ Two
prog = scanᵉ step seed src

-- the cap is the SMALLEST the `valCaps?` premise admits, which is what
-- makes this a crossing rather than a badly chosen number
c₁ : Caps
c₁ = caps (sizeᵉ prog) 100 100

sched₁ : Sched Γ₂
sched₁ = sched-init prog slots

st₁ : EvalSt prog
st₁ = st-init prog

----------------------------------------------------------------------
-- THE FIGURES, PINNED.
----------------------------------------------------------------------

syn≡39 : sizeᵉ prog ≡ 39
syn≡39 = refl

val≡45 : sizeᵛ Two (evalTm seed) ≡ 45
val≡45 = refl

capsBefore : capsOK? c₁ sched₁ st₁ ≡ true
capsBefore = refl

valOK : valCaps? c₁ slots (obs Two) prog ≡ true
valOK = refl

capsAfter : capsOK? c₁ (proj₂ (mintNode sched₁))
              (installNode (proj₁ (mintNode sched₁)) (scan-st (evalTm seed)) st₁)
              ≡ false
capsAfter = refl

----------------------------------------------------------------------
-- THE ABSURDITY.
----------------------------------------------------------------------

scan-seed-caps-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
     (c : Caps) (sl : Slots Γ) (f : Fn Γ [] [] [] (u ×ᵗ s) u)
     (z : Tm Γ [] [] [] u) (b : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
     Sched.slots sched ≡ sl →
     capsOK? c sched st ≡ true →
     valCaps? c sl (obs u) (scanᵉ f z b) ≡ true →
     capsOK? c (proj₂ (mintNode sched))
       (installNode (proj₁ (mintNode sched)) (scan-st (evalTm z)) st) ≡ true)
  → ⊥
scan-seed-caps-absurd h
  with h c₁ slots step seed src sched₁ st₁ refl capsBefore valOK
... | ()
