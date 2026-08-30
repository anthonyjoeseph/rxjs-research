-- ══════════════════════════════════════════════════════════════════
-- THE WALK'S ENTRY KEYS CANNOT BE PRODUCED FROM THE WALK'S OWN
-- PREMISES.  The path key is the half that breaks, and it breaks for
-- a reason no strengthening of the caps or the slot table repairs:
-- nothing in the hypothesis bundle mentions the path at all except
-- through two measures that a one-shot source drives to zero.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAYS.  At a cap, a slot table and a state inside
-- the invariant, there is a LEVEL at which the caps face's five entry
-- keys all hold -- and the level is under the instant's own ceiling,
-- which is the conjunct that stops the claim from being satisfied by
-- taking the level enormous.
--
-- WHERE IT BREAKS.  The ceiling is fixed by the cap and the descent
-- DEPTH, and the depth of a one-shot is zero whatever path it is
-- subscribed under -- so the ceiling is one number for every path in
-- the family at once.  The size field at that ceiling is therefore
-- also one number, and the path key asks it to exceed the length of a
-- path the statement quantifies over freely.  A path one frame longer
-- than that number refutes it, and such a path exists for the same
-- reason the ceiling is a number: it is built by recursion on it.
--
-- Note that this is not an arithmetic near-miss to be closed by a
-- wider cap.  The witness is defined FROM whatever bound the statement
-- offers, so every enlargement of the cap enlarges the counterexample
-- with it.
--
-- WHAT THIS DOES NOT SHOW.  It says nothing about the four other keys,
-- which read the source and the table and are plausibly derivable
-- where the path key is not; and it says nothing against the same
-- keys threaded as PREMISES at a level, which is what the proven
-- burst face does and what this refutation licenses.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Caps-Keys where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _⊔_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤; 1+n≰n; +-identityʳ)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp using (Closed; natᵗ; obs; ofᵉ; nat̂; sizeᵉ)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (root; sched-init; st-init; EvalSt; Sched; Path; _↠_; take-f; opIterD)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; frameStep; sizeCount; frameStep-mono-j; opIterD-infl)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Nest-Burst using (descW)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?; capsOK?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Verify-Budget-Sufficient.Nest-Walk using (nestClosOK?; FaceOK; faceOK)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs g0)))

-- a one-shot: it reaches no subscribe, so its descent depth is zero at
-- EVERY path, which is what freezes the ceiling
src : Closed Γ₂ natᵗ
src = ofᵉ (nat̂ 0 ∷ [])

cap : Caps
cap = caps 256 2 1

sched₀ : Sched Γ₂
sched₀ = sched-init src slots

st₀ : EvalSt src
st₀ = st-init src

face : FaceOK cap slots
face = faceOK (≤ᵇ⇒≤ 2 256 tt) ≤-refl refl
              (≤ᵇ⇒≤ (slotsSize slots) 256 tt)

-- THE CEILING THE STATEMENT PROMISES TO STAY UNDER, at the depth a
-- one-shot reports, and the size field it grants there
ceil : ℕ
ceil = sizeCount cap 0 ⊔ Caps.cSize cap

grant : ℕ
grant = Caps.cSize (frameStep ceil cap)

-- a path of any requested length, built by recursion on the number the
-- ceiling names -- so the witness is not a numeral and needs none
long : ℕ → Path Γ₂ natᵗ natᵗ
long zero    = root
long (suc k) = take-f 0 ↠ long k

long-len : ∀ (k : ℕ) → pathLen (long k) ≡ k
long-len zero    = refl
long-len (suc k) rewrite long-len k = refl

κ : Path Γ₂ natᵗ natᵗ
κ = long grant

W : ℕ
W = descW gasBig src κ 0 0 sched₀ st₀

Stmt : Set
Stmt =
  FaceOK cap slots →
  Sched.slots sched₀ ≡ slots →
  capsOK? cap sched₀ st₀ ≡ true →
  nestValOK? cap (obs natᵗ) src ≡ true →
  nestClosOK? cap slots src ≡ true →
  descW gasBig src κ 0 0 sched₀ st₀ ≤ W →
  depthE gasBig src κ 0 0 sched₀ st₀ ≤ 0 →
  Σ ℕ λ L →
    (∀ (L′ : ℕ) →
       L + L′ ≤ opIterD (Caps.cSize cap) (Caps.cWid cap)
                  (depthE gasBig src κ 0 0 sched₀ st₀)
                  (nest src slots (EvalSt.connectedShares st₀)) (suc (sizeᵉ src)) L →
       L + L′ ≤ sizeCount cap 0 ⊔ Caps.cSize cap)
    × (capsOK? (frameStep L cap) sched₀ st₀ ≡ true)
    × (sizeᵉ src ≤ Caps.cSize (frameStep L cap))
    × (dWᵉ 2 slots src ≤ Caps.cWid (frameStep L cap))
    × (pathSz? (Caps.cSize (frameStep L cap)) κ ≡ true)
    × (suc (pathLen κ) ≤ Caps.cSize (frameStep L cap))

nest-caps-keys-absurd : Stmt → ⊥
nest-caps-keys-absurd h
  with h face refl refl refl refl ≤-refl ≤-refl
... | L , pr , _ , _ , _ , _ , hpl = 1+n≰n grant≥
  where
  L≤ceil : L ≤ ceil
  L≤ceil = subst (_≤ ceil) (+-identityʳ L)
             (pr 0 (subst (_≤ opIterD (Caps.cSize cap) (Caps.cWid cap)
                                 (depthE gasBig src κ 0 0 sched₀ st₀)
                                 (nest src slots (EvalSt.connectedShares st₀))
                                 (suc (sizeᵉ src)) L)
                          (sym (+-identityʳ L))
                          (opIterD-infl (Caps.cSize cap) (Caps.cWid cap)
                             (depthE gasBig src κ 0 0 sched₀ st₀)
                             (nest src slots (EvalSt.connectedShares st₀))
                             (suc (sizeᵉ src)) L)))

  grant≥ : suc grant ≤ grant
  grant≥ = ≤-trans (subst (λ x → suc x ≤ Caps.cSize (frameStep L cap))
                          (long-len grant) hpl)
                   (proj₁ (frameStep-mono-j cap (≤ᵇ⇒≤ 2 256 tt) L≤ceil))
