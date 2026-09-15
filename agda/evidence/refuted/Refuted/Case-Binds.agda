-- THE JOIN OVER A `caseᵗ`'S THREE SUBTERMS, WHICH IS THE READING THIS
-- ARM USED TO TAKE.
--
-- Every head of the term language but one leaves the environment the
-- run was called with alone, and for those a join is exactly right: the
-- subterms are alternatives or siblings, so the deepest of them is what
-- gets written.  `caseᵗ` is the exception.  It evaluates its scrutinee
-- and BINDS what came out, so the branch runs under an environment the
-- caller never supplied, and a branch that WRAPS its binder writes on
-- top of the scrutinee's nesting instead of beside it.  The two compose
-- by addition, and no join of the three can see that.
--
-- THE WITNESS.  A scrutinee the template writes three deep, a left
-- branch wrapping its binder twice, and a right branch that writes one
-- and never runs — evaluated in the EMPTY environment, so nothing is
-- hidden in a hypothesis and the reading is the program's alone.  The
-- join reads three; the emission lands at four, which is the branch's
-- two climbing on the scrutinee's inner two.  Both figures are claimed,
-- because the finding is the gap: a repair moving either end alone
-- would leave a witness reporting numbers that no longer meet.
--
-- WHAT IT COST WHEN IT WAS LIVE.  The join was the reading, so this
-- same program met two statements over it at once — the open form,
-- which claimed the join, and the closed form, which claimed its
-- PREDECESSOR and so missed by twice as much.  The closed form is gated
-- on the environment being DATA and the empty environment is data, so
-- the gate stood open at the witness that breaks it: the observable is
-- not in the environment, it is in the scrutinee.  The data hypothesis
-- isolates the environment, and this arm makes its own.
--
-- WHAT IT DOES NOT REACH.  A scrutinee coming FROM the environment,
-- which is already paid for: a reading of an environment measures
-- through `reify`, so the branch's wrap climbs on a figure the open
-- form's premise bounds.  And `ifᵗ`, which selects between two branches
-- without binding anything, so the join there is untouched by this.
module Refuted.Case-Binds where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ)
open import Data.Nat using (ℕ; _≤_; _⊔_; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Ty; Tm; Exp; natᵗ; unitᵗ; obs; _+ᵗ_; varᵗ;
  nat̂; inlᵗ; caseᵗ; strmᵗ; ofᵉ; emptyᵉ; evalWith)
open import Rx.Obs-Depth using (depᵗ; depᵛ)

open import Refuted.Apparatus using (zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

----------------------------------------------------------------------
-- 1.  THE SCRUTINEE, WHICH THE TEMPLATE WRITES.  Three `strmᵗ` heads
-- over a numeral, so the term reads three and the VALUE it evaluates to
-- — the inner expression, one head peeled — reads two.
----------------------------------------------------------------------

Deep : Ty
Deep = obs (obs (obs natᵗ))

inner : Exp Γ₀ [] [] [] (obs (obs natᵗ))
inner = ofᵉ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])) ∷ [])

scrut : Tm Γ₀ [] [] [] (Deep +ᵗ unitᵗ)
scrut = inlᵗ (strmᵗ inner)

scrut-is : depᵗ {Γ = Γ₀} zeroη scrut ≡ 3
scrut-is = refl

----------------------------------------------------------------------
-- 2.  THE BRANCHES.  The left wraps its binder under two heads; the
-- right writes one and never runs.  Neither reaches the scrutinee's
-- three, so the join is the scrutinee's.
----------------------------------------------------------------------

left : Tm Γ₀ [] [] (Deep ∷ []) (obs (obs Deep))
left = strmᵗ (ofᵉ (strmᵗ (ofᵉ (varᵗ (here refl) ∷ [])) ∷ []))

right : Tm Γ₀ [] [] (unitᵗ ∷ []) (obs (obs Deep))
right = strmᵗ emptyᵉ

left-is : depᵗ {Γ = Γ₀} zeroη left ≡ 2
left-is = refl

right-is : depᵗ {Γ = Γ₀} zeroη right ≡ 1
right-is = refl

----------------------------------------------------------------------
-- 3.  THE CANDIDATE, STATED OVER THE REAL READING OF THE THREE
-- SUBTERMS.  Only this arm is written out, because only this arm is
-- what is being refuted: every other clause of the reading is the one
-- `src` carries, so a move anywhere underneath breaks a numeral here
-- rather than going quiet.
----------------------------------------------------------------------

joined : ℕ
joined = depᵗ {Γ = Γ₀} zeroη scrut
       ⊔ depᵗ {Γ = Γ₀} zeroη left
       ⊔ depᵗ {Γ = Γ₀} zeroη right

joined-is : joined ≡ 3
joined-is = refl

----------------------------------------------------------------------
-- 4.  THE TWO FIGURES THAT MEET, AND THE REFUTATION BETWEEN THEM.
----------------------------------------------------------------------

tm : Tm Γ₀ [] [] [] (obs (obs Deep))
tm = caseᵗ scrut left right

emission-is : depᵛ {Γ = Γ₀} zeroη (obs (obs Deep)) (evalWith tm []ᵃ) ≡ 4
emission-is = refl

case-join-false :
  ¬ (depᵛ {Γ = Γ₀} zeroη (obs (obs Deep)) (evalWith tm []ᵃ) ≤ joined)
case-join-false (s≤s (s≤s (s≤s ())))
