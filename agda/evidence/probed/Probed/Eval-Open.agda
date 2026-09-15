-- THE OPEN FORM AT THE BINDER THAT IS THE WHOLE REASON IT EXISTS: AN
-- ENVIRONMENT HOLDING AN OBSERVABLE.
--
-- WHAT IS AT RISK.  `dep-eval-open` prices an instance as a SUM, and a
-- sum is the right currency only if the environment is paid for ONCE.
-- The two ways it could be wrong are both about occurrence: a template
-- that reads its binder TWICE would pay twice if the reading added
-- over occurrences, and a template that WRAPS what it read climbs on
-- top of the addend rather than beside it.  Either would make the true
-- price a product in the occurrence count, which is the shape the size
-- half of this shelf was already found to have.
--
-- COVERAGE: the empty environment, where the row is TIGHT and the
-- statement degenerates to the closed drop; a data binder, likewise
-- contributing nothing; an observable binder read straight back; the
-- same binder WRAPPED under a `strmᵗ` the template writes; and the
-- same binder read TWICE, which is the row that decides the currency —
-- the reading joins over the occurrences, so the second costs nothing
-- and the price stays a sum.
--
-- NOT reached, and it cannot be: TIGHTNESS at an observable binder.
-- `envDepth` measures through `reify`, which writes a `strmᵗ` the
-- value does not have, so every such row carries exactly one of slack
-- and no choice of program removes it.  Also not reached: the
-- ITERATION axis, since one evaluation crosses one binder and the
-- growth a fold pays is per refold.
--
-- TARGET: dep-eval-open @0f3824
module Probed.Eval-Open where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Tm; Val; natᵗ; obs; varᵗ; nat̂; strmᵗ; ofᵉ;
  evalWith)
open import Rx.Obs-Depth using (depᵗ; depᵛ)
open import Rx.Obs-Depth.Substitution using (envDepth; dep-eval-open)

open import Probed.Apparatus using (Confirms; zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

----------------------------------------------------------------------
-- 0.  THE POINT EVERY ROW BELOW IS TAKEN AT: one observable, of
-- reading ONE, whose environment entry therefore measures TWO.
----------------------------------------------------------------------

Inner : _
Inner = obs natᵗ

o : Val Γ₀ (obs Inner)
o = ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])

o-reading : depᵛ {Γ = Γ₀} zeroη (obs Inner) o ≡ 1
o-reading = refl

o-entry : envDepth {Γ = Γ₀} zeroη (o ∷ᵃ []ᵃ) ≡ 2
o-entry = refl

----------------------------------------------------------------------
-- 1.  THE EMPTY ENVIRONMENT, WHICH IS TIGHT AND IS THE DEGENERATE ROW.
-- Nothing is substituted, so the addend is nought and the statement is
-- the closed reading with a `+ 0` on it.
----------------------------------------------------------------------

closed-tm : Tm Γ₀ [] [] [] natᵗ
closed-tm = nat̂ 7

row-empty : Confirms (dep-eval-open {Γ = Γ₀} zeroη closed-tm []ᵃ 0 z≤n)
row-empty = z≤n

----------------------------------------------------------------------
-- 2.  A DATA BINDER, WHICH IS DEGENERATE FOR THE SAME REASON ONE LEVEL
-- UP: a `nat̂` reifies to itself and reads nought, so the environment
-- still contributes nothing and the whole price is the template's.
----------------------------------------------------------------------

data-tm : Tm Γ₀ [] [] (natᵗ ∷ []) (obs natᵗ)
data-tm = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

row-data : Confirms
  (dep-eval-open {Γ = Γ₀} zeroη data-tm (7 ∷ᵃ []ᵃ) 0 z≤n)
row-data = z≤n

----------------------------------------------------------------------
-- 3.  THE BINDER READ STRAIGHT BACK, WHICH IS THE PASS-THROUGH THAT
-- REFUTES THE CLOSED FORM.  The template writes nothing, so the whole
-- price is the environment's — a reading no premise about the template
-- could have supplied.
----------------------------------------------------------------------

pass-tm : Tm Γ₀ [] [] (obs Inner ∷ []) (obs Inner)
pass-tm = varᵗ (here refl)

row-pass : Confirms
  (dep-eval-open {Γ = Γ₀} zeroη pass-tm (o ∷ᵃ []ᵃ) 2 (s≤s (s≤s z≤n)))
row-pass = s≤s z≤n

pass-template : depᵗ {Γ = Γ₀} zeroη pass-tm ≡ 0
pass-template = refl

----------------------------------------------------------------------
-- 4.  THE BINDER WRAPPED AGAIN, WHICH IS THE CLIMB.  Both addends are
-- non-zero here and the value lands one under their sum, so the row
-- separates a sum from a join: a join of one and two is two, and the
-- emission reads two, so a join would have been exactly saturated and
-- the next wrap would have broken it.
----------------------------------------------------------------------

wrap-tm : Tm Γ₀ [] [] (obs Inner ∷ []) (obs (obs Inner))
wrap-tm = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

row-wrap : Confirms
  (dep-eval-open {Γ = Γ₀} zeroη wrap-tm (o ∷ᵃ []ᵃ) 2 (s≤s (s≤s z≤n)))
row-wrap = s≤s (s≤s z≤n)

wrap-template : depᵗ {Γ = Γ₀} zeroη wrap-tm ≡ 1
wrap-template = refl

wrap-value : depᵛ {Γ = Γ₀} zeroη (obs (obs Inner))
               (evalWith wrap-tm (o ∷ᵃ []ᵃ)) ≡ 2
wrap-value = refl

----------------------------------------------------------------------
-- 5.  THE BINDER READ TWICE, WHICH IS THE ROW THE CURRENCY TURNS ON.
-- Were the price per OCCURRENCE the emission would read four against a
-- bound of three; the reading joins over the list, so the second
-- occurrence costs nothing and the emission is where one occurrence
-- left it.
----------------------------------------------------------------------

twice-tm : Tm Γ₀ [] [] (obs Inner ∷ []) (obs (obs Inner))
twice-tm = strmᵗ (ofᵉ (varᵗ (here refl) ∷ varᵗ (here refl) ∷ []))

row-twice : Confirms
  (dep-eval-open {Γ = Γ₀} zeroη twice-tm (o ∷ᵃ []ᵃ) 2 (s≤s (s≤s z≤n)))
row-twice = s≤s (s≤s z≤n)

twice-value : depᵛ {Γ = Γ₀} zeroη (obs (obs Inner))
                (evalWith twice-tm (o ∷ᵃ []ᵃ)) ≡ 2
twice-value = refl
