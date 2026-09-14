-- THE THREE ARMS THE STRICT DROP COULD NOT TAKE ITSELF, INSTANTIATED
-- AT THE BINDER THAT IS THE WHOLE REASON THEY ARE SEPARATE.
--
-- WHAT IS AT RISK.  `dep-eval-strict` is an induction over the term,
-- and it runs out at exactly the two heads that BIND into their own
-- subterms: a `caseᵗ` puts the scrutinee's payload into the branch
-- environment, so the branch is evaluated under an environment the
-- data hypothesis does not cover.  Where that payload is an
-- OBSERVABLE the branch can hand it straight back, and then the
-- value's reading comes from the scrutinee rather than from the head
-- the bound is stated over — which is the way these two could be
-- false.
--
-- COVERAGE: a `caseᵗ` at a data payload with both branches writing,
-- and at an OBSERVABLE payload handed back by the branch — the row
-- that reaches the risk, and it is TIGHT, the value's reading landing
-- exactly on the predecessor.  An `ifᵗ` at a selected branch that is
-- the deeper of the two and at one that is not.
--
-- NOT reached: a `caseᵗ` whose branches differ in reading with the
-- observable arm selected — the join takes the deeper, so such a row
-- has slack by construction and cannot fail.
--
-- TARGET: eval-case @64558a
-- TARGET: eval-if @e9a512
module Probed.Eval-Binders where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (z≤n; s≤s)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Tm; unitᵗ; natᵗ; _+ᵗ_; obs; varᵗ; unit̂; bool̂; nat̂; inlᵗ; caseᵗ; strmᵗ; ofᵉ; evalWith)
open import Rx.Obs-Depth using (depᵗ; depᵛ)
open import Rx.Obs-Depth.Substitution using (AllData; []ᵈ;
  eval-case; eval-if)

open import Probed.Apparatus using (Confirms; zeroη)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

dd₀ : AllData []
dd₀ = []ᵈ

----------------------------------------------------------------------
-- 1.  THE BRANCH AT A DATA PAYLOAD.  Both arms write one level, so the
-- join is one and the predecessor is nought — the tightest point the
-- statement has at a data binder.
----------------------------------------------------------------------

one-level : Tm Γ₀ [] [] (unitᵗ ∷ []) (obs natᵗ)
one-level = strmᵗ (ofᵉ (nat̂ 7 ∷ []))

data-sc : Tm Γ₀ [] [] [] (unitᵗ +ᵗ unitᵗ)
data-sc = inlᵗ unit̂

row-case-data : Confirms
  (eval-case {Γ = Γ₀} zeroη dd₀ data-sc one-level one-level []ᵃ)
row-case-data = z≤n

case-data-bound : depᵗ {Γ = Γ₀} zeroη (caseᵗ data-sc one-level one-level) ≡ 1
case-data-bound = refl

----------------------------------------------------------------------
-- 2.  THE BRANCH AT AN OBSERVABLE PAYLOAD, WHICH IS THE ROW THAT
-- REACHES THE RISK.  The scrutinee carries an observable, the branch
-- is the variable that names it, and the value handed back is
-- therefore the scrutinee's — read against a bound stated over the
-- `caseᵗ`.  It lands exactly on the predecessor.
----------------------------------------------------------------------

Inner : _
Inner = obs natᵗ

obs-sc : Tm Γ₀ [] [] [] (obs Inner +ᵗ unitᵗ)
obs-sc = inlᵗ (strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ [])))

hands-back : Tm Γ₀ [] [] (obs Inner ∷ []) (obs Inner)
hands-back = varᵗ (here refl)

other-arm : Tm Γ₀ [] [] (unitᵗ ∷ []) (obs Inner)
other-arm = strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ []))

row-case-obs : Confirms
  (eval-case {Γ = Γ₀} zeroη dd₀ obs-sc hands-back other-arm []ᵃ)
row-case-obs = s≤s z≤n

-- the two figures that make the row tight rather than slack: the
-- bound's predecessor and the value's own reading are the same number
case-obs-bound : depᵗ {Γ = Γ₀} zeroη (caseᵗ obs-sc hands-back other-arm) ≡ 2
case-obs-bound = refl

case-obs-value : depᵛ {Γ = Γ₀} zeroη (obs Inner)
                   (evalWith (caseᵗ obs-sc hands-back other-arm) []ᵃ) ≡ 1
case-obs-value = refl

----------------------------------------------------------------------
-- 3.  THE CONDITIONAL, WHICH IS SEPARATE ONLY BECAUSE THE SELECTION IS
-- OPAQUE.  One row where the selected arm is the one setting the join,
-- one where it is not.
----------------------------------------------------------------------

shallow : Tm Γ₀ [] [] [] (obs natᵗ)
shallow = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

deep : Tm Γ₀ [] [] [] (obs Inner)
deep = strmᵗ (ofᵉ (strmᵗ (ofᵉ (nat̂ 7 ∷ [])) ∷ []))

row-if-selected : Confirms
  (eval-if {Γ = Γ₀} zeroη dd₀ (bool̂ true) shallow shallow []ᵃ)
row-if-selected = z≤n

row-if-unselected : Confirms
  (eval-if {Γ = Γ₀} zeroη dd₀ (bool̂ true) deep deep []ᵃ)
row-if-unselected = s≤s z≤n
