-- A TEST'S CUT RELATION CANNOT QUANTIFY OVER THE PLAIN BUDGET.
-- `CutLifts` asks the impl's cut step, from one cell, to match the plain
-- `takeVals` at every plain budget its `Bud` relates to that cell -- and
-- a test's cell carries `tt`, so a `Bud` at `⊤` makes the one impl
-- output match the plain step at budget zero, which passes nothing, and
-- at budget one, which passes a value its predicate accepts.  No closure
-- does both, so a test's row pins the plain budget rather than leaving
-- it free.
module Refuted.Cut-Budget where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Ctx; Val; FnClo; natᵗ; boolᵗ; unitᵗ; _×ᵗ_; bool̂; []ᵉ)
open import SExp.Syntax using (Kinds; emitᵗ)
open import SExp.Elaborate using (CutS)
open import Simulation.Stores using (CutLifts)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

κ₀ : Kinds 0
κ₀ = []ⱽ

-- the test that always holds
always : FnClo Γ₀ natᵗ boolᵗ
always = [] , bool̂ true , []ᵉ

-- one emit carrying the value zero
e₀ : Val Γ₀ (emitᵗ natᵗ)
e₀ = inj₂ (inj₁ 0) ∷ [] , 0 , 0 , inj₁ tt

-- nothing, and one thing, are not one list
none-and-one : ∀ {A B : Set} {R : A → B → Set} {xs y} → Pointwise R xs [] → Pointwise R xs (y ∷ []) → ⊥
none-and-one [] ()

cut-budget-false : ∀ (F₁ : FnClo Γ₀ (CutS unitᵗ natᵗ ×ᵗ emitᵗ natᵗ) (CutS unitᵗ natᵗ))
                 → ¬ CutLifts {Γ = Γ₀} κ₀ unitᵗ natᵗ (λ _ _ → ⊤) F₁ (just always)
cut-budget-false F₁ cl with cl tt 0 [] e₀ e₀ (0 ∷ []) tt (refl ∷ []) | cl tt 1 [] e₀ e₀ (0 ∷ []) tt (refl ∷ [])
... | _ , _ , r₀ , _ | _ , _ , r₁ , _ = none-and-one r₀ r₁
