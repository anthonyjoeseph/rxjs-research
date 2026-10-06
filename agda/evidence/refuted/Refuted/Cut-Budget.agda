-- A TEST'S CUT RELATION CANNOT QUANTIFY OVER THE PLAIN BUDGET.
-- `CutLifts` asks the impl's cut step, from one cell, to match the plain
-- `takeVals` at every plain budget its `Bud` relates to that cell -- and
-- a test's cell carries `tt`, so a `Bud` at `⊤` makes the one impl
-- output match the plain step at budget zero, which passes nothing, and
-- at budget one, which passes a value its predicate accepts.  No closure
-- does both, so a test's row pins the plain budget rather than leaving
-- it free.
--
-- AND A COUNT'S ROW CANNOT ADMIT A PLAIN BUDGET OF ZERO.  The plain
-- `take` installs its frame only at a positive count, and its zero
-- step cuts nothing; the elaborated count cutter at zero takes nothing
-- and reads "all of the quota taken", so it cuts on an emit carrying
-- no value.  `Bud` at `_≡_` relates the two at zero, where they part.
module Refuted.Cut-Budget where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Ctx; Val; FnClo; natᵗ; boolᵗ; unitᵗ; uniqᵗ; _×ᵗ_; bool̂; []ᵉ; _∷ᵉ_)
open import SExp.Syntax using (Kinds; emitᵗ)
open import SExp.Elaborate using (CutS; cutStepᵖ; countCutᵖ)
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

-- the elaborated count's step, under its mint's token alone
count : FnClo Γ₀ (CutS natᵗ natᵗ ×ᵗ emitᵗ natᵗ) (CutS natᵗ natᵗ)
count = uniqᵗ ∷ [] , cutStepᵖ countCutᵖ , 3 ∷ᵉ []ᵉ

-- an emit carrying nothing
e∅ : Val Γ₀ (emitᵗ natᵗ)
e∅ = [] , 0 , 0 , inj₁ tt

cut-zero-false : ¬ CutLifts {Γ = Γ₀} κ₀ natᵗ natᵗ _≡_ count nothing
cut-zero-false cl with cl 0 0 [] e∅ e∅ [] refl []
... | _ , () , _ , _
