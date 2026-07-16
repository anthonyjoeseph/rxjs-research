module Rx.Evaluator-Theorems where

open import Data.Nat     using (_≤_)
open import Data.List    using ([]; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Tick; Fuel; ObservableInput)
open import Rx.Exp       using (Ctx; Closed; Exp; μᵉ; unfoldμ)
open import Rx.Evaluator using (Inputs; Stream; evaluate)




------------------------------------------------------------------
-- Evaluator-level theorems (tested against TS, proven where cheap)
------------------------------------------------------------------

postulate
  -- fuel is arrivals: processing more arrivals only extends the stream
  fuel-coherent :
    ∀ {n} {Γ : Ctx n} {t} (f₁ f₂ : Fuel) → f₁ ≤ f₂ →
    (e : Closed Γ t) (ins : Inputs Γ) →
    Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)

  -- causality: agreeing input prefixes (arrivals before tick k) give
  -- agreeing output prefixes
  truncateIn : ∀ {A} → Tick → ObservableInput A → ObservableInput A
  emittedBefore : ∀ {n} {Γ : Ctx n} {t} → Tick → Stream Γ t → Stream Γ t

  causality :
    ∀ {n} {Γ : Ctx n} {t} (k : Tick) (fuel : Fuel)
      (e : Closed Γ t) (ins₁ ins₂ : Inputs Γ) →
    (∀ i → truncateIn k (ins₁ i) ≡ truncateIn k (ins₂ i)) →
    emittedBefore k (evaluate fuel e ins₁)
      ≡ emittedBefore k (evaluate fuel e ins₂)

  -- μ laws
  μ-unfold :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Inputs Γ) →
    evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins

  μ-guarded :   -- k arrivals force ≤ k unfoldings (syntactic, via deferᵉ gate)
    ∀ {n} {Γ : Ctx n} {t} (k : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Inputs Γ) →
    evaluate k (μᵉ e) ins ≡ evaluate k (unfoldμ e) ins

  -- deferᵉ's temporal law (≈ because the body's ids are re-minted)
  defer-shift :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Inputs Γ) →
    ⊤   -- state as: stream of (deferᵉ e) ≈ stream of e with ticks +1

