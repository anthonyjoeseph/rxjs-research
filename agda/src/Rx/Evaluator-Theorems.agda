module Rx.Evaluator-Theorems where

open import Data.Nat     using (_≤_)
open import Data.List    using ([]; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Tick; Fuel)
open import Rx.Exp       using (Ctx; Closed; Exp; μᵉ; unfoldμ)
open import Rx.Evaluator using (Slot; Slots; Stream; evaluate)
open import Rx.Protocol  using (WellFormed)




------------------------------------------------------------------
-- Evaluator-level theorems (tested against TS, proven where cheap)
------------------------------------------------------------------

postulate
  -- the primitives' half of the sandwich (see The-Proof): every
  -- stream the evaluator renders satisfies the protocol.  Proven,
  -- this is one preservation lemma per primitive — a primitive is
  -- correctly implemented iff its stepFrame clause preserves the
  -- automaton's invariant against the registry EvalSt already keeps
  evaluate-well-formed :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    WellFormed (evaluate fuel e ins)

  -- fuel is arrivals: processing more arrivals only extends the stream
  fuel-coherent :
    ∀ {n} {Γ : Ctx n} {t} (f₁ f₂ : Fuel) → f₁ ≤ f₂ →
    (e : Closed Γ t) (ins : Slots Γ) →
    Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)

  -- causality: agreeing slot prefixes (scripted arrivals before tick
  -- k; shared defs, carrying no scripts, must agree outright) give
  -- agreeing output prefixes
  truncateIn : ∀ {n} {Γ : Ctx n} {t} → Tick → Slot Γ t → Slot Γ t
  emittedBefore : ∀ {n} {Γ : Ctx n} {t} → Tick → Stream Γ t → Stream Γ t

  causality :
    ∀ {n} {Γ : Ctx n} {t} (k : Tick) (fuel : Fuel)
      (e : Closed Γ t) (ins₁ ins₂ : Slots Γ) →
    (∀ i → truncateIn k (ins₁ i) ≡ truncateIn k (ins₂ i)) →
    emittedBefore k (evaluate fuel e ins₁)
      ≡ emittedBefore k (evaluate fuel e ins₂)

  -- μ laws
  μ-unfold :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Slots Γ) →
    evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins

  μ-guarded :   -- k arrivals force ≤ k unfoldings (syntactic, via deferᵉ gate)
    ∀ {n} {Γ : Ctx n} {t} (k : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Slots Γ) →
    evaluate k (μᵉ e) ins ≡ evaluate k (unfoldμ e) ins

  -- deferᵉ's temporal law (≈ because the body's ids are re-minted)
  defer-shift :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ⊤   -- state as: stream of (deferᵉ e) ≈ stream of e with ticks +1

