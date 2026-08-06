module Rx.Evaluator-Theorems where

open import Data.Nat     using (_≤_)
open import Data.List    using ([]; _∷_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Tick; Fuel)
open import Rx.Exp       using (Ctx; Closed; Exp; μᵉ; unfoldμ)
open import Rx.Evaluator using (Slot; Slots; Stream; evaluate)




------------------------------------------------------------------
-- Evaluator-level theorems (tested against TS, proven where cheap)
------------------------------------------------------------------

-- evaluate-well-formed (the primitives' half of the sandwich) now
-- lives in Verify-Well-Formed as a real proof over postulated
-- stage lemmas.

postulate
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

  -- deferᵉ's temporal law — NOT YET STATABLE, honestly.  The intent
  -- ("stream of (deferᵉ e) ≈ stream of e with ticks +1") needs two
  -- pieces that do not exist as DEFINITIONS today, only as postulated
  -- abstractions or nowhere at all:
  --   (1) a tick per emission.  InstEmit's fields are events, instant,
  --       source, kind (Rx.Prim:118-123) — no Tick.  The arrival's
  --       tick is threaded through subscribeE/foldPath internally
  --       (Arrival.tick, Rx.Evaluator:69; consumed at foldPath's call
  --       site, Rx.Evaluator:1599) and discarded before it reaches
  --       Stream.  So there is no way, today, to read "the tick of
  --       this emit" back off `evaluate`'s result — the same gap
  --       `causality`'s `emittedBefore` runs into below.
  --   (2) the "≈" itself.  The comment's hedge ("because the body's
  --       ids are re-minted") wants an equivalence up to id renaming,
  --       but no relation of that shape exists in the codebase.  One
  --       was postulated once (`Rx.Time-Theorems._≈ˢ_`) and deleted as
  --       an unconsumed abstract Set: borrowing such a thing relocates
  --       the vacuity rather than fixing it, so it has to be DEFINED.
  -- Stating this for real needs new machinery (a defined tick-trace or
  -- ticked-emit variant, plus a defined — not postulated — renaming
  -- equivalence), which is a design call, not a leaf-module fix. Left
  -- as ⊤ on purpose: an honest gap, not a claim.
  defer-shift :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    ⊤

