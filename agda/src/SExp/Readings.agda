------------------------------------------------------------------
-- WHAT THE STATEMENTS READ OFF A RUN, kept out of the modules that
-- state and prove things about them.  The compiled runners decide the
-- statements by computing these readings, so they import this module
-- and never a statement's: a proof there reads the evaluator's erased
-- derivations, which the compiled build cannot carry.
------------------------------------------------------------------
module SExp.Readings where

open import Data.Bool    using (T)
open import Data.List    using (List; []; concat; map; length; replicate; _++_)
open import Data.Nat     using (ℕ; zero; suc; _∸_)
open import Data.Product using (proj₂)

open import Rx.Prim      using (Fuel)
open import Rx.Exp       using (Ctx; Val; isData)
open import SExp.Syntax  using (SExp; Kinds)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Plain   using (unplainᵈ)
open import SExp.Simul-Slots using (SimulSlots)
open import SExp.InstEmit.Decode using (decodeEmits)
open import SExp.Batch   using (batchSimultaneousᵖ)
open import SExp.Pipeline using (elaborateImpl; embedSlotsImpl; runᴵ; runᴾ)
open import Batchable.Inst-Extract using (instExtract)

-- the batches, joined back up
joinedᴵ : ∀ {n} {Γ : Ctx n} {t} → T (isData t) → (κ : Kinds n) → Fuel
        → SExp Γ [] [] [] t → SimulSlots Γ κ → List (Val Γ t)
joinedᴵ {t = t} ok κ fuel e ins =
  map (unplainᵈ t ok) (concat (map proj₂ (instExtract (decodeEmits
      (concat (evaluate↓ fuel (batchSimultaneousᵖ (elaborateImpl κ e)) (embedSlotsImpl ins)))))))

-- the elaborated run without the batcher, read at data
valsᴵ : ∀ {n} {Γ : Ctx n} {t} → T (isData t) → (κ : Kinds n) → Fuel
      → SExp Γ [] [] [] t → SimulSlots Γ κ → List (Val Γ t)
valsᴵ {t = t} ok κ fuel e ins = map (unplainᵈ t ok) (map proj₂ (instExtract (runᴵ κ fuel e ins)))

-- each plain value's ARRIVAL, given how many values the run has
-- delivered at each fuel: 0 for the subscription, k for the k-th drain
-- step
arrivalsᴾ : (ℕ → ℕ) → ℕ → List ℕ
arrivalsᴾ c zero    = replicate (c zero) zero
arrivalsᴾ c (suc k) = arrivalsᴾ c k ++ replicate (c (suc k) ∸ c k) (suc k)

-- the plain run's arrivals at a fuel
arrivalsOf : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ → List ℕ
arrivalsOf {κ = κ} fuel e ins = arrivalsᴾ (λ k → length (runᴾ {κ = κ} k e ins)) fuel
