------------------------------------------------------------------
-- THE SLOT-HOP ENVIRONMENT: the η that `Rx.Hop-Depth`'s input clause
-- was parameterised FOR.
--
-- `hopDᵉ` reads η at `input i` and nowhere else, so every consumer of
-- the measure has to say which environment it means.  The constant-0
-- reading is FALSE rather than merely coarse: an obs-typed shared
-- slot's def emits values of positive hop, and a subscription
-- connecting to that slot receives them, so zeroing the share
-- boundary breaks at the first flattener over an input.  What is
-- built here is the honest one.
--
-- IT IS WELL DEFINED BECAUSE THE TELESCOPE IS STRATIFIED.  `Rx.Slots`
-- carries a side condition saying a shared def reads only inputs at
-- strictly smaller indices, so slot k's hop is computable by
-- recursion on k: `ηAt` builds the stage-k environment — correct
-- below k, zero at and above it — and `slotHop` reads each slot's hop
-- off its own stage.  That side condition is in the syntax for this
-- and discharges by unification at every concrete program.
--
-- WHAT IS NOT HERE, AND WHY.  The FIXPOINT half — that the staged
-- number at a shared slot IS the def's hopD under the full environment,
-- plus the scripted slot's zero — and the η congruence it is proven
-- from are complete bodies resting on no postulate.  They are absent
-- because nothing consumes them yet: the equation is what a proof
-- charging an input clause spends, and no such proof is written.
--
-- RECOVERY: `git show 919f115:agda/src/Rx/Slot-Hop.agda` restores the
--   fixpoint half and `git show 919f115:agda/src/Rx/Hop-Eta-Cong.agda`
--   the η congruence.
------------------------------------------------------------------
module Rx.Slot-Hop where

open import Data.Nat  using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Fin  using (Fin; toℕ)
open import Data.Bool using (if_then_else_)

open import Rx.Exp       using (Ctx)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Hop-Depth using (hopDᵉ)

-- one slot's hop, given an environment for the inputs its def may
-- read.  A scripted slot carries data only (`isData`), so no emission
-- of its can hold an observable: hop 0.
slotHopD : ∀ {n} {Γ : Ctx n} {k t} (V : ℕ) (η : Fin n → ℕ) →
           Slot Γ k t → ℕ
slotHopD V η (scripted _) = 0
slotHopD V η (shared d)   = hopDᵉ V η d

-- the stage-k environment: the true hops at indices < k, 0 above.
-- Structural on k — this is the recursion stratification pays for.
ηAt : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) (k : ℕ) → Fin n → ℕ
ηAt V sl zero    i = 0
ηAt V sl (suc k) i =
  if toℕ i ≡ᵇ k then slotHopD V (ηAt V sl k) (sl i)
                else ηAt V sl k i

-- THE ENVIRONMENT: each slot's hop off its own stage
slotHop : ∀ {n} {Γ : Ctx n} (V : ℕ) (sl : Slots Γ) → Fin n → ℕ
slotHop V sl i = slotHopD V (ηAt V sl (toℕ i)) (sl i)
