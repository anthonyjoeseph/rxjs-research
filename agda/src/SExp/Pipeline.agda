-- THE IMPL SIDE OF THE TOP LINE, AND EVERYTHING HERE IS FREE.  The
-- top line holds this pipeline to fixed things and nothing else: the
-- author's program read plain (`SExp.Plain`), whose values its batches
-- must carry in order; the timed translation (`Timed.Translation`), whose
-- packets its instant stamps must agree with; and
-- `spec-batchSimultaneous`, the grouping its batcher must reproduce.
-- The InstEmit this side runs on -- its fields, its ids, its kinds --
-- is an implementation detail the theorem never sees past those.
--
-- What is NOT free is below this module: `Rx.Exp`, `SExp.Syntax` and the
-- evaluator.  A change that needs one of those is a question for
-- Anthony, never a patch.
--
-- RECOVERY: git show 0de565ef:agda/src/Implementation/Elaborate.agda
--   restores the impl side's own walk, a copy of `toInstEmit` whose flattener
--   arms call their own lane -- the place a per-former InstEmit change lands.
module SExp.Pipeline where

open import Data.List    using (List; []; concat)

open import Rx.Prim      using (Fuel; InstEmit)
open import Rx.Exp       using (Ctx; Ty; Val)
open import SExp.Syntax      using (SExp; Kinds; plainᵏ; plainᵗ; emitᵗ)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Simul-Slots using (SimulSlots; plainSlots)
open import SExp.Plain using (plainExp; plainValues)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)

-- the elaborated program's output, flat, as the wire carries it
emitsᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
       → SimulSlots Γ κ → Burst (plainᵏ Γ κ) (emitᵗ t)
emitsᴵ κ fuel e ins = concat (evaluate↓ fuel (elaborateImpl κ e) (embedSlotsImpl ins))

-- THE IMPL'S RUN, AS THE TOP LINE READS IT: each emit decoded back to
-- the InstEmit record.
runᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
     → SimulSlots Γ κ → List (InstEmit (Val (plainᵏ Γ κ) (plainᵗ t)))
runᴵ κ fuel e ins = decodeEmits (emitsᴵ κ fuel e ins)

-- AND WHAT IT IS HELD TO: the author's program read as plain rxjs, its
-- values as a subscriber receives them.  One name for the one run that
-- `left-to-right` and `timed-faithful` both compare against.
runᴾ : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t : Ty} → Fuel → SExp Γ [] [] [] t
     → SimulSlots Γ κ → List (Val Γ t)
runᴾ fuel e ins = plainValues (concat (evaluate↓ fuel (plainExp e) (plainSlots ins)))
