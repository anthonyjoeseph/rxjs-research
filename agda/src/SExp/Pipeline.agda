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

open import Data.Bool    using (true; false; T)
open import Data.Fin     using (toℕ)
open import Data.List    using (List; []; concat)
open import Data.Unit    using (tt)
open import Data.Vec     using (lookup)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Rx.Prim      using (Fuel; InstEmit)
open import Rx.Exp       using (Ctx; Ty; Exp; Val; mintᵉ; inputsBelowᵉ)
open import SExp.Syntax      using (SExp; Kinds; scriptedᵏ; sharedᵏ; slotTy; plainᵏ; plainᵗ; emitᵗ; emptyˢ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Elaborate using (toInstEmit)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; scriptedˢ; sharedˢ)

-- ONE MINT FOR THE WHOLE PROGRAM.  `mintᵉ` draws once per subscription
-- of the node it stands at, and it stands at the root, so every source
-- beneath reads the same token for one subscription of the program and
-- a fresh one for the next -- which is what a subscribe frame is.  A
-- resubscribe through `deferᵉ` re-runs the body and not this binder, so
-- an inner's frame is its outer's.
elaborateImpl : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t : Ty}
              → SExp Γ [] [] [] t → Exp (plainᵏ Γ κ) [] [] [] (emitᵗ t)
elaborateImpl κ e = mintᵉ (toInstEmit κ e)

-- A SHARE'S STRATIFICATION IS CHECKED HERE, NOT ASSUMED.  The table
-- certifies it of the definition read plain; the elaboration adds no
-- input, so the check below always passes, but saying so is a fact
-- about `toInstEmit` that nothing proves yet -- and `left-to-right` is
-- where it is owed, since the fallback would change the values.
sharedᴵ : ∀ {n} {Γ : Ctx n} (κ : Kinds n) (k : _) {t : Ty}
        → SExp Γ [] [] [] t → Slot (plainᵏ Γ κ) k (emitᵗ t)
sharedᴵ κ k d with inputsBelowᵉ k (elaborateImpl κ d) in eq
... | true  = shared (elaborateImpl κ d) {ok = subst T (sym eq) tt}
... | false = shared (elaborateImpl κ emptyˢ) {ok = tt}

embedSlotsImpl : ∀ {n} {Γ : Ctx n} {κ : Kinds n}
               → SimulSlots Γ κ → Slots (plainᵏ Γ κ)
embedSlotsImpl {Γ = Γ} {κ = κ} ins i =
  subst (Slot (plainᵏ Γ κ) (toℕ i))
        (sym (lookup-zipWith slotTy i Γ κ))
        (go (lookup κ i) (ins i))
  where
    go : ∀ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → Slot (plainᵏ Γ κ) (toℕ i) (slotTy (lookup Γ i) kd)
    go scriptedᵏ (scriptedˢ {ok = ok} inp) = scripted {ok = ok} inp
    go sharedᵏ   (sharedˢ d)               = sharedᴵ κ (toℕ i) d

-- the elaborated program's output, flat, as the wire carries it
emitsᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
       → SimulSlots Γ κ → Burst (plainᵏ Γ κ) (emitᵗ t)
emitsᴵ κ fuel e ins = concat (evaluate↓ fuel (elaborateImpl κ e) (embedSlotsImpl ins))

-- THE IMPL'S RUN, AS THE TOP LINE READS IT: each emit decoded back to
-- the InstEmit record.
runᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
     → SimulSlots Γ κ → List (InstEmit (Val (plainᵏ Γ κ) (plainᵗ t)))
runᴵ κ fuel e ins = decodeEmits (emitsᴵ κ fuel e ins)
