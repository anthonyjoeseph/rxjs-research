-- THE IMPL SIDE OF THE TOP LINE, AND EVERYTHING HERE IS FREE.  The
-- top line holds this pipeline to fixed things and nothing else: the
-- author's program read plain (`Rx.Plain`), whose values its batches
-- must carry in order; the timed translation (`Rx.Timed`), whose
-- packets its instant stamps must agree with; and
-- `Verify-Batch-Simultaneous.Countable`, what its envelope must tell a
-- batcher.  The envelope this side runs on --
-- its fields, its ids, its kinds -- is an implementation detail the
-- theorem never sees past those two.
--
-- What is NOT free is below this module: `Rx.Exp`, `Rx.SExp` and the
-- evaluator.  A change that needs one of those is a question for
-- Anthony, never a patch.
--
-- RECOVERY: git show 0de565ef:agda/src/Implementation/Elaborate.agda
--   restores the impl side's own walk, a copy of `toEnvelope` whose flattener
--   arms call their own lane -- the place a per-former envelope change lands.
module Implementation.Pipeline where

open import Data.Bool    using (true; false; T)
open import Data.Fin     using (toℕ)
open import Data.List    using (List; []; _∷_; _++_; concat)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.Vec     using (lookup)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Rx.Prim      using (Fuel; InstEmit; valueᵖ; completeᵖ)
open import Rx.Exp       using (Ctx; Ty; Exp; Val; listᵗ; uniqᵗ; mintᵉ; inputsBelowᵉ)
open import Rx.SExp      using (SExp; Kinds; scriptedᵏ; sharedᵏ; slotTy; plainᵏ; plainᵗ; emitᵗ; emptyˢ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import Rx.Envelope  using (instEventᵗ; machineEmitᵗ)
open import Rx.Envelope.Decode using (decodeEmits)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Elaborate using (toEnvelope)
open import Rx.Simul-Slots using (SimulSlots; SimulSlot; scriptedˢ; sharedˢ)
open import Rx.Batch     using (batchSimultaneousᵖ)

-- ONE MINT FOR THE WHOLE PROGRAM.  `mintᵉ` draws once per subscription
-- of the node it stands at, and it stands at the root, so every source
-- beneath reads the same token for one subscription of the program and
-- a fresh one for the next -- which is what a subscribe frame is.  A
-- resubscribe through `deferᵉ` re-runs the body and not this binder, so
-- an inner's frame is its outer's.
elaborateImpl : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t : Ty}
              → SExp Γ [] [] [] t → Exp (plainᵏ Γ κ) [] [] [] (emitᵗ t)
elaborateImpl κ e = mintᵉ (toEnvelope κ e)

-- A SHARE'S STRATIFICATION IS CHECKED HERE, NOT ASSUMED.  The table
-- certifies it of the definition read plain; the elaboration adds no
-- input, so the check below always passes, but saying so is a fact
-- about `toEnvelope` that nothing proves yet -- and `left-to-right` is
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

-- THE IMPL'S RUN, AS THE TOP LINE READS IT: the elaborated program's
-- output, flat, each emit decoded back to the envelope record.
runᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
     → SimulSlots Γ κ → List (InstEmit (Val (plainᵏ Γ κ) (plainᵗ t)))
runᴵ κ fuel e ins = decodeEmits (concat (evaluate↓ fuel (elaborateImpl κ e) (embedSlotsImpl ins)))

-- an envelope's value payloads, read off the wire directly: the impl
-- side has no use for the spec's decoded `InstEmit`
payloadsᴵ : ∀ {n} {Γ : Ctx n} {u b : Ty}
          → List (Val Γ (instEventᵗ u b)) → List (Val Γ b)
payloadsᴵ []                  = []
payloadsᴵ (inj₂ (inj₁ v) ∷ xs) = v ∷ payloadsᴵ xs
payloadsᴵ (_ ∷ xs)            = payloadsᴵ xs

-- one burst of the batched run, as a subscriber sees it: one entry per
-- batch, in stream order
unwrapImpl : ∀ {n} {Γ : Ctx n} {a : Ty}
           → Burst Γ (machineEmitᵗ (listᵗ a)) → List (List (Val Γ a))
unwrapImpl []                     = []
unwrapImpl {a = a} (valueᵖ (evs , _) ∷ es) =
  payloadsᴵ {u = uniqᵗ} {b = listᵗ a} evs ++ unwrapImpl es
unwrapImpl (completeᵖ ∷ es)       = unwrapImpl es

-- THE BATCHED RUN, AS A SUBSCRIBER SEES IT: the elaborated program
-- through `batchSimultaneousᵖ`, one entry per batch, in stream order
batchesᴵ : ∀ {n} {Γ : Ctx n} {t : Ty} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t
         → SimulSlots Γ κ → List (List (Val (plainᵏ Γ κ) (plainᵗ t)))
batchesᴵ κ fuel e ins =
  unwrapImpl (concat (evaluate↓ fuel (batchSimultaneousᵖ (elaborateImpl κ e)) (embedSlotsImpl ins)))
