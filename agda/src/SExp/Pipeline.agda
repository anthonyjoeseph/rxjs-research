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
open import Data.Fin     using (Fin; toℕ; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List    using (List; []; _∷_; concat)
open import Data.Unit    using (tt)
open import Data.Vec     using (lookup; zipWith)
open import Data.Vec.Properties using (lookup-zipWith; lookup-++ˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Rx.Prim      using (Fuel; InstEmit; hot; cold)
open import Rx.Exp       using (Ctx; Ty; Exp; Val; Closed; mintᵉ; inputsBelowᵉ; uniqᵗ; varᵗ)
open import SExp.InstEmit using (machineEmitᵗ)
open import SExp.Syntax      using (SExp; Kinds; hotᵏ; coldᵏ; sharedᵏ; slotTy; rawTy; plainᵏ; plainᵗ; emitᵗ; emptyˢ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import SExp.InstEmit.Decode using (decodeEmits)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Builder using (evaluate↓)
open import SExp.Elaborate using (toInstEmit; inputᵖ; stampedSlot)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ; plainSlots)
open import SExp.Plain using (plainExp; plainValues)

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
sharedᴵ {Γ = Γ} κ k d with inputsBelowᵉ k (elaborateImpl κ d) in eq
... | true  = shared (elaborateImpl κ d) {ok = subst T (sym eq) tt}
... | false = shared (elaborateImpl {Γ = Γ} κ emptyˢ) {ok = tt}

-- THE RAW HALF: each hot script itself, where the evaluator anchors it
-- at tick zero, and an inert cold everywhere a program never reads.
rawSlotImpl : ∀ {n} {Γ : Ctx n} {κ : Kinds n} → SimulSlots Γ κ → (i : Fin n)
            → Slot (plainᵏ Γ κ) (toℕ (i ↑ˡ n)) (lookup (plainᵏ Γ κ) (i ↑ˡ n))
rawSlotImpl {n} {Γ = Γ} {κ = κ} ins i =
  subst (Slot (plainᵏ Γ κ) (toℕ (i ↑ˡ n)))
        (sym (trans (lookup-++ˡ (zipWith rawTy Γ κ) (zipWith slotTy Γ κ) i)
                    (lookup-zipWith rawTy i Γ κ)))
        (go (lookup κ i) (ins i))
  where
    go : ∀ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → Slot (plainᵏ Γ κ) (toℕ (i ↑ˡ n)) (rawTy (lookup Γ i) kd)
    go hotᵏ    (hotˢ {ok = ok} as) = scripted {ok = ok} (hot as)
    go coldᵏ   (coldˢ _ _)         = scripted {ok = tt} (cold [] [])
    go sharedᵏ (sharedˢ _)         = scripted {ok = tt} (cold [] [])

-- HOT SCRIPT i, WRAPPED ONCE.  `inputᵖ` over the raw slot under its own
-- frame, so each arrival is minted one instant here and every reference
-- reads that one.  A share connects at its first subscription, so a
-- late first reader sees only later arrivals -- which is what a hot
-- source shows a late subscriber anyway.
hotShareImpl : ∀ {n} {Γ : Ctx n} (κ : Kinds n) (i : Fin n)
             → lookup κ i ≡ hotᵏ → Closed (plainᵏ Γ κ) (emitᵗ (lookup Γ i))
hotShareImpl {n} {Γ} κ i hot≡ =
  mintᵉ (subst (λ u → Exp (plainᵏ Γ κ) [] [] (uniqᵗ ∷ []) (machineEmitᵗ u))
               (trans (trans (lookup-++ˡ (zipWith rawTy Γ κ) (zipWith slotTy Γ κ) i)
                             (lookup-zipWith rawTy i Γ κ))
                      (cong (rawTy (lookup Γ i)) hot≡))
               (inputᵖ (i ↑ˡ n) (varᵗ (here refl))))

-- the share's stratification computes only at a concrete table, so it is
-- checked, as `sharedᴵ`'s is
hotSlotImpl : ∀ {n} {Γ : Ctx n} (κ : Kinds n) (i : Fin n) → lookup κ i ≡ hotᵏ
            → Slot (plainᵏ Γ κ) (toℕ (n ↑ʳ i)) (emitᵗ (lookup Γ i))
hotSlotImpl {n} {Γ} κ i hot≡ with inputsBelowᵉ (toℕ (n ↑ʳ i)) (hotShareImpl {Γ = Γ} κ i hot≡) in eq
... | true  = shared (hotShareImpl {Γ = Γ} κ i hot≡) {ok = subst T (sym eq) tt}
... | false = shared (elaborateImpl {Γ = Γ} κ emptyˢ) {ok = tt}

-- THE STAMPED HALF: the author's slot i at `n ↑ʳ i`.
stampedSlotImpl : ∀ {n} {Γ : Ctx n} {κ : Kinds n} → SimulSlots Γ κ → (i : Fin n)
                → Slot (plainᵏ Γ κ) (toℕ (n ↑ʳ i)) (lookup (plainᵏ Γ κ) (n ↑ʳ i))
stampedSlotImpl {n} {Γ = Γ} {κ = κ} ins i =
  subst (Slot (plainᵏ Γ κ) (toℕ (n ↑ʳ i))) (sym (stampedSlot Γ κ i))
        (go (lookup κ i) refl (ins i))
  where
    go : ∀ kd → lookup κ i ≡ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → Slot (plainᵏ Γ κ) (toℕ (n ↑ʳ i)) (slotTy (lookup Γ i) kd)
    go hotᵏ    hot≡ (hotˢ _)                 = hotSlotImpl {Γ = Γ} κ i hot≡
    go coldᵏ   _    (coldˢ {ok = ok} ss as)  = scripted {ok = ok} (cold ss as)
    go sharedᵏ _    (sharedˢ d)              = sharedᴵ κ (toℕ (n ↑ʳ i)) d

embedSlotsImpl : ∀ {n} {Γ : Ctx n} {κ : Kinds n}
               → SimulSlots Γ κ → Slots (plainᵏ Γ κ)
embedSlotsImpl {n} {Γ = Γ} {κ = κ} ins j with splitAt n j in eq
... | inj₁ i = subst (λ j′ → Slot (plainᵏ Γ κ) (toℕ j′) (lookup (plainᵏ Γ κ) j′))
                     (splitAt⁻¹-↑ˡ eq) (rawSlotImpl ins i)
... | inj₂ i = subst (λ j′ → Slot (plainᵏ Γ κ) (toℕ j′) (lookup (plainᵏ Γ κ) j′))
                     (splitAt⁻¹-↑ʳ eq) (stampedSlotImpl ins i)

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
