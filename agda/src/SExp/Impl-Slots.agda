-- THE IMPL'S TABLE AND ITS ROOT BINDER: the author's slots embedded twice
-- over the doubled context, raw below and stamped above, and the program
-- elaborated under one mint.  Free in the same way `SExp.Pipeline` is; it
-- sits below the evaluator's builder so a store can name the impl's
-- table without that cone.
module SExp.Impl-Slots where

open import Data.Bool    using (true; false; T)
open import Data.Fin     using (Fin; toℕ; _↑ˡ_; _↑ʳ_; splitAt)
open import Data.Fin.Properties using (splitAt⁻¹-↑ˡ; splitAt⁻¹-↑ʳ)
open import Data.Sum     using (inj₁; inj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List    using ([]; _∷_)
open import Data.Unit    using (tt)
open import Data.Vec     using (lookup; zipWith)
open import Data.Vec.Properties using (lookup-zipWith; lookup-++ˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import Rx.Prim      using (hot; cold)
open import Rx.Exp       using (Ctx; Ty; Exp; Closed; mintᵉ; inputsBelowᵉ; uniqᵗ; varᵗ)
open import SExp.InstEmit using (machineEmitᵗ)
open import SExp.Syntax      using (SExp; Kinds; hotᵏ; coldᵏ; sharedᵏ; slotTy; rawTy; plainᵏ; emitᵗ; emptyˢ)
open import Rx.Slots     using (Slot; Slots; scripted; shared)
open import SExp.Elaborate using (toInstEmit; inputᵖ; stampedSlot)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ)

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
