-- THE SLOT TELESCOPE A CLAIM ABOUT SRXJS QUANTIFIES OVER, and the
-- whole of what used to be the palette.
--
-- `Rx.Slots` is the evaluator's telescope and it is deliberately wide:
-- a shared definition there is an arbitrary plain tree, because the
-- TypeScript fast-check drives that evaluator over plain trees and
-- knows nothing of srxjs.  Narrowing it would narrow the thing under
-- test.  But a theorem about the simul operators cannot stand over
-- that width, for two separate reasons, and this module answers both
-- in one telescope.
--
-- ONE: A PLAIN SHARED DEF IS NOT A SRXJS PROGRAM.  It is an arbitrary
-- body at the slot's type, so a claim quantified over it is a claim
-- about the plain evaluator with some trees bolted on -- not about the
-- srxjs operators in isolation, which is the claim being made.  Here a
-- shared definition is an `SExp` and reaches the evaluator only by
-- being elaborated, so every operator in it went through `toPlain`.
--
-- TWO: A KIND AND ITS SLOT HAVE TO AGREE.  `Rx.SExp`'s `Kinds` vector
-- tells the elaboration how to read each slot -- `scriptedᵏ` stands at
-- the PAYLOAD and `inputᵖ` wraps it, `sharedᵏ` stands at the ENVELOPE
-- and `input` reads it straight.  Held apart from the table, those two
-- can disagree, and one direction of disagreement is the forgery hole
-- itself: a table that scripts slot i while `κ` calls it `sharedᵏ`
-- types fine -- the slot stands at `emitᵗ a`, so the script is asked
-- for envelope VALUES -- and hands the machine deliveries no `init`
-- ever enlisted.  `SimulSlot` is INDEXED BY THE KIND, so the arm is
-- forced by the vector and the two cannot come apart.
--
-- AND THAT IS WHY `Rx.Slots.shared` NEEDS NO `isData`.  The bar there
-- was closing the forgery channel at `plainᵗ (obs u) = obs (emitᵗ u)`,
-- where a slot's values are observables of envelopes that the
-- consumer's `mergeAllˢ` subscribes directly, past `stamp`.  A
-- definition here cannot stand at that type dishonestly whatever its
-- type is, because it was BUILT by the elaboration -- so the
-- observable-typed shared slot, which a real author wants, survives.
-- The restriction that closes the hole is the one on scripts, and it
-- is already carried below by `scriptedˢ`.
module Rx.Simul-Slots where

open import Data.Bool using (T)
open import Data.List using ([])
open import Data.Nat  using (ℕ)
open import Data.Vec  using (lookup)
open import Data.Fin  using (toℕ)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import Rx.Prim using (ObservableInput)
open import Rx.Exp  using (Ty; Ctx; Val; isData; inputsBelowᵉ)
open import Rx.SExp using (SExp; Kind; Kinds; scriptedᵏ; sharedᵏ;
                           slotTy; plainᵏ; plainᵗ)
open import Rx.Elaborate using (elaborate)
open import Rx.Slots using (Slot; Slots; scripted; shared)

-- slot i of Γ, as the AUTHOR states it.  The kind index is the last
-- one so that `SimulSlots` can supply it from the vector: the arm is
-- then not a choice the table makes but a fact the vector already
-- fixed.
data SimulSlot {n} (Γ : Ctx n) (κ : Kinds n) (k : ℕ) (t : Ty)
     : Kind → Set where
  -- AN EXTERNAL SOURCE, stated at the author's payload type.  The
  -- elaboration wraps it: `inputᵖ` mints per subscription and stamps
  -- each arrival, so a scripted arrival cannot reach the wire except
  -- inside an envelope the machine wrote.  Data only, exactly as in
  -- `Rx.Slots` and for the same descent reason.
  scriptedˢ : {ok : T (isData (plainᵗ t))}
            → ObservableInput (Val (plainᵏ Γ κ) (plainᵗ t))
            → SimulSlot Γ κ k t scriptedᵏ
  -- ANOTHER SRXJS PROGRAM, stated in the author's syntax.  It stands
  -- at the envelope because it is already elaborated, and the
  -- stratification side condition is charged on the ELABORATION,
  -- since that is the tree the evaluator's measure walks.
  sharedˢ   : (d : SExp Γ [] [] [] t)
            → {ok : T (inputsBelowᵉ k (elaborate κ d))}
            → SimulSlot Γ κ k t sharedᵏ

SimulSlots : ∀ {n} (Γ : Ctx n) (κ : Kinds n) → Set
SimulSlots Γ κ = ∀ i → SimulSlot Γ κ (toℕ i) (lookup Γ i) (lookup κ i)

-- THE READING BACK INTO THE EVALUATOR'S TELESCOPE -- the old palette's
-- `embed`, now a function between two concrete telescopes rather than
-- a field of a record every evaluator module had to be parameterised
-- by.  Nothing downstream of `Rx.Slots` changes; a statement simply
-- quantifies over `SimulSlots` and runs this.
embedSlots : ∀ {n} {Γ : Ctx n} {κ : Kinds n}
           → SimulSlots Γ κ → Slots (plainᵏ Γ κ)
embedSlots {Γ = Γ} {κ = κ} ins i =
  subst (Slot (plainᵏ Γ κ) (toℕ i))
        (sym (lookup-zipWith slotTy i Γ κ))
        (go (lookup κ i) (ins i))
  where
    go : ∀ kd → SimulSlot Γ κ (toℕ i) (lookup Γ i) kd
       → Slot (plainᵏ Γ κ) (toℕ i) (slotTy (lookup Γ i) kd)
    go scriptedᵏ (scriptedˢ {ok = ok} inp) = scripted {ok = ok} inp
    go sharedᵏ   (sharedˢ d {ok = ok})     = shared (elaborate κ d) {ok = ok}
