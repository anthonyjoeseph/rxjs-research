-- THE ROOM CANNOT FUND THE FLATTENER'S BACKLOG SPEND, AND THE WITNESS
-- IS A PROGRAM WITH NO SHARE IN IT AT ALL.
--
-- WHAT THIS KILLS.  A resumption-tree candidate indexed by the room
-- closes every edge of the subscribe cycle on `unconn`: the connect
-- spends a slot and peels the accessibility, and every other edge
-- passes the same peel along.  The one edge with nothing to spend is
-- the flattener's backlog -- a lane that had no room kept the arriving
-- observable, and the drain later takes it back out of the store and
-- SUBSCRIBES it, which re-enters the candidate at a value the store
-- chose.  The repair on offer is an invariant saying a non-empty lane
-- queue witnesses that the room has fallen strictly since the frame
-- holding that lane was built, so the pop peels a real step.
--
-- WHY IT CANNOT HOLD.  The room counts SHARED slots the connected set
-- does not yet hold, and `unconnAt` is zero at a scripted slot by its
-- first clause.  A program whose table is all scripted therefore has
-- room zero at every state of its run, before any connect and after
-- all of them.  `evaluate!` seeds the candidate's ceiling at the room
-- itself, and every ceiling the run derives sits below that one -- so
-- on such a program every ceiling in the whole run is zero, and the
-- peel the drain needs reads `0 < 0`.
--
-- AND THE BACKLOG STILL HAPPENS THERE, which is what makes this a
-- refutation rather than an observation about an empty case.  A
-- bounded merge over two inners enqueues the second through
-- `consume-all-enqueue` -- the ordinary refusal path, fired on
-- `hasRoom lim act ≡ false`, which appends to the same `mergeAll-st`
-- queue the fan-out writes and `mergeAllDrain!` reads.  No connect is
-- anywhere near it.  The smallest such program is one scripted nat
-- slot under `mergeAll` at limit one with the slot subscribed twice;
-- the compiled CLI emits its inner's values TWICE for it, so the
-- queued inner is spent and the store re-entry is taken.
--
-- SO THE OBSTRUCTION IS NOT THE PHRASING.  Any invariant funding that
-- re-entry out of the room has this conclusion, and this program
-- refutes the conclusion outright.  The room is the wrong currency for
-- the store re-entry: the backlog exists in programs where the room is
-- constantly zero.
module Refuted.Room-Backlog where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _<_)
open import Data.Nat.Properties using (n≤0⇒n≡0)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Rx.Prim using (Source; cold; after_,_)
open import Rx.Exp using (Ctx; natᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator.Unconn-Arith using (unconn; unconnAt)

-- ONE SCRIPTED NAT SLOT, and nothing shared anywhere in the table.
-- The script is the one the CLI was run at: two synchronous values and
-- one asynchronous, so the inner has a lifetime and the lane is
-- genuinely occupied when the second arrival is refused.
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

ins₁ : Slots Γ₁
ins₁ fzero = scripted (cold (1 ∷ 2 ∷ []) ((after 0 , 3) ∷ []))

-- THE FIRST CLAUSE OF `unconnAt` IS THE WHOLE ARGUMENT: a scripted
-- slot has no definition to subscribe, so connecting it is not an
-- operation and it never counts.
zeroAt : ∀ (cs : List Source) (i : Fin 1) → unconnAt ins₁ cs i ≡ 0
zeroAt cs fzero = refl

-- so the room is zero at EVERY state this program can reach, for every
-- connected set whatever -- the quantifier is what makes it a fact
-- about the run rather than about one state of it
room-zero : ∀ (cs : List Source) → unconn ins₁ cs ≡ 0
room-zero cs rewrite zeroAt cs fzero = refl

-- THE REFUTATION.  `m₀` is any ceiling the run derives -- the seed is
-- the room itself and every later one is below it -- and the peel is
-- what the drain's pop would have to produce.  Both sides are zero
-- here, so no peel exists at any state of this program, while the
-- queue it would have funded is demonstrably spent.
saw-room-cannot-fund : ∀ (cs cs′ : List Source) (m₀ : ℕ)
                     → m₀ ≤ unconn ins₁ cs
                     → unconn ins₁ cs′ < m₀
                     → ⊥
saw-room-cannot-fund cs cs′ m₀ ceil peel =
  absurd (subst (unconn ins₁ cs′ <_)
                (n≤0⇒n≡0 (subst (m₀ ≤_) (room-zero cs) ceil))
                peel)
  where
    absurd : ∀ {k : ℕ} → k < 0 → ⊥
    absurd ()
