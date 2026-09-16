----------------------------------------------------------------------
-- TAKE'S BUDGET, ACROSS THE FRAME BOUNDARY.
--
-- WHAT A ROW HERE DECIDES.  The bound the rows carry is a length
-- against a numeral, so the whole statement computes: the take node's
-- budget is spent at the dispatch and its cut is emitted from the
-- frame, and a row is green only if those two points agree at the
-- program it names.  Nothing is postulated on the path — `rootBurst`,
-- `drainRest` and `takeBudget` are the builder's own output read back
-- — so a row that failed would be a refutation rather than an unproven
-- goal.
--
-- AND THE ROW HAS TO REACH PAST THE FRAME, which is what makes it the
-- one worth having.  What the frame itself spends is settled without
-- the drain running at all; what is open is whether the budget the
-- frame hands on survives being carried and is spent THERE.
--
-- AND THE INTERESTING ROWS ARE THE ONES WHERE THE BOUND IS TIGHT.  A
-- take whose budget exceeds what the program can emit is bounded by
-- arithmetic rather than by the node, so it cannot refute; the rows
-- below are chosen so the take actually cuts.
--
-- NOT REACHED: every flattening program; any type other than `natᵗ`;
-- any COLD source; a take nested under another take; and a take at a
-- term that is not a literal, since the budget is read through
-- `evalTm` and no row here makes that step non-trivial.
----------------------------------------------------------------------

-- TARGET: take-drain-bound @eea582
module Probed.Take-Bounds where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.Vec using ([]; _∷_)     -- contexts are Vecs; ∷/[] overload per type
open import Data.Nat using (s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (after_,_; hot)
open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; input; takeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Readme-Theorems using (oneSlot; emitValues)
open import Verify-Take-Bounds using (take-drain-bound)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- 1.  THE CUT LANDS ACROSS AN ARRIVAL, which is the shape the drain
-- decides rather than the frame.  A scripted source delivers two values and the
-- take is at one, so the budget has to survive being carried from the
-- frame into the drain's state and be spent THERE.  LOAD-BEARING on
-- that carry: the frame emits NOTHING here, so the whole bound is
-- decided in the drain, against a budget of one that the drain did not
-- compute.  A drain that admitted the second arrival emits two against
-- that one and fails the row.  What this row does NOT catch is a
-- budget re-minted LARGER, which only weakens its own right-hand side
-- — that shape is decided by `take-burst-bound`, which pins what the
-- frame may leave behind and is proven rather than probed.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ []

src₁ : Closed Γ₁ natᵗ
src₁ = input zero

slots₁ : Slots Γ₁
slots₁ = oneSlot (scripted (hot ((after 0 , 5) ∷ (after 0 , 7) ∷ [])))

row-arrival : Confirms (take-drain-bound 6 1 src₁ slots₁)
row-arrival = s≤s z≤n

----------------------------------------------------------------------
-- NON-VACUITY, and it is what makes the row a row at all.  The bound
-- is TIGHT — the take emits exactly its budget — so it is not
-- satisfied by a node that emits nothing, which is the shape a
-- mis-spent budget would produce and the one an inequality hides.
-- Pinned beside it is what the SAME program emits with the take
-- removed, because a cut that let everything through would also
-- satisfy `1 ≤ 1` at a program that only ever had one value.
----------------------------------------------------------------------

arrival-cuts : emitValues (evaluate↓ 6 (takeᵉ (nat̂ 1) src₁) slots₁) ≡ 5 ∷ []
arrival-cuts = refl

arrival-uncut : emitValues (evaluate↓ 6 src₁ slots₁) ≡ 5 ∷ 7 ∷ []
arrival-uncut = refl
