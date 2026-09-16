----------------------------------------------------------------------
-- TAKE'S BOUND, AT THE CUT IT IS ABOUT.
--
-- WHAT A ROW HERE DECIDES.  The bound is a length against a numeral, so
-- the whole statement computes: the take node's budget is spent at the
-- dispatch and its cut is emitted from the frame, and a row is green
-- only if those two points agree at the program it names.  Nothing is
-- postulated on the path — `evaluate↓` is the builder's own output —
-- so a row that failed would be a refutation rather than an unproven
-- goal.
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

-- TARGET: take-bounds-values @189781
module Probed.Take-Bounds where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.Vec using ([]; _∷_)     -- contexts are Vecs; ∷/[] overload per type
open import Data.Nat using (s≤s; z≤n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (after_,_; hot)
open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; ofᵉ; input; takeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Readme-Theorems using (noSlots; oneSlot; emitValues)
open import Verify-Take-Bounds using (take-bounds-values)

open import Probed.Apparatus using (Confirms)

Γ₀ : Ctx 0
Γ₀ = []

----------------------------------------------------------------------
-- 1.  THE CUT LANDS MID-BURST.  LOAD-BEARING: the subscribe frame
-- delivers two values in one instant and the take is at one, so the
-- bound holds only if the node stops INSIDE the burst rather than at
-- the instant boundary.  A take that let a whole batch through would
-- emit two and fail the row.
----------------------------------------------------------------------

pair₀ : Closed Γ₀ natᵗ
pair₀ = ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])

row-mid-burst : Confirms (take-bounds-values 0 1 pair₀ noSlots)
row-mid-burst = s≤s z≤n

----------------------------------------------------------------------
-- 2.  A TAKE AT ZERO.  LOAD-BEARING on the one shape that has no
-- decrement to get right: the budget is spent before anything is
-- delivered, so a node that emitted first and checked afterwards
-- parts from the bound here and nowhere else.
----------------------------------------------------------------------

row-zero : Confirms (take-bounds-values 0 0 pair₀ noSlots)
row-zero = z≤n

----------------------------------------------------------------------
-- 3.  THE CUT LANDS ACROSS AN ARRIVAL, which rows 1 and 2 cannot
-- reach: both decide the bound inside the subscribe frame, where the
-- drain never runs.  A scripted source delivers two values and the
-- take is at one, so the budget has to survive being carried from the
-- frame into the drain's state and be spent THERE.  LOAD-BEARING on
-- that carry — a budget re-minted at the drain's entry, or one read
-- off the expression rather than off the node's state, admits the
-- second arrival and fails the row.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ []

src₁ : Closed Γ₁ natᵗ
src₁ = input zero

slots₁ : Slots Γ₁
slots₁ = oneSlot (scripted (hot ((after 0 , 5) ∷ (after 0 , 7) ∷ [])))

row-arrival : Confirms (take-bounds-values 6 1 src₁ slots₁)
row-arrival = s≤s z≤n

----------------------------------------------------------------------
-- NON-VACUITY, and it is what makes rows 1 and 3 rows at all.  Each
-- bound is TIGHT — the take emits exactly its budget — so neither is
-- satisfied by a node that emits nothing, which is the shape a
-- mis-spent budget would produce and the one an inequality hides.
-- Pinned beside it is what the SAME program emits with the take
-- removed, because a cut that let everything through would also
-- satisfy `1 ≤ 1` at a program that only ever had one value.
----------------------------------------------------------------------

mid-burst-cuts : emitValues (evaluate↓ 0 (takeᵉ (nat̂ 1) pair₀) noSlots) ≡ 3 ∷ []
mid-burst-cuts = refl

mid-burst-uncut : emitValues (evaluate↓ 0 pair₀ noSlots) ≡ 3 ∷ 7 ∷ []
mid-burst-uncut = refl

arrival-cuts : emitValues (evaluate↓ 6 (takeᵉ (nat̂ 1) src₁) slots₁) ≡ 5 ∷ []
arrival-cuts = refl

arrival-uncut : emitValues (evaluate↓ 6 src₁ slots₁) ≡ 5 ∷ 7 ∷ []
arrival-uncut = refl
