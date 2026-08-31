-- WHAT A PARKED TERM OWES, HELD WHERE THE STORE CAN CARRY IT.  A
-- `mergeAll` queue is written by one arm and read by another, with an
-- arbitrary amount of walking in between, so the ceiling its drain
-- reads cannot be derived at the read: nothing the walk holds there
-- mentions a term parked before it started.  It is therefore an
-- invariant of the STORE, one implication per queued term.
--
-- AND IT IS QUANTIFIED OVER THE LEVEL RATHER THAN HELD AT ONE, which is
-- what makes it preservable and is the weakest of the forms that work.
-- A ceiling does not transport upward for free -- a higher level has
-- strictly less room -- so a receipt held at the level of the WRITE
-- would have to be climbed to the level of the READ, and paying for
-- that climb means holding a receipt with room for every level the walk
-- might still reach.  Asking instead for the receipt AT each such level
-- demands nothing at the levels in between, and the reader takes the
-- one it is standing at.  The bound is the count, because a level above
-- it has no room at all and the claim there would be false.
module Verify-Budget-Sufficient.Drain-Store where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp using (Ctx; Closed; sizeᵉ)
open import Rx.Prim using (Source)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (EvalSt; NodeId; mergeAll-st; lookupNode)
open import Verify-Budget-Sufficient.Caps using (Caps; sizeCount)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Verify-Budget-Sufficient.Nest-Ceiling using (CeilD)

queueCeil : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (d : ℕ) (sl : Slots Γ)
  (sh : List Source) → List (Closed Γ u) → Set
queueCeil c d sl sh []      = ⊤
queueCeil c d sl sh (o ∷ q) =
  (∀ (Lv : ℕ) → Lv ≤ sizeCount c d ⊔ Caps.cSize c →
     CeilD c d Lv (nest o sl sh) (suc (suc (sizeᵉ o))))
  × queueCeil c d sl sh q

storeCeil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (st : EvalSt e) → Set
storeCeil {Γ = Γ} c d sl st =
  ∀ {u} (j : NodeId) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
    lookupNode j (EvalSt.nodes st) ≡ just (mergeAll-st {t = u} lim act q od) →
    queueCeil c d sl (EvalSt.connectedShares st) q
