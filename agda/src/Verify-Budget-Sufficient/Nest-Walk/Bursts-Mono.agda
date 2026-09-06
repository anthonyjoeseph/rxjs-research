-- THE WALK'S BURST LEDGER IS UPWARD-CLOSED IN ITS WIDTH, WHICH IS THE
-- ONE DIRECTION THE CAPS LADDER LEAVES OPEN.  Every occurrence of the
-- width in this family sits on the RIGHT of a `≤` -- the head conjunct
-- at each clause, the drain's count at a merging frame, and both room
-- readings at a subscribing one -- so a ledger held at one width is
-- held at every larger one, and nothing about the state or the path
-- has to move with it.  The descent is what the ladder refuses, and it
-- is refuted where the statement that wanted it lives.
--
-- CUT OFF THE WALK FACE BECAUSE A FOCUS CHECK PAYS FOR THE WHOLE FILE.
-- These are one genuine cycle -- the ledger recurses through its own
-- sink dispatch, so nothing here may be split further -- and they are
-- not mutual with the predicates they walk, which is why they are not
-- left beside them.
module Verify-Budget-Sufficient.Nest-Walk.Bursts-Mono where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)

open import Rx.Prim using (Tick; Id; Gas)
open import Rx.Exp using (Ctx; Closed; Val; obs)
open import Rx.Evaluator using (Sched; EvalSt; Path; Frame; AllOp; NodeId; RegId;
  root; share-sink; _↠_; map-f; scan-f; take-f; thru-outer; from-inner;
  shareAdmit; shareLatch)
open import Verify-Budget-Sufficient.Nest-Walk using
  (burstsOK; dispatchBurstsOK; shareBurstsOK; frameDrainW; thruRoomW;
   thruRoomWOK)

----------------------------------------------------------------------
-- ONE SUBSCRIBING FRAME'S ROOM, which is where the width is read twice
-- -- once at the state handed in and once at the state a kill leaves
-- -- and both readings are bounds rather than equalities.
----------------------------------------------------------------------

thruRoomW-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W W′ : ℕ) → W ≤ W′ → (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  thruRoomW W fuel op nid κ id now o sched st →
  thruRoomW W′ fuel op nid κ id now o sched st
thruRoomW-mono-W W W′ hW fuel op nid κ id now o sched st (h₁ , h₂) =
  ≤-trans h₁ hW , λ cur od eq → ≤-trans (h₂ cur od eq) hW

thruRoomWOK-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (W W′ : ℕ) → W ≤ W′ → (fuel : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  thruRoomWOK W fuel op nid κ id now os sched st →
  thruRoomWOK W′ fuel op nid κ id now os sched st
thruRoomWOK-mono-W W W′ hW fuel op nid κ id now [] sched st h = tt
thruRoomWOK-mono-W W W′ hW fuel op nid κ id now (o ∷ os) sched st (h₁ , h₂) =
  thruRoomW-mono-W W W′ hW fuel op nid κ id now o sched st h₁
  , thruRoomWOK-mono-W W W′ hW fuel op nid κ id now os _ _ h₂

----------------------------------------------------------------------
-- AND THE PER-FRAME DRAIN, whose three forwarding arms owe nothing at
-- either width and whose two `*All` arms are the readings above and a
-- queue's own count.
----------------------------------------------------------------------

frameDrainW-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (W W′ : ℕ) → W ≤ W′ → (sf : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  frameDrainW W sf id now f p vals sched st →
  frameDrainW W′ sf id now f p vals sched st
frameDrainW-mono-W W W′ hW sf id now (map-f _) p vals sched st h = tt
frameDrainW-mono-W W W′ hW sf id now (scan-f _ _) p vals sched st h = tt
frameDrainW-mono-W W W′ hW sf id now (take-f _) p vals sched st h = tt
frameDrainW-mono-W W W′ hW sf id now (thru-outer op nid) p vals sched st h =
  thruRoomWOK-mono-W W W′ hW sf op nid p id now vals sched st h
frameDrainW-mono-W W W′ hW sf id now (from-inner _ _ _) p vals sched st h =
  λ lim act q od eq → ≤-trans (h lim act q od eq) hW

----------------------------------------------------------------------
-- THE LEDGER ITSELF, walking the path and then the fan-out the same
-- way the predicate does.
----------------------------------------------------------------------

mutual
  burstsOK-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (W W′ : ℕ) → W ≤ W′ → (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
    (p : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    burstsOK W sf gas id now p vals fin sched st →
    burstsOK W′ sf gas id now p vals fin sched st
  burstsOK-mono-W W W′ hW sf gas id now root vals fin sched st h =
    ≤-trans h hW
  burstsOK-mono-W W W′ hW sf gas id now (share-sink i) vals fin sched st
    (h₁ , h₂) =
    ≤-trans h₁ hW
    , dispatchBurstsOK-mono-W W W′ hW sf gas id now i vals fin sched st h₂
  burstsOK-mono-W W W′ hW sf gas id now (f ↠ p) vals fin sched st
    (h₁ , h₂ , h₃) =
    ≤-trans h₁ hW
    , frameDrainW-mono-W W W′ hW sf id now f p vals sched st h₂
    , burstsOK-mono-W W W′ hW sf gas id now p _ _ _ _ h₃

  dispatchBurstsOK-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (W W′ : ℕ) → W ≤ W′ → (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    dispatchBurstsOK W sf gas id now i vals fin sched st →
    dispatchBurstsOK W′ sf gas id now i vals fin sched st
  dispatchBurstsOK-mono-W W W′ hW sf zero id now i vals fin sched st h = tt
  dispatchBurstsOK-mono-W W W′ hW sf (suc gas) id now i vals fin sched st h =
    shareBurstsOK-mono-W W W′ hW sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st) h

  shareBurstsOK-mono-W : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (W W′ : ℕ) → W ≤ W′ → (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) →
    shareBurstsOK W sf gas id now i vals fin ps sched st →
    shareBurstsOK W′ sf gas id now i vals fin ps sched st
  shareBurstsOK-mono-W W W′ hW sf gas id now i vals fin [] sched st h = tt
  shareBurstsOK-mono-W W W′ hW sf gas id now i vals fin ((rid , p) ∷ ps)
    sched st with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = λ h →
    shareBurstsOK-mono-W W W′ hW sf gas id now i vals fin ps sched st h
  ... | false = λ h →
    burstsOK-mono-W W W′ hW sf gas id now p vals fin _ _ (proj₁ h)
    , shareBurstsOK-mono-W W W′ hW sf gas id now i vals fin ps _ _ (proj₂ h)
