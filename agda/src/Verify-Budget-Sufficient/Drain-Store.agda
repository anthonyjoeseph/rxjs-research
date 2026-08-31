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

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _⊔_; _≤_; _≡ᵇ_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (yes; no)

open import Rx.Exp using (Ctx; Closed; sizeᵉ; Val; _≟ᵗ_; obs)
open import Rx.Prim using (Source; Gas; Id; Tick)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (NodeId; NodeState; mergeAll-st; lookupNode; setNode;
  EvalSt; Sched; Frame; Path; AllOp; stepFrame; scan-st; take-st;
  switch-st; exhaust-st; map-f; scan-f; take-f; from-inner; thru-outer;
  scanVals; takeVals)
open import Decide using (≡ᵇ→≡; just-injᵂ)
open import Verify-Budget-Sufficient.Node-Table
  using (lookupNode-setNode; lookupNode-setNode-other)
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

-- AND IT IS STATED OVER THE TWO PIECES IT READS, NOT OVER THE STATE.
-- Every arm that writes the store writes a RECORD UPDATE, and two
-- updates touching different fields are different terms however
-- irrelevant the extra field is here; a preservation lemma phrased at
-- one of them does not apply at the other.  The projections reduce, so
-- a caller holding a state supplies `EvalSt.connectedShares` and
-- `EvalSt.nodes` and every such difference disappears.
storeCeil : ∀ {n} {Γ : Ctx n} (c : Caps) (d : ℕ) (sl : Slots Γ)
  (sh : List Source) (nodes : List (NodeId × NodeState Γ)) → Set
storeCeil {Γ = Γ} c d sl sh nodes =
  ∀ {u} (j : NodeId) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ u)) (od : Bool) →
    lookupNode j nodes ≡ just (mergeAll-st {t = u} lim act q od) →
    queueCeil c d sl sh q

-- a node the drain never reads.  The invariant above speaks only about
-- `mergeAll` queues, so a write anywhere else is invisible to it -- and
-- the three frame arms that cannot subscribe write exactly here.
notQueue : ∀ {n} {Γ : Ctx n} → NodeState Γ → Set
notQueue (mergeAll-st _ _ _ _) = ⊥
notQueue _                     = ⊤

abstract
  -- and the invariant survives any such write, at either position: the
  -- one that was overwritten now answers a shape the reader cannot ask
  -- about, and every other reading is the one the hypothesis already
  -- covers
  storeCeil-set : ∀ {n} {Γ : Ctx n} (c : Caps) (d : ℕ) (sl : Slots Γ)
    (sh : List Source) (nodes : List (NodeId × NodeState Γ))
    (j : NodeId) (ns : NodeState Γ) → notQueue ns →
    storeCeil c d sl sh nodes → storeCeil c d sl sh (setNode j ns nodes)
  storeCeil-set c d sl sh nodes j ns nq h i lim act q od with j ≡ᵇ i in eji
  ... | true  = λ hl → ⊥-elim (subst notQueue
                  (just-injᵂ (trans (sym (lookupNode-setNode i ns nodes))
                    (subst (λ x → lookupNode i (setNode x ns nodes)
                                    ≡ just (mergeAll-st lim act q od))
                           (≡ᵇ→≡ j i eji) hl))) nq)
  ... | false = λ hl → h i lim act q od
                  (trans (sym (lookupNode-setNode-other i j ns nodes eji)) hl)

-- WHICH ARMS CAN MOVE IT, AND IT IS THE TWO THAT SUBSCRIBE.  A frame
-- step either rewrites one node of its own -- a scan's accumulator, a
-- take's remaining count -- or reaches `subscribeInner`, and only the
-- second can install a queue, connect a share, or park a term in a
-- queue that already exists.  The first three arms are therefore the
-- write-preservation lemma at a point, and the shares they hand on are
-- the shares they were given.
postulate
  store-ceil-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (d : ℕ) (sl : Slots Γ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId) (p : Path Γ s t) (vals : List (Val Γ s))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    storeCeil c d sl (EvalSt.connectedShares st) (EvalSt.nodes st) →
    let st′ = proj₂ (proj₂ (proj₂ (proj₂
                (stepFrame sf nid now (from-inner op allNid inst) p vals fin sched st))))
    in storeCeil c d sl (EvalSt.connectedShares st′) (EvalSt.nodes st′)

  store-ceil-thru : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (d : ℕ) (sl : Slots Γ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (onid : NodeId) (p : Path Γ u t) (vals : List (Val Γ (obs u)))
    (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    storeCeil c d sl (EvalSt.connectedShares st) (EvalSt.nodes st) →
    let st′ = proj₂ (proj₂ (proj₂ (proj₂
                (stepFrame sf nid now (thru-outer op onid) p vals fin sched st))))
    in storeCeil c d sl (EvalSt.connectedShares st′) (EvalSt.nodes st′)

frame-store-ceil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (d : ℕ) (sl : Slots Γ) (sf : Gas) (nid : Id) (now : Tick)
  (f : Frame Γ s u) (p : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  storeCeil c d sl (EvalSt.connectedShares st) (EvalSt.nodes st) →
  let st′ = proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf nid now f p vals fin sched st))))
  in storeCeil c d sl (EvalSt.connectedShares st′) (EvalSt.nodes st′)
frame-store-ceil c d sl sf nid now (map-f fn) p vals fin sched st h = h
frame-store-ceil c d sl sf nid now (from-inner op a i) p vals fin sched st h =
  store-ceil-inner c d sl sf nid now op a i p vals fin sched st h
frame-store-ceil c d sl sf nid now (thru-outer op onid) p vals fin sched st h =
  store-ceil-thru c d sl sf nid now op onid p vals fin sched st h
frame-store-ceil {u = u} c d sl sf nid now (scan-f fn j) p vals fin sched st h
  with lookupNode j (EvalSt.nodes st)
... | nothing = h
... | just (take-st _) = h
... | just (mergeAll-st _ _ _ _) = h
... | just (switch-st _ _) = h
... | just (exhaust-st _ _) = h
... | just (scan-st {w} acc) with w ≟ᵗ u
...   | no _ = h
...   | yes refl = storeCeil-set c d sl _ (EvalSt.nodes st) j
                     (scan-st (proj₂ (scanVals fn acc vals))) tt h
frame-store-ceil c d sl sf nid now (take-f j) p vals fin sched st h
  with lookupNode j (EvalSt.nodes st)
... | nothing = h
... | just (scan-st _) = h
... | just (mergeAll-st _ _ _ _) = h
... | just (switch-st _ _) = h
... | just (exhaust-st _ _) = h
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | true  = storeCeil-set c d sl _ (EvalSt.nodes st) j (take-st 0) tt h
...   | false = storeCeil-set c d sl _ (EvalSt.nodes st) j
                  (take-st (proj₁ (proj₂ (takeVals k vals)))) tt h
