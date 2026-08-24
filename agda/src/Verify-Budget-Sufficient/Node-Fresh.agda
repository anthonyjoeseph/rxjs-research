------------------------------------------------------------------
-- FRESHNESS OF THE NODE TABLE ACROSS ONE SUBSCRIBE — the ring, now
-- discharged, over no leaf at all.
--
-- THE FACT.  `subscribeE` never writes a node BELOW the `nextNode`
-- watermark it was handed.  Everything it writes, it minted.  So a node
-- the CALLER installed — at an id the caller minted, hence strictly
-- below the watermark the callee receives — comes back untouched, and
-- the caller reads it back by `lookupNode-setNode` (.Node-Table).
--
-- WHY IT IS TRUE, from the evaluator.  The only writers to a node are
-- `stepFrame`'s scan-f and take-f clauses and the *All machinery
-- (`flattenBump`, `thruConsume`, `thruWrap`, `innerFinish`, `takeDispatch`),
-- and EVERY ONE of them writes the nid CARRIED BY THE FRAME IT IS
-- STEPPING — never another.  `pushBurst` applies `stepFrame` for ONE
-- frame and returns the transformed burst; it does not walk the rest of
-- the path.  So a subscribe pushes only through the frame it just built,
-- over a nid it just minted.  The share path does not break this:
-- `sharedConnect` lets the connect burst flow up the FIRST subscriber's
-- own frames (the burst it returns), while the other registered chains
-- are served by dispatch on later ARRIVALS, not by the connect.
--
-- ⚠ THE WATERMARK IS AN ARGUMENT, NOT A FIELD, AND THAT IS THE WHOLE
-- ASYMMETRY WITH `.Keeps-Ring`.  A `stepFrame` at `scan-f nid` writes a
-- node minted BEFORE the reaction, so "writes nothing below the current
-- nextNode" is FALSE at a `stepFrame` boundary and TRUE at a `subscribeE`
-- one.  Threading `w` explicitly is what lets both live in one ring: the
-- frame-carrying members take `w ≤ nid` (or `frameAbove w f`) as a
-- premise, and the subscribe clauses discharge it with `≤-refl` because
-- they push through the nid they just minted.  Fixing ONE `w` across a
-- composition is also what makes `fresh-trans` need no weakening — the
-- inequality that would otherwise have to be re-derived at every hop.
--
-- WHAT IT IS NOT, kept because the alignment is the trap: the caps face.
-- `capsOK?` BOUNDS every node and IDENTIFIES none, so no strengthening of
-- a caps receipt reaches a statement that a particular nid holds a
-- particular value — the difference is in KIND, not in a quantifier.
--
-- A probe series once carried this fact and no longer does: the ring
-- proves it at every `κ`, including the `share-sink` tail the probe could
-- not reach, so the probe expired with its target and was deleted.  The
--
-- THE MEMBER LIST MIRRORS `.Keeps-Ring` ONE FOR ONE, and the two rings
-- are complementary in a way worth knowing before editing either: where
-- Keeps says `keeps refl (λ s p → p)` — state changed, but not the slots
-- or the share list — is exactly where the NODES changed, so those arms
-- are this ring's only real work, and everything else is `fresh-refl` or
-- a `fresh-trans`.
------------------------------------------------------------------
--
-- The recovery pointer for this module sits on `subscribeE-nodes-below`.
module Verify-Budget-Sufficient.Node-Fresh where

open import Data.Bool  using (Bool; true; false; not; if_then_else_)
open import Data.Nat   using (ℕ; zero; suc; pred; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.List  using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin   using (Fin; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit  using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

open import Rx.Prim   using (Gas; g0; gs; Tick; Id; InstEmit; InstEvent;
                             hot; cold)
open import Data.Vec  using (lookup)
open import Rx.Exp    using (Ctx; Closed; Val; obs; _≟ᵗ_; evalTm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; flattenᵉ;
  switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; Stream; Path;
                                Frame; AllOp;
                                flattenᵒ; switchᵒ; exhaustᵒ;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                share-sink; _↠_;
                                scan-st; take-st; flatten-st;
                                switch-st; exhaust-st;
                                lookupNode; setNode; flattenBump; hasRoom;
                                mintNode; installNode; register;
                                memberSource; takeVals; splitEvents;
                                burstCompleted;
                                subscribeE; subscribeInner; subscribeAll;
                                stepFrame; pushBurst;
                                takeDispatch; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                flattenDrain; innerFinish; innerReact;
                                sharedConnect; subscribeSharedSlot;
                                aliveThroughᶠ)
open import Rx.Slots using (scripted; shared)

open import Verify-Budget-Sufficient.Node-Table
  using (lookupNode-setNode; lookupNode-setNode-other)
open import Decide using (sucle→≢ᵇ)

------------------------------------------------------------------
-- the relation, and its two structural facts
------------------------------------------------------------------

record FreshC {n} {Γ : Ctx n} (w nx nx′ : ℕ)
              (ns ns′ : List (NodeId × NodeState Γ)) : Set where
  constructor fresh
  field
    nxMono : nx ≤ nx′
    frozen : ∀ k → suc k ≤ w → lookupNode k ns′ ≡ lookupNode k ns
open FreshC

Fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
        ℕ → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
Fresh w sched st sched′ st′ =
  FreshC w (Sched.nextNode sched) (Sched.nextNode sched′)
           (EvalSt.nodes st) (EvalSt.nodes st′)

fresh-refl : ∀ {n} {Γ : Ctx n} {w nx : ℕ} {ns : List (NodeId × NodeState Γ)} →
             FreshC w nx nx ns ns
fresh-refl = fresh ≤-refl (λ k _ → refl)

fresh-trans : ∀ {n} {Γ : Ctx n} {w a b c : ℕ}
              {x y z : List (NodeId × NodeState Γ)} →
              FreshC w a b x y → FreshC w b c y z → FreshC w a c x z
fresh-trans p q =
  fresh (≤-trans (nxMono p) (nxMono q))
        (λ k h → trans (frozen q k h) (frozen p k h))

-- BELOW THE WATERMARK A WRITE IS INVISIBLE.  Every real arm of the ring
-- is this line; the `w ≤ nid` premise is what the frame carries.
frozen-setNode : ∀ {n} {Γ : Ctx n} (w nid : ℕ) (v : NodeState Γ)
  (ns : List (NodeId × NodeState Γ)) → w ≤ nid →
  ∀ k → suc k ≤ w → lookupNode k (setNode nid v ns) ≡ lookupNode k ns
frozen-setNode w nid v ns hw k hk =
  lookupNode-setNode-other k nid v ns (sucle→≢ᵇ (≤-trans hk hw))

frozen-flattenBump : ∀ {n} {Γ : Ctx n} (w nid : ℕ) (d : Bool)
  (ns : List (NodeId × NodeState Γ)) → w ≤ nid →
  ∀ k → suc k ≤ w → lookupNode k (flattenBump nid d ns) ≡ lookupNode k ns
frozen-flattenBump w nid d ns hw k hk with lookupNode nid ns
... | just (flatten-st lim m q od) =
      frozen-setNode w nid
        (flatten-st lim (if d then m else suc m) q od) ns hw k hk
... | just (scan-st _)       = refl
... | just (take-st _)       = refl
... | just (switch-st _ _)   = refl
... | just (exhaust-st _ _)  = refl
... | nothing                = refl

-- what a frame owes the watermark: its own nid, since its own nid is the
-- only one it writes.  `map-f` writes nothing, hence the trivial arm.
frameAbove : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Set
frameAbove w (map-f _)              = ⊤
frameAbove w (scan-f _ nid)         = w ≤ nid
frameAbove w (take-f nid)           = w ≤ nid
frameAbove w (from-inner _ a i)     = w ≤ a × w ≤ i
frameAbove w (thru-outer _ nid)     = w ≤ nid

------------------------------------------------------------------
-- the ring's members, stated before any is proven
------------------------------------------------------------------

subscribeE-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let r = subscribeE g b κ id now sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeInner-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let r = subscribeInner g op allNid κ id now o sched st
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

thruConsume-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched → w ≤ nid →
  let r = thruConsume g op nid κ id now o sched st
  in Fresh w sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWalk-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched → w ≤ nid →
  let r = thruWalk g op nid κ id now os sched st
  in Fresh w sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWrap-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) → w ≤ nid →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

flattenDrain-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (w : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched →
  let r = flattenDrain g allNid κ id now lim act q sched st
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

innerFinish-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (w : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  w ≤ Sched.nextNode sched → w ≤ allNid →
  let r = innerFinish g op allNid inst κ id now vals sched st mns
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

innerReact-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (w : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
  w ≤ Sched.nextNode sched → w ≤ allNid →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

takeDispatch-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (w : ℕ) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) → w ≤ nid →
  let r = takeDispatch {t = t} {e = e} nid vals fin sched st mns
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

switchKill-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (w : ℕ) (mv : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  let r = switchKill {t = t} {e = e} mv sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

stepFrame-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (w : ℕ) (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched → frameAbove w f →
  let r = stepFrame g id now f κ vals fin sched st
  in Fresh w sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

pushBurst-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (w : ℕ) (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched → frameAbove w f →
  let r = pushBurst g id now f κ ems sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeAll-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let r = subscribeAll g op ns b κ id now sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (w : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let r = sharedConnect g i d κ id now sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedSlot-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (w : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-core-fresh : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (w : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → w ≤ Sched.nextNode sched →
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      r   = subscribeE g d (share-sink i) id now sched st₁
  in Fresh w sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

------------------------------------------------------------------
-- THE PURE LEAVES.  `switchKill` cuts registrations and sweeps live —
-- it never touches the node table, so it is the one member with no
-- watermark premise at all.
------------------------------------------------------------------

takeDispatch-fresh w nid vals fin sched st (just (take-st k)) hn
  with proj₂ (proj₂ (takeVals k vals))
... | true  = fresh ≤-refl (frozen-setNode w nid (take-st zero) (EvalSt.nodes st) hn)
... | false = fresh ≤-refl (frozen-setNode w nid
                (take-st (proj₁ (proj₂ (takeVals k vals)))) (EvalSt.nodes st) hn)
takeDispatch-fresh w nid vals fin sched st nothing                  hn = fresh-refl
takeDispatch-fresh w nid vals fin sched st (just (scan-st _))       hn = fresh-refl
takeDispatch-fresh w nid vals fin sched st (just (flatten-st _ _ _ _)) hn = fresh-refl
takeDispatch-fresh w nid vals fin sched st (just (switch-st _ _))   hn = fresh-refl
takeDispatch-fresh w nid vals fin sched st (just (exhaust-st _ _))  hn = fresh-refl

switchKill-fresh w nothing  sched st = fresh-refl
switchKill-fresh w (just v) sched st = fresh-refl

thruWrap-fresh w op nid false vs bs sched st hn = fresh-refl
thruWrap-fresh w flattenᵒ nid true vs bs sched st hn
  with lookupNode nid (EvalSt.nodes st)
... | just (flatten-st lim act q _) = fresh ≤-refl (frozen-setNode w nid
                                    (flatten-st lim act q true) (EvalSt.nodes st) hn)
... | just (scan-st _)         = fresh-refl
... | just (take-st _)         = fresh-refl
... | just (switch-st _ _)     = fresh-refl
... | just (exhaust-st _ _)    = fresh-refl
... | nothing                  = fresh-refl
thruWrap-fresh w switchᵒ nid true vs bs sched st hn
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _)   = fresh ≤-refl (frozen-setNode w nid
                                    (switch-st cur true) (EvalSt.nodes st) hn)
... | just (scan-st _)         = fresh-refl
... | just (take-st _)         = fresh-refl
... | just (flatten-st _ _ _ _) = fresh-refl
... | just (exhaust-st _ _)    = fresh-refl
... | nothing                  = fresh-refl
thruWrap-fresh w exhaustᵒ nid true vs bs sched st hn
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _)  = fresh ≤-refl (frozen-setNode w nid
                                    (exhaust-st act true) (EvalSt.nodes st) hn)
... | just (scan-st _)         = fresh-refl
... | just (take-st _)         = fresh-refl
... | just (flatten-st _ _ _ _) = fresh-refl
... | just (switch-st _ _)     = fresh-refl
... | nothing                  = fresh-refl

------------------------------------------------------------------
-- THE RECURSIVE MEMBERS
------------------------------------------------------------------

subscribeInner-fresh w g0 op allNid κ id now o sched st hw =
  fresh (n≤1+n _) (λ k _ → refl)
subscribeInner-fresh w (gs fuel) op allNid κ id now o sched st hw =
  fresh (≤-trans (n≤1+n _) (nxMono SE)) (frozen SE)
  where
  SE = subscribeE-fresh w fuel o
         (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
         (record sched { nextNode = suc (Sched.nextNode sched) }) st
         (≤-trans hw (n≤1+n _))

thruConsume-fresh {u = u} w g flattenᵒ nid κ id now o sched st hw hn
  with lookupNode nid (EvalSt.nodes st)
... | just (flatten-st {v} lim act q od) with v ≟ᵗ u
...   | no _     = fresh-refl
...   | yes refl with hasRoom lim act
...     | false  = fresh ≤-refl (frozen-setNode w nid
                      (flatten-st lim act (q ++ o ∷ []) od) (EvalSt.nodes st) hn)
...     | true   =
          fresh-trans (subscribeInner-fresh w g flattenᵒ nid κ id now o sched st hw)
            (fresh ≤-refl (frozen-flattenBump w nid
               (proj₁ (proj₂ (proj₂ (proj₂
                 (subscribeInner g flattenᵒ nid κ id now o sched st)))))
               (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
                 (subscribeInner g flattenᵒ nid κ id now o sched st))))))) hn))
thruConsume-fresh w g flattenᵒ nid κ id now o sched st hw hn | nothing = fresh-refl
thruConsume-fresh w g flattenᵒ nid κ id now o sched st hw hn | just (scan-st _) = fresh-refl
thruConsume-fresh w g flattenᵒ nid κ id now o sched st hw hn | just (take-st _) = fresh-refl
thruConsume-fresh w g flattenᵒ nid κ id now o sched st hw hn | just (switch-st _ _) = fresh-refl
thruConsume-fresh w g flattenᵒ nid κ id now o sched st hw hn | just (exhaust-st _ _) = fresh-refl
thruConsume-fresh w g switchᵒ nid κ id now o sched st hw hn
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
      fresh-trans (switchKill-fresh w cur sched st)
        (fresh-trans
          (subscribeInner-fresh w g switchᵒ nid κ id now o
             (proj₁ (proj₂ (switchKill cur sched st)))
             (proj₂ (proj₂ (switchKill cur sched st)))
             (≤-trans hw (nxMono (switchKill-fresh w cur sched st))))
          (fresh ≤-refl (frozen-setNode w nid
             (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ SI)))
                         then nothing else just (proj₁ SI)) od)
             (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))) hn)))
      where SI = subscribeInner g switchᵒ nid κ id now o
                   (proj₁ (proj₂ (switchKill cur sched st)))
                   (proj₂ (proj₂ (switchKill cur sched st)))
... | just (scan-st _)       = fresh-refl
... | just (take-st _)       = fresh-refl
... | just (flatten-st _ _ _ _) = fresh-refl
... | just (exhaust-st _ _)  = fresh-refl
... | nothing                = fresh-refl
thruConsume-fresh w g exhaustᵒ nid κ id now o sched st hw hn
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st true od)  = fresh-refl
... | just (exhaust-st false od) =
      fresh-trans (subscribeInner-fresh w g exhaustᵒ nid κ id now o sched st hw)
                  (fresh ≤-refl (frozen-setNode w nid
                     (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ SI))))) od)
                     (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))) hn))
      where SI = subscribeInner g exhaustᵒ nid κ id now o sched st
... | just (scan-st _)       = fresh-refl
... | just (take-st _)       = fresh-refl
... | just (flatten-st _ _ _ _) = fresh-refl
... | just (switch-st _ _)   = fresh-refl
... | nothing                = fresh-refl

thruWalk-fresh w g op nid κ id now [] sched st hw hn = fresh-refl
thruWalk-fresh w g op nid κ id now (o ∷ os) sched st hw hn =
  fresh-trans TC
    (thruWalk-fresh w g op nid κ id now os
      (proj₁ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      (proj₂ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      (≤-trans hw (nxMono TC)) hn)
  where TC = thruConsume-fresh w g op nid κ id now o sched st hw hn

flattenDrain-fresh w g allNid κ id now lim act [] sched st hw = fresh-refl
flattenDrain-fresh w g allNid κ id now lim act (o ∷ q) sched st hw
  with hasRoom lim act
... | false = fresh-refl
... | true  =
      fresh-trans SI
        (flattenDrain-fresh w g allNid κ id now lim
          (if proj₁ (proj₂ (proj₂ (proj₂
             (subscribeInner g flattenᵒ allNid κ id now o sched st))))
           then act else suc act) q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g flattenᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g flattenᵒ allNid κ id now o sched st))))))
          (≤-trans hw (nxMono SI)))
      where SI = subscribeInner-fresh w g flattenᵒ allNid κ id now o sched st hw

innerFinish-fresh {s = s} w g flattenᵒ allNid inst κ id now vals sched st
                  (just (flatten-st {v} lim act q od)) hw ha with v ≟ᵗ s
... | yes refl =
      fresh-trans FD
        (fresh ≤-refl (frozen-setNode w allNid
           (flatten-st lim (proj₁ (proj₂ (proj₂ DR)))
                       (proj₁ (proj₂ (proj₂ (proj₂ DR)))) od)
           (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR)))))) ha))
      where
      FD = flattenDrain-fresh w g allNid κ id now lim (pred act) q sched st hw
      DR = flattenDrain g allNid κ id now lim (pred act) q sched st
... | no _ = fresh-refl
innerFinish-fresh w g flattenᵒ allNid inst κ id now vals sched st nothing hw ha = fresh-refl
innerFinish-fresh w g flattenᵒ allNid inst κ id now vals sched st (just (scan-st _)) hw ha = fresh-refl
innerFinish-fresh w g flattenᵒ allNid inst κ id now vals sched st (just (take-st _)) hw ha = fresh-refl
innerFinish-fresh w g flattenᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) hw ha = fresh-refl
innerFinish-fresh w g flattenᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st
                  (just (switch-st (just c) od)) hw ha with c ≡ᵇ inst
... | true  = fresh ≤-refl (frozen-setNode w allNid
                 (switch-st nothing od) (EvalSt.nodes st) ha)
... | false = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing od)) hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st nothing hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st (just (scan-st _)) hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st (just (take-st _)) hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st (just (flatten-st _ _ _ _)) hw ha = fresh-refl
innerFinish-fresh w g switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) hw ha = fresh-refl
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st
                  (just (exhaust-st act od)) hw ha =
  fresh ≤-refl (frozen-setNode w allNid (exhaust-st false od) (EvalSt.nodes st) ha)
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st nothing hw ha = fresh-refl
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st (just (scan-st _)) hw ha = fresh-refl
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st (just (take-st _)) hw ha = fresh-refl
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st (just (flatten-st _ _ _ _)) hw ha = fresh-refl
innerFinish-fresh w g exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) hw ha = fresh-refl

innerReact-fresh w g op allNid inst κ id now vals sched st false hw ha = fresh-refl
innerReact-fresh w g op allNid inst κ id now vals sched st true hw ha
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = fresh-refl
... | false = innerFinish-fresh w g op allNid inst κ id now vals sched st
                (lookupNode allNid (EvalSt.nodes st)) hw ha

stepFrame-fresh w g id now (map-f fn) κ vals fin sched st hw hf = fresh-refl
stepFrame-fresh {u = u} w g id now (scan-f fn nid) κ vals fin sched st hw hf
  with lookupNode nid (EvalSt.nodes st)
... | just (scan-st {v} sacc) with v ≟ᵗ u
...   | yes refl = fresh ≤-refl (frozen-setNode w nid
                      (scan-st (proj₂ (Rx.Evaluator.scanVals fn sacc vals)))
                      (EvalSt.nodes st) hf)
...   | no _     = fresh-refl
stepFrame-fresh w g id now (scan-f fn nid) κ vals fin sched st hw hf | nothing = fresh-refl
stepFrame-fresh w g id now (scan-f fn nid) κ vals fin sched st hw hf | just (take-st _) = fresh-refl
stepFrame-fresh w g id now (scan-f fn nid) κ vals fin sched st hw hf | just (flatten-st _ _ _ _) = fresh-refl
stepFrame-fresh w g id now (scan-f fn nid) κ vals fin sched st hw hf | just (switch-st _ _) = fresh-refl
stepFrame-fresh w g id now (scan-f fn nid) κ vals fin sched st hw hf | just (exhaust-st _ _) = fresh-refl
stepFrame-fresh w g id now (take-f nid) κ vals fin sched st hw hf =
  takeDispatch-fresh w nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) hf
stepFrame-fresh w g id now (from-inner op allNid inst) κ vals fin sched st hw hf =
  innerReact-fresh w g op allNid inst κ id now vals sched st fin hw (proj₁ hf)
stepFrame-fresh w g id now (thru-outer op nid) κ vals fin sched st hw hf =
  fresh-trans (thruWalk-fresh w g op nid κ id now vals sched st hw hf)
    (thruWrap-fresh w op nid fin
      (proj₁ TW) (proj₁ (proj₂ TW))
      (proj₁ (proj₂ (proj₂ TW))) (proj₂ (proj₂ (proj₂ TW))) hf)
  where TW = thruWalk g op nid κ id now vals sched st

pushBurst-fresh w g id now f κ [] sched st hw hf = fresh-refl
pushBurst-fresh w g id now f κ (em ∷ ems) sched st hw hf =
  fresh-trans SFf
    (pushBurst-fresh w g id now f κ ems
       (proj₁ (proj₂ (proj₂ (proj₂ SF))))
       (proj₂ (proj₂ (proj₂ (proj₂ SF))))
       (≤-trans hw (nxMono SFf)) hf)
  where
  sp  = splitEvents (InstEmit.events em)
  SF  = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  SFf = stepFrame-fresh w g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st hw hf

subscribeAll-fresh w g op ns b κ id now sched st hw =
  fresh-trans (fresh (n≤1+n _)
                (frozen-setNode w (Sched.nextNode sched) ns (EvalSt.nodes st) hw))
    (fresh-trans SEf
      (pushBurst-fresh w g id now (thru-outer op (Sched.nextNode sched)) κ
        (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
        (≤-trans hw (≤-trans (n≤1+n _) (nxMono SEf))) hw))
  where
  SE  = subscribeE g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) ns st)
  SEf = subscribeE-fresh w g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) ns st)
          (≤-trans hw (n≤1+n _))

sharedConnect-core-fresh w fuel i d κ id now sched st hw =
  subscribeE-fresh w fuel d (share-sink i) id now sched
    (register (toℕ i) κ
      (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })) hw

sharedConnect-fresh w g0 i d κ id now sched st hw = fresh-refl
sharedConnect-fresh w (gs fuel) i d κ id now sched st hw
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-core-fresh w fuel i d κ id now sched st hw
... | false = sharedConnect-core-fresh w fuel i d κ id now sched st hw

sharedSlot-fresh w g i d κ id now sched st hw
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = fresh-refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = fresh-refl
...   | false = sharedConnect-fresh w g i d κ id now sched st hw

subscribeE-fresh {Γ = Γ} w g (input i) κ id now sched st hw with Sched.slots sched i
... | shared d = sharedSlot-fresh w g i d κ id now sched st hw
... | scripted (hot _) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = fresh-refl
...   | false = fresh-refl
subscribeE-fresh w g (input i) κ id now sched st hw | scripted (cold sync []) = fresh-refl
subscribeE-fresh w g (input i) κ id now sched st hw | scripted (cold sync (x ∷ xs)) = fresh-refl
subscribeE-fresh w g (ofᵉ ts)  κ id now sched st hw = fresh-refl
subscribeE-fresh w g emptyᵉ    κ id now sched st hw = fresh-refl
subscribeE-fresh w g (mapᵉ f b) κ id now sched st hw =
  fresh-trans SEf
    (pushBurst-fresh w g id now (map-f f) κ
      (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
      (≤-trans hw (nxMono SEf)) tt)
  where
  SE  = subscribeE g b (map-f f ↠ κ) id now sched st
  SEf = subscribeE-fresh w g b (map-f f ↠ κ) id now sched st hw
subscribeE-fresh w g (takeᵉ count b) κ id now sched st hw with evalTm count
... | zero  = fresh-refl
... | suc k =
      fresh-trans (fresh (n≤1+n _)
                    (frozen-setNode w (Sched.nextNode sched)
                       (take-st (suc k)) (EvalSt.nodes st) hw))
        (fresh-trans SEf
          (pushBurst-fresh w g id now (take-f (Sched.nextNode sched)) κ
            (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
            (≤-trans hw (≤-trans (n≤1+n _) (nxMono SEf))) hw))
      where
      SE  = subscribeE g b (take-f (Sched.nextNode sched) ↠ κ) id now
              (record sched { nextNode = suc (Sched.nextNode sched) })
              (installNode (Sched.nextNode sched) (take-st (suc k)) st)
      SEf = subscribeE-fresh w g b (take-f (Sched.nextNode sched) ↠ κ) id now
              (record sched { nextNode = suc (Sched.nextNode sched) })
              (installNode (Sched.nextNode sched) (take-st (suc k)) st)
              (≤-trans hw (n≤1+n _))
subscribeE-fresh w g (scanᵉ f z b) κ id now sched st hw =
  fresh-trans (fresh (n≤1+n _)
                (frozen-setNode w (Sched.nextNode sched)
                   (scan-st (evalTm z)) (EvalSt.nodes st) hw))
    (fresh-trans SEf
      (pushBurst-fresh w g id now (scan-f f (Sched.nextNode sched)) κ
        (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
        (≤-trans hw (≤-trans (n≤1+n _) (nxMono SEf))) hw))
  where
  SE  = subscribeE g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
  SEf = subscribeE-fresh w g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
          (≤-trans hw (n≤1+n _))
subscribeE-fresh {u = u} w g (flattenᵉ lim b) κ id now sched st hw =
  subscribeAll-fresh w g flattenᵒ (flatten-st {t = u} lim 0 [] false) b κ id now sched st hw
subscribeE-fresh w g (switchAllᵉ b) κ id now sched st hw =
  subscribeAll-fresh w g switchᵒ (switch-st nothing false) b κ id now sched st hw
subscribeE-fresh w g (exhaustAllᵉ b) κ id now sched st hw =
  subscribeAll-fresh w g exhaustᵒ (exhaust-st false false) b κ id now sched st hw
subscribeE-fresh w g0 (μᵉ body) κ id now sched st hw = fresh-refl
subscribeE-fresh w (gs fuel) (μᵉ body) κ id now sched st hw =
  subscribeE-fresh w fuel (unfoldμ body) κ id now sched st hw
subscribeE-fresh w g (varᵉ ()) κ id now sched st hw
subscribeE-fresh {u = u} w g (deferᵉ body) κ id now sched st hw =
  fresh (n≤1+n _) (frozen-setNode w (Sched.nextNode sched)
                     (flatten-st {t = u} nothing 0 [] false) (EvalSt.nodes st) hw)

------------------------------------------------------------------
-- THE FACE THE CONSUMERS SPEND
------------------------------------------------------------------

-- RECOVERY: `git log --diff-filter=D -- agda/src/Verify-Budget-Sufficient/Scan-Node-Probe.agda`
--   restores 297 lines / 24 refl rows that probed this fact at the scan source
--   before it was proven here.  They pinned the EVALUATOR (that those composites
--   reduce, and reduce to this) rather than the statement, which is why they
--   outlived their target and had to go.
subscribeE-nodes-below : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (k : NodeId) →
  suc k ≤ Sched.nextNode sched →
  lookupNode k (EvalSt.nodes (proj₂ (proj₂ (subscribeE g b κ id now sched st))))
    ≡ lookupNode k (EvalSt.nodes st)
subscribeE-nodes-below g b κ id now sched st k hk =
  frozen (subscribeE-fresh (Sched.nextNode sched) g b κ id now sched st ≤-refl) k hk

-- THE SHAPE EVERY CONSUMER WANTS: mint, install, subscribe under a frame
-- that mentions the minted nid, read the node back unchanged.  The
-- watermark premise is `≤-refl` here and nowhere else has to know that —
-- `mintNode` returns the old `nextNode` and leaves `suc` of it behind, so
-- the installed id is exactly one below the watermark the callee sees.
mint-install-survives : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  lookupNode (proj₁ (mintNode sched))
    (EvalSt.nodes (proj₂ (proj₂ (subscribeE g b κ id now (proj₂ (mintNode sched))
      (installNode (proj₁ (mintNode sched)) ns st)))))
    ≡ just ns
mint-install-survives g b κ id now ns sched st =
  trans (subscribeE-nodes-below g b κ id now (proj₂ (mintNode sched))
           (installNode (proj₁ (mintNode sched)) ns st)
           (proj₁ (mintNode sched)) ≤-refl)
        (lookupNode-setNode (proj₁ (mintNode sched)) ns (EvalSt.nodes st))
