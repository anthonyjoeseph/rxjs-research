------------------------------------------------------------------
-- THE QUEUE STAYS DEAD AT AN UNBOUNDED LIMIT — the ring's third
-- instance, and the first whose predicate is not a freezing claim.
--
-- THE FACT.  A `mergeAll` node whose limit is `nothing` never acquires
-- a parked inner.  The gate `hasRoom nothing act` is `true` by its
-- first clause, so the one syntactic site that appends to a queue —
-- `thruConsume`'s capacity-shut branch — is unreachable there, and
-- every other writer either reinstalls the queue it read or drains one
-- that was already empty.
--
-- WHY IT NEEDS A RING AND NOT A WALK.  The append site is local, but
-- the node the claim is about outlives a whole burst: `pushBurst` steps
-- one frame, the frame subscribes inners, and each inner's synchronous
-- burst runs the evaluator again.  Nothing bounds that by inspection,
-- so the obligation is closed the way its two siblings are — one
-- statement per evaluator function, all mutually recursive.
--
-- ⚠ THE HYPOTHESIS IS READ AT THE START TABLE, AND EVERY ARM DEPENDS
-- ON IT.  A write of a `switch-st` (or a `take-st`, or a `scan-st`)
-- into node k would break the predicate outright if k were the node the
-- claim is about — and what rules that out is not the node table at the
-- moment of the write, which is several sub-steps downstream, but the
-- read the arm already performed at the table it was ENTERED with.  If
-- that read says k holds a switch, the caller's hypothesis about k is
-- already absurd and the arm closes on `⊥`.  This is why the members
-- carry no watermark and no `frameAbove`: the sibling rings need an
-- ordering premise to prove a write invisible, and this one gets the
-- same conclusion from the hypothesis it is handed.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Queue-Dead where

open import Data.Bool  using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat   using (ℕ; zero; suc; pred; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n)
open import Data.List  using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Fin   using (Fin; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Data.Vec  using (lookup)
open import Rx.Prim   using (Gas; g0; gs; Tick; Id; InstEmit; InstEvent;
                             hot; cold)
open import Rx.Exp    using (Ctx; Closed; Val; obs; _≟ᵗ_; evalTm; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ;
  deferᵉ; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; NodeState; Stream; Path;
                                Frame; AllOp;
                                mergeAllᵒ; switchᵒ; exhaustᵒ;
                                map-f; scan-f; take-f; from-inner; thru-outer;
                                share-sink; _↠_;
                                scan-st; take-st; mergeAll-st;
                                switch-st; exhaust-st;
                                lookupNode; setNode; mergeAllBump; hasRoom;
                                installNode; register;
                                memberSource; takeVals; splitEvents;
                                burstCompleted;
                                subscribeE; subscribeInner; subscribeAll;
                                stepFrame; pushBurst;
                                takeDispatch; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                mergeAllDrain; innerFinish; innerReact;
                                sharedConnect; subscribeSharedSlot;
                                aliveThroughᶠ; scanVals)
open import Rx.Slots using (scripted; shared)

open import Verify-Budget-Sufficient.Node-Table
  using (lookupNode-setNode; lookupNode-setNode-other)
open import Decide using (sucle→≢ᵇ; ≡ᵇ→≡)

------------------------------------------------------------------
-- the predicate, and the relation the ring preserves
------------------------------------------------------------------

-- the parked queue of whatever state sits at a node, as the claim that
-- it is EMPTY AT AN UNBOUNDED LIMIT.  A predicate and not an equation
-- because `NodeState` holds the queue's element type existentially, so
-- the two sides of an equation would not even be at the same type.  The
-- limit is pinned INSIDE it rather than left to the consumer, because
-- the fact is only true at `nothing` — a bounded wrap parks, which is
-- what bounding it is for — and a predicate that reads as
-- limit-agnostic is one a ring can be asked to preserve at a limit
-- where it does not hold
emptyQueue? : ∀ {n} {Γ : Ctx n} → Maybe (NodeState Γ) → Set
emptyQueue? (just (mergeAll-st nothing act q od)) = q ≡ []
emptyQueue? _                                     = ⊥

-- the watermark rides along for exactly one purpose: a freshly minted
-- node is not the node the claim is about, and `suc k ≤ nx` is what
-- says so
record QDeadC {n} {Γ : Ctx n} (k : NodeId) (nx nx′ : ℕ)
              (ns ns′ : List (NodeId × NodeState Γ)) : Set where
  constructor qdead
  field
    nxMono : nx ≤ nx′
    keep   : suc k ≤ nx →
             emptyQueue? (lookupNode k ns) → emptyQueue? (lookupNode k ns′)
open QDeadC

QDead : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
        NodeId → Sched Γ → EvalSt e → Sched Γ → EvalSt e → Set
QDead k sched st sched′ st′ =
  QDeadC k (Sched.nextNode sched) (Sched.nextNode sched′)
           (EvalSt.nodes st) (EvalSt.nodes st′)

qdead-refl : ∀ {n} {Γ : Ctx n} {k nx} {ns : List (NodeId × NodeState Γ)} →
             QDeadC k nx nx ns ns
qdead-refl = qdead ≤-refl (λ _ e → e)

qdead-trans : ∀ {n} {Γ : Ctx n} {k} {a b c : ℕ}
              {x y z : List (NodeId × NodeState Γ)} →
              QDeadC k a b x y → QDeadC k b c y z → QDeadC k a c x z
qdead-trans p q =
  qdead (≤-trans (nxMono p) (nxMono q))
        (λ h e → keep q (≤-trans h (nxMono p)) (keep p h e))

------------------------------------------------------------------
-- the three write shapes
------------------------------------------------------------------

-- a write at an id the caller has to reason about: either it misses k,
-- and the lookup is untouched, or it hits and the value written must
-- itself be queue-dead
qd-set : ∀ {n} {Γ : Ctx n} (k nid : NodeId) (v : NodeState Γ)
  (ns : List (NodeId × NodeState Γ)) →
  (nid ≡ k → emptyQueue? (lookupNode k ns) → emptyQueue? {Γ = Γ} (just v)) →
  emptyQueue? (lookupNode k ns) →
  emptyQueue? (lookupNode k (setNode nid v ns))
qd-set k nid v ns f e with nid ≡ᵇ k in eq
... | true  rewrite ≡ᵇ→≡ nid k eq =
      subst emptyQueue? (sym (lookupNode-setNode k v ns)) (f refl e)
... | false =
      subst emptyQueue? (sym (lookupNode-setNode-other k nid v ns eq)) e

-- a write at a FRESHLY MINTED id.  `suc k ≤ w ≤ nid` is the whole
-- argument, and it is the only place the watermark is spent
qd-mint : ∀ {n} {Γ : Ctx n} (k w nid : NodeId) (v : NodeState Γ)
  (ns : List (NodeId × NodeState Γ)) → w ≤ nid → suc k ≤ w →
  emptyQueue? (lookupNode k ns) →
  emptyQueue? (lookupNode k (setNode nid v ns))
qd-mint k w nid v ns hw hk e =
  subst emptyQueue? (sym (lookupNode-setNode-other k nid v ns
    (sucle→≢ᵇ (≤-trans hk hw)))) e

-- what the hypothesis says about a node the arm has just READ
qd-at : ∀ {n} {Γ : Ctx n} (k nid : NodeId) (ov : NodeState Γ)
  (ns : List (NodeId × NodeState Γ)) →
  lookupNode nid ns ≡ just ov → nid ≡ k →
  emptyQueue? (lookupNode k ns) → emptyQueue? {Γ = Γ} (just ov)
qd-at k nid ov ns leq ne e =
  subst emptyQueue? (trans (cong (λ z → lookupNode z ns) (sym ne)) leq) e

-- THE ARM THAT WOULD OTHERWISE NEED A SECOND INVARIANT.  A write of a
-- state of the wrong KIND is only dangerous when it lands on k, and the
-- read the arm was entered with already says what k holds
qd-clash : ∀ {n} {Γ : Ctx n} {A : Set} (k nid : NodeId) (ov : NodeState Γ)
  (ns0 : List (NodeId × NodeState Γ)) →
  lookupNode nid ns0 ≡ just ov → (emptyQueue? {Γ = Γ} (just ov) → ⊥) →
  nid ≡ k → emptyQueue? (lookupNode k ns0) → A
qd-clash k nid ov ns0 leq bad ne e = ⊥-elim (bad (qd-at k nid ov ns0 leq ne e))

-- the counter and the outer-done flag are not the queue
qd-same : ∀ {n} {Γ : Ctx n} {w} (lim : Maybe ℕ) (a a′ : ℕ)
  (q : List (Closed Γ w)) (od od′ : Bool) →
  emptyQueue? {Γ = Γ} (just (mergeAll-st lim a q od)) →
  emptyQueue? {Γ = Γ} (just (mergeAll-st lim a′ q od′))
qd-same nothing  a a′ q od od′ e = e
qd-same (just m) a a′ q od od′ ()

qd-bump : ∀ {n} {Γ : Ctx n} (k nid : NodeId) (d : Bool)
  (ns : List (NodeId × NodeState Γ)) →
  emptyQueue? (lookupNode k ns) →
  emptyQueue? (lookupNode k (mergeAllBump nid d ns))
qd-bump k nid d ns e with lookupNode nid ns in leq
... | just (mergeAll-st lim m q od) =
      qd-set k nid (mergeAll-st lim (if d then m else suc m) q od) ns
        (λ ne e′ → qd-same lim m (if d then m else suc m) q od od
           (subst emptyQueue?
             (trans (cong (λ z → lookupNode z ns) (sym ne)) leq) e′))
        e
... | just (scan-st _)      = e
... | just (take-st _)      = e
... | just (switch-st _ _)  = e
... | just (exhaust-st _ _) = e
... | nothing               = e

-- AN OPEN GATE IS NOT A SHUT ONE, which is the whole reason the
-- statement is about `nothing` and not about a limit
qd-append : ∀ {n} {Γ : Ctx n} {w} (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ w)) (o : Closed Γ w) (od : Bool) →
  hasRoom lim act ≡ false →
  emptyQueue? {Γ = Γ} (just (mergeAll-st lim act q od)) →
  emptyQueue? {Γ = Γ} (just (mergeAll-st lim act (q ++ o ∷ []) od))
qd-append nothing  act q o od () e
qd-append (just m) act q o od hr ()

-- A DRAIN OF NOTHING DRAINS TO NOTHING, and that is the whole of the
-- `innerFinish` arm: the residue it reinstalls is the queue it was
-- given, which the hypothesis says was already empty
qd-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  emptyQueue? {Γ = Γ} (just (mergeAll-st lim act q od)) →
  let DR = mergeAllDrain g allNid κ id now lim (pred act) q sched st
  in emptyQueue? {Γ = Γ}
       (just (mergeAll-st lim (proj₁ (proj₂ (proj₂ DR)))
                              (proj₁ (proj₂ (proj₂ (proj₂ DR)))) od))
qd-drain g allNid κ id now nothing  act .[] od sched st refl = refl
qd-drain g allNid κ id now (just m) act q   od sched st ()

------------------------------------------------------------------
-- the ring's members, stated before any is proven
------------------------------------------------------------------

subscribeE-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeE g b κ id now sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeInner-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (g : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeInner g op allNid κ id now o sched st
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

thruConsume-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruConsume g op nid κ id now o sched st
  in QDead k sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWalk-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (os : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWalk g op nid κ id now os sched st
  in QDead k sched st (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))

thruWrap-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

mergeAllDrain-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (k : NodeId) (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  let r = mergeAllDrain g allNid κ id now lim act q sched st
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))

innerFinish-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (k : NodeId) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  lookupNode allNid (EvalSt.nodes st) ≡ mns →
  let r = innerFinish g op allNid inst κ id now vals sched st mns
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

innerReact-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (k : NodeId) (g : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

takeDispatch-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (k : NodeId) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  lookupNode nid (EvalSt.nodes st) ≡ mns →
  let r = takeDispatch {t = t} {e = e} nid vals fin sched st mns
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

switchKill-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (k : NodeId) (mv : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  let r = switchKill {t = t} {e = e} mv sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

stepFrame-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (k : NodeId) (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  let r = stepFrame g id now f κ vals fin sched st
  in QDead k sched st (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))

pushBurst-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (k : NodeId) (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (ems : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  let r = pushBurst g id now f κ ems sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

subscribeAll-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : NodeId) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeAll g op ns b κ id now sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (k : NodeId) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = sharedConnect g i d κ id now sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedSlot-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (k : NodeId) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

sharedConnect-core-qd : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (k : NodeId) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      r   = subscribeE g d (share-sink i) id now sched st₁
  in QDead k sched st (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

------------------------------------------------------------------
-- THE PURE LEAVES
------------------------------------------------------------------

switchKill-qd k nothing  sched st = qdead-refl
switchKill-qd k (just v) sched st = qdead-refl

takeDispatch-qd k nid vals fin sched st (just (take-st kk)) leq
  with proj₂ (proj₂ (takeVals kk vals))
... | true  = qdead ≤-refl (λ h e →
                qd-set k nid (take-st zero) (EvalSt.nodes st)
                  (λ ne _ → qd-clash k nid (take-st kk) (EvalSt.nodes st)
                              leq (λ x → x) ne e) e)
... | false = qdead ≤-refl (λ h e →
                qd-set k nid (take-st (proj₁ (proj₂ (takeVals kk vals))))
                  (EvalSt.nodes st)
                  (λ ne _ → qd-clash k nid (take-st kk) (EvalSt.nodes st)
                              leq (λ x → x) ne e) e)
takeDispatch-qd k nid vals fin sched st nothing                      leq = qdead-refl
takeDispatch-qd k nid vals fin sched st (just (scan-st _))           leq = qdead-refl
takeDispatch-qd k nid vals fin sched st (just (mergeAll-st _ _ _ _)) leq = qdead-refl
takeDispatch-qd k nid vals fin sched st (just (switch-st _ _))       leq = qdead-refl
takeDispatch-qd k nid vals fin sched st (just (exhaust-st _ _))      leq = qdead-refl

thruWrap-qd k op nid false vs bs sched st = qdead-refl
thruWrap-qd k mergeAllᵒ nid true vs bs sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (mergeAll-st lim act q _) =
      qdead ≤-refl (λ h e →
        qd-set k nid (mergeAll-st lim act q true) (EvalSt.nodes st)
          (λ ne _ → qd-same lim act act q _ true
                      (qd-at k nid (mergeAll-st lim act q _)
                         (EvalSt.nodes st) leq ne e)) e)
... | just (scan-st _)       = qdead-refl
... | just (take-st _)       = qdead-refl
... | just (switch-st _ _)   = qdead-refl
... | just (exhaust-st _ _)  = qdead-refl
... | nothing                = qdead-refl
thruWrap-qd k switchᵒ nid true vs bs sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (switch-st cur od) =
      qdead ≤-refl (λ h e →
        qd-set k nid (switch-st cur true) (EvalSt.nodes st)
          (λ ne _ → qd-clash k nid (switch-st cur od) (EvalSt.nodes st)
                      leq (λ x → x) ne e) e)
... | just (scan-st _)           = qdead-refl
... | just (take-st _)           = qdead-refl
... | just (mergeAll-st _ _ _ _) = qdead-refl
... | just (exhaust-st _ _)      = qdead-refl
... | nothing                    = qdead-refl
thruWrap-qd k exhaustᵒ nid true vs bs sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (exhaust-st act od) =
      qdead ≤-refl (λ h e →
        qd-set k nid (exhaust-st act true) (EvalSt.nodes st)
          (λ ne _ → qd-clash k nid (exhaust-st act od) (EvalSt.nodes st)
                      leq (λ x → x) ne e) e)
... | just (scan-st _)           = qdead-refl
... | just (take-st _)           = qdead-refl
... | just (mergeAll-st _ _ _ _) = qdead-refl
... | just (switch-st _ _)       = qdead-refl
... | nothing                    = qdead-refl

------------------------------------------------------------------
-- THE RECURSIVE MEMBERS
------------------------------------------------------------------

subscribeInner-qd k g0 op allNid κ id now o sched st =
  qdead (n≤1+n _) (λ _ e → e)
subscribeInner-qd k (gs fuel) op allNid κ id now o sched st =
  qdead (≤-trans (n≤1+n _) (nxMono SE))
        (λ h e → keep SE (≤-trans h (n≤1+n _)) e)
  where
  SE = subscribeE-qd k fuel o
         (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
         (record sched { nextNode = suc (Sched.nextNode sched) }) st

thruConsume-qd {u = u} k g mergeAllᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (mergeAll-st {v} lim act q od) with v ≟ᵗ u
...   | no _     = qdead-refl
...   | yes refl with hasRoom lim act in hr
...     | false  =
          qdead ≤-refl (λ h e →
            qd-set k nid (mergeAll-st lim act (q ++ o ∷ []) od) (EvalSt.nodes st)
              (λ ne _ → qd-append lim act q o od hr
                          (qd-at k nid (mergeAll-st lim act q od)
                             (EvalSt.nodes st) leq ne e)) e)
...     | true   =
          qdead-trans (subscribeInner-qd k g mergeAllᵒ nid κ id now o sched st)
            (qdead ≤-refl (λ h e →
              qd-bump k nid
                (proj₁ (proj₂ (proj₂ (proj₂ SI))))
                (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))) e))
          where SI = subscribeInner g mergeAllᵒ nid κ id now o sched st
thruConsume-qd k g mergeAllᵒ nid κ id now o sched st | nothing = qdead-refl
thruConsume-qd k g mergeAllᵒ nid κ id now o sched st | just (scan-st _) = qdead-refl
thruConsume-qd k g mergeAllᵒ nid κ id now o sched st | just (take-st _) = qdead-refl
thruConsume-qd k g mergeAllᵒ nid κ id now o sched st | just (switch-st _ _) = qdead-refl
thruConsume-qd k g mergeAllᵒ nid κ id now o sched st | just (exhaust-st _ _) = qdead-refl
thruConsume-qd k g switchᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (switch-st cur od) =
      qdead (nxMono P) (λ h e →
        qd-set k nid
          (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ SI)))
                      then nothing else just (proj₁ SI)) od)
          (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
          (λ ne _ → qd-clash k nid (switch-st cur od) (EvalSt.nodes st)
                      leq (λ x → x) ne e)
          (keep P h e))
      where
      SK = switchKill cur sched st
      SI = subscribeInner g switchᵒ nid κ id now o (proj₁ (proj₂ SK)) (proj₂ (proj₂ SK))
      P  = qdead-trans (switchKill-qd k cur sched st)
             (subscribeInner-qd k g switchᵒ nid κ id now o
                (proj₁ (proj₂ SK)) (proj₂ (proj₂ SK)))
... | just (scan-st _)           = qdead-refl
... | just (take-st _)           = qdead-refl
... | just (mergeAll-st _ _ _ _) = qdead-refl
... | just (exhaust-st _ _)      = qdead-refl
... | nothing                    = qdead-refl
thruConsume-qd k g exhaustᵒ nid κ id now o sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (exhaust-st true od)  = qdead-refl
... | just (exhaust-st false od) =
      qdead (nxMono P) (λ h e →
        qd-set k nid (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ SI))))) od)
          (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
          (λ ne _ → qd-clash k nid (exhaust-st false od) (EvalSt.nodes st)
                      leq (λ x → x) ne e)
          (keep P h e))
      where
      SI = subscribeInner g exhaustᵒ nid κ id now o sched st
      P  = subscribeInner-qd k g exhaustᵒ nid κ id now o sched st
... | just (scan-st _)           = qdead-refl
... | just (take-st _)           = qdead-refl
... | just (mergeAll-st _ _ _ _) = qdead-refl
... | just (switch-st _ _)       = qdead-refl
... | nothing                    = qdead-refl

thruWalk-qd k g op nid κ id now [] sched st = qdead-refl
thruWalk-qd k g op nid κ id now (o ∷ os) sched st =
  qdead-trans TC
    (thruWalk-qd k g op nid κ id now os
      (proj₁ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st))))
      (proj₂ (proj₂ (proj₂ (thruConsume g op nid κ id now o sched st)))))
  where TC = thruConsume-qd k g op nid κ id now o sched st

mergeAllDrain-qd k g allNid κ id now lim act [] sched st = qdead-refl
mergeAllDrain-qd k g allNid κ id now lim act (o ∷ q) sched st
  with hasRoom lim act
... | false = qdead-refl
... | true  =
      qdead-trans SI
        (mergeAllDrain-qd k g allNid κ id now lim
          (if proj₁ (proj₂ (proj₂ (proj₂
             (subscribeInner g mergeAllᵒ allNid κ id now o sched st))))
           then act else suc act) q
          (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g mergeAllᵒ allNid κ id now o sched st))))))
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
            (subscribeInner g mergeAllᵒ allNid κ id now o sched st)))))))
      where SI = subscribeInner-qd k g mergeAllᵒ allNid κ id now o sched st

innerFinish-qd {s = s} k g mergeAllᵒ allNid inst κ id now vals sched st
               (just (mergeAll-st {v} lim act q od)) leq with v ≟ᵗ s
... | yes refl =
      qdead (nxMono DRq) (λ h e →
        qd-set k allNid
          (mergeAll-st lim (proj₁ (proj₂ (proj₂ DR)))
                           (proj₁ (proj₂ (proj₂ (proj₂ DR)))) od)
          (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR))))))
          (λ ne _ → qd-drain g allNid κ id now lim act q od sched st
                      (qd-at k allNid (mergeAll-st lim act q od)
                         (EvalSt.nodes st) leq ne e))
          (keep DRq h e))
      where
      DR  = mergeAllDrain g allNid κ id now lim (pred act) q sched st
      DRq = mergeAllDrain-qd k g allNid κ id now lim (pred act) q sched st
... | no _ = qdead-refl
innerFinish-qd k g mergeAllᵒ allNid inst κ id now vals sched st nothing leq = qdead-refl
innerFinish-qd k g mergeAllᵒ allNid inst κ id now vals sched st (just (scan-st _)) leq = qdead-refl
innerFinish-qd k g mergeAllᵒ allNid inst κ id now vals sched st (just (take-st _)) leq = qdead-refl
innerFinish-qd k g mergeAllᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) leq = qdead-refl
innerFinish-qd k g mergeAllᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st
               (just (switch-st (just c) od)) leq with c ≡ᵇ inst
... | true  = qdead ≤-refl (λ h e →
                qd-set k allNid (switch-st nothing od) (EvalSt.nodes st)
                  (λ ne _ → qd-clash k allNid (switch-st (just c) od)
                              (EvalSt.nodes st) leq (λ x → x) ne e) e)
... | false = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st (just (switch-st nothing od)) leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st nothing leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st (just (scan-st _)) leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st (just (take-st _)) leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st (just (mergeAll-st _ _ _ _)) leq = qdead-refl
innerFinish-qd k g switchᵒ allNid inst κ id now vals sched st (just (exhaust-st _ _)) leq = qdead-refl
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st
               (just (exhaust-st act od)) leq =
  qdead ≤-refl (λ h e →
    qd-set k allNid (exhaust-st false od) (EvalSt.nodes st)
      (λ ne _ → qd-clash k allNid (exhaust-st act od) (EvalSt.nodes st)
                  leq (λ x → x) ne e) e)
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st nothing leq = qdead-refl
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st (just (scan-st _)) leq = qdead-refl
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st (just (take-st _)) leq = qdead-refl
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st (just (mergeAll-st _ _ _ _)) leq = qdead-refl
innerFinish-qd k g exhaustᵒ allNid inst κ id now vals sched st (just (switch-st _ _)) leq = qdead-refl

innerReact-qd k g op allNid inst κ id now vals sched st false = qdead-refl
innerReact-qd k g op allNid inst κ id now vals sched st true
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = qdead-refl
... | false = innerFinish-qd k g op allNid inst κ id now vals sched st
                (lookupNode allNid (EvalSt.nodes st)) refl

stepFrame-qd k g id now (map-f fn) κ vals fin sched st = qdead-refl
stepFrame-qd {u = u} k g id now (scan-f fn nid) κ vals fin sched st
  with lookupNode nid (EvalSt.nodes st) in leq
... | just (scan-st {v} sacc) with v ≟ᵗ u
...   | yes refl = qdead ≤-refl (λ h e →
                     qd-set k nid (scan-st (proj₂ (scanVals fn sacc vals)))
                       (EvalSt.nodes st)
                       (λ ne _ → qd-clash k nid (scan-st sacc) (EvalSt.nodes st)
                                   leq (λ x → x) ne e) e)
...   | no _     = qdead-refl
stepFrame-qd k g id now (scan-f fn nid) κ vals fin sched st | nothing = qdead-refl
stepFrame-qd k g id now (scan-f fn nid) κ vals fin sched st | just (take-st _) = qdead-refl
stepFrame-qd k g id now (scan-f fn nid) κ vals fin sched st | just (mergeAll-st _ _ _ _) = qdead-refl
stepFrame-qd k g id now (scan-f fn nid) κ vals fin sched st | just (switch-st _ _) = qdead-refl
stepFrame-qd k g id now (scan-f fn nid) κ vals fin sched st | just (exhaust-st _ _) = qdead-refl
stepFrame-qd k g id now (take-f nid) κ vals fin sched st =
  takeDispatch-qd k nid vals fin sched st (lookupNode nid (EvalSt.nodes st)) refl
stepFrame-qd k g id now (from-inner op allNid inst) κ vals fin sched st =
  innerReact-qd k g op allNid inst κ id now vals sched st fin
stepFrame-qd k g id now (thru-outer op nid) κ vals fin sched st =
  qdead-trans (thruWalk-qd k g op nid κ id now vals sched st)
    (thruWrap-qd k op nid fin
      (proj₁ TW) (proj₁ (proj₂ TW))
      (proj₁ (proj₂ (proj₂ TW))) (proj₂ (proj₂ (proj₂ TW))))
  where TW = thruWalk g op nid κ id now vals sched st

pushBurst-qd k g id now f κ [] sched st = qdead-refl
pushBurst-qd k g id now f κ (em ∷ ems) sched st =
  qdead-trans SFq
    (pushBurst-qd k g id now f κ ems
       (proj₁ (proj₂ (proj₂ (proj₂ SF))))
       (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  where
  sp  = splitEvents (InstEmit.events em)
  SF  = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  SFq = stepFrame-qd k g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

subscribeAll-qd k g op ns b κ id now sched st =
  qdead (≤-trans (n≤1+n _) (≤-trans (nxMono SEq) (nxMono PBq)))
        (λ h e →
          keep PBq (≤-trans (≤-trans h (n≤1+n _)) (nxMono SEq))
            (keep SEq (≤-trans h (n≤1+n _))
              (qd-mint k (Sched.nextNode sched) (Sched.nextNode sched) ns
                 (EvalSt.nodes st) ≤-refl h e)))
  where
  SE  = subscribeE g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) ns st)
  SEq = subscribeE-qd k g b (thru-outer op (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) ns st)
  PBq = pushBurst-qd k g id now (thru-outer op (Sched.nextNode sched)) κ
          (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))

sharedConnect-core-qd k fuel i d κ id now sched st =
  subscribeE-qd k fuel d (share-sink i) id now sched
    (register (toℕ i) κ
      (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))

sharedConnect-qd k g0 i d κ id now sched st = qdead-refl
sharedConnect-qd k (gs fuel) i d κ id now sched st
  with burstCompleted (proj₁ (subscribeE fuel d (share-sink i) id now sched
         (register (toℕ i) κ
           (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))))
... | true  = sharedConnect-core-qd k fuel i d κ id now sched st
... | false = sharedConnect-core-qd k fuel i d κ id now sched st

sharedSlot-qd k g i d κ id now sched st
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  = qdead-refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  = qdead-refl
...   | false = sharedConnect-qd k g i d κ id now sched st

subscribeE-qd {Γ = Γ} k g (input i) κ id now sched st with Sched.slots sched i
... | shared d = sharedSlot-qd k g i d κ id now sched st
... | scripted (hot _) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = qdead-refl
...   | false = qdead-refl
subscribeE-qd k g (input i) κ id now sched st | scripted (cold sync []) = qdead-refl
subscribeE-qd k g (input i) κ id now sched st | scripted (cold sync (x ∷ xs)) = qdead-refl
subscribeE-qd k g (ofᵉ ts)  κ id now sched st = qdead-refl
subscribeE-qd k g emptyᵉ    κ id now sched st = qdead-refl
subscribeE-qd k g (mapᵉ f b) κ id now sched st =
  qdead (≤-trans (nxMono SEq) (nxMono PBq))
        (λ h e → keep PBq (≤-trans h (nxMono SEq)) (keep SEq h e))
  where
  SE  = subscribeE g b (map-f f ↠ κ) id now sched st
  SEq = subscribeE-qd k g b (map-f f ↠ κ) id now sched st
  PBq = pushBurst-qd k g id now (map-f f) κ
          (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
subscribeE-qd k g (takeᵉ count b) κ id now sched st with evalTm count
... | zero  = qdead-refl
... | suc j =
      qdead (≤-trans (n≤1+n _) (≤-trans (nxMono SEq) (nxMono PBq)))
            (λ h e →
              keep PBq (≤-trans (≤-trans h (n≤1+n _)) (nxMono SEq))
                (keep SEq (≤-trans h (n≤1+n _))
                  (qd-mint k (Sched.nextNode sched) (Sched.nextNode sched)
                     (take-st (suc j)) (EvalSt.nodes st) ≤-refl h e)))
      where
      SE  = subscribeE g b (take-f (Sched.nextNode sched) ↠ κ) id now
              (record sched { nextNode = suc (Sched.nextNode sched) })
              (installNode (Sched.nextNode sched) (take-st (suc j)) st)
      SEq = subscribeE-qd k g b (take-f (Sched.nextNode sched) ↠ κ) id now
              (record sched { nextNode = suc (Sched.nextNode sched) })
              (installNode (Sched.nextNode sched) (take-st (suc j)) st)
      PBq = pushBurst-qd k g id now (take-f (Sched.nextNode sched)) κ
              (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
subscribeE-qd k g (scanᵉ f z b) κ id now sched st =
  qdead (≤-trans (n≤1+n _) (≤-trans (nxMono SEq) (nxMono PBq)))
        (λ h e →
          keep PBq (≤-trans (≤-trans h (n≤1+n _)) (nxMono SEq))
            (keep SEq (≤-trans h (n≤1+n _))
              (qd-mint k (Sched.nextNode sched) (Sched.nextNode sched)
                 (scan-st (evalTm z)) (EvalSt.nodes st) ≤-refl h e)))
  where
  SE  = subscribeE g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
  SEq = subscribeE-qd k g b (scan-f f (Sched.nextNode sched) ↠ κ) id now
          (record sched { nextNode = suc (Sched.nextNode sched) })
          (installNode (Sched.nextNode sched) (scan-st (evalTm z)) st)
  PBq = pushBurst-qd k g id now (scan-f f (Sched.nextNode sched)) κ
          (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE))
subscribeE-qd {u = u} k g (mergeAllᵉ lim b) κ id now sched st =
  subscribeAll-qd k g mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b κ id now sched st
subscribeE-qd k g (switchAllᵉ b) κ id now sched st =
  subscribeAll-qd k g switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE-qd k g (exhaustAllᵉ b) κ id now sched st =
  subscribeAll-qd k g exhaustᵒ (exhaust-st false false) b κ id now sched st
subscribeE-qd k g0 (μᵉ body) κ id now sched st = qdead-refl
subscribeE-qd k (gs fuel) (μᵉ body) κ id now sched st =
  subscribeE-qd k fuel (unfoldμ body) κ id now sched st
subscribeE-qd k g (varᵉ ()) κ id now sched st
subscribeE-qd {u = u} k g (deferᵉ body) κ id now sched st =
  qdead (n≤1+n _) (λ h e →
    qd-mint k (Sched.nextNode sched) (Sched.nextNode sched)
      (mergeAll-st {t = u} nothing 0 [] false) (EvalSt.nodes st) ≤-refl h e)
