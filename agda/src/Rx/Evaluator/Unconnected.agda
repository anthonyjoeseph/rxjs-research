------------------------------------------------------------------
-- WHAT THE UNCONNECTED COUNT SURVIVES.
------------------------------------------------------------------

-- THE COUNT IS THE BUILDER'S MEASURE, AND THIS IS THE ONE THING IT
-- OWES.  Every builder obligation is stated under a bound on the store
-- it was handed, so a frame that runs a step and then spends the next
-- obligation has to know the step left the count where it was.  It
-- did: the connected list is written at exactly one site in the whole
-- tree -- a connect, which EXTENDS it -- and the slot telescope is
-- fixed at the start of the run, so every other move leaves both
-- readings alone and the count with them.
--
-- TWO LAYERS, AND ONLY THE FIRST IS FREE.  A STEP is a record update
-- on a field the count cannot read, so its obligation is a case split
-- all of whose arms are `refl`.  A RELATION is what a builder actually
-- holds at the point of spending -- the derivation, not the function
-- that produced it -- so each of the five is an induction over
-- constructors, every arm of which is a step or a smaller derivation.
--
-- AND IT SITS BELOW THE BUILDER BECAUSE NOTHING HERE LOOKS AT A
-- CANDIDATE.  The count is a natural number read off two fields; the
-- bound rides as an inert index.  That is what lets the whole layer be
-- written once, under the levels rather than inside one.
module Rx.Evaluator.Unconnected where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (zero; suc; _≤_; _<_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-reflexive; ≤-refl; ≤-trans)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Exp using (_×ᵗ_; obs; listᵗ; _≟ᵗ_; Ctx; Closed; Val; FnClo)
open import Rx.Prim using (PlainEvent)
open import Data.Vec using (lookup)
open import Rx.Evaluator using (Sched; EvalSt; Path; AllOp; NodeId; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; lookupNode; switchKill; markInnerDone;
  markOuterDone; mergeAllQueue; scanStep; takeStep; cutAt; batchSyncPush; batchSyncFlush;
  shareLatch; shareFinish; isFinᵖ; NodeState; RegId; mergeAllClaim; mergeAllRestore;
  mergeAllPark)
open import Rx.Evaluator.Domain using (emit⇓; close⇓; emits⇓; subscribeE⇓; consume⇓; drainQueue⇓; subscribeAll⇓;
  sharedConnect⇓; subscribeSharedSlot⇓; dispatchShare⇓; shareGo⇓;
  emit-root; emit-sink; emit-map; emit-scan; emit-scan-stuck; emit-take-more; emit-take-last;
  emit-take-spent; emit-batchSync; emit-batchSync-held; emit-from-inner; emit-thru-outer;
  close-root; close-sink; close-map; close-scan; close-take-spent; close-take; close-batchSync;
  close-batchSync-empty; close-inner-absorb; close-inner-done; close-inner-open;
  close-outer-done; close-outer-open; emits-nil; emits-cons; subs-floor; subs-shared;
  subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of; subs-empty;
  subs-take-zero; subs-take-suc; subs-batchSync; subs-batchSync-empty; subs-map; subs-scan;
  subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer; subs-mint;
  consume-merge-sub; consume-merge-park; consume-merge-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; dq-nil; dq-full; dq-run;
  sub-all; connect; slot-spent; slot-join; slot-connect; disp; go-nil; go-cut; go-val; go-fin)
open import Rx.Evaluator.Reducible using (Out; unconnected; unconn-cong; unconn-extend)

-- THE LATCH RUNS BEFORE THE FAN-OUT AND THE SWEEP AFTER IT, WHICH IS
-- WHY BOTH STAY APPLIED.  An end latches the share as completed on the
-- way in, so a chain subscribing to it DURING the fan-out sees a spent
-- slot; the registrations are dropped on the way out, once every chain
-- that was admitted has had its end.
-- THE LATCH IS THE ONE STORE STEP THE COUNT CANNOT READ THROUGH ON
-- ITS OWN, and it is a two-line case split rather than a leaf: the
-- completion arm writes two fields, neither of them the connected
-- list, and the other arm writes nothing at all.  What makes it owed
-- here rather than free is only that the step branches on a value the
-- caller has not forced.
unconn-latch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
               (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e)
             → unconnected sched st ≤ m
             → unconnected sched (shareLatch i b st) ≤ m
unconn-latch i false sched st le = le
unconn-latch i true  sched st le = le

-- WHAT A NODE STEP OWES THE COUNT, AND IT IS THE SAME PROOF IN EVERY
-- ARM.  Each of these hands back either the store it was given or a
-- record update on a field the count does not read, so the whole
-- obligation is a case split all of whose arms are `refl`.  They are
-- split out from the frames below rather than inlined because a frame
-- runs its step under a `with` and so never has the step's own result
-- in a form that reduces.
shares-scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
                → EvalSt.connectedShares (proj₂ (scanStep fn nid v st))
                  ≡ EvalSt.connectedShares st
shares-scanStep {u = u} fn nid v st with lookupNode nid (EvalSt.nodes st)
... | just (cell-st {w} ac) with w ≟ᵗ u
...   | no  _    = refl
...   | yes refl = refl
shares-scanStep fn nid v st | nothing = refl
shares-scanStep fn nid v st | just (take-st _) = refl
shares-scanStep fn nid v st | just (batchSync-st _ _) = refl
shares-scanStep fn nid v st | just (mergeAll-st _ _ _ _) = refl
shares-scanStep fn nid v st | just (switch-st _ _) = refl
shares-scanStep fn nid v st | just (exhaust-st _ _) = refl

shares-takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (nid : NodeId) (st : EvalSt e)
                → EvalSt.connectedShares (proj₂ (takeStep nid st))
                  ≡ EvalSt.connectedShares st
shares-takeStep nid st with lookupNode nid (EvalSt.nodes st)
... | just (take-st (suc k)) = refl
... | just (take-st zero)    = refl
shares-takeStep nid st | nothing = refl
shares-takeStep nid st | just (cell-st _) = refl
shares-takeStep nid st | just (batchSync-st _ _) = refl
shares-takeStep nid st | just (mergeAll-st _ _ _ _) = refl
shares-takeStep nid st | just (switch-st _ _) = refl
shares-takeStep nid st | just (exhaust-st _ _) = refl

shares-batchSyncPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (nid : NodeId) (v : Val Γ s) (st : EvalSt e)
                     → EvalSt.connectedShares (proj₂ (batchSyncPush nid v st))
                       ≡ EvalSt.connectedShares st
shares-batchSyncPush {s = s} nid v st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} true buf) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-batchSyncPush nid v st | just (batchSync-st false buf) = refl
shares-batchSyncPush nid v st | nothing = refl
shares-batchSyncPush nid v st | just (cell-st _) = refl
shares-batchSyncPush nid v st | just (take-st _) = refl
shares-batchSyncPush nid v st | just (mergeAll-st _ _ _ _) = refl
shares-batchSyncPush nid v st | just (switch-st _ _) = refl
shares-batchSyncPush nid v st | just (exhaust-st _ _) = refl

shares-batchSyncFlush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                        (nid : NodeId) (st : EvalSt e)
                      → EvalSt.connectedShares (proj₂ (batchSyncFlush {s = s} nid st))
                        ≡ EvalSt.connectedShares st
shares-batchSyncFlush {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} _ buf) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-batchSyncFlush nid st | nothing = refl
shares-batchSyncFlush nid st | just (cell-st _) = refl
shares-batchSyncFlush nid st | just (take-st _) = refl
shares-batchSyncFlush nid st | just (mergeAll-st _ _ _ _) = refl
shares-batchSyncFlush nid st | just (switch-st _ _) = refl
shares-batchSyncFlush nid st | just (exhaust-st _ _) = refl

shares-markInnerDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                       (op : AllOp) (nid inst : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (markInnerDone op nid inst st)
                       ≡ EvalSt.connectedShares st
shares-markInnerDone mergeAllᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) = refl
shares-markInnerDone mergeAllᵒ nid inst st | nothing = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (switch-st _ _) = refl
shares-markInnerDone mergeAllᵒ nid inst st | just (exhaust-st _ _) = refl
shares-markInnerDone switchᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st (just c) od) with c ≡ᵇ inst
...   | true  = refl
...   | false = refl
shares-markInnerDone switchᵒ nid inst st | just (switch-st nothing od) = refl
shares-markInnerDone switchᵒ nid inst st | nothing = refl
shares-markInnerDone switchᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone switchᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone switchᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone switchᵒ nid inst st | just (mergeAll-st _ _ _ _) = refl
shares-markInnerDone switchᵒ nid inst st | just (exhaust-st _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st ia od) = refl
shares-markInnerDone exhaustᵒ nid inst st | nothing = refl
shares-markInnerDone exhaustᵒ nid inst st | just (cell-st _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (take-st _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (batchSync-st _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (mergeAll-st _ _ _ _) = refl
shares-markInnerDone exhaustᵒ nid inst st | just (switch-st _ _) = refl

shares-mergeAllQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                       (nid : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (proj₂ (mergeAllQueue {s = s} nid st))
                       ≡ EvalSt.connectedShares st
shares-mergeAllQueue {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-mergeAllQueue nid st | nothing = refl
shares-mergeAllQueue nid st | just (cell-st _) = refl
shares-mergeAllQueue nid st | just (take-st _) = refl
shares-mergeAllQueue nid st | just (batchSync-st _ _) = refl
shares-mergeAllQueue nid st | just (switch-st _ _) = refl
shares-mergeAllQueue nid st | just (exhaust-st _ _) = refl

-- THE COUNT, CARRIED ACROSS A STEP THAT LEFT THE CONNECTED LIST ALONE.
unconn-shares : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                (sched : Sched Γ) (st st′ : EvalSt e)
              → EvalSt.connectedShares st′ ≡ EvalSt.connectedShares st
              → unconnected sched st ≤ m → unconnected sched st′ ≤ m
unconn-shares sched st st′ p le =
  ≤-trans (≤-reflexive (unconn-cong sched {st = st} {st′ = st′} p)) le

-- AND THE SIX A FRAME ACTUALLY SPENDS, each reading its step's result
-- back off the equation the frame's own `with` recorded.
unconn-scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u m}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId) (v : Val Γ s)
                  (sched : Sched Γ) (st : EvalSt e)
                  {ac : Maybe (Val Γ u)} {st₁ : EvalSt e}
                → scanStep fn nid v st ≡ (ac , st₁)
                → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-scanStep fn nid v sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-scanStep fn nid v st))

unconn-takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                  (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                  {b : Maybe Bool} {st₁ : EvalSt e}
                → takeStep nid st ≡ (b , st₁)
                → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-takeStep nid sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-takeStep nid st))

unconn-cutAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
               (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
             → unconnected sched st ≤ m
             → unconnected (proj₁ (cutAt nid sched st)) (proj₂ (cutAt nid sched st)) ≤ m
unconn-cutAt nid sched st le = le

unconn-batchSyncPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                       (nid : NodeId) (v : Val Γ s)
                       (sched : Sched Γ) (st : EvalSt e)
                       {g : Maybe (Val Γ (s ×ᵗ listᵗ s))} {st₁ : EvalSt e}
                     → batchSyncPush nid v st ≡ (g , st₁)
                     → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-batchSyncPush nid v sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-batchSyncPush nid v st))

unconn-batchSyncFlush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                        (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                        {g : Maybe (Val Γ (s ×ᵗ listᵗ s))} {st₁ : EvalSt e}
                      → batchSyncFlush {s = s} nid st ≡ (g , st₁)
                      → unconnected sched st ≤ m → unconnected sched st₁ ≤ m
unconn-batchSyncFlush {s = s} nid sched st {st₁ = st₁} eq =
  unconn-shares sched st st₁
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
           (shares-batchSyncFlush {s = s} nid st))

unconn-mergeAllQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s m}
                       (op : AllOp) (nid inst : NodeId)
                       (sched : Sched Γ) (st : EvalSt e)
                       {q : List (Val Γ (obs s))} {st₀ : EvalSt e}
                     → mergeAllQueue {s = s} nid (markInnerDone op nid inst st) ≡ (q , st₀)
                     → unconnected sched st ≤ m → unconnected sched st₀ ≤ m
unconn-mergeAllQueue {s = s} op nid inst sched st {st₀ = st₀} eq =
  unconn-shares sched st st₀
    (trans (cong (λ z → EvalSt.connectedShares (proj₂ z)) (sym eq))
      (trans (shares-mergeAllQueue {s = s} nid (markInnerDone op nid inst st))
             (shares-markInnerDone op nid inst st)))

shares-markOuterDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                       (op : AllOp) (nid : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (markOuterDone op nid st)
                       ≡ EvalSt.connectedShares st
shares-markOuterDone mergeAllᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) = refl
shares-markOuterDone mergeAllᵒ nid st | nothing = refl
shares-markOuterDone mergeAllᵒ nid st | just (cell-st _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (take-st _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (switch-st _ _) = refl
shares-markOuterDone mergeAllᵒ nid st | just (exhaust-st _ _) = refl
shares-markOuterDone switchᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) = refl
shares-markOuterDone switchᵒ nid st | nothing = refl
shares-markOuterDone switchᵒ nid st | just (cell-st _) = refl
shares-markOuterDone switchᵒ nid st | just (take-st _) = refl
shares-markOuterDone switchᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone switchᵒ nid st | just (mergeAll-st _ _ _ _) = refl
shares-markOuterDone switchᵒ nid st | just (exhaust-st _ _) = refl
shares-markOuterDone exhaustᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st ia od) = refl
shares-markOuterDone exhaustᵒ nid st | nothing = refl
shares-markOuterDone exhaustᵒ nid st | just (cell-st _) = refl
shares-markOuterDone exhaustᵒ nid st | just (take-st _) = refl
shares-markOuterDone exhaustᵒ nid st | just (batchSync-st _ _) = refl
shares-markOuterDone exhaustᵒ nid st | just (mergeAll-st _ _ _ _) = refl
shares-markOuterDone exhaustᵒ nid st | just (switch-st _ _) = refl

unconn-markOuterDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                       (op : AllOp) (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                     → unconnected sched st ≤ m
                     → unconnected sched (markOuterDone op nid st) ≤ m
unconn-markOuterDone op nid sched st =
  unconn-shares sched st (markOuterDone op nid st) (shares-markOuterDone op nid st)

-- THE SWITCH'S CUT MOVES BOTH HALVES AT ONCE, so this one is stated
-- over the pair rather than over the store alone.
unconn-switchKill : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                    (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                  → unconnected sched st ≤ m
                  → unconnected (proj₁ (switchKill cur sched st))
                                (proj₂ (switchKill cur sched st)) ≤ m
unconn-switchKill nothing  sched st le = le
unconn-switchKill (just v) sched st le = le

unconn-switchKill-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                       (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e)
                       {sched₁ : Sched Γ} {st₁ : EvalSt e}
                     → switchKill cur sched st ≡ (sched₁ , st₁)
                     → unconnected sched st ≤ m → unconnected sched₁ st₁ ≤ m
unconn-switchKill-eq cur sched st refl le = unconn-switchKill cur sched st le


-- THE THREE LANE MOVES, WHICH ARE THE SAME `refl` SPLIT AS THE NODE
-- STEPS ABOVE.  A claim, a park and a restore each rewrite one node's
-- queue or lane count, so the connected list is untouched in every arm.
shares-mergeAllClaim : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                       (nid : NodeId) (st : EvalSt e)
                     → EvalSt.connectedShares (mergeAllClaim nid st)
                       ≡ EvalSt.connectedShares st
shares-mergeAllClaim nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st _ _ _ _) = refl
shares-mergeAllClaim nid st | nothing = refl
shares-mergeAllClaim nid st | just (cell-st _) = refl
shares-mergeAllClaim nid st | just (take-st _) = refl
shares-mergeAllClaim nid st | just (batchSync-st _ _) = refl
shares-mergeAllClaim nid st | just (switch-st _ _) = refl
shares-mergeAllClaim nid st | just (exhaust-st _ _) = refl

shares-mergeAllRestore : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                         (nid : NodeId) (os : List (Val Γ (obs s))) (st : EvalSt e)
                       → EvalSt.connectedShares (mergeAllRestore nid os st)
                         ≡ EvalSt.connectedShares st
shares-mergeAllRestore {s = s} nid os st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} _ _ _ _) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-mergeAllRestore nid os st | nothing = refl
shares-mergeAllRestore nid os st | just (cell-st _) = refl
shares-mergeAllRestore nid os st | just (take-st _) = refl
shares-mergeAllRestore nid os st | just (batchSync-st _ _) = refl
shares-mergeAllRestore nid os st | just (switch-st _ _) = refl
shares-mergeAllRestore nid os st | just (exhaust-st _ _) = refl

shares-mergeAllPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                      (nid : NodeId) (o : Val Γ (obs s)) (st : EvalSt e)
                    → EvalSt.connectedShares (mergeAllPark nid o st)
                      ≡ EvalSt.connectedShares st
shares-mergeAllPark {s = s} nid o st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} _ _ _ _) with w ≟ᵗ s
...   | no  _    = refl
...   | yes refl = refl
shares-mergeAllPark nid o st | nothing = refl
shares-mergeAllPark nid o st | just (cell-st _) = refl
shares-mergeAllPark nid o st | just (take-st _) = refl
shares-mergeAllPark nid o st | just (batchSync-st _ _) = refl
shares-mergeAllPark nid o st | just (switch-st _ _) = refl
shares-mergeAllPark nid o st | just (exhaust-st _ _) = refl

-- AND THE SWEEP, WHICH MOVES THE SCHEDULE AS WELL AS THE STORE.  It
-- drops a finished share's registrations and the live rows that fed
-- them; the slot telescope and the connected list are the two readings
-- it does not touch, so the count is the same on both sides.
unconn-shareFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                     (i : Fin n) (b : Bool) (r : Out e)
                   → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≤ m
                   → unconnected (proj₁ (proj₂ (shareFinish i b r)))
                                 (proj₂ (proj₂ (shareFinish i b r))) ≤ m
unconn-shareFinish i false r le = le
unconn-shareFinish i true (_ , _ , _) le = le

unconn-cutAt-eq : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {m}
                  (nid : NodeId) (sched : Sched Γ) (st : EvalSt e)
                  {sched₁ : Sched Γ} {st₁ : EvalSt e}
                → cutAt nid sched st ≡ (sched₁ , st₁)
                → unconnected sched st ≤ m → unconnected sched₁ st₁ ≤ m
unconn-cutAt-eq nid sched st refl le = unconn-cutAt nid sched st le

-- ELEVEN, THOUGH THE BUILDER SPENDS ONLY FIVE.  The five it holds
-- recurse through six more -- a flattener's consume, a lane's drain, an
-- `*All` subscribe, a slot's two halves and the share fan-out -- so the
-- induction is over the whole delivery cycle or over none of it.
--
-- EVERY ARM IS ONE OF THREE THINGS, and that is the whole proof.  A
-- store the relation hands back untouched, which is `≤-refl` because a
-- record update on a field the count cannot read reduces away.  A node
-- step, which is one of the equations above.  Or a smaller derivation,
-- composed by transitivity in the order the run took.
--
-- THE CONNECT IS THE ONE ARM THAT MOVES THE COUNT, and it moves it
-- DOWN: the slot it names joins the connected list, so the count is
-- charged for one fewer slot afterwards.  That is `unconn-extend`, the
-- guard-free half of the strict drop the builder's recursion is
-- ordered by -- a derivation ending in a connect is no worse, which is
-- all a `≤` statement needs to say.
mutual
  unconn-emit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {κ : Path Γ lo u t} {now} {v : Val Γ u}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → emit⇓ {e = e} κ now v sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st
  unconn-emit emit-root                = ≤-refl
  unconn-emit (emit-sink d)            = unconn-disp d
  unconn-emit (emit-map d)             = unconn-emit d
  unconn-emit (emit-scan {fn = fn} {nid = nid} {v = v} {sched = sched} {st = st} seq d) =
    ≤-trans (unconn-emit d) (unconn-scanStep fn nid v sched st seq ≤-refl)
  unconn-emit (emit-scan-stuck {fn = fn} {nid = nid} {v = v} {sched = sched} {st = st} seq) =
    unconn-scanStep fn nid v sched st seq ≤-refl
  unconn-emit (emit-take-more {nid = nid} {sched = sched} {st = st} teq d) =
    ≤-trans (unconn-emit d) (unconn-takeStep nid sched st teq ≤-refl)
  unconn-emit (emit-take-last {nid = nid} {sched = sched} {st = st}
                 {sched₁ = sched₁} {st₂ = st₂} teq d ceq c) =
    ≤-trans (unconn-close c)
      (≤-trans (unconn-cutAt-eq nid sched₁ st₂ ceq ≤-refl)
        (≤-trans (unconn-emit d) (unconn-takeStep nid sched st teq ≤-refl)))
  unconn-emit (emit-take-spent {nid = nid} {sched = sched} {st = st} teq) =
    unconn-takeStep nid sched st teq ≤-refl
  unconn-emit (emit-batchSync {nid = nid} {v = v} {sched = sched} {st = st} peq d) =
    ≤-trans (unconn-emit d) (unconn-batchSyncPush nid v sched st peq ≤-refl)
  unconn-emit (emit-batchSync-held {nid = nid} {v = v} {sched = sched} {st = st} peq) =
    unconn-batchSyncPush nid v sched st peq ≤-refl
  unconn-emit (emit-from-inner d)      = unconn-emit d
  unconn-emit (emit-thru-outer d)      = unconn-consume d

  unconn-close : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → close⇓ {e = e} κ now sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st
  unconn-close close-root              = ≤-refl
  unconn-close (close-sink d)          = unconn-disp d
  unconn-close (close-map d)           = unconn-close d
  unconn-close (close-scan d)          = unconn-close d
  unconn-close (close-take-spent _)    = ≤-refl
  unconn-close (close-take _ d)        = unconn-close d
  unconn-close (close-batchSync {nid = nid} {sched = sched} {st = st} fq d c) =
    ≤-trans (unconn-close c)
      (≤-trans (unconn-emit d) (unconn-batchSyncFlush nid sched st fq ≤-refl))
  unconn-close (close-batchSync-empty {nid = nid} {sched = sched} {st = st} fq d) =
    ≤-trans (unconn-close d) (unconn-batchSyncFlush nid sched st fq ≤-refl)
  unconn-close (close-inner-absorb _)  = ≤-refl
  unconn-close (close-inner-done {op = op} {allNid = allNid} {inst = inst}
                  {sched = sched} {st = st} _ qeq dd _ c) =
    ≤-trans (unconn-close c)
      (≤-trans (unconn-drain dd)
        (unconn-mergeAllQueue op allNid inst sched st qeq ≤-refl))
  unconn-close (close-inner-open {op = op} {allNid = allNid} {inst = inst}
                  {sched = sched} {st = st} _ qeq dd _) =
    ≤-trans (unconn-drain dd)
      (unconn-mergeAllQueue op allNid inst sched st qeq ≤-refl)
  unconn-close (close-outer-done {op = op} {nid = nid} {sched = sched} {st = st} _ c) =
    ≤-trans (unconn-close c) (unconn-markOuterDone op nid sched st ≤-refl)
  unconn-close (close-outer-open {op = op} {nid = nid} {sched = sched} {st = st} _) =
    unconn-markOuterDone op nid sched st ≤-refl

  unconn-emits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {κ : Path Γ lo u t} {now} {vs : List (Val Γ u)}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → emits⇓ {e = e} κ now vs sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st
  unconn-emits emits-nil         = ≤-refl
  unconn-emits (emits-cons d ds) = ≤-trans (unconn-emits ds) (unconn-emit d)

  unconn-subs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                  {b : Val Γ (obs u)} {κ : Path Γ lo u t} {now}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → subscribeE⇓ {e = e} b κ now sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st
  unconn-subs (subs-floor _ c)          = unconn-close c
  unconn-subs (subs-shared _ ss)        = unconn-sslot ss
  unconn-subs (subs-hot-done _ _ _ c)   = unconn-close c
  unconn-subs (subs-hot-live _ _ _ _)   = ≤-refl
  unconn-subs (subs-cold-sync _ _ es c) = ≤-trans (unconn-close c) (unconn-emits es)
  unconn-subs (subs-cold-async _ _ _ _ _ es) = unconn-emits es
  unconn-subs (subs-of es c)            = ≤-trans (unconn-close c) (unconn-emits es)
  unconn-subs (subs-empty c)            = unconn-close c
  unconn-subs (subs-take-zero _ c)      = unconn-close c
  unconn-subs (subs-take-suc _ _ d)     = unconn-subs d
  unconn-subs (subs-batchSync {nid = nid} {sched₁ = sched₁} {st₁ = st₁} _ d fq em) =
    ≤-trans (unconn-emit em)
      (≤-trans (unconn-batchSyncFlush nid sched₁ st₁ fq ≤-refl) (unconn-subs d))
  unconn-subs (subs-batchSync-empty {nid = nid} {sched₁ = sched₁} {st₁ = st₁} _ d fq) =
    ≤-trans (unconn-batchSyncFlush nid sched₁ st₁ fq ≤-refl) (unconn-subs d)
  unconn-subs (subs-map d)              = unconn-subs d
  unconn-subs (subs-scan _ d)           = unconn-subs d
  unconn-subs (subs-merge-all d)        = unconn-suball d
  unconn-subs (subs-switch-all d)       = unconn-suball d
  unconn-subs (subs-exhaust-all d)      = unconn-suball d
  unconn-subs (subs-μ d)                = unconn-subs d
  unconn-subs (subs-defer _ _ _ _)      = ≤-refl
  unconn-subs (subs-mint _ d)           = unconn-subs d

  unconn-consume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                     {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {now}
                     {o : Val Γ (obs u)}
                     {sched : Sched Γ} {st : EvalSt e} {r : Out e}
                 → consume⇓ {e = e} op nid κ now o sched st r
                 → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                     ≤ unconnected sched st
  unconn-consume (consume-merge-sub _ _ _ d)  = unconn-subs d
  unconn-consume (consume-merge-park {nid = nid} {o = o} {sched = sched} {st = st} _ _) =
    unconn-shares sched st (mergeAllPark nid o st) (shares-mergeAllPark nid o st) ≤-refl
  unconn-consume (consume-merge-nil _)        = ≤-refl
  unconn-consume (consume-switch-sub {sched = sched} {st = st} {cur = cur} _ keq _ d) =
    ≤-trans (unconn-subs d) (unconn-switchKill-eq cur sched st keq ≤-refl)
  unconn-consume (consume-switch-nil _)       = ≤-refl
  unconn-consume (consume-exhaust-sub _ _ d)  = unconn-subs d
  unconn-consume (consume-exhaust-nil _)      = ≤-refl

  unconn-drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                   {op : AllOp} {nid : NodeId} {κ : Path Γ lo u t} {now}
                   {q : List (Val Γ (obs u))}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → drainQueue⇓ {e = e} op nid κ now q sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st
  unconn-drain dq-nil = ≤-refl
  unconn-drain (dq-full {nid = nid} {sched = sched} {st = st} {o = o} {q = q} _) =
    unconn-shares sched st (mergeAllRestore nid (o ∷ q) st)
      (shares-mergeAllRestore nid (o ∷ q) st) ≤-refl
  unconn-drain (dq-run {nid = nid} {sched = sched} {st = st} _ _ d dd) =
    ≤-trans (unconn-drain dd)
      (≤-trans (unconn-subs d)
        (unconn-shares sched st (mergeAllClaim nid st)
          (shares-mergeAllClaim nid st) ≤-refl))

  unconn-suball : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
                    {op : AllOp} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
                    {κ : Path Γ lo u t} {now}
                    {sched : Sched Γ} {st : EvalSt e} {r : Out e}
                → subscribeAll⇓ {e = e} op ns b κ now sched st r
                → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                    ≤ unconnected sched st
  unconn-suball (sub-all _ d) = unconn-subs d

  unconn-sconnect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                      {i : Fin n} {d : Closed Γ (lookup Γ i)}
                      {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo} {now}
                      {sched : Sched Γ} {st : EvalSt e} {r : Out e}
                  → sharedConnect⇓ {e = e} i d κ below now sched st r
                  → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                      ≤ unconnected sched st
  unconn-sconnect (connect {i = i} {sched = sched} {st = st} _ d) =
    ≤-trans (unconn-subs d)
      (unconn-extend (Sched.slots sched) (toℕ i) (EvalSt.connectedShares st))

  unconn-sslot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                   {i : Fin n} {d : Closed Γ (lookup Γ i)}
                   {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo} {now}
                   {sched : Sched Γ} {st : EvalSt e} {r : Out e}
               → subscribeSharedSlot⇓ {e = e} i d κ below now sched st r
               → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                   ≤ unconnected sched st
  unconn-sslot (slot-spent _ c)      = unconn-close c
  unconn-sslot (slot-join _ _ _)     = ≤-refl
  unconn-sslot (slot-connect _ _ cd) = unconn-sconnect cd

  unconn-disp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                  {now} {i : Fin n} {below : lo ≤ toℕ i}
                  {ev : PlainEvent (Val Γ (lookup Γ i))}
                  {sched : Sched Γ} {st : EvalSt e} {r : Out e}
              → dispatchShare⇓ {e = e} now i below ev sched st r
              → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  ≤ unconnected sched st
  unconn-disp (disp {i = i} {ev = ev} {sched = sched} {st = st} g) =
    unconn-shareFinish i (isFinᵖ ev) _
      (≤-trans (unconn-go g) (unconn-latch i (isFinᵖ ev) sched st ≤-refl))

  unconn-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
                {now} {i : Fin n} {ev : PlainEvent (Val Γ (lookup Γ i))}
                {ps : List (RegId × Path Γ lo (lookup Γ i) t)}
                {sched : Sched Γ} {st : EvalSt e} {r : Out e}
            → shareGo⇓ {e = e} now i ev ps sched st r
            → unconnected (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                ≤ unconnected sched st
  unconn-go go-nil            = ≤-refl
  unconn-go (go-cut _ g)      = unconn-go g
  unconn-go (go-val _ d g)    = ≤-trans (unconn-go g) (unconn-emit d)
  unconn-go (go-fin _ c g)    = ≤-trans (unconn-go g) (unconn-close c)
