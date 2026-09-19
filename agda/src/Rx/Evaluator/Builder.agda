------------------------------------------------------------------
-- THE BUILDER: THE RUN, CONSTRUCTED RATHER THAN TESTED.
------------------------------------------------------------------

-- WHAT A BUILDER IS.  Every family in `Rx.Evaluator.Domain` is a graph
-- relation, so a member of it is a complete run; this module inhabits
-- them.  The result is not fixed by a machine -- the builder RETURNS
-- the pair, so it CHOOSES which clause ran, and a clause it does not
-- write is a run that does not exist.  That is why no arm here tests a
-- rank and no arm answers a negative case: there is no negative case to
-- answer.
--
-- SO THE EVALUATOR IS A PROJECTION.  `evaluate↓` is `proj₁` of
-- `evaluate!`, and a projection computes only as far as the thing
-- projected is a real body -- so while a leaf below is a postulate a
-- run typechecks and does not reduce, which is why the bug cache is a
-- target to type rather than one the gate types for you.
--
-- WHY IT SITS BELOW THE PROOF THAT CONSUMES IT.  Its cone is
-- `Rx.Evaluator`, `Rx.Evaluator.Domain` and `Rx.Evaluator.Reducible`,
-- all of which check in seconds, so the dev loop stays a loop while
-- this is being written.

-- HOW THE MODULE LAYERS, AND WHY IT IS NOT ONE MUTUAL BLOCK.  A path
-- builder for an EXTENDED path is constructed here from the `Handles`
-- its caller was handed -- never by walking the path again -- so the
-- frame helpers bottom out in their argument and mention no recursion
-- at all.  Two edges genuinely close a cycle and each is cut by a leaf:
-- a lane drain subscribes under a frame whose own closing side drains,
-- and a share connect spends the walk at the floor above its slot.
-- With those two cut the rest is a straight line -- frame helpers, the
-- share fan-out, then the term face with itself, then the fundamental
-- theorem at values, then the general path walk, then the arrival
-- spine.
module Rx.Evaluator.Builder where

open import Data.Bool using (Bool; true; false; T; _∧_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _+_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-reflexive; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<; ∸-monoʳ-<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Rx.Prim using (Fuel; Tick; hot; cold; PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; obs; listᵗ; _≟ᵗ_;
  Ctx; Closed; Val; Exp; Tm; Fn; FnClo; Env; []ᵉ; _∷ᵉ_; evalWith; unfoldμ;
  input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
  nilᵗ; consᵗ; foldᵗ; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ; ib-topᵗ)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; ordinalᵏ; freshId; setAt)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId; NodeState; root; share-sink; _↠_; map-f; scan-f;
  take-f; batchSync-f; from-inner; thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; installNode; lookupNode; setNode; hasRoom;
  consumeUsable; switchKill; aliveThroughᶠ; markInnerDone; markOuterDone; allFinished;
  mergeAllQueue; scanStep; takeStep; takeSpent; cutAt; batchSyncPush; batchSyncFlush;
  memberSource; register; atSlot; atDyn; lowerFloor; resolve; Arrival; AtFloor; RegId; arrTick;
  arrTy; arrVal; chainsOf; cascadeLatch; sched-next; sched-init; st-init;
  shareAdmit; shareLatch; isFinᵖ)
open import Rx.Evaluator.Domain using (emits⇓; subscribeE⇓; consume⇓; drainQueue⇓; subscribeAll⇓; chainStep⇓; cascadeGo⇓; cascade⇓;
  drain⇓; evaluate⇓; emit-root; emit-map; emit-scan; emit-scan-stuck; emit-take-more;
  emit-take-last; emit-take-spent; emit-batchSync; emit-batchSync-held; emit-from-inner;
  emit-thru-outer; close-root; close-map; close-scan; close-take-spent; close-take;
  close-batchSync; close-batchSync-empty; close-inner-absorb; close-inner-done;
  close-inner-open; close-outer-done; close-outer-open; emits-nil; emits-cons; subs-floor;
  subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync; subs-cold-async; subs-of;
  subs-empty; subs-take-zero; subs-take-suc; subs-batchSync; subs-batchSync-empty; subs-map;
  subs-scan; subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer; subs-mint;
  consume-merge-sub; consume-merge-park; consume-merge-nil; consume-switch-sub;
  consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil; sub-all; connect; slot-spent;
  slot-join; slot-connect; chain-more; chain-last; casc-nil; casc-cut; casc-live; casc-run;
  drain-done; drain-empty; drain-step; eval-run; dispatchShare⇓; shareGo⇓; disp;
  go-nil; go-cut; go-val; go-fin; emit-sink; close-sink)
open import Rx.Evaluator.Reducible using (Out; Red; Emits; Closes; Handles; RedFn; RedEnv; redDatas; redLookup; redFoldVals;
  unconnected; unconn-cong; unconn-emit; unconn-close; unconn-emits; unconn-subs; unconn-drain;
  unconn-connect; red-scanned; red-pushed; red-flushed)

------------------------------------------------------------------
-- THE TWO LEAVES, AND WHY THEY ARE THE ONLY TWO.
------------------------------------------------------------------

-- A LANE DRAIN AND A SHARE CONNECT ARE THE MODULE'S TWO CYCLES, AND
-- CUTTING THEM HERE IS WHAT MAKES EVERYTHING ELSE A STRAIGHT LINE.
-- Every other block below takes what it needs from the block above it;
-- these two alone want something declared after them.  Each is stated
-- as narrowly as its own cycle allows: the drain leaf is the whole
-- drain, since what it wants back is the fundamental theorem at values,
-- while the share leaf is only the WALK a connect spends -- the fan-out
-- itself, which is what a share actually does, is a body a few lines
-- down over that walk.
--
-- NEITHER HAS BEEN INSTANTIATED.  They are stated at full strength and
-- the probe that would reach them cannot be written until the module
-- they live in typechecks, which is the tier's own first leg.

-- THE PARKED LANE, HANDED BACK ITS QUEUE.  A flattener that could not
-- subscribe when a value arrived kept it; this is the walk that spends
-- the backlog once a lane frees, one carried value at a time.
--
-- DEAD ROUTE: writing it as a body here needs the general path walk,
--   and the walk's own `from-inner` CLOSING side is what runs the drain
--   -- so the direct route does not fail on difficulty, it fails by
--   putting every declaration between the two into one mutual block,
--   which is the single shape this module's layering exists to avoid.
postulate
  drainQueue! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo m}
                (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
                (now : Tick) (q : List (Val Γ (obs u)))
              → Handles {m = m} u κ → (sched : Sched Γ) (st : EvalSt e)
              → unconnected sched st ≤ m
              → Σ (Out e) λ r → drainQueue⇓ {e = e} op nid κ now q sched st r

------------------------------------------------------------------
-- THE SHARE'S SINK, WHICH FANS A VALUE OUT -- AND THE ONE LEAF LEFT
-- UNDER IT.
------------------------------------------------------------------

-- A WALK IS WHAT A PATH IS OWED, AND NAMING IT IS WHAT LETS THE FAN-OUT
-- BE A BODY.  The sink does not walk anything itself: it hands each
-- admitted chain to a walk it was GIVEN, so the recursion lives at the
-- caller and this file's share machinery has none.
Walk : ∀ {n} (Γ : Ctx n) (t : Ty) (m lo : ℕ) → Set
Walk Γ t m lo = ∀ {u} (κ : Path Γ lo u t) → Handles {m = m} u κ

-- THE PAYLOAD'S CANDIDATE, WHICH ONLY ONE OF THE TWO EVENTS HAS.  An
-- end carries nothing, so the fan-out's value arm is the only one that
-- owes a candidate and the completion arm asks for `⊤`.
RedEv : ∀ {n} {Γ : Ctx n} (m : ℕ) (u : Ty) → PlainEvent (Val Γ u) → Set
RedEv m u (valueᵖ v) = Red m u v
RedEv m u completeᵖ  = ⊤

-- THE DESCENT THE SINK BUYS ITS CALLER, AND IT IS A FACT ABOUT THE
-- INDEX RATHER THAN A PEELED WITNESS.  `shareAdmit` returns chains at
-- floor `suc (toℕ i)` IN THEIR TYPE, so a chain registered on share `i`
-- can only sink into a share strictly above `i`, and the room left
-- above the floor is what shrinks at every fan-out.
monus-sink : ∀ {n lo} (i : Fin n) → lo ≤ toℕ i → n ∸ suc (toℕ i) < n ∸ lo
monus-sink i below = ∸-monoʳ-< (s≤s below) (toℕ<n i)

-- ONE ADMITTED CHAIN AT A TIME, IN REGISTRATION ORDER, EACH MARKED
-- DELIVERED BEFORE IT RUNS.  A victim cut earlier in this same cascade
-- is skipped rather than delivered to, which is the one thing the list
-- order cannot express and the equation carries instead.
share-go! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo m} (i : Fin n)
            (w : Walk Γ t m lo) (now : Tick)
            (ev : PlainEvent (Val Γ (lookup Γ i))) → RedEv m (lookup Γ i) ev
          → (ps : List (RegId × Path Γ lo (lookup Γ i) t))
          → (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
          → Σ (Out e) λ r → shareGo⇓ {e = e} now i ev ps sched st r
share-go! i w now ev rev []              sched st le = _ , go-nil
share-go! i w now (valueᵖ v) rv ((rid , p) ∷ ps) sched st le
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (r , g) = share-go! i w now (valueᵖ v) rv ps sched st le
              in r , go-cut eqc g
... | false =
      let ((_ , sched₁ , st₁) , f) =
            proj₁ (w p) rv now sched
              (record st { delivered = rid ∷ EvalSt.delivered st }) le
          (_ , g) = share-go! i w now (valueᵖ v) rv ps sched₁ st₁
                      (≤-trans (unconn-emit f) le)
      in _ , go-val eqc f g
share-go! i w now completeᵖ rv ((rid , p) ∷ ps) sched st le
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (r , g) = share-go! i w now completeᵖ rv ps sched st le
              in r , go-cut eqc g
... | false =
      let ((_ , sched₁ , st₁) , f) =
            proj₂ (w p) now sched
              (record st { delivered = rid ∷ EvalSt.delivered st }) le
          (_ , g) = share-go! i w now completeᵖ rv ps sched₁ st₁
                      (≤-trans (unconn-close f) le)
      in _ , go-fin eqc f g

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
                  {ac : Val Γ u} {st₁ : EvalSt e}
                → scanStep fn nid v st ≡ (just ac , st₁)
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

dispatch-share! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo m} (i : Fin n)
                  (below : lo ≤ toℕ i) (w : Walk Γ t m (suc (toℕ i))) (now : Tick)
                  (ev : PlainEvent (Val Γ (lookup Γ i))) → RedEv m (lookup Γ i) ev
                → (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
                → Σ (Out e) λ r → dispatchShare⇓ {e = e} now i below ev sched st r
dispatch-share! i below w now ev rev sched st le =
  let (_ , g) = share-go! i w now ev rev (shareAdmit i (EvalSt.registry st))
                  sched (shareLatch i (isFinᵖ ev) st) (unconn-latch i (isFinᵖ ev) sched st le)
  in _ , disp g

handles-share : ∀ {n} {Γ : Ctx n} {t lo m} (i : Fin n) (below : lo ≤ toℕ i)
              → Walk Γ t m (suc (toℕ i))
              → Handles {Γ = Γ} {t = t} {m = m} (lookup Γ i) (share-sink i below)
handles-share i below w =
    (λ {_} {v} rv now sched st le →
       let (r , d) = dispatch-share! i below w now (valueᵖ v) rv sched st le
       in r , emit-sink d)
  , (λ now sched st le →
       let (r , d) = dispatch-share! i below w now completeᵖ tt sched st le
       in r , close-sink d)

-- THE LEAF THAT REPLACED THE FAN-OUT, AND IT IS A STATEMENT ABOUT
-- DECLARATION ORDER RATHER THAN ABOUT SHARES.  What a connect spends is
-- the general walk at the floor directly above the slot it is
-- connecting; the walk is written at the foot of this module, and it
-- reaches the term face back HERE -- a frame's function is handed to the
-- walk with a fresh accessibility, so nothing around that loop shrinks.
--
-- THE MEASURE IS A COUNT THE STORE CARRIES, AND IT ORDERS THE ROUND
-- TRIP THE FLOOR CANNOT.  What a connect consumes is a share that has
-- not been connected yet -- the arm is guarded by the slot's absence
-- from the connected list and adds it on the way out -- so the number
-- of slots that are shared and unconnected strictly drops across
-- exactly the call that raises the floor measure.  Nothing anywhere
-- puts a slot back, so every other arm leaves that number alone or
-- lowers it.
--
-- AND IT IS A COUNT RATHER THAN AN INVARIANT, WHICH IS WHY THE ROUTE
-- BELOW DOES NOT REACH IT.  That route dies because the candidate
-- cannot be a premise of a statement about the store; a natural number
-- is not the candidate, so the bound rides as an inert index and the
-- type descent is untouched.
--
-- WHAT IS LEFT IS THE KNOT AND NOTHING ELSE.  The connect arm already
-- spends the level below and already refutes the zero one, so this leaf
-- is the walk at a STRICTLY SMALLER bound than its caller's -- which is
-- what a recursion on the bound is allowed to supply.  Tying it needs
-- the module CUT at this line: everything above is level-free, so a
-- level-indexed module can take the walks below it as a parameter and
-- the file that opens it can close the loop by well-founded recursion.
--
-- DEAD ROUTE: merging the term face and the walk into one block puts
--   both recursions under one measure, and the two move in OPPOSITE
--   directions: a connect drops to the floor `toℕ i` its own slot names,
--   while a fan-out only ever rises to `suc (toℕ i)`, so neither `n ∸ lo`
--   nor the input ceiling orders the pair.  What does order it is that a
--   share connects AT MOST ONCE EVER, which is a fact about the store --
--   and `Rx.Evaluator.Reducible`'s own dead route records why a store
--   invariant cannot be a premise of the candidate.
postulate
  walk-above : ∀ {n} {Γ : Ctx n} {t m} (i : Fin n) → Walk Γ t m (suc (toℕ i))

------------------------------------------------------------------
-- SEVERAL VALUES IN ORDER, WHICH IS A SCRIPT'S SYNCHRONOUS PREFIX.
------------------------------------------------------------------

emits! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo m} (κ : Path Γ lo u t)
       → Emits {m = m} u κ → (now : Tick) (vs : List (Val Γ u)) → All (Red m u) vs
       → (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
       → Σ (Out e) λ r → emits⇓ {e = e} κ now vs sched st r
emits! κ em now []       []ᵃ         sched st le = _ , emits-nil
emits! κ em now (v ∷ vs) (rv ∷ᵃ rs)  sched st le =
  let ((out , sched₁ , st₁) , d) = em rv now sched st le
      (r , ds)                   = emits! κ em now vs rs sched₁ st₁
                                     (≤-trans (unconn-emit d) le)
  in _ , emits-cons d ds

------------------------------------------------------------------
-- THE FRAME HELPERS.  Each builds a `Handles` for the path ONE FRAME
-- LONGER out of the `Handles` its caller already holds, which is what
-- keeps the general walk out of them.
------------------------------------------------------------------

handles-root : ∀ {n} {Γ : Ctx n} {t lo m} → Handles {Γ = Γ} {t = t} {lo = lo} {m = m} t root
handles-root = (λ _ _ _ _ _ → _ , emit-root) , (λ _ _ _ _ → _ , close-root)

handles-map : ∀ {n} {Γ : Ctx n} {t s u lo m} (fn : FnClo Γ s u) (κ : Path Γ lo u t)
            → RedFn m fn → Handles {m = m} u κ → Handles {m = m} s (map-f fn ↠ κ)
handles-map fn κ rf (em , cl) =
    (λ rv now sched st le → let (r , d) = em (rf rv) now sched st le in r , emit-map d)
  , (λ now sched st le → let (r , d) = cl now sched st le in r , close-map d)

-- THE FOLD'S STEP HANDS ITS ACCUMULATOR BACK OUT OF THE STORE, so the
-- candidate that travels with the emitted value is the leaf's rather
-- than the arriving value's.
emits-scan : ∀ {n} {Γ : Ctx n} {t s u lo m} (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
             (κ : Path Γ lo u t) → Emits {m = m} u κ → Emits {m = m} s (scan-f fn nid ↠ κ)
emits-scan fn nid κ em {v = v} rv now sched st le with scanStep fn nid v st in seq
... | (nothing , st₁) = _ , emit-scan-stuck seq
... | (just ac , st₁) =
      let (r , d) = em (red-scanned fn nid v st seq) now sched st₁
                      (unconn-scanStep fn nid v sched st seq le)
      in r , emit-scan seq d

handles-scan : ∀ {n} {Γ : Ctx n} {t s u lo m} (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
               (κ : Path Γ lo u t) → Handles {m = m} u κ → Handles {m = m} s (scan-f fn nid ↠ κ)
handles-scan fn nid κ hκ =
    emits-scan fn nid κ (proj₁ hκ)
  , (λ now sched st le → let (r , d) = proj₂ hκ now sched st le in r , close-scan d)

-- THE TRUNCATION SPENDS ITS COUNT ONE VALUE AT A TIME AND CUTS
-- MID-BURST, which is what real `take` does: the last value owed leaves
-- and the completion follows it in the same breath.
emits-take : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId) (κ : Path Γ lo s t)
           → Handles {m = m} s κ → Emits {m = m} s (take-f nid ↠ κ)
emits-take nid κ (em , cl) rv now sched st le with takeStep nid st in teq
... | (nothing , st₁)    = _ , emit-take-spent teq
... | (just false , st₁) =
      let (r , d) = em rv now sched st₁ (unconn-takeStep nid sched st teq le)
      in r , emit-take-more teq d
... | (just true , st₁)  =
      let le₁                        = unconn-takeStep nid sched st teq le
          ((out , sched₁ , st₂) , d) = em rv now sched st₁ le₁
          cut                        = cutAt nid sched₁ st₂
          (r , c)                    = cl now (proj₁ cut) (proj₂ cut)
                                         (unconn-cutAt nid sched₁ st₂
                                           (≤-trans (unconn-emit d) le₁))
      in _ , emit-take-last teq d refl c

closes-take : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId) (κ : Path Γ lo s t)
            → Closes {m = m} κ → Closes {m = m} (take-f nid ↠ κ)
closes-take nid κ cl now sched st le with takeSpent nid st in seq
... | true  = _ , close-take-spent seq
... | false = let (r , d) = cl now sched st le in r , close-take seq d

handles-take : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId) (κ : Path Γ lo s t)
             → Handles {m = m} s κ → Handles {m = m} s (take-f nid ↠ κ)
handles-take nid κ hκ = emits-take nid κ hκ , closes-take nid κ (proj₂ hκ)

-- THE BRACKET.  While the node's bit is up the value is held and
-- nothing leaves; once it is down each value leaves as its own group of
-- one.  Both are the helper's own answer, so neither arm tests
-- anything the store does not already say.
emits-batchSync : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId)
                  (κ : Path Γ lo (s ×ᵗ listᵗ s) t)
                → Emits {m = m} (s ×ᵗ listᵗ s) κ → Emits {m = m} s (batchSync-f nid ↠ κ)
emits-batchSync nid κ em {v = v} rv now sched st le
  with batchSyncPush nid v st in peq
... | (nothing , st₁) = _ , emit-batchSync-held peq
... | (just g , st₁)  =
      let (r , d) = em (red-pushed nid v st rv peq) now sched st₁
                      (unconn-batchSyncPush nid v sched st peq le)
      in r , emit-batchSync peq d

closes-batchSync : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId)
                   (κ : Path Γ lo (s ×ᵗ listᵗ s) t)
                 → Handles {m = m} (s ×ᵗ listᵗ s) κ → Closes {m = m} (batchSync-f nid ↠ κ)
closes-batchSync {s = s} nid κ (em , cl) now sched st le
  with batchSyncFlush {s = s} nid st in feq
... | (nothing , st₁) = let (r , d) = cl now sched st₁
                                        (unconn-batchSyncFlush nid sched st feq le)
                        in r , close-batchSync-empty feq d
... | (just g , st₁)  =
      let le₁                        = unconn-batchSyncFlush nid sched st feq le
          ((out , sched₁ , st₂) , d) = em (red-flushed nid st feq) now sched st₁ le₁
          (r , c)                    = cl now sched₁ st₂
                                         (≤-trans (unconn-emit d) le₁)
      in _ , close-batchSync feq d c

handles-batchSync : ∀ {n} {Γ : Ctx n} {t s lo m} (nid : NodeId)
                    (κ : Path Γ lo (s ×ᵗ listᵗ s) t)
                  → Handles {m = m} (s ×ᵗ listᵗ s) κ → Handles {m = m} s (batchSync-f nid ↠ κ)
handles-batchSync nid κ hκ = emits-batchSync nid κ (proj₁ hκ) , closes-batchSync nid κ hκ

-- LEAVING A SUBSCRIBED INNER IS FREE; the completion side is where the
-- lane is released, the queue drained and the operator finally asked
-- whether it is finished -- and it is asked of the store the DRAIN
-- left, since a lane freed here is refilled there.
emits-from-inner : ∀ {n} {Γ : Ctx n} {t s lo m} (op : AllOp) (allNid inst : NodeId)
                   (κ : Path Γ lo s t)
                 → Emits {m = m} s κ → Emits {m = m} s (from-inner op allNid inst ↠ κ)
emits-from-inner op allNid inst κ em rv now sched st le =
  let (r , d) = em rv now sched st le in r , emit-from-inner d

closes-from-inner : ∀ {n} {Γ : Ctx n} {t s lo m} (op : AllOp) (allNid inst : NodeId)
                    (κ : Path Γ lo s t)
                  → Handles {m = m} s κ → Closes {m = m} (from-inner op allNid inst ↠ κ)
closes-from-inner {s = s} op allNid inst κ hκ now sched st le
  with any (aliveThroughᶠ inst st) (EvalSt.registry st) in aeq
... | true  = _ , close-inner-absorb aeq
... | false with mergeAllQueue {s = s} allNid (markInnerDone op allNid inst st) in qeq
...   | (q , st₀) with unconn-mergeAllQueue op allNid inst sched st qeq le
...     | le₀ with drainQueue! op allNid κ now q hκ sched st₀ le₀
...       | ((out , sched₁ , st₁) , dd) with allFinished op allNid st₁ in feq
...         | true  = let (r , c) = proj₂ hκ now sched₁ st₁
                                      (≤-trans (unconn-drain dd) le₀)
                      in _ , close-inner-done aeq qeq dd feq c
...         | false = _ , close-inner-open aeq qeq dd feq

handles-from-inner : ∀ {n} {Γ : Ctx n} {t s lo m} (op : AllOp) (allNid inst : NodeId)
                     (κ : Path Γ lo s t)
                   → Handles {m = m} s κ → Handles {m = m} s (from-inner op allNid inst ↠ κ)
handles-from-inner op allNid inst κ hκ =
    emits-from-inner op allNid inst κ (proj₁ hκ)
  , closes-from-inner op allNid inst κ hκ

------------------------------------------------------------------
-- AN INNER OBSERVABLE ARRIVING AT A FLATTENER'S OUTER FRAME.  The
-- candidate travels WITH the value, so the frame subscribes what
-- reaches it without asking the store for anything but its own lane.
------------------------------------------------------------------

consume! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo m}
           (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t) → Handles {m = m} u κ
         → {o : Val Γ (obs u)} → Red m (obs u) o
         → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
         → Σ (Out e) λ r → consume⇓ {e = e} op nid κ now o sched st r
consume! {u = u} mergeAllᵒ nid κ hκ ro now sched st le
  with lookupNode nid (EvalSt.nodes st) in neq
... | nothing                 = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (cell-st _)        = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (take-st _)        = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (batchSync-st _ _) = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (switch-st _ _)    = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (exhaust-st _ _)   = _ , consume-merge-nil (cong (consumeUsable mergeAllᵒ u) neq)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u in weq
...   | no ¬p = _ , consume-merge-nil
                      (trans (cong (consumeUsable mergeAllᵒ u) neq) (cong ⌊_⌋ weq))
...   | yes refl with hasRoom lim act in req
...     | false = _ , consume-merge-park neq req
...     | true  =
          let inst = freshId nodeᵏ (Sched.mint sched)
              (r , d) =
                ro (from-inner mergeAllᵒ nid inst ↠ κ)
                   (handles-from-inner mergeAllᵒ nid inst κ hκ) now
                   (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) })
                   (record st { nodes = setNode nid (mergeAll-st lim (suc act) q od)
                                                (EvalSt.nodes st) })
                   le
          in r , consume-merge-sub neq req refl d
consume! {u = u} switchᵒ nid κ hκ ro now sched st le
  with lookupNode nid (EvalSt.nodes st) in neq
... | nothing                    = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (cell-st _)           = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (take-st _)           = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (batchSync-st _ _)    = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (mergeAll-st _ _ _ _) = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (exhaust-st _ _)      = _ , consume-switch-nil (cong (consumeUsable switchᵒ u) neq)
... | just (switch-st cur od) with switchKill cur sched st in keq
...   | (sched₁ , st₁) =
        let inst = freshId nodeᵏ (Sched.mint sched₁)
            (r , d) =
              ro (from-inner switchᵒ nid inst ↠ κ)
                 (handles-from-inner switchᵒ nid inst κ hκ) now
                 (record sched₁ { mint = setAt nodeᵏ (suc inst) (Sched.mint sched₁) })
                 (record st₁ { nodes = setNode nid (switch-st (just inst) od)
                                               (EvalSt.nodes st₁) })
                 (unconn-switchKill-eq cur sched st keq le)
        in r , consume-switch-sub neq keq refl d
consume! {u = u} exhaustᵒ nid κ hκ ro now sched st le
  with lookupNode nid (EvalSt.nodes st) in neq
... | nothing                    = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (cell-st _)           = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (take-st _)           = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (batchSync-st _ _)    = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (mergeAll-st _ _ _ _) = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (switch-st _ _)       = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (exhaust-st true _)   = _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) neq)
... | just (exhaust-st false od) =
      let inst = freshId nodeᵏ (Sched.mint sched)
          (r , d) =
            ro (from-inner exhaustᵒ nid inst ↠ κ)
               (handles-from-inner exhaustᵒ nid inst κ hκ) now
               (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) })
               (record st { nodes = setNode nid (exhaust-st true od) (EvalSt.nodes st) })
               le
      in r , consume-exhaust-sub neq refl d

emits-thru-outer : ∀ {n} {Γ : Ctx n} {t u lo m} (op : AllOp) (nid : NodeId)
                   (κ : Path Γ lo u t)
                 → Handles {m = m} u κ → Emits {m = m} (obs u) (thru-outer op nid ↠ κ)
emits-thru-outer op nid κ hκ ro now sched st le =
  let (r , d) = consume! op nid κ hκ ro now sched st le in r , emit-thru-outer d

closes-thru-outer : ∀ {n} {Γ : Ctx n} {t u lo m} (op : AllOp) (nid : NodeId)
                    (κ : Path Γ lo u t) → Closes {m = m} κ
                  → Closes {m = m} (thru-outer op nid ↠ κ)
closes-thru-outer op nid κ cl now sched st le
  with allFinished op nid (markOuterDone op nid st) in feq
... | true  = let (r , d) = cl now sched (markOuterDone op nid st)
                              (unconn-markOuterDone op nid sched st le)
              in r , close-outer-done feq d
... | false = _ , close-outer-open feq

handles-thru-outer : ∀ {n} {Γ : Ctx n} {t u lo m} (op : AllOp) (nid : NodeId)
                     (κ : Path Γ lo u t)
                   → Handles {m = m} u κ → Handles {m = m} (obs u) (thru-outer op nid ↠ κ)
handles-thru-outer op nid κ hκ =
  emits-thru-outer op nid κ hκ , closes-thru-outer op nid κ (proj₂ hκ)

------------------------------------------------------------------
-- THE TWO SUBSCRIBE-SIDE ASSEMBLIES THE TERM FACE WOULD OTHERWISE
-- HAVE TO INLINE.
------------------------------------------------------------------

subsAll! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo m}
           (op : AllOp) (ns : NodeState Γ) {b : Val Γ (obs (obs u))}
         → Red m (obs (obs u)) b
         → (κ : Path Γ lo u t) → Handles {m = m} u κ
         → (now : Tick) (sched : Sched Γ) (st : EvalSt e) → unconnected sched st ≤ m
         → Σ (Out e) λ r → subscribeAll⇓ {e = e} op ns b κ now sched st r
subsAll! op ns rb κ hκ now sched st le =
  let nid     = freshId nodeᵏ (Sched.mint sched)
      (r , d) = rb (thru-outer op nid ↠ κ) (handles-thru-outer op nid κ hκ) now
                   (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                   (installNode nid ns st)
                   le
  in r , sub-all refl d

-- THE FLUSH SITS AFTER THE SUBSCRIBE CALL RETURNS, which is where the
-- TypeScript's merged second input is subscribed.  A body that
-- completed inside the call has already been flushed by its own
-- completion, so what this finds is an empty buffer.
subsBatchSync! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo Θ}
                 {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                 (κ : Path Γ lo (u ×ᵗ listᵗ u) t) {m : ℕ} → Emits {m = m} (u ×ᵗ listᵗ u) κ
               → (nid : NodeId) (now : Tick) (sched₀ : Sched Γ) (st₀ : EvalSt e)
                 (out : Stream Γ t) (sched₁ : Sched Γ) (st₁ : EvalSt e)
               → unconnected sched₀ st₀ ≤ m
               → freshId nodeᵏ (Sched.mint sched₀) ≡ nid
               → subscribeE⇓ {e = e} (Θ , b , ρ) (batchSync-f nid ↠ κ) now
                   (record sched₀ { mint = setAt nodeᵏ (suc nid) (Sched.mint sched₀) })
                   (installNode nid (batchSync-st {t = u} true []) st₀)
                   (out , sched₁ , st₁)
               → Σ (Out e) λ r →
                   subscribeE⇓ {e = e} (Θ , batchSyncᵉ b , ρ) κ now sched₀ st₀ r
subsBatchSync! {u = u} κ em nid now sched₀ st₀ out sched₁ st₁ le neq d
  with batchSyncFlush {s = u} nid st₁ in fq
... | (nothing , st₂) = _ , subs-batchSync-empty neq d fq
... | (just g , st₂)  =
      let le₁     = unconn-batchSyncFlush nid sched₁ st₁ fq (≤-trans (unconn-subs d) le)
          (r , ed) = em (red-flushed nid st₁ fq) now sched₁ st₂ le₁
      in _ , subs-batchSync neq d fq ed

------------------------------------------------------------------
-- THE FUNDAMENTAL THEOREM AT TERMS.
------------------------------------------------------------------

-- THE CEILING IS A MEASURE COMPONENT, NOT A HYPOTHESIS.  The walk
-- carries a stratum `k` with the guard `T (inputsBelowᵉ k b)` and an
-- `Acc` on it, ordered ABOVE the g-size accessibility.  A term step
-- holds the ceiling and shrinks the size; the SHARED-SLOT step drops
-- the ceiling to the slot's own index -- which its `ok` field licenses
-- -- and lets the size go free.  That is what funds the descent into a
-- definition drawn from the slot table rather than from the term, and
-- an input's g-size being zero is why nothing smaller could.
--
-- AND THE PATH IS THREADED, NEVER WALKED.  Every arm that pushes a
-- frame builds the longer path's `Handles` from the one it was handed,
-- so nothing here reaches the general walk -- which is what keeps this
-- block mutual with itself alone.
mutual
  redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t m} (b : Exp Γ [] [] Θ t)
              (σ : Env Γ Θ) → RedEnv m σ
            → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
            → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} m (obs t) (Θ , b , σ)
  redExpAcc (input i) σ rσ k ok aK a κ hκ now sched st le =
    red-input i σ k ok aK κ hκ now sched st le
  redExpAcc (ofᵉ ts) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let ((out , sched₁ , st₁) , d) =
          emits! κ (proj₁ hκ) now (map (λ tm → evalWith tm σ) ts)
            (redTmsAcc ts σ rσ k ok aK (rs ≤-refl)) sched st le
        (r , c) = proj₂ hκ now sched₁ st₁ (≤-trans (unconn-emits d) le)
    in _ , subs-of d c
  redExpAcc emptyᵉ σ rσ k ok aK a κ hκ now sched st le =
    let (r , c) = proj₂ hκ now sched st le in r , subs-empty c
  redExpAcc (takeᵉ c b) σ rσ k ok aK (acc rs) κ hκ now sched st le
    with evalWith c σ in ceq
  ... | zero  = let (r , cl) = proj₂ hκ now sched st le in r , subs-take-zero ceq cl
  ... | suc j =
        let nid = freshId nodeᵏ (Sched.mint sched)
            okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
            (r , d) =
              redExpAcc b σ rσ k okb aK
                (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c))))
                (take-f nid ↠ κ) (handles-take nid κ hκ) now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (take-st (suc j)) st) le
        in r , subs-take-suc ceq refl d
  redExpAcc (batchSyncᵉ {t = u} b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((out , sched₁ , st₁) , d) =
          redExpAcc b σ rσ k ok aK (rs ≤-refl)
            (batchSync-f nid ↠ κ) (handles-batchSync nid κ hκ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (batchSync-st {t = u} true []) st) le
    in subsBatchSync! κ (proj₁ hκ) nid now sched st out sched₁ st₁ le refl d
  redExpAcc (mapᵉ f b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let fn  = _ , f , σ
        okf = ∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        okb = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        rf  = redFnAcc f σ rσ k okf aK (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b))))
        (r , d) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f))))
            (map-f fn ↠ κ) (handles-map fn κ rf hκ) now sched st le
    in r , subs-map d
  redExpAcc (scanᵉ f z b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let nid  = freshId nodeᵏ (Sched.mint sched)
        fn   = _ , f , σ
        rest = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵗ k z ∧ inputsBelowᵉ k b) ok
        okb  = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        (r , d) =
          redExpAcc b σ rσ k okb aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
            (scan-f fn nid ↠ κ) (handles-scan fn nid κ hκ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (cell-st (evalWith z σ)) st) le
    in r , subs-scan refl d
  redExpAcc (mergeAllᵉ {t = u} lim b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-merge-all d
  redExpAcc (switchAllᵉ b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! switchᵒ (switch-st nothing false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-switch-all d
  redExpAcc (exhaustAllᵉ b) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let (r , d) = subsAll! exhaustᵒ (exhaust-st false false)
                    (redExpAcc b σ rσ k ok aK (rs ≤-refl)) κ hκ now sched st le
    in r , subs-exhaust-all d
  redExpAcc (μᵉ body) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let ih = redExpAcc (unfoldμ body) σ rσ k (ib-unfoldμ k body ok) aK
               (rs (subst (_< suc (gsizeᵉ body))
                          (sym (gsize-unfoldμ body)) ≤-refl))
        (r , d) = ih κ hκ now sched st le
    in r , subs-μ d
  redExpAcc (varᵉ ()) σ rσ k ok aK a
  redExpAcc (deferᵉ body) σ rσ k ok aK a κ hκ now sched st le =
    _ , subs-defer refl refl refl refl
  redExpAcc (mintᵉ body) σ rσ k ok aK (acc rs) κ hκ now sched st le =
    let src     = freshId sourceᵏ (Sched.mint sched)
        sched′  = record sched { mint = setAt sourceᵏ (suc src) (Sched.mint sched) }
        (r , d) = redExpAcc body (src ∷ᵉ σ) (tt , rσ) k ok aK (rs ≤-refl)
                    κ hκ now sched′ st le
    in r , subs-mint refl d

  -- THE SLOT ARM, WHICH IS FIVE SUB-ARMS OF PROTOCOL AND ONE THAT
  -- SPENDS THE CEILING.  A scripted slot's values are DATA by the
  -- slot's own side condition, so `redDatas` closes them outright; the
  -- ceiling's accessibility is taken apart here rather than passed on,
  -- since `toℕ i < k` is exactly what the guard reduces to at this
  -- former.
  red-input : ∀ {n} {Γ : Ctx n} {Θ m} (i : Fin n) (σ : Env Γ Θ) (k : ℕ)
            → T (toℕ i <ᵇ k) → Acc _<_ k
            → Red {Γ = Γ} m (obs (lookup Γ i)) (Θ , input i , σ)
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      with toℕ i <? lo
  ... | no  ¬below = let (r , c) = proj₂ hκ now sched st le
                     in r , subs-floor (≮⇒≥ ¬below) c
  ... | yes below  with Sched.slots sched i in slEq
  ...   | scripted {ok = okD} (hot async)
          with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ...     | true  = let (r , c) = proj₂ hκ now sched st le
                    in r , subs-hot-done below slEq doneEq c
  ...     | false = _ , subs-hot-live below slEq doneEq refl
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | scripted {ok = okD} (cold sync []) =
        let ((out , sched₁ , st₁) , d) =
              emits! κ (proj₁ hκ) now sync (redDatas _ okD sync) sched st le
            (r , c) = proj₂ hκ now sched₁ st₁ (≤-trans (unconn-emits d) le)
        in _ , subs-cold-sync below slEq d c
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | scripted {ok = okD} (cold sync (dv ∷ ds)) =
        let src   = freshId sourceᵏ (Sched.mint sched)
            ord   = freshId ordinalᵏ (Sched.mint sched)
            rid   = freshId regᵏ (Sched.mint sched)
            sched′ = record sched
                       { mint = setAt regᵏ (suc rid)
                                  (setAt sourceᵏ (suc src)
                                    (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                       ; live = record { source = src ; ordinal = ord
                                       ; elemTy = lookup Γ i
                                       ; pending = resolve now (dv ∷ ds) }
                                ∷ Sched.live sched }
            (r , d) = emits! κ (proj₁ hκ) now sync (redDatas _ okD sync)
                        sched′ (register rid (atDyn src lo) κ st) le
        in r , subs-cold-async below slEq refl refl refl d
  red-input {Γ = Γ} i σ k ok (acc rsK) {lo = lo} κ hκ now sched st le
      | yes below | shared d {ok = okd} =
        red-input-shared i σ d (rsK (<ᵇ⇒< (toℕ i) k ok))
          κ below now sched slEq st hκ le

  -- THE SIXTH SLOT SUB-ARM, WHICH IS THE ONE THE OTHER FIVE ARE NOT.
  -- A share's definition is an arbitrary term standing in no relation
  -- to `input i`, so it cannot be reached by any descent on the TERM.
  -- The telescope's own side condition is what reaches it instead: a
  -- slot's definition may reference only inputs STRICTLY BELOW that
  -- slot, so the definition is charged against the ceiling `toℕ i`,
  -- which the caller's accessibility has just been taken apart to
  -- supply.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ m}
      (i : Fin n) (σ : Env Γ Θ) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → (st : EvalSt e) → Handles {m = m} (lookup Γ i) κ → unconnected sched st ≤ m
    → Σ (Out e) λ r → subscribeE⇓ {e = e} (Θ , input i , σ) κ now sched st r
  red-input-shared {Γ = Γ} i σ d {okd} aI κ below now sched slEq st hκ le
      with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ... | true  = let (r , c) = proj₂ hκ now sched st le
                in r , subs-shared {κ = κ} {below = below} slEq
                         (slot-spent {κ = κ} {below = below} doneEq c)
  ... | false with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
  ...   | true  = _ , subs-shared {κ = κ} {below = below} slEq
                        (slot-join {κ = κ} {below = below} doneEq connEq refl)
  ...   | false =
          red-connect _ i σ d aI κ below now sched slEq st doneEq connEq le

  -- WHERE THE ROUND TRIP IS ORDERED, AND IT IS THE ONLY CLAUSE IN THE
  -- MODULE THAT LOOKS AT THE BOUND.  The guard says this slot is shared
  -- and not yet connected, so the count is at least one -- which makes
  -- a zero bound absurd outright -- and connecting it drops the count,
  -- so what the definition is subscribed under is the walk ONE LEVEL
  -- DOWN rather than a fresh one at the same level.
  red-connect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ} (m : ℕ)
                  (i : Fin n) (σ : Env Γ Θ) (d : Closed Γ (lookup Γ i))
                  {okd : T (inputsBelowᵉ (toℕ i) d)}
                → Acc _<_ (toℕ i)
                → (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
                  (now : Tick) (sched : Sched Γ)
                → Sched.slots sched i ≡ shared d {ok = okd}
                → (st : EvalSt e)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
                → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false
                → unconnected sched st ≤ m
                → Σ (Out e) λ r → subscribeE⇓ {e = e} (Θ , input i , σ) κ now sched st r
  red-connect zero i σ d aI κ below now sched slEq st doneEq connEq le
    with ≤-trans (unconn-connect i sched st slEq connEq) le
  ... | ()
  red-connect (suc m′) i σ d {okd} aI κ below now sched slEq st doneEq connEq le
    with ≤-trans (unconn-connect i sched st slEq connEq) le
  ... | s≤s le′ =
          let rid = freshId regᵏ (Sched.mint sched)
              (r , dv) =
                redExpAcc d []ᵉ tt (toℕ i) okd aI
                  (<-wellFounded-fast (gsizeᵉ d))
                  (share-sink i ≤-refl)
                  (handles-share i ≤-refl (walk-above {m = m′} i)) now
                  (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                  (register rid (atSlot i) (lowerFloor below κ)
                    (record st
                      { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                  le′
          in r , subs-shared {κ = κ} {below = below} slEq
                   (slot-connect doneEq connEq (connect refl dv))

  -- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
  -- former hands the recursion back to the expression face.
  redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u m} (tm : Tm Γ [] [] Θ u)
             (σ : Env Γ Θ) → RedEnv m σ
           → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
           → Acc _<_ (gsizeᵗ tm) → Red m u (evalWith tm σ)
  redTmAcc (varᵗ x) σ rσ k ok aK a = redLookup σ rσ x
  redTmAcc unit̂     σ rσ k ok aK a = tt
  redTmAcc (bool̂ b) σ rσ k ok aK a = tt
  redTmAcc (nat̂ j)  σ rσ k ok aK a = tt
  redTmAcc (pairᵗ x y) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y))))
    , redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x))))
  redTmAcc nilᵗ σ rσ k ok aK a = []ᵃ
  redTmAcc (consᵗ x xs) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs))))
    ∷ᵃ redTmAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x))))
  redTmAcc (foldᵗ l z f) σ rσ k ok aK (acc rs) =
    redFoldVals f σ
      (λ rx ra →
        redTmAcc f (_ ∷ᵉ _ ∷ᵉ σ) (rx , ra , rσ) k
          (∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
            (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
          (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                            (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
      (redTmAcc l σ rσ k
        (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))))
      (redTmAcc z σ rσ k
        (∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f)
          (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k z ∧ inputsBelowᵗ k f) ok)) aK
        (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                          (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
  redTmAcc (fstᵗ q) σ rσ k ok aK (acc rs) =
    proj₁ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (sndᵗ q) σ rσ k ok aK (acc rs) =
    proj₂ (redTmAcc q σ rσ k ok aK (rs ≤-refl))
  redTmAcc (inlᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (inrᵗ x) σ rσ k ok aK (acc rs) = redTmAcc x σ rσ k ok aK (rs ≤-refl)
  redTmAcc (caseᵗ sc l r) σ rσ k ok aK (acc rs)
    with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
       | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
  ... | oksc | rest
    with evalWith sc σ
       | redTmAcc sc σ rσ k oksc aK
           (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r))))
  ... | inj₁ x | q =
    redTmAcc l (x ∷ᵉ σ) (q , rσ) k
      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  ... | inj₂ y | q =
    redTmAcc r (y ∷ᵉ σ) (q , rσ) k
      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  redTmAcc (ifᵗ c x y) σ rσ k ok aK (acc rs)
    with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
  ... | rest with evalWith c σ
  ... | true  =
    redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  ... | false =
    redTmAcc y σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  redTmAcc (primᵗ add x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ sub x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ mul x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ ltᵖ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ eqᵘ x) σ rσ k ok aK a  = tt
  redTmAcc (primᵗ notᵖ x) σ rσ k ok aK a = tt
  redTmAcc (strmᵗ e) σ rσ k ok aK (acc rs) =
    redExpAcc e σ rσ k ok aK (rs ≤-refl)

  redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u m} (ts : List (Tm Γ [] [] Θ u))
              (σ : Env Γ Θ) → RedEnv m σ
            → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
            → Acc _<_ (gsizeᵗˢ ts)
            → All (Red m u) (map (λ tm → evalWith tm σ) ts)
  redTmsAcc []       σ rσ k ok aK a = []ᵃ
  redTmsAcc (x ∷ xs) σ rσ k ok aK (acc rs) =
      redTmAcc x σ rσ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs))))
    ∷ᵃ redTmsAcc xs σ rσ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x))))

  -- A FRAME'S FUNCTION, PAIRED WITH THE AMBIENT ENVIRONMENT AND THEN
  -- APPLIED, is the term face at one more entry.
  redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u m} (f : Fn Γ [] [] Θ s u)
             (σ : Env Γ Θ) → RedEnv m σ
           → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
           → Acc _<_ (gsizeᵗ f) → RedFn {Γ = Γ} m (Θ , f , σ)
  redFnAcc f σ rσ k ok aK a {v} p = redTmAcc f (v ∷ᵉ σ) (p , rσ) k ok aK a

------------------------------------------------------------------
-- THE TOP LINE, AND THE SAME CLAIM WITH NO OBLIGATION LEFT.
------------------------------------------------------------------

-- A value at observable type IS a body paired with an environment, and
-- an entry of that environment at observable type is another such
-- value, so nothing could be claimed about the pair that was not
-- already claimed of its entries.  That is what a runtime value costs
-- now that a value is a CLOSURE: the environment's entries are where
-- the claim is re-established, once, rather than threaded through every
-- site that meets a stored value.
reducible : ∀ {n} {Γ : Ctx n} {Θ t m} (b : Exp Γ [] [] Θ t) (σ : Env Γ Θ) → RedEnv m σ
          → Red {Γ = Γ} m (obs t) (Θ , b , σ)
reducible b σ rσ =
  redExpAcc b σ rσ _ (ib-topᵉ b) (<-wellFounded-fast _) (<-wellFounded-fast (gsizeᵉ b))

mutual
  red-val : ∀ {n} {Γ : Ctx n} {m} (t : Ty) (v : Val Γ t) → Red m t v
  red-val unitᵗ     v           = tt
  red-val boolᵗ     v           = tt
  red-val natᵗ      v           = tt
  red-val uniqᵗ     v           = tt
  red-val (s ×ᵗ u)  (a , b)     = red-val s a , red-val u b
  red-val (s +ᵗ u)  (inj₁ a)    = red-val s a
  red-val (s +ᵗ u)  (inj₂ b)    = red-val u b
  red-val (listᵗ s) []          = []ᵃ
  red-val (listᵗ s) (x ∷ xs)    = red-val s x ∷ᵃ red-val (listᵗ s) xs
  red-val (obs u)   (Θ , b , σ) = reducible b σ (red-env σ)

  red-env : ∀ {n} {Γ : Ctx n} {Θ : List Ty} {m} (σ : Env Γ Θ) → RedEnv m σ
  red-env []ᵉ                 = tt
  red-env (_∷ᵉ_ {s = s} v vs) = red-val s v , red-env vs

redFn : ∀ {n} {Γ : Ctx n} {s u m} (fn : FnClo Γ s u) → RedFn m fn
redFn (Θ , f , σ) =
  redFnAcc f σ (red-env σ) _ (ib-topᵗ f)
    (<-wellFounded-fast _) (<-wellFounded-fast (gsizeᵗ f))

------------------------------------------------------------------
-- THE GENERAL PATH WALK, which is what the arrival spine spends and
-- the one place a path is taken apart rather than extended.
------------------------------------------------------------------

-- THE SINK ARM IS THE ONLY ONE THAT IS NOT STRUCTURAL, and what pays
-- for it is the floor: `shareAdmit` hands back chains at `suc (toℕ i)`,
-- strictly above the floor this path sinks at, so `n ∸ lo` drops.  Every
-- other arm peels a frame.
handlesAcc : ∀ {n} {Γ : Ctx n} {t lo m} → Acc _<_ (n ∸ lo) → Walk Γ t m lo
handlesAcc ac       root                    = handles-root
handlesAcc (acc rec) (share-sink i below)   =
  handles-share i below (λ {u} κ → handlesAcc (rec (monus-sink i below)) {u} κ)
handlesAcc ac (map-f fn ↠ κ)          = handles-map fn κ (redFn fn) (handlesAcc ac κ)
handlesAcc ac (scan-f fn nid ↠ κ)     = handles-scan fn nid κ (handlesAcc ac κ)
handlesAcc ac (take-f nid ↠ κ)        = handles-take nid κ (handlesAcc ac κ)
handlesAcc ac (batchSync-f nid ↠ κ)   = handles-batchSync nid κ (handlesAcc ac κ)
handlesAcc ac (from-inner op a i ↠ κ) = handles-from-inner op a i κ (handlesAcc ac κ)
handlesAcc ac (thru-outer op nid ↠ κ) = handles-thru-outer op nid κ (handlesAcc ac κ)

handles! : ∀ {n} {Γ : Ctx n} {t u lo m} (κ : Path Γ lo u t) → Handles {m = m} u κ
handles! {n = n} {lo = lo} = handlesAcc (<-wellFounded-fast (n ∸ lo))

------------------------------------------------------------------
-- THE ARRIVAL SPINE.
------------------------------------------------------------------

-- A SCRIPTED SOURCE'S LAST VALUE IS FOLLOWED BY ITS END, IN THAT ORDER
-- AND DOWN THE SAME CHAIN, which is what an rxjs observer sees.
chainStep! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (c : AtFloor Γ (arrTy a) t)
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Out e) λ r → chainStep⇓ {e = e} a c sched st r
chainStep! a (lo , path) sched st with Arrival.isLast a in leq
... | false = let (r , d) = proj₁ (handles! path) (red-val (arrTy a) (arrVal a))
                              (arrTick a) sched st ≤-refl
              in r , chain-more leq d
... | true  = let ((out , sched₁ , st₁) , d) =
                    proj₁ (handles! path) (red-val (arrTy a) (arrVal a))
                      (arrTick a) sched st ≤-refl
                  (r , c) = proj₂ (handles! path) (arrTick a) sched₁ st₁ ≤-refl
              in _ , chain-last leq d c

cascadeGo! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (a : Arrival Γ) (chains : List (RegId × AtFloor Γ (arrTy a) t))
             (sched : Sched Γ) (st : EvalSt e)
           → Σ (Out e) λ r → cascadeGo⇓ {e = e} a chains sched st r
cascadeGo! a []               sched st = _ , casc-nil
cascadeGo! a ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st) in eqc
... | true  = let (r , g) = cascadeGo! a cs sched st in r , casc-cut eqc g
... | false =
      let ((emits , sched₁ , st₁) , s) =
            chainStep! a c sched (record st { delivered = rid ∷ EvalSt.delivered st })
          (_ , g) = cascadeGo! a cs sched₁ st₁
      in _ , casc-live eqc s g

cascade! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e)
         → Σ (Out e) λ r → cascade⇓ {e = e} a sched st r
cascade! a sched st =
  let (_ , g) = cascadeGo! a (chainsOf a st) sched (cascadeLatch a sched st)
  in _ , casc-run g

drain! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e)
       → Σ (Stream Γ t) λ s → drain⇓ {e = e} fuel sched st s
drain! zero    sched st = _ , drain-done
drain! (suc k) sched st with sched-next sched in eqn
... | inj₁ _            = _ , drain-empty eqn
... | inj₂ (a , sched′) =
      let ((out , sched″ , st′) , c) = cascade! a sched′ st
          (_ , d)                    = drain! k sched″ st′
      in _ , drain-step eqn c d

evaluate! : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
          → Σ (Stream Γ t) λ s → evaluate⇓ fuel e ins s
evaluate! {n = n} fuel e ins =
  let ((burst , sched₀ , st₀) , s) =
        reducible e []ᵉ tt (root {lo = n}) handles-root 0
          (sched-init e ins) (st-init e) ≤-refl
      (rest , d) = drain! fuel sched₀ st₀
  in _ , eval-run s d

-- AND THE EVALUATOR IS THE PROJECTION.  Not a new machine -- the same
-- machine with every rank reading and every `<?` gone, reached through
-- the builder rather than through a witness it seeds itself.
evaluate↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → Stream Γ t
evaluate↓ fuel e ins = proj₁ (evaluate! fuel e ins)
