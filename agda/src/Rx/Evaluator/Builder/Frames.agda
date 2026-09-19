------------------------------------------------------------------
-- THE BUILDER'S LEVEL-FREE HALF.
------------------------------------------------------------------

-- EVERYTHING HERE IS POLYMORPHIC IN THE BOUND, which is what makes it
-- the half that can be written once.  The share fan-out, the store
-- steps the count reads through, and the sink's own handles ask only
-- that SOME bound be respected; none of them looks at its shape.  The
-- half that does is the term face and the walk, and it is cut off into
-- a module indexed by the bound -- because a connect spends the pair
-- one level down, and a single file cannot state that.
module Rx.Evaluator.Builder.Frames where

open import Data.Bool using (true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc; _<_; _≤_; s≤s; _∸_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans; ∸-monoʳ-<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Rx.Prim using (Tick; PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp using (Ty; _×ᵗ_; obs; listᵗ; _≟ᵗ_; Ctx; Closed; Val; Exp; FnClo; Env; batchSyncᵉ; inputsBelowᵉ)
open import Rx.Exp.Guarded using (gsizeᵉ)
open import Rx.Mint using (nodeᵏ; freshId; setAt)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; AllOp; NodeId; NodeState; root; share-sink; _↠_; map-f; scan-f;
  take-f; batchSync-f; from-inner; thru-outer; mergeAllᵒ; switchᵒ; exhaustᵒ; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; installNode; lookupNode; setNode; hasRoom;
  consumeUsable; switchKill; aliveThroughᶠ; markInnerDone; markOuterDone; allFinished;
  mergeAllQueue; scanStep; takeStep; takeSpent; cutAt; batchSyncPush; batchSyncFlush; RegId;
  shareAdmit; shareLatch; isFinᵖ)
open import Rx.Evaluator.Domain using (emits⇓; subscribeE⇓; consume⇓; drainQueue⇓; subscribeAll⇓; emit-root; emit-map; emit-scan;
  emit-scan-stuck; emit-take-more; emit-take-last; emit-take-spent; emit-batchSync;
  emit-batchSync-held; emit-from-inner; emit-thru-outer; close-root; close-map; close-scan;
  close-take-spent; close-take; close-batchSync; close-batchSync-empty; close-inner-absorb;
  close-inner-done; close-inner-open; close-outer-done; close-outer-open; emits-nil;
  emits-cons; subs-batchSync; subs-batchSync-empty; consume-merge-sub; consume-merge-park;
  consume-merge-nil; consume-switch-sub; consume-switch-nil; consume-exhaust-sub;
  consume-exhaust-nil; sub-all; dispatchShare⇓; shareGo⇓; disp; go-nil; go-cut; go-val; go-fin;
  emit-sink; close-sink)
open import Rx.Evaluator.Reducible using (Out; Red; Emits; Closes; Handles; RedFn; RedEnv; unconnected; red-scanned; red-pushed; red-flushed)
open import Rx.Evaluator.Unconnected using (unconn-latch; unconn-scanStep; unconn-takeStep; unconn-cutAt; unconn-batchSyncPush;
  unconn-batchSyncFlush; unconn-mergeAllQueue; unconn-markOuterDone; unconn-switchKill-eq;
  unconn-emit; unconn-close; unconn-subs; unconn-drain)
------------------------------------------------------------------
-- THE ONE LEAF LEFT, AND WHY IT IS THE ONLY ONE.
------------------------------------------------------------------

-- A LANE DRAIN IS THE LEVEL-FREE HALF'S ONE REMAINING CYCLE, AND
-- CUTTING IT HERE IS WHAT MAKES EVERYTHING ELSE A STRAIGHT LINE.
-- Every other block below takes what it needs from the block above it;
-- this one alone wants something declared after it.  It is stated as
-- the whole drain, because what it wants back is the fundamental
-- theorem at values -- there is no narrower cut, the way the share's
-- was a walk rather than a fan-out.
--
-- THE SHARE'S CYCLE IS NO LONGER ONE.  A connect spends the pair a
-- STRICTLY SMALLER bound offers, which is a recursion on the bound
-- rather than a forward reference, and the file above this one ties it.
--
-- AND A PROBE CANNOT REACH WHAT IS IN DOUBT HERE, which is why it is
-- stated at full strength and left uninstantiated.  The conclusion is
-- an EXISTENCE claim, so a row means hand-building one derivation at
-- one concrete point -- and that succeeds whenever the queue handed
-- over is finite, so it could not have failed.  What is in doubt is
-- uniform rather than pointwise: whether a body exists at EVERY store,
-- which is the measure question the statement's own header carries.
-- A parked lane that frees is the right shape for a bug-cache row and
-- the wrong shape for a receipt.

postulate
  -- THE PARKED LANE, HANDED BACK ITS QUEUE.  A flattener that could not
  -- subscribe when a value arrived kept it; this is the walk that spends
  -- the backlog once a lane frees, one carried value at a time.
  --
  -- WHAT IT CONSUMES, AND WHY THAT IS FIVE STATEMENTS RATHER THAN ONE.
  -- A drain hands back a derivation, so its call site reaches the frame's
  -- closing side only by carrying the count PAST that derivation, which
  -- is `unconn-drain`.  And `unconn-drain` cannot be had on its own:
  -- `drainQueue⇓` is mutually defined with the delivery relations, so its
  -- count lemma is one member of an indivisible block it shares with
  -- `unconn-emit`, `unconn-close`, `unconn-emits` and `unconn-subs`.
  --
  -- WHICH MEASURE THE QUEUE OFFERS, AND IT IS A PAIR RATHER THAN A
  -- NUMBER.  A drain pops the node's queue WHOLE, so the store it
  -- recurses under holds strictly fewer parked inners than the one it
  -- was handed.  That count alone cannot be the bound, because a
  -- subscribe run DURING the drain may park again -- and the pair
  -- survives exactly that, since a park is not free.  An inner's own
  -- values travel UP its frame and park nothing, so a park during a
  -- drain needs the node's OUTER to fire, and the drain is not walking
  -- the outer's chain.  The one edge that reaches a chain the walk is
  -- not on is the share fan-out, and its path constructor is installed
  -- by a connect and by nothing else -- so regrowth costs the count
  -- the builder is ALREADY ordered by, and the measure is that count
  -- and the parked total read LEXICOGRAPHICALLY, where the second
  -- component is free to jump because it jumps only where the first
  -- has fallen.  That is read off the subscribe relation's own
  -- constructors rather than instantiated, which is why the obligation
  -- below is stated as a statement and not as a remark.
  --
  -- AND THE PAIR IS SPENT AS A DISJUNCTION, WHICH IS THE PART THAT IS
  -- NOT OBVIOUS.  The parked total cannot be a budget the way the count
  -- is, because a budget has to be PRESERVED across every step and a
  -- park raises it.  What IS preserved is weaker: the count is under
  -- its bound, and either STRICTLY under it or the parked total is
  -- under a bound of its own -- since a subscribe that parks pays a
  -- connect, which buys the first disjunct, and one that does not keeps
  -- the second.  That is the obligation to state, one more induction
  -- over the delivery relations in the idiom of the count's own, and
  -- its leaves are not minted until this parent can spend them.
  --
  -- DEAD ROUTE: writing it as a body here needs the general path walk,
  --   and the walk's own `from-inner` CLOSING side is what runs the drain
  --   -- so the direct route does not fail on difficulty, it fails by
  --   putting every declaration between the two into one mutual block,
  --   which is the single shape this module's layering exists to avoid.
  drainQueue! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo m}
                (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t)
                (now : Tick) (q : List (Val Γ (obs u)))
              → Handles {m = m} u κ → (sched : Sched Γ) (st : EvalSt e)
              → unconnected sched st ≤ m
              → Σ (Out e) λ r → drainQueue⇓ {e = e} op nid κ now q sched st r

------------------------------------------------------------------
-- THE SHARE'S SINK, WHICH FANS A VALUE OUT OVER A WALK IT IS HANDED.
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
-- WHAT A LEVEL OFFERS THE LEVEL ABOVE IT.
------------------------------------------------------------------

-- A CONNECT DROPS THE BOUND, AND WHAT IT SPENDS IS NOT ONLY A WALK.
-- The share's definition is subscribed by the TERM face at the smaller
-- bound, and that face needs walks smaller still, so the two travel
-- together or neither descends.  Packaging them is what makes the
-- recursion on the bound ONE function rather than a mutual block --
-- and the fundamental theorem at values rides along because the
-- arrival spine reads it at whatever bound it is standing at.
record Below (m : ℕ) : Set where
  field
    walk : ∀ {n} {Γ : Ctx n} {t lo} → Walk Γ t m lo
    term : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t)
             (σ : Env Γ Θ) → RedEnv m σ
         → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
         → Acc _<_ (gsizeᵉ b) → Red m (obs t) (Θ , b , σ)
    val  : ∀ {n} {Γ : Ctx n} (u : Ty) (v : Val Γ u) → Red m u v
