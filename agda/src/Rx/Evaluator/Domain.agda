-- THE EVALUATOR'S RECURSION, AS A RELATION RATHER THAN AS A MEASURE.
-- One family per frame function in the evaluator's two genuine cycles,
-- one constructor per clause, and every recursive call a PREMISE at the
-- arguments that call actually makes.  A derivation is therefore a
-- complete run, and the argument that runs exist is an induction free
-- to use any measure a PROOF may use — including quantities no function
-- of this development can compute.
--
-- WHY A GRAPH RELATION AND NOT A DOMAIN PREDICATE.  Bove-Capretta's
-- domain wants one premise per recursive call, but this evaluator
-- THREADS STATE: a later call's arguments are an earlier call's
-- results, so the premises mention the function and the domain has to
-- be defined inductive-recursively WITH it.  That would mean a second
-- copy of every body.  Indexing on the result instead binds those
-- intermediates as constructor variables, so the families stand alone
-- and no body is duplicated.
--
-- AND THE PREMISE IS WHAT THE GUARD WAS BUYING.  The hop into an
-- arriving observable is not structural in the caller's term, so the
-- running machine has to ASK whether the value is smaller — and answers
-- the negative case by emitting a marker.  Here the hop's premise is a
-- sub-derivation at that very value, so the question is asked of the
-- DERIVATION and never of the run: nothing is tested, and no
-- constructor emits the marker.

-- A SUBSCRIPTION EMITS AT THE ROOT TYPE, ONE VALUE AT A TIME, AND THAT
-- IS WHAT MAKES DEPTH-FIRST THE RECURSION'S OWN ORDER RATHER THAN A
-- PROPERTY SOMETHING HAD TO RE-ESTABLISH.  A subscription used to hand
-- its whole output back at the SOURCE's element type, and each
-- enclosing frame pushed that finished list through itself; a source
-- was therefore materialised whole before any of it descended, so a
-- re-entrant subscribe wrote into a registry that the loop it should
-- have joined had already read past.  Carrying the rest of the path
-- INTO the subscribe fixes it at the root: a value reaches the
-- subscriber before the next one is produced, exactly as an rxjs
-- observer does, and the burst-pushing family is deleted rather than
-- repaired.
--
-- AND IT IS WHAT LETS EVERY OPERATOR BE WRITTEN AS ITS MIRROR IS.  A
-- frame handed a finished list could group it, count it or truncate it
-- knowing how much was coming; none of those is a capability rxjs
-- gives an operator.  So the bracket operator holds a flag and a
-- buffer, the truncation spends its count one value at a time and cuts
-- mid-burst, and a saturated flattener queues the OBSERVABLE — which
-- is what the TypeScript does in each case, and what the list encoding
-- was quietly standing in for.

-- THE DESCENT IS DENOMINATED IN THE TYPE, AND THAT IS WHAT REACHES
-- THE ONE FORMER A FIGURE AND A TERM PREDICATE BOTH MISS.  Every
-- killed reading recursed on the TERM or on a quantity fixed before
-- the run, and a fold's payload is its own previous payload rebuilt
-- by substitution — neither a subterm of what produced it nor
-- smaller than it, so nothing inverts and nothing descends.
-- Recursion on the TYPE has nothing to invert: `Val` is already
-- defined by recursion on `Ty`, and a runtime observable at an `obs`
-- IS a closed expression, so a type-indexed reducibility predicate
-- lands on that same recursion and the hop relates two indices the
-- definition already identifies.  The fold does not move the type at
-- all and so asks the descent for nothing; the flattener strictly
-- shrinks it, and the flattener is exactly where the hop is.

-- AND THE FIGURE THE OLD DESCENT READ IS NOT THE ONE THE RECURSION
-- SPENDS.  At a doubling fold the accumulator's nesting grows without
-- bound while the expression subscribed at each hop stays the same
-- two-node flattener, so the quantity every numeric reading tried to
-- bound is not the quantity the subscribe cycle consumes.  That gap
-- is what the marker was emitted into.

-- AND THE THREE FLATTENERS COST ONE CASE BETWEEN THEM, NOT THREE.
-- Cancellation and refusal only REMOVE deliveries and add no
-- subscription, so whatever really governs a switch's currency and an
-- exhaust's acceptance enters as a premise the argument DISCARDS —
-- the bounded and unbounded merges, the switch and the exhaust share
-- one shape, and the exhaust's premise may be stated weaker still.
-- The threaded state is the same story from the other side: quantify
-- the predicate over every state rather than the one a frame
-- subscribed in, and no property of the state is used at all, so
-- nothing depends on a store growing, persisting or being ordered.

-- THE CONSTRAINT TO CARRY BEFORE ANY OF THIS IS BUILT: the delivery
-- family may NOT mention the subscription family.  "A value is only
-- delivered by something that was subscribed" is true of every run
-- and is fatal as a premise — the subscription family already stores
-- a delivery-indexed continuation for its arriving inners, so naming
-- it back puts each family to the left of an arrow in the other and
-- the positivity checker refuses the pair outright, in both
-- directions.  Operational truth about a run belongs in a statement
-- ABOUT a derivation, never among a derivation's own constructors.

-- DEAD ROUTE: threading the hop's provenance in the types instead —
--   indexing a stream by the term whose pipeline produced it, so the
--   arriving observable is structurally related to the subscribed term
--   and the recursion becomes ordinary structural descent.  It is
--   cheaper in volume than these families and it was not taken: the
--   index has to run through `Stream`, `Val` and every frame that
--   moves a value, which is a refactor of the evaluator's own
--   vocabulary rather than an addition beside it, and it cannot be
--   abandoned halfway.  AND IT IS NOW KNOWN TO STOP SHORT OF THE ONE
--   FORMER IT WOULD BE BOUGHT FOR.  The index descends wherever an
--   arriving payload is a SUBTERM of the term that produced it, which
--   is every former but one; a FOLD's payload is its own previous
--   payload re-wrapped, so both sides of the hop carry the same index
--   and the descent is not there.  That is not an accident of the
--   encoding: the fold is the only former whose output is fed back as
--   its own input, which is why a pipeline's depth is a sum along the
--   program and a fold's is a product with a count only the RUN
--   knows.
module Rx.Evaluator.Domain where

open import Data.Bool using (true; false)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _<_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Tick; Fuel; PlainEvent; valueᵖ; completeᵖ; hot; cold)
open import Rx.Exp using (obs; Ctx; Val; Closed; Exp; Tm; Fn; FnClo; applyClo;
  _×ᵗ_; listᵗ; uniqᵗ;
  Env; _∷ᵉ_; []ᵉ; evalWith; unfoldμ; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; deferᵉ; mintᵉ)
open import Rx.Mint using (ordinalᵏ; sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; NodeId;
  root; share-sink; _↠_; shareAdmit; shareLatch; shareFinish;
  from-inner; isFinᵖ;
  arrTick; arrVal; chainsOf; cascadeLatch; cascadeFinish;
  sched-next; sched-init; st-init;
  NodeState; AllOp; RegId; Arrival; AtFloor; arrTy;
  memberSource; register; installNode; resolve;
  atSlot; atDyn; lowerFloor;
  map-f; scan-f; take-f; batchSync-f; thru-outer;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ;
  lookupNode; setNode; hasRoom; switchKill; aliveThroughᶠ; consumeUsable;
  scanStep; takeStep; cutAt; batchSyncPush; batchSyncFlush;
  markOuterDone; markInnerDone; mergeAllPark;
  mergeAllQueue; mergeRoom; mergeAllClaim; mergeAllRestore;
  allFinished; takeSpent)

------------------------------------------------------------------
-- THE DELIVERY CYCLE.  Every family here answers in the ROOT's
-- stream, because a value's whole remaining journey — the frames
-- above it, the shares it fans into, the subscriber at the end — is
-- carried in the path it is handed alongside.  That is what makes a
-- subscription's own re-entry ordinary recursion: what a frame does
-- with a value is finished before the next value exists.
------------------------------------------------------------------

-- ONE VALUE, ENTERING THE PATH AT ITS FOOT.
data emit⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} → Path Γ lo s t → Tick → Val Γ s
   → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e → Set

-- THE END OF A SOURCE, ENTERING THE SAME PATH.  It is a separate
-- family rather than an event column because every frame treats it
-- differently from a value, and several of them answer it by doing
-- work: a bracket flushes, a flattener asks whether anything is still
-- running under it.
data close⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} → Path Γ lo s t → Tick
   → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e → Set

-- SEVERAL VALUES IN ORDER, WHICH IS A SCRIPT'S SYNCHRONOUS PREFIX AND
-- NOTHING ELSE.  It is not a frame's capability: no constructor of
-- `emit⇓` names it, and the only things that do are the source
-- formers that are WRITTEN as a list of values.
data emits⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} → Path Γ lo s t → Tick → List (Val Γ s)
   → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e → Set

data subscribeE⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Val Γ (obs u) → Path Γ lo u t → Tick → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

-- AN INNER OBSERVABLE HAS ARRIVED AT A FLATTENER'S OUTER FRAME.
data consume⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick → Val Γ (obs u)
   → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e → Set

-- A LANE HAS FREED, SO WHATEVER IS PARKED MAY NOW RUN.  The queue is
-- a COLUMN of the relation rather than something each step reads back
-- out of the store, and that is what orders this edge: a drain
-- subscribes, a subscribe runs user code, and user code can park
-- further inners on this very node -- so a store-reading drain walks a
-- list its own walk extends.  Carried, it is an ordinary list and the
-- recursion is structural on it.  Only the merge ever has a nonempty
-- one; the other two are handed `[]`, so their case is the empty arm
-- rather than an operator-specific one.
data drainQueue⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick → List (Val Γ (obs u))
   → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e → Set

data subscribeAll⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeState Γ → Val Γ (obs (obs u)) → Path Γ lo u t
   → Tick → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data sharedConnect⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data subscribeSharedSlot⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE SHARE CYCLE.  The evaluator's second genuine cycle, entered
-- once per delivered chain; its members carry the delivery cycle's
-- derivation too, because a fold re-enters a frame.
------------------------------------------------------------------

data dispatchShare⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n) → lo ≤ toℕ i
   → PlainEvent (Val Γ (lookup Γ i)) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data shareGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n) → PlainEvent (Val Γ (lookup Γ i))
   → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE ARRIVAL SPINE.  Structurally recursive in the evaluator, and
-- related here only because each of these reaches a cycle above and so
-- cannot be applied without a derivation to hand it.
------------------------------------------------------------------

data chainStep⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ) → AtFloor Γ (arrTy a) t → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data cascadeGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ)
   → List (RegId × AtFloor Γ (arrTy a) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data cascade⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Arrival Γ → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data drain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Fuel → Sched Γ → EvalSt e → Stream Γ t → Set

data evaluate⇓ {n} {Γ : Ctx n} {t} :
     Fuel → Closed Γ t → Slots Γ → Stream Γ t → Set

----------------------------------------------------------------------
-- THE CONSTRUCTORS.  One per clause of the function each family
-- mirrors, every recursive call appearing as a sub-derivation.
----------------------------------------------------------------------

-- THE PATH IS WALKED SINKWARD AND WHAT REACHES THE ROOT IS WHAT THE
-- SUBSCRIBER SEES, so the root clause is the only one that emits and
-- every other clause hands its own result on.  The sink clause is
-- where the floor descends: its premise is the path constructor's
-- argument, so nothing has to be carried alongside.
--
-- A HELPER OUTSIDE THE CYCLE IS NAMED IN A PREMISE'S EQUATION RATHER
-- THAN UNFOLDED INTO ARMS, AND THAT IS A CHOICE ABOUT WHAT THIS
-- RELATION IS FOR.  Each stateful frame branches on a node lookup, but
-- none of those branches re-enters the cycle, so relating them
-- separately would add cases the induction never splits on.  What the
-- relation must expose is exactly the recursive structure; a total
-- function of the state is carried as itself, and the equation is what
-- keeps two arms from both applying.
--
-- RECOVERY: git show 234074e:agda/src/Verify-Rank-Sufficient/ restores
--   the CARRIED tower, whose whole subject was the per-frame step: a
--   bound a frame's emissions were held to, stated per template and
--   pushed through a burst.  It is the apparatus to read if a
--   strengthened return type is ever wanted here — what killed it is
--   that the figure was seeded off SYNTAX, which is a property of that
--   tower's currency and not of the per-frame statement it proved.
data emit⇓ {n} {Γ} {t} {e} where

  emit-root : ∀ {lo now} {v : Val Γ t} {sched st}
            → emit⇓ {lo = lo} root now v sched st
                (valueᵖ v ∷ [] , sched , st)

  emit-sink : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
                {v : Val Γ (lookup Γ i)} {sched st r}
            → dispatchShare⇓ now i below (valueᵖ v) sched st r
            → emit⇓ (share-sink i below) now v sched st r

  emit-map : ∀ {s u lo} {fn : FnClo Γ s u} {κ : Path Γ lo u t}
               {now} {v : Val Γ s} {sched st r}
           → emit⇓ κ now (applyClo fn v) sched st r
           → emit⇓ (map-f fn ↠ κ) now v sched st r

  emit-scan : ∀ {s u lo} {fn : FnClo Γ (u ×ᵗ s) u} {nid} {κ : Path Γ lo u t}
                {now} {v : Val Γ s} {sched st} {ac st₁ r}
            → scanStep fn nid v st ≡ (just ac , st₁)
            → emit⇓ κ now ac sched st₁ r
            → emit⇓ (scan-f fn nid ↠ κ) now v sched st r

  emit-scan-stuck : ∀ {s u lo} {fn : FnClo Γ (u ×ᵗ s) u} {nid}
                      {κ : Path Γ lo u t}
                      {now} {v : Val Γ s} {sched st st₁}
                  → scanStep fn nid v st ≡ (nothing , st₁)
                  → emit⇓ (scan-f fn nid ↠ κ) now v sched st
                      ([] , sched , st₁)

  -- THE TRUNCATION PASSES THE VALUE ON AND KEEPS ITS COUNT.
  emit-take-more : ∀ {s lo nid} {κ : Path Γ lo s t}
                     {now} {v : Val Γ s} {sched st st₁ r}
                 → takeStep nid st ≡ (just false , st₁)
                 → emit⇓ κ now v sched st₁ r
                 → emit⇓ (take-f nid ↠ κ) now v sched st r

  -- AND THE LAST ONE OWED LEAVES BEFORE THE CUT, WHICH IS WHAT REAL
  -- `take` DOES: the nth value is emitted and the completion follows
  -- it, mid-burst, without waiting for whatever else the source was
  -- about to produce.
  emit-take-last : ∀ {s lo nid} {κ : Path Γ lo s t}
                     {now} {v : Val Γ s} {sched st st₁}
                     {out sched₁ st₂ sched₂ st₃ out′ sched₃ st₄}
                 → takeStep nid st ≡ (just true , st₁)
                 → emit⇓ κ now v sched st₁ (out , sched₁ , st₂)
                 → cutAt nid sched₁ st₂ ≡ (sched₂ , st₃)
                 → close⇓ κ now sched₂ st₃ (out′ , sched₃ , st₄)
                 → emit⇓ (take-f nid ↠ κ) now v sched st
                     (out ++ out′ , sched₃ , st₄)

  emit-take-spent : ∀ {s lo nid} {κ : Path Γ lo s t}
                      {now} {v : Val Γ s} {sched st st₁}
                  → takeStep nid st ≡ (nothing , st₁)
                  → emit⇓ (take-f nid ↠ κ) now v sched st
                      ([] , sched , st₁)

  -- THE BRACKET, ARRIVING SIDE.  While the node's bit is up nothing
  -- leaves at all; once it is down each value leaves as its own group
  -- of one.  Which of the two happened is the helper's answer, so the
  -- two arms are told apart by its equation rather than by a test
  -- stated here.
  emit-batchSync : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                     {now} {v : Val Γ s} {sched st g st₁ r}
                 → batchSyncPush nid v st ≡ (just g , st₁)
                 → emit⇓ κ now g sched st₁ r
                 → emit⇓ (batchSync-f nid ↠ κ) now v sched st r

  emit-batchSync-held : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                          {now} {v : Val Γ s} {sched st st₁}
                      → batchSyncPush nid v st ≡ (nothing , st₁)
                      → emit⇓ (batchSync-f nid ↠ κ) now v sched st
                          ([] , sched , st₁)

  -- LEAVING A SUBSCRIBED INNER IS FREE, and it is the completion side
  -- of this frame that does all the work.
  emit-from-inner : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                      {now} {v : Val Γ s} {sched st r}
                  → emit⇓ κ now v sched st r
                  → emit⇓ (from-inner op allNid inst ↠ κ) now v sched st r

  emit-thru-outer : ∀ {u lo op nid} {κ : Path Γ lo u t}
                      {now} {o : Val Γ (obs u)} {sched st r}
                  → consume⇓ op nid κ now o sched st r
                  → emit⇓ (thru-outer op nid ↠ κ) now o sched st r

data close⇓ {n} {Γ} {t} {e} where

  close-root : ∀ {lo now sched st}
             → close⇓ {s = t} {lo = lo} root now sched st
                 (completeᵖ ∷ [] , sched , st)

  close-sink : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i} {sched st r}
             → dispatchShare⇓ now i below completeᵖ sched st r
             → close⇓ (share-sink i below) now sched st r

  close-map : ∀ {s u lo} {fn : FnClo Γ s u} {κ : Path Γ lo u t}
                {now sched st r}
            → close⇓ κ now sched st r
            → close⇓ (map-f fn ↠ κ) now sched st r

  close-scan : ∀ {s u lo} {fn : FnClo Γ (u ×ᵗ s) u} {nid}
                 {κ : Path Γ lo u t} {now sched st r}
             → close⇓ κ now sched st r
             → close⇓ (scan-f fn nid ↠ κ) now sched st r

  -- A SPENT TRUNCATION IS SILENT, because it has already cut: the
  -- registrations under it are severed and its own completion has
  -- gone rootward, and in rxjs an unsubscribed chain delivers
  -- nothing.
  close-take-spent : ∀ {s lo nid} {κ : Path Γ lo s t} {now sched st}
                   → takeSpent nid st ≡ true
                   → close⇓ (take-f nid ↠ κ) now sched st ([] , sched , st)

  close-take : ∀ {s lo nid} {κ : Path Γ lo s t} {now sched st r}
             → takeSpent nid st ≡ false
             → close⇓ κ now sched st r
             → close⇓ (take-f nid ↠ κ) now sched st r

  -- THE BRACKET, CLOSING SIDE, AND THE FLUSH COMES FIRST.  A source
  -- that completes inside the subscribe call must still deliver what
  -- it buffered, and it must deliver it BEFORE the completion — which
  -- is the order the TypeScript's merged flush produces, since its
  -- second input is subscribed while the first has only just
  -- finished.
  close-batchSync : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                      {now sched st g st₁}
                      {out sched₁ st₂ out′ sched₂ st₃}
                  → batchSyncFlush {s = s} nid st ≡ (just g , st₁)
                  → emit⇓ κ now g sched st₁ (out , sched₁ , st₂)
                  → close⇓ κ now sched₁ st₂ (out′ , sched₂ , st₃)
                  → close⇓ (batchSync-f nid ↠ κ) now sched st
                      (out ++ out′ , sched₂ , st₃)

  close-batchSync-empty : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                            {now sched st st₁ r}
                        → batchSyncFlush {s = s} nid st ≡ (nothing , st₁)
                        → close⇓ κ now sched st₁ r
                        → close⇓ (batchSync-f nid ↠ κ) now sched st r

  -- AN INNER'S COMPLETION IS ABSORBED WHILE ANYTHING UNDER THIS
  -- INSTANCE IS STILL LIVE, which is the one reading of the registry
  -- a frame makes.
  close-inner-absorb : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                         {now sched st}
                     → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true
                     → close⇓ (from-inner op allNid inst ↠ κ) now sched st
                         ([] , sched , st)

  -- OTHERWISE THE LANE IS RELEASED, WHATEVER IS PARKED IS RUN, AND
  -- ONLY THEN IS THE OPERATOR ASKED WHETHER IT IS FINISHED.  The
  -- question is asked of the store the drain LEFT, because a lane
  -- freed here is refilled there and a verdict taken before the drain
  -- would be a verdict about a store that no longer stands.
  close-inner-done : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                       {now sched st} {q st₀ out sched₁ st₁ out′ sched₂ st₂}
                   → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
                   → mergeAllQueue {s = s} allNid
                       (markInnerDone op allNid inst st) ≡ (q , st₀)
                   → drainQueue⇓ op allNid κ now q sched st₀
                       (out , sched₁ , st₁)
                   → allFinished op allNid st₁ ≡ true
                   → close⇓ κ now sched₁ st₁ (out′ , sched₂ , st₂)
                   → close⇓ (from-inner op allNid inst ↠ κ) now sched st
                       (out ++ out′ , sched₂ , st₂)

  close-inner-open : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                       {now sched st} {q st₀ out sched₁ st₁}
                   → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
                   → mergeAllQueue {s = s} allNid
                       (markInnerDone op allNid inst st) ≡ (q , st₀)
                   → drainQueue⇓ op allNid κ now q sched st₀
                       (out , sched₁ , st₁)
                   → allFinished op allNid st₁ ≡ false
                   → close⇓ (from-inner op allNid inst ↠ κ) now sched st
                       (out , sched₁ , st₁)

  -- THE OUTER HAS FINISHED, and an `*All` outlives it for exactly as
  -- long as something is still running underneath.
  close-outer-done : ∀ {u lo op nid} {κ : Path Γ lo u t} {now sched st r}
                   → allFinished op nid (markOuterDone op nid st) ≡ true
                   → close⇓ κ now sched (markOuterDone op nid st) r
                   → close⇓ (thru-outer op nid ↠ κ) now sched st r

  close-outer-open : ∀ {u lo op nid} {κ : Path Γ lo u t} {now sched st}
                   → allFinished op nid (markOuterDone op nid st) ≡ false
                   → close⇓ (thru-outer op nid ↠ κ) now sched st
                       ([] , sched , markOuterDone op nid st)

data emits⇓ {n} {Γ} {t} {e} where

  emits-nil : ∀ {s lo} {κ : Path Γ lo s t} {now sched st}
            → emits⇓ κ now [] sched st ([] , sched , st)

  emits-cons : ∀ {s lo} {κ : Path Γ lo s t} {now} {v : Val Γ s} {vs}
                 {sched st out sched₁ st₁ out′ sched₂ st₂}
             → emit⇓ κ now v sched st (out , sched₁ , st₁)
             → emits⇓ κ now vs sched₁ st₁ (out′ , sched₂ , st₂)
             → emits⇓ κ now (v ∷ vs) sched st
                 (out ++ out′ , sched₂ , st₂)

-- THE SLOT TESTS STAY PREMISES AND THE SCRIPT'S OWN WELL-FORMEDNESS
-- WITNESS IS BOUND RATHER THAN LEFT TO INFERENCE.  A slot's constructor
-- carries a proof that the element type is data, or that a shared def's
-- inputs sit below the slot; at a variable type neither reduces, so an
-- unwritten one is an unsolved meta and a build failure.  Binding it
-- costs a name and asserts nothing, which is the right trade: the
-- relation is about which arm ran, never about why the slot is legal.
data subscribeE⇓ {n} {Γ} {t} {e} where

  subs-floor : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                 {Θ ρ} {now sched st r}
             → lo ≤ toℕ i
             → close⇓ κ now sched st r
             → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-shared : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                  {below : toℕ i < lo} {ok} {Θ ρ} {now sched st r}
              → Sched.slots sched i ≡ shared d {ok = ok}
              → subscribeSharedSlot⇓ i d κ below now sched st r
              → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-hot-done : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {Θ ρ} {now sched st r}
                → toℕ i < lo
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
                → close⇓ κ now sched st r
                → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-hot-live : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {Θ ρ} {now sched st rid}
                → (below : toℕ i < lo)
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
                → freshId regᵏ (Sched.mint sched) ≡ rid
                → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                    ( []
                    , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                    , register rid (atSlot i) (lowerFloor below κ) st )

  -- A COLD IS `new Observable()`: A FRESH INDEPENDENT RUN PER
  -- SUBSCRIBER, ITS SYNCHRONOUS PREFIX REPLAYED INTO THE SUBSCRIBE
  -- FRAME.  With no asynchronous tail the run is over as it starts,
  -- so the prefix is followed by the end and nothing is registered.
  subs-cold-sync : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                     {ok sync} {Θ ρ} {now sched st}
                     {out sched₁ st₁ out′ sched₂ st₂}
                 → toℕ i < lo
                 → Sched.slots sched i ≡ scripted {ok = ok} (cold sync [])
                 → emits⇓ κ now sync sched st (out , sched₁ , st₁)
                 → close⇓ κ now sched₁ st₁ (out′ , sched₂ , st₂)
                 → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                     (out ++ out′ , sched₂ , st₂)

  -- AND WITH A TAIL THE REGISTRATION IS MADE BEFORE THE PREFIX IS
  -- REPLAYED, NOT AFTER.  A synchronous value can cut this very
  -- chain, and a cut severs REGISTRATIONS — so a source registered
  -- afterwards would go on delivering into something nothing reads.
  subs-cold-async : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                      {ok sync d ds} {Θ ρ} {now sched st src ord rid r}
                  → toℕ i < lo
                  → Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                  → freshId sourceᵏ (Sched.mint sched) ≡ src
                  → freshId ordinalᵏ (Sched.mint sched) ≡ ord
                  → freshId regᵏ (Sched.mint sched) ≡ rid
                  → emits⇓ κ now sync
                      (record sched
                         { mint = setAt regᵏ (suc rid)
                                    (setAt sourceᵏ (suc src)
                                      (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                         ; live = record { source = src ; ordinal = ord
                                         ; elemTy = lookup Γ i
                                         ; pending = resolve now (d ∷ ds) }
                                  ∷ Sched.live sched })
                      (register rid (atDyn src lo) κ st)
                      r
                  → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-of : ∀ {lo u Θ} {ts} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
              {now sched st out sched₁ st₁ out′ sched₂ st₂}
          → emits⇓ κ now (map (λ tm → evalWith tm ρ) ts) sched st
              (out , sched₁ , st₁)
          → close⇓ κ now sched₁ st₁ (out′ , sched₂ , st₂)
          → subscribeE⇓ (Θ , ofᵉ ts , ρ) κ now sched st
              (out ++ out′ , sched₂ , st₂)

  subs-empty : ∀ {lo u Θ} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
                 {now sched st r}
             → close⇓ κ now sched st r
             → subscribeE⇓ (Θ , emptyᵉ , ρ) κ now sched st r

  -- `take(0)` NEVER SUBSCRIBES ITS SOURCE, which was measured rather
  -- than assumed: the operator completes on subscription and the
  -- source is not touched at all.
  subs-take-zero : ∀ {lo u Θ} {ρ : Env Γ Θ} {count} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo u t} {now sched st r}
                 → evalWith count ρ ≡ zero
                 → close⇓ κ now sched st r
                 → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st r

  subs-take-suc : ∀ {lo u Θ} {ρ : Env Γ Θ} {count k} {b : Exp Γ [] [] Θ u}
                    {κ : Path Γ lo u t} {now sched st nid r}
                → evalWith count ρ ≡ suc k
                → freshId nodeᵏ (Sched.mint sched) ≡ nid
                → subscribeE⇓ (Θ , b , ρ) (take-f nid ↠ κ) now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                    (installNode nid (take-st (suc k)) st)
                    r
                → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st r

  -- THE BRACKET IS OPENED BY THE INSTALL AND CLOSED BY THE FLUSH, AND
  -- THE FLUSH SITS AFTER THE SUBSCRIBE CALL RETURNS — which is where
  -- the TypeScript's merged second input is subscribed.  A body that
  -- completed inside the call has already been flushed by its own
  -- completion, so what this finds is an empty buffer and no value
  -- leaves twice.
  subs-batchSync : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo (u ×ᵗ listᵗ u) t}
                     {now sched st nid out sched₁ st₁ g st₂}
                     {out′ sched₂ st₃}
                 → freshId nodeᵏ (Sched.mint sched) ≡ nid
                 → subscribeE⇓ (Θ , b , ρ) (batchSync-f nid ↠ κ) now
                     (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                     (installNode nid (batchSync-st {t = u} true []) st)
                     (out , sched₁ , st₁)
                 → batchSyncFlush {s = u} nid st₁ ≡ (just g , st₂)
                 → emit⇓ κ now g sched₁ st₂ (out′ , sched₂ , st₃)
                 → subscribeE⇓ (Θ , batchSyncᵉ b , ρ) κ now sched st
                     (out ++ out′ , sched₂ , st₃)

  subs-batchSync-empty : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                           {κ : Path Γ lo (u ×ᵗ listᵗ u) t}
                           {now sched st nid out sched₁ st₁ st₂}
                       → freshId nodeᵏ (Sched.mint sched) ≡ nid
                       → subscribeE⇓ (Θ , b , ρ) (batchSync-f nid ↠ κ) now
                           (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                           (installNode nid (batchSync-st {t = u} true []) st)
                           (out , sched₁ , st₁)
                       → batchSyncFlush {s = u} nid st₁ ≡ (nothing , st₂)
                       → subscribeE⇓ (Θ , batchSyncᵉ b , ρ) κ now sched st
                           (out , sched₁ , st₂)

  -- A MAP INSTALLS NOTHING, WHICH IS WHY THIS ARM IS SHORTER THAN
  -- EVERY OTHER SUBSCRIBE ARM HERE.  There is no node to mint, so no
  -- freshness premise and no advanced mint in the recursive call: the
  -- frame is pushed onto the path and the subscription runs under it.
  subs-map : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f : Fn Γ [] [] Θ s u}
               {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
               {now sched st r}
           → subscribeE⇓ (Θ , b , ρ) (map-f (Θ , f , ρ) ↠ κ) now sched st r
           → subscribeE⇓ (Θ , mapᵉ f b , ρ) κ now sched st r

  subs-scan : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f} {i : Tm Γ [] [] Θ u}
                {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
                {now sched st nid r}
            → freshId nodeᵏ (Sched.mint sched) ≡ nid
            → subscribeE⇓ (Θ , b , ρ) (scan-f (Θ , f , ρ) nid ↠ κ) now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (cell-st (evalWith i ρ)) st)
                r
            → subscribeE⇓ (Θ , scanᵉ f i b , ρ) κ now sched st r

  subs-merge-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {lim} {b : Exp Γ [] [] Θ (obs u)}
                     {κ : Path Γ lo u t} {now sched st r}
                 → subscribeAll⇓ mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false)
                     (Θ , b , ρ) κ now sched st r
                 → subscribeE⇓ (Θ , mergeAllᵉ lim b , ρ) κ now sched st r

  subs-switch-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ (obs u)}
                      {κ : Path Γ lo u t} {now sched st r}
                  → subscribeAll⇓ switchᵒ (switch-st nothing false)
                      (Θ , b , ρ) κ now sched st r
                  → subscribeE⇓ (Θ , switchAllᵉ b , ρ) κ now sched st r

  subs-exhaust-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ (obs u)}
                       {κ : Path Γ lo u t} {now sched st r}
                   → subscribeAll⇓ exhaustᵒ (exhaust-st false false)
                       (Θ , b , ρ) κ now sched st r
                   → subscribeE⇓ (Θ , exhaustAllᵉ b , ρ) κ now sched st r

  -- THE SECOND DRY ARM, AND THE ONE THE RELATION CANNOT EVEN ASK ABOUT.
  -- The machine compares the unfolding's synchronous size against a
  -- number it was handed by its caller, and answers the negative case
  -- dry.  That number is threaded alongside every argument and is a
  -- function of none of them, so it is not among this relation's
  -- indices and no premise here could pin it.  The constructor is
  -- therefore unconditional, and that concedes nothing: the relation is
  -- spent only in the direction that builds a derivation AT THE
  -- MACHINE'S OWN RESULT, and at a run that answered dry the result is
  -- a dry burst, which no constructor of this family produces.  So the
  -- comparison is still owed — it is owed by the inhabitation proof,
  -- which is where the measure belongs, since the unfolding is larger
  -- than the term it replaces and nothing here is structural in it.
  subs-μ : ∀ {lo u Θ} {ρ : Env Γ Θ} {body} {κ : Path Γ lo u t}
             {now sched st r}
         → subscribeE⇓ (Θ , unfoldμ body , ρ) κ now sched st r
         → subscribeE⇓ (Θ , μᵉ body , ρ) κ now sched st r

  subs-defer : ∀ {lo u Θ} {ρ : Env Γ Θ} {body} {κ : Path Γ lo u t}
                 {now sched st nid src ord rid}
             → freshId nodeᵏ (Sched.mint sched) ≡ nid
             → freshId sourceᵏ (Sched.mint sched) ≡ src
             → freshId ordinalᵏ (Sched.mint sched) ≡ ord
             → freshId regᵏ (Sched.mint sched) ≡ rid
             → subscribeE⇓ (Θ , deferᵉ body , ρ) κ now sched st
                 ( []
                 , record sched
                     { mint = setAt regᵏ (suc rid)
                                (setAt nodeᵏ (suc nid)
                                  (setAt sourceᵏ (suc src)
                                    (setAt ordinalᵏ (suc ord) (Sched.mint sched))))
                     ; live = record { source = src ; ordinal = ord
                                     ; elemTy = obs u
                                     ; pending = (suc now , (Θ , body , ρ)) ∷ [] }
                              ∷ Sched.live sched }
                 , register rid (atDyn src lo)
                            (thru-outer mergeAllᵒ nid ↠ κ)
                            (installNode nid
                              (mergeAll-st {t = u} nothing 0 [] false) st) )

  -- MINTING IS THE RUN'S, AND THE BODY RECEIVES THE TOKEN AS A VALUE.
  -- The hop allocates at the same key `subs-defer` draws from and then
  -- EXTENDS THE ENVIRONMENT with the identifier, so the premise is a
  -- subscription of the same body under one more token.  The binder is
  -- the only thing in the tree that lengthens the telescope, which is
  -- why every other arm passes its environment down untouched.  That
  -- is the whole of the rule: no event, no registration and no node,
  -- because
  -- the operator this serves is the one WRAPPING the binder and it is
  -- the operator that owes those.  A token the body could have written
  -- for itself would need no rule at all -- the point is that it
  -- cannot, so the value can only arrive from here.
  subs-mint : ∀ {lo u Θ} {ρ : Env Γ Θ} {body : Exp Γ [] [] (uniqᵗ ∷ Θ) u}
                {κ : Path Γ lo u t} {now sched st src r}
            → freshId sourceᵏ (Sched.mint sched) ≡ src
            → subscribeE⇓ (uniqᵗ ∷ Θ , body , src ∷ᵉ ρ) κ now
                (record sched
                   { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
                st r
            → subscribeE⇓ (Θ , mintᵉ body , ρ) κ now sched st r

-- THE LANE IS TAKEN BEFORE THE SUBSCRIBE, NOT AFTER IT, AND THAT IS
-- WHAT A PER-VALUE MACHINE FORCES.  An inner that completes inside its
-- own subscribe call releases its lane on the way back up, so a count
-- raised afterwards would be raised against a release that already
-- happened — the same reasoning that puts a switch's current instance
-- in the node before the call rather than after.  It is also what rxjs
-- does: `mergeMap` takes the slot, then subscribes.
data consume⇓ {n} {Γ} {t} {e} where

  consume-merge-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                        {o : Val Γ (obs u)} {sched st} {lim act q od}
                        {inst r}
                    → lookupNode nid (EvalSt.nodes st)
                        ≡ just (mergeAll-st {t = u} lim act q od)
                    → hasRoom lim act ≡ true
                    → freshId nodeᵏ (Sched.mint sched) ≡ inst
                    → subscribeE⇓ o (from-inner mergeAllᵒ nid inst ↠ κ) now
                        (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) })
                        (record st { nodes = setNode nid
                            (mergeAll-st lim (suc act) q od) (EvalSt.nodes st) })
                        r
                    → consume⇓ mergeAllᵒ nid κ now o sched st r

  -- A SATURATED MERGE QUEUES THE OBSERVABLE, WHICH IS WHAT rxjs
  -- QUEUES.  A full lane has subscribed nothing, so there are no
  -- values to hold and nothing to hold them for.
  consume-merge-park : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched st} {lim act q od}
                     → lookupNode nid (EvalSt.nodes st)
                         ≡ just (mergeAll-st {t = u} lim act q od)
                     → hasRoom lim act ≡ false
                     → consume⇓ mergeAllᵒ nid κ now o sched st
                         ([] , sched , mergeAllPark nid o st)

  consume-merge-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                        {o : Val Γ (obs u)} {sched st}
                    → consumeUsable mergeAllᵒ u (lookupNode nid (EvalSt.nodes st))
                        ≡ false
                    → consume⇓ mergeAllᵒ nid κ now o sched st ([] , sched , st)

  consume-switch-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched st} {cur od}
                         {sched₁ st₁ inst r}
                     → lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od)
                     → switchKill cur sched st ≡ (sched₁ , st₁)
                     → freshId nodeᵏ (Sched.mint sched₁) ≡ inst
                     → subscribeE⇓ o (from-inner switchᵒ nid inst ↠ κ) now
                         (record sched₁ { mint = setAt nodeᵏ (suc inst) (Sched.mint sched₁) })
                         (record st₁ { nodes = setNode nid
                             (switch-st (just inst) od) (EvalSt.nodes st₁) })
                         r
                     → consume⇓ switchᵒ nid κ now o sched st r

  consume-switch-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched st}
                     → consumeUsable switchᵒ u (lookupNode nid (EvalSt.nodes st))
                         ≡ false
                     → consume⇓ switchᵒ nid κ now o sched st ([] , sched , st)

  consume-exhaust-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {sched st} {od} {inst r}
                      → lookupNode nid (EvalSt.nodes st)
                          ≡ just (exhaust-st false od)
                      → freshId nodeᵏ (Sched.mint sched) ≡ inst
                      → subscribeE⇓ o (from-inner exhaustᵒ nid inst ↠ κ) now
                          (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) })
                          (record st { nodes = setNode nid
                              (exhaust-st true od) (EvalSt.nodes st) })
                          r
                      → consume⇓ exhaustᵒ nid κ now o sched st r

  -- A BUSY EXHAUST REFUSES THE ARRIVAL OUTRIGHT, and the refusal is
  -- the same reading as a mistyped or absent node: forward nothing.
  consume-exhaust-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {sched st}
                      → consumeUsable exhaustᵒ u (lookupNode nid (EvalSt.nodes st))
                          ≡ false
                      → consume⇓ exhaustᵒ nid κ now o sched st ([] , sched , st)

-- THE LANE IS CLAIMED BEFORE THE SUBSCRIBE AND THE ROOM IS ASKED
-- AGAIN AT EVERY STEP.  Both halves are the same reading: an inner
-- can complete synchronously inside the subscribe, so a verdict about
-- free lanes taken once at the top is a verdict about a store that no
-- longer stands by the second item — and a lane counted as filled
-- only afterwards would be decremented by that death before it was
-- ever raised.
data drainQueue⇓ {n} {Γ} {t} {e} where

  dq-nil : ∀ {u lo op nid} {κ : Path Γ lo u t} {now sched st}
         → drainQueue⇓ op nid κ now [] sched st ([] , sched , st)

  -- THE LANES REFILLED WHILE THE DRAIN RAN, so what it did not reach
  -- goes back in front of whatever parked behind it.
  dq-full : ∀ {u lo op nid} {κ : Path Γ lo u t} {now sched st}
              {o : Val Γ (obs u)} {q}
          → mergeRoom nid st ≡ false
          → drainQueue⇓ op nid κ now (o ∷ q) sched st
              ([] , sched , mergeAllRestore nid (o ∷ q) st)

  dq-run : ∀ {u lo op nid} {κ : Path Γ lo u t} {now sched st}
             {o : Val Γ (obs u)} {q inst out sched₁ st₂ out′ sched₂ st₃}
         → mergeRoom nid st ≡ true
         → freshId nodeᵏ (Sched.mint sched) ≡ inst
         → subscribeE⇓ o (from-inner op nid inst ↠ κ) now
             (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) })
             (mergeAllClaim nid st) (out , sched₁ , st₂)
         → drainQueue⇓ op nid κ now q sched₁ st₂ (out′ , sched₂ , st₃)
         → drainQueue⇓ op nid κ now (o ∷ q) sched st
             (out ++ out′ , sched₂ , st₃)

data subscribeAll⇓ {n} {Γ} {t} {e} where

  sub-all : ∀ {u lo op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
              {κ : Path Γ lo u t} {now sched st nid r}
          → freshId nodeᵏ (Sched.mint sched) ≡ nid
          → subscribeE⇓ b (thru-outer op nid ↠ κ) now
              (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
              (installNode nid ns st)
              r
          → subscribeAll⇓ op ns b κ now sched st r

-- THE CONNECT IS ONE ARM, AND THE SECOND ONE WENT WITH THE LIST.  A
-- def that completes synchronously used to be told apart by READING
-- its returned burst for an end; the connect's output is the root's
-- stream now, where an end is the ROOT's and not the share's.  It
-- needs no telling: a def completing inside its own subscribe routes
-- through the sink's close, which latches the share and drops its
-- registrations exactly as the second arm did.
--
-- THE THIRD GUARD THE RELATION DOES NOT INDEX, AND THE SAME RULING AS
-- THE UNFOLD'S.  The connect compares the unconnected-share count
-- against a component of the caller's own measure, which is threaded
-- alongside every argument and is a function of none of them — so it is
-- not among these indices and no premise could pin it.  The
-- constructor is therefore unconditional in it, and that concedes
-- nothing: at a run that answered no, the result is a dry burst, which
-- no constructor of this family produces, so the comparison stays owed
-- by the inhabitation proof rather than being assumed away here.
data sharedConnect⇓ {n} {Γ} {t} {e} where

  connect : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
              {below : toℕ i < lo} {now sched st rid r}
          → freshId regᵏ (Sched.mint sched) ≡ rid
          → subscribeE⇓ ([] , d , []ᵉ) (share-sink i ≤-refl) now
              (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
              (register rid (atSlot i) (lowerFloor below κ)
                (record st
                  { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
              r
          → sharedConnect⇓ i d κ below now sched st r

data subscribeSharedSlot⇓ {n} {Γ} {t} {e} where

  slot-spent : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                 {below : toℕ i < lo} {now sched st r}
             → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
             → close⇓ κ now sched st r
             → subscribeSharedSlot⇓ i d κ below now sched st r

  slot-join : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                {below : toℕ i < lo} {now sched st rid}
            → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
            → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ true
            → freshId regᵏ (Sched.mint sched) ≡ rid
            → subscribeSharedSlot⇓ i d κ below now sched st
                ( []
                , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                , register rid (atSlot i) (lowerFloor below κ) st )

  slot-connect : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {now sched st r}
               → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
               → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false
               → sharedConnect⇓ i d κ below now sched st r
               → subscribeSharedSlot⇓ i d κ below now sched st r

-- THE ONE CLAUSE, and the whole reason the share cycle is separate: the
-- fan-out re-enters at the floor the sink's own premise names, so the
-- relation carries that premise as a constructor argument and the
-- descent it buys is a fact about the index rather than a peeled
-- witness.  `shareFinish`, `shareAdmit` and `shareLatch` compute, so
-- they stay applied.
data dispatchShare⇓ {n} {Γ} {t} {e} where
  disp : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
           {ev : PlainEvent (Val Γ (lookup Γ i))} {sched st r}
       → shareGo⇓ now i ev
           (shareAdmit i (EvalSt.registry st)) sched (shareLatch i (isFinᵖ ev) st) r
       → dispatchShare⇓ now i below ev sched st (shareFinish i (isFinᵖ ev) r)

-- THE CANCELLATION TEST STAYS A PREMISE RATHER THAN A SIDE CONDITION.
-- It is decidable and it decides which of two clauses ran, so the
-- relation carries the answer as an equation and the two arms cannot
-- both apply.  The live arms are where the threading shows: what the
-- tail is handed is the head's own results, which is why this is a
-- graph relation and not a domain predicate.
data shareGo⇓ {n} {Γ} {t} {e} where
  go-nil : ∀ {lo now} {i : Fin n} {ev sched st}
         → shareGo⇓ {lo = lo} now i ev [] sched st ([] , sched , st)

  go-cut : ∀ {lo now} {i : Fin n} {ev rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st r}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
         → shareGo⇓ now i ev ps sched st r
         → shareGo⇓ now i ev ((rid , p) ∷ ps) sched st r

  go-val : ∀ {lo now} {i : Fin n} {v : Val Γ (lookup Γ i)} {rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st}
             {emits sched₁ st₁ rest sched₂ st₂}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
         → emit⇓ p now v sched
             (record st { delivered = rid ∷ EvalSt.delivered st })
             (emits , sched₁ , st₁)
         → shareGo⇓ now i (valueᵖ v) ps sched₁ st₁ (rest , sched₂ , st₂)
         → shareGo⇓ now i (valueᵖ v) ((rid , p) ∷ ps) sched st
             (emits ++ rest , sched₂ , st₂)

  go-fin : ∀ {lo now} {i : Fin n} {rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st}
             {emits sched₁ st₁ rest sched₂ st₂}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
         → close⇓ p now sched
             (record st { delivered = rid ∷ EvalSt.delivered st })
             (emits , sched₁ , st₁)
         → shareGo⇓ now i completeᵖ ps sched₁ st₁ (rest , sched₂ , st₂)
         → shareGo⇓ now i completeᵖ ((rid , p) ∷ ps) sched st
             (emits ++ rest , sched₂ , st₂)

-- A SCRIPTED SOURCE'S LAST VALUE IS FOLLOWED BY ITS END, IN THAT
-- ORDER AND DOWN THE SAME CHAIN.  The end used to ride alongside the
-- value as a flag a frame read; a plain carrier has two separate
-- things to deliver, and delivering them in order is what an rxjs
-- observer sees.
data chainStep⇓ {n} {Γ} {t} {e} where
  chain-more : ∀ {a : Arrival Γ} {lo} {path : Path Γ lo (arrTy a) t}
                 {sched st r}
             → Arrival.isLast a ≡ false
             → emit⇓ path (arrTick a) (arrVal a) sched st r
             → chainStep⇓ a (lo , path) sched st r

  chain-last : ∀ {a : Arrival Γ} {lo} {path : Path Γ lo (arrTy a) t}
                 {sched st out sched₁ st₁ out′ sched₂ st₂}
             → Arrival.isLast a ≡ true
             → emit⇓ path (arrTick a) (arrVal a) sched st (out , sched₁ , st₁)
             → close⇓ path (arrTick a) sched₁ st₁ (out′ , sched₂ , st₂)
             → chainStep⇓ a (lo , path) sched st
                 (out ++ out′ , sched₂ , st₂)

data cascadeGo⇓ {n} {Γ} {t} {e} where
  casc-nil : ∀ {a sched st}
           → cascadeGo⇓ a [] sched st ([] , sched , st)
  casc-cut : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains sched st r}
           → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
           → cascadeGo⇓ a chains sched st r
           → cascadeGo⇓ a ((rid , c) ∷ chains) sched st r
  casc-live : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains sched st}
                {emits sched₁ st₁ rest sched₂ st₂}
            → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
            → chainStep⇓ a c sched
                (record st { delivered = rid ∷ EvalSt.delivered st })
                (emits , sched₁ , st₁)
            → cascadeGo⇓ a chains sched₁ st₁ (rest , sched₂ , st₂)
            → cascadeGo⇓ a ((rid , c) ∷ chains) sched st
                (emits ++ rest , sched₂ , st₂)

data cascade⇓ {n} {Γ} {t} {e} where
  casc-run : ∀ {a sched st} {emits sched′ st′}
           → cascadeGo⇓ a (chainsOf a st) sched (cascadeLatch a sched st)
               (emits , sched′ , st′)
           → cascade⇓ a sched st (emits , cascadeFinish a sched′ st′)

data drain⇓ {n} {Γ} {t} {e} where
  drain-done : ∀ {sched st}
             → drain⇓ zero sched st []
  drain-empty : ∀ {k sched st}
              → sched-next sched ≡ inj₁ tt
              → drain⇓ (suc k) sched st []
  drain-step : ∀ {k sched st} {a : Arrival Γ}
                 {sched′ out sched″ st′ rest}
             → sched-next sched ≡ inj₂ (a , sched′)
             → cascade⇓ a sched′ st (out , sched″ , st′)
             → drain⇓ k sched″ st′ rest
             → drain⇓ (suc k) sched st (out ++ rest)

data evaluate⇓ {n} {Γ} {t} where
  eval-run : ∀ {fuel} {e : Closed Γ t} {ins : Slots Γ}
               {burst sched₀ st₀ rest}
           → subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
               (sched-init e ins) (st-init e) (burst , sched₀ , st₀)
           → drain⇓ {e = e} fuel sched₀ st₀ rest
           → evaluate⇓ fuel e ins (burst ++ rest)
