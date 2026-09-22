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

open import Data.Bool using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; null)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; pred; _<_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Tick; Fuel; valueᵖ; completeᵖ; hot; cold)
open import Rx.Exp using (obs; Ctx; Val; Closed; Exp; Tm; Fn; FnClo; applyClo;
  _×ᵗ_; listᵗ; uniqᵗ;
  Env; _∷ᵉ_; []ᵉ; evalWith; unfoldμ; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; deferᵉ; mintᵉ)
open import Rx.Mint using (ordinalᵏ; sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; NodeId;
  W; Pushed; Subbed; root; share-sink; _↠[_]_; shareAdmit;
  shareLatch; shareFinish; from-inner; arrTick; arrVal; chainsOf; cascadeLatch;
  cascadeFinish; sched-next; sched-init;
  st-init; NodeState; AllOp; RegId; Arrival; AtFloor; arrTy; memberSource; register;
  installNode; resolve; atSlot; atDyn; lowerFloor; map-f; scan-f; take-f;
  batchSync-f; thru-outer; cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ; lookupNode; setNode; hasRoom; mergeAllBump; switchKill;
  aliveThroughᶠ; scanDispatch; takeDispatch; batchTake; batchStep; batchVals;
  thruWrap; allDone; consumeUsable; finishUsable)

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE.  Thirteen families, exactly the members of the
-- evaluator's larger genuine cycle: everything else it calls is
-- structurally recursive and is APPLIED here rather than related.
--
-- A SUBSCRIPTION PUSHES, AND THAT IS THE ONE STRUCTURAL FACT THE WHOLE
-- FILE RESTS ON.  What every clause carries in and out is the world a
-- push threads -- what has reached the ROOT so far, beside the schedule
-- and the state -- and what it reports back is a single bit.  So a
-- reaction to a value runs while its source is still emitting, which is
-- what an rxjs observer sees and what a carrier handing its caller a
-- finished list could not express.
--
-- THE TWO BITS ARE ASKED BY OPPOSITE SIDES, which is why they are named
-- apart though they are the same type.  ALIVE is the SOURCE's question:
-- a truncation that cuts mid-emission unsubscribes its source, so a
-- synchronous source pushing value by value has to stop.  DONE is the
-- CONSUMER's: whether a completion left this subscription.
------------------------------------------------------------------

-- A SHARE IS WHERE THE LIST CARRIER WAS REFUTED, and that refutation is
-- what the push is bought with.  A list is sound exactly while a
-- downstream reaction cannot change what the source still owes, and a
-- share is where it can: a value delivered to a subscriber may
-- SUBSCRIBE that same share, and rxjs re-reads the subject's observer
-- list between every pair of values, so the joiner receives the rest of
-- the emission.  Harvesting it whole makes the fan-out SUBSCRIBER-MAJOR
-- where rxjs is VALUE-MAJOR, and the two agree up to three values and
-- part at four: a share of `of` read by a `mergeAll` of itself yields
-- 2,3,4,3,4,4 against rxjs's 2,3,3,4,4,4.

-- THE REGION IS THREE CONDITIONS AT ONCE, AND DROPPING ANY ONE OF THEM
-- RESTORED AGREEMENT -- which is what the neighbours drawn around the
-- oracle's pinned corpus row measured, rather than what reading the
-- clauses suggested.  There must be (i) a SHARE, (ii) a SYNCHRONOUS
-- emission of two or more values through it, and (iii) a subscription
-- to THAT share caused by one of those values.  The predicate is
-- `typescript/src/region.ts`, counted on every draw so that a draw
-- which stops reaching the region fails loudly rather than reading as a
-- stronger green.
--
-- Each condition has its own witness.  For (i): the identical program
-- over a scripted cold of the same two sync values agrees, so it is the
-- sharing and not the emission length or the flattener; and a HOT, the
-- other source many subscribers share, agrees too, because its values
-- arrive one per cascade and the cascade fan-out re-reads the registry
-- per arrival.  For (ii): one sync value agrees, and one sync value
-- plus an async tail agrees.  For (iii): the same share read through
-- `scan`, through `take`, through a `batchSync` bracket, and by a
-- flattener whose inner is NOT the share, all agree -- so an emission
-- crossing a stateful frame is not the problem, and re-entry is.

-- NO REPAIR KEPT THE LIST, so this is a finding about the carrier
-- rather than about the share.  Handing a joiner the undelivered tail
-- is subscriber-major and fails at four values.  Dispatching the
-- emission value-major through the registry makes those emits
-- ROOT-level while the subscriber's own output is still deferred to the
-- unwind, and no fixed position for them is right -- a share ahead of a
-- sibling inner needs them first, a share behind one needs them last,
-- and the two shapes differ only in that order.

data subscribeE⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Val Γ (obs u) → Path Γ lo u t → Tick → W e → Subbed e → Set

data subscribeInner⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → W e
   → NodeId × Subbed e → Set

data thruConsume⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → W e → W e → Set

data thruWalk⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → List (Val Γ (obs u)) → W e → W e → Set

data mergeAllDrain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     NodeId → Path Γ lo s t → Tick → W e → W e → Set

data innerFinish⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → W e → Bool × W e → Set

data innerReact⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → W e → Bool × W e → Set

data stepFrame⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Tick → Frame Γ s u → Path Γ lo u t
   → List (Val Γ s) → Bool → W e
   → List (Val Γ u) × Bool × Bool × W e → Set

data pushVals⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t → List (Val Γ u) → W e → Pushed e → Set

data pushAll⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t
   → List (Val Γ u) → Bool → W e → Subbed e → Set

data subscribeAll⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeState Γ → Val Γ (obs (obs u)) → Path Γ lo u t
   → Tick → W e → Subbed e → Set

data sharedConnect⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → W e → Subbed e → Set

data subscribeSharedSlot⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → W e → Subbed e → Set

------------------------------------------------------------------
-- THE SHARE CYCLE.  The evaluator's second genuine cycle, entered
-- once per delivered chain; its members carry the subscribe cycle's
-- derivation too, because a fold re-enters a frame.
------------------------------------------------------------------

data dispatchShare⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n) → lo ≤ toℕ i
   → List (Val Γ (lookup Γ i)) → Bool → W e → Pushed e → Set

data shareGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n)
   → List (Val Γ (lookup Γ i)) → Bool
   → List (RegId × Path Γ lo (lookup Γ i) t) → W e → W e → Set

data foldPath⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t
   → List (Val Γ u) → Bool → W e → Pushed e → Set

------------------------------------------------------------------
-- THE ARRIVAL SPINE.  Structurally recursive in the evaluator, and
-- related here only because each of these reaches a cycle above and so
-- cannot be applied without a derivation to hand it.
------------------------------------------------------------------

data chainStep⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ) → AtFloor Γ (arrTy a) t → W e → W e → Set

data cascadeGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ)
   → List (RegId × AtFloor Γ (arrTy a) t) → W e → W e → Set

data cascade⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Arrival Γ → W e → W e → Set

data drain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Fuel → W e → W e → Set

data evaluate⇓ {n} {Γ : Ctx n} {t} :
     Fuel → Closed Γ t → Slots Γ → Stream Γ t → Set

----------------------------------------------------------------------
-- THE CONSTRUCTORS.  One per clause of the function each family
-- mirrors, every recursive call appearing as a sub-derivation.
----------------------------------------------------------------------

-- THE SLOT TESTS STAY PREMISES AND THE SCRIPT'S OWN WELL-FORMEDNESS
-- WITNESS IS BOUND RATHER THAN LEFT TO INFERENCE.  A slot's constructor
-- carries a proof that the element type is data, or that a shared def's
-- inputs sit below the slot; at a variable type neither reduces, so an
-- unwritten one is an unsolved meta and a build failure.
--
-- AND EVERY ARM THAT USED TO HAND BACK A FINISHED BURST NOW PUSHES IT,
-- which is why the ones that emit nothing at all are the short ones
-- here.  A registration is all a live source leaves behind; everything
-- a subscription actually produces has reached the root before the
-- clause returns.
data subscribeE⇓ {n} {Γ} {t} {e} where

  subs-floor : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                 {Θ ρ} {now w r}
             → lo ≤ toℕ i
             → pushAll⇓ now κ [] true w r
             → subscribeE⇓ (Θ , input i , ρ) κ now w r

  subs-shared : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                  {below : toℕ i < lo} {ok} {Θ ρ} {now out sched st r}
              → Sched.slots sched i ≡ shared d {ok = ok}
              → subscribeSharedSlot⇓ i d κ below now (out , sched , st) r
              → subscribeE⇓ (Θ , input i , ρ) κ now (out , sched , st) r

  subs-hot-done : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {Θ ρ} {now out sched st r}
                → toℕ i < lo
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
                → pushAll⇓ now κ [] true (out , sched , st) r
                → subscribeE⇓ (Θ , input i , ρ) κ now (out , sched , st) r

  -- A LIVE HOT PRODUCES NOTHING AT ALL, and under a push that is not a
  -- loss of information but the absence of one: what the subscription
  -- leaves is the registry row, and the values arrive later, one per
  -- cascade, through it.
  subs-hot-live : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {Θ ρ} {now out sched st rid}
                → (below : toℕ i < lo)
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
                → freshId regᵏ (Sched.mint sched) ≡ rid
                → subscribeE⇓ (Θ , input i , ρ) κ now (out , sched , st)
                    ( false
                    , out
                    , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                    , register rid (atSlot i) (lowerFloor below κ) st )

  -- A COLD IS `new Observable()`: A FRESH INDEPENDENT RUN PER
  -- SUBSCRIBER, ITS SYNCHRONOUS PREFIX PUSHED FROM INSIDE THE SUBSCRIBE
  -- CALL.  With no asynchronous tail the run is over as it starts, so
  -- the prefix carries the end and nothing is registered.
  subs-cold-sync : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                     {ok sync} {Θ ρ} {now out sched st r}
                 → toℕ i < lo
                 → Sched.slots sched i ≡ scripted {ok = ok} (cold sync [])
                 → pushAll⇓ now κ sync true (out , sched , st) r
                 → subscribeE⇓ (Θ , input i , ρ) κ now (out , sched , st) r

  -- AND WITH A TAIL THE REGISTRATION IS MADE BEFORE THE PREFIX IS
  -- PUSHED, NOT AFTER.  A synchronous value can cut this very chain,
  -- and a cut severs REGISTRATIONS — so a source registered afterwards
  -- would go on delivering into something nothing reads.
  subs-cold-async : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                      {ok sync d ds} {Θ ρ} {now out sched st src ord rid r}
                  → toℕ i < lo
                  → Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                  → freshId sourceᵏ (Sched.mint sched) ≡ src
                  → freshId ordinalᵏ (Sched.mint sched) ≡ ord
                  → freshId regᵏ (Sched.mint sched) ≡ rid
                  → pushAll⇓ now κ sync false
                      ( out
                      , record sched
                          { mint = setAt regᵏ (suc rid)
                                     (setAt sourceᵏ (suc src)
                                       (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                          ; live = record { source = src ; ordinal = ord
                                          ; elemTy = lookup Γ i
                                          ; pending = resolve now (d ∷ ds) }
                                   ∷ Sched.live sched }
                      , register rid (atDyn src lo) κ st )
                      r
                  → subscribeE⇓ (Θ , input i , ρ) κ now (out , sched , st) r

  subs-of : ∀ {lo u Θ} {ts} {ρ : Env Γ Θ} {κ : Path Γ lo u t} {now w r}
          → pushAll⇓ now κ (map (λ tm → evalWith tm ρ) ts) true w r
          → subscribeE⇓ (Θ , ofᵉ ts , ρ) κ now w r

  subs-empty : ∀ {lo u Θ} {ρ : Env Γ Θ} {κ : Path Γ lo u t} {now w r}
             → pushAll⇓ now κ [] true w r
             → subscribeE⇓ {u = u} (Θ , emptyᵉ , ρ) κ now w r

  -- `take(0)` NEVER SUBSCRIBES ITS SOURCE, which was measured rather
  -- than assumed: the operator completes on subscription and the
  -- source is not touched at all.
  subs-take-zero : ∀ {lo u Θ} {ρ : Env Γ Θ} {count} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo u t} {now w r}
                 → evalWith count ρ ≡ zero
                 → pushAll⇓ now κ [] true w r
                 → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now w r

  -- AND THE SOURCE'S OWN VERDICT IS THIS SUBSCRIPTION'S.  A truncation
  -- forwards its source's end and manufactures one when it cuts, and a
  -- cut is already reported as done by the push that made it — so there
  -- is nothing left for this clause to decide.
  subs-take-suc : ∀ {lo u Θ} {ρ : Env Γ Θ} {count k} {b : Exp Γ [] [] Θ u}
                    {κ : Path Γ lo u t} {now out sched st nid r}
                → evalWith count ρ ≡ suc k
                → freshId nodeᵏ (Sched.mint sched) ≡ nid
                → subscribeE⇓ (Θ , b , ρ) (take-f nid ↠[ ≤-refl ] κ) now
                    ( out
                    , record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }
                    , installNode nid (take-st (suc k)) st )
                    r
                → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now (out , sched , st) r

  -- CLOSING THE BRACKET IS WHERE THE GROUP LEAVES, AND IT IS THE ONE
  -- PLACE THIS CARRIER CHANGES AN ANSWER RATHER THAN RE-THREADING ONE.
  -- The group used to be read straight off the list a subscription
  -- handed back; with nothing handed back the bracket accumulates into
  -- its own node while the bit is up, and flushes here — carrying the
  -- end if the source finished inside the call, since a source that
  -- finishes within the subscribe has to leave WITH its group rather
  -- than ahead of it.
  subs-batchSync : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo (u ×ᵗ listᵗ u) t}
                     {now out sched st nid d out₁ sched₁ st₁ a w₂}
                 → freshId nodeᵏ (Sched.mint sched) ≡ nid
                 → subscribeE⇓ (Θ , b , ρ) (batchSync-f nid ↠[ ≤-refl ] κ) now
                     ( out
                     , record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }
                     , installNode nid (batchSync-st {t = u} true []) st )
                     (d , (out₁ , sched₁ , st₁))
                 → foldPath⇓ now κ
                     (batchVals true (batchTake u (lookupNode nid (EvalSt.nodes st₁))))
                     d
                     ( out₁ , sched₁
                     , installNode nid (batchSync-st {t = u} false []) st₁ )
                     (a , w₂)
                 → subscribeE⇓ (Θ , batchSyncᵉ b , ρ) κ now (out , sched , st) (d , w₂)

  -- A MAP INSTALLS NOTHING, WHICH IS WHY THIS ARM IS SHORTER THAN
  -- EVERY OTHER SUBSCRIBE ARM HERE.  There is no node to mint, so no
  -- freshness premise and no advanced mint in the recursive call.
  subs-map : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f : Fn Γ [] [] Θ s u}
               {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t} {now w r}
           → subscribeE⇓ (Θ , b , ρ) (map-f (Θ , f , ρ) ↠[ ≤-refl ] κ) now w r
           → subscribeE⇓ (Θ , mapᵉ f b , ρ) κ now w r

  subs-scan : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f} {i : Tm Γ [] [] Θ u}
                {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
                {now out sched st nid r}
            → freshId nodeᵏ (Sched.mint sched) ≡ nid
            → subscribeE⇓ (Θ , b , ρ) (scan-f (Θ , f , ρ) nid ↠[ ≤-refl ] κ) now
                ( out
                , record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }
                , installNode nid (cell-st (evalWith i ρ)) st )
                r
            → subscribeE⇓ (Θ , scanᵉ f i b , ρ) κ now (out , sched , st) r

  subs-merge-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {lim} {b : Exp Γ [] [] Θ (obs u)}
                     {κ : Path Γ lo u t} {now w r}
                 → subscribeAll⇓ mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false)
                     (Θ , b , ρ) κ now w r
                 → subscribeE⇓ (Θ , mergeAllᵉ lim b , ρ) κ now w r

  subs-switch-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ (obs u)}
                      {κ : Path Γ lo u t} {now w r}
                  → subscribeAll⇓ switchᵒ (switch-st nothing false)
                      (Θ , b , ρ) κ now w r
                  → subscribeE⇓ (Θ , switchAllᵉ b , ρ) κ now w r

  subs-exhaust-all : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ (obs u)}
                       {κ : Path Γ lo u t} {now w r}
                   → subscribeAll⇓ exhaustᵒ (exhaust-st false false)
                       (Θ , b , ρ) κ now w r
                   → subscribeE⇓ (Θ , exhaustAllᵉ b , ρ) κ now w r

  -- THE UNFOLDING IS UNCONDITIONAL, AND THAT CONCEDES NOTHING.  A
  -- machine comparing the unfolding's synchronous size against a
  -- number its caller handed it has that number among none of these
  -- indices, so no premise here could pin it; the comparison is owed
  -- by the inhabitation proof, which is where a measure belongs, since
  -- the unfolding is larger than the term it replaces and nothing here
  -- is structural in it.
  subs-μ : ∀ {lo u Θ} {ρ : Env Γ Θ} {body} {κ : Path Γ lo u t} {now w r}
         → subscribeE⇓ (Θ , unfoldμ body , ρ) κ now w r
         → subscribeE⇓ (Θ , μᵉ body , ρ) κ now w r

  subs-defer : ∀ {lo u Θ} {ρ : Env Γ Θ} {body} {κ : Path Γ lo u t}
                 {now out sched st nid src ord rid}
             → freshId nodeᵏ (Sched.mint sched) ≡ nid
             → freshId sourceᵏ (Sched.mint sched) ≡ src
             → freshId ordinalᵏ (Sched.mint sched) ≡ ord
             → freshId regᵏ (Sched.mint sched) ≡ rid
             → subscribeE⇓ (Θ , deferᵉ body , ρ) κ now (out , sched , st)
                 ( false
                 , out
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
                            (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ)
                            (installNode nid
                              (mergeAll-st {t = u} nothing 0 [] false) st) )

  -- MINTING IS THE RUN'S, AND THE BODY RECEIVES THE TOKEN AS A VALUE.
  -- The hop allocates at the same key `subs-defer` draws from and then
  -- EXTENDS THE ENVIRONMENT with the identifier, so the premise is a
  -- subscription of the same body under one more token.  The binder is
  -- the only thing in the tree that lengthens the telescope, which is
  -- why every other arm passes its environment down untouched.
  subs-mint : ∀ {lo u Θ} {ρ : Env Γ Θ} {body : Exp Γ [] [] (uniqᵗ ∷ Θ) u}
                {κ : Path Γ lo u t} {now out sched st src r}
            → freshId sourceᵏ (Sched.mint sched) ≡ src
            → subscribeE⇓ (uniqᵗ ∷ Θ , body , src ∷ᵉ ρ) κ now
                ( out
                , record sched
                    { mint = setAt sourceᵏ (suc src) (Sched.mint sched) }
                , st )
                r
            → subscribeE⇓ (Θ , mintᵉ body , ρ) κ now (out , sched , st) r

-- ONE CONSTRUCTOR WHERE A RUNNING MACHINE HAS TWO, AND THE MISSING ONE
-- IS THE POINT.  The machine asks whether what arrived is written
-- shallower than the component it stands at, and answers the negative
-- case by minting an instance and closing it dry.  Here the hop's
-- premise IS a sub-derivation at the arriving value, so there is
-- nothing to ask and no arm to answer.
data subscribeInner⇓ {n} {Γ} {t} {e} where
  inner : ∀ {u lo op allNid} {κ : Path Γ lo u t} {now}
            {o : Val Γ (obs u)} {out sched st inst done w′}
        → freshId nodeᵏ (Sched.mint sched) ≡ inst
        → subscribeE⇓ o (from-inner op allNid inst ↠[ ≤-refl ] κ) now
            ( out
            , record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }
            , st )
            (done , w′)
        → subscribeInner⇓ op allNid κ now o (out , sched , st) (inst , done , w′)

-- EACH COLLAPSE CARRIES THE SIDE CONDITION THAT DISTINGUISHES IT, so
-- no fallback here stands free.  A prover that CHOOSES its own run is
-- not the machine, and for it a premise-free fallback is an arm
-- available at every input -- and every one of these leaves the world
-- untouched, which would discharge any statement quantified over SOME
-- derivation with a reducible result.
data thruConsume⇓ {n} {Γ} {t} {e} where

  consume-all-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {out sched st} {lim act q od}
                      {inst done out₁ sched₁ st₁}
                  → lookupNode nid (EvalSt.nodes st)
                      ≡ just (mergeAll-st {t = u} lim act q od)
                  → hasRoom lim act ≡ true
                  → subscribeInner⇓ mergeAllᵒ nid κ now o (out , sched , st)
                      (inst , done , (out₁ , sched₁ , st₁))
                  → thruConsume⇓ mergeAllᵒ nid κ now o (out , sched , st)
                      ( out₁ , sched₁
                      , record st₁
                          { nodes = mergeAllBump nid done (EvalSt.nodes st₁) } )

  consume-all-enqueue : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {out sched st} {lim act q od}
                      → lookupNode nid (EvalSt.nodes st)
                          ≡ just (mergeAll-st {t = u} lim act q od)
                      → hasRoom lim act ≡ false
                      → thruConsume⇓ mergeAllᵒ nid κ now o (out , sched , st)
                          ( out , sched
                          , record st
                              { nodes = setNode nid
                                  (mergeAll-st lim act (q ++ o ∷ []) od)
                                  (EvalSt.nodes st) } )

  consume-all-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                    {o : Val Γ (obs u)} {out sched st}
                  → consumeUsable mergeAllᵒ u (lookupNode nid (EvalSt.nodes st)) ≡ false
                  → thruConsume⇓ mergeAllᵒ nid κ now o (out , sched , st)
                      (out , sched , st)

  consume-switch-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {out sched st} {cur od}
                         {sched₁ st₁} {inst done out₂ sched₂ st₂}
                     → lookupNode nid (EvalSt.nodes st) ≡ just (switch-st cur od)
                     → switchKill cur sched st ≡ (sched₁ , st₁)
                     → subscribeInner⇓ switchᵒ nid κ now o (out , sched₁ , st₁)
                         (inst , done , (out₂ , sched₂ , st₂))
                     → thruConsume⇓ switchᵒ nid κ now o (out , sched , st)
                         ( out₂ , sched₂
                         , record st₂
                             { nodes = setNode nid
                                 (switch-st (if done then nothing else just inst) od)
                                 (EvalSt.nodes st₂) } )

  consume-switch-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                       {o : Val Γ (obs u)} {out sched st}
                     → consumeUsable switchᵒ u (lookupNode nid (EvalSt.nodes st)) ≡ false
                     → thruConsume⇓ switchᵒ nid κ now o (out , sched , st)
                         (out , sched , st)

  consume-exhaust-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {out sched st} {od}
                          {inst done out₁ sched₁ st₁}
                      → lookupNode nid (EvalSt.nodes st)
                          ≡ just (exhaust-st false od)
                      → subscribeInner⇓ exhaustᵒ nid κ now o (out , sched , st)
                          (inst , done , (out₁ , sched₁ , st₁))
                      → thruConsume⇓ exhaustᵒ nid κ now o (out , sched , st)
                          ( out₁ , sched₁
                          , record st₁
                              { nodes = setNode nid (exhaust-st (not done) od)
                                  (EvalSt.nodes st₁) } )

  consume-exhaust-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                        {o : Val Γ (obs u)} {out sched st}
                      → consumeUsable exhaustᵒ u (lookupNode nid (EvalSt.nodes st)) ≡ false
                      → thruConsume⇓ exhaustᵒ nid κ now o (out , sched , st)
                          (out , sched , st)

data thruWalk⇓ {n} {Γ} {t} {e} where

  walk-nil : ∀ {u lo op nid} {κ : Path Γ lo u t} {now} {w}
           → thruWalk⇓ {u = u} op nid κ now [] w w

  walk-cons : ∀ {u lo op nid} {κ : Path Γ lo u t} {now}
                {o : Val Γ (obs u)} {os w w₁ w₂}
            → thruConsume⇓ op nid κ now o w w₁
            → thruWalk⇓ op nid κ now os w₁ w₂
            → thruWalk⇓ op nid κ now (o ∷ os) w w₂

-- THE QUEUE IS RE-READ FROM THE NODE AT EVERY STEP, and under a push
-- carrier that is not caution.  An inner that completes INSIDE its own
-- subscribe call re-enters this node and drains it further, so a
-- carried queue goes on to subscribe rows the re-entrant drain has
-- already taken — one queued inner emitting eight times over.  The list
-- carrier could carry them safely, because a synchronous completion
-- reached this node only once the subscribe had returned; nothing about
-- the drain changed, the moment did.
--
-- THE SHORTENED QUEUE IS STILL WRITTEN BEFORE THE SUBSCRIBE, NOT AFTER
-- THE DRAIN.  A batch write-back leaves the node holding the items
-- already spent, and rxjs takes the item OUT of the buffer before it
-- subscribes it, which is also what the re-entrant call has to see.
data mergeAllDrain⇓ {n} {Γ} {t} {e} where

  drain-nil : ∀ {s lo allNid} {κ : Path Γ lo s t} {now out sched st}
            → consumeUsable mergeAllᵒ s (lookupNode allNid (EvalSt.nodes st)) ≡ false
            → mergeAllDrain⇓ {s = s} allNid κ now (out , sched , st) (out , sched , st)

  drain-empty : ∀ {s lo allNid} {κ : Path Γ lo s t} {now out sched st}
                  {lim act od}
              → lookupNode allNid (EvalSt.nodes st)
                  ≡ just (mergeAll-st {t = s} lim act [] od)
              → mergeAllDrain⇓ allNid κ now (out , sched , st) (out , sched , st)

  drain-no-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now out sched st}
                    {lim act od} {o : Val Γ (obs s)} {q}
                → lookupNode allNid (EvalSt.nodes st)
                    ≡ just (mergeAll-st {t = s} lim act (o ∷ q) od)
                → hasRoom lim act ≡ false
                → mergeAllDrain⇓ allNid κ now (out , sched , st) (out , sched , st)

  drain-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now out sched st}
                 {lim act od} {o : Val Γ (obs s)} {q}
                 {inst done out₁ sched₁ st₁} {w₂}
             → lookupNode allNid (EvalSt.nodes st)
                 ≡ just (mergeAll-st {t = s} lim act (o ∷ q) od)
             → hasRoom lim act ≡ true
             → subscribeInner⇓ mergeAllᵒ allNid κ now o
                 ( out , sched
                 , record st
                     { nodes = setNode allNid (mergeAll-st lim act q od)
                         (EvalSt.nodes st) } )
                 (inst , done , (out₁ , sched₁ , st₁))
             → mergeAllDrain⇓ allNid κ now
                 ( out₁ , sched₁
                 , record st₁
                     { nodes = mergeAllBump allNid done (EvalSt.nodes st₁) } )
                 w₂
             → mergeAllDrain⇓ allNid κ now (out , sched , st) w₂

-- THE LEAVING INNER COMES OFF THE COUNT BEFORE THE DRAIN, AND THE
-- VERDICT IS READ OFF THE NODE AFTERWARDS — never off the state this
-- clause opened on, which a re-entrant drain may have replaced
-- underneath it.
data innerFinish⇓ {n} {Γ} {t} {e} where

  finish-all-drain : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                       {out sched st} {lim act q od} {out′ sched′ st′}
                   → lookupNode allNid (EvalSt.nodes st)
                       ≡ just (mergeAll-st {t = s} lim act q od)
                   → mergeAllDrain⇓ allNid κ now
                       ( out , sched
                       , record st
                           { nodes = setNode allNid
                               (mergeAll-st lim (pred act) q od)
                               (EvalSt.nodes st) } )
                       (out′ , sched′ , st′)
                   → innerFinish⇓ mergeAllᵒ allNid inst κ now (out , sched , st)
                       (allDone mergeAllᵒ allNid st′ , (out′ , sched′ , st′))

  finish-switch-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                          {out sched st} {c od}
                      → lookupNode allNid (EvalSt.nodes st)
                          ≡ just (switch-st (just c) od)
                      → (c ≡ᵇ inst) ≡ true
                      → innerFinish⇓ {s = s} switchᵒ allNid inst κ now
                          (out , sched , st)
                          ( od
                          , out , sched
                          , record st
                              { nodes = setNode allNid (switch-st nothing od)
                                  (EvalSt.nodes st) } )

  finish-exhaust-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                           {out sched st} {act od}
                       → lookupNode allNid (EvalSt.nodes st)
                           ≡ just (exhaust-st act od)
                       → innerFinish⇓ {s = s} exhaustᵒ allNid inst κ now
                           (out , sched , st)
                           ( od
                           , out , sched
                           , record st
                               { nodes = setNode allNid (exhaust-st false od)
                                   (EvalSt.nodes st) } )

  finish-nil : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                 {out sched st}
             → finishUsable op s inst (lookupNode allNid (EvalSt.nodes st)) ≡ false
             → innerFinish⇓ {s = s} op allNid inst κ now (out , sched , st)
                 (false , out , sched , st)

-- A COMPLETION OUT OF AN INNER IS ABSORBED WHILE ANYTHING UNDER THAT
-- INSTANCE IS STILL LIVE.
data innerReact⇓ {n} {Γ} {t} {e} where

  react-alive : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                  {out sched st}
              → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true
              → innerReact⇓ {s = s} op allNid inst κ now (out , sched , st)
                  (false , out , sched , st)

  react-dead : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                 {out sched st r}
             → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
             → innerFinish⇓ op allNid inst κ now (out , sched , st) r
             → innerReact⇓ {s = s} op allNid inst κ now (out , sched , st) r

-- A HELPER OUTSIDE THE CYCLE IS NAMED IN THE RESULT INDEX RATHER THAN
-- UNFOLDED INTO ARMS, AND THAT IS A CHOICE ABOUT WHAT THIS RELATION IS
-- FOR.  The take dispatch, the scan's fold, the bracket's grouping and
-- the outer wrap each branch on a node lookup, but none re-enters the
-- subscribe cycle, so relating their arms separately would add cases
-- the induction never splits on.  What the relation must expose is
-- exactly the recursive structure; a total function of the state is
-- carried as itself.
data stepFrame⇓ {n} {Γ} {t} {e} where

  step-map : ∀ {s u lo} {fn : FnClo Γ s u} {κ : Path Γ lo u t}
               {now} {vals : List (Val Γ s)} {fin w}
           → stepFrame⇓ now (map-f fn) κ vals fin w
               (map (applyClo fn) vals , fin , true , w)

  step-scan : ∀ {s u lo} {fn : FnClo Γ (u ×ᵗ s) u} {nid} {κ : Path Γ lo u t}
                {now} {vals : List (Val Γ s)} {fin out sched st}
                {vs fin′ sched′ st′}
            → scanDispatch fn nid vals fin sched st
                (lookupNode nid (EvalSt.nodes st))
                ≡ (vs , fin′ , sched′ , st′)
            → stepFrame⇓ now (scan-f fn nid) κ vals fin (out , sched , st)
                (vs , fin′ , true , (out , sched′ , st′))

  -- A CUT IS THE TRUNCATION ENDING A SUBSCRIPTION THE SOURCE DID NOT
  -- END, and it is the one thing that makes a live source stop — which
  -- is the whole reason a push reports an ALIVE bit at all.
  step-take : ∀ {s lo nid} {κ : Path Γ lo s t}
                {now} {vals : List (Val Γ s)} {fin out sched st}
                {vs fin′ sched′ st′}
            → takeDispatch nid vals fin sched st
                (lookupNode nid (EvalSt.nodes st))
                ≡ (vs , fin′ , sched′ , st′)
            → stepFrame⇓ now (take-f nid) κ vals fin (out , sched , st)
                (vs , fin′ , not (fin′ ∧ not fin) , (out , sched′ , st′))

  step-batchSync : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                     {now} {vals : List (Val Γ s)} {fin out sched st}
                     {vs fin′ st′}
                 → batchStep nid vals fin st (lookupNode nid (EvalSt.nodes st))
                     ≡ (vs , fin′ , st′)
                 → stepFrame⇓ now (batchSync-f nid) κ vals fin (out , sched , st)
                     (vs , fin′ , true , (out , sched , st′))

  -- A COMPLETION IS THE ONLY THING AN INNER'S FRAME REACTS TO; values
  -- pass straight through it.
  step-from-inner-val : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                          {now} {vals : List (Val Γ s)} {w}
                      → stepFrame⇓ now (from-inner op allNid inst) κ vals false w
                          (vals , false , true , w)

  step-from-inner-end : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                          {now} {vals : List (Val Γ s)} {w fin′ w′}
                      → innerReact⇓ op allNid inst κ now w (fin′ , w′)
                      → stepFrame⇓ now (from-inner op allNid inst) κ vals true w
                          (vals , fin′ , true , w′)

  -- THE INNERS' OWN VALUES REACH THE ROOT THROUGH THEIR OWN INNER
  -- PATHS, so nothing passes through the outer frame.
  step-thru-outer : ∀ {u lo op nid} {κ : Path Γ lo u t}
                      {now} {vals : List (Val Γ (obs u))} {fin out sched st}
                      {out′ sched′ st′} {fin′ sched″ st″}
                  → thruWalk⇓ op nid κ now vals (out , sched , st)
                      (out′ , sched′ , st′)
                  → thruWrap {u = u} op nid fin ([] , sched′ , st′)
                      ≡ ([] , fin′ , sched″ , st″)
                  → stepFrame⇓ now (thru-outer op nid) κ vals fin (out , sched , st)
                      ([] , fin′ , true , (out′ , sched″ , st″))

-- VALUE BY VALUE, STOPPING THE MOMENT THE CHAIN IS CUT.  Once a
-- truncation downstream has severed this subscription there is nothing
-- left to push into, and a source that goes on producing is a source
-- rxjs would have unsubscribed.
data pushVals⇓ {n} {Γ} {t} {e} where

  vals-nil : ∀ {u lo} {κ : Path Γ lo u t} {now w}
           → pushVals⇓ {u = u} now κ [] w (true , w)

  vals-cut : ∀ {u lo} {κ : Path Γ lo u t} {now} {v : Val Γ u} {vs w w′}
           → foldPath⇓ now κ (v ∷ []) false w (false , w′)
           → pushVals⇓ now κ (v ∷ vs) w (false , w′)

  vals-more : ∀ {u lo} {κ : Path Γ lo u t} {now} {v : Val Γ u} {vs w w′ r}
            → foldPath⇓ now κ (v ∷ []) false w (true , w′)
            → pushVals⇓ now κ vs w′ r
            → pushVals⇓ now κ (v ∷ vs) w r

-- A VALUE AND AN END MAY NEVER SHARE A FOLD, AND THIS IS THE ONLY PLACE
-- THAT GUARANTEES IT — so every emission goes through here, a scheduled
-- arrival carrying its last flag as much as a synchronous prefix.  The
-- frames REACT to an end: an inner's frame drains its joiner's queue
-- there, and a queued inner subscribed inside that reaction emits
-- BEFORE the value it was handed alongside.  A carrier handing its
-- caller a finished list could not see this, because under it the pair
-- was the unit of delivery.
data pushAll⇓ {n} {Γ} {t} {e} where

  -- a cut ENDED this subscription, so it is done whether or not the
  -- source got as far as saying so
  push-cut : ∀ {u lo} {κ : Path Γ lo u t} {now vals fin w w′}
           → pushVals⇓ now κ vals w (false , w′)
           → pushAll⇓ now κ vals fin w (true , w′)

  push-open : ∀ {u lo} {κ : Path Γ lo u t} {now vals w w′}
            → pushVals⇓ now κ vals w (true , w′)
            → pushAll⇓ now κ vals false w (false , w′)

  push-end : ∀ {u lo} {κ : Path Γ lo u t} {now vals w w′ a w″}
           → pushVals⇓ now κ vals w (true , w′)
           → foldPath⇓ now κ [] true w′ (a , w″)
           → pushAll⇓ now κ vals true w (true , w″)

-- WHAT AN `*All` SUBSCRIPTION REPORTS IS A READING OF ITS OWN NODE, not
-- the outer's verdict.  The operator outlives its outer for exactly as
-- long as something is still running under it, and a synchronous inner
-- may have completed inside the very call this clause is returning
-- from.
data subscribeAll⇓ {n} {Γ} {t} {e} where

  sub-all : ∀ {u lo op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
              {κ : Path Γ lo u t} {now out sched st nid d out₁ sched₁ st₁}
          → freshId nodeᵏ (Sched.mint sched) ≡ nid
          → subscribeE⇓ b (thru-outer op nid ↠[ ≤-refl ] κ) now
              ( out
              , record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) }
              , installNode nid ns st )
              (d , (out₁ , sched₁ , st₁))
          → subscribeAll⇓ op ns b κ now (out , sched , st)
              (allDone op nid st₁ , (out₁ , sched₁ , st₁))

-- THE CONNECT'S OWN GUARD IS NOT INDEXED HERE EITHER, AND THE SAME
-- RULING AS THE UNFOLD'S APPLIES: a run's answer to a question this
-- relation does not name is owed by the inhabitation proof.
--
-- AND THE CONNECT HAS NOTHING LEFT TO DO AFTERWARDS, which is the
-- carrier showing through.  The def's values and its end now travel the
-- share's own sink like any other emission, so the dispatch latches the
-- completion and drops the rows, and the two arms this clause used to
-- have — one for a def that finished inside the connect, one for a def
-- that did not — are one.
data sharedConnect⇓ {n} {Γ} {t} {e} where

  connect : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
              {below : toℕ i < lo} {now out sched st rid r}
          → freshId regᵏ (Sched.mint sched) ≡ rid
          → subscribeE⇓ ([] , d , []ᵉ) (share-sink i ≤-refl) now
              ( out
              , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
              , register rid (atSlot i) (lowerFloor below κ)
                  (record st
                    { connectedShares = toℕ i ∷ EvalSt.connectedShares st }) )
              r
          → sharedConnect⇓ i d κ below now (out , sched , st) r

data subscribeSharedSlot⇓ {n} {Γ} {t} {e} where

  -- a completed Subject re-delivers completion to late subscribers
  slot-spent : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                 {below : toℕ i < lo} {now out sched st r}
             → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
             → pushAll⇓ now κ [] true (out , sched , st) r
             → subscribeSharedSlot⇓ i d κ below now (out , sched , st) r

  slot-join : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                {below : toℕ i < lo} {now out sched st rid}
            → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
            → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ true
            → freshId regᵏ (Sched.mint sched) ≡ rid
            → subscribeSharedSlot⇓ i d κ below now (out , sched , st)
                ( false
                , out
                , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                , register rid (atSlot i) (lowerFloor below κ) st )

  slot-connect : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {now out sched st r}
               → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
               → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false
               → sharedConnect⇓ i d κ below now (out , sched , st) r
               → subscribeSharedSlot⇓ i d κ below now (out , sched , st) r

-- THE ONE CLAUSE, and the whole reason the share cycle is separate: the
-- fan-out re-enters at the floor the sink's own premise names, so the
-- relation carries that premise as a constructor argument and the
-- descent it buys is a fact about the index rather than a peeled
-- witness.  `shareFinish`, `shareAdmit` and `shareLatch` compute, so
-- they stay applied.
--
-- AND READING THE REGISTRY ONCE IS NOW ENOUGH, which is what the whole
-- carrier change buys.  The snapshot is per CALL, and a call carries
-- one value, so a subscription made in reaction to a value is present
-- for the next one.  Under a list this same line saw the registry as it
-- stood before any of the emission had been delivered.
data dispatchShare⇓ {n} {Γ} {t} {e} where
  disp : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
           {vals fin out sched st w′}
       → shareGo⇓ now i vals fin
           (shareAdmit i (EvalSt.registry st))
           (out , sched , shareLatch i fin st) w′
       → dispatchShare⇓ now i below vals fin (out , sched , st)
           (true , shareFinish i fin w′)

-- THE CANCELLATION TEST STAYS A PREMISE RATHER THAN A SIDE CONDITION.
-- It is decidable and it decides which of two clauses ran, so the
-- relation carries the answer as an equation and the two arms cannot
-- both apply.  `go-live` is where the threading shows: what the tail is
-- handed is the head's own result.
data shareGo⇓ {n} {Γ} {t} {e} where
  go-nil : ∀ {lo now} {i : Fin n} {vals fin w}
         → shareGo⇓ {lo = lo} now i vals fin [] w w

  go-cut : ∀ {lo now} {i : Fin n} {vals fin rid}
             {p : Path Γ lo (lookup Γ i) t} {ps out sched st w′}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
         → shareGo⇓ now i vals fin ps (out , sched , st) w′
         → shareGo⇓ now i vals fin ((rid , p) ∷ ps) (out , sched , st) w′

  go-live : ∀ {lo now} {i : Fin n} {vals fin rid}
              {p : Path Γ lo (lookup Γ i) t} {ps out sched st}
              {d w₁ w₂}
          → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
          → pushAll⇓ now p vals fin
              ( out , sched
              , record st { delivered = rid ∷ EvalSt.delivered st } )
              (d , w₁)
          → shareGo⇓ now i vals fin ps w₁ w₂
          → shareGo⇓ now i vals fin ((rid , p) ∷ ps) (out , sched , st) w₂

-- THE PATH IS WALKED SINKWARD AND THE ROOT IS WHERE AN EMIT IS MINTED,
-- so the root clauses are the only ones that make something out of
-- nothing and the other two hand their own results on.  The sink clause
-- is where the floor descends: its premise is the path constructor's
-- argument, so nothing has to be carried alongside.
--
-- A QUIET FOLD IS NOT AN EMPTY ONE.  Under a push a fold is entered
-- once per value, and the frames absorb: a bracket inside its own
-- subscribe call, an inner's frame swallowing a completion it is not
-- ready to forward.  What reaches the root from such a fold is nothing
-- at all, and appending an empty envelope for it would put a group in
-- the stream that no observer saw.
data foldPath⇓ {n} {Γ} {t} {e} where

  fold-root-quiet : ∀ {lo now w}
                  → foldPath⇓ {lo = lo} now root [] false w (true , w)

  fold-root-vals : ∀ {lo now} {v : Val Γ t} {vs fin out sched st}
                 → foldPath⇓ {lo = lo} now root (v ∷ vs) fin (out , sched , st)
                     ( true
                     , out ++ (map valueᵖ (v ∷ vs)
                                 ++ (if fin then completeᵖ ∷ [] else [])) ∷ []
                     , sched , st )

  fold-root-end : ∀ {lo now out sched st}
                → foldPath⇓ {lo = lo} now root [] true (out , sched , st)
                    (true , out ++ (completeᵖ ∷ []) ∷ [] , sched , st)

  fold-sink : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
                {vals fin w r}
            → dispatchShare⇓ now i below vals fin w r
            → foldPath⇓ now (share-sink i below) vals fin w r

  -- AND THE ALIVE BITS MULTIPLY ALONG THE PATH.  A cut anywhere
  -- rootward of a frame is a cut for everything sinkward of it, so the
  -- source hears about a truncation it never met.
  fold-step : ∀ {lo ℓ s u now} {f : Frame Γ s u} {le : lo ≤ ℓ}
                {path′ : Path Γ ℓ u t} {vals fin w}
                {vals′ fin′ al w₁} {al′ w₂}
            → stepFrame⇓ now f path′ vals fin w (vals′ , fin′ , al , w₁)
            → foldPath⇓ now path′ vals′ fin′ w₁ (al′ , w₂)
            → foldPath⇓ {lo = lo} now (f ↠[ le ] path′) vals fin w (al ∧ al′ , w₂)

-- ONE CLAUSE WHERE THERE WERE TWO, AND THE SPLIT IT USED TO MAKE HAS
-- MOVED TO WHERE EVERY EMISSION PASSES.  An arrival carries a value and
-- possibly an end, and separating them is the push's own discipline
-- rather than this clause's.
data chainStep⇓ {n} {Γ} {t} {e} where
  chain-push : ∀ {a : Arrival Γ} {lo} {path : Path Γ lo (arrTy a) t}
                 {w d w′}
             → pushAll⇓ (arrTick a) path (arrVal a ∷ []) (Arrival.isLast a) w
                 (d , w′)
             → chainStep⇓ a (lo , path) w w′

data cascadeGo⇓ {n} {Γ} {t} {e} where
  casc-nil : ∀ {a w}
           → cascadeGo⇓ a [] w w
  casc-cut : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains out sched st w′}
           → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
           → cascadeGo⇓ a chains (out , sched , st) w′
           → cascadeGo⇓ a ((rid , c) ∷ chains) (out , sched , st) w′
  casc-live : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains out sched st}
                {w₁ w₂}
            → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ false
            → chainStep⇓ a c
                ( out , sched
                , record st { delivered = rid ∷ EvalSt.delivered st } )
                w₁
            → cascadeGo⇓ a chains w₁ w₂
            → cascadeGo⇓ a ((rid , c) ∷ chains) (out , sched , st) w₂

data cascade⇓ {n} {Γ} {t} {e} where
  casc-run : ∀ {a out sched st} {out′ sched′ st′}
           → cascadeGo⇓ a (chainsOf a st)
               (out , sched , cascadeLatch a sched st)
               (out′ , sched′ , st′)
           → cascade⇓ a (out , sched , st) (out′ , cascadeFinish a sched′ st′)

data drain⇓ {n} {Γ} {t} {e} where
  drain-done : ∀ {w}
             → drain⇓ zero w w
  drain-empty : ∀ {k out sched st}
              → sched-next sched ≡ inj₁ tt
              → drain⇓ (suc k) (out , sched , st) (out , sched , st)
  drain-step : ∀ {k out sched st} {a : Arrival Γ} {sched′ w₁ w₂}
             → sched-next sched ≡ inj₂ (a , sched′)
             → cascade⇓ a (out , sched′ , st) w₁
             → drain⇓ k w₁ w₂
             → drain⇓ (suc k) (out , sched , st) w₂

data evaluate⇓ {n} {Γ} {t} where
  eval-run : ∀ {fuel} {e : Closed Γ t} {ins : Slots Γ}
               {d w₀ out sched′ st′}
           → subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
               ([] , sched-init e ins , st-init e) (d , w₀)
           → drain⇓ {e = e} fuel w₀ (out , sched′ , st′)
           → evaluate⇓ fuel e ins out
