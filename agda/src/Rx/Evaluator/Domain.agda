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

-- A SUBSCRIPTION EMITS AT THE ROOT TYPE, AND THAT IS WHAT MAKES
-- DEPTH-FIRST THE RECURSION'S OWN ORDER RATHER THAN A PROPERTY
-- SOMETHING HAD TO RE-ESTABLISH.  A subscription used to hand its
-- whole output back at the SOURCE's element type, and each enclosing
-- frame pushed that finished list through itself, so the order a value
-- reached the root in was assembled on the way out rather than being
-- the order it was produced in.  Carrying the rest of the path INTO
-- the subscribe puts it back: a subscription's result is already at
-- `t`, and the burst-pushing family is deleted rather than repaired.
--
-- IT DOES NOT BY ITSELF MAKE A RE-ENTRANT SUBSCRIBE VISIBLE, and that
-- is the distinction the root type costs nothing to blur.  A value may
-- still be handed to a whole loop at once, and the fan-out at a share
-- did exactly that, reading its subscriber list before any value of an
-- emission was delivered -- so a subscription created by one of those
-- values joined a loop that had already read past it and received
-- NOTHING, which is the empty list the oracle measured against rxjs's
-- six values.  Where the emission order lives is `shareWalk⇓`, below.
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
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _<_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Tick; Fuel; valueᵖ; completeᵖ; hot; cold)
open import Rx.Exp using (obs; Ctx; Val; Closed; Exp; Tm; Fn; FnClo; applyClo;
  _×ᵗ_; listᵗ; uniqᵗ;
  Env; _∷ᵉ_; []ᵉ; evalWith; unfoldμ; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; deferᵉ; mintᵉ)
open import Rx.Mint using (ordinalᵏ; sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Stream; Burst; Sched; EvalSt; Path; Frame; NodeId; root; share-sink; _↠_; shareAdmit;
  shareDying; shareFinish; from-inner; splitEvents; oneShotBurst; spentBurst; arrTick; arrVal;
  chainsOf; cascadeLatch; cascadeFinish; sched-next; sched-init; st-init; NodeState; AllOp;
  RegId; Arrival; AtFloor; arrTy; memberSource; register; installNode; resolve; dropSource;
  atSlot; atDyn; lowerFloor; map-f; scan-f; take-f; batchSync-f; thru-outer; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; mergeAllᵒ; switchᵒ; exhaustᵒ; lookupNode;
  setNode; hasRoom; mergeAllBump; switchKill; aliveThroughᶠ; scanDispatch; takeDispatch;
  batchDispatch; thruWrap; consumeUsable; finishUsable; VSegs; oneVSeg; Segs; oneSeg; stepSegs;
  segVSegs; segsCompleted; resolveSegs)

-- THE FRAME A SUBSCRIBE CAN PUSH, WHICH IS EVERY FRAME BUT ONE, AND
-- SAYING SO IN A TYPE IS WHAT TAKES THE DRAIN OUT OF A PUSH CYCLE.  A
-- push cycle steps the frame it was handed, and what hands it one is a
-- source former -- the map, the take, the bracket, the scan, the outer
-- of an operator.  The inner's own frame is never pushed: a subscribe
-- returns the inner's synchronous burst UP to its caller as values, and
-- the frame is walked later, by the instant loop, down a path the
-- registry holds.  So the completion side -- react, finish, drain, and
-- the queued subscribe they end in -- is not reachable from a subscribe
-- at all, and the cycle that a measure was owed for does not exist.

-- AND THAT IS PRECISELY WHAT A SHARE'S FAN-OUT AT THE CONNECT WOULD
-- SPEND, WHICH IS WHY IT IS WORTH PRICING HERE RATHER THAN DISCOVERING
-- LATER.  Handing a burst UP is what keeps the two halves apart; a
-- subscribe that pushes where it produces puts the fold back inside
-- the subscribe's own cycle and re-owes the measure this arrangement
-- retired.  The order that would fund it is three deep -- the
-- UNCONNECTED-SLOT count outermost, which only a connect moves and
-- which nothing anywhere raises, the share floor's remaining room
-- next, and the element type's observable nesting under that -- and
-- each component is the one the edge above it cannot order.  So the
-- price is not a lemma but a measure, and `connectedShares` stops
-- being bookkeeping and becomes load-bearing.
srcFrame : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
srcFrame (from-inner _ _ _) = ⊥
srcFrame _                  = ⊤

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE.  Eleven families, exactly the members of the
-- evaluator's larger genuine cycle: everything else it calls is
-- structurally recursive and is APPLIED here rather than related.
--
-- A SUBSCRIPTION HANDS BACK BURSTS, WHICH IS THE ONE STRUCTURAL FACT
-- THE WHOLE FILE RESTS ON.  Everything one incoming emit causes leaves
-- together, so a frame is handed a LIST of values rather than one --
-- and an operator bracketing the subscribe call sees the group already
-- assembled instead of having to record which side of that call it is
-- on.
------------------------------------------------------------------

data subscribeE⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Val Γ (obs u) → Path Γ lo u t → Tick → Sched Γ → EvalSt e
   → Segs Γ u t × Sched Γ × EvalSt e → Set

data subscribeInner⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → NodeId × VSegs Γ u t × Bool × Sched Γ × EvalSt e → Set

data thruConsume⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → VSegs Γ u t × Sched Γ × EvalSt e → Set

data thruWalk⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → List (Val Γ (obs u)) → Sched Γ → EvalSt e
   → VSegs Γ u t × Sched Γ × EvalSt e → Set

data mergeAllDrain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     NodeId → Path Γ lo s t → Tick
   → Maybe ℕ → ℕ → Bool → List (Val Γ (obs s)) → Sched Γ → EvalSt e
   → VSegs Γ s t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e → Set

data innerFinish⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
   → VSegs Γ s t × Bool × Sched Γ × EvalSt e → Set

data innerReact⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Bool
   → VSegs Γ s t × Bool × Sched Γ × EvalSt e → Set

data stepFrame⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Tick → Frame Γ s u → Path Γ lo u t
   → List (Val Γ s) → Bool → Sched Γ → EvalSt e
   → VSegs Γ u t × Bool × Sched Γ × EvalSt e → Set

data pushBurst⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Tick → Frame Γ s u → Path Γ lo u t
   → Stream Γ s → Sched Γ → EvalSt e
   → Segs Γ u t × Sched Γ × EvalSt e → Set

data pushSegs⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Tick → Frame Γ s u → Path Γ lo u t
   → Segs Γ s t → Sched Γ → EvalSt e
   → Segs Γ u t × Sched Γ × EvalSt e → Set

data subscribeAll⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeState Γ → Val Γ (obs (obs u)) → Path Γ lo u t
   → Tick → Sched Γ → EvalSt e
   → Segs Γ u t × Sched Γ × EvalSt e → Set

data sharedConnect⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → Sched Γ → EvalSt e
   → Segs Γ (lookup Γ i) t × Sched Γ × EvalSt e → Set

data subscribeSharedSlot⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Tick → Sched Γ → EvalSt e
   → Segs Γ (lookup Γ i) t × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE SHARE CYCLE.  The evaluator's second genuine cycle, entered
-- once per delivered chain; its members carry the subscribe cycle's
-- derivation too, because a fold re-enters a frame.
------------------------------------------------------------------

data dispatchShare⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n) → lo ≤ toℕ i
   → List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

-- THE VALUE LOOP SITS ABOVE THE SUBSCRIBER LOOP, which is the whole of
-- the fan-out's order: one value is delivered to every admitted chain
-- before the next value is delivered to any, and the admitted list is
-- re-derived from the registry between them.  That is what makes a
-- subscription created by value `j` receive values after `j` and none
-- before -- the joiner's entitlement as a CONSEQUENCE of when the list
-- is read, so nothing has to carry a join index and no registry row
-- gains a field.
--
-- AND THE ORDER IT IMPLEMENTS IS A DEPTH-FIRST WALK OF AN EXECUTION
-- TREE IN WHICH EACH NODE ORDERS ITS OWN CHILDREN (Anthony).  A
-- flattener orders them by (inner, then value); a share orders them by
-- (value, then subscriber).  Those are opposite, which is why no single
-- sort key over the whole emission can be right -- one uniform order
-- repairs the share and breaks every flattener, and a global emission
-- counter is that key by another name.  So the transpose belongs at the
-- share and nowhere else, which is what this loop is.
--
-- THE ROUTE IF THIS ONE FAILS was to make the traversal's position
-- EXPLICIT: stamp each emit with its path through that tree and sort
-- lexicographically, rather than relying on each node to emit its
-- children in order.  It is not wanted, and that is now measured
-- rather than deferred: the stamp's cost was a significance ordering
-- ACROSS NESTED SHARES, and the nested row of
-- `typescript/corpus/depth-first.ndjson` answers exactly as its
-- un-nested twin does -- one share read through another, with the
-- inner loop entered once per outer value and nothing ranking the two.
-- A local transpose composes, so there is nothing for a total order to
-- decide.
data shareWalk⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Tick → (i : Fin n)
   → List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data shareGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Tick → (i : Fin n)
   → Val Γ (lookup Γ i) → Bool
   → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data foldPath⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t
   → List (Val Γ u) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data foldVSegs⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t
   → VSegs Γ u t → Bool → Sched Γ → EvalSt e
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
-- HELPERS FOR COMPUTED-INDEX CONSTRUCTORS.  `scanDispatch` and
-- `takeDispatch` return `List × Bool × Sched × EvalSt`; `injectRoot`
-- lifts that shape into the widened result -- one segment, whose root
-- component is empty because a frame that computes its own output
-- cannot reach the root.
----------------------------------------------------------------------

injectRoot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → List (Val Γ u) × Bool × Sched Γ × EvalSt e
             → VSegs Γ u t × Bool × Sched Γ × EvalSt e
injectRoot (vs , fin , sc , st) = oneVSeg vs , fin , sc , st

----------------------------------------------------------------------
-- THE CONSTRUCTORS.  One per clause of the function each family
-- mirrors, every recursive call appearing as a sub-derivation.
----------------------------------------------------------------------

-- THE SLOT TESTS STAY PREMISES AND THE SCRIPT'S OWN WELL-FORMEDNESS
-- WITNESS IS BOUND RATHER THAN LEFT TO INFERENCE.  A slot's constructor
-- carries a proof that the element type is data, or that a shared def's
-- inputs sit below the slot; at a variable type neither reduces, so an
-- unwritten one is an unsolved meta and a build failure.
data subscribeE⇓ {n} {Γ} {t} {e} where

  subs-floor : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                 {Θ ρ} {now sched st}
             → lo ≤ toℕ i
             → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                 (oneSeg spentBurst , sched , st)

  subs-shared : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                  {below : toℕ i < lo} {ok} {Θ ρ} {now sched st r}
              → Sched.slots sched i ≡ shared d {ok = ok}
              → subscribeSharedSlot⇓ i d κ below now sched st r
              → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-hot-done : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {Θ ρ} {now sched st}
                → toℕ i < lo
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
                → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                    (oneSeg spentBurst , sched , st)

  -- A LIVE HOT HANDS BACK NOTHING AT ALL, which is what a plain
  -- carrier makes of a registration: the old shape emitted one
  -- `init`-only envelope so the ledger downstream had something to
  -- count, and counting has left the carrier.  What remains of the
  -- subscription is the registry row.
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
  -- so the prefix and the end are ONE burst and nothing is registered.
  subs-cold-sync : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                     {ok sync} {Θ ρ} {now sched st}
                 → toℕ i < lo
                 → Sched.slots sched i ≡ scripted {ok = ok} (cold sync [])
                 → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                     (oneSeg (oneShotBurst sync) , sched , st)

  -- AND WITH A TAIL THE REGISTRATION IS MADE BEFORE THE PREFIX IS
  -- REPLAYED, NOT AFTER.  A synchronous value can cut this very
  -- chain, and a cut severs REGISTRATIONS — so a source registered
  -- afterwards would go on delivering into something nothing reads.
  subs-cold-async : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                      {ok sync d ds} {Θ ρ} {now sched st src ord rid}
                  → toℕ i < lo
                  → Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                  → freshId sourceᵏ (Sched.mint sched) ≡ src
                  → freshId ordinalᵏ (Sched.mint sched) ≡ ord
                  → freshId regᵏ (Sched.mint sched) ≡ rid
                  → subscribeE⇓ (Θ , input i , ρ) κ now sched st
                      ( oneSeg (map valueᵖ sync ∷ [])
                      , record sched
                          { mint = setAt regᵏ (suc rid)
                                     (setAt sourceᵏ (suc src)
                                       (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                          ; live = record { source = src ; ordinal = ord
                                          ; elemTy = lookup Γ i
                                          ; pending = resolve now (d ∷ ds) }
                                   ∷ Sched.live sched }
                      , register rid (atDyn src lo) κ st )

  subs-of : ∀ {lo u Θ} {ts} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
              {now sched st}
          → subscribeE⇓ (Θ , ofᵉ ts , ρ) κ now sched st
              (oneSeg (oneShotBurst (map (λ tm → evalWith tm ρ) ts)) , sched , st)

  subs-empty : ∀ {lo u Θ} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
                 {now sched st}
             → subscribeE⇓ {u = u} (Θ , emptyᵉ , ρ) κ now sched st
                 (oneSeg (oneShotBurst []) , sched , st)

  -- `take(0)` NEVER SUBSCRIBES ITS SOURCE, which was measured rather
  -- than assumed: the operator completes on subscription and the
  -- source is not touched at all.
  subs-take-zero : ∀ {lo u Θ} {ρ : Env Γ Θ} {count} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo u t} {now sched st}
                 → evalWith count ρ ≡ zero
                 → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st
                     (oneSeg (oneShotBurst []) , sched , st)

  subs-take-suc : ∀ {lo u Θ} {ρ : Env Γ Θ} {count k} {b : Exp Γ [] [] Θ u}
                    {κ : Path Γ lo u t} {now sched st nid segs₁ sched₁ st₁ r}
                → evalWith count ρ ≡ suc k
                → freshId nodeᵏ (Sched.mint sched) ≡ nid
                → subscribeE⇓ (Θ , b , ρ) (take-f nid ↠ κ) now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                    (installNode nid (take-st (suc k)) st)
                    (segs₁ , sched₁ , st₁)
                → pushSegs⇓ now (take-f nid) κ segs₁ sched₁ st₁ r
                → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st r

  -- THE BRACKET IS OPENED BY THE INSTALL AND CLOSED WHEN THE
  -- SUBSCRIBE CALL RETURNS, WHICH IS WHERE THE BIT GOES DOWN.  No
  -- buffer is kept and no flush is owed: a subscription hands its
  -- whole output back as BURSTS, so the group the bracket wants is
  -- what `batchVals` reads straight off the burst it is stepping.
  subs-batchSync : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo (u ×ᵗ listᵗ u) t}
                     {now sched st nid segs₁ sched₁ st₁ out sched₂ st₂}
                 → freshId nodeᵏ (Sched.mint sched) ≡ nid
                 → subscribeE⇓ (Θ , b , ρ) (batchSync-f nid ↠ κ) now
                     (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                     (installNode nid (batchSync-st true) st)
                     (segs₁ , sched₁ , st₁)
                 → pushSegs⇓ now (batchSync-f nid) κ segs₁ sched₁ st₁
                     (out , sched₂ , st₂)
                 → subscribeE⇓ (Θ , batchSyncᵉ b , ρ) κ now sched st
                     (out , sched₂ , installNode nid (batchSync-st false) st₂)

  -- A MAP INSTALLS NOTHING, WHICH IS WHY THIS ARM IS SHORTER THAN
  -- EVERY OTHER SUBSCRIBE ARM HERE.  There is no node to mint, so no
  -- freshness premise and no advanced mint in the recursive call.
  subs-map : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f : Fn Γ [] [] Θ s u}
               {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
               {now sched st segs₁ sched₁ st₁ r}
           → subscribeE⇓ (Θ , b , ρ) (map-f (Θ , f , ρ) ↠ κ) now sched st
               (segs₁ , sched₁ , st₁)
           → pushSegs⇓ now (map-f (Θ , f , ρ)) κ segs₁ sched₁ st₁ r
           → subscribeE⇓ (Θ , mapᵉ f b , ρ) κ now sched st r

  subs-scan : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f} {i : Tm Γ [] [] Θ u}
                {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
                {now sched st nid segs₁ sched₁ st₁ r}
            → freshId nodeᵏ (Sched.mint sched) ≡ nid
            → subscribeE⇓ (Θ , b , ρ) (scan-f (Θ , f , ρ) nid ↠ κ) now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (cell-st (evalWith i ρ)) st)
                (segs₁ , sched₁ , st₁)
            → pushSegs⇓ now (scan-f (Θ , f , ρ) nid) κ segs₁ sched₁ st₁ r
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

  -- THE UNFOLDING IS UNCONDITIONAL, AND THAT CONCEDES NOTHING.  A
  -- machine comparing the unfolding's synchronous size against a
  -- number its caller handed it has that number among none of these
  -- indices, so no premise here could pin it; the comparison is owed
  -- by the inhabitation proof, which is where a measure belongs, since
  -- the unfolding is larger than the term it replaces and nothing here
  -- is structural in it.
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
  -- why every other arm passes its environment down untouched.
  subs-mint : ∀ {lo u Θ} {ρ : Env Γ Θ} {body : Exp Γ [] [] (uniqᵗ ∷ Θ) u}
                {κ : Path Γ lo u t} {now sched st src r}
            → freshId sourceᵏ (Sched.mint sched) ≡ src
            → subscribeE⇓ (uniqᵗ ∷ Θ , body , src ∷ᵉ ρ) κ now
                (record sched
                   { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
                st r
            → subscribeE⇓ (Θ , mintᵉ body , ρ) κ now sched st r

-- ONE CONSTRUCTOR WHERE A RUNNING MACHINE HAS TWO, AND THE MISSING ONE
-- IS THE POINT.  The machine asks whether what arrived is written
-- shallower than the component it stands at, and answers the negative
-- case by minting an instance and closing it dry.  Here the hop's
-- premise IS a sub-derivation at the arriving value, so there is
-- nothing to ask and no arm to answer.
--
-- A SUBSCRIBE ANSWERS AT BOTH TYPES AT ONCE, which is why one segment
-- is a PAIR and not just a value list.  `subscribeE⇓` hands back a
-- burst at `u` beside a stream already at `t`, and both come from the
-- one subscribe this constructor ran -- so segmenting further cannot
-- make the order between them unaskable, the way it does for the order
-- between two inners.  It has to be decided, and `foldVSegs⇓` decides
-- it.
data subscribeInner⇓ {n} {Γ} {t} {e} where
  inner : ∀ {u lo op allNid} {κ : Path Γ lo u t} {now}
            {o : Val Γ (obs u)} {sched st inst segs sched′ st′ done}
        → freshId nodeᵏ (Sched.mint sched) ≡ inst
        → subscribeE⇓ o (from-inner op allNid inst ↠ κ) now
            (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st
            (segs , sched′ , st′)
        → segsCompleted segs ≡ done
        → subscribeInner⇓ op allNid κ now o sched st
            (inst , segVSegs segs , done , sched′ , st′)

-- EACH COLLAPSE CARRIES THE SIDE CONDITION THAT DISTINGUISHES IT, so
-- no fallback here stands free.  A prover that CHOOSES its own run is
-- not the machine, and for it a premise-free fallback is an arm
-- available at every input -- and every one of these has an empty
-- value column, which would discharge any statement quantified over
-- SOME derivation with a reducible column.
data thruConsume⇓ {n} {Γ} {t} {e} where

  consume-all-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {sched₀ st₀} {lim act q od}
                      {inst segs done sched₁ st₁}
                  → lookupNode nid (EvalSt.nodes st₀)
                      ≡ just (mergeAll-st {t = u} lim act q od)
                  → hasRoom lim act ≡ true
                  → subscribeInner⇓ mergeAllᵒ nid κ now o sched₀ st₀
                      (inst , segs , done , sched₁ , st₁)
                  → thruConsume⇓ mergeAllᵒ nid κ now o sched₀ st₀
                      ( segs , sched₁
                      , record st₁
                          { nodes = mergeAllBump nid done (EvalSt.nodes st₁) } )

  consume-all-enqueue : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {sched₀ st₀} {lim act q od}
                      → lookupNode nid (EvalSt.nodes st₀)
                          ≡ just (mergeAll-st {t = u} lim act q od)
                      → hasRoom lim act ≡ false
                      → thruConsume⇓ mergeAllᵒ nid κ now o sched₀ st₀
                          ( [] , sched₀
                          , record st₀
                              { nodes = setNode nid
                                  (mergeAll-st lim act (q ++ o ∷ []) od)
                                  (EvalSt.nodes st₀) } )

  consume-all-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                    {o : Val Γ (obs u)} {sched₀ st₀}
                  → consumeUsable mergeAllᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                  → thruConsume⇓ mergeAllᵒ nid κ now o sched₀ st₀
                      ([] , sched₀ , st₀)

  consume-switch-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                         {o : Val Γ (obs u)} {sched₀ st₀} {cur od}
                         {sched₁ st₁} {inst segs done sched₂ st₂}
                     → lookupNode nid (EvalSt.nodes st₀) ≡ just (switch-st cur od)
                     → switchKill cur sched₀ st₀ ≡ (sched₁ , st₁)
                     → subscribeInner⇓ switchᵒ nid κ now o sched₁ st₁
                         (inst , segs , done , sched₂ , st₂)
                     → thruConsume⇓ switchᵒ nid κ now o sched₀ st₀
                         ( segs , sched₂
                         , record st₂
                             { nodes = setNode nid
                                 (switch-st (if done then nothing else just inst) od)
                                 (EvalSt.nodes st₂) } )

  consume-switch-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                       {o : Val Γ (obs u)} {sched₀ st₀}
                     → consumeUsable switchᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                     → thruConsume⇓ switchᵒ nid κ now o sched₀ st₀
                         ([] , sched₀ , st₀)

  consume-exhaust-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {sched₀ st₀} {od}
                          {inst segs done sched₁ st₁}
                      → lookupNode nid (EvalSt.nodes st₀)
                          ≡ just (exhaust-st false od)
                      → subscribeInner⇓ exhaustᵒ nid κ now o sched₀ st₀
                          (inst , segs , done , sched₁ , st₁)
                      → thruConsume⇓ exhaustᵒ nid κ now o sched₀ st₀
                          ( segs , sched₁
                          , record st₁
                              { nodes = setNode nid (exhaust-st (not done) od)
                                  (EvalSt.nodes st₁) } )

  consume-exhaust-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                        {o : Val Γ (obs u)} {sched₀ st₀}
                      → consumeUsable exhaustᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                      → thruConsume⇓ exhaustᵒ nid κ now o sched₀ st₀
                          ([] , sched₀ , st₀)

data thruWalk⇓ {n} {Γ} {t} {e} where

  walk-nil : ∀ {u lo op nid} {κ : Path Γ lo u t} {now} {sched₀ st₀}
           → thruWalk⇓ op nid κ now [] sched₀ st₀ ([] , sched₀ , st₀)

  walk-cons : ∀ {u lo op nid} {κ : Path Γ lo u t} {now}
                {o : Val Γ (obs u)} {os sched₀ st₀}
                {segs₁ sched₁ st₁} {segs₂ sched₂ st₂}
            → thruConsume⇓ op nid κ now o sched₀ st₀ (segs₁ , sched₁ , st₁)
            → thruWalk⇓ op nid κ now os sched₁ st₁ (segs₂ , sched₂ , st₂)
            → thruWalk⇓ op nid κ now (o ∷ os) sched₀ st₀
                (segs₁ ++ segs₂ , sched₂ , st₂)

data mergeAllDrain⇓ {n} {Γ} {t} {e} where

  drain-nil : ∀ {s lo allNid} {κ : Path Γ lo s t} {now} {lim act od sched₀ st₀}
            → mergeAllDrain⇓ {s = s} allNid κ now lim act od [] sched₀ st₀
                ([] , act , [] , sched₀ , st₀)

  drain-no-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now}
                    {lim act od} {o : Val Γ (obs s)} {q sched₀ st₀}
                → hasRoom lim act ≡ false
                → mergeAllDrain⇓ allNid κ now lim act od (o ∷ q) sched₀ st₀
                    ([] , act , o ∷ q , sched₀ , st₀)

  -- THE SHORTENED QUEUE IS WRITTEN BEFORE THE SUBSCRIBE, NOT AFTER THE
  -- WHOLE DRAIN.  A batch write-back leaves the node holding the items
  -- already spent, so anything re-entering this node mid-drain reads a
  -- queue that is no longer true — and rxjs takes the item OUT of the
  -- buffer before it subscribes it, so the batch form was the one that
  -- diverged.
  drain-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now}
                 {lim act od} {o : Val Γ (obs s)} {q sched₀ st₀}
                 {inst segs done sched₁ st₁} {segs′ act′ q′ sched₂ st₂}
             → hasRoom lim act ≡ true
             → subscribeInner⇓ mergeAllᵒ allNid κ now o sched₀
                 (record st₀
                    { nodes = setNode allNid (mergeAll-st {t = s} lim act q od)
                        (EvalSt.nodes st₀) })
                 (inst , segs , done , sched₁ , st₁)
             → mergeAllDrain⇓ allNid κ now lim
                 (if done then act else suc act) od q sched₁ st₁
                 (segs′ , act′ , q′ , sched₂ , st₂)
             → mergeAllDrain⇓ allNid κ now lim act od (o ∷ q) sched₀ st₀
                 (segs ++ segs′ , act′ , q′ , sched₂ , st₂)

data innerFinish⇓ {n} {Γ} {t} {e} where

  finish-all-drain : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                       {vals : List (Val Γ s)} {sched st} {lim act q od}
                       {segs act′ q′ sched′ st′}
                   → mergeAllDrain⇓ allNid κ now lim (pred act) od q sched st
                       (segs , act′ , q′ , sched′ , st′)
                   → innerFinish⇓ mergeAllᵒ allNid inst κ now vals sched st
                       (just (mergeAll-st {t = s} lim act q od))
                       ( (vals , []) ∷ segs , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched′
                       , record st′
                           { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                               (EvalSt.nodes st′) } )

  finish-switch-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                          {vals : List (Val Γ s)} {sched st} {c od}
                      → (c ≡ᵇ inst) ≡ true
                      → innerFinish⇓ switchᵒ allNid inst κ now vals sched st
                          (just (switch-st (just c) od))
                          ( oneVSeg vals , od , sched
                          , record st
                              { nodes = setNode allNid (switch-st nothing od)
                                  (EvalSt.nodes st) } )

  finish-exhaust-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                           {vals : List (Val Γ s)} {sched st} {act od}
                       → innerFinish⇓ exhaustᵒ allNid inst κ now vals sched st
                           (just (exhaust-st act od))
                           ( oneVSeg vals , od , sched
                           , record st
                               { nodes = setNode allNid (exhaust-st false od)
                                   (EvalSt.nodes st) } )

  finish-nil : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                 {vals : List (Val Γ s)} {sched st ns}
             → finishUsable op s inst ns ≡ false
             → innerFinish⇓ op allNid inst κ now vals sched st ns
                 (oneVSeg vals , false , sched , st)

data innerReact⇓ {n} {Γ} {t} {e} where

  react-false : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                  {vals : List (Val Γ s)} {sched st}
              → innerReact⇓ op allNid inst κ now vals sched st false
                  (oneVSeg vals , false , sched , st)

  react-alive : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                  {vals : List (Val Γ s)} {sched st}
              → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true
              → innerReact⇓ op allNid inst κ now vals sched st true
                  (oneVSeg vals , false , sched , st)

  react-dead : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                 {vals : List (Val Γ s)} {sched st r}
             → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
             → innerFinish⇓ op allNid inst κ now vals sched st
                 (lookupNode allNid (EvalSt.nodes st)) r
             → innerReact⇓ op allNid inst κ now vals sched st true r

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
               {now} {vals : List (Val Γ s)} {fin sched st}
           → stepFrame⇓ now (map-f fn) κ vals fin sched st
               (oneVSeg (map (applyClo fn) vals) , fin , sched , st)

  step-scan : ∀ {s u lo} {fn : FnClo Γ (u ×ᵗ s) u} {nid} {κ : Path Γ lo u t}
                {now} {vals : List (Val Γ s)} {fin sched st}
            → stepFrame⇓ now (scan-f fn nid) κ vals fin sched st
                (injectRoot (scanDispatch fn nid vals fin sched st
                  (lookupNode nid (EvalSt.nodes st))))

  step-take : ∀ {s lo nid} {κ : Path Γ lo s t}
                {now} {vals : List (Val Γ s)} {fin sched st}
            → stepFrame⇓ now (take-f nid) κ vals fin sched st
                (injectRoot (takeDispatch nid vals fin sched st
                  (lookupNode nid (EvalSt.nodes st))))

  step-batchSync : ∀ {s lo nid} {κ : Path Γ lo (s ×ᵗ listᵗ s) t}
                     {now} {vals : List (Val Γ s)} {fin sched st}
                 → stepFrame⇓ now (batchSync-f nid) κ vals fin sched st
                     ( oneVSeg {u = s ×ᵗ listᵗ s}
                         (batchDispatch nid vals st
                           (lookupNode nid (EvalSt.nodes st)))
                     , fin , sched , st )

  step-from-inner : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                      {now} {vals : List (Val Γ s)} {fin sched st r}
                  → innerReact⇓ op allNid inst κ now vals sched st fin r
                  → stepFrame⇓ now (from-inner op allNid inst) κ
                      vals fin sched st r

  step-thru-outer : ∀ {u lo op nid} {κ : Path Γ lo u t}
                      {now} {vals : List (Val Γ (obs u))} {fin sched st}
                      {segs sched′ st′}
                  → thruWalk⇓ op nid κ now vals sched st
                      (segs , sched′ , st′)
                  → stepFrame⇓ now (thru-outer op nid) κ vals fin sched st
                      (segs , thruWrap op nid fin (sched′ , st′))

data pushBurst⇓ {n} {Γ} {t} {e} where

  push-nil : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now sched st}
           → pushBurst⇓ now f κ [] sched st ([] , sched , st)

  push-cons : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now}
                {b : Burst Γ s} {bs sched st} {vs c}
                {segs fin′ sched₁ st₁} {rest sched₂ st₂}
            → splitEvents b ≡ (vs , c)
            → stepFrame⇓ now f κ vs c sched st
                (segs , fin′ , sched₁ , st₁)
            → pushBurst⇓ now f κ bs sched₁ st₁ (rest , sched₂ , st₂)
            → pushBurst⇓ now f κ (b ∷ bs) sched st
                (stepSegs segs fin′ ++ rest , sched₂ , st₂)

-- PUSHING A SEGMENTED ANSWER IS PUSHING EACH SEGMENT'S OWN STREAM, and
-- the segment's root column crosses the frame untouched -- a frame
-- transforms values at `s`, and what already reached `t` is past it.
-- It becomes a leading segment of the answer, which is the same
-- root-before-values rule `foldVSegs⇓` resolves by.
--
-- FOUR SUBSCRIBE ARMS USED TO DROP THAT COLUMN ON THE FLOOR: `take`,
-- `map`, `scan` and a flattener's `sub-all` all bound their inner
-- subscribe's roots and answered with the push's result alone, so only
-- `batchSync` carried them.  Nothing showed it, because nothing on
-- this side mints a root emit yet.  Threading the whole segment makes
-- the drop unwritable rather than merely noticed.
data pushSegs⇓ {n} {Γ} {t} {e} where

  psegs-nil : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now sched st}
            → pushSegs⇓ now f κ [] sched st ([] , sched , st)

  psegs-cons : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {now}
                 {bs : Stream Γ s} {rs ss sched st}
                 {out sched₁ st₁} {rest sched₂ st₂}
             → pushBurst⇓ now f κ bs sched st (out , sched₁ , st₁)
             → pushSegs⇓ now f κ ss sched₁ st₁ (rest , sched₂ , st₂)
             → pushSegs⇓ now f κ ((bs , rs) ∷ ss) sched st
                 (([] , rs) ∷ out ++ rest , sched₂ , st₂)

-- THIS IS WHERE A FLATTENER'S TWO INNERS ARE WALKED, AND SO WHERE THE
-- ORDER BETWEEN THEM IS EITHER KEPT OR LOST.  The outer is subscribed
-- with the `thru-outer` frame already pushed, and what comes back is
-- pushed through that frame here -- so an inner that answers with a
-- burst at `u` and one that answers with a stream already at `t` are
-- consumed by the same walk, and the result is handed UP as this
-- subscribe's own answer.  Nothing between here and the root folds.
-- So a carrier holding one group at `u` beside one stream at `t` has
-- to pick an order, and the corpus's exchanged pair -- two programs
-- carrying the same values out of the flattener and out of the share,
-- answered `[7,1,2]` and `[1,2,7]` -- refutes every fixed pick.  The
-- order has to be part of the ANSWER, one segment per inner, all the
-- way up to whoever folds.
--
-- DEAD ROUTE: fold each inner rootward inside the consume, so that no
--   subscribe ever holds both at once and no carrier is needed.  It is
--   not the module direction that blocks it, which a closure would
--   escape: the termination checker has to SEE the fold applied to a
--   structurally smaller path, and an applied function argument hides
--   exactly that.  Threading the fold in therefore fails on its own
--   terms, and calling it directly puts `reducible` inside this cycle
--   -- `stepFrameAny!` reaches `red-val` for values a registry path
--   carries no candidate for, which `sharedConnect⇓` already records.
data subscribeAll⇓ {n} {Γ} {t} {e} where

  sub-all : ∀ {u lo op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
              {κ : Path Γ lo u t} {now sched st nid segs₁ sched₁ st₁ r}
          → freshId nodeᵏ (Sched.mint sched) ≡ nid
          → subscribeE⇓ b (thru-outer op nid ↠ κ) now
              (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
              (installNode nid ns st)
              (segs₁ , sched₁ , st₁)
          → pushSegs⇓ now (thru-outer op nid) κ segs₁ sched₁ st₁ r
          → subscribeAll⇓ op ns b κ now sched st r

-- THE CONNECT'S OWN GUARD IS NOT INDEXED HERE EITHER, AND THE SAME
-- RULING AS THE UNFOLD'S APPLIES: a run's answer to a question this
-- relation does not name is owed by the inhabitation proof.

-- A SYNCHRONOUS SHARE NEVER CONSULTS ITS OWN REGISTRY, and that -- not
-- the order the registry is read in -- is what the oracle measures.
-- Both arms hand the definition's burst BACK, at the share's element
-- type, so the subscriber whose arrival triggered the connect receives
-- every value and the fan-out below is not entered at all.  It is
-- entered only from `foldPath⇓`'s sink clause, which a chain reaches
-- when an ASYNCHRONOUS arrival is folded -- so a hot-fed share fans out
-- per arrival and agrees with rxjs, and a share whose definition emits
-- during the connect delivers to exactly one observer however the
-- fan-out is written.
--
-- THE RESULT TYPE IS NOT WHAT STANDS IN THE WAY.  A fan-out's emits are
-- at `t`, because a share's subscribers sink at unrelated points of the
-- tree, and the burst its caller still has path to push is at `u`; one
-- segment carries both, so spending the emission on the registry and
-- answering the caller stopped being exclusive.  Nor is a candidate the
-- gap at either end: `red-val` is total, so the arrival side carries no
-- premise, and `stepFrameAny!` asks nothing about the frames of a path
-- it read out of the registry.  What is left is the MEASURE, and the
-- cycle it has to fund is one edge long: a fold reaches `stepFrameAny!`,
-- which reaches `inner!`, which applies `red-val` at `obs s` -- and
-- that arm is `reducible`.  Every step of that runs DOWNWARD today, so
-- adding the one call from the connect closes it, and nineteen
-- definitions across the two modules become a single mutual block.

-- AND NONE OF THE ACCESSIBILITIES ALREADY IN THE CYCLE CAN FUND IT,
-- WHICH IS WHAT MAKES THE OUTERMOST COMPONENT LOAD-BEARING RATHER THAN
-- OUTER.  `reducible` re-seeds both of `redExpAcc`'s -- the input
-- ceiling at the body's own top and the expression size at its own
-- `gsizeᵉ` -- and `red-val` at `obs` is exactly that call.  So the
-- inner returning through the fold arrives with a fresh ceiling, a
-- fresh size, and a body standing in no relation to the one the cycle
-- started at, and the fold's own floor argument is re-seeded the same
-- way when the connect calls it.  That is sound today only because
-- `red-val` sits BELOW the candidate and the call is not recursive.

-- SO THE PRICE IS ONE QUANTITY THAT SURVIVES THE WHOLE LOOP, AND THE
-- ARITHMETIC OF IT IS ALREADY PROVEN.  The quantity is the unconnected
-- SHARE count, summed over the slot table: a shared slot reads one
-- until the connected set holds it, a scripted slot reads nought
-- whatever the set holds.  It drops strictly across the connect arm on
-- exactly the two facts that arm already binds -- the slot's `shared`
-- shape and the membership reading `false` -- so neither is a new
-- hypothesis nor an arithmetic side condition, but the branch the
-- clause is already standing in.  Conditioning on the shape is what
-- makes it true rather than what weakens it: without it a scripted
-- slot connects and moves nothing.

-- AND THE HALF THAT READS LIKE A MONOTONICITY THEOREM IS TRUE FOR A
-- SYNTACTIC REASON, WHICH IS NOT THE SAME AS BEING FREE.  The count is
-- taken over the slot TABLE and the connected set, and neither can
-- move against it: the table has ONE writer in the whole evaluator,
-- the run's own initialisation, and the set is only ever consed, since
-- every state below that initialisation is reached by record update.
-- The checker cannot read either off a state it was handed, so the
-- pair is still proven once, as a relation between two states' fields.

-- AND IT IS PROVEN ABOUT THE DERIVATION, WHICH COSTS NO RESULT TYPE
-- ANYTHING.  Every builder's Σ already carries its own derivation as a
-- conjunct, and so does the candidate's observable arm, so the fact is
-- read off what is there rather than added to it: slots definitionally
-- equal, membership preserved.  Indexing that pair by the two FIELDS
-- rather than by the two states is not a stylistic choice -- a step
-- rebuilds the schedule by record update, which is not definitionally
-- the schedule it came from, so a state-indexed form is refused at the
-- recursive call.

-- AND MEMBERSHIP-PRESERVATION IS THE FORM THE COUNT WANTS, rather than
-- a cons.  A step does not connect once; it hands back a set reached
-- by some number of connects, and what its induction can carry is that
-- whatever was a member still is.  The antitone form takes exactly
-- that, and the cons form is its special case at the connect itself.

-- THE RING IS ONE CLAUSE PER CONSTRUCTOR OF EVERY RELATION THE CYCLE
-- PASSES THROUGH, and this relation calling a fold is what fixes how
-- many that is: the thirteen of the subscribe cycle AND the five of the
-- fold's, in one block, because the connect joined the two into one.

-- AND THAT IS WHAT PAYS FOR THE RE-SEEDING RATHER THAN ROUTING ROUND
-- IT.  The count is the OUTERMOST component, so the two accessibilities
-- `reducible` seeds afresh are seeded UNDER a component that has
-- already dropped, and the lexicographic step belongs to the loop
-- rather than to any one call in it.  Which is why the re-seeding
-- stopped being the obstruction the moment the outer component was
-- found: it was only ever fatal to an order with nothing above it.

-- AND THE MEASURE IS OWED ONLY BECAUSE THE FOLD BEING CALLED IS THE
-- BUILDER'S, WHICH IS WHY IT IS WORTH SAYING WHAT THE OTHER FOLD COSTS
-- RATHER THAN LEAVING IT LOOKING UNTRIED.  A fold on the REDUCIBILITY
-- side closes no cycle at all, being a member of the candidate's own
-- recursion, and nearly everything it must carry is free: `RedFrame`
-- is the unit at four frames and `RedFn` at the two holding a closure,
-- which `redFnAcc` gives with its accessibilities seeded at their own
-- subjects exactly as `reducible` seeds `redExpAcc`, and `RedNode` is
-- the unit at five of six.  The sixth is `scan-f`, whose cell holds a
-- VALUE that leaves the frame -- the contrast `redTakeVals`'s header
-- draws against a cell holding a count -- and that one obligation is
-- what the route dies on.

-- AND THE FAN-OUT IS THE RIGHT ANSWER, WHICH IS MEASURED RATHER THAN
-- ARGUED.  Delivering the definition's burst value-major, re-reading
-- the registry between values, reproduces rxjs by hand on all three
-- shapes of `typescript/corpus/depth-first.ndjson`'s re-entrant rows,
-- the NESTED one included -- a share read through another share, where
-- the inner fan-out is entered once per outer value and the two orders
-- compose with nothing ranking them.  So there is no question left
-- about the ORDER a share emits in, and no significance ordering
-- across nested shares is wanted.

-- THE OPEN QUESTION IS WHERE A FAN-OUT'S EMITS ATTACH, AND IT IS NOT
-- ANSWERED BY A SECOND RESULT COMPONENT.  That reading -- a burst at
-- `u` for the caller to push and a stream already at `t` beside it --
-- is refuted by the last two rows of that corpus, which are the same
-- flattener with its two inners exchanged: both hand back the same
-- values in both components, and rxjs answers `[7,1,2]` for one and
-- `[1,2,7]` for the other.  No fixed rule for concatenating the two
-- reads both, because what separates them is WHEN each was produced.

-- WHAT SURVIVES THAT PAIR IS PUSHING WHERE A VALUE IS PRODUCED.  A
-- flattener's walk folds each inner's burst rootward as it consumes
-- it, rather than collecting the inners and handing the caller one
-- list, so the two components are never both live and the order is
-- carried by the walk instead of by a rule.  What that costs is the
-- fan-out running inside the reducibility cycle, which is what the
-- block below prices.

-- AND THE CONNECT IS THE FAN-OUT'S ONLY CONSUMER, WHICH IS WHY IT HAS
-- TO FOLD.  A subscribe NEVER walks its own path: every leaf hands its
-- values back in the segment's unresolved column and whoever consumed
-- that subscribe pushes them through its frame.  A share's definition
-- is subscribed at `share-sink i` and nothing consumes it, so with the
-- connect handing those segments straight up, `dispatchShare⇓` was
-- unreachable and the registry was read by nobody -- a joiner, and
-- every re-entrant subscriber, saw an empty stream while the FIRST
-- subscriber still answered correctly off the raw column.  Folding
-- here is the missing consumer and nothing else; the trigger then
-- receives its own values the way a joiner does, through the chain it
-- registered, so its unresolved column is empty by the same argument
-- that makes `slot-join`'s empty.

-- DEAD ROUTE: answering at `t` -- folding the burst through the path
--   INSIDE the subscribe, so the sink clause reaches the fan-out and
--   `sharedConnect⇓` has nothing left to hand back.  It is blocked by
--   `Red`, not by the evaluator: the candidate's observable arm reads
--   `Red (obs u) b` as a subscription derivation together with
--   `StreamSat (Red u)` over its result, and that recursive occurrence
--   at a STRICTLY SMALLER type is the whole of the Girard-Tait descent.
--   The root type is quantified INSIDE that arm -- `∀ {t} (κ : Path Γ lo
--   u t)` -- so a result at `t` makes the conjunct `StreamSat (Red t)`,
--   which is not smaller, is impredicative, and ranges over `obs u`
--   itself.  The descent is denominated in the SOURCE type, and a
--   root-typed answer has no source type in it.  Worth stating because
--   the per-value push was refuted with the root type attached and the
--   two came apart here: it is the TYPE that kills it, and no carrier
--   that keeps the root type can be rescued by emitting differently.

-- DEAD ROUTE: schedule the connect's emission as arrivals and let the
--   DRAIN fan it out, which is attractive because it reuses the one
--   path already measured to agree with rxjs and leaves the fold on
--   the side that builds it today.  The exchanged pair refutes it: a
--   drained emission lands in `eval-run`'s `rest`, after everything
--   the subscribe produced, so both rows would answer with the share's
--   values last and one of them answers with them first.  Deferring is
--   a fixed position under another name, and the pair refutes those.

-- DEAD ROUTE: fold on the REDUCIBILITY side instead, so no cycle is
--   closed and no measure is owed, paying for it with `RedNode` at the
--   one frame whose cell holds a value.  Supplying that needs the
--   candidate parameterised over a state predicate, which is the only
--   form that survives the impredicativity -- written concretely it
--   reaches the candidate at every fold's accumulator type with
--   nothing ordering those, and quantified inside the arm it sits one
--   level above the candidate it instantiates.  The parameter was
--   built, and it puts the predicate at BOTH SIGNS of the observable
--   arm, which takes a state and answers with one.  `RedNode`'s own
--   header carries the routes out of that.

-- RECOVERY: git show 104d61de^:agda/src/Rx/Evaluator/Unconn-Arith.agda
--   restores the count's whole arithmetic proven -- consing a source
--   never raises it, a slot reading one drops the sum strictly when
--   its own source is consed, and a `shared` slot outside the set
--   reads one.  Chained, that last pair is the connect step from the
--   two facts the arm binds.  The count itself is in the same commit's
--   `git show 104d61de^:agda/src/Rx/Evaluator.agda`, and `Slot` has
--   not moved since, so both port back unedited.  Deleted with them
--   was `Refuted.Scripted-Connect`, which refutes the membership-ONLY
--   form and so refutes nothing the module proves -- it is the witness
--   that the `shared` premise is load-bearing rather than defensive.
data sharedConnect⇓ {n} {Γ} {t} {e} where

  connect-live : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {now sched st rid segs sched₁ st₁}
                   {out sched₂ st₂}
               → freshId regᵏ (Sched.mint sched) ≡ rid
               → subscribeE⇓ ([] , d , []ᵉ) (share-sink i ≤-refl) now
                   (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                   (register rid (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                   (segs , sched₁ , st₁)
               → segsCompleted segs ≡ false
               → foldVSegs⇓ now (share-sink i ≤-refl) (segVSegs segs) false
                   sched₁ st₁ (out , sched₂ , st₂)
               → sharedConnect⇓ i d κ below now sched st
                   (([] , out) ∷ [] , sched₂ , st₂)

  connect-died : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {now sched st rid segs sched₁ st₁}
                   {out sched₂ st₂}
               → freshId regᵏ (Sched.mint sched) ≡ rid
               → subscribeE⇓ ([] , d , []ᵉ) (share-sink i ≤-refl) now
                   (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                   (register rid (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
                   (segs , sched₁ , st₁)
               → segsCompleted segs ≡ true
               → foldVSegs⇓ now (share-sink i ≤-refl) (segVSegs segs) true
                   sched₁ st₁ (out , sched₂ , st₂)
               → sharedConnect⇓ i d κ below now sched st
                   ( ([] , out) ∷ [] , sched₂
                   , record st₂
                       { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                       ; completedSources =
                           toℕ i ∷ EvalSt.completedSources st₂ } )

data subscribeSharedSlot⇓ {n} {Γ} {t} {e} where

  slot-spent : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                 {below : toℕ i < lo} {now sched st}
             → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
             → subscribeSharedSlot⇓ i d κ below now sched st
                 (oneSeg spentBurst , sched , st)

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
-- witness.  `shareFinish`, `shareAdmit` and `shareDying` compute, so
-- they stay applied.
data dispatchShare⇓ {n} {Γ} {t} {e} where
  disp : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
           {vals fin sched st r}
       → shareWalk⇓ now i vals fin sched (shareDying i fin st) r
       → dispatchShare⇓ {lo = lo} now i below vals fin sched st
           (shareFinish i fin r)

-- THE LAST VALUE IS TOLD APART BY ITS TAIL BEING EMPTY, which is what
-- carries `fin` to exactly one delivery.  A share's end belongs to the
-- emission's final value and to no earlier one, and matching the tail
-- says so without a Bool computed from a length.
data shareWalk⇓ {n} {Γ} {t} {e} where
  walk-nil : ∀ {now} {i : Fin n} {fin sched st}
           → shareWalk⇓ now i [] fin sched st ([] , sched , st)

  walk-last : ∀ {now} {i : Fin n} {v fin sched st r}
            → shareGo⇓ now i v fin
                (shareAdmit i (EvalSt.registry st)) sched st r
            → shareWalk⇓ now i (v ∷ []) fin sched st r

  walk-more : ∀ {now} {i : Fin n} {v w vs fin sched₀ st₀}
                {emits sched₁ st₁ rest sched₂ st₂}
            → shareGo⇓ now i v false
                (shareAdmit i (EvalSt.registry st₀)) sched₀ st₀
                (emits , sched₁ , st₁)
            → shareWalk⇓ now i (w ∷ vs) fin sched₁ st₁ (rest , sched₂ , st₂)
            → shareWalk⇓ now i (v ∷ w ∷ vs) fin sched₀ st₀
                (emits ++ rest , sched₂ , st₂)

-- THE CANCELLATION TEST STAYS A PREMISE RATHER THAN A SIDE CONDITION.
-- It is decidable and it decides which of two clauses ran, so the
-- relation carries the answer as an equation and the two arms cannot
-- both apply.  `go-live` is where the threading shows: what the tail is
-- handed is the head's own results.
data shareGo⇓ {n} {Γ} {t} {e} where
  go-nil : ∀ {lo now} {i : Fin n} {v fin sched st}
         → shareGo⇓ {lo = lo} now i v fin [] sched st ([] , sched , st)

  go-cut : ∀ {lo now} {i : Fin n} {v fin rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st r}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
         → shareGo⇓ now i v fin ps sched st r
         → shareGo⇓ now i v fin ((rid , p) ∷ ps) sched st r

  go-live : ∀ {lo now} {i : Fin n} {v fin rid}
              {p : Path Γ lo (lookup Γ i) t} {ps sched₀ st₀}
              {emits sched₁ st₁ rest sched₂ st₂}
          → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
          → foldPath⇓ now p (v ∷ []) fin sched₀
              (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
              (emits , sched₁ , st₁)
          → shareGo⇓ now i v fin ps sched₁ st₁ (rest , sched₂ , st₂)
          → shareGo⇓ now i v fin ((rid , p) ∷ ps) sched₀ st₀
              (emits ++ rest , sched₂ , st₂)

-- THE PATH IS WALKED SINKWARD AND THE BURST IS ASSEMBLED AT THE ROOT,
-- so the root clause is the only one that mints an emit from nothing
-- and the other two hand their own results on.  The sink clause is
-- where the floor descends: its premise is the path constructor's
-- argument, so nothing has to be carried alongside -- and with the
-- protocol out of the carrier the sink itself emits nothing, since a
-- hand-off was the one thing it used to have to say.
data foldPath⇓ {n} {Γ} {t} {e} where
  fold-root : ∀ {lo now} {vals : List (Val Γ t)} {fin sched st}
            → foldPath⇓ {lo = lo} now root vals fin sched st
                ( (map valueᵖ vals ++ (if fin then completeᵖ ∷ [] else [])) ∷ []
                , sched , st )

  fold-sink : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
                {vals fin sched st r}
            → dispatchShare⇓ now i below vals fin sched st r
            → foldPath⇓ now (share-sink i below) vals fin sched st r

  fold-step : ∀ {lo s u now} {f : Frame Γ s u}
                {path′ : Path Γ lo u t} {vals fin sched st}
                {segs fin′ sched₁ st₁} {r}
            → stepFrame⇓ now f path′ vals fin sched st
                (segs , fin′ , sched₁ , st₁)
            → foldVSegs⇓ now path′ segs fin′ sched₁ st₁ r
            → foldPath⇓ now (f ↠ path′) vals fin sched st r

-- RESOLVING AN ORDERED ANSWER, ONE SEGMENT AT A TIME AND IN ORDER.  A
-- step hands back what each inner subscribe contributed, kept apart;
-- resolving folds each segment's value group rootward on its own and
-- lays the result down AFTER the root stream that same segment already
-- sent, so the two halves of one inner stay adjacent and the inners
-- stay in the order they ran.  Concatenating the two columns instead
-- -- every group, then every root stream -- is what the corpus's
-- exchanged pair refutes.
--
-- ONLY THE LAST SEGMENT CARRIES THE `fin`.  A completion is the whole
-- path finishing, not one inner's contribution ending, so every
-- earlier segment folds with `false` and the flag is spent once.
--
-- ROOT STREAM BEFORE VALUE GROUP WITHIN ONE SEGMENT IS THE UNTESTED
-- HALF.  It is what the frame step answered before there were segments
-- at all, so the corpus cannot move on it -- and it cannot until a
-- root component stops being empty, which is a share connecting.  The
-- argument for it is that a connect fans out to subscribers already
-- registered, so that delivery ran before the subscribe holding this
-- segment existed; the leg that fills the root components is where
-- that stops being an argument.
data foldVSegs⇓ {n} {Γ} {t} {e} where
  segs-nil : ∀ {u lo now} {κ : Path Γ lo u t} {fin sched st r}
           → foldPath⇓ now κ [] fin sched st r
           → foldVSegs⇓ now κ [] fin sched st r

  segs-last : ∀ {u lo now} {κ : Path Γ lo u t} {vs rts fin sched st}
                {emits sched₁ st₁}
            → foldPath⇓ now κ vs fin sched st (emits , sched₁ , st₁)
            → foldVSegs⇓ now κ ((vs , rts) ∷ []) fin sched st
                (rts ++ emits , sched₁ , st₁)

  segs-more : ∀ {u lo now} {κ : Path Γ lo u t} {vs rts s ss fin sched st}
                {emits sched₁ st₁} {rest sched₂ st₂}
            → foldPath⇓ now κ vs false sched st (emits , sched₁ , st₁)
            → foldVSegs⇓ now κ (s ∷ ss) fin sched₁ st₁ (rest , sched₂ , st₂)
            → foldVSegs⇓ now κ ((vs , rts) ∷ s ∷ ss) fin sched st
                (rts ++ emits ++ rest , sched₂ , st₂)

data chainStep⇓ {n} {Γ} {t} {e} where
  chain-step : ∀ {a : Arrival Γ} {lo} {path : Path Γ lo (arrTy a) t}
                 {sched st r}
             → foldPath⇓ (arrTick a) path (arrVal a ∷ [])
                 (Arrival.isLast a) sched st r
             → chainStep⇓ a (lo , path) sched st r

data cascadeGo⇓ {n} {Γ} {t} {e} where
  casc-nil : ∀ {a sched₀ st₀}
           → cascadeGo⇓ a [] sched₀ st₀ ([] , sched₀ , st₀)
  casc-cut : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀ r}
           → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ true
           → cascadeGo⇓ a chains sched₀ st₀ r
           → cascadeGo⇓ a ((rid , c) ∷ chains) sched₀ st₀ r
  casc-live : ∀ {a rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀}
                {emits sched₁ st₁ rest sched₂ st₂}
            → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
            → chainStep⇓ a c sched₀
                (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
                (emits , sched₁ , st₁)
            → cascadeGo⇓ a chains sched₁ st₁ (rest , sched₂ , st₂)
            → cascadeGo⇓ a ((rid , c) ∷ chains) sched₀ st₀
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
               {segs sched₀ st₀ rest}
           → subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
               (sched-init e ins) (st-init e) (segs , sched₀ , st₀)
           → drain⇓ {e = e} fuel sched₀ st₀ rest
           → evaluate⇓ fuel e ins (resolveSegs segs ++ rest)
