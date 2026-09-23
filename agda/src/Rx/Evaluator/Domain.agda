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
-- THE ANSWER IS ROOT-ONLY, AND THE CANDIDATE TRAVELS THE OTHER WAY.
-- Nothing a subscribe hands back is at the element type: a source
-- folds what it produces down the path it was subscribed with, a
-- transformer pushes its frame onto that path and subscribes its
-- body, and what comes up is a stream at `t` beside the threaded
-- state.  So there is no burst for a caller to push, no segment to
-- resolve, and no second column for a satisfaction claim to ride --
-- which is what dissolves the dead route recorded at
-- `sharedConnect⇓`: the candidate's observable arm used to read a
-- burst OUT of the answer, and now hands its candidates DOWN, into
-- the continuation the fold runs through (`Rx.Evaluator.Reducible`).
-- The relation sees none of that: it names the fold's arguments and
-- the fold's answer, and the continuation is the builder's business.
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

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; null)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; pred; _<_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
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
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; NodeId; root; share-sink; _↠[_]_; shareAdmit;
  shareDying; shareSpend; shareFinish; from-inner; arrTick; arrVal;
  chainsOf; cascadeOpen; cascadeClose; cascadeFinish; sched-next; sched-init; st-init; NodeState; AllOp;
  RegId; Arrival; AtFloor; arrTy; memberSource; register; installNode; resolve;
  atSlot; atDyn; lowerFloor; map-f; scan-f; take-f; batchSync-f; thru-outer; cell-st; take-st;
  batchSync-st; mergeAll-st; switch-st; exhaust-st; mergeAllᵒ; switchᵒ; exhaustᵒ; lookupNode;
  setNode; hasRoom; switchKill; aliveThroughᶠ; scanDispatch; takeDispatch;
  batchDispatch; batchBuf; thruWrap; consumeUsable; finishUsable; drainSt)

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE.  Eleven families, exactly the members of the
-- evaluator's larger genuine cycle: everything else it calls is
-- structurally recursive and is APPLIED here rather than related.
--
-- A FRAME IS HANDED A GROUP, WHICH IS THE ONE STRUCTURAL FACT THE
-- WHOLE FILE RESTS ON.  Everything one incoming emit causes leaves
-- together, so a frame steps a LIST of values rather than one -- and
-- an operator bracketing the subscribe call sees the group already
-- assembled instead of having to record which side of that call it is
-- on.  A subscription itself hands back nothing at the element type:
-- its groups are folded where they are produced and only the root
-- stream comes up.
------------------------------------------------------------------

data subscribeE⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Val Γ (obs u) → Path Γ lo u t → Tick → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data subscribeInner⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → NodeId × Stream Γ t × Sched Γ × EvalSt e → Set

data thruConsume⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data thruWalk⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Tick
   → List (Val Γ (obs u)) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data mergeAllDrain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     NodeId → Path Γ lo s t → Tick → List (Val Γ (obs s))
   → Maybe ℕ → ℕ → Bool → List (Val Γ (obs s)) → Sched Γ → EvalSt e
   → Stream Γ t × ℕ × List (Val Γ (obs s)) × Sched Γ × EvalSt e → Set

data innerFinish⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
   → Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e → Set

data innerReact⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Bool
   → Stream Γ t × List (Val Γ s) × Bool × Sched Γ × EvalSt e → Set

data stepFrame⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Tick → Frame Γ s u → Path Γ lo u t
   → List (Val Γ s) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × List (Val Γ u) × Bool × Sched Γ × EvalSt e → Set

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
   → List (Val Γ (lookup Γ i)) → Bool
   → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data foldPath⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Tick → Path Γ lo u t
   → List (Val Γ u) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE ARRIVAL SPINE.  Structurally recursive in the evaluator, and
-- related here only because each of these reaches a cycle above and so
-- cannot be applied without a derivation to hand it.
------------------------------------------------------------------

data chainStep⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ) → List (Val Γ (arrTy a)) → Bool
   → AtFloor Γ (arrTy a) t → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data cascadeGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ) → List (Val Γ (arrTy a)) → Bool
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
-- lifts that shape into a step's answer, whose root stream is empty
-- because a frame that computes its own output subscribes nothing
-- and so cannot reach the root.
----------------------------------------------------------------------

injectRoot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → List (Val Γ u) × Bool × Sched Γ × EvalSt e
             → Stream Γ t × List (Val Γ u) × Bool × Sched Γ × EvalSt e
injectRoot (vs , fin , sc , st) = [] , vs , fin , sc , st

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

  -- A SOURCE FOLDS WHAT THE SLOT SAYS DOWN THE PATH IT WAS SUBSCRIBED
  -- WITH, AND ITS ANSWER IS THE FOLD'S.  One `foldPath⇓` premise per
  -- source arm, at the values the script names and the end the script
  -- implies; a source that says nothing folds the empty group with the
  -- end, because the end is a delivery of its own.
  subs-floor : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                 {Θ ρ} {now sched st r}
             → lo ≤ toℕ i
             → foldPath⇓ now κ [] true sched st r
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
                → foldPath⇓ now κ [] true sched st r
                → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

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
  -- SUBSCRIBER, ITS SYNCHRONOUS PREFIX FOLDED DOWN THE SUBSCRIBE
  -- FRAME'S PATH.  With no asynchronous tail the run is over as it
  -- starts, so the prefix and the end are ONE group and nothing is
  -- registered.
  subs-cold-sync : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                     {ok sync} {Θ ρ} {now sched st r}
                 → toℕ i < lo
                 → Sched.slots sched i ≡ scripted {ok = ok} (cold sync [])
                 → foldPath⇓ now κ sync true sched st r
                 → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  -- AND WITH A TAIL THE REGISTRATION IS MADE BEFORE THE PREFIX IS
  -- FOLDED, NOT AFTER.  A synchronous value can cut this very chain,
  -- and a cut severs REGISTRATIONS — so a source registered afterwards
  -- would go on delivering into something nothing reads.  The fold
  -- therefore runs in the registered schedule and state.
  subs-cold-async : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                      {ok sync d ds} {Θ ρ} {now sched st src ord rid r}
                  → toℕ i < lo
                  → Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                  → freshId sourceᵏ (Sched.mint sched) ≡ src
                  → freshId ordinalᵏ (Sched.mint sched) ≡ ord
                  → freshId regᵏ (Sched.mint sched) ≡ rid
                  → foldPath⇓ now κ sync false
                      (record sched
                         { mint = setAt regᵏ (suc rid)
                                    (setAt sourceᵏ (suc src)
                                      (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                         ; live = record { source = src ; ordinal = ord
                                         ; elemTy = lookup Γ i
                                         ; pending = resolve now (d ∷ ds) }
                                  ∷ Sched.live sched })
                      (register rid (atDyn src lo) κ st) r
                  → subscribeE⇓ (Θ , input i , ρ) κ now sched st r

  subs-of : ∀ {lo u Θ} {ts} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
              {now sched st r}
          → foldPath⇓ now κ (map (λ tm → evalWith tm ρ) ts) true sched st r
          → subscribeE⇓ (Θ , ofᵉ ts , ρ) κ now sched st r

  subs-empty : ∀ {lo u Θ} {ρ : Env Γ Θ} {κ : Path Γ lo u t}
                 {now sched st r}
             → foldPath⇓ now κ [] true sched st r
             → subscribeE⇓ {u = u} (Θ , emptyᵉ , ρ) κ now sched st r

  -- `take(0)` NEVER SUBSCRIBES ITS SOURCE, which was measured rather
  -- than assumed: the operator completes on subscription and the
  -- source is not touched at all.
  subs-take-zero : ∀ {lo u Θ} {ρ : Env Γ Θ} {count} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo u t} {now sched st r}
                 → evalWith count ρ ≡ zero
                 → foldPath⇓ now κ [] true sched st r
                 → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st r

  -- A TRANSFORMER PUSHES ITS FRAME AND SUBSCRIBES ITS BODY, AND THAT
  -- IS ITS WHOLE ARM.  What the body produces crosses the frame inside
  -- the body's own fold, one group at a time and in the order the
  -- groups were produced, so there is nothing left for this arm to
  -- push afterwards and its answer is the body's answer.
  subs-take-suc : ∀ {lo u Θ} {ρ : Env Γ Θ} {count k} {b : Exp Γ [] [] Θ u}
                    {κ : Path Γ lo u t} {now sched st nid r}
                → evalWith count ρ ≡ suc k
                → freshId nodeᵏ (Sched.mint sched) ≡ nid
                → subscribeE⇓ (Θ , b , ρ) (take-f nid ↠[ ≤-refl ] κ) now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                    (installNode nid (take-st (suc k)) st) r
                → subscribeE⇓ (Θ , takeᵉ count b , ρ) κ now sched st r

  -- THE BRACKET IS OPENED BY THE INSTALL AND CLOSED WHEN THE
  -- SUBSCRIBE CALL RETURNS, WHICH IS WHERE THE BIT GOES DOWN AND THE
  -- GROUP LEAVES.  Everything that reached the frame while the bit was
  -- up is in the buffer and nothing went downstream, so the flush is
  -- the last thing this subscribe answers -- which is where the
  -- TypeScript's second `defer` sits in its `merge`.
  --
  -- AND THE TWO ROUTES IN MEET AT THE BUFFER, WHICH IS WHY THERE IS
  -- ONLY ONE FLUSH.  Values reach the frame either through the body's
  -- own fold or through a registered path a share's fan-out walks
  -- during the very same call; both write the buffer, so reading it
  -- once at the boundary groups them together.  The flush is one
  -- `foldPath⇓` of the buffer's group, with the buffer's end, in the
  -- state where the bit is already down.
  subs-batchSync : ∀ {lo u Θ} {ρ : Env Γ Θ} {b : Exp Γ [] [] Θ u}
                     {κ : Path Γ lo (u ×ᵗ listᵗ u) t}
                     {now sched st nid out₁ sched₁ st₁ out₂ sched₂ st₂}
                 → freshId nodeᵏ (Sched.mint sched) ≡ nid
                 → subscribeE⇓ (Θ , b , ρ) (batchSync-f nid ↠[ ≤-refl ] κ) now
                     (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                     (installNode nid (batchSync-st {s = u} true [] false) st)
                     (out₁ , sched₁ , st₁)
                 → foldPath⇓ now κ
                     (proj₁ (batchBuf u (lookupNode nid (EvalSt.nodes st₁))))
                     (proj₂ (batchBuf u (lookupNode nid (EvalSt.nodes st₁))))
                     sched₁ (installNode nid (batchSync-st {s = u} false [] false) st₁)
                     (out₂ , sched₂ , st₂)
                 → subscribeE⇓ (Θ , batchSyncᵉ b , ρ) κ now sched st
                     (out₁ ++ out₂ , sched₂ , st₂)

  -- A MAP INSTALLS NOTHING, WHICH IS WHY THIS ARM IS SHORTER THAN
  -- EVERY OTHER SUBSCRIBE ARM HERE.  There is no node to mint, so no
  -- freshness premise and no advanced mint in the recursive call.
  subs-map : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f : Fn Γ [] [] Θ s u}
               {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
               {now sched st r}
           → subscribeE⇓ (Θ , b , ρ) (map-f (Θ , f , ρ) ↠[ ≤-refl ] κ) now sched st r
           → subscribeE⇓ (Θ , mapᵉ f b , ρ) κ now sched st r

  subs-scan : ∀ {lo s u Θ} {ρ : Env Γ Θ} {f} {i : Tm Γ [] [] Θ u}
                {b : Exp Γ [] [] Θ s} {κ : Path Γ lo u t}
                {now sched st nid r}
            → freshId nodeᵏ (Sched.mint sched) ≡ nid
            → subscribeE⇓ (Θ , b , ρ) (scan-f (Θ , f , ρ) nid ↠[ ≤-refl ] κ) now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (cell-st (evalWith i ρ)) st) r
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
-- THE INNER IS SUBSCRIBED WITH ITS EXIT FRAME PUSHED, AND THAT FRAME
-- IS WHERE ITS END IS REACTED TO.  A synchronous value of the inner
-- crosses `from-inner` inside the inner's own fold, and so does its
-- synchronous end -- the react, the finish and the drain all run
-- there, in order, before this subscribe returns.  So the answer
-- carries no completion bit: whatever the end caused has already been
-- written to the flattener's node by the time the instance is handed
-- back.
data subscribeInner⇓ {n} {Γ} {t} {e} where
  inner : ∀ {u lo op allNid} {κ : Path Γ lo u t} {now}
            {o : Val Γ (obs u)} {sched st inst out sched′ st′}
        → freshId nodeᵏ (Sched.mint sched) ≡ inst
        → subscribeE⇓ o (from-inner op allNid inst ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st
            (out , sched′ , st′)
        → subscribeInner⇓ op allNid κ now o sched st
            (inst , out , sched′ , st′)

-- EACH COLLAPSE CARRIES THE SIDE CONDITION THAT DISTINGUISHES IT, so
-- no fallback here stands free.  A prover that CHOOSES its own run is
-- not the machine, and for it a premise-free fallback is an arm
-- available at every input -- and every one of these has an empty
-- value column, which would discharge any statement quantified over
-- SOME derivation with a reducible column.
-- A CONSUME ANSWERS AT THE ROOT TYPE, BECAUSE WHAT A SUBSCRIBE EMITS
-- IS FOLDED WHERE IT IS PRODUCED.  An inner subscribed here can reach
-- the path below the flattener before this consume has returned: a
-- share connecting fans out through the chains already registered, and
-- a registered chain is the whole path.  An answer carried back as an
-- unresolved burst and folded once the walk is over therefore arrives
-- BEHIND deliveries that were made during it.  Concatenation puts the
-- two back in the right ORDER, so nothing below can tell -- unless
-- something below is COUNTING, which a `take`, a `scan` and a
-- `batchSync` each are.  So the consume's answer IS the inner
-- subscribe's answer, and there is no react and no second fold after
-- it: both happened inside, at the exit frame.
data thruConsume⇓ {n} {Γ} {t} {e} where

  -- THE LANE IS TAKEN BEFORE THE INNER IS SUBSCRIBED, AND THE INNER'S
  -- DEATH IS ONE EVENT WHICHEVER WAY IT ARRIVES.  Recording the start
  -- afterwards reads the two routes an inner can die by as one: a leaf
  -- reports its end through its exit frame, but a shared definition
  -- reports it through the registry, re-entrantly, while this very
  -- subscribe is still running -- so the freeing ran against a count
  -- that had not been raised yet, `pred 0` swallowed it, and the write
  -- afterwards took a lane for an inner that was already gone.  Raising
  -- it first is what gives the re-entrant end something to spend, and
  -- the frame-carried end then spends it through the SAME relation
  -- instead of a second rule that has to agree with it.  `drain-room`
  -- had already found this for the queue and not for the count.
  consume-all-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                      {o : Val Γ (obs u)} {sched₀ st₀} {lim act q od}
                      {inst out sched₁ st₁}
                  → lookupNode nid (EvalSt.nodes st₀)
                      ≡ just (mergeAll-st {t = u} lim act q od)
                  → hasRoom lim act ≡ true
                  → subscribeInner⇓ mergeAllᵒ nid κ now o sched₀
                      (record st₀
                        { nodes = setNode nid (mergeAll-st lim (suc act) q od)
                            (EvalSt.nodes st₀) })
                      (inst , out , sched₁ , st₁)
                  → thruConsume⇓ mergeAllᵒ nid κ now o sched₀ st₀
                      (out , sched₁ , st₁)

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
                         {sched₁ st₁} {inst out sched₂ st₂}
                     → lookupNode nid (EvalSt.nodes st₀) ≡ just (switch-st cur od)
                     → switchKill cur sched₀ st₀ ≡ (sched₁ , st₁)
                     → freshId nodeᵏ (Sched.mint sched₁) ≡ inst
                     → subscribeInner⇓ switchᵒ nid κ now o sched₁
                         (record st₁
                           { nodes = setNode nid (switch-st (just inst) od)
                               (EvalSt.nodes st₁) })
                         (inst , out , sched₂ , st₂)
                     → thruConsume⇓ switchᵒ nid κ now o sched₀ st₀
                         (out , sched₂ , st₂)

  consume-switch-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                       {o : Val Γ (obs u)} {sched₀ st₀}
                     → consumeUsable switchᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                     → thruConsume⇓ switchᵒ nid κ now o sched₀ st₀
                         ([] , sched₀ , st₀)

  consume-exhaust-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {now}
                          {o : Val Γ (obs u)} {sched₀ st₀} {od}
                          {inst out sched₁ st₁}
                      → lookupNode nid (EvalSt.nodes st₀)
                          ≡ just (exhaust-st false od)
                      → subscribeInner⇓ exhaustᵒ nid κ now o sched₀
                          (record st₀
                            { nodes = setNode nid (exhaust-st true od)
                                (EvalSt.nodes st₀) })
                          (inst , out , sched₁ , st₁)
                      → thruConsume⇓ exhaustᵒ nid κ now o sched₀ st₀
                          (out , sched₁ , st₁)

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
                {out₁ sched₁ st₁} {out₂ sched₂ st₂}
            → thruConsume⇓ op nid κ now o sched₀ st₀ (out₁ , sched₁ , st₁)
            → thruWalk⇓ op nid κ now os sched₁ st₁ (out₂ , sched₂ , st₂)
            → thruWalk⇓ op nid κ now (o ∷ os) sched₀ st₀
                (out₁ ++ out₂ , sched₂ , st₂)

data mergeAllDrain⇓ {n} {Γ} {t} {e} where

  -- A DRAINED SUBSCRIBE IS A SUBSCRIBE, SO ITS ANSWER IS FOLDED WHERE
  -- IT IS PRODUCED.  This is the second route a flattener subscribes by
  -- and the one no walk reaches: a lane frees, the queue is spent, and
  -- each spend can fan out through chains already registered below this
  -- flattener.  Carrying those answers back to the finishing inner's
  -- burst puts them BEHIND deliveries made during the drain, which only
  -- a frame that COUNTS can tell -- the same distinction `thruConsume⇓`
  -- is stated at, met through the queue instead of through the walk.
  -- THE COUNT IS THE DESCENT AND THE NODE IS THE TRUTH.  A drain
  -- re-reads the buffer it is spending, so nothing about what is left
  -- can be carried; what is carried is a LIST whose length bounds the
  -- iterations, because the node's queue is not an argument this
  -- recursion falls on.  It is the queue as the drain found it, which
  -- is exact while nothing enqueues mid-drain and an under-count when
  -- something does -- and an under-count leaves items parked for the
  -- next completion rather than spending one twice.
  drain-spent : ∀ {s lo allNid} {κ : Path Γ lo s t} {now}
                  {lim act od q sched₀ st₀}
              → mergeAllDrain⇓ {s = s} allNid κ now [] lim act od q sched₀ st₀
                  ([] , act , q , sched₀ , st₀)

  drain-nil : ∀ {s lo allNid} {κ : Path Γ lo s t} {now}
                {f fs lim act od sched₀ st₀}
            → mergeAllDrain⇓ {s = s} allNid κ now (f ∷ fs) lim act od []
                sched₀ st₀ ([] , act , [] , sched₀ , st₀)

  drain-no-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now} {f fs}
                    {lim act od} {o : Val Γ (obs s)} {q sched₀ st₀}
                → hasRoom lim act ≡ false
                → mergeAllDrain⇓ allNid κ now (f ∷ fs) lim act od (o ∷ q)
                    sched₀ st₀ ([] , act , o ∷ q , sched₀ , st₀)

  -- THE SHORTENED QUEUE AND THE RAISED COUNT ARE BOTH WRITTEN BEFORE
  -- THE SUBSCRIBE, NOT AFTER IT.  A batch write-back leaves the node
  -- holding the items already spent, so anything re-entering this node
  -- mid-drain reads a queue that is no longer true — and rxjs takes the
  -- item OUT of the buffer and raises `active` before it subscribes,
  -- so the batch form was the one that diverged.  The count is the same
  -- question and was missed: an inner whose end comes back through the
  -- registry frees its lane while this subscribe is still running, and
  -- against an unraised count that freeing lands on a SIBLING's lane.
  -- What stays carried rather than re-read is the count the recursion
  -- walks on, because re-reading the queue is what would let a
  -- re-entrant enqueue feed this drain its own tail forever.
  --
  -- AND THE SPENT INNER'S SYNCHRONOUS END HAS ALREADY BEEN SPENT BY THE
  -- TIME THE NODE IS RE-READ.  It crossed the inner's exit frame inside
  -- the inner's own subscribe, where the finish lowered the count and
  -- ran its own drain of what was queued; so the node read here holds
  -- the count as that finish left it, and no bit rides the answer to
  -- say whether to lower it again.
  drain-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {now} {f fs}
                 {lim act od} {o : Val Γ (obs s)} {q sched₀ st₀}
                 {inst out sched₁ st₁}
                 {lim₂ act₂ q₂ od₂} {out′ act′ q′ sched₂ st₂}
             → hasRoom lim act ≡ true
             → subscribeInner⇓ mergeAllᵒ allNid κ now o sched₀
                 (record st₀
                    { nodes = setNode allNid (mergeAll-st {t = s} lim (suc act) q od)
                        (EvalSt.nodes st₀) })
                 (inst , out , sched₁ , st₁)
             → drainSt s (lookupNode allNid (EvalSt.nodes st₁))
                 ≡ (lim₂ , act₂ , q₂ , od₂)
             → mergeAllDrain⇓ allNid κ now fs lim₂ act₂ od₂ q₂ sched₁ st₁
                 (out′ , act′ , q′ , sched₂ , st₂)
             → mergeAllDrain⇓ allNid κ now (f ∷ fs) lim act od (o ∷ q) sched₀ st₀
                 (out ++ out′ , act′ , q′ , sched₂ , st₂)

-- A FINISH ANSWERS THREE THINGS: THE STREAM IT SENT ROOTWARD ITSELF,
-- THE GROUP IT LEAVES FOR THE FRAME ABOVE TO FOLD, AND THE END THAT
-- GROUP CARRIES.  The merge's finish folds the group itself, because
-- its drain has to run AFTER the values and BEFORE the end, and hands
-- an empty group up with the end; the switch's and the exhaust's send
-- nothing rootward and leave the group to the fold, because nothing
-- of theirs has to come between the values and the end.
data innerFinish⇓ {n} {Γ} {t} {e} where

  -- THE DYING INNER'S LAST VALUE REACHES THE SINK BEFORE THE DRAIN
  -- RUNS, AND THAT IS AN ORDER BETWEEN EFFECTS RATHER THAN BETWEEN
  -- EMITS.  The stream this hands back is the same either way -- the
  -- value's fold, then the drain's, then the completion -- so the
  -- thing the old form got wrong was invisible in its own answer: it
  -- subscribed the queued inner while the value was still unfolded,
  -- and anything that value causes to SUBSCRIBE was therefore
  -- registered behind the queue's item instead of ahead of it.  On a
  -- shared source read in registration order that is a different
  -- observer list for every later value of the same burst, and a
  -- `switchAll` downstream then cuts a registration that had not yet
  -- spoken.  rxjs fixes the order at the inner subscriber: `next`
  -- runs the whole sink chain, and only the later `complete` drops
  -- the lane and shifts the buffer.
  --
  -- So the fold is INSIDE the rule and its result is the root stream
  -- this finish sent; the group left behind is empty and carries the
  -- walk's completion alone.
  finish-all-drain : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                       {vals : List (Val Γ s)} {sched st} {lim act q od}
                       {outV sched₁ st₁} {out act′ q′ sched₂ st₂}
                   → foldPath⇓ now κ vals false sched st (outV , sched₁ , st₁)
                   → mergeAllDrain⇓ allNid κ now q lim (pred act) od q sched₁ st₁
                       (out , act′ , q′ , sched₂ , st₂)
                   → innerFinish⇓ mergeAllᵒ allNid inst κ now vals sched st
                       (just (mergeAll-st {t = s} lim act q od))
                       ( outV ++ out , []
                       , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched₂
                       , record st₂
                           { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                               (EvalSt.nodes st₂) } )

  finish-switch-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                          {vals : List (Val Γ s)} {sched st} {c od}
                      → (c ≡ᵇ inst) ≡ true
                      → innerFinish⇓ switchᵒ allNid inst κ now vals sched st
                          (just (switch-st (just c) od))
                          ( [] , vals , od , sched
                          , record st
                              { nodes = setNode allNid (switch-st nothing od)
                                  (EvalSt.nodes st) } )

  finish-exhaust-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {now}
                           {vals : List (Val Γ s)} {sched st} {act od}
                       → innerFinish⇓ exhaustᵒ allNid inst κ now vals sched st
                           (just (exhaust-st act od))
                           ( [] , vals , od , sched
                           , record st
                               { nodes = setNode allNid (exhaust-st false od)
                                   (EvalSt.nodes st) } )

  finish-nil : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                 {vals : List (Val Γ s)} {sched st ns}
             → finishUsable op s inst ns ≡ false
             → innerFinish⇓ op allNid inst κ now vals sched st ns
                 ([] , vals , false , sched , st)

data innerReact⇓ {n} {Γ} {t} {e} where

  react-false : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                  {vals : List (Val Γ s)} {sched st}
              → innerReact⇓ op allNid inst κ now vals sched st false
                  ([] , vals , false , sched , st)

  react-alive : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {now}
                  {vals : List (Val Γ s)} {sched st}
              → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true
              → innerReact⇓ op allNid inst κ now vals sched st true
                  ([] , vals , false , sched , st)

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
--
-- A STEP ANSWERS A ROOT STREAM BESIDE THE GROUP IT PASSES ON.  A frame
-- that subscribes -- the flattener's outer, the inner's exit -- may
-- have sent values all the way to the root while stepping, and those
-- come FIRST in the fold's answer, before whatever the group it hands
-- on reaches when the rest of the path folds it.  A frame that
-- subscribes nothing sends nothing.
data stepFrame⇓ {n} {Γ} {t} {e} where

  step-map : ∀ {s u lo} {fn : FnClo Γ s u} {κ : Path Γ lo u t}
               {now} {vals : List (Val Γ s)} {fin sched st}
           → stepFrame⇓ now (map-f fn) κ vals fin sched st
               ([] , map (applyClo fn) vals , fin , sched , st)

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
                     (injectRoot {u = s ×ᵗ listᵗ s}
                       (batchDispatch nid vals fin sched st
                         (lookupNode nid (EvalSt.nodes st))))

  step-from-inner : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                      {now} {vals : List (Val Γ s)} {fin sched st r}
                  → innerReact⇓ op allNid inst κ now vals sched st fin r
                  → stepFrame⇓ now (from-inner op allNid inst) κ
                      vals fin sched st r

  -- THE OUTER'S WALK SENDS EVERYTHING ROOTWARD ITSELF, and what it
  -- hands on is the empty group with the wrapped end: the flattener's
  -- own completion, if the outer's end and the node's state make one.
  step-thru-outer : ∀ {u lo op nid} {κ : Path Γ lo u t}
                      {now} {vals : List (Val Γ (obs u))} {fin sched st}
                      {out sched′ st′}
                  → thruWalk⇓ op nid κ now vals sched st
                      (out , sched′ , st′)
                  → stepFrame⇓ now (thru-outer op nid) κ vals fin sched st
                      (out , [] , thruWrap op nid fin (sched′ , st′))

-- THIS IS WHERE A FLATTENER'S OUTER IS SUBSCRIBED, WITH THE
-- `thru-outer` FRAME ALREADY PUSHED -- so every observable the outer
-- produces is consumed inside the outer's own fold, each inner folded
-- rootward where it is subscribed, and the order between two inners
-- is the order the walk ran them in.  Nothing is handed up at the
-- element type and nothing is pushed afterwards: the corpus's
-- exchanged pair -- two programs carrying the same values out of the
-- flattener and out of the share, answered `[7,1,2]` and `[1,2,7]` --
-- is answered by WHEN each value was produced, which is the only thing
-- that separates the two.
data subscribeAll⇓ {n} {Γ} {t} {e} where

  sub-all : ∀ {u lo op} {ns : NodeState Γ} {b : Val Γ (obs (obs u))}
              {κ : Path Γ lo u t} {now sched st nid r}
          → freshId nodeᵏ (Sched.mint sched) ≡ nid
          → subscribeE⇓ b (thru-outer op nid ↠[ ≤-refl ] κ) now
              (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
              (installNode nid ns st) r
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

-- DEAD ROUTE: answering at `t` WITH THE CANDIDATE STILL RIDING THE
--   ANSWER -- folding the burst through the path inside the subscribe
--   while the candidate's observable arm keeps reading `StreamSat (Red
--   u)` off the result.  A result at `t` makes that conjunct
--   `StreamSat (Red t)`, which is not smaller, is impredicative, and
--   ranges over `obs u` itself; the descent is denominated in the
--   SOURCE type and a root-typed answer has no source type in it.  The
--   route is dead as stated and it is BYPASSED rather than reopened:
--   the arm no longer reads anything off the answer.  Its candidates
--   go DOWN, in the continuation the fold runs through, and the
--   recursive occurrence at the strictly smaller type is the
--   continuation's parameter (`Rx.Evaluator.Reducible`, at `RP`).

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

  -- ONE ARM, BECAUSE THE DEF IS SUBSCRIBED AT THE SINK AND THE SINK IS
  -- THE FAN-OUT.  Everything the definition produces synchronously --
  -- its values and, if it has one, its end -- crosses `share-sink i`
  -- inside the def's own fold, and the sink's dispatch is what marks
  -- the share dying, spends it, and drops its registry rows.  So the
  -- two arms a running machine used to tell apart by the answer's
  -- completion bit are one subscribe here, and the bookkeeping the
  -- died arm did by hand is the dispatch's, done once and in the
  -- order rxjs does it.  The caller's chain is registered before the
  -- def is subscribed, so the trigger receives its own values the way
  -- a joiner does, through the chain it registered.
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
             → foldPath⇓ now κ [] true sched st r
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
-- witness.  `shareFinish`, `shareAdmit` and `shareDying` compute, so
-- they stay applied.
data dispatchShare⇓ {n} {Γ} {t} {e} where
  disp : ∀ {lo now} {i : Fin n} {below : lo ≤ toℕ i}
           {vals fin sched st r}
       → shareWalk⇓ now i vals fin sched (shareDying i fin st) r
       → dispatchShare⇓ {lo = lo} now i below vals fin sched st
           (shareFinish i fin r)

-- EVERY VALUE IS DELIVERED WITH `fin` FALSE AND THE END IS THE WALK'S
-- BASE CASE, so `fin` reaches exactly one delivery without any clause
-- having to tell the last value apart by its tail.  It also means an
-- emission that carries an end and no values is not the degenerate
-- case: it is this recursion at depth zero.
data shareWalk⇓ {n} {Γ} {t} {e} where
  walk-nil : ∀ {now} {i : Fin n} {sched st}
           → shareWalk⇓ now i [] false sched st ([] , sched , st)

  -- THE END IS A DELIVERY OF ITS OWN, AND IT READS THE REGISTRY AS IT
  -- THEN STANDS.  Riding it on the last value meant the end reached
  -- exactly the chains that value reached -- a snapshot taken before
  -- that value was pushed -- so a chain REGISTERED BY THAT PUSH was
  -- never told the share ended, and `shareFinish` then dropped it.
  -- Nothing reaches such a joiner afterwards: its flattener's lane is
  -- freed by the completion and by nothing else, so it holds one
  -- forever.  Separating them is also the order rxjs emits in, whose
  -- subject pushes `next` to the observers it had and `complete` to
  -- the ones it has; the two coincide only when nothing subscribed
  -- mid-burst, which is the case that used to be tested.
  --
  -- The share is CLOSED before this delivery rather than after it, and
  -- the argument for that half of the order is at `shareSpend`.
  walk-end : ∀ {now} {i : Fin n} {sched st r}
           → shareGo⇓ now i [] true
               (shareAdmit i (EvalSt.registry st)) sched (shareSpend i st) r
           → shareWalk⇓ now i [] true sched st r

  walk-more : ∀ {now} {i : Fin n} {v vs fin sched₀ st₀}
                {emits sched₁ st₁ rest sched₂ st₂}
            → shareGo⇓ now i (v ∷ []) false
                (shareAdmit i (EvalSt.registry st₀)) sched₀ st₀
                (emits , sched₁ , st₁)
            → shareWalk⇓ now i vs fin sched₁ st₁ (rest , sched₂ , st₂)
            → shareWalk⇓ now i (v ∷ vs) fin sched₀ st₀
                (emits ++ rest , sched₂ , st₂)

-- THE CANCELLATION TEST STAYS A PREMISE RATHER THAN A SIDE CONDITION.
-- It is decidable and it decides which of two clauses ran, so the
-- relation carries the answer as an equation and the two arms cannot
-- both apply.  `go-live` is where the threading shows: what the tail is
-- handed is the head's own results.
data shareGo⇓ {n} {Γ} {t} {e} where
  go-nil : ∀ {lo now} {i : Fin n} {vals fin sched st}
         → shareGo⇓ {lo = lo} now i vals fin [] sched st ([] , sched , st)

  go-cut : ∀ {lo now} {i : Fin n} {vals fin rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st r}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
         → shareGo⇓ now i vals fin ps sched st r
         → shareGo⇓ now i vals fin ((rid , p) ∷ ps) sched st r

  go-live : ∀ {lo now} {i : Fin n} {vals fin rid}
              {p : Path Γ lo (lookup Γ i) t} {ps sched₀ st₀}
              {emits sched₁ st₁ rest sched₂ st₂}
          → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
          → foldPath⇓ now p vals fin sched₀
              (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
              (emits , sched₁ , st₁)
          → shareGo⇓ now i vals fin ps sched₁ st₁ (rest , sched₂ , st₂)
          → shareGo⇓ now i vals fin ((rid , p) ∷ ps) sched₀ st₀
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

  -- THE STEP'S OWN ROOT STREAM COMES FIRST, THEN WHAT THE GROUP IT
  -- HANDS ON REACHES.  A step that subscribed sent values rootward
  -- while it ran, before the group it passes on existed; the fold
  -- lays them down in that order and nothing below can reorder them.
  fold-step : ∀ {lo ℓ s u now} {f : Frame Γ s u} {le : lo ≤ ℓ}
                {path′ : Path Γ ℓ u t} {vals fin sched st}
                {out₁ vals′ fin′ sched₁ st₁} {out₂ sched₂ st₂}
            → stepFrame⇓ now f path′ vals fin sched st
                (out₁ , vals′ , fin′ , sched₁ , st₁)
            → foldPath⇓ now path′ vals′ fin′ sched₁ st₁ (out₂ , sched₂ , st₂)
            → foldPath⇓ {lo = lo} now (f ↠[ le ] path′) vals fin sched st
                (out₁ ++ out₂ , sched₂ , st₂)

data chainStep⇓ {n} {Γ} {t} {e} where
  chain-step : ∀ {a : Arrival Γ} {vs fin lo} {path : Path Γ lo (arrTy a) t}
                 {sched st r}
             → foldPath⇓ (arrTick a) path vs fin sched st r
             → chainStep⇓ a vs fin (lo , path) sched st r

data cascadeGo⇓ {n} {Γ} {t} {e} where
  casc-nil : ∀ {a vs fin sched₀ st₀}
           → cascadeGo⇓ a vs fin [] sched₀ st₀ ([] , sched₀ , st₀)
  casc-cut : ∀ {a vs fin rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀ r}
           → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ true
           → cascadeGo⇓ a vs fin chains sched₀ st₀ r
           → cascadeGo⇓ a vs fin ((rid , c) ∷ chains) sched₀ st₀ r
  casc-live : ∀ {a vs fin rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀}
                {emits sched₁ st₁ rest sched₂ st₂}
            → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
            → chainStep⇓ a vs fin c sched₀
                (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
                (emits , sched₁ , st₁)
            → cascadeGo⇓ a vs fin chains sched₁ st₁ (rest , sched₂ , st₂)
            → cascadeGo⇓ a vs fin ((rid , c) ∷ chains) sched₀ st₀
                (emits ++ rest , sched₂ , st₂)

-- A VALUE AND THE END THAT RIDES WITH IT ARE TWO PASSES OVER THE SAME
-- CHAINS, NOT ONE PASS CARRYING BOTH.  A subject's `next` walks its
-- observers and its `complete` walks them again, so a chain that
-- SUBSCRIBES on the end -- a flattener's queue draining as a lane
-- frees, a share's fan-out at a connect -- cannot run until every
-- observer has had the value.  Folding the pair into each chain in turn
-- lets the first chain's completion, and everything it subscribes, get
-- ahead of the second chain's value; the multiset is the same either
-- way, so only a frame downstream of the second chain can tell, which
-- is what makes this a different question from the order WITHIN one
-- chain.  Each pass takes its OWN snapshot, because a chain that
-- subscribed during the value pass is an observer of an open subject
-- and is owed the completion.
data cascade⇓ {n} {Γ} {t} {e} where
  casc-run : ∀ {a sched st} {emits sched′ st′}
           → Arrival.isLast a ≡ false
           → cascadeGo⇓ a (arrVal a ∷ []) false (chainsOf a st) sched
               (cascadeOpen st) (emits , sched′ , st′)
           → cascade⇓ a sched st (emits , cascadeFinish a sched′ st′)

  casc-run-last : ∀ {a sched st} {emits sched₁ st₁} {ends sched₂ st₂}
                → Arrival.isLast a ≡ true
                → cascadeGo⇓ a (arrVal a ∷ []) false (chainsOf a st) sched
                    (cascadeOpen st) (emits , sched₁ , st₁)
                → cascadeGo⇓ a [] true (chainsOf a st₁) sched₁
                    (cascadeClose a st₁) (ends , sched₂ , st₂)
                → cascade⇓ a sched st
                    (emits ++ ends , cascadeFinish a sched₂ st₂)

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
               {out sched₀ st₀ rest}
           → subscribeE⇓ {e = e} {lo = n} ([] , e , []ᵉ) root 0
               (sched-init e ins) (st-init e) (out , sched₀ , st₀)
           → drain⇓ {e = e} fuel sched₀ st₀ rest
           → evaluate⇓ fuel e ins (out ++ rest)
