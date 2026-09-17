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

open import Rx.Prim using (Tick; Fuel; Id; Source; InstEvent; InstEmit; value; close;
  handoff; complete; exhausted; delivery; _at_from_as_;
  init; subscribe; hot; cold)
open import Rx.Exp using (obs; Ctx; Val; Closed; Tm; Fn; _×ᵗ_; listᵗ; evalTm; unfoldμ; input; ofᵉ; emptyᵉ; takeᵉ;
  liftᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; deferᵉ)
open import Rx.Mint using (ordinalᵏ; sourceᵏ; nodeᵏ; regᵏ; freshId; setAt)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; NodeId;
  root; share-sink; _↠_; shareAdmit; shareLatch; shareFinish;
  from-inner; splitBurst;
  arrTick; arrSource; arrVal; chainsOf; cascadeLatch; cascadeFinish;
  sched-next; sched-init; st-init;
  NodeState; AllOp; RegId; Arrival; AtFloor; arrTy;
  spentBurst; oneShotBurst; memberSource; register; installNode; resolve;
  atSlot; atDyn; lowerFloor;
  lift-f; take-f; thru-outer;
  cell-st; take-st; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ;
  lookupNode; setNode; hasRoom; mergeAllBump; switchKill; aliveThroughᶠ;
  splitEvents; retagEvents; liftDispatch; takeDispatch; thruWrap;
  consumeUsable; finishUsable;
  burstCompleted; sharedPlumb; dropSource)

-- THE FRAME A SUBSCRIBE CAN PUSH, WHICH IS EVERY FRAME BUT ONE, AND
-- SAYING SO IN A TYPE IS WHAT TAKES THE DRAIN OUT OF A PUSH CYCLE.  A
-- push cycle steps the frame it was handed, and what hands it one is a
-- source former -- the map, the take, the scan, the outer of an
-- operator.  The inner's own frame is never pushed: a subscribe returns
-- the inner's synchronous burst UP to its caller as values, and the
-- frame is walked later, by the instant loop, down a path the registry
-- holds.  So the completion side -- react, finish, drain, and the
-- queued subscribe they end in -- is not reachable from a subscribe at
-- all, and the cycle that a measure was owed for does not exist.  What
-- did exist was a DEFINITION order: a block answering for a frame it
-- can never be given pays for that answer, and this is what stops it.
-- The fact is stated here rather than beside either consumer because
-- BOTH faces of the subscribe cycle need it and neither imports the
-- other.
srcFrame : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Set
srcFrame (from-inner _ _ _) = ⊥
srcFrame _                  = ⊤

------------------------------------------------------------------
-- THE SUBSCRIBE CYCLE.  Twelve families, exactly the members of the
-- evaluator's larger genuine cycle: everything else it calls is
-- structurally recursive and is APPLIED here rather than related.
------------------------------------------------------------------

data subscribeE⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Closed Γ u → Path Γ lo u t → Id → Tick → Sched Γ → EvalSt e
   → Stream Γ u × Sched Γ × EvalSt e → Set

data subscribeInner⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Id → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool
     × Sched Γ × EvalSt e → Set

data thruConsume⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Id → Tick
   → Val Γ (obs u) → Sched Γ → EvalSt e
   → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e → Set

data thruWalk⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeId → Path Γ lo u t → Id → Tick
   → List (Val Γ (obs u)) → Sched Γ → EvalSt e
   → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e → Set

data mergeAllDrain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     NodeId → Path Γ lo s t → Id → Tick
   → Maybe ℕ → ℕ → Bool → List (Closed Γ s) → Sched Γ → EvalSt e
   → List (Val Γ s) × List (InstEvent (Val Γ t)) × ℕ
     × List (Closed Γ s) × Sched Γ × EvalSt e → Set

data innerFinish⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
   → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool
     × Sched Γ × EvalSt e → Set

data innerReact⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s lo} →
     AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
   → List (Val Γ s) → Sched Γ → EvalSt e → Bool
   → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool
     × Sched Γ × EvalSt e → Set

data stepFrame⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Id → Tick → Frame Γ s u → Path Γ lo u t
   → List (Val Γ s) → Bool → Sched Γ → EvalSt e
   → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool
     × Sched Γ × EvalSt e → Set

data pushBurst⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {s u lo} →
     Id → Tick → Frame Γ s u → Path Γ lo u t
   → Stream Γ s → Sched Γ → EvalSt e
   → Stream Γ u × Sched Γ × EvalSt e → Set

data subscribeAll⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ lo u t
   → Id → Tick → Sched Γ → EvalSt e
   → Stream Γ u × Sched Γ × EvalSt e → Set

data sharedConnect⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Id → Tick → Sched Γ → EvalSt e
   → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e → Set

data subscribeSharedSlot⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     (i : Fin n) → Closed Γ (lookup Γ i) → Path Γ lo (lookup Γ i) t
   → toℕ i < lo → Id → Tick → Sched Γ → EvalSt e
   → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE SHARE CYCLE.  The evaluator's second genuine cycle, entered
-- once per delivered chain; its members carry the subscribe cycle's
-- derivation too, because a fold re-enters a frame.
------------------------------------------------------------------

data dispatchShare⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Id → Tick → (i : Fin n) → lo ≤ toℕ i
   → List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data shareGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {lo} →
     Id → Tick → (i : Fin n)
   → List (Val Γ (lookup Γ i)) → Bool
   → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data foldPath⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     ∀ {u lo} →
     Id → Tick → Source → Path Γ lo u t
   → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
   → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

------------------------------------------------------------------
-- THE ARRIVAL SPINE.  Structurally recursive in the evaluator, and
-- related here only because each of these reaches a cycle above and so
-- cannot be applied without a derivation to hand it.
------------------------------------------------------------------

data chainStep⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Id → (a : Arrival Γ) → AtFloor Γ (arrTy a) t → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data cascadeGo⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     (a : Arrival Γ) → Id
   → List (RegId × AtFloor Γ (arrTy a) t) → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data cascade⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Arrival Γ → Id → Sched Γ → EvalSt e
   → Stream Γ t × Sched Γ × EvalSt e → Set

data drain⇓ {n} {Γ : Ctx n} {t} {e : Closed Γ t} :
     Fuel → Id → Sched Γ → EvalSt e → Stream Γ t → Set

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
-- unwritten one is an unsolved meta and a build failure.  Binding it
-- costs a name and asserts nothing, which is the right trade: the
-- relation is about which arm ran, never about why the slot is legal.
data subscribeE⇓ {n} {Γ} {t} {e} where

  subs-floor : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                 {id now sched st}
             → lo ≤ toℕ i
             → subscribeE⇓ (input i) κ id now sched st
                 (spentBurst (toℕ i) id , sched , st)

  subs-shared : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                  {below : toℕ i < lo} {ok} {id now sched st r}
              → Sched.slots sched i ≡ shared d {ok = ok}
              → subscribeSharedSlot⇓ i d κ below id now sched st r
              → subscribeE⇓ (input i) κ id now sched st r

  subs-hot-done : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {id now sched st}
                → toℕ i < lo
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
                → subscribeE⇓ (input i) κ id now sched st
                    (spentBurst (toℕ i) id , sched , st)

  subs-hot-live : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                    {ok async} {id now sched st rid}
                → (below : toℕ i < lo)
                → Sched.slots sched i ≡ scripted {ok = ok} (hot async)
                → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
                → freshId regᵏ (Sched.mint sched) ≡ rid
                → subscribeE⇓ (input i) κ id now sched st
                    ( ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
                    , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                    , register rid (atSlot i) (lowerFloor below κ) st )

  subs-cold-sync : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                     {ok sync} {id now sched st burst sched₁}
                 → toℕ i < lo
                 → Sched.slots sched i ≡ scripted {ok = ok} (cold sync [])
                 → oneShotBurst sync id sched ≡ (burst , sched₁)
                 → subscribeE⇓ (input i) κ id now sched st
                     (burst , sched₁ , st)

  subs-cold-async : ∀ {lo} {i : Fin n} {κ : Path Γ lo (lookup Γ i) t}
                      {ok sync d ds} {id now sched st src ord rid}
                  → toℕ i < lo
                  → Sched.slots sched i ≡ scripted {ok = ok} (cold sync (d ∷ ds))
                  → freshId sourceᵏ (Sched.mint sched) ≡ src
                  → freshId ordinalᵏ (Sched.mint sched) ≡ ord
                  → freshId regᵏ (Sched.mint sched) ≡ rid
                  → subscribeE⇓ (input i) κ id now sched st
                      ( ((init src ∷ map value sync)
                           at id from src as subscribe) ∷ []
                      , record sched
                          { mint = setAt regᵏ (suc rid)
                                     (setAt sourceᵏ (suc src)
                                       (setAt ordinalᵏ (suc ord) (Sched.mint sched)))
                          ; live = record { source = src ; ordinal = ord
                                          ; elemTy = lookup Γ i
                                          ; pending = resolve now (d ∷ ds) }
                                   ∷ Sched.live sched }
                      , register rid (atDyn src lo) κ st )

  subs-of : ∀ {lo u} {ts} {κ : Path Γ lo u t} {id now sched st burst sched₁}
          → oneShotBurst (map (λ tm → evalTm tm) ts) id sched ≡ (burst , sched₁)
          → subscribeE⇓ (ofᵉ ts) κ id now sched st (burst , sched₁ , st)

  subs-empty : ∀ {lo u} {κ : Path Γ lo u t} {id now sched st burst sched₁}
             → oneShotBurst [] id sched ≡ (burst , sched₁)
             → subscribeE⇓ emptyᵉ κ id now sched st (burst , sched₁ , st)


  subs-take-zero : ∀ {lo u} {count} {b : Closed Γ u} {κ : Path Γ lo u t}
                     {id now sched st burst sched₁}
                 → evalTm count ≡ zero
                 → oneShotBurst [] id sched ≡ (burst , sched₁)
                 → subscribeE⇓ (takeᵉ count b) κ id now sched st
                     (burst , sched₁ , st)

  subs-take-suc : ∀ {lo u} {count k} {b : Closed Γ u} {κ : Path Γ lo u t}
                    {id now sched st nid burst sched₂ st₁ r}
                → evalTm count ≡ suc k
                → freshId nodeᵏ (Sched.mint sched) ≡ nid
                → subscribeE⇓ b (take-f nid ↠ κ) id now
                    (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                    (installNode nid (take-st (suc k)) st)
                    (burst , sched₂ , st₁)
                → pushBurst⇓ id now (take-f nid) κ burst sched₂ st₁ r
                → subscribeE⇓ (takeᵉ count b) κ id now sched st r


  subs-lift : ∀ {lo s u w} {f} {i : Tm Γ [] [] [] w} {b : Closed Γ s}
                {κ : Path Γ lo u t}
                {id now sched st nid burst sched₂ st₁ r}
            → freshId nodeᵏ (Sched.mint sched) ≡ nid
            → subscribeE⇓ b (lift-f f nid ↠ κ) id now
                (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
                (installNode nid (cell-st (evalTm i)) st)
                (burst , sched₂ , st₁)
            → pushBurst⇓ id now (lift-f f nid) κ burst sched₂ st₁ r
            → subscribeE⇓ (liftᵉ f i b) κ id now sched st r

  subs-merge-all : ∀ {lo u} {lim} {b : Closed Γ (obs u)} {κ : Path Γ lo u t}
                     {id now sched st r}
                 → subscribeAll⇓ mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false)
                     b κ id now sched st r
                 → subscribeE⇓ (mergeAllᵉ lim b) κ id now sched st r

  subs-switch-all : ∀ {lo u} {b : Closed Γ (obs u)} {κ : Path Γ lo u t}
                      {id now sched st r}
                  → subscribeAll⇓ switchᵒ (switch-st nothing false)
                      b κ id now sched st r
                  → subscribeE⇓ (switchAllᵉ b) κ id now sched st r

  subs-exhaust-all : ∀ {lo u} {b : Closed Γ (obs u)} {κ : Path Γ lo u t}
                       {id now sched st r}
                   → subscribeAll⇓ exhaustᵒ (exhaust-st false false)
                       b κ id now sched st r
                   → subscribeE⇓ (exhaustAllᵉ b) κ id now sched st r

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
  subs-μ : ∀ {lo u} {body} {κ : Path Γ lo u t} {id now sched st r}
         → subscribeE⇓ (unfoldμ body) κ id now sched st r
         → subscribeE⇓ (μᵉ body) κ id now sched st r

  subs-defer : ∀ {lo u} {body} {κ : Path Γ lo u t}
                 {id now sched st nid src ord rid}
             → freshId nodeᵏ (Sched.mint sched) ≡ nid
             → freshId sourceᵏ (Sched.mint sched) ≡ src
             → freshId ordinalᵏ (Sched.mint sched) ≡ ord
             → freshId regᵏ (Sched.mint sched) ≡ rid
             → subscribeE⇓ (deferᵉ body) κ id now sched st
                 ( ((init src ∷ []) at id from src as subscribe) ∷ []
                 , record sched
                     { mint = setAt regᵏ (suc rid)
                                (setAt nodeᵏ (suc nid)
                                  (setAt sourceᵏ (suc src)
                                    (setAt ordinalᵏ (suc ord) (Sched.mint sched))))
                     ; live = record { source = src ; ordinal = ord
                                     ; elemTy = obs u
                                     ; pending = (suc now , body) ∷ [] }
                              ∷ Sched.live sched }
                 , register rid (atDyn src lo)
                            (thru-outer mergeAllᵒ nid ↠ κ)
                            (installNode nid
                              (mergeAll-st {t = u} nothing 0 [] false) st) )

-- ONE CONSTRUCTOR WHERE THE EVALUATOR HAS TWO, AND THE MISSING ONE IS
-- THE POINT.  The machine asks whether what arrived is written
-- shallower than the component it stands at, and answers the negative
-- case by minting an instance and closing it dry.  Here the hop's
-- premise IS a sub-derivation at the arriving value, so there is
-- nothing to ask and no arm to answer: a relation with no dry
-- constructor cannot relate a run to a dry stream.
data subscribeInner⇓ {n} {Γ} {t} {e} where
  inner : ∀ {u lo op allNid} {κ : Path Γ lo u t} {id now}
            {o : Val Γ (obs u)} {sched st inst burst sched′ st′ vs bs done}
        → freshId nodeᵏ (Sched.mint sched) ≡ inst
        → subscribeE⇓ o (from-inner op allNid inst ↠ κ) id now
            (record sched { mint = setAt nodeᵏ (suc inst) (Sched.mint sched) }) st
            (burst , sched′ , st′)
        → splitBurst burst ≡ (vs , bs , done)
        → subscribeInner⇓ op allNid κ id now o sched st
            (inst , vs , bs , done , sched′ , st′)

-- FOUR TYPE-MISMATCH ARMS COLLAPSE INTO THE CATCH-ALL BESIDE THEM, AND
-- THAT IS A MERGE RATHER THAN A DROP.  Each returns exactly what the
-- wildcard directly below it returns, so relating them separately would
-- need a disequality premise to tell two constructors apart that agree
-- on their result.  The catch-alls carry no premise for the same
-- reason, and it costs nothing: a premise-free constructor whose RESULT
-- INDEX is fixed admits no run it did not already admit, and the only
-- direction spent here builds a derivation at the machine's own result.
--
-- AND THAT LAST CLAUSE WAS A PREMISE RATHER THAN A PROPERTY, WHICH IS
-- WHY NO FALLBACK HERE STANDS FREE ANY MORE.  A prover that CHOOSES
-- its own run is not the machine, so for it a premise-free fallback is
-- an arm available at every input -- and every one of these has an
-- empty or passed-through value column, which discharges any statement
-- quantified over SOME derivation with a reducible column.  The cost
-- fell entirely on the other direction, and which direction a consumer
-- is in is not visible from here.  So each collapse now carries the
-- side condition that distinguishes it: a fold and a truncation name
-- the machine's own dispatch from a SINGLE constructor, and the
-- flattener's consume and finish arms carry a `usable` reading of the
-- store that is false exactly where the machine collapses.  The
-- builder pays for this in clauses -- a condition on two variables
-- does not reduce, so its catch-alls are spelt out -- and the
-- reducibility direction gets a relation with nothing to prefer.
data thruConsume⇓ {n} {Γ} {t} {e} where

  consume-all-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                      {o : Val Γ (obs u)} {sched₀ st₀} {lim act q od}
                      {inst vs bs done sched₁ st₁}
                  → lookupNode nid (EvalSt.nodes st₀)
                      ≡ just (mergeAll-st {t = u} lim act q od)
                  → hasRoom lim act ≡ true
                  → subscribeInner⇓ mergeAllᵒ nid κ id now o sched₀ st₀
                      (inst , vs , bs , done , sched₁ , st₁)
                  → thruConsume⇓ mergeAllᵒ nid κ id now o sched₀ st₀
                      ( vs , bs , sched₁
                      , record st₁
                          { nodes = mergeAllBump nid done (EvalSt.nodes st₁) } )

  consume-all-enqueue : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                          {o : Val Γ (obs u)} {sched₀ st₀} {lim act q od}
                      → lookupNode nid (EvalSt.nodes st₀)
                          ≡ just (mergeAll-st {t = u} lim act q od)
                      → hasRoom lim act ≡ false
                      → thruConsume⇓ mergeAllᵒ nid κ id now o sched₀ st₀
                          ( [] , [] , sched₀
                          , record st₀
                              { nodes = setNode nid
                                  (mergeAll-st lim act (q ++ o ∷ []) od)
                                  (EvalSt.nodes st₀) } )

  consume-all-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                    {o : Val Γ (obs u)} {sched₀ st₀}
                  → consumeUsable mergeAllᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                  → thruConsume⇓ mergeAllᵒ nid κ id now o sched₀ st₀
                      ([] , [] , sched₀ , st₀)

  consume-switch-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                         {o : Val Γ (obs u)} {sched₀ st₀} {cur od}
                         {closes sched₁ st₁} {inst vs bs done sched₂ st₂}
                     → lookupNode nid (EvalSt.nodes st₀) ≡ just (switch-st cur od)
                     → switchKill cur sched₀ st₀ ≡ (closes , sched₁ , st₁)
                     → subscribeInner⇓ switchᵒ nid κ id now o sched₁ st₁
                         (inst , vs , bs , done , sched₂ , st₂)
                     → thruConsume⇓ switchᵒ nid κ id now o sched₀ st₀
                         ( vs , closes ++ bs , sched₂
                         , record st₂
                             { nodes = setNode nid
                                 (switch-st (if done then nothing else just inst) od)
                                 (EvalSt.nodes st₂) } )

  consume-switch-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                       {o : Val Γ (obs u)} {sched₀ st₀}
                     → consumeUsable switchᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                     → thruConsume⇓ switchᵒ nid κ id now o sched₀ st₀
                         ([] , [] , sched₀ , st₀)

  consume-exhaust-sub : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                          {o : Val Γ (obs u)} {sched₀ st₀} {od}
                          {inst vs bs done sched₁ st₁}
                      → lookupNode nid (EvalSt.nodes st₀)
                          ≡ just (exhaust-st false od)
                      → subscribeInner⇓ exhaustᵒ nid κ id now o sched₀ st₀
                          (inst , vs , bs , done , sched₁ , st₁)
                      → thruConsume⇓ exhaustᵒ nid κ id now o sched₀ st₀
                          ( vs , bs , sched₁
                          , record st₁
                              { nodes = setNode nid (exhaust-st (not done) od)
                                  (EvalSt.nodes st₁) } )

  consume-exhaust-nil : ∀ {u lo nid} {κ : Path Γ lo u t} {id now}
                        {o : Val Γ (obs u)} {sched₀ st₀}
                      → consumeUsable exhaustᵒ u (lookupNode nid (EvalSt.nodes st₀)) ≡ false
                      → thruConsume⇓ exhaustᵒ nid κ id now o sched₀ st₀
                          ([] , [] , sched₀ , st₀)

data thruWalk⇓ {n} {Γ} {t} {e} where

  walk-nil : ∀ {u lo op nid} {κ : Path Γ lo u t} {id now} {sched₀ st₀}
           → thruWalk⇓ op nid κ id now [] sched₀ st₀ ([] , [] , sched₀ , st₀)

  walk-cons : ∀ {u lo op nid} {κ : Path Γ lo u t} {id now}
                {o : Val Γ (obs u)} {os sched₀ st₀}
                {vs bs sched₁ st₁} {vs′ bs′ sched₂ st₂}
            → thruConsume⇓ op nid κ id now o sched₀ st₀ (vs , bs , sched₁ , st₁)
            → thruWalk⇓ op nid κ id now os sched₁ st₁ (vs′ , bs′ , sched₂ , st₂)
            → thruWalk⇓ op nid κ id now (o ∷ os) sched₀ st₀
                (vs ++ vs′ , bs ++ bs′ , sched₂ , st₂)

data mergeAllDrain⇓ {n} {Γ} {t} {e} where

  drain-nil : ∀ {s lo allNid} {κ : Path Γ lo s t} {id now} {lim act od sched₀ st₀}
            → mergeAllDrain⇓ allNid κ id now lim act od [] sched₀ st₀
                ([] , [] , act , [] , sched₀ , st₀)

  drain-no-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {id now}
                    {lim act od} {o : Closed Γ s} {q sched₀ st₀}
                → hasRoom lim act ≡ false
                → mergeAllDrain⇓ allNid κ id now lim act od (o ∷ q) sched₀ st₀
                    ([] , [] , act , o ∷ q , sched₀ , st₀)

  -- THE SHORTENED QUEUE IS WRITTEN BEFORE THE SUBSCRIBE, NOT AFTER THE
  -- WHOLE DRAIN.  A batch write-back leaves the node holding the items
  -- already spent, so anything re-entering this node mid-drain reads a
  -- queue that is no longer true — and rxjs takes the item OUT of the
  -- buffer before it subscribes it, so the batch form was the one that
  -- diverged.  It is also what lets the store be read as a census: a
  -- reading over a stale queue cannot fall as the drain proceeds, so no
  -- measure denominated in it can order this edge.
  drain-room : ∀ {s lo allNid} {κ : Path Γ lo s t} {id now}
                 {lim act od} {o : Closed Γ s} {q sched₀ st₀}
                 {inst vs bs done sched₁ st₁} {vs′ bs′ act′ q′ sched₂ st₂}
             → hasRoom lim act ≡ true
             → subscribeInner⇓ mergeAllᵒ allNid κ id now o sched₀
                 (record st₀
                    { nodes = setNode allNid (mergeAll-st {t = s} lim act q od)
                        (EvalSt.nodes st₀) })
                 (inst , vs , bs , done , sched₁ , st₁)
             → mergeAllDrain⇓ allNid κ id now lim
                 (if done then act else suc act) od q sched₁ st₁
                 (vs′ , bs′ , act′ , q′ , sched₂ , st₂)
             → mergeAllDrain⇓ allNid κ id now lim act od (o ∷ q) sched₀ st₀
                 (vs ++ vs′ , bs ++ bs′ , act′ , q′ , sched₂ , st₂)

data innerFinish⇓ {n} {Γ} {t} {e} where

  finish-all-drain : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {id now}
                       {vals : List (Val Γ s)} {sched st} {lim act q od}
                       {vs bs act′ q′ sched′ st′}
                   → mergeAllDrain⇓ allNid κ id now lim (pred act) od q sched st
                       (vs , bs , act′ , q′ , sched′ , st′)
                   → innerFinish⇓ mergeAllᵒ allNid inst κ id now vals sched st
                       (just (mergeAll-st {t = s} lim act q od))
                       ( vals ++ vs , bs , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched′
                       , record st′
                           { nodes = setNode allNid (mergeAll-st lim act′ q′ od)
                               (EvalSt.nodes st′) } )

  finish-switch-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {id now}
                          {vals : List (Val Γ s)} {sched st} {c od}
                      → (c ≡ᵇ inst) ≡ true
                      → innerFinish⇓ switchᵒ allNid inst κ id now vals sched st
                          (just (switch-st (just c) od))
                          ( vals , [] , od , sched
                          , record st
                              { nodes = setNode allNid (switch-st nothing od)
                                  (EvalSt.nodes st) } )

  finish-exhaust-clear : ∀ {s lo allNid inst} {κ : Path Γ lo s t} {id now}
                           {vals : List (Val Γ s)} {sched st} {act od}
                       → innerFinish⇓ exhaustᵒ allNid inst κ id now vals sched st
                           (just (exhaust-st act od))
                           ( vals , [] , od , sched
                           , record st
                               { nodes = setNode allNid (exhaust-st false od)
                                   (EvalSt.nodes st) } )

  finish-nil : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {id now}
                 {vals : List (Val Γ s)} {sched st ns}
             → finishUsable op s inst ns ≡ false
             → innerFinish⇓ op allNid inst κ id now vals sched st ns
                 (vals , [] , false , sched , st)

data innerReact⇓ {n} {Γ} {t} {e} where

  react-false : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {id now}
                  {vals : List (Val Γ s)} {sched st}
              → innerReact⇓ op allNid inst κ id now vals sched st false
                  (vals , [] , false , sched , st)

  react-alive : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {id now}
                  {vals : List (Val Γ s)} {sched st}
              → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ true
              → innerReact⇓ op allNid inst κ id now vals sched st true
                  (vals , [] , false , sched , st)

  react-dead : ∀ {s lo op allNid inst} {κ : Path Γ lo s t} {id now}
                 {vals : List (Val Γ s)} {sched st r}
             → any (aliveThroughᶠ inst st) (EvalSt.registry st) ≡ false
             → innerFinish⇓ op allNid inst κ id now vals sched st
                 (lookupNode allNid (EvalSt.nodes st)) r
             → innerReact⇓ op allNid inst κ id now vals sched st true r

-- A HELPER OUTSIDE THE CYCLE IS NAMED IN THE RESULT INDEX RATHER THAN
-- UNFOLDED INTO ARMS, AND THAT IS A CHOICE ABOUT WHAT THIS RELATION IS
-- FOR.  The take dispatch and the outer wrap each branch on a node
-- lookup, but neither re-enters the subscribe cycle, so relating their
-- arms separately would add cases the induction never splits on.  What
-- the relation must expose is exactly the recursive structure; a total
-- function of the state is carried as itself.  The one place this would
-- cost something is the dry proof, and it does not arise here: this
-- family hands back EVENTS rather than emits, and the dry marker is an
-- emit's, so no arm of it can carry one however the helper computes.
--
-- RECOVERY: git show 234074e:agda/src/Verify-Rank-Sufficient/ restores
--   the CARRIED tower, whose whole subject was this family: a bound a
--   frame's emissions were held to, stated per template and pushed
--   through a burst.  It is the apparatus to read if a strengthened
--   return type is ever wanted here — what killed it is that the
--   figure was seeded off SYNTAX, which is a property of that tower's
--   currency and not of the per-frame statement it proved.
data stepFrame⇓ {n} {Γ} {t} {e} where



  step-lift : ∀ {s u w lo} {fn : Fn Γ [] [] [] (w ×ᵗ listᵗ s) (w ×ᵗ listᵗ u)}
                {nid} {κ : Path Γ lo u t}
                {id now} {vals : List (Val Γ s)} {fin sched st}
            → stepFrame⇓ id now (lift-f fn nid) κ vals fin sched st
                (liftDispatch fn nid vals fin sched st
                  (lookupNode nid (EvalSt.nodes st)))

  step-take : ∀ {s lo nid} {κ : Path Γ lo s t}
                {id now} {vals : List (Val Γ s)} {fin sched st}
            → stepFrame⇓ id now (take-f nid) κ vals fin sched st
                (takeDispatch nid vals fin sched st
                  (lookupNode nid (EvalSt.nodes st)))

  step-from-inner : ∀ {s lo op allNid inst} {κ : Path Γ lo s t}
                      {id now} {vals : List (Val Γ s)} {fin sched st r}
                  → innerReact⇓ op allNid inst κ id now vals sched st fin r
                  → stepFrame⇓ id now (from-inner op allNid inst) κ
                      vals fin sched st r

  step-thru-outer : ∀ {u lo op nid} {κ : Path Γ lo u t}
                      {id now} {vals : List (Val Γ (obs u))} {fin sched st}
                      {vs bs sched′ st′}
                  → thruWalk⇓ op nid κ id now vals sched st
                      (vs , bs , sched′ , st′)
                  → stepFrame⇓ id now (thru-outer op nid) κ vals fin sched st
                      (thruWrap op nid fin (vs , bs , sched′ , st′))

data pushBurst⇓ {n} {Γ} {t} {e} where

  push-nil : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {id now sched st}
           → pushBurst⇓ id now f κ [] sched st ([] , sched , st)

  push-cons : ∀ {s u lo} {f : Frame Γ s u} {κ : Path Γ lo u t} {id now}
                {em ems sched st} {vs bs c}
                {vals′ evs fin′ sched₁ st₁} {rest sched₂ st₂}
            → splitEvents {A = Val Γ u} (InstEmit.events em) ≡ (vs , bs , c)
            → stepFrame⇓ id now f κ vs c sched st
                (vals′ , evs , fin′ , sched₁ , st₁)
            → pushBurst⇓ id now f κ ems sched₁ st₁ (rest , sched₂ , st₂)
            → pushBurst⇓ id now f κ (em ∷ ems) sched st
                ( ((bs ++ retagEvents evs ++ map value vals′
                      ++ (if fin′ then complete ∷ [] else []))
                    at InstEmit.instant em
                    from InstEmit.source em
                    as InstEmit.kind em)
                  ∷ rest
                , sched₂ , st₂ )

data subscribeAll⇓ {n} {Γ} {t} {e} where

  sub-all : ∀ {u lo op} {ns : NodeState Γ} {b : Closed Γ (obs u)}
              {κ : Path Γ lo u t} {id now sched st nid burst sched₂ st₁ r}
          → freshId nodeᵏ (Sched.mint sched) ≡ nid
          → subscribeE⇓ b (thru-outer op nid ↠ κ) id now
              (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
              (installNode nid ns st)
              (burst , sched₂ , st₁)
          → pushBurst⇓ id now (thru-outer op nid) κ burst sched₂ st₁ r
          → subscribeAll⇓ op ns b κ id now sched st r

-- THE THIRD GUARD THE RELATION DOES NOT INDEX, AND THE SAME RULING AS
-- THE UNFOLD'S.  The connect compares the unconnected-share count
-- against a component of the caller's own measure, which is threaded
-- alongside every argument and is a function of none of them — so it is
-- not among these indices and no premise could pin it.  Both
-- constructors are therefore unconditional in it, and that concedes
-- nothing: at a run that answered no, the result is a dry burst, which
-- no constructor of this family produces, so the comparison stays owed
-- by the inhabitation proof rather than being assumed away here.
data sharedConnect⇓ {n} {Γ} {t} {e} where

  connect-live : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {id now sched st burst sched₁ st₂ rid}
               → freshId regᵏ (Sched.mint sched) ≡ rid
               → subscribeE⇓ d (share-sink i ≤-refl) id now
                   (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                   (register rid (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares =
                           toℕ i ∷ EvalSt.connectedShares st }))
                   (burst , sched₁ , st₂)
               → burstCompleted burst ≡ false
               → sharedConnect⇓ i d κ below id now sched st
                   ( ((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                     ∷ sharedPlumb burst
                   , sched₁ , st₂ )

  connect-died : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {id now sched st burst sched₁ st₂ rid}
               → freshId regᵏ (Sched.mint sched) ≡ rid
               → subscribeE⇓ d (share-sink i ≤-refl) id now
                   (record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) })
                   (register rid (atSlot i) (lowerFloor below κ)
                     (record st
                       { connectedShares =
                           toℕ i ∷ EvalSt.connectedShares st }))
                   (burst , sched₁ , st₂)
               → burstCompleted burst ≡ true
               → sharedConnect⇓ i d κ below id now sched st
                   ( ((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                       at id from toℕ i as subscribe)
                     ∷ sharedPlumb burst
                   , sched₁
                   , record st₂
                       { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                       ; completedSources =
                           toℕ i ∷ EvalSt.completedSources st₂ } )

data subscribeSharedSlot⇓ {n} {Γ} {t} {e} where

  slot-spent : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                 {below : toℕ i < lo} {id now sched st}
             → memberSource (toℕ i) (EvalSt.completedSources st) ≡ true
             → subscribeSharedSlot⇓ i d κ below id now sched st
                 (spentBurst (toℕ i) id , sched , st)

  slot-join : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                {below : toℕ i < lo} {id now sched st rid}
            → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
            → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ true
            → freshId regᵏ (Sched.mint sched) ≡ rid
            → subscribeSharedSlot⇓ i d κ below id now sched st
                ( ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
                , record sched { mint = setAt regᵏ (suc rid) (Sched.mint sched) }
                , register rid (atSlot i) (lowerFloor below κ) st )

  slot-connect : ∀ {lo} {i : Fin n} {d} {κ : Path Γ lo (lookup Γ i) t}
                   {below : toℕ i < lo} {id now sched st r}
               → memberSource (toℕ i) (EvalSt.completedSources st) ≡ false
               → memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false
               → sharedConnect⇓ i d κ below id now sched st r
               → subscribeSharedSlot⇓ i d κ below id now sched st r

-- THE ONE CLAUSE, and the whole reason the share cycle is separate: the
-- fan-out re-enters at the floor the sink's own premise names, so the
-- relation carries that premise as a constructor argument and the
-- descent it buys is a fact about the index rather than a peeled
-- witness.  `shareFinish`, `shareAdmit` and `shareLatch` compute, so
-- they stay applied.
data dispatchShare⇓ {n} {Γ} {t} {e} where
  disp : ∀ {lo id now} {i : Fin n} {below : lo ≤ toℕ i}
           {vals fin sched st} {r}
       → shareGo⇓ id now i vals fin
           (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st) r
       → dispatchShare⇓ id now i below vals fin sched st
           (shareFinish i fin r)

-- THE CANCELLATION TEST STAYS A PREMISE RATHER THAN A SIDE CONDITION.
-- It is decidable and it decides which of two clauses ran, so the
-- relation carries the answer as an equation and the two arms cannot
-- both apply.  `go-live` is where the threading shows: what the tail is
-- handed is the head's own results, which is why this is a graph
-- relation and not a domain predicate.
data shareGo⇓ {n} {Γ} {t} {e} where
  go-nil : ∀ {lo id now} {i : Fin n} {vals fin sched st}
         → shareGo⇓ {lo = lo} id now i vals fin [] sched st
             ([] , sched , st)

  go-cut : ∀ {lo id now} {i : Fin n} {vals fin rid}
             {p : Path Γ lo (lookup Γ i) t} {ps sched st r}
         → any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true
         → shareGo⇓ id now i vals fin ps sched st r
         → shareGo⇓ id now i vals fin ((rid , p) ∷ ps) sched st r

  go-live : ∀ {lo id now} {i : Fin n} {vals fin rid}
              {p : Path Γ lo (lookup Γ i) t} {ps sched₀ st₀}
              {emits sched₁ st₁ rest sched₂ st₂}
          → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
          → foldPath⇓ id now (toℕ i) p vals
              (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched₀
              (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
              (emits , sched₁ , st₁)
          → shareGo⇓ id now i vals fin ps sched₁ st₁ (rest , sched₂ , st₂)
          → shareGo⇓ id now i vals fin ((rid , p) ∷ ps) sched₀ st₀
              (emits ++ rest , sched₂ , st₂)

-- THE PATH IS WALKED SINKWARD AND THE ENVELOPE IS ASSEMBLED HERE, so
-- the root clause is the only one that mints an emit from nothing and
-- the other two hand their own results on.  The sink clause is where
-- the floor descends: its premise is the path constructor's argument,
-- so nothing has to be carried alongside.
data foldPath⇓ {n} {Γ} {t} {e} where
  fold-root : ∀ {lo id now envSrc} {vals : List (Val Γ t)} {evs fin sched st}
            → foldPath⇓ {lo = lo} id now envSrc root vals evs fin sched st
                ( ((evs ++ map value vals
                        ++ (if fin then complete ∷ [] else []))
                     at id from envSrc as delivery) ∷ []
                , sched , st )

  fold-sink : ∀ {lo id now envSrc} {i : Fin n} {below : lo ≤ toℕ i}
                {vals evs fin sched st} {fanout sched₁ st₁}
            → dispatchShare⇓ id now i below vals fin sched st
                (fanout , sched₁ , st₁)
            → foldPath⇓ id now envSrc (share-sink i below) vals evs fin sched st
                ( ((evs ++ handoff (toℕ i) ∷ [])
                     at id from envSrc as delivery) ∷ fanout
                , sched₁ , st₁ )

  fold-step : ∀ {lo s u id now envSrc} {f : Frame Γ s u}
                {path′ : Path Γ lo u t} {vals evs fin sched st}
                {vals′ evs′ fin′ sched₁ st₁ r}
            → stepFrame⇓ id now f path′ vals fin sched st
                (vals′ , evs′ , fin′ , sched₁ , st₁)
            → foldPath⇓ id now envSrc path′ vals′ (evs ++ evs′) fin′ sched₁ st₁ r
            → foldPath⇓ id now envSrc (f ↠ path′) vals evs fin sched st r

data chainStep⇓ {n} {Γ} {t} {e} where
  chain-step : ∀ {id} {a : Arrival Γ} {lo} {path : Path Γ lo (arrTy a) t}
                 {sched st r}
             → foldPath⇓ id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a
                    then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st r
             → chainStep⇓ id a (lo , path) sched st r

data cascadeGo⇓ {n} {Γ} {t} {e} where
  casc-nil : ∀ {a id sched₀ st₀}
           → cascadeGo⇓ a id [] sched₀ st₀ ([] , sched₀ , st₀)
  casc-cut : ∀ {a id rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀ r}
           → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ true
           → cascadeGo⇓ a id chains sched₀ st₀ r
           → cascadeGo⇓ a id ((rid , c) ∷ chains) sched₀ st₀ r
  casc-live : ∀ {a id rid} {c : AtFloor Γ (arrTy a) t} {chains sched₀ st₀}
                {emits sched₁ st₁ rest sched₂ st₂}
            → any (_≡ᵇ rid) (EvalSt.cancelled st₀) ≡ false
            → chainStep⇓ id a c sched₀
                (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
                (emits , sched₁ , st₁)
            → cascadeGo⇓ a id chains sched₁ st₁ (rest , sched₂ , st₂)
            → cascadeGo⇓ a id ((rid , c) ∷ chains) sched₀ st₀
                (emits ++ rest , sched₂ , st₂)

data cascade⇓ {n} {Γ} {t} {e} where
  casc-run : ∀ {a id sched st} {emits sched′ st′}
           → cascadeGo⇓ a id (chainsOf a st) sched (cascadeLatch a sched st)
               (emits , sched′ , st′)
           → cascade⇓ a id sched st (emits , cascadeFinish a sched′ st′)

data drain⇓ {n} {Γ} {t} {e} where
  drain-done : ∀ {nextId sched st}
             → drain⇓ zero nextId sched st []
  drain-empty : ∀ {k nextId sched st}
              → sched-next sched ≡ inj₁ tt
              → drain⇓ (suc k) nextId sched st []
  drain-step : ∀ {k nextId sched st} {a : Arrival Γ}
                 {sched′ out sched″ st′ rest}
             → sched-next sched ≡ inj₂ (a , sched′)
             → cascade⇓ a nextId sched′ st (out , sched″ , st′)
             → drain⇓ k (suc nextId) sched″ st′ rest
             → drain⇓ (suc k) nextId sched st (out ++ rest)

data evaluate⇓ {n} {Γ} {t} where
  eval-run : ∀ {fuel} {e : Closed Γ t} {ins : Slots Γ}
               {burst sched₀ st₀ rest}
           → subscribeE⇓ {e = e} {lo = n} e root 0 0
               (sched-init e ins) (st-init e) (burst , sched₀ , st₀)
           → drain⇓ {e = e} fuel 1 sched₀ st₀ rest
           → evaluate⇓ fuel e ins (burst ++ rest)
