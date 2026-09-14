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
--
-- DEAD ROUTE: threading the hop's provenance in the types instead —
--   indexing a stream by the term whose pipeline produced it, so the
--   arriving observable is structurally related to the subscribed term
--   and the recursion becomes ordinary structural descent.  It is
--   cheaper in volume than these families and it was not taken: the
--   index has to run through `Stream`, `Val` and every frame that
--   moves a value, which is a refactor of the evaluator's own
--   vocabulary rather than an addition beside it, and it cannot be
--   abandoned halfway.  It stays available and nothing here forecloses
--   it.
module Rx.Evaluator.Domain where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _<_; _≤_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Tick; Fuel; Id; Source; InstEvent; value; close;
  handoff; complete; exhausted; delivery; _at_from_as_)
open import Rx.Exp using (Ty; obs; Ctx; Val; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; NodeId;
  root; share-sink; _↠_; shareAdmit; shareLatch; shareFinish;
  NodeState; AllOp; RegId; Arrival; AtFloor; arrTy)

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
   → Maybe ℕ → ℕ → List (Closed Γ s) → Sched Γ → EvalSt e
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

data subscribeE⇓ {n} {Γ} {t} {e} where

data subscribeInner⇓ {n} {Γ} {t} {e} where

data thruConsume⇓ {n} {Γ} {t} {e} where

data thruWalk⇓ {n} {Γ} {t} {e} where

data mergeAllDrain⇓ {n} {Γ} {t} {e} where

data innerFinish⇓ {n} {Γ} {t} {e} where

data innerReact⇓ {n} {Γ} {t} {e} where

data stepFrame⇓ {n} {Γ} {t} {e} where

data pushBurst⇓ {n} {Γ} {t} {e} where

data subscribeAll⇓ {n} {Γ} {t} {e} where

data sharedConnect⇓ {n} {Γ} {t} {e} where

data subscribeSharedSlot⇓ {n} {Γ} {t} {e} where

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

data cascadeGo⇓ {n} {Γ} {t} {e} where

data cascade⇓ {n} {Γ} {t} {e} where

data drain⇓ {n} {Γ} {t} {e} where

data evaluate⇓ {n} {Γ} {t} where
