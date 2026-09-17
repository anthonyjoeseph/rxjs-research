-- WHAT A SUBSCRIPTION LEAVES ALONE, WHICH IS THE ONE THING THE
-- REDUCIBILITY BODY CANNOT ESTABLISH FOR ITSELF.  The fold installs its
-- accumulator at an identifier taken from the scheduler's counter and
-- then subscribes its source with that counter already advanced past
-- it.  Whether the accumulator is still there afterwards is not a fact
-- about reducibility at all -- it is a fact about ALLOCATION, and it is
-- stated here so the candidate can spend it rather than assume it.
--
-- THE STATEMENT IS PARAMETERISED BY A FLOOR RATHER THAN READING ONE OFF
-- THE SCHEDULER, AND THAT IS WHAT KEEPS THE TWO CONJUNCTS APART.
-- Stated against the mint's node counter directly, every premise
-- would sit at an advanced counter and the induction would have to
-- transport the bound through each one.  Taking the floor as an
-- argument makes each premise an instance of the SAME statement at the
-- SAME floor, so preservation is one family.  Monotonicity is still
-- owed, but only to re-establish the floor hypothesis for a premise
-- running at a scheduler an earlier premise handed back -- which is a
-- separate induction over the same relations, in its own module,
-- because neither family is a member of the other's cycle.
--
-- AND THE INHERITED CONTINUATION IS NEVER STEPPED, WHICH IS WHY A
-- FRAME'S NODE IS A HYPOTHESIS RATHER THAN A SIDE CONDITION.  No
-- constructor of the frame-step relation walks into the path it is
-- handed: a continuation is threaded down to SUBSCRIBE an inner and
-- nowhere else, and the walk that folds a chain sinkward is reachable
-- only from the cascade, which no subscription enters.  So every node a
-- subscription writes is named by a frame that same subscription built
-- out of the counter, and the only frame whose identifier is not fixed
-- that way is the one its caller handed it -- which is exactly what
-- `FrameAbove` asks about.
module Rx.Evaluator.Freshness where

open import Data.Bool using (true; false)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_)
open import Decide using (≡ᵇ-refl; ≡ᵇ→≡)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Evaluator using (EvalSt; Frame; NodeId; NodeState; take-f; batchSync-f; lift-f; from-inner; thru-outer; lookupNode;
  setNode)

-- a node just written reads back as what was written
lookup-set : ∀ {n} {Γ : Ctx n} (nid : NodeId) (ns : NodeState Γ)
             (ts : List (NodeId × NodeState Γ))
           → lookupNode nid (setNode nid ns ts) ≡ just ns
lookup-set nid ns []             rewrite ≡ᵇ-refl nid = refl
lookup-set nid ns ((k , s) ∷ r) with k ≡ᵇ nid in eq
... | true  rewrite ≡ᵇ-refl nid = refl
... | false rewrite eq = lookup-set nid ns r

-- every node strictly below the floor reads back exactly as it did
-- and it is a RECORD rather than the function type it wraps, because
-- both states appear in that type only under a projection.  A
-- transparent alias would leave every composition asking Agda to
-- invert `EvalSt.nodes`, and the whole induction would arrive as
-- unsolved metas rather than as type errors.
record PreservedBelow {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                      (f : ℕ) (st st′ : EvalSt e) : Set where
  constructor pres
  field below : ∀ k → k < f
              → lookupNode k (EvalSt.nodes st′) ≡ lookupNode k (EvalSt.nodes st)

open PreservedBelow using (below)

-- the frame a caller hands down writes at or above the floor.  A map
-- carries no node at all; the flattener's inner frame carries two, the
-- operator's own and the instance it was opened at.
FrameAbove : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Set
FrameAbove f (lift-f fn nid)             = f ≤ nid
FrameAbove f (take-f nid)                = f ≤ nid
FrameAbove f (batchSync-f nid)           = f ≤ nid
FrameAbove f (from-inner op allNid inst) = f ≤ allNid × f ≤ inst
FrameAbove f (thru-outer op nid)         = f ≤ nid

-- and every node strictly below a write reads back as it did.  The
-- table is an association list, so the two clauses are the two ways a
-- write can miss: past the end, where the write lands as a fresh head
-- the reader walks past, and at a row whose key is the written one,
-- where the reader's own test already answered.
set-above : ∀ {n} {Γ : Ctx n} (nid k : NodeId) (ns : NodeState Γ)
              (ts : List (NodeId × NodeState Γ))
          → (nid ≡ᵇ k) ≡ false
          → lookupNode k (setNode nid ns ts) ≡ lookupNode k ts
set-above nid k ns []            ne rewrite ne = refl
set-above nid k ns ((j , s) ∷ r) ne with j ≡ᵇ nid in eq
... | true  rewrite ≡ᵇ→≡ j nid eq | ne = refl
... | false with j ≡ᵇ k
...   | true  = refl
...   | false = set-above nid k ns r ne

-- a key below a bound is not that bound
<→≢ᵇ : ∀ {k m} → k < m → (m ≡ᵇ k) ≡ false
<→≢ᵇ {zero}  {suc m} _       = refl
<→≢ᵇ {suc k} {suc m} (s≤s p) = <→≢ᵇ p

-- THE TWO INTRODUCTIONS ARE STATED OVER AN EQUATION ON THE TABLE
-- RATHER THAN OVER THE STATES, BECAUSE A STEP THAT LEAVES THE TABLE
-- ALONE RARELY LEAVES THE STATE ALONE.  A truncation's cut rewrites
-- its node and sweeps the registry in one record; a registration
-- touches no node and is still a different state.  Taking the table
-- equation as an argument lets both arrive as `refl` at the call site
-- while the record above stays rigid enough to solve its own indices.
pres-same : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f} (st st′ : EvalSt e)
          → EvalSt.nodes st′ ≡ EvalSt.nodes st
          → PreservedBelow f st st′
pres-same st st′ eq = pres λ k k<f → cong (lookupNode k) eq

pres-trans : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f}
               {st st′ st″ : EvalSt e}
           → PreservedBelow f st st′ → PreservedBelow f st′ st″
           → PreservedBelow f st st″
pres-trans p q = pres λ k k<f → trans (below q k k<f) (below p k k<f)

-- a write at or above the floor preserves everything below it
pres-write : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {f nid}
               (st st′ : EvalSt e) (ns : NodeState Γ)
             → EvalSt.nodes st′ ≡ setNode nid ns (EvalSt.nodes st)
             → f ≤ nid
             → PreservedBelow f st st′
pres-write {nid = nid} st st′ ns eq f≤nid =
  pres λ k k<f → trans (cong (lookupNode k) eq)
                       (set-above nid k ns (EvalSt.nodes st)
                         (<→≢ᵇ (≤-trans k<f f≤nid)))
