-- TAKE BOUNDS THE STREAM.  A program whose outermost node is `take k`
-- emits at most k values, whatever sits underneath it and whatever the
-- slots deliver.  It is the smallest claim in this repo that is about
-- the EVALUATOR's own bookkeeping rather than about a correspondence:
-- no spec, no batching, no second run to compare against.
--
-- WHICH IS WHY IT IS THE REHEARSAL (Anthony).  Every other claim on
-- this face needs the run relation to be a function before a statement
-- about "the" output means anything; this one does not, because it is
-- an inequality about the one output the builder produces and holds of
-- any output at all.  So it exercises the take node's budget --
-- `take-st`, the frame, the dispatch split -- with none of the
-- determinacy apparatus in the way, and what it rehearses is the
-- induction over the drain that every well-formedness leaf also owes.
--
-- AND IT IS THE CHEAPEST THING HERE THAT CAN BE FALSE.  The budget is
-- decremented at the dispatch and the cut is emitted from the frame, so
-- an off-by-one between those two points, or a path that delivers
-- before it spends, is a counterexample rather than a hard proof -- and
-- it is reachable at a scripted slot with two entries and a take at one.
module Verify-Take-Bounds where

open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (++-assoc; length-++)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; +-monoʳ-≤)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Nat.Induction using (<-wellFounded)
import Data.List.Relation.Unary.All as All
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Fuel; InstEmit; _at_from_as_; Id; Tick)
open import Rx.Exp using (Ctx; Closed; nat̂; takeᵉ; obs)
open import Rx.Evaluator using (Stream; Sched; EvalSt; take-st; lookupNode;
  sched-init; st-init; root; Path)
open import Rx.Evaluator.Reducible using (reducible; Red; redExpAcc)
open import Rx.Evaluator.Builder using (evaluate↓; drain!)
open import Rx.Slots using (Slots)
open import Rx.Inputs-Below using (ib-topᵉ)
open import Rx.Exp.Guarded using (gsizeᵉ)
open import Rx.Subst-Identity using (subΘ-id-exp)
open import Spec using (valuesOf)
open import Readme-Theorems using (emitValues)

----------------------------------------------------------------------
-- CONCATENATION IS WHAT THE TWO HALVES SHARE.  `emitValues` flattens
-- each instant's events in place, so it commutes with appending runs --
-- and nothing in the repo said so, because every consumer until now
-- read a whole run at once rather than a burst and a drain separately.
----------------------------------------------------------------------

emitValues-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  emitValues (xs ++ ys) ≡ emitValues xs ++ emitValues ys
emitValues-++ []                            ys = refl
emitValues-++ ((es at i from src as κ) ∷ xs) ys =
  trans (cong (valuesOf es ++_) (emitValues-++ xs ys))
        (sym (++-assoc (valuesOf es) (emitValues xs) (emitValues ys)))

----------------------------------------------------------------------
-- THE RUN, IN ITS TWO HALVES.  `evaluate↓` is a subscribe frame followed
-- by a drain, and the take node's budget is the ONLY thing that crosses
-- between them -- so these name the three components the builder threads
-- and nothing else.  They are definitions rather than a shared Σ because
-- a Σ shared by the two leaves would be satisfied by enlarging the
-- witness, and what has to be pinned is that both leaves speak of the
-- SAME budget.
----------------------------------------------------------------------

rootRun : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt (takeᵉ (nat̂ k) e)
rootRun {n = n} k e ins =
  proj₁ (reducible (takeᵉ (nat̂ k) e) (root {lo = n}) 0 0
          (sched-init (takeᵉ (nat̂ k) e) ins) (st-init (takeᵉ (nat̂ k) e)))

rootBurst : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
rootBurst k e ins = proj₁ (rootRun k e ins)

drainRest : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
  (ins : Slots Γ) → Stream Γ t
drainRest fuel k e ins =
  proj₁ (drain! fuel 1 (proj₁ (proj₂ (rootRun k e ins))) (proj₂ (proj₂ (rootRun k e ins))))

-- THE BUDGET THE FRAME HANDS THE DRAIN.  The root's take node is minted
-- at `nextNode` of the initial schedule, which is zero, so the node is
-- named by a numeral rather than by a lookup of its own.  A state with
-- no such node reads as zero, which is the honest reading: the drain
-- then has nothing to spend.  Read off a TRIPLE rather than off the run,
-- so that a statement about the budget transports along an equation
-- between two runs -- which is what the frame's zero arm needs.
budgetOf : ∀ {n} {Γ : Ctx n} {t u} {E : Closed Γ u} →
  Stream Γ t × Sched Γ × EvalSt E → ℕ
budgetOf r with lookupNode 0 (EvalSt.nodes (proj₂ (proj₂ r)))
... | just (take-st b) = b
... | _                = zero

takeBudget : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) → ℕ
takeBudget k e ins = budgetOf (rootRun k e ins)

-- A RUN IS ITS BURST FOLLOWED BY ITS DRAIN, DEFINITIONALLY.  Pinned
-- rather than assumed, because every line below reads the two halves
-- separately and nothing else says they reassemble into the one stream
-- the statement is about.
run-splits : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
  (ins : Slots Γ) →
  evaluate↓ fuel (takeᵉ (nat̂ k) e) ins ≡ rootBurst k e ins ++ drainRest fuel k e ins
run-splits _ _ _ _ = refl

----------------------------------------------------------------------
-- THE TRANSPORT IS WHAT STOPS THE FRAME COMPUTING, and lifting it is
-- the whole of this block.  `reducible` hands back its walk under a
-- `subst` along an expression identity, and that identity is a
-- congruence over the SUBTERM -- stuck the moment the subterm is a
-- variable.  So nothing under it reduces, at any budget, however
-- concrete the take's own argument is.
--
-- IT LIFTS BECAUSE THE EXPRESSION IS NOT IN THE TRIPLE'S TYPE.  A
-- reducibility witness at an observable returns a stream, a schedule
-- and a state, and the expression being transported occurs only in the
-- derivation the Σ pairs alongside them.  So the triple is the SAME
-- triple on both sides and the transport can be pulled off it -- which
-- is what makes the walk's own clauses visible to `refl`.
----------------------------------------------------------------------

red-subst-burst : ∀ {n} {Γ : Ctx n} {u} {b₁ b₂ : Closed Γ u} (eq : b₁ ≡ b₂)
  (f : Red (obs u) b₁) {t} {e : Closed Γ t} {lo}
  (κ : Path Γ lo u t) (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  proj₁ (subst (Red (obs u)) eq f κ id now sched st)
    ≡ proj₁ (f κ id now sched st)
red-subst-burst refl f κ id now sched st = refl

-- THE WALK ITSELF, at the indices `reducible` instantiates: the
-- context's own size as the ceiling out of `ib-topᵉ`, and the two
-- accessors the descent is funded by.
rawRun : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt (takeᵉ (nat̂ k) e)
rawRun {n = n} k e ins =
  proj₁ (redExpAcc (takeᵉ (nat̂ k) e) All.[] tt n (ib-topᵉ (takeᵉ (nat̂ k) e))
          (<-wellFounded n) (<-wellFounded (gsizeᵉ (takeᵉ (nat̂ k) e)))
          (root {lo = n}) 0 0 (sched-init (takeᵉ (nat̂ k) e) ins)
          (st-init (takeᵉ (nat̂ k) e)))

-- AND THE RUN IS THAT WALK.  One equation, and it carries all three
-- components, since the transport was only ever over the derivation.
root-raw : ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  rootRun k e ins ≡ rawRun k e ins
root-raw k e ins =
  red-subst-burst (subΘ-id-exp (takeᵉ (nat̂ k) e)) _ _ _ _ _ _

----------------------------------------------------------------------
-- THE TWO HALVES OF THE BUDGET, and the split is the whole design.  The
-- frame spends some of `k` and hands the rest on; the drain spends no
-- more than it was handed.  Both leaves are denominated in the SAME
-- `takeBudget`, which is a computed number rather than a witness, so
-- neither can be met by enlarging anything.
----------------------------------------------------------------------

postulate
  -- What the subscribe frame spends, plus what it leaves, is within the
  -- budget it started with, AT A POSITIVE BUDGET.  This is the half
  -- that can be false: the node's decrement happens at the dispatch
  -- while the cut is emitted from the frame, so a path that delivers
  -- before it spends parts from this inequality and from nothing else.
  -- Stated at `suc j` because the zero arm is proven below rather than
  -- assumed -- there the frame mints no node at all, so there is no
  -- decrement to get wrong and nothing for a counterexample to exploit.
  -- PROBED: `Probed.Take-Bounds`, at a cut landing INSIDE the burst --
  --   the shape the frame decides on its own.  The row is TIGHT and
  --   pinned beside the same program with the take removed, so it is
  --   not met by a node that emits nothing and does not stand at a
  --   program that was short anyway.  Not reached: every flattening
  --   program, a take nested under another take, and a budget that is
  --   not a literal.
  take-burst-bound-suc :
    ∀ {n} {Γ : Ctx n} {t} (j : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
    length (emitValues (rootBurst (suc j) e ins))
      + takeBudget (suc j) e ins ≤ suc j

  -- And the drain spends no more than it was handed.  Stated over the
  -- budget rather than over `k` because the drain never sees `k`: it
  -- reads the node's state, which is the only thing that crosses the
  -- frame boundary.
  -- PROBED: `Probed.Take-Bounds`, at a cut landing ACROSS two arrivals,
  --   which is the one shape that forces the budget to survive the frame
  --   and be spent in the drain.  TIGHT, and pinned beside the same
  --   program with the take removed.  Not reached: every flattening
  --   program, a take nested under another take, and a budget that is
  --   not a literal.
  take-drain-bound :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ) (e : Closed Γ t)
      (ins : Slots Γ) →
    length (emitValues (drainRest fuel k e ins)) ≤ takeBudget k e ins

----------------------------------------------------------------------
-- THE BOUND.  Stated over the flat value stream rather than over
-- batches, because `take` counts values: a batch-level statement would
-- be weaker exactly where the node is interesting, since the cut can
-- land mid-batch.
----------------------------------------------------------------------

-- THE FRAME'S HALF, and the zero arm is a theorem rather than a
-- hypothesis.  At a budget of zero the walk takes the arm that mints no
-- node, so both summands compute to zero off an abstract subterm -- the
-- one place on this face where the machine decides the bound by itself.
take-burst-bound :
  ∀ {n} {Γ : Ctx n} {t} (k : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  length (emitValues (rootBurst k e ins)) + takeBudget k e ins ≤ k
take-burst-bound zero    e ins =
  subst (λ r → length (emitValues (proj₁ r)) + budgetOf r ≤ 0)
        (sym (root-raw 0 e ins)) z≤n
take-burst-bound (suc j) e ins = take-burst-bound-suc j e ins

take-bounds-values :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ)
    (e : Closed Γ t) (ins : Slots Γ) →
  length (emitValues (evaluate↓ fuel (takeᵉ (nat̂ k) e) ins)) ≤ k
take-bounds-values fuel k e ins =
  subst (λ xs → length (emitValues xs) ≤ k) (sym (run-splits fuel k e ins))
    (subst (_≤ k)
      (sym (trans (cong length (emitValues-++ (rootBurst k e ins)
                                              (drainRest fuel k e ins)))
                  (length-++ (emitValues (rootBurst k e ins)))))
      (≤-trans (+-monoʳ-≤ (length (emitValues (rootBurst k e ins)))
                          (take-drain-bound fuel k e ins))
               (take-burst-bound k e ins)))
