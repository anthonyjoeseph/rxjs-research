-- THE TWO GUARDS' DEAD BRANCHES, INSTANTIATED WHERE THE SWEEP REACHES
-- THEM.  Both statements conclude that a derivation EXISTS at a state
-- whose room cannot peel, so a row is a derivation built from the
-- relation's constructors at a point where the premises hold -- which
-- with no slots is every point, since the room is zero and cannot fall.
--
-- `stuck-hop` is reached by the sweep: `defer(of(5))` schedules its
-- body as an observable arriving at a `mergeAll` frame, and the arrival
-- folds it with no candidate, so the hop that subscribes `of(5)` under
-- the flattener's exit frame is exactly this statement.  `hop-inner` is
-- that subscription, down `from-inner` to the root.
--
-- LOAD-BEARING: `hop-inner`.  It goes through the exit frame's react,
-- the node lookup, the finish's own fold and the drain; it fails if any
-- of them has no rule at this state -- a flattener node the lookup does
-- not find, a registry row the react reads as alive, a drain with no
-- clause for an empty queue.
-- DEGENERATE: `hop-root` and `hop-defer`.  The first folds straight to
-- the root and the second is a premise-free constructor, so neither
-- could fail; they pin that the premises are satisfiable at all.
-- DEGENERATE: `finish-empty`.  `stuck-finish` at an empty queue is the
-- drain's spent clause.  The sweep never reached the statement, so no
-- shape of it is the one a run hands over.
-- DEGENERATE: the continuation each row hands back.  A guard answers
-- with a continuation at its own path, and the raw builder over the
-- root is one at every path here; no row folds it.
--
-- NOT COVERED: a state the RUN reached.  Every state here is the
-- initial one or the initial one with the flattener's node installed by
-- hand; the registry the arrival writes and the lane the consume opens
-- are not modelled.  Nor is a nonempty queue at `stuck-finish`, which
-- is the only shape of it that subscribes anything.
module Probed.Stuck-Branches where

-- TARGET: stuck-hop @f588e7
-- TARGET: stuck-finish @d82f9d

open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (z≤n)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (refl)

open import Probed.Apparatus using (Confirms)
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; ofᵉ; deferᵉ; nat̂; []ᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; sched-init; st-init; installNode;
  mergeAll-st; root; from-inner; mergeAllᵒ; _↠[_]_)
open import Rx.Evaluator.Domain using (subs-of; subs-defer; fold-root; fold-step;
  step-from-inner; react-dead; finish-all-drain; drain-spent)
open import Rx.Evaluator.Reducible using (stuck-hop; stuck-finish; rootRP; fromInnerRawRP)

Γ₀ : Ctx 0
Γ₀ = []ᵛ

prog : Closed Γ₀ natᵗ
prog = deferᵉ (ofᵉ (nat̂ 5 ∷ []))

noSlots : Slots Γ₀
noSlots ()

sched₀ : Sched Γ₀
sched₀ = sched-init prog noSlots

st₀ : EvalSt prog
st₀ = st-init prog

-- the flattener `subs-defer` installs, at the node id it mints first
st₁ : EvalSt prog
st₁ = installNode 0 (mergeAll-st {t = natᵗ} nothing 1 [] false) st₀

five : Val Γ₀ (obs natᵗ)
five = [] , ofᵉ (nat̂ 5 ∷ []) , []ᵉ

later : Val Γ₀ (obs natᵗ)
later = [] , prog , []ᵉ

hop-inner : Confirms (stuck-hop {e = prog} {m = 0} {lo = 0} {S = ⊤} five
              (from-inner mergeAllᵒ 0 1 ↠[ ≤-refl ] root) 1 tt sched₀ st₁
              z≤n (λ ()))
hop-inner =
  (_ , subs-of (fold-step
         (step-from-inner (react-dead refl (finish-all-drain fold-root drain-spent)))
         fold-root))
  , tt , fromInnerRawRP mergeAllᵒ 0 1 (<-wellFounded 0) ≤-refl root rootRP

hop-root : Confirms (stuck-hop {e = prog} {m = 0} {lo = 0} {S = ⊤} five root 0 tt
             sched₀ st₀ z≤n (λ ()))
hop-root = (_ , subs-of fold-root) , tt , rootRP

hop-defer : Confirms (stuck-hop {e = prog} {m = 0} {lo = 0} {S = ⊤} later
              (from-inner mergeAllᵒ 0 1 ↠[ ≤-refl ] root) 1 tt sched₀ st₁
              z≤n (λ ()))
hop-defer = (_ , subs-defer refl refl refl refl) , tt
          , fromInnerRawRP mergeAllᵒ 0 1 (<-wellFounded 0) ≤-refl root rootRP

finish-empty : Confirms (stuck-finish {e = prog} {m = 0} {lo = 0} {S = ⊤} 0 root 1 tt
                 sched₀ st₁ nothing 1 [] false z≤n (λ ()))
finish-empty = (_ , drain-spent) , tt , rootRP
