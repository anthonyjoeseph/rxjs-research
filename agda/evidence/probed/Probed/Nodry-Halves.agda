-- THE HALVES OF A RUN, INSTANTIATED AT DERIVATIONS BUILT BY HAND.
--
-- WHAT IS AT RISK HERE IS THE MIRROR, NOT THE ARITHMETIC.  Every target
-- is inhabited by a finite tree of constructors that were written to
-- mirror the evaluator's clauses one for one.  Nothing checks that
-- mirroring: a constructor whose output index is spelt even slightly
-- differently from the clause it copies still typechecks, and every
-- statement above it goes on being provable about a relation that
-- relates the wrong streams.  A row here is a derivation whose premises
-- are `refl` against the real helpers, so the output index has to be
-- the one the evaluator computes -- which is the only way this repo has
-- to test a mirror short of proving totality.
--
-- AND THE DRAIN ROW REACHES ITS STATE BY RUNNING.  A schedule written
-- out as a record is not one the machine can be in, so the drain row
-- takes the root subscribe's own output as its entry: the live source
-- is the one `sched-init` seeded, the registry is the one the subscribe
-- wrote, and `sched-next` resolving is pinned by `refl` rather than
-- assumed.  It covers `drain-step` over a `fold-root` chain and the
-- `drain-done` tail; the `casc-cut` arm and every path with a frame on
-- it are NOT covered, which is the boundary to read this file against.
module Probed.Nodry-Halves where

open import Data.Bool using (false)
open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Maybe using (nothing)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; n≤1+n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (hot; after_,_)
open import Rx.Exp using (Ctx; Closed; obs; natᵗ; nat̂; strmᵗ; ofᵉ; emptyᵉ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; root; sched-init; st-init; mergeAllᵒ; mergeAll-st)
open import Rx.Evaluator.Doorless using (rootWitness)
open import Rx.Evaluator.Run using (subscribeE)
open import Rx.Evaluator.Domain using (subs-empty; subs-hot-live; push-cons; push-nil; step-thru-outer; walk-nil; sub-all;
  consume-all-nil; react-false; drain-step; drain-done; casc-run; casc-live; casc-nil;
  chain-step; fold-root)
open import Verify-Rank-Sufficient using (
  subscribeE⇓-input-total; subscribeAll⇓-total;
  thruConsume⇓-total; innerReact⇓-total; drain⇓-total)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE SUBSCRIBE HALF.  Four sources, each ending its burst through a
-- different helper.
--
-- TARGET: subscribeAll⇓-total @c07c6e
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

three : Closed Γ₀ natᵗ
three = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

-- THE FLATTENER OVER A SOURCE THAT HANDS IT NO OBSERVABLE, which is the
-- arm that reaches the wrapper's own plumbing and nothing else: a node
-- is installed, the outer runs, and the walk is entered on an empty
-- value list, so the whole derivation is the install, the outer's close
-- and a push carrying no consume.  DEGENERATE in the walk and
-- LOAD-BEARING in the wrapper: the node id the install writes is the one
-- the frame is built at, and a wrapper that minted it twice, or built
-- the frame at the pre-mint counter, fails this row.
flat : Closed Γ₀ natᵗ
flat = mergeAllᵉ nothing (emptyᵉ {t = obs natᵗ})

row-total-all :
  Confirms (subscribeAll⇓-total {e = flat} (rootWitness flat ins₀) mergeAllᵒ
             (mergeAll-st {t = natᵗ} nothing 0 [] false) emptyᵉ
             (n≤1+n 1 , z≤n)
             (root {lo = 0}) 0 0 (sched-init flat ins₀) (st-init flat))
row-total-all =
  sub-all refl (subs-empty refl)
    (push-cons refl (step-thru-outer walk-nil) push-nil)

----------------------------------------------------------------------
-- THE DRAIN HALF, ENTERED AT THE STATE THE ROOT SUBSCRIBE LEFT.
--
-- TARGET: drain⇓-total @abae59
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

ins₁ : Slots Γ₁
ins₁ zero = scripted (hot (after 1 , 7 ∷ []))

src : Closed Γ₁ natᵗ
src = input zero

sched₀ : Sched Γ₁
sched₀ = proj₁ (proj₂ (subscribeE {e = src} (rootWitness src ins₁)
           src (root {lo = 1}) 0 0 (sched-init src ins₁) (st-init src)))

st₀ : EvalSt src
st₀ = proj₂ (proj₂ (subscribeE {e = src} (rootWitness src ins₁)
        src (root {lo = 1}) 0 0 (sched-init src ins₁) (st-init src)))

-- LOAD-BEARING ON THE OUTPUT INDEX: the arrival cycle concatenates a
-- cascade's emits with the rest of the drain, so the row fails unless
-- the cascade's own output index is the one the helpers compute and the
-- recursive call is entered at the id the clause threads.
row-total-drain :
  Confirms (drain⇓-total {e = src} 1 1 sched₀ st₀)
row-total-drain =
  drain-step refl
    (casc-run (casc-live refl (chain-step fold-root) casc-nil))
    drain-done

----------------------------------------------------------------------
-- THE SLOT SUBSCRIBE, WHICH IS THE ONE LEAF WITH A GUARD OF ITS OWN.
--
-- TARGET: subscribeE⇓-input-total @b1fcd2
----------------------------------------------------------------------

-- LOAD-BEARING ON THE FLOOR TEST AND ON THE REGISTRATION, which are the
-- two things this arm does that no other source arm does: the floor
-- comparison decides between a spent burst and a live registration, and
-- the registration lowers the path's floor by the very proof that
-- comparison produced — so a clause lowering by a different witness, or
-- registering under the unlowered path, fails here.  NOT covered: the
-- share arm, whose connect reads the unconnected count against the
-- entry's first component and is where this leaf's falsity is expected;
-- nor the spent script, nor either cold arm.
row-total-input :
  Confirms (subscribeE⇓-input-total {e = src} (rootWitness src ins₁) zero
             (≤-refl , ≤-refl) (root {lo = 1}) 0 0 (sched-init src ins₁)
             (st-init src))
row-total-input = subs-hot-live (s≤s z≤n) refl refl

----------------------------------------------------------------------
-- THE TWO CLAUSES THE PUSH CYCLE LOCALISED ITS HOP ONTO.  Everything
-- between them and the burst is list plumbing and is proven, so these
-- are the only places left where a frame re-enters the subscribe cycle.
--
-- TARGET: thruConsume⇓-total @0eb219
-- TARGET: innerReact⇓-total @4e00e5
----------------------------------------------------------------------

-- AND THE CONSUME ROW STANDS AT A DEEPER PROGRAM THAN ITS SIBLINGS, FOR
-- A REASON THAT IS ITSELF THE FINDING.  The premise the statement now
-- carries asks the handed observable to be written strictly below the
-- rank, and the rank a root builds is the program's own nesting — so at
-- the flattener over an EMPTY inner the rank is nought and no value
-- whatever can clear it.  The point therefore has to give the outer one
-- level of its own, which costs nothing here because the arm under test
-- never reads the program: what it reads is a node id.
flat-deep : Closed Γ₀ natᵗ
flat-deep = mergeAllᵉ nothing (ofᵉ (strmᵗ three ∷ []))

-- DEGENERATE IN THE GUARD AND LOAD-BEARING ON THE DROP: the walk is
-- entered at a node id nothing installed, which is the arm that
-- DISCARDS the observable rather than subscribing it.  The row fails if
-- the clause hands back anything but the schedule and store it was
-- given.  So it pins the drop and NOT the hop: `subscribeInner`'s rank
-- test is not reached at all, nor is the enqueue arm, nor either other
-- operator — and the hop is exactly where this leaf's falsity is
-- expected.
row-total-consume :
  Confirms (thruConsume⇓-total {e = flat-deep} (rootWitness flat-deep ins₀)
             mergeAllᵒ 0 (root {lo = 0}) 0 0 three (≤-refl ∷ᵃ []ᵃ)
             (sched-init flat-deep ins₀) (st-init flat-deep))
row-total-consume = consume-all-nil

-- LOAD-BEARING ON THE HAND-BACK: an inner reaction whose burst did not
-- finish returns its values untouched and reports the frame unfinished,
-- so a clause dropping a value or carrying the incoming flag through
-- fails the row.  NOT covered: the finishing arm, where the registry is
-- read for a live subscription and `innerFinish` re-enters the cycle.
row-total-react :
  Confirms (innerReact⇓-total {e = flat} (rootWitness flat ins₀) mergeAllᵒ
             0 0 (root {lo = 0}) 0 0 (1 ∷ []) (sched-init flat ins₀)
             (st-init flat) false)
row-total-react = react-false
