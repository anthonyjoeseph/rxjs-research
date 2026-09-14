-- THE TWO HALVES OF A RUN, INSTANTIATED AT DERIVATIONS BUILT BY HAND.
--
-- WHAT IS AT RISK HERE IS THE MIRROR, NOT THE ARITHMETIC.  Both targets
-- read dryness off a derivation, and a derivation is a finite tree of
-- constructors that were written to mirror the evaluator's clauses one
-- for one.  Nothing checks that mirroring: a constructor whose output
-- index is spelt even slightly differently from the clause it copies
-- still typechecks, and every statement above it goes on being provable
-- about a relation that relates the wrong streams.  A row here is a
-- derivation whose premises are `refl` against the real helpers, so the
-- output index has to be the one the evaluator computes -- which is the
-- only way this repo has to test a mirror short of proving totality.
--
-- THE ROWS ARE LOAD-BEARING BY THE CLOSE EVENT AND NOT BY THE VALUES.
-- `hasDry` looks for a `close _ dried`, so a burst of pure values could
-- not fail whatever it carries; what decides every row below is the
-- event a clause appends when its source finishes.  The one-shot source,
-- the empty source, the zero-take and the mapped source all end in a
-- `close`, and each is a different helper reaching it -- `oneShotBurst`
-- directly, and `pushBurst` through a retag.
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

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (hot; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; nat̂; varᵗ; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; root; rootWitness; subscribeE;
  sched-init; st-init)
open import Rx.Evaluator.Domain using (subs-of; subs-empty; subs-map;
  subs-take-zero; push-cons; push-nil; step-map;
  drain-step; drain-done; casc-run; casc-live; casc-nil; chain-step; fold-root)
open import Verify-Rank-Sufficient using (subscribeE⇓-nodry; drain⇓-nodry;
  subscribeE⇓-total; drain⇓-total)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE SUBSCRIBE HALF.  Four sources, each ending its burst through a
-- different helper.
--
-- TARGET: subscribeE⇓-nodry @c66df9
-- TARGET: subscribeE⇓-total @dc2849
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

three : Closed Γ₀ natᵗ
three = ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])

dbl : Fn Γ₀ [] [] [] natᵗ natᵗ
dbl = varᵗ (here refl)

mapped : Closed Γ₀ natᵗ
mapped = mapᵉ dbl three

zeroTake : Closed Γ₀ natᵗ
zeroTake = takeᵉ (nat̂ 0) three

nothingAtAll : Closed Γ₀ natᵗ
nothingAtAll = emptyᵉ

-- THE ENTRY IS THE MACHINE'S OWN.  Every row below stands at the tick,
-- id and schedule the evaluator enters a run with, so the source
-- allocation the helpers do is the real one rather than one this file
-- chose.
S : (p : Closed Γ₀ natᵗ) → Sched Γ₀
S p = sched-init p ins₀

-- LOAD-BEARING: `oneShotBurst` closes the source itself, so the row
-- fails the moment that close is spelt `dried`.
row-of : Confirms (subscribeE⇓-nodry {e = three} {b = three} {κ = root {lo = 0}}
           {id = 0} {now = 0} {sched = S three} {st = st-init three}
           (subs-of refl))
row-of = refl

-- LOAD-BEARING for the same reason and DEGENERATE in its values: an
-- empty source emits its close and nothing else, which is exactly the
-- burst a value-blind reading of `hasDry` would get wrong.
row-empty : Confirms (subscribeE⇓-nodry
              {e = nothingAtAll} {b = nothingAtAll} {κ = root {lo = 0}}
              {id = 0} {now = 0} {sched = S nothingAtAll}
              {st = st-init nothingAtAll}
              (subs-empty refl))
row-empty = refl

-- LOAD-BEARING: a refused take still closes, and it closes through the
-- same helper on a source that had values to give.
row-take-zero :
  Confirms (subscribeE⇓-nodry {e = zeroTake} {b = zeroTake} {κ = root {lo = 0}}
             {id = 0} {now = 0} {sched = S zeroTake} {st = st-init zeroTake}
             (subs-take-zero refl refl))
row-take-zero = refl

-- LOAD-BEARING AND THE WIDEST OF THE FOUR: the burst reaches the caller
-- through `pushBurst`, which SPLITS the events, re-tags what the frame
-- produced and re-appends the rest — so this row is the one that would
-- catch a retag carrying a close through unchanged.
row-map :
  Confirms (subscribeE⇓-nodry {e = mapped} {b = mapped} {κ = root {lo = 0}}
             {id = 0} {now = 0} {sched = S mapped} {st = st-init mapped}
             (subs-map (subs-of refl) (push-cons refl step-map push-nil)))
row-map = refl

-- LOAD-BEARING ON THE OUTPUT INDEX, which is the one thing the rows
-- above cannot test: they hand a derivation in and let unification
-- choose the triple it is about, so a constructor relating the wrong
-- stream satisfies them.  Here the triple is `subscribeE`'s OWN result,
-- so the row fails unless the clause and the constructor agree on what
-- was emitted, on the schedule left behind and on the state written.
row-total-of :
  Confirms (subscribeE⇓-total {e = three} (rootWitness three ins₀)
             three (root {lo = 0}) 0 0 (S three) (st-init three))
row-total-of = subs-of refl

-- LOAD-BEARING and the widest of the pair, for `row-map`'s reason: the
-- burst reaches the caller through a split, a retag and a re-append, so
-- the index this row pins is one three helpers computed rather than one
-- clause.
row-total-map :
  Confirms (subscribeE⇓-total {e = mapped} (rootWitness mapped ins₀)
             mapped (root {lo = 0}) 0 0 (S mapped) (st-init mapped))
row-total-map = subs-map (subs-of refl) (push-cons refl step-map push-nil)

----------------------------------------------------------------------
-- THE DRAIN HALF, ENTERED AT THE STATE THE ROOT SUBSCRIBE LEFT.
--
-- TARGET: drain⇓-nodry @29af89
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

-- LOAD-BEARING: the arrival is the last of its source, so `fold-root`
-- appends a `complete` and the cascade's finish closes the source — the
-- one place in a drain where a close is written at all.
row-drain :
  Confirms (drain⇓-nodry {e = src} {fuel = 1} {id = 1} {sched = sched₀}
             {st = st₀}
             (drain-step refl
               (casc-run (casc-live refl (chain-step fold-root) casc-nil))
               drain-done))
row-drain = refl

-- LOAD-BEARING ON THE OUTPUT INDEX, as its sibling above: the arrival
-- cycle concatenates a cascade's emits with the rest of the drain, so
-- the row fails unless the cascade's own output index is the one the
-- helpers compute and the recursive call is entered at the id the
-- clause threads.
row-total-drain :
  Confirms (drain⇓-total {e = src} 1 1 sched₀ st₀)
row-total-drain =
  drain-step refl
    (casc-run (casc-live refl (chain-step fold-root) casc-nil))
    drain-done
