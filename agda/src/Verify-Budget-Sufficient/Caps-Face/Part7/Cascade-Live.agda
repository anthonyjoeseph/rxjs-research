-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Live
-- cascadeGo-nest-live
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Live where

open import Data.Bool    using (true)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _⊔_; _≤_)
open import Data.Nat.Properties using (≤-trans; m≤n+m)
open import Data.List    using (List; foldr)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Id)
open import Rx.Exp       using (Ctx; Closed)
open import Verify-Budget-Sufficient.Nest-Store using
  (storeNestMax; nestFacAt; 1≤nestFacAt; nest-inflate; nestIncAt; sizeSuc≤nestIncAt;
  stBounded?-live; liveNest)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; cascadeGo; Path; arrTy)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-parts)

-- THE LIVE PLACE IS PRICED BY THE INSTANT'S OWN SIZE CAP, and not by
-- anything the walk carries.  A cascade's post-state satisfies the
-- caps predicate at the cap the instant CLOSES at -- that is what the
-- caps face proves about the same round -- and that predicate's store
-- conjunct bounds every live pending's SIZE.  Depth is pointwise under
-- size, so the whole live ⊔-fold is under the exit cap's size, which
-- is under the instant's increment.  Nothing here inducts over the
-- chain list, and nothing charges an arrival's payload per chain: the
-- fold is not a quantity that accumulates across the walk, so a bound
-- that reads the FINAL state is both the true one and the cheap one.
--
-- DEAD ROUTE: the per-step form -- a chain step charging the live fold
--   it inherits plus its own path factor times the arrival's size, with
--   the round's bound assembled by folding that over the selection --
--   cannot be proven and is not true.  A step's schedule gains pendings
--   from sources the step SUBSCRIBES, whose payloads are neither the
--   arrival's nor bounded by any factor of the path walked; the walk's
--   currency has no term for them, so no per-step statement in it can
--   close, whatever the factor.  The exit cap is where those payloads
--   are already accounted, and reading the fold there is what makes the
--   accounting available.
--
-- REFUTED: `Refuted.Chain-Step-Live-Nest`, three against one at a
--   deferred body three layers deep and five against one at five, so
--   the per-step gap is unbounded in the body's depth.
-- REFUTED: `Refuted.Chain-Step-Live-Seed`, the same at a deep deferred
--   constant parked as a scan's SEED and handed through: the arrival
--   is one unit wide and the node fold reads the seed as zero.
-- REFUTED: `Refuted.Chain-Step-Live-Additive`, the depth-additive
--   charge, at a `map-f` whose function is a deferred constant.
cascadeGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = cascadeGo a nextId chains sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
       ≤ nestFacAt e sl id * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-live {e = e} sl id a nextId chains sched st capsOut =
  ≤-trans (≤-trans liveFits
                   (≤-trans (sizeSuc≤nestIncAt e sl id)
                            (m≤n+m (nestIncAt e sl id) (storeNestMax sched st))))
          (nest-inflate (nestFacAt e sl id) RHS (1≤nestFacAt e sl id))
  where
  r      = cascadeGo a nextId chains sched st
  schedG = proj₁ (proj₂ r)
  stG    = proj₂ (proj₂ r)

  Ŝ : ℕ
  Ŝ = Caps.cSize (capsAt e sl (suc id))

  RHS : ℕ
  RHS = storeNestMax sched st + nestIncAt e sl id

  liveFits : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live schedG) ≤ Ŝ
  liveFits =
    stBounded?-live Ŝ schedG stG
      (proj₁ (capsOK?-parts (capsAt e sl (suc id)) schedG stG capsOut))
