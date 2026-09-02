-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN SUBSCRIBES A PARKED DEFER, so charging one frame's live
-- mints to the arrival it was handed is FALSE at the completion arm.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  One frame's step leaves the deepest live
-- source under what it found there, joined with the schedule's slot
-- nesting and with the potential the frame was handed.  The three
-- terms are meant to cover the two mint sites between them: a script's
-- resolved tail comes from a slot, and a deferred body arrives as a
-- value in flight, which the potential charges.
--
-- WHERE IT BREAKS.  There is a THIRD way in, and it reads neither
-- side.  `from-inner` takes its payload out of the *All node's QUEUE
-- and subscribes it, and a queued `deferᵉ` mints a live outright --
-- the clause writes `elemTy = obs u` and puts the deferred BODY in as
-- the pending payload.  The walk that reaches this frame is a
-- COMPLETION walk, empty-handed by construction, so the premise it had
-- to clear is `all` over nothing and holds at every budget, `U = 0`
-- included; the slot sum does not move with a term the slots never
-- held.  So the live grows by the parked body's own depth against a
-- charge that is pinned.
--
-- AND THE GATE IS WHY NO GRANT OVER THE QUEUE REPAIRS IT EITHER.
-- `nestDᵉ` truncates at a defer -- that is what makes μ safe -- so the
-- parked term reads ZERO in the very currency the conclusion is
-- stated in, while the live it mints reads the body.  A premise
-- bounding the queue's nesting is therefore satisfied by the witness
-- as it stands, and the crossing survives it.
--
-- WHAT THIS ADDS TO THE TWO IT SITS BETWEEN.
-- `Refuted.Chain-Step-Live-Nest` found the defer mint and its repair
-- was to charge the ARRIVAL, which is the grant this statement now
-- carries; `Refuted.Drain-Regs-Nest` found the drain arm reading a
-- payload no walk handed it, on the registry axis.  Neither reaches
-- the corner where the two meet, and the corner is where the grant
-- fails: the frame that mints is the one the grant is silent at.
--
-- WHAT DIES AND WHAT DOES NOT.  The dynamics are untouched -- a queued
-- inner really is subscribed when a sibling finishes, and a defer
-- really does schedule its body -- and the arrival grant is not
-- contradicted, since it is what the outer arm needs.  What dies is
-- reading the live axis through the values in flight ALONE.  The
-- numbers point the same way the registry axis already did: a grant
-- denominated over the NODE the frame reads, in a currency that sees
-- through the gate, since the one the conclusion uses does not.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Drain-Live-Defer where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp using (Closed; Val; natᵗ; obs; emptyᵉ; deferᵉ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; from-inner; mergeAllᵒ; mergeAll-st; root; _↠_;
         stepFrame; sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Nest-Store using (liveNest; slotsNestSum)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; insF)
open import Refuted.Chain-Step-Live-Nest using (deepV)

----------------------------------------------------------------------
-- THE WITNESS.  A `mergeAll` node holding one parked `deferᵉ`, and a
-- completion walk over it.  Nothing else is needed: the parked term is
-- not an arrival, so no grant over the walk's values can see it, and
-- it is not a slot, so the schedule's own sum cannot either.
----------------------------------------------------------------------

e : Closed Γ₂ natᵗ
e = emptyᵉ

slots : Slots Γ₂
slots = insF 0 0 2

-- the queued term: a gate over a payload three `switchAllᵉ` layers down
parked : Closed Γ₂ natᵗ
parked = deferᵉ (deepV 3)

sched₀ : Sched Γ₂
sched₀ = sched-init e slots

st₀ : EvalSt e
st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 1 (parked ∷ []) true)
        (st-init e)

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

-- the completion walk carries nothing, which is what makes the premise
-- free and the mint invisible to it
vals : List (Val Γ₂ natᵗ)
vals = []

f : Frame Γ₂ natᵗ natᵗ
f = from-inner mergeAllᵒ 0 1

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

----------------------------------------------------------------------
-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality.
----------------------------------------------------------------------

after : ℕ
after = liveMax (proj₁ (proj₂ (proj₂ (proj₂
          (stepFrame gas 0 0 f root vals true sched₀ st₀)))))

before : ℕ
before = liveMax sched₀

before≡0 : before ≡ 0
before≡0 = refl

after≡3 : after ≡ 3
after≡3 = refl

-- the whole right-hand side at the strongest budget: the slot sum is
-- the only term that is not zero, and it does not move with the body
charge≡1 : before ⊔ slotsNestSum (Sched.slots sched₀) ⊔ 0 ≡ 1
charge≡1 = refl

-- AND THE GATE READS ZERO, which is why bounding the queue does not
-- repair it: the parked term's own nesting is not the live's
parkedNest≡0 : nestDᵛ (obs natᵗ) parked ≡ 0
parkedNest≡0 = refl

-- the burst is empty, so the premise is `all` over nothing and holds
-- at the strongest budget there is
Φ-hyp-drain : valsΦ? 3 0 (f ↠ root) vals ≡ true
Φ-hyp-drain = refl

stepFrame-nest-live-drain-absurd :
  after ≤ before ⊔ slotsNestSum (Sched.slots sched₀) ⊔ 0 → ⊥
-- `3 ≤ᵇ 0 ⊔ 1 ⊔ 0` reduces to `false`, so `T` of it IS the empty type
stepFrame-nest-live-drain-absurd h = ≤⇒≤ᵇ h
