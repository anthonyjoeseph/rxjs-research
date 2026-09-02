-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN REGISTERS WHILE THE WALK CARRIES NOTHING, so the
-- registry arm of the potential's per-frame law is FALSE as written.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  One frame's step may deepen the registry
-- by at most the potential it was handed: the fold over the registry's
-- paths after the step is under the fold before it, joined with `U`.
-- The charge is the potential rather than the frame's own size because
-- what a subscription mints is the subscribed value's frames over the
-- rest of the path, and the potential is exactly that count.
--
-- WHERE IT BREAKS.  The premise is `valsΦ?`, which is `all` over the
-- values the walk is carrying, so an EMPTY burst discharges it by
-- computation at every budget -- `U = 0` included.  The drain arm does
-- not read that list: `from-inner` takes its payload out of the *All
-- node's QUEUE, subscribes it, and `register` appends a path with the
-- fresh `thru-outer` frame on the front.  So a completion walk, which
-- is empty-handed by construction, still lengthens the registry with a
-- path of positive nesting while the premise it had to clear was
-- vacuous.  The gap is not a scale error: it is the same structural
-- one `Refuted.Inner-Drain-Nest` records on the depth face, an arm
-- reading a payload the walk did not hand it, so no hypothesis about
-- the walk's values can reach it.
--
-- WHAT THE NUMBERS SAY.  The registry starts empty, so the fold before
-- the step is zero and the join with `U = 0` is zero; the drain of one
-- queued term whose source is an async input registers one path, whose
-- `pathNestD` is one.  One is not under zero.
--
-- WHAT DIES AND WHAT DOES NOT.  The dynamics are untouched -- the
-- registry really does grow by exactly the frames the subscribed value
-- will push, which is the reading its own instantiation recorded on
-- the rootward-stacking shapes, and that reading is not contradicted
-- here.  What dies is the arm's shape: `valsΦ?` over the burst is the
-- wrong hypothesis for the frame whose input is the queue rather than
-- the burst, and no choice of `U` repairs it, since the hypothesis
-- holds at every `U` while the conclusion fails at the smallest.  The
-- repair is the one the potential's own drain arm has already taken:
-- a grant denominated over the NODE the frame reads, not over the
-- values the walk carries.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Drain-Regs-Nest where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _≤_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; emptyᵉ; ofᵉ; mapᵉ; mergeAllᵉ; nat̂; strmᵗ; input)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; from-inner; mergeAllᵒ; mergeAll-st; root; _↠_;
         stepFrame; sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Nest-Store using (regsNestMax)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; insF)

----------------------------------------------------------------------
-- THE WITNESS.  An outer *All over a map of an ASYNC input, sitting in
-- the node's queue, drained by a completion walk.  The source has to
-- be async for anything to be registered at all -- a synchronous term
-- is subscribed and finished inside the step, minting nothing -- and
-- that is the whole content of the shape: the queue holds a term the
-- walk never saw, and subscribing it is what appends to the registry.
----------------------------------------------------------------------

slots : Slots Γ₂
slots = insF 0 0 2

e : Closed Γ₂ natᵗ
e = emptyᵉ

q : Closed Γ₂ natᵗ
q = mergeAllᵉ nothing (mapᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (input (fsuc fzero)))

sched₀ : Sched Γ₂
sched₀ = sched-init e slots

st₀ : EvalSt e
st₀ = installNode 0 (mergeAll-st nothing 1 (q ∷ []) true) (st-init e)

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

-- the completion walk carries nothing, which is what makes the premise
-- free and the registration invisible to it
vals : List (Val Γ₂ natᵗ)
vals = []

f : Frame Γ₂ natᵗ natᵗ
f = from-inner mergeAllᵒ 0 1

----------------------------------------------------------------------
-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality.
----------------------------------------------------------------------

before : ℕ
before = regsNestMax (EvalSt.registry st₀)

after : ℕ
after = regsNestMax (EvalSt.registry
          (proj₂ (proj₂ (proj₂ (proj₂
            (stepFrame gas 0 0 f root vals true sched₀ st₀))))))

before≡0 : before ≡ 0
before≡0 = refl

after≡1 : after ≡ 1
after≡1 = refl

-- the burst is empty, so the premise is `all` over nothing and holds
-- at the strongest budget there is
Φ-hyp-drain : valsΦ? 3 0 (f ↠ root) vals ≡ true
Φ-hyp-drain = refl

stepFrame-nest-regs-drain-absurd : after ≤ before ⊔ 0 → ⊥
stepFrame-nest-regs-drain-absurd ()
