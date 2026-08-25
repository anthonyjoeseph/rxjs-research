-- ══════════════════════════════════════════════════════════════════
-- A SHARE SLOT IS NESTING THE NODE TABLE CANNOT SEE, so an inner-frame
-- bound stated against `nodesMax` alone is FALSE however large its
-- factor.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  The restated inner arm bounds what leaves a
-- `from-inner` frame by the store it entered with, scaled: `nodesMax
-- st′ ⊔ nestDᵛˢ out ≤ 2 ^ cSize c * (nodesMax st ⊔ nestDᵛˢ vals)`.  The
-- factor is there because the drain's subscription SUBSTITUTES, and a
-- substitution multiplies depth by an occurrence count.  That reading
-- is right about the factor and wrong about what it multiplies.
--
-- WHERE IT BREAKS.  `nodesMax` reads the node table, and `nodeNest` of
-- a parked `mergeAll-st` is the max `nestDᵉ` over its QUEUE -- which is
-- SYNTAX.  `nestDᵉ (input i)` is zero, by definition and correctly: the
-- syntax of a slot reference says nothing about the slot.  So a queued
-- inner that is nothing but a reference to a shared def is charged
-- zero, and subscribing it connects the share and delivers whatever the
-- def emits.  A def emitting a payload forty `*All` layers deep sends
-- forty out through a frame whose entire right-hand side is zero.
--
-- AND ZERO IS WHY THE FACTOR CANNOT SAVE IT, which is the half worth
-- having: the refutation below is quantified over EVERY factor, because
-- any multiple of zero is zero.  This is not a bound that needs
-- widening.  It is a bound stated in a currency that does not contain
-- the quantity.
--
-- WHAT DIES AND WHAT DOES NOT.  The store-relative form dies.  The
-- walk's own conclusion does NOT -- it already carries `nestUnit e sl`,
-- which is 41 at this witness against a delivery of 40, so the term the
-- arm is missing is one its parent has had all along.  That makes the
-- repair a summand rather than a redesign, and it composes with the
-- factor the sibling refutation forces rather than replacing it: what
-- the frame owes is the substitution's factor applied to the store AND
-- the slots, since either alone is refuted.
--
-- WHAT IS HAND-BUILT, AND WHY IT DOES NOT SOFTEN THE FINDING.  The
-- state is `st-init` plus one `installNode`, and the arm quantifies
-- over every `st`.  The caps hypothesis is the one that could have made
-- this vacuous, so it is DISCHARGED here rather than argued about:
-- `capsPin` is a `refl` that the arm's own premise holds at this state.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Inner-Drain-Share-Nest where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _*_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; *-zeroʳ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; subst; sym)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Ctx; Closed; Val; natᵗ; obs; emptyᵉ; ofᵉ; switchAllᵉ; input;
         nat̂; strmᵗ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; mergeAll-st; Frame; from-inner; mergeAllᵒ; root;
         stepFrame; sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Nest-Store
  using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?)

----------------------------------------------------------------------
-- THE WITNESS.  One slot, observable-typed, shared with a def whose one
-- emission is a payload forty layers deep -- and a queue holding
-- nothing but a reference to it.  An observable-typed slot MUST be
-- `shared` (`scripted` carries data only), so this is the only shape
-- the finding can take, and it is a shape the telescope permits at
-- index zero because the def mentions no input.
----------------------------------------------------------------------

Γ₃ : Ctx 1
Γ₃ = obs natᵗ ∷ []

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₃ (obs natᵗ)
deepV 0       = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

shareDef : Closed Γ₃ (obs natᵗ)
shareDef = ofᵉ (strmᵗ (deepV 40) ∷ [])

slots₃ : Slots Γ₃
slots₃ zero = shared shareDef {ok = tt}

e : Closed Γ₃ (obs natᵗ)
e = emptyᵉ

sched₀ : Sched Γ₃
sched₀ = sched-init e slots₃

-- the queued inner: a slot reference and nothing else, so the syntax
-- the node table charges is zero
o : Closed Γ₃ (obs natᵗ)
o = input zero

st₀ : EvalSt e
st₀ = installNode 0 (mergeAll-st nothing 1 (o ∷ []) true) (st-init e)

gas : Gas
gas = gs (gs (gs (gs (gs (gs (gs (gs g0)))))))

vals : List (Val Γ₃ (obs natᵗ))
vals = []

f : Frame Γ₃ (obs natᵗ) (obs natᵗ)
f = from-inner mergeAllᵒ 0 1

row : ℕ × ℕ
row = let r = stepFrame gas 0 0 f root vals true sched₀ st₀
      in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)
       , nodesMax st₀ ⊔ nestDᵛˢ vals

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
delivered≡40 : proj₁ row ≡ 40
delivered≡40 = refl

charged≡0 : proj₂ row ≡ 0
charged≡0 = refl

-- THE CAPS PREMISE IS SATISFIED, which is what makes the row load-
-- bearing rather than a state the hypothesis excludes
c₀ : Caps
c₀ = caps 500 500 500

capsPin : capsOK? c₀ sched₀ st₀ ≡ true
capsPin = refl

----------------------------------------------------------------------
-- AND NO FACTOR REPAIRS IT.  Quantified over every `F`, because the
-- charged side is zero and every multiple of zero is zero -- so this
-- kills the caps-scaled form, the unscaled form, and anything between
-- them, in one statement.
----------------------------------------------------------------------

stepFrame-nodes-inner-share-absurd : ∀ (F : ℕ) → proj₁ row ≤ F * proj₂ row → ⊥
-- `40 ≤ᵇ 0` reduces to `false`, so `T` of it IS the empty type
stepFrame-nodes-inner-share-absurd F h =
  ≤⇒≤ᵇ (subst (λ z → proj₁ row ≤ z)
              (subst (λ z → F * z ≡ 0) (sym charged≡0) (*-zeroʳ F)) h)

----------------------------------------------------------------------
-- AND THE TERM THE WALK ALREADY HAS DOES PAY, which is the repair and
-- the reason this refutation costs a summand rather than a design.
-- `foldPath-nodes` charges `nestUnit e sl`; the arm under it does not.
----------------------------------------------------------------------

unit≡41 : nestUnit e slots₃ ≡ 41
unit≡41 = refl
