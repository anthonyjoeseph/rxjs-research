-- ══════════════════════════════════════════════════════════════════
-- WHAT ONE STEP BUYS AT THE WRAP, whose second factor is neither an
-- arrival nor an accumulator but the inner's own DEFINITION.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT THE QUESTION IS.  A `thru-outer` frame hands on what
-- SUBSCRIBING each arrival emitted, so the arm's bill is not read off
-- the arrival's syntax at all -- the arrival is an observable, and its
-- syntax is a description of a computation whose outputs may be far
-- larger than it is.  A wrapper adds a constructor, which is what
-- makes a fixed report look plausible here and nowhere else in the
-- family; these rows say what the subscription underneath it costs.
--
-- THE ARRIVAL IS A SUBSTITUTING LADDER, whose layers each apply a
-- template that lands its payload twice -- so its own reading grows by
-- a constant per layer while what it EMITS doubles.  That is the gap
-- the head has to pay for, and it is the widest gap an arrival of
-- bounded reading can open.  The node the frame names is REACHED by
-- running a `mergeAll`, not written down; the values are the head's
-- own quantified argument and are supplied.
--
-- WHAT THE ROWS SAY.  At the level the arrival's own premise forces,
-- four layers are admitted outright -- kept as the degenerate boundary
-- -- and eight overflow it while one more level admits them.  So the
-- report is not fixed and it is not large: it grows by one per four
-- layers, against a charge exponential in the width cap.
--
-- WHAT IS COVERED IS THE CLOSURE CONJUNCT AT A FLOOR CAP, not the
-- entry recurrence: `sizeCount` is sealed, so no row here computes
-- `capsAt`, and what transfers is the RATIO, the floor being below the
-- recurrence and the step monotone.  The width cap is read small so
-- the charge is a number rather than a shape.
--
-- AND THE HEAD THE ROWS READ IS THE WRAP, at `mergeAllᵒ` alone.
-- Nothing is claimed of a switch or an exhaust, whose node states
-- gate the subscription differently, and nothing of the three arms
-- that rebuild rather than subscribe.
--
-- TARGET: step-frame-clos-thru @abba14
module Probed.Step-Frame-Clos-Wrap where

open import Data.Bool using (true; false; T)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; strmᵗ; sizeᵉ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Prim using (Gas; g0; gasPad)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; thru-outer; mergeAllᵒ;
  stepFrame; subscribeE; sched-init; st-init; fCharge)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Slot-Clos using (slotClos; slotsClos)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestClosOK?ᵛ; capsOK?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsCaps?)
open import Refuted.Thru-Fit-Frame-Slot using (Γₛ; dDup; sl)

gas : Gas
gas = gasPad 400 g0

progT : Closed Γₛ (obs natᵗ)
progT = mergeAllᵉ nothing (ofᵉ (strmᵗ (dDup 0) ∷ []))

κ : Path Γₛ (obs natᵗ) (obs natᵗ)
κ = root

D : Set
D = Closed Γₛ (obs natᵗ)

slotsOf : (d : D) → T (inputsBelowᵉ 0 d) → Slots Γₛ
slotsOf d ok = sl d ok

runOf : (d : D) → T (inputsBelowᵉ 0 d) → _
runOf d ok = subscribeE gas progT root 0 0
               (sched-init progT (slotsOf d ok)) (st-init progT)

vals : ℕ → List (Val Γₛ (obs (obs natᵗ)))
vals k = dDup k ∷ []

outs : (d : D) (ok : T (inputsBelowᵉ 0 d)) → ℕ → List (Val Γₛ (obs natᵗ))
outs d ok k = proj₁ (stepFrame gas 0 0 (thru-outer mergeAllᵒ 0) κ (vals k) false
                       (proj₁ (proj₂ (runOf d ok))) (proj₂ (proj₂ (runOf d ok))))

base : (d : D) → T (inputsBelowᵉ 0 d) → ℕ
base d ok = 2 + sizeᵉ progT + slotsSize (slotsOf d ok) + slotsClos (slotsOf d ok)

cap : (d : D) → T (inputsBelowᵉ 0 d) → Caps
cap d ok = caps (base d ok) 16 4096

sumClos : (d : D) (ok : T (inputsBelowᵉ 0 d)) → List (Val Γₛ (obs natᵗ)) → ℕ
sumClos d ok []       = 0
sumClos d ok (v ∷ vs) = closSizeᵉ (slotClos (slotsOf d ok)) v + sumClos d ok vs

arrival : ℕ → ℕ
arrival k = closSizeᵉ (slotClos (slotsOf (dDup 0) tt)) (dDup k)

readings : ℕ
readings = arrival 8
         + 100000 * sumClos (dDup 0) tt (outs (dDup 0) tt 8)
         + 10000000000 * Caps.cSize (frameStep 2 (cap (dDup 0) tt))

readingsʷ≡ : readings ≡ 2053870408700130
readingsʷ≡ = refl

sched₀ : Sched Γₛ
sched₀ = proj₁ (proj₂ (runOf (dDup 0) tt))

st₀ : EvalSt progT
st₀ = proj₂ (proj₂ (runOf (dDup 0) tt))

capBase : Caps
capBase = cap (dDup 0) tt

------------------------------------------------------------------
-- THE PREMISES THE HEAD CARRIES, at the level the arrival forces
------------------------------------------------------------------

capOKʷ : capsOK? (frameStep 1 capBase) sched₀ st₀ ≡ true
capOKʷ = refl

argOKʷ : all (nestClosOK?ᵛ (frameStep 1 capBase) (slotsOf (dDup 0) tt) (obs (obs natᵗ)))
          (vals 8) ≡ true
argOKʷ = refl

valsOKʷ : valsCaps? (frameStep 1 capBase) (slotsOf (dDup 0) tt) (vals 8) ≡ true
valsOKʷ = refl

pathOKʷ : pathSz? (Caps.cSize (frameStep 1 capBase)) (thru-outer mergeAllᵒ 0 ↠ κ) ≡ true
pathOKʷ = refl

------------------------------------------------------------------
-- DEGENERATE at four layers: the level the arrival forces already
-- admits what the wrap hands on
------------------------------------------------------------------

deg₄ʷ : all (nestClosOK?ᵛ (frameStep 1 capBase) (slotsOf (dDup 0) tt) (obs natᵗ))
         (outs (dDup 0) tt 4) ≡ true
deg₄ʷ = refl

------------------------------------------------------------------
-- LOAD-BEARING at eight: that level REFUSES and one more admits
------------------------------------------------------------------

flat₈ʷ : all (nestClosOK?ᵛ (frameStep 1 capBase) (slotsOf (dDup 0) tt) (obs natᵗ))
          (outs (dDup 0) tt 8) ≡ false
flat₈ʷ = refl

step₈ʷ : all (nestClosOK?ᵛ (frameStep 2 capBase) (slotsOf (dDup 0) tt) (obs natᵗ))
          (outs (dDup 0) tt 8) ≡ true
step₈ʷ = refl

------------------------------------------------------------------
-- AND THE REPORT FITS THE CHARGE WITH ROOM THAT IS NOT CLOSE
------------------------------------------------------------------

chargeOKʷ : (1 ≤ᵇ fCharge (Caps.cSize capBase) (Caps.cWid capBase) 1) ≡ true
chargeOKʷ = refl
