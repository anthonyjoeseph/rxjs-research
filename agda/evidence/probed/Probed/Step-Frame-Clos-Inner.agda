-- ══════════════════════════════════════════════════════════════════
-- WHAT ONE STEP BUYS AT THE EXITING INNER, whose values do not come
-- from the head's argument at all when it drains.
--
-- PROBES: `refl` receipts at concrete programs.  See EVIDENCE.md.
--
-- WHAT THE QUESTION IS.  A `from-inner` frame passes its values on
-- untouched unless the exit COMPLETES the *All -- the inner is the
-- last alive -- and then the node's parked QUEUE is drained, each
-- queued observable subscribed and its burst appended.  So the arm's
-- second factor is a history: what was enqueued, at whatever level was
-- current when it arrived, and nothing in the head's hypotheses reads
-- that level.  Whether the arm needs a climb at all is the first
-- question, and these rows answer it.
--
-- HOW THE STATE IS REACHED, since a drain cannot be written down.  A
-- concurrency of one over two inners, the first of them open on a hot
-- slot whose only event is asynchronous: the run therefore returns
-- with one lane live and one observable PARKED, which is the state the
-- head is applied at.  The parked one is a substituting ladder, whose
-- layers each land their payload twice, so what the drain emits
-- doubles per layer while the program's own reading grows by a
-- constant.  Completion is the head's own quantified argument and is
-- supplied: an instance id no registration threads.
--
-- WHAT THE ROWS SAY.  One layer is admitted at the base cap and kept
-- as the degenerate boundary; eight overflow it and are admitted one
-- level up.  The drained reading is 26, 250 and 4090 at one, four and
-- eight layers against a base of 147, so the arm is not free and its
-- climb is a step per four layers, against a charge exponential in the
-- width cap.
--
-- WHAT IS COVERED IS THE CLOSURE CONJUNCT AT A FLOOR CAP, not the
-- entry recurrence: `sizeCount` is sealed, so no row here computes
-- `capsAt`, and what transfers is the RATIO, the floor being below the
-- recurrence and the step monotone.  Nothing is claimed about the
-- level the queue was FILLED at -- these rows drain a queue the same
-- instant it was built, which is the easy case and the one the drain
-- law's own row is about.
--
-- AND THE HEAD THE ROWS READ IS `mergeAllᵒ`, the only *All that
-- queues; a switch and an exhaust reach `innerFinish` by other arms
-- that drain nothing.
--
-- TARGET: step-frame-clos-inner @dd3223
module Probed.Step-Frame-Clos-Inner where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Val; Ctx; Fn; natᵗ; obs; ofᵉ; mergeAllᵉ; mapᵉ;
  strmᵗ; nat̂; input; varᵗ; caseᵗ; inlᵗ; sizeᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Prim using (Gas; g0; gasPad; hot; after_,_)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; from-inner; mergeAllᵒ;
  stepFrame; subscribeE; sched-init; st-init; fCharge)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Slot-Clos using (slotClos; slotsClos)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestClosOK?ᵛ; capsOK?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsCaps?)

gas : Gas
gas = gasPad 400 g0

Γᵢ : Ctx 1
Γᵢ = natᵗ ∷ᵛ []ᵛ

slotsI : Slots Γᵢ
slotsI fzero = scripted {ok = tt} (hot ((after 3 , 7) ∷ []))

dup : Fn Γᵢ [] [] [] (obs natᵗ) (obs natᵗ)
dup = strmᵗ (mapᵉ
        (caseᵗ (inlᵗ (varᵗ (there (here refl)))) (nat̂ 0) (varᵗ (here refl)))
        (ofᵉ (varᵗ (here refl) ∷ [])))

lad : ℕ → Closed Γᵢ (obs natᵗ)
lad zero    = ofᵉ (strmᵗ (mergeAllᵉ nothing
                (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))) ∷ [])
lad (suc k) = mapᵉ dup (mergeAllᵉ nothing (ofᵉ (strmᵗ (lad k) ∷ [])))

lift1 : Fn Γᵢ [] [] [] natᵗ (obs natᵗ)
lift1 = strmᵗ (ofᵉ (varᵗ (here refl) ∷ []))

opn : Closed Γᵢ (obs natᵗ)
opn = mapᵉ lift1 (input fzero)

progI : ℕ → Closed Γᵢ (obs natᵗ)
progI k = mergeAllᵉ (just 1) (ofᵉ (strmᵗ opn ∷ strmᵗ (lad k) ∷ []))

κ : Path Γᵢ (obs natᵗ) (obs natᵗ)
κ = root

vals : List (Val Γᵢ (obs natᵗ))
vals = ofᵉ (nat̂ 0 ∷ []) ∷ []

outs : (k : ℕ) → List (Val Γᵢ (obs natᵗ))
outs k = proj₁ (stepFrame gas 0 0 (from-inner mergeAllᵒ 0 99) κ vals true
           (proj₁ (proj₂ (subscribeE gas (progI k) root 0 0
                            (sched-init (progI k) slotsI) (st-init (progI k)))))
           (proj₂ (proj₂ (subscribeE gas (progI k) root 0 0
                            (sched-init (progI k) slotsI) (st-init (progI k))))))

base : ℕ → ℕ
base k = 2 + sizeᵉ (progI k) + slotsSize slotsI + slotsClos slotsI

cap : ℕ → Caps
cap k = caps (base k) 16 4096

sumClos : List (Val Γᵢ (obs natᵗ)) → ℕ
sumClos []       = 0
sumClos (v ∷ vs) = closSizeᵉ (slotClos slotsI) v + sumClos vs

readings : ℕ
readings = sumClos (outs 8) + 100000 * Caps.cSize (cap 8)
         + 10000000000 * Caps.cSize (frameStep 1 (cap 8))
         + 1000000000000000 * sumClos (outs 4)
         + 100000000000000000000 * sumClos (outs 1)

readingsⁱ≡ : readings ≡ 2600250433650014704090
readingsⁱ≡ = refl

schedOf : (k : ℕ) → Sched Γᵢ
schedOf k = proj₁ (proj₂ (subscribeE gas (progI k) root 0 0
                            (sched-init (progI k) slotsI) (st-init (progI k))))

stOf : (k : ℕ) → EvalSt (progI k)
stOf k = proj₂ (proj₂ (subscribeE gas (progI k) root 0 0
                         (sched-init (progI k) slotsI) (st-init (progI k))))

capOKⁱ : capsOK? (cap 8) (schedOf 8) (stOf 8) ≡ true
capOKⁱ = refl

argOKⁱ : all (nestClosOK?ᵛ (cap 8) slotsI (obs natᵗ)) vals ≡ true
argOKⁱ = refl

valsOKⁱ : valsCaps? (cap 8) slotsI vals ≡ true
valsOKⁱ = refl

pathOKⁱ : pathSz? (Caps.cSize (cap 8)) (from-inner mergeAllᵒ 0 99 ↠ κ) ≡ true
pathOKⁱ = refl

degⁱ : all (nestClosOK?ᵛ (cap 1) slotsI (obs natᵗ)) (outs 1) ≡ true
degⁱ = refl

flat₈ⁱ : all (nestClosOK?ᵛ (cap 8) slotsI (obs natᵗ)) (outs 8) ≡ false
flat₈ⁱ = refl

step₈ⁱ : all (nestClosOK?ᵛ (frameStep 1 (cap 8)) slotsI (obs natᵗ)) (outs 8) ≡ true
step₈ⁱ = refl

chargeOKⁱ : (1 ≤ᵇ fCharge (Caps.cSize (cap 8)) (Caps.cWid (cap 8)) 0) ≡ true
chargeOKⁱ = refl
