-- ══════════════════════════════════════════════════════════════════
-- THE SCAN FRAME EMITS THE ACCUMULATOR, AND NO PREMISE HERE BOUNDS
-- IT, so the potential's scan arm is FALSE as written.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  A `scan-f` frame surrenders a factor of
-- `2 ^ sizeᵗ fn` and charges `nestDᵗ fn`, and the arm asks that the
-- values it emits fit the potential the path below it still carries.
-- That reading is right for the MAP frame, whose output is the step
-- function applied to a value the premise measures.  The fold's output
-- is not: `scanVals` emits `applyFn fn (acc , v)`, and `acc` is read
-- out of the NODE TABLE.
--
-- WHERE IT BREAKS.  Take the step function to be the first projection.
-- Then the emit IS the accumulator, its depth is the accumulator's,
-- and the premise reads the incoming value alone -- a numeral, whose
-- depth is zero, under a charge the projection makes zero as well.  So
-- the premise holds at `U = 0`, the strongest reading available, while
-- the emit leaves at the depth the table was carrying.  The gap is the
-- stored value's own depth: it is a parameter of the STATE, and
-- nothing in `vals`, `path` or `B` moves with it.
--
-- WHAT DIES AND WHAT DOES NOT.  Nothing here says the fold cannot be
-- bounded.  It says the bound cannot come from the values in hand,
-- because the frame is not a function of them -- which is the same
-- finding `Refuted.Inner-Drain-Nest` records one arm over, and for the
-- same structural reason: `FrameΦHyp` is `⊤` at both arms while both
-- read a payload the walk did not hand them.  The repair is a grant
-- over what the NODE may hold, and the family raises that obligation
-- where the state is already in scope.
--
-- WHAT IS HAND-BUILT, AND WHY IT DOES NOT SOFTEN THE FINDING.  The
-- state is `st-init` plus ONE `installNode`, and the statement
-- quantifies over every `st`, so this refutes it as written.  Nor is
-- the table an unreachable shape: a scan node holds whatever its own
-- step function last returned, and a fold over observables returns
-- observables, so a deep accumulator is what this node stores after
-- one delivery rather than a state written to order.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Acc-Nest where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; emptyᵉ; varᵗ; fstᵗ; _×ᵗ_)
open import Rx.Evaluator
  using (EvalSt; Frame; scan-f; scan-st; root; _↠_; stepFrame;
         st-init; installNode)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Inner-Drain-Nest using (deepV; sched₀; gas)

----------------------------------------------------------------------
-- THE WITNESS.  A fold whose step function returns its accumulator
-- untouched, so the emit's depth is exactly what the table held and
-- the step function contributes nothing to either side of the reading.
-- Stripping the frame's own contribution is what makes the gap legible
-- as the accumulator's rather than as a constant.
----------------------------------------------------------------------

-- the step function names the payload not at all: it hands back what
-- it was accumulating, which is the smallest fold the language admits
fstFn : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
fstFn = fstᵗ (varᵗ (here refl))

eS : Closed Γ₂ (obs natᵗ)
eS = emptyᵉ

fS : Frame Γ₂ natᵗ (obs natᵗ)
fS = scan-f fstFn 0

-- one numeral in flight: shallow, so the premise reads at zero
valsS : List (Val Γ₂ natᵗ)
valsS = 0 ∷ []

stS : EvalSt eS
stS = installNode 0 (scan-st (deepV 40)) (st-init eS)

outS : List (Val Γ₂ (obs natᵗ))
outS = proj₁ (stepFrame gas 0 0 fS root valsS false sched₀ stS)

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
depthOut : ℕ
depthOut = nestDᵛˢ outS

drainedΦˢ≡40 : depthOut ≡ 40
drainedΦˢ≡40 = refl

-- the walk arrives with a numeral, so the premise is discharged at the
-- strongest budget there is
Φ-hyp-scan : valsΦ? 3 0 (fS ↠ root) valsS ≡ true
Φ-hyp-scan = refl

stepFrame-nest-Φ-scan-absurd : valsΦ? 3 0 root outS ≡ true → ⊥
stepFrame-nest-Φ-scan-absurd ()

----------------------------------------------------------------------
-- AND THE GAP IS THE STORED DEPTH, NOT A CORNER, which is the half
-- worth having: doubling what the table holds doubles what leaves,
-- while the premise does not move at all.  So no summand fixed by the
-- program and no constant repairs the arm -- what is owed is a bound
-- on the NODE, and the values in hand cannot supply one.
----------------------------------------------------------------------

stS′ : EvalSt eS
stS′ = installNode 0 (scan-st (deepV 80)) (st-init eS)

outS′ : List (Val Γ₂ (obs natᵗ))
outS′ = proj₁ (stepFrame gas 0 0 fS root valsS false sched₀ stS′)

depthOut′ : ℕ
depthOut′ = nestDᵛˢ outS′

drainedΦˢ≡80 : depthOut′ ≡ 80
drainedΦˢ≡80 = refl

stepFrame-nest-Φ-scan-wide-absurd : valsΦ? 3 0 root outS′ ≡ true → ⊥
stepFrame-nest-Φ-scan-wide-absurd ()
