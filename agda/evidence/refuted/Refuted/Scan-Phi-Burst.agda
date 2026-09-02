-- ══════════════════════════════════════════════════════════════════
-- A GRANT OVER THE NODE DOES NOT REPAIR THE POTENTIAL'S SCAN ARM.
-- The accumulator here is at depth ZERO, so every grant the state can
-- carry is discharged at the same budget, and the arm is still FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHY THIS IS NOT THE REFUTATION ALREADY ON THE ARM.
-- `Refuted.Scan-Acc-Nest` kills the arm on the STORE axis: the emit is
-- the accumulator, the accumulator is deep, and no premise reads the
-- table.  Its finding names a repair -- a grant over what the node may
-- hold -- and this file says that repair is not sufficient on its own.
-- The accumulator here is a bare `ofᵉ`, so a grant bounding what the
-- node holds costs nothing to discharge and the premise is met at the
-- SAME budget with or without it; the gap that remains is the fold's
-- own, and it is a WIDTH.
--
-- WHERE IT BREAKS.  `scanVals` THREADS: each output is the step
-- function applied to the previous output, so a burst of k values
-- applies it k times in sequence and whatever the step adds accrues k
-- times.  The reading refuted surrenders `2 ^ sizeᵗ fn` ONCE for the
-- frame and charges `nestDᵗ fn` once, both read off the step function
-- alone -- neither mentions the burst.  So the premise is a constant
-- in k and the conclusion is linear in it, and the factor buys a fixed
-- number of values rather than a bound.
--
-- WHAT THE NUMBERS SAY.  The step function's size is six, so the
-- premise clears at a budget of 64 whatever the burst.  Sixty-five
-- values fold sixty-five layers on, and the last of them is over.
--
-- WHAT DIES AND WHAT DOES NOT.  The dynamics are untouched: the fold
-- really does return an accumulator sixty-five layers deep, and one
-- substitution really does cost `2 ^ sizeᵗ fn`, which `applyFn-nest`
-- proves.  What dies is the arm's shape -- a per-frame charge with no
-- term in how many times the frame fires -- and with it the reading of
-- the restatement that adds only a store grant.  The iteration face
-- has already paid for this: `stepFrame-nodes-scan` is proven with
-- `(2 ^ sizeᵗ fn) ^ W` under a `length vals ≤ W` premise, so the
-- currency the potential is missing is a power in the BURST WIDTH and
-- not another summand.
--
-- WHAT IS REUSED, AND WHY.  The witness is `Refuted.Scan-Fold-Burst`'s
-- verbatim -- same step function, same accumulator, same burst, same
-- state.  That file states the crossing on the ITERATION's quantity;
-- this one states it on the POTENTIAL's, and sharing the program is
-- what makes the two comparable: one witness, two faces, and the gap
-- is the same fold in both.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Phi-Burst where

open import Data.Bool using (Bool; false; true)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List)
open import Data.Nat using (ℕ; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; natᵗ; obs; sizeᵗ)
open import Rx.Prim using (g0)
open import Rx.Evaluator using
  (Frame; map-f; scan-f; take-f; from-inner; thru-outer;
   Path; root; share-sink; _↠_; stepFrame)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Refuted.Scan-Fold-Burst
  using (Γ₀; deepen; nid; burst; st₀; sched₀)

----------------------------------------------------------------------
-- THE CURRENCY, STATED HERE RATHER THAN IMPORTED, because the reading
-- refuted is a CONSTANT-in-burst charge and the live factor no longer
-- is: the walk's scan arm has since been repriced per burst value, to
-- `(2 ^ suc (sizeᵗ f)) ^ B`.  Reading the live measure would enlarge
-- the right-hand side along with the repair and turn this crossing
-- into an equality without anything going red -- so the frame charge
-- the finding is ABOUT is spelled out below, and the live one is
-- pinned beside the witness so a further repair fails here naming its
-- number.
----------------------------------------------------------------------

frameΦFᶜ : ∀ {n} {Γ : Ctx n} {s u} (B : ℕ) → Frame Γ s u → ℕ
frameΦFᶜ B (map-f f)          = 2 ^ sizeᵗ f
frameΦFᶜ B (scan-f f _)       = 2 ^ sizeᵗ f
frameΦFᶜ B (take-f _)         = 1
frameΦFᶜ B (from-inner _ _ _) = 1
frameΦFᶜ B (thru-outer _ _)   = 2 ^ B

pathΦFᶜ : ∀ {n} {Γ : Ctx n} {s t} (B : ℕ) → Path Γ s t → ℕ
pathΦFᶜ B root           = 1
pathΦFᶜ B (share-sink _) = 1
pathΦFᶜ B (f ↠ p)        = frameΦFᶜ B f * pathΦFᶜ B p

valsΦ?ᶜ : ∀ {n} {Γ : Ctx n} {s t} (B U : ℕ) (path : Path Γ s t)
  (vals : List (Val Γ s)) → Bool
valsΦ?ᶜ {s = s} B U path vals =
  all (λ v → pathΦFᶜ B path * (nestDᵛ s v + pathNestD path) ≤ᵇ U) vals

----------------------------------------------------------------------
-- THE BUDGET.  Exactly what the frame surrenders: the values are bare
-- naturals, so the premise reads `2 ^ sizeᵗ deepen` times the frame's
-- own charge and nothing else.  Taking it as the budget is what makes
-- the row a crossing rather than a scale error -- there is no slack
-- left to blame.
----------------------------------------------------------------------

U : ℕ
U = 64

-- the walk arrives with naturals, so the premise is discharged with
-- the accumulator's own depth playing no part
Φ-hyp-burst : valsΦ?ᶜ 3 U (scan-f deepen nid ↠ root) burst ≡ true
Φ-hyp-burst = refl

outs : List (Val Γ₀ (obs natᵗ))
outs = proj₁ (stepFrame g0 0 0 (scan-f deepen nid) root burst false sched₀ st₀)

-- and it fails on the far side, at the value the sixty-fifth fold left
scan-Φ-burst-absurd : valsΦ?ᶜ 3 U root outs ≡ true → ⊥
scan-Φ-burst-absurd ()

-- WHERE THE LIVE MEASURE SITS AGAINST IT, pinned so that the next
-- repair to the walk's factor fails here naming a number instead of
-- quietly buying this witness room.  The repricing bought the arm a
-- power in the size cap: at a cap of three the same frame surrenders
-- fifteen doublings more than the reading above.
live-factor : pathΦF 3 (scan-f deepen nid ↠ root) ≡ 2097152
live-factor = refl

refuted-factor : pathΦFᶜ 3 (scan-f deepen nid ↠ root) ≡ 64
refuted-factor = refl
