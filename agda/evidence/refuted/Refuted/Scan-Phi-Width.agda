-- ══════════════════════════════════════════════════════════════════
-- THE FOLD'S PREMISE IS PER-VALUE AND ITS CHARGE IS EXPONENTIAL IN
-- THE COUNT, so a budget that affords one value does not afford two.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  A scan frame handed a legal path and a
-- burst whose values are affordable can name a ceiling on its
-- accumulator and pay for the fold under the instant's budget.  What
-- it must pay is `(2 ^ sizeᵗ fn) ^ length vals` times that ceiling --
-- one re-wrap of the accumulator per value folded in, which is what a
-- scan does.
--
-- WHERE IT BREAKS, AND IT IS NOT THE BUDGET.  Three of the four
-- premises are about the PATH -- its size legality, its nesting
-- depth, the frame's own shape -- and the fourth is an `all` over the
-- values, which constrains each value separately and says nothing
-- about how many there are.  So the count is a free parameter of the
-- statement while the conclusion is an exponential in it, and no
-- budget survives: the one that exactly affords a single value is
-- beaten by the SAME value repeated once.
-- ══════════════════════════════════════════════════════════════════

-- AND THE MIRROR SAYS WHICH PREMISE IS MISSING, WHICH IS WHAT MAKES
-- THIS A RESTATEMENT AND NOT A DESIGN FAILURE.  The caps face proves
-- `stepFrame-scan-caps` about this very frame, and it takes
-- `length vals ≤ suc (Caps.cWid (frameStep j c))` -- the burst
-- ledger's width conjunct -- as an explicit premise.  The Φ face's
-- version of the same operation does not take it.  So the two faces
-- disagree about the ARGUMENTS rather than about the mathematics, and
-- the undischarged side is the one that has not been checked.
--
-- AND THE WIDTH IS CARRIED WHERE THIS ARM STANDS, so asking for it is
-- not the laundering an added hypothesis usually is.  The walk face's
-- own statements already read the burst's length -- `thruWalk-nodry`
-- spends `length vals` inside `sIterD` -- so the caller has the fact,
-- and what is missing is that this statement never asked for it.
module Refuted.Scan-Phi-Width where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc; _≤_; _+_; _*_; _^_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≮n;
  ≤ᵇ⇒≤; *-identityˡ; *-monoʳ-≤; m≤n+m; m≤m+n)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; emptyᵉ; sizeᵗ)
open import Rx.Nest-Depth using (nestDᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; NodeId; root; _↠_;
  scan-f; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nodeNestAt)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂; foldD; insT)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything -- and it could not be instantiated in any case, since its
-- cap does not return at any program and its budget is sealed.  So the
-- obligation is stated over the quantities the arm's own premises
-- deliver: an abstract cap, budget and nesting unit, with every one of
-- the four premises kept, and the scan arm of `FrameΦHyp` written out
-- as the conclusion.
----------------------------------------------------------------------
ScanΦFits : Set
ScanΦFits = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (B U nu : ℕ) (nid : NodeId)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (p : Path Γ u t) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? B (scan-f fn nid ↠ p) ≡ true →
  pathNestD (scan-f fn nid ↠ p) ≤ nu →
  valsΦ? B U (scan-f fn nid ↠ p) vals ≡ true →
  Σ ℕ λ G →
    (nodeNestAt nid st ⊔ nestDᵛˢ vals ≤ G)
    × (pathΦF B p * ((2 ^ sizeᵗ fn) ^ length vals
                       * (G + length vals * nestDᵗ fn)
                     + pathNestD p) ≤ U)

----------------------------------------------------------------------
-- THE WITNESS.  One scan frame whose function wraps its accumulator a
-- single level -- the smallest fold that nests at all -- sitting at
-- the ROOT, so the path contributes no factor and no depth of its own
-- and the crossing cannot be blamed on anything but the fold.  The
-- burst is one bare nat repeated: both values are at depth zero, so
-- the premise is the same single inequality twice over, and the size
-- cap is the REACHABLE floor this development discharges from rather
-- than the weakest one proven.
----------------------------------------------------------------------

sl : Slots Γ₂
sl = insT 0 0 0

prog : Closed Γ₂ (obs natᵗ)
prog = emptyᵉ

st₀ : EvalSt prog
st₀ = st-init prog

sd : Sched Γ₂
sd = sched-init prog sl

fn : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn = foldD 1

rt : Path Γ₂ (obs natᵗ) (obs natᵗ)
rt = root

whole : Path Γ₂ natᵗ (obs natᵗ)
whole = scan-f fn 0 ↠ rt

v : Val Γ₂ natᵗ
v = 0

pair : List (Val Γ₂ natᵗ)
pair = v ∷ v ∷ []

-- THE BUDGET IS TAKEN AT EXACTLY WHAT ONE VALUE COSTS, so the
-- refutation cannot be dismissed as a budget chosen too small: it is
-- the least one at which the burst is affordable at all, and the
-- crossing is already there at the second value.  A larger budget is
-- beaten by the same construction one value further along, since the
-- premise grows with neither.
U : ℕ
U = pathΦF 21 whole * (0 + pathNestD whole)

-- THE QUANTITIES, PINNED, so a repair moving any of them fails here
-- naming the number rather than turning the crossing into an
-- equality.
nestD≡ : nestDᵗ fn ≡ 1
nestD≡ = refl

depth≡ : pathNestD whole ≡ 1
depth≡ = refl

rootFac≡ : pathΦF 21 rt ≡ 1
rootFac≡ = refl

legal : pathSz? 21 whole ≡ true
legal = refl

unit-ok : pathNestD whole ≤ pathNestD whole
unit-ok = ≤-refl

-- both values clear the budget, since it was taken at their cost
premΦ : valsΦ? 21 U whole pair ≡ true
premΦ = refl

----------------------------------------------------------------------
-- THE ARITHMETIC, AND THE CEILING PLAYS NO PART IN IT.  The bound is
-- taken through the burst's own contribution, so it holds at every
-- `G` the fold could be granted -- including zero.  What crosses is
-- the SQUARE of the re-wrap against a budget that paid for one of it,
-- which is why no ceiling and no larger budget is the repair.
----------------------------------------------------------------------
bound : ∀ (G : ℕ) →
  suc U ≤ pathΦF 21 rt * ((2 ^ sizeᵗ fn) ^ length pair
                            * (G + length pair * nestDᵗ fn)
                          + pathNestD rt)
bound G =
  ≤-trans (≤-trans (≤-trans (≤ᵇ⇒≤ (suc U) ((2 ^ sizeᵗ fn) ^ 2 * 2) tt)
                            (*-monoʳ-≤ ((2 ^ sizeᵗ fn) ^ 2) (m≤n+m 2 G)))
                   (m≤m+n ((2 ^ sizeᵗ fn) ^ 2 * (G + 2)) 0))
          (≤-reflexive (sym (*-identityˡ _)))

scan-phi-width-absurd : ScanΦFits → ⊥
scan-phi-width-absurd pr
  with pr {Γ = Γ₂} {t = obs natᵗ} {e = prog} {s = natᵗ} {u = obs natᵗ}
          sl 21 U (pathNestD whole) 0 fn rt pair sd st₀
          refl legal unit-ok premΦ
... | G , _ , fits = n≮n U (≤-trans (bound G) fits)
