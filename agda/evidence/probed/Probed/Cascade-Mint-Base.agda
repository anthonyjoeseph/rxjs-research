-- THE ENTRY MINT COUNT AGAINST THE ENTRY WIDTH.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
-- TARGET: cascadeGo-mint-pW
--
-- WHY THIS INDEX AND NO OTHER, and it is the reason the target was split
-- off from its tower half.  The charge here is a WIDTH CEILING, a
-- syntactic reading that reduces; one index up the charge is a width
-- raised to a cap and nothing renders it, so the entry is the only place
-- a row can be taken at all -- and it is also the tight place.
--
-- AND THE CEILING IS THE CHARGE BECAUSE THE SMALLER CANDIDATE IS FALSE.
-- The obvious leaf is the program's own size, and rows kill it: two
-- families mint past their whole syntax at the entry -- 64 against 50,
-- and 140 against 46 -- so a size-denominated leaf would have been
-- stated and refuted.  The ceiling is what the entry charge actually
-- carries, and it survives everywhere the smaller reading dies.
--
-- WHICH SIDE IS BLOCKED, since only one is.  The CONCLUSION computes
-- fully: the count comes off the schedule's own counter across a real
-- walk, and `capsBase` off the program's syntax.  The premises do NOT --
-- `capsOK?` reads `capsAt`, whose every field is an iteration whose count
-- is exponential in the registry cap, so no instantiation of it
-- terminates and these rows cannot certify that their states are ones the
-- target admits.  What a row here can do is REFUTE, and that is the use
-- it is put to.
--
-- EVERY ROW IS LOAD-BEARING, and the count is what makes it so.  The mint
-- count is whatever the run makes it -- it grows with the fold depth of
-- the family, unboundedly, and nothing in the walk holds it down -- so a
-- program whose entry cascade minted past its own `capsBase` would refute
-- the target outright.  Each block therefore pins the COUNT and the
-- CHARGE beside the verdict: a count pinned above zero is a walk that
-- actually subscribed something, and the two numbers together say how
-- much room the row had rather than merely that it fitted.
module Probed.Cascade-Mint-Base where

open import Data.List using ([])
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _∸_; _≤ᵇ_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; cascadeGo; chainsOf)
open import Rx.Slots using (Slots)
open import Rx.Frame-Width using (entryCeil; outWⱽ; dWⱽ)

open import Verify-Budget-Sufficient.Demand-Programs
  using (Γ₂; progU; progC; progF; insF; sucGU; sucGC; sucGF)

----------------------------------------------------------------------
-- The reading: how many instances the ENTRY walk mints, the charge it
-- is allowed, and the verdict.  Taken at the arrival the subscribe
-- leaves behind, which is the index the target is stated at.
----------------------------------------------------------------------

readM : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool × ℕ × Bool
readM e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false , 0 , false
... | inj₂ (a , sd) =
  let g  = cascadeGo a 1 (chainsOf a st) sd (cascadeLatch a st)
      m  = Sched.nextNode (proj₁ (proj₂ g)) ∸ Sched.nextNode sd
      pw = outWⱽ 2 [] sl e ⊔ dWⱽ 2 [] sl e
  in m , entryCeil 2 sl e , (m ≤ᵇ entryCeil 2 sl e) , pw , (m ≤ᵇ pw)

entry : ∀ {t} (e : Closed Γ₂ t) → Slots Γ₂ → ℕ → Sched Γ₂ × EvalSt e
entry e sl g =
  let r = subscribeE (gasPad g g0) e root 0 0 (sched-init e sl) (st-init e)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

sl₁ : Slots Γ₂
sl₁ = insF 1 2 2

----------------------------------------------------------------------
-- ROW 1 — THE BOUNDED DRAIN.  `progU` is the limit-1 mergeAll family,
-- so its inners park and every release is a subscription; this is the
-- family whose count the harness watched grow with fold depth, and so
-- the one whose entry row has the most to lose.
----------------------------------------------------------------------

pU : Closed Γ₂ natᵗ
pU = progU 2 2

rowU : ℕ × ℕ × Bool × ℕ × Bool
rowU = let e₀ = entry pU sl₁ (sucGU 1 2 2 2 2)
       in readM pU sl₁ (proj₁ e₀) (proj₂ e₀)

U-mint : proj₁ rowU ≡ 5
U-mint = refl

U-charge : proj₁ (proj₂ rowU) ≡ 72
U-charge = refl

U-fits : proj₁ (proj₂ (proj₂ rowU)) ≡ true
U-fits = refl

----------------------------------------------------------------------
-- ROW 2 — THE SKIP BRANCH.  `progC`'s arrival selects more chains than
-- it delivers on, so the walk steps chains that mint nothing; the count
-- has to come out below the chain count here rather than tracking it.
----------------------------------------------------------------------

pC : Closed Γ₂ natᵗ
pC = progC 1 2 2

rowC : ℕ × ℕ × Bool × ℕ × Bool
rowC = let e₀ = entry pC sl₁ (sucGC 1 2 2 1 2 2)
       in readM pC sl₁ (proj₁ e₀) (proj₂ e₀)

C-mint : proj₁ rowC ≡ 7
C-mint = refl

C-charge : proj₁ (proj₂ rowC) ≡ 96
C-charge = refl

C-fits : proj₁ (proj₂ (proj₂ rowC)) ≡ true
C-fits = refl

----------------------------------------------------------------------
-- ROW 3 — DELIVERY ON EVERY CHAIN.  `progF` exercises the arm `progC`
-- skips, so its entry walk mints on each chain it selects rather than
-- on a subset.
----------------------------------------------------------------------

pF : Closed Γ₂ natᵗ
pF = progF 1 1

rowF : ℕ × ℕ × Bool × ℕ × Bool
rowF = let e₀ = entry pF sl₁ (sucGF 1 2 2 1 1)
       in readM pF sl₁ (proj₁ e₀) (proj₂ e₀)

F-mint : proj₁ rowF ≡ 20
F-mint = refl

F-charge : proj₁ (proj₂ rowF) ≡ 96
F-charge = refl

F-fits : proj₁ (proj₂ (proj₂ rowF)) ≡ true
F-fits = refl

----------------------------------------------------------------------
-- THE WIDTH CHARGE, read beside the ceiling one.  `entryCeil` is a ⊔
-- over the whole syntax tree and a proven family already bounds each
-- width measure by it, so if the entry count fits under the PATH width
-- the leaf can be restated there and the transport is spent rather
-- than proven.  These rows are what say whether that is worth doing.
----------------------------------------------------------------------

U-pw : proj₁ (proj₂ (proj₂ (proj₂ rowU))) ≡ 72
U-pw = refl

U-pw-fits : proj₂ (proj₂ (proj₂ (proj₂ rowU))) ≡ true
U-pw-fits = refl

C-pw : proj₁ (proj₂ (proj₂ (proj₂ rowC))) ≡ 96
C-pw = refl

C-pw-fits : proj₂ (proj₂ (proj₂ (proj₂ rowC))) ≡ true
C-pw-fits = refl

F-pw : proj₁ (proj₂ (proj₂ (proj₂ rowF))) ≡ 96
F-pw = refl

F-pw-fits : proj₂ (proj₂ (proj₂ (proj₂ rowF))) ≡ true
F-pw-fits = refl
