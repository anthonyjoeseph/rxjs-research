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

open import Data.List using ([]; length; foldr)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _∸_; _≤ᵇ_; _⊔_; _*_; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; cascadeGo; chainsOf; capsBase)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (nodeNest; storeNestMax; nestSyn)
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

----------------------------------------------------------------------
-- THE CHAIN-COUNT AXIS, which is the one that can refute this leaf.
-- The mint count is a SUM over the chains `cascadeGo` folds, and the
-- charge is a MAX over the syntax; nothing in the shape of the two
-- says the sum stays under it.  `progF`'s `w` registers `suc w` copies
-- of one input, so an arrival there presents `suc w` chains and the
-- sum is driven directly.  LOAD-BEARING on every row: if the count
-- climbs per chain while the width does not, one of these fails, and
-- that is a refutation of the statement rather than of a route.
----------------------------------------------------------------------

rowF2 : ℕ × ℕ × Bool × ℕ × Bool
rowF2 = let e₀ = entry (progF 2 1) sl₁ (sucGF 1 2 2 2 1)
        in readM (progF 2 1) sl₁ (proj₁ e₀) (proj₂ e₀)

rowF3 : ℕ × ℕ × Bool × ℕ × Bool
rowF3 = let e₀ = entry (progF 3 1) sl₁ (sucGF 1 2 2 3 1)
        in readM (progF 3 1) sl₁ (proj₁ e₀) (proj₂ e₀)

rowF4 : ℕ × ℕ × Bool × ℕ × Bool
rowF4 = let e₀ = entry (progF 4 1) sl₁ (sucGF 1 2 2 4 1)
        in readM (progF 4 1) sl₁ (proj₁ e₀) (proj₂ e₀)

F2-mint : proj₁ rowF2 ≡ 33
F2-mint = refl

F3-mint : proj₁ rowF3 ≡ 48
F3-mint = refl

F4-mint : proj₁ rowF4 ≡ 65
F4-mint = refl

F2-pw : proj₁ (proj₂ (proj₂ (proj₂ rowF2))) ≡ 120
F2-pw = refl

F3-pw : proj₁ (proj₂ (proj₂ (proj₂ rowF3))) ≡ 144
F3-pw = refl

rowF18 : ℕ × ℕ × Bool × ℕ × Bool
rowF18 = let e₀ = entry (progF 18 1) sl₁ (sucGF 1 2 2 18 1)
         in readM (progF 18 1) sl₁ (proj₁ e₀) (proj₂ e₀)

F18-pw-fits : proj₂ (proj₂ (proj₂ (proj₂ rowF18))) ≡ false
F18-pw-fits = refl

F18-fits : proj₁ (proj₂ (proj₂ rowF18)) ≡ false
F18-fits = refl

-- AND WHETHER IT REACHES THE CURRENCY.  `capsBase` pads the ceiling by
-- the program's own size, so the question the margin decides is whether
-- this is a restatement of one leaf or a refutation of the charge the
-- caps face actually spends.
F18-base : capsBase (progF 18 1) sl₁ ≡ 586
F18-base = refl

F3-base : capsBase (progF 3 1) sl₁ ≡ 196
F3-base = refl

-- AND THE DECISIVE ROW.  The count is quadratic in the chain axis and
-- every charge over it is linear, so the only question was WHERE they
-- cross, not whether.  This is the first shape past the crossing.
readB : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readB e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let g = cascadeGo a 1 (chainsOf a st) sd (cascadeLatch a st)
      m = Sched.nextNode (proj₁ (proj₂ g)) ∸ Sched.nextNode sd
  in m , capsBase e sl , (m ≤ᵇ capsBase e sl)

rowB22 : ℕ × ℕ × Bool
rowB22 = let e₀ = entry (progF 22 1) sl₁ (sucGF 1 2 2 22 1)
         in readB (progF 22 1) sl₁ (proj₁ e₀) (proj₂ e₀)

B22-mint : proj₁ rowB22 ≡ 713
B22-mint = refl

B22-base : proj₁ (proj₂ rowB22) ≡ 690
B22-base = refl

B22-fits : proj₂ (proj₂ rowB22) ≡ false
B22-fits = refl

----------------------------------------------------------------------
-- THE CANDIDATE REPLACEMENT, read at the shape that refuted the old
-- one.  The count is a SUM over chains, so the charge has to carry the
-- chain count; `chainsOf-length` already reduces that count to the
-- registry, which is what makes the factor payable rather than merely
-- correct.  LOAD-BEARING: at the crossing shape the old charge is 690
-- against 713, so a candidate that also fails here is no candidate.
----------------------------------------------------------------------

readP : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readP e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let ch = chainsOf a st
      g  = cascadeGo a 1 ch sd (cascadeLatch a st)
      m  = Sched.nextNode (proj₁ (proj₂ g)) ∸ Sched.nextNode sd
      c  = length ch * entryCeil 2 sl e
  in m , c , (m ≤ᵇ c)

rowP22 : ℕ × ℕ × Bool
rowP22 = let e₀ = entry (progF 22 1) sl₁ (sucGF 1 2 2 22 1)
         in readP (progF 22 1) sl₁ (proj₁ e₀) (proj₂ e₀)

P22-charge : proj₁ (proj₂ rowP22) ≡ 13800
P22-charge = refl

P22-fits : proj₂ (proj₂ rowP22) ≡ true
P22-fits = refl

rowP1 : ℕ × ℕ × Bool
rowP1 = let e₀ = entry pF sl₁ (sucGF 1 2 2 1 1)
        in readP pF sl₁ (proj₁ e₀) (proj₂ e₀)

P1-charge : proj₁ (proj₂ rowP1) ≡ 192
P1-charge = refl

P1-fits : proj₂ (proj₂ rowP1) ≡ true
P1-fits = refl

----------------------------------------------------------------------
-- THE ASSEMBLY'S OWN CONCLUSION, which is the row that says how much
-- the refutation above actually costs.  The count bound is one ROUTE
-- to `cascadeGo-nest-nodes`; its conclusion is a MAX on the left and a
-- SUM on the right, so a route that over-counts can fail while the
-- fact stands.  LOAD-BEARING both ways: green here means the repair is
-- a better decomposition, red means the currency itself is short.
-- The entry width is spelled `capsBase`, which is what `realWidAt-0`
-- proves it to be -- the family itself is sealed and does not reduce.
----------------------------------------------------------------------

readN : ∀ {t} (e : Closed Γ₂ t) (sl : Slots Γ₂)
      → Sched Γ₂ → EvalSt e → ℕ × ℕ × Bool
readN e sl sched st with sched-next sched
... | inj₁ _        = 0 , 0 , false
... | inj₂ (a , sd) =
  let stL = cascadeLatch a st
      g   = cascadeGo a 1 (chainsOf a st) sd stL
      lhs = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
                  (EvalSt.nodes (proj₂ (proj₂ g)))
      rhs = storeNestMax sd stL + capsBase e sl * nestSyn e sl
  in lhs , rhs , (lhs ≤ᵇ rhs)

rowN22 : ℕ × ℕ × Bool
rowN22 = let e₀ = entry (progF 22 1) sl₁ (sucGF 1 2 2 22 1)
         in readN (progF 22 1) sl₁ (proj₁ e₀) (proj₂ e₀)

N22-fits : proj₂ (proj₂ rowN22) ≡ true
N22-fits = refl
