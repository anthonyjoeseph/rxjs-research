-- ══════════════════════════════════════════════════════════════════
-- WHAT ONE CHAIN ADDS, CHARGED TO THE PROGRAM AND NOT TO THE STORE IT
-- STARTED FROM.
--
-- TARGET: chainStep-nest-nodesC @532695
-- TARGET: chainStep-nest-regsC @c7e44c
--
-- WHY A SURROGATE AND NOT THE STATEMENT.  The three arms charge the
-- growth to `nestUnit` plus the instant's SIZE CAP, and a cap does not
-- evaluate -- so the right side of the arms as written cannot be
-- instantiated at all.  What the tree proves is that the size cap
-- dominates `2 + sizeᵉ` at every instant, so the charge read here is
-- pure syntax and is SMALLER than the arms'.  Every row is therefore a
-- stronger claim than the arm it is evidence for: green here implies
-- the arm at this program, red here does not refute it.
--
-- WHY THE CHAINS COME FROM THE RUN.  The arms carry a `pathSz?`
-- premise, and a path built by hand does not satisfy it -- that is the
-- refutation the premise exists for.  So the rows take the chain the
-- evaluator itself presents at the second cascade, where the premise
-- holds by the caps invariant the round already carries.
--
-- WHAT IS LOAD-BEARING, AND WHAT IS NOT.  The node and registry rows
-- can fail: both move under a real `chainStep` at one family or the
-- other, and the charge names the program and the slot vocabulary
-- alone -- no term of it reads the state the chain produced.  The LIVE
-- rows are DEGENERATE and are pinned as such: the fold reads zero
-- before and after at both families, so no charge could have lost
-- there and the live arm is UNREACHED by this corpus.  That is why it
-- is not a target here.  The pins are separate from the ordering, so a
-- repair moving either side fails naming a number.
-- ══════════════════════════════════════════════════════════════════
module Probed.Chain-Step-Abs-Charge where

open import Data.Bool using (true; _∧_)
open import Data.Nat using (ℕ; _≤ᵇ_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; sizeᵉ)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascade; cascadeLatch; chainStep; chainsOf)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; nodeNest; regsNestMax; nestUnit)
open import Refuted.Demand-Programs using (Γ₂; progU; progF; insF; sucGU; sucGF)

prog : Closed Γ₂ natᵗ
prog = progU 8 6

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGU 1 2 2 8 6) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

after1 : Sched Γ₂ × EvalSt prog
after1 with sched-next (proj₁ sub)
... | inj₁ _        = sub
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ sub)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

nodesMax : EvalSt prog → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

-- the syntactic charge the instant's size cap dominates, and the arms
-- are stated at that cap
charge : ℕ
charge = nestUnit prog slots + (2 + sizeᵉ prog)

-- the six readings: each component before and after the round's first
-- chain, taken off states the evaluator reached
row : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
row with sched-next (proj₁ after1)
... | inj₁ _        = (0 , 0) , (0 , 0) , (0 , 0)
... | inj₂ (a , sd) with chainsOf a (proj₂ after1)
...   | []            = (0 , 0) , (0 , 0) , (0 , 0)
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ after1)
            r   = chainStep 2 a c sd st₀
            sd′ = proj₁ (proj₂ r)
            st′ = proj₂ (proj₂ r)
        in (liveMax sd , liveMax sd′)
         , (nodesMax st₀ , nodesMax st′)
         , (regsNestMax (EvalSt.registry st₀)
           , regsNestMax (EvalSt.registry st′))

liveRow : ℕ × ℕ
liveRow = proj₁ row

nodesRow : ℕ × ℕ
nodesRow = proj₁ (proj₂ row)

regsRow : ℕ × ℕ
regsRow = proj₂ (proj₂ row)

packed : ℕ
packed = proj₁ liveRow + 100 * proj₂ liveRow
       + 10000 * proj₁ nodesRow + 1000000 * proj₂ nodesRow
       + 100000000 * proj₁ regsRow + 10000000000 * proj₂ regsRow
       + 1000000000000 * charge

figures≡ : packed ≡ 71090916080000
figures≡ = refl

fits : (proj₂ liveRow  ≤ᵇ proj₁ liveRow  ⊔ charge)
     ∧ (proj₂ nodesRow ≤ᵇ proj₁ nodesRow ⊔ charge)
     ∧ (proj₂ regsRow  ≤ᵇ proj₁ regsRow  ⊔ charge) ≡ true
fits = refl

-- ── the fold family, whose frames carry accumulator functions ──────

progB : Closed Γ₂ natᵗ
progB = progF 1 1

subB : Sched Γ₂ × EvalSt progB
subB = let r = subscribeE (gasPad (sucGF 1 2 2 1 1) g0) progB root 0 0
                          (sched-init progB slots) (st-init progB)
       in proj₁ (proj₂ r) , proj₂ (proj₂ r)

afterB : Sched Γ₂ × EvalSt progB
afterB with sched-next (proj₁ subB)
... | inj₁ _        = subB
... | inj₂ (a , sd) =
  let r = cascade a 1 sd (proj₂ subB)
  in proj₁ (proj₂ r) , proj₂ (proj₂ r)

nodesMaxB : EvalSt progB → ℕ
nodesMaxB st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

chargeB : ℕ
chargeB = nestUnit progB slots + (2 + sizeᵉ progB)

rowB : (ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)
rowB with sched-next (proj₁ afterB)
... | inj₁ _        = (0 , 0) , (0 , 0) , (0 , 0)
... | inj₂ (a , sd) with chainsOf a (proj₂ afterB)
...   | []            = (0 , 0) , (0 , 0) , (0 , 0)
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ afterB)
            r   = chainStep 2 a c sd st₀
            sd′ = proj₁ (proj₂ r)
            st′ = proj₂ (proj₂ r)
        in (liveMax sd , liveMax sd′)
         , (nodesMaxB st₀ , nodesMaxB st′)
         , (regsNestMax (EvalSt.registry st₀)
           , regsNestMax (EvalSt.registry st′))

liveRowB : ℕ × ℕ
liveRowB = proj₁ rowB

nodesRowB : ℕ × ℕ
nodesRowB = proj₁ (proj₂ rowB)

regsRowB : ℕ × ℕ
regsRowB = proj₂ (proj₂ rowB)

packedB : ℕ
packedB = proj₁ liveRowB + 100 * proj₂ liveRowB
        + 10000 * proj₁ nodesRowB + 1000000 * proj₂ nodesRowB
        + 100000000 * proj₁ regsRowB + 10000000000 * proj₂ regsRowB
        + 1000000000000 * chargeB

figuresB≡ : packedB ≡ 33020206050000
figuresB≡ = refl

fitsB : (proj₂ liveRowB  ≤ᵇ proj₁ liveRowB  ⊔ chargeB)
      ∧ (proj₂ nodesRowB ≤ᵇ proj₁ nodesRowB ⊔ chargeB)
      ∧ (proj₂ regsRowB  ≤ᵇ proj₁ regsRowB  ⊔ chargeB) ≡ true
fitsB = refl
