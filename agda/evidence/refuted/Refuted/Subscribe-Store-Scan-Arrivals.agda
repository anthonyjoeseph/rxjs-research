-- ══════════════════════════════════════════════════════════════════
-- THE ARRIVAL COUNT, WHICH IS THE ONE AXIS THIS BOUND DOES NOT PAY
-- FOR.
--
-- The premise bounds the table by iterating `sizeStep` once per unit
-- of `descChg` plus the telescope, and `descChg` is two DEPTH counts
-- -- unfoldings and layers -- with no size in either.  A synchronous
-- source therefore buys arrivals without buying iterations: the
-- emitted values sit at one layer whatever their number, so the
-- exponent is fixed while the seed grows only with the program's
-- syntax.
--
-- WHAT SPENDS THEM IS A STEP THAT WRAPS ITS OWN ACCUMULATOR.  The
-- cell holds the accumulator VALUE, and a step planting that value at
-- two occurrences doubles the cell per arrival while the program text
-- stays fixed.  So the cell is exponential in the arrivals and the
-- bound is affine in them, and the two cross.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Subscribe-Store-Scan-Arrivals where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; hot; Tick; Id)
open import Rx.Exp using (Ctx; Tm; Fn; Closed; natᵗ; obs; _×ᵗ_;
  ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; varᵗ; fstᵗ; nat̂; sizeᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; st-init;
  sched-init; subscribeE; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (descChg)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
SubscribeEStoreScan : Set
SubscribeEStoreScan = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
  (sl : Slots Γ) (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u)
  (z : Tm Γ [] [] [] u) (b : Closed Γ s) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (descChg (obs u) B (scanᵉ f z b) + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵉ (scanᵉ f z b) ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (subscribeE g (scanᵉ f z b) κ id now sched st))))
    ≡ true

-- AND THE GENERAL STATEMENT, WHICH THE SCAN ONE IS A SPECIAL CASE OF.
-- The bound is spelled the same way and reads the same program, so the
-- witness below is a witness against both; the general form is the one
-- worth having, since the scan arm is only where the doubling was
-- easiest to write.
SubscribeESzStore : Set
SubscribeESzStore = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (descChg (obs u) B o + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵉ o ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (subscribeE g o κ id now sched st))))
    ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `dbl` throws the arriving value away and
-- returns a stream built from the accumulator TWICE, so each arrival
-- plants the previous cell at two occurrences.  The source is a
-- synchronous run of `k` naturals, which is the only thing that moves
-- between the two readings below.
----------------------------------------------------------------------
Γ : Ctx 1
Γ = natᵗ ∷ⱽ []ⱽ

sl : Slots Γ
sl fzero = scripted (hot [])

e₀ : Closed Γ (obs natᵗ)
e₀ = ofᵉ []

accᵗ : Tm Γ [] [] (obs natᵗ ×ᵗ natᵗ ∷ []) (obs natᵗ)
accᵗ = fstᵗ (varᵗ (here refl))

dbl : Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
dbl = strmᵗ (mergeAllᵉ nothing (ofᵉ (accᵗ ∷ accᵗ ∷ [])))

seed : Tm Γ [] [] [] (obs natᵗ)
seed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

fires : ℕ → List (Tm Γ [] [] [] natᵗ)
fires zero    = []
fires (suc j) = nat̂ 0 ∷ fires j

srcAt : (k : ℕ) → Closed Γ natᵗ
srcAt k = ofᵉ (fires k)

progAt : (k : ℕ) → Closed Γ (obs natᵗ)
progAt k = scanᵉ dbl seed (srcAt k)

Bval : ℕ → ℕ
Bval k = sizeᵉ (progAt k)

Mval : ℕ → ℕ
Mval k = iterSize 2 (descChg (obs (obs natᵗ)) (Bval k) (progAt k)
                     + slotsSize sl) (Bval k)

stAt : (k : ℕ) → EvalSt e₀
stAt k = proj₂ (proj₂ (subscribeE (gasPad 512 g0) (progAt k)
                        root 0 0 (sched-init e₀ sl) (st-init e₀)))

----------------------------------------------------------------------
-- THE FIGURES, READ ON BOTH SIDES OF THE CROSSING.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the whole mechanism in four numbers.  The
-- exponent is the SAME at both arrival counts -- a synchronous run
-- sits at one layer and unfolds nothing -- so the bound moves only
-- through the seed, which is the program's own syntax.  A charge that
-- saw the arrivals would not report the same figure twice.
charges : List ℕ
charges = descChg (obs (obs natᵗ)) (Bval 6) (progAt 6) + slotsSize sl
        ∷ descChg (obs (obs natᵗ)) (Bval 9) (progAt 9) + slotsSize sl
        ∷ Bval 6 ∷ Bval 9 ∷ []

charges≡ : charges ≡ 3 ∷ 3 ∷ 21 ∷ 24 ∷ []
charges≡ = refl

rowAt : ℕ → Bool
rowAt k = all (λ kv → boundedNode (Mval k) (proj₂ kv))
              (EvalSt.nodes (stAt k))

-- LOAD-BEARING, and it brackets the crossing rather than exhibiting
-- one side of it.  Three arrivals fewer and the claim HOLDS at the
-- very same program shape, so what fails is the arrival count and not
-- the gas, the telescope, or the arithmetic of `iterSize`.
rows : List Bool
rows = rowAt 6 ∷ rowAt 9 ∷ []

rows≡ : rows ≡ true ∷ false ∷ []
rows≡ = refl

----------------------------------------------------------------------
-- THE WITNESS.  Entered at `root` on the initial table, so nothing is
-- hand-built and no frame stands between the subscription and the
-- cell it writes.
----------------------------------------------------------------------
subscribeE-sz-store-scan-absurd : SubscribeEStoreScan → ⊥
subscribeE-sz-store-scan-absurd pr =
  f≡t (trans (sym row9≡false)
             (pr {e = e₀} sl (gasPad 512 g0) dbl seed (srcAt 9) root 0 0
                 (sched-init e₀ sl) (st-init e₀) 2 (Bval 9) (Mval 9)
                 (s≤s (s≤s z≤n)) refl ≤-refl refl refl))
  where
    row9≡false : rowAt 9 ≡ false
    row9≡false = refl

subscribeE-sz-store-absurd : SubscribeESzStore → ⊥
subscribeE-sz-store-absurd pr =
  f≡t (trans (sym row9≡false)
             (pr {e = e₀} sl (gasPad 512 g0) (progAt 9) root 0 0
                 (sched-init e₀ sl) (st-init e₀) 2 (Bval 9) (Mval 9)
                 (s≤s (s≤s z≤n)) refl ≤-refl refl refl))
  where
    row9≡false : rowAt 9 ≡ false
    row9≡false = refl
