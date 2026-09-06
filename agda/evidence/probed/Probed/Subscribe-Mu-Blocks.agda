-- ══════════════════════════════════════════════════════════════════
-- THE UNFOLDINGS THE CHARGE NOW BUYS, READ AT THE EDGE THAT KILLED
-- THE READING BEFORE IT.
--
-- TARGET: subscribeE-sz @8d93e9
--
-- WHY THIS IS THE REGION AND NOT ANOTHER.  Every other row standing
-- over this statement is at a program carrying no `μ` at all, where
-- the block count is nought and the charge reduces to the layer count
-- the predecessor was denominated in.  So the six of them are
-- evidence about a reading this one replaces, and the RATE -- one
-- block of rungs per level of nesting, bought at the bound reached so
-- far -- is a design choice nothing has instantiated.
--
-- THE ROWS.  The refutation's own family, unchanged: a `μ` whose body
-- emits ONE value, that value being a deferred subtree mentioning the
-- recursive occurrence `k` times, entered at `root` on the initial
-- table.  Beside it the same construction nested twice and then three
-- deep, each level's body naming every occurrence above it.  Each is
-- read at the SMALLEST bound the statement admits -- the program's own
-- size -- since the charge grows with the bound and a larger one would
-- be a weaker reading.
--
-- WHAT THEY FIND.  The block is what buys the multiplicity: at the
-- very mention count that refuted the predecessor, the layer-only
-- level still fails and the charge clears it, and at each further
-- level the layer count does not move while the block count does.  So
-- the crossing the refutation sits on is closed by the denomination
-- and not by the programs being small.
--
-- AND THE THIRD LEVEL IS WHERE A RATE STOPS READING LIKE A CONSTANT.
-- One block per level is bought at the bound reached so far, and the
-- bound SQUARES per level, so the first two levels are consistent with
-- a charge that is merely generous: their blocks are read at the size
-- and at its square, both small enough that a wrong rate would still
-- clear.  The third is read at the square of a square, where a block
-- that did not grow with the bound would be outrun -- and it clears at
-- the same sharpest bound, with the layer-only side still failing.
--
-- WHAT THEY DO NOT BUY.  A row instantiates one program at one bound,
-- and the question the rate answers is asymptotic: whether ONE block
-- per level covers what an unfolding delivers at EVERY bound.  These
-- stand at the sharpest bound the premise admits and clear it, so what
-- they kill is the claim that the block is UNNECESSARY and never the
-- claim that it is enough.  The nesting reached is three and the
-- mentions four; nothing here is read past a `root` entry, so the
-- telescope is one scripted slot and no door stands in the way.
-- ══════════════════════════════════════════════════════════════════
module Probed.Subscribe-Mu-Blocks where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad; hot)
open import Rx.Exp using (Ctx; Exp; Tm; Closed; Val; natᵗ; obs;
  emptyᵉ; ofᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Layer-Count using (layᵉ; muDepthᵉ)
open import Rx.Evaluator using (root; st-init; sched-init; subscribeE;
  splitBurst; iterSize)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; descChg; subscribeE-sz)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE FAMILY.  The `defer` is what the guard demands and what keeps
-- the emission ONE value carrying every copy, rather than `k` values
-- a reading over the list would join away.
----------------------------------------------------------------------
Γ : Ctx 1
Γ = natᵗ ∷ⱽ []ⱽ

sl : Slots Γ
sl fzero = scripted (hot [])

musO : (j : ℕ) → List (Tm Γ [] (obs natᵗ ∷ []) [] (obs natᵗ))
musO zero    = []
musO (suc j) = strmᵗ (mergeAllᵉ nothing (varᵉ (here refl))) ∷ musO j

bigAt : (k : ℕ) → Exp Γ [] (obs natᵗ ∷ []) [] natᵗ
bigAt k = mergeAllᵉ nothing (ofᵉ (musO k))

oAt : (k : ℕ) → Closed Γ (obs natᵗ)
oAt k = μᵉ (ofᵉ (strmᵗ (deferᵉ (bigAt k)) ∷ []))

----------------------------------------------------------------------
-- THE SAME CONSTRUCTION NESTED TWICE, which is the shape the block
-- count exists for: the inner subtree mentions BOTH recursive
-- occurrences, so an unfolding of either plants a copy the other
-- still names.
----------------------------------------------------------------------
musT : (j : ℕ) → List (Tm Γ [] (obs natᵗ ∷ obs natᵗ ∷ []) [] (obs natᵗ))
musT zero    = []
musT (suc j) = strmᵗ (mergeAllᵉ nothing (varᵉ (here refl)))
             ∷ strmᵗ (mergeAllᵉ nothing (varᵉ (there (here refl))))
             ∷ musT j

bigTwo : (k : ℕ) → Exp Γ [] (obs natᵗ ∷ obs natᵗ ∷ []) [] natᵗ
bigTwo k = mergeAllᵉ nothing (ofᵉ (musT k))

oTwo : (k : ℕ) → Closed Γ (obs natᵗ)
oTwo k = μᵉ (μᵉ (ofᵉ (strmᵗ (deferᵉ (bigTwo k)) ∷ [])))

----------------------------------------------------------------------
-- AND THE SAME NESTED THREE DEEP, which is where the rate is bought
-- at a bound already squared twice.  The innermost subtree mentions
-- all THREE occurrences, so an unfolding at any level plants a copy
-- the other two still name.
----------------------------------------------------------------------
musR : (j : ℕ) → List (Tm Γ [] (obs natᵗ ∷ obs natᵗ ∷ obs natᵗ ∷ []) [] (obs natᵗ))
musR zero    = []
musR (suc j) = strmᵗ (mergeAllᵉ nothing (varᵉ (here refl)))
             ∷ strmᵗ (mergeAllᵉ nothing (varᵉ (there (here refl))))
             ∷ strmᵗ (mergeAllᵉ nothing (varᵉ (there (there (here refl)))))
             ∷ musR j

bigThree : (k : ℕ) → Exp Γ [] (obs natᵗ ∷ obs natᵗ ∷ obs natᵗ ∷ []) [] natᵗ
bigThree k = mergeAllᵉ nothing (ofᵉ (musR k))

oThree : (k : ℕ) → Closed Γ (obs natᵗ)
oThree k = μᵉ (μᵉ (μᵉ (ofᵉ (strmᵗ (deferᵉ (bigThree k)) ∷ []))))

e₀ : Closed Γ (obs natᵗ)
e₀ = emptyᵉ

outOf : Closed Γ (obs natᵗ) → List (Val Γ (obs natᵗ))
outOf o = proj₁ (splitBurst {A = Val Γ (obs natᵗ)}
            (proj₁ (subscribeE (gasPad 64 g0) o root 0 0
                      (sched-init e₀ sl) (st-init e₀))))

----------------------------------------------------------------------
-- THE FIGURES, at the smallest bound the statement admits.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the denomination's whole content in six numbers.
-- The layer count is ZERO at every one of these programs -- a defer
-- cuts it and a `μ` added nothing to it -- so a charge that had not
-- moved would report the same figure three times.  It moves with the
-- NESTING and not with the mentions, which is what a block per level
-- means.
figures : List ℕ
figures = layᵉ (oAt 4) ∷ muDepthᵉ (oAt 4)
        ∷ descChg (obs (obs natᵗ)) (sizeᵉ (oAt 4)) (oAt 4)
        ∷ layᵉ (oTwo 2) ∷ muDepthᵉ (oTwo 2)
        ∷ descChg (obs (obs natᵗ)) (sizeᵉ (oTwo 2)) (oTwo 2)
        ∷ []

figures≡ : figures ≡ 0 ∷ 1 ∷ 5 ∷ 0 ∷ 2 ∷ 14 ∷ []
figures≡ = refl

-- LOAD-BEARING: the runs DELIVER, and each delivers ONE value.  An
-- empty burst would make the conclusion hold on nothing, and separate
-- emissions would be joined rather than carried in one value.
delivered : List ℕ
delivered = length (outOf (oAt 4)) ∷ length (outOf (oTwo 2)) ∷ []

delivered≡ : delivered ≡ 1 ∷ 1 ∷ []
delivered≡ = refl

-- LOAD-BEARING: the third level's own three numbers, read the same
-- way.  The layer count is nought here too, so a charge that read
-- only the layers would report the same figure it reports two levels
-- up, and the block count is the whole of what separates them.
thirdFigures : List ℕ
thirdFigures = layᵉ (oThree 1) ∷ muDepthᵉ (oThree 1)
             ∷ descChg (obs (obs natᵗ)) (sizeᵉ (oThree 1)) (oThree 1)
             ∷ length (outOf (oThree 1))
             ∷ []

thirdFigures≡ : thirdFigures ≡ 0 ∷ 3 ∷ 31 ∷ 1 ∷ []
thirdFigures≡ = refl

----------------------------------------------------------------------
-- THE CROSSING, read at both denominations over one program.
----------------------------------------------------------------------

-- LOAD-BEARING, and it is the whole finding: the first row is the
-- level the predecessor was stated at, at the very mention count that
-- refuted it, and the second is the same reading with the block
-- added.  A charge the block did not buy would repeat the first.
crossRows : List Bool
crossRows = valsSz? {Γ = Γ} {s = obs natᵗ}
              (iterSize 2 (layᵉ (oAt 4) + slotsSize sl) (sizeᵉ (oAt 4)))
              (outOf (oAt 4))
          ∷ valsSz? {Γ = Γ} {s = obs natᵗ}
              (iterSize 2 (descChg (obs (obs natᵗ)) (sizeᵉ (oAt 4)) (oAt 4)
                             + slotsSize sl) (sizeᵉ (oAt 4)))
              (outOf (oAt 4))
          ∷ []

crossRows≡ : crossRows ≡ false ∷ true ∷ []
crossRows≡ = refl

-- LOAD-BEARING the same way one level deeper, where the layer count
-- is still nought and the second block is the only thing between the
-- two readings.
deepRows : List Bool
deepRows = valsSz? {Γ = Γ} {s = obs natᵗ}
             (iterSize 2 (layᵉ (oTwo 2) + slotsSize sl) (sizeᵉ (oTwo 2)))
             (outOf (oTwo 2))
         ∷ valsSz? {Γ = Γ} {s = obs natᵗ}
             (iterSize 2 (descChg (obs (obs natᵗ)) (sizeᵉ (oTwo 2)) (oTwo 2)
                            + slotsSize sl) (sizeᵉ (oTwo 2)))
             (outOf (oTwo 2))
         ∷ []

deepRows≡ : deepRows ≡ false ∷ true ∷ []
deepRows≡ = refl

-- LOAD-BEARING at the level the rate is actually a rate: three blocks
-- are read at bounds squared twice over, and the layer-only side still
-- fails while the charged side clears.  A rate that covered the first
-- squaring by luck rather than by accounting would run out here, since
-- the third block is bought against a bound the first two already
-- squared and nothing else between the two readings has moved.
thirdRows : List Bool
thirdRows = valsSz? {Γ = Γ} {s = obs natᵗ}
              (iterSize 2 (layᵉ (oThree 1) + slotsSize sl) (sizeᵉ (oThree 1)))
              (outOf (oThree 1))
          ∷ valsSz? {Γ = Γ} {s = obs natᵗ}
              (iterSize 2 (descChg (obs (obs natᵗ)) (sizeᵉ (oThree 1)) (oThree 1)
                             + slotsSize sl) (sizeᵉ (oThree 1)))
              (outOf (oThree 1))
          ∷ []

thirdRows≡ : thirdRows ≡ false ∷ true ∷ []
thirdRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so
-- a restatement moves the row rather than leaving the rungs above
-- copied out beside a claim.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the same bound the rows are, which is the
-- smallest the premise admits, so a charge the delivered syntax
-- outran would fail it exactly as the layer-only reading beside it
-- does.
tieMu : Confirms
  (subscribeE-sz {e = e₀} (gasPad 64 g0) (oAt 4) root 0 0
     (sched-init e₀ sl) (st-init e₀) 2 (sizeᵉ (oAt 4)))
tieMu = λ _ _ → refl

tieNest : Confirms
  (subscribeE-sz {e = e₀} (gasPad 64 g0) (oTwo 2) root 0 0
     (sched-init e₀ sl) (st-init e₀) 2 (sizeᵉ (oTwo 2)))
tieNest = λ _ _ → refl

tieThird : Confirms
  (subscribeE-sz {e = e₀} (gasPad 64 g0) (oThree 1) root 0 0
     (sched-init e₀ sl) (st-init e₀) 2 (sizeᵉ (oThree 1)))
tieThird = λ _ _ → refl
