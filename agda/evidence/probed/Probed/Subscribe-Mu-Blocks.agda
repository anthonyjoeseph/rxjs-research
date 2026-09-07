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
-- table.  It is read at the SMALLEST bound the statement admits --
-- the program's own size -- since the charge grows with the bound and
-- a larger one would be a weaker reading.
--
-- WHAT THEY FIND.  The block is what buys the multiplicity: at the
-- very mention count that refuted the predecessor, the layer-only
-- level still fails and the charge clears it.  So the crossing the
-- refutation sits on is closed by the denomination and not by the
-- program being small.
--
-- WHAT THEY DO NOT BUY.  A row instantiates one program at one bound,
-- and the question the rate answers is asymptotic: whether ONE block
-- per level covers what an unfolding delivers at EVERY bound.  This
-- stands at the sharpest bound the premise admits and clears it, so
-- what it kills is the claim that the block is UNNECESSARY and never
-- the claim that it is enough.  The mentions are four, nothing is
-- read past a `root` entry, so the telescope is one scripted slot and
-- no door stands in the way.
-- DEAD ROUTE: reading the RATE across levels by instantiation, at the
--   same family nested twice and three deep -- which is where a rate
--   stops reading like a constant, since each level's block is bought
--   at a bound the level below has already squared.  The charge at
--   two levels of this family is some three and a half MILLION rungs,
--   and while that figure computes in seconds the `iterSize` tower it
--   indexes does not: a rung multiplies the bound, so the table the
--   row would compare against runs to millions of digits reached one
--   multiplication at a time.  Nor is there a smaller point that both
--   computes and discriminates, since separating a block from no
--   block needs a multiplicity large enough to outrun the layer-only
--   reading.  The rate is therefore settled by the arithmetic written
--   into `descRungsᴺ`'s own header and never by a row.
-- ══════════════════════════════════════════════════════════════════
module Probed.Subscribe-Mu-Blocks where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
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

e₀ : Closed Γ (obs natᵗ)
e₀ = emptyᵉ

outOf : Closed Γ (obs natᵗ) → List (Val Γ (obs natᵗ))
outOf o = proj₁ (splitBurst {A = Val Γ (obs natᵗ)}
            (proj₁ (subscribeE (gasPad 64 g0) o root 0 0
                      (sched-init e₀ sl) (st-init e₀))))

----------------------------------------------------------------------
-- THE FIGURES, at the smallest bound the statement admits.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the denomination's whole content in three
-- numbers.  The layer count is ZERO at this program -- a defer cuts
-- it and a `μ` adds nothing to it -- so the charge beside it is
-- bought entirely by the one level of nesting, and a reading that saw
-- only the layers would report nought in its place.
figures : List ℕ
figures = layᵉ (oAt 4) ∷ muDepthᵉ (oAt 4)
        ∷ descChg (obs (obs natᵗ)) (sizeᵉ (oAt 4)) (oAt 4)
        ∷ []

figures≡ : figures ≡ 0 ∷ 1 ∷ 3705 ∷ []
figures≡ = refl

-- LOAD-BEARING: the run DELIVERS, and delivers ONE value.  An empty
-- burst would make the conclusion hold on nothing, and separate
-- emissions would be joined rather than carried in one value.
delivered : List ℕ
delivered = length (outOf (oAt 4)) ∷ []

delivered≡ : delivered ≡ 1 ∷ []
delivered≡ = refl

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
