-- ══════════════════════════════════════════════════════════════════
-- TWO NESTINGS COMPOSED, WHICH IS THE FIRST POINT WHERE THE BLOCK'S
-- RATE SAYS ANYTHING.
--
-- TARGET: pushBurst-sz-store-outer @911df7
--
-- WHY A COMPOSITION AND NOT A LARGER SINGLE LEVEL.  The count reads a
-- `μ` through an EMISSION as well as through a binder, joining the
-- terms of an `ofᵉ` by `⊔` -- so a `μ` handed out from inside another
-- one is the smallest program where that descent returns two, and it
-- is the only shape at this leaf where the second rung-group is bought
-- at all.  Every other reading of this statement stands at one nesting
-- or at none.
--
-- THE ROWS.  A one-shot source whose single emission is a `μ` whose
-- body emits a `μ` of its own, the inner body mentioning BOTH
-- recursive occurrences `k` times under one defer, folded back through
-- a merging door with no room, entered at the table and the schedule
-- that subscription left.  Beside it the same reading with the block
-- count forced to nought, and again with the count stopped at ONE
-- level, which is the composition blinded away.
--
-- WHAT THEY FIND, AND HALF OF IT IS A BOUND ON THE OTHER HALF.  The
-- block is what closes the crossing at a composed program too: forced
-- to nought the conclusion fails at a mention count where it holds one
-- mention below, so the bracket is the multiplicity and not the second
-- door the composition adds.  But the count stopped at ONE level
-- CLEARS the same row -- one group already affords the cube of the
-- bound, where a second unfolding delivers a sixteenth of it -- so
-- what the second group buys is not what closes this crossing, and no
-- mention count reaches a reading where it is.
--
-- WHAT THEY DO NOT BUY, AND IT IS STILL THE RATE.  Two nesting levels,
-- one door, one telescope of a single scripted slot -- so nothing
-- about three, where the third group is bought at a bound already
-- squared twice, and nothing about a nesting reached through the
-- TELESCOPE rather than through the program term.  The rate stays
-- asymptotic: these clear at the smallest bound the premise admits and
-- say nothing about every bound.
-- ══════════════════════════════════════════════════════════════════
module Probed.Mu-Compose where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Exp; Tm; Closed; natᵗ; obs;
  ofᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ; strmᵗ; sizeᵉ; unfoldμ)
open import Rx.Slots using (slotsSize)
open import Rx.Layer-Count using (layᵉ; muDepthᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Stream; root; _↠_;
  mergeAllᵒ; thru-outer; subscribeE; pushBurst; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (muRungsᴺ; pushBurst-sz-store-outer)
open import Refuted.Burst-Mu-Square using (Γ; sl; e₀; st₀; sched₀)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE FAMILY.  The inner body mentions BOTH occurrences, so unfolding
-- the outer `μ` plants copies that the inner unfolding then squares.
----------------------------------------------------------------------

mus² : (j : ℕ) → List (Tm Γ [] (natᵗ ∷ natᵗ ∷ []) [] (obs natᵗ))
mus² 0       = []
mus² (suc j) = strmᵗ (varᵉ (here refl))
             ∷ strmᵗ (varᵉ (there (here refl)))
             ∷ mus² j

innerAt : (k : ℕ) → Exp Γ (natᵗ ∷ natᵗ ∷ []) [] [] natᵗ
innerAt k = mergeAllᵉ (just 0)
              (ofᵉ (strmᵗ (deferᵉ (mergeAllᵉ nothing (ofᵉ (mus² k)))) ∷ []))

bodyAt² : (k : ℕ) → Exp Γ (natᵗ ∷ []) [] [] natᵗ
bodyAt² k = mergeAllᵉ (just 0) (ofᵉ (strmᵗ (μᵉ (innerAt k)) ∷ []))

srcAt² : (k : ℕ) → Closed Γ (obs natᵗ)
srcAt² k = ofᵉ (strmᵗ (μᵉ (bodyAt² k)) ∷ [])

----------------------------------------------------------------------
-- THE FIGURES.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the composition in six numbers.  The nesting is
-- TWO, and the block it buys is one logarithm of the program plus one
-- of the program SQUARED -- against a layer count that stands at the
-- two operators outside the defer, however many copies either
-- unfolding plants.
figures : List ℕ
figures = muDepthᵉ (srcAt² 8) ∷ layᵉ (srcAt² 8) ∷ sizeᵉ (srcAt² 8)
        ∷ sizeᵉ (unfoldμ (bodyAt² 8))
        ∷ muRungsᴺ (muDepthᵉ (srcAt² 8)) (sizeᵉ (srcAt² 8))
        ∷ slotsSize sl ∷ []

figures≡ : figures ≡ 2 ∷ 2 ∷ 49 ∷ 405 ∷ 18 ∷ 1 ∷ []
figures≡ = refl

----------------------------------------------------------------------
-- THE CROSSING.
----------------------------------------------------------------------

subAt² : (k : ℕ) → Stream Γ (obs natᵗ) × Sched Γ × EvalSt e₀
subAt² k = subscribeE (gasPad 64 g0) (srcAt² k)
             (thru-outer mergeAllᵒ 0 ↠ root) 0 0 sched₀ st₀

afterAt² : (k : ℕ) → EvalSt e₀
afterAt² k = proj₂ (proj₂
  (pushBurst (gasPad 64 g0) 0 0 (thru-outer mergeAllᵒ 0) root
     (proj₁ (subAt² k)) (proj₁ (proj₂ (subAt² k)))
     (proj₂ (proj₂ (subAt² k)))))

-- LOAD-BEARING: the fold has something to push and pushing it WRITES.
-- An empty burst would make the crossing the identity and every row
-- below a reading of the subscription instead.
liveness : List ℕ
liveness = length (proj₁ (subAt² 8))
         ∷ length (EvalSt.nodes (proj₂ (proj₂ (subAt² 8))))
         ∷ length (EvalSt.nodes (afterAt² 8)) ∷ []

liveness≡ : liveness ≡ 1 ∷ 1 ∷ 2 ∷ []
liveness≡ = refl

Mblind : ℕ → ℕ
Mblind k = iterSize 2 (muRungsᴺ 0 (sizeᵉ (srcAt² k))
                       + suc (layᵉ (srcAt² k)) + slotsSize sl)
                   (sizeᵉ (srcAt² k))

blindRow : ℕ → Bool
blindRow k = all (λ kv → boundedNode (Mblind k) (proj₂ kv))
                 (EvalSt.nodes (afterAt² k))

-- LOAD-BEARING, and it brackets rather than exhibiting one side: one
-- mention fewer and the same reading HOLDS at the same rungs, so what
-- fails is the multiplicity alone and not the second door the
-- composition adds.
blindRows : List Bool
blindRows = blindRow 256 ∷ blindRow 257 ∷ []

blindRows≡ : blindRows ≡ true ∷ false ∷ []
blindRows≡ = refl

Mone : ℕ → ℕ
Mone k = iterSize 2 (muRungsᴺ 1 (sizeᵉ (srcAt² k))
                     + suc (layᵉ (srcAt² k)) + slotsSize sl)
                 (sizeᵉ (srcAt² k))

oneRow : ℕ → Bool
oneRow k = all (λ kv → boundedNode (Mone k) (proj₂ kv))
               (EvalSt.nodes (afterAt² k))

Mnow : ℕ → ℕ
Mnow k = iterSize 2 (muRungsᴺ (muDepthᵉ (srcAt² k)) (sizeᵉ (srcAt² k))
                     + suc (layᵉ (srcAt² k)) + slotsSize sl)
                 (sizeᵉ (srcAt² k))

nowRow : ℕ → Bool
nowRow k = all (λ kv → boundedNode (Mnow k) (proj₂ kv))
               (EvalSt.nodes (afterAt² k))

-- LOAD-BEARING, and what it reports is a BOUND on the rows above
-- rather than a second crossing: the first reads the count stopped at
-- ONE level, which is the composition blinded away, and it CLEARS at
-- the very mention count the block-blinded reading fails at.  A block
-- the second level had been needed for would fail here.
rateRows : List Bool
rateRows = oneRow 257 ∷ nowRow 257 ∷ []

rateRows≡ : rateRows ≡ true ∷ true ∷ []
rateRows≡ = refl

-- LOAD-BEARING: the table premise at the level the rows are read at,
-- spelled out so the witness cannot be read as one that merely fails
-- to satisfy it.
premNow : all (λ kv → boundedNode (Mnow 257) (proj₂ kv))
              (EvalSt.nodes (proj₂ (proj₂ (subAt² 257)))) ≡ true
premNow = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement moves the row rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the same level the rows are, at the smallest
-- bound the premise admits, so a charge the unfolding outran would
-- fail it exactly as the blinded reading beside it does.
tieCompose : Confirms
  (pushBurst-sz-store-outer {e = e₀} sl (gasPad 64 g0) mergeAllᵒ 0
     (srcAt² 257) root 0 0 sched₀ st₀ (subAt² 257) 2
     (sizeᵉ (srcAt² 257)) (Mnow 257))
tieCompose = λ _ _ _ _ _ _ → refl
