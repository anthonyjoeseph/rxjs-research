-- ══════════════════════════════════════════════════════════════════
-- THE `μ` A SOURCE HANDS OUT RATHER THAN RUNS, WHICH IS THE POSITION
-- THE BLOCK COUNT USED TO READ AS NOUGHT.
--
-- TARGET: pushBurst-sz-store-outer @911df7
--
-- WHY THIS POINT AND NOT THE ONE THE OTHER ROW STANDS AT.  This leaf's
-- level is denominated in the program it FOLDS, and a crossing door
-- re-subscribes what that program emitted -- so a `μ` reachable only
-- through an emission is charged here or nowhere.  The `ofᵉ` position
-- is where those emissions are written, and the count that reads it as
-- zero fixes the rung count before the multiplicity is chosen, which
-- is the crossing the refutation beside this receipt sits on.
--
-- THE ROWS.  The refutation's own family, imported rather than rebuilt:
-- a one-shot source whose single emission is a `μ` whose body mentions
-- its recursive occurrence `k` times under one defer, folded back
-- through a merging door with no room, entered at the table and the
-- schedule that subscription left.  Beside it the SAME reading with the
-- block count forced to nought, which is what the position returning
-- zero gives and is the only difference between the two.
--
-- WHAT THEY FIND.  The block is what closes it.  Forced to nought the
-- conclusion fails at the refutation's own mention count and holds one
-- mention below it, so the bracket is the multiplicity and not the
-- door, the gas or the arithmetic; read at the count as it now stands
-- the same table clears, and clears again at three times the mentions,
-- where the copies are an order of magnitude more syntax.
--
-- WHAT THEY DO NOT BUY.  One nesting level, one door, one telescope of
-- a single scripted slot, and two mention counts -- so nothing about a
-- `μ` handed out from INSIDE another one, where the levels compose,
-- and nothing about an emission the telescope manufactures, where the
-- layer count is nought and the rungs are bought by `slotsSize` alone.
-- The rate stays asymptotic: these clear at the smallest bound the
-- premise admits and say nothing about every bound.
-- ══════════════════════════════════════════════════════════════════
module Probed.Burst-Mu-Door where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (sizeᵉ)
open import Rx.Slots using (slotsSize)
open import Rx.Layer-Count using (layᵉ; muDepthᵉ)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (muRungsᴺ; pushBurst-sz-store-outer)
open import Refuted.Burst-Mu-Square
  using (sl; srcAt; e₀; st₀; sched₀; subAt; afterAt)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE FIGURES.
----------------------------------------------------------------------

-- LOAD-BEARING: it is the repair in five numbers.  The nesting is ONE
-- where the position returning zero reported none, and the block it
-- buys is the BIT LENGTH of the whole program's own size -- against a
-- layer count that stands at one however many copies the unfolding
-- plants.
figures : List ℕ
figures = muDepthᵉ (srcAt 66) ∷ layᵉ (srcAt 66) ∷ sizeᵉ (srcAt 66)
        ∷ muRungsᴺ (muDepthᵉ (srcAt 66)) (sizeᵉ (srcAt 66))
        ∷ slotsSize sl ∷ []

figures≡ : figures ≡ 1 ∷ 1 ∷ 144 ∷ 8 ∷ 1 ∷ []
figures≡ = refl

-- LOAD-BEARING: the fold has something to push and pushing it WRITES.
-- An empty burst would make the crossing the identity and every row
-- below a reading of the subscription instead.
liveness : List ℕ
liveness = length (proj₁ (subAt 66))
         ∷ length (EvalSt.nodes (proj₂ (proj₂ (subAt 66))))
         ∷ length (EvalSt.nodes (afterAt 66)) ∷ []

liveness≡ : liveness ≡ 1 ∷ 1 ∷ 2 ∷ []
liveness≡ = refl

----------------------------------------------------------------------
-- THE CROSSING, read with the block count forced to nought and then as
-- the statement now reads it.
----------------------------------------------------------------------
Mblind : ℕ → ℕ
Mblind k = iterSize 2 (muRungsᴺ 0 (sizeᵉ (srcAt k))
                       + suc (layᵉ (srcAt k)) + slotsSize sl)
                   (sizeᵉ (srcAt k))

blindRow : ℕ → Bool
blindRow k = all (λ kv → boundedNode (Mblind k) (proj₂ kv))
                 (EvalSt.nodes (afterAt k))

-- LOAD-BEARING, and it brackets rather than exhibiting one side: one
-- mention fewer and the same reading HOLDS at the same rungs, so what
-- fails at sixty-six is the multiplicity alone.
blindRows : List Bool
blindRows = blindRow 65 ∷ blindRow 66 ∷ []

blindRows≡ : blindRows ≡ true ∷ false ∷ []
blindRows≡ = refl

Mnow : ℕ → ℕ
Mnow k = iterSize 2 (muRungsᴺ (muDepthᵉ (srcAt k)) (sizeᵉ (srcAt k))
                     + suc (layᵉ (srcAt k)) + slotsSize sl)
                 (sizeᵉ (srcAt k))

nowRow : ℕ → Bool
nowRow k = all (λ kv → boundedNode (Mnow k) (proj₂ kv))
               (EvalSt.nodes (afterAt k))

-- LOAD-BEARING: the second reads three times the mentions, where the
-- unfolding is an order of magnitude more syntax and the bound the
-- block is bought at has only trebled.  A block that merely outran one
-- witness would show here.
nowRows : List Bool
nowRows = nowRow 66 ∷ nowRow 200 ∷ []

nowRows≡ : nowRows ≡ true ∷ true ∷ []
nowRows≡ = refl

-- LOAD-BEARING: the table premise at the level the rows are read at,
-- spelled out so the witness cannot be read as one that merely fails
-- to satisfy it.
premNow : all (λ kv → boundedNode (Mnow 66) (proj₂ kv))
              (EvalSt.nodes (proj₂ (proj₂ (subAt 66)))) ≡ true
premNow = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement moves the row rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the same level the rows are, at the smallest
-- bound the premise admits, so a charge the unfolding outran would fail
-- it exactly as the blinded reading beside it does.
tieDoorMu : Confirms
  (pushBurst-sz-store-outer {e = e₀} sl (gasPad 64 g0) mergeAllᵒ 0
     (srcAt 66) root 0 0 sched₀ st₀ (subAt 66) 2 (sizeᵉ (srcAt 66))
     (Mnow 66))
tieDoorMu = λ _ _ _ _ _ _ → refl
