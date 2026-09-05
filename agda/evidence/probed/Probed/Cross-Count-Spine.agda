-- ══════════════════════════════════════════════════════════════════
-- THE SPINE A FRAME MANUFACTURES, which is the property the crossing
-- arm's repair turns on and which no row had instantiated.  A count of
-- the arrival's operators is worth having only if the walk cannot
-- inflate it; otherwise it climbs with the level exactly as the size
-- reading it replaces does, and the repair buys nothing.

-- WHERE THE INFLATION COMES FROM, AND IT IS ONE CLAUSE.  A count that
-- charges a map or a scan its FUNCTION'S SYNTAX is reading a quantity
-- substitution grows: applying a frame's closed function reifies the
-- arriving value into the term, so a function that names its argument
-- inside a `strmᵗ` hands back an observable whose syntax carries the
-- whole datum.  The frame is fixed, the program is fixed, and the
-- count is not.

-- THE TWO CANDIDATES.  `opsV` charges a function's `sizeᵗ`.  `layV` is
-- `src`'s own `layᵛ`, which charges operator LAYERS only -- one per
-- map, take, scan or `*All`, joined by MAX wherever a payload branches
-- -- so a reified datum contributes nothing to it however large, and
-- the count of an observable is bounded by the syntax of the program
-- that wrote it.  The rows are taken against that definition rather
-- than a copy of it, so a restatement of the measure moves them.

-- FORK: subscribeE-sz-store-scan

-- THE ROWS.  A `map-f` frame is run on a data arrival whose two counts
-- are both nothing, and what it emits reads four thousand and
-- ninety-five under the syntax charge against one under the layer
-- charge.  That is the inflation, exhibited rather than argued: one
-- frame, from a program of fixed size, takes the syntax reading from
-- the floor to the arrival's own size, which is the climb the whole
-- repair exists to remove.  And the layer reading does not pay for its
-- immunity: at the duplication chain, where the emission is genuinely
-- exponential and one rung is refuted, it charges twelve where the
-- syntax reading charges thirty-six, and the emission still fits.

-- WHAT THE ROWS DO NOT BUY.  They separate the two readings at a
-- `map-f` frame; the crossing arms are not run here at all, so nothing
-- says the layer count is what those arms should charge -- only that
-- the syntax count cannot be, since a level-free charge is the whole
-- of what the repair claims.  Nothing about `μᵉ`, whose unfolding
-- writes operator layers no static count of the arrival can see;
-- nothing about a scan's width, which is the residue the neighbouring
-- fork already names; and nothing about the store conclusion this fork
-- names, which no row here runs -- what reaches it is the SEPARATION,
-- the count being one object across both halves of the arm.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Count-Spine where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Val; Closed; Fn; obs; ofᵉ; emptyᵉ; mapᵉ; varᵗ;
  nat̂; strmᵗ)
open import Rx.Layer-Count using (layᵛ)
open import Rx.Evaluator using (EvalSt; root; map-f; stepFrame; sched-init;
  st-init; iterSize)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Refuted.Frame-Step-Size-Cross using (Γ₁; sl₁; Pow; chain)
open import Probed.Cross-Count-Fork using (pow; bigObs; out₂)
open import Probed.Cross-Count-Data using (opsᵛ; opsV)
open import Probed.Apparatus using (Separates; separates-at)

-- The layer reading at the one type this file's frame emits, so the
-- separation below is between two functions of the same argument.
layV : Val Γ₁ (obs (Pow 11)) → ℕ
layV v = layᵛ (obs (Pow 11)) v

----------------------------------------------------------------------
-- THE INFLATING FRAME.  A closed function of fixed size whose body
-- names its argument inside a map's function position, so the closure
-- writes the whole arriving datum into an operator's syntax.
----------------------------------------------------------------------
inflate : Fn Γ₁ [] [] [] (Pow 11) (obs (Pow 11))
inflate = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (nat̂ 0 ∷ [])))

eI : Closed Γ₁ (obs (Pow 11))
eI = emptyᵉ

stI : EvalSt eI
stI = st-init eI

valsI : List (Val Γ₁ (Pow 11))
valsI = pow 11 ∷ []

outI : List (Val Γ₁ (obs (Pow 11)))
outI = proj₁ (stepFrame {e = eI} (gasPad 8 g0) 0 0
                (map-f inflate) root valsI false
                (sched-init eI sl₁) stI)

-- The emission is read from what the frame RETURNED; a state or a
-- value written out by hand would be evidence the walk cannot reach.
hd : List (Val Γ₁ (obs (Pow 11))) → Val Γ₁ (obs (Pow 11))
hd []      = emptyᵉ
hd (v ∷ _) = v

emitted : Val Γ₁ (obs (Pow 11))
emitted = hd outI

-- LOAD-BEARING, and it is this file's product: the two readings part
-- on a value one frame manufactured.  `apart` cannot be written where
-- a frame's own function is unable to grow the count.
separates : Separates opsV layV
separates = separates-at emitted (λ ())

-- LOAD-BEARING: the arrival is DATA, so both readings start at the
-- floor and the row below is a gain rather than a difference carried
-- in.  It fails for any reading that descends into a payload.
arrivalCounts : List ℕ
arrivalCounts = opsᵛ {Γ = Γ₁} (Pow 11) (pow 11)
                  ∷ layᵛ {Γ = Γ₁} (Pow 11) (pow 11) ∷ []

arrivalCounts≡ : arrivalCounts ≡ 0 ∷ 0 ∷ []
arrivalCounts≡ = refl

-- LOAD-BEARING: this is the inflation itself.  The syntax reading
-- lands on the arrival's own size, which is the store bound the walk
-- climbs; the layer reading lands on the program's one map.  A row that
-- could not have failed would show the two moving together.
emitCounts : List ℕ
emitCounts = opsV emitted ∷ layV emitted ∷ []

emitCounts≡ : emitCounts ≡ 4095 ∷ 1 ∷ []
emitCounts≡ = refl

----------------------------------------------------------------------
-- AND THE LAYER READING STILL COVERS, at the shape where a count that
-- is too small is refuted.  Twelve rungs against the syntax reading's
-- thirty-six, on the same emission.
----------------------------------------------------------------------
layChain : ℕ
layChain = layᵛ (obs (Pow 12)) (chain 12)

layChain≡ : layChain ≡ 12
layChain≡ = refl

-- LOAD-BEARING: eight thousand one hundred and ninety-one against the
-- cap this count buys.  One rung loses here, which is the row
-- `Refuted.Frame-Step-Size-Cross` owns.
layRow₂ : valsSz? {Γ = Γ₁} {s = Pow 12}
            (iterSize 51 layChain 51) out₂ ≡ true
layRow₂ = refl

-- LOAD-BEARING jointly with the neighbouring fork's reified row: the
-- two readings AGREE at the shape whose coverage that file already
-- checked, so nothing is lost there by charging layers instead.
layBig≡ : layV bigObs ≡ opsV bigObs
layBig≡ = refl
