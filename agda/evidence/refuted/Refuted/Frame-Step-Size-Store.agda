-- ONE FRAME'S SIZE STEP READS THE NODE STORE, AND NO HYPOTHESIS OF THE
-- SIZE FACE READS THE STORE AT ALL.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- The frame law's size half prices what a frame EMITS against what
-- arrived and what the frame's own syntax costs.  That is the whole of
-- the story for `map-f`, whose emission is a substitution into the
-- values in hand.  It is not the story for `scan-f`: its emission is
-- the ACCUMULATOR, fetched out of `EvalSt.nodes`, and the frame's
-- syntax may be as small as a projection that hands the accumulator
-- straight back.  Then the emitted size is the STORED value's, which
-- neither the arriving values' reading nor the frame's reading sees --
-- the "conclusion needs information no hypothesis carries" shape, one
-- arm over from where it was first found.
--
-- THE WITNESS IS THE SMALLEST FRAME THERE IS.  `fstᵗ (varᵗ …)` has
-- `sizeᵗ` two, so it fits under every cap from two upward, and
-- `scanVals` computes `applyFn fn (acc , v)` -- the accumulator
-- unchanged.  So the cap can be made as roomy as the level allows and
-- the emission still answers with whatever the store happens to hold,
-- which the statement quantifies over with nothing said about it.
--
-- AND THE REPAIR IS NOT A NEW INVARIANT: `boundedNode` ALREADY READS
-- THIS.  The caps face carries `stBounded?`, whose store half is
-- exactly `sizeᵛ t v ≤ᵇ B` at a `scan-st`, and this witness dies
-- against it at the base cap.  What the rows do NOT settle is whether
-- the store reading is SUFFICIENT: `scanVals` folds the accumulator
-- through the whole arriving list, so a growing accumulator compounds
-- once per value while one level buys a single factor.  A first-order
-- accumulator cannot grow -- `sizeᵛ` at a first-order type is fixed by
-- the type -- so any such witness has to carry an `obs` payload, and
-- none is built here.
module Refuted.Frame-Step-Size-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; hot; Tick; Id)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; _×ᵗ_; emptyᵉ;
  varᵗ; fstᵗ; sizeᵗ; sizeᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Frame; scan-f; Path; root;
  scan-st; setNode; stepFrame; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

-- THE STATEMENT AS IT NOW READS, with the frame priced at the program's
-- cap.  That reading is what survived the level refutation; it does not
-- survive the store, because `frameSz?` at a `scan-f` reads the FUNCTION
-- and the emission is the accumulator.
StepFrameSz : Set
StepFrameSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (S j : ℕ) →
  frameSz? S f ≡ true →
  valsSz? (iterSize S j S) vals ≡ true →
  valsSz? (iterSize S (suc j) S)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

-- A TWELVE-LEAF FIRST-ORDER ACCUMULATOR, whose `sizeᵛ` is fixed by its
-- type at twenty-three -- two over the level one step from the base cap
-- three, and the cap itself is three, so nothing about the frame or the
-- arriving value is near it.
P : Ty
P = natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ
      (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ (natᵗ ×ᵗ natᵗ))))))))))

vP : Val Γ₁ P
vP = 0 , (0 , (0 , (0 , (0 , (0 , (0 , (0 , (0 , (0 , (0 , 0))))))))))

eS : Closed Γ₁ P
eS = emptyᵉ

-- the smallest frame that emits the store: hand the accumulator back
fnS : Fn Γ₁ [] [] [] (P ×ᵗ natᵗ) P
fnS = fstᵗ (varᵗ (here refl))

stS : EvalSt eS
stS = record (st-init eS) { nodes = setNode 0 (scan-st {Γ = Γ₁} {t = P} vP) [] }

valsS : List (Val Γ₁ natᵗ)
valsS = 0 ∷ []

outS : List (Val Γ₁ P)
outS = proj₁ (stepFrame {e = eS} g0 0 0 (scan-f fnS 0) root valsS false
                        (sched-init eS sl₁) stS)

-- the four figures, so the margin is on the page rather than inferred:
-- the base cap, one level up from it, the frame's own size, and what
-- the store holds.
figures : List ℕ
figures = iterSize 3 0 3 ∷ iterSize 3 1 3 ∷ sizeᵗ fnS ∷ sizeᵛ {Γ = Γ₁} P vP ∷ []

figures≡ : figures ≡ 3 ∷ 21 ∷ 2 ∷ 23 ∷ []
figures≡ = refl

-- both premises hold at the base cap three
premFrame : frameSz? {Γ = Γ₁} 3 (scan-f fnS 0) ≡ true
premFrame = refl

premVals : valsSz? {Γ = Γ₁} {s = natᵗ} (iterSize 3 0 3) valsS ≡ true
premVals = refl

-- and the conclusion fails one level up
rowS : Bool
rowS = valsSz? {Γ = Γ₁} {s = P} (iterSize 3 1 3) outS

rowS≡false : rowS ≡ false
rowS≡false = refl

stepFrame-sz-store-absurd : StepFrameSz → ⊥
stepFrame-sz-store-absurd pr =
  f≡t (trans (sym rowS≡false)
             (pr {e = eS} g0 0 0 (scan-f fnS 0) root valsS false
                 (sched-init eS sl₁) stS 3 0 premFrame premVals))

-- AND THE STORE READING THAT ALREADY EXISTS EXCLUDES THIS WITNESS, so
-- the finding names a premise rather than asking for one to be invented.
storeReading : boundedNode {Γ = Γ₁} 3 (scan-st {t = P} vP) ≡ false
storeReading = refl
