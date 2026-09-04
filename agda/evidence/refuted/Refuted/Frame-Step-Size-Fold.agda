-- ══════════════════════════════════════════════════════════════════
-- THE STORE-CONDITIONED FRAME SIZE STEP IS STILL FALSE, because a
-- scan frame's accumulator can grow once per arriving value while
-- one level buys a single `sizeStep` factor.
--
-- WHAT THE STATEMENT CLAIMED.  `Frame-Step-Size-Store` showed that
-- the unconditioned size step fails because a scan-f emits its stored
-- accumulator, which the premise does not see.  The natural repair is
-- to add a store premise bounding every node at `iterSize S j S`, the
-- same level as the arriving values.  This file refutes that repaired
-- statement: the store premise holds on the seed accumulator, but the
-- fold compounds it once per value while the level ceiling is fixed,
-- so a burst of sufficient length drives an emitted accumulator past
-- `iterSize S (suc j) S`.
--
-- WHERE IT BREAKS.  `scanVals` threads: it applies the step function
-- to the PREVIOUS output and re-emits it as the next output.  With
-- `deepen` (from `Scan-Fold-Burst`, size axis rather than nest axis)
-- each fold wraps the accumulator expression in one more layer of
-- `mergeAllᵉ (ofᵉ [fstᵗ (pairᵗ (strmᵗ …) (nat̂ 0))])`, adding 7
-- to `sizeᵉ` per value regardless of the burst length, while one
-- level buys `sizeStep 6 6 = 78` total.  Eleven values suffice: the
-- seed has `sizeᵉ = 3`, the eleventh emitted accumulator has
-- `sizeᵉ = 80 > 78 = iterSize 6 1 6`.
--
-- WHAT DIES AND WHAT DOES NOT.  The store-conditioned repair dies,
-- and with it the last reading under which one level pays for a scan.
-- A count carrying the BURST LENGTH is untouched here, and so is every
-- other arm: the rows fire at a `scan-f` and nowhere else, which is
-- what makes them evidence for a split by frame kind rather than
-- against the charge as such.  The dynamics are correct -- after
-- eleven folds the accumulator really does measure 80.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Frame-Step-Size-Fold where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Exp using
  (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; sizeᵗ; sizeᵉ;
   ofᵉ; mergeAllᵉ; nat̂; varᵗ; fstᵗ; strmᵗ)
open import Rx.Prim using (Gas; g0; Tick; Id)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using
  (Sched; EvalSt; Frame; Path; sched-init; st-init; stepFrame;
   scan-f; root; scan-st; NodeId; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)

-- THE STORE-CONDITIONED STATEMENT — `stepFrame-sz` with the store
-- premise added at the same level as the arriving values.  This is
-- the strongest reasonable repair: bounding every node value by the
-- cap in hand.
StepFrameSzFold : Set
StepFrameSzFold = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S j : ℕ) →
  frameSz? S f ≡ true →
  all (λ kv → boundedNode (iterSize S j S) (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? (iterSize S j S) vals ≡ true →
  valsSz? (iterSize S (suc j) S)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

-- SHARED WITH `Scan-Fold-Burst`: the empty context, the step
-- function that deepens an obs-accumulator by one layer per fold,
-- and the seed accumulator.  The size axis differs from that file's
-- nest-depth axis; the construction is otherwise the same.
Γ₀ : Ctx 0
Γ₀ = []

slots₀ : Slots Γ₀
slots₀ ()

prog : Closed Γ₀ (obs natᵗ)
prog = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

acc₀ : Val Γ₀ (obs natᵗ)
acc₀ = ofᵉ (nat̂ 0 ∷ [])

nid : NodeId
nid = 0

st₀ : EvalSt prog
st₀ = record (st-init prog) { nodes = (nid , scan-st acc₀) ∷ [] }

sched₀ : Sched Γ₀
sched₀ = sched-init prog slots₀

-- ELEVEN VALUES: eleven folds add 7 × 11 = 77 to `sizeᵉ`, carrying
-- the seed (size 3) to 80, which crosses 78 = iterSize 6 1 6.
burst : List (Val Γ₀ natᵗ)
burst = replicate 11 0

-- THE FIGURES, PINNED so a repair moving either side fails here by
-- name rather than silently turning the crossing into an equality.
figuresFold : List ℕ
figuresFold = iterSize 6 0 6 ∷ iterSize 6 1 6 ∷ sizeᵗ deepen ∷ sizeᵉ acc₀ ∷ []

figuresFold≡ : figuresFold ≡ 6 ∷ 78 ∷ 6 ∷ 3 ∷ []
figuresFold≡ = refl

-- ALL THREE PREMISES hold at S = 6, j = 0.
premFrameFold : frameSz? {Γ = Γ₀} 6 (scan-f deepen nid) ≡ true
premFrameFold = refl

premStoreFold : all (λ kv → boundedNode (iterSize 6 0 6) (proj₂ kv))
                  (EvalSt.nodes st₀) ≡ true
premStoreFold = refl

premValsFold : valsSz? {Γ = Γ₀} {s = natᵗ} (iterSize 6 0 6) burst ≡ true
premValsFold = refl

-- THE CONCLUSION FAILS: the eleventh emitted accumulator has sizeᵉ 80
-- which exceeds the cap 78 = iterSize 6 1 6.
deliveredFold≡false : valsSz? {Γ = Γ₀} {s = obs natᵗ} (iterSize 6 1 6)
                        (proj₁ (stepFrame g0 0 0 (scan-f deepen nid) root burst false
                                  sched₀ st₀)) ≡ false
deliveredFold≡false = refl

stepFrame-sz-fold-absurd : StepFrameSzFold → ⊥
stepFrame-sz-fold-absurd pr =
  f≡t (trans (sym deliveredFold≡false)
             (pr g0 0 0 (scan-f deepen nid) root burst false sched₀ st₀ 6 0
                 premFrameFold premStoreFold premValsFold))
