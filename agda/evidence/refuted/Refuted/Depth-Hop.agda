-- THE DEPTH MIRROR IS NOT TRUE FOR EVERY REFOLD BOUND.
--
-- `depth-hop` (Depth-Compositional) bounds `depthE` by
-- `hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ`.  Stated
-- with `V` universally quantified it is FALSE, and the reason is
-- structural rather than incidental: `hopDᵉ`'s scan clause is
-- `(2 + pmᵗ V 0 f) ^ V * (…)`, an EXPONENTIAL IN `V`, so at `V = 0` the
-- factor is 1 and a scan is charged its step, seed and source and
-- nothing for refolding at all.  A program whose depth comes from
-- refolding then outruns the bound.
--
-- WHICH IS WHY THE STATEMENT CARRIES `2 ≤ V` AND `sizeᵉ b ≤ V`.  That
-- is a RESTATEMENT and this file is its justification: the
-- unconditional form is refuted, so the conditioned form replaces a
-- false statement rather than weakening a true one.
--
-- ⚠ WHAT THIS FILE PINS IS THAT *SOME* CONDITION ON `V` IS NEEDED, NOT
-- THAT THESE TWO ARE THE WEAKEST ONES.  It kills `V = 0` and says
-- nothing against `V = 1`, which was MEASURED to hold on this same
-- program (the green row is in `Probed.Depth-Hop`, and it holds there
-- with no margin at all).  So do not read the pair as tight: it is the
-- shape every other hop consumer in this tree already uses —
-- `thruOuter-face-core-go` takes `2 ≤ C` with `sizeᵉ o ≤ C`, and
-- `subscribeE-wet-via-caps` reads `hopDᵉ Ŝ (slotHop Ŝ sl) b` at
-- `Ŝ = sizeCapAt e sl (suc id)`, where `2≤sizeCapAt` and
-- `size≤sizeCapAt` are both proven.
--
-- THE WITNESS IS THE CHEAPEST ONE IN THE FAMILY, and it is cheap for a
-- reason worth stating: its widening lives in a LITERAL LIST, which
-- `hopDᵉ` charges 0 for at every `V` (`hopDᵗ (nat̂ _) = 0`).  So
-- widening the map's source from three literals to seven leaves the hop
-- depth EXACTLY WHERE IT WAS while doubling `depthE` to 8.  Only the
-- refold factor `(2 + pmᵗ V 0 f) ^ V` can pay for that program, and at
-- `V = 0` that factor is 1 — the scan is charged its step, its seed and
-- its source, and nothing for refolding.  Twenty units of gas and a
-- program of constant size settle it; no quadratic gadget is needed.
module Refuted.Depth-Hop where

open import Data.Empty using (⊥)
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_)

open import Rx.Prim using (Gas; g0; gs; Id; Tick)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ; fstᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; sched-init; st-init)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Decide using (≤ᵇ-true)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (pathNestD)

gN : ℕ → Gas
gN zero    = g0
gN (suc n) = gs (gN n)

Γ₀ : Ctx 0
Γ₀ = []ⱽ

slots₀ : Slots Γ₀
slots₀ ()

gA : Fn Γ₀ [] [] (obs natᵗ ∷ []) (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
gA = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

fA : Fn Γ₀ [] [] [] (obs natᵗ) (obs (obs natᵗ))
fA = strmᵗ (scanᵉ gA (strmᵗ emptyᵉ) (mergeAllᵉ (ofᵉ (varᵗ (here refl) ∷ []))))

progB : Closed Γ₀ natᵗ
progB = mergeAllᵉ (mergeAllᵉ (mapᵉ fA
          (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ nat̂ 5 ∷ nat̂ 6 ∷ [])) ∷ []))))

schedB : Sched Γ₀
schedB = sched-init progB slots₀

stB : EvalSt progB
stB = st-init progB

theDepth : depthE (gN 20) progB root 0 0 schedB stB ≡ 8
theDepth = refl

-- THE ROW, stated as a DIRECTION rather than a pair of values: the
-- refutation needs only that the comparison comes out `false`, so it
-- does not have to be re-read every time either side's arithmetic
-- moves.
theRow : (depthE (gN 20) progB root 0 0 schedB stB
           ≤ᵇ hopDᵉ 0 (slotHop 0 slots₀) progB
               + pathNestD (root {Γ = Γ₀} {t = natᵗ}))
         ≡ false
theRow = refl

-- and the statement itself, taken as a hypothesis, so this file says
-- the STATEMENT is false rather than reporting on whatever `src`
-- currently proves it through
depth-hop-∀V-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
     (V : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (bid : Id) (now : Tick)
     (sched : Sched Γ) (st : EvalSt e) →
     depthE g b κ bid now sched st
       ≤ hopDᵉ V (slotHop V (Sched.slots sched)) b + pathNestD κ) → ⊥
depth-hop-∀V-absurd h =
  bad (trans (sym (≤ᵇ-true _ _ (h 0 (gN 20) progB root 0 0 schedB stB))) theRow)
  where
  bad : true ≡ false → ⊥
  bad ()
