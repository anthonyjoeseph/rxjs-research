-- ══════════════════════════════════════════════════════════════════
-- A SCAN FRAME'S CHARGE CANNOT BE A CONSTANT IN THE BURST, because the
-- frame applies its step function ONCE PER VALUE and the charge is
-- read off the step function alone.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One frame moves its node and the values it
-- hands on together, under one factor read off the frame: at a scan,
-- two to the step function's size, against the pair before it plus the
-- step function's own nesting.
--
-- WHY IT LOOKED RIGHT.  It is the repair the map arm's refutation
-- pointed at, and at a map frame it holds: `mapVals-nest` is proven,
-- because a map applies its step function to each value INDEPENDENTLY
-- and a list of results is read by `⊔`.  The scan arm reads as the same
-- statement with a node attached.
--
-- WHERE IT BREAKS.  A scan THREADS: each output is the step function
-- applied to the PREVIOUS output, so a burst of k values applies it k
-- times in sequence and whatever the function adds to its accumulator
-- accrues k times.  The frame's charge cannot see k -- neither `sizeᵗ`
-- nor `nestDᵗ` of the step function mentions the burst -- so the two
-- sides move on different axes and no constant closes the gap.
--
-- THE WITNESS is the smallest step function that deepens its own
-- accumulator: it re-emits the accumulator inside one `mergeAllᵉ`, so
-- one fold adds exactly one layer and k folds add k.  Its size is 6, so
-- the charge is 64 whatever the burst is, and 65 values are over it.
-- The payloads are naturals and weigh nothing, which is the point: the
-- growth is the FOLD's and not the burst's own nesting.
--
-- WHAT DIES AND WHAT DOES NOT.  The scan arm's constant factor dies,
-- and the per-frame charge above it with it, since that charge is a
-- real body whose scan arm IS this leaf -- so the same witness refutes
-- the parent, which is the more expensive half.  The dynamics are
-- untouched: the accumulator really is 65 layers deep after 65 folds.
-- What is refuted is a MEASURE that prices a frame without reference to
-- how many times the frame fires, and the repair the numbers point at
-- is a factor carrying the burst length -- which the width face already
-- bounds -- rather than a tighter argument about the same constant.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Fold-Burst where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; replicate)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _⊔_; _*_; _^_; _+_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using
  (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; sizeᵗ;
   ofᵉ; mergeAllᵉ; nat̂; varᵗ; fstᵗ; strmᵗ)
open import Rx.Nest-Depth using (nestDᵗ)
open import Rx.Prim using (g0)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using
  (Sched; EvalSt; sched-init; st-init; stepFrame; scan-f; root;
   scan-st; NodeId)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)

Γ₀ : Ctx 0
Γ₀ = []

slots₀ : Slots Γ₀
slots₀ ()

prog : Closed Γ₀ (obs natᵗ)
prog = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

-- the step function re-emits its own accumulator one layer down: one
-- fold, one layer, and nothing else moves
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

burst : List (Val Γ₀ natᵗ)
burst = replicate 65 0

row : ℕ × ℕ
row = let r = stepFrame g0 0 0 (scan-f deepen nid) root burst false sched₀ st₀
      in (nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ {u = obs natᵗ} (proj₁ r))
       , 2 ^ sizeᵗ deepen * ((nodesMax st₀ ⊔ nestDᵛˢ {Γ = Γ₀} {u = natᵗ} burst) + nestDᵗ deepen)

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
fold≡65 : proj₁ row ≡ 65
fold≡65 = refl

charge≡64 : proj₂ row ≡ 64
charge≡64 = refl

scan-fold-burst-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `65 ≤ᵇ 64` reduces to `false`, so `T` of it IS the empty type
scan-fold-burst-absurd h = ≤⇒≤ᵇ h
