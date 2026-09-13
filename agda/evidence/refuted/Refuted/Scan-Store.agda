-- A SCAN'S OUTPUTS ARE ITS STORE, SO THEY ARE NOT BOUNDED BY WHAT THE
-- FRAME WAS HANDED.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- `stepFrame` at a `scan-f` returns the successive ACCUMULATORS, each
-- the step applied to the one before it — so what it hands back is a
-- function of the STORE and the step, and the payload enters only as
-- the step's second argument.  A step that ignores that argument cuts
-- the payload out of the answer entirely, and then no bound on the
-- payload can bound the output: the frame predicate compares the two
-- against ONE number and the number is the payload's.
--
-- THE WITNESS IS THE SMALLEST STEP THAT DEEPENS.  One flattening layer
-- over a literal, with the bound pair discarded — a numeral arrives
-- reading zero against a payload bound of zero, and one accumulator
-- comes back reading one.  The store it is written into is the machine's
-- own: `installNode` at the state `st-init` returns, which is what a
-- subscribe frame does to seed a fold, so nothing here is a record
-- written by hand.
--
-- AND THE STORE CONJUNCT CANNOT FAIL ON ITS OWN, WHICH IS WHY ONE
-- WITNESS SETTLES BOTH.  The state this frame writes is the state it
-- was handed with one node replaced by the LAST of the outputs, so the
-- store half follows from the payload half and the `Rv ≤ Rst` premise.
-- The store bound is left slack here on purpose — at five against a
-- reading of one — so the row cannot be read as a store bound that was
-- merely too tight.
--
-- WHAT THIS DOES NOT KILL.  Not the frame predicate, and not the two
-- sibling leaves: a map's outputs ARE a template at the payload and a
-- take's are a prefix of it, so both genuinely hand back what they were
-- handed.  The scan is the one frame whose output is not a function of
-- its input, and it is the one whose bound has to come from somewhere
-- else.  `Probed.Fuel-Growth` exhibits the same growth under a REAL
-- drain at the same program shape, one hop per arrival, so the repair
-- is not a reachability hypothesis either — the machine mints these
-- states itself.
module Refuted.Scan-Store where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; mergeAllᵉ; strmᵗ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Frame; Path; root; scan-f; scan-st; NodeId;
  Sched; EvalSt; stepFrame; stHop; installNode; rootWitness; sched-init;
  st-init)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried using (FrameCarries)

----------------------------------------------------------------------
-- THE STATEMENT, RESTATED.  The frame predicate is IMPORTED rather than
-- spelled out: what is refuted is the scan leaf's choice of bound, not
-- the predicate, so a repair that changes the predicate must make this
-- file fail to typecheck rather than leave it quietly green.
----------------------------------------------------------------------

ScanFrameCarried : Set
ScanFrameCarried = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rv Rst : ℕ) → Rv ≤ Rst →
  FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ Rv Rv Rst

----------------------------------------------------------------------
-- THE PROGRAM AND THE SEEDED STORE.  The root term is an observable of
-- the empty observable — the smallest thing this language can run at
-- the type the chain's root demands — because nothing about the term
-- enters the statement being refuted.  What does enter is the node, and
-- it is installed exactly as a subscribe frame installs one.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

ψ₀ : Fin 0 → Rd₃
ψ₀ = slotRd ins₀

root₀ : Closed Γ₀ (obs natᵗ)
root₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

-- the seed: reads zero, so the store enters at the floor
seed : Val Γ₀ (obs natᵗ)
seed = emptyᵉ

-- THE STEP THAT DISCARDS.  Its bound pair does not occur, so the
-- output is fixed by the step alone — one flattener over a one-literal
-- source, which is the least a term of this language can read above
-- nothing.
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])))

st₀ : EvalSt root₀
st₀ = installNode 0 (scan-st {t = obs natᵗ} seed) (st-init root₀)

sd₀ : Sched Γ₀
sd₀ = sched-init root₀ ins₀

vals₀ : List (Val Γ₀ natᵗ)
vals₀ = 3 ∷ []

frame₀ : Frame Γ₀ natᵗ (obs natᵗ)
frame₀ = scan-f step 0

outs : List (Val Γ₀ (obs natᵗ))
outs = proj₁ (stepFrame (rootWitness root₀ ins₀) 0 0 frame₀ root vals₀ false
                sd₀ st₀)

----------------------------------------------------------------------
-- THE CROSSING, PINNED ON BOTH SIDES.  An inequality refutation dies
-- quietly when a repair enlarges the right side, so each figure is
-- claimed by name: the payload and the store enter at zero, and one
-- delivery comes back reading one.
----------------------------------------------------------------------

-- `Val Γ natᵗ` is `ℕ` whatever the context, so the payload cannot say
-- which one it belongs to and the measure is told
payload-is : valsHop {Γ = Γ₀} ψ₀ natᵗ vals₀ ≡ 0        -- LOAD-BEARING
payload-is = refl

store-is : stHop ψ₀ st₀ ≡ 0                            -- LOAD-BEARING
store-is = refl

out-is : valsHop ψ₀ (obs natᵗ) outs ≡ 1                -- LOAD-BEARING
out-is = refl

scan-frame-carried-false : ScanFrameCarried → ⊥
scan-frame-carried-false h
  with proj₁ (h (rootWitness root₀ ins₀) 0 0 step 0 root ψ₀ 0 5 z≤n
                vals₀ false sd₀ st₀ z≤n z≤n)
... | ()
