-- ══════════════════════════════════════════════════════════════════
-- AFFORDABILITY IS GRANTED UP TO A LEVEL AND A REGISTRY CHAIN CLIMBS
-- PAST IT, so pricing the hop correctly is not enough to make it true.
-- The premise says every iterate up to a ceiling is under the value
-- budget, and the walk offers only that the level it is AT is under
-- that ceiling.  Where the values go next is a chain in the registry
-- whose length is bounded by the REGISTRY reading, and nothing ties
-- that reading to the ceiling -- so a chain one frame longer than the
-- ceiling covers walks off the end of the premise.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- THE ESCAPE IS A FRAME THAT EMBEDS ITS INPUT, which the constant map
-- of the sibling witness is not.  A constant map lands at a `sizeᵛ` one
-- BELOW the `sizeᵗ` the chain's legality already paid for, so it can
-- never exceed a budget that dominates the chain; an embedding map
-- substitutes the arriving value into its own template, so it adds its
-- template's cost to whatever arrived.  That is growth per hop, and
-- legality prices the template once while the conclusion is read after
-- the hop.
--
-- SO THE TWO WITNESSES TOGETHER SAY THE SHAPE OF THE REPAIR.  Pricing
-- has to relate the two readings -- that is the first one -- and the
-- relation has to reach the level a FANNED-INTO chain arrives at, not
-- the level the walk is at when it hands the values over.  Both hold
-- at every choice of the numbers, since the ceiling here is met exactly
-- and the chain is legal exactly.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Live-Level where

open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Fn; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂;
  strmᵗ; varᵗ; input; sizeᵛ; sizeᵗ; applyFn)
open import Rx.Prim using (g0; Source)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ;
  mergeAll-st; Path; RegId; Chain; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Verify-Budget-Sufficient.Live-Nest-Walk using (DispatchLiveHyp)
open import Refuted.Demand-Programs using (Γ₂; insT)

prog : Closed Γ₂ natᵗ
prog = input fzero

slots : Slots Γ₂
slots = insT 0 0 0

-- THE TWO FRAMES.  The first only gets the values out of `natᵗ`, where
-- every value costs one however large; the second is the growth
constOne : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
constOne = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

embed : Fn Γ₂ [] [] [] (obs natᵗ) (obs natᵗ)
embed = strmᵗ (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))

-- THE REGISTERED CHAIN, legal at exactly the budget it is priced at
rpath : Path Γ₂ natᵗ natᵗ
rpath = map-f constOne ↠ (map-f embed ↠ (thru-outer mergeAllᵒ 0 ↠ root))

registry : List (RegId × Source × Chain Γ₂ natᵗ)
registry = (1 , 0 , (natᵗ , rpath)) ∷ []

st₀ : EvalSt prog
st₀ = record (st-init prog)
        { nodes    = (0 , mergeAll-st {t = natᵗ} (just 0) 0 [] false) ∷ []
        ; registry = registry }

vals : List (Val Γ₂ natᵗ)
vals = 7 ∷ []

-- THE ROWS THAT MAKE IT A CROSSING.  Each frame's template is priced
-- once by legality …
frame₁≡ : sizeᵗ {Γ = Γ₂} constOne ≡ 4
frame₁≡ = refl

frame₂≡ : sizeᵗ {Γ = Γ₂} embed ≡ 5
frame₂≡ = refl

-- … while the value it produces is read after the hop, and the second
-- frame adds its template to what arrived rather than replacing it
after₁≡ : sizeᵛ {Γ = Γ₂} (obs natᵗ) (applyFn constOne 7) ≡ 3
after₁≡ = refl

after₂≡ : sizeᵛ {Γ = Γ₂} (obs natᵗ) (applyFn embed (applyFn constOne 7)) ≡ 7
after₂≡ = refl

-- EVERY PREMISE OF THE GRANT HOLDS, at `S = U = 5`, `Lv = j = 0`.
-- Affordability is met exactly: the only iterate it covers is
-- `iterSize S 0 S`, which is `S` itself
afford : ∀ k → k ≤ 0 → iterSize 5 k 5 ≤ 5
afford zero    _  = ≤-refl
afford (suc _) ()

1≤S : 1 ≤ 5
1≤S = s≤s z≤n

hV : valsSz? {Γ = Γ₂} {s = natᵗ} (iterSize 5 0 5) vals ≡ true
hV = refl

hR : regsSz? (iterSize 5 0 5) registry ≡ true
hR = refl

j≤Lv : 0 ≤ 0
j≤Lv = z≤n

-- THE CONCLUSION, at one unit of dispatch gas -- zero would make it `⊤`
Concl : Set
Concl = DispatchLiveHyp {e = prog} g0 1 0 0 5 fzero vals false
          (sched-init prog slots) st₀

-- and it contains `valsSz? 5` of a value of size seven, which is
-- `false ≡ true`.  `proj₁` leaves the one admitted chain's
-- `PathLiveHyp`; both `map-f` arms are `⊤`; the `thru-outer` arm IS
-- the side condition
share-live-level-absurd : Concl → ⊥
share-live-level-absurd h with proj₁ (proj₂ (proj₂ (proj₁ h)))
... | ()
