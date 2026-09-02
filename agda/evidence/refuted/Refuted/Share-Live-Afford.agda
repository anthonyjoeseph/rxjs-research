-- ══════════════════════════════════════════════════════════════════
-- A VALUE BUDGET AND A REGISTRY BUDGET WITH NOTHING BETWEEN THEM LET A
-- SINK BE HANDED A BUDGET ITS OWN REGISTRY BREAKS ON THE FIRST FRAME.
-- Price the values ENTERING the sink at one number and the registry's
-- chains at another, leaving the two free of each other, and the
-- conclusion still demands the first bound the values a `thru-outer`
-- sees AFTER those chains' own frames have run.  One `map-f` to a
-- constant observable is the whole gap: it costs the registry reading
-- nothing a large budget does not cover, and it takes a value from size
-- one to its own syntax.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- SO THE HOP MAY NOT BE STATED ON PRICES ALONE, WHICH IS WHAT THIS
-- WITNESS BUYS.  Legality is a bound on a chain's SYNTAX; the
-- conclusion is a bound on the VALUES that syntax produces, and the
-- data below is legal and unbounded at once -- so the two readings have
-- to be RELATED, and no larger choice of either relates them.  The
-- relation available is the one the sole call site walks under: every
-- iterate up to the level reached is under the value budget, dropped
-- exactly at the hop where the values leave the walked path for chains
-- nobody walked.
--
-- AND IT FIXES WHAT SUCH A PREMISE HAS TO DO, which is more than it
-- rules out.  The escape here is a value landing at `sizeᵛ` under a
-- frame whose `sizeᵗ` the registry reading already paid for, so any
-- premise dominating the registry reading at the level the values sit
-- at closes it.  What that leaves open is the LEVEL: a registry chain
-- climbs from where the walk is by its own length, and its length is
-- bounded by the registry reading rather than by the affordability's
-- ceiling.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Live-Afford where

open import Data.Bool using (false; true)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Exp; Fn; Val; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂;
  strmᵗ; input; sizeᵛ; applyFn)
open import Rx.Prim using (g0; Source)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ; mergeAll-st; Path;
  RegId; Chain; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (regsSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Verify-Budget-Sufficient.Live-Nest-Walk using (DispatchLiveHyp)
open import Refuted.Demand-Programs using (Γ₂; insT)

prog : Closed Γ₂ natᵗ
prog = input fzero

slots : Slots Γ₂
slots = insT 0 0 0

-- a constant observable, four layers deep: what the map hands the
-- node has nothing to do with what arrived
deep : ∀ {Δᵍ Δ Θ} → ℕ → Exp Γ₂ Δᵍ Δ Θ natᵗ
deep 0         = ofᵉ (nat̂ 0 ∷ [])
deep (ℕ.suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

constDeep : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
constDeep = strmᵗ (deep 4)

-- THE REGISTERED CHAIN: one map to the deep constant, then the outer
-- hop whose side condition is the one the grant has to discharge
rpath : Path Γ₂ natᵗ natᵗ
rpath = map-f constDeep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

registry : List (RegId × Source × Chain Γ₂ natᵗ)
registry = (1 , 0 , (natᵗ , rpath)) ∷ []

st₀ : EvalSt prog
st₀ = record (st-init prog)
        { nodes    = (0 , mergeAll-st {t = natᵗ} (just 0) 0 [] false) ∷ []
        ; registry = registry }

-- THE VALUES ENTERING THE SINK are nats, and a nat is one unit however
-- large it is -- which is the whole reason `U` can be this small
vals : List (Val Γ₂ natᵗ)
vals = 7 ∷ []

-- and THE VALUE THE REGISTRY CHAIN PRODUCES is an observable, whose
-- size is its entire syntax.  The asymmetry is the refutation axis
entering≡ : sizeᵛ {Γ = Γ₂} natᵗ 7 ≡ 1
entering≡ = refl

produced≡ : sizeᵛ {Γ = Γ₂} (obs natᵗ) (applyFn constDeep 7) ≡ 19
produced≡ = refl

-- BOTH PREMISES HOLD AT THE WITNESS, so what fails is the statement.
-- `U = 1` is exactly what the sink's own values admit …
hU : valsSz? {Γ = Γ₂} {s = natᵗ} 1 vals ≡ true
hU = refl

-- … and `S = 1000`, `j = 0` prices the registry with room to spare:
-- `iterSize S 0 S` is `S`, and the chain is legal far below it
hR : regsSz? (iterSize 1000 0 1000) registry ≡ true
hR = refl

-- THE CONCLUSION, at one unit of dispatch gas -- zero would make it `⊤`
Concl : Set
Concl = DispatchLiveHyp {e = prog} g0 1 0 0 1 fzero vals false
          (sched-init prog slots) st₀

-- and it contains `valsSz? 1 [deep 4] ≡ true`, which is `false ≡ true`.
-- `proj₁` leaves the one admitted chain's `PathLiveHyp`; the `map-f`
-- arm is `⊤`; the `thru-outer` arm IS the side condition
share-live-afford-absurd : Concl → ⊥
share-live-afford-absurd h with proj₁ (proj₂ (proj₁ h))
... | ()
