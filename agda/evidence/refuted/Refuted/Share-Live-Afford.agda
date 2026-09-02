-- ══════════════════════════════════════════════════════════════════
-- THE VALUE BUDGET AND THE REGISTRY BUDGET ARE TWO FREE NUMBERS WITH
-- NOTHING BETWEEN THEM, so a sink can be handed a value budget its own
-- registry breaks on the first frame.  The grant prices the values
-- ENTERING the sink at `U` and the registry's chains at
-- `iterSize S j S`, and `S`, `U` and `j` are independent arguments of
-- the statement -- while the conclusion demands `U` still bound the
-- values a `thru-outer` sees AFTER the registry chain's own frames have
-- run.  One `map-f` to a constant observable is the whole gap: it costs
-- the registry reading nothing that a large `S` does not cover, and it
-- takes a value from size one to its own syntax.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE CALLER HAS AND THE GRANT DOES NOT.  The one call site walks
-- under an affordability premise -- every iterate up to the level
-- reached is under `U` -- and hands the grant only the two readings
-- above, so the link is dropped exactly at the hop where the values
-- leave the walked path for chains nobody walked.  That is the missing
-- hypothesis, and it is why no arrangement of the arithmetic repairs
-- this: the statement is not too weak in its numbers, it is missing a
-- relation between them.  Note the repair is not free either -- the
-- caller's premise reaches its own level budget, and a registry chain
-- climbs past it by that chain's length, which is the quantity the
-- grant would then have to name.
--
-- AND THE HEADER IT REFUTES SAYS THE OPPOSITE IN SO MANY WORDS: that
-- every admitted path being legal under the registry reading is "what
-- makes the grant statable at all".  Legality is a bound on the chain's
-- SYNTAX; the conclusion is a bound on the VALUES that syntax produces,
-- and the witness below is legal and unbounded at once.
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
