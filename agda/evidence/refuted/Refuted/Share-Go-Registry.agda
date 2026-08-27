-- ══════════════════════════════════════════════════════════════════
-- THE PREMISE PRICES THE TOP LIST AND THE SINK READS THE STATE'S OWN
-- REGISTRY, so one zero-cost hop routes the fold into paths no
-- hypothesis ever saw.  `pathNestD` charges a `share-sink` zero, which
-- makes `chainsNestD` of a list of bare sinks zero however adversarial
-- the registry those sinks admit from -- and the registry is a field
-- of `st`, a bound variable of the statement.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- THE WITNESS is `Refuted.Share-Go-Path`'s registration verbatim --
-- map to a four-deep constant, park at a spent merge -- moved one
-- level down: it sits in `st`'s registry under source 0, and the
-- priced list holds only `share-sink 0`, whose charge is zero.  The
-- fold takes the hop, admits the registration, and stores the same
-- four-deep observable against the same two-unit charge -- so the
-- CONDITIONED form dies on the sibling witness's own figures, and the
-- premise that repaired the premise-free form is shown to price the
-- wrong list.  The repair has to reach the registry: a second premise
-- bounding the wraps of what `st` itself can register, which is
-- exactly the conjunct `capsWalkOK` carries at its sink arm and the
-- one `dispatchShare-nodes` already takes.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Go-Registry where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; _+_; _⊔_; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Exp; Fn; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂; strmᵗ; input)
open import Rx.Prim using (g0; Source)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ;
         mergeAll-st; shareGo; share-sink; Path; RegId; Chain; Sched)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit; chainsNestD)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

prog : Closed Γ₂ natᵗ
prog = input fzero

slots : Slots Γ₂
slots = insT 0 0 0

-- a constant observable, four layers deep: what the map hands the
-- node has nothing to do with what arrived
deep : ∀ {Δᵍ Δ Θ} → ℕ → Exp Γ₂ Δᵍ Δ Θ natᵗ
deep 0       = ofᵉ (nat̂ 0 ∷ [])
deep (ℕ.suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

constDeep : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
constDeep = strmᵗ (deep 4)

-- the deep registration, REGISTERED rather than priced: it lives in
-- the state's registry on source 0, where `chainsNestD` cannot see it
rpath : Path Γ₂ natᵗ natᵗ
rpath = map-f constDeep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

registry : List (RegId × Source × Chain Γ₂ natᵗ)
registry = (1 , 0 , (natᵗ , rpath)) ∷ []

-- the PRICED list is one bare hop into share 0, and its charge is zero
regs : List (RegId × Path Γ₂ natᵗ natᵗ)
regs = (0 , share-sink fzero) ∷ []

st₀ : EvalSt prog
st₀ = record (st-init prog)
        { nodes    = (0 , mergeAll-st {t = natᵗ} (just 0) 0 [] false) ∷ []
        ; registry = registry }

run : EvalSt prog
run = proj₂ (proj₂ (shareGo {t = natᵗ} g0 1 0 0 (fsuc fzero) (0 ∷ []) false regs
                            (sched-init prog slots) st₀))

grown : ℕ
grown = nodesMax run

charge : ℕ
charge = (nodesMax st₀ ⊔ nestDᵛˢ {Γ = Γ₂} {u = natᵗ} (0 ∷ [])) + nestUnit prog slots

-- THE PREMISE HOLDS AT THE WITNESS -- a bare sink's charge is zero --
-- so what fails is the statement and not its hypothesis
priced : chainsNestD regs ≤ nestUnit prog slots
priced = z≤n

-- and so does the slots premise, definitionally off `sched-init`
slots-fixed : Sched.slots (sched-init prog slots) ≡ slots
slots-fixed = refl

-- THE FIGURES, PINNED, so a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
grown≡ : grown ≡ 4
grown≡ = refl

charge≡ : charge ≡ 2
charge≡ = refl

share-go-registry-absurd : grown ≤ charge → ⊥
-- `4 ≤ᵇ 2` reduces to `false`, so `T` of it IS the empty type
share-go-registry-absurd h = ≤⇒≤ᵇ h
