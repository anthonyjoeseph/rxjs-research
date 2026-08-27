-- ══════════════════════════════════════════════════════════════════
-- ONE UNIT DOES NOT SURVIVE TWO SINKS: pricing the registry by its
-- MAX charges each hop a whole unit and the conclusion only carries
-- one, so a branch that descends through two shares stacks what the
-- premise licensed twice.  This kills the candidate repair of
-- `Refuted.Share-Go-Registry` -- keep the statement, add
-- `regsNestMax st ≤ nestUnit` -- BEFORE it is adopted: with the
-- priced list and the registry each at exactly the unit, the walk
-- wraps the payload once per level and stores their SUM.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- THE WITNESS needs a share whose ELEMENT type is an observable, so
-- that a value can gain wraps before the hop -- a two-slot context
-- `obs natᵗ ∷ natᵗ`, the share at index zero with a one-deep constant
-- def (which sets the unit at two).  The priced list maps the arrival
-- to a two-deep constant and hops into the share; the registry's one
-- admitted path wraps its input once more and parks it at a spent
-- merge.  Both premises hold at exactly the unit, and the store takes
-- three against a charge of two.
--
-- WHAT THIS RULES OUT, and what it leaves.  Any restatement whose
-- registry premise prices paths INDEPENDENTLY (a max, one unit each)
-- dies here, because a branch spends its hops in SEQUENCE.  What
-- survives is a premise over the branch STRUCTURE -- the wraps a
-- descent can spend, summed along it, inside one unit -- which is
-- what a registry built by a real run satisfies: each registered
-- path's wraps are a subterm of its subscriber's syntax, and the
-- subscribers of a strict slot descent are distinct summands of
-- `nestUnit`'s own `nestDᵉ e + slotsNestSum`.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Go-Stack where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; _+_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; Fn; natᵗ; obs; ofᵉ; mergeAllᵉ;
                          emptyᵉ; nat̂; strmᵗ; varᵗ; input)
open import Rx.Prim using (g0; Source; cold)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ;
         mergeAll-st; shareGo; share-sink; Path; RegId; Chain; Sched)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit; chainsNestD; regsNestMax)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)

Γ₃ : Ctx 2
Γ₃ = obs natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

prog : Closed Γ₃ natᵗ
prog = input (fsuc fzero)

-- the share's def: one *All layer over an empty inner, nest ONE --
-- which puts the unit at exactly two
def₀ : Closed Γ₃ (obs natᵗ)
def₀ = ofᵉ (strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ emptyᵉ ∷ []))) ∷ [])

slots : Slots Γ₃
slots fzero         = shared def₀
slots (fsuc fzero)  = scripted (cold [] [])

-- a constant observable, k layers deep
deep : ∀ {Δᵍ Δ Θ} → ℕ → Exp Γ₃ Δᵍ Δ Θ natᵗ
deep 0       = ofᵉ (nat̂ 0 ∷ [])
deep (ℕ.suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

-- WRAP THE ARGUMENT, one *All layer per step: the level-two path's
-- spending is a function of what level one delivered, which is what
-- makes the two hops' charges SEQUENCE instead of joining
wrap : ℕ → Fn Γ₃ [] [] [] (obs natᵗ) (obs natᵗ)
wrap 0       = varᵗ (here refl)
wrap (ℕ.suc k) = strmᵗ (mergeAllᵉ nothing (ofᵉ (wrap k ∷ [])))

-- level one, PRICED: map the arrival to a two-deep constant, hop into
-- the share -- charge two, the unit exactly
p₁ : Path Γ₃ natᵗ natᵗ
p₁ = map-f (strmᵗ (deep 2)) ↠ share-sink fzero

regs : List (RegId × Path Γ₃ natᵗ natᵗ)
regs = (0 , p₁) ∷ []

-- level two, REGISTERED: wrap once more, park at a spent merge --
-- charge two again, the registry's max at the unit exactly
p₂ : Path Γ₃ (obs natᵗ) natᵗ
p₂ = map-f (wrap 1) ↠ (thru-outer mergeAllᵒ 0 ↠ root)

registry : List (RegId × Source × Chain Γ₃ natᵗ)
registry = (2 , 0 , (obs natᵗ , p₂)) ∷ []

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
charge = (nodesMax st₀ ⊔ nestDᵛˢ {Γ = Γ₃} {u = natᵗ} (0 ∷ [])) + nestUnit prog slots

-- EVERY PREMISE OF THE CANDIDATE HOLDS AT THE WITNESS, at the unit
-- exactly, so what fails is the candidate and not a hypothesis
priced : chainsNestD regs ≤ nestUnit prog slots
priced = s≤s (s≤s z≤n)

reg-priced : regsNestMax registry ≤ nestUnit prog slots
reg-priced = s≤s (s≤s z≤n)

slots-fixed : Sched.slots (sched-init prog slots) ≡ slots
slots-fixed = refl

-- THE FIGURES, PINNED, so a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
grown≡ : grown ≡ 3
grown≡ = refl

charge≡ : charge ≡ 2
charge≡ = refl

share-go-stack-absurd : grown ≤ charge → ⊥
-- `3 ≤ᵇ 2` reduces to `false`, so `T` of it IS the empty type
share-go-stack-absurd h = ≤⇒≤ᵇ h
