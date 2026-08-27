-- ══════════════════════════════════════════════════════════════════
-- THE SINK'S FOLD IS CHARGED IN THE PROGRAM'S CURRENCY AND WALKS PATHS
-- THE PROGRAM NEVER PRICED.  The fold's statement quantifies its
-- registration list freely, with no premise tying those paths to the
-- registry or the program, while its charge is one `nestUnit` -- a
-- quantity of the PROGRAM and the slots -- above the store and the
-- arrival.  A registration is a path, a path carries frames, and a
-- `map-f` frame carries a function whose output the walk stores; none
-- of those appear in any hypothesis.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- THE WITNESS hands the fold one registration whose path maps every
-- arrival to a CONSTANT four-deep observable and parks it at a spent

-- The charge reads the arrival (zero), the store (zero) and the unit
-- of a one-slot program (two), and the store moves to six.
--
-- WHAT THIS SAYS AND WHAT IT DOES NOT.  The statement as written is
-- false, so the leaf cannot be proven; that much is unconditional,
-- because both the list and the state are its own bound variables --
-- the same licence `Probed.Cascade-Chain-Count` records for the
-- chain-step face, where a frame the program never mentions is a
-- legitimate instantiation.  Whether the fact the CALLER needs is
-- false is a separate question this witness does not answer: the one
-- real call site passes `shareAdmit` of the registry, and a registry
-- built by a run holds only paths the program subscribed.  The repair
-- is therefore one of two restatements, and both are known shapes
-- here: denominate the charge in the registrations' own measure, the
-- way the chain-step face already charges `pathNestF` after its own
-- refutation of a program-denominated bound; or keep the unit and add
-- the premise that every registered path's frames are the program's,
-- which is a registry invariant no hypothesis currently carries.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Share-Go-Path where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; _≤_; _+_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Exp; Fn; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂; strmᵗ; input)
open import Rx.Prim using (g0)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ; mergeAll-st; shareGo;
  Path; RegId)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
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

-- one registration: map to the deep constant, park at a spent merge
path : Path Γ₂ natᵗ natᵗ
path = map-f constDeep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

regs : List (RegId × Path Γ₂ natᵗ natᵗ)
regs = (0 , path) ∷ []

st₀ : EvalSt prog
st₀ = record (st-init prog)
        { nodes = (0 , mergeAll-st {t = natᵗ} (just 0) 0 [] false) ∷ [] }

run : EvalSt prog
run = proj₂ (proj₂ (shareGo {t = natᵗ} g0 0 0 0 fzero (0 ∷ []) false regs
                            (sched-init prog slots) st₀))

grown : ℕ
grown = nodesMax run

charge : ℕ
charge = (nodesMax st₀ ⊔ nestDᵛˢ {Γ = Γ₂} {u = natᵗ} (0 ∷ [])) + nestUnit prog slots

-- THE FIGURES, PINNED, so a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
grown≡ : grown ≡ 4
grown≡ = refl

charge≡ : charge ≡ 2
charge≡ = refl

share-go-path-absurd : grown ≤ charge → ⊥
-- `4 ≤ᵇ 2` reduces to `false`, so `T` of it IS the empty type
share-go-path-absurd h = ≤⇒≤ᵇ h
