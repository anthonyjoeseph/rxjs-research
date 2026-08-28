-- THE SHARE FOLD AT A SPENDABLE BRANCH BUDGET, on the witness family
-- that killed the two forms before it.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: shareGoFold-nodes @c17f49
--
-- WHAT IS BEING TESTED, and it is the axis the predecessors died on.
-- The fold walks one registration after another, and each one's
-- subscription may deepen the store the next is read against -- so the
-- charge STACKS across the list, which is what no fixed-gas form could
-- carry.  This statement pays for that with a budget `k` spent per
-- branch, and the whole question is whether a list of length `k`
-- actually fits inside it.  A one-registration row cannot see this:
-- the stacking needs at least two.
--
-- THE WITNESS IS `Refuted.Share-Go-Path`'s, extended along the axis it
-- did not move.  Its registration maps every arrival to a CONSTANT
-- four-deep observable and parks it at a spent merge, so the store
-- grows by something the arrival never carried -- the shape that
-- refuted the program-denominated charge.  Rows here hand the fold one,
-- two and three copies of it, so the delivered store grows along the
-- axis the budget is supposed to price.
--
-- WHAT THE ROWS DO NOT REACH is the stacking itself: the delivery is
-- flat in the list's length here, pinned by `flat` and explained where
-- it sits.  So this file measures that the budgeted grant HOLDS, and
-- not that the budget is ever spent.
--
-- WHAT IS BLOCKED, AND IT IS THE HYPOTHESIS SIDE.  `shareBurstsOK` and
-- `shareCapsOK` are Set-valued walks over the same fold, so no row can
-- discharge them by `refl` and none is claimed to.  What is pinned is
-- the size premise, which IS decidable, and the conclusion, which
-- computes at every state a run can reach.  A conclusion that failed
-- here would be a refutation whose hypotheses' satisfiability is then
-- the smaller question; a conclusion that holds is a receipt about the
-- arithmetic and not about the walk's own invariants.
--
-- THE SEALED QUANTITIES ARE WRITTEN OUT.  `nestFac`, `fanLen`, `fanSq`
-- and `delSq` live inside a performance seal, so the bound is spelled
-- from their own recurrences rather than read through them.
module Probed.Share-Go-Fold where

open import Data.Bool using (true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Exp; Fn; natᵗ; obs; ofᵉ; mergeAllᵉ; nat̂; strmᵗ; input)
open import Rx.Prim using (g0)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (EvalSt; sched-init; st-init; root; _↠_; map-f; thru-outer; mergeAllᵒ;
         mergeAll-st; shareGo; Path; RegId)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Deliver-Measure using (admSz?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

prog : Closed Γ₂ natᵗ
prog = input fzero

slots : Slots Γ₂
slots = insT 0 0 0

deep : ∀ {Δᵍ Δ Θ} → ℕ → Exp Γ₂ Δᵍ Δ Θ natᵗ
deep 0       = ofᵉ (nat̂ 0 ∷ [])
deep (suc k) = mergeAllᵉ nothing (ofᵉ (strmᵗ (deep k) ∷ []))

constDeep : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
constDeep = strmᵗ (deep 4)

path : Path Γ₂ natᵗ natᵗ
path = map-f constDeep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

-- one, two and three copies of the refuting registration
regs : ℕ → List (RegId × Path Γ₂ natᵗ natᵗ)
regs zero    = []
regs (suc k) = (k , path) ∷ regs k

st₀ : EvalSt prog
st₀ = record (st-init prog)
        { nodes = (0 , mergeAll-st {t = natᵗ} (just 0) 0 [] false) ∷ [] }

-- THE CAP.  `cSize` must admit the registered paths, which is the one
-- premise of this statement that decides -- pinned below rather than
-- assumed; `cReg` is the budget's own ceiling.
cap : Caps
cap = caps 40 1 3

W gas : ℕ
W = 1
gas = 1

-- the sealed recurrences, written from their own definitions
fanLenᶜ fanSqᶜ : ℕ → ℕ
fanLenᶜ zero    = 0
fanLenᶜ (suc g) = Caps.cReg cap * suc (Caps.cSize cap + fanLenᶜ g)
fanSqᶜ zero    = 0
fanSqᶜ (suc g) = Caps.cReg cap * (Caps.cSize cap * Caps.cSize cap + fanSqᶜ g)

delSqᶜ : ℕ → ℕ
delSqᶜ g = (Caps.cSize cap + fanLenᶜ g) * (Caps.cSize cap + fanLenᶜ g)

nestFacᶜ : ℕ
nestFacᶜ = ((2 ^ Caps.cSize cap) ^ suc W) ^ Caps.cSize cap

-- the fold's delivered store, and the budgeted grant it must fit
delivered : ℕ → ℕ
delivered k =
  nodesMax (proj₂ (proj₂ (shareGo {t = natᵗ} g0 gas 0 0 fzero (0 ∷ []) false
                                  (regs k) (sched-init prog slots) st₀)))

grant : ℕ → ℕ
grant k =
  nestFacᶜ ^ (k * suc (Caps.cSize cap + fanLenᶜ gas))
    * ((2 ^ (k * (Caps.cSize cap * Caps.cSize cap + fanSqᶜ gas))) ^ W
       * ((nodesMax st₀ ⊔ nestDᵛˢ {Γ = Γ₂} {u = natᵗ} (0 ∷ []))
          + W * (k * (Caps.cSize cap * Caps.cSize cap + fanSqᶜ gas)
                 + suc (k * suc (Caps.cSize cap + fanLenᶜ gas))
                   * (suc (delSqᶜ (suc gas)) * nestUnit prog slots))))

-- THE DECIDABLE PREMISE, pinned rather than assumed
admits : (admSz? (Caps.cSize cap) (regs 1) ≡ true)
       × (admSz? (Caps.cSize cap) (regs 2) ≡ true)
       × (admSz? (Caps.cSize cap) (regs 3) ≡ true)
admits = refl , refl , refl

-- AND THE STACKING AXIS IS NOT REACHED BY THIS FAMILY, which is the
-- finding rather than a gap to fill.  The delivered store at three
-- registrations is EQUAL to the one at a single registration, pinned
-- as an equality below.  The reason is structural and not a poor
-- choice of witness: `nodesMax` is a JOIN over the table, and parallel
-- registrations each install their OWN node, so identical branches
-- cannot compound however many are folded.  Compounding needs a
-- registration whose subscription deepens a node a LATER registration
-- is then read at -- and this witness's paths all park at the same
-- spent merge, so the fold's own threading never carries depth
-- forward.  So rows A, B and C are DEGENERATE on the axis the budget
-- `k` is spent for, and the budget itself remains untested.
flat : delivered 1 ≡ delivered 3
flat = refl

-- ROW A, B, C: the conclusion at one, two and three registrations, the
-- budget spent at the list's own length
fitsA : (delivered 1 ≤ᵇ grant 1) ≡ true
fitsA = refl

fitsB : (delivered 2 ≤ᵇ grant 2) ≡ true
fitsB = refl

fitsC : (delivered 3 ≤ᵇ grant 3) ≡ true
fitsC = refl
