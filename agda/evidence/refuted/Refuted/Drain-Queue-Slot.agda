-- ══════════════════════════════════════════════════════════════════
-- THE DRAIN'S COUNT IS FALSE FOR THE SAME REASON THE OUTER ARM'S WAS,
-- one door over: a parked program may be `input i`, whose layers are
-- ZERO and whose run is the whole of slot `i`'s shared definition.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
-- ══════════════════════════════════════════════════════════════════
--
-- WHAT THE STATEMENT SAYS.  A drain of an `*All` node's parked queue
-- charges the ladder one rung per LAYER of the deepest parked program,
-- and delivers within the rungs that charge buys, given that every
-- parked program's syntax fits the bound and that the node table does.
--
-- WHERE IT BREAKS.  `layᵉ (input i) = 0`, by the same one-line clause
-- that prices a `varᵉ`, so the charge is zero and the conclusion is
-- asked to hold at the bare bound.  Nothing in the premises mentions
-- the slot telescope: the store premise reads the node table and the
-- queue premise reads the parked syntax, so a shared slot is off both
-- axes exactly as it was off the arriving value's.  Subscribing
-- `input i` at a `shared` slot connects that slot's definition and
-- runs it, so a duplication chain parked in the slot emits
-- exponentially against a charge pinned at nothing at all.
--
-- AND THE SECOND ROW SAYS THE AXIS IS MEASURE-SIDE.  Both rows tie the
-- bound to the slot definition's own size, which is the most generous
-- tie the premises admit; one more rung behind the slot takes the
-- emission from `8191` to `16383` while the bound it is measured
-- against moves from `51` to `55`.  The charge between them does not
-- move at all, and cannot: it reads a syntax node whose layer count is
-- zero whatever stands behind it.
--
-- WHAT SURVIVES.  The queue is a SINGLETON in both rows, so the max
-- join over several parked programs is neither bought nor spent here —
-- what dies is the denomination, and it dies before the join is
-- reachable.  The repair is the one the outer arm already took:
-- charge the telescope as a summand of its own, which the drain can
-- read off the schedule it is handed.  The count is written out below
-- rather than imported, because these rows are evidence about a
-- READING and not about whichever function the tower spells today.
module Refuted.Drain-Queue-Slot where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; s≤s; z≤n)
open import Data.Maybe using (Maybe; nothing)
open import Data.Product using (proj₁; proj₂)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; Tick; Id)
open import Rx.Exp using (Ctx; Closed; Val; obs; input; sizeᵉ)
open import Rx.Layer-Count using (layᵛˢ)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; NodeId;
  mergeAll-st; installNode; mergeAllDrain; sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?)
open import Refuted.Frame-Step-Size-Slot
  using (Pw; chnG; f≡t; Γ₂; sl₂; e₂; Γ₃; sl₃; e₃)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
MergeAllDrainSz : Set
MergeAllDrainSz = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ B) q ≡ true →
  valsSz? (iterSize S (layᵛˢ (obs s) q) B)
    (proj₁ (mergeAllDrain sf allNid κ id now lim act q sched st)) ≡ true

----------------------------------------------------------------------
-- WITNESS ONE — twelve rungs behind the slot.  The definition measures
-- `51`, the parked program's layers measure `0`, the bound is tied to
-- the definition, and the drain emits `8191`-sized values against it.
-- The telescope and the duplication family are the sibling
-- refutation's, so the two doors are read against ONE program rather
-- than against two that merely look alike.
----------------------------------------------------------------------
o₂ : Closed Γ₂ (Pw 12)
o₂ = input fzero

q₂ : List (Closed Γ₂ (Pw 12))
q₂ = o₂ ∷ []

-- THE NODE THE DRAIN RUNS OFF, holding the very queue that is drained
-- — so the store premise is read at a table the arm actually reaches
-- rather than at an empty one.
st₂ : EvalSt e₂
st₂ = installNode 0 (mergeAll-st {Γ = Γ₂} {t = Pw 12} nothing 1 q₂ true)
        (st-init e₂)

out₂ : List (Val Γ₂ (Pw 12))
out₂ = proj₁ (mergeAllDrain {e = e₂} (gasPad 64 g0) 0 root 0 0
                nothing 0 q₂ (sched-init e₂ sl₂) st₂)

-- THE TWO READINGS SIDE BY SIDE: the definition that runs against the
-- layers the charge is allowed to see.
figures₂ : List ℕ
figures₂ = sizeᵉ (chnG {Γ = Γ₂} 12)
         ∷ layᵛˢ {Γ = Γ₂} (obs (Pw 12)) q₂
         ∷ iterSize 51 0 51 ∷ []

figures₂≡ : figures₂ ≡ 51 ∷ 0 ∷ 51 ∷ []
figures₂≡ = refl

-- THE PREMISES HOLD, spelled out so the witness cannot be read as one
-- that merely fails to satisfy them.
nodes₂ : all (λ kv → boundedNode 51 (proj₂ kv)) (EvalSt.nodes st₂) ≡ true
nodes₂ = refl

prem₂ : all (λ o → sizeᵉ o ≤ᵇ 51) q₂ ≡ true
prem₂ = refl

row₂ : Bool
row₂ = valsSz? {Γ = Γ₂} {s = Pw 12}
         (iterSize 51 (layᵛˢ {Γ = Γ₂} (obs (Pw 12)) q₂) 51)
         out₂

row₂≡false : row₂ ≡ false
row₂≡false = refl

mergeAllDrain-sz-slot-absurd : MergeAllDrainSz → ⊥
mergeAllDrain-sz-slot-absurd pr =
  f≡t (trans (sym row₂≡false)
             (pr {e = e₂} (gasPad 64 g0) 0 root 0 0 nothing 0 q₂
                 (sched-init e₂ sl₂) st₂ 51 51 (s≤s (s≤s z≤n)) refl refl))

----------------------------------------------------------------------
-- WITNESS TWO — one more rung behind the slot, bound moved with it.
-- The definition measures `55` and the emission doubles.  The charge
-- is `0` here as well, which is the finding.
----------------------------------------------------------------------
o₃ : Closed Γ₃ (Pw 13)
o₃ = input fzero

q₃ : List (Closed Γ₃ (Pw 13))
q₃ = o₃ ∷ []

st₃ : EvalSt e₃
st₃ = installNode 0 (mergeAll-st {Γ = Γ₃} {t = Pw 13} nothing 1 q₃ true)
        (st-init e₃)

out₃ : List (Val Γ₃ (Pw 13))
out₃ = proj₁ (mergeAllDrain {e = e₃} (gasPad 64 g0) 0 root 0 0
                nothing 0 q₃ (sched-init e₃ sl₃) st₃)

figures₃ : List ℕ
figures₃ = sizeᵉ (chnG {Γ = Γ₃} 13)
         ∷ layᵛˢ {Γ = Γ₃} (obs (Pw 13)) q₃
         ∷ iterSize 55 0 55 ∷ []

figures₃≡ : figures₃ ≡ 55 ∷ 0 ∷ 55 ∷ []
figures₃≡ = refl

nodes₃ : all (λ kv → boundedNode 55 (proj₂ kv)) (EvalSt.nodes st₃) ≡ true
nodes₃ = refl

prem₃ : all (λ o → sizeᵉ o ≤ᵇ 55) q₃ ≡ true
prem₃ = refl

row₃ : Bool
row₃ = valsSz? {Γ = Γ₃} {s = Pw 13}
         (iterSize 55 (layᵛˢ {Γ = Γ₃} (obs (Pw 13)) q₃) 55)
         out₃

row₃≡false : row₃ ≡ false
row₃≡false = refl

mergeAllDrain-sz-slot-absurd′ : MergeAllDrainSz → ⊥
mergeAllDrain-sz-slot-absurd′ pr =
  f≡t (trans (sym row₃≡false)
             (pr {e = e₃} (gasPad 64 g0) 0 root 0 0 nothing 0 q₃
                 (sched-init e₃ sl₃) st₃ 55 55 (s≤s (s≤s z≤n)) refl refl))
