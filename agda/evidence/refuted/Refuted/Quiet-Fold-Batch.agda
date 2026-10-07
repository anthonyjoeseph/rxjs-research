-- `quiet-fold` OVER EVERY TAIL IS FALSE.  A lowered bracket flushes
-- its buffer on the first fold through it, whatever that fold hands
-- it, so a tail handed nothing and no end still sends the buffer when
-- a bracket on it is down with a value held.
--
-- THE STATE IS BUILT, NOT REACHED, and that is the claim: the
-- statement quantified over every tail and every state it is folded in.
module Refuted.Quiet-Fold-Batch where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Rx.Exp using (Ctx; Closed; Val; FnClo; _×ᵗ_; listᵗ; natᵗ; uniqᵗ; []ᵉ; fstᵗ; varᵗ)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; map-f; batchSync-f; _↠[_]_; sched-init; st-init; batchSync-st)
open import Rx.Evaluator.Domain using (fold-root; fold-step; step-map; step-batchSync)
open import SExp.Syntax using (Kinds; plainᵏ; emitᵗ; inputˢ; emptyˢ)
open import SExp.InstEmit using (instEmitᵗ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import SExp.Simul-Slots using (SimulSlots)
open import Simulation.Arm using (QuietTail)
open import CLI.Unit-Test.Prelude using (Γ₂; κOf; mkSlots)
open import Rx.Prim using (hot)

κ₀ : Kinds 2
κ₀ = κOf (hot [])

ins : SimulSlots Γ₂ κ₀
ins = mkSlots (hot []) emptyˢ

Γ′ = plainᵏ Γ₂ κ₀

ei : Closed Γ′ (emitᵗ natᵗ)
ei = elaborateImpl {Γ = Γ₂} κ₀ (inputˢ zero)

-- one emit carrying one value
v : Val Γ′ (emitᵗ natᵗ)
v = inj₂ (inj₁ 7) ∷ [] , 0 , 0 , inj₁ tt

-- the bracket is down and still holds it
st : EvalSt ei
st = record (st-init ei) { nodes = (0 , batchSync-st {s = emitᵗ natᵗ} false (v ∷ []) false) ∷ [] }

sI : Sched Γ′
sI = sched-init ei (embedSlotsImpl ins)

fst′ : FnClo Γ′ (emitᵗ natᵗ ×ᵗ listᵗ (emitᵗ natᵗ)) (emitᵗ natᵗ)
fst′ = [] , fstᵗ (varᵗ (here refl)) , []ᵉ

q : Path Γ′ 0 (emitᵗ natᵗ) (emitᵗ natᵗ)
q = batchSync-f 0 ↠[ ≤-refl ] (map-f fst′ ↠[ ≤-refl ] root)

QuietFold : Set
QuietFold = ∀ {m} {Δ : Ctx m} {t} {e : Closed Δ (instEmitᵗ uniqᵗ t)} {ℓ u} {q : Path Δ ℓ u (instEmitᵗ uniqᵗ t)} → QuietTail e q

-- folded with nothing and no end, the tail sends the held value
quiet-fold-false : ¬ QuietFold
quiet-fold-false QF with proj₁ (QF {e = ei} {q = q} {now = 0} {sched = sI} {st = st} (fold-step step-batchSync (fold-step step-map fold-root)))
... | ()
