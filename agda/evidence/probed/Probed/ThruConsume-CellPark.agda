-- ══════════════════════════════════════════════════════════════════
-- THE ENQUEUE ARM OF `thruConsume` (mergeAllᵒ, hasRoom = false)
-- PRESERVES `parkStrat?` WHEN THE ARRIVING VALUE'S INPUTS ARE BELOW
-- THE FLOOR.
--
-- TARGET: thruConsume-cellPark @73ea8f
--
-- WHAT THE ROW INSTANTIATES.  A one-slot context, outer observable
-- source.  The node at nid=0 holds a capacity-ZERO mergeAll state
-- (`just 0`, active=0) with an empty queue; the arriving value is
-- `input fzero`, a closed expression whose single input reference is
-- at index 0, strictly below the floor k=1.  `hasRoom (just 0) 0 =
-- false`, so `thruConsume` enqueues rather than subscribes, leaving
-- the node in state `mergeAll-st (just 0) 0 [input fzero] false`.
-- `parkStrat? 1` on that node computes `all (inputsBelowᵉ 1)
-- [input fzero] = 0 <ᵇ 1 = true`.
--
-- WHAT MAKES THE ROW LOAD-BEARING.  The row would not hold if the
-- input reference were at or above the floor: `input fzero` at k=0
-- gives `inputsBelowᵛ 0 (obs natᵗ) (input fzero) = 0 <ᵇ 0 = false`,
-- blocking the hypothesis.  The hypothesis is what keeps the enqueued
-- term in range; without it the conclusion goes false.  Both
-- reductions are by transparent computation; the body is `refl`.
--
-- WHAT IS NOT COVERED.  The `hasRoom = true` (subscribe) arm calls
-- `subscribeInner`, which is complex and requires `Gas` to unfold.
-- The `switchᵒ` and `exhaustᵒ` ops, which follow independent arms.
-- A non-empty initial queue (the pre-hypothesis then carries a
-- non-trivial `all`, not just `true` from an empty list).
-- ══════════════════════════════════════════════════════════════════
module Probed.ThruConsume-CellPark where

open import Data.Bool using (false)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using ([])
open import Data.Maybe using (just)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (g0; cold)
open import Rx.Exp using (Ctx; Closed; natᵗ; emptyᵉ; input)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (EvalSt; mergeAllᵒ; root;
         sched-init; st-init; installNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
  using (thruConsume-cellPark)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT AND INITIAL STATE
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

e₁ : Closed Γ₁ natᵗ
e₁ = emptyᵉ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (cold [] [])

-- A capacity-zero mergeAll node at nid 0; `hasRoom (just 0) 0 = false`
-- so any arriving value is enqueued rather than subscribed.
st₀ : EvalSt e₁
st₀ = installNode 0 (mergeAll-st {t = natᵗ} (just 0) 0 [] false) (st-init e₁)

----------------------------------------------------------------------
-- THE TIE.  `thruConsume g0 mergeAllᵒ 0 root 0 0 (input fzero)
-- (sched-init e₁ sl₁) st₀` takes the enqueue arm: it writes
-- `mergeAll-st (just 0) 0 [input fzero] false` at nid 0.
-- `parkStrat? (pathFloor root)` on that node reduces to
-- `all (inputsBelowᵉ 1) [input fzero] = 0 <ᵇ 1 = true`.
----------------------------------------------------------------------

tie : Confirms
  (thruConsume-cellPark g0 mergeAllᵒ 0 root 0 0
     (input fzero)
     (sched-init e₁ sl₁) st₀ refl refl)
tie = refl
