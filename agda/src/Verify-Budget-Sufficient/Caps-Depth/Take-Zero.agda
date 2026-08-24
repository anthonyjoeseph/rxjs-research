------------------------------------------------------------------
-- A TAKE'S PUSH COSTS NO DEPTH AT ALL, and it lives beside the measure
-- rather than beside a bound: `takeDispatch` subscribes nothing, so the
-- frame clause is `0` and the burst is a fold of `0`s.  Nothing about
-- the currency a consumer bounds this by enters the statement.
--
-- IT SITS IN ITS OWN MODULE BECAUSE IT NEEDS `depthBurst` TO REDUCE,
-- and a body that needs one of a mutual block's members to unfold
-- cannot live beside that block: the dev loop stubs the block, so the
-- `[]` clause loses the equation it is `z≤n` by.  From out here the
-- import carries the real clauses, and every consumer of the depth
-- family already reaches this file through .Caps-Depth.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Caps-Depth.Take-Zero where

open import Data.Nat     using (_≤_; z≤n)
open import Data.Nat.Properties using (⊔-lub)
open import Data.List    using ([]; _∷_)
open import Data.Product using (proj₁; proj₂)

open import Rx.Prim  using (Gas; Id; Tick; InstEmit)
open import Rx.Exp   using (Ctx; Closed; Val)
open import Rx.Evaluator using (Sched; EvalSt; NodeId; Path; Stream;
  take-f; splitEvents; stepFrame)
open import Verify-Budget-Sufficient.Caps-Depth using (depthBurst)

burst-takef-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (bid : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (stream : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  depthBurst fuel bid now (take-f nid) κ stream sched st ≤ 0
burst-takef-zero fuel bid now nid κ [] sched st = z≤n
burst-takef-zero {Γ = Γ} {s = s} fuel bid now nid κ (em ∷ ems) sched st =
  ⊔-lub z≤n (burst-takef-zero fuel bid now nid κ ems sched' st')
  where
  sp     = splitEvents {A = Val Γ s} (InstEmit.events em)
  r      = stepFrame fuel bid now (take-f nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sched' = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st'    = proj₂ (proj₂ (proj₂ (proj₂ r)))
