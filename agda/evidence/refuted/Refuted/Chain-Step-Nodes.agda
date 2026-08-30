-- ══════════════════════════════════════════════════════════════════
-- ONE CHAIN'S STEP DOES NOT DEEPEN THE NODE ARM BY ONE `nestSyn`, and
-- the free argument that kills it is the PATH.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A `chainStep` leaves the nodes map no
-- deeper than it found it plus one `nestSyn e sl` -- premise-free, over
-- every arrival and every path of the context.
--
-- WHY IT LOOKED RIGHT.  Every chain a RUN presents is a rootward path
-- through `e`'s own spine, so its wraps are `e`'s wraps and a
-- syntactic ceiling on `e` covers them by construction.  The sweep that
-- ranked the row reads the arrival's own selection, where that is true,
-- and reads it comfortably even with the selection duplicated.
--
-- WHERE IT BREAKS.  The path is UNIVERSALLY QUANTIFIED and the charge
-- names `e` alone, so the two are free to move apart.  A scan frame
-- carries its own accumulator function, and the node the step installs
-- is that function applied to the payload -- so a frame whose function
-- wraps `d` times installs a node `d` deep against a program that never
-- mentions it.  Nothing in the statement ties the two together.
--
-- THE WITNESS is `progF 1 1` at `insF 1 2 2`, the smallest family in
-- reach, walked at a path built here rather than taken from the run:
-- one scan frame carrying `foldD 20`, then a constant map back to the
-- root type.  Twenty-two against a charge of fifteen.  The left side is
-- the fold depth plus two and the right side does not move at all, so
-- the gap is unbounded in `d`; the row is pinned well clear of the
-- crossing, since a charge that grows by a constant factor moves the
-- crossing and not the verdict.
--
-- WHAT DIES AND WHAT DOES NOT.  The premise-free form dies outright.
-- The claim about the runs is untouched, and the repair the numbers
-- point at is to charge the PATH -- `pathNestD`, which counts exactly
-- the wraps this frame smuggles in -- rather than to tie the path back
-- to `e` by a hypothesis, since the consuming walk has the path in
-- hand and not a proof about it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Nodes where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (foldr)
open import Data.Nat using (ℕ; _+_; _*_; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ; nat̂)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root;
         chainStep; Arrival; Path; _↠_; scan-f; map-f)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store using (nodeNest; nestUnit)
open import Refuted.Demand-Programs
  using (Γ₂; progF; foldD; insF; sucGF)

prog : Closed Γ₂ natᵗ
prog = progF 1 1

slots : Slots Γ₂
slots = insF 1 2 2

sub : Sched Γ₂ × EvalSt prog
sub = let r = subscribeE (gasPad (sucGF 1 2 2 1 1) g0) prog root 0 0
                         (sched-init prog slots) (st-init prog)
      in proj₁ (proj₂ r) , proj₂ (proj₂ r)

nodesMax : ∀ {t} {e : Closed Γ₂ t} → EvalSt e → ℕ
nodesMax st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

-- the arrival is ordinary; the PATH is what the statement leaves free
arr : Arrival Γ₂
arr = record { tick = 0 ; ordinal = 0 ; source = 1 ; elemTy = natᵗ
             ; payload = 0 ; isLast = false }

deep : ℕ → Path Γ₂ natᵗ natᵗ
deep d = scan-f (foldD d) 7 ↠ (map-f (nat̂ 0) ↠ root)

row : ℕ × ℕ
row = let st = proj₂ sub
          r  = chainStep 1 arr (deep 20) (proj₁ sub) st
      in nodesMax (proj₂ (proj₂ r)) , nodesMax st + (2 * nestUnit prog slots)

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
grown≡22 : proj₁ row ≡ 22
grown≡22 = refl

charge≡15 : proj₂ row ≡ 15
charge≡15 = refl

chainStep-nodes-absurd : proj₁ row ≤ proj₂ row → ⊥
-- `22 ≤ᵇ 15` reduces to `false`, so `T` of it IS the empty type
chainStep-nodes-absurd h = ≤⇒≤ᵇ h
