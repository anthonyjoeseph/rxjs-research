-- ══════════════════════════════════════════════════════════════════
-- THE REGISTRY ARM AT THE ONE SHAPE THAT DEEPENS A REGISTRATION: *All
-- FRAMES STACKED ROOTWARD OF THE LEAF, NOT NESTED INSIDE THE VALUE.
--
-- TARGET: chainStep-nest-regsC @c7e44c
--
-- WHY THIS PROGRAM AND NOT A DEEPER VALUE.  A registration carries the
-- path of the CONTINUATION it hangs off, and only `thru-outer` counts
-- -- the frame an *All pushes when it subscribes its own SOURCE.  An
-- inner subscription pushes `from-inner`, which charges nothing, so
-- nesting inside the emitted value cannot raise this fold however deep
-- it goes.  What raises it is a stack of *All operators whose sources
-- are each other, which needs the leaf at an iterated observable type.
-- `arriving k` is that stack: `k` flattens over a `deferᵉ` at `obs^k
-- nat`, and the async input hands one to the outer *All per arrival.
--
-- WHAT THE SWEEP FOUND, AND IT IS A MECHANISM RATHER THAN A NUMBER.
-- The fold reads `k + 1` on BOTH sides, at both depths: the chain mints
-- its registration at exactly the depth the map frame carrying the
-- emitted observable is already charged.  That is not a coincidence of
-- these two programs.  The frame's own `nestDᵉ` counts the `thru-outer`
-- frames the emitted expression will push, and where the count stops --
-- at a `deferᵉ`, whose gate truncates it to zero -- the defer's own
-- registration adds back exactly the one frame the gate dropped.  So a
-- chain cannot leave a registration deeper than the one it came from
-- plus what its own frames charge, which is the arm's content arriving
-- as a property of the measure.
--
-- WHAT IS LOAD-BEARING.  Both rows can fail, and it is the tie they
-- pin: the left side is the evaluator's own registry fold after a real
-- `chainStep`, `k` is swept so the measured side moves between the
-- rows, and a minted path exceeding the frame's charge by even one
-- would read as a rise the charge is not asked to cover.  The charge is
-- the syntactic surrogate the tree proves the arm's cap dominates, so
-- green here implies the arm at this program and red here does not
-- refute it.
module Probed.Chain-Step-Regs-Rootward where

open import Data.Bool using (true; _∧_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_; _⊔_; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Ty; Closed; Exp; Tm; natᵗ; obs; sizeᵉ; syncSizeᵉ; ofᵉ; mapᵉ;
         mergeAllᵉ; deferᵉ; strmᵗ; nat̂; input)
open import Rx.Prim using (gasPad; g0)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root; sched-next;
         cascadeLatch; chainStep; chainsOf)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit; regsNestMax)
open import Refuted.Demand-Programs using (Γ₂; insF)

slots : Slots Γ₂
slots = insF 1 1 2

obsⁿ : ℕ → Ty → Ty
obsⁿ zero    t = t
obsⁿ (suc k) t = obs (obsⁿ k t)

vⁿ : ∀ {Θ} (k : ℕ) → Tm Γ₂ [] [] Θ (obsⁿ k natᵗ)
vⁿ zero    = nat̂ 0
vⁿ (suc k) = strmᵗ (ofᵉ (vⁿ k ∷ []))

-- k flattens, each pushing a thru-outer frame rootward of the next
flat : ∀ {Θ} (k : ℕ) → Exp Γ₂ [] [] Θ (obsⁿ k natᵗ) → Exp Γ₂ [] [] Θ natᵗ
flat zero    e = e
flat (suc k) e = flat k (mergeAllᵉ nothing e)

arriving : ∀ {Θ} (k : ℕ) → Exp Γ₂ [] [] Θ natᵗ
arriving k = flat k (deferᵉ (ofᵉ (vⁿ k ∷ [])))

progR : ℕ → Closed Γ₂ natᵗ
progR k = mergeAllᵉ nothing (mapᵉ (strmᵗ (arriving k)) (input (fsuc fzero)))

sucGR : ℕ → ℕ
sucGR k = suc (syncSizeᵉ (progR k) + hopDᵉ 0 (slotHop 0 slots) (progR k))

sub : (k : ℕ) → Sched Γ₂ × EvalSt (progR k)
sub k = let r = subscribeE (gasPad (sucGR k) g0) (progR k) root 0 0
                           (sched-init (progR k) slots) (st-init (progR k))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

charge : ℕ → ℕ
charge k = nestUnit (progR k) slots + (2 + sizeᵉ (progR k))

-- the registry fold before and after the first chain of the first
-- arrival's cascade, taken off states the evaluator reached
regsRow : (k : ℕ) → ℕ × ℕ
regsRow k with sched-next (proj₁ (sub k))
... | inj₁ _        = 0 , 0
... | inj₂ (a , sd) with chainsOf a (proj₂ (sub k))
...   | []            = 0 , 0
...   | (rid , c) ∷ _ =
        let st₀ = cascadeLatch a (proj₂ (sub k))
            r   = chainStep 1 a c sd st₀
        in regsNestMax (EvalSt.registry st₀)
         , regsNestMax (EvalSt.registry (proj₂ (proj₂ r)))

packed : ℕ
packed = proj₁ (regsRow 1) + 100 * proj₂ (regsRow 1) + 10000 * charge 1
       + 1000000 * proj₁ (regsRow 3) + 100000000 * proj₂ (regsRow 3)
       + 10000000000 * charge 3

figures≡ : packed ≡ 290404190202
figures≡ = refl

fits : (proj₂ (regsRow 1) ≤ᵇ proj₁ (regsRow 1) ⊔ charge 1)
     ∧ (proj₂ (regsRow 3) ≤ᵇ proj₁ (regsRow 3) ⊔ charge 3) ≡ true
fits = refl
