-- THE SERIES Q PROGRAM FAMILY.  One home, and today one consumer.
--
-- Q varies a scan fold's wrap DEPTH d and its source list LENGTH k
-- independently, which is what makes it the only probe family that can
-- see the walk face's live edge: the demand hypothesis supplies a SUM
-- (`sucG`, a static syntactic size) while gas demand tracks the
-- within-instant nesting depth, a PRODUCT d·k.  A sum cannot dominate a
-- product forever.
--
-- WHY IT IS A MODULE OF ITS OWN, and why that survives the probe that
-- used to share it.  The crossing region is unreachable in the
-- TYPECHECKER — `runDry` gives no
-- short-circuit in either direction (`hasDry` reads the stream
-- `subscribeE` returns, so the whole run normalises before the first dry
-- event is visible), and the cost is quadratic in k: a run normalises
-- d·k(k+1)/2 subscription levels, ~250 at the cheapest crossing point,
-- where (8,8) burned 56 min CPU without finishing.  Only the COMPILED
-- harness reaches it.  The type-level half of that pair — a probe that
-- pinned what the checker COULD reach — has since expired with its
-- targets and been deleted, so `Harness.Main` is the sole consumer; see
-- the RECOVERY pointer in `.Burst-Walk` for what those rows measured.
--
-- IMPORTS ONLY `Rx.*`, deliberately, and that is why the deletion cost
-- nothing here: `Harness.Main` is a cheap calculator, and a family that
-- reached up into the Verify tower would drag the whole thing into
-- `make harness-build`.
module Verify-Budget-Sufficient.Demand-Programs where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Bool using (Bool)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; _×ᵗ_; ofᵉ; mergeAllᵉ; scanᵉ; strmᵗ; fstᵗ; varᵗ; nat̂; syncSizeᵉ; Tm;
  Fn)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; hasDry; root)
open import Rx.Slots using (Slots)
open import Rx.Hop-Depth using (hopDᵉ)
open import Rx.Slot-Hop using (slotHop)

----------------------------------------------------------------------
-- Context and slots: empty (no inputs)
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE RUNNERS.  `subscribeE` at the ENTRY — root path, tick 0, and the
-- evaluator's OWN initial schedule and state, so these are states the
-- evaluator reaches by running rather than states built by hand.
----------------------------------------------------------------------

runDry : ∀ {t} (h : ℕ) (e : Closed Γ₀ t) → Bool
runDry h e =
  hasDry (proj₁ (subscribeE (gasPad h g0) e root 0 0
                             (sched-init e ins₀) (st-init e)))

----------------------------------------------------------------------
-- THE FAMILY.  `progD d k` scans a k-element list with a fold that
-- wraps its accumulator d mergeAll-levels deeper per value, so accᵢ
-- carries d·i nested levels and the outer *All subscribes all of them.
----------------------------------------------------------------------

-- wrap a term d mergeAll-levels deeper
wrapD : ∀ {Θ} → ℕ → Tm Γ₀ [] [] Θ (obs natᵗ) → Tm Γ₀ [] [] Θ (obs natᵗ)
wrapD 0       t = t
wrapD (suc d) t = strmᵗ (mergeAllᵉ (ofᵉ (wrapD d t ∷ [])))

-- the fold that wraps the accumulator d levels per value
foldD : ℕ → Fn Γ₀ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
foldD d = wrapD d (fstᵗ (varᵗ (here refl)))

natsD : ℕ → List (Tm Γ₀ [] [] [] natᵗ)
natsD 0       = []
natsD (suc k) = nat̂ k ∷ natsD k

progD : ℕ → ℕ → Closed Γ₀ natᵗ
progD d k =
  mergeAllᵉ (scanᵉ (foldD d) (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) (ofᵉ (natsD k)))

-- THE GAS THE FACE'S DEMAND HYPOTHESIS SUPPLIES at the adversarial
-- (smallest) instantiation Ŝ := R̂ := F := 0 and U := 0, where dBound
-- degenerates to `syncSizeᵉ b + hopDᵉ 0 b` and `hasAtLeast-pad` makes
-- `gasPad (suc G) g0 hasAtLeast suc G` hold EXACTLY, nothing spare.
-- So `runDry (sucG p) p ≡ true` REFUTES WalkStmt at p.
sucG : Closed Γ₀ natᵗ → ℕ
sucG b = suc (syncSizeᵉ b + hopDᵉ 0 (slotHop 0 ins₀) b)
