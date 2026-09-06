-- ══════════════════════════════════════════════════════════════════
-- THE LIVE FOLD'S ARRIVAL-SIZE CHARGE, AGAINST A DEFERRED BODY THE
-- ARRIVAL NEVER CARRIED AND THE STORE'S DEPTH MEASURE CANNOT SEE.
--
-- `chainStep-nest-live` charges a step `pathNestF path * sizeᵛ` of the
-- ARRIVAL, on top of the incoming live fold and the slots.  The
-- witness parks a deep deferred constant as a scan's SEED, delivers a
-- unit-sized arrival, and lets the scan hand the seed through unchanged
-- (`fstᵗ`) to a `mergeAllᵉ` outer, whose subscribe strips the gate and
-- mints a live whose pending payload is the body at its full depth.
-- The arrival is one unit wide, the path's factor is a small constant,
-- and the grown fold is the body's depth -- so the gap is unbounded in
-- the seed.
--
-- AND NO STORE TERM IN THE DEPTH CURRENCY REPAIRS IT.  The parked seed
-- is a `deferᵉ`, and `nodeNest` reads a deferred value as ZERO -- the
-- row below pins the node fold at nought while the step mints a live
-- of depth nine out of it.  What sees the body is its SIZE, or a depth
-- measure that looks through ONE gate; the plain depth measure the
-- store invariant is stated over sees nothing.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Chain-Step-Live-Seed where

open import Data.Empty using (⊥)
open import Data.Maybe using (nothing)
open import Data.Bool using (false)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_; foldr; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _≤_; _⊔_; _*_; _+_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
  using (Closed; Exp; natᵗ; nat̂; ofᵉ; strmᵗ; deferᵉ; switchAllᵉ;
         mergeAllᵉ; scanᵉ; fstᵗ; varᵗ; input; sizeᵛ)
open import Rx.Prim using (Gas; g0; gs; Source)
open import Rx.Evaluator
  using (Sched; EvalSt; subscribeE; sched-init; st-init; root;
         chainStep; chainsOf; Arrival; Path)
open import Rx.Slots using (Slots)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; pathNestF; nodeNest)
open import Refuted.Demand-Programs using (Γ₂; insT)

-- the seed: a body k `switchAllᵉ` layers deep, under one gate
deepE : ∀ {Θ} → ℕ → Exp Γ₂ [] [] Θ natᵗ
deepE zero    = ofᵉ (nat̂ 0 ∷ [])
deepE (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepE k) ∷ []))

-- a scan whose step hands the accumulator through untouched, seeded
-- with the deferred body, fed by the scripted slot so nothing
-- completes inside the subscribe
prog : ℕ → Closed Γ₂ natᵗ
prog k = mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (here refl))) (strmᵗ (deferᵉ (deepE k)))
                  (input (fsuc fzero)))

slots : Slots Γ₂
slots = insT 0 0 1

gas : Gas
gas = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

sub : (k : ℕ) → Sched Γ₂ × EvalSt (prog k)
sub k = let r = subscribeE gas (prog k) root 0 0 (sched-init (prog k) slots) (st-init (prog k))
        in proj₁ (proj₂ r) , proj₂ (proj₂ r)

-- THE SOURCE AND THE PATH ARE READ OFF THE REGISTRY THE RUN BUILT,
-- not written by hand: the one registration is the scan's, on the
-- scripted slot
srcOf : (k : ℕ) → Source
srcOf k with EvalSt.registry (proj₂ (sub k))
... | (_ , s , _) ∷ _ = s
... | []              = 0

-- the arrival: one unit from the scripted slot the scan is fed by
shallow : ℕ → Arrival Γ₂
shallow k = record { tick = 1 ; ordinal = 0 ; source = srcOf k ; elemTy = natᵗ
                   ; payload = 0 ; isLast = false }

pathOf : (k : ℕ) → Path Γ₂ natᵗ natᵗ
pathOf k with chainsOf (shallow k) (proj₂ (sub k))
... | (_ , p) ∷ _ = p
... | []          = root

oneChain : length (chainsOf (shallow 9) (proj₂ (sub 9))) ≡ 1
oneChain = refl

liveMax : Sched Γ₂ → ℕ
liveMax sched = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)

grown : ℕ → ℕ
grown k = liveMax (proj₁ (proj₂ (chainStep {e = prog k} 1 (shallow k) (pathOf k) (proj₁ (sub k)) (proj₂ (sub k)))))

charge : ℕ → ℕ
charge k = liveMax (proj₁ (sub k)) ⊔ slotsNestSum (Sched.slots (proj₁ (sub k)))
             ⊔ pathNestF (pathOf k) * sizeᵛ {Γ = Γ₂} natᵗ 0

-- the store's own depth reading of the parked seed: blind
armed : ℕ → ℕ
armed k = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (sub k)))

figures : ℕ
figures = grown 9 + 100 * charge 9 + 10000 * armed 9 + 100000 * grown 6

figures≡ : figures ≡ 600409
figures≡ = refl

chainStep-nest-live-seed-absurd : grown 9 ≤ charge 9 → ⊥
chainStep-nest-live-seed-absurd h = ≤⇒≤ᵇ h
