-- THE SEMANTIC BURST AGAINST THE SYNTACTIC PAYLOAD COUNT, which is the
-- one leaf left under the descent's ceiling and the first leaf on that
-- face either of whose sides could be instantiated at all.
--
-- WHAT IS RESTATED AND WHY.  `burstW` is `abstract`, so no probe can
-- apply it; these rows compute its BODY -- the split of a real
-- subscribe's emission stream -- against `outWⱽ` at the same slots.
-- That is a restatement of the measure and not of the claim: the body
-- is the seal's whole content at this name.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: burst-outW @3c7e84
module Probed.Burst-OutW where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; ofᵉ; emptyᵉ; takeᵉ; mergeAllᵉ; switchAllᵉ; μᵉ; varᵉ; deferᵉ; input; nat̂;
  strmᵗ)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Refuted.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 1 1 2

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

-- the two sides at the ROOT frame
lhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
lhs {t} e =
  length (proj₁ (splitBurst {A = Val Γ₂ t}
    (proj₁ (subscribeE gasBig e root 0 0 (sched-init e slots) (st-init e)))))

rhs : ∀ {t} (e : Closed Γ₂ t) → ℕ
rhs e = outWⱽ 2 [] slots e

p-of : Closed Γ₂ natᵗ
p-of = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

p-empty : Closed Γ₂ natᵗ
p-empty = emptyᵉ

p-take0 : Closed Γ₂ natᵗ
p-take0 = takeᵉ (nat̂ 0) p-of

p-defer : Closed Γ₂ natᵗ
p-defer = deferᵉ p-of

p-script : Closed Γ₂ natᵗ
p-script = input (fsuc fzero)

p-share : Closed Γ₂ natᵗ
p-share = input fzero

p-merge : Closed Γ₂ natᵗ
p-merge = mergeAllᵉ nothing
            (ofᵉ (strmᵗ p-of ∷ strmᵗ p-of ∷ []))

-- THE μ HEAD, whose body reaches its own variable only from under a
-- defer -- the shape the ceiling's whole design turns on.  A frame at
-- a μ subscribes the UNFOLDING; the reading is of the body.
p-mu : Closed Γ₂ natᵗ
p-mu = μᵉ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (deferᵉ (varᵉ (here refl)))
                 ∷ strmᵗ (ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ [])) ∷ [])))

p-switch : Closed Γ₂ natᵗ
p-switch = switchAllᵉ (ofᵉ (strmᵗ p-of ∷ strmᵗ p-of ∷ []))

readout : List ℕ
readout = lhs p-of ∷ rhs p-of
        ∷ lhs p-empty ∷ rhs p-empty
        ∷ lhs p-take0 ∷ rhs p-take0
        ∷ lhs p-defer ∷ rhs p-defer
        ∷ lhs p-script ∷ rhs p-script
        ∷ lhs p-share ∷ rhs p-share
        ∷ lhs p-merge ∷ rhs p-merge
        ∷ lhs p-mu ∷ rhs p-mu
        ∷ lhs p-switch ∷ rhs p-switch
        ∷ []

-- THE ROWS, `lhs` then `rhs` at each program.  THREE ARE TIGHT and
-- those are the load-bearing ones: `ofᵉ` at 3, `mergeAllᵉ` at 6 and
-- `switchAllᵉ` at 6 are equalities, so any payload the frame emits
-- beyond the reading would refute the claim outright -- and the two
-- `*All` heads are where the reading is a PRODUCT, which is the only
-- place it could be under-counted.  The `takeᵉ 0`, scripted and shared
-- rows carry slack and are DEGENERATE on the failure axis: nothing
-- they could report would fail.  The defer row is neither -- it reads
-- 0 against 0, and it is the row the whole ceiling rests on, since a
-- single payload delivered under a defer would refute both this and
-- the ceiling's right to stop there.
readout≡ : readout ≡ 3 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 3 ∷ 0 ∷ 0 ∷ 0 ∷ 1
                   ∷ 1 ∷ 2 ∷ 6 ∷ 6 ∷ 2 ∷ 4 ∷ 6 ∷ 6 ∷ []
readout≡ = refl
