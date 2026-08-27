-- ══════════════════════════════════════════════════════════════════
-- A SHARED SLOT WHOSE DEFINITION FOLDS OVER A SCRIPTED ONE BELOW IT,
-- which is the composition of the two shapes that have each broken a
-- key on this face.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THE COMPOSITION IS NOT COVERED BY EITHER HALF.  The slot arm's
-- rows vary a definition and hold the telescope shared throughout, so
-- the key they exercise is built entirely from syntax.  The scan rows
-- vary a script and hold the arrival at the ROOT, so the key they
-- exercise is read once.  Here the script sits BELOW a shared slot:
-- the arrival's key has to reach through the reference AND read a
-- script at the far end of it, and it is the staged environment that
-- has to carry the second half to the first.
--
-- WHAT WOULD MAKE THE ROWS FAIL.  The definition is the same doubling
-- fold that refutes the reading which charges a script nothing, so the
-- delivered depth doubles per scripted value.  A key that reached
-- through the reference but flattened what it found there would stand
-- still while the left column doubled, and the rows would cross within
-- four values.  Both columns are pinned.
--
-- NOT COVERED: the two store conjuncts, which this shape leaves at
-- `0 ≤ _`, and a script of OBSERVABLE values.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeSharedSlot-nest-arr @891d01
module Probed.Shared-Slot-Script-Below where

open import Data.Bool using (T; true)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Data.Vec using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_; ofᵉ; scanᵉ; mergeAllᵉ; emptyᵉ;
         nat̂; input; strmᵗ; varᵗ; fstᵗ; inputsBelowᵉ)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator
  using (subscribeSharedSlot; splitBurst; root; sched-init; st-init; Path; _↠_;
  thru-outer; mergeAllᵒ)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)

Γₘ : Ctx 2
Γₘ = natᵗ ∷ obs natᵗ ∷ []

gas : Gas
gas = gasPad 400 g0

prog : Closed Γₘ natᵗ
prog = ofᵉ (nat̂ 0 ∷ [])

sync : ℕ → List ℕ
sync zero    = []
sync (suc j) = j ∷ sync j

-- the step names its accumulator twice, so one application doubles the
-- delivered depth -- the same fold that refutes a script-blind key
deepen : Fn Γₘ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input fzero)))

-- SLOT ONE's definition: fold the step over the script sitting at slot
-- zero, which is the reference the staged key has to reach through
defn : Closed Γₘ (obs natᵗ)
defn = scanᵉ deepen (strmᵗ emptyᵉ) (input fzero)

sl : (j : ℕ) → T (inputsBelowᵉ 1 defn) → Slots Γₘ
sl j ok fzero        = scripted (cold (sync j) [])
sl j ok (fsuc fzero) = shared defn {ok = ok}

κ : Path Γₘ (obs natᵗ) natᵗ
κ = thru-outer mergeAllᵒ 0 ↠ root

burstOf : (j : ℕ) (ok : T (inputsBelowᵉ 1 defn)) → ℕ
burstOf j ok =
  nestDᵛˢ (proj₁ (splitBurst {A = Val Γₘ natᵗ}
    (proj₁ (subscribeSharedSlot gas (fsuc fzero) defn κ 0 0
              (sched-init prog (sl j ok)) (st-init prog)))))

GOf : (j : ℕ) (ok : T (inputsBelowᵉ 1 defn)) → ℕ
GOf j ok = arrD (nestUnit prog (sl j ok)) 0
             (suc (closSizeᵉ (slotClos (sl j ok)) defn))

-- THE KEY REACHES THROUGH THE REFERENCE AND READS THE SCRIPT AT THE FAR
-- END OF IT, which is the one thing these rows exist to see: the
-- definition is the SAME term at every row, so any movement here is the
-- staged environment carrying the script inward.
keys : ℕ
keys = suc (closSizeᵉ (slotClos (sl 0 tt)) defn)
     + 100 * suc (closSizeᵉ (slotClos (sl 4 tt)) defn)
     + 10000 * suc (closSizeᵉ (slotClos (sl 8 tt)) defn)

keys≡ : keys ≡ 292113
keys≡ = refl

fit0 : (burstOf 0 tt ≤ᵇ GOf 0 tt) ≡ true
fit0 = refl

fit4 : (burstOf 4 tt ≤ᵇ GOf 4 tt) ≡ true
fit4 = refl

fit8 : (burstOf 8 tt ≤ᵇ GOf 8 tt) ≡ true
fit8 = refl
