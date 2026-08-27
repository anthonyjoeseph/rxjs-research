-- ══════════════════════════════════════════════════════════════════
-- THE SCAN HEAD OF THE ARRIVAL-KEYED WALK, AT THE KEY THAT CHARGES A
-- SCRIPT — the same witness that refutes the reading which does not.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT MAKES THE ROWS LOAD-BEARING.  Both columns compute at the same
-- program, and the left one DOUBLES per delivered value: a step naming
-- its accumulator twice adds a level per fold, and the fold runs once
-- per value of the cold script.  A key that stood still would be
-- crossed by the fourth or fifth row, which is precisely what the
-- refutation of the written reading measures at this program.  So a
-- row fails exactly when the key fails to keep up, and nothing here is
-- upward-closed.
--
-- WHAT IS NOT COVERED.  One scripted slot, and a script of literal
-- naturals — a script of OBSERVABLE values would charge more on the key
-- side and deliver more on the left, and which side wins there is not
-- read here.  Nor is the interaction with a substituting slot: the
-- telescope below is scripted throughout, so the staged environment is
-- constant and does no work in these rows.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: subscribeE-nest-arr-scan @b3dbe3
module Probed.Scan-Arr-Clos-Key where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ; emptyᵉ; input;
         varᵗ; fstᵗ; strmᵗ; syncSizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Slot-Clos using (slotClos)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nestCapsOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

sync : ℕ → List ℕ
sync zero    = []
sync (suc k) = k ∷ sync k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (sync k) [])

deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input (fsuc fzero))))

prog : Closed Γ₂ (obs natᵗ)
prog = scanᵉ deepen (strmᵗ emptyᵉ) (input (fsuc fzero))

gas : Gas
gas = gasPad 400 g0

cap : Caps
cap = caps (syncSizeᵉ prog) 4000 4000

row : ℕ → ℕ × ℕ
row k =
  let sl = slots k
      r  = subscribeE gas prog root 0 0 (sched-init prog sl) (st-init prog)
  in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))
   , arrD (nestUnit prog sl) (nestDᵉ prog) (closSizeᵉ (slotClos sl) prog)

-- THE HEAD'S OWN PREMISES, pinned rather than assumed, so the rows are
-- not evidence about a region the statement grants nothing at.  `B` is
-- `nestDᵉ prog` exactly, so the depth premise holds by construction.
premises : (nestValOK? cap (obs (obs natᵗ)) prog ≡ true)
         × (nestCapsOK? cap (sched-init prog (slots 14)) (st-init prog) ≡ true)
premises = refl , refl

-- THE KEY NOW MOVES WITH THE SCRIPT, two units per value, against a
-- delivery that doubles -- so the grant doubles twice per value and
-- the margin widens rather than closing.
keys : ℕ × ℕ × ℕ × ℕ
keys = closSizeᵉ (slotClos (slots 0)) prog
     , closSizeᵉ (slotClos (slots 7)) prog
     , closSizeᵉ (slotClos (slots 13)) prog
     , closSizeᵉ (slotClos (slots 14)) prog

keys≡ : keys ≡ (12 , 26 , 38 , 40)
keys≡ = refl

fit0 : (proj₁ (row 0) ≤ᵇ proj₂ (row 0)) ≡ true
fit0 = refl

fit7 : (proj₁ (row 7) ≤ᵇ proj₂ (row 7)) ≡ true
fit7 = refl

fit13 : (proj₁ (row 13) ≤ᵇ proj₂ (row 13)) ≡ true
fit13 = refl

fit14 : (proj₁ (row 14) ≤ᵇ proj₂ (row 14)) ≡ true
fit14 = refl
