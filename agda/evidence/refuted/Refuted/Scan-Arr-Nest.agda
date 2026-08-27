-- ══════════════════════════════════════════════════════════════════
-- THE ARRIVAL-KEYED SCAN HEAD IS FALSE AT A SCRIPTED SOURCE, and the
-- key that repaired the SLOT head does not repair this one.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A subscription of `scanᵉ f z b` delivers
-- nesting inside `arrD U B m`, with `m` the arrival's CLOSURE size --
-- the written size with each slot reference replaced by its definition.
-- That key is what carries the shared-slot head, where the arrival's
-- own definition is the thing being descended into.
--
-- WHY IT DOES NOT CARRY THIS ONE.  A closure expands a SUBSTITUTING
-- slot and nothing else: at a SCRIPTED slot the definition is a value
-- list, not an expression, and the measure reads one there -- the same
-- one the written size reads.  So the key is fixed the moment the
-- program is written, while a scan applied once per value of a cold
-- script doubles the delivered depth per value.  The script is charged
-- to neither the exponent nor the base.
--
-- WHAT DIES AND WHAT DOES NOT.  A longer key does not repair it and
-- neither does a larger `B`: both sides are read at the SAME program,
-- and only the script grows.  What the rows leave open is the shape of
-- the repair, which has to be a term in a width the SLOTS bound --
-- the same conclusion the burst face reached at this witness, arriving
-- now at the face that was supposed to be immune to it.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Arr-Nest where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
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
open import Verify-Budget-Sufficient.Nest-Cap using (arrD)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; nestCapsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (nestValOK?)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

-- k values delivered synchronously at subscribe, off slot 1
sync : ℕ → List ℕ
sync zero    = []
sync (suc k) = k ∷ sync k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (sync k) [])

-- the step names its accumulator twice, in the two additive slots an
-- inner `scanᵉ` offers, so one application doubles the delivered depth
deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input (fsuc fzero))))

prog : Closed Γ₂ (obs natᵗ)
prog = scanᵉ deepen (strmᵗ emptyᵉ) (input (fsuc fzero))

gas : Gas
gas = gasPad 400 g0

-- the SIZE cap is the arrival's own written size, the smallest the
-- admissibility premise takes, so there is no slack in the choice
cap : Caps
cap = caps (syncSizeᵉ prog) 4000 4000

row : ℕ → ℕ × ℕ
row k =
  let sl = slots k
      r  = subscribeE gas prog root 0 0 (sched-init prog sl) (st-init prog)
  in nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))
   , arrD (nestUnit prog sl) (nestDᵉ prog) (closSizeᵉ (slotClos sl) prog)

-- THE PREMISES, PINNED RATHER THAN ASSUMED.  `B` is `nestDᵉ prog`
-- exactly, so the depth premise holds by construction; the two that
-- could have failed are these.
premises : (nestValOK? cap (obs (obs natᵗ)) prog ≡ true)
         × (nestCapsOK? cap (sched-init prog (slots 14)) (st-init prog) ≡ true)
premises = refl , refl

-- the burst really is fourteen values wide, in ONE subscribe frame
burst≡14 : length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)}
             (proj₁ (subscribeE gas prog root 0 0
                       (sched-init prog (slots 14)) (st-init prog))))) ≡ 14
burst≡14 = refl

-- AND THE KEY DOES NOT MOVE WITH IT, which is the whole finding: the
-- closure of a scripted slot is one, so the arrival reads the same
-- size at every script length.
keys≡ : closSizeᵉ (slotClos (slots 0)) prog
      ≡ closSizeᵉ (slotClos (slots 14)) prog
keys≡ = refl

delivered≡ : proj₁ (row 14) ≡ 16383
delivered≡ = refl

charged≡ : proj₂ (row 14) ≡ 6144
charged≡ = refl

-- AND THE ROW BELOW IT STILL HOLDS, which is what makes this a crossing
-- and not a scale error: at thirteen values the descent delivers 8191
-- against the same charge.  The budget is the SAME number in both rows,
-- because the script is charged to neither side of it.
delivered₁₃≡ : proj₁ (row 13) ≡ 8191
delivered₁₃≡ = refl

charged₁₃≡ : proj₂ (row 13) ≡ 6144
charged₁₃≡ = refl

subscribeE-nest-arr-scan-absurd : proj₁ (row 14) ≤ proj₂ (row 14) → ⊥
subscribeE-nest-arr-scan-absurd h = ≤⇒≤ᵇ h
