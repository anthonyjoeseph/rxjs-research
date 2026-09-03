-- THE SUBSCRIBE DESCENT'S NEST BOUND, ON THE FAMILY THAT REFUTED ITS
-- PREVIOUS FORM.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-nest-scan @b2e74d
--
-- WHAT IS BEING TESTED, AND IT IS THE AXIS AND NOT THE PROGRAM.  The
-- statement's factor is now a power in the BURST the descent hands
-- back, because a stored step function is refolded once per value of
-- one.  `Refuted.Scan-Burst-Nest` is where the un-indexed form died, at
-- a burst of fourteen from a cold script; these rows are that same
-- witness read against the indexed form.
--
-- HOW THE FAMILY WORKS.  A `scanᵉ` whose step function names its
-- accumulator in the two additive slots an inner `scanᵉ` offers is
-- written ONCE and applied once per value of the burst, so the
-- delivered depth doubles per value while the syntax the grant is read
-- off does not move at all.  The burst comes from a COLD SCRIPT: a
-- script is invisible to `sizeᵉ` and `slotNest` reads zero at every
-- scripted slot, which is what made it free on both sides.
--
-- THE PREMISES ARE PINNED AND NOT ASSUMED.  `B` is `nestDᵉ prog`
-- exactly, the store is `st-init` so its `nodesMax` is zero and the
-- store premise holds at every index, and the size cap is the
-- program's own -- the smallest `nestValOK?` admits.  The burst premise
-- is met by the measured length rather than by a chosen `W`.
--
-- NO ROW HERE COULD HAVE FAILED, AND THAT IS THE FINDING RATHER THAN A
-- DEFECT IN THE ROWS.  The demand rises by ONE bit per value of the
-- burst and the grant by `cSize` -- twelve on this program -- so once
-- the index is the burst, this family is carried with eleven bits per
-- value unspent.  That is a statement about the CURRENCY: the axis that
-- refuted the flat form cannot refute the indexed one, because the two
-- now move together and the indexed one moves faster.  What the rows
-- buy is the contrast pinned as numbers -- the same program, green
-- here and absurd there.
--
-- WHAT IS NOT COVERED.  The next crossing of this family sits near a
-- script of twenty-six, where the accumulator is some sixty-seven
-- million nodes; fourteen is already a quarter of a million and four
-- seconds, so the geometry puts it out of reach and the second
-- crossing is unmeasured.  Nothing here varies the store, the path or
-- the cap.  Nor the LEVEL: the statement reports a level and bounds it
-- by the caps count at the descent's depth, and every row here reads
-- the grant at level zero, where the stepped cap is the entry cap
-- outright.  So the bound conjunct is untouched, and what these rows
-- cover is the three that sit beside it.  Nor the CEILING the statement
-- now takes as a premise, which is an implication about every level the
-- descent could reach and is discharged by nothing a row computes.
module Probed.Scan-Burst-Nest where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤ᵇ⇒≤; m≤n⊔m)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ; emptyᵉ; input;
         varᵗ; fstᵗ; strmᵗ; syncSizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init; EvalSt)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; nestValOK?)
open import Verify-Budget-Sufficient.Nest-Cap using (nestB-base)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; subscribeE-nest-scan)
open import Refuted.Demand-Programs using (Γ₂)
open import Probed.Apparatus using (Confirms; nodeNestAt≤max)

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

burst : ℕ → ℕ
burst k =
  length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)}
            (proj₁ (subscribeE gas prog root 0 0
                      (sched-init prog (slots k)) (st-init prog)))))

delivered : ℕ → ℕ
delivered k =
  let r = subscribeE gas prog root 0 0 (sched-init prog (slots k)) (st-init prog)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))

-- the state the descent leaves, named because the `∀ (k : NodeId)`
-- conjunct reads it under an already-reduced `lookupNode` and the
-- unifier has nothing left to solve it from
resSt : (k : ℕ) → EvalSt prog
resSt k = proj₂ (proj₂ (subscribeE gas prog root 0 0
                         (sched-init prog (slots k)) (st-init prog)))

-- the indexed grant, at the burst the row actually hands back
charged : ℕ → ℕ
charged k =
  (2 ^ Caps.cSize cap) ^ suc (burst k) * (nestDᵉ prog + nestUnit prog (slots k))

premises : (nestValOK? cap (obs (obs natᵗ)) prog ≡ true)
         × (capsOK? cap (sched-init prog (slots 14)) (st-init prog) ≡ true)
premises = refl , refl

-- the burst premise, met by measurement
scanBursts : ℕ × ℕ
scanBursts = burst 13 , burst 14

scanBursts≡ : scanBursts ≡ (13 , 14)
scanBursts≡ = refl

scanEmits : ℕ × ℕ
scanEmits = delivered 13 , delivered 14

scanEmits≡ : scanEmits ≡ (8191 , 16383)
scanEmits≡ = refl

fits₁₃ : (delivered 13 ≤ᵇ charged 13) ≡ true
fits₁₃ = refl

fits₁₄ : (delivered 14 ≤ᵇ charged 14) ≡ true
fits₁₄ = refl

-- THE CONTRAST, AND IT IS THE WHOLE POINT OF THE FILE.  At index zero
-- the grant is the flat form, and the flat form is the one
-- `Refuted.Scan-Burst-Nest` kills -- pinned here as a `false` beside
-- the greens above so the two readings sit at the same program.
flat : ℕ → ℕ
flat k = (2 ^ Caps.cSize cap) ^ 1 * (nestDᵉ prog + nestUnit prog (slots k))

flatFigs : ℕ × ℕ
flatFigs = flat 14 , delivered 14

flat≡ : flatFigs ≡ (12288 , 16383)
flat≡ = refl

flat-fails : (delivered 14 ≤ᵇ flat 14) ≡ false
flat-fails = refl

----------------------------------------------------------------------
-- THE TIE, at this file's own program and script.  The type is
-- generated from the statement, so what the row asserts moves with any
-- restatement of it rather than with a predicate copied down here.
--
-- WHAT THE ROW CHOOSES AND WHAT IT LEAVES STANDING.  It chooses the
-- point -- program, script, entry state, and the three free numbers
-- `d`, `W` and `B` -- and reports the level at ZERO, which is the
-- entry level, so both level conjuncts are `z≤n`.  Every premise is
-- left STANDING and the body reads none: three of them name `capsAt`
-- or `nestCapAt`, and a row that discharged those would report on the
-- seal rather than on the descent.  Unasked, the claim is the
-- conclusion with the caps invariant not assumed.
--
-- AND `B` IS WHAT MAKES THE SEALED CONCLUSION REACHABLE AT ALL.
-- `nestB` is sealed for cost, so `G` reduces at no point and no
-- numeral instantiates the right side.  But `B` is a parameter the row
-- picks and `nestB-base` puts it under `G` unconditionally, so setting
-- `B` to the run's own delivered figure turns all three bound
-- conjuncts into one numeric comparison the evaluator settles.  The
-- last of them quantifies over every node id, which no row can
-- enumerate; `nodeNestAt≤max` reads it back through the `nodesMax`
-- figure the conjunct beside it already computes.
----------------------------------------------------------------------

tie₁₃ : Confirms
  (subscribeE-nest-scan cap 0 (slots 13) (delivered 13) 0 0 gas
     deepen (strmᵗ emptyᵉ) (input (fsuc fzero)) root 0 0
     (sched-init prog (slots 13)) (st-init prog))
tie₁₃ _ _ _ _ _ _ _ _ _ _ _ _ =
  0 , z≤n , z≤n
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) base
  , ≤-trans (≤-trans (≤ᵇ⇒≤ _ _ tt) base) (m≤n⊔m _ _)
  , (λ j → ≤-trans (nodeNestAt≤max j (resSt 13))
             (≤-trans (≤-trans (≤ᵇ⇒≤ _ _ tt) base) (m≤n⊔m _ _)))
  where
  base = nestB-base (Caps.cSize (frameStep 0 cap)) 0
                    (nestUnit prog (slots 13)) (delivered 13) (syncSizeᵉ prog)

tie₁₄ : Confirms
  (subscribeE-nest-scan cap 0 (slots 14) (delivered 14) 0 0 gas
     deepen (strmᵗ emptyᵉ) (input (fsuc fzero)) root 0 0
     (sched-init prog (slots 14)) (st-init prog))
tie₁₄ _ _ _ _ _ _ _ _ _ _ _ _ =
  0 , z≤n , z≤n
  , ≤-trans (≤ᵇ⇒≤ _ _ tt) base
  , ≤-trans (≤-trans (≤ᵇ⇒≤ _ _ tt) base) (m≤n⊔m _ _)
  , (λ j → ≤-trans (nodeNestAt≤max j (resSt 14))
             (≤-trans (≤-trans (≤ᵇ⇒≤ _ _ tt) base) (m≤n⊔m _ _)))
  where
  base = nestB-base (Caps.cSize (frameStep 0 cap)) 0
                    (nestUnit prog (slots 14)) (delivered 14) (syncSizeᵉ prog)
