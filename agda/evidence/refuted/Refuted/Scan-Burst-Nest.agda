-- ══════════════════════════════════════════════════════════════════
-- A SUBSCRIPTION'S BURST IS NOT PAID FOR BY THE SUBSCRIBED VALUE'S
-- SIZE, so charging the descent `2 ^ cSize` once is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  A subscription of `o` deepens what it emits
-- and what it installs by at most `2 ^ cSize` times the depth it was
-- handed, with the cap tied to `o` itself by a `valCaps?` premise -- so
-- the exponent is at least `sizeᵉ o`, and two to a program's size is
-- the ceiling on how many times its syntax can name a payload.
--
-- WHY IT READ AS SAFE, AND WHAT THAT READING MISSED.  Every family that
-- had been instantiated against it buys its depth by STACKING FRAMES: a
-- `mapᵉ` naming its payload twice doubles the emitted depth and costs
-- seven size units doing it, so the grant outruns the demand six bits to
-- one and the margin widens with every layer.  A `scanᵉ` inverts that
-- ratio exactly.  Its step function is written ONCE and applied once per
-- value of the burst it is fed, so a step that doubles its accumulator
-- doubles the delivered depth PER VALUE while the size the cap is read
-- off does not move.
--
-- AND THE BURST IS FREE, which is the half that makes the gap unbounded
-- rather than merely tight.  The values come from a COLD SCRIPT: they
-- live in the slot telescope, `sizeᵉ` cannot see them, and `slotNest` is
-- zero at every scripted slot by construction, so they are charged to
-- neither the exponent nor the base.  Fourteen of them deliver 16383
-- against a budget of 12288, and each further value doubles the left
-- side while the right side stands still -- so no constant, no larger
-- `B` and no wider cap repairs it.
--
-- WHAT DIES AND WHAT DOES NOT.  The bound is not false -- one
-- substitution costs `2 ^ sizeᵗ fn` and `applyFn-nest` proves it.  What
-- dies is spending that factor ONCE for a whole descent.  The frame face
-- already carries the right currency: `stepFrame-nodes` charges
-- `frameNestF f ^ W` and `scanVals-nest` charges `(2 ^ sizeᵗ fn) ^ W`,
-- both powers in the BURST WIDTH, and the descent's flat form was the
-- one statement of the family without one.  The repair is therefore a
-- power in a width, and the width has to be one the caps or the slots
-- actually bound -- which `cWid` does NOT: `pWᵛ` reads 1 at this program
-- and `entryCeil` reads 8, against a burst measured at fourteen, because
-- `slotCeil` is zero at a scripted slot.  `slotsSize` is the quantity
-- that does see a script.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Burst-Nest where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ; emptyᵉ; input;
         varᵗ; fstᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

-- k values delivered synchronously at subscribe, off slot 1
sync : ℕ → List ℕ
sync zero    = []
sync (suc k) = k ∷ sync k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (sync k) [])

-- THE STEP FUNCTION NAMES ITS ACCUMULATOR TWICE, in the two additive
-- slots an inner `scanᵉ` offers -- its own seed and its own step -- so
-- one application doubles the accumulator's depth and adds the single
-- layer the `mergeAllᵉ` wrapper costs.  Eight size units, paid once
-- however long the burst is.
deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input (fsuc fzero))))

prog : Closed Γ₂ (obs natᵗ)
prog = scanᵉ deepen (strmᵗ emptyᵉ) (input (fsuc fzero))

gas : Gas
gas = gasPad 400 g0

-- the SIZE cap is the value's own -- the smallest the `valCaps?` premise
-- admits, so there is no slack in the choice.  The width and registry
-- caps are given room instead of tightened, which only makes the
-- premises EASIER and the refutation stronger.
cap : Caps
cap = caps (sizeᵉ prog) 4000 4000

row : ℕ → ℕ × ℕ
row k =
  let sl = slots k
      r  = subscribeE gas prog root 0 0 (sched-init prog sl) (st-init prog)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (proj₁ r)))
   , 2 ^ Caps.cSize cap * (nestDᵉ prog + nestUnit prog sl)

-- THE PREMISES, PINNED RATHER THAN ASSUMED.  `B` is `nestDᵉ prog`
-- exactly and the store is `st-init`, whose `nodesMax` is zero, so the
-- depth and store premises hold by construction; these two are the ones
-- that could have failed.
premises : (valCaps? cap (slots 14) (obs (obs natᵗ)) prog ≡ true)
         × (capsOK? cap (sched-init prog (slots 14)) (st-init prog) ≡ true)
premises = refl , refl

-- the burst really is fourteen values wide, in ONE subscribe frame
burst≡14 : length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)}
             (proj₁ (subscribeE gas prog root 0 0
                       (sched-init prog (slots 14)) (st-init prog))))) ≡ 14
burst≡14 = refl

delivered≡16383 : proj₁ (row 14) ≡ 16383
delivered≡16383 = refl

charged≡12288 : proj₂ (row 14) ≡ 12288
charged≡12288 = refl

-- AND THE ROW BELOW IT STILL HOLDS, which is what makes this a crossing
-- and not a scale error: at thirteen values the descent delivers 8191
-- against the same 12288.  The budget is the SAME number in both rows,
-- because the script is charged to neither side of it.
delivered₁₃≡8191 : proj₁ (row 13) ≡ 8191
delivered₁₃≡8191 = refl

charged₁₃≡12288 : proj₂ (row 13) ≡ 12288
charged₁₃≡12288 = refl

subscribeE-nest-burst-absurd : proj₁ (row 14) ≤ proj₂ (row 14) → ⊥
subscribeE-nest-burst-absurd h = ≤⇒≤ᵇ h
