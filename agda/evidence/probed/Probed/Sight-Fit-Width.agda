-- THE ENTRY FOLD'S GRANT, RUN AGAINST THE FAMILY THAT KILLS ITS
-- PREDECESSOR.  A grant read as a tower over `syncSizeᵉ` alone is
-- blind to a script: a doubling `scanᵉ` over a cold script crosses
-- such a grant between twelve and thirteen script values, and both
-- forms are computed here so the crossing is a column rather than a
-- claim.  The fold's own currency is `nestB`, whose exponent carries a
-- WIDTH beside the size base, and these rows ask whether that width
-- closes the crossing.
--
-- THE WIDTH IS READ AT THE BURST AND NOT AT `descW`, WHICH IS WHAT
-- MAKES THE ROWS LOAD-BEARING RATHER THAN UNFALSIFIABLE.  `descW` is
-- sealed, so no row can evaluate it; and it is the SMALLEST legal
-- witness that matters, since the width sits in the grant and a larger
-- one only weakens the claim.  The burst count is a LOWER bound on
-- `descW` -- the head clause of every arm joins it -- so a grant read
-- at the burst count is under the grant read at any legal `W`, and a
-- row that holds here holds there.
--
-- AND THE GRANT IS WRITTEN OUT RATHER THAN CALLED, because `nestB` is
-- sealed for the reason every caps family is.  The expression below is
-- its body at a size base of one, which is the strongest reading: the
-- family is monotone in the base, so the run's own size -- which is
-- what the statement takes -- widens into these rows, never out.
-- TARGET: subscribeE-fit @d8da3b
module Probed.Sight-Fit-Width where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Val; natᵗ; obs; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (Stream; Path; splitEvents; splitBurst; subscribeE; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; slotWrapSum; slotWrapBSum; nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)
open import Verify-Budget-Sufficient.Sighted-Fit using (subscribeE-fit)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Scan-Burst-Nest using (prog; slots; gas)
open import Probed.Apparatus using (Confirms; fitB-tower; streamFitG-floor)

burstVals : ∀ {t} → Stream Γ₂ t → List (Val Γ₂ t)
burstVals []                       = []
burstVals {t = t} (em ∷ ems) =
  proj₁ (splitEvents {A = Val Γ₂ t} (InstEmit.events em)) ++ burstVals ems

κ₀ : Path Γ₂ (obs natᵗ) (obs natᵗ)
κ₀ = root

runAt : ℕ → Stream Γ₂ (obs natᵗ)
runAt N = proj₁ (subscribeE gas prog κ₀ 0 0
                   (sched-init prog (slots N)) (st-init prog))

-- what the run actually delivers -- the refuted side, unchanged
deliv : ℕ → ℕ
deliv N = nestDᵛˢ (burstVals (runAt N))

-- the width the burst itself exhibits, a lower bound on `descW`
wid : ℕ → ℕ
wid N = length (proj₁ (splitBurst {A = Val Γ₂ (obs natᵗ)} (runAt N)))

-- the grant as it stands, and as the repair would read it
grantOld : ℕ → ℕ
grantOld N = 2 ^ syncSizeᵉ prog * (pathNestD κ₀ + nestDᵉ prog)
           + 2 * slotWrapSum (slots N)

grantNew : ℕ → ℕ
grantNew N =
  ((2 ^ 1) ^ suc (wid N)) ^ syncSizeᵉ prog
    * ((pathNestD κ₀ + nestDᵉ prog)
        + suc (syncSizeᵉ prog) * nestUnit prog (slots N))
  + 2 * slotWrapBSum prog (slots N) (wid N)

-- THE THREE FIGURES THE ROWS TURN ON, and the exponent is the finding:
-- the delivered side doubles per script value while `syncSizeᵉ` does
-- not move, which is the refutation restated as numbers.
figures : ℕ
figures = syncSizeᵉ prog
        + 100 * wid 12 + 10000 * wid 13
        + 1000000 * deliv 12 + 10000000000 * deliv 13

figures≡ : figures ≡ 81914095131212
figures≡ = refl

-- the crossing, in the form it is refuted at: the grant does not move
-- between the two script lengths and the delivery doubles past it
oldRow : List Bool
oldRow = (deliv 12 ≤ᵇ grantOld 12) ∷ (deliv 13 ≤ᵇ grantOld 13) ∷ []

oldRow≡ : oldRow ≡ true ∷ false ∷ []
oldRow≡ = refl

-- AND THE REPAIR AT THE SAME THREE LENGTHS, one of them past the
-- crossing and one further still, so the row is not read at the edge
-- the old grant happened to sit on
newRow : List Bool
newRow = (deliv 12 ≤ᵇ grantNew 12)
       ∷ (deliv 13 ≤ᵇ grantNew 13)
       ∷ (deliv 16 ≤ᵇ grantNew 16) ∷ []

newRow≡ : newRow ≡ true ∷ true ∷ true ∷ []
newRow≡ = refl

----------------------------------------------------------------------
-- THE TIE, AT THE SAME THREE SCRIPT LENGTHS THE ROWS ABOVE READ.  Its
-- type is the statement applied at this file's own point, so the
-- columns above stop being a hand-written grant standing beside the
-- postulate and become the margin reading of the grant actually spent.
--
-- WHAT IT STANDS ON, since the grant is sealed and cannot be a
-- numeral.  The caps family exports a base and a per-level doubling
-- bought by a unit of the descent's size; iterating them at a key of
-- one gives a FLOOR that computes -- four to the arrival's sync size,
-- times the depth the grant is opened at.  That floor is strictly
-- above the width-free grant the refutation crosses, which is why the
-- rows reach past the crossing rather than stopping at it.
--
-- LOAD-BEARING at exactly the axis this file exists for: the delivered
-- side doubles per script value while the floor does not move, so a
-- long enough script crosses even this floor.  What is NOT covered is
-- the burst WIDTH, which the floor drops entirely and the real grant
-- carries in its exponent -- so these rows say nothing about the axis
-- the repair was made on, and the columns above are what read it.
-- Both premises are left standing and unread.
----------------------------------------------------------------------

floorAt : ℕ
floorAt = (2 ^ suc 1) ^ syncSizeᵉ prog * (pathNestD κ₀ + nestDᵉ prog)

tie12 : Confirms
  (subscribeE-fit gas 2 (wid 12) prog κ₀ 0 0
     (sched-init prog (slots 12)) (st-init prog))
tie12 _ _ =
  streamFitG-floor 2 (slots 12) floorAt _ (pathNestD κ₀) (obs natᵗ) (runAt 12)
    (fitB-tower prog (slots 12) 2 (wid 12)
       (pathNestD κ₀ + nestDᵉ prog) (syncSizeᵉ prog) 1 (≤ᵇ⇒≤ _ _ tt))
    tt

tie13 : Confirms
  (subscribeE-fit gas 2 (wid 13) prog κ₀ 0 0
     (sched-init prog (slots 13)) (st-init prog))
tie13 _ _ =
  streamFitG-floor 2 (slots 13) floorAt _ (pathNestD κ₀) (obs natᵗ) (runAt 13)
    (fitB-tower prog (slots 13) 2 (wid 13)
       (pathNestD κ₀ + nestDᵉ prog) (syncSizeᵉ prog) 1 (≤ᵇ⇒≤ _ _ tt))
    tt

tie16 : Confirms
  (subscribeE-fit gas 2 (wid 16) prog κ₀ 0 0
     (sched-init prog (slots 16)) (st-init prog))
tie16 _ _ =
  streamFitG-floor 2 (slots 16) floorAt _ (pathNestD κ₀) (obs natᵗ) (runAt 16)
    (fitB-tower prog (slots 16) 2 (wid 16)
       (pathNestD κ₀ + nestDᵉ prog) (syncSizeᵉ prog) 1 (≤ᵇ⇒≤ _ _ tt))
    tt
