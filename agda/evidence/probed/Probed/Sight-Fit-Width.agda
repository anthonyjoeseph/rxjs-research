-- THE PROPOSED REPAIR, RUN AGAINST THE FAMILY THAT KILLED THE CURRENT
-- FORM.  The entry fold prices a subscription's emitted values at a
-- tower over `syncSizeᵉ`, and that exponent is blind to a script: the
-- refutation drives a doubling `scanᵉ` over a cold script and crosses
-- the grant between twelve and thirteen script values.  The repair
-- named in the statement's own header moves the fold into the `nestB`
-- currency, whose exponent carries a WIDTH beside the size cap.  These
-- rows ask whether that width closes the crossing.
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
-- family is monotone in the base, so a consumer at any real cap widens
-- into these rows rather than out of them.
-- TARGET: subscribeE-fit @48e936
module Probed.Sight-Fit-Width where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Nat using (ℕ; suc; _+_; _*_; _^_; _≤ᵇ_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEmit)
open import Rx.Exp using (Val; natᵗ; obs; syncSizeᵉ)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (Stream; Path; splitEvents; splitBurst; subscribeE; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD; slotWrapSum; nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Scan-Burst-Nest using (prog; slots; gas)

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
  + 2 * slotWrapSum (slots N)

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
