-- ══════════════════════════════════════════════════════════════════
-- THE ARRIVAL CAP CANNOT BE RE-ENTERED AT A STEPPED CAP, so raising
-- the drain's queue conjuncts to the walk's level does not reach the
-- family that consumes them.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE ROUTE SAID.  The drain's queue conjuncts are refused at the
-- entry cap and hold at the walk's, so raise them; every lemma between
-- the queue and the arrival family is generic in its cap, so the raise
-- costs nothing but instantiating that family at the stepped cap
-- instead of the bare one, and ordering its answer under the index the
-- shelf already reports at.
--
-- WHY IT CANNOT WORK, AND IT IS THE ARRIVAL DENOMINATION AND NOT THE
-- STEP.  The arrival family does not answer at the cap it was asked
-- at: it answers at that cap stepped its own SIZE many times.  So a
-- bare cap of size S answers at S steps, while the same family entered
-- one level up answers at the STEPPED size many steps -- and the
-- stepped size is already better than the square of S.  The index the
-- shelf can offer against it is a count fixed by the program, so the
-- two sides move at different rates in the level and no index the
-- shelf can name catches up.
--
-- THE ROWS ARE THE TWO HALVES OF THAT.  The first takes the level and
-- the index both at one, which is the smallest instance that says
-- anything, since at level zero the step is the identity.  The second
-- keeps the level at one and spends twenty on the index -- far past
-- anything the count affords at this cap -- and the ordering is still
-- false, so the failure is the RATE and not a small-index artifact.
--
-- WHAT IS LEFT is the discipline the caps face beside this one keeps:
-- take the invariant at the stepped cap, report an increment, restate
-- at the SUM, with no arrival cap in the denomination at all.  That is
-- a restatement of the arrival family itself, not an instantiation of
-- it; `Refuted.Frame-Step-Compose` kills the other way around, and
-- `Refuted.Drain-Queue-Flat` is why the conjuncts cannot simply stay.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Arr-Cap-Step where

open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤-refl; m≤n+m)
open import Data.Product using (proj₁)

open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; frameStep; arrCapAt; _⊑ᶜ_)

-- the smallest cap this development admits.  Nothing turns on the
-- choice: the gap is a rate, so a larger cap widens it
cA : Caps
cA = caps 2 1 1

-- STATED WITH THE SIDE CONDITIONS THE REAL LEMMA WOULD CARRY -- a cap
-- the face admits, and an index at least the level -- so the
-- refutation reaches the conditioned form and not merely the bare one.
ArrCapStep : Set
ArrCapStep = ∀ (c : Caps) (Lv j : ℕ) → 2 ≤ Caps.cSize c → Lv ≤ j →
  arrCapAt (Caps.cSize (frameStep Lv c)) (frameStep Lv c) ⊑ᶜ frameStep j c

-- ONE LEVEL AND ONE INDEX: the arrival cap is entered at size ten and
-- so steps ten times from ten, against a flat cap of ten
arr-cap-step-absurd : ArrCapStep → ⊥
arr-cap-step-absurd pr = ≤⇒≤ᵇ (proj₁ (pr cA 1 1 ≤-refl ≤-refl))

-- AND TWENTY ON THE INDEX DOES NOT BUY IT, which is the row that makes
-- the finding about the rate: the index is spent far past the count
-- this cap affords and the ordering is false by the same arithmetic
arr-cap-step-wide-absurd : ArrCapStep → ⊥
arr-cap-step-wide-absurd pr = ≤⇒≤ᵇ (proj₁ (pr cA 1 20 ≤-refl (m≤n+m 1 19)))
