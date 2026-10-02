-- THE SIMULATION AT THREE FIRST-ORDER PROGRAMS AND THEIR TIMED
-- TRANSLATIONS, AT FUEL 3: values agree position by position, decided,
-- and the stamps are an injective renaming of the plain run's arrivals,
-- pinned by `refl` under a shift.  Fuel 3 is past every run's
-- completion, so a later arrival would add nothing.
--
-- LOAD-BEARING where two values are stamped: `two-arrivals` (two
-- arrivals, so one shared stamp fails the injective renaming) and
-- `of-two` (both at the subscription, so a split stamp fails it), and
-- every timed row, whose END item must share its last value's arrival.
-- `take-one` plain stamps one value and is DEGENERATE for the stamps.
-- TARGET: simulation @45314e
module Probed.Simulation where

open import Data.Unit using (tt)
open import Data.Nat using (_≟_; _+_)
open import Data.Nat.Properties using (+-cancelʳ-≡)
open import Data.Product using (_,_; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Binary.Pointwise.Properties using (decidable)
open import Relation.Nullary.Decidable using (Dec; yes; no; toWitness; _×-dec_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ctx; Val; natᵗ)
open import SExp.Syntax using (plainᵗ)
open import Timed.Translation using (timed; timedSlots; itemᵗ)
open import Simulation.Statement using (simulation; Agrees)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

-- `Agrees` at a timed item of `natᵗ`, decided
item? : ∀ {n m} {Γ′ : Ctx m} {Γ : Ctx n} (v : Val Γ′ (plainᵗ (itemᵗ natᵗ))) (w : Val Γ (itemᵗ natᵗ))
      → Dec (Agrees Γ′ Γ (itemᵗ natᵗ) v w)
item? (p , inj₁ a) (q , inj₁ b) = decidable _≟_ p q ×-dec (a ≟ b)
item? (p , inj₂ _) (q , inj₂ _) = decidable _≟_ p q ×-dec yes refl
item? (_ , inj₁ _) (_ , inj₂ _) = no λ ()
item? (_ , inj₂ _) (_ , inj₁ _) = no λ ()

_ : Confirms (simulation (κᵖ take-one) 3 (Point.prog take-one) (insᵖ take-one))
_ = toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt ,
    (_+ 8) , (λ {a} {b} → +-cancelʳ-≡ 8 a b) , refl

_ : Confirms (simulation (κᵖ two-arrivals) 3 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt ,
    (_+ 7) , (λ {a} {b} → +-cancelʳ-≡ 7 a b) , refl

_ : Confirms (simulation (κᵖ of-two) 3 (Point.prog of-two) (insᵖ of-two))
_ = toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt ,
    (_+ 5) , (λ {a} {b} → +-cancelʳ-≡ 5 a b) , refl

_ : Confirms (simulation (κᵖ take-one) 3 (timed (κᵖ take-one) (Point.prog take-one))
                         (timedSlots (insᵖ take-one)))
_ = toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt ,
    (_+ 14) , (λ {a} {b} → +-cancelʳ-≡ 14 a b) , refl

_ : Confirms (simulation (κᵖ two-arrivals) 3 (timed (κᵖ two-arrivals) (Point.prog two-arrivals))
                         (timedSlots (insᵖ two-arrivals)))
_ = toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt ,
    (_+ 9) , (λ {a} {b} → +-cancelʳ-≡ 9 a b) , refl

_ : Confirms (simulation (κᵖ of-two) 3 (timed (κᵖ of-two) (Point.prog of-two))
                         (timedSlots (insᵖ of-two)))
_ = toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt ,
    (_+ 5) , (λ {a} {b} → +-cancelʳ-≡ 5 a b) , refl
