-- THE SIMULATION'S TWO LEAVES AT FOUR FIRST-ORDER PROGRAMS AND THE
-- TIMED TRANSLATIONS OF TWO, ONE ARRIVAL AT A TIME THROUGH FUEL 3: each
-- plain slice's values agree with the impl slice the fuel map sends it
-- to, decided, the impl slices it skips are empty, and each impl slice's
-- stamps are one instant, an injective function of the arrival, pinned
-- under a shift.  Fuel 3 is past every plain run's completion.
--
-- LOAD-BEARING for the values at every slice, the empty ones included:
-- the elaborated run must send nothing at an arrival the plain run
-- sends nothing at, which `take-one`'s dropped second arrival tests.
-- LOAD-BEARING for the map where it is not the identity: `take-two-cold`,
-- whose impl spends its second arrival on the cut lane's copy of the
-- first, so the map skips it and the skipped slice must be empty.
-- LOAD-BEARING for one instant per arrival where a slice holds two
-- values -- `of-two`'s subscription and every timed row's last arrival,
-- whose END item shares it -- and for none shared wherever two slices
-- hold values: `two-arrivals`, plain and timed.  `take-one` plain stamps
-- one value and is DEGENERATE for the instants.
--
-- NOT `take-one`'s timed translation: its elaborated run does not
-- reduce in the typechecker in useful time, even at fuel 0 (measured in
-- typecheck-performance-numbers.md), so a timed `take` is
-- `make quickcheck`'s alone.  Nor `take-two-cold`'s instants: its impl
-- run at fuel 4 does not reduce within the dev loop's budget.
-- TARGET: arrival-values @be3c0a
-- TARGET: arrival-instants @15b371
module Probed.Simulation where

open import Data.Empty using (⊥-elim)
open import Data.Unit using (tt)
open import Data.List using (List; [])
open import Data.List.Relation.Unary.All using (All) renaming (all? to all?ᴬ)
open import Data.Nat using (ℕ; suc; _≤_; _<_; s≤s; z≤n; _≟_; _+_)
open import Data.Nat.Properties using (+-cancelʳ-≡; n<1+n)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.List.Relation.Binary.Pointwise.Properties using (decidable)
open import Relation.Nullary.Decidable using (Dec; True; yes; no; toWitness; _×-dec_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Rx.Exp using (Ctx; Val; natᵗ)
open import SExp.Syntax using (plainᵗ)
open import Timed.Translation using (timed; timedSlots; itemᵗ)
open import Simulation.Statement using (arrival-values; arrival-instants; Agrees; sliceAt; stampedAt)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two; take-two-cold)

-- `Agrees` at a timed item of `natᵗ`, decided
item? : ∀ {n m} {Γ′ : Ctx m} {Γ : Ctx n} (v : Val Γ′ (plainᵗ (itemᵗ natᵗ))) (w : Val Γ (itemᵗ natᵗ))
      → Dec (Agrees Γ′ Γ (itemᵗ natᵗ) v w)
item? (p , inj₁ a) (q , inj₁ b) = decidable _≟_ p q ×-dec (a ≟ b)
item? (p , inj₂ _) (q , inj₂ _) = decidable _≟_ p q ×-dec yes refl
item? (_ , inj₁ _) (_ , inj₂ _) = no λ ()
item? (_ , inj₂ _) (_ , inj₁ _) = no λ ()

-- one slice's stamps, all one instant, decided
stamps : ∀ {A : Set} {c : ℕ} {xs : List (ℕ × A)} {ok : True (all?ᴬ (λ p → proj₁ p ≟ c) xs)}
       → All (λ p → proj₁ p ≡ c) xs
stamps {c = c} {xs = xs} {ok = ok} = toWitness {a? = all?ᴬ (λ p → proj₁ p ≟ c) xs} ok

-- a claim at each arrival through the fourth
upTo3 : (P : ℕ → Set) → P 0 → P 1 → P 2 → P 3 → ∀ k → k ≤ 3 → P k
upTo3 P p₀ p₁ p₂ p₃ 0 _ = p₀
upTo3 P p₀ p₁ p₂ p₃ 1 _ = p₁
upTo3 P p₀ p₁ p₂ p₃ 2 _ = p₂
upTo3 P p₀ p₁ p₂ p₃ 3 _ = p₃
upTo3 P p₀ p₁ p₂ p₃ (suc (suc (suc (suc _)))) (s≤s (s≤s (s≤s ())))

-- a run whose impl arrivals are the plain run's, one for one
same : ℕ → ℕ
same k = k

same-up : ∀ k → same k < same (suc k)
same-up k = n<1+n k

-- a run whose impl spends one arrival past the plain run's first: the
-- cut lane's copy of it
skip : ℕ → ℕ
skip 0             = 0
skip 1             = 1
skip (suc (suc k)) = suc (suc (suc k))

skip-up : ∀ k → skip k < skip (suc k)
skip-up 0             = s≤s z≤n
skip-up 1             = s≤s (s≤s z≤n)
skip-up (suc (suc k)) = n<1+n _

_ : Confirms (arrival-values (κᵖ take-one) 3 (Point.prog take-one) (insᵖ take-one))
_ = same , same-up , (λ j _ f → ⊥-elim (f j refl)) , upTo3 _
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)

_ : Confirms (arrival-instants (κᵖ take-one) 3 (Point.prog take-one) (insᵖ take-one))
_ = (_+ 8) , (λ {a} {b} → +-cancelʳ-≡ 8 a b) , upTo3 _ stamps stamps stamps stamps

_ : Confirms (arrival-values (κᵖ two-arrivals) 3 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = same , same-up , (λ j _ f → ⊥-elim (f j refl)) , upTo3 _
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)

_ : Confirms (arrival-values (κᵖ two-arrivals) 3 (timed (κᵖ two-arrivals) (Point.prog two-arrivals)) (timedSlots (insᵖ two-arrivals)))
_ = same , same-up , (λ j _ f → ⊥-elim (f j refl)) , upTo3 _
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)

_ : Confirms (arrival-instants (κᵖ two-arrivals) 3 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = (_+ 7) , (λ {a} {b} → +-cancelʳ-≡ 7 a b) , upTo3 _ stamps stamps stamps stamps

_ : Confirms (arrival-instants (κᵖ two-arrivals) 3 (timed (κᵖ two-arrivals) (Point.prog two-arrivals)) (timedSlots (insᵖ two-arrivals)))
_ = (_+ 9) , (λ {a} {b} → +-cancelʳ-≡ 9 a b) , upTo3 _ stamps stamps stamps stamps

_ : Confirms (arrival-values (κᵖ of-two) 3 (Point.prog of-two) (insᵖ of-two))
_ = same , same-up , (λ j _ f → ⊥-elim (f j refl)) , upTo3 _
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)

_ : Confirms (arrival-values (κᵖ of-two) 3 (timed (κᵖ of-two) (Point.prog of-two)) (timedSlots (insᵖ of-two)))
_ = same , same-up , (λ j _ f → ⊥-elim (f j refl)) , upTo3 _
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)
    (toWitness {a? = decidable (λ p w → item? (proj₂ p) w) _ _} tt)

_ : Confirms (arrival-instants (κᵖ of-two) 3 (Point.prog of-two) (insᵖ of-two))
_ = (_+ 5) , (λ {a} {b} → +-cancelʳ-≡ 5 a b) , upTo3 _ stamps stamps stamps stamps

_ : Confirms (arrival-instants (κᵖ of-two) 3 (timed (κᵖ of-two) (Point.prog of-two)) (timedSlots (insᵖ of-two)))
_ = (_+ 5) , (λ {a} {b} → +-cancelʳ-≡ 5 a b) , upTo3 _ stamps stamps stamps stamps

_ : Confirms (arrival-values (κᵖ take-two-cold) 3 (Point.prog take-two-cold) (insᵖ take-two-cold))
_ = skip , skip-up , gaps , upTo3 _
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
    (toWitness {a? = decidable (λ p w → proj₂ p ≟ w) _ _} tt)
  where
    gaps : ∀ j → j ≤ skip 3 → (∀ k → skip k ≢ j) → sliceAt (stampedAt (κᵖ take-two-cold) (Point.prog take-two-cold) (insᵖ take-two-cold)) j ≡ []
    gaps 0 _ f = ⊥-elim (f 0 refl)
    gaps 1 _ f = ⊥-elim (f 1 refl)
    gaps 2 _ f = refl
    gaps 3 _ f = ⊥-elim (f 2 refl)
    gaps 4 _ f = ⊥-elim (f 3 refl)
    gaps (suc (suc (suc (suc (suc _))))) (s≤s (s≤s (s≤s (s≤s ())))) _
