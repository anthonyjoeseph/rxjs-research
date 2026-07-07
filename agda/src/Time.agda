-- Time is a pair (tick , origin), ordered lexicographically. Two emissions
-- are simultaneous exactly when their Times are equal; distinct root-source
-- events carry distinct Times by construction (origin = source index).
module Time where

open import Prelude

Time : Set
Time = ℕ × ℕ  -- tick , origin

timeEq : Time → Time → Bool
timeEq (t₁ , o₁) (t₂ , o₂) = eqℕ t₁ t₂ ∧ eqℕ o₁ o₂

timeLt : Time → Time → Bool
timeLt (t₁ , o₁) (t₂ , o₂) = ltℕ t₁ t₂ ∨ (eqℕ t₁ t₂ ∧ ltℕ o₁ o₂)

timeLeq : Time → Time → Bool
timeLeq (t₁ , o₁) (t₂ , o₂) = ltℕ t₁ t₂ ∨ (eqℕ t₁ t₂ ∧ leqℕ o₁ o₂)

timeEq-refl : (t : Time) → timeEq t t ≡ true
timeEq-refl (a , b) rewrite eqℕ-refl a | eqℕ-refl b = refl

timeLeq-refl : (t : Time) → timeLeq t t ≡ true
timeLeq-refl (a , b) rewrite ltℕ-irrefl a | eqℕ-refl a | leqℕ-refl b = refl

timeLt⇒timeEq-false : (x y : Time) → timeLt x y ≡ true → timeEq x y ≡ false
timeLt⇒timeEq-false (a , b) (c , d) p with ltℕ a c in lt-ac
... | true rewrite ltℕ⇒eqℕ-false a c lt-ac = refl
... | false
  rewrite ∧-split-left (eqℕ a c) (ltℕ b d) p
        | ltℕ⇒eqℕ-false b d (∧-split-right (eqℕ a c) (ltℕ b d) p)
  = refl

timeLt⇒timeLeq-flip-false :
  (x y : Time) → timeLt x y ≡ true → timeLeq y x ≡ false
timeLt⇒timeLeq-flip-false (a , b) (c , d) p with ltℕ a c in lt-ac
... | true rewrite ltℕ-asym a c lt-ac | ltℕ⇒eqℕ-false-flip a c lt-ac = refl
... | false
  rewrite eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) p)
        | ltℕ-irrefl c
        | eqℕ-refl c
        | ltℕ⇒leqℕ-flip-false b d (∧-split-right (eqℕ a c) (ltℕ b d) p)
  = refl

-- the beginning of time: a boundary below every Time (closes of not-yet-
-- started observables live here; it is a bound, not an emission, so no
-- origin-ownership is claimed)
timeMin : Time
timeMin = (0 , 0)

timeMin-least : (t : Time) → timeLeq timeMin t ≡ true
timeMin-least (zero  , b) = refl
timeMin-least (suc a , b) = refl

timeMax : Time → Time → Time
timeMax x y = if timeLeq x y then y else x

-- helpers that make a timeLeq/timeLt goal compute after rewriting
lt-head-leq : (a c b d : ℕ) → ltℕ a c ≡ true → timeLeq (a , b) (c , d) ≡ true
lt-head-leq a c b d p rewrite p = refl

eq-head-leq : (a b d : ℕ) → leqℕ b d ≡ true → timeLeq (a , b) (a , d) ≡ true
eq-head-leq a b d p rewrite ltℕ-irrefl a | eqℕ-refl a | p = refl

lt-head-lt : (a c b d : ℕ) → ltℕ a c ≡ true → timeLt (a , b) (c , d) ≡ true
lt-head-lt a c b d p rewrite p = refl

eq-head-lt : (a b d : ℕ) → ltℕ b d ≡ true → timeLt (a , b) (a , d) ≡ true
eq-head-lt a b d p rewrite ltℕ-irrefl a | eqℕ-refl a | p = refl

timeEq-sound : (x y : Time) → timeEq x y ≡ true → x ≡ y
timeEq-sound (a , b) (c , d) p
  with eqℕ-sound a c (∧-split-left (eqℕ a c) (eqℕ b d) p)
     | eqℕ-sound b d (∧-split-right (eqℕ a c) (eqℕ b d) p)
... | refl | refl = refl

timeLt⇒timeLeq : (x y : Time) → timeLt x y ≡ true → timeLeq x y ≡ true
timeLt⇒timeLeq (a , b) (c , d) p with ∨-split (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p
... | left ac = lt-head-leq a c b d ac
... | right r =
  subst (λ z → timeLeq (a , b) (z , d) ≡ true)
        (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r))
        (eq-head-leq a b d (ltℕ⇒leqℕ b d (∧-split-right (eqℕ a c) (ltℕ b d) r)))

timeLeq-total : (x y : Time) → timeLeq x y ≡ false → timeLeq y x ≡ true
timeLeq-total (a , b) (c , d) h
  with ltℕ-false-split a c (∨-false-left (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h)
... | left ca = lt-head-leq c a d b ca
... | right aeqc =
  subst (λ z → timeLeq (c , d) (z , b) ≡ true) (sym aeqc)
        (eq-head-leq c d b
          (leqℕ-false⇒flip b d
            (∧-true-false (eqℕ a c) (leqℕ b d)
              (eqℕ-complete a c aeqc)
              (∨-false-right (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h))))

timeLeq-trans : (x y z : Time)
  → timeLeq x y ≡ true → timeLeq y z ≡ true → timeLeq x z ≡ true
timeLeq-trans (a , b) (c , d) (e , f) p q
  with ∨-split (ltℕ a c) (eqℕ a c ∧ leqℕ b d) p
     | ∨-split (ltℕ c e) (eqℕ c e ∧ leqℕ d f) q
... | left ac  | left ce  = lt-head-leq a e b f (ltℕ-trans a c e ac ce)
... | left ac  | right r  =
  lt-head-leq a e b f
    (subst (λ z′ → ltℕ a z′ ≡ true)
           (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r)) ac)
... | right r  | left ce  =
  lt-head-leq a e b f
    (subst (λ z′ → ltℕ z′ e ≡ true)
           (sym (eqℕ-sound a c (∧-split-left (eqℕ a c) (leqℕ b d) r))) ce)
... | right r₁ | right r₂ =
  subst (λ z′ → timeLeq (a , b) (z′ , f) ≡ true)
        (trans (eqℕ-sound a c (∧-split-left (eqℕ a c) (leqℕ b d) r₁))
               (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r₂)))
        (eq-head-leq a b f
          (leqℕ-trans b d f
            (∧-split-right (eqℕ a c) (leqℕ b d) r₁)
            (∧-split-right (eqℕ c e) (leqℕ d f) r₂)))

timeLt-trans : (x y z : Time)
  → timeLt x y ≡ true → timeLt y z ≡ true → timeLt x z ≡ true
timeLt-trans (a , b) (c , d) (e , f) p q
  with ∨-split (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p
     | ∨-split (ltℕ c e) (eqℕ c e ∧ ltℕ d f) q
... | left ac  | left ce  = lt-head-lt a e b f (ltℕ-trans a c e ac ce)
... | left ac  | right r  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ a z′ ≡ true)
           (eqℕ-sound c e (∧-split-left (eqℕ c e) (ltℕ d f) r)) ac)
... | right r  | left ce  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ z′ e ≡ true)
           (sym (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r))) ce)
... | right r₁ | right r₂ =
  subst (λ z′ → timeLt (a , b) (z′ , f) ≡ true)
        (trans (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r₁))
               (eqℕ-sound c e (∧-split-left (eqℕ c e) (ltℕ d f) r₂)))
        (eq-head-lt a b f
          (ltℕ-trans b d f
            (∧-split-right (eqℕ a c) (ltℕ b d) r₁)
            (∧-split-right (eqℕ c e) (ltℕ d f) r₂)))

timeLt-leq-trans : (x y z : Time)
  → timeLt x y ≡ true → timeLeq y z ≡ true → timeLt x z ≡ true
timeLt-leq-trans (a , b) (c , d) (e , f) p q
  with ∨-split (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p
     | ∨-split (ltℕ c e) (eqℕ c e ∧ leqℕ d f) q
... | left ac  | left ce  = lt-head-lt a e b f (ltℕ-trans a c e ac ce)
... | left ac  | right r  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ a z′ ≡ true)
           (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r)) ac)
... | right r  | left ce  =
  lt-head-lt a e b f
    (subst (λ z′ → ltℕ z′ e ≡ true)
           (sym (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r))) ce)
... | right r₁ | right r₂ =
  subst (λ z′ → timeLt (a , b) (z′ , f) ≡ true)
        (trans (eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) r₁))
               (eqℕ-sound c e (∧-split-left (eqℕ c e) (leqℕ d f) r₂)))
        (eq-head-lt a b f
          (ltℕ-leqℕ-trans b d f
            (∧-split-right (eqℕ a c) (ltℕ b d) r₁)
            (∧-split-right (eqℕ c e) (leqℕ d f) r₂)))

timeLeq-false⇒timeLt-flip : (x y : Time)
  → timeLeq x y ≡ false → timeLt y x ≡ true
timeLeq-false⇒timeLt-flip (a , b) (c , d) h
  with ltℕ-false-split a c (∨-false-left (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h)
... | left ca = lt-head-lt c a d b ca
... | right aeqc =
  subst (λ z → timeLt (c , d) (z , b) ≡ true) (sym aeqc)
        (eq-head-lt c d b
          (leqℕ-false⇒ltℕ-flip b d
            (∧-true-false (eqℕ a c) (leqℕ b d)
              (eqℕ-complete a c aeqc)
              (∨-false-right (ltℕ a c) (eqℕ a c ∧ leqℕ b d) h))))

timeLeq-neq⇒timeLt : (x y : Time)
  → timeLeq x y ≡ true → timeEq x y ≡ false → timeLt x y ≡ true
timeLeq-neq⇒timeLt (a , b) (c , d) p ne
  with ∨-split (ltℕ a c) (eqℕ a c ∧ leqℕ b d) p
... | left ac = lt-head-lt a c b d ac
... | right r =
  subst (λ z → timeLt (a , b) (z , d) ≡ true)
        (eqℕ-sound a c (∧-split-left (eqℕ a c) (leqℕ b d) r))
        (eq-head-lt a b d
          (leqℕ-neq⇒ltℕ b d
            (∧-split-right (eqℕ a c) (leqℕ b d) r)
            (∧-true-false (eqℕ a c) (eqℕ b d)
              (∧-split-left (eqℕ a c) (leqℕ b d) r) ne)))

timeLt⇒timeEq-false-flip : (x y : Time)
  → timeLt x y ≡ true → timeEq y x ≡ false
timeLt⇒timeEq-false-flip (a , b) (c , d) p with ltℕ a c in lt-ac
... | true rewrite ltℕ⇒eqℕ-false-flip a c lt-ac = refl
... | false
  rewrite eqℕ-sound a c (∧-split-left (eqℕ a c) (ltℕ b d) p)
        | eqℕ-refl c
        | ltℕ⇒eqℕ-false-flip b d (∧-split-right (eqℕ a c) (ltℕ b d) p)
  = refl

timeLt-irrefl : (t : Time) → timeLt t t ≡ false
timeLt-irrefl (a , b) rewrite ltℕ-irrefl a | eqℕ-refl a | ltℕ-irrefl b = refl

timeLt-false⇒timeLeq-flip : (x y : Time)
  → timeLt x y ≡ false → timeLeq y x ≡ true
timeLt-false⇒timeLeq-flip (a , b) (c , d) p
  with ltℕ-false-split a c (∨-false-left (ltℕ a c) (eqℕ a c ∧ ltℕ b d) p)
... | left q     = lt-head-leq c a d b q
... | right refl = eq-head-leq a d b
    (ltℕ-false⇒leqℕ-flip b d
      (∧-true-false (eqℕ a a) (ltℕ b d) (eqℕ-refl a)
        (∨-false-right (ltℕ a a) (eqℕ a a ∧ ltℕ b d) p)))

timeMax-left : (x y : Time) → timeLeq x (timeMax x y) ≡ true
timeMax-left x y with timeLeq x y in e
... | true  = e
... | false = timeLeq-refl x

timeMax-right : (x y : Time) → timeLeq y (timeMax x y) ≡ true
timeMax-right x y with timeLeq x y in e
... | true  = timeLeq-refl y
... | false = timeLeq-total x y e
