-- THE INSTANT IS THE TIMESTAMP.  What the denotation says about
-- simultaneity, as facts about positions alone (`denotation.Position`):
-- two rows are simultaneous exactly when their instants are equal, and
-- these laws say when that is.  None of them is about a program: every
-- operator places a row by `_⊕_` under its cause, and every cascade root
-- by `cascadeAt`, so they hold of every emission set by construction.
--
-- Read together: two positions share an instant exactly when they lie
-- under one root, and a root is the subscription or one `cascadeAt`.  So
-- a hot's deliveries are simultaneous with the source step that caused
-- them, a burst's steps with each other, and a completion's
-- continuations with the burst it ends; and two timer firings are never
-- simultaneous.  The order puts the subscribe frame first, then
-- cascades by tick, same-tick ones in creation order as rxjs fires them,
-- and a cascade after the position its timer was created at.
module denotation.Simultaneity where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.List using ([])
open import Data.Nat using (ℕ; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<⇒<ᵇ; <ᵇ⇒<; n≮n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.Position

------------------------------------------------------------------------
-- When two positions are simultaneous

-- An effect runs in its cause's instant: a hot's delivery, a burst's
-- step, a completion's continuation.
effect-instant : ∀ p q → instant (p ⊕ q) ≡ instant p
effect-instant (_ ∙ _) _ = refl

-- A cascade's instant is shared only by positions beneath its root.
cascade-own : ∀ t e p → instant p ≡ cascade t e → p ≡ cascadeAt t e ⊕ path p
cascade-own t e (_ ∙ _) refl = refl

-- The subscribe frame's instant is shared only by positions beneath the root.
frame-own : ∀ p → instant p ≡ frame → p ≡ root ⊕ path p
frame-own (_ ∙ _) refl = refl

-- Two firings share an instant only if they are one firing.
cascade-inj : ∀ {t e t′ e′} → cascade t e ≡ cascade t′ e′ → t ≡ t′ × e ≡ e′
cascade-inj refl = refl , refl

------------------------------------------------------------------------
-- How instants are ordered

ℕ-lt : ∀ {m n} → m < n → cmpℕ m n ≡ lt
ℕ-lt {m} {n} h with m <ᵇ n | <⇒<ᵇ h
... | true  | _  = refl
... | false | ()

ℕ-eq : ∀ n → cmpℕ n n ≡ eq
ℕ-eq n with n <ᵇ n in h
... | false = refl
... | true  = ⊥-elim (n≮n n (<ᵇ⇒< n n (subst T (sym h) tt)))

-- The subscribe frame comes before every cascade.
frame-first : ∀ t e → frame <ⁱ cascade t e ≡ true
frame-first _ _ = refl

-- A later tick is later.
later-tick : ∀ {t t′} e e′ → t < t′ → cascade t e <ⁱ cascade t′ e′ ≡ true
later-tick e e′ h rewrite ℕ-lt h = refl

-- Same-tick timers fire in creation order.
same-tick : ∀ t e e′ → (cascade t e <ⁱ cascade t e′) ≡ (e <ᵖ e′)
same-tick t e e′ rewrite ℕ-eq t = refl

-- A cascade fires after the position its timer was created at.
after-creator : ∀ {t} e → tick e < t → e <ᵖ cascadeAt t e ≡ true
after-creator (frame ∙ _)       _ = refl
after-creator (cascade _ _ ∙ _) h rewrite ℕ-lt h = refl

-- AN INSTANT IS AN INTERVAL OF POSITIONS: a position between two of one
-- instant is of it.  The order compares instants first, so this is
-- asymmetry of `cmpInstant` together with `eq` reflecting equality.
postulate
  between : ∀ {a b c} → a <ᵖ b ≡ true → b <ᵖ c ≡ true → instant a ≡ instant c → instant b ≡ instant a
