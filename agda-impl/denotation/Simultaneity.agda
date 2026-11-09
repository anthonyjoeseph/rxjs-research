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
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<⇒<ᵇ; <ᵇ⇒<; n≮n; <-asym; ≮⇒≥; ≤-antisym)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

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

------------------------------------------------------------------------
-- The comparison is an order: `eq` is equality, `lt` flips to `gt`

ℕ-≡ : ∀ {m n} → cmpℕ m n ≡ eq → m ≡ n
ℕ-≡ {m} {n} h with m <ᵇ n in a | n <ᵇ m in b
... | false | false = ≤-antisym (≮⇒≥ (λ l → subst T b (<⇒<ᵇ l))) (≮⇒≥ (λ l → subst T a (<⇒<ᵇ l)))
... | false | true  = ⊥-elim (gt≢eq h) where gt≢eq : gt ≡ eq → ⊥ ; gt≢eq ()
... | true  | _     = ⊥-elim (lt≢eq h) where lt≢eq : lt ≡ eq → ⊥ ; lt≢eq ()

ℕ-flip : ∀ {m n} → cmpℕ m n ≡ lt → cmpℕ n m ≡ gt
ℕ-flip {m} {n} h with m <ᵇ n in a | n <ᵇ m in b
... | true  | false = refl
... | true  | true  = ⊥-elim (<-asym (<ᵇ⇒< m n (subst T (sym a) tt)) (<ᵇ⇒< n m (subst T (sym b) tt)))
... | false | true  = ⊥-elim (gt≢lt h) where gt≢lt : gt ≡ lt → ⊥ ; gt≢lt ()
... | false | false = ⊥-elim (eq≢lt h) where eq≢lt : eq ≡ lt → ⊥ ; eq≢lt ()

lexi-eq : ∀ x y → lexi x y ≡ eq → x ≡ eq × y ≡ eq
lexi-eq eq y h = refl , h
lexi-eq lt y ()
lexi-eq gt y ()

lexi-lt : ∀ x y → lexi x y ≡ lt → x ≡ lt ⊎ (x ≡ eq × y ≡ lt)
lexi-lt lt y _ = inj₁ refl
lexi-lt eq y h = inj₂ (refl , h)
lexi-lt gt y ()

lexi-gt₁ : ∀ x y → x ≡ gt → lexi x y ≡ gt
lexi-gt₁ _ _ refl = refl

lexi-eq₁ : ∀ x y → x ≡ eq → lexi x y ≡ y
lexi-eq₁ _ _ refl = refl

mutual
  eqˡ : ∀ a b → cmpLabel a b ≡ eq → a ≡ b
  eqˡ (ix m)  (ix n)  h = cong ix (ℕ-≡ {m} {n} h)
  eqˡ (ix _)  (sub _) ()
  eqˡ (ix _)  last    ()
  eqˡ (sub _) (ix _)  ()
  eqˡ (sub p) (sub q) h = cong sub (eqᵖ p q h)
  eqˡ (sub _) last    ()
  eqˡ last    (ix _)  ()
  eqˡ last    (sub _) ()
  eqˡ last    last    _ = refl

  eqⁱ : ∀ i j → cmpInstant i j ≡ eq → i ≡ j
  eqⁱ frame         frame         _ = refl
  eqⁱ frame         (cascade _ _) ()
  eqⁱ (cascade _ _) frame         ()
  eqⁱ (cascade t e) (cascade u d) h with lexi-eq (cmpℕ t u) (cmpPos e d) h
  ... | a , b = cong₂ cascade (ℕ-≡ {t} {u} a) (eqᵖ e d b)

  eqᵗ : ∀ (p q : Path) → cmpPath p q ≡ eq → p ≡ q
  eqᵗ []      []      _ = refl
  eqᵗ []      (_ ∷ _) ()
  eqᵗ (_ ∷ _) []      ()
  eqᵗ (a ∷ p) (b ∷ q) h with lexi-eq (cmpLabel a b) (cmpPath p q) h
  ... | x , y = cong₂ _∷_ (eqˡ a b x) (eqᵗ p q y)

  eqᵖ : ∀ p q → cmpPos p q ≡ eq → p ≡ q
  eqᵖ (i ∙ p) (j ∙ q) h with lexi-eq (cmpInstant i j) (cmpPath p q) h
  ... | x , y = cong₂ _∙_ (eqⁱ i j x) (eqᵗ p q y)

mutual
  flipˡ : ∀ a b → cmpLabel a b ≡ lt → cmpLabel b a ≡ gt
  flipˡ (ix m)  (ix n)  h = ℕ-flip {m} {n} h
  flipˡ (ix _)  (sub _) _ = refl
  flipˡ (ix _)  last    _ = refl
  flipˡ (sub _) (ix _)  ()
  flipˡ (sub p) (sub q) h = flipᵖ p q h
  flipˡ (sub _) last    _ = refl
  flipˡ last    (ix _)  ()
  flipˡ last    (sub _) ()
  flipˡ last    last    ()

  flipⁱ : ∀ i j → cmpInstant i j ≡ lt → cmpInstant j i ≡ gt
  flipⁱ frame         frame         ()
  flipⁱ frame         (cascade _ _) _ = refl
  flipⁱ (cascade _ _) frame         ()
  flipⁱ (cascade t e) (cascade u d) h with lexi-lt (cmpℕ t u) (cmpPos e d) h
  ... | inj₁ a = lexi-gt₁ (cmpℕ u t) (cmpPos d e) (ℕ-flip {t} {u} a)
  ... | inj₂ (a , b) with ℕ-≡ {t} {u} a
  ...   | refl = trans (lexi-eq₁ (cmpℕ t t) (cmpPos d e) a) (flipᵖ e d b)

  flipᵗ : ∀ (p q : Path) → cmpPath p q ≡ lt → cmpPath q p ≡ gt
  flipᵗ []      []      ()
  flipᵗ []      (_ ∷ _) _ = refl
  flipᵗ (_ ∷ _) []      ()
  flipᵗ (a ∷ p) (b ∷ q) h with lexi-lt (cmpLabel a b) (cmpPath p q) h
  ... | inj₁ x = lexi-gt₁ (cmpLabel b a) (cmpPath q p) (flipˡ a b x)
  ... | inj₂ (x , y) with eqˡ a b x
  ...   | refl = trans (lexi-eq₁ (cmpLabel a a) (cmpPath q p) x) (flipᵗ p q y)

  flipᵖ : ∀ p q → cmpPos p q ≡ lt → cmpPos q p ≡ gt
  flipᵖ (i ∙ p) (j ∙ q) h with lexi-lt (cmpInstant i j) (cmpPath p q) h
  ... | inj₁ x = lexi-gt₁ (cmpInstant j i) (cmpPath q p) (flipⁱ i j x)
  ... | inj₂ (x , y) with eqⁱ i j x
  ...   | refl = trans (lexi-eq₁ (cmpInstant i i) (cmpPath q p) x) (flipᵗ p q y)

-- AN INSTANT IS AN INTERVAL OF POSITIONS: a position between two of one
-- instant is of it.  The order compares instants first, so a position
-- strictly inside two of one instant can be in no other.
private
  f≢t : false ≡ true → ⊥
  f≢t ()

between : ∀ {a b c} → a <ᵖ b ≡ true → b <ᵖ c ≡ true → instant a ≡ instant c → instant b ≡ instant a
between {i ∙ p} {j ∙ q} {_ ∙ r} ab bc refl with cmpInstant i j in ij
... | eq = sym (eqⁱ i j ij)
... | gt = ⊥-elim (f≢t ab)
... | lt = ⊥-elim (f≢t (subst (λ x → isLt (lexi x (cmpPath q r)) ≡ true) (flipⁱ i j ij) bc))
