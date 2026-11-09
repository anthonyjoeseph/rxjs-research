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
open import Data.Nat.Properties using (<⇒<ᵇ; <ᵇ⇒<; n≮n; <-asym; <-trans; ≮⇒≥; ≤-antisym)
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
  reflˡ : ∀ a → cmpLabel a a ≡ eq
  reflˡ (ix n)  = ℕ-eq n
  reflˡ (sub p) = reflᵖ p
  reflˡ last    = refl

  reflⁱ : ∀ i → cmpInstant i i ≡ eq
  reflⁱ frame         = refl
  reflⁱ (cascade t e) = cong₂ lexi (ℕ-eq t) (reflᵖ e)

  reflᵗ : ∀ (p : Path) → cmpPath p p ≡ eq
  reflᵗ []      = refl
  reflᵗ (a ∷ p) = cong₂ lexi (reflˡ a) (reflᵗ p)

  reflᵖ : ∀ p → cmpPos p p ≡ eq
  reflᵖ (i ∙ p) = cong₂ lexi (reflⁱ i) (reflᵗ p)

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
-- Transitive, and `gt` flips to `lt`.
lt-ℕ : ∀ {m n} → cmpℕ m n ≡ lt → m < n
lt-ℕ {m} {n} h with m <ᵇ n in e | n <ᵇ m
lt-ℕ {m} {n} h  | true  | _     = <ᵇ⇒< m n (subst T (sym e) tt)
lt-ℕ {m} {n} () | false | true
lt-ℕ {m} {n} () | false | false

gt-ℕ : ∀ {m n} → cmpℕ m n ≡ gt → n < m
gt-ℕ {m} {n} h with m <ᵇ n | n <ᵇ m in e
gt-ℕ {m} {n} () | true  | _
gt-ℕ {m} {n} h  | false | true  = <ᵇ⇒< n m (subst T (sym e) tt)
gt-ℕ {m} {n} () | false | false

ℕ-trans : ∀ {m n k} → cmpℕ m n ≡ lt → cmpℕ n k ≡ lt → cmpℕ m k ≡ lt
ℕ-trans {m} {n} {k} h₁ h₂ = ℕ-lt {m} {k} (<-trans (lt-ℕ {m} {n} h₁) (lt-ℕ {n} {k} h₂))

ℕ-gt : ∀ {m n} → cmpℕ m n ≡ gt → cmpℕ n m ≡ lt
ℕ-gt {m} {n} h = ℕ-lt {n} {m} (gt-ℕ {m} {n} h)

lexi-l : ∀ {x y} → x ≡ lt → lexi x y ≡ lt
lexi-l refl = refl

lexi-e : ∀ {x y} → x ≡ eq → y ≡ lt → lexi x y ≡ lt
lexi-e refl h = h

lexi-gt : ∀ x y → lexi x y ≡ gt → x ≡ gt ⊎ (x ≡ eq × y ≡ gt)
lexi-gt eq y h = inj₂ (refl , h)
lexi-gt lt y ()
lexi-gt gt y _ = inj₁ refl

-- A lexicographic pair is transitive when its halves are.
lexi-trans : ∀ x₁ x₂ x₃ y₁ y₂ y₃
           → (x₁ ≡ lt → x₂ ≡ lt → x₃ ≡ lt) → (x₁ ≡ lt → x₂ ≡ eq → x₃ ≡ lt)
           → (x₁ ≡ eq → x₂ ≡ lt → x₃ ≡ lt) → (x₁ ≡ eq → x₂ ≡ eq → x₃ ≡ eq)
           → (y₁ ≡ lt → y₂ ≡ lt → y₃ ≡ lt)
           → lexi x₁ y₁ ≡ lt → lexi x₂ y₂ ≡ lt → lexi x₃ y₃ ≡ lt
lexi-trans x₁ x₂ x₃ y₁ y₂ y₃ ll le el ee yy h₁ h₂ with lexi-lt x₁ y₁ h₁ | lexi-lt x₂ y₂ h₂
... | inj₁ a       | inj₁ b       = lexi-l (ll a b)
... | inj₁ a       | inj₂ (b , _) = lexi-l (le a b)
... | inj₂ (a , _) | inj₁ b       = lexi-l (el a b)
... | inj₂ (a , u) | inj₂ (b , v) = lexi-e (ee a b) (yy u v)

-- A lexicographic pair flips `gt` to `lt` when its halves do.
lexi-flip : ∀ x y x′ y′ → lexi x y ≡ gt → (x ≡ gt → x′ ≡ lt) → (x ≡ eq → x′ ≡ eq) → (y ≡ gt → y′ ≡ lt) → lexi x′ y′ ≡ lt
lexi-flip x y x′ y′ h g e f with lexi-gt x y h
... | inj₁ a       = lexi-l (g a)
... | inj₂ (a , b) = lexi-e (e a) (f b)

mutual
  ltˡ : ∀ a b c → cmpLabel a b ≡ lt → cmpLabel b c ≡ lt → cmpLabel a c ≡ lt
  ltˡ (ix m)  (ix n)  (ix k)  h₁ h₂ = ℕ-trans {m} {n} {k} h₁ h₂
  ltˡ (ix _)  _       (sub _) _  _  = refl
  ltˡ (ix _)  _       last    _  _  = refl
  ltˡ (ix _)  (sub _) (ix _)  _  ()
  ltˡ (ix _)  last    (ix _)  _  ()
  ltˡ (sub p) (sub q) (sub r) h₁ h₂ = ltᵖ p q r h₁ h₂
  ltˡ (sub _) _       last    _  _  = refl
  ltˡ (sub _) (ix _)  _       () _
  ltˡ (sub _) (sub _) (ix _)  _  ()
  ltˡ (sub _) last    (ix _)  _  ()
  ltˡ (sub _) last    (sub _) _  ()
  ltˡ last    (ix _)  _       () _
  ltˡ last    (sub _) _       () _
  ltˡ last    last    _       () _

  ltⁱ : ∀ i j k → cmpInstant i j ≡ lt → cmpInstant j k ≡ lt → cmpInstant i k ≡ lt
  ltⁱ frame         frame         _             () _
  ltⁱ frame         (cascade _ _) frame         _  ()
  ltⁱ frame         (cascade _ _) (cascade _ _) _  _  = refl
  ltⁱ (cascade _ _) frame         _             () _
  ltⁱ (cascade _ _) (cascade _ _) frame         _  ()
  ltⁱ (cascade t e) (cascade u d) (cascade v f) h₁ h₂ =
    lexi-trans (cmpℕ t u) (cmpℕ u v) (cmpℕ t v) (cmpPos e d) (cmpPos d f) (cmpPos e f)
      (ℕ-trans {t} {u} {v})
      (λ a b → subst (λ z → cmpℕ t z ≡ lt) (ℕ-≡ {u} {v} b) a)
      (λ a b → subst (λ z → cmpℕ z v ≡ lt) (sym (ℕ-≡ {t} {u} a)) b)
      (λ a b → subst (λ z → cmpℕ z v ≡ eq) (sym (ℕ-≡ {t} {u} a)) b)
      (λ a b → ltᵖ e d f a b) h₁ h₂

  ltᵗ : ∀ (p q r : Path) → cmpPath p q ≡ lt → cmpPath q r ≡ lt → cmpPath p r ≡ lt
  ltᵗ []      (_ ∷ _) (_ ∷ _) _  _  = refl
  ltᵗ []      []      _       () _
  ltᵗ (_ ∷ _) []      _       () _
  ltᵗ _       (_ ∷ _) []      _  ()
  ltᵗ (a ∷ p) (b ∷ q) (c ∷ r) h₁ h₂ =
    lexi-trans (cmpLabel a b) (cmpLabel b c) (cmpLabel a c) (cmpPath p q) (cmpPath q r) (cmpPath p r)
      (λ x y → ltˡ a b c x y)
      (λ x y → subst (λ z → cmpLabel a z ≡ lt) (eqˡ b c y) x)
      (λ x y → subst (λ z → cmpLabel z c ≡ lt) (sym (eqˡ a b x)) y)
      (λ x y → subst (λ z → cmpLabel z c ≡ eq) (sym (eqˡ a b x)) y)
      (λ x y → ltᵗ p q r x y) h₁ h₂

  ltᵖ : ∀ p q r → cmpPos p q ≡ lt → cmpPos q r ≡ lt → cmpPos p r ≡ lt
  ltᵖ (i ∙ p) (j ∙ q) (k ∙ r) h₁ h₂ =
    lexi-trans (cmpInstant i j) (cmpInstant j k) (cmpInstant i k) (cmpPath p q) (cmpPath q r) (cmpPath p r)
      (λ x y → ltⁱ i j k x y)
      (λ x y → subst (λ z → cmpInstant i z ≡ lt) (eqⁱ j k y) x)
      (λ x y → subst (λ z → cmpInstant z k ≡ lt) (sym (eqⁱ i j x)) y)
      (λ x y → subst (λ z → cmpInstant z k ≡ eq) (sym (eqⁱ i j x)) y)
      (λ x y → ltᵗ p q r x y) h₁ h₂

mutual
  gtˡ : ∀ a b → cmpLabel a b ≡ gt → cmpLabel b a ≡ lt
  gtˡ (ix m)  (ix n)  h = ℕ-gt {m} {n} h
  gtˡ (sub p) (sub q) h = gtᵖ p q h
  gtˡ (sub _) (ix _)  _ = refl
  gtˡ last    (ix _)  _ = refl
  gtˡ last    (sub _) _ = refl
  gtˡ (ix _)  (sub _) ()
  gtˡ (ix _)  last    ()
  gtˡ (sub _) last    ()
  gtˡ last    last    ()

  gtⁱ : ∀ i j → cmpInstant i j ≡ gt → cmpInstant j i ≡ lt
  gtⁱ frame         frame         ()
  gtⁱ frame         (cascade _ _) ()
  gtⁱ (cascade _ _) frame         _ = refl
  gtⁱ (cascade t e) (cascade u d) h =
    lexi-flip (cmpℕ t u) (cmpPos e d) (cmpℕ u t) (cmpPos d e) h
      (ℕ-gt {t} {u})
      (λ x → subst (λ z → cmpℕ z t ≡ eq) (ℕ-≡ {t} {u} x) (ℕ-eq t))
      (λ x → gtᵖ e d x)

  gtᵗ : ∀ (p q : Path) → cmpPath p q ≡ gt → cmpPath q p ≡ lt
  gtᵗ []      []      ()
  gtᵗ []      (_ ∷ _) ()
  gtᵗ (_ ∷ _) []      _ = refl
  gtᵗ (a ∷ p) (b ∷ q) h =
    lexi-flip (cmpLabel a b) (cmpPath p q) (cmpLabel b a) (cmpPath q p) h
      (λ x → gtˡ a b x)
      (λ x → subst (λ z → cmpLabel z a ≡ eq) (eqˡ a b x) (reflˡ a))
      (λ x → gtᵗ p q x)

  gtᵖ : ∀ p q → cmpPos p q ≡ gt → cmpPos q p ≡ lt
  gtᵖ (i ∙ p) (j ∙ q) h =
    lexi-flip (cmpInstant i j) (cmpPath p q) (cmpInstant j i) (cmpPath q p) h
      (λ x → gtⁱ i j x)
      (λ x → subst (λ z → cmpInstant z i ≡ eq) (eqⁱ i j x) (reflⁱ i))
      (λ x → gtᵗ p q x)

private
  f≢t : false ≡ true → ⊥
  f≢t ()

between : ∀ {a b c} → a <ᵖ b ≡ true → b <ᵖ c ≡ true → instant a ≡ instant c → instant b ≡ instant a
between {i ∙ p} {j ∙ q} {_ ∙ r} ab bc refl with cmpInstant i j in ij
... | eq = sym (eqⁱ i j ij)
... | gt = ⊥-elim (f≢t ab)
... | lt = ⊥-elim (f≢t (subst (λ x → isLt (lexi x (cmpPath q r)) ≡ true) (flipⁱ i j ij) bc))
