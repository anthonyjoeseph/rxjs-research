{-# OPTIONS --guardedness #-}

module denotation.Events where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import denotation.Position using (Time; Pos; Path; ix; sub; last; _∙_; tick; _⊕_; Root; nested; fired; _▸_; lt; eq; gt; lexi; isLt; isEq;
  cmpLabel; cmpInstant; cmpPath; cmpPos; _<ˡ_; _<ᵖ_; insideᵗ; inside)
open import denotation.Simultaneity using (ℕ-lt; ℕ-eq; reflˡ; reflⁱ; reflᵖ; eqˡ; eqⁱ; eqᵖ; ltˡ; ltⁱ; ltᵖ; gtᵖ; lexi-l; isLt-lt)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Data.Nat using (_<_; _≤_; z≤n)
open import Data.Nat.Properties using (n<1+n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
import Data.Nat as ℕ

------------------------------------------------------------------------
-- Timelines: what a cold leaf says, and what a runtime reports

-- Frames, each a synchronous burst.  A runtime reports one, with ticks
-- absolute.
mutual
  data ML (A : Set) : Set where
    done  : ML A                      -- completed
    quiet : ML A                      -- silent forever, never completes
    at    : Time → Burst A → ML A     -- the next frame

  data Burst (A : Set) : Set where
    emit  : A → Burst∞ A → Burst A
    stall : Burst∞ A → Burst A        -- a synchronous step emitting nothing
    close : ML∞ A → Burst A           -- the burst is over; the rest of the timeline

  record Burst∞ (A : Set) : Set where
    coinductive
    field force : Burst A

  record ML∞ (A : Set) : Set where
    coinductive
    field force : ML A

-- WHAT A COLD LEAF SAYS: frames at strictly increasing ticks, relative
-- to its subscription, by construction.  Every frame of `From A t` is at
-- `t` or later, and the timeline after a frame at `t′` is `From A (suc t′)`.
-- A frame's values between stalls are finite: a synchronous run that
-- never yields would hang rxjs, and its scripted colds are finite lists.
mutual
  data From (A : Set) (t : Time) : Set where
    done  : From A t
    quiet : From A t
    at    : ∀ t′ → t ≤ t′ → Frame A t′ → From A t

  data Frame (A : Set) (t : Time) : Set where
    emit  : A → Frame A t → Frame A t
    stall : Frame∞ A t → Frame A t
    close : From∞ A (suc t) → Frame A t

  record Frame∞ (A : Set) (t : Time) : Set where
    coinductive
    field force : Frame A t

  record From∞ (A : Set) (t : Time) : Set where
    coinductive
    field force : From A t

------------------------------------------------------------------------
-- The cold leaf

-- WHAT A COLD LEAF IS: a timeline fixed relative to its subscription, or
-- `fresh`, which emits the position it is subscribed at and completes —
-- a name no other subscription has.  So a leaf is a timeline read at its
-- subscription position, and every runtime that knows the position plays
-- the same one.  In `Set₁` because the leaf slot of a program tree is.
data Timeline : Set → Set₁ where
  fixed : ∀ {A} → From A 0 → Timeline A
  fresh : ∀ {A} → (Pos → A) → Timeline A

timelineAt : ∀ {A} → Timeline A → Pos → From A 0
timelineAt (fixed m) p = m
timelineAt (fresh f) p = at 0 z≤n (emit (f p) (close λ where
  .From∞.force → done))

------------------------------------------------------------------------
-- The order, a position at a time

-- Positions of one instant compare as their paths do.
private
  _<ᵗ_ : Path → Path → Bool
  p <ᵗ q = isLt (cmpPath p q)

  one : ∀ i x y → cmpPos (i ∙ x) (i ∙ y) ≡ cmpPath x y
  one i x y = cong (λ c → lexi c (cmpPath x y)) (reflⁱ i)

  within : ∀ i x y → (i ∙ x) <ᵖ (i ∙ y) ≡ x <ᵗ y
  within i x y = cong isLt (one i x y)

<ᵖ-trans : ∀ p q r → p <ᵖ q ≡ true → q <ᵖ r ≡ true → p <ᵖ r ≡ true
<ᵖ-trans p q r h₁ h₂ = cong isLt (ltᵖ p q r (isLt-lt {cmpPos p q} h₁) (isLt-lt {cmpPos q r} h₂))

<ᵖ-irrefl : ∀ p → p <ᵖ p ≡ false
<ᵖ-irrefl p = cong isLt (reflᵖ p)

<ᵖ-asym : ∀ p q → p <ᵖ q ≡ true → q <ᵖ p ≡ false
<ᵖ-asym p q h with q <ᵖ p in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans p q p h e)) (<ᵖ-irrefl p)

-- No later is earlier or the same.
<ᵖ-split : ∀ p q → q <ᵖ p ≡ false → p <ᵖ q ≡ true ⊎ p ≡ q
<ᵖ-split p q h with cmpPos p q in c
... | lt = inj₁ refl
... | eq = inj₂ (eqᵖ p q c)
... | gt with () ← trans (sym h) (cong isLt (gtᵖ p q c))

------------------------------------------------------------------------
-- The same, along a path

private
  pastᵗ : ∀ (p : Path) → cmpPath (p ++ [ ix 0 ]) [] ≡ gt
  pastᵗ []      = refl
  pastᵗ (_ ∷ _) = refl

  top : ∀ a → isLt (lexi (cmpLabel a (ix 0)) gt) ≡ false
  top (ix m) with 0 <ᵇ m
  ... | true  = refl
  ... | false = refl
  top (sub _) = refl
  top last    = refl

  shiftᵗ : ∀ (p q : Path) → p <ᵗ q ≡ false → (p ++ [ ix 0 ]) <ᵗ (q ++ [ ix 0 ]) ≡ false
  shiftᵗ []      []      h = refl
  shiftᵗ (a ∷ p) []      h rewrite pastᵗ p = top a
  shiftᵗ (a ∷ p) (b ∷ q) h with cmpLabel a b
  ... | eq = shiftᵗ p q h
  ... | gt = refl

  stepᵗ : ∀ (p q : Path) → p <ᵗ q ≡ true → q <ᵗ (p ++ [ ix 0 ]) ≡ false
  stepᵗ []      []                ()
  stepᵗ []      (ix zero ∷ [])    h = refl
  stepᵗ []      (ix zero ∷ _ ∷ _) h = refl
  stepᵗ []      (ix (suc _) ∷ _)  h = refl
  stepᵗ []      (sub _ ∷ _)       h = refl
  stepᵗ []      (last ∷ _)        h = refl
  stepᵗ (a ∷ p) []                ()
  stepᵗ (a ∷ p) (b ∷ q)           h with cmpLabel a b in c | cmpLabel b a in d
  ... | lt | lt with () ← trans (sym (reflˡ a)) (ltˡ a b a c d)
  ... | lt | eq with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel a z ≡ lt) (eqˡ b a d) c)
  ... | lt | gt = refl
  ... | eq | lt with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel z a ≡ lt) (sym (eqˡ a b c)) d)
  ... | eq | eq = stepᵗ p q h
  ... | eq | gt with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel z a ≡ gt) (sym (eqˡ a b c)) d)
  ... | gt | _  with () ← h

  belowᵗ : ∀ (p : Path) {l} ys → p <ᵗ (p ++ l ∷ ys) ≡ true
  belowᵗ []      ys = refl
  belowᵗ (a ∷ p) {l} ys = trans (cong (λ c → isLt (lexi c (cmpPath p (p ++ l ∷ ys)))) (reflˡ a)) (belowᵗ p ys)

  partᵗ : ∀ (p : Path) {a b} ys zs → a <ˡ b ≡ true → (p ++ a ∷ ys) <ᵗ (p ++ b ∷ zs) ≡ true
  partᵗ [] {a} {b} ys zs h = cong isLt (lexi-l {cmpLabel a b} {cmpPath ys zs} (isLt-lt {cmpLabel a b} h))
  partᵗ (x ∷ p) {a} {b} ys zs h =
    trans (cong (λ c → isLt (lexi c (cmpPath (p ++ a ∷ ys) (p ++ b ∷ zs)))) (reflˡ x)) (partᵗ p ys zs h)

  downᵗ : ∀ (k h : Path) x y → k <ᵗ h ≡ true → (∀ l ls → h ≡ k ++ l ∷ ls → ⊥) → (k ++ [ x ]) <ᵗ (h ++ [ y ]) ≡ true
  downᵗ []      []      x y () ne
  downᵗ []      (l ∷ h) x y _  ne = ⊥-elim (ne l h refl)
  downᵗ (a ∷ k) []      x y () ne
  downᵗ (a ∷ k) (b ∷ h) x y kh ne with cmpLabel a b in c
  ... | lt = refl
  ... | eq = downᵗ k h x y kh (λ l ls e → ne l ls (cong₂ _∷_ (sym (eqˡ a b c)) e))
  ... | gt with () ← kh

  overᵗ : ∀ (k h : Path) ys → (k ++ [ ix 0 ]) <ᵗ h ≡ true → (∀ l ls → h ≡ k ++ l ∷ ls → ⊥) → (k ++ ys) <ᵗ h ≡ true
  overᵗ []      []      ys () ne
  overᵗ []      (l ∷ h) ys _  ne = ⊥-elim (ne l h refl)
  overᵗ (a ∷ k) []      ys () ne
  overᵗ (a ∷ k) (b ∷ h) ys kh ne with cmpLabel a b in c
  ... | lt = refl
  ... | eq = overᵗ k h ys kh (λ l ls e → ne l ls (cong₂ _∷_ (sym (eqˡ a b c)) e))
  ... | gt with () ← kh

  nextᵗ : ∀ (p q : Path) y → p <ᵗ q ≡ true → (p ++ [ ix 0 ]) <ᵗ (q ++ [ y ]) ≡ true
  nextᵗ []      []                  y ()
  nextᵗ []      (ix zero ∷ [])      y h = refl
  nextᵗ []      (ix zero ∷ _ ∷ _)   y h = refl
  nextᵗ []      (ix (suc _) ∷ _)    y h = refl
  nextᵗ []      (sub _ ∷ _)         y h = refl
  nextᵗ []      (last ∷ _)          y h = refl
  nextᵗ (a ∷ p) []                  y ()
  nextᵗ (a ∷ p) (b ∷ q)             y h with cmpLabel a b
  ... | lt = refl
  ... | eq = nextᵗ p q y h
  ... | gt with () ← h

  apartᵗ : ∀ (p q y : Path) → p <ᵗ q ≡ true → (∀ ys → q ≡ p ++ ys → ⊥) → (p ++ y) <ᵗ q ≡ true
  apartᵗ []      []      y () ne
  apartᵗ []      (b ∷ q) y _  ne = ⊥-elim (ne (b ∷ q) refl)
  apartᵗ (a ∷ p) []      y () ne
  apartᵗ (a ∷ p) (b ∷ q) y h  ne with cmpLabel a b in c
  ... | lt = refl
  ... | eq = apartᵗ p q y h (λ ys e → ne ys (cong₂ _∷_ (sym (eqˡ a b c)) e))
  ... | gt with () ← h

  betweenᵗ : ∀ (p q ys : Path) → p <ᵗ q ≡ true → q <ᵗ (p ++ ys) ≡ true → Σ Path (λ zs → q ≡ p ++ zs)
  betweenᵗ []      q       ys _ _  = q , refl
  betweenᵗ (a ∷ p) []      ys () _
  betweenᵗ (a ∷ p) (b ∷ q) ys h h′ with cmpLabel a b in c | cmpLabel b a in d
  ... | lt | lt with () ← trans (sym (reflˡ a)) (ltˡ a b a c d)
  ... | lt | eq with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel a z ≡ lt) (eqˡ b a d) c)
  ... | lt | gt with () ← h′
  ... | eq | lt with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel z a ≡ lt) (sym (eqˡ a b c)) d)
  ... | eq | gt with () ← trans (sym (reflˡ a)) (subst (λ z → cmpLabel z a ≡ gt) (sym (eqˡ a b c)) d)
  ... | gt | _  with () ← h
  ... | eq | eq with betweenᵗ p q ys h h′
  ...   | zs , e = zs , cong₂ _∷_ (sym (eqˡ a b c)) e

  inside-++ᵗ : ∀ (r k ys : Path) → insideᵗ r k ≡ true → insideᵗ r (k ++ ys) ≡ true
  inside-++ᵗ []      k       ys i = refl
  inside-++ᵗ (a ∷ r) []      ys ()
  inside-++ᵗ (a ∷ r) (b ∷ k) ys i with cmpLabel a b
  ... | lt with () ← i
  ... | eq = inside-++ᵗ r k ys i
  ... | gt with () ← i

  inside-selfᵗ : ∀ (r : Path) → insideᵗ r r ≡ true
  inside-selfᵗ []      = refl
  inside-selfᵗ (a ∷ r) = trans (cong (λ c → isEq c ∧ insideᵗ r r) (reflˡ a)) (inside-selfᵗ r)

  -- Two instants that compare `eq` are one, and none compares `lt` both ways.
  same-or : ∀ i j → cmpInstant i j ≡ lt → cmpInstant j i ≡ lt → ⊥
  same-or i j c d with () ← trans (sym (reflⁱ i)) (ltⁱ i j i c d)

  lt-eq : ∀ i j → cmpInstant i j ≡ lt → cmpInstant j i ≡ eq → ⊥
  lt-eq i j c d with () ← trans (sym (reflⁱ i)) (subst (λ z → cmpInstant i z ≡ lt) (eqⁱ j i d) c)

  eq-gt : ∀ i j → cmpInstant i j ≡ eq → cmpInstant j i ≡ gt → ⊥
  eq-gt i j c d with () ← trans (sym (reflⁱ i)) (subst (λ z → cmpInstant z i ≡ gt) (sym (eqⁱ i j c)) d)

------------------------------------------------------------------------
-- The same, between positions

-- What is no earlier stays so a step past each.
<ᵖ-shift : ∀ p q → p <ᵖ q ≡ false → (p ⊕ [ ix 0 ]) <ᵖ (q ⊕ [ ix 0 ]) ≡ false
<ᵖ-shift (i ∙ x) (j ∙ y) h with cmpInstant i j
... | lt with () ← h
... | eq = shiftᵗ x y h
... | gt = refl

-- Nothing lies strictly between a position and the one just past it.
<ᵖ-step : ∀ p q → p <ᵖ q ≡ true → q <ᵖ (p ⊕ [ ix 0 ]) ≡ false
<ᵖ-step (i ∙ x) (j ∙ y) h with cmpInstant i j in c | cmpInstant j i in d
... | lt | lt = ⊥-elim (same-or i j c d)
... | lt | eq = ⊥-elim (lt-eq i j c d)
... | lt | gt = refl
... | eq | lt = ⊥-elim (lt-eq j i d c)
... | eq | eq = stepᵗ x y h
... | eq | gt = ⊥-elim (eq-gt i j c d)
... | gt | _  with () ← h

-- A position is before every position below it, and of two positions
-- that part at one label, the earlier label's is the earlier.
<ᵖ-below : ∀ p {l} ys → p <ᵖ (p ⊕ (l ∷ ys)) ≡ true
<ᵖ-below (i ∙ x) {l} ys = trans (within i x (x ++ l ∷ ys)) (belowᵗ x ys)

<ᵖ-part : ∀ p {a b} ys zs → a <ˡ b ≡ true → (p ⊕ (a ∷ ys)) <ᵖ (p ⊕ (b ∷ zs)) ≡ true
<ᵖ-part (i ∙ x) {a} {b} ys zs h = trans (within i (x ++ a ∷ ys) (x ++ b ∷ zs)) (partᵗ x ys zs h)

-- A burst's steps part in order, whatever its root.
<ᵖ-▸ : ∀ r {a b} → a <ˡ b ≡ true → (r ▸ a) <ᵖ (r ▸ b) ≡ true
<ᵖ-▸ (nested p)  h = <ᵖ-part p [] [] h
<ᵖ-▸ (fired t e) h rewrite ℕ-eq t | reflᵖ e | isLt-lt h = refl

-- A burst's values part in order.
<ᵖ-ix : ∀ i → ix i <ˡ ix (suc i) ≡ true
<ᵖ-ix i = cong isLt (ℕ-lt {i} {suc i} (n<1+n i))

-- A later tick comes later.
ix-< : ∀ {m n} → m < n → ix m <ˡ ix n ≡ true
ix-< {m} {n} l = cong isLt (ℕ-lt {m} {n} l)

-- Positions in order and not one below the other stay in order a label
-- down; and what is past `p` is past `p ⊕ [ ix 0 ]` a label down.
<ᵖ-down : ∀ k h x y → k <ᵖ h ≡ true → (∀ l ls → h ≡ k ⊕ (l ∷ ls) → ⊥) → (k ⊕ [ x ]) <ᵖ (h ⊕ [ y ]) ≡ true
<ᵖ-down (i ∙ a) (j ∙ b) x y kh ne with cmpInstant i j in c
... | lt = refl
... | gt with () ← kh
... | eq with eqⁱ i j c
...   | refl = downᵗ a b x y kh (λ l ls e → ne l ls (cong (i ∙_) e))

-- Past `k ⊕ [ ix 0 ]` and not below `k`, past everything below `k`.
<ᵖ-over : ∀ k h ys → (k ⊕ [ ix 0 ]) <ᵖ h ≡ true → (∀ l ls → h ≡ k ⊕ (l ∷ ls) → ⊥) → (k ⊕ ys) <ᵖ h ≡ true
<ᵖ-over (i ∙ a) (j ∙ b) ys kh ne with cmpInstant i j in c
... | lt = refl
... | gt with () ← kh
... | eq with eqⁱ i j c
...   | refl = overᵗ a b ys kh (λ l ls e → ne l ls (cong (i ∙_) e))

<ᵖ-next : ∀ p q y → p <ᵖ q ≡ true → (p ⊕ [ ix 0 ]) <ᵖ (q ⊕ [ y ]) ≡ true
<ᵖ-next (i ∙ a) (j ∙ b) y h with cmpInstant i j
... | lt = refl
... | eq = nextᵗ a b y h
... | gt with () ← h

-- Past `p` and not under it: past everything under it.
<ᵖ-apart : ∀ p q y → p <ᵖ q ≡ true → (∀ ys → q ≡ p ⊕ ys → ⊥) → (p ⊕ y) <ᵖ q ≡ true
<ᵖ-apart (i ∙ a) (j ∙ b) y h ne with cmpInstant i j in c
... | lt = refl
... | gt with () ← h
... | eq with eqⁱ i j c
...   | refl = apartᵗ a b y h (λ ys e → ne ys (cong (i ∙_) e))

-- Past `p` and before something under it: under it.
<ᵖ-between : ∀ p q ys → p <ᵖ q ≡ true → q <ᵖ (p ⊕ ys) ≡ true → Σ Path (λ zs → q ≡ p ⊕ zs)
<ᵖ-between (i ∙ a) (j ∙ b) ys h h′ with cmpInstant i j in c | cmpInstant j i in d
... | lt | lt = ⊥-elim (same-or i j c d)
... | lt | eq = ⊥-elim (lt-eq i j c d)
... | lt | gt with () ← h′
... | eq | lt = ⊥-elim (lt-eq j i d c)
... | eq | gt = ⊥-elim (eq-gt i j c d)
... | gt | _  with () ← h
... | eq | eq with eqⁱ i j c
...   | refl with betweenᵗ a b ys h h′
...     | zs , e = zs , cong (i ∙_) e

-- Under `r`, and so is everything under it.
inside-++ : ∀ r k ys → inside r k ≡ true → inside r (k ⊕ ys) ≡ true
inside-++ (i ∙ r) (j ∙ k) ys h with cmpInstant i j
... | lt with () ← h
... | eq = inside-++ᵗ r k ys h
... | gt with () ← h

-- Under `r`, a label at a time.
inside-cons : ∀ a r b k → insideᵗ (a ∷ r) (b ∷ k) ≡ true → a ≡ b × insideᵗ r k ≡ true
inside-cons a r b k i with cmpLabel a b in e
... | lt with () ← i
... | eq = eqˡ a b e , i
... | gt with () ← i

-- Under itself.
inside-self : ∀ r → inside r r ≡ true
inside-self (i ∙ r) = trans (cong (λ c → isEq c ∧ insideᵗ r r) (reflⁱ i)) (inside-selfᵗ r)

------------------------------------------------------------------------
-- What a subscriber sees

-- WHAT A CUT LEAVES RUNNING.  rxjs subscribes a connect's source after
-- its body and attaches it to the subscriber only once the source's
-- subscribe returns, so nothing stops that subscribe burst: not the body
-- ending, not a cut above, not a cut before the source is even reached.
-- A run's tail is what remains of every such burst it has begun: skips
-- only, in position order, idle once the last is done.  It shows
-- nothing, but its steps are taken, and one that never returns holds up
-- everything after it.
mutual
  data Tail : Set where
    pin  : Pos → Tail∞ → Tail
    idle : Tail

  record Tail∞ : Set where
    coinductive
    field later : Tail

open Tail∞

-- Two tails run side by side, in position order.
sooner : Pos → Tail → Bool
sooner k idle       = true
sooner k (pin k′ _) = k <ᵖ k′

mutual
  _∪_ : Tail → Tail → Tail
  idle    ∪ u = u
  pin k r ∪ u = first k r u (sooner k u)

  first : Pos → Tail∞ → Tail → Bool → Tail
  first k r u          true  = pin k λ where .later → later r ∪ u
  first k r idle       false = pin k r
  first k r (pin k′ u) false = pin k′ λ where .later → pin k r ∪ later u

infixr 5 _∪_

-- Events at strictly increasing positions.  A `skip` is a step that
-- shows nothing — a dropped element, a `defer`'s subscription — kept so
-- that every step yields a constructor, and positioned so that a merge
-- can still place it.  A run in progress is a state: its next event, and
-- its tail were it cut there, before that event — which a completion
-- next leaves running too.
mutual
  data Events (A : Set) : Set where
    out  : Pos → A → Events∞ A → Events A
    skip : Pos → Events∞ A → Events A
    end  : Pos → Events A             -- completed, at this position
    hush : Events A                   -- silent forever, never completes

  record Events∞ (A : Set) : Set where
    coinductive
    field
      force : Events A
      cut   : Tail

open Events∞

------------------------------------------------------------------------
-- A cold leaf, placed

-- A burst at `r` puts its i-th step at `r ▸ ix i` and ends at
-- `r ▸ last`, which is also where the timer for the next frame is
-- created: after the burst and all it caused.  A frame at tick 0 is the
-- subscribe burst, `nested` at the subscription, so all of it is one
-- instant, its completion included; a later frame is `fired`, so each of
-- its steps is an instant of its own: every call an async callback makes
-- into its subscriber, a completion as much as a value.  A timer firing
-- shows no step of its own: at the root a hot's rekeying under `sub`
-- puts it after the burst below it, and at the burst's first position it
-- ties with that step, where an event must rise.
mutual
  frames : ∀ {A t} → Time → Pos → From A t → Events A
  frames τ e done       = end e
  frames τ e quiet      = hush
  frames τ e (at t _ b) = burst τ (fired (τ + t) e) 0 b

  burst : ∀ {A t} → Time → Root → ℕ → Frame A t → Events A
  burst τ r i (emit a k) = out (r ▸ ix i) a λ where
    .force → burst τ r (suc i) k
    .cut   → idle
  burst τ r i (stall k)  = skip (r ▸ ix i) λ where
    .force → burst τ r (suc i) (Frame∞.force k)
    .cut   → idle
  burst τ r i (close k)  = skip (r ▸ ix i) λ where
    .force → frames τ (r ▸ last) (From∞.force k)
    .cut   → idle

start : ∀ {A} → Pos → From A 0 → Events A
start p (at zero _ b) = burst (tick p) (nested p) 0 b
start p m             = frames (tick p) (p ⊕ [ last ]) m

-- `of`'s steps from the i-th on, under the subscription at `p`.
ofᴱ : ∀ {A} → Pos → ℕ → List A → Events A
ofᴱ p i []       = end (p ⊕ [ last ])
ofᴱ p i (x ∷ xs) = out (p ⊕ [ ix i ]) x λ where
  .force → ofᴱ p (suc i) xs
  .cut   → idle
