{-# OPTIONS --guardedness #-}

module denotation.MonotonicList.Events where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; _++_; [_])
open import Data.Product using (_×_; _,_; Σ)
open import Data.Nat using (ℕ; zero; suc; _<ᵇ_)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Data.Bool using (T)
open import Data.Nat using (_<_; _≤_; z≤n)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; ≮⇒≥; ≤-antisym; <-trans; n≮n; n<1+n; <⇒≤; ≤-reflexive)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary using (yes; no)
import Data.Nat as ℕ

------------------------------------------------------------------------
-- Timelines: what a cold leaf says, and what a runtime reports

Time : Set
Time = ℕ

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
mutual
  data From (A : Set) (t : Time) : Set where
    done  : From A t
    quiet : From A t
    at    : ∀ t′ → t ≤ t′ → Frame A t′ → From A t

  data Frame (A : Set) (t : Time) : Set where
    emit  : A → Frame∞ A t → Frame A t
    stall : Frame∞ A t → Frame A t
    close : From∞ A (suc t) → Frame A t

  record Frame∞ (A : Set) (t : Time) : Set where
    coinductive
    field force : Frame A t

  record From∞ (A : Set) (t : Time) : Set where
    coinductive
    field force : From A t

------------------------------------------------------------------------
-- Positions

-- WHERE AN EVENT SITS IN THE WHOLE RUN.  A tick says when; it does not
-- say which of two simultaneous events comes first, and rxjs always
-- does.  A position is a path in the run's call tree — an event's
-- effects are its children — read in pre-order, which is execution
-- order.  So a merge is a sorted merge, and nothing coordinates it.
--
-- Three kinds of step.  `ix i`: an operator's i-th effect.  `sub p`: a
-- subject delivering to the subscriber that joined at `p`, so a subject's
-- subscribers come in the order they joined.  `last`: after every other
-- effect — where a burst ends and its completion sits.
--
-- A timer cascade at tick t is rooted at `ix t ∷ sub e ∷ []`, where `e`
-- is the position its timer was created at.  Same-tick timers therefore
-- fire in creation order, as in rxjs.
data Label : Set where
  ix   : ℕ → Label
  sub  : List Label → Label
  last : Label

Pos : Set
Pos = List Label

-- The root subscription: tick 0, before any timer.
root : Pos
root = ix 0 ∷ []

tick : Pos → Time
tick []          = 0
tick (ix t ∷ _)  = t
tick (sub _ ∷ _) = 0
tick (last ∷ _)  = 0

-- Positions' equality: all a name is read for.
mutual
  _≟ˡ_ : DecidableEquality Label
  ix m  ≟ˡ ix n  with m ℕ.≟ n
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  sub p ≟ˡ sub q with p ≟ᵖ q
  ... | yes refl = yes refl
  ... | no ne    = no λ { refl → ne refl }
  last  ≟ˡ last  = yes refl
  ix _  ≟ˡ sub _ = no λ ()
  ix _  ≟ˡ last  = no λ ()
  sub _ ≟ˡ ix _  = no λ ()
  sub _ ≟ˡ last  = no λ ()
  last  ≟ˡ ix _  = no λ ()
  last  ≟ˡ sub _ = no λ ()

  _≟ᵖ_ : DecidableEquality Pos
  []      ≟ᵖ []      = yes refl
  []      ≟ᵖ (_ ∷ _) = no λ ()
  (_ ∷ _) ≟ᵖ []      = no λ ()
  (a ∷ p) ≟ᵖ (b ∷ q) with a ≟ˡ b | p ≟ᵖ q
  ... | yes refl | yes refl = yes refl
  ... | no ne    | _        = no λ { refl → ne refl }
  ... | yes _    | no ne    = no λ { refl → ne refl }

------------------------------------------------------------------------
-- The cold leaf

-- WHAT A COLD LEAF IS: a timeline fixed relative to its subscription, or
-- `fresh`, which emits the position it is subscribed at and completes —
-- a name no other subscription has.  So a leaf is a timeline read at its
-- subscription position, and every runtime that knows the position plays
-- the same one.  In `Set₁` because the leaf slot of a program tree is.
data Timeline : Set → Set₁ where
  fixed : ∀ {A} → From A 0 → Timeline A
  fresh : Timeline Pos

timelineAt : ∀ {A} → Timeline A → Pos → From A 0
timelineAt (fixed m) p = m
timelineAt fresh     p = at 0 z≤n (emit p λ where
  .Frame∞.force → close λ where
    .From∞.force → done)

private
  data Cmp : Set where
    lt eq gt : Cmp

  cmpℕ : ℕ → ℕ → Cmp
  cmpℕ m n = if m <ᵇ n then lt else if n <ᵇ m then gt else eq

  lexi : Cmp → Cmp → Cmp
  lexi eq r = r
  lexi lt _ = lt
  lexi gt _ = gt

  mutual
    cmpLabel : Label → Label → Cmp
    cmpLabel (ix m)  (ix n)  = cmpℕ m n
    cmpLabel (ix _)  (sub _) = lt
    cmpLabel (ix _)  last    = lt
    cmpLabel (sub _) (ix _)  = gt
    cmpLabel (sub p) (sub q) = cmpPos p q
    cmpLabel (sub _) last    = lt
    cmpLabel last    (ix _)  = gt
    cmpLabel last    (sub _) = gt
    cmpLabel last    last    = eq

    cmpPos : Pos → Pos → Cmp
    cmpPos []      []      = eq
    cmpPos []      (_ ∷ _) = lt
    cmpPos (_ ∷ _) []      = gt
    cmpPos (a ∷ p) (b ∷ q) = lexi (cmpLabel a b) (cmpPos p q)

  isLt : Cmp → Bool
  isLt lt = true
  isLt eq = false
  isLt gt = false

_<ᵖ_ : Pos → Pos → Bool
p <ᵖ q = isLt (cmpPos p q)

-- `k` lies under `r`: an effect, however deep, of what sits at `r`.
inside : Pos → Pos → Bool
inside []      k       = true
inside (_ ∷ _) []      = false
inside (a ∷ r) (b ∷ k) = same (cmpLabel a b) r k
  where same : Cmp → Pos → Pos → Bool
        same eq r k = inside r k
        same _  _ _ = false

-- The order is an order: transitive, and led by the tick.
private
  lt-ℕ : ∀ {m n} → cmpℕ m n ≡ lt → m < n
  lt-ℕ {m} {n} h with m <ᵇ n in e | n <ᵇ m
  lt-ℕ {m} {n} h  | true  | _     = <ᵇ⇒< m n (subst T (sym e) tt)
  lt-ℕ {m} {n} () | false | true
  lt-ℕ {m} {n} () | false | false

  ℕ-lt : ∀ {m n} → m < n → cmpℕ m n ≡ lt
  ℕ-lt {m} {n} l with m <ᵇ n in e
  ... | true  = refl
  ... | false with subst T e (<⇒<ᵇ l)
  ...   | ()

  eq-ℕ : ∀ {m n} → cmpℕ m n ≡ eq → m ≡ n
  eq-ℕ {m} {n} h with m <ᵇ n in e₁ | n <ᵇ m in e₂
  eq-ℕ {m} {n} () | true  | _
  eq-ℕ {m} {n} () | false | true
  eq-ℕ {m} {n} h  | false | false =
    ≤-antisym (≮⇒≥ λ l → subst T e₂ (<⇒<ᵇ l)) (≮⇒≥ λ l → subst T e₁ (<⇒<ᵇ l))

  lexi-lt : ∀ c r → lexi c r ≡ lt → c ≡ lt ⊎ (c ≡ eq × r ≡ lt)
  lexi-lt lt r h = inj₁ refl
  lexi-lt eq r h = inj₂ (refl , h)
  lexi-lt gt r ()

  lexi-eq : ∀ c r → lexi c r ≡ eq → c ≡ eq × r ≡ eq
  lexi-eq lt r ()
  lexi-eq eq r h = refl , h
  lexi-eq gt r ()

  mutual
    eq-label : ∀ a b → cmpLabel a b ≡ eq → a ≡ b
    eq-label (ix m)  (ix n)  h = cong ix (eq-ℕ {m} {n} h)
    eq-label (sub p) (sub q) h = cong sub (eq-pos p q h)
    eq-label last    last    h = refl
    eq-label (ix _)  (sub _) ()
    eq-label (ix _)  last    ()
    eq-label (sub _) (ix _)  ()
    eq-label (sub _) last    ()
    eq-label last    (ix _)  ()
    eq-label last    (sub _) ()

    eq-pos : ∀ p q → cmpPos p q ≡ eq → p ≡ q
    eq-pos []      []      h = refl
    eq-pos []      (_ ∷ _) ()
    eq-pos (_ ∷ _) []      ()
    eq-pos (a ∷ p) (b ∷ q) h with lexi-eq (cmpLabel a b) (cmpPos p q) h
    ... | x , y = cong₂ _∷_ (eq-label a b x) (eq-pos p q y)

  mutual
    lt-label : ∀ a b c → cmpLabel a b ≡ lt → cmpLabel b c ≡ lt → cmpLabel a c ≡ lt
    lt-label (ix m)  (ix n)  (ix k)  h₁ h₂ = ℕ-lt {m} {k} (<-trans (lt-ℕ {m} {n} h₁) (lt-ℕ {n} {k} h₂))
    lt-label (ix _)  _       (sub _) _  _  = refl
    lt-label (ix _)  _       last    _  _  = refl
    lt-label (ix _)  (sub _) (ix _)  _  ()
    lt-label (ix _)  last    (ix _)  _  ()
    lt-label (sub p) (sub q) (sub r) h₁ h₂ = lt-pos p q r h₁ h₂
    lt-label (sub _) _       last    _  _  = refl
    lt-label (sub _) (ix _)  _       () _
    lt-label (sub _) (sub _) (ix _)  _  ()
    lt-label (sub _) last    (ix _)  _  ()
    lt-label (sub _) last    (sub _) _  ()
    lt-label last    (ix _)  _       () _
    lt-label last    (sub _) _       () _
    lt-label last    last    _       () _

    lt-pos : ∀ p q r → cmpPos p q ≡ lt → cmpPos q r ≡ lt → cmpPos p r ≡ lt
    lt-pos []      (_ ∷ _) (_ ∷ _) _  _  = refl
    lt-pos []      []      _       () _
    lt-pos (_ ∷ _) []      _       () _
    lt-pos _       (_ ∷ _) []      _  ()
    lt-pos (a ∷ p) (b ∷ q) (c ∷ r) h₁ h₂
      with lexi-lt (cmpLabel a b) (cmpPos p q) h₁ | lexi-lt (cmpLabel b c) (cmpPos q r) h₂
    ... | inj₁ x       | inj₁ y       rewrite lt-label a b c x y = refl
    ... | inj₁ x       | inj₂ (y , _) rewrite subst (λ z → cmpLabel a z ≡ lt) (eq-label b c y) x = refl
    ... | inj₂ (x , _) | inj₁ y       rewrite subst (λ z → cmpLabel z c ≡ lt) (sym (eq-label a b x)) y = refl
    ... | inj₂ (x , u) | inj₂ (y , v)
      rewrite subst (λ z → cmpLabel z c ≡ eq) (sym (eq-label a b x)) y | lt-pos p q r u v = refl

  refl-ℕ : ∀ m → cmpℕ m m ≡ eq
  refl-ℕ m with m <ᵇ m in e
  ... | true  = ⊥-elim (n≮n m (<ᵇ⇒< m m (subst T (sym e) tt)))
  ... | false = refl

  mutual
    refl-label : ∀ a → cmpLabel a a ≡ eq
    refl-label (ix m)  = refl-ℕ m
    refl-label (sub p) = refl-pos p
    refl-label last    = refl

    refl-pos : ∀ p → cmpPos p p ≡ eq
    refl-pos []      = refl
    refl-pos (a ∷ p) rewrite refl-label a = refl-pos p

  isLt-lt : ∀ {c} → isLt c ≡ true → c ≡ lt
  isLt-lt {lt} h = refl
  isLt-lt {eq} ()
  isLt-lt {gt} ()

  gt-ℕ : ∀ {m n} → cmpℕ m n ≡ gt → n < m
  gt-ℕ {m} {n} h with m <ᵇ n | n <ᵇ m in e
  gt-ℕ {m} {n} () | true  | _
  gt-ℕ {m} {n} h  | false | true  = <ᵇ⇒< n m (subst T (sym e) tt)
  gt-ℕ {m} {n} () | false | false

  lexi-gt : ∀ c r → lexi c r ≡ gt → c ≡ gt ⊎ (c ≡ eq × r ≡ gt)
  lexi-gt lt r ()
  lexi-gt eq r h = inj₂ (refl , h)
  lexi-gt gt r h = inj₁ refl

  mutual
    flip-label : ∀ a b → cmpLabel a b ≡ gt → cmpLabel b a ≡ lt
    flip-label (ix m)  (ix n)  h = ℕ-lt {n} {m} (gt-ℕ {m} {n} h)
    flip-label (sub p) (sub q) h = flip-pos p q h
    flip-label (sub _) (ix _)  h = refl
    flip-label last    (ix _)  h = refl
    flip-label last    (sub _) h = refl
    flip-label (ix _)  (sub _) ()
    flip-label (ix _)  last    ()
    flip-label (sub _) last    ()
    flip-label last    last    ()

    flip-pos : ∀ p q → cmpPos p q ≡ gt → cmpPos q p ≡ lt
    flip-pos []      []      ()
    flip-pos []      (_ ∷ _) ()
    flip-pos (_ ∷ _) []      h = refl
    flip-pos (a ∷ p) (b ∷ q) h with lexi-gt (cmpLabel a b) (cmpPos p q) h
    ... | inj₁ x rewrite flip-label a b x = refl
    ... | inj₂ (x , y)
      rewrite subst (λ z → cmpLabel z a ≡ eq) (eq-label a b x) (refl-label a) | flip-pos p q y = refl

<ᵖ-trans : ∀ p q r → p <ᵖ q ≡ true → q <ᵖ r ≡ true → p <ᵖ r ≡ true
<ᵖ-trans p q r h₁ h₂ rewrite lt-pos p q r (isLt-lt h₁) (isLt-lt h₂) = refl

<ᵖ-irrefl : ∀ p → p <ᵖ p ≡ false
<ᵖ-irrefl p rewrite refl-pos p = refl

<ᵖ-asym : ∀ p q → p <ᵖ q ≡ true → q <ᵖ p ≡ false
<ᵖ-asym p q h with q <ᵖ p in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans p q p h e)) (<ᵖ-irrefl p)

-- What is no earlier than what is no earlier is no earlier.
private
  ≮-by : ∀ p q r c → cmpPos q p ≡ c → q <ᵖ p ≡ false → r <ᵖ q ≡ false → r <ᵖ p ≡ true → ⊥
  ≮-by p q r lt c h₁ h₂ e with () ← trans (sym h₁) (cong isLt c)
  ≮-by p q r eq c h₁ h₂ e with () ← trans (sym e) (subst (λ z → r <ᵖ z ≡ false) (eq-pos q p c) h₂)
  ≮-by p q r gt c h₁ h₂ e with () ← trans (sym (cong isLt (lt-pos r p q (isLt-lt e) (flip-pos q p c)))) h₂

≮-trans : ∀ p q r → q <ᵖ p ≡ false → r <ᵖ q ≡ false → r <ᵖ p ≡ false
≮-trans p q r h₁ h₂ with r <ᵖ p in e
... | false = refl
... | true  = ⊥-elim (≮-by p q r (cmpPos q p) refl h₁ h₂ e)

-- No later is earlier or the same.
<ᵖ-split : ∀ p q → q <ᵖ p ≡ false → p <ᵖ q ≡ true ⊎ p ≡ q
<ᵖ-split p q h with cmpPos p q in c
... | lt = inj₁ refl
... | eq = inj₂ (eq-pos p q c)
... | gt with () ← trans (sym h) (cong isLt (flip-pos p q c))

private
  past : ∀ p → cmpPos (p ++ [ ix 0 ]) [] ≡ gt
  past []      = refl
  past (_ ∷ _) = refl

  top : ∀ a → isLt (lexi (cmpLabel a (ix 0)) gt) ≡ false
  top (ix m) with 0 <ᵇ m
  ... | true  = refl
  ... | false = refl
  top (sub _) = refl
  top last    = refl

-- What is no earlier stays so a step past each.
<ᵖ-shift : ∀ p q → p <ᵖ q ≡ false → (p ++ [ ix 0 ]) <ᵖ (q ++ [ ix 0 ]) ≡ false
<ᵖ-shift []      []      h = refl
<ᵖ-shift (a ∷ p) []      h rewrite past p = top a
<ᵖ-shift (a ∷ p) (b ∷ q) h with cmpLabel a b
... | eq = <ᵖ-shift p q h
... | gt = refl

-- Nothing lies strictly between a position and the one just past it.
<ᵖ-step : ∀ p q → p <ᵖ q ≡ true → q <ᵖ (p ++ [ ix 0 ]) ≡ false
<ᵖ-step []      []                ()
<ᵖ-step []      (ix zero ∷ [])    h = refl
<ᵖ-step []      (ix zero ∷ _ ∷ _) h = refl
<ᵖ-step []      (ix (suc _) ∷ _)  h = refl
<ᵖ-step []      (sub _ ∷ _)       h = refl
<ᵖ-step []      (last ∷ _)        h = refl
<ᵖ-step (a ∷ p) []                ()
<ᵖ-step (a ∷ p) (b ∷ q)           h with cmpLabel a b in c | cmpLabel b a in d
... | lt | lt with () ← trans (sym (refl-label a)) (lt-label a b a c d)
... | lt | eq with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel a z ≡ lt) (eq-label b a d) c)
... | lt | gt = refl
... | eq | lt with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel z a ≡ lt) (sym (eq-label a b c)) d)
... | eq | eq = <ᵖ-step p q h
... | eq | gt with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel z a ≡ gt) (sym (eq-label a b c)) d)
... | gt | _  with () ← h

-- A position is before every position below it, and of two positions
-- that part at one label, the earlier label's is the earlier.
<ᵖ-below : ∀ p {l} ys → p <ᵖ (p ++ l ∷ ys) ≡ true
<ᵖ-below []      ys = refl
<ᵖ-below (a ∷ p) ys rewrite refl-label a = <ᵖ-below p ys

<ᵖ-part : ∀ p {a b} ys zs → (a ∷ []) <ᵖ (b ∷ []) ≡ true → (p ++ a ∷ ys) <ᵖ (p ++ b ∷ zs) ≡ true
<ᵖ-part [] {a} {b} ys zs h with lexi-lt (cmpLabel a b) eq (isLt-lt h)
... | inj₁ x rewrite x = refl
... | inj₂ (_ , ())
<ᵖ-part (x ∷ p) ys zs h rewrite refl-label x = <ᵖ-part p ys zs h

-- Led by the tick.
<ᵖ-tick : ∀ a b p q → (ix a ∷ p) <ᵖ (ix b ∷ q) ≡ true → a ≤ b
<ᵖ-tick a b p q h with lexi-lt (cmpℕ a b) (cmpPos p q) (isLt-lt h)
... | inj₁ c       = <⇒≤ (lt-ℕ c)
... | inj₂ (c , _) = ≤-reflexive (eq-ℕ c)

-- A burst's values part in order.
<ᵖ-ix : ∀ i → (ix i ∷ []) <ᵖ (ix (suc i) ∷ []) ≡ true
<ᵖ-ix i rewrite ℕ-lt {i} {suc i} (n<1+n i) = refl

-- Positions in order and not one below the other stay in order a label
-- down; and what is past `p` is past `p ++ [ ix 0 ]` a label down.
<ᵖ-down : ∀ k h x y → k <ᵖ h ≡ true → (∀ l ls → h ≡ k ++ l ∷ ls → ⊥) → (k ++ [ x ]) <ᵖ (h ++ [ y ]) ≡ true
<ᵖ-down []      []      x y () ne
<ᵖ-down []      (l ∷ h) x y _  ne = ⊥-elim (ne l h refl)
<ᵖ-down (a ∷ k) []      x y () ne
<ᵖ-down (a ∷ k) (b ∷ h) x y kh ne with cmpLabel a b in c
... | lt = refl
... | eq = <ᵖ-down k h x y kh (λ l ls e → ne l ls (cong₂ _∷_ (sym (eq-label a b c)) e))
... | gt with () ← kh

<ᵖ-next : ∀ p q y → p <ᵖ q ≡ true → (p ++ [ ix 0 ]) <ᵖ (q ++ [ y ]) ≡ true
<ᵖ-next []      []                  y ()
<ᵖ-next []      (ix zero ∷ [])      y h = refl
<ᵖ-next []      (ix zero ∷ _ ∷ _)   y h = refl
<ᵖ-next []      (ix (suc _) ∷ _)    y h = refl
<ᵖ-next []      (sub _ ∷ _)         y h = refl
<ᵖ-next []      (last ∷ _)          y h = refl
<ᵖ-next (a ∷ p) []                  y ()
<ᵖ-next (a ∷ p) (b ∷ q)             y h with cmpLabel a b
... | lt = refl
... | eq = <ᵖ-next p q y h
... | gt with () ← h

-- Past `p` and not under it: past everything under it.
<ᵖ-apart : ∀ p q y → p <ᵖ q ≡ true → (∀ ys → q ≡ p ++ ys → ⊥) → (p ++ y) <ᵖ q ≡ true
<ᵖ-apart []      []      y () ne
<ᵖ-apart []      (b ∷ q) y _  ne = ⊥-elim (ne (b ∷ q) refl)
<ᵖ-apart (a ∷ p) []      y () ne
<ᵖ-apart (a ∷ p) (b ∷ q) y h  ne with cmpLabel a b in c
... | lt = refl
... | eq = <ᵖ-apart p q y h (λ ys e → ne ys (cong₂ _∷_ (sym (eq-label a b c)) e))
... | gt with () ← h

-- Past `p` and before something under it: under it.
<ᵖ-between : ∀ p q ys → p <ᵖ q ≡ true → q <ᵖ (p ++ ys) ≡ true → Σ Pos (λ zs → q ≡ p ++ zs)
<ᵖ-between []      q       ys _ _  = q , refl
<ᵖ-between (a ∷ p) []      ys () _
<ᵖ-between (a ∷ p) (b ∷ q) ys h h′ with cmpLabel a b in c | cmpLabel b a in d
... | lt | lt with () ← trans (sym (refl-label a)) (lt-label a b a c d)
... | lt | eq with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel a z ≡ lt) (eq-label b a d) c)
... | lt | gt with () ← h′
... | eq | lt with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel z a ≡ lt) (sym (eq-label a b c)) d)
... | eq | gt with () ← trans (sym (refl-label a)) (subst (λ z → cmpLabel z a ≡ gt) (sym (eq-label a b c)) d)
... | gt | _  with () ← h
... | eq | eq with <ᵖ-between p q ys h h′
...   | zs , e = zs , cong₂ _∷_ (sym (eq-label a b c)) e

-- Under `r`, and so is everything under it.
inside-++ : ∀ r k ys → inside r k ≡ true → inside r (k ++ ys) ≡ true
inside-++ []      k       ys i = refl
inside-++ (a ∷ r) []      ys ()
inside-++ (a ∷ r) (b ∷ k) ys i with cmpLabel a b
... | lt with () ← i
... | eq = inside-++ r k ys i
... | gt with () ← i

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
