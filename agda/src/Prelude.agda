-- Self-contained prelude — no standard library.
module Prelude where

------------------------------------------------------------------------
-- booleans

data Bool : Set where
  true  : Bool
  false : Bool

infix 0 if_then_else_

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

not : Bool → Bool
not true  = false
not false = true

infixr 6 _∧_
infixr 5 _∨_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

------------------------------------------------------------------------
-- naturals

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- truncated subtraction (monus)
_∸_ : ℕ → ℕ → ℕ
m     ∸ zero  = m
zero  ∸ suc n = zero
suc m ∸ suc n = m ∸ n

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc m) (suc n) = eqℕ m n

ltℕ : ℕ → ℕ → Bool
ltℕ _       zero    = false
ltℕ zero    (suc _) = true
ltℕ (suc m) (suc n) = ltℕ m n

leqℕ : ℕ → ℕ → Bool
leqℕ zero    _       = true
leqℕ (suc _) zero    = false
leqℕ (suc m) (suc n) = leqℕ m n

------------------------------------------------------------------------
-- equality

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

true≢false : {A : Set} → true ≡ false → A
true≢false ()

-- dependent elimination of an if: lets a proof branch on a Bool while
-- keeping recursive calls direct (no with-function indirection, which
-- the termination checker cannot always see through)
if-elim : (b : Bool) (P : Bool → Set)
        → (b ≡ true → P true) → (b ≡ false → P false) → P b
if-elim true  P pt pf = pt refl
if-elim false P pt pf = pf refl

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

------------------------------------------------------------------------
-- unit, pairs, sums, maybe

record ⊤ : Set where
  constructor tt

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B
open _×_ public

infixr 4 _,_
infixr 2 _×_

-- dependent pair (a running inner machine: which element spawned it,
-- paired with the state of THAT element's machine)
record Σ (A : Set) (B : A → Set) : Set where
  constructor _▹_
  field
    proj₁ : A
    proj₂ : B proj₁
open Σ public

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

maybe′ : {A B : Set} → B → (A → B) → Maybe A → B
maybe′ d f nothing  = d
maybe′ d f (just x) = f x

------------------------------------------------------------------------
-- lists

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

infixr 5 _++_

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

concatMap : {A B : Set} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

foldl : {A B : Set} → (B → A → B) → B → List A → B
foldl f z []       = z
foldl f z (x ∷ xs) = foldl f (f z x) xs

any : {A : Set} → (A → Bool) → List A → Bool
any p []       = false
any p (x ∷ xs) = if p x then true else any p xs

replicate : {A : Set} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

-- 0 , 1 , … , n-1
upTo : ℕ → List ℕ
upTo zero    = []
upTo (suc n) = 0 ∷ map suc (upTo n)

-- drop the first n elements
drop : {A : Set} → ℕ → List A → List A
drop zero    xs       = xs
drop (suc n) []       = []
drop (suc n) (x ∷ xs) = drop n xs

-- index with a default (total; the default is never reached below length)
at : {A : Set} → ℕ → List A → A → A
at _       []       d = d
at zero    (x ∷ _)  d = x
at (suc n) (_ ∷ xs) d = at n xs d

-- large lists (for collections of machines, which live in Set₁)
data List₁ (A : Set₁) : Set₁ where
  []  : List₁ A
  _∷_ : A → List₁ A → List₁ A

length₁ : {A : Set₁} → List₁ A → ℕ
length₁ []       = zero
length₁ (_ ∷ xs) = suc (length₁ xs)

lookup₁ : {A : Set₁} → List₁ A → ℕ → A → A
lookup₁ []       _       d = d
lookup₁ (x ∷ _)  zero    d = x
lookup₁ (_ ∷ xs) (suc k) d = lookup₁ xs k d

------------------------------------------------------------------------
-- finite indices and vectors (sources are counted at the type level)

data Fin : ℕ → Set where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc  : {n : ℕ} → Fin n → Fin (suc n)

toℕ : {n : ℕ} → Fin n → ℕ
toℕ fzero    = zero
toℕ (fsuc i) = suc (toℕ i)

-- every index, in slot order
allFins : {n : ℕ} → List (Fin n)
allFins {zero}  = []
allFins {suc n} = fzero ∷ map fsuc allFins

data Vec (A : Set) : ℕ → Set where
  []   : Vec A zero
  _∷_  : {n : ℕ} → A → Vec A n → Vec A (suc n)

lookupV : {A : Set} {n : ℕ} → Vec A n → Fin n → A
lookupV (x ∷ _)  fzero    = x
lookupV (_ ∷ xs) (fsuc i) = lookupV xs i

pureV : {A : Set} {n : ℕ} → A → Vec A n
pureV {n = zero}  x = []
pureV {n = suc n} x = x ∷ pureV x

------------------------------------------------------------------------
-- boolean-algebra helpers (consumed by the Time order lemmas)

∧-split-left : (a b : Bool) → a ∧ b ≡ true → a ≡ true
∧-split-left true  _ _ = refl
∧-split-left false _ ()

∧-split-right : (a b : Bool) → a ∧ b ≡ true → b ≡ true
∧-split-right true  b p = p
∧-split-right false b ()

∧-true-false : (a b : Bool) → a ≡ true → a ∧ b ≡ false → b ≡ false
∧-true-false true  b _  q = q
∧-true-false false b () _

∨-split : (a b : Bool) → a ∨ b ≡ true → Either (a ≡ true) (b ≡ true)
∨-split true  b _ = left refl
∨-split false b p = right p

∨-false-left : (a b : Bool) → a ∨ b ≡ false → a ≡ false
∨-false-left true  b ()
∨-false-left false b _ = refl

∨-false-right : (a b : Bool) → a ∨ b ≡ false → b ≡ false
∨-false-right true  b ()
∨-false-right false b p = p

------------------------------------------------------------------------
-- ℕ comparison lemmas (consumed by the Time order lemmas)

+-suc : (a b : ℕ) → a + suc b ≡ suc (a + b)
+-suc zero    b = refl
+-suc (suc a) b = cong suc (+-suc a b)

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ-sound : (a b : ℕ) → eqℕ a b ≡ true → a ≡ b
eqℕ-sound zero    zero    _ = refl
eqℕ-sound zero    (suc b) ()
eqℕ-sound (suc a) zero    ()
eqℕ-sound (suc a) (suc b) p = cong suc (eqℕ-sound a b p)

eqℕ-complete : (a b : ℕ) → a ≡ b → eqℕ a b ≡ true
eqℕ-complete a .a refl = eqℕ-refl a

leqℕ-refl : (n : ℕ) → leqℕ n n ≡ true
leqℕ-refl zero    = refl
leqℕ-refl (suc n) = leqℕ-refl n

ltℕ-irrefl : (n : ℕ) → ltℕ n n ≡ false
ltℕ-irrefl zero    = refl
ltℕ-irrefl (suc n) = ltℕ-irrefl n

ltℕ-asym : (a b : ℕ) → ltℕ a b ≡ true → ltℕ b a ≡ false
ltℕ-asym zero    zero    ()
ltℕ-asym zero    (suc b) _ = refl
ltℕ-asym (suc a) zero    ()
ltℕ-asym (suc a) (suc b) p = ltℕ-asym a b p

ltℕ⇒eqℕ-false : (a b : ℕ) → ltℕ a b ≡ true → eqℕ a b ≡ false
ltℕ⇒eqℕ-false zero    zero    ()
ltℕ⇒eqℕ-false zero    (suc b) _ = refl
ltℕ⇒eqℕ-false (suc a) zero    ()
ltℕ⇒eqℕ-false (suc a) (suc b) p = ltℕ⇒eqℕ-false a b p

ltℕ⇒eqℕ-false-flip : (a b : ℕ) → ltℕ a b ≡ true → eqℕ b a ≡ false
ltℕ⇒eqℕ-false-flip zero    zero    ()
ltℕ⇒eqℕ-false-flip zero    (suc b) _ = refl
ltℕ⇒eqℕ-false-flip (suc a) zero    ()
ltℕ⇒eqℕ-false-flip (suc a) (suc b) p = ltℕ⇒eqℕ-false-flip a b p

ltℕ⇒leqℕ-flip-false : (a b : ℕ) → ltℕ a b ≡ true → leqℕ b a ≡ false
ltℕ⇒leqℕ-flip-false zero    zero    ()
ltℕ⇒leqℕ-flip-false zero    (suc b) _ = refl
ltℕ⇒leqℕ-flip-false (suc a) zero    ()
ltℕ⇒leqℕ-flip-false (suc a) (suc b) p = ltℕ⇒leqℕ-flip-false a b p

ltℕ-suc : (n : ℕ) → ltℕ n (suc n) ≡ true
ltℕ-suc zero    = refl
ltℕ-suc (suc n) = ltℕ-suc n

ltℕ-trans : (a b c : ℕ) → ltℕ a b ≡ true → ltℕ b c ≡ true → ltℕ a c ≡ true
ltℕ-trans a       b       zero    p  ()
ltℕ-trans a       zero    (suc c) () q
ltℕ-trans zero    (suc b) (suc c) p  q = refl
ltℕ-trans (suc a) (suc b) (suc c) p  q = ltℕ-trans a b c p q

leqℕ-trans : (a b c : ℕ) → leqℕ a b ≡ true → leqℕ b c ≡ true → leqℕ a c ≡ true
leqℕ-trans zero    b       c       p  q  = refl
leqℕ-trans (suc a) zero    c       () q
leqℕ-trans (suc a) (suc b) zero    p  ()
leqℕ-trans (suc a) (suc b) (suc c) p  q  = leqℕ-trans a b c p q

ltℕ⇒leqℕ : (a b : ℕ) → ltℕ a b ≡ true → leqℕ a b ≡ true
ltℕ⇒leqℕ a       zero    ()
ltℕ⇒leqℕ zero    (suc b) p = refl
ltℕ⇒leqℕ (suc a) (suc b) p = ltℕ⇒leqℕ a b p

leqℕ-false⇒flip : (a b : ℕ) → leqℕ a b ≡ false → leqℕ b a ≡ true
leqℕ-false⇒flip zero    b       ()
leqℕ-false⇒flip (suc a) zero    p = refl
leqℕ-false⇒flip (suc a) (suc b) p = leqℕ-false⇒flip a b p

leqℕ-false⇒ltℕ-flip : (a b : ℕ) → leqℕ a b ≡ false → ltℕ b a ≡ true
leqℕ-false⇒ltℕ-flip zero    b       ()
leqℕ-false⇒ltℕ-flip (suc a) zero    p = refl
leqℕ-false⇒ltℕ-flip (suc a) (suc b) p = leqℕ-false⇒ltℕ-flip a b p

leqℕ-neq⇒ltℕ : (a b : ℕ) → leqℕ a b ≡ true → eqℕ a b ≡ false → ltℕ a b ≡ true
leqℕ-neq⇒ltℕ zero    zero    _  ()
leqℕ-neq⇒ltℕ zero    (suc b) _  _ = refl
leqℕ-neq⇒ltℕ (suc a) zero    () _
leqℕ-neq⇒ltℕ (suc a) (suc b) p  q = leqℕ-neq⇒ltℕ a b p q

ltℕ-leqℕ-trans : (a b c : ℕ) → ltℕ a b ≡ true → leqℕ b c ≡ true → ltℕ a c ≡ true
ltℕ-leqℕ-trans a       zero    c       () _
ltℕ-leqℕ-trans a       (suc b) zero    _  ()
ltℕ-leqℕ-trans zero    (suc b) (suc c) _  _ = refl
ltℕ-leqℕ-trans (suc a) (suc b) (suc c) p  q = ltℕ-leqℕ-trans a b c p q

ltℕ-false⇒leqℕ-flip : (a b : ℕ) → ltℕ a b ≡ false → leqℕ b a ≡ true
ltℕ-false⇒leqℕ-flip a       zero    p  = refl
ltℕ-false⇒leqℕ-flip zero    (suc b) ()
ltℕ-false⇒leqℕ-flip (suc a) (suc b) p  = ltℕ-false⇒leqℕ-flip a b p

ltℕ-false-split : (a b : ℕ) → ltℕ a b ≡ false → Either (ltℕ b a ≡ true) (a ≡ b)
ltℕ-false-split zero    zero    p  = right refl
ltℕ-false-split zero    (suc b) ()
ltℕ-false-split (suc a) zero    p  = left refl
ltℕ-false-split (suc a) (suc b) p with ltℕ-false-split a b p
... | left  q = left q
... | right e = right (cong suc e)

leqℕ-plus : (a b : ℕ) → leqℕ a (a + b) ≡ true
leqℕ-plus zero    b = refl
leqℕ-plus (suc a) b = leqℕ-plus a b
