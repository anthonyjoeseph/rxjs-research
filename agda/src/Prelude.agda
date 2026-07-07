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

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

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

replicate : {A : Set} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

-- 0 , 1 , … , n-1
upTo : ℕ → List ℕ
upTo zero    = []
upTo (suc n) = 0 ∷ map suc (upTo n)

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
