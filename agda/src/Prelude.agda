-- Self-contained prelude (no standard library dependency):
-- booleans, naturals, propositional equality, lists, pairs,
-- and the boolean-comparison lemmas the Time order needs.
module Prelude where

data Bool : Set where
  true  : Bool
  false : Bool

if_then_else_ : {A : Set} → Bool → A → A → A
if true  then x else _ = x
if false then _ else y = y

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ _ = false

_∨_ : Bool → Bool → Bool
true  ∨ _ = true
false ∨ b = b

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

eqℕ : ℕ → ℕ → Bool
eqℕ zero    zero    = true
eqℕ zero    (suc _) = false
eqℕ (suc _) zero    = false
eqℕ (suc a) (suc b) = eqℕ a b

ltℕ : ℕ → ℕ → Bool
ltℕ _       zero    = false
ltℕ zero    (suc _) = true
ltℕ (suc a) (suc b) = ltℕ a b

leqℕ : ℕ → ℕ → Bool
leqℕ zero    _       = true
leqℕ (suc _) zero    = false
leqℕ (suc a) (suc b) = leqℕ a b

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_ #-}

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

cong₂ : {A B C : Set} (f : A → B → C) {x y : A} {u v : B}
      → x ≡ y → u ≡ v → f x u ≡ f y v
cong₂ f refl refl = refl

_∘_ : {A B C : Set} → (B → C) → (A → B) → A → C
(g ∘ f) x = g (f x)

subst : {A : Set} (P : A → Set) {x y : A} → x ≡ y → P x → P y
subst P refl p = p

-- dependent elimination of an if: lets a proof branch on a Bool while
-- keeping recursive calls direct (no with-function indirection, which the
-- termination checker cannot always see through)
if-elim : (b : Bool) (P : Bool → Set)
        → (b ≡ true → P true) → (b ≡ false → P false) → P b
if-elim true  P pt pf = pt refl
if-elim false P pt pf = pf refl

-- reduce an if under a known condition (for hypotheses, which
-- with-abstraction does not rewrite)
if-true : {X : Set} {b : Bool} {x y : X} → b ≡ true → (if b then x else y) ≡ x
if-true refl = refl

if-false : {X : Set} {b : Bool} {x y : X} → b ≡ false → (if b then x else y) ≡ y
if-false refl = refl

suc-inj : {m n : ℕ} → suc m ≡ suc n → m ≡ n
suc-inj refl = refl

true≢false : {A : Set} → true ≡ false → A
true≢false ()

zero≢suc : {A : Set} {n : ℕ} → zero ≡ suc n → A
zero≢suc ()

suc≢zero : {A : Set} {n : ℕ} → suc n ≡ zero → A
suc≢zero ()

data Either (A B : Set) : Set where
  left  : A → Either A B
  right : B → Either A B

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

map : {A B : Set} → (A → B) → List A → List B
map f []       = []
map f (x ∷ xs) = f x ∷ map f xs

length : {A : Set} → List A → ℕ
length []       = 0
length (x ∷ xs) = suc (length xs)

replicate : {A : Set} → ℕ → A → List A
replicate zero    x = []
replicate (suc n) x = x ∷ replicate n x

data Maybe (A : Set) : Set where
  nothing : Maybe A
  just    : A → Maybe A

min : ℕ → ℕ → ℕ
min zero    b       = zero
min (suc a) zero    = zero
min (suc a) (suc b) = suc (min a b)

infixr 5 _++_
_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

++-nil : {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-nil []       = refl
++-nil (x ∷ xs) = cong (_∷_ x) (++-nil xs)

replicate-snoc : {A : Set} (n : ℕ) (x : A)
  → replicate n x ++ (x ∷ []) ≡ x ∷ replicate n x
replicate-snoc zero    x = refl
replicate-snoc (suc n) x = cong (_∷_ x) (replicate-snoc n x)

++-snoc : {A : Set} (xs : List A) (y : A) (zs : List A)
        → (xs ++ (y ∷ [])) ++ zs ≡ xs ++ (y ∷ zs)
++-snoc []       y zs = refl
++-snoc (x ∷ xs) y zs = cong (_∷_ x) (++-snoc xs y zs)

++-assoc : {A : Set} (xs ys zs : List A)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []       ys zs = refl
++-assoc (x ∷ xs) ys zs = cong (_∷_ x) (++-assoc xs ys zs)

map-++ : {A B : Set} (f : A → B) (xs ys : List A)
       → map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++ f []       ys = refl
map-++ f (x ∷ xs) ys = cong (_∷_ (f x)) (map-++ f xs ys)

concatMap : {A B : Set} → (A → List B) → List A → List B
concatMap f []       = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

map-map : {A B C : Set} (g : B → C) (f : A → B) (l : List A)
        → map g (map f l) ≡ map (λ a → g (f a)) l
map-map g f []       = refl
map-map g f (x ∷ xs) = cong (_∷_ (g (f x))) (map-map g f xs)

map-ext : {A B : Set} {f g : A → B}
        → ((a : A) → f a ≡ g a) → (l : List A) → map f l ≡ map g l
map-ext h []       = refl
map-ext h (x ∷ xs) = cong₂ _∷_ (h x) (map-ext h xs)

infixr 4 _,_
infixr 2 _×_
data _×_ (A B : Set) : Set where
  _,_ : A → B → A × B

fst : {A B : Set} → A × B → A
fst (a , _) = a

snd : {A B : Set} → A × B → B
snd (_ , b) = b

-- boolean-algebra helpers ----------------------------------------------------

∧-split-left : (a b : Bool) → a ∧ b ≡ true → a ≡ true
∧-split-left true  _ _ = refl
∧-split-left false _ ()

∧-split-right : (a b : Bool) → a ∧ b ≡ true → b ≡ true
∧-split-right true  b p = p
∧-split-right false b ()

∧-true-false : (a b : Bool) → a ≡ true → a ∧ b ≡ false → b ≡ false
∧-true-false true  b _  q = q
∧-true-false false b () _

∧-absorb-false : (a : Bool) → a ∧ false ≡ false
∧-absorb-false true  = refl
∧-absorb-false false = refl

∨-split : (a b : Bool) → a ∨ b ≡ true → Either (a ≡ true) (b ≡ true)
∨-split true  b _ = left refl
∨-split false b p = right p

∨-false-left : (a b : Bool) → a ∨ b ≡ false → a ≡ false
∨-false-left true  b ()
∨-false-left false b _ = refl

∨-false-right : (a b : Bool) → a ∨ b ≡ false → b ≡ false
∨-false-right true  b ()
∨-false-right false b p = p

-- comparison lemmas ----------------------------------------------------------

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ true
eqℕ-refl zero    = refl
eqℕ-refl (suc n) = eqℕ-refl n

eqℕ-sound : (a b : ℕ) → eqℕ a b ≡ true → a ≡ b
eqℕ-sound zero    zero    _ = refl
eqℕ-sound zero    (suc b) ()
eqℕ-sound (suc a) zero    ()
eqℕ-sound (suc a) (suc b) p = cong suc (eqℕ-sound a b p)

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

eqℕ-complete : (a b : ℕ) → a ≡ b → eqℕ a b ≡ true
eqℕ-complete a .a refl = eqℕ-refl a

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
