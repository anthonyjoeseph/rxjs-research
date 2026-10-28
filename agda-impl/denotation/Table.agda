{-# OPTIONS --guardedness #-}

-- THE TABLE: a program's meaning as every row of work it causes, each at
-- its position.  The positions are `MonotonicList`'s, and they are totally
-- ordered, so a table needs no order of its own: the n-th event is the
-- n-th row by position.  An operator is a function on tables, defined
-- all at once — a merge is a union, a joiner is a filter and a rekey.
--
-- Work that keeps running after whoever listens stops — a connect's
-- source still in its subscribe burst — stays in the table as `skip`
-- rows.  A table's PROPER rows are those at or before its end; a hot
-- shows only those.
--
-- What a subscriber sees is the ω-prefix (`Seen`): a row with infinitely
-- many rows before it is never reached, which is how a synchronous loop
-- blocks everything after it.
module denotation.Table where

open import Data.Bool using (Bool; T)
open import Data.Empty using (⊥)
open import Data.List using (List; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (Σ; _×_)
open import Data.Unit using (⊤)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; Later; FlatOp; mergeᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
import denotation.MonotonicList.Events as E
open import denotation.MonotonicList.Events using (Pos; Timeline; timelineAt; _<ᵖ_; inside; ix; sub; last)
open import denotation.MonotonicList using (start; ofᴱ)

------------------------------------------------------------------------
-- Rows

data Ev (A : Set) : Set where
  out  : A → Ev A
  skip : Ev A
  end  : Ev A

Table : Set → Set₁
Table A = Pos → Ev A → Set

_≺_ : Pos → Pos → Set
p ≺ q = T (p <ᵖ q)

-- At or before.
_≼_ : Pos → Pos → Set
p ≼ q = ¬ (q ≺ p)

-- Work that is not a completion.
Work : ∀ {A} → Ev A → Set
Work end = ⊥
Work _   = ⊤

-- The rows a stream reaches, each at a finite index.
data InE {A : Set} : E.Events A → Table A where
  at-out  : ∀ {k a r} → InE (E.out k a r) k (out a)
  at-skip : ∀ {k r} → InE (E.skip k r) k skip
  at-end  : ∀ {k} → InE (E.end k) k end
  on-out  : ∀ {k a r q e} → InE (E.Events∞.force r) q e → InE (E.out k a r) q e
  on-skip : ∀ {k r q e} → InE (E.Events∞.force r) q e → InE (E.skip k r) q e

-- Rows at or before the end.
Proper : ∀ {A} → Table A → Table A
Proper t q e = t q e × (∀ {c} → t c end → q ≼ c)

-- What a subscriber reaches: a row with finitely many rows before it.
Seen : ∀ {A} → Table A → Table A
Seen t q e = Proper t q e × Σ (List Pos) λ ks → ∀ {k e′} → t k e′ → k ≺ q → k ∈ ks

------------------------------------------------------------------------
-- Observables

-- A hot is one table at absolute positions; a cold, a table for every
-- subscription position.  Only a `connect` makes a hot.
data Den (A : Set) : Set₁ where
  hot  : Table A → Den A
  cold : (Pos → Table A) → Den A

-- JOINING A HOT AT `p`: what comes after `p`, rekeyed under `sub p`; a
-- hot already ended at `p` ends at once.  Nothing is shown for what was
-- missed: the work was the source's, and the source shows it.
data Rejoin {A : Set} (p : Pos) (t : Table A) : Table A where
  shown : ∀ {q e} → t q e → Work e → p ≺ q → Rejoin p t (q ++ [ sub p ]) e
  ended : ∀ {c} → t c end → p ≺ c → Rejoin p t (c ++ [ sub p ]) end
  late  : ∀ {c} → t c end → c ≼ p → Rejoin p t (p ++ [ last ]) end

enter : ∀ {A} → Den A → Pos → Table A
enter (hot t)  p = Rejoin p t
enter (cold f) p = f p

------------------------------------------------------------------------
-- Leaves

coldᵀ : ∀ {A} → Timeline A → Den A
coldᵀ c = cold λ p → InE (start p (timelineAt c p))

emptyᵀ : ∀ {A} → Den A
emptyᵀ = cold λ p → InE (E.end (p ++ [ last ]))

ofᵀ : ∀ {A} → List A → Den A
ofᵀ xs = cold λ p → InE (ofᴱ p 0 xs)

-- No information yet: a subscription that spins and never closes.
data Spin {A : Set} (p : Pos) : Table A where
  spin : ∀ i → Spin p (p ++ [ ix i ]) skip

⊥ᵀ : ∀ {A} → Den A
⊥ᵀ = cold Spin

------------------------------------------------------------------------
-- One input

data MapT {A B : Set} (f : A → B) (t : Table A) : Table B where
  map-out  : ∀ {q a} → t q (out a) → MapT f t q (out (f a))
  map-skip : ∀ {q} → t q skip → MapT f t q skip
  map-end  : ∀ {q} → t q end → MapT f t q end

mapᵀ : ∀ {A B} → (A → B) → Den A → Den B
mapᵀ f s = cold λ p → MapT f (enter s p)

-- A `skip`, then the body: rxjs's own `defer`, synchronous.
data DeferT {A : Set} (s : Den A) (p : Pos) : Table A where
  guard : DeferT s p (p ++ [ ix 0 ]) skip
  body  : ∀ {q e} → enter s (p ++ [ ix 1 ]) q e → DeferT s p q e

deferᵀ : ∀ {A} → Den A → Den A
deferᵀ s = cold (DeferT s)

------------------------------------------------------------------------
-- Merge

-- The outer `o`, and each of its values `a` at `q` subscribed as a lane
-- at `q ++ [ ix 1 ]`, its first effect `q ++ [ ix 0 ]` silent.
module Merge {A B : Set} (f : A → Den B) (o : Table A) where

  Lane : Pos → A → Table B
  Lane q a = enter (f a) (q ++ [ ix 1 ])

  -- Every part has ended by `c`.
  Done : Pos → Set
  Done c = (Σ Pos λ c₀ → o c₀ end × c₀ ≼ c)
         × (∀ {q a} → o q (out a) → Σ Pos λ c′ → Lane q a c′ end × c′ ≼ c)

  -- The whole ends where the last part does; every other end is a skip.
  data MergeT : Table B where
    val   : ∀ {q a} → o q (out a) → MergeT (q ++ [ ix 0 ]) skip
    step  : ∀ {q} → o q skip → MergeT q skip
    oend  : ∀ {c} → o c end → Done c → MergeT c end
    opass : ∀ {c} → o c end → ¬ Done c → MergeT c skip
    lane  : ∀ {q a k e} → o q (out a) → Lane q a k e → Work e → MergeT k e
    lend  : ∀ {q a c} → o q (out a) → Lane q a c end → Done c → MergeT c end
    lpass : ∀ {q a c} → o q (out a) → Lane q a c end → ¬ Done c → MergeT c skip

-- CONCAT: lane i+1 waits for lane i.  It is subscribed where its value
-- arrives if lane i has ended by then, and otherwise where lane i ends,
-- that end shown silent at its first effect.
module Concat {A B : Set} (f : A → Den B) (o : Table A) where

  -- The outer's i-th value.
  data Nth : ℕ → Pos → A → Set where
    first : ∀ {q a} → o q (out a) → (∀ {k b} → o k (out b) → q ≼ k) → Nth 0 q a
    next  : ∀ {i q a q′ a′} → Nth i q a → o q′ (out a′) → q ≺ q′
          → (∀ {k b} → o k (out b) → q ≺ k → q′ ≼ k) → Nth (suc i) q′ a′

  -- Lane i, for the outer's value at `q`, subscribed at `s`.
  data Sub : ℕ → Pos → Pos → A → Set where
    sub₀   : ∀ {q a} → Nth 0 q a → Sub 0 q (q ++ [ ix 1 ]) a
    free   : ∀ {i q₀ s a c q a′} → Sub i q₀ s a → enter (f a) s c end → Nth (suc i) q a′ → c ≺ q
           → Sub (suc i) q (q ++ [ ix 1 ]) a′
    queued : ∀ {i q₀ s a c q a′} → Sub i q₀ s a → enter (f a) s c end → Nth (suc i) q a′ → q ≺ c
           → Sub (suc i) q (c ++ [ ix 1 ]) a′

  -- Lane i+1's value has arrived by `c`.
  Waiting : ℕ → Pos → Set
  Waiting i c = Σ Pos λ q → Σ A λ a → Nth (suc i) q a × q ≺ c

  -- The outer has ended by `c`.
  Over : Pos → Set
  Over c = Σ Pos λ c₀ → o c₀ end × c₀ ≺ c

  -- Every lane has ended by `c`.
  Drained : Pos → Set
  Drained c = ∀ {i q a} → Nth i q a → Σ Pos λ s → Σ Pos λ c′ → Sub i q s a × enter (f a) s c′ end × c′ ≺ c

  data ConcatT : Table B where
    val     : ∀ {q a} → o q (out a) → ConcatT (q ++ [ ix 0 ]) skip
    step    : ∀ {q} → o q skip → ConcatT q skip
    oend    : ∀ {c} → o c end → Drained c → ConcatT c end
    opass   : ∀ {c} → o c end → ¬ Drained c → ConcatT c skip
    lane    : ∀ {i q s a k e} → Sub i q s a → enter (f a) s k e → Work e → ConcatT k e
    handoff : ∀ {i q s a c} → Sub i q s a → enter (f a) s c end → Waiting i c → ConcatT (c ++ [ ix 0 ]) skip
    lend    : ∀ {i q s a c} → Sub i q s a → enter (f a) s c end → ¬ Waiting i c → Over c → ConcatT c end
    lpass   : ∀ {i q s a c} → Sub i q s a → enter (f a) s c end → ¬ Waiting i c → ¬ Over c → ConcatT c skip

------------------------------------------------------------------------
-- Connect

-- Subscribed at `p`: the body at `p ++ [ ix 0 ]` over the source made hot,
-- then the source at `r = p ++ [ ix 1 ]`.  Each source step at `k` shows
-- silent at its first effect while the body lives; once the body has
-- ended, what remains of the source's subscribe burst still runs, at its
-- own positions.  The body's end ends the connect.
module Connect {A B : Set} (s : Den A) (F : Den A → Den B) (p : Pos) where

  r : Pos
  r = p ++ [ ix 1 ]

  σ : Table A
  σ = enter s r

  β : Table B
  β = enter (F (hot (Proper σ))) (p ++ [ ix 0 ])

  -- The body has not ended by `q`.
  Alive : Pos → Set
  Alive q = ∀ {c} → β c end → q ≺ c

  data ConnT : Table B where
    body   : ∀ {k e} → β k e → ConnT k e
    shown  : ∀ {k e} → σ k e → Alive (k ++ [ ix 0 ]) → ConnT (k ++ [ ix 0 ]) skip
    pinned : ∀ {k e} → σ k e → ¬ Alive (k ++ [ ix 0 ]) → T (inside r k) → ConnT k skip

connectᵀ : ∀ {A B} → Den A → (Den A → Den B) → Den B
connectᵀ s F = cold λ p → Connect.ConnT s F p

------------------------------------------------------------------------
-- FlatMap

-- The operators the spike leaves out: a gap per operator.
postulate
  scanᵀ      : ∀ {A B} → (B → A → B) → B → Den A → Den B
  takeWhileᵀ : ∀ {A} → Bool → (A → Bool) → Den A → Den A
  flatOtherᵀ : ∀ {A B} → FlatOp → (A → Den B) → Den A → Den B

flatMapᵀ : ∀ {A B} → FlatOp → (A → Den B) → Den A → Den B
flatMapᵀ (mergeᶠ nothing)        f s = cold λ p → Merge.MergeT f (enter s p)
flatMapᵀ (mergeᶠ (just (suc zero))) f s = cold λ p → Concat.ConcatT f (enter s p)
flatMapᵀ op                      f s = flatOtherᵀ op f s

------------------------------------------------------------------------
-- A program tree's table

DenEnv : List Set → Set₁
DenEnv = All Den

-- APPROXIMANT n: every path through more than n `defer`s cut off at ⊥ᵀ,
-- as `denotation.Denote`'s.
approxᵀ : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → Den A
approxᵀ n       (cold c)          ρ = coldᵀ c
approxᵀ n       empty             ρ = emptyᵀ
approxᵀ n       (of xs)           ρ = ofᵀ xs
approxᵀ n       (map f s)         ρ = mapᵀ f (approxᵀ n s ρ)
approxᵀ n       (scan f z s)      ρ = scanᵀ f z (approxᵀ n s ρ)
approxᵀ n       (takeWhile i p s) ρ = takeWhileᵀ i p (approxᵀ n s ρ)
approxᵀ n       (flatMap op f s)  ρ = flatMapᵀ op (λ a → approxᵀ n (f a) ρ) (approxᵀ n s ρ)
approxᵀ n       (connect s b)     ρ = connectᵀ (approxᵀ n s ρ) λ h → approxᵀ n b (h ∷ ρ)
approxᵀ n       (connected i)     ρ = lookup ρ i
approxᵀ zero    (defer l)         ρ = ⊥ᵀ
approxᵀ (suc n) (defer l)         ρ = deferᵀ (approxᵀ n (Later.force l) ρ)

-- THE LIMIT: a row every approximant has from some index on.
data Lim {A : Set} (c : ℕ → Table A) (q : Pos) (e : Ev A) : Set where
  from : ∀ N → (∀ n → N ≤ n → c n q e) → Lim c q e

⟦_⟧ᵀ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → Den A
⟦ o ⟧ᵀ ρ = cold λ p → Lim λ n → enter (approxᵀ n o ρ) p
