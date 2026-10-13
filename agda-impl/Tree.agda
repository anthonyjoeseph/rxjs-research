{-# OPTIONS --guardedness #-}

-- THE PROGRAM TREE.  Shared by both semantics: `operation.AbstractObservable`
-- compiles it, `denotation.Denote` gives it a meaning.  Neither half of this
-- module knows how a program runs.
module Tree where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)

------------------------------------------------------------------------
-- Programs

-- How `flatten` handles a lane arriving while others are live: merge
-- (with an optional concurrency bound; `just 1` is concat), switch to it,
-- or ignore it.
data FlatOp : Set where
  mergeᶠ            : Maybe ℕ → FlatOp
  switchᶠ exhaustᶠ  : FlatOp

-- `C` is the cold leaf.  `Γ` lists the connects in scope.  `connect`
-- is rxjs's `connect(selector)`: subscribing it makes a fresh subject,
-- subscribes the body with that subject as its handle, then subscribes
-- the source into the subject, once.  The handle is BOUND by the body and
-- referred to by position (`connected`), so it is the one operator with
-- identity and still needs no names: the binder is the identity, and a
-- `connect` inside a lane is a fresh one per subscription, as in rxjs.
-- Every hot observable is a `connect`; a ref-counted `share` is not a
-- primitive.
--
-- Recursion is Agda's own, guarded by `defer`, which is SYNCHRONOUS as in
-- rxjs.  So a synchronous infinite loop is a legal program; the runtimes
-- report it as a burst that never closes, rather than refusing it.
--
-- THE PRIMITIVES, and nothing derivable: merge, mergeMap, switchMap and
-- the rest are `flatten` (see Derived, below).
--
-- `flatten` reads each element as an optional ECHO — a value leaving as
-- the element arrives, before its lane is handled — beside an optional
-- LANE.  The lane comes out of a function rather than an element of type
-- `Obs`, because `Obs` lives in `Set₁` and an element type is a `Set`:
-- the size of the universe, not taste, puts that `map` inside `flatten`.
mutual
  data Obs (C : Set → Set₁) : List Set → Set → Set₁ where
    cold      : ∀ {Γ A} → C A → Obs C Γ A
    empty     : ∀ {Γ A} → Obs C Γ A
    of        : ∀ {Γ A} → List A → Obs C Γ A
    map       : ∀ {Γ A B} → (A → B) → Obs C Γ A → Obs C Γ B
    scan      : ∀ {Γ A B} → (B → A → B) → B → Obs C Γ A → Obs C Γ B
    takeWhile : ∀ {Γ A} → (A → Bool) → Obs C Γ A → Obs C Γ A
    flatten   : ∀ {Γ A B} → FlatOp → (A → Maybe B × Maybe (Obs C Γ B)) → Obs C Γ A → Obs C Γ B
    connect   : ∀ {Γ A B} → Obs C Γ A → Obs C (A ∷ Γ) B → Obs C Γ B
    connected : ∀ {Γ A} → A ∈ Γ → Obs C Γ A
    defer     : ∀ {Γ A} → Later C Γ A → Obs C Γ A

  record Later (C : Set → Set₁) (Γ : List Set) (A : Set) : Set₁ where
    coinductive
    field force : Obs C Γ A

-- Move a program to a larger scope (a `connect` bound around it).
-- Corecursive through `defer`: the renamed body is produced only when
-- forced.
mutual
  rename : ∀ {C Γ Δ A} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Obs C Γ A → Obs C Δ A
  rename r (cold c)         = cold c
  rename r empty            = empty
  rename r (of xs)          = of xs
  rename r (map f s)        = map f (rename r s)
  rename r (scan f z s)     = scan f z (rename r s)
  rename r (takeWhile p s)  = takeWhile p (rename r s)
  rename r (flatten op f s) = flatten op (λ a → renameLane r (f a)) (rename r s)
  rename r (connect s b)    = connect (rename r s) (rename (ext r) b)
    where
      ext : ∀ {B Γ Δ} → (∀ {X} → X ∈ Γ → X ∈ Δ) → ∀ {X} → X ∈ B ∷ Γ → X ∈ B ∷ Δ
      ext r (here p)  = here p
      ext r (there i) = there (r i)
  rename r (connected i)   = connected (r i)
  rename r (defer l)        = defer (renameLater r l)

  renameLane : ∀ {C Γ Δ B} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Maybe B × Maybe (Obs C Γ B) → Maybe B × Maybe (Obs C Δ B)
  renameLane r (e , nothing) = e , nothing
  renameLane r (e , just l)  = e , just (rename r l)

  renameLater : ∀ {C Γ Δ A} → (∀ {X} → X ∈ Γ → X ∈ Δ) → Later C Γ A → Later C Δ A
  renameLater r l .Later.force = rename r (Later.force l)

------------------------------------------------------------------------
-- Derived

merge : ∀ {C Γ A} → Obs C Γ A → Obs C Γ A → Obs C Γ A
merge s t = flatten (mergeᶠ nothing) (λ b → nothing , just (if b then s else t)) (of (true ∷ false ∷ []))

flatMap : ∀ {C Γ A B} → FlatOp → (A → Obs C Γ B) → Obs C Γ A → Obs C Γ B
flatMap op f = flatten op λ a → nothing , just (f a)

-- The motivating example: no μ, no binder, no restriction on where the
-- self-reference sits beyond `defer`.  Emits 1 forever, synchronously:
-- the echo, then the same program again as the lane.
ones : ∀ {C Γ} → Obs C Γ ℕ
ones = flatten (mergeᶠ nothing) (λ _ → just 1 , just (defer λ where .Later.force → ones)) (of (tt ∷ []))
