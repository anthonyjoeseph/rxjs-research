{-# OPTIONS --guardedness #-}

-- THE DENOTATIONAL SEMANTICS, AS A LIBRARY.  An observable means a
-- timeline, and every operator is an ordinary function on timelines —
-- `takeWhileᴰ p xs` is a value, the way `2 * 3` is.  Nothing here knows
-- about program trees; `Denote` maps a tree onto these functions.
--
-- A timeline is frames at strictly increasing times, each frame a
-- synchronous burst.  Everything is coinductive — a timeline can have
-- infinitely many frames, and a single burst can be infinite (`ones`) or
-- spin silently forever — so divergence is a VALUE here, not an absence
-- of one.
module denotation.MonotonicList where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; [])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)

Time : Set
Time = ℕ

mutual
  -- A timeline from some point on.
  data ML (A : Set) : Set where
    done  : ML A                      -- completed
    quiet : ML A                      -- silent forever, never completes
    at    : Time → Burst A → ML A     -- the next frame

  -- One synchronous burst.
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

postulate
  -- Frame times strictly increase, and the first frame of a cold is at
  -- offset 0 when it bursts on subscribe.  Stated, not yet enforced by
  -- the type.
  Monotone : ∀ {A} → ML A → Set

data MonotonicList (A : Set) : Set where
  hot  : ML A → MonotonicList A       -- times are absolute
  cold : ML A → MonotonicList A       -- times are relative to subscribe

postulate
  -- What a subscriber arriving at time t sees: a cold shifted to t, a
  -- hot with everything before t dropped.
  observe : ∀ {A} → MonotonicList A → Time → ML A

-- A cold leaf is a relative timeline.  Lifted only because the leaf slot
-- of a program tree is `Set₁` (the IO leaf carries an existential).
Timeline : Set → Set₁
Timeline A = Lift (lsuc 0ℓ) (ML A)

------------------------------------------------------------------------
-- The operators

-- How `flattenᴰ` handles a lane arriving while others are live: merge
-- (with an optional concurrency bound; `just 1` is concat), switch to it,
-- or ignore it.
data FlatOp : Set where
  mergeᶠ           : Maybe ℕ → FlatOp
  switchᶠ exhaustᶠ : FlatOp

-- THE PRIMITIVES, and nothing derivable (see Derived, below).
postulate
  emptyᴰ     : ∀ {A} → MonotonicList A
  ofᴰ        : ∀ {A} → List A → MonotonicList A
  mapᴰ       : ∀ {A B} → (A → B) → MonotonicList A → MonotonicList B
  scanᴰ      : ∀ {A B} → (B → A → B) → B → MonotonicList A → MonotonicList B
  takeWhileᴰ : ∀ {A} → (A → Bool) → MonotonicList A → MonotonicList A
  -- Each element is an optional ECHO, leaving as the element arrives,
  -- beside an optional LANE, observed from the time of that element.
  flattenᴰ   : ∀ {A} → FlatOp → MonotonicList (Maybe A × Maybe (MonotonicList A)) → MonotonicList A
  -- One `stall` at the head of the subscribe burst, then the body.  Not
  -- a delay: everything else stays in the same frame.
  deferᴰ     : ∀ {A} → MonotonicList A → MonotonicList A

-- CONNECT, as a binder: the body receives the source made hot, started
-- the moment the connect is subscribed, so each consumer sees it from
-- whenever it joins.  Not a primitive: with no reference counting, what
-- the handle shows never depends on who joins, so it is a function.
-- Inside the body, time is counted from the connect's subscription; the
-- result is rebased to that origin, so a cold source gives a cold result.
-- Where in the subscribe burst a consumer joins is `observe`'s business.
connectᴰ : ∀ {A B} → MonotonicList A → (MonotonicList A → MonotonicList B) → MonotonicList B
connectᴰ (cold m) f = cold (observe (f (hot m)) 0)
connectᴰ (hot m)  f = f (hot m)

------------------------------------------------------------------------
-- Approximation and recursion

-- No information yet: a subscribe burst that spins and never closes.
-- The bottom of the approximation order, and also the honest meaning of a
-- silent synchronous loop — the two coincide, as in any domain.
spin : ∀ {A} → Burst A
spin = stall λ where .Burst∞.force → spin

⊥ᴰ : ∀ {A} → MonotonicList A
⊥ᴰ = cold (at 0 spin)

postulate
  -- Information order: the left is the right with some suffixes replaced
  -- by `spin`, and finitely many `stall`s inserted or dropped.
  _⊑_ : ∀ {A} → MonotonicList A → MonotonicList A → Set
  ⊑-trans : ∀ {A} {x y z : MonotonicList A} → x ⊑ y → y ⊑ z → x ⊑ z
  -- The same timeline, up to finitely many `stall`s.
  _≈_ : ∀ {A} → MonotonicList A → MonotonicList A → Set

  -- The least upper bound of a chain of approximants.
  lub : ∀ {A} → (ℕ → MonotonicList A) → MonotonicList A

-- Approximant n of a recursive definition: unfold it n times from ⊥ᴰ.
iterate : ∀ {A} → ℕ → (MonotonicList A → MonotonicList A) → MonotonicList A
iterate zero    f = ⊥ᴰ
iterate (suc n) f = f (iterate n f)

-- RECURSION.  Agda cannot accept `ones = mergeᴰ (ofᴰ [ 1 ]) (deferᴰ ones)`:
-- it never looks inside `flattenᴰ`, which could strip the guard.  So
-- recursion here is a least fixed point, total for any `f`.
fixᴰ : ∀ {A} → (MonotonicList A → MonotonicList A) → MonotonicList A
fixᴰ f = lub λ n → iterate n f

postulate
  -- Built from the operators, `f` preserves `_⊑_` and limits; that is
  -- one lemma per operator, proven once.
  Continuous : ∀ {A} → (MonotonicList A → MonotonicList A) → Set
  fix-unfold : ∀ {A} {f : MonotonicList A → MonotonicList A}
             → Continuous f → fixᴰ f ≈ f (fixᴰ f)

------------------------------------------------------------------------
-- Derived

mergeᴰ : ∀ {A} → MonotonicList A → MonotonicList A → MonotonicList A
mergeᴰ s t = flattenᴰ (mergeᶠ nothing) (mapᴰ (λ b → nothing , just (if b then s else t)) (ofᴰ (true ∷ false ∷ [])))

flatMapᴰ : ∀ {A B} → FlatOp → (A → MonotonicList B) → MonotonicList A → MonotonicList B
flatMapᴰ op f s = flattenᴰ op (mapᴰ (λ a → nothing , just (f a)) s)

-- Emits 1 forever, synchronously: the echo, then itself as the lane.
ones : MonotonicList ℕ
ones = fixᴰ λ x → flattenᴰ (mergeᶠ nothing) (ofᴰ ((just 1 , just (deferᴰ x)) ∷ []))
