{-# OPTIONS --guardedness #-}

-- THE UPPER HALF'S BUDGET, READ OFF THE MEANING.  Reaching k items of
-- what the root is shown, `denotation.Unfold` passes finitely many
-- configurations; the run needs no more fuel than their events and their
-- depth.  Each loop turn fires a frame some event set going, each burst
-- step is an event, and each callback hop is a node of the configuration
-- it runs through, or one an earlier event put there.
module Progress where

open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _⊔_; _≤_)

open import denotation.MonotonicList using (root)
open import denotation.Unfold using (Node; Step; framesᶜ; burstᶜ; endᶜ; ofᶜ; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; joinᶜ; deferᶜ;
  outˢ; skipˢ; endˢ; hushˢ; step; shown; unfold; subscribe)
open import operation.Placed using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; module Ran)
open import operation.PureObservable using (PureObs; module Pure)

-- How deep a configuration nests: each node one level, a shared source
-- under its joiner.
mutual
  depth : ∀ {A} → Node A → ℕ
  depth (framesᶜ τ e m)         = 1
  depth (burstᶜ τ r i b)        = 1
  depth (endᶜ p)                = 1
  depth (ofᶜ p i xs)            = 1
  depth (mapᶜ f c)              = suc (depth c)
  depth (scanᶜ f z c)           = suc (depth c)
  depth (takeWhileᶜ i p c)      = suc (depth c)
  depth (flatMapᶜ op g o ls qs) = suc (depthᵒ o ⊔ depthˡ ls)
  depth (joinᶜ p i c)           = suc (depth c)
  depth (deferᶜ l ρ p)          = 1

  depthᵒ : ∀ {A} → Maybe (Node A) → ℕ
  depthᵒ nothing  = 0
  depthᵒ (just c) = depth c

  depthˡ : ∀ {A} → List (Node A) → ℕ
  depthˡ []       = 0
  depthˡ (c ∷ cs) = depth c ⊔ depthˡ cs

-- The events up to the target.
events : ∀ {A k} {e} → Ahead {A} e k → ℕ
events none      = 0
events (outᵃ x)  = suc (events x)
events (skipᵃ x) = suc (events x)
events endᵃ      = 1
events hushᵃ     = 1

-- The deepest configuration passed on the way.
mutual
  deepest : ∀ {A k} (c : Node A) → Ahead (unfold c) k → ℕ
  deepest c a = depth c ⊔ deepestˢ (step c) a

  deepestˢ : ∀ {A k} (s : Step A) → Ahead (shown s) k → ℕ
  deepestˢ (outˢ p a c) none     = 0
  deepestˢ (outˢ p a c) (outᵃ x) = deepest c x
  deepestˢ (skipˢ p c)  none      = 0
  deepestˢ (skipˢ p c)  (skipᵃ x) = deepest c x
  deepestˢ (endˢ p)     none = 0
  deepestˢ (endˢ p)     endᵃ = 0
  deepestˢ hushˢ        none  = 0
  deepestˢ hushˢ        hushᵃ = 0

-- Each event may cost a loop turn of its own and one for a timer it set
-- that fires spent; callbacks nest no deeper than the configuration, and
-- than the events that subscribed it inline.  `make gets` finds it
-- enough on every seed past the edge `gets` records, and `events` alone
-- short on many.
budget : ∀ {A k} (c : Node A) → Ahead (unfold c) k → ℕ
budget c a = 2 * events a + deepest c a

module Gets (R : Set) where
  open Pure R using (compileᴺ)
  open Ran R using (ran; itemsOf)

  postulate
    -- THE RUN GETS AS FAR, AT THE BUDGET: wherever the meaning's events
    -- reach, any approximant past their budget records as many items.
    --
    -- False wherever a `connect` source the body outlives stands between
    -- the root and an event the meaning shows.  The meaning steps a
    -- source only as its joiners copy it, so a body that never joins
    -- shows past it; the engine runs the source inline, and a source
    -- that spins stops the whole run there — as rxjs does, by
    -- overflowing — while one that runs forever keeps the engine firing
    -- its timers, so the silence the meaning shows after the body is
    -- never reported.  The meaning keeping such a source's events, or
    -- `adequacy` assuming none, is Anthony's call.
    -- DEAD ROUTE: a logical relation per operator, by induction over
    --   the tree's approximants, each kernel against its own timeline.  A
    --   connect's subject is state its siblings share, which no relation
    --   on one kernel at a time can carry.
    gets : (o : PureObs [] R) → ∀ {k} (a : Ahead (unfold (subscribe o [] root)) k) n → budget (subscribe o [] root) a ≤ n
         → k ≤ length (itemsOf (ran n (compileᴺ n o [])))
