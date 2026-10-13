{-# OPTIONS --guardedness #-}

-- THE DENOTATIONAL SEMANTICS, AS A LIBRARY.  An observable means what
-- each subscriber sees, and every operator is an ordinary function on
-- those meanings — `takeWhileᴰ p xs` is a value, the way `2 * 3` is.
-- Nothing here knows about program trees; `Denote` maps a tree onto
-- these functions.
--
-- Everything is coinductive — a run can have infinitely many events,
-- even inside one tick (`ones`), or spin silently forever — so
-- divergence is a VALUE here, not an absence of one.
module denotation.MonotonicList where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; _++_; [_]; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)

------------------------------------------------------------------------
-- Timelines: what a cold leaf says, and what a runtime reports

Time : Set
Time = ℕ

-- Frames at strictly increasing ticks, each a synchronous burst.  A
-- cold leaf is one of these, with ticks relative to its subscription;
-- a runtime reports one, with ticks absolute.
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

-- Lifted only because the leaf slot of a program tree is `Set₁` (the
-- IO leaf carries an existential).
Timeline : Set → Set₁
Timeline A = Lift (lsuc 0ℓ) (ML A)

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

------------------------------------------------------------------------
-- What a subscriber sees

-- Events at strictly increasing positions.  A `skip` is a step that
-- shows nothing — a dropped element, a `defer`'s subscription — kept so
-- that every step yields a constructor, and positioned so that a merge
-- can still place it.
mutual
  data Events (A : Set) : Set where
    out  : Pos → A → Events∞ A → Events A
    skip : Pos → Events∞ A → Events A
    end  : Pos → Events A             -- completed, at this position
    hush : Events A                   -- silent forever, never completes

  record Events∞ (A : Set) : Set where
    coinductive
    field force : Events A

open Events∞

-- A hot is one run, at absolute positions; a cold is a run for every
-- subscription position.  Only a `connect` makes a hot.
data MonotonicList (A : Set) : Set where
  hot  : Events A → MonotonicList A
  cold : (Pos → Events A) → MonotonicList A

-- JOINING A HOT AT `p` shows what comes after `p` and nothing before:
-- joining while a value is being delivered misses that value, and
-- joining after completion completes at once, both as an rxjs Subject.
-- What the subject delivers is rekeyed under `sub p`.  The dropped
-- prefix becomes skips just after `p`, before anything the join shows.
private
  mutual
    rejoin : ∀ {A} → Pos → ℕ → Events A → Events A
    rejoin p i (out q a k) = shown p i q (just a) k (p <ᵖ q)
    rejoin p i (skip q k)  = shown p i q nothing k (p <ᵖ q)
    rejoin p i (end c)     = if p <ᵖ c then end (c ++ [ sub p ]) else end (p ++ [ last ])
    rejoin p i hush        = hush

    shown : ∀ {A} → Pos → ℕ → Pos → Maybe A → Events∞ A → Bool → Events A
    shown p i q (just a) k true  = out (q ++ [ sub p ]) a λ where .force → rejoin p i (force k)
    shown p i q nothing  k true  = skip (q ++ [ sub p ]) λ where .force → rejoin p i (force k)
    shown p i q _        k false = skip (p ++ [ ix i ]) λ where .force → rejoin p (suc i) (force k)

-- What a subscriber arriving at position `p` sees.
observe : ∀ {A} → MonotonicList A → Pos → Events A
observe (hot e)  p = rejoin p 0 e
observe (cold f) p = f p

------------------------------------------------------------------------
-- A cold leaf, placed

-- A burst at `r` puts its i-th step at `r ++ [ ix i ]` and ends at
-- `r ++ [ last ]`, which is also where the timer for the next frame is
-- created: after the burst and all it caused.  A frame at tick 0 is the
-- subscribe burst, rooted at the subscription itself.
private
  mutual
    frames : ∀ {A} → Time → Pos → ML A → Events A
    frames τ e done     = end e
    frames τ e quiet    = hush
    frames τ e (at t b) = burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

    burst : ∀ {A} → Time → Pos → ℕ → Burst A → Events A
    burst τ r i (emit a k) = out (r ++ [ ix i ]) a (λ where .force → burst τ r (suc i) (Burst∞.force k))
    burst τ r i (stall k)  = skip (r ++ [ ix i ]) (λ where .force → burst τ r (suc i) (Burst∞.force k))
    burst τ r i (close k)  = skip (r ++ [ ix i ]) (λ where .force → frames τ (r ++ [ last ]) (ML∞.force k))

  start : ∀ {A} → Pos → ML A → Events A
  start p (at zero b) = burst (tick p) p 0 b
  start p m           = frames (tick p) (p ++ [ last ]) m

coldᴰ : ∀ {A} → ML A → MonotonicList A
coldᴰ m = cold λ p → start p m

------------------------------------------------------------------------
-- What a runtime reports: positions forgotten, ticks kept

mutual
  ticks : ∀ {A} → Events A → ML A
  ticks (out k a r) = at (tick k) (emit a λ where .Burst∞.force → inFrame (tick k) (force r))
  ticks (skip k r)  = at (tick k) (stall λ where .Burst∞.force → inFrame (tick k) (force r))
  ticks (end k)     = done
  ticks hush        = quiet

  private
    inFrame : ∀ {A} → Time → Events A → Burst A
    inFrame t e = within t e (sameTick t e)

    sameTick : ∀ {A} → Time → Events A → Bool
    sameTick t (out k _ _) = tick k <ᵇ suc t
    sameTick t (skip k _)  = tick k <ᵇ suc t
    sameTick t (end _)     = false
    sameTick t hush        = false

    within : ∀ {A} → Time → Events A → Bool → Burst A
    within t (out k a r) true = emit a λ where .Burst∞.force → inFrame t (force r)
    within t (skip k r)  true = stall λ where .Burst∞.force → inFrame t (force r)
    within t e           _    = close λ where .ML∞.force → ticks e

------------------------------------------------------------------------
-- The operators

-- How `flattenᴰ` handles a lane arriving while others are live: merge
-- (with an optional concurrency bound; `just 1` is concat), switch to it,
-- or ignore it.
data FlatOp : Set where
  mergeᶠ           : Maybe ℕ → FlatOp
  switchᶠ exhaustᶠ : FlatOp

-- Every operator subscribes its source where it is itself subscribed,
-- so a stateful one (scan, takeWhile) starts afresh per subscriber.
private
  mapᴱ : ∀ {A B} → (A → B) → Events A → Events B
  mapᴱ f (out k a r) = out k (f a) λ where .force → mapᴱ f (force r)
  mapᴱ f (skip k r)  = skip k λ where .force → mapᴱ f (force r)
  mapᴱ f (end k)     = end k
  mapᴱ f hush        = hush

  scanᴱ : ∀ {A B} → (B → A → B) → B → Events A → Events B
  scanᴱ f z (out k a r) = out k (f z a) λ where .force → scanᴱ f (f z a) (force r)
  scanᴱ f z (skip k r)  = skip k λ where .force → scanᴱ f z (force r)
  scanᴱ f z (end k)     = end k
  scanᴱ f z hush        = hush

  -- The first failing value leaves first only when inclusive; the
  -- completion sits after its position either way.
  mutual
    takeWhileᴱ : ∀ {A} → Bool → (A → Bool) → Events A → Events A
    takeWhileᴱ i p (out k a r) = taking i p k a (p a) r
    takeWhileᴱ i p (skip k r)  = skip k λ where .force → takeWhileᴱ i p (force r)
    takeWhileᴱ i p (end k)     = end k
    takeWhileᴱ i p hush        = hush

    taking : ∀ {A} → Bool → (A → Bool) → Pos → A → Bool → Events∞ A → Events A
    taking i     p k a true  r = out k a λ where .force → takeWhileᴱ i p (force r)
    taking true  p k a false r = out k a λ where .force → end (k ++ [ last ])
    taking false p k a false r = end (k ++ [ last ])

  ofᴱ : ∀ {A} → Pos → ℕ → List A → Events A
  ofᴱ p i []       = end (p ++ [ last ])
  ofᴱ p i (x ∷ xs) = out (p ++ [ ix i ]) x λ where .force → ofᴱ p (suc i) xs

emptyᴰ : ∀ {A} → MonotonicList A
emptyᴰ = cold λ p → end (p ++ [ last ])

ofᴰ : ∀ {A} → List A → MonotonicList A
ofᴰ xs = cold λ p → ofᴱ p 0 xs

mapᴰ : ∀ {A B} → (A → B) → MonotonicList A → MonotonicList B
mapᴰ f s = cold λ p → mapᴱ f (observe s p)

scanᴰ : ∀ {A B} → (B → A → B) → B → MonotonicList A → MonotonicList B
scanᴰ f z s = cold λ p → scanᴱ f z (observe s p)

takeWhileᴰ : ∀ {A} → Bool → (A → Bool) → MonotonicList A → MonotonicList A
takeWhileᴰ i p s = cold λ q → takeWhileᴱ i p (observe s q)

-- A `skip`, then the body: rxjs's own `defer`, synchronous.
deferᴰ : ∀ {A} → MonotonicList A → MonotonicList A
deferᴰ s = cold λ p → skip (p ++ [ ix 0 ]) λ where .force → observe s (p ++ [ ix 1 ])

-- CONNECT, as a binder: rxjs's `connect(selector)`.  The body is
-- subscribed first, over the source made hot; then the source, into
-- the subject — so whatever the body joined synchronously sees the
-- source's whole subscribe burst.  Not a primitive: what the handle
-- shows a subscriber depends only on where it joins, so it is a value.
connectᴰ : ∀ {A B} → MonotonicList A → (MonotonicList A → MonotonicList B) → MonotonicList B
connectᴰ s f = cold λ p → observe (f (hot (observe s (p ++ [ ix 1 ])))) (p ++ [ ix 0 ])

-- FLATTEN: a sorted merge of the outer and its lanes in flight.  Each
-- element is an optional ECHO, at its first effect, beside an optional
-- LANE, subscribed at its second.  A bounded merge queues a lane past
-- its bound and subscribes it where a lane completes; the whole
-- completes where the last of the outer and its lanes does.
private
  Lane : Set → Set
  Lane B = Maybe B × Maybe (MonotonicList B)

  head : ∀ {A} → Events A → Maybe Pos
  head (out k _ _) = just k
  head (skip k _)  = just k
  head (end k)     = just k
  head hush        = nothing

  -- the lane whose next event comes first, with the lanes around it
  data Earliest (B : Set) : Set where
    none  : Earliest B
    found : Pos → List (Events B) → Events B → List (Events B) → Earliest B

  earliest : ∀ {B} → List (Events B) → Earliest B
  earliest []       = none
  earliest (l ∷ ls) = pick (head l) (earliest ls)
    where
      pick : Maybe Pos → Earliest _ → Earliest _
      pick nothing  none               = none
      pick nothing  (found k bs c as)  = found k (l ∷ bs) c as
      pick (just k) none               = found k [] l ls
      pick (just k) (found k′ bs c as) = if k <ᵖ k′ then found k [] l ls else found k′ (l ∷ bs) c as

  -- a lane arriving, subscribed at `q`
  admit : ∀ {B} → FlatOp → Pos → Maybe (MonotonicList B) → List (Events B) → List (MonotonicList B)
        → List (Events B) × List (MonotonicList B)
  admit op                q nothing  ls        qs = ls , qs
  admit (mergeᶠ nothing)  q (just m) ls        qs = observe m q ∷ ls , qs
  admit (mergeᶠ (just n)) q (just m) ls        qs =
    if length ls <ᵇ n then (observe m q ∷ ls , qs) else (ls , qs ++ [ m ])
  admit switchᶠ           q (just m) ls        qs = [ observe m q ] , qs
  admit exhaustᶠ          q (just m) []        qs = [ observe m q ] , qs
  admit exhaustᶠ          q (just m) (l ∷ ls)  qs = l ∷ ls , qs

  -- `o` is the outer, `nothing` once it has completed; `ls` the lanes in
  -- flight; `qs` the queue.
  mutual
    go : ∀ {B} → FlatOp → Maybe (Events (Lane B)) → List (Events B) → List (MonotonicList B) → Events B
    go op o ls qs with earliest ls
    ... | none            = viaOuter op o ls qs
    ... | found k bs l as = race op o k bs l as qs

    viaOuter : ∀ {B} → FlatOp → Maybe (Events (Lane B)) → List (Events B) → List (MonotonicList B) → Events B
    viaOuter op nothing  ls qs = hush
    viaOuter op (just e) ls qs = outer op e ls qs

    race : ∀ {B} → FlatOp → Maybe (Events (Lane B)) → Pos → List (Events B) → Events B → List (Events B)
         → List (MonotonicList B) → Events B
    race op nothing  k bs l as qs = lane op nothing bs l as qs
    race op (just e) k bs l as qs with head e
    ... | nothing = lane op (just e) bs l as qs
    ... | just k′ with k′ <ᵖ k
    ...   | true  = outer op e (bs ++ l ∷ as) qs
    ...   | false = lane op (just e) bs l as qs

    outer : ∀ {B} → FlatOp → Events (Lane B) → List (Events B) → List (MonotonicList B) → Events B
    outer op (out q (just b , m) r) ls qs with admit op (q ++ [ ix 1 ]) m ls qs
    ... | ls′ , qs′ = out (q ++ [ ix 0 ]) b λ where .force → go op (just (force r)) ls′ qs′
    outer op (out q (nothing , m) r) ls qs with admit op (q ++ [ ix 1 ]) m ls qs
    ... | ls′ , qs′ = skip (q ++ [ ix 0 ]) λ where .force → go op (just (force r)) ls′ qs′
    outer op (skip q r) ls qs = skip q λ where .force → go op (just (force r)) ls qs
    outer op (end c)    [] [] = end c
    outer op (end c)    ls qs = skip c λ where .force → go op nothing ls qs
    outer op hush       ls qs = hush

    lane : ∀ {B} → FlatOp → Maybe (Events (Lane B)) → List (Events B) → Events B → List (Events B)
         → List (MonotonicList B) → Events B
    lane op o bs (out k b r) as qs       = out k b λ where .force → go op o (bs ++ force r ∷ as) qs
    lane op o bs (skip k r)  as qs       = skip k λ where .force → go op o (bs ++ force r ∷ as) qs
    lane op o bs (end c)     as (m ∷ qs) =
      skip (c ++ [ ix 0 ]) λ where .force → go op o (observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs
    lane op nothing [] (end c) [] []     = end c
    lane op o bs (end c)     as []       = skip c λ where .force → go op o (bs ++ as) []
    lane op o bs hush        as qs       = hush

flattenᴰ : ∀ {A} → FlatOp → MonotonicList (Maybe A × Maybe (MonotonicList A)) → MonotonicList A
flattenᴰ op s = cold λ p → go op (just (observe s p)) [] []

------------------------------------------------------------------------
-- Approximation and recursion

-- No information yet: a subscription that spins and never closes.  The
-- bottom of the approximation order, and also the honest meaning of a
-- silent synchronous loop — the two coincide, as in any domain.
private
  spin : ∀ {A} → Pos → ℕ → Events A
  spin p i = skip (p ++ [ ix i ]) λ where .force → spin p (suc i)

⊥ᴰ : ∀ {A} → MonotonicList A
⊥ᴰ = cold λ p → spin p 0

postulate
  -- The same meaning, up to finitely many `skip`s, at every subscription.
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
  -- Built from the operators, `f` preserves the information order and
  -- limits; that is one lemma per operator, proven once.
  Continuous : ∀ {A} → (MonotonicList A → MonotonicList A) → Set
  fix-unfold : ∀ {A} {f : MonotonicList A → MonotonicList A}
             → Continuous f → fixᴰ f ≈ f (fixᴰ f)

------------------------------------------------------------------------
-- Comparing runs

postulate
  -- Information order on reported timelines: the left is the right with
  -- some suffixes replaced by a burst that stalls forever, and finitely
  -- many `stall`s inserted or dropped.
  _⊑_ : ∀ {A} → ML A → ML A → Set
  ⊑-trans : ∀ {A} {x y z : ML A} → x ⊑ y → y ⊑ z → x ⊑ z
  -- The same timeline, up to finitely many `stall`s.
  _≃_ : ∀ {A} → ML A → ML A → Set

  -- The least upper bound of a chain of runs.
  limit : ∀ {A} → (ℕ → ML A) → ML A

------------------------------------------------------------------------
-- Derived

mergeᴰ : ∀ {A} → MonotonicList A → MonotonicList A → MonotonicList A
mergeᴰ s t = flattenᴰ (mergeᶠ nothing) (mapᴰ (λ b → nothing , just (if b then s else t)) (ofᴰ (true ∷ false ∷ [])))

flatMapᴰ : ∀ {A B} → FlatOp → (A → MonotonicList B) → MonotonicList A → MonotonicList B
flatMapᴰ op f s = flattenᴰ op (mapᴰ (λ a → nothing , just (f a)) s)

-- Emits 1 forever, synchronously: the echo, then itself as the lane.
ones : MonotonicList ℕ
ones = fixᴰ λ x → flattenᴰ (mergeᶠ nothing) (ofᴰ ((just 1 , just (deferᴰ x)) ∷ []))
