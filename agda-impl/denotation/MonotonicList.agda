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
open import Data.Nat using (ℕ; zero; suc; _+_; _<ᵇ_; _≤′_; ≤′-refl; ≤′-step)
open import Level using (Lift; 0ℓ) renaming (suc to lsuc)
open import Data.Bool using (T)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ; ≮⇒≥; ≤-antisym; <⇒≤; <-trans; ≤-reflexive; n≮n)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong; cong₂)

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

-- Lifted only because the leaf slot of a program tree is `Set₁` (the
-- IO leaf carries an existential).
Timeline : Set → Set₁
Timeline A = Lift (lsuc 0ℓ) (From A 0)

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

<ᵖ-trans : ∀ p q r → p <ᵖ q ≡ true → q <ᵖ r ≡ true → p <ᵖ r ≡ true
<ᵖ-trans p q r h₁ h₂ rewrite lt-pos p q r (isLt-lt h₁) (isLt-lt h₂) = refl

<ᵖ-irrefl : ∀ p → p <ᵖ p ≡ false
<ᵖ-irrefl p rewrite refl-pos p = refl

-- An earlier position is at no later a tick.
<ᵖ-ix : ∀ m n p q → (ix m ∷ p) <ᵖ (ix n ∷ q) ≡ true → m ≤ n
<ᵖ-ix m n p q h with lexi-lt (cmpℕ m n) (cmpPos p q) (isLt-lt h)
... | inj₁ x       = <⇒≤ (lt-ℕ {m} {n} x)
... | inj₂ (x , _) = ≤-reflexive (eq-ℕ {m} {n} x)

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
mutual
  frames : ∀ {A t} → Time → Pos → From A t → Events A
  frames τ e done       = end e
  frames τ e quiet      = hush
  frames τ e (at t _ b) = burst τ (ix (τ + t) ∷ sub e ∷ []) 0 b

  burst : ∀ {A t} → Time → Pos → ℕ → Frame A t → Events A
  burst τ r i (emit a k) = out (r ++ [ ix i ]) a (λ where .force → burst τ r (suc i) (Frame∞.force k))
  burst τ r i (stall k)  = skip (r ++ [ ix i ]) (λ where .force → burst τ r (suc i) (Frame∞.force k))
  burst τ r i (close k)  = skip (r ++ [ ix i ]) (λ where .force → frames τ (r ++ [ last ]) (From∞.force k))

start : ∀ {A} → Pos → From A 0 → Events A
start p (at zero _ b) = burst (tick p) p 0 b
start p m             = frames (tick p) (p ++ [ last ]) m

coldᴰ : ∀ {A} → From A 0 → MonotonicList A
coldᴰ m = cold λ p → start p m

------------------------------------------------------------------------
-- What a runtime reports: positions forgotten, ticks kept

mutual
  ticks : ∀ {A} → Events A → ML A
  ticks (out k a r) = at (tick k) (emit a λ where .Burst∞.force → inFrame (tick k) (force r))
  ticks (skip k r)  = at (tick k) (stall λ where .Burst∞.force → inFrame (tick k) (force r))
  ticks (end k)     = done
  ticks hush        = quiet

  -- The rest of a frame at tick t: whatever comes no later than t.
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

-- How `flatMapᴰ` handles a lane arriving while others are live: merge
-- (with an optional concurrency bound; `just 1` is concat), switch to it,
-- or ignore it.
data FlatOp : Set where
  mergeᶠ           : Maybe ℕ → FlatOp
  switchᶠ exhaustᶠ : FlatOp

-- Every operator subscribes its source where it is itself subscribed,
-- so a stateful one (scan, takeWhile) starts afresh per subscriber.
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

-- FLATMAP: a sorted merge of the outer and its lanes in flight.  Each
-- element's lane is subscribed at the element's second effect, its first
-- being silent.  A bounded merge queues a lane past
-- its bound and subscribes it where a lane completes; the whole
-- completes where the last of the outer and its lanes does.
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
admit : ∀ {B} → FlatOp → Pos → MonotonicList B → List (Events B) → List (MonotonicList B)
      → List (Events B) × List (MonotonicList B)
admit (mergeᶠ nothing)  q m ls        qs = observe m q ∷ ls , qs
admit (mergeᶠ (just n)) q m ls        qs =
  if length ls <ᵇ n then (observe m q ∷ ls , qs) else (ls , qs ++ [ m ])
admit switchᶠ           q m ls        qs = [ observe m q ] , qs
admit exhaustᶠ          q m []        qs = [ observe m q ] , qs
admit exhaustᶠ          q m (l ∷ ls)  qs = l ∷ ls , qs

-- `o` is the outer, `nothing` once it has completed; `ls` the lanes in
-- flight; `qs` the queue.
mutual
  go : ∀ {B} → FlatOp → Maybe (Events (MonotonicList B)) → List (Events B) → List (MonotonicList B) → Events B
  go op o ls qs with earliest ls
  ... | none            = viaOuter op o ls qs
  ... | found k bs l as = race op o k bs l as qs

  viaOuter : ∀ {B} → FlatOp → Maybe (Events (MonotonicList B)) → List (Events B) → List (MonotonicList B) → Events B
  viaOuter op nothing  ls qs = hush
  viaOuter op (just e) ls qs = outer op e ls qs

  race : ∀ {B} → FlatOp → Maybe (Events (MonotonicList B)) → Pos → List (Events B) → Events B → List (Events B)
       → List (MonotonicList B) → Events B
  race op nothing  k bs l as qs = lane op nothing bs l as qs
  race op (just e) k bs l as qs with head e
  ... | nothing = lane op (just e) bs l as qs
  ... | just k′ with k′ <ᵖ k
  ...   | true  = outer op e (bs ++ l ∷ as) qs
  ...   | false = lane op (just e) bs l as qs

  outer : ∀ {B} → FlatOp → Events (MonotonicList B) → List (Events B) → List (MonotonicList B) → Events B
  outer op (out q m r) ls qs with admit op (q ++ [ ix 1 ]) m ls qs
  ... | ls′ , qs′ = skip (q ++ [ ix 0 ]) λ where .force → go op (just (force r)) ls′ qs′
  outer op (skip q r) ls qs = skip q λ where .force → go op (just (force r)) ls qs
  outer op (end c)    [] [] = end c
  outer op (end c)    ls qs = skip c λ where .force → go op nothing ls qs
  outer op hush       ls qs = hush

  lane : ∀ {B} → FlatOp → Maybe (Events (MonotonicList B)) → List (Events B) → Events B → List (Events B)
       → List (MonotonicList B) → Events B
  lane op o bs (out k b r) as qs       = out k b λ where .force → go op o (bs ++ force r ∷ as) qs
  lane op o bs (skip k r)  as qs       = skip k λ where .force → go op o (bs ++ force r ∷ as) qs
  lane op o bs (end c)     as (m ∷ qs) =
    skip (c ++ [ ix 0 ]) λ where .force → go op o (observe m (c ++ [ ix 1 ]) ∷ bs ++ as) qs
  lane op nothing [] (end c) [] []     = end c
  lane op o bs (end c)     as []       = skip c λ where .force → go op o (bs ++ as) []
  lane op o bs hush        as qs       = hush

flatMapᴰ : ∀ {A B} → FlatOp → (A → MonotonicList B) → MonotonicList A → MonotonicList B
flatMapᴰ op f s = cold λ p → go op (just (observe (mapᴰ f s) p)) [] []

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

-- AGREEING FOR k STEPS: the same first k steps, positions and values
-- alike.  Approximants settle one step at a time, so this is what every
-- limit below is measured in.
data Agree {A : Set} : ℕ → Events A → Events A → Set where
  stop  : ∀ {x y} → Agree zero x y
  out⁼  : ∀ {k p a l r} → Agree k (force l) (force r) → Agree (suc k) (out p a l) (out p a r)
  skip⁼ : ∀ {k p l r} → Agree k (force l) (force r) → Agree (suc k) (skip p l) (skip p r)
  end⁼  : ∀ {k p} → Agree (suc k) (end p) (end p)
  hush⁼ : ∀ {k} → Agree (suc k) hush hush

-- Agreeing for k steps at every subscription.
_≈[_]_ : ∀ {A} → MonotonicList A → ℕ → MonotonicList A → Set
x ≈[ k ] y = ∀ p → Agree k (observe x p) (observe y p)

-- THE SAME MEANING: alike at every subscription, for any number of steps.
_≈_ : ∀ {A} → MonotonicList A → MonotonicList A → Set
x ≈ y = ∀ k → x ≈[ k ] y

-- Each approximant agrees with the next for as many steps as its index.
-- A program's approximants do, on every seed `make chain` draws: every
-- cut in approximant n sits under n `defer`s, each a `skip` before it.
Settling : ∀ {A} → (ℕ → MonotonicList A) → Set
Settling c = ∀ n → c n ≈[ n ] c (suc n)

private
  agree-refl : ∀ {A} k (x : Events A) → Agree k x x
  agree-refl zero    x           = stop
  agree-refl (suc k) (out p a l) = out⁼ (agree-refl k (force l))
  agree-refl (suc k) (skip p l)  = skip⁼ (agree-refl k (force l))
  agree-refl (suc k) (end p)     = end⁼
  agree-refl (suc k) hush        = hush⁼

  agree-sym : ∀ {A k} {x y : Events A} → Agree k x y → Agree k y x
  agree-sym stop      = stop
  agree-sym (out⁼ a)  = out⁼ (agree-sym a)
  agree-sym (skip⁼ a) = skip⁼ (agree-sym a)
  agree-sym end⁼      = end⁼
  agree-sym hush⁼     = hush⁼

  agree-trans : ∀ {A k} {x y z : Events A} → Agree k x y → Agree k y z → Agree k x z
  agree-trans stop      _         = stop
  agree-trans (out⁼ a)  (out⁼ b)  = out⁼ (agree-trans a b)
  agree-trans (skip⁼ a) (skip⁼ b) = skip⁼ (agree-trans a b)
  agree-trans end⁼      end⁼      = end⁼
  agree-trans hush⁼     hush⁼     = hush⁼

  agree-pred : ∀ {A k} {x y : Events A} → Agree (suc k) x y → Agree k x y
  agree-pred {k = zero}  _         = stop
  agree-pred {k = suc k} (out⁼ a)  = out⁼ (agree-pred a)
  agree-pred {k = suc k} (skip⁼ a) = skip⁼ (agree-pred a)
  agree-pred {k = suc k} end⁼      = end⁼
  agree-pred {k = suc k} hush⁼     = hush⁼

  agree-≤ : ∀ {A m n} {x y : Events A} → m ≤′ n → Agree n x y → Agree m x y
  agree-≤ ≤′-refl       a = a
  agree-≤ (≤′-step m≤n) a = agree-≤ m≤n (agree-pred a)

  -- Past the first step.
  rest : ∀ {A} → Events A → Events A
  rest (out _ _ r) = force r
  rest (skip _ r)  = force r
  rest e           = e

  agree-rest : ∀ {A k} {x y : Events A} → Agree (suc k) x y → Agree k (rest x) (rest y)
  agree-rest (out⁼ a)  = a
  agree-rest (skip⁼ a) = a
  agree-rest end⁼      = agree-refl _ _
  agree-rest hush⁼     = agree-refl _ _

  mutual
    -- Step j of the limit, read off the (j+1)-th stream, each stream
    -- already j steps in.
    diag : ∀ {A} → (ℕ → Events A) → Events A
    diag es = settle (es 1) es

    settle : ∀ {A} → Events A → (ℕ → Events A) → Events A
    settle (out p a _) es = out p a λ where .force → diag λ n → rest (es (suc n))
    settle (skip p _)  es = skip p λ where .force → diag λ n → rest (es (suc n))
    settle (end p)     es = end p
    settle hush        es = hush

  1≤′suc : ∀ m → 1 ≤′ suc m
  1≤′suc zero    = ≤′-refl
  1≤′suc (suc m) = ≤′-step (1≤′suc m)

  -- A settling sequence of streams agrees with itself further on.
  settled : ∀ {A} {es : ℕ → Events A} → (∀ n → Agree n (es n) (es (suc n)))
          → ∀ {n m} → n ≤′ m → Agree n (es n) (es m)
  settled s ≤′-refl                    = agree-refl _ _
  settled s {m = suc m} (≤′-step n≤m) = agree-trans (settled s n≤m) (agree-≤ n≤m (s m))

  settle-agree : ∀ {A k} {x y : Events A} {es} → Agree 1 x y
               → Agree k (rest y) (diag λ n → rest (es (suc n))) → Agree (suc k) y (settle x es)
  settle-agree (out⁼ _)  a = out⁼ a
  settle-agree (skip⁼ _) a = skip⁼ a
  settle-agree end⁼      a = end⁼
  settle-agree hush⁼     a = hush⁼

  diag-limit : ∀ {A} {es : ℕ → Events A} → (∀ n → Agree n (es n) (es (suc n))) → ∀ m → Agree m (es m) (diag es)
  diag-limit s zero              = stop
  diag-limit {es = es} s (suc m) =
    settle-agree {es = es} (settled s (1≤′suc m))
      (diag-limit {es = λ n → rest (es (suc n))} (λ n → agree-rest (s (suc n))) m)

-- THE LIMIT of approximants that settle one step at a time: approximant
-- n's first n steps are final, so step j is read off approximant j+1.
-- Defined for any sequence; `lub-limit` says what it is of a settling one.
lub : ∀ {A} → (ℕ → MonotonicList A) → MonotonicList A
lub c = cold λ p → diag λ n → observe (c n) p

-- A settling sequence agrees with its limit for as many steps as the
-- approximant's index.
lub-limit : ∀ {A} {c : ℕ → MonotonicList A} → Settling c → ∀ m → c m ≈[ m ] lub c
lub-limit s m p = diag-limit (λ n → s n p) m

-- Approximant n of a recursive definition: unfold it n times from ⊥ᴰ.
iterate : ∀ {A} → ℕ → (MonotonicList A → MonotonicList A) → MonotonicList A
iterate zero    f = ⊥ᴰ
iterate (suc n) f = f (iterate n f)

-- RECURSION.  Agda cannot accept `ones = mergeᴰ (ofᴰ [ 1 ]) (deferᴰ ones)`:
-- it never looks inside `flatMapᴰ`, which could strip the guard.  So
-- recursion here is the limit of `f`'s iterates from ⊥ᴰ, total for any `f`.
fixᴰ : ∀ {A} → (MonotonicList A → MonotonicList A) → MonotonicList A
fixᴰ f = lub λ n → iterate n f

-- Settling one step more than its argument has: a recursion guarded the
-- way a `defer` guards one.
Contractive : ∀ {A} → (MonotonicList A → MonotonicList A) → Set
Contractive f = ∀ {k x y} → x ≈[ k ] y → f x ≈[ suc k ] f y

-- A contractive `f`'s limit is its fixed point.
fix-unfold : ∀ {A} {f : MonotonicList A → MonotonicList A} → Contractive f → fixᴰ f ≈ f (fixᴰ f)
fix-unfold {f = f} cf k p =
  agree-trans (agree-sym (lub-limit {c = c} iterates k p))
    (agree-trans (iterates k p) (agree-pred (cf (lub-limit {c = c} iterates k) p)))
  where
    c : ℕ → MonotonicList _
    c n = iterate n f
    iterates : Settling c
    iterates zero    p = stop
    iterates (suc n)   = cf (iterates n)

------------------------------------------------------------------------
-- Derived

mergeᴰ : ∀ {A} → MonotonicList A → MonotonicList A → MonotonicList A
mergeᴰ s t = flatMapᴰ (mergeᶠ nothing) (λ b → if b then s else t) (ofᴰ (true ∷ false ∷ []))

-- Emits 1 forever, synchronously.
ones : MonotonicList ℕ
ones = fixᴰ λ x → mergeᴰ (ofᴰ (1 ∷ [])) (deferᴰ x)
