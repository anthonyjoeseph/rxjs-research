{-# OPTIONS --guardedness #-}

-- THE BOUND HALF, AS A SIMULATION.  The pure run's record is placed
-- against the events the denotation shows the root (`operation.Placed`):
-- each value at its own event, in order, the run ending as the events do.
--
-- One invariant over the whole running program, `Live`, carried by the
-- event loop: subscribing establishes it, each turn keeps it, a cut
-- leaves the record a prefix, and a dry queue leaves events that show
-- nothing more.  The loop itself is proven here once, over any such
-- invariant.
module Bound where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Pos; tick; Events; Events∞;
  out; skip; hush; observe; root)
open import denotation.Denote using (⟦_⟧[_])
open import operation.PureObservable using (PureObs; Pureᴾ; same; _⊑_; _⨾_; module Pure)
open import operation.Placed using (Placed; cut; quiets; sends; skips; module Ran)

open Events∞

------------------------------------------------------------------------
-- Timelines that rise

-- A place along a cold's timeline: a frame to come, or inside one.
data Along (A : Set) : Set where
  ahead  : ML A → Along A
  inside : Burst A → Along A

-- A TIMELINE THAT RISES: no frame before tick t, each after the last.
mutual
  record Rises {A : Set} (t : Time) (x : Along A) : Set where
    coinductive
    field rises : Rise t x

  Rise : ∀ {A} → Time → Along A → Set
  Rise t (ahead done)              = ⊤
  Rise t (ahead quiet)             = ⊤
  Rise t (ahead (at t′ b))         = t ≤ t′ × Rises (suc t′) (inside b)
  Rise t (inside (emit _ k))       = Rises t (inside (Burst∞.force k))
  Rise t (inside (stall k))        = Rises t (inside (Burst∞.force k))
  Rise t (inside (close k))        = Rises t (ahead (ML∞.force k))

-- Every cold a program reaches within n `defer`s rises.
Rising : ∀ {Γ A} → ℕ → PureObs Γ A → Set
Rising n       (cold c)          = Rises 0 (ahead (lower c))
Rising n       empty             = ⊤
Rising n       (of xs)           = ⊤
Rising n       (map f s)         = Rising n s
Rising n       (scan f z s)      = Rising n s
Rising n       (takeWhile i p s) = Rising n s
Rising n       (flatMap op f s)  = (∀ a → Rising n (f a)) × Rising n s
Rising n       (connect s b)     = Rising n s × Rising n b
Rising n       (connected i)     = ⊤
Rising zero    (defer l)         = ⊤
Rising (suc n) (defer l)         = Rising n (Later.force l)

------------------------------------------------------------------------
-- The record so far

module Prefix (A : Set) where
  open Pure A using (End; dry; cutOff)

  -- Through skips only.
  data _↝_ : Events A → Events A → Set where
    stay : ∀ {e} → e ↝ e
    past : ∀ {p k e} → force k ↝ e → skip p k ↝ e

  -- The record so far, each value at its own event of `E`, with `r` left.
  data Pre : List Pos → List (Time × A) → Events A → Events A → Set where
    pnil  : ∀ {e} → Pre [] [] e e
    pskip : ∀ {qs xs p k r} → Pre qs xs (force k) r → Pre qs xs (skip p k) r
    pout  : ∀ {qs xs p a k r} → Pre qs xs (force k) r → Pre (p ∷ qs) ((tick p , a) ∷ xs) (out p a k) r

  -- Read off where the run was cut.
  pre-cut : ∀ {qs xs E r} c → Pre qs xs E r → Placed (cutOff c) qs xs E
  pre-cut c pnil      = cut
  pre-cut c (pskip p) = skips (pre-cut c p)
  pre-cut c (pout p)  = sends (pre-cut c p)

  -- Read off where the queue ran dry, over events that show nothing more.
  pre-dry : ∀ {qs xs E r} → Pre qs xs E r → r ↝ hush → Placed dry qs xs E
  pre-dry pnil      stay     = quiets
  pre-dry pnil      (past s) = skips (pre-dry pnil s)
  pre-dry (pskip p) s        = skips (pre-dry p s)
  pre-dry (pout p)  s        = sends (pre-dry p s)

------------------------------------------------------------------------
-- How a run may stand, against the root's events `E₀`

module Ends (R : Set) (E₀ : Events R) where
  open Prefix R
  open Pure R using (State; finished)

  -- The root's record so far, with `r` left; or complete.
  data Root {h} (r : Events R) (st : State h) : Set where
    live : State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r → Root r st
    over : State.ended st ≡ true → Placed finished (State.marks st) (State.log st) E₀ → Root r st

  -- Where a cut may leave it: a prefix, or complete.
  data CutOk {h} (st : State h) : Set₁ where
    cutok : ∀ {r} → Root r st → CutOk st

  -- Where a dry queue may leave it: silent over events that show nothing
  -- more, or complete.
  data Done {h} (st : State h) : Set₁ where
    silent : ∀ {r} → State.ended st ≡ false → Pre (State.marks st) (State.log st) E₀ r → r ↝ hush → Done st
    over   : State.ended st ≡ true → Placed finished (State.marks st) (State.log st) E₀ → Done st

------------------------------------------------------------------------
-- THE LOOP, over any invariant `Live` it is handed: a run that keeps it
-- turn by turn leaves its record placed.

module Loop (R : Set) (E₀ : Events R) (N : ℕ) (Live : ∀ {h} → Pure.State R h → Set₁) where
  open Ends R E₀
  open Pure R using (State; Res; res; Timer; M; module Play; runᴺ; loopᴺ; cascade; ret; then; unlessSpent)

  -- A run so far, as the loop needs it: cut anywhere, or live.
  PostV : ∀ {h} → State h → Maybe ⊤ → Set₁
  PostV st nothing  = CutOk st
  PostV st (just _) = Live st

  Post : ∀ {h} → Res h ⊤ → Set₁
  Post x = PostV (Res.state x) (Res.value x)

  -- The whole run: cut anywhere, or done.
  PostDV : ∀ {h} → State h → Maybe ⊤ → Set₁
  PostDV st nothing  = CutOk st
  PostDV st (just _) = Done st

  PostD : ∀ {h} → Res h ⊤ → Set₁
  PostD x = PostDV (Res.state x) (Res.value x)

  -- One turn's work: the earliest timer's frame, on a callback budget k.
  turn : ∀ k {h} → State h → Timer h → List (Timer h) → Res h ⊤
  turn k st tm ts = unlessSpent (Timer.handle tm)
    (Play.burst N (runᴺ N k) N (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm))
    same (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })

  then-ok : ∀ {h} (K : ⊤ → M h ⊤) (Y : Res h ⊤) → Post Y
          → (∀ {v} (g : h ⊑ v) (st : State v) → Live st → PostD (K tt g st)) → PostD (then K Y)
  then-ok K (res g st nothing)   q f = q
  then-ok K (res g st (just tt)) q f = f g st q

  module Turns (live-cut  : ∀ {h} {st : State h} → Live st → CutOk st)
               (live-dry  : ∀ {h} {st : State h} → Live st → State.timers st ≡ [] → Done st)
               (live-turn : ∀ k {h} (st : State h) {tm ts} → Live st → State.timers st ≡ tm ∷ ts → Post (turn k st tm ts)) where

    again : ℕ → Bool → M [] ⊤
    again m a = if_then_else_ {A = M [] ⊤} a (loopᴺ N m) (ret tt)

    mutual
      loop-ok : ∀ m {h} (σ : [] ⊑ h) (st : State h) → Live st → PostD (loopᴺ N m σ st)
      loop-ok zero    σ st q = live-cut q
      loop-ok (suc m) σ st q with State.timers st in eq
      ... | []     = live-dry q eq
      ... | tm ∷ ts = loop-tail m σ (turn (suc m) st tm ts) (live-turn (suc m) st q eq)

      loop-tail : ∀ m {h} (σ : [] ⊑ h) (Y : Res h ⊤) → Post Y
                → PostD (then (λ a τ → again m a (σ ⨾ τ)) (then (λ _ _ st′ → res same st′ (just true)) Y))
      loop-tail m σ (res g st nothing)   q = q
      loop-tail m σ (res g st (just tt)) q = loop-ok m (σ ⨾ g) st q

------------------------------------------------------------------------
-- THE BOUND HALF

module Places (R : Set) where
  open Ran R using (ran; Recorded)
  open Pure R using (State; Res; res; start; recorder; compileᴺ; runᴺ; loopᴺ)
  open import operation.AbstractObservable using (module Run)
  open Run (Pureᴾ R) using (done)

  -- What the root is shown: approximant n of the program's denotation.
  shown : ℕ → PureObs [] R → Events R
  shown n o = observe (⟦ o ⟧[ n ] []) root

  postulate
    -- THE CONFIGURATION: the running program's state, related to what is
    -- left of the events each part of it shows — every subscription's
    -- cells, timers and observer against its denotation's remainder, and
    -- the root's record against the prefix of `shown n o` it has passed.
    -- One relation for the whole program, carried by the loop.
    --
    -- DEAD ROUTE: a relation per operator (a `Below s d`, against any
    --   observer that keeps an abstract interface) cannot be carried.
    --   Siblings that share one observer — a merge's lanes, a subject's
    --   joiners — each hold a remainder only the shared state records, and
    --   an abstract step returns its sibling's as an existential witness,
    --   forgotten; and a merge's order needs every sibling's pending
    --   positions, which an abstract subscription does not expose.
    Live : ∀ (n : ℕ) (o : PureObs [] R) {h} → State h → Set₁

  module At (n : ℕ) (o : PureObs [] R) (N : ℕ) where
    open Ends R (shown n o) public
    open Loop R (shown n o) N (Live n o) public

  postulate
    -- Subscribing the program at the root, on any budget, leaves it live
    -- or cut.
    live-start : ∀ n (o : PureObs [] R) → Rising n o → ∀ N k
               → At.Post n o N (runᴺ N k (compileᴺ n o [] same recorder λ _ _ → done tt) same start)
    -- A cut leaves the record a prefix.
    live-cut   : ∀ n o {h} {st : State h} → Live n o st → At.CutOk n o 0 st
    -- With no timer left, nothing more is shown.
    live-dry   : ∀ n o {h} {st : State h} → Live n o st → State.timers st ≡ [] → At.Done n o 0 st
    -- One turn of the loop keeps it.
    --
    -- RECOVERY: `git show 016c16a2` restores a cold at the root proven
    --   against the engine: its subscribe burst, each timer's turn, and
    --   the record placed, frame by frame.
    live-turn : ∀ n o N k {h} (st : State h) {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts → At.Post n o N (At.turn n o N k st tm ts)

  -- THE BOUND HALF: approximant m of the engine leaves its record placed
  -- against the events approximant n of the denotation shows the root,
  -- each value at its own event.
  places : ∀ n (o : PureObs [] R) → Rising n o → ∀ m → Recorded (ran m (compileᴺ n o [])) (shown n o)
  places n o u m = rec (ran m (compileᴺ n o []))
    (then-ok (λ _ τ → loopᴺ m m (same ⨾ τ)) (runᴺ m m (compileᴺ n o [] same recorder λ _ _ → done tt) same start)
             (live-start n o u m m) λ g st q → loop-ok m (same ⨾ g) st q)
    where
      open At n o m
      open Turns (live-cut n o) (live-dry n o) (live-turn n o m)
      open Prefix R

      rec : (x : Res [] ⊤) → PostD x → Recorded x (shown n o)
      rec (res σ st nothing)   (cutok (live e p)) rewrite e = pre-cut _ p
      rec (res σ st nothing)   (cutok (over e p)) rewrite e = p
      rec (res σ st (just tt)) (silent e p r)     rewrite e = pre-dry p r
      rec (res σ st (just tt)) (over e p)         rewrite e = p
