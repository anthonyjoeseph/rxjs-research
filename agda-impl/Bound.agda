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
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Data.List.Membership.Propositional using (_∈_)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Pos; tick; Events; Events∞;
  out; skip; hush; observe; root)
open import denotation.Denote using (⟦_⟧[_])
open import operation.PureObservable using (PureObs; Pureᴾ; same; _⊑_; _⨾_; module Pure)
open import operation.Placed using (Placed; cut; quiets; sends; skips; module Ran)
open import Config using (_≅_; skipˡ; hush≅; module Nodes)
open import Realize using (module Realizing)

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

  -- Agreeing with silence up to skips is reaching it through them.
  ≅-hush : ∀ {r} → r ≅ hush → r ↝ hush
  ≅-hush (skipˡ q) = past (≅-hush q)
  ≅-hush hush≅     = stay

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
  open Pure R using (State; Res; res; shift; start; recorder; compileᴺ; runᴺ; loopᴺ; Timer; get; cascade; finished; module Play)
  open import operation.AbstractObservable using (module Run)
  open Run (Pureᴾ R) using (done; eff; Observer; Env)
  open Prefix R using (_↝_; ≅-hush)

  -- What the root is shown: approximant n of the program's denotation.
  shown : ℕ → PureObs [] R → Events R
  shown n o = observe (⟦ o ⟧[ n ] []) root

  -- THE CONFIGURATION: until the root completes, the state realizes a
  -- tree that means what is left of the root's events.
  Rest : ∀ (n : ℕ) {h} → Events R → State h → Set₁
  Rest n r st = State.ended st ≡ false → Σ (Nodes.Node n [] R) λ c → Realizing.Realizes R n c st × r ≅ Nodes.⟦_⟧ᶜ n c []

  -- THE INVARIANT: the root's record so far, against the root's events,
  -- with what is left of them the configuration's.
  record Live (n : ℕ) (o : PureObs [] R) {h} (st : State h) : Set₁ where
    constructor config
    field
      {left} : Events R
      sofar  : Ends.Root R (shown n o) left st
      rest   : Rest n left st

  module At (n : ℕ) (o : PureObs [] R) (N : ℕ) where
    open Ends R (shown n o) public
    open Loop R (shown n o) N (Live n o) public

  postulate
    -- Subscribing the program at the root, on any budget, leaves it live
    -- or cut.
    live-start : ∀ n (o : PureObs [] R) → Rising n o → ∀ N k
               → At.Post n o N (runᴺ N k (compileᴺ n o [] same recorder λ _ _ → done tt) same start)
    -- A turn from a run already complete leaves it complete, its record
    -- untouched: the engine notes nothing once the root has ended.
    turn-over : ∀ n o N k {h} (st : State h) {tm ts} → State.ended st ≡ true
              → State.ended (Res.state (At.turn n o N k st tm ts)) ≡ true
              × State.log (Res.state (At.turn n o N k st tm ts)) ≡ State.log st
              × State.marks (Res.state (At.turn n o N k st tm ts)) ≡ State.marks st
    -- A frame played from a configuration whose one firing cold is the
    -- timer's keeps it: the clock at the timer's tick, the position at
    -- its cascade, the root not yet complete.
    --
    -- RECOVERY: `git show 016c16a2` restores a cold at the root proven
    --   against the engine: its subscribe burst, each timer's turn, and
    --   the record placed, frame by frame.
    live-burst : ∀ n o N k {h} {st : State h} {tm} {r} {c} (σ : h ⊑ h) (t : Realizing.Sub R n h [] R) (p : tm ∈ Realizing.pendings R n t)
               → Ends.Root R (shown n o) r st → State.ended st ≡ false
               → (z : Realizing.Holding R n c st) → Realizing.Holding.tree z ≡ Realizing.fire R n t p → Realizing.Calm R n t
               → r ≅ Nodes.⟦_⟧ᶜ n c [] → State.clock st ≡ Timer.due tm → State.pos st ≡ cascade tm
               → At.Post n o N (Play.burst N (runᴺ N k) N (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) σ st)

  -- Popping a timer moves neither the record nor whether it is complete.
  moved : ∀ n o {h} {st : State h} {tm : Timer h} {ts} {r} → Ends.Root R (shown n o) r st
        → Ends.Root R (shown n o) r (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  moved n o (Ends.live e p) = Ends.live e p
  moved n o (Ends.over e p) = Ends.over e p

  -- Only the state and the value are judged, never the world's path.
  post-shift : ∀ n o N {h v} (ρ : h ⊑ v) (Y : Res v ⊤) → At.Post n o N Y → At.Post n o N (shift ρ Y)
  post-shift n o N ρ (res σ st b) q = q

  -- A complete record keeps it, live or cut.
  post-over : ∀ n o N {h} (Y : Res h ⊤) → State.ended (Res.state Y) ≡ true
            → Placed finished (State.marks (Res.state Y)) (State.log (Res.state Y)) (shown n o) → At.Post n o N Y
  post-over n o N (res σ st nothing)   e p = Ends.cutok {r = hush} (Ends.over e p)
  post-over n o N (res σ st (just tt)) e p = config {left = hush} (Ends.over e p) λ f → Realizing.absurd R n (trans (sym e) f)

  -- A spent timer's turn keeps it: nothing is played.
  live-spent : ∀ n o {h} {st : State h} {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts
             → lower (get (State.heap st) (Timer.handle tm)) ≡ true
             → Live n o (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  live-spent n o {st = st} {tm} {ts} (config sofar rest) eq s = config (moved n o {tm = tm} {ts} sofar) λ e →
    proj₁ (rest e) , Realizing.realizes-spent R n (proj₁ (proj₂ (rest e))) eq s , proj₂ (proj₂ (rest e))

  -- A turn that fires a frame keeps it: complete already, or its cold
  -- started and the frame played.
  live-fire : ∀ n o N k {h} (st : State h) {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts
            → lower (get (State.heap st) (Timer.handle tm)) ≡ false → At.Post n o N (At.turn n o N k st tm ts)
  live-fire n o N k st {tm} {ts} (config sofar rest) eq s = by (State.ended st) refl
    where
      by : ∀ b → State.ended st ≡ b → At.Post n o N (At.turn n o N k st tm ts)
      by true e = post-over n o N (At.turn n o N k st tm ts) (proj₁ ov)
        (subst₂ (λ ms ls → Placed finished ms ls (shown n o)) (sym (proj₂ (proj₂ ov))) (sym (proj₁ (proj₂ ov))) (complete sofar))
        where
          ov = turn-over n o N k st {tm} {ts} e
          complete : ∀ {r} → Ends.Root R (shown n o) r st → Placed finished (State.marks st) (State.log st) (shown n o)
          complete (Ends.live f _) = Realizing.absurd R n (trans (sym e) f)
          complete (Ends.over _ p) = p
      by false e with rest e
      ... | c , z , b with Realizing.firing-start R n (Realizing.Realizes.holding z) eq s
      ... | p , z′ , teq rewrite s = post-shift n o N same
            (Play.burst N (runᴺ N k) N (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) (same ⨾ same)
              (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }))
            (live-burst n o N k (same ⨾ same) (Realizing.Holding.tree (Realizing.Realizes.holding z)) p (moved n o {tm = tm} {ts} sofar) e z′ teq
                        (Realizing.Realizes.calm z) b refl refl)

  -- One turn of the loop keeps it.
  live-turn : ∀ n o N k {h} (st : State h) {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts → At.Post n o N (At.turn n o N k st tm ts)
  live-turn n o N k st {tm} {ts} q eq = by (lower (get (State.heap st) (Timer.handle tm))) refl
    where
      by : ∀ b → lower (get (State.heap st) (Timer.handle tm)) ≡ b → At.Post n o N (At.turn n o N k st tm ts)
      by true  s rewrite s = live-spent n o q eq s
      by false s           = live-fire n o N k st q eq s

  -- With no timer left, a root not yet complete is shown nothing more.
  rest-dry : ∀ n {h} {r} {st : State h} → Rest n r st → State.ended st ≡ false → State.timers st ≡ [] → r ↝ hush
  rest-dry n {r = r} z e eq with z e
  ... | c , q , b = ≅-hush (subst (r ≅_) (Nodes.dry-hush n c [] (Realizing.realizes-dry R n q eq)) b)

  -- A cut leaves the record a prefix.
  live-cut : ∀ n o {h} {st : State h} → Live n o st → At.CutOk n o 0 st
  live-cut n o (config q _) = cutok q
    where open At n o 0

  -- With no timer left, nothing more is shown.
  live-dry : ∀ n o {h} {st : State h} → Live n o st → State.timers st ≡ [] → At.Done n o 0 st
  live-dry n o (config (Ends.live e p) z) eq = Ends.silent e p (rest-dry n z e eq)
  live-dry n o (config (Ends.over e p) z) eq = Ends.over e p

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
