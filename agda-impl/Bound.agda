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
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _∸_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Level using (lower; lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer; Later)
open import denotation.MonotonicList using (ML; Burst; Burst∞; ML∞; done; quiet; at; emit; stall; close; Time; Pos; tick; Events; Events∞;
  out; skip; hush; observe; root; ix; last)
open import denotation.Denote using (⟦_⟧[_])
open import operation.PureObservable using (PureObs; Pureᴾ; same; grow; _⊑_; _⨾_; wk∋; Sink; Handle; module Pure)
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
  open Pure R using (State; Res; res; shift; start; recorder; compileᴺ; runᴺ; loopᴺ; Timer; get; put; cascade; insert; M; then; ret; unlessSpent;
    module Callbacks; module Play)
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

  -- MID-FRAME: the root's record so far, and until the root completes, a
  -- configuration whose one firing cold, at sink `s` and handle `hd`, is
  -- at step `i` of the frame at `r`, the clock where its timeline,
  -- subscribed at `τ`, puts tick `t`.
  record Mid (n : ℕ) (o : PureObs [] R) {h} (st : State h) {B} (s : Sink h B) (hd : Handle h) (τ t : Time) (r : Pos) (i : ℕ) (b : Burst B) : Set₁ where
    constructor mid
    field
      {left} : Events R
      sofar  : Ends.Root R (shown n o) left st
      rest   : State.ended st ≡ false
             → Σ (Nodes.Node n [] R) λ c → Realizing.Playing R n c st s hd τ r i b × left ≅ Nodes.⟦_⟧ᶜ n c [] × State.clock st ≡ τ + t

  -- A step's result judged: cut anywhere, or `P` where it reached.
  Reach : ∀ n o {h A} → (∀ {v} → h ⊑ v → State v → A → Set₁) → Res h A → Set₁
  Reach n o P (res g st nothing)  = Ends.CutOk R (shown n o) st
  Reach n o P (res g st (just a)) = P g st a

  -- The cold's subscriber read closed: the turn stops, the configuration
  -- settled.  Read open: the frame plays on.
  Closed : ∀ n o {h} → Bool → State h → ∀ {B} → Sink h B → Handle h → Time → Time → Pos → ℕ → Burst B → Set₁
  Closed n o true  st s hd τ t r i b = Live n o st
  Closed n o false st s hd τ t r i b = Mid n o st s hd τ t r i b

  postulate
    -- Subscribing the program at the root, on any budget, leaves it live
    -- or cut.
    live-start : ∀ n (o : PureObs [] R) → Rising n o → ∀ N k
               → At.Post n o N (runᴺ N k (compileᴺ n o [] same recorder λ _ _ → done tt) same start)
    -- A spent cold settles, whatever step of its frame it stood at.
    mid-spent : ∀ n o {h} {st : State h} {B} {s : Sink h B} {hd τ t r i b} → Mid n o st s hd τ t r i b
              → lower (get (State.heap st) hd) ≡ true → Live n o st
    -- Asking a live cold's subscriber whether it is closed.
    closed-ok : ∀ n o N k {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i b}
              → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i b → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
              → Reach n o (λ g st′ c → Closed n o c st′ (wk∋ (σ ⨾ g) s) (wk∋ (σ ⨾ g) hd) τ t r i b)
                      (Play.runCb N (runᴺ N k) s Callbacks.isClosed σ st)
    -- An emit, sent from its own position, moves the cold a step on.
    --
    -- RECOVERY: `git show 016c16a2` restores a cold at the root proven
    --   against the engine: its subscribe burst, each timer's turn, and
    --   the record placed, frame by frame.
    send-ok : ∀ n o N k {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i a k′}
            → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i (emit a k′) → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
            → Reach n o (λ g st′ _ → Mid n o st′ (wk∋ (σ ⨾ g) s) (wk∋ (σ ⨾ g) hd) τ t r (suc i) (Burst∞.force k′))
                    (Play.sendᴾ N (runᴺ N k) s a σ (record st { pos = r ++ [ ix i ] }))
    -- A stall moves it a step on, sending nothing.
    stall-ok : ∀ n o {h} {st : State h} {B} {s : Sink h B} {hd τ t r i k′} → Mid n o st s hd τ t r i (stall k′)
             → Mid n o st s hd τ t r (suc i) (Burst∞.force k′)
    -- A frame closing on nothing more settles it.
    quiet-ok : ∀ n o {h} {st : State h} {B} {s : Sink h B} {hd τ t r i k′} → Mid n o st s hd τ t r i (close k′)
             → ML∞.force k′ ≡ quiet → Live n o st
    -- A frame closing on the completion: the cold spent, the completion
    -- sent from where the frame ends.
    finish-ok : ∀ n o N k {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i k′}
              → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i (close k′) → ML∞.force k′ ≡ done
              → lower (get (State.heap st) (wk∋ σ hd)) ≡ false
              → Reach n o (λ _ st′ _ → Live n o st′)
                      (Play.finishᴾ N (runᴺ N k) s σ (record st { heap = put (State.heap st) (wk∋ σ hd) (lift true) ; pos = r ++ [ last ] }))
    -- A frame closing on a later one sets its timer.  False for a cold
    -- whose ticks fall (`rising`): the timer is due at the clock, not at
    -- the tick the frame is pending for.
    timer-ok : ∀ n o {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i k′ t′ b′}
             → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i (close k′) → ML∞.force k′ ≡ at t′ b′
             → Live n o (record st { timers = insert (record { due = State.clock st + (t′ ∸ t) ; sink = wk∋ σ s ; handle = wk∋ σ hd
                                                            ; at′ = t′ ; from = r ++ [ last ] ; frame = b′ }) (State.timers st) })

  -- Popping a timer moves neither the record nor whether it is complete.
  moved : ∀ n o {h} {st : State h} {tm : Timer h} {ts} {r} → Ends.Root R (shown n o) r st
        → Ends.Root R (shown n o) r (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  moved n o (Ends.live e p) = Ends.live e p
  moved n o (Ends.over e p) = Ends.over e p

  -- Only the state and the value are judged, never the world's path.
  post-shift : ∀ n o N {h v} (ρ : h ⊑ v) (Y : Res v ⊤) → At.Post n o N Y → At.Post n o N (shift ρ Y)
  post-shift n o N ρ (res σ st b) q = q

  same-⨾ : ∀ {h v} (g : h ⊑ v) → same ⨾ g ≡ g
  same-⨾ same     = refl
  same-⨾ (grow g) = cong grow (same-⨾ g)

  reach-shift : ∀ n o {h A} {P : ∀ {v} → h ⊑ v → State v → A → Set₁} (Y : Res h A) → Reach n o P Y → Reach n o P (shift same Y)
  reach-shift n o (res g st nothing)  q = q
  reach-shift n o {P = P} (res g st (just a)) q = subst (λ x → P x st a) (sym (same-⨾ g)) q

  reach-post : ∀ n o N {h} (Y : Res h ⊤) → Reach n o (λ _ st′ _ → Live n o st′) Y → At.Post n o N Y
  reach-post n o N (res g st nothing)   q = q
  reach-post n o N (res g st (just tt)) q = q

  -- A step, run on into the rest of the frame.
  then-reach : ∀ n o N {w h A} (f : A → M w ⊤) (σ : w ⊑ h) (Y : Res h A) {P : ∀ {v} → h ⊑ v → State v → A → Set₁}
             → Reach n o P Y → (∀ {v} (g : h ⊑ v) (st′ : State v) a → P g st′ a → At.Post n o N (f a (σ ⨾ g) st′))
             → At.Post n o N (then (λ a τ → f a (σ ⨾ τ)) (shift same Y))
  then-reach n o N f σ (res g st nothing)  q k = q
  then-reach n o N f σ (res g st (just a)) q k rewrite same-⨾ g = post-shift n o N g (f a (σ ⨾ g) st) (k g st a q)

  -- A spent cold plays nothing more.
  spent-unless : ∀ n o N {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i b} (m : M w ⊤)
               → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i b → lower (get (State.heap st) (wk∋ σ hd)) ≡ true
               → At.Post n o N (unlessSpent hd m σ st)
  spent-unless n o N s hd σ st m q e rewrite e = mid-spent n o q e

  unless-false : ∀ n o N {w h} (hd : Handle w) (m : M w ⊤) (σ : w ⊑ h) (st : State h)
               → lower (get (State.heap st) (wk∋ σ hd)) ≡ false → At.Post n o N (m σ st) → At.Post n o N (unlessSpent hd m σ st)
  unless-false n o N hd m σ st e q rewrite e = post-shift n o N same (m σ st) q

  -- THE FRAME PLAYED, step by step as the engine plays it.
  mutual
    burst-ok : ∀ n o N k f {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i b}
             → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i b → At.Post n o N (Play.burst N (runᴺ N k) f s hd t r i b σ st)
    burst-ok n o N k zero    s hd σ st q = Ends.cutok (Mid.sofar q)
    burst-ok n o N k (suc f) s hd σ st {τ} {t} {r} {i} {b} q = by (lower (get (State.heap st) (wk∋ σ hd))) refl
      where
        after : ∀ {v} (g : _ ⊑ v) (st′ : State v) c → Closed n o c st′ (wk∋ (σ ⨾ g) s) (wk∋ (σ ⨾ g) hd) τ t r i b
              → At.Post n o N ((if c then ret tt else Play.stepᴾ N (runᴺ N k) f s hd t r i b) (σ ⨾ g) st′)
        after g st′ true  q′ = q′
        after g st′ false q′ = step-ok n o N k f s hd (σ ⨾ g) st′ q′
        by : ∀ x → lower (get (State.heap st) (wk∋ σ hd)) ≡ x → At.Post n o N (Play.burst N (runᴺ N k) (suc f) s hd t r i b σ st)
        by true  e rewrite e = mid-spent n o q e
        by false e rewrite e = then-reach n o N (λ c → if c then ret tt else Play.stepᴾ N (runᴺ N k) f s hd t r i b) σ
                                 (Play.runCb N (runᴺ N k) s Callbacks.isClosed σ st) (closed-ok n o N k s hd σ st q e) after

    step-ok : ∀ n o N k f {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i b}
            → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i b → At.Post n o N (Play.stepᴾ N (runᴺ N k) f s hd t r i b σ st)
    step-ok n o N k f s hd σ st {τ} {t} {r} {i} {emit a k′} q = by (lower (get (State.heap st) (wk∋ σ hd))) refl
      where
        by : ∀ x → lower (get (State.heap st) (wk∋ σ hd)) ≡ x → At.Post n o N (Play.stepᴾ N (runᴺ N k) f s hd t r i (emit a k′) σ st)
        by true  e rewrite e = post-shift n o N same (unlessSpent hd (Play.burst N (runᴺ N k) f s hd t r (suc i) (Burst∞.force k′)) σ st)
                                 (spent-unless n o N s hd σ st (Play.burst N (runᴺ N k) f s hd t r (suc i) (Burst∞.force k′)) q e)
        by false e rewrite e = then-reach n o N (λ _ → unlessSpent hd (Play.burst N (runᴺ N k) f s hd t r (suc i) (Burst∞.force k′))) σ
                                 (shift same (Play.sendᴾ N (runᴺ N k) s a σ (record st { pos = r ++ [ ix i ] })))
                                 (reach-shift n o (Play.sendᴾ N (runᴺ N k) s a σ (record st { pos = r ++ [ ix i ] })) (send-ok n o N k s hd σ st q e))
                                 λ g st′ _ q′ → unless-ok n o N k f s hd (σ ⨾ g) st′ q′
    step-ok n o N k f s hd σ st {b = stall k′} q = burst-ok n o N k f s hd σ st (stall-ok n o q)
    step-ok n o N k f s hd σ st {b = close k′} q = schedule-ok n o N k s hd σ st (ML∞.force k′) refl q

    unless-ok : ∀ n o N k f {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i b}
              → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i b
              → At.Post n o N (unlessSpent hd (Play.burst N (runᴺ N k) f s hd t r i b) σ st)
    unless-ok n o N k f s hd σ st {τ} {t} {r} {i} {b} q = by (lower (get (State.heap st) (wk∋ σ hd))) refl
      where
        by : ∀ x → lower (get (State.heap st) (wk∋ σ hd)) ≡ x
           → At.Post n o N (unlessSpent hd (Play.burst N (runᴺ N k) f s hd t r i b) σ st)
        by true  e = spent-unless n o N s hd σ st (Play.burst N (runᴺ N k) f s hd t r i b) q e
        by false e = unless-false n o N hd (Play.burst N (runᴺ N k) f s hd t r i b) σ st e (burst-ok n o N k f s hd σ st q)

    schedule-ok : ∀ n o N k {w h B} (s : Sink w B) (hd : Handle w) (σ : w ⊑ h) (st : State h) {τ t r i k′} (m : ML B)
                → ML∞.force k′ ≡ m → Mid n o st (wk∋ σ s) (wk∋ σ hd) τ t r i (close k′)
                → At.Post n o N (Play.schedule N (runᴺ N k) s hd t (r ++ [ last ]) m σ st)
    schedule-ok n o N k s hd σ st {τ} {t} {r} {i} done m q = by (lower (get (State.heap st) (wk∋ σ hd))) refl
      where
        by : ∀ x → lower (get (State.heap st) (wk∋ σ hd)) ≡ x
           → At.Post n o N (Play.schedule N (runᴺ N k) s hd t (r ++ [ last ]) done σ st)
        st₂ = record st { heap = put (State.heap st) (wk∋ σ hd) (lift true) }
        by true  e = spent-unless n o N s hd σ st (Pure.bind R (Pure.spend R hd) λ _ → Pure.bind R (Pure.gotoᴾ R (r ++ [ last ])) λ _ → Play.finishᴾ N (runᴺ N k) s) q e
        by false e = unless-false n o N hd (Pure.bind R (Pure.spend R hd) λ _ → Pure.bind R (Pure.gotoᴾ R (r ++ [ last ])) λ _ → Play.finishᴾ N (runᴺ N k) s) σ st e
          (post-shift n o N same (Pure.bind R (Pure.gotoᴾ R (r ++ [ last ])) (λ _ → Play.finishᴾ N (runᴺ N k) s) σ st₂)
            (post-shift n o N same (Play.finishᴾ N (runᴺ N k) s σ (record st₂ { pos = r ++ [ last ] }))
              (reach-post n o N (Play.finishᴾ N (runᴺ N k) s σ (record st₂ { pos = r ++ [ last ] })) (finish-ok n o N k s hd σ st q m e))))
    schedule-ok n o N k s hd σ st quiet    m q = quiet-ok n o q m
    schedule-ok n o N k s hd σ st (at t′ b′) m q = timer-ok n o s hd σ st q m

  -- A turn that fires a frame keeps it: the frame played from the
  -- configuration with its cold started, or from a run already complete.
  live-fire : ∀ n o N k {h} (st : State h) {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts
            → lower (get (State.heap st) (Timer.handle tm)) ≡ false → At.Post n o N (At.turn n o N k st tm ts)
  live-fire n o N k st {tm} {ts} (config sofar rest) eq s rewrite s =
    post-shift n o N same (Play.burst N (runᴺ N k) N (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same st′)
      (by (State.ended st) refl)
    where
      st′ = record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }
      by : ∀ x → State.ended st ≡ x
         → At.Post n o N (Play.burst N (runᴺ N k) N (Timer.sink tm) (Timer.handle tm) (Timer.at′ tm) (cascade tm) 0 (Timer.frame tm) same st′)
      by true e = burst-ok n o N k N (Timer.sink tm) (Timer.handle tm) same st′ {τ = 0}
        (mid (moved n o {tm = tm} {ts} sofar) λ f → Realizing.absurd R n (trans (sym e) f))
      by false e with rest e
      ... | c , z , b with Realizing.firing-start R n (Realizing.Realizes.holding z) eq s
      ... | p , z′ , teq with Realizing.fire-spot R n (Realizing.Holding.tree (Realizing.Realizes.holding z)) p
      ... | τ , d , sp , feq = burst-ok n o N k N (Timer.sink tm) (Timer.handle tm) same st′ {τ = τ}
        (mid (moved n o {tm = tm} {ts} sofar) λ _ → c , Realizing.playing _ (Realizing.Realizes.calm z) sp z′ (trans teq feq) , b , d)

  -- A spent timer's turn keeps it: nothing is played.
  live-spent : ∀ n o {h} {st : State h} {tm ts} → Live n o st → State.timers st ≡ tm ∷ ts
             → lower (get (State.heap st) (Timer.handle tm)) ≡ true
             → Live n o (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm })
  live-spent n o {st = st} {tm} {ts} (config sofar rest) eq s = config (moved n o {tm = tm} {ts} sofar) λ e →
    proj₁ (rest e) , Realizing.realizes-spent R n (proj₁ (proj₂ (rest e))) eq s , proj₂ (proj₂ (rest e))

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
