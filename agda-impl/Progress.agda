{-# OPTIONS --guardedness #-}

-- THE UPPER HALF'S BUDGET, READ OFF THE MEANING.  Reaching k items of
-- what the root is shown, `denotation.Unfold` passes finitely many
-- configurations; the run needs no more fuel than their events and their
-- depth.  Each loop turn fires a frame some event set going, each burst
-- step is an event, and each callback hop is a node of the configuration
-- it runs through, or one an earlier event put there.
module Progress where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.List.Properties using (length-++)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; ≤-pred; m≤m+n; m≤n+m; m≤m⊔n; +-suc)
open import Data.Unit using (⊤; tt)
open import Level using (Lift; lift; lower)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import denotation.MonotonicList using (root; Events)
open import denotation.Unfold using (Node; Step; framesᶜ; burstᶜ; endᶜ; ofᶜ; mapᶜ; scanᶜ; takeWhileᶜ; flatMapᶜ; joinᶜ; deferᶜ;
  outˢ; skipˢ; endˢ; hushˢ; step; shown; unfold; subscribe)
open import operation.Placed using (Ahead; none; outᵃ; skipᵃ; endᵃ; hushᵃ; items; module Ran)
open import operation.PureObservable using (PureObs; Pureᴾ; same; _⊑_; _⨾_; module Pure)
open import operation.AbstractObservable using (module Run)
open import operation.Budget using (module Approx)
open import Config using (_≅_; ⟦_⟧ᶜ; copy) renaming (Node to Conf)
open import Realize using (module Realizing)
open import Bound using (module Places; module Ends; module Loop)

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

-- Every configuration nests at least one deep.
depth-pos : ∀ {A} (c : Node A) → 1 ≤ depth c
depth-pos (framesᶜ τ e m)         = s≤s z≤n
depth-pos (burstᶜ τ r i b)        = s≤s z≤n
depth-pos (endᶜ p)                = s≤s z≤n
depth-pos (ofᶜ p i xs)            = s≤s z≤n
depth-pos (mapᶜ f c)              = s≤s z≤n
depth-pos (scanᶜ f z c)           = s≤s z≤n
depth-pos (takeWhileᶜ i p c)      = s≤s z≤n
depth-pos (flatMapᶜ op g o ls qs) = s≤s z≤n
depth-pos (joinᶜ p i c)           = s≤s z≤n
depth-pos (deferᶜ l ρ p)          = s≤s z≤n

-- So no budget is spent.
budget-pos : ∀ {A k} (c : Node A) (a : Ahead (unfold c) k) → 1 ≤ budget c a
budget-pos c a = ≤-trans (depth-pos c) (≤-trans (m≤m⊔n (depth c) (deepestˢ (step c) a)) (m≤n+m (deepest c a) (2 * events a)))

------------------------------------------------------------------------
-- THE LOOP, OWING: the run still owes the items the target asks for, and
-- the turns left pay for them.

module Owing (R : Set) (o : PureObs [] R) (N : ℕ) {k : ℕ} (a : Ahead (unfold (subscribe o [] root)) k) where
  open Pure R using (State; Res; res; M; Timer; get; cascade; then; ret; loopᴺ; runᴺ; compileᴺ; recorder; start; endOf; cutOff)
  open Places R using (Live; moved) renaming (shown to root-shown)
  open Loop R (root-shown o) N (Live N o) using (turn)
  open Approx R using (Grows; GrowsAt; open≈; shut≈; loopᴺ-grow; module Grower)
  open Run (Pureᴾ R) using (done)

  -- The record, cut where it stands, already shows k items.
  Got : ∀ {h} → State h → Set
  Got st = k ≤ length (items (State.log st) (endOf (State.ended st) nothing (State.clock st)))

  -- The run's whole record shows k items.
  Final : ∀ {h} → Res h ⊤ → Set
  Final x = k ≤ length (items (State.log (Res.state x)) (endOf (State.ended (Res.state x)) (Res.value x) (State.clock (Res.state x))))

  items-len : ∀ xs en → length xs ≤ length (items {A = R} xs en)
  items-len []       en = z≤n
  items-len (x ∷ xs) en = s≤s (items-len xs en)

  items-cut : ∀ xs c → length (items {A = R} xs (cutOff c)) ≡ length xs
  items-cut []       c = refl
  items-cut (x ∷ xs) c = cong suc (items-cut xs c)

  -- A record that grew, however it ends, shows what it showed cut.
  got-at : ∀ {e ms xs e′ ns ys} → GrowsAt e ms xs e′ ns ys → ∀ c c′ v
         → k ≤ length (items xs (endOf e nothing c)) → k ≤ length (items ys (endOf e′ v c′))
  got-at shut≈ c c′ v g = g
  got-at {xs = xs} (open≈ ps zs refl refl l) c c′ v g =
    ≤-trans g (≤-trans (≤-reflexive (items-cut xs c)) (≤-trans (≤-trans (m≤m+n (length xs) (length zs)) (≤-reflexive (sym (length-++ xs))))
                                                                (items-len (xs ++ zs) _)))

  final-got : ∀ {h} {st : State h} (x : Res h ⊤) → Grows st (Res.state x) → Got st → Final x
  final-got x g q = got-at g _ _ (Res.value x) q

  -- THE CONFIGURATION, PAID FOR: until the root completes, a tree the
  -- state realizes, what is left of the root's events its meaning, the
  -- items still owed ahead in it, and their budget, with a turn for each
  -- timer set, within the turns left.
  record Owing {h} (st : State h) (m : ℕ) : Set₁ where
    field
      {left}  : Events R
      sofar   : Ends.Root R (root-shown o) left st
      unended : State.ended st ≡ false
      conf    : Conf [] R
      real    : Realizing.Realizes R N conf st
      agree   : left ≅ ⟦ conf ⟧ᶜ []
      {owe}   : ℕ
      ahead   : Ahead (⟦ conf ⟧ᶜ []) owe
      owed    : k ≤ length (State.log st) + owe
      paid    : budget (copy conf []) ahead + length (State.timers st) ≤ m

  -- Owing nothing, no turn is left over.
  owing-zero : ∀ {h} {st : State h} → Owing st 0 → ⊥
  owing-zero w = no (≤-trans (budget-pos (copy (Owing.conf w) []) (Owing.ahead w)) (≤-trans (m≤m+n _ _) (Owing.paid w)))
    where
      no : 1 ≤ 0 → ⊥
      no ()

  data Owes {h} (st : State h) (m : ℕ) : Set₁ where
    got   : Got st → Owes st m
    owing : Owing st m → Owes st m

  -- A step's result: cut where the record already shows k items, or owing.
  OwesV : ∀ {h} → State h → Maybe ⊤ → ℕ → Set₁
  OwesV st nothing  m = Lift _ (Got st)
  OwesV st (just _) m = Owes st m

  OwePost : ∀ {h} → Res h ⊤ → ℕ → Set₁
  OwePost x = OwesV (Res.state x) (Res.value x)

  postulate
    -- Subscribing the program at the root, within its budget, leaves it
    -- owing at most that budget.
    owe-start : budget (subscribe o [] root) a ≤ N → OwePost (runᴺ N N (compileᴺ N o [] same recorder λ _ _ → done tt) same start) N
    -- A turn that fires a frame spends a turn's worth of what is owed.
    --
    -- False wherever a `connect` source the body outlives stands between
    -- the root and an event the meaning shows, and so is `owe-start`.
    -- The meaning steps a source only as its joiners copy it, so a body
    -- that never joins shows past it; the engine runs the source inline,
    -- and a source that spins stops the whole run there — as rxjs does,
    -- by overflowing — while one that runs forever keeps the engine
    -- firing its timers, so the silence the meaning shows after the body
    -- is never reported.  The meaning keeping such a source's events, or
    -- `adequacy` assuming none, is Anthony's call.
    -- DEAD ROUTE: a logical relation per operator, by induction over
    --   the tree's approximants, each kernel against its own timeline.  A
    --   connect's subject is state its siblings share, which no relation
    --   on one kernel at a time can carry.
    owe-fire  : ∀ m {h} (st : State h) {tm ts} → Owing st (suc m) → State.timers st ≡ tm ∷ ts
              → lower (get (State.heap st) (Timer.handle tm)) ≡ false → OwePost (turn (suc m) st tm ts) m
    -- With no timer left, the items owed are the silence the meaning ends in.
    owe-dry   : ∀ m {h} (st : State h) → Owing st m → State.timers st ≡ []
              → k ≤ length (items (State.log st) (endOf (State.ended st) (just tt) (State.clock st)))

  -- A spent timer's turn plays nothing: the turn it spends is its own.
  owing-spent : ∀ m {h} {st : State h} {tm ts} → Owing st (suc m) → State.timers st ≡ tm ∷ ts
              → lower (get (State.heap st) (Timer.handle tm)) ≡ true
              → Owing (record st { clock = Timer.due tm ; timers = ts ; pos = cascade tm }) m
  owing-spent m {st = st} {tm} {ts} w eq s = record
    { sofar   = moved o {tm = tm} {ts} (Owing.sofar w)
    ; unended = Owing.unended w
    ; conf    = Owing.conf w
    ; real    = Realizing.realizes-spent R N (Owing.real w) eq s
    ; agree   = Owing.agree w
    ; ahead   = Owing.ahead w
    ; owed    = Owing.owed w
    ; paid    = ≤-pred (≤-trans (≤-reflexive (sym (+-suc (budget (copy (Owing.conf w) []) (Owing.ahead w)) (length ts))))
                                (subst (λ l → budget (copy (Owing.conf w) []) (Owing.ahead w) + length l ≤ suc m) eq (Owing.paid w))) }

  -- One turn spends a turn's worth of what is owed.
  owe-turn : ∀ m {h} (st : State h) {tm ts} → Owing st (suc m) → State.timers st ≡ tm ∷ ts → OwePost (turn (suc m) st tm ts) m
  owe-turn m st {tm} {ts} w eq = by (lower (get (State.heap st) (Timer.handle tm))) refl
    where
      by : ∀ b → lower (get (State.heap st) (Timer.handle tm)) ≡ b → OwePost (turn (suc m) st tm ts) m
      by true  s rewrite s = owing (owing-spent m w eq s)
      by false s           = owe-fire m st w eq s

  again : ℕ → Bool → M [] ⊤
  again m b = if_then_else_ {A = M [] ⊤} b (loopᴺ N m) (ret tt)

  -- THE LOOP, turn by turn.
  mutual
    loop-owes : ∀ m {h} (σ : [] ⊑ h) (st : State h) → Owes st m → Final (loopᴺ N m σ st)
    loop-owes m       σ st (got q)   = final-got {st = st} (loopᴺ N m σ st) (Grower.grow (loopᴺ-grow N m) σ st) q
    loop-owes zero    σ st (owing w) = ⊥-elim (owing-zero w)
    loop-owes (suc m) σ st (owing w) with State.timers st in eq
    ... | []      = owe-dry (suc m) st w eq
    ... | tm ∷ ts = loop-tail m σ (turn (suc m) st tm ts) (owe-turn m st w eq)

    loop-tail : ∀ m {h} (σ : [] ⊑ h) (Y : Res h ⊤) → OwePost Y m
              → Final (then (λ b τ → again m b (σ ⨾ τ)) (then (λ _ _ st′ → res same st′ (just true)) Y))
    loop-tail m σ (res g st nothing)   (lift q) = q
    loop-tail m σ (res g st (just tt)) q        = loop-owes m (σ ⨾ g) st q

  -- From the subscription on.
  runs : budget (subscribe o [] root) a ≤ N
       → Final (then (λ _ τ → loopᴺ N N (same ⨾ τ)) (runᴺ N N (compileᴺ N o [] same recorder λ _ _ → done tt) same start))
  runs le = by (runᴺ N N (compileᴺ N o [] same recorder λ _ _ → done tt) same start) (owe-start le)
    where
      by : (Y : Res [] ⊤) → OwePost Y N → Final (then (λ _ τ → loopᴺ N N (same ⨾ τ)) Y)
      by (res g st nothing)   (lift q) = q
      by (res g st (just tt)) q        = loop-owes N (same ⨾ g) st q

module Gets (R : Set) where
  open Pure R using (compileᴺ)
  open Ran R using (ran; itemsOf)

  -- THE RUN GETS AS FAR, AT THE BUDGET: wherever the meaning's events
  -- reach, any approximant past their budget records as many items.
  gets : (o : PureObs [] R) → ∀ {k} (a : Ahead (unfold (subscribe o [] root)) k) n → budget (subscribe o [] root) a ≤ n
       → k ≤ length (itemsOf (ran n (compileᴺ n o [])))
  gets o a n le = Owing.runs R o n a le
