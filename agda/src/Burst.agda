-- BURST BATCHING over the canonical primitive grammar: one subscribe()
-- call is one root cause, so the entire synchronous subscription frame is
-- ONE instant.
--
-- The grammar is exactly the system's primitives —
--   of, empty, map, take, share, scan, mergeAll, concatAll, switchAll,
--   exhaustAll
-- — two-sorted, because the *All joins consume streams OF streams: Exp
-- denotes a stream of values, ExpS a stream of inner streams (ofS = a sync
-- burst of inners, mapS = one inner per trigger value). merge, concat and
-- mergeMap are one-line derived forms, not constructors.
--
-- The technical device is the subscription-time-parameterized denotation:
-- ⟦ e ⟧ env t is the observable obtained by subscribing e at time t, and an
-- inner stream denotes a FUNCTION from subscription time to observable
-- (Inner) — a cold stream is literally "tell me when you subscribe me".
-- Cold values (`of`) emit at the subscription time they are handed; a join
-- hands each inner its own subscription time (arrival, or the previous
-- close for the serial joins). Two consequences fall out by construction:
--   • static (share-free) programs land entirely at the subscription
--     instant — ONE batch (frame-batch);
--   • an inner spawned by an async event is subscribed AT that event's
--     time, so its synchronous output batches with its cause, transitively
--     (Phase-A causation; cascade-example).
--
-- share: an environment slot is a hot stream PLUS the instant it
-- connected. shareE first? i reads slot i; a ref subscribed strictly after
-- the connection sees only the strict suffix (hot semantics: a subject
-- does not replay), and the CONNECTING ref — flagged true, the pre-order-
-- first static ref, exactly the TS model's shareRef.first — additionally
-- receives the connection frame itself (rxjs: the first subscriber
-- triggers connect and the source emits synchronously into it). Root
-- subjects are free slots, referenced with the flag false (a subject has
-- no subscription-frame values to replay). letShareE src body BINDS slot 0
-- (de Bruijn: shareE _ 0 in the body is the bound share, shareE _ (suc i)
-- reaches outward) to src subscribed at the letShare's own subscription
-- time — the slot's content is DERIVED, not hypothesized. Ratified spec
-- decisions carried over from the TS model (oracle-validated): the share
-- connects at the subscription frame and lives exactly once per letShare
-- scope (no refcount reset mid-lifetime); connection time is provably
-- irrelevant for hot bindings (filterAfter-absorb), which is why
-- connecting at the binder rather than literally at the first ref is
-- faithful.
--
-- INTRA-BATCH ORDER (ratified, matching rxjs): a batch delivers in the
-- implementation's delivery order — a share's subject fires its refs
-- consecutively as ONE block in registration order (static refs in
-- pre-order, spawned refs in trigger order) at the connecting ref's
-- position; a cascade delivers inside the chain of the ref that triggered
-- it; scan folds in this order. ⟦_⟧ produces exactly this order for trees
-- whose same-slot ref arms appear in registration order (every theorem
-- below is order-EXACT, not up-to-order). For non-canonical trees (a
-- spawn arm written left of a static arm of the same share) the flat
-- merge order diverges from the block rule; the rank-tagged delivery
-- model that decides those trees belongs to the counting tower, where
-- delivery order is derived from the implementation's own mechanism.
--
-- NODE REUSE (resolved): cold origins are gone from this spec — ⟦ e ⟧ env
-- t is a pure function of the tree, the environment and the subscription
-- time, so subscribing one node twice IS subscribing two copies; cold
-- sharing is semantically inert, and hot sharing is exactly letShareE.
-- (The TS transcription must assert the same law: a memoized interpret
-- may not behave differently from interpreting a copy.)
module Burst where

open import Prelude
open import Time
open import TimedObs
open import Sorting
open import Obs
open import Diamond
open import BatchImpl

Val : Set
Val = ℕ

-- a cold inner stream: subscription time → observable
Inner : Set
Inner = Time → Obs Val

-- an environment assigns every share slot its connection instant and its
-- connected emission history
Slot : Set
Slot = Time × Obs Val

Env : Set
Env = ℕ → Slot

extendEnv : Slot → Env → Env
extendEnv s env zero    = s
extendEnv s env (suc i) = env i

data Exp : Set
data ExpS : Set

data Exp where
  emptyE      : Exp
  ofE         : List Val → Exp
  -- shareE first? i: a subscription of hot slot i; the flag marks the
  -- CONNECTING ref (the pre-order-first static ref of its letShare binder)
  shareE      : Bool → ℕ → Exp
  letShareE   : Exp → Exp → Exp
  mapE        : (Val → Val) → Exp → Exp
  takeE       : ℕ → Exp → Exp
  scanE       : (Val → Val → Val) → Val → Exp → Exp
  mergeAllE   : ExpS → Exp
  concatAllE  : ExpS → Exp
  switchAllE  : ExpS → Exp
  exhaustAllE : ExpS → Exp

data ExpS where
  ofS  : List Exp → ExpS
  mapS : (Val → Exp) → Exp → ExpS

-- the familiar combinators, as the derived forms they really are
mergeE : Exp → Exp → Exp
mergeE a b = mergeAllE (ofS (a ∷ b ∷ []))

concatE : Exp → Exp → Exp
concatE a b = concatAllE (ofS (a ∷ b ∷ []))

mergeMapE : (Val → Exp) → Exp → Exp
mergeMapE f e = mergeAllE (mapS f e)

-- list machinery for the denotation ---------------------------------------------

-- scan: times preserved, values folded
scanT : {A B : Set} → (B → A → B) → B → TimedObs A → TimedObs B
scanT f z []             = []
scanT f z ((u , v) ∷ xs) = (u , f z v) ∷ scanT f (f z v) xs

-- the close of `take n` when the subscription happened at t: the time of
-- the nth emission if it exists, the source's close if it has fewer, and
-- the subscription instant itself for take 0 (which completes immediately)
takeCloseB : {A : Set} → Time → ℕ → TimedObs A → Time → Time
takeCloseB t zero          _               _ = t
takeCloseB t (suc n)       []              c = c
takeCloseB t (suc zero)    ((t′ , _) ∷ _)  _ = t′
takeCloseB t (suc (suc n)) (_ ∷ xs)        c = takeCloseB t (suc n) xs c

-- mergeAll: subscribe every inner at its arrival, merge everything
mergeAllT : TimedObs Inner → TimedObs Val
mergeAllT []             = []
mergeAllT ((a , d) ∷ os) = mergeT (emits (d a)) (mergeAllT os)

maxCloses : Time → TimedObs Inner → Time
maxCloses c []             = c
maxCloses c ((a , d) ∷ os) = maxCloses (timeMax c (close (d a))) os

-- concatAll: subscribe each inner once the previous has closed (or at its
-- arrival, whichever is later — a queued inner starts at the previous close)
concatAllT : Time → TimedObs Inner → TimedObs Val
concatAllT r []             = []
concatAllT r ((a , d) ∷ os) =
  emits (d (timeMax r a)) ++ concatAllT (close (d (timeMax r a))) os

concatAllClose : Time → TimedObs Inner → Time
concatAllClose r []             = r
concatAllClose r ((a , d) ∷ os) = concatAllClose (close (d (timeMax r a))) os

-- switchAll: an inner keeps its own subscription frame (a sync inner runs to
-- completion before the next arrival is processed) but its async tail is cut
-- when the next inner arrives
cutAt : Time → Time → TimedObs Val → TimedObs Val
cutAt a nxt []             = []
cutAt a nxt ((u , v) ∷ xs) =
  if timeEq u a ∨ timeLt u nxt
  then ((u , v) ∷ cutAt a nxt xs)
  else cutAt a nxt xs

switchAllT : TimedObs Inner → TimedObs Val
switchAllT []                          = []
switchAllT ((a , d) ∷ [])              = emits (d a)
switchAllT ((a , d) ∷ (a′ , d′) ∷ os)  =
  cutAt a a′ (emits (d a)) ++ switchAllT ((a′ , d′) ∷ os)

lastClose : Time → TimedObs Inner → Time
lastClose c []                 = c
lastClose c ((a , d) ∷ [])     = close (d a)
lastClose c ((a , d) ∷ x ∷ os) = lastClose c (x ∷ os)

-- exhaustAll: an arrival is dropped only while the previous accepted inner
-- is still open (an of-then-of burst emits both — sync inners close
-- immediately, so the next arrival is not "during" them)
exhaustAllT : Time → TimedObs Inner → TimedObs Val
exhaustAllT b []             = []
exhaustAllT b ((a , d) ∷ os) =
  if timeLt a b
  then exhaustAllT b os
  else (emits (d a) ++ exhaustAllT (close (d a)) os)

exhaustClose : Time → TimedObs Inner → Time
exhaustClose b []             = b
exhaustClose b ((a , d) ∷ os) =
  if timeLt a b
  then exhaustClose b os
  else exhaustClose (close (d a)) os

-- what a ref subscribed at t sees of a share connected at tc: the whole
-- connected history for the connecting ref subscribed at the connection
-- instant, the strict suffix otherwise
refView : Bool → Time → Time → TimedObs Val → TimedObs Val
refView false t tc xs = filterAfter t xs
refView true  t tc xs = if timeEq t tc then xs else filterAfter t xs

-- the denotation -----------------------------------------------------------------

⟦_⟧  : Exp → Env → Time → Obs Val
⟦_⟧S : ExpS → Env → Time → Obs Inner
denoteList : List Exp → Env → Time → TimedObs Inner
denoteFun  : (Val → Exp) → Env → TimedObs Val → TimedObs Inner

⟦ emptyE ⟧ env t = obs [] t
⟦ ofE vs ⟧ env t = obs (map (λ v → (t , v)) vs) t
⟦ shareE b i ⟧ env t =
  obs (refView b t (fst (env i)) (emits (snd (env i))))
      (timeMax t (close (snd (env i))))
⟦ letShareE src body ⟧ env t =
  ⟦ body ⟧ (extendEnv (t , ⟦ src ⟧ env t) env) t
⟦ mapE f e ⟧ env t =
  obs (mapT f (emits (⟦ e ⟧ env t))) (close (⟦ e ⟧ env t))
⟦ takeE n e ⟧ env t =
  obs (takeT n (emits (⟦ e ⟧ env t)))
      (takeCloseB t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)))
⟦ scanE f z e ⟧ env t =
  obs (scanT f z (emits (⟦ e ⟧ env t))) (close (⟦ e ⟧ env t))
⟦ mergeAllE s ⟧ env t =
  obs (mergeAllT (emits (⟦ s ⟧S env t)))
      (maxCloses (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t)))
⟦ concatAllE s ⟧ env t =
  obs (concatAllT t (emits (⟦ s ⟧S env t)))
      (timeMax (close (⟦ s ⟧S env t)) (concatAllClose t (emits (⟦ s ⟧S env t))))
⟦ switchAllE s ⟧ env t =
  obs (switchAllT (emits (⟦ s ⟧S env t)))
      (timeMax (close (⟦ s ⟧S env t))
               (lastClose (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t))))
⟦ exhaustAllE s ⟧ env t =
  obs (exhaustAllT t (emits (⟦ s ⟧S env t)))
      (timeMax (close (⟦ s ⟧S env t)) (exhaustClose t (emits (⟦ s ⟧S env t))))

⟦ ofS es ⟧S env t = obs (denoteList es env t) t
⟦ mapS f e ⟧S env t =
  obs (denoteFun f env (emits (⟦ e ⟧ env t))) (close (⟦ e ⟧ env t))

denoteList []       env t = []
denoteList (e ∷ es) env t = (t , ⟦ e ⟧ env) ∷ denoteList es env t

denoteFun f env []             = []
denoteFun f env ((a , v) ∷ xs) = (a , ⟦ f v ⟧ env) ∷ denoteFun f env xs

-- well-formedness ------------------------------------------------------------------

-- relative to a subscription time: emissions start no earlier than the
-- subscription, the close is no earlier than the subscription, and
-- emissions happen before the close
record WFAt {A : Set} (t : Time) (o : Obs A) : Set where
  constructor wfAt
  field
    sortedAt  : SortedFrom t (emits o)
    closeAt   : timeLeq t (close o) ≡ true
    boundedAt : BoundedBy (close o) (emits o)
open WFAt public

WFDen : Inner → Set
WFDen d = (u : Time) → WFAt u (d u)

-- every slot's history is well-formed relative to its connection instant
EnvWF : Env → Set
EnvWF env = (i : ℕ) → WFAt (fst (env i)) (snd (env i))

extendEnv-wf : (t : Time) (o : Obs Val) (env : Env)
  → EnvWF env → WFAt t o → EnvWF (extendEnv (t , o) env)
extendEnv-wf t o env wfe w zero    = w
extendEnv-wf t o env wfe w (suc i) = wfe i

-- a predicate on every carried value of a timed list (the inners of a
-- stream of streams)
data AllVals {A : Set} (P : A → Set) : TimedObs A → Set where
  av[] : AllVals P []
  av∷  : {u : Time} {d : A} {xs : TimedObs A}
       → P d → AllVals P xs → AllVals P ((u , d) ∷ xs)

-- scan and take preserve well-formedness -------------------------------------------

scanT-sortedFrom : {A B : Set} {b : Time} (f : B → A → B) (z : B)
  (xs : TimedObs A) → SortedFrom b xs → SortedFrom b (scanT f z xs)
scanT-sortedFrom f z []             sf[]       = sf[]
scanT-sortedFrom f z ((u , v) ∷ xs) (sf∷ le s) =
  sf∷ le (scanT-sortedFrom f (f z v) xs s)

scanT-bounded : {A B : Set} {c : Time} (f : B → A → B) (z : B)
  (xs : TimedObs A) → BoundedBy c xs → BoundedBy c (scanT f z xs)
scanT-bounded f z []             bb[]       = bb[]
scanT-bounded f z ((u , v) ∷ xs) (bb∷ le b) =
  bb∷ le (scanT-bounded f (f z v) xs b)

head-leq-takeCloseB : {A : Set} (t₀ : Time) (n : ℕ) (xs : TimedObs A)
  (c t : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseB t₀ (suc n) xs c) ≡ true
head-leq-takeCloseB t₀ n       []              c t _          _           tc = tc
head-leq-takeCloseB t₀ zero    ((t′ , v) ∷ xs) c t (sf∷ le _) _           _  = le
head-leq-takeCloseB t₀ (suc n) ((t′ , v) ∷ xs) c t (sf∷ le s) (bb∷ lc bx) _  =
  timeLeq-trans t t′ _ le (head-leq-takeCloseB t₀ n xs c t′ s bx lc)

takeB-closeAt : {A : Set} (t : Time) (n : ℕ) (xs : TimedObs A) (c : Time)
  → SortedFrom t xs → BoundedBy c xs → timeLeq t c ≡ true
  → timeLeq t (takeCloseB t n xs c) ≡ true
takeB-closeAt t zero    xs c _ _ _  = timeLeq-refl t
takeB-closeAt t (suc n) xs c s b tc = head-leq-takeCloseB t n xs c t s b tc

take-boundedB : {A : Set} (t₀ : Time) {b : Time} (n : ℕ) (xs : TimedObs A)
  (c : Time)
  → SortedFrom b xs → BoundedBy c xs
  → BoundedBy (takeCloseB t₀ n xs c) (takeT n xs)
take-boundedB t₀ zero          xs             c _          _           = bb[]
take-boundedB t₀ (suc n)       []             c _          _           = bb[]
take-boundedB t₀ (suc zero)    ((t , v) ∷ xs) c _          _           =
  bb∷ (timeLeq-refl t) bb[]
take-boundedB t₀ (suc (suc n)) ((t , v) ∷ xs) c (sf∷ le s) (bb∷ tc bx) =
  bb∷ (head-leq-takeCloseB t₀ n xs c t s bx tc)
      (take-boundedB t₀ (suc n) xs c s bx)

-- the joins preserve well-formedness ------------------------------------------------

maxCloses-lb : (c : Time) (os : TimedObs Inner)
  → timeLeq c (maxCloses c os) ≡ true
maxCloses-lb c []             = timeLeq-refl c
maxCloses-lb c ((a , d) ∷ os) =
  timeLeq-trans c (timeMax c (close (d a))) _
    (timeMax-left c (close (d a)))
    (maxCloses-lb (timeMax c (close (d a))) os)

mergeAll-sorted : {t : Time} (os : TimedObs Inner)
  → SortedFrom t os → AllVals WFDen os → SortedFrom t (mergeAllT os)
mergeAll-sorted []             sf[]       av[]       = sf[]
mergeAll-sorted ((a , d) ∷ os) (sf∷ le s) (av∷ p ps) =
  merge-sortedFrom _ _
    (sortedFrom-weaken le (sortedAt (p a)))
    (mergeAll-sorted os (sortedFrom-weaken le s) ps)

mergeAll-bounded : (c : Time) (os : TimedObs Inner)
  → AllVals WFDen os → BoundedBy (maxCloses c os) (mergeAllT os)
mergeAll-bounded c []             av[]       = bb[]
mergeAll-bounded c ((a , d) ∷ os) (av∷ p ps) =
  merge-bounded _ _
    (boundedBy-weaken
      (timeLeq-trans (close (d a)) (timeMax c (close (d a))) _
        (timeMax-right c (close (d a)))
        (maxCloses-lb (timeMax c (close (d a))) os))
      (boundedAt (p a)))
    (mergeAll-bounded (timeMax c (close (d a))) os ps)

concatAllClose-lb : (r : Time) (os : TimedObs Inner)
  → AllVals WFDen os → timeLeq r (concatAllClose r os) ≡ true
concatAllClose-lb r []             av[]       = timeLeq-refl r
concatAllClose-lb r ((a , d) ∷ os) (av∷ p ps) =
  timeLeq-trans r (close (d (timeMax r a))) _
    (timeLeq-trans r (timeMax r a) _
      (timeMax-left r a) (closeAt (p (timeMax r a))))
    (concatAllClose-lb (close (d (timeMax r a))) os ps)

concatAll-sorted : (r : Time) (os : TimedObs Inner)
  → AllVals WFDen os → SortedFrom r (concatAllT r os)
concatAll-sorted r []             av[]       = sf[]
concatAll-sorted r ((a , d) ∷ os) (av∷ p ps) =
  append-sortedFrom _ _
    (sortedFrom-weaken (timeMax-left r a) (sortedAt (p (timeMax r a))))
    (boundedAt (p (timeMax r a)))
    (concatAll-sorted (close (d (timeMax r a))) os ps)
    (timeLeq-trans r (timeMax r a) _
      (timeMax-left r a) (closeAt (p (timeMax r a))))

concatAll-bounded : (r : Time) (os : TimedObs Inner)
  → AllVals WFDen os → BoundedBy (concatAllClose r os) (concatAllT r os)
concatAll-bounded r []             av[]       = bb[]
concatAll-bounded r ((a , d) ∷ os) (av∷ p ps) =
  append-bounded _ _
    (boundedBy-weaken (concatAllClose-lb (close (d (timeMax r a))) os ps)
      (boundedAt (p (timeMax r a))))
    (concatAll-bounded (close (d (timeMax r a))) os ps)

cutAt-sortedFrom : {b : Time} (a nxt : Time) (xs : TimedObs Val)
  → SortedFrom b xs → SortedFrom b (cutAt a nxt xs)
cutAt-sortedFrom a nxt []             sf[]       = sf[]
cutAt-sortedFrom a nxt ((u , v) ∷ xs) (sf∷ le s) with timeEq u a ∨ timeLt u nxt
... | true  = sf∷ le (cutAt-sortedFrom a nxt xs s)
... | false = cutAt-sortedFrom a nxt xs (sortedFrom-weaken le s)

cutAt-bounded-next : (a nxt : Time) (xs : TimedObs Val)
  → timeLeq a nxt ≡ true → BoundedBy nxt (cutAt a nxt xs)
cutAt-bounded-next a nxt []             an = bb[]
cutAt-bounded-next a nxt ((u , v) ∷ xs) an
  with timeEq u a ∨ timeLt u nxt in k
... | false = cutAt-bounded-next a nxt xs an
... | true with ∨-split (timeEq u a) (timeLt u nxt) k
...   | left  eq rewrite timeEq-sound u a eq =
        bb∷ an (cutAt-bounded-next a nxt xs an)
...   | right lt = bb∷ (timeLt⇒timeLeq u nxt lt) (cutAt-bounded-next a nxt xs an)

switchAll-sorted : {t : Time} (os : TimedObs Inner)
  → SortedFrom t os → AllVals WFDen os → SortedFrom t (switchAllT os)
switchAll-sorted []             sf[]       av[]       = sf[]
switchAll-sorted ((a , d) ∷ []) (sf∷ le _) (av∷ p _)  =
  sortedFrom-weaken le (sortedAt (p a))
switchAll-sorted {t} ((a , d) ∷ (a′ , d′) ∷ os)
                 (sf∷ le (sf∷ le′ s′)) (av∷ p ps) =
  append-sortedFrom (cutAt a a′ (emits (d a))) (switchAllT ((a′ , d′) ∷ os))
    (cutAt-sortedFrom a a′ (emits (d a))
      (sortedFrom-weaken le (sortedAt (p a))))
    (cutAt-bounded-next a a′ (emits (d a)) le′)
    (switchAll-sorted ((a′ , d′) ∷ os) (sf∷ (timeLeq-refl a′) s′) ps)
    (timeLeq-trans t a a′ le le′)

switchAll-bounded : {t : Time} (cS : Time) (os : TimedObs Inner)
  → SortedFrom t os → BoundedBy cS os → AllVals WFDen os
  → BoundedBy (timeMax cS (lastClose cS os)) (switchAllT os)
switchAll-bounded cS [] sf[] bb[] av[] = bb[]
switchAll-bounded cS ((a , d) ∷ []) _ _ (av∷ p _) =
  boundedBy-weaken (timeMax-right cS (close (d a))) (boundedAt (p a))
switchAll-bounded cS ((a , d) ∷ (a′ , d′) ∷ os)
                  (sf∷ le s) (bb∷ lc (bb∷ lc′ b′)) (av∷ p ps) =
  append-bounded (cutAt a a′ (emits (d a))) (switchAllT ((a′ , d′) ∷ os))
    (boundedBy-weaken
      (timeLeq-trans a′ cS (timeMax cS (lastClose cS ((a′ , d′) ∷ os)))
        lc′ (timeMax-left cS (lastClose cS ((a′ , d′) ∷ os))))
      (cutAt-bounded-next a a′ (emits (d a)) (sortedFrom-head s)))
    (switchAll-bounded cS ((a′ , d′) ∷ os) s (bb∷ lc′ b′) ps)
  where
    sortedFrom-head : {A : Set} {b u : Time} {x : A} {xs : TimedObs A}
                    → SortedFrom b ((u , x) ∷ xs) → timeLeq b u ≡ true
    sortedFrom-head (sf∷ le _) = le

exhaustClose-lb : (b : Time) (os : TimedObs Inner)
  → AllVals WFDen os → timeLeq b (exhaustClose b os) ≡ true
exhaustClose-lb b []             av[]       = timeLeq-refl b
exhaustClose-lb b ((a , d) ∷ os) (av∷ p ps) with timeLt a b in k
... | true  = exhaustClose-lb b os ps
... | false = timeLeq-trans b (close (d a)) _
    (timeLeq-trans b a _ (timeLt-false⇒timeLeq-flip a b k) (closeAt (p a)))
    (exhaustClose-lb (close (d a)) os ps)

exhaust-sorted : (b : Time) (os : TimedObs Inner)
  → AllVals WFDen os → SortedFrom b (exhaustAllT b os)
exhaust-sorted b []             av[]       = sf[]
exhaust-sorted b ((a , d) ∷ os) (av∷ p ps) with timeLt a b in k
... | true  = exhaust-sorted b os ps
... | false = append-sortedFrom _ _
    (sortedFrom-weaken (timeLt-false⇒timeLeq-flip a b k) (sortedAt (p a)))
    (boundedAt (p a))
    (exhaust-sorted (close (d a)) os ps)
    (timeLeq-trans b a _ (timeLt-false⇒timeLeq-flip a b k) (closeAt (p a)))

exhaust-bounded : (b : Time) (os : TimedObs Inner)
  → AllVals WFDen os → BoundedBy (exhaustClose b os) (exhaustAllT b os)
exhaust-bounded b []             av[]       = bb[]
exhaust-bounded b ((a , d) ∷ os) (av∷ p ps) with timeLt a b in k
... | true  = exhaust-bounded b os ps
... | false = append-bounded _ _
    (boundedBy-weaken (exhaustClose-lb (close (d a)) os ps) (boundedAt (p a)))
    (exhaust-bounded (close (d a)) os ps)

-- ANY program, subscribed at ANY time, is well-formed relative to that
-- subscription time -----------------------------------------------------------------

denote-wf  : (e : Exp) (env : Env) → EnvWF env
  → (t : Time) → WFAt t (⟦ e ⟧ env t)
denoteS-wf : (s : ExpS) (env : Env) → EnvWF env
  → (t : Time) → WFAt t (⟦ s ⟧S env t)
denoteS-inners-wf : (s : ExpS) (env : Env) → EnvWF env
  → (t : Time) → AllVals WFDen (emits (⟦ s ⟧S env t))
wfDen-list : (es : List Exp) (env : Env) → EnvWF env
  → (t : Time) → AllVals WFDen (denoteList es env t)
wfDen-fun : (f : Val → Exp) (env : Env) → EnvWF env
  → (xs : TimedObs Val) → AllVals WFDen (denoteFun f env xs)

denoteList-sorted : (es : List Exp) (env : Env) (t : Time)
  → SortedFrom t (denoteList es env t)
denoteList-sorted []       env t = sf[]
denoteList-sorted (e ∷ es) env t =
  sf∷ (timeLeq-refl t) (denoteList-sorted es env t)

denoteList-bounded : (es : List Exp) (env : Env) (t : Time)
  → BoundedBy t (denoteList es env t)
denoteList-bounded []       env t = bb[]
denoteList-bounded (e ∷ es) env t =
  bb∷ (timeLeq-refl t) (denoteList-bounded es env t)

denoteFun-sorted : {b : Time} (f : Val → Exp) (env : Env) (xs : TimedObs Val)
  → SortedFrom b xs → SortedFrom b (denoteFun f env xs)
denoteFun-sorted f env []             sf[]       = sf[]
denoteFun-sorted f env ((a , v) ∷ xs) (sf∷ le s) =
  sf∷ le (denoteFun-sorted f env xs s)

denoteFun-bounded : {c : Time} (f : Val → Exp) (env : Env) (xs : TimedObs Val)
  → BoundedBy c xs → BoundedBy c (denoteFun f env xs)
denoteFun-bounded f env []             bb[]       = bb[]
denoteFun-bounded f env ((a , v) ∷ xs) (bb∷ le b) =
  bb∷ le (denoteFun-bounded f env xs b)

denote-wf emptyE env wfe t = wfAt sf[] (timeLeq-refl t) bb[]
denote-wf (ofE vs) env wfe t =
  wfAt (const-sortedFrom t vs) (timeLeq-refl t) (const-bounded t vs)
denote-wf (shareE false i) env wfe t =
  wfAt (filterAfter-from t (emits (snd (env i))) (sortedAt (wfe i)))
       (timeMax-left t (close (snd (env i))))
       (boundedBy-weaken (timeMax-right t (close (snd (env i))))
         (filterAfter-bounded t (emits (snd (env i))) (boundedAt (wfe i))))
denote-wf (shareE true i) env wfe t with timeEq t (fst (env i)) in k
... | true rewrite timeEq-sound t (fst (env i)) k =
  wfAt (sortedAt (wfe i))
       (timeMax-left (fst (env i)) (close (snd (env i))))
       (boundedBy-weaken (timeMax-right (fst (env i)) (close (snd (env i))))
         (boundedAt (wfe i)))
... | false =
  wfAt (filterAfter-from t (emits (snd (env i))) (sortedAt (wfe i)))
       (timeMax-left t (close (snd (env i))))
       (boundedBy-weaken (timeMax-right t (close (snd (env i))))
         (filterAfter-bounded t (emits (snd (env i))) (boundedAt (wfe i))))
denote-wf (letShareE src body) env wfe t =
  denote-wf body (extendEnv (t , ⟦ src ⟧ env t) env)
    (extendEnv-wf t (⟦ src ⟧ env t) env wfe (denote-wf src env wfe t)) t
denote-wf (mapE f e) env wfe t with denote-wf e env wfe t
... | wfAt s c b =
  wfAt (mapT-sortedFrom f (emits (⟦ e ⟧ env t)) s)
       c
       (mapT-bounded f (emits (⟦ e ⟧ env t)) b)
denote-wf (takeE n e) env wfe t with denote-wf e env wfe t
... | wfAt s c b =
  wfAt (take-sortedFrom n (emits (⟦ e ⟧ env t)) s)
       (takeB-closeAt t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)) s b c)
       (take-boundedB t n (emits (⟦ e ⟧ env t)) (close (⟦ e ⟧ env t)) s b)
denote-wf (scanE f z e) env wfe t with denote-wf e env wfe t
... | wfAt s c b =
  wfAt (scanT-sortedFrom f z (emits (⟦ e ⟧ env t)) s)
       c
       (scanT-bounded f z (emits (⟦ e ⟧ env t)) b)
denote-wf (mergeAllE s) env wfe t
  with denoteS-wf s env wfe t | denoteS-inners-wf s env wfe t
... | wfAt so co bo | iw =
  wfAt (mergeAll-sorted (emits (⟦ s ⟧S env t)) so iw)
       (timeLeq-trans t (close (⟦ s ⟧S env t))
         (maxCloses (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t))) co
         (maxCloses-lb (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t))))
       (mergeAll-bounded (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t)) iw)
denote-wf (concatAllE s) env wfe t
  with denoteS-wf s env wfe t | denoteS-inners-wf s env wfe t
... | wfAt so co bo | iw =
  wfAt (concatAll-sorted t (emits (⟦ s ⟧S env t)) iw)
       (timeLeq-trans t (concatAllClose t (emits (⟦ s ⟧S env t)))
         (timeMax (close (⟦ s ⟧S env t))
                  (concatAllClose t (emits (⟦ s ⟧S env t))))
         (concatAllClose-lb t (emits (⟦ s ⟧S env t)) iw)
         (timeMax-right (close (⟦ s ⟧S env t))
                        (concatAllClose t (emits (⟦ s ⟧S env t)))))
       (boundedBy-weaken
         (timeMax-right (close (⟦ s ⟧S env t))
                        (concatAllClose t (emits (⟦ s ⟧S env t))))
         (concatAll-bounded t (emits (⟦ s ⟧S env t)) iw))
denote-wf (switchAllE s) env wfe t
  with denoteS-wf s env wfe t | denoteS-inners-wf s env wfe t
... | wfAt so co bo | iw =
  wfAt (switchAll-sorted (emits (⟦ s ⟧S env t)) so iw)
       (timeLeq-trans t (close (⟦ s ⟧S env t))
         (timeMax (close (⟦ s ⟧S env t))
                  (lastClose (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t))))
         co
         (timeMax-left (close (⟦ s ⟧S env t))
                       (lastClose (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t)))))
       (switchAll-bounded (close (⟦ s ⟧S env t)) (emits (⟦ s ⟧S env t)) so bo iw)
denote-wf (exhaustAllE s) env wfe t
  with denoteS-wf s env wfe t | denoteS-inners-wf s env wfe t
... | wfAt so co bo | iw =
  wfAt (exhaust-sorted t (emits (⟦ s ⟧S env t)) iw)
       (timeLeq-trans t (exhaustClose t (emits (⟦ s ⟧S env t)))
         (timeMax (close (⟦ s ⟧S env t))
                  (exhaustClose t (emits (⟦ s ⟧S env t))))
         (exhaustClose-lb t (emits (⟦ s ⟧S env t)) iw)
         (timeMax-right (close (⟦ s ⟧S env t))
                        (exhaustClose t (emits (⟦ s ⟧S env t)))))
       (boundedBy-weaken
         (timeMax-right (close (⟦ s ⟧S env t))
                        (exhaustClose t (emits (⟦ s ⟧S env t))))
         (exhaust-bounded t (emits (⟦ s ⟧S env t)) iw))

denoteS-wf (ofS es) env wfe t =
  wfAt (denoteList-sorted es env t) (timeLeq-refl t)
       (denoteList-bounded es env t)
denoteS-wf (mapS f e) env wfe t with denote-wf e env wfe t
... | wfAt s c b =
  wfAt (denoteFun-sorted f env (emits (⟦ e ⟧ env t)) s)
       c
       (denoteFun-bounded f env (emits (⟦ e ⟧ env t)) b)

denoteS-inners-wf (ofS es)    env wfe t = wfDen-list es env wfe t
denoteS-inners-wf (mapS f e) env wfe t =
  wfDen-fun f env wfe (emits (⟦ e ⟧ env t))

wfDen-list []       env wfe t = av[]
wfDen-list (e ∷ es) env wfe t =
  av∷ (λ u → denote-wf e env wfe u) (wfDen-list es env wfe t)

wfDen-fun f env wfe []             = av[]
wfDen-fun f env wfe ((a , v) ∷ xs) =
  av∷ (λ u → denote-wf (f v) env wfe u) (wfDen-fun f env wfe xs)

-- static programs: no share slots — everything the program does happens
-- inside the subscription frame ------------------------------------------------------

data All {A : Set} (P : A → Set) : List A → Set where
  all[] : All P []
  all∷  : {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

data Static  : Exp → Set
data StaticS : ExpS → Set

data Static where
  st-empty      : Static emptyE
  st-of         : {vs : List Val} → Static (ofE vs)
  st-map        : {f : Val → Val} {e : Exp} → Static e → Static (mapE f e)
  st-take       : {n : ℕ} {e : Exp} → Static e → Static (takeE n e)
  st-scan       : {f : Val → Val → Val} {z : Val} {e : Exp}
                → Static e → Static (scanE f z e)
  st-mergeAll   : {s : ExpS} → StaticS s → Static (mergeAllE s)
  st-concatAll  : {s : ExpS} → StaticS s → Static (concatAllE s)
  st-switchAll  : {s : ExpS} → StaticS s → Static (switchAllE s)
  st-exhaustAll : {s : ExpS} → StaticS s → Static (exhaustAllE s)

data StaticS where
  st-ofS  : {es : List Exp} → All Static es → StaticS (ofS es)
  st-mapS : {f : Val → Exp} {e : Exp}
          → ((v : Val) → Static (f v)) → Static e → StaticS (mapS f e)

-- every emission in the list happens at exactly time t
data AllAt {A : Set} (t : Time) : TimedObs A → Set where
  aa[] : AllAt t []
  aa∷  : {v : A} {xs : TimedObs A} → AllAt t xs → AllAt t ((t , v) ∷ xs)

-- a static inner: subscribed anywhere, it emits everything at its
-- subscription time and closes there too
StaticDen : Inner → Set
StaticDen d = (u : Time) → AllAt u (emits (d u)) × (close (d u) ≡ u)

allAt-const : {A : Set} (t : Time) (vs : List A)
  → AllAt t (map (λ v → (t , v)) vs)
allAt-const t []       = aa[]
allAt-const t (v ∷ vs) = aa∷ (allAt-const t vs)

allAt-mapT : {A B : Set} {t : Time} (f : A → B) (xs : TimedObs A)
  → AllAt t xs → AllAt t (mapT f xs)
allAt-mapT f []             aa[]     = aa[]
allAt-mapT f ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (allAt-mapT f xs ax)

allAt-scan : {A B : Set} {t : Time} (f : B → A → B) (z : B) (xs : TimedObs A)
  → AllAt t xs → AllAt t (scanT f z xs)
allAt-scan f z []             aa[]     = aa[]
allAt-scan f z ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (allAt-scan f (f z v) xs ax)

allAt-take : {A : Set} {t : Time} (n : ℕ) (xs : TimedObs A)
  → AllAt t xs → AllAt t (takeT n xs)
allAt-take zero    xs             _        = aa[]
allAt-take (suc n) []             aa[]     = aa[]
allAt-take (suc n) ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (allAt-take n xs ax)

allAt-merge : {A : Set} {t : Time} (xs ys : TimedObs A)
  → AllAt t xs → AllAt t ys → AllAt t (mergeT xs ys)
allAt-merge []       ys       aa[]     ay       = ay
allAt-merge (x ∷ xs) []       ax       aa[]     = ax
allAt-merge {A} {t} ((_ , v) ∷ xs) ((_ , w) ∷ ys) (aa∷ ax) (aa∷ ay)
  rewrite timeLeq-refl t = aa∷ (allAt-merge xs ((t , w) ∷ ys) ax (aa∷ ay))

allAt-append : {A : Set} {t : Time} (xs ys : TimedObs A)
  → AllAt t xs → AllAt t ys → AllAt t (xs ++ ys)
allAt-append []       ys aa[]     ay = ay
allAt-append (_ ∷ xs) ys (aa∷ ax) ay = aa∷ (allAt-append xs ys ax ay)

takeCloseB-allAt : {A : Set} (t : Time) (n : ℕ) (xs : TimedObs A)
  → AllAt t xs → takeCloseB t n xs t ≡ t
takeCloseB-allAt t zero          xs             _        = refl
takeCloseB-allAt t (suc n)       []             aa[]     = refl
takeCloseB-allAt t (suc zero)    ((_ , v) ∷ xs) (aa∷ ax) = refl
takeCloseB-allAt t (suc (suc n)) ((_ , v) ∷ xs) (aa∷ ax) =
  takeCloseB-allAt t (suc n) xs ax

denoteList-allAt : (es : List Exp) (env : Env) (t : Time)
  → AllAt t (denoteList es env t)
denoteList-allAt []       env t = aa[]
denoteList-allAt (e ∷ es) env t = aa∷ (denoteList-allAt es env t)

denoteFun-allAt : {t : Time} (f : Val → Exp) (env : Env) (xs : TimedObs Val)
  → AllAt t xs → AllAt t (denoteFun f env xs)
denoteFun-allAt f env []             aa[]     = aa[]
denoteFun-allAt f env ((_ , v) ∷ xs) (aa∷ ax) = aa∷ (denoteFun-allAt f env xs ax)

-- each join, applied to a static burst of static inners, stays inside the
-- instant ---------------------------------------------------------------------------

mergeAll-allAt : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → AllAt t (mergeAllT os)
mergeAll-allAt t []             aa[]     av[]       = aa[]
mergeAll-allAt t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps) =
  allAt-merge _ _ (fst (p t)) (mergeAll-allAt t os ax ps)

mergeAll-close-static : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → maxCloses t os ≡ t
mergeAll-close-static t []             aa[]     av[]       = refl
mergeAll-close-static t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps)
  rewrite snd (p t) | timeLeq-refl t = mergeAll-close-static t os ax ps

concatAll-allAt : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → AllAt t (concatAllT t os)
concatAll-allAt t []             aa[]     av[]       = aa[]
concatAll-allAt t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps)
  rewrite timeLeq-refl t | snd (p t) =
  allAt-append _ _ (fst (p t)) (concatAll-allAt t os ax ps)

concatAll-close-static : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → concatAllClose t os ≡ t
concatAll-close-static t []             aa[]     av[]       = refl
concatAll-close-static t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps)
  rewrite timeLeq-refl t | snd (p t) = concatAll-close-static t os ax ps

cutAt-allAt : {t : Time} (xs : TimedObs Val)
  → AllAt t xs → AllAt t (cutAt t t xs)
cutAt-allAt []             aa[]     = aa[]
cutAt-allAt {t} ((_ , v) ∷ xs) (aa∷ ax)
  rewrite timeEq-refl t = aa∷ (cutAt-allAt xs ax)

switchAll-allAt : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → AllAt t (switchAllT os)
switchAll-allAt t []                        aa[]     av[]      = aa[]
switchAll-allAt t ((_ , d) ∷ [])            (aa∷ _)  (av∷ p _) = fst (p t)
switchAll-allAt t ((_ , d) ∷ (_ , d′) ∷ os) (aa∷ (aa∷ ax)) (av∷ p ps) =
  allAt-append _ _ (cutAt-allAt _ (fst (p t)))
    (switchAll-allAt t ((t , d′) ∷ os) (aa∷ ax) ps)

lastClose-static : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → lastClose t os ≡ t
lastClose-static t []                    aa[]     av[]       = refl
lastClose-static t ((_ , d) ∷ [])        (aa∷ _)  (av∷ p _)  = snd (p t)
lastClose-static t ((_ , d) ∷ (u , d′) ∷ os) (aa∷ ax) (av∷ p ps) =
  lastClose-static t ((u , d′) ∷ os) ax ps

exhaust-allAt : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → AllAt t (exhaustAllT t os)
exhaust-allAt t []             aa[]     av[]       = aa[]
exhaust-allAt t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps)
  rewrite timeLt-irrefl t | snd (p t) =
  allAt-append _ _ (fst (p t)) (exhaust-allAt t os ax ps)

exhaust-close-static : (t : Time) (os : TimedObs Inner)
  → AllAt t os → AllVals StaticDen os → exhaustClose t os ≡ t
exhaust-close-static t []             aa[]     av[]       = refl
exhaust-close-static t ((_ , d) ∷ os) (aa∷ ax) (av∷ p ps)
  rewrite timeLt-irrefl t | snd (p t) = exhaust-close-static t os ax ps

-- THE BURST RULE, by mutual structural induction: a static program
-- subscribed at t emits everything at t AND closes at t. (The close half is
-- what keeps the serial joins inside the instant: a queued cold inner is
-- subscribed at the previous close, which IS the subscription instant.)

static-frame : (e : Exp) → Static e → (env : Env) (t : Time)
  → AllAt t (emits (⟦ e ⟧ env t)) × (close (⟦ e ⟧ env t) ≡ t)
staticS-arrAt : (s : ExpS) → StaticS s → (env : Env) (t : Time)
  → AllAt t (emits (⟦ s ⟧S env t))
staticS-close : (s : ExpS) → StaticS s → (env : Env) (t : Time)
  → close (⟦ s ⟧S env t) ≡ t
staticS-inners : (s : ExpS) → StaticS s → (env : Env) (t : Time)
  → AllVals StaticDen (emits (⟦ s ⟧S env t))
staticDen-list : (es : List Exp) → All Static es → (env : Env) (t : Time)
  → AllVals StaticDen (denoteList es env t)
staticDen-fun : (f : Val → Exp) → ((v : Val) → Static (f v)) → (env : Env)
  → (xs : TimedObs Val) → AllVals StaticDen (denoteFun f env xs)

static-frame emptyE st-empty env t = aa[] , refl
static-frame (ofE vs) st-of env t = allAt-const t vs , refl
static-frame (mapE f e) (st-map se) env t =
  allAt-mapT f (emits (⟦ e ⟧ env t)) (fst (static-frame e se env t)) ,
  snd (static-frame e se env t)
static-frame (takeE n e) (st-take se) env t
  rewrite snd (static-frame e se env t) =
  allAt-take n (emits (⟦ e ⟧ env t)) (fst (static-frame e se env t)) ,
  takeCloseB-allAt t n (emits (⟦ e ⟧ env t)) (fst (static-frame e se env t))
static-frame (scanE f z e) (st-scan se) env t =
  allAt-scan f z (emits (⟦ e ⟧ env t)) (fst (static-frame e se env t)) ,
  snd (static-frame e se env t)
static-frame (mergeAllE s) (st-mergeAll ss) env t
  rewrite staticS-close s ss env t =
  mergeAll-allAt t (emits (⟦ s ⟧S env t))
    (staticS-arrAt s ss env t) (staticS-inners s ss env t) ,
  mergeAll-close-static t (emits (⟦ s ⟧S env t))
    (staticS-arrAt s ss env t) (staticS-inners s ss env t)
static-frame (concatAllE s) (st-concatAll ss) env t
  rewrite staticS-close s ss env t
        | concatAll-close-static t (emits (⟦ s ⟧S env t))
            (staticS-arrAt s ss env t) (staticS-inners s ss env t)
        | timeLeq-refl t =
  concatAll-allAt t (emits (⟦ s ⟧S env t))
    (staticS-arrAt s ss env t) (staticS-inners s ss env t) ,
  refl
static-frame (switchAllE s) (st-switchAll ss) env t
  rewrite staticS-close s ss env t
        | lastClose-static t (emits (⟦ s ⟧S env t))
            (staticS-arrAt s ss env t) (staticS-inners s ss env t)
        | timeLeq-refl t =
  switchAll-allAt t (emits (⟦ s ⟧S env t))
    (staticS-arrAt s ss env t) (staticS-inners s ss env t) ,
  refl
static-frame (exhaustAllE s) (st-exhaustAll ss) env t
  rewrite staticS-close s ss env t
        | exhaust-close-static t (emits (⟦ s ⟧S env t))
            (staticS-arrAt s ss env t) (staticS-inners s ss env t)
        | timeLeq-refl t =
  exhaust-allAt t (emits (⟦ s ⟧S env t))
    (staticS-arrAt s ss env t) (staticS-inners s ss env t) ,
  refl

staticS-arrAt (ofS es)    (st-ofS _)      env t = denoteList-allAt es env t
staticS-arrAt (mapS f e) (st-mapS sf se) env t =
  denoteFun-allAt f env _ (fst (static-frame e se env t))

staticS-close (ofS es)    _               env t = refl
staticS-close (mapS f e) (st-mapS sf se) env t = snd (static-frame e se env t)

staticS-inners (ofS es)    (st-ofS ses)    env t = staticDen-list es ses env t
staticS-inners (mapS f e) (st-mapS sf se) env t =
  staticDen-fun f sf env (emits (⟦ e ⟧ env t))

staticDen-list []       all[]         env t = av[]
staticDen-list (e ∷ es) (all∷ se ses) env t =
  av∷ (λ u → static-frame e se env u) (staticDen-list es ses env t)

staticDen-fun f sf env []             = av[]
staticDen-fun f sf env ((a , v) ∷ xs) =
  av∷ (λ u → static-frame (f v) (sf v) env u) (staticDen-fun f sf env xs)

-- batching a single-instant stream yields exactly one batch --------------------------

vals : {A : Set} → TimedObs A → List A
vals = map snd

allAt-batch : {A : Set} (t : Time) (v : A) (xs : TimedObs A)
  → AllAt t xs
  → batchSpec ((t , v) ∷ xs) ≡ (t , v ∷ vals xs) ∷ []
allAt-batch t v []             aa[]     = refl
allAt-batch t v ((_ , w) ∷ xs) (aa∷ ax)
  rewrite allAt-batch t w xs ax | timeEq-refl t = refl

-- [] for the empty stream, one batch of all the values otherwise
oneBatch : {A : Set} → Time → TimedObs A → TimedObs (List A)
oneBatch t []       = []
oneBatch t (x ∷ xs) = (t , vals (x ∷ xs)) ∷ []

-- THE FRAME-BATCH THEOREM: any static program, nested to any depth,
-- subscribed at any time, batches to AT MOST ONE batch — the whole
-- subscription frame is one instant. And the implementation port agrees.
frame-batch : (e : Exp) → Static e → (env : Env) (t : Time)
  → batchSpec (emits (⟦ e ⟧ env t)) ≡ oneBatch t (emits (⟦ e ⟧ env t))
frame-batch e se env t with emits (⟦ e ⟧ env t) | fst (static-frame e se env t)
... | []           | aa[]   = refl
... | (_ , v) ∷ xs | aa∷ ax = allAt-batch t v xs ax

impl-frame-batch : (e : Exp) → Static e → (env : Env) (t : Time)
  → batchImpl (emits (⟦ e ⟧ env t)) ≡ oneBatch t (emits (⟦ e ⟧ env t))
impl-frame-batch e se env t =
  trans (batchImpl-spec (emits (⟦ e ⟧ env t))) (frame-batch e se env t)

-- the motivating examples, as concrete equations -------------------------------------

-- merge(of(1), of(2)) delivers ONE batch [1, 2]
merge-of-emits : (env : Env) (t : Time)
  → emits (⟦ mergeE (ofE (1 ∷ [])) (ofE (2 ∷ [])) ⟧ env t)
    ≡ (t , 1) ∷ (t , 2) ∷ []
merge-of-emits env t rewrite timeLeq-refl t = refl

merge-of-example : (env : Env) (t : Time)
  → batchSpec (emits (⟦ mergeE (ofE (1 ∷ [])) (ofE (2 ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ []) ∷ []
merge-of-example env t =
  trans (cong batchSpec (merge-of-emits env t))
        (allAt-batch t 1 ((t , 2) ∷ []) (aa∷ aa[]))

-- concat(of(1, 2), of(3)) delivers ONE batch [1, 2, 3]
concat-of-emits : (env : Env) (t : Time)
  → emits (⟦ concatE (ofE (1 ∷ 2 ∷ [])) (ofE (3 ∷ [])) ⟧ env t)
    ≡ (t , 1) ∷ (t , 2) ∷ (t , 3) ∷ []
concat-of-emits env t rewrite timeLeq-refl t | timeLeq-refl t = refl

concat-of-example : (env : Env) (t : Time)
  → batchSpec (emits (⟦ concatE (ofE (1 ∷ 2 ∷ [])) (ofE (3 ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ 3 ∷ []) ∷ []
concat-of-example env t =
  trans (cong batchSpec (concat-of-emits env t))
        (allAt-batch t 1 ((t , 2) ∷ (t , 3) ∷ []) (aa∷ (aa∷ aa[])))

-- switchAll over a sync burst passes every inner in full (each sync inner
-- completes before the next arrival is processed — mirroring rxjs)
switch-of-emits : (env : Env) (t : Time)
  → emits (⟦ switchAllE (ofS (ofE (1 ∷ 2 ∷ []) ∷ ofE (3 ∷ []) ∷ [])) ⟧ env t)
    ≡ (t , 1) ∷ (t , 2) ∷ (t , 3) ∷ []
switch-of-emits env t rewrite timeEq-refl t = refl

switch-of-example : (env : Env) (t : Time)
  → batchSpec
      (emits (⟦ switchAllE (ofS (ofE (1 ∷ 2 ∷ []) ∷ ofE (3 ∷ []) ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ 3 ∷ []) ∷ []
switch-of-example env t =
  trans (cong batchSpec (switch-of-emits env t))
        (allAt-batch t 1 ((t , 2) ∷ (t , 3) ∷ []) (aa∷ (aa∷ aa[])))

-- exhaustAll accepts a sync sibling because the previous inner has already
-- closed (of-then-of emits both — mirroring rxjs)
exhaust-of-emits : (env : Env) (t : Time)
  → emits (⟦ exhaustAllE (ofS (ofE (1 ∷ 2 ∷ []) ∷ ofE (3 ∷ []) ∷ [])) ⟧ env t)
    ≡ (t , 1) ∷ (t , 2) ∷ (t , 3) ∷ []
exhaust-of-emits env t rewrite timeLt-irrefl t = refl

exhaust-of-example : (env : Env) (t : Time)
  → batchSpec
      (emits (⟦ exhaustAllE (ofS (ofE (1 ∷ 2 ∷ []) ∷ ofE (3 ∷ []) ∷ [])) ⟧ env t))
    ≡ (t , 1 ∷ 2 ∷ 3 ∷ []) ∷ []
exhaust-of-example env t =
  trans (cong batchSpec (exhaust-of-emits env t))
        (allAt-batch t 1 ((t , 2) ∷ (t , 3) ∷ []) (aa∷ (aa∷ aa[])))

-- the async half of the burst rule: a cold triggered by a source event
-- shares that event's root cause, so it batches WITH the event.
-- concat(take 1 (share s), of(9)) delivers the source's first value and the
-- 9 as ONE batch, at the source event's time.
cascade-emits : (i : ℕ) (env : Env) (t t₁ : Time) (v₁ : Val)
  (rest : TimedObs Val) (c : Time)
  → snd (env i) ≡ obs ((t₁ , v₁) ∷ rest) c
  → timeLt t t₁ ≡ true      -- subscribed before the source's first event
  → emits (⟦ concatE (takeE 1 (shareE false i)) (ofE (9 ∷ [])) ⟧ env t)
    ≡ (t₁ , v₁) ∷ (t₁ , 9) ∷ []
cascade-emits i env t t₁ v₁ rest c eq lt
  rewrite eq | timeLeq-refl t | lt
        | timeLt⇒timeLeq-flip-false t t₁ lt = refl

cascade-example : (i : ℕ) (env : Env) (t t₁ : Time) (v₁ : Val)
  (rest : TimedObs Val) (c : Time)
  → snd (env i) ≡ obs ((t₁ , v₁) ∷ rest) c
  → timeLt t t₁ ≡ true
  → batchSpec
      (emits (⟦ concatE (takeE 1 (shareE false i)) (ofE (9 ∷ [])) ⟧ env t))
    ≡ (t₁ , v₁ ∷ 9 ∷ []) ∷ []
cascade-example i env t t₁ v₁ rest c eq lt =
  trans (cong batchSpec (cascade-emits i env t t₁ v₁ rest c eq lt))
        (allAt-batch t₁ v₁ ((t₁ , 9) ∷ []) (aa∷ aa[]))

-- the diamond anchor law transfers: source events keep distinct times, so
-- batching the self-merge of any strictly monotone denotation still pairs
-- every value with itself
diamond-burst : (e : Exp) (env : Env) (t : Time)
  → StrictMono (emits (⟦ e ⟧ env t))
  → batchSpec (emits (⟦ mergeE e e ⟧ env t))
    ≡ mapT dbl (emits (⟦ e ⟧ env t))
diamond-burst e env t m
  rewrite mergeT-nil (emits (⟦ e ⟧ env t)) = diamond _ m

-- SHARE CONNECTION, DERIVED ----------------------------------------------
-- The slot content of a letShare is computed from its binding; nothing
-- about the share is hypothesized beyond the root subjects' own shape.

-- n merged refs of one hot slot
nRefs : ℕ → ℕ → Exp
nRefs n i = mergeAllE (ofS (replicate n (shareE false i)))

nRefs-emits : (n i : ℕ) (env : Env) (t : Time)
  → emits (⟦ nRefs n i ⟧ env t)
    ≡ nMerge n (filterAfter t (emits (snd (env i))))
nRefs-emits zero    i env t = refl
nRefs-emits (suc n) i env t =
  cong (mergeT (filterAfter t (emits (snd (env i))))) (nRefs-emits n i env t)

-- THE N-ARY FRAME JOIN (Grow's law, derived): n refs of a hot source
-- deliver every source event as ONE batch of n copies
share-growth : (n i : ℕ) (env : Env) (t : Time)
  → StrictMono (emits (snd (env i)))
  → batchSpec (emits (⟦ nRefs (suc n) i ⟧ env t))
    ≡ mapT (λ v → replicate (suc n) v)
           (filterAfter t (emits (snd (env i))))
share-growth n i env t m =
  trans (cong batchSpec (nRefs-emits (suc n) i env t))
        (diamondN n (filterAfter t (emits (snd (env i))))
                  (filterAfter-mono t (emits (snd (env i))) m))

-- THE SHARE DIAMOND, END TO END: bind a hot slot with letShare, fan out
-- two mapped refs (the first flagged as connecting), merge. Both refs see
-- the same suffix — the connecting ref through the connection frame, the
-- second because filterAfter t absorbs the binding's own filterAfter t
-- (connection-time invariance for hot bindings) — so every source event
-- delivers as ONE batch [f v , g v].
share-diamond-emits : (j : ℕ) (f g : Val → Val) (env : Env) (t : Time)
  → emits (⟦ letShareE (shareE false j)
               (mergeE (mapE f (shareE true 0))
                       (mapE g (shareE false 0))) ⟧ env t)
    ≡ mergeT (mapT f (filterAfter t (emits (snd (env j)))))
             (mapT g (filterAfter t (emits (snd (env j)))))
share-diamond-emits j f g env t
  rewrite timeEq-refl t
        | filterAfter-absorb t t (emits (snd (env j))) (timeLeq-refl t)
        | mergeT-nil (mapT g (filterAfter t (emits (snd (env j)))))
  = refl

share-diamond : (j : ℕ) (f g : Val → Val) (env : Env) (t : Time)
  → StrictMono (emits (snd (env j)))
  → batchSpec
      (emits (⟦ letShareE (shareE false j)
                  (mergeE (mapE f (shareE true 0))
                          (mapE g (shareE false 0))) ⟧ env t))
    ≡ mapT (λ v → f v ∷ g v ∷ []) (filterAfter t (emits (snd (env j))))
share-diamond j f g env t m =
  trans (cong batchSpec (share-diamond-emits j f g env t))
        (diamond2 f g (filterAfter t (emits (snd (env j))))
                  (filterAfter-mono t (emits (snd (env j))) m))

-- a COLD binding: the connecting ref receives the subscription-frame
-- value, the second ref's registration-only replay misses it (ratified:
-- hot semantics, matching the TS model's shareRef and the v5 share)
cold-share-emits : (env : Env) (t : Time)
  → emits (⟦ letShareE (ofE (5 ∷ []))
               (mergeE (shareE true 0) (shareE false 0)) ⟧ env t)
    ≡ (t , 5) ∷ []
cold-share-emits env t rewrite timeEq-refl t | timeLt-irrefl t = refl

cold-share-example : (env : Env) (t : Time)
  → batchSpec (emits (⟦ letShareE (ofE (5 ∷ []))
                          (mergeE (shareE true 0) (shareE false 0)) ⟧ env t))
    ≡ (t , 5 ∷ []) ∷ []
cold-share-example env t = cong batchSpec (cold-share-emits env t)

-- THE LATE-JOIN GROWTH LAW (the README's [7,7] then [8,8,8], n-ary):
-- suc n static refs of hot slot j, plus one ref spawned by slot k's event
-- at u between the source's two events — the first event delivers suc n
-- copies as one batch, the second delivers suc (suc n) copies as one
-- batch. The late ref's suffix (it missed the first event) and the grown
-- multiplicity are both DERIVED from the denotation.
late-join-emits : (n j k : ℕ) (env : Env) (t t₁ t₂ u c c′ : Time)
  → snd (env j) ≡ obs ((t₁ , 7) ∷ (t₂ , 8) ∷ []) c
  → snd (env k) ≡ obs ((u , 0) ∷ []) c′
  → timeLt t t₁ ≡ true → timeLt t₁ u ≡ true → timeLt u t₂ ≡ true
  → emits (⟦ mergeE (nRefs (suc n) j)
              (mergeAllE (mapS (λ _ → shareE false j) (shareE false k)))
           ⟧ env t)
    ≡ mergeT (nMerge (suc n) ((t₁ , 7) ∷ (t₂ , 8) ∷ [])) ((t₂ , 8) ∷ [])
late-join-emits n j k env t t₁ t₂ u c c′ eqj eqk l1 l2 l3
  rewrite nRefs-emits (suc n) j env t
        | eqj
        | l1
        | timeLt-trans t t₁ t₂ l1 (timeLt-trans t₁ u t₂ l2 l3)
        | eqk
        | timeLt-trans t t₁ u l1 l2
        -- the spawned ref's view of slot j only surfaces once the trigger
        -- has reduced — rewrite the slot equation again for it
        | eqj
        | timeLt-asym t₁ u l2
        | l3
  = refl

late-join-list : {A : Set} (n : ℕ) (t₁ t₂ : Time) (v w : A)
  → timeLt t₁ t₂ ≡ true
  → mergeT (nMerge (suc n) ((t₁ , v) ∷ (t₂ , w) ∷ [])) ((t₂ , w) ∷ [])
    ≡ replicate (suc n) (t₁ , v) ++ replicate (suc (suc n)) (t₂ , w)
late-join-list n t₁ t₂ v w lt =
  trans (cong (λ l → mergeT l ((t₂ , w) ∷ []))
          (trans (nMerge-cons (suc n) (t₁ , v) ((t₂ , w) ∷ []) lt)
            (cong (_++_ (replicate (suc n) (t₁ , v)))
              (trans (nMerge-cons (suc n) (t₂ , w) [] refl)
                (trans (cong (_++_ (replicate (suc n) (t₂ , w)))
                             (nMerge-nil (suc n)))
                       (++-nil (replicate (suc n) (t₂ , w))))))))
  (trans (merge-repL (suc n) t₁ v (replicate (suc n) (t₂ , w))
           ((t₂ , w) ∷ []) (timeLt⇒timeLeq t₁ t₂ lt))
         (cong (_++_ (replicate (suc n) (t₁ , v)))
               (merge-rep-self (suc n) t₂ w)))

late-join-growth : (n j k : ℕ) (env : Env) (t t₁ t₂ u c c′ : Time)
  → snd (env j) ≡ obs ((t₁ , 7) ∷ (t₂ , 8) ∷ []) c
  → snd (env k) ≡ obs ((u , 0) ∷ []) c′
  → timeLt t t₁ ≡ true → timeLt t₁ u ≡ true → timeLt u t₂ ≡ true
  → batchSpec
      (emits (⟦ mergeE (nRefs (suc n) j)
                 (mergeAllE (mapS (λ _ → shareE false j) (shareE false k)))
              ⟧ env t))
    ≡ (t₁ , replicate (suc n) 7) ∷ (t₂ , replicate (suc (suc n)) 8) ∷ []
late-join-growth n j k env t t₁ t₂ u c c′ eqj eqk l1 l2 l3 =
  trans (cong batchSpec
    (trans (late-join-emits n j k env t t₁ t₂ u c c′ eqj eqk l1 l2 l3)
           (late-join-list n t₁ t₂ 7 8 lt₁₂)))
  (trans (rep-batch n t₁ 7 (replicate (suc (suc n)) (t₂ , 8))
           (hn∷ (timeLt⇒timeEq-false t₁ t₂ lt₁₂)))
         (cong (_∷_ (t₁ , replicate (suc n) 7))
           (trans (cong batchSpec
                    (sym (++-nil (replicate (suc (suc n)) (t₂ , 8)))))
                  (rep-batch (suc n) t₂ 8 [] hn[]))))
  where
    lt₁₂ : timeLt t₁ t₂ ≡ true
    lt₁₂ = timeLt-trans t₁ u t₂ l2 l3

-- the README instance: two subscribers see [7 , 7]; a third joins between
-- the events; everyone sees [8 , 8 , 8]
readme-late-subscriber : (j k : ℕ) (env : Env) (t t₁ t₂ u c c′ : Time)
  → snd (env j) ≡ obs ((t₁ , 7) ∷ (t₂ , 8) ∷ []) c
  → snd (env k) ≡ obs ((u , 0) ∷ []) c′
  → timeLt t t₁ ≡ true → timeLt t₁ u ≡ true → timeLt u t₂ ≡ true
  → batchSpec
      (emits (⟦ mergeE (nRefs 2 j)
                 (mergeAllE (mapS (λ _ → shareE false j) (shareE false k)))
              ⟧ env t))
    ≡ (t₁ , 7 ∷ 7 ∷ []) ∷ (t₂ , 8 ∷ 8 ∷ 8 ∷ []) ∷ []
readme-late-subscriber = late-join-growth 1

-- THE DRIVER CONTRACT AND FEEDBACK -----------------------------------------
-- Root subjects are the model's async inputs. The driver (the outside
-- world) guarantees: each .next() call is its OWN instant — per-slot
-- histories are strictly monotone and distinct slots never share a Time
-- (tick , origin) — and a REENTRANT .next(), fired from user code while a
-- batch is delivering, is a FRESH instant strictly after the batch that
-- caused it (ratified: one .next() = one root cause; feedback never
-- extends the instant it reacts to). Under that contract feedback is just
-- a later event, and everything here applies to it unchanged: its own
-- synchronous cascade batches with IT, not with its cause.

-- slot k is a feedback echo of slot j (user code calls k.next on receiving
-- j's batch, so the driver stamps it strictly later): the feedback's
-- serial-join cascade lands in the FEEDBACK's batch
feedback-emits : (j k : ℕ) (env : Env) (t t₁ u c c′ : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ []) c
  → snd (env k) ≡ obs ((u , 2) ∷ []) c′
  → timeLt t t₁ ≡ true → timeLt t₁ u ≡ true
  → emits (⟦ mergeE (shareE false j)
              (concatE (takeE 1 (shareE false k)) (ofE (9 ∷ []))) ⟧ env t)
    ≡ (t₁ , 1) ∷ (u , 2) ∷ (u , 9) ∷ []
feedback-emits j k env t t₁ u c c′ eqj eqk l1 l2
  rewrite eqj | eqk
        | l1
        | timeLeq-refl t
        | timeLt-trans t t₁ u l1 l2
        | timeLt⇒timeLeq-flip-false t u (timeLt-trans t t₁ u l1 l2)
        | timeLt⇒timeLeq t₁ u l2
  = refl

feedback-example : (j k : ℕ) (env : Env) (t t₁ u c c′ : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ []) c
  → snd (env k) ≡ obs ((u , 2) ∷ []) c′
  → timeLt t t₁ ≡ true → timeLt t₁ u ≡ true
  → batchSpec
      (emits (⟦ mergeE (shareE false j)
                 (concatE (takeE 1 (shareE false k)) (ofE (9 ∷ []))) ⟧ env t))
    ≡ (t₁ , 1 ∷ []) ∷ (u , 2 ∷ 9 ∷ []) ∷ []
feedback-example j k env t t₁ u c c′ eqj eqk l1 l2 =
  trans (cong batchSpec (feedback-emits j k env t t₁ u c c′ eqj eqk l1 l2))
        (batches t₁ u (timeLt⇒timeEq-false t₁ u l2))
  where
    batches : (x y : Time) → timeEq x y ≡ false
      → batchSpec ((x , 1) ∷ (y , 2) ∷ (y , 9) ∷ [])
        ≡ (x , 1 ∷ []) ∷ (y , 2 ∷ 9 ∷ []) ∷ []
    batches x y ne rewrite timeEq-refl y | ne = refl

-- FENCED ORACLE FRONTIERS, CLOSED -------------------------------------------
-- Each of the shapes the TS oracle fenced off now has an Agda answer.

-- transient refs: a take-limited ref leaves early; the connection is one
-- life per letShare scope (ratified: no refcount reset mid-lifetime), so
-- the surviving ref keeps receiving — and the shared event still delivers
-- to both while both live
transient-ref-example : (j : ℕ) (env : Env) (t t₁ t₂ c : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ (t₂ , 2) ∷ []) c
  → timeLt t t₁ ≡ true → timeLt t₁ t₂ ≡ true
  → batchSpec
      (emits (⟦ mergeE (takeE 1 (shareE false j)) (shareE false j) ⟧ env t))
    ≡ (t₁ , 1 ∷ 1 ∷ []) ∷ (t₂ , 2 ∷ []) ∷ []
transient-ref-example j env t t₁ t₂ c eqj l1 l2
  rewrite eqj
        | l1
        | timeLt-trans t t₁ t₂ l1 l2
        | timeLeq-refl t₁
        | timeEq-refl t₂
        | timeLt⇒timeEq-false t₁ t₂ l2
        | timeEq-refl t₁
  = refl

-- upstream race: a ref-triggered inner that emits synchronously mid-fan-out
-- inherits the trigger's instant — it batches WITH the fan-out, never
-- splits it
upstream-race-example : (j : ℕ) (env : Env) (t t₁ c : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ []) c
  → timeLt t t₁ ≡ true
  → batchSpec
      (emits (⟦ mergeE (shareE false j)
                 (mergeAllE (mapS (λ _ → ofE (9 ∷ [])) (shareE false j)))
              ⟧ env t))
    ≡ (t₁ , 1 ∷ 9 ∷ []) ∷ []
upstream-race-example j env t t₁ c eqj l1
  rewrite eqj | l1 | timeLeq-refl t₁
  = allAt-batch t₁ 1 ((t₁ , 9) ∷ []) (aa∷ aa[])

-- tick-0 ref spawns: a ref spawned by a STATIC trigger subscribes at the
-- frame itself and behaves exactly like a static ref of the same share
frame-spawn-example : (j : ℕ) (env : Env) (t t₁ c : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ []) c
  → timeLt t t₁ ≡ true
  → batchSpec
      (emits (⟦ letShareE (shareE false j)
                  (mergeE (shareE true 0)
                          (mergeAllE (mapS (λ _ → shareE false 0)
                                           (ofE (0 ∷ []))))) ⟧ env t))
    ≡ (t₁ , 1 ∷ 1 ∷ []) ∷ []
frame-spawn-example j env t t₁ c eqj l1
  rewrite timeEq-refl t
        | filterAfter-absorb t t (emits (snd (env j))) (timeLeq-refl t)
        | eqj | l1
        | timeLeq-refl t₁
  = allAt-batch t₁ 1 ((t₁ , 1) ∷ []) (aa∷ aa[])

-- stateful folds over ref fan-outs: scan threads its accumulator through
-- the fan-out in delivery order, within and ACROSS batches (ratified:
-- exactly rxjs scan)
scan-fanout-example : (j : ℕ) (env : Env) (t t₁ t₂ c : Time)
  → snd (env j) ≡ obs ((t₁ , 5) ∷ (t₂ , 6) ∷ []) c
  → timeLt t t₁ ≡ true → timeLt t₁ t₂ ≡ true
  → batchSpec
      (emits (⟦ scanE (λ acc _ → suc acc) 0 (nRefs 2 j) ⟧ env t))
    ≡ (t₁ , 1 ∷ 2 ∷ []) ∷ (t₂ , 3 ∷ 4 ∷ []) ∷ []
scan-fanout-example j env t t₁ t₂ c eqj l1 l2
  rewrite eqj
        | l1
        | timeLt-trans t t₁ t₂ l1 l2
        | timeLeq-refl t₁
        | timeLt⇒timeLeq-flip-false t₁ t₂ l2
        | timeLeq-refl t₂
        | timeEq-refl t₂
        | timeLt⇒timeEq-false t₁ t₂ l2
        | timeEq-refl t₁
  = refl

-- multi-value async arrival units: an async inner's whole synchronous
-- burst is one unit at the trigger's instant — one batch
multi-value-unit-example : (j : ℕ) (env : Env) (t t₁ c : Time)
  → snd (env j) ≡ obs ((t₁ , 1) ∷ []) c
  → timeLt t t₁ ≡ true
  → batchSpec
      (emits (⟦ mergeAllE (mapS (λ v → ofE (v ∷ 9 ∷ [])) (shareE false j))
              ⟧ env t))
    ≡ (t₁ , 1 ∷ 9 ∷ []) ∷ []
multi-value-unit-example j env t t₁ c eqj l1
  rewrite eqj | l1
  = allAt-batch t₁ 1 ((t₁ , 9) ∷ []) (aa∷ aa[])
