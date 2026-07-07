-- The SPEC's batchSimultaneous: the referee. FULLY DEFINED — no
-- postulates in this file.
--
-- It receives the ENTIRE Emissions record — past and future — and may
-- "cheat" freely: read timestamps, look ahead, sort. Its job is to
-- define the right answer, not to be computable by a subscriber.
--
-- Shape: a timed denotation ⟦_⟧ maps every Exp to a TObs — its complete
-- timed emission history, WELL-FORMED BY CONSTRUCTION (sorted from the
-- subscription time, bounded by its close; the evidence travels inside
-- the record, so v1's separate denote-wf theorem is absorbed into the
-- types). batchSpec then groups equal times.
--
-- The technical device (v1's, kept): subscription-time-parameterized
-- denotation. ⟦ e ⟧ em ρ t is the observable obtained by subscribing e
-- at time t; an inner stream denotes a FUNCTION from subscription time
-- to observable (Inner) — a cold stream is literally "tell me when you
-- subscribe me". Cold values emit at the subscription time they are
-- handed; a join hands each inner its own subscription time (arrival,
-- or the previous close for the serial joins). Burst batching is
-- compositional by construction.
module Spec.Batch-Simultaneous where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList

------------------------------------------------------------------------
-- timed observables, inner streams, and share slots

TObs : Time → Set
TObs = TObsOf Val

-- a cold inner stream: subscription time → observable, well-formed AT
-- that time — the type carries what v1 called WFDen
Inner : Set
Inner = (u : Time) → TObs u

TObsS : Time → Set
TObsS = TObsOf Inner

-- a share environment assigns every slot its connection instant and its
-- connected emission history (well-formed at the connection)
Slot : Set
Slot = Σ Time TObs

Env : Set
Env = ℕ → Slot

extendEnv : Slot → Env → Env
extendEnv s ρ zero    = s
extendEnv s ρ (suc i) = ρ i

ρ₀ : Env
ρ₀ _ = t₀ ▹ emptyT t₀

------------------------------------------------------------------------
-- hot histories: subscribing at t sees the strict suffix after t

filterAfterT : {b : Time} (t : Time) → TObsOf Val b → TObs t
filterAfterT t o =
  tobs (filterAfterL t (emits o))
       (timeMax t (close o))
       (filterAfter-from t (emits o) (sorted o))
       (timeMax-left t (close o))
       (boundedBy-weaken (timeMax-right t (close o))
         (filterAfter-bounded t (emits o) (bounded o)))

-- what a ref subscribed at t sees of a slot connected at tc: the whole
-- connected history for the connecting ref subscribed at the connection
-- instant, the strict suffix otherwise (v1: refView)
refT : Bool → Slot → (t : Time) → TObs t
refT false (tc ▹ o) t = filterAfterT t o
refT true  (tc ▹ o) t with timeEq t tc in k
... | false = filterAfterT t o
... | true rewrite timeEq-sound t tc k =
  tobs (emits o) (timeMax tc (close o)) (sorted o)
       (timeMax-left tc (close o))
       (boundedBy-weaken (timeMax-right tc (close o)) (bounded o))

------------------------------------------------------------------------
-- the complete timed history of source subject i, DERIVED from the
-- world: its sync flush at t₀, its k-th async firing at tick k+1, its
-- completion at tick K+1+i where K = length asyncs (matching flatten's
-- serialization order exactly)

srcGo : {n : ℕ} → ℕ → Fin n → List (Fin n × Val) → TimedObs Val
srcGo k i []             = []
srcGo k i ((j , v) ∷ xs) with eqℕ (toℕ j) (toℕ i)
... | true  = ((k , 0) , v) ∷ srcGo (suc k) i xs
... | false = srcGo (suc k) i xs

srcGo-sorted : {n : ℕ} (k : ℕ) (i : Fin n) (xs : List (Fin n × Val))
  → SortedFrom (k , 0) (srcGo k i xs)
srcGo-sorted k i []             = sf[]
srcGo-sorted k i ((j , v) ∷ xs) with eqℕ (toℕ j) (toℕ i)
... | true  = sf∷ (timeLeq-refl (k , 0))
                  (sortedFrom-weaken (lt-head-leq k (suc k) 0 0 (ltℕ-suc k))
                    (srcGo-sorted (suc k) i xs))
... | false = sortedFrom-weaken (lt-head-leq k (suc k) 0 0 (ltℕ-suc k))
                (srcGo-sorted (suc k) i xs)

srcGo-bounded : {n : ℕ} (k : ℕ) (i : Fin n) (xs : List (Fin n × Val))
  → BoundedBy (k + length xs , 0) (srcGo k i xs)
srcGo-bounded k i [] = bb[]
srcGo-bounded k i ((j , v) ∷ xs) rewrite +-suc k (length xs)
  with eqℕ (toℕ j) (toℕ i)
... | true  = bb∷ (tick-leq k (suc (k + length xs))
                    (ltℕ⇒leqℕ k (suc (k + length xs))
                      (subst (λ z → ltℕ k z ≡ true) (+-suc k (length xs))
                        (leq-lt-suc k (length xs)))))
              (srcGo-bounded (suc k) i xs)
  where
    leq-lt-suc : (a b : ℕ) → ltℕ a (a + suc b) ≡ true
    leq-lt-suc zero    b = refl
    leq-lt-suc (suc a) b = leq-lt-suc a b
... | false = srcGo-bounded (suc k) i xs

srcT : {n : ℕ} → Fin n → Emissions n → TObs t₀
srcT {n} i em =
  tobs (map (λ v → (t₀ , v)) (lookupV (syncs em) i) ++ srcGo 1 i (asyncs em))
       ((suc (length (asyncs em)) + toℕ i) , 0)
       (append-sortedFrom _ _
         (const-sortedFrom t₀ (lookupV (syncs em) i))
         (const-bounded t₀ (lookupV (syncs em) i))
         (sortedFrom-weaken (t₀-least (1 , 0)) (srcGo-sorted 1 i (asyncs em)))
         (timeLeq-refl t₀))
       (t₀-least ((suc (length (asyncs em)) + toℕ i) , 0))
       (append-bounded _ _
         (boundedBy-weaken (t₀-least ((suc (length (asyncs em)) + toℕ i) , 0))
           (const-bounded t₀ (lookupV (syncs em) i)))
         (boundedBy-weaken
           (tick-leq (suc (length (asyncs em)))
                     (suc (length (asyncs em)) + toℕ i)
                     (leqℕ-plus (suc (length (asyncs em))) (toℕ i)))
           (srcGo-bounded 1 i (asyncs em))))

------------------------------------------------------------------------
-- the pointwise primitives

ofT : List Val → (t : Time) → TObs t
ofT vs t =
  tobs (map (λ v → (t , v)) vs) t
       (const-sortedFrom t vs) (timeLeq-refl t) (const-bounded t vs)

mapT : (Val → Val) → {t : Time} → TObs t → TObs t
mapT f o =
  tobs (mapL f (emits o)) (close o)
       (mapL-sortedFrom f (emits o) (sorted o))
       (closeAt o)
       (mapL-bounded f (emits o) (bounded o))

scanT : (Val → Val → Val) → Val → {t : Time} → TObs t → TObs t
scanT f z o =
  tobs (scanL f z (emits o)) (close o)
       (scanL-sortedFrom f z (emits o) (sorted o))
       (closeAt o)
       (scanL-bounded f z (emits o) (bounded o))

takeT : ℕ → {t : Time} → TObs t → TObs t
takeT n {t} o =
  tobs (takeL n (emits o))
       (takeCloseL t n (emits o) (close o))
       (take-sortedFrom n (emits o) (sorted o))
       (take-closeAt t n (emits o) (close o) (sorted o) (bounded o) (closeAt o))
       (take-bounded t n (emits o) (close o) (sorted o) (bounded o))

------------------------------------------------------------------------
-- mergeAll: subscribe every inner at its arrival, merge everything.
-- The inner's own well-formedness needs no side hypothesis — it is a
-- field of its type.

mergeAllL : TimedObs Inner → TimedObs Val
mergeAllL []             = []
mergeAllL ((a , d) ∷ os) = mergeL (emits (d a)) (mergeAllL os)

maxCloses : Time → TimedObs Inner → Time
maxCloses c []             = c
maxCloses c ((a , d) ∷ os) = maxCloses (timeMax c (close (d a))) os

mergeAll-sorted : {t : Time} (os : TimedObs Inner)
  → SortedFrom t os → SortedFrom t (mergeAllL os)
mergeAll-sorted []             sf[]       = sf[]
mergeAll-sorted ((a , d) ∷ os) (sf∷ le s) =
  merge-sortedFrom _ _
    (sortedFrom-weaken le (sorted (d a)))
    (mergeAll-sorted os (sortedFrom-weaken le s))

maxCloses-lb : (c : Time) (os : TimedObs Inner)
  → timeLeq c (maxCloses c os) ≡ true
maxCloses-lb c []             = timeLeq-refl c
maxCloses-lb c ((a , d) ∷ os) =
  timeLeq-trans c (timeMax c (close (d a))) _
    (timeMax-left c (close (d a)))
    (maxCloses-lb (timeMax c (close (d a))) os)

mergeAll-bounded : (c : Time) (os : TimedObs Inner)
  → BoundedBy (maxCloses c os) (mergeAllL os)
mergeAll-bounded c []             = bb[]
mergeAll-bounded c ((a , d) ∷ os) =
  merge-bounded _ _
    (boundedBy-weaken
      (timeLeq-trans (close (d a)) (timeMax c (close (d a))) _
        (timeMax-right c (close (d a)))
        (maxCloses-lb (timeMax c (close (d a))) os))
      (bounded (d a)))
    (mergeAll-bounded (timeMax c (close (d a))) os)

------------------------------------------------------------------------
-- concatAll: subscribe each inner once the previous has closed (or at
-- its arrival, whichever is later — a queued inner starts at the
-- previous close)

concatAllL : Time → TimedObs Inner → TimedObs Val
concatAllL r []             = []
concatAllL r ((a , d) ∷ os) =
  emits (d (timeMax r a)) ++ concatAllL (close (d (timeMax r a))) os

concatAllClose : Time → TimedObs Inner → Time
concatAllClose r []             = r
concatAllClose r ((a , d) ∷ os) = concatAllClose (close (d (timeMax r a))) os

concatAllClose-lb : (r : Time) (os : TimedObs Inner)
  → timeLeq r (concatAllClose r os) ≡ true
concatAllClose-lb r []             = timeLeq-refl r
concatAllClose-lb r ((a , d) ∷ os) =
  timeLeq-trans r (close (d (timeMax r a))) _
    (timeLeq-trans r (timeMax r a) _
      (timeMax-left r a) (closeAt (d (timeMax r a))))
    (concatAllClose-lb (close (d (timeMax r a))) os)

concatAll-sorted : (r : Time) (os : TimedObs Inner)
  → SortedFrom r (concatAllL r os)
concatAll-sorted r []             = sf[]
concatAll-sorted r ((a , d) ∷ os) =
  append-sortedFrom _ _
    (sortedFrom-weaken (timeMax-left r a) (sorted (d (timeMax r a))))
    (bounded (d (timeMax r a)))
    (concatAll-sorted (close (d (timeMax r a))) os)
    (timeLeq-trans r (timeMax r a) _
      (timeMax-left r a) (closeAt (d (timeMax r a))))

concatAll-bounded : (r : Time) (os : TimedObs Inner)
  → BoundedBy (concatAllClose r os) (concatAllL r os)
concatAll-bounded r []             = bb[]
concatAll-bounded r ((a , d) ∷ os) =
  append-bounded _ _
    (boundedBy-weaken (concatAllClose-lb (close (d (timeMax r a))) os)
      (bounded (d (timeMax r a))))
    (concatAll-bounded (close (d (timeMax r a))) os)

------------------------------------------------------------------------
-- switchAll: an inner keeps its own subscription frame (a sync inner
-- runs to completion before the next arrival is processed) but its
-- async tail is cut when the next inner arrives

cutAt : {A : Set} → Time → Time → TimedObs A → TimedObs A
cutAt a nxt []             = []
cutAt a nxt ((u , v) ∷ xs) =
  if timeEq u a ∨ timeLt u nxt
  then ((u , v) ∷ cutAt a nxt xs)
  else cutAt a nxt xs

switchAllL : TimedObs Inner → TimedObs Val
switchAllL []                         = []
switchAllL ((a , d) ∷ [])             = emits (d a)
switchAllL ((a , d) ∷ (a′ , d′) ∷ os) =
  cutAt a a′ (emits (d a)) ++ switchAllL ((a′ , d′) ∷ os)

lastClose : Time → TimedObs Inner → Time
lastClose c []                 = c
lastClose c ((a , d) ∷ [])     = close (d a)
lastClose c ((a , d) ∷ x ∷ os) = lastClose c (x ∷ os)

cutAt-sortedFrom : {A : Set} {b : Time} (a nxt : Time) (xs : TimedObs A)
  → SortedFrom b xs → SortedFrom b (cutAt a nxt xs)
cutAt-sortedFrom a nxt []             sf[]       = sf[]
cutAt-sortedFrom a nxt ((u , v) ∷ xs) (sf∷ le s) with timeEq u a ∨ timeLt u nxt
... | true  = sf∷ le (cutAt-sortedFrom a nxt xs s)
... | false = cutAt-sortedFrom a nxt xs (sortedFrom-weaken le s)

cutAt-bounded-next : {A : Set} (a nxt : Time) (xs : TimedObs A)
  → timeLeq a nxt ≡ true → BoundedBy nxt (cutAt a nxt xs)
cutAt-bounded-next a nxt []             an = bb[]
cutAt-bounded-next a nxt ((u , v) ∷ xs) an
  with timeEq u a ∨ timeLt u nxt in k
... | false = cutAt-bounded-next a nxt xs an
... | true with ∨-split (timeEq u a) (timeLt u nxt) k
...   | left  eq rewrite timeEq-sound u a eq =
        bb∷ an (cutAt-bounded-next a nxt xs an)
...   | right lt =
        bb∷ (timeLt⇒timeLeq u nxt lt) (cutAt-bounded-next a nxt xs an)

switchAll-sorted : {t : Time} (os : TimedObs Inner)
  → SortedFrom t os → SortedFrom t (switchAllL os)
switchAll-sorted []             sf[]       = sf[]
switchAll-sorted ((a , d) ∷ []) (sf∷ le _) =
  sortedFrom-weaken le (sorted (d a))
switchAll-sorted {t} ((a , d) ∷ (a′ , d′) ∷ os)
                 (sf∷ le (sf∷ le′ s′)) =
  append-sortedFrom (cutAt a a′ (emits (d a))) (switchAllL ((a′ , d′) ∷ os))
    (cutAt-sortedFrom a a′ (emits (d a))
      (sortedFrom-weaken le (sorted (d a))))
    (cutAt-bounded-next a a′ (emits (d a)) le′)
    (switchAll-sorted ((a′ , d′) ∷ os) (sf∷ (timeLeq-refl a′) s′))
    (timeLeq-trans t a a′ le le′)

switchAll-bounded : {t : Time} (cS : Time) (os : TimedObs Inner)
  → SortedFrom t os → BoundedBy cS os
  → BoundedBy (timeMax cS (lastClose cS os)) (switchAllL os)
switchAll-bounded cS [] sf[] bb[] = bb[]
switchAll-bounded cS ((a , d) ∷ []) _ _ =
  boundedBy-weaken (timeMax-right cS (close (d a))) (bounded (d a))
switchAll-bounded cS ((a , d) ∷ (a′ , d′) ∷ os)
                  (sf∷ le s) (bb∷ lc (bb∷ lc′ b′)) =
  append-bounded (cutAt a a′ (emits (d a))) (switchAllL ((a′ , d′) ∷ os))
    (boundedBy-weaken
      (timeLeq-trans a′ cS (timeMax cS (lastClose cS ((a′ , d′) ∷ os)))
        lc′ (timeMax-left cS (lastClose cS ((a′ , d′) ∷ os))))
      (cutAt-bounded-next a a′ (emits (d a)) (sortedFrom-head s)))
    (switchAll-bounded cS ((a′ , d′) ∷ os) s (bb∷ lc′ b′))
  where
    sortedFrom-head : {A : Set} {b u : Time} {x : A} {xs : TimedObs A}
                    → SortedFrom b ((u , x) ∷ xs) → timeLeq b u ≡ true
    sortedFrom-head (sf∷ le _) = le

------------------------------------------------------------------------
-- exhaustAll: an arrival is dropped only while the previous accepted
-- inner is still open (an of-then-of burst emits both — sync inners
-- close immediately, so the next arrival is not "during" them)

exhaustAllL : Time → TimedObs Inner → TimedObs Val
exhaustAllL b []             = []
exhaustAllL b ((a , d) ∷ os) =
  if timeLt a b
  then exhaustAllL b os
  else (emits (d a) ++ exhaustAllL (close (d a)) os)

exhaustClose : Time → TimedObs Inner → Time
exhaustClose b []             = b
exhaustClose b ((a , d) ∷ os) =
  if timeLt a b
  then exhaustClose b os
  else exhaustClose (close (d a)) os

exhaustClose-lb : (b : Time) (os : TimedObs Inner)
  → timeLeq b (exhaustClose b os) ≡ true
exhaustClose-lb b []             = timeLeq-refl b
exhaustClose-lb b ((a , d) ∷ os) with timeLt a b in k
... | true  = exhaustClose-lb b os
... | false = timeLeq-trans b (close (d a)) _
    (timeLeq-trans b a _ (timeLt-false⇒timeLeq-flip a b k) (closeAt (d a)))
    (exhaustClose-lb (close (d a)) os)

exhaust-sorted : (b : Time) (os : TimedObs Inner)
  → SortedFrom b (exhaustAllL b os)
exhaust-sorted b []             = sf[]
exhaust-sorted b ((a , d) ∷ os) with timeLt a b in k
... | true  = exhaust-sorted b os
... | false = append-sortedFrom _ _
    (sortedFrom-weaken (timeLt-false⇒timeLeq-flip a b k) (sorted (d a)))
    (bounded (d a))
    (exhaust-sorted (close (d a)) os)
    (timeLeq-trans b a _ (timeLt-false⇒timeLeq-flip a b k) (closeAt (d a)))

exhaust-bounded : (b : Time) (os : TimedObs Inner)
  → BoundedBy (exhaustClose b os) (exhaustAllL b os)
exhaust-bounded b []             = bb[]
exhaust-bounded b ((a , d) ∷ os) with timeLt a b in k
... | true  = exhaust-bounded b os
... | false = append-bounded _ _
    (boundedBy-weaken (exhaustClose-lb (close (d a)) os) (bounded (d a)))
    (exhaust-bounded (close (d a)) os)

------------------------------------------------------------------------
-- the four joins, fused

mergeAllT : {t : Time} → TObsS t → TObs t
mergeAllT {t} S =
  tobs (mergeAllL (emits S))
       (maxCloses (close S) (emits S))
       (mergeAll-sorted (emits S) (sorted S))
       (timeLeq-trans t (close S) _ (closeAt S)
         (maxCloses-lb (close S) (emits S)))
       (mergeAll-bounded (close S) (emits S))

concatAllT : (t : Time) → TObsS t → TObs t
concatAllT t S =
  tobs (concatAllL t (emits S))
       (timeMax (close S) (concatAllClose t (emits S)))
       (concatAll-sorted t (emits S))
       (timeLeq-trans t (concatAllClose t (emits S)) _
         (concatAllClose-lb t (emits S))
         (timeMax-right (close S) (concatAllClose t (emits S))))
       (boundedBy-weaken
         (timeMax-right (close S) (concatAllClose t (emits S)))
         (concatAll-bounded t (emits S)))

switchAllT : {t : Time} → TObsS t → TObs t
switchAllT {t} S =
  tobs (switchAllL (emits S))
       (timeMax (close S) (lastClose (close S) (emits S)))
       (switchAll-sorted (emits S) (sorted S))
       (timeLeq-trans t (close S) _ (closeAt S)
         (timeMax-left (close S) (lastClose (close S) (emits S))))
       (switchAll-bounded (close S) (emits S) (sorted S) (bounded S))

exhaustAllT : (t : Time) → TObsS t → TObs t
exhaustAllT t S =
  tobs (exhaustAllL t (emits S))
       (timeMax (close S) (exhaustClose t (emits S)))
       (exhaust-sorted t (emits S))
       (timeLeq-trans t (exhaustClose t (emits S)) _
         (exhaustClose-lb t (emits S))
         (timeMax-right (close S) (exhaustClose t (emits S))))
       (boundedBy-weaken
         (timeMax-right (close S) (exhaustClose t (emits S)))
         (exhaust-bounded t (emits S)))

------------------------------------------------------------------------
-- stream-of-streams introduction

ofST : List Inner → (t : Time) → TObsS t
ofST ds t =
  tobs (map (λ d → (t , d)) ds) t
       (const-sortedFrom t ds) (timeLeq-refl t) (const-bounded t ds)

mapST : (Val → Inner) → {t : Time} → TObs t → TObsS t
mapST f o =
  tobs (mapL f (emits o)) (close o)
       (mapL-sortedFrom f (emits o) (sorted o))
       (closeAt o)
       (mapL-bounded f (emits o) (bounded o))

------------------------------------------------------------------------
-- the denotation: real structural recursion, no holes. ⟦ e ⟧ em ρ t =
-- the timed history observed by subscribing e at time t, under share
-- environment ρ, in the world em.
--
-- srcE is a hot slot connected at t₀ whose EVERY frame subscriber is
-- "connecting" (a subject flushes its frame values to every subscriber
-- present during subscribe); spawned refs see the strict suffix.

⟦_⟧ : {n : ℕ} → Exp n → Emissions n → Env → (t : Time) → TObs t
⟦_⟧S : {n : ℕ} → ExpS n → Emissions n → Env → (t : Time) → TObsS t
-- list denotation spelled out structurally (a `map` lambda would hide
-- the descent from the termination checker)
⟦_⟧L : {n : ℕ} → List (Exp n) → Emissions n → Env → List Inner

⟦ srcE i        ⟧ em ρ t = refT true (t₀ ▹ srcT i em) t
⟦ emptyE        ⟧ em ρ t = emptyT t
⟦ ofE vs        ⟧ em ρ t = ofT vs t
⟦ shareE f i    ⟧ em ρ t = refT f (ρ i) t
⟦ letShareE s b ⟧ em ρ t = ⟦ b ⟧ em (extendEnv (t ▹ ⟦ s ⟧ em ρ t) ρ) t
⟦ mapE f e      ⟧ em ρ t = mapT f (⟦ e ⟧ em ρ t)
⟦ takeE k e     ⟧ em ρ t = takeT k (⟦ e ⟧ em ρ t)
⟦ scanE f z e   ⟧ em ρ t = scanT f z (⟦ e ⟧ em ρ t)
⟦ mergeAllE ss  ⟧ em ρ t = mergeAllT (⟦ ss ⟧S em ρ t)
⟦ concatAllE ss ⟧ em ρ t = concatAllT t (⟦ ss ⟧S em ρ t)
⟦ switchAllE ss ⟧ em ρ t = switchAllT (⟦ ss ⟧S em ρ t)
⟦ exhaustAllE ss ⟧ em ρ t = exhaustAllT t (⟦ ss ⟧S em ρ t)

⟦ ofS es   ⟧S em ρ t = ofST (⟦ es ⟧L em ρ) t
⟦ mapS f e ⟧S em ρ t = mapST (λ v u → ⟦ f v ⟧ em ρ u) (⟦ e ⟧ em ρ t)

⟦ []     ⟧L em ρ = []
⟦ e ∷ es ⟧L em ρ = (λ u → ⟦ e ⟧ em ρ u) ∷ ⟦ es ⟧L em ρ

------------------------------------------------------------------------
-- batching: group equal adjacent times. Defined over the raw list so
-- the verification theorem can rewrite through it; sortedness-by-
-- construction is what makes "adjacent" the same as "equal anywhere".

batchGo : Time → List Val → List (Time × Val) → List (List Val)
batchGo t acc []             = acc ∷ []
batchGo t acc ((u , w) ∷ ys) =
  if timeEq t u
  then batchGo u (acc ++ (w ∷ [])) ys
  else acc ∷ batchGo u (w ∷ []) ys

batchSpecL : List (Time × Val) → List (List Val)
batchSpecL []             = []
batchSpecL ((t , v) ∷ xs) = batchGo t (v ∷ []) xs

batchSpec : {t : Time} → TObs t → Subscription (List Val)
batchSpec o = batchSpecL (emits o)

------------------------------------------------------------------------
-- THE SPEC. Whole-input, clairvoyant, one line.

spec-batchSimultaneous : {n : ℕ} → Emissions n → Exp n → Subscription (List Val)
spec-batchSimultaneous em e = batchSpec (⟦ e ⟧ em ρ₀ t₀)
