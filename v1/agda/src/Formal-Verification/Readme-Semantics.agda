-- README SEMANTICS PROOFS — the root README.md's semantics-by-edge-case,
-- each a top-line result checked against the Agda spec.
--
-- These are STRUCTURAL truths, not unit tests: every statement quantifies
-- over the values and functions the README example happened to pick (the
-- `5` and the `×10` were never the point), and three of them are universal
-- over the WHOLE grammar. The concrete README examples are instances.
--
-- The single principle underneath all of them: an emission's `Time` in the
-- denotation IS the instant that caused it, and `batchSpec` groups by equal
-- time. So every claim is really about timestamps, and batching is an
-- order-preserving partition by time (`readme-batch-order-is-delivery-order`
-- is exactly that, made universal).
--
-- STATUS: all 10 proven, no postulates. The seven quantified instances hold by
-- computation (`refl`, except cascades-inherit which needs the equal-time merge
-- lemmas below); the batch-order and take-counts universal laws by induction on
-- `batchSpecL`; one-subscribe-one-batch by `bounded-t₀-length` (batching side)
-- composed with Readme-Semantics.Static.emits-static (the Exp 0 denotation emits
-- everything at t₀). A statement that will NOT prove is a drift between the
-- README and the Agda spec: exactly what this file exists to catch.
--
-- Every result below is hyperlinked from its section in README.md.
module Formal-Verification.Readme-Semantics where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Formal-Verification.Readme-Semantics.Static using (emits-static)

------------------------------------------------------------------------
-- source-slot names (read the driver's Fin n indices)

private
  s0 : {n : ℕ} → Fin (suc n)
  s0 = fzero

  s1 : {n : ℕ} → Fin (suc (suc n))
  s1 = fsuc fzero

  -- flatten a batched result back to its raw value stream
  flat : Subscription (List Val) → List Val
  flat = concatMap (λ xs → xs)

------------------------------------------------------------------------
-- LEMMAS: batching is an order-preserving, loss-free partition
--
-- The spine of the whole file. `batchSpecL` only groups a (sorted) timed
-- list by equal times; flattening the groups recovers the raw value stream
-- exactly. This is what makes "batch order = delivery order" true, and it
-- reduces "take counts values" to a take/map commutation.

private
  -- flushing the batcher's accumulator: everything already accumulated,
  -- then every remaining value in order
  batchGo-flat : (t : Time) (acc : List Val) (ys : List (Time × Val))
    → flat (batchGo t acc ys) ≡ acc ++ map snd ys
  batchGo-flat t acc []             = refl
  batchGo-flat t acc ((u , w) ∷ ys) with timeEq t u
  ... | true  = trans (batchGo-flat u (acc ++ (w ∷ [])) ys)
                      (++-assoc acc (w ∷ []) (map snd ys))
  ... | false = cong (acc ++_) (batchGo-flat u (w ∷ []) ys)

  batchSpecL-flat : (xs : List (Time × Val))
    → flat (batchSpecL xs) ≡ map snd xs
  batchSpecL-flat []             = refl
  batchSpecL-flat ((t , v) ∷ xs) = batchGo-flat t (v ∷ []) xs

  -- take and takeL are the same cut; map snd slides through it
  takeL-map-snd : (k : ℕ) (xs : List (Time × Val))
    → map snd (takeL k xs) ≡ take k (map snd xs)
  takeL-map-snd zero    xs       = refl
  takeL-map-snd (suc n) []       = refl
  takeL-map-snd (suc n) (x ∷ xs) = cong (snd x ∷_) (takeL-map-snd n xs)

  -- equal-time merging (used by cascades): a right-empty merge is identity,
  -- and merging an at-t head into an all-at-t list is a cons (ties favour
  -- the left operand, and everything shares time t)
  mergeL-nil-right : {A : Set} (xs : TimedObs A) → mergeL xs [] ≡ xs
  mergeL-nil-right []       = refl
  mergeL-nil-right (x ∷ xs) = refl

  cascade-merge : (t : Time) (v : Val) (l : List Val)
    → mergeL ((t , v) ∷ []) (map (λ x → (t , x)) l)
        ≡ (t , v) ∷ map (λ x → (t , x)) l
  cascade-merge t v []       = refl
  cascade-merge t v (z ∷ zs) rewrite timeLeq-refl t = refl

  -- batching an all-at-t list is exactly one batch: acc, then every value
  batchGo-const : (t : Time) (acc : List Val) (l : List Val)
    → batchGo t acc (map (λ x → (t , x)) l) ≡ (acc ++ l) ∷ []
  batchGo-const t acc []       = cong (λ z → z ∷ []) (sym (++-[] acc))
  batchGo-const t acc (z ∷ zs) rewrite timeEq-refl t =
    trans (batchGo-const t (acc ++ (z ∷ [])) zs)
          (cong (λ z′ → z′ ∷ []) (++-assoc acc (z ∷ []) zs))

  -- t₀ is the least time, so anything bounded by t₀ IS at t₀
  t₀-max-eq : (u : Time) → timeLeq u t₀ ≡ true → u ≡ t₀
  t₀-max-eq (zero  , zero)  p = refl
  t₀-max-eq (zero  , suc b) p = true≢false (sym p)
  t₀-max-eq (suc a , b)     p = true≢false (sym p)

  -- a list all at t₀ batches into exactly one group (its length is 1)…
  batchGo-t₀-len : (acc : List Val) (xs : TimedObs Val)
    → BoundedBy t₀ xs → length (batchGo t₀ acc xs) ≡ 1
  batchGo-t₀-len acc []             bb[]           = refl
  batchGo-t₀-len acc ((u , w) ∷ ys) (bb∷ le rest)
    rewrite t₀-max-eq u le | timeEq-refl t₀ = batchGo-t₀-len (acc ++ (w ∷ [])) ys rest

  -- …so a t₀-bounded emission stream yields at most one batch
  bounded-t₀-length : (xs : TimedObs Val)
    → BoundedBy t₀ xs → leqℕ (length (batchSpecL xs)) 1 ≡ true
  bounded-t₀-length []             bb[]           = refl
  bounded-t₀-length ((u , w) ∷ ys) (bb∷ le rest)
    rewrite t₀-max-eq u le | batchGo-t₀-len (w ∷ []) ys rest = refl

------------------------------------------------------------------------
-- THREE UNIVERSAL LAWS (over the whole grammar)
------------------------------------------------------------------------

-- Batch order is delivery order (README §"Batch order is delivery order").
-- The flagship: batching only GROUPS — it never reorders and never drops.
-- Flattening the batches recovers the denotation's raw value stream, for
-- every program and every driver. Every other claim rides on this.

readme-batch-order-is-delivery-order : {n : ℕ} (em : Emissions n) (e : Exp n)
  → flat (spec-batchSimultaneous em e) ≡ map snd (emits (⟦ e ⟧ em ρ₀ t₀))
readme-batch-order-is-delivery-order em e =
  batchSpecL-flat (emits (⟦ e ⟧ em ρ₀ t₀))

-- take counts values, even mid-batch (README §"take counts values, even mid-batch").
-- `take k` keeps the first k VALUES of the flat stream — never the first k
-- batches — so it can cut a batch in half. Universal: take commutes with
-- flattening, for any program. (⟦ takeE k e ⟧ = takeT k ⟦ e ⟧, whose emits
-- is takeL k of the source's emits, so this is batchSpecL-flat on both sides
-- glued by the take/map commutation.)

readme-take-counts-values : {n : ℕ} (em : Emissions n) (k : ℕ) (e : Exp n)
  → flat (spec-batchSimultaneous em (takeE k e))
      ≡ take k (flat (spec-batchSimultaneous em e))
readme-take-counts-values em k e =
  trans (batchSpecL-flat (takeL k xs))
        (trans (takeL-map-snd k xs)
               (cong (take k) (sym (batchSpecL-flat xs))))
  where xs = emits (⟦ e ⟧ em ρ₀ t₀)

-- One subscribe() call is one batch (README §"One subscribe() call is one batch").
-- A source-free program (Exp 0 — no subject can fire, so the whole run is the
-- subscription frame) lands in a single instant: at most one batch, however
-- it is wired.
--
-- The batching side (bounded-t₀-length) turns "every emission is at t₀" into
-- "≤ 1 batch"; the denotational side (Readme-Semantics.Static.emits-static:
-- an Exp 0 program emits everything at its subscription instant t₀) is proven
-- by induction on the source-free grammar.

readme-one-subscribe-one-batch : (em : Emissions 0) (e : Exp 0)
  → leqℕ (length (spec-batchSimultaneous em e)) 1 ≡ true
readme-one-subscribe-one-batch em e =
  bounded-t₀-length (emits (⟦ e ⟧ em ρ₀ t₀)) (emits-static em e)

------------------------------------------------------------------------
-- QUANTIFIED INSTANCES (the shape is the truth; the numerals are free)
------------------------------------------------------------------------

-- The flagship diamond (README §"The idea: provenance + batchSimultaneous").
-- A mapped copy of a source shares that source's batch — whatever the value,
-- whatever the map.
--
--   merge(s, s.map(f)) on s.next(v)  ≡  [[v, f v]]

diamondP : (Val → Val) → Exp 1
diamondP f = mergeE (srcE s0) (mapE f (srcE s0))

readme-diamond : (f : Val → Val) (v : Val)
  → spec-batchSimultaneous (emissions (pureV []) ((s0 , v) ∷ [])) (diamondP f)
      ≡ (v ∷ f v ∷ []) ∷ []
readme-diamond f v = refl

-- Each .next() call is its own instant (README §"Each .next() call is its own instant").
-- Two subjects fired back to back are two instants; a diamond on the first
-- collapses, the second subject is a separate root cause.
--
--   merge(a, a.map(f), b);  a.next(u) ≡ [u, f u];  b.next(v) ≡ [v]

eachNextP : (Val → Val) → Exp 2
eachNextP f = mergeAllE (ofS (srcE s0 ∷ mapE f (srcE s0) ∷ srcE s1 ∷ []))

readme-each-next-own-instant : (f : Val → Val) (u v : Val)
  → spec-batchSimultaneous
      (emissions (pureV []) ((s0 , u) ∷ (s1 , v) ∷ [])) (eachNextP f)
      ≡ (u ∷ f u ∷ []) ∷ (v ∷ []) ∷ []
readme-each-next-own-instant f u v = refl

-- Cascades inherit their trigger's instant (README §"Cascades inherit their trigger's instant").
-- A spawned inner's WHOLE synchronous burst joins the batch of the event
-- that spawned it — any burst g, any value v.
--
--   merge(s, s.mergeMap(n => of(g n)))  on s.next(v)  ≡  [v ∷ g v]

cascadeP : (Val → List Val) → Exp 1
cascadeP g = mergeAllE (ofS (srcE s0 ∷ mergeMapE (λ n → ofE (g n)) (srcE s0) ∷ []))

readme-cascades-inherit : (g : Val → List Val) (v : Val)
  → spec-batchSimultaneous (emissions (pureV []) ((s0 , v) ∷ [])) (cascadeP g)
      ≡ (v ∷ g v) ∷ []
readme-cascades-inherit g v =
  trans (cong batchSpecL emitsEq) (batchGo-const (1 , 0) (v ∷ []) (g v))
  where
    B : TimedObs Val
    B = map (λ x → ((1 , 0) , x)) (g v)
    -- the two spawned inners flush v (direct src) then g v (mergeMap), both
    -- at the source's instant (1,0); the trailing []-merges are identity
    emitsEq : mergeL (((1 , 0) , v) ∷ []) (mergeL (mergeL B []) [])
                ≡ ((1 , 0) , v) ∷ B
    emitsEq = trans (cong (mergeL (((1 , 0) , v) ∷ []))
                          (trans (mergeL-nil-right (mergeL B [])) (mergeL-nil-right B)))
                    (cascade-merge (1 , 0) v (g v))

-- Completion cascades inherit too (README §"Completion cascades inherit too").
-- When take(1) closes on an event, the concat's queued next leg subscribes
-- at that same instant — the final value, the close, and the freshly
-- subscribed value are one batch.
--
--   merge(s, concat(take(1)(s), of(w)));  s.next(u) ≡ [u, u, w];  s.next(v) ≡ [v]

completionP : Val → Exp 1
completionP w = mergeAllE (ofS (srcE s0 ∷ concatE (takeE 1 (srcE s0)) (ofE (w ∷ [])) ∷ []))

readme-completion-cascades : (u v w : Val)
  → spec-batchSimultaneous
      (emissions (pureV []) ((s0 , u) ∷ (s0 , v) ∷ [])) (completionP w)
      ≡ (u ∷ u ∷ w ∷ []) ∷ (v ∷ []) ∷ []
readme-completion-cascades u v w = refl

-- share: connect at first subscription, no replay (README §"share: connect at first subscription, no replay").
-- A share connects once, at its first subscriber; a hot stream does not
-- replay, so a second subscriber a moment later gets nothing. The source's
-- synchronous value reaches exactly one ref — whatever the value.
--
--   merge(shared, shared) where shared = of(v).share()  ≡  [[v]]

shareP : Val → Exp 0
shareP v = letShareE (ofE (v ∷ [])) (mergeAllE (ofS (shareE true 0 ∷ shareE false 0 ∷ [])))

readme-share-connect-no-replay : (v : Val)
  → spec-batchSimultaneous (emissions (pureV []) []) (shareP v)
      ≡ (v ∷ []) ∷ []
readme-share-connect-no-replay v = refl

-- Late subscribers see only later events — diamonds grow (README §"Late subscribers see only later events — diamonds grow").
-- Each trigger firing adds one live ref of a hot share (a trigger instant
-- alone is empty — no replay), so a later source value is seen with strictly
-- growing multiplicity. slot 0 = src, slot 1 = trigger.
--
--   trigger; src.next(u) ≡ [u, u];  trigger; src.next(v) ≡ [v, v, v]

growthP : Exp 2
growthP = letShareE (srcE s0)
            (mergeAllE (ofS ( shareE true 0
                            ∷ mergeMapE (λ _ → shareE false 0) (srcE s1)
                            ∷ [])))

readme-late-join-growth : (u v : Val)
  → spec-batchSimultaneous
      (emissions (pureV []) ((s1 , 0) ∷ (s0 , u) ∷ (s1 , 0) ∷ (s0 , v) ∷ [])) growthP
      ≡ (u ∷ u ∷ []) ∷ (v ∷ v ∷ v ∷ []) ∷ []
readme-late-join-growth u v = refl

-- The serial joins mirror rxjs (README §"The serial joins mirror rxjs").
-- exhaustMap over a synchronous burst runs EVERY inner: a sync inner closes
-- before the next arrival, so nothing is dropped. One frame, both inners.
--
--   of(v, w).exhaustMap(n => of(g n))  ≡  [[g v, g w]]

serialP : (Val → Val) → Val → Val → Exp 0
serialP g v w = exhaustAllE (mapS (λ n → ofE (g n ∷ [])) (ofE (v ∷ w ∷ [])))

readme-serial-joins-mirror-rxjs : (g : Val → Val) (v w : Val)
  → spec-batchSimultaneous (emissions (pureV []) []) (serialP g v w)
      ≡ (g v ∷ g w ∷ []) ∷ []
readme-serial-joins-mirror-rxjs g v w = refl
