-- README SEMANTICS THEOREMS — the root README's semantics-by-edge-case,
-- each a top-line result stated against the spec (ported from v1, where
-- all ten were proven).  A statement that will not prove is a drift
-- between the README and the Agda spec: exactly what this file catches.
--
-- Three universal laws over the whole grammar, then seven quantified
-- instances (the shape is the truth; the numerals are free).  The
-- instances compare only VALUES (emitValues) — ids and protocol traffic
-- are the other theorem files' business.
module Readme-Theorems where

open import Data.Nat     using (ℕ; _≤_)
open import Data.List    using (List; []; _∷_; _++_; map; take; concat; length)
open import Data.Vec     using ([]; _∷_)     -- contexts are Vecs; ∷/[] overload per type
open import Data.Fin     using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel; InstEmit; _at_from_; after_,_; hot)
open import Rx.Exp       using (Ty; Ctx; Closed; Val; Fn; Tm; nat̂; strmᵗ;
                                input; ofᵉ; mapᵉ; takeᵉ; mergeAllᵉ;
                                concatAllᵉ; exhaustAllᵉ; evalTm; applyFn)
open import Rx.Evaluator using (Slot; scripted; shared; Slots; evaluate)
open import Spec         using (spec-batchSimultaneous; valuesOf)

------------------------------------------------------------------
-- projections: a stream's values in delivery order (at A this is
-- the raw value stream; at List A, each batch's value list)
------------------------------------------------------------------

emitValues : ∀ {A : Set} → List (InstEmit A) → List A
emitValues []                     = []
emitValues ((es at _ from _) ∷ xs) = valuesOf es ++ emitValues xs

------------------------------------------------------------------
-- shorthands: merge as mergeAll∘of, and the tiny slot assignments
-- the instances run against
------------------------------------------------------------------

mergeOf : ∀ {n} {Γ : Ctx n} {t} → List (Closed Γ t) → Closed Γ t
mergeOf es = mergeAllᵉ (ofᵉ (map strmᵗ es))

hotOnce : ∀ {n} {Γ : Ctx n} {t} → Val Γ t → Slot Γ t
hotOnce v = scripted (hot ((after 0 , v) ∷ []))

oneSlot : ∀ {t} → Slot (t ∷ []) t → Slots (t ∷ [])
oneSlot s zero    = s
oneSlot s (suc ())

twoHots : ∀ {t} → Val (t ∷ t ∷ []) t → Val (t ∷ t ∷ []) t → Slots (t ∷ t ∷ [])
twoHots u v zero          = hotOnce u
twoHots u v (suc zero)    = hotOnce v
twoHots u v (suc (suc ()))

noSlots : Slots []
noSlots ()

------------------------------------------------------------------
-- THREE UNIVERSAL LAWS (over the whole grammar)
------------------------------------------------------------------

postulate
  -- Batch order is delivery order.  The flagship: batching only
  -- GROUPS — never reorders, never drops.  Flattening the batches
  -- recovers the raw value stream, for every program and driver.
  readme-batch-order-is-delivery-order :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    concat (emitValues (spec-batchSimultaneous (evaluate fuel e ins)))
      ≡ emitValues (evaluate fuel e ins)

  -- take counts values, even mid-batch: take k keeps the first k
  -- VALUES of the flat stream — never the first k batches — so it
  -- can cut a batch in half.
  readme-take-counts-values :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (k : ℕ)
      (e : Closed Γ t) (ins : Slots Γ) →
    concat (emitValues (spec-batchSimultaneous
                          (evaluate fuel (takeᵉ (nat̂ k) e) ins)))
      ≡ take k (concat (emitValues (spec-batchSimultaneous
                                      (evaluate fuel e ins))))

  -- One subscribe() call is one batch.  Fuel 0 runs only the
  -- subscribe frame — a single instant — so ANY program, however
  -- wired, yields at most one batch.  (Strictly stronger than v1's
  -- source-free version: arrivals cost fuel, defers included.)
  readme-one-subscribe-one-batch :
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    length (spec-batchSimultaneous (evaluate 0 e ins)) ≤ 1

------------------------------------------------------------------
-- SEVEN QUANTIFIED INSTANCES
------------------------------------------------------------------

-- the flagship diamond: a mapped copy of a source shares that
-- source's batch — whatever the value, whatever the map.
--   merge(s, s.map(f)) on s.next(v)  ≡  [[v, f v]]
diamondProgram : ∀ {t} → Fn (t ∷ []) [] [] [] t t → Closed (t ∷ []) t
diamondProgram f = mergeOf (input zero ∷ mapᵉ f (input zero) ∷ [])

-- each .next() call is its own instant: two hots fired at the same
-- tick are still two instants; the diamond on the first collapses,
-- the second is a separate root cause.
--   merge(a, a.map(f), b);  a.next(u) ≡ [u, f u];  b.next(v) ≡ [v]
eachNextProgram : ∀ {t} → Fn (t ∷ t ∷ []) [] [] [] t t → Closed (t ∷ t ∷ []) t
eachNextProgram f =
  mergeOf (input zero ∷ mapᵉ f (input zero) ∷ input (suc zero) ∷ [])

-- cascades inherit their trigger's instant: a spawned inner's WHOLE
-- synchronous burst joins the batch of the event that spawned it —
-- any burst (a list of open terms in the trigger value), any value.
--   merge(s, s.mergeMap(n => of(…n…)))  on s.next(v)  ≡  [[v, …v…]]
cascadeProgram : ∀ {t} → List (Fn (t ∷ []) [] [] [] t t) → Closed (t ∷ []) t
cascadeProgram ws =
  mergeOf (input zero ∷ mergeAllᵉ (mapᵉ (strmᵗ (ofᵉ ws)) (input zero)) ∷ [])

-- completion cascades inherit too: take(1) closes on the event, the
-- concat's queued leg subscribes at that same instant — final value,
-- close, and freshly subscribed value are one batch.
--   merge(s, concat(take(1)(s), of(w)));  s.next(u) ≡ [u, u, w];  s.next(v) ≡ [v]
completionProgram : ∀ {t} → Tm (t ∷ []) [] [] [] t → Closed (t ∷ []) t
completionProgram w =
  mergeOf (input zero
          ∷ concatAllᵉ (ofᵉ (strmᵗ (takeᵉ (nat̂ 1) (input zero))
                            ∷ strmᵗ (ofᵉ (w ∷ [])) ∷ []))
          ∷ [])

-- share: connect at first subscription, no replay.  The shared slot
-- connects once, at its first ref; values are not re-observable, so
-- the second ref gets nothing.
--   merge(shared, shared) where shared = of(v).share()  ≡  [[v]]
shareProgram : ∀ {t} → Closed (t ∷ []) t
shareProgram = mergeOf (input zero ∷ input zero ∷ [])

-- late subscribers see only later events — diamonds grow: each
-- trigger firing adds one live ref of the hot share, so a later
-- source value is seen with strictly growing multiplicity.
--   trigger; src.next(u) ≡ [u, u];  trigger; src.next(v) ≡ [v, v, v]
growthCtx : Ty → Ctx 3
growthCtx t = t ∷ t ∷ t ∷ []          -- src ∷ trigger ∷ shared src

growthProgram : ∀ {t} → Closed (growthCtx t) t
growthProgram =
  mergeOf (input (suc (suc zero))
          ∷ mergeAllᵉ (mapᵉ (strmᵗ (input (suc (suc zero)))) (input (suc zero)))
          ∷ [])

growthSlots : ∀ {t} (u v w x : Val (growthCtx t) t) → Slots (growthCtx t)
growthSlots u v w x zero =                              -- src: ticks 2 and 4
  scripted (hot ((after 1 , u) ∷ (after 1 , v) ∷ []))
growthSlots u v w x (suc zero) =                        -- trigger: ticks 1 and 3
  scripted (hot ((after 0 , w) ∷ (after 1 , x) ∷ []))
growthSlots u v w x (suc (suc zero)) = shared (input zero)
growthSlots u v w x (suc (suc (suc ())))

-- the serial joins mirror rxjs: exhaustMap over a synchronous burst
-- runs EVERY inner — a sync inner closes before the next arrival.
--   of(a, b).exhaustMap(n => of(g n))  ≡  [[g a, g b]]
serialProgram : ∀ {t} → Fn [] [] [] [] t t
              → Tm [] [] [] [] t → Tm [] [] [] [] t → Closed [] t
serialProgram g a b =
  exhaustAllᵉ (mapᵉ (strmᵗ (ofᵉ (g ∷ []))) (ofᵉ (a ∷ b ∷ [])))

postulate
  readme-diamond :
    ∀ {t} (f : Fn (t ∷ []) [] [] [] t t) (v : Val (t ∷ []) t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 1 (diamondProgram f) (oneSlot (hotOnce v))))
      ≡ (v ∷ applyFn f v ∷ []) ∷ []

  readme-each-next-own-instant :
    ∀ {t} (f : Fn (t ∷ t ∷ []) [] [] [] t t) (u v : Val (t ∷ t ∷ []) t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 2 (eachNextProgram f) (twoHots u v)))
      ≡ (u ∷ applyFn f u ∷ []) ∷ (v ∷ []) ∷ []

  readme-cascades-inherit :
    ∀ {t} (ws : List (Fn (t ∷ []) [] [] [] t t)) (v : Val (t ∷ []) t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 1 (cascadeProgram ws) (oneSlot (hotOnce v))))
      ≡ (v ∷ map (λ w → applyFn w v) ws) ∷ []

  readme-completion-cascades :
    ∀ {t} (w : Tm (t ∷ []) [] [] [] t) (u v : Val (t ∷ []) t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 2 (completionProgram w)
                   (oneSlot (scripted (hot ((after 0 , u) ∷ (after 0 , v) ∷ []))))))
      ≡ (u ∷ u ∷ evalTm w ∷ []) ∷ (v ∷ []) ∷ []

  readme-share-connect-no-replay :
    ∀ {t} (v : Tm (t ∷ []) [] [] [] t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 0 shareProgram (oneSlot (shared (ofᵉ (v ∷ []))))))
      ≡ (evalTm v ∷ []) ∷ []

  readme-late-join-growth :
    ∀ {t} (u v w x : Val (growthCtx t) t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 4 growthProgram (growthSlots u v w x)))
      ≡ (u ∷ u ∷ []) ∷ (v ∷ v ∷ v ∷ []) ∷ []

  readme-serial-joins-mirror-rxjs :
    ∀ {t} (g : Fn [] [] [] [] t t) (a b : Tm [] [] [] [] t) →
    emitValues (spec-batchSimultaneous
                 (evaluate 0 (serialProgram g a b) noSlots))
      ≡ (applyFn g (evalTm a) ∷ applyFn g (evalTm b) ∷ []) ∷ []
