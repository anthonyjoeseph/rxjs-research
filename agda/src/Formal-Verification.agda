-- THE ENTRYPOINT. The one theorem this repository exists to prove:
--
--   formal-verification :
--     ∀ {n} (em : Emissions n) (e : Exp n) → Canonical e
--     → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
--
-- The clairvoyant referee (Spec/) and the blind machine
-- (Implementation/) agree on every program, on every run.
--
-- `formal-verification` is a VALUE, not a postulate: its proof term is
-- real, and every remaining gap is a named postulate below, consumed by
-- the proof. A postulate that cannot be proven as stated is a spec bug
-- to rework, not work around.
--
-- The bridge (`groupsOf`, `stamped`) is fully DEFINED, and the theorem
-- statement already HOLDS BY COMPUTATION on concrete programs — see the
-- refl-proofs at the bottom (`diamond-counting` is a literal instance
-- of `counting-recovers`, checked by normalization). What remains is
-- the generalization over all canonical programs.
module Formal-Verification where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous

------------------------------------------------------------------------
-- the bridge between the two worlds: the referee's grouped view.
--
-- The machine's own experience is the flattened output stream (`run`
-- concatenates it away); the referee keeps the responses grouped BY
-- INPUT — and since flatten places input j at tick j (frame = 0, async
-- k = k+1, endSlot i = K+1+i), stamping is just: group j's values get
-- time (j , 0).

groupsGo : {I O : Set} (m : Machine I O) → State m → List I → List (List O)
groupsGo m s []       = []
groupsGo m s (i ∷ is) = snd (step m s i) ∷ groupsGo m (fst (step m s i)) is

groupsOf : {I O : Set} → Machine I O → List I → List (List O)
groupsOf m = groupsGo m (start m)

concatL : {A : Set} → List (List A) → List A
concatL = concatMap (λ g → g)

-- PROVEN: flattening the referee's grouped view is exactly the
-- machine's own flattened experience — the grouping is knowledge the
-- referee ADDS, never information the machine had
feed-groups : {I O : Set} (m : Machine I O) (s : State m) (is : List I)
            → snd (feed m s is) ≡ concatL (groupsGo m s is)
feed-groups m s []       = refl
feed-groups m s (i ∷ is) =
  cong (λ ys → snd (step m s i) ++ ys) (feed-groups m (fst (step m s i)) is)

run-groups : {I O : Set} (m : Machine I O) (is : List I)
           → run m is ≡ concatL (groupsOf m is)
run-groups m = feed-groups m (start m)

-- the referee's clock, re-attached: group j's values at time (j , 0)
stampFrom : ℕ → List (List (Emit Val)) → List (Time × Val)
stampFrom k []       = []
stampFrom k (g ∷ gs) =
  map (λ v → (k , 0) , v) (concatMap (λ e → values (snd e)) g)
    ++ stampFrom (suc k) gs

-- the implementation's protocol trace, stamped — fully DEFINED
stamped : {n : ℕ} → Emissions n → Exp n → List (Time × Val)
stamped em e = stampFrom 0 (groupsOf (compile e) (flatten em))

------------------------------------------------------------------------
-- the remaining holes

postulate
  -- the validity domain (v1: Canonical + the fenced order corners):
  -- non-resetting shares, registration-canonical trees. To be defined
  -- as a recursive predicate; its exact conditions are settled by the
  -- proofs below (what they need is what it says).
  Canonical : {n : ℕ} → Exp n → Set

  -- THE TWO HALVES OF THE PROOF ------------------------------------

  -- (1) counting correctness: the batching machine, fed the pipeline's
  -- emits blind, flushes exactly the groups the referee finds by
  -- stamping the same emits and comparing clocks
  -- (v1: endgame — machine ≡ batchSpec ∘ stamp, proven for fragments)
  counting-recovers :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → impl-batchSimultaneous em e ≡ batchSpecL (stamped em e)

  -- (2) trace faithfulness: stamping the implementation's trace yields
  -- EXACTLY the spec's timed denotation — value for value, instant for
  -- instant (v1: traceOf-ok + stamp-sound)
  trace-faithful :
    {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
    → stamped em e ≡ list (⟦ e ⟧ em ρ₀ t₀)

------------------------------------------------------------------------
-- THE THEOREM

formal-verification :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
formal-verification em e can =
  trans (counting-recovers em e can)
        (cong batchSpecL (trace-faithful em e can))

------------------------------------------------------------------------
-- sanity instances, PROVEN BY COMPUTATION: the whole implementation
-- pipeline — compile, the joins' scans, the counting machine — reduces
-- on concrete programs, and the theorem's two sides literally agree.

-- a cold source alone: one frame batch
em₀ : Emissions 0
em₀ = emissions [] []

of-batches : impl-batchSimultaneous em₀ (ofE (1 ∷ 2 ∷ []))
           ≡ (1 ∷ 2 ∷ []) ∷ []
of-batches = refl

-- THE DIAMOND: one source, two arms, one .next(5) — ONE batch [5, 6]
diamondE : Exp 1
diamondE = mergeE (srcE fzero) (mapE suc (srcE fzero))

em₁ : Emissions 1
em₁ = emissions ([] ∷ []) ((fzero , 5) ∷ [])

diamond-batches : impl-batchSimultaneous em₁ diamondE
                ≡ (5 ∷ 6 ∷ []) ∷ []
diamond-batches = refl

-- the referee's view of the same run: both arm values at tick 1
diamond-stamped : stamped em₁ diamondE
                ≡ ((1 , 0) , 5) ∷ ((1 , 0) , 6) ∷ []
diamond-stamped = refl

-- a LITERAL INSTANCE of counting-recovers, by normalization: the blind
-- machine and the clock-reading referee compute the same batches
diamond-counting : impl-batchSimultaneous em₁ diamondE
                 ≡ batchSpecL (stamped em₁ diamondE)
diamond-counting = refl

-- take(1) cutting the diamond MID-INSTANT — the corner v1 fenced behind
-- the runMemCut postulate — and the two sides STILL agree
take-batches : impl-batchSimultaneous em₁ (takeE 1 diamondE)
             ≡ (5 ∷ []) ∷ []
take-batches = refl

take-counting : impl-batchSimultaneous em₁ (takeE 1 diamondE)
              ≡ batchSpecL (stamped em₁ (takeE 1 diamondE))
take-counting = refl

-- a stateful fold across instants
scan-batches : impl-batchSimultaneous
                 (emissions ([] ∷ []) ((fzero , 5) ∷ (fzero , 2) ∷ []))
                 (scanE _+_ 0 (srcE fzero))
             ≡ (5 ∷ []) ∷ (7 ∷ []) ∷ []
scan-batches = refl

-- spawned inners COALESCE: each .next(5) spawns of([5,5]), whose flush
-- rides the trigger's instant — one batch [5, 5]
mergeMap-batches : impl-batchSimultaneous em₁
                     (mergeMapE (λ v → ofE (v ∷ v ∷ [])) (srcE fzero))
                 ≡ (5 ∷ 5 ∷ []) ∷ []
mergeMap-batches = refl

-- two sources, interleaved instants, and the counting instance again
em₂ : Emissions 2
em₂ = emissions ([] ∷ [] ∷ [])
                ((fzero , 1) ∷ (fsuc fzero , 2) ∷ (fzero , 3) ∷ [])

merge2E : Exp 2
merge2E = mergeE (srcE fzero) (srcE (fsuc fzero))

merge2-batches : impl-batchSimultaneous em₂ merge2E
               ≡ (1 ∷ []) ∷ (2 ∷ []) ∷ (3 ∷ []) ∷ []
merge2-batches = refl

merge2-counting : impl-batchSimultaneous em₂ merge2E
                ≡ batchSpecL (stamped em₂ merge2E)
merge2-counting = refl

-- and the diamond under the full theorem, once Canonical holds for it
postulate
  diamond-canonical : Canonical diamondE

diamond-verified :
  (em : Emissions 1)
  → impl-batchSimultaneous em diamondE ≡ spec-batchSimultaneous em diamondE
diamond-verified em = formal-verification em diamondE diamond-canonical
