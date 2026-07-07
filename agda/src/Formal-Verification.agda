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
-- the validity domain: REGISTRATION-CANONICAL trees (v1's ratified
-- fence, now a real predicate). Share semantics themselves are
-- untouched — this is a syntactic discipline: per letShareE binder,
-- the slot's pre-order-FIRST ref is its connecting ref (flagged true,
-- exactly rxjs's "first subscriber triggers connect") and every later
-- ref is flagged false. The relation threads "is the connecting ref
-- still owed" per slot through the tree in registration (pre-order)
-- order; a spawn arm written left of its slot's connecting static arm
-- fails, matching v1's ranked-delivery derivation. mapS templates are
-- quantified over their trigger value and may not change the state (a
-- spawned ref can never connect).

lookupB : List Bool → ℕ → Bool
lookupB []       _       = false
lookupB (b ∷ bs) zero    = b
lookupB (b ∷ bs) (suc i) = lookupB bs i

clearB : List Bool → ℕ → List Bool
clearB []       _       = []
clearB (b ∷ bs) zero    = false ∷ bs
clearB (b ∷ bs) (suc i) = b ∷ clearB bs i

data CanE {n : ℕ} : List Bool → Exp n → List Bool → Set
data CanS {n : ℕ} : List Bool → ExpS n → List Bool → Set
data CanL {n : ℕ} : List Bool → List (Exp n) → List Bool → Set

data CanE {n} where
  can-src   : {w : List Bool} {i : Fin n} → CanE w (srcE i) w
  can-empty : {w : List Bool} → CanE w emptyE w
  can-of    : {w : List Bool} {vs : List Val} → CanE w (ofE vs) w
  -- a ref's flag must be exactly what its slot is owed: the first
  -- (pre-order) ref connects and consumes the debt, later refs are late
  can-ref   : {w : List Bool} {i : ℕ} → ltℕ i (length w) ≡ true
            → CanE w (shareE (lookupB w i) i) (clearB w i)
  can-let   : {w w₁ w₂ : List Bool} {b₀ : Bool} {s b : Exp n}
            → CanE w s w₁ → CanE (true ∷ w₁) b (b₀ ∷ w₂)
            → CanE w (letShareE s b) w₂
  can-map   : {w w′ : List Bool} {f : Val → Val} {e : Exp n}
            → CanE w e w′ → CanE w (mapE f e) w′
  can-take  : {w w′ : List Bool} {k : ℕ} {e : Exp n}
            → CanE w e w′ → CanE w (takeE k e) w′
  can-scan  : {w w′ : List Bool} {f : Val → Val → Val} {z : Val} {e : Exp n}
            → CanE w e w′ → CanE w (scanE f z e) w′
  can-mergeAll   : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (mergeAllE ss) w′
  can-concatAll  : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (concatAllE ss) w′
  can-switchAll  : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (switchAllE ss) w′
  can-exhaustAll : {w w′ : List Bool} {ss : ExpS n}
                 → CanS w ss w′ → CanE w (exhaustAllE ss) w′

data CanS {n} where
  can-ofS  : {w w′ : List Bool} {es : List (Exp n)}
           → CanL w es w′ → CanS w (ofS es) w′
  can-mapS : {w w′ : List Bool} {f : Val → Exp n} {e : Exp n}
           → CanE w e w′
           → ((v : Val) → CanE w′ (f v) w′)
           → CanS w (mapS f e) w′

data CanL {n} where
  canl-[] : {w : List Bool} → CanL w [] w
  canl-∷  : {w w₁ w₂ : List Bool} {e : Exp n} {es : List (Exp n)}
          → CanE w e w₁ → CanL w₁ es w₂ → CanL w (e ∷ es) w₂

Canonical : {n : ℕ} → Exp n → Set
Canonical e = CanE [] e []

------------------------------------------------------------------------
-- the remaining holes

postulate
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
    → stamped em e ≡ emits (⟦ e ⟧ em ρ₀ t₀)

------------------------------------------------------------------------
-- THE THEOREM

formal-verification :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
formal-verification em e can =
  trans (counting-recovers em e can)
        (cong batchSpecL (trace-faithful em e can))

------------------------------------------------------------------------
-- THE THEOREM STATEMENT, PROVEN BY COMPUTATION: both sides are now
-- fully defined, so on concrete programs Agda normalizes the ENTIRE
-- pipeline — compile, the joins' scans, the counting machine on one
-- side; the timed denotation and the clock-grouping referee on the
-- other — and they literally agree. Every instance below is a data
-- point the general theorem can no longer be false at.

-- a cold source alone: one frame batch
em₀ : Emissions 0
em₀ = emissions [] []

of-full : impl-batchSimultaneous em₀ (ofE (1 ∷ 2 ∷ []))
        ≡ spec-batchSimultaneous em₀ (ofE (1 ∷ 2 ∷ []))
of-full = refl

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

diamond-full : impl-batchSimultaneous em₁ diamondE
             ≡ spec-batchSimultaneous em₁ diamondE
diamond-full = refl

-- the two HALVES of the general proof, instantiated by normalization:
-- the referee's stamped view of the machine's trace, the counting
-- machine recovering its batches, and the stamped trace agreeing with
-- the timed denotation — each a literal instance of its postulate
diamond-stamped : stamped em₁ diamondE
                ≡ ((1 , 0) , 5) ∷ ((1 , 0) , 6) ∷ []
diamond-stamped = refl

diamond-counting : impl-batchSimultaneous em₁ diamondE
                 ≡ batchSpecL (stamped em₁ diamondE)
diamond-counting = refl

diamond-trace : stamped em₁ diamondE ≡ emits (⟦ diamondE ⟧ em₁ ρ₀ t₀)
diamond-trace = refl

-- Canonical holds for the diamond (no shares — the discipline is
-- vacuous), so the general theorem instantiates
diamond-canonical : Canonical diamondE
diamond-canonical =
  can-mergeAll (can-ofS (canl-∷ can-src (canl-∷ (can-map can-src) canl-[])))

diamond-verified :
  (em : Emissions 1)
  → impl-batchSimultaneous em diamondE ≡ spec-batchSimultaneous em diamondE
diamond-verified em = formal-verification em diamondE diamond-canonical

-- take(1) cutting the diamond MID-INSTANT — the corner v1 fenced behind
-- the runMemCut postulate — and the two sides STILL agree
take-full : impl-batchSimultaneous em₁ (takeE 1 diamondE)
          ≡ spec-batchSimultaneous em₁ (takeE 1 diamondE)
take-full = refl

take-batches : impl-batchSimultaneous em₁ (takeE 1 diamondE)
             ≡ (5 ∷ []) ∷ []
take-batches = refl

-- a stateful fold across instants
scan-full : impl-batchSimultaneous
              (emissions ([] ∷ []) ((fzero , 5) ∷ (fzero , 2) ∷ []))
              (scanE _+_ 0 (srcE fzero))
          ≡ spec-batchSimultaneous
              (emissions ([] ∷ []) ((fzero , 5) ∷ (fzero , 2) ∷ []))
              (scanE _+_ 0 (srcE fzero))
scan-full = refl

-- spawned inners COALESCE: each .next(5) spawns of([5,5]), whose flush
-- rides the trigger's instant — one batch [5, 5]
mergeMap-full : impl-batchSimultaneous em₁
                  (mergeMapE (λ v → ofE (v ∷ v ∷ [])) (srcE fzero))
              ≡ spec-batchSimultaneous em₁
                  (mergeMapE (λ v → ofE (v ∷ v ∷ [])) (srcE fzero))
mergeMap-full = refl

mergeMap-batches : impl-batchSimultaneous em₁
                     (mergeMapE (λ v → ofE (v ∷ v ∷ [])) (srcE fzero))
                 ≡ (5 ∷ 5 ∷ []) ∷ []
mergeMap-batches = refl

-- two sources, interleaved instants
em₂ : Emissions 2
em₂ = emissions ([] ∷ [] ∷ [])
                ((fzero , 1) ∷ (fsuc fzero , 2) ∷ (fzero , 3) ∷ [])

merge2E : Exp 2
merge2E = mergeE (srcE fzero) (srcE (fsuc fzero))

merge2-full : impl-batchSimultaneous em₂ merge2E
            ≡ spec-batchSimultaneous em₂ merge2E
merge2-full = refl

merge2-batches : impl-batchSimultaneous em₂ merge2E
               ≡ (1 ∷ []) ∷ (2 ∷ []) ∷ (3 ∷ []) ∷ []
merge2-batches = refl

-- THE CASCADE: concat(take 1 (src), of(9)) — the queued cold leg
-- subscribes at the take's cut, INSIDE the trigger's instant
cascade-full : impl-batchSimultaneous em₁
                 (concatE (takeE 1 (srcE fzero)) (ofE (9 ∷ [])))
             ≡ spec-batchSimultaneous em₁
                 (concatE (takeE 1 (srcE fzero)) (ofE (9 ∷ [])))
cascade-full = refl

cascade-batches : impl-batchSimultaneous em₁
                    (concatE (takeE 1 (srcE fzero)) (ofE (9 ∷ [])))
                ≡ (5 ∷ 9 ∷ []) ∷ []
cascade-batches = refl

-- switch cuts a live inner; exhaust drops arrivals while one is open
emSE : Emissions 2
emSE = emissions ([] ∷ [] ∷ [])
                 ((fzero , 1) ∷ (fzero , 2) ∷ (fsuc fzero , 7) ∷ [])

switch-full : impl-batchSimultaneous emSE
                (switchAllE (mapS (λ _ → srcE (fsuc fzero)) (srcE fzero)))
            ≡ spec-batchSimultaneous emSE
                (switchAllE (mapS (λ _ → srcE (fsuc fzero)) (srcE fzero)))
switch-full = refl

exhaust-full : impl-batchSimultaneous emSE
                 (exhaustAllE (mapS (λ _ → srcE (fsuc fzero)) (srcE fzero)))
             ≡ spec-batchSimultaneous emSE
                 (exhaustAllE (mapS (λ _ → srcE (fsuc fzero)) (srcE fzero)))
exhaust-full = refl

-- THE SHARE DIAMOND: bind a hot slot, fan out two refs (the first
-- connecting), merge — each source event delivers ONE batch [v, v+1]
shareDiamondE : Exp 1
shareDiamondE = letShareE (srcE fzero)
                  (mergeE (shareE true 0) (mapE suc (shareE false 0)))

share-diamond-batches : impl-batchSimultaneous em₁ shareDiamondE
                      ≡ (5 ∷ 6 ∷ []) ∷ []
share-diamond-batches = refl

share-diamond-full : impl-batchSimultaneous em₁ shareDiamondE
                   ≡ spec-batchSimultaneous em₁ shareDiamondE
share-diamond-full = refl

-- and it is registration-canonical: the pre-order-first ref carries the
-- connecting flag, the second is late
share-diamond-canonical : Canonical shareDiamondE
share-diamond-canonical =
  can-let can-src
    (can-mergeAll (can-ofS
      (canl-∷ (can-ref refl)
        (canl-∷ (can-map (can-ref refl)) canl-[]))))

-- LATE-JOIN GROWTH (the README's growth law): one static ref plus one
-- ref spawned by another source's event between the two source events —
-- [7] then [8, 8]
growthE : Exp 2
growthE = letShareE (srcE fzero)
            (mergeE (shareE true 0)
                    (mergeAllE (mapS (λ _ → shareE false 0)
                                     (srcE (fsuc fzero)))))

emG : Emissions 2
emG = emissions ([] ∷ [] ∷ [])
                ((fzero , 7) ∷ (fsuc fzero , 0) ∷ (fzero , 8) ∷ [])

growth-batches : impl-batchSimultaneous emG growthE
               ≡ (7 ∷ []) ∷ (8 ∷ 8 ∷ []) ∷ []
growth-batches = refl

growth-full : impl-batchSimultaneous emG growthE
            ≡ spec-batchSimultaneous emG growthE
growth-full = refl

growth-canonical : Canonical growthE
growth-canonical =
  can-let can-src
    (can-mergeAll (can-ofS
      (canl-∷ (can-ref refl)
        (canl-∷ (can-mergeAll (can-mapS can-src (λ v → can-ref refl)))
                canl-[]))))
