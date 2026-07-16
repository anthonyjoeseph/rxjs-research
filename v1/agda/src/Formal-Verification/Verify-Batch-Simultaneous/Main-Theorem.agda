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
-- real. The folder decomposes the work (see Roadmap.md for the plan):
--
--   Bridge.agda            — groupsOf / stamped / Canonical, all DEFINED
--   Counting-Recovers.agda — half one, a value over four postulates
--   Trace-Faithful.agda    — half two, a value over three postulates
--
-- A postulate that cannot be proven as stated is a spec bug to rework,
-- not work around. The theorem statement already HOLDS BY COMPUTATION
-- on concrete programs — see the refl-proofs at the bottom, where both
-- sides normalize end to end with no postulate in the path.
module Formal-Verification.Verify-Batch-Simultaneous.Main-Theorem where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList
open import Spec.Batch-Simultaneous
open import Implementation.Naive-Rx
open import Implementation.Batch-Simultaneous
open import Formal-Verification.Verify-Batch-Simultaneous.Bridge
open import Formal-Verification.Verify-Batch-Simultaneous.Counting-Recovers
open import Formal-Verification.Verify-Batch-Simultaneous.Trace-Faithful

------------------------------------------------------------------------
-- THE THEOREM

verify-batch-simultaneous :
  {n : ℕ} (em : Emissions n) (e : Exp n) → Canonical e
  → impl-batchSimultaneous em e ≡ spec-batchSimultaneous em e
verify-batch-simultaneous em e can =
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
diamond-verified em = verify-batch-simultaneous em diamondE diamond-canonical

-- take(1) cutting the diamond MID-INSTANT — the corner the previous generation fenced behind
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
