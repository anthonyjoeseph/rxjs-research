-- BATTERY-README (2026-08-06).  Concrete instance probes for all ten
-- postulates from Readme-Theorems:
--
--   readme-batch-order-is-delivery-order  (universal)
--   readme-take-counts-values             (universal)
--   readme-one-subscribe-one-batch        (universal)
--   readme-diamond
--   readme-each-next-own-instant
--   readme-cascades-inherit
--   readme-completion-cascades
--   readme-share-connect-no-replay
--   readme-late-join-growth
--   readme-serial-joins-mirror-rxjs
--
-- A REFUTATION HERE IS A SPEC-LEVEL FINDING — STOP AND REPORT.
-- Do not patch, adjust, or touch any file under agda/src/Spec/.
--
-- Each test is labelled:
--   LOAD-BEARING  — would fail if the named postulate were false at this instance
--   DEGENERATE    — passes even if the postulate were false (empty lists, 0≤_, etc.)
--
-- Every postulate has at least one LOAD-BEARING row.
--
-- Probe method: refl-checked equality at concrete values.  For the
-- universal laws, test at fuel=0 with no-slot programs (fast).  For
-- the quantified instances, test at the fuel level the postulate
-- specifies, with the smallest concrete values.
--
-- For fuel=1+ checks: these invoke drain and may be slow (seconds per
-- check) but should normalise since every evaluation is finite.
-- If a check times out the build, report it as BLOCKED.
module Battery-Readme where

open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; map; concat; take; length)
open import Data.Vec     using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin     using (zero; suc)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Timed; after_,_; hot; cold; InstEmit)
open import Rx.Exp       using (Ty; Ctx; natᵗ; Closed; Val; Fn; Tm;
                                nat̂; strmᵗ; varᵗ; input; ofᵉ; emptyᵉ;
                                mapᵉ; takeᵉ; mergeAllᵉ; concatAllᵉ; exhaustAllᵉ;
                                evalTm; applyFn)
open import Rx.Evaluator using (Slot; scripted; shared; Slots; evaluate)
open import Spec         using (spec-batchSimultaneous; valuesOf)

-- import Readme-Theorems for programs and helpers
open import Readme-Theorems
  using (emitValues; noSlots; hotOnce; oneSlot; twoHots;
         diamondProgram; eachNextProgram; cascadeProgram;
         completionProgram; shareProgram; growthCtx; growthProgram; growthSlots;
         serialProgram; mergeOf)

-- Empty context
Γ₀ : Ctx 0
Γ₀ = []ᵛ

-------------------------------------------------------------------
-- §1  UNIVERSAL LAW: readme-batch-order-is-delivery-order
--
-- concat (emitValues (spec-batchSimultaneous stream))
--   ≡ emitValues stream
-------------------------------------------------------------------

-- LOAD-BEARING: ofᵉ [3,7] emits at instant 0 in order 3 then 7.
-- spec-batchSimultaneous groups into one batch (3∷7∷[])∷[].
-- concat (3∷7∷[])∷[] = [3,7] = emitValues of raw stream.
-- Would fail if spec reordered (emitted 7 before 3 → [7,3] ≠ [3,7]).
_ : concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots)))
    ≡ emitValues (evaluate 0 (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots)
_ = refl

-- DEGENERATE: emptyᵉ emits nothing; concat [] = [] = [] trivially.
-- Nothing in the batching or ordering mechanism is exercised.
_ : concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (emptyᵉ {Γ = Γ₀} {t = natᵗ}) noSlots)))
    ≡ emitValues (evaluate 0 (emptyᵉ {Γ = Γ₀} {t = natᵗ}) noSlots)
_ = refl

-------------------------------------------------------------------
-- §2  UNIVERSAL LAW: readme-take-counts-values
--
-- concat (emitValues (spec-batchSimultaneous (evaluate fuel (takeᵉ k e) ins)))
--   ≡ take k (concat (emitValues (spec-batchSimultaneous (evaluate fuel e ins))))
-------------------------------------------------------------------

-- LOAD-BEARING: takeᵉ 1 on ofᵉ [3,7] keeps only 3.
-- LHS = concat [[3]] = [3].  RHS = take 1 [3,7] = [3].
-- Would fail if takeᵉ kept 2 values (result [3,7] ≠ [3]).
_ : concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (takeᵉ (nat̂ 1) (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ []))) noSlots)))
    ≡ take 1 (concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots))))
_ = refl

-- DEGENERATE: k=0, take keeps nothing; both sides reduce to [].
-- No take behaviour is exercised — trivially true for any stream.
_ : concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (takeᵉ (nat̂ 0) (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ []))) noSlots)))
    ≡ take 0 (concat (emitValues (spec-batchSimultaneous
      (evaluate 0 (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots))))
_ = refl

-------------------------------------------------------------------
-- §3  UNIVERSAL LAW: readme-one-subscribe-one-batch
--
-- length (spec-batchSimultaneous (evaluate 0 e ins)) ≤ 1
--
-- At fuel=0, drain is empty, so only the subscribe frame runs —
-- producing a SINGLE instant.  The spec groups by instant, so
-- at most one batch.  The emptyᵉ case produces zero batches
-- (no values, empty batches are dropped by the spec); ofᵉ produces one.
-------------------------------------------------------------------

-- DEGENERATE: emptyᵉ produces zero emits → spec output = [] → length 0.
-- 0 ≤ 1 holds by z≤n regardless; no batching constraint is exercised.
readme-one-subscribe-emptyᵉ :
    length (spec-batchSimultaneous
              (evaluate 0 (emptyᵉ {Γ = Γ₀} {t = natᵗ}) noSlots)) ≤ 1
readme-one-subscribe-emptyᵉ = z≤n

-- LOAD-BEARING: ofᵉ [3,7] at fuel=0 emits both values at instant 0.
-- spec-batchSimultaneous groups them into ONE batch → length 1.
-- s≤s z≤n proves 1 ≤ 1.  Would fail (s≤s (s≤s z≤n) : 2 ≤ 1 is rejected)
-- if spec batched instant 0 into two groups.
readme-one-subscribe-ofᵉ :
    length (spec-batchSimultaneous
              (evaluate 0 (ofᵉ {Γ = Γ₀} {t = natᵗ} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots)) ≤ 1
readme-one-subscribe-ofᵉ = s≤s z≤n

-------------------------------------------------------------------
-- §4  readme-serial-joins-mirror-rxjs (fuel=0)
--
-- emitValues (spec-batchSimultaneous (evaluate 0 (serialProgram g a b) noSlots))
--   ≡ (applyFn g (evalTm a) ∷ applyFn g (evalTm b) ∷ []) ∷ []
--
-- LOAD-BEARING: g=identity, a=nat̂ 3, b=nat̂ 7.
-- Expected: (3 ∷ 7 ∷ []) ∷ []
-- Would fail if g were applied wrong (e.g. skipped), values reordered, or batched
-- separately ((3∷[])∷(7∷[])∷[] ≠ (3∷7∷[])∷[]).
-------------------------------------------------------------------

readme-serial-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 0 (serialProgram (varᵗ (here refl)) (nat̂ 3) (nat̂ 7)) noSlots))
    ≡ (3 ∷ 7 ∷ []) ∷ []
readme-serial-refl = refl

-------------------------------------------------------------------
-- §5  readme-share-connect-no-replay (fuel=0)
--
-- emitValues (spec-batchSimultaneous
--   (evaluate 0 shareProgram (oneSlot (shared (ofᵉ (v ∷ []))))))
--   ≡ (evalTm v ∷ []) ∷ []
--
-- LOAD-BEARING: v = nat̂ 5.
-- Expected: (5 ∷ []) ∷ []
-- Would fail if share replayed the value to both subscribers ((5∷5∷[])∷[]).
-------------------------------------------------------------------

readme-share-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 0 shareProgram
                   (oneSlot (shared (ofᵉ (nat̂ 5 ∷ []))))))
    ≡ (5 ∷ []) ∷ []
readme-share-refl = refl

-------------------------------------------------------------------
-- §6  readme-diamond (fuel=1)
--
-- LOAD-BEARING: f = identity (varᵗ (here refl)), v = 3, fuel=1.
-- Expected: (3 ∷ 3 ∷ []) ∷ []
-- (v once direct, once through identity map — they batch together)
-- Would fail if the two diamond paths fired at different instants
-- ((3∷[])∷(3∷[])∷[] ≠ (3∷3∷[])∷[]).
-- fuel=1 is sufficient: the hot slot fires at drain step 1.
-------------------------------------------------------------------

readme-diamond-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 1 (diamondProgram (varᵗ (here refl)))
                   (oneSlot (hotOnce 3))))
    ≡ (3 ∷ 3 ∷ []) ∷ []
readme-diamond-refl = refl

-------------------------------------------------------------------
-- §7  readme-each-next-own-instant (fuel=2)
--
-- LOAD-BEARING: f = identity, u = 3, v = 7.
-- Expected: (3 ∷ 3 ∷ []) ∷ (7 ∷ []) ∷ []
-- (u fires as instant 1: u direct + u through map; v fires as instant 2: v only)
-- Would fail if u and map(u) batched separately, or v batched with u.
-------------------------------------------------------------------

readme-each-next-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 2 (eachNextProgram (varᵗ (here refl)))
                   (twoHots 3 7)))
    ≡ (3 ∷ 3 ∷ []) ∷ (7 ∷ []) ∷ []
readme-each-next-refl = refl

-------------------------------------------------------------------
-- §8  readme-cascades-inherit (fuel=1)
-------------------------------------------------------------------

-- DEGENERATE: ws = [] (empty cascade list), v = 5.
-- Expected: (5 ∷ []) ∷ []  (just v, no cascade observables)
-- No cascade fires — the inner mergeAll merges nothing.
-- Passes trivially: (5 ∷ map _ [] = []) = (5 ∷ []) regardless of batching.
readme-cascades-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 1 (cascadeProgram []) (oneSlot (hotOnce 5))))
    ≡ (5 ∷ []) ∷ []
readme-cascades-refl = refl

-- LOAD-BEARING: ws = [identity], v = 5, fuel=1.
-- Expected: (5 ∷ 5 ∷ []) ∷ []
-- (v fires direct + identity(v) = v via cascade, both at the same instant)
-- Would fail if the cascade value fired at a later instant
-- ((5∷[])∷(5∷[])∷[] ≠ (5∷5∷[])∷[]).
-- The postulate: result ≡ (v ∷ map (λ w → applyFn w v) ws) ∷ []
-- Here map (λ w → applyFn w v) [varᵗ (here refl)] = [applyFn id 5] = [5].
readme-cascades-identity :
    emitValues (spec-batchSimultaneous
                 (evaluate 1 (cascadeProgram (varᵗ (here refl) ∷ []))
                   (oneSlot (hotOnce 5))))
    ≡ (5 ∷ 5 ∷ []) ∷ []
readme-cascades-identity = refl

-------------------------------------------------------------------
-- §9  readme-completion-cascades (fuel=2)
--
-- completionProgram uses concatAllᵉ: takes 1 from source, then emits w.
-- Test: w = nat̂ 5, u = 3, v = 7.
-- Slot: scripted hot with both u and v at tick 0 (after 0).
-- Expected: (3 ∷ 3 ∷ 5 ∷ []) ∷ (7 ∷ []) ∷ []
-- (u fires as instant 1: take closes after u, concat's second leg emits w = 5,
--  all batched with u; v fires as instant 2, just v)
--
-- LOAD-BEARING: would fail if completion w fired at its own instant
-- ((3∷3∷[])∷(5∷[])∷(7∷[])∷[] ≠ (3∷3∷5∷[])∷(7∷[])∷[]).
-------------------------------------------------------------------

readme-completion-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 2 (completionProgram (nat̂ 5))
                   (oneSlot (scripted (hot ((after 0 , 3) ∷ (after 0 , 7) ∷ []))))))
    ≡ (3 ∷ 3 ∷ 5 ∷ []) ∷ (7 ∷ []) ∷ []
readme-completion-refl = refl

-------------------------------------------------------------------
-- §10  readme-late-join-growth (fuel=4)
--
-- growthProgram uses merge + mergeAll(map(strmᵗ(shared-src))(trigger)).
-- Test: u = 3, v = 7, w = 0, x = 0 (trigger values).
-- Expected: (3 ∷ 3 ∷ []) ∷ (7 ∷ 7 ∷ 7 ∷ []) ∷ []
-- (2 triggers + 2 src values; first trigger creates 1 extra ref,
--  second trigger creates 2 extra refs)
--
-- LOAD-BEARING: would fail if late-join refs batched separately from src
-- (each 7 in its own batch would give (3∷[])∷(3∷[])∷(7∷[])∷(7∷[])∷(7∷[])∷[]).
-------------------------------------------------------------------

readme-growth-refl :
    emitValues (spec-batchSimultaneous
                 (evaluate 4 growthProgram (growthSlots 3 7 0 0)))
    ≡ (3 ∷ 3 ∷ []) ∷ (7 ∷ 7 ∷ 7 ∷ []) ∷ []
readme-growth-refl = refl
