------------------------------------------------------------------
-- THE DEPTH-BLOWUP PROBE: can `depthE` outrun `capsBase` once
-- deliveries are pushed high?
--
-- `Depth-Discharge-Probe` measured `depthE` only at the ROOT SUBSCRIBE
-- (instant 0), on programs whose nesting is built SYNCHRONOUSLY out of
-- literal `ofᵉ` lists.  There, every extra fold costs the SAME program
-- to grow its own syntax (an extra list element), and `capsBase` reads
-- that same syntax directly — so the two racing quantities are stuck
-- paying from the same purse, and the margin only widened (16, 18, 20,
-- 25 across folds 1, 3, 5, 10 — Depth-Discharge-Probe § 2).
--
-- THIS PROBE ASKS THE SHARPER QUESTION: what if the folds are not
-- written into the syntax at all, but arrive one per CASCADE off a
-- scripted source?  `capsBase`'s only per-arrival cost is
-- `slotsSize`'s `inputSize`, which sums `sizeᵛ` of each scripted VALUE
-- — and `sizeᵛ natᵗ _ ≡ 1` for every nat, regardless of what the fold's
-- STEP FUNCTION does with it.  So one extra scripted arrival costs
-- `capsBase` exactly +1, no matter how many nesting levels the step
-- function's own (fixed, written-once) body pays per fold.  If a step
-- function nests `k+1` levels per fold — cheap to write once, since the
-- Fn's syntax is fixed and reused, not repeated per arrival — then the
-- N-th cascade's subscribe of the accumulator should cost roughly
-- `(k+1) * N`, a SLOPE the flat `+1`-per-arrival budget cannot match
-- once `k ≥ 1`.
--
-- THE HARNESS.  `depthNextCascade` mirrors `Fold-Count-Probe`'s
-- `runSt`/`burstAt`: drain `fuel` real cascades with the actual
-- evaluator (`cascade`), then, rather than running the next cascade,
-- read off `chainsOf` at the resulting state and feed each chain to
-- `depthChain` — the mirror's own per-arrival, per-chain entry point,
-- exactly as `cascadeGo` feeds each chain to `chainStep`/`foldPath`.
-- Multiple chains are ⊔'d, matching the mirror's own "duplication costs
-- nothing" reading, since a real cascade can register a source under
-- more than one chain.
--
-- THE STEP FAMILY.  `wrapK k` is `Depth-Discharge-Probe`'s `wrapFn`
-- with `k` EXTRA `mergeAllᵉ (ofᵉ (strmᵗ _ ∷ []))` wrappers around the
-- accumulator projection — `wrapK 0 ≡ wrapFn` (one merge layer total),
-- `wrapK k` has `k + 1` layers.  Every layer is fixed syntax, written
-- once in the Fn body; it does not repeat per fold.
--
-- THE FINDING, up front: `depthE ≤ capsBase` IS FALSE.  The control at
-- k = 0 holds at every rung, but k = 1 breaches at N = 22 (45 against 44)
-- and k = 2 at N = 13 (40 against 39) — and the `≡ false` rows below are
-- typechecked, so the breach is CONFIRMED, not merely unproven.
--
-- THE OBLIGATION ITSELF SURVIVES, because `capsBase` is not its cap: § 4
-- shows both breach points clearing `capsH`'s provable lower bound by a
-- wide margin.  What dies is the naive route — no proof of
-- `depthE ≤ capsH` can go through `capsBase` alone.  § 5 draws out the
-- consequence for the proof's shape, which is the part worth keeping.
------------------------------------------------------------------
module Depth-Blowup-Probe where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤ᵇ_; _+_; _*_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin; zero)
open import Data.Sum  using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Timed; ObservableInput; hot; after_,_)
open import Rx.Exp
open import Rx.Evaluator using (Slots; Slot; scripted; shared; Sched; EvalSt;
                                sched-init; sched-next; st-init; budgetAt;
                                subscribeE; cascade; capsBase; slotsSize;
                                root; chainsOf; RegId; Path; Arrival; arrTy)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE; depthChain)

------------------------------------------------------------------
-- THE HARNESS
------------------------------------------------------------------

-- one root subscribe, mirrored — verbatim Depth-Discharge-Probe's shape
measureDepth : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → ℕ
measureDepth e sl = depthE (budgetAt e sl 0) e root 0 0 (sched-init e sl) (st-init e)

-- drain `fuel` real cascades with the ACTUAL evaluator, tracking the
-- next id — verbatim Fold-Count-Probe's runSt/drainSt shape
drainSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Fuel → Id → Sched Γ → EvalSt e → Id × Sched Γ × EvalSt e
drainSt zero    nextId sched st = nextId , sched , st
drainSt (suc k) nextId sched st with sched-next sched
... | inj₁ _            = nextId , sched , st
... | inj₂ (a , sched′) =
      let (_ , sched″ , st′) = cascade a nextId sched′ st
      in drainSt k (suc nextId) sched″ st′

runSt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
      → Id × Sched Γ × EvalSt e
runSt fuel e ins =
  let (_ , sched₀ , st₀) =
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
  in drainSt fuel 1 sched₀ st₀

-- the depth mirror's own reading of ONE cascade: every live chain of
-- the next arrival's source, ⊔'d — the mirror's counterpart of
-- `cascadeGo`, which feeds every such chain to `chainStep`
depthCascadeGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
               → Id → (a : Arrival Γ) → List (RegId × Path Γ (arrTy a) t)
               → Sched Γ → EvalSt e → ℕ
depthCascadeGo id a []             sched st = 0
depthCascadeGo id a ((rid , c) ∷ cs) sched st =
  depthChain id a c sched st ⊔ depthCascadeGo id a cs sched st

-- drain `fuel` cascades for real, then read the depth mirror's verdict
-- on the NEXT one without running it
depthNextCascade : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ → ℕ
depthNextCascade fuel e ins with runSt fuel e ins
... | nid , sched , st with sched-next sched
...   | inj₁ _            = 0
...   | inj₂ (a , sched′) = depthCascadeGo nid a (chainsOf a st) sched′ st

------------------------------------------------------------------
-- THE STEP FAMILY: `wrapK k` nests `k + 1` merge layers, fixed syntax,
-- written once regardless of the fold count N that will drive it
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

seedO : ∀ {n} {Γ : Ctx n} {Θ} → Tm Γ [] [] Θ (obs natᵗ)
seedO = strmᵗ emptyᵉ

-- one extra merge layer around an already-built natᵗ expression
nestMerge : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Exp Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ natᵗ
nestMerge e = mergeAllᵉ (ofᵉ (strmᵗ e ∷ []))

nestMergeK : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → ℕ → Exp Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ natᵗ
nestMergeK zero    e = e
nestMergeK (suc k) e = nestMerge (nestMergeK k e)

wrapK : ∀ {n} {Γ : Ctx n} → ℕ → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapK k = strmᵗ (nestMergeK k (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))))

pushD : ℕ → Closed Γ₁ natᵗ
pushD k = mergeAllᵉ (scanᵉ (wrapK k) seedO (input zero))

------------------------------------------------------------------
-- THE SLOTS: one scripted source, N ticks, all `after 0` — the value
-- carried does not matter, since `sizeᵛ natᵗ _ ≡ 1` regardless
------------------------------------------------------------------

hotList : ℕ → List (Timed ℕ)
hotList zero    = []
hotList (suc j) = after 0 , 1 ∷ hotList j

insN : ℕ → Slots Γ₁
insN n zero = scripted (hot (hotList n))

------------------------------------------------------------------
-- § 0  SANITY: `slotsSize` really is `N + 1`, and `sizeᵉ`/`capsBase`
-- really do not move with N — the two facts the whole probe rests on
------------------------------------------------------------------

_ : slotsSize (insN 0) ∷ slotsSize (insN 1) ∷ slotsSize (insN 5) ∷ slotsSize (insN 20) ∷ []
  ≡ 1 ∷ 2 ∷ 6 ∷ 21 ∷ []
_ = refl

_ : capsBase (pushD 0) (insN 0) ∷ capsBase (pushD 0) (insN 5) ∷ capsBase (pushD 0) (insN 20) ∷ []
  ≡ 18 ∷ 23 ∷ 38 ∷ []
_ = refl

------------------------------------------------------------------
-- § 1  k = 0, THE CONTROL — the single-layer step, expected to behave
-- like Fold-Count-Probe's `pD`: one nesting level per fold, matching
-- `capsBase`'s own +1-per-arrival slope
------------------------------------------------------------------

_ : depthNextCascade 0 (pushD 0) (insN 1) ≡ 2
_ = refl

_ : depthNextCascade 1 (pushD 0) (insN 2) ≡ 3
_ = refl

_ : depthNextCascade 4 (pushD 0) (insN 5) ≡ 6
_ = refl

_ : depthNextCascade 9 (pushD 0) (insN 10) ≡ 11
_ = refl

_ : depthNextCascade 19 (pushD 0) (insN 20) ≡ 21
_ = refl

-- capsBase at the SAME (k, N) pairs
_ : capsBase (pushD 0) (insN 1) ∷ capsBase (pushD 0) (insN 2) ∷ capsBase (pushD 0) (insN 5)
  ∷ capsBase (pushD 0) (insN 10) ∷ capsBase (pushD 0) (insN 20) ∷ []
  ≡ 19 ∷ 20 ∷ 23 ∷ 28 ∷ 38 ∷ []
_ = refl

-- HOLDS at every rung, control included
_ : (depthNextCascade 0 (pushD 0) (insN 1)   ≤ᵇ capsBase (pushD 0) (insN 1))
  ∷ (depthNextCascade 1 (pushD 0) (insN 2)   ≤ᵇ capsBase (pushD 0) (insN 2))
  ∷ (depthNextCascade 4 (pushD 0) (insN 5)   ≤ᵇ capsBase (pushD 0) (insN 5))
  ∷ (depthNextCascade 9 (pushD 0) (insN 10)  ≤ᵇ capsBase (pushD 0) (insN 10))
  ∷ (depthNextCascade 19 (pushD 0) (insN 20) ≤ᵇ capsBase (pushD 0) (insN 20))
  ∷ []
  ≡ true ∷ true ∷ true ∷ true ∷ true ∷ []
_ = refl

------------------------------------------------------------------
-- § 2  k = 1 — TWO merge layers per fold, written once.  If the slope
-- doubles while `capsBase`'s slope stays fixed at 1 per arrival, the
-- margin (constant at k = 0) must start shrinking with N
------------------------------------------------------------------

_ : depthNextCascade 0 (pushD 1) (insN 1) ≡ 3
_ = refl

_ : depthNextCascade 1 (pushD 1) (insN 2) ≡ 5
_ = refl

_ : depthNextCascade 4 (pushD 1) (insN 5) ≡ 11
_ = refl

_ : depthNextCascade 9 (pushD 1) (insN 10) ≡ 21
_ = refl

_ : capsBase (pushD 1) (insN 1) ∷ capsBase (pushD 1) (insN 2) ∷ capsBase (pushD 1) (insN 5)
  ∷ capsBase (pushD 1) (insN 10) ∷ []
  ≡ 23 ∷ 24 ∷ 27 ∷ 32 ∷ []
_ = refl

-- so far HOLDS, but with a margin that is SHRINKING with N (22 - N,
-- read off `capsBase = 22 + N` and `depthNextCascade = 2N + 1` above):
-- 19 at N = 1 down to 1 at N = 21.  Pin the last rung where it still
-- holds, and the crossover itself
_ : depthNextCascade 20 (pushD 1) (insN 21) ≡ 43
_ = refl

_ : capsBase (pushD 1) (insN 21) ≡ 43
_ = refl

_ : (depthNextCascade 20 (pushD 1) (insN 21) ≤ᵇ capsBase (pushD 1) (insN 21)) ≡ true
_ = refl

-- THE BREACH: one more fold, and `depthE` overtakes `capsBase` for good
_ : depthNextCascade 21 (pushD 1) (insN 22) ≡ 45
_ = refl

_ : capsBase (pushD 1) (insN 22) ≡ 44
_ = refl

_ : (depthNextCascade 21 (pushD 1) (insN 22) ≤ᵇ capsBase (pushD 1) (insN 22)) ≡ false
_ = refl

------------------------------------------------------------------
-- § 3  k = 2 — THREE merge layers per fold: the same finding, a
-- shallower N, since the slope is now 3 against `capsBase`'s fixed 1
------------------------------------------------------------------

_ : depthNextCascade 0 (pushD 2) (insN 1) ≡ 4
_ = refl

_ : depthNextCascade 4 (pushD 2) (insN 5) ≡ 16
_ = refl

_ : capsBase (pushD 2) (insN 1) ∷ capsBase (pushD 2) (insN 5) ∷ []
  ≡ 27 ∷ 31 ∷ []
_ = refl

-- HOLDS here (margin 23 at N=1, 15 at N=5) but the slope gap is now 2
-- per fold (3 against 1), so the crossover should arrive roughly twice
-- as fast as k = 1's — measure it directly rather than trust the linear
-- extrapolation
_ : depthNextCascade 10 (pushD 2) (insN 11) ≡ 34
_ = refl

_ : capsBase (pushD 2) (insN 11) ≡ 37
_ = refl

_ : (depthNextCascade 10 (pushD 2) (insN 11) ≤ᵇ capsBase (pushD 2) (insN 11)) ≡ true
_ = refl

_ : depthNextCascade 11 (pushD 2) (insN 12) ≡ 37
_ = refl

_ : capsBase (pushD 2) (insN 12) ≡ 38
_ = refl

_ : (depthNextCascade 11 (pushD 2) (insN 12) ≤ᵇ capsBase (pushD 2) (insN 12)) ≡ true
_ = refl

_ : depthNextCascade 12 (pushD 2) (insN 13) ≡ 40
_ = refl

_ : capsBase (pushD 2) (insN 13) ≡ 39
_ = refl

_ : (depthNextCascade 12 (pushD 2) (insN 13) ≤ᵇ capsBase (pushD 2) (insN 13)) ≡ false
_ = refl

------------------------------------------------------------------
-- § 4  AND WHY THE OBLIGATION SURVIVES ITS OWN COUNTEREXAMPLE.
--
-- Everything above compares against `capsBase`, i.e. the cap at instant
-- ZERO — but every row was measured AFTER draining N cascades, so each
-- one sits at instant N.  The fuel the proof actually gets there is
-- `capsH e sl N` (.Caps-Face's `caps-tick` hands `cascadeGo-caps` exactly
-- `capsH e sl id`), and that is a much bigger number:
--
--     capsHgo m zero    = blowH m
--     capsHgo m (suc id) = blowH (capsHgo m id)
--     blowH m           = 6 + m + 2 * poolCount (towerℕ m) m   ≥  6 + m
--
-- so `capsH e sl id ≥ capsBase e sl + 6 * suc id`, dropping the
-- `poolCount` term entirely.  `blowH` is `abstract`, so that bound cannot
-- be COMPUTED here — but it can be checked against, since the right-hand
-- side is ordinary arithmetic on a computable `capsBase`.
--
-- Both breach points clear it with room to spare, and that is the real
-- finding: `depthE ≤ capsBase` is FALSE, `depthE ≤ capsH` is untouched.
------------------------------------------------------------------

-- the k = 1 breach: 45 against a real cap of at least 44 + 6*23 = 182
_ : (depthNextCascade 21 (pushD 1) (insN 22)
       ≤ᵇ (capsBase (pushD 1) (insN 22) + 6 * 23)) ≡ true
_ = refl

-- the k = 2 breach: 40 against at least 39 + 6*14 = 123
_ : (depthNextCascade 12 (pushD 2) (insN 13)
       ≤ᵇ (capsBase (pushD 2) (insN 13) + 6 * 14)) ≡ true
_ = refl

------------------------------------------------------------------
-- § 5  THE SHAPE OF THE PROOF THIS LEAVES, and it is the one thing here
-- that changes the design.
--
-- The campaign's standing refutations of static measures (Mu-Nest-Probe
-- § 2, Nest-Budget-Probe § 3) are about depth's TOTAL, and they stand.
-- What the slopes above say is something different and weaker: the
-- PER-INSTANT INCREMENT is `k + 1`, the step function's own STATIC
-- nesting — syntax written once in the Fn body, paid once per fold.  The
-- total is dynamic; the increment is not.
--
--   depth  at instant N  =  (k+1) * N + 1        -- measured, § 1-3
--   capsH  at instant N  ≥  capsBase + 6*(N+1)   -- from blowH, above
--
-- So the induction that discharges the obligation compares INCREMENTS,
-- not totals: one instant costs depth at most the program's static
-- nesting, and costs `capsH` one whole `blowH` story.  For `k + 1 ≤ 6`
-- the LINEAR part of `blowH` already dominates and `poolCount` is never
-- needed.  Past that it is needed — and it is available, since `towerℕ`'s
-- argument grows with the same `sizeᵉ e` that bounds `k` in the first
-- place (each `nestMerge` layer costs `capsBase` +4, measured in § 1-3).
--
-- NOT MEASURED, and not to be assumed: every row here is k ≤ 2 and
-- N ≤ 22, one scripted source, one shared slot, instant-0 subscribe plus
-- N cascades.  The `poolCount` regime (k ≥ 6) is untested — it cannot be
-- probed at all while `blowH` is `abstract`, so it has to be PROVEN.
------------------------------------------------------------------
