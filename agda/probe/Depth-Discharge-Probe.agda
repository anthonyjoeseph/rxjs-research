-- THE DEPTH-DISCHARGE PROBE: does a real run's nesting stay under the
-- cheap, size-linear cap?
--
-- `Verify-Budget-Sufficient.Caps-Depth` (NEW, green) mirrors the
-- evaluator's subscribe clique clause-for-clause and returns, as a plain
-- ℕ, how many nested depth-spending arcs one root subscribe actually
-- takes: `depthE <root's own entry args>`.  The clique still OWES one
-- hypothesis at the top — `depthE/depthChain at the instant's entry
-- args ≤ capsH e sl id` — and `capsH` is a `blowH`-iterated tower that
-- cannot be computed (it need not even reduce).  But `capsBase e sl =
-- 3 + (sizeᵉ e + slotsSize sl) + suc (entryCeil n sl e)`
-- (`Rx.Evaluator:922`) is the RECURRENCE'S OWN BASE, it dominates
-- `capsH` at every id (`capsHgo` only ever inflates it, Caps.agda:449),
-- and it IS computable: roughly linear in program size.  So `depthE ≤
-- capsBase` would already discharge the real obligation, and unlike
-- `capsH` it is something this probe can actually measure.
--
-- WHY THIS IS IN DOUBT.  `Nest-Budget-Probe` § 3 built a real evaluator
-- value — a `scanᵉ` whose step wraps the running accumulator in a fresh
-- `mergeAllᵉ` — and showed the MINTED PAYLOAD nests one level deeper per
-- fold, while the carrier's own syntax (hence its `sizeᵉ`) barely moves
-- with the fold count of the source list.  If the RUN actually walks
-- into each minted payload (rather than merely allowing it to exist),
-- `depthE` on that carrier grows with the fold count too, and a bound
-- that is only linear in `sizeᵉ` cannot track it — `depthE ≤ capsBase`
-- would be FALSE, and the deferred obligation would need a completely
-- different currency than `capsBase` to close.  This probe is the
-- measurement that settles which of those two worlds we are in.
--
-- METHOD: build one root-subscribe call exactly as `subscribeE` is
-- called at the top (`Burst-Probe.runProbe`'s shape) but hand it to
-- `depthE` instead, and to `capsBase`, for a baseline family (§ 1) and
-- for the adversarial fold family itself, at growing fold counts (§ 2).
-- Every row below is `refl`-checked against its LITERAL measured value
-- — none of these numbers were guessed and kept; each was found by
-- typechecking a wrong guess and reading the real number out of the
-- resulting Agda error, per the brief's method.
module Depth-Discharge-Probe where

open import Data.Nat using (ℕ; zero; suc; _≤ᵇ_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (zero)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp
open import Rx.Evaluator using (Slots; capsBase; budgetAt; sched-init; st-init; root)
open import Rx.Slots using (shared)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

------------------------------------------------------------------
-- THE HARNESS: one root subscribe, mirrored, at instant 0 / tick 0 —
-- copied verbatim in shape from `Burst-Probe.runProbe`'s own call
-- (`agda/probe/Burst-Probe.agda:276`), just handed to `depthE` and to
-- `capsBase` instead of to the real `subscribeE`.
------------------------------------------------------------------

measureDepth : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → ℕ
measureDepth e sl = depthE (budgetAt e sl 0) e root 0 0 (sched-init e sl) (st-init e)

Γ₀ : Ctx 0
Γ₀ = []ᵛ

-- the empty telescope: Fin 0 is empty, so every case is absurd
sl0 : Slots Γ₀
sl0 ()

------------------------------------------------------------------
-- § 1  BASELINE: three small closed programs, trivial up to one
-- `mergeAllᵉ`, `Ctx 0` throughout.
------------------------------------------------------------------

-- P1: a bare `ofᵉ` — no frame, no subscribe of anything
P1 : Closed Γ₀ natᵗ
P1 = ofᵉ (nat̂ 0 ∷ [])

_ : sizeᵉ P1 ≡ 3
_ = refl

_ : measureDepth P1 sl0 ≡ 0
_ = refl

_ : capsBase P1 sl0 ≡ 8
_ = refl

-- P2: a `mapᵉ` chain edge over P1's source — still no subscribe: a
-- chain edge is one more frame on the SAME sweep, never a nesting level
P2 : Closed Γ₀ natᵗ
P2 = mapᵉ (varᵗ (here refl)) (ofᵉ (nat̂ 0 ∷ []))

_ : sizeᵉ P2 ≡ 5
_ = refl

_ : measureDepth P2 sl0 ≡ 0
_ = refl

_ : capsBase P2 sl0 ≡ 10
_ = refl

-- P3: one `mergeAllᵉ` over a single minted (empty) inner — the first
-- program that actually re-enters the subscribe family
P3 : Closed Γ₀ natᵗ
P3 = mergeAllᵉ (ofᵉ (strmᵗ emptyᵉ ∷ []))

_ : sizeᵉ P3 ≡ 5
_ = refl

_ : measureDepth P3 sl0 ≡ 1
_ = refl

_ : capsBase P3 sl0 ≡ 10
_ = refl

_ : (measureDepth P3 sl0 ≤ᵇ capsBase P3 sl0) ≡ true
_ = refl

------------------------------------------------------------------
-- § 2  THE ADVERSARIAL FAMILY: `Nest-Budget-Probe` § 3's `carrier`
-- (`wrapFn`, `acc`), at growing fold counts.  `wrapFn` is copied
-- VERBATIM — it is the real `applyFn` step, not a hand-drawn stand-in —
-- and `carrierN` is `Nest-Budget-Probe`'s `carrier` with the `ofᵉ`
-- literal list at length N in place of its fixed length 5, so the fold
-- count varies while the surrounding syntax (one `scanᵉ` under one
-- `mergeAllᵉ`) does not move at all.
------------------------------------------------------------------

-- the step function: `λ (acc , x) → strm (mergeAll (of [ fst (acc,x) ]))`
-- — the BODY is verbatim Nest-Budget-Probe § 3; the type is generalised
-- from `Γ₀` to any `Γ` (the body never mentions Γ at all) so § 3 below
-- can reuse the identical mint at a one-slot context
wrapFn : ∀ {n} {Γ : Ctx n} → Fn Γ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
wrapFn = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

carrier1 : Closed Γ₀ natᵗ
carrier1 = mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ) (ofᵉ (nat̂ 0 ∷ [])))

carrier3 : Closed Γ₀ natᵗ
carrier3 = mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ)
             (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))

-- Nest-Budget-Probe's own `carrier`, at fold count 5
carrier5 : Closed Γ₀ natᵗ
carrier5 = mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ)
             (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷ [])))

-- fold count 1 --------------------------------------------------

_ : sizeᵉ carrier1 ≡ 13
_ = refl

_ : measureDepth carrier1 sl0 ≡ 2
_ = refl

_ : capsBase carrier1 sl0 ≡ 18
_ = refl

_ : (measureDepth carrier1 sl0 ≤ᵇ capsBase carrier1 sl0) ≡ true
_ = refl

-- fold count 3 --------------------------------------------------

_ : sizeᵉ carrier3 ≡ 15
_ = refl

_ : measureDepth carrier3 sl0 ≡ 4
_ = refl

_ : capsBase carrier3 sl0 ≡ 22
_ = refl

_ : (measureDepth carrier3 sl0 ≤ᵇ capsBase carrier3 sl0) ≡ true
_ = refl

-- fold count 5 --------------------------------------------------

_ : sizeᵉ carrier5 ≡ 17
_ = refl

_ : measureDepth carrier5 sl0 ≡ 6
_ = refl

_ : capsBase carrier5 sl0 ≡ 26
_ = refl

_ : (measureDepth carrier5 sl0 ≤ᵇ capsBase carrier5 sl0) ≡ true
_ = refl

-- fold count 10, one extra rung beyond the brief's suggested lengths —
-- confirms the trend from three points is not an accident of small
-- numbers before trusting the "linear, not exponential" headline
carrier10 : Closed Γ₀ natᵗ
carrier10 = mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ)
              (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ nat̂ 4 ∷
                    nat̂ 5 ∷ nat̂ 6 ∷ nat̂ 7 ∷ nat̂ 8 ∷ nat̂ 9 ∷ [])))

_ : sizeᵉ carrier10 ≡ 22
_ = refl

_ : measureDepth carrier10 sl0 ≡ 11
_ = refl

_ : capsBase carrier10 sl0 ≡ 36
_ = refl

_ : (measureDepth carrier10 sl0 ≤ᵇ capsBase carrier10 sl0) ≡ true
_ = refl

------------------------------------------------------------------
-- § 3  A SHARED SLOT whose stored def is itself a deepening scan — one
-- probe of the delivery-multiplication axis (Nest-Count-Probe: stories
-- per instant = deliveries × nesting).
--
-- CAVEAT, READ BEFORE TRUSTING THIS ROW: `measureDepth` only calls
-- `depthE` on the ROOT SUBSCRIBE.  The connect side (`depthConn`,
-- Caps-Depth.agda:273-277) IS covered by that one call — every `input i`
-- reading a `shared` slot re-subscribes the def with path `share-sink i`
-- as part of THIS SAME subscribe, and the mirror's own header note says
-- it reports that connect UNCONDITIONALLY, at every occurrence, even
-- though the real evaluator only actually re-subscribes on the first —
-- so this row is already an OVER-approximation of subscribe-time work,
-- in the mirror's favour.  What it does NOT cover is the true
-- delivery-multiplication axis: fan-out to an already-registered chain
-- when the shared source emits LATER, across instants.  That lives in
-- `depthChain`/`depthFold`/`depthDisp`/`depthShareGo`, which walk the
-- registry at an ARRIVAL, not at the root subscribe — building a probe
-- for that would mean constructing an `Arrival` and a post-subscribe
-- `Sched`/`EvalSt` pair by hand, which is materially more machinery than
-- one extra row buys here.  NOT ATTEMPTED — reported, not guessed.
------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

-- slot 0: a shared def that is itself the fold-count-3 deepening scan
sharedDef : Closed Γ₁ natᵗ
sharedDef = mergeAllᵉ (scanᵉ wrapFn (strmᵗ emptyᵉ)
              (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))

sl1 : Slots Γ₁
sl1 zero = shared sharedDef

-- the root reads the SAME shared slot TWICE — the minimal shape that can
-- exercise a duplicated connect
eShare : Closed Γ₁ natᵗ
eShare = mergeAllᵉ (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input zero) ∷ []))

_ : sizeᵉ eShare ≡ 7
_ = refl

_ : measureDepth eShare sl1 ≡ 5
_ = refl

_ : capsBase eShare sl1 ≡ 32
_ = refl

_ : (measureDepth eShare sl1 ≤ᵇ capsBase eShare sl1) ≡ true
_ = refl
