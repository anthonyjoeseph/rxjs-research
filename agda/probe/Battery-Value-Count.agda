-- ROADMAP: tier-1 #1/#2/#3 — the anchor.  REFUTES `sync-count-bounded`; keeps the route from being retried.
-- DELETE WHEN: the three Anchor-Dry demand postulates are discharged (tier-1 #1/#2/#3)  [T1]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- BATTERY: VALUE-COUNT vs syncSizeᵉ  (2026-08-06)
--
-- THE QUESTION, and it is the anchor's load-bearing arithmetic.  The dry
-- family (Anchor-Dry-Probe.agda) needs the inner observables reaching
-- `subscribeInner` to fit under `sizeCapAt e sl (suc id)`.  The size of a
-- doubling scan's accumulator is `12·2^k − 11` in the EMISSION COUNT k
-- (Battery-Obs-Growth), while the caps ceiling is entry-computable — so the
-- whole chain rests on `k ≤ syncSizeᵉ e`, i.e. one instant cannot emit more
-- values than the program's sync measure allows.
--
-- WHY NOT `burstLen`.  BurstLen-SyncSize-Probe refuted
-- `burstLen … ≤ syncSizeᵉ e` at `deferᵉ emptyᵉ` (2 > 1).  That refutation is
-- real but OFF-TARGET: `burstLen` sums `suc (length events)` over every
-- InstEmit, and `InstEvent` (Rx/Prim.agda:107) carries `init`, `close`,
-- `handoff` and `complete` beside `value`.  The refuting burst has one `init`
-- and ZERO values.  Only `value` events feed a scan accumulator, so only they
-- drive `12·2^k`.  Hence `valueCount` below — the measure named by what it
-- COUNTS.
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/Battery-Value-Count.agda &&
--   agda -i src -i probe probe/Battery-Value-Count.agda
module Battery-Value-Count where

open import Data.Nat      using (ℕ; zero; suc; _+_; _⊔_)
open import Data.List     using (List; []; _∷_; map; sum; foldr)
open import Data.Vec      using () renaming ([] to []ᵛ)
open import Data.Product  using (proj₁)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Gas; gs; g0; InstEmit; InstEvent;
                                init; value; close; handoff; complete)
open import Rx.Exp
  using (Ty; Ctx; obs; natᵗ; _×ᵗ_; Val; Closed; Fn; Tm;
         varᵗ; fstᵗ; nat̂; strmᵗ;
         ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ; deferᵉ;
         syncSizeᵉ; sizeᵉ)
open import Rx.Evaluator
  using (Slots; Stream; subscribeE; sched-init; st-init; root)

----------------------------------------------------------------------
-- § 0  THE MEASURE — value events only.
----------------------------------------------------------------------

countVals : ∀ {A : Set} → List (InstEvent A) → ℕ
countVals []              = 0
countVals (value _ ∷ es)  = suc (countVals es)
countVals (init _ ∷ es)   = countVals es
countVals (close _ _ ∷ es) = countVals es
countVals (handoff _ ∷ es) = countVals es
countVals (complete ∷ es)  = countVals es

-- Generic in the payload: `Stream Γ u` is `List (InstEmit (Val Γ u))`, and
-- `Val Γ natᵗ` REDUCES to `ℕ` — so an index-carrying signature leaves Γ and u
-- un-inferrable at exactly the natᵗ-typed programs this file needs.
valueCount : ∀ {A : Set} → List (InstEmit A) → ℕ
valueCount b = sum (map (λ em → countVals (InstEmit.events em)) b)

----------------------------------------------------------------------
-- SETUP
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

bigGas : Gas
bigGas = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))

burstOf : ∀ {u} → Closed Γ₀ u → Stream Γ₀ u
burstOf p = proj₁ (subscribeE bigGas p root 0 0 (sched-init p ins₀) (st-init p))

----------------------------------------------------------------------
-- § 1  DEGENERATE ROWS — the two programs that refuted `burstLen`.
--
-- Both emit NO values, so any bound holds trivially.  They are recorded to
-- show explicitly that the `burstLen` refutation does NOT carry over, and
-- they are NOT evidence for the bound.  A row that could not have failed is
-- not a row.
----------------------------------------------------------------------

deferProg : Closed Γ₀ (obs natᵗ)
deferProg = deferᵉ emptyᵉ

-- DEGENERATE: 0 ≤ anything.  Would only fail if deferᵉ started emitting.
_ : valueCount (burstOf deferProg) ≡ 0
_ = refl

_ : syncSizeᵉ deferProg ≡ 1
_ = refl

emptyProg : Closed Γ₀ natᵗ
emptyProg = emptyᵉ

-- DEGENERATE: same.
_ : valueCount (burstOf emptyProg) ≡ 0
_ = refl

----------------------------------------------------------------------
-- § 2  THE ADVERSARIAL SHAPE — a doubling scan over a NON-EMPTY seed.
--
-- Battery-Obs-Growth's doubling scan uses `seed = strmᵗ emptyᵉ`, so every
-- accumulator is a tree of merges over EMPTY leaves: it grows in SIZE but
-- emits nothing.  That is why its value counts stayed small.
--
-- Give the seed one value and the tree's leaves become live:
--   acc₀ = ofᵉ [0]                     emits 1
--   accⱼ = mergeAllᵉ (ofᵉ [accⱼ₋₁, accⱼ₋₁])   emits 2·(j−1) ⇒ 2^j
-- The program `mergeAllᵉ (scanᵉ step seed src)` subscribes EVERY emitted
-- accumulator, all inside the one instant `ofᵉ` fires in, so
--   valueCount = Σ_{j=1..K} 2^j = 2^(K+1) − 2
-- while `syncSizeᵉ` is LINEAR in K (`ofᵉ` adds ~1 per element,
-- `mergeAllᵉ` costs a bare `suc` — Exp.agda:504,509).
--
-- Exponential against linear: if this is right the bound breaks at small K,
-- and `k ≤ syncSizeᵉ e` is FALSE.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

-- THE ONE CHANGE from Battery-Obs-Growth: a live seed.
liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

prog₁ : Closed Γ₀ natᵗ
prog₁ = mergeAllᵉ (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ [])))

prog₂ : Closed Γ₀ natᵗ
prog₂ = mergeAllᵉ (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ [])))

prog₃ : Closed Γ₀ natᵗ
prog₃ = mergeAllᵉ (scanᵉ step liveSeed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog₄ : Closed Γ₀ natᵗ
prog₄ = mergeAllᵉ (scanᵉ step liveSeed
                    (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

-- LOAD-BEARING.  valueCount = 2^(K+1) − 2, measured.  Would fail if the
-- accumulator tree stopped doubling or if the merged inners landed in
-- separate instants.
_ : valueCount (burstOf prog₁) ≡ 2
_ = refl
_ : valueCount (burstOf prog₂) ≡ 6
_ = refl
_ : valueCount (burstOf prog₃) ≡ 14
_ = refl
_ : valueCount (burstOf prog₄) ≡ 30
_ = refl

_ : syncSizeᵉ prog₄ ≡ 20
_ = refl


maxInstant : ∀ {A : Set} → List (InstEmit A) → ℕ
maxInstant b = foldr (λ em acc → InstEmit.instant em ⊔ acc) 0 b

-- LOAD-BEARING, and it is what makes this a PER-INSTANT refutation rather
-- than a statement about a whole run: every emit in the burst carries
-- instant 0.  Would fail if the merged inners were deferred to later ticks.
_ : maxInstant (burstOf prog₄) ≡ 0
_ = refl

----------------------------------------------------------------------
-- § 3  VERDICT — `k ≤ syncSizeᵉ e` IS FALSE.
--
--   K | valueCount | syncSizeᵉ | k ≤ syncSizeᵉ ?   | row
--   1 |      2     |    17     |  2 ≤ 17   YES     | LOAD-BEARING
--   2 |      6     |    18     |  6 ≤ 18   YES     | LOAD-BEARING
--   3 |     14     |    19     | 14 ≤ 19   YES     | LOAD-BEARING
--   4 |     30     |    20     | 30 > 20   **NO**  | LOAD-BEARING, REFUTES
--
-- valueCount = 2^(K+1) − 2 (exponential in the source length);
-- syncSizeᵉ  = 16 + K      (linear).  They cross at K = 4 and the gap only
-- widens.  Every number by `refl`; every emit at instant 0 (§ 2 above).
--
-- WHY.  `syncSizeᵉ (mergeAllᵉ e) = suc (syncSizeᵉ e)` (Exp.agda:509) charges
-- a bare `suc` for a merge, but a merge over a doubling accumulator
-- SUBSCRIBES an exponentially large tree of live leaves inside the one
-- instant.  A syntactic measure that charges additively cannot bound a
-- multiplicative runtime effect.
--
-- WHAT IT KILLS.  Any anchor route through "emissions per instant ≤
-- syncSizeᵉ e" — including `sync-count-bounded` in
-- Battery-Instant-Headroom.agda, whose abstract `SyncCount` is FALSE the
-- moment it is instantiated to the real value count, and the chain
-- `sizeᵛ o ≤ 12·2^k ≤ 12·2^(syncSizeᵉ e)` built on it.  Since k is itself
-- exponential in program size, `sizeᵛ o` is DOUBLY exponential in entry
-- data, not `12·2^sz`.
--
-- WHAT IT DOES NOT KILL.  The three dry postulates bound `sizeᵛ` at
-- `sizeCapAt e sl (suc id)`, which is tower-shaped and may still dominate a
-- doubly-exponential value.  That is now an OPEN question, and a different
-- one from the one this file closes.
--
-- SHAPES COVERED: doubling `scanᵉ` over a live `ofᵉ` seed, K = 1..4, plus
-- two degenerate zero-emission rows.  NOT COVERED: `μᵉ`, shared slots,
-- `concatAllᵉ`/`switchAllᵉ`/`exhaustAllᵉ`, sources beyond `ofᵉ`.  One
-- counterexample suffices for the refutation; no claim is made about shapes
-- outside this list.
----------------------------------------------------------------------
