-- Battery-Reached-Sizes.agda
--
-- QUESTION: What sizes do inner observables actually have when they arrive
-- at subscribeInner (Evaluator:1109) — the hop-edge call site?
--
-- APPROACH: Run subscribeE on the scan sub-expression and extract the emitted
-- inner observable values via splitBurst.  These ARE the values that reach
-- subscribeInner's `o` argument in the full mergeAllᵉ (scanᵉ …) program.
--
-- THE HANDOFF CHAIN (all Evaluator line numbers):
--   mergeAllᵉ b subscribed via subscribeAll (1307–1316)
--   → subscribeE fuel b (thru-outer mergeᵒ nid ↠ root) returns burst [structural]
--   → pushBurst fuel id now (thru-outer mergeᵒ nid) root burst (1295–1303)
--   → stepFrame fuel … (thru-outer mergeᵒ nid) κ vals fin (1272–1273)
--   → thruWalk fuel mergeᵒ nid root id now vals (1149–1153)
--   → for each o ∈ vals: thruConsume → subscribeInner fuel mergeᵒ nid root id now o
--     (1107–1110)
-- where vals = proj₁ (splitBurst (burst from subscribeE fuel (scanᵉ step seed src_k) …)).
-- Running subscribeE on (scanᵉ step seed src_k) and calling splitBurst IS
-- running the evaluator's scan path; it produces exactly [acc₁, …, acc_k] via
-- scanVals (1052–1056) — not via direct applyFn.
--
-- SECTIONS:
--   § 0  Setup: step, seed, no-slot context (mirrors Battery-Obs-Growth.agda)
--   § 1  Scan evaluator run: reached inner observable sizes (source lengths 1–4)
--   § 2  Full program metrics: sizeᵉ and slotsSize by source length + hasDry
--   § 3  Tripling experiment: can growth beat doubling?
--   § 4  connect-edge verdict: is sizeᵉ d ≤ Ŝ entry-computable?
--
-- PROBE-LYING GUARDS applied throughout:
--   (a) VACUOUS ROWS: every sizeᵛ check tests a positive value that would
--       differ if the evaluator collapsed or mis-computed.
--   (b) HAND-BUILT STATES: § 1 reads values from splitBurst of a real
--       subscribeE run, not directly from applyFn.
--   (c) LOAD-BEARING labels: each check states its failure mode.
--   (d) NOT AN ASSEMBLY READ: these rows do NOT prove subscribeE-wet;
--       they only measure what o subscribeInner receives.

module Battery-Reached-Sizes where

open import Data.Bool    using (Bool; true; false)
open import Data.List    using (List; []; _∷_; map)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin     using (Fin) renaming (zero to fin₀)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Gas; g0; gs)
open import Rx.Exp       using (Ty; Ctx; obs; natᵗ; _×ᵗ_;
                                Val; Closed; Fn; Tm;
                                varᵗ; fstᵗ; nat̂; strmᵗ;
                                ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ;
                                sizeᵉ; sizeᵛ; evalTm; applyFn)
open import Rx.Evaluator using (Slots; Slot; shared; slotsSize;
                                Path; root; Stream;
                                sched-init; st-init; subscribeE;
                                splitBurst; hasDry; evaluate)

------------------------------------------------------------------------
-- § 0  SETUP — mirrors Battery-Obs-Growth.agda
------------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

-- The doubling step: acc ↦ mergeAllᵉ (ofᵉ [acc, acc]).
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

-- Named accumulator values (used to label checks and tripling experiment).
acc₀ acc₁ acc₂ acc₃ acc₄ : Val Γ₀ (obs natᵗ)
acc₀ = evalTm seed
acc₁ = applyFn step (acc₀ , 0)
acc₂ = applyFn step (acc₁ , 1)
acc₃ = applyFn step (acc₂ , 2)
acc₄ = applyFn step (acc₃ , 3)

-- CROSS-CHECK: sizes match Battery-Obs-Growth.agda.
_ : sizeᵛ (obs natᵗ) acc₀ ≡ 1;   _ = refl
_ : sizeᵛ (obs natᵗ) acc₁ ≡ 13;  _ = refl
_ : sizeᵛ (obs natᵗ) acc₂ ≡ 37;  _ = refl
_ : sizeᵛ (obs natᵗ) acc₃ ≡ 85;  _ = refl
_ : sizeᵛ (obs natᵗ) acc₄ ≡ 181; _ = refl

-- Small gas for scan-only subscriptions.  The scan over ofᵉ uses NO gas
-- decrements (no μ, no share connect, no subscribeInner) so any gas, even
-- g0, is sufficient.  gs^3 provides conservative safety.
smallGas : Gas
smallGas = gs (gs (gs g0))

------------------------------------------------------------------------
-- § 1  SCAN EVALUATOR RUN — reading sizes OUT of the burst
--
-- For source length k: run subscribeE on (scanᵉ step seed src_k) and
-- extract the emitted inner observable values with splitBurst.
-- These values are PRODUCED by scanVals (Evaluator:1052–1056); they
-- are NOT computed here by direct applyFn calls.
--
-- The values are what thruWalk at the thru-outer frame passes to
-- subscribeInner — see the handoff chain in the module header.
--
-- LOAD-BEARING label applies to every row:
-- • Wrong size → scan evaluator collapsed or step function incorrect.
-- • Empty list → splitBurst mis-extracted or scan emitted nothing.
-- • sizeᵛ = 1 → acc not updated (seed unchanged, doubling failed).
------------------------------------------------------------------------

scan₁ : Closed Γ₀ (obs natᵗ)
scan₁ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ []))

-- LOAD-BEARING (k=1): one inner obs of sizeᵛ = 13.
-- Degenerate failure: sizeᵛ ≡ 1 (identity step) or list empty.
_ : map (sizeᵛ (obs natᵗ))
      (proj₁ (splitBurst
        (proj₁ (subscribeE smallGas scan₁ root 0 0
                  (sched-init scan₁ ins₀) (st-init scan₁)))))
    ≡ 13 ∷ []
_ = refl

scan₂ : Closed Γ₀ (obs natᵗ)
scan₂ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ []))

-- LOAD-BEARING (k=2): two inner obs, max sizeᵛ = 37.
_ : map (sizeᵛ (obs natᵗ))
      (proj₁ (splitBurst
        (proj₁ (subscribeE smallGas scan₂ root 0 0
                  (sched-init scan₂ ins₀) (st-init scan₂)))))
    ≡ 13 ∷ 37 ∷ []
_ = refl

scan₃ : Closed Γ₀ (obs natᵗ)
scan₃ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))

-- LOAD-BEARING (k=3): the Battery-Obs-Growth program's scan.
-- max sizeᵛ = 85 against sizeᵉ prog₃ = 17 (5× the program size).
_ : map (sizeᵛ (obs natᵗ))
      (proj₁ (splitBurst
        (proj₁ (subscribeE smallGas scan₃ root 0 0
                  (sched-init scan₃ ins₀) (st-init scan₃)))))
    ≡ 13 ∷ 37 ∷ 85 ∷ []
_ = refl

scan₄ : Closed Γ₀ (obs natᵗ)
scan₄ = scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

-- LOAD-BEARING (k=4): max sizeᵛ = 181 against sizeᵉ prog₄ = 18 (10×).
_ : map (sizeᵛ (obs natᵗ))
      (proj₁ (splitBurst
        (proj₁ (subscribeE smallGas scan₄ root 0 0
                  (sched-init scan₄ ins₀) (st-init scan₄)))))
    ≡ 13 ∷ 37 ∷ 85 ∷ 181 ∷ []
_ = refl

------------------------------------------------------------------------
-- § 2  FULL PROGRAM METRICS
--
-- TABLE (all entries LOAD-BEARING):
--
--   k | sizeᵉ prog_k | slotsSize ins₀ | max sizeᵛ at subscribeInner
--   --+-------------+----------------+----------------------------
--   1 |      15     |       0        |          13
--   2 |      16     |       0        |          37
--   3 |      17     |       0        |          85    ← Battery-Obs-Growth prog
--   4 |      18     |       0        |         181
--
-- Reading: sizeᵉ grows LINEARLY (+1 per element) while max sizeᵛ grows
-- EXPONENTIALLY (×2 per step).  A linear anchor is refuted; an exponential
-- anchor with base ≥ 2 is consistent.
--
-- sizeᵉ prog_k = k + 14 (formula: sizeᵉ mergeAllᵉ = suc; scanᵉ adds
-- sizeᵗ step + sizeᵗ seed = 8+2=10; ofᵉ [k nats] = k+2; total = k+14).
------------------------------------------------------------------------

prog₁ : Closed Γ₀ natᵗ
prog₁ = mergeAllᵉ (scanᵉ step seed (ofᵉ (nat̂ 0 ∷ [])))

prog₂ : Closed Γ₀ natᵗ
prog₂ = mergeAllᵉ (scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ [])))

prog₃ : Closed Γ₀ natᵗ
prog₃ = mergeAllᵉ (scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])))

prog₄ : Closed Γ₀ natᵗ
prog₄ = mergeAllᵉ (scanᵉ step seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

-- LOAD-BEARING: sizeᵉ = k + 14 formula.
_ : sizeᵉ prog₁ ≡ 15; _ = refl
_ : sizeᵉ prog₂ ≡ 16; _ = refl
_ : sizeᵉ prog₃ ≡ 17; _ = refl
_ : sizeᵉ prog₄ ≡ 18; _ = refl

-- LOAD-BEARING: no slots in ins₀ (syntax-only programs, no scripted inputs).
_ : slotsSize ins₀ ≡ 0
_ = refl

-- hasDry: gas budget is sufficient for all inner subscriptions.
-- LOAD-BEARING: hasDry ≡ true would mean acc_k's recursive mergeAll nesting
-- exceeded the budget (each subscribeInner peels one gs; deepest nesting
-- for prog_k is k+1 levels, well within budgetAt's tower).
_ : hasDry (evaluate 0 prog₁ ins₀) ≡ false; _ = refl
_ : hasDry (evaluate 0 prog₂ ins₀) ≡ false; _ = refl
_ : hasDry (evaluate 0 prog₃ ins₀) ≡ false; _ = refl
-- prog₄ hasDry check omitted: budgetAt prog₄ ins₀ 0 involves gasTower
-- which normalizes slowly for larger program sizes.  The k=1..3 checks
-- establish the pattern; k=4 holds by the same budget argument.

------------------------------------------------------------------------
-- § 3  TRIPLING EXPERIMENT — can growth beat doubling?
--
-- Hypothesis: the tripling step (3 accumulator copies) still produces
-- EXPONENTIAL growth, just with base 3 instead of 2.  No fixed step
-- function can produce super-exponential growth.
--
-- ARGUMENT: for any step function Fn of size S and branching factor n
-- (= number of accumulator occurrences in the output), the recurrence is
--   sizeᵛ acc_{k+1} = C_S + n · sizeᵛ acc_k
-- giving sizeᵛ acc_k = O(n^k).  The maximum n ≤ S ≤ sizeᵉ e.
-- Super-exponential growth would require n to grow with k — impossible
-- for a fixed Fn.  Even embedding a scanᵉ inside the step only produces
-- linear growth (one copy, so n=1 → arithmetic growth).
--
-- CONCLUSION: Ŝ ≈ 12·2^k is the RIGHT SHAPE — exponential — and the
-- specific base depends only on the step's branching factor.  capsH is a
-- tower-of-towers that dominates any polynomial-base exponential.
------------------------------------------------------------------------

step₃ : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step₃ = strmᵗ (mergeAllᵉ
                (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                      fstᵗ (varᵗ (here refl)) ∷
                      fstᵗ (varᵗ (here refl)) ∷ [])))

acc₁₃ acc₂₃ acc₃₃ : Val Γ₀ (obs natᵗ)
acc₁₃ = applyFn step₃ (acc₀ , 0)
acc₂₃ = applyFn step₃ (acc₁₃ , 1)
acc₃₃ = applyFn step₃ (acc₂₃ , 2)

-- LOAD-BEARING: exact tripling-step sizes.
-- Recurrence: A_{k+1} = 3·A_k + 15 (with A_0=1).
-- A_1 = 3·1 + 15 = 18; A_2 = 3·18 + 15 = 69; A_3 = 3·69 + 15 = 222.
-- Derivation: fstᵗ(pairᵗ(strmᵗ acc_k)(nat̂ k)) has size A_k+4;
-- ofᵉ[t₁,t₂,t₃] has sizeᵗˢ = 3(A_k+4)+1 = 3A_k+13; mergeAllᵉ adds 2.
-- So A_{k+1} = 3A_k + 15.
_ : sizeᵛ (obs natᵗ) acc₁₃ ≡ 18;  _ = refl
_ : sizeᵛ (obs natᵗ) acc₂₃ ≡ 69;  _ = refl
_ : sizeᵛ (obs natᵗ) acc₃₃ ≡ 222; _ = refl

-- VERIFY via scan run: subscribeE on the tripling scan produces the same values.
scan₃₃ : Closed Γ₀ (obs natᵗ)
scan₃₃ = scanᵉ step₃ seed (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ []))

-- LOAD-BEARING (tripling, k=3): evaluator agrees with applyFn; confirms
-- the scan evaluator path (scanVals → thruWalk → subscribeInner) produces
-- the tripling-step values.
_ : map (sizeᵛ (obs natᵗ))
      (proj₁ (splitBurst
        (proj₁ (subscribeE smallGas scan₃₃ root 0 0
                  (sched-init scan₃₃ ins₀) (st-init scan₃₃)))))
    ≡ 18 ∷ 69 ∷ 222 ∷ []
_ = refl

-- SHAPE VERDICT: doubling gives 2^k growth; tripling gives 3^k; an n-copy
-- step gives n^k.  All are exponential.  No fixed step beats exponential.
-- Ŝ must be at least exponential in k.  capsH = blowH (capsBase e ins)
-- is a tower, dominating any fixed exponential.

------------------------------------------------------------------------
-- § 4  connect-edge VERDICT
--
-- connect-edge (Wet.agda:4066) requires sizeᵉ d ≤ Ŝ where sl i ≡ shared d.
-- The claim is: this is FREE from entry data alone, with no runtime growth.
--
-- DERIVATION:
--   slotSize (shared d) = sizeᵉ d          (Slots.agda:61)
--   slotsSize ins = Σ_i slotSize (ins i) ≥ sizeᵉ d   (the i-th summand)
--   capsBase e ins = 2 + sizeᵉ e + slotsSize ins > sizeᵉ d
--   Ŝ = cSize (capsAt e ins id) ≥ cSize (baseCaps e ins) = capsBase e ins
--   ∴ sizeᵉ d ≤ slotsSize ins < Ŝ  — all computable from entry data.
--
-- CONTRAST: hop-edge needs sizeᵛ o ≤ Ŝ for a RUNTIME value o (the scan
-- accumulator) that can grow exponentially in the emission count.
-- connect-edge needs sizeᵉ d ≤ Ŝ for a SYNTAX term d fixed at entry.
-- Only hop-edge is hard; connect-edge follows from entry data.
--
-- DEMONSTRATION: a concrete shared slot.
------------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ᵛ []ᵛ

-- Shared def: a small expression (size 5).
d₁ : Closed Γ₁ natᵗ
d₁ = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

ins-shared : Slots Γ₁
ins-shared fin₀ = shared d₁

-- LOAD-BEARING: sizeᵉ d₁ = slotSize (shared d₁) = slotsSize ins-shared.
-- This confirms that the shared def's static size IS the slot's full contribution.
-- Failure: if slotSize or slotsSize computed differently, these would differ.
_ : sizeᵉ d₁ ≡ 5
_ = refl

_ : slotsSize ins-shared ≡ 5
_ = refl

-- sizeᵉ d₁ ≤ slotsSize ins-shared (follows from equality; shown explicitly).
-- LOAD-BEARING: confirms the bound direction (not just equality in this case).
_ : sizeᵉ d₁ ≤ slotsSize ins-shared
_ = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

-- VERDICT: connect-edge's sizeᵉ d ≤ Ŝ is entailed by entry data alone.
-- It is not the hard edge.  Only hop-edge (the observable growth edge) is.
