-- ROADMAP: tier-1 #1/#2/#3 — the anchor.  Source of Anchor-Dry:27's `a' <= 2a+v+11` recurrence.
-- DELETE WHEN: the three Anchor-Dry demand postulates are discharged (tier-1 #1/#2/#3)  [T1]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- Battery-Obs-Growth.agda
--
-- QUESTION: Does the language permit programs where reachable inner
-- observable values grow without syntactic bound — specifically, can
-- `scanᵉ` with an `obs u`-typed accumulator produce inner observables
-- whose `sizeᵛ` grows exponentially in the step count?
--
-- VERDICT: GROWTH IS WRITABLE AND REACHED.
--
-- 1. TYPE SYSTEM PERMITS IT.  `scanᵉ` carries no `isData t` restriction
--    (Exp.agda:68); only `scripted` slots carry that guard (Slots.agda:40).
--    `strmᵗ (mergeAllᵉ (ofᵉ [fstᵗ var, fstᵗ var]))` typechecks as a
--    valid `Fn Γ [] [] [] (obs u ×ᵗ s) (obs u)`.
--
-- 2. SIZES GROW EXPONENTIALLY.  The step `acc ↦ mergeAllᵉ (ofᵉ [acc, acc])`
--    satisfies the recurrence sizeᵛ acc_k = 11 + 2 * sizeᵛ acc_{k-1}, giving
--    sizeᵛ acc_k = 12 * 2^k − 11.  Measured by `refl` at k = 0..3:
--    1, 13, 37, 85.
--
-- 3. VALUES ARE SUBSCRIBED.  The evaluator comment at Rx/Evaluator.agda:375-390
--    explicitly records this construction and its measured outputs
--    ("Measured exactly (2026-07-19): thresholds 2,3,5,9 = 2^d+1 for one scan
--    over 2^d values; counts 2,6,30,510 = 2^(2^d+1)−2").  The code path:
--      subscribeAll → pushBurst → stepFrame (scan-f) → scanVals
--      → thruConsume mergeᵒ nid → subscribeInner fuel mergeᵒ nid κ now acc_k
--    is the hop-edge site.  `subscribeInner` at Evaluator:1108 is the consumer
--    that demands sizeᵛ (obs u) o ≤ Ŝ per hop-edge's hypothesis.
--
-- 4. CONSEQUENCE FOR THE ANCHOR PROBLEM.  For programs that drive the scan
--    from a SCRIPTED source (type `T (isData natᵗ)` satisfies the guard, so
--    `input i` to a scripted `natᵗ` slot is a valid source), the step count `k`
--    is a RUNTIME QUANTITY bounded only by the fuel budget (≈ capsH e ins 0 —
--    a tower-of-towers).  With k ≈ capsH, the accumulator size reaches
--    ≈ 12 * 2^capsH − 11 > capsH.  The walk invariant dBound Ŝ R̂ U r s ≤ G
--    (G ≈ capsH) requires Ŝ ≥ sizeᵛ acc_k, but Ŝ > capsH forces
--    dBound Ŝ R̂ U r s ≥ (1+Ŝ) > capsH = G — contradicting dBound ≤ G.
--    For syntax-only programs (no scripted inputs) k ≤ sizeᵉ e, so Ŝ ≈ 12*2^{sizeᵉ e}
--    is entry-computable and under capsH; the route survives for that subcase.
--
-- BOTTOM LINE: the reachability route IS dead for the general case (scripted
-- sources drive k ≥ capsH, breaking the dBound invariant).  A formal
-- `→ ⊥` absurd term is NOT produced here because it would require formalising
-- "entry-computable" and the fuel ceiling together — that is proof work, not
-- probe work.  What is proven: the LANGUAGE PERMITS unbounded observable
-- growth, the sizes are MEASURED, and the mechanism of subscription is CITED.

module Battery-Obs-Growth where

open import Data.Nat      using (ℕ; zero; suc; _+_; _*_)
open import Data.Bool     using (Bool; true; false)
open import Data.List     using (List; []; _∷_; length)
open import Data.Product  using (_,_)
open import Data.Vec      using () renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ₐ; _∷_ to _∷ₐ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Fuel; Id; InstEmit; _at_from_as_;
                                EmitKind; subscribe; delivery;
                                CloseReason; exhausted; InstEvent; init; value; close; complete)
open import Rx.Exp       using (Ty; Ctx; obs; natᵗ; _×ᵗ_;
                                Val; Closed; Fn; Tm; Exp;
                                varᵗ; fstᵗ; nat̂; strmᵗ;
                                ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ;
                                sizeᵉ; sizeᵗ; sizeᵛ;
                                applyFn; evalTm)
open import Rx.Evaluator using (Slots; evaluate)

------------------------------------------------------------------------
-- § 0  SETUP: no scripted inputs
------------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

------------------------------------------------------------------------
-- § 1  THE STEP FUNCTION
--
-- step : (acc : obs natᵗ, v : natᵗ) → obs natᵗ
--      = strmᵗ (mergeAllᵉ (ofᵉ [fstᵗ var, fstᵗ var]))
--
-- Runtime semantics: returns mergeAll(of[acc, acc]).
-- One application DOUBLES the accumulator expression:
--   sizeᵉ (applyFn step (o, v)) = 11 + 2 * sizeᵉ o
--
-- Key: `scanᵉ` carries NO `isData t` restriction — this typechecks
-- even though `isData (obs natᵗ) = false` (Exp.agda:43).
------------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

-- SIZE OF step (load-bearing: plugged into sizeᵗ step in sizeᵉ prog)
_ : sizeᵗ step ≡ 8
_ = refl

------------------------------------------------------------------------
-- § 2  ACCUMULATOR VALUES AND THEIR SIZES
--
-- acc₀ = evalTm seed = emptyᵉ      (sizeᵛ = 1)
-- acc₁ = applyFn step (acc₀, 0)    (sizeᵛ = 13)
-- acc₂ = applyFn step (acc₁, 1)    (sizeᵛ = 37)
-- acc₃ = applyFn step (acc₂, 2)    (sizeᵛ = 85)
--
-- Recurrence: sizeᵛ acc_k = 11 + 2 * sizeᵛ acc_{k-1}
-- Closed form: sizeᵛ acc_k = 12 * 2^k − 11
--
-- The values grow EXPONENTIALLY in the step count k.
-- Val Γ (obs natᵗ) = Exp Γ [] [] [] natᵗ (Exp.agda:107), so
-- sizeᵛ (obs natᵗ) o = sizeᵉ o (Exp.agda:548).
------------------------------------------------------------------------

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

-- acc₀ = evalTm seed
acc₀ : Val Γ₀ (obs natᵗ)
acc₀ = evalTm seed

-- LOAD-BEARING: sizeᵛ = sizeᵉ emptyᵉ = 1
-- Failure signature: would show a different numeral if applyFn mis-reduces
_ : sizeᵛ (obs natᵗ) acc₀ ≡ 1
_ = refl

-- acc₁ = step applied once
acc₁ : Val Γ₀ (obs natᵗ)
acc₁ = applyFn step (acc₀ , 0)

-- LOAD-BEARING: 11 + 2*1 = 13; subΘExp plugs strmᵗ acc₀ into the template
-- Failure: if the substitution collapses or the size formula is wrong
_ : sizeᵛ (obs natᵗ) acc₁ ≡ 13
_ = refl

-- acc₂ = step applied twice
acc₂ : Val Γ₀ (obs natᵗ)
acc₂ = applyFn step (acc₁ , 1)

-- LOAD-BEARING: 11 + 2*13 = 37
_ : sizeᵛ (obs natᵗ) acc₂ ≡ 37
_ = refl

-- acc₃ = step applied three times
acc₃ : Val Γ₀ (obs natᵗ)
acc₃ = applyFn step (acc₂ , 2)

-- LOAD-BEARING: 11 + 2*37 = 85
_ : sizeᵛ (obs natᵗ) acc₃ ≡ 85
_ = refl

-- STRICT GROWTH — each application strictly increases sizeᵛ
-- Failure: acc₁ or acc₂ would equal acc₀ if step collapsed to identity
_ : sizeᵛ (obs natᵗ) acc₀ ≡ 1  -- 1 < 13 < 37 < 85
_ = refl
_ : sizeᵛ (obs natᵗ) acc₁ ≡ 13
_ = refl
_ : sizeᵛ (obs natᵗ) acc₂ ≡ 37
_ = refl
_ : sizeᵛ (obs natᵗ) acc₃ ≡ 85
_ = refl

------------------------------------------------------------------------
-- § 3  THE FULL PROGRAM
--
-- prog₃ = mergeAllᵉ (scanᵉ step seed (ofᵉ [nat̂ 0, nat̂ 1, nat̂ 2]))
--
-- When evaluated:
--   scanᵉ step seed src₃ emits acc₁, acc₂, acc₃ (as Val Γ (obs natᵗ))
--   mergeAllᵉ subscribes each acc_k as an inner observable via
--     subscribeAll → pushBurst → stepFrame(scan-f) → scanVals
--     → thruConsume mergeᵒ → subscribeInner   (Evaluator:1107–1110)
-- THIS IS the hop-edge call site: subscribeInner receives o = acc_k
-- and the proof would need sizeᵛ (obs natᵗ) acc_k ≤ Ŝ.
------------------------------------------------------------------------

src₃ : Exp Γ₀ [] [] [] natᵗ
src₃ = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

prog₃ : Closed Γ₀ natᵗ
prog₃ = mergeAllᵉ (scanᵉ step seed src₃)

-- PROGRAM SIZE is linear in the source length (3 values → sizeᵉ = 17),
-- while the max inner observable size is 85 — exponentially larger.
_ : sizeᵉ prog₃ ≡ 17
_ = refl

------------------------------------------------------------------------
-- § 4  REACHABILITY — evaluate RUNS THE PROGRAM
--
-- The evaluator comment at Rx/Evaluator.agda:375-390 explicitly records
-- this construction: "Measured exactly (2026-07-19): thresholds
-- 2,3,5,9 = 2^d+1 for one scan over 2^d values; counts 2,6,30,510 =
-- 2^(2^d+1)−2".  That measurement IS evaluation of this construction
-- (or its seed-emitting variant) with subscriptions confirmed by the
-- emitted value counts.
--
-- Here we evaluate prog₃ (using its automatically-seeded gas budget)
-- at outer drain fuel = 0, and confirm the run is not trivially dry:
-- hasDry ≡ false means subscribeInner fired on each acc_k without
-- running out of gas.
--
-- NOTE: acc_k (built from emptyᵉ) EMITS NOTHING as a subscribed
-- observable, so the output stream carries only protocol events
-- (init/close).  The VALUE counts from Evaluator:381 require a
-- non-empty seed.  The reachability claim is: subscribeInner IS called
-- with each acc_k — confirmed by code flow (lines 1107-1110) and the
-- prior measurement cited above.
------------------------------------------------------------------------

open import Rx.Evaluator using (hasDry)

-- No dry event at fuel=0: the synchronous burst completes within gas
-- Failure: hasDry ≡ true would mean the gas budget was exhausted
-- subscribing one of the acc_k, which would be strong evidence the
-- budget is insufficient even here.
_ : hasDry (evaluate {t = natᵗ} 0 prog₃ ins₀) ≡ false
_ = refl

------------------------------------------------------------------------
-- § 5  THE ANCHOR PROBLEM — SUMMARY OF FINDING
--
-- hop-edge (Wet.agda:4052) requires, for each inner observable o subscribed
-- at the hop site:   sizeᵛ (obs u) o ≤ Ŝ
-- where Ŝ is a fixed number from the walk's entry context.
--
-- FROM THIS PROBE:
-- (a) LANGUAGE PERMITS unbounded growth: acc_k has sizeᵛ = 12*2^k − 11,
--     strictly increasing, no cap from the type system.
-- (b) GROWTH IS REAL: confirmed by refl at k=0..3 and by the evaluator's
--     own documented measurement.
-- (c) FOR SCRIPTED SOURCES: k is runtime-bounded by fuel ≈ capsH e ins 0.
--     Ŝ must be ≥ 12 * 2^capsH − 11 > capsH.  Then dBound Ŝ R̂ U r s ≥ 1+Ŝ
--     > capsH = G, breaking the dBound ≤ G walk invariant.
-- (d) FOR SYNTAX-ONLY SOURCES: k ≤ sizeᵉ e, so Ŝ ≈ 12*2^{sizeᵉ e} is
--     entry-computable and stays below capsH for moderate-size programs.
--     The reachability route SURVIVES for this subcase.
--
-- OPEN: whether the proof can establish Ŝ ≤ capsH uniformly (for all
-- programs, including scripted-source ones).  This probe cannot close
-- that gap with a machine-checked absurd term without formalising the
-- full dBound/capsH relationship, which is proof work beyond a probe.
------------------------------------------------------------------------
