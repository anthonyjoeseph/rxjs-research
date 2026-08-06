-- Battery-Mu-Emissions.agda
--
-- QUESTION: Can a μᵉ-driven source, within ONE anchor scope (one subscribe
-- walk, or one cascade), emit MORE values into a doubling scanᵉ than anything
-- computable from `e` and `ins`?
--
-- This is the DECIDING FORM of THE ANCHOR PROBLEM (PROOF-STATE.md):
-- if k (emission count) is bounded by entry data, then Ŝ ≈ 12·2^k is
-- entry-computable and the route survives.  If k escapes, the route is dead.
--
-- VERDICTS:
--
--   WALK SCOPE (one synchronous subscribe frame, one tick):
--   ENTRY-BOUNDED.
--   Restriction: Exp.agda:76–78 (μᵉ binds into Δᵍ; varᵉ reads Δ only;
--   deferᵉ is the sole gate from Δᵍ → Δ, at a tick cost).
--   Bound: synchronous emissions per walk ≤ syncSizeᵉ e ≤ sizeᵉ e.
--   Mechanism: unfoldμ substitutes (μᵉ body) ONLY at deferᵉ-gated positions
--   (elimGExp:350–351); syncSizeᵉ (deferᵉ e) = 1 for any e (Exp.agda:515);
--   so syncSizeᵉ is INVARIANT under μ-unfolding (postulate below, refl-verified
--   for our concrete source).
--   THE SYNC-μ RULING IS THE LOAD-BEARING FACT OF THE ANCHOR PROOF.
--
--   CASCADE SCOPE (one cascade, possibly spanning multiple ticks):
--   ENTRY-BOUNDED.
--   Bound: total emissions across one cascade ≤ gas × syncSizeᵉ e.
--   Per-tick: ≤ syncSizeᵉ e (same bound as walk, same mechanism applies
--   because every tick begins a fresh synchronous scope for the deferred body).
--   Ticks per cascade: ≤ gas (subscribeE g0 (μᵉ body) = dryBurst,
--   Evaluator:1452 — each μ-unfold costs one gs layer).
--   gas = capsH(e, ins) — entry-computable.
--   Both factors entry-computable → total IS entry-computable.
--   NOTE: sizeᵛ (acc at tick k) ≈ 12·2^k grows without a LINEAR bound in
--   capsH; the REMAINING open question (NOT answered here) is whether this
--   Ŝ ≤ capsH uniformly.  The emission-COUNT question is answered: ENTRY-BOUNDED.
--
-- ESCAPING PROGRAM ATTEMPT:
--   The escaping program μᵉ (varᵉ (here refl)) is a TYPE ERROR.
--   varᵉ requires its index in Δ (usable context); inside μᵉ body, the bound
--   variable is in Δᵍ (guarded context).  The ONLY gate from Δᵍ to Δ is
--   deferᵉ (Exp.agda:78), which is a tick boundary.  No synchronous self-
--   subscription is writeable; the typechecker enforces this structurally.

module Battery-Mu-Emissions where

open import Data.Nat      using (ℕ; zero; suc; _+_)
open import Data.Bool     using (Bool; true; false)
open import Data.List     using (List; []; _∷_)
open import Data.Vec      using () renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp       using (Ty; Ctx; obs; natᵗ; _×ᵗ_;
                                Val; Closed; Fn; Tm; Exp;
                                varᵗ; fstᵗ; nat̂; strmᵗ;
                                ofᵉ; emptyᵉ; mergeAllᵉ; concatAllᵉ; scanᵉ;
                                μᵉ; varᵉ; deferᵉ;
                                sizeᵉ; sizeᵛ; syncSizeᵉ;
                                applyFn; evalTm; unfoldμ)
open import Rx.Evaluator using (Slots; evaluate; hasDry)

------------------------------------------------------------------------
-- § 0  SETUP
------------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

noSlots : Slots Γ₀
noSlots ()

-- THE DOUBLING STEP (same as Battery-Obs-Growth.agda §1).
-- step (acc, v) = mergeAll(of[acc, acc])
-- Each application: sizeᵛ (step acc_k v) = 11 + 2 * sizeᵛ acc_k.
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ
               (ofᵉ (fstᵗ (varᵗ (here refl)) ∷
                     fstᵗ (varᵗ (here refl)) ∷ [])))

-- SEED: acc₀ = emptyᵉ (sizeᵛ = 1).
seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

------------------------------------------------------------------------
-- § 1  THE TYPE-LEVEL GATE (Exp.agda:76–78)
--
-- μᵉ : Exp Γ (t ∷ Δᵍ) Δ Θ t → Exp Γ Δᵍ Δ Θ t   (binds into Δᵍ)
-- varᵉ : t ∈ Δ → Exp Γ Δᵍ Δ Θ t                 (reads from Δ, NOT Δᵍ)
-- deferᵉ : Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t (sole gate Δᵍ → Δ)
--
-- Consequence: inside μᵉ body, the bound variable sits in Δᵍ.
-- varᵉ cannot read it directly — only after deferᵉ moves it into Δ.
-- ESCAPING PROGRAM μᵉ (varᵉ (here refl)) IS A TYPE ERROR:
--   here refl : t ∈ (t ∷ Δᵍ)  but  varᵉ needs  t ∈ Δ
-- The typechecker enforces this; no synchronous self-subscription is writable.
--
-- The following DOES typecheck — deferᵉ is the required tick gate:
------------------------------------------------------------------------

-- The simplest guarded body: defer the self-reference to the next tick.
gate-body : ∀ {n} {Γ : Ctx n} {t} → Exp Γ (t ∷ []) [] [] t
gate-body = deferᵉ (varᵉ (here refl))

-- LOAD-BEARING: deferᵉ is a LEAF in syncSizeᵉ (Exp.agda:515).
-- syncSizeᵉ (deferᵉ e) = 1 regardless of e.
-- This is the structural fact that makes the sync-μ invariant work:
-- substituting anything at a deferᵉ-gated position cannot change syncSizeᵉ.
_ : syncSizeᵉ (gate-body {Γ = Γ₀} {t = natᵗ}) ≡ 1
_ = refl

-- Failure signature: if deferᵉ were NOT a leaf (e.g. if syncSizeᵉ (deferᵉ e)
-- = suc (syncSizeᵉ e)), the invariant would be false and μ-unfolding would
-- grow sync size without bound.

------------------------------------------------------------------------
-- § 2  CONCRETE μ-SOURCE
--
-- μ-body = concatAllᵉ (of [strmᵗ (of [nat̂ 0]),  strmᵗ (deferᵉ (varᵉ x))])
--
-- Semantics: at every tick, concatAllᵉ subscribes the FIRST segment
-- (of [nat̂ 0] — emits one nat synchronously) and then subscribes the
-- SECOND segment (deferᵉ (varᵉ x) — schedules the recursive call for the
-- next tick, emits ZERO values in the current tick).
--
-- This is the MAXIMAL synchronous emitter from a μᵉ with one literal value:
-- one emission per tick, zero growth in syncSizeᵉ across unfolds.
------------------------------------------------------------------------

μ-body : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
μ-body = concatAllᵉ (ofᵉ
           (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷
            strmᵗ (deferᵉ (varᵉ (here refl))) ∷ []))

μ-src : Closed Γ₀ natᵗ
μ-src = μᵉ μ-body

-- Size: sizeᵉ μ-src ≡ 11, syncSizeᵉ μ-body ≡ 9.
-- LOAD-BEARING (non-degenerate: μ-body has both sync and deferred parts).
_ : sizeᵉ μ-src ≡ 11
_ = refl

_ : syncSizeᵉ μ-body ≡ 9
_ = refl

------------------------------------------------------------------------
-- § 3  WALK SCOPE: SYNC SIZE IS INVARIANT UNDER μ-UNFOLDING
--
-- KEY CLAIM: syncSizeᵉ (unfoldμ body) = syncSizeᵉ body
--
-- Reason: unfoldμ = elimGExp (here refl) (μᵉ body) body.
-- elimGExp only substitutes inside deferᵉ (see elimGExp:350–351);
-- syncSizeᵉ (deferᵉ e) = 1 for ANY e (§1 above);
-- therefore the substitution cannot change syncSizeᵉ.
--
-- CONSEQUENCE: no matter how many times a μᵉ unfolds, the synchronous
-- emission count per tick stays ≤ syncSizeᵉ body ≤ sizeᵉ e.
-- This is the bound k ≤ sizeᵉ e that makes Ŝ ≈ 12·2^k entry-computable.
------------------------------------------------------------------------

-- LOAD-BEARING: syncSizeᵉ is preserved under one μ-unfolding.
-- Failure: if this refl fails, then unfoldμ changes syncSize, invalidating
-- the whole entry-boundedness argument.
_ : syncSizeᵉ (unfoldμ μ-body) ≡ syncSizeᵉ μ-body
_ = refl

-- BY CONTRAST: sizeᵉ GROWS under unfolding (the deferred position
-- changes from varᵉ (size 1) to wkExp (μᵉ body) (size 11)).
-- After one unfold, size doubles from 10 to 20 in the body.
_ : sizeᵉ μ-body ≡ 10
_ = refl

_ : sizeᵉ (unfoldμ μ-body) ≡ 20
_ = refl

-- CONTRAST SUMMARY:
-- sizeᵉ body = 10;   sizeᵉ (unfoldμ body) = 20    — GROWS (doubled)
-- syncSizeᵉ body = 9; syncSizeᵉ (unfoldμ body) = 9 — STABLE (invariant)
-- This is the formal content of "syncSize is the right measure."

------------------------------------------------------------------------
-- § 4  DOUBLING SCAN ON μ-SRC
--
-- scan-on-μ = mergeAllᵉ (scanᵉ step seed μ-src)
--
-- Walk scope (fuel=0, one synchronous tick):
--   μ-src emits nat̂ 0 once → scan produces acc₁ (sizeᵛ = 13)
--   → mergeAllᵉ subscribes acc₁ (finite, no gas issue)
--   Deferred recursive call is NOT processed at fuel=0.
--   EMISSION COUNT k = 1 ≤ syncSizeᵉ μ-body = 9 ≤ sizeᵉ e.
--
-- Cascade scope (fuel=F, F+1 ticks):
--   Each tick: μ-src emits nat̂ 0 again → scan accumulates → acc_{k+1} subscribed
--   acc_k has sizeᵛ = 12·2^k − 11 (Battery-Obs-Growth.agda §2)
--   EMISSION COUNT after F ticks: k = F+1 ≤ capsH(e, ins) + 1 — ENTRY-BOUNDED.
------------------------------------------------------------------------

scan-on-μ : Closed Γ₀ natᵗ
scan-on-μ = mergeAllᵉ (scanᵉ step seed μ-src)

-- WALK SCOPE reachability (fuel=0, synchronous only):
-- hasDry ≡ false: the walk completes within gas (k=1 μ-unfold, acc₁ subscribed).
-- LOAD-BEARING: if true, the gas budget fails for a 1-emission walk — that would
-- be a budget-sufficiency failure independent of μ recursion.
_ : hasDry (evaluate {t = natᵗ} 0 scan-on-μ noSlots) ≡ false
_ = refl

-- CASCADE SCOPE reachability (fuel=1, 2 ticks):
-- deferred μ-src fires at tick 1 → acc₂ (sizeᵛ=37) subscribed.
-- hasDry ≡ false: k=2 emissions, both subscriptions within gas.
-- LOAD-BEARING: verifies the cascade's 2nd tick still fits in gas;
-- would fail if sizeᵛ acc₂ = 37 exceeded the hop-edge's available budget.
_ : hasDry (evaluate {t = natᵗ} 1 scan-on-μ noSlots) ≡ false
_ = refl

-- fuel=2, 3 ticks: acc₃ (sizeᵛ=85) subscribed.
-- LOAD-BEARING: 3rd emission still within gas.
_ : hasDry (evaluate {t = natᵗ} 2 scan-on-μ noSlots) ≡ false
_ = refl

------------------------------------------------------------------------
-- § 5  FORMAL STATEMENTS
--
-- WALK SCOPE:
--   THE STRUCTURAL INVARIANT (provable, stated as postulate for probe):
--   syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body  for any body.
--   Proof sketch: induction on body; only deferᵉ clauses change, and
--   syncSizeᵉ (deferᵉ e) = 1 for any e (Exp.agda:515).
--   This bounds synchronous emissions per tick ≤ syncSizeᵉ e ≤ sizeᵉ e.
--
-- CASCADE SCOPE:
--   Each tick's emissions ≤ syncSizeᵉ e (walk bound, same mechanism).
--   Total ticks ≤ gas (subscribeE g0 (μᵉ body) = dryBurst, Evaluator:1452).
--   gas = capsH(e, ins) — computable from entry data.
--   Total emissions across cascade ≤ capsH(e,ins) · syncSizeᵉ e — ENTRY-BOUNDED.
------------------------------------------------------------------------

-- THE LOAD-BEARING POSTULATE: syncSize-μ-invariant.
-- This is the formal statement of the sync-μ ruling being a TYPING INVARIANT,
-- not merely a programming discipline.
postulate
  syncSize-μ-invariant : ∀ {n} {Γ : Ctx n} {t}
    (body : Exp Γ (t ∷ []) [] [] t) →
    syncSizeᵉ (unfoldμ body) ≡ syncSizeᵉ body
-- Proof sketch: structural induction. Base: every non-deferᵉ, non-μᵉ constructor
-- propagates syncSizeᵉ unchanged. μᵉ case: elimGExp (there x) shifts the index,
-- same argument applies. deferᵉ case: elimGExp wraps in deferᵉ and calls
-- elimDExp inside; the result is still under deferᵉ; syncSizeᵉ (deferᵉ _) = 1
-- before and after substitution. varᵉ case: varᵉ y where y ∈ Δ (not Δᵍ) is
-- preserved unchanged by elimGExp (see elimGExp (varᵉ y) = varᵉ y, Exp.agda:349).
-- The guarded variable (in Δᵍ) only appears under deferᵉ by the type discipline.
-- Machine-verified for μ-body (§3 above): syncSizeᵉ (unfoldμ μ-body) ≡ 9 ≡ syncSizeᵉ μ-body.

