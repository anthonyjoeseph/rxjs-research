-- ROADMAP: tier-0 T0-2 — `subscribeInner-demand` (Anchor-Dry.agda:117).  Its only coverage.
-- DELETE WHEN: the three Anchor-Dry demand postulates are discharged (tier-1 #1/#2/#3)  [T1]
-- Mirrored in PROOF-STATE.md § "PROBE ROADMAP TIES".  If you change one,
-- change the other -- the duplication is deliberate cross-checking.
--
-- SubInner-Demand-Probe.agda  (2026-08-07)
--
-- QUESTION: what does subscribeInner-demand (Anchor-Dry.agda:117)
-- assert, and which pieces are decidable/provable at concrete programs?
--
-- THE POSTULATE HAS FIVE HYPOTHESES and ONE CONCLUSION:
--
--   Hyp 1  INV? Ψ B sched st ≡ true
--   Hyp 2  capsOK? (capsAt e sl id) sched st ≡ true
--   Hyp 3  valB? B Ψ (obs u) o ≡ true          (the inner observable)
--   Hyp 4  pathB? B Ψ κ ≡ true
--   Hyp 5  pathOccs? sz κ ≡ true
--   Concl  all (valB? Dm Ψ u) vs ≡ true
--     where vs  = proj₁(proj₂(subscribeInner g op allNid κ id now o sched st))
--           Dm  = (2*B + 12) * towerℕ (suc sz)
--           valB? N Ψ u v = (sizeᵛ u v ≤ᵇ N) ∧ (fnCapᵛ u v ≤ᵇ Ψ)
--
-- FINDINGS (detailed in §§ 1–4):
--
--   FULLY COMPUTABLE by refl at the initial state for no-slot programs:
--     Hyp 1 (INV?), Hyp 2 (capsOK?), Hyp 4 (pathB? root), Hyp 5 (pathOccs? root).
--     All reduce to `true` because all list structures in the initial state
--     are empty and the zero-case of ≤ᵇ absorbs the abstract bound B.
--
--   PARTIALLY STUCK:
--     Hyp 3 (valB? B Ψ (obs u) o): the fnCapᵛ conjunct is computable by refl;
--     the sizeᵛ ≤ᵇ B conjunct is stuck (B = sizeCapAt is abstract).
--     Symbolic discharge: sizeᵉ o ≤ sizeCapAt e sl id via iterSize-le-capsAt.
--
--   CONCLUSION:
--     sizeᵛ of returned values: COMPUTABLE by refl (§ 1, LOAD-BEARING rows).
--     fnCapᵛ ≤ ΨAt second conjunct: COMPUTABLE by refl (§ 2).
--     sizeᵛ ≤ Dm first conjunct: SYMBOLIC proof (§ 4).
--
-- PROGRAMS:
--   A  e_A = mergeAllᵉ(ofᵉ[strmᵗ inner_A]),  inner_A = ofᵉ[nat̂ 0, nat̂ 1]
--            subscribeInner returns [0, 1];  sizeᵛ natᵗ = [1, 1];  N_A = 1
--
--   B  e_B = exhaustAllᵉ(ofᵉ[strmᵗ inner_B]),  inner_B = ofᵉ[strmᵗ(ofᵉ[nat̂ 0])]
--            subscribeInner returns [ofᵉ[nat̂ 0]];  sizeᵛ(obs natᵗ) = [3];  N_B = 3
--
-- BUILD:
--   cd /Users/flipside-anthony/Developer/personal/rxjs-research/agda &&
--   ls probe/SubInner-Demand-Probe.agda &&
--   agda -i src -i probe probe/SubInner-Demand-Probe.agda
--
-- IMPORT CHAIN (cached interfaces — iteration is fast):
--   Rx.Exp, Rx.Evaluator, Verify-Budget-Sufficient.Wet
--   (Wet → Caps → Keeps-Ring → Measures all via public),
--   Verify-Budget-Sufficient.Caps-Face, Verify-Budget-Sufficient.Occurrences,
--   Verify-Budget-Sufficient.Caps

module SubInner-Demand-Probe where

open import Data.Bool using (Bool; true; false)
open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; *-monoˡ-≤; *-monoʳ-≤; *-mono-≤; +-monoˡ-≤; m≤m+n)
open import Data.List    using (List; []; _∷_; map)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec     using () renaming ([] to []ᵛ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs; towerℕ; Id)
open import Rx.Exp
  using (Ty; Ctx; Closed; Val; natᵗ; obs;
         ofᵉ; mergeAllᵉ; exhaustAllᵉ;
         nat̂; strmᵗ; sizeᵉ; sizeᵛ; evalTm)
open import Rx.Evaluator
  using (Slots; slotsSize; Path; root; mergeᵒ; exhaustᵒ; NodeId;
         subscribeInner; sched-init; st-init; EvalSt; Sched)

-- Wet imports Caps public → Keeps-Ring public → Measures public,
-- so INV?, ΨAt, sizeCapAt, capsAt, valB?, pathB?, fnCapᵛ,
-- fnCapBounded?, stBounded?, 2≤sizeCapAt are all in scope.
open import Verify-Budget-Sufficient.Wet
  using (INV?; ΨAt; sizeCapAt;
         valB?; pathB?; fnCapᵛ;
         2≤sizeCapAt)

-- capsOK? and capsAt are in Caps-Face (not re-exported by Wet).
open import Verify-Budget-Sufficient.Caps-Face
  using (capsOK?; capsAt)

open import Verify-Budget-Sufficient.Occurrences
  using (pathOccs?)

-- 1≤towerℕ is defined in Caps (and re-exported via the Wet chain,
-- but named explicitly for clarity).
open import Verify-Budget-Sufficient.Caps
  using (1≤towerℕ)

----------------------------------------------------------------------
-- § 0  SETUP — empty context, no-slot programs
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

ins₀ : Slots Γ₀
ins₀ ()

-- PROGRAM A: mergeAllᵉ of a singleton whose inner_A emits two nats.
-- u = natᵗ; subscribeInner will produce values of type Val Γ₀ natᵗ.
inner_A : Val Γ₀ (obs natᵗ)
inner_A = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ [])

e_A : Closed Γ₀ natᵗ
e_A = mergeAllᵉ (ofᵉ (strmᵗ inner_A ∷ []))

-- PROGRAM B: exhaustAllᵉ of a singleton whose inner_B emits one obs natᵗ value.
-- u = obs natᵗ; subscribeInner will produce values of type Val Γ₀ (obs natᵗ).
inner_B : Val Γ₀ (obs (obs natᵗ))
inner_B = ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])

e_B : Closed Γ₀ (obs natᵗ)
e_B = exhaustAllᵉ (ofᵉ (strmᵗ inner_B ∷ []))

-- Gas: gs g0 suffices.
-- subscribeInner (gs g0) calls subscribeE g0 inner; ofᵉ requires no fuel.
fuel : Gas
fuel = gs g0

----------------------------------------------------------------------
-- § 1  CONCRETE HALF — run subscribeInner at the initial state
--
-- The initial state (sched-init e ins₀, st-init e) is the REACHED
-- STATE at program start (0 evaluation steps).  Constructed from
-- sched-init/st-init, NOT from record ... { ... } hand-building.
--
-- subscribeInner mints inst = Sched.nextNode (sched-init e ins₀) = 0,
-- then calls subscribeE g0 inner (from-inner op 0 0 ↠ root) ...,
-- and returns (inst, vs, bs, done, sched', st').
-- The probe extracts vs = proj₁(proj₂(result)).
----------------------------------------------------------------------

-- PROGRAM A result
si_A : _
si_A = subscribeInner fuel mergeᵒ 0 root 0 0 inner_A
         (sched-init e_A ins₀) (st-init e_A)

vs_A : List (Val Γ₀ natᵗ)
vs_A = proj₁ (proj₂ si_A)

-- LOAD-BEARING: subscribeInner on ofᵉ[nat̂ 0, nat̂ 1] returns [0, 1].
-- vs_A : List ℕ (since Val Γ₀ natᵗ = ℕ).
-- Failure: broken subscribeE / splitBurst, or gas exhausted inner.
_ : vs_A ≡ 0 ∷ 1 ∷ []
_ = refl

-- LOAD-BEARING: sizeᵛ natᵗ = 1 for all nat values; N_A = 1.
-- Explicit {Γ = Γ₀} needed because Val Γ₀ natᵗ = ℕ erases the Γ parameter.
-- Failure: sizeᵛ formula changed.
_ : map (sizeᵛ {Γ = Γ₀} natᵗ) vs_A ≡ 1 ∷ 1 ∷ []
_ = refl

-- PROGRAM B result
si_B : _
si_B = subscribeInner fuel exhaustᵒ 0 root 0 0 inner_B
         (sched-init e_B ins₀) (st-init e_B)

vs_B : List (Val Γ₀ (obs natᵗ))
vs_B = proj₁ (proj₂ si_B)

-- LOAD-BEARING: subscribeInner on ofᵉ[strmᵗ(ofᵉ[nat̂ 0])] returns
-- [ofᵉ[nat̂ 0]] — the evaluated strmᵗ term is ofᵉ[nat̂ 0].
-- Failure: wrong value type, wrong list length, or empty list.
_ : vs_B ≡ evalTm (strmᵗ (ofᵉ (nat̂ 0 ∷ []))) ∷ []
_ = refl

-- LOAD-BEARING: sizeᵛ(obs natᵗ)(ofᵉ[nat̂ 0]) = sizeᵉ(ofᵉ[nat̂ 0]) = 3.
-- Derivation: sizeᵉ(ofᵉ ts) = suc(sizeᵗˢ ts);
--   sizeᵗˢ[nat̂ 0] = sizeᵗ(nat̂ 0) + sizeᵗˢ[] = 1 + 1 = 2;
--   sizeᵉ(ofᵉ[nat̂ 0]) = suc 2 = 3.  N_B = 3.
-- Failure: sizeᵉ formula changed or evalTm strmᵗ recomputed size.
_ : map (sizeᵛ (obs natᵗ)) vs_B ≡ 3 ∷ []
_ = refl

----------------------------------------------------------------------
-- § 2  SECOND CONJUNCT COMPUTABILITY
--
-- valB? N Ψ u v = (sizeᵛ u v ≤ᵇ N) ∧ (fnCapᵛ u v ≤ᵇ Ψ).
-- The SECOND conjunct fnCapᵛ u v ≤ᵇ ΨAt e sl is DECIDABLE because:
--   fnCapᵛ: structural recursion on the value; computable.
--   ΨAt e sl = fnCapᵉ e + slotsFnCap sl: both computable.
-- For programs built from nat̂, strmᵗ, ofᵉ, mergeAllᵉ, exhaustAllᵉ
-- (no map/scan/take functions), fnCapᵉ = 0 hence ΨAt = 0.
----------------------------------------------------------------------

-- LOAD-BEARING: ΨAt e_A ins₀ = 0; ΨAt e_B ins₀ = 0.
-- Failure: fnCapᵉ / slotsFnCap miscounted for these expressions.
_ : ΨAt e_A ins₀ ≡ 0
_ = refl

_ : ΨAt e_B ins₀ ≡ 0
_ = refl

-- LOAD-BEARING: fnCapᵛ natᵗ v = 0 for all nat values.
-- Explicit {Γ = Γ₀} because Val Γ₀ natᵗ = ℕ erases Γ.
-- → second conjunct of valB? Dm Ψ natᵗ v is 0 ≤ᵇ 0 = true by refl.
_ : map (fnCapᵛ {Γ = Γ₀} natᵗ) vs_A ≡ 0 ∷ 0 ∷ []
_ = refl

-- LOAD-BEARING: fnCapᵛ (obs natᵗ) (ofᵉ[nat̂ 0]) = fnCapᵉ(ofᵉ[nat̂ 0]) = 0.
-- vs_B : List (Exp Γ₀ [] [] [] natᵗ), so Γ is inferable.
_ : map (fnCapᵛ (obs natᵗ)) vs_B ≡ 0 ∷ []
_ = refl

-- DECIDED: second conjunct holds for ALL returned values.
-- LOAD-BEARING: if ΨAt > 0 or fnCapᵛ > 0, these would fail.
_ : map (λ v → fnCapᵛ {Γ = Γ₀} natᵗ v ≤ᵇ ΨAt e_A ins₀) vs_A ≡ true ∷ true ∷ []
_ = refl

_ : map (λ v → fnCapᵛ (obs natᵗ) v ≤ᵇ ΨAt e_B ins₀) vs_B ≡ true ∷ []
_ = refl

-- STUCK: first conjunct sizeᵛ u v ≤ᵇ Dm involves sizeCapAt → abstract.
-- We check sizeᵛ concretely above (§ 1) and prove N ≤ Dm in § 4.

----------------------------------------------------------------------
-- § 3  HYPOTHESIS COVERAGE AT THE INITIAL STATE
--
-- At (sched-init e ins₀, st-init e) for a no-slot program (Γ₀):
--   live  = concat(tabulate(mkHot ins₀)) = concat [] = []
--   nodes = []
--   registry = []
-- All list-iterating parts of INV?/capsOK? are vacuously true.
-- The zero-case of ≤ᵇ absorbs the abstract bound B wherever 0 appears.
--
-- HYP 1 (INV?) conjuncts at initial state:
--   stBounded? B sched₀ st₀  = all(live)[] ∧ all(nodes)[] = true ✓
--   fnCapBounded? Ψ sched₀ st₀ = all(live)[] ∧ all(nodes)[] = true ✓
--   length [] ≤ᵇ B = 0 ≤ᵇ B = true  (zero ≤ᵇ _ = true by defn) ✓
--   regsB? B Ψ [] = true ✓
--   slotsSize ins₀ ≤ᵇ B = 0 ≤ᵇ B = true ✓
--   slotsFnCap ins₀ ≤ᵇ Ψ = 0 ≤ᵇ Ψ = true ✓
--   → INV? Ψ B sched₀ st₀ = true BY REFL (abstract B, Ψ never inspected).
--
-- HYP 2 (capsOK?) conjuncts at initial state:
--   stBounded? (cSize c) sched₀ st₀ = true ✓
--   regsSz? (cSize c) [] = true ✓
--   all(widLive (cWid c) ins₀) [] = true (live=[]) ✓
--   all(widNode ...) [] = true (nodes=[]) ✓
--   length [] ≤ᵇ cReg c = 0 ≤ᵇ cReg c = true ✓
--   → capsOK? (capsAt e ins₀ 0) sched₀ st₀ = true BY REFL.
--
-- HYP 4 (pathB? root): true by definition (root case).
-- HYP 5 (pathOccs? root): true by definition (root case).
--
-- HYP 3 (valB? B Ψ (obs u) inner): PARTIAL.
--   fnCapᵛ (obs u) inner ≤ᵇ Ψ = 0 ≤ᵇ 0 = true ✓  (§ 2 above)
--   sizeᵛ (obs u) inner ≤ᵇ B = sizeᵉ inner ≤ᵇ B: STUCK.
--   For inner_A: sizeᵉ inner_A = 4 ≤ B ≥ iterSize 10 9 10 >> 4 (symbolic)
--   For inner_B: sizeᵉ inner_B = 6 ≤ B similarly.
----------------------------------------------------------------------

-- HYPS 1 and 2 by refl (Program A).
-- LOAD-BEARING: would fail if initial state had non-empty lists,
-- which would expose the abstract B/capsAt to ≤ᵇ pattern matching.
_ : INV? (ΨAt e_A ins₀) (sizeCapAt e_A ins₀ 0)
          (sched-init e_A ins₀) (st-init e_A) ≡ true
_ = refl

_ : capsOK? (capsAt e_A ins₀ 0)
            (sched-init e_A ins₀) (st-init e_A) ≡ true
_ = refl

-- HYPS 1 and 2 by refl (Program B).
_ : INV? (ΨAt e_B ins₀) (sizeCapAt e_B ins₀ 0)
          (sched-init e_B ins₀) (st-init e_B) ≡ true
_ = refl

_ : capsOK? (capsAt e_B ins₀ 0)
            (sched-init e_B ins₀) (st-init e_B) ≡ true
_ = refl

-- HYP 4 (pathB? root): true for any B, Ψ.
-- Typed alias to anchor {Γ = Γ₀} {s = natᵗ} {t = natᵗ} for Agda.
-- LOAD-BEARING: would fail if root were not the trivial base case.
root_A : Path Γ₀ natᵗ natᵗ
root_A = root

_ : pathB? 0 0 root_A ≡ true
_ = refl

-- HYP 5 (pathOccs? root): true for any sz.
_ : pathOccs? 0 root_A ≡ true
_ = refl

-- HYP 3 stuck part: sizeᵛ (obs natᵗ) inner_A = 4.
-- Not checkable against abstract B by refl; symbolic route in § 4.
_ : sizeᵛ (obs natᵗ) inner_A ≡ 4
_ = refl

_ : sizeᵛ (obs (obs natᵗ)) inner_B ≡ 6
_ = refl

----------------------------------------------------------------------
-- § 4  SYMBOLIC BOUND — N ≤ Dm (the stuck first conjunct)
--
-- Measured: N_A = 1 (max sizeᵛ natᵗ, Program A).
--           N_B = 3 (max sizeᵛ (obs natᵗ), Program B).
-- Both ≤ 16. Route:
--
--   B  = sizeCapAt e sl id     ≥  2    [2≤sizeCapAt]
--   T  = towerℕ (suc sz)      ≥  1    [1≤towerℕ]
--   2*2+12 ≤ 2*B+12             [*-monoʳ-≤ 2 (2≤sizeCapAt), +-monoˡ-≤ 12]
--   i.e.  16 ≤ 2*B+12
--   Dm = (2*B+12)*T ≥ 16*1 = 16  [*-mono-≤]
--   N_A = 1 ≤ 16 ≤ Dm,  N_B = 3 ≤ 16 ≤ Dm.
--
-- COVERAGE: N ≤ 16 suffices for both programs.
-- NOT COVERED: programs where inner observables have sizeᵛ > 16
-- (e.g., the scan-merge programs from Battery-Reached-Sizes with
-- sizeᵉ acc_k up to 85).  For those, the tower scale (§ 4 of
-- Battery-Instant-Headroom) applies: Dm grows exponentially in sz,
-- and iterSize-le-capsAt gives sizeᵉ o ≤ Caps.cSize(capsAt) ≤ B.
----------------------------------------------------------------------

-- PROVED: Dm ≥ 16 for any program, slot, and instant id.
-- One-liner via *-mono-≤, +-monoˡ-≤, *-monoʳ-≤, 2≤sizeCapAt, 1≤towerℕ.
-- LOAD-BEARING: if any of the four imported lemmas were wrong, or if
-- the arithmetic chain were incorrect, this would fail to typecheck.
Dm-ge-16 : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : Id)
  → 16 ≤ (2 * sizeCapAt e sl id + 12) * towerℕ (suc (sizeᵉ e + slotsSize sl))
Dm-ge-16 e sl id =
  *-mono-≤ (+-monoˡ-≤ 12 (*-monoʳ-≤ 2 (2≤sizeCapAt e sl id)))
           (1≤towerℕ (suc (sizeᵉ e + slotsSize sl)))

-- COROLLARY for Program A: N_A = 1 ≤ Dm.
-- LOAD-BEARING: 1 ≤ 16 is a concrete arithmetic fact that typechecks.
N_A≤Dm : ∀ (e : Closed Γ₀ natᵗ) (id : Id)
  → 1 ≤ (2 * sizeCapAt e ins₀ id + 12) * towerℕ (suc (sizeᵉ e + slotsSize ins₀))
N_A≤Dm e id = ≤-trans (s≤s z≤n) (Dm-ge-16 e ins₀ id)

-- COROLLARY for Program B: N_B = 3 ≤ Dm.
-- LOAD-BEARING: 3 ≤ 16 is a concrete arithmetic fact.
N_B≤Dm : ∀ (e : Closed Γ₀ (obs natᵗ)) (id : Id)
  → 3 ≤ (2 * sizeCapAt e ins₀ id + 12) * towerℕ (suc (sizeᵉ e + slotsSize ins₀))
N_B≤Dm e id = ≤-trans (s≤s (s≤s (s≤s z≤n))) (Dm-ge-16 e ins₀ id)
