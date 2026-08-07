------------------------------------------------------------------
-- INSTALL-SCAN DEPTH PROBE
--
-- Two goals:
-- §1: REFUTATION of old (FALSE) postulate `storeNestMax-installScan`.
--     Shows that storeNestMax after installing a caseᵗ-duplicated seed
--     value exceeds storeNestMax(entry) + sizeᵗ(seed), confirming the
--     old postulate was false as stated.
--     MECHANISM: caseᵗ binds `here` to `evalTm (inlᵗ bigObs)` and the
--     left arm `pairᵗ (varᵗ (here refl)) (varᵗ (here refl))` duplicates it, giving
--     sizeᵛ = suc(2·N) while sizeᵗ(seed) = N+11.  For N=12: 25 > 23.
--
-- §2: VALIDATION of new postulate `installScan-depth-bound`.
--     Shows depthE = 0 for b=emptyᵉ even with a LARGE scan value
--     (storeNestMax post-install = 5 > 2 = RHS bound), confirming
--     install-invariance: depthE never reads the scan accumulator on
--     the subscribe side (depthFrame(scan-f) = 0 definitionally).
--
-- LOAD-BEARING STATUS:
--   §1 ROW 3: LOAD-BEARING.
--     storeNestMax post-install = 25, old bound = 23.  25 ≤ᵇ 23 = false.
--     WHAT MAKES IT FAIL: using strmᵗ bigObs directly (no duplication)
--     gives sizeᵛ = sizeᵉ bigObs = 12 ≤ sizeᵗ(strmᵗ bigObs) = 13,
--     so ≤ᵇ = true — the old postulate holds for non-duplicating seeds.
--
--   §2 ROW 3: LOAD-BEARING.
--     storeNestMax post-install = 5 > 2 = sizeᵉ emptyᵉ + suc 0 + 0.
--     depthE = 0 despite the large stored value.
--     WHAT MAKES IT FAIL: if depthFrame(scan-f) were nonzero (like
--     depthFrame(thru-outer) = suc ...), depthE would be ≥ 5 > 2,
--     violating the bound — confirming the bound relies on scan-f's
--     definitional 0.
--
-- PROBED 2026-08-07: emptyᵉ inner (b), simple sched (Γ=[], scripted
-- slots), initial state, gas = g0.  NOT COVERED: shared-slot inner b,
-- post-cascade state, b with recursive depthE > 0.
------------------------------------------------------------------
module Install-Scan-Depth-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _≤ᵇ_)
open import Data.Bool using (Bool; false; true)
open import Data.List using (List; []; _∷_)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0)
open import Rx.Exp
  using (Ty; natᵗ; obs; _×ᵗ_; _+ᵗ_; Ctx; Closed; Exp; Tm; Fn;
         evalTm; emptyᵉ; scanᵉ; strmᵗ; inlᵗ; caseᵗ; pairᵗ; varᵗ;
         mergeAllᵉ; sizeᵉ; sizeᵗ; sizeᵛ)
open import Rx.Evaluator
  using (Sched; EvalSt; NodeState; NodeId;
         scan-st; mintNode; installNode;
         sched-init; st-init; root; scan-f)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Depth-Compositional using (storeNestMax)

------------------------------------------------------------------
-- SHARED SETUP
-- Γ₀ = []ᵛ (empty context), sched₀/sched₁/nid₀ shared across §1 and §2.
-- The phantom `e` in EvalSt differs per section.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

sched₀ : Sched Γ₀
sched₀ = sched-init (emptyᵉ {t = natᵗ}) (λ ())

nid₀ : NodeId
nid₀ = proj₁ (mintNode sched₀)

sched₁ : Sched Γ₀
sched₁ = proj₂ (mintNode sched₀)

------------------------------------------------------------------
-- § 1  REFUTATION OF OLD FORM (`storeNestMax-installScan`)
--
-- bigObs: 11 levels of mergeAllᵉ wrapping, sizeᵉ = 12
-- bigSeed: caseᵗ that duplicates bigObs in a pair
--   evalTm bigSeed = (bigObs, bigObs)
--   sizeᵛ(evalTm bigSeed) = suc(12 + 12) = 25
--   sizeᵗ bigSeed          = 23
-- OLD claim: 25 ≤ 0 + 23 — refuted by ROW 3.
------------------------------------------------------------------

private
  e₁ : Closed Γ₀ natᵗ
  e₁ = emptyᵉ

  -- 11 mergeAllᵉ wrappers, each requiring the inner to be obs(_).
  -- emptyᵉ is polymorphic in t, so Agda infers the type chain.
  bigObs : Exp Γ₀ [] [] [] (obs natᵗ)
  bigObs = mergeAllᵉ (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ
             (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ
             (mergeAllᵉ emptyᵉ))))))))))
  -- sizeᵉ bigObs = 12 (11 wrappers + 1 for emptyᵉ)

  bigSeed : Tm Γ₀ [] [] [] (obs (obs natᵗ) ×ᵗ obs (obs natᵗ))
  bigSeed = caseᵗ (inlᵗ {t = obs (obs natᵗ)} (strmᵗ bigObs))
                  (pairᵗ (varᵗ (here refl)) (varᵗ (here refl)))
                  (pairᵗ (strmᵗ emptyᵉ) (strmᵗ emptyᵉ))
  -- evalTm bigSeed = (bigObs, bigObs)
  -- sizeᵛ = suc(sizeᵉ bigObs + sizeᵉ bigObs) = suc(12+12) = 25

  st₁-old : EvalSt e₁
  st₁-old = installNode nid₀ (scan-st (evalTm bigSeed)) (st-init e₁)

-- ROW 1: storeNestMax after install = 25
-- (slotsNestMax = 0, nodesNestMax = sizeᵛ(evalTm bigSeed) = 25)
_ : storeNestMax sched₁ st₁-old ≡ 25
_ = refl

-- ROW 2: old bound = storeNestMax(entry) + sizeᵗ(seed) = 0 + 23 = 23
_ : storeNestMax sched₀ (st-init e₁) + sizeᵗ bigSeed ≡ 23
_ = refl

-- ROW 3: LOAD-BEARING refutation: 25 ≤ᵇ 23 = false
-- WHAT MAKES IT FAIL: non-duplicating seeds (e.g. strmᵗ bigObs, no caseᵗ)
-- give sizeᵛ = 12 ≤ 13 = sizeᵗ(strmᵗ bigObs), so ≤ᵇ = true.
_ : (storeNestMax sched₁ st₁-old ≤ᵇ
       (storeNestMax sched₀ (st-init e₁) + sizeᵗ bigSeed)) ≡ false
_ = refl

------------------------------------------------------------------
-- § 2  VALIDATION OF NEW FORM (`installScan-depth-bound`)
--
-- The new postulate claims:
--   depthE g b (scan-f f nid ↠ κ) bid now sched₁ (installNode nid (scan-st v) st)
--     ≤ sizeᵉ b + suc(pathLen κ) + storeNestMax sched st
--
-- Checked at b = emptyᵉ, κ = root, v = bigVal (sizeᵉ = 5).
-- storeNestMax post-install = 5 > 2 = RHS — LOAD-BEARING.
-- depthE = 0 despite the large scan value.
--
-- The key: depthFrame(scan-f) = 0 definitionally (Caps-Depth:362),
-- so no burst depth comes from the scan frame.  The recursive IH on
-- emptyᵉ returns 0 (BUCKET a).  Nothing reads the stored accumulator.
------------------------------------------------------------------

private
  -- Phantom program type matching the depthE call's root type.
  e-prog : Closed Γ₀ (obs (obs natᵗ))
  e-prog = emptyᵉ

  -- bigVal: 4 mergeAllᵉ wrappers, type = obs natᵗ, sizeᵉ = 5.
  -- As a VALUE: bigVal : Val Γ₀ (obs (obs natᵗ)) = Exp Γ₀ [] [] [] (obs natᵗ).
  -- sizeᵛ(obs (obs natᵗ)) bigVal = sizeᵉ bigVal = 5.
  bigVal : Exp Γ₀ [] [] [] (obs natᵗ)
  bigVal = mergeAllᵉ (mergeAllᵉ (mergeAllᵉ (mergeAllᵉ emptyᵉ)))

  largeSeed : Tm Γ₀ [] [] [] (obs (obs natᵗ))
  largeSeed = strmᵗ bigVal
  -- evalTm largeSeed = bigVal, sizeᵉ bigVal = 5

  -- trivial scan function: always returns emptyᵉ regardless of input
  f₀ : Fn Γ₀ [] [] [] (obs (obs natᵗ) ×ᵗ obs natᵗ) (obs (obs natᵗ))
  f₀ = strmᵗ emptyᵉ

  st₂-new : EvalSt e-prog
  st₂-new = installNode nid₀ (scan-st (evalTm largeSeed)) (st-init e-prog)

-- ROW 1: storeNestMax post-install = 5
-- (nodesNestMax = sizeᵛ(obs(obs natᵗ)) bigVal = sizeᵉ bigVal = 5)
_ : storeNestMax sched₁ st₂-new ≡ 5
_ = refl

-- ROW 2: RHS of new bound at b=emptyᵉ, κ=root, storeNestMax entry = 0
-- sizeᵉ b + suc(pathLen root) + storeNestMax sched₀ (st-init e-prog)
-- = sizeᵉ e-prog + 1 + 0 = 1 + 1 + 0 = 2
-- storeNestMax post-install (5) > RHS (2): LOAD-BEARING.
_ : sizeᵉ e-prog + suc 0 + storeNestMax sched₀ (st-init e-prog) ≡ 2
_ = refl

-- ROW 3: LOAD-BEARING validation: depthE = 0 despite large scan value.
-- depthE (scanᵉ f₀ largeSeed emptyᵉ) root ... reduces:
--   = depthE g0 emptyᵉ (scan-f f₀ 0 ↠ root) ... sched₁ st₂-new  ← 0 (BUCKET a)
--   ⊔ depthBurst g0 ... (scan-f f₀ 0) root [em] ...              ← 0 (depthFrame(scan-f)=0)
--   = 0
-- WHAT MAKES IT FAIL: if depthFrame(scan-f fn nid) returned suc (...) instead of 0.
_ : depthE g0 (scanᵉ f₀ largeSeed emptyᵉ) root 0 0
      sched₀ (st-init e-prog) ≡ 0
_ = refl
