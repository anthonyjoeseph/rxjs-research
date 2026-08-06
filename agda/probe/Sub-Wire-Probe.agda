-- SUB-WIRE PROBE (2026-08-05).  Rehearsal for wiring sub-charge
-- (Caps-Bridge.agda:439) into subscribeE-wet-via-caps (ibid:941).
-- sub-charge is proven but orphaned; this probe converts the postulate
-- into a real definition calling sub-charge, plus rehearses that the
-- updated consumer (burst-caps) can supply the two new hypotheses.
--
-- ──────────────────────────────────────────────────────────────────
-- STEP 1 HYPOTHESIS TABLE
-- (c := capsAt e sl id, j := 0, bud := nest b sl cs, ops := suc (sizeᵉ b))
--
-- # │ sub-charge hypothesis                        │ status
-- ──┼──────────────────────────────────────────────┼────────────────────
--  1│ 2 ≤ Caps.cSize c                             │ DIRECT: 2≤capsAt-size e sl id
--  2│ 1 ≤ Caps.cReg c                              │ DIRECT: 1≤capsAt-reg e sl id
--  3│ Sched.slots sched ≡ sl                        │ DIRECT: refl
--  4│ slotsCaps? (cSize c) (cWid c) sl              │ DIRECT: slotsCaps?-capsAt e sl id
--  5│ slotsSize sl ≤ Caps.cSize c                   │ DERIVABLE: INV-parts (5th component)
--   │                                               │ then ≤ᵇ⇒≤ ∘ T-to
--  6│ capsOK? (frameStep 0 c) sched st              │ DIRECT: H6 + subst (frameStep-0 c)
--  7│ sizeᵉ b ≤ Caps.cSize (frameStep 0 c)          │ DIRECT: H3 + subst (frameStep-0 c)
--  8│ dWᵉ n sl b ≤ Caps.cWid (frameStep 0 c)        │ DIRECT: H7 + subst (frameStep-0 c)
--  9│ pathSz? (Caps.cSize (frameStep 0 c)) κ        │ THREADED: new hyp pathSzκ of
--   │                                               │ subscribeE-wet-via-caps, subst f0
-- 10│ suc (pathLen κ) ≤ Caps.cSize (frameStep 0 c) │ THREADED: new hyp lenκ, subst f0
-- 11│ nest b sl cs ≤ bud                            │ DIRECT: ≤-refl
-- 12│ suc (sizeᵉ b) ≤ ops                           │ DIRECT: ≤-refl
--
-- CONCLUSION GAPS:
-- G1 hasDry ≡ false   — subscribeE-wet (proj₁), no new postulate needed
-- G2 INV? output      — subscribeE-wet (proj₂), no new postulate needed
-- G3 capsOK?@(suc id) — NEW POSTULATE P4 (sub-charge-capsOK-lift)
--
-- POSTULATE COUNT: ONE (P4).
-- P1/P2 were FALSE (coordinator ruling: pathLen κ is the continuation
--   from b up to the root; it is bounded by the AMBIENT expression, not
--   by b itself.  A long chain of map-f frames with tiny step functions
--   satisfies all hypotheses while violating suc (pathLen κ) ≤ sizeCapAt
--   e sl id).  Fix: add pathSz? and suc pathLen as HYPOTHESES.
-- P3/P5 are REDUNDANT: subscribeE-wet (Wet.agda:4302, a postulate) already
--   gives both hasDry and INV? from the same hypotheses — just call it.
-- P4 is TRUE: j′ ≤ opIterD ≤ sizeCount c h (general opIterD≤sizeCount,
--   generalising Caps-Bridge:908's root case) → frameStep-mono-j →
--   capsAt-suc-full (Caps.agda:893-895, refl) → capsOK?-mono.  Proof
--   obligation: general depthE≤capsH + opIterD≤sizeCount lemmas.
-- ──────────────────────────────────────────────────────────────────

module Sub-Wire-Probe where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤-trans; ≤-refl; n≤1+n; m≤m+n)
open import Data.List    using (List)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst)

open import Rx.Prim      using (Gas; Tick; Id)
open import Rx.Exp       using (Ty; Ctx; Closed; sizeᵉ; syncSizeᵉ)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Hop-Depth  using (hopDᵉ)
open import Rx.Evaluator using (Sched; EvalSt; Slots;
                                Path; root; _↠_; Frame;
                                hasDry; subscribeE; slotsSize; opIterD;
                                sched-init; st-init; budgetAt)

-- wet family + Caps public + Keeps-Ring public + Measures public
-- (brings: INV?, INV-parts, ΨAt, sizeCapAt, pathLen, pathB?,
--  T-to, subscribeE-slots, frameStep, frameStep-0, capsAt,
--  2≤capsAt-size, 1≤capsAt-reg, dBound, hopR, unconn, hasAtLeast,
--  subscribeE-wet, fnCapᵉ, …)
open import Verify-Budget-Sufficient.Wet

-- caps face public chain (brings: capsOK?, pathSz?, slotsCaps?,
--  slotsCaps?-capsAt, capsOK?-parts, capsOK?-mono, nest, …)
open import Verify-Budget-Sufficient.Subscribe-Face

-- depth mirror
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

-- the piece we are wiring in: sub-charge (proven, Caps-Bridge:439)
-- also import helpers used in burst-caps-rehearsal
-- (caps-fuel-root and init-INV come from Wet above; init-capsOK? is here)
open import Verify-Budget-Sufficient.Caps-Bridge
  using (sub-charge; sizeE≤cap; dWe≤cWid; init-capsOK?)

-- ================================================================
-- POSTULATE P4: the one genuine remaining gap
-- ================================================================

postulate
  -- P4: capsOK? at frameStep j′ c lifts to capsAt (suc id)
  -- TRUTH: route is j′ ≤ opIterD ≤ sizeCount c (capsH e sl id)  via the
  -- general opIterD≤sizeCount lemma (generalises Caps-Bridge:908's root
  -- case).  Then frameStep-mono-j gives frameStep j′ c ⊑ᶜ
  -- frameStep (sizeCount c h) c; capsAt-suc-full (Caps.agda:893, refl)
  -- identifies the latter with capsAt (suc id); capsOK?-mono closes it.
  -- Proof obligation: general depthE≤capsH and opIterD≤sizeCount.
  -- NON-VACUOUS: concludes capsOK? at (suc id), strictly stronger than
  -- the hypothesis which sits at j′; false if j′ exceeds sizeCount.
  sub-charge-capsOK-lift : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
    let sl = Sched.slots sched
        c  = capsAt e sl id
        r  = subscribeE g b κ id now sched st
    in capsOK? (frameStep j′ c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
       j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c)
                    (depthE g b κ id now sched st)
                    (nest b sl (EvalSt.connectedShares st))
                    (suc (sizeᵉ b)) 0 →
       capsOK? (capsAt e sl (suc id))
               (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

-- ================================================================
-- THE ASSEMBLY: subscribeE-wet-via-caps as a real definition.
-- TWO NEW HYPOTHESES added immediately after pathB? (per directive):
--   pathSz? B κ ≡ true         (replaces false P1)
--   suc (pathLen κ) ≤ B        (replaces false P2)
-- These are threaded straight to sub-charge hyps 9-10 via frameStep-0.
-- ================================================================

subscribeE-wet-via-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     pathSz? B κ ≡ true →               -- NEW (replaces false P1)
     suc (pathLen κ) ≤ B →              -- NEW (replaces false P2)
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
     capsOK? (capsAt e sl id) sched st ≡ true →
     dWᵉ n sl b ≤ Caps.cWid (capsAt e sl id) →
     let r   = subscribeE g b κ id now sched st
         sl′ = Sched.slots (proj₁ (proj₂ r))
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e sl′) (sizeCapAt e sl′ (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
        × (capsOK? (capsAt e sl′ (suc id))
                   (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet-via-caps {n = n} {e = e} g b κ id now sched st
                        inv pathB pathSzκ lenκ szB fnB gas cOK dW =
  dry , invOut , capsOut
  where
  sl      = Sched.slots sched
  Ψ       = ΨAt e sl
  B       = sizeCapAt e sl id
  c       = capsAt e sl id
  r       = subscribeE g b κ id now sched st
  sched′  = proj₁ (proj₂ r)
  st′     = proj₂ (proj₂ r)

  -- output slots = entry slots
  sl′Eq : Sched.slots sched′ ≡ sl
  sl′Eq = subscribeE-slots g b κ id now sched st

  -- slotsSize sl ≤ Caps.cSize c from INV? (5th INV-parts component)
  invP    = INV-parts Ψ B sched st inv
  ss-in   : (slotsSize sl ≤ᵇ B) ≡ true
  ss-in   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ invP))))
  slotsOK : slotsSize sl ≤ Caps.cSize c
  slotsOK = ≤ᵇ⇒≤ (slotsSize sl) B (T-to ss-in)

  -- G1 and G2 from subscribeE-wet — no new postulate needed
  wet     = subscribeE-wet g b κ id now sched st inv pathB szB fnB gas
  dry     : hasDry (proj₁ r) ≡ false
  dry     = proj₁ wet
  invOut  : INV? (ΨAt e (Sched.slots sched′))
                 (sizeCapAt e (Sched.slots sched′) (suc id))
                 sched′ st′ ≡ true
  invOut  = proj₂ wet

  -- frameStep-0 rewrite (f0 : frameStep 0 c ≡ c) for hyps 6–10
  f0 = frameStep-0 c

  -- thread pathSzκ and lenκ through frameStep-0 for sub-charge hyps 9–10
  pκSz  : pathSz? (Caps.cSize (frameStep 0 c)) κ ≡ true
  pκSz  = subst (λ x → pathSz? (Caps.cSize x) κ ≡ true) (sym f0) pathSzκ

  pκLen : suc (pathLen κ) ≤ Caps.cSize (frameStep 0 c)
  pκLen = subst (λ x → suc (pathLen κ) ≤ Caps.cSize x) (sym f0) lenκ

  -- CALL sub-charge: this is the consumer that wires the orphan
  IH = sub-charge c
                  (nest b sl (EvalSt.connectedShares st))
                  (suc (sizeᵉ b))
                  0
                  g b κ id now sl sched st
                  (2≤capsAt-size e sl id)                                  -- hyp 1
                  (1≤capsAt-reg e sl id)                                   -- hyp 2
                  refl                                                     -- hyp 3
                  (slotsCaps?-capsAt e sl id)                              -- hyp 4
                  slotsOK                                                  -- hyp 5
                  (subst (λ x → capsOK? x sched st ≡ true) (sym f0) cOK) -- hyp 6
                  (subst (λ x → sizeᵉ b ≤ Caps.cSize x) (sym f0) szB)    -- hyp 7
                  (subst (λ x → dWᵉ n sl b ≤ Caps.cWid x) (sym f0) dW)   -- hyp 8
                  pκSz                                                     -- hyp 9
                  pκLen                                                    -- hyp 10
                  ≤-refl                                                   -- hyp 11
                  ≤-refl                                                   -- hyp 12

  j′      = proj₁ IH
  capOut  = proj₁ (proj₂ IH)
  jBound  = proj₂ (proj₂ (proj₂ (proj₂ IH)))

  -- G3: capsOK? at capsAt (suc id) via P4, transported from sl to sl′
  capsOut₀ : capsOK? (capsAt e sl (suc id)) sched′ st′ ≡ true
  capsOut₀ = sub-charge-capsOK-lift g b κ id now sched st j′ capOut jBound

  capsOut : capsOK? (capsAt e (Sched.slots sched′) (suc id)) sched′ st′ ≡ true
  capsOut = subst (λ x → capsOK? (capsAt e x (suc id)) sched′ st′ ≡ true)
                  (sym sl′Eq) capsOut₀

-- ================================================================
-- CONSUMER REHEARSAL: burst-caps at κ = root.
-- Verifies that both new hypotheses of subscribeE-wet-via-caps
-- discharge at the root call site:
--   pathSz? B root ≡ true       by refl (Caps-Face.agda:290, clause eq)
--   suc (pathLen root) ≤ B      = 1 ≤ B, from s≤s z≤n : 1 ≤ 2
--                                 and 2≤capsAt-size e ins 0 : 2 ≤ B
-- The rest mirrors burst-caps (Caps-Bridge.agda:990-1014) exactly.
-- ================================================================

burst-caps-rehearsal : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in capsOK? (capsAt e ins 1) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-caps-rehearsal {n = n} e ins =
  let r      = subscribeE (budgetAt e ins 0) e root 0 0
                          (sched-init e ins) (st-init e)
      sched₁ = proj₁ (proj₂ r)
      st₁    = proj₂ (proj₂ r)
      sl′Eq  = subscribeE-slots (budgetAt e ins 0) e root 0 0
                                (sched-init e ins) (st-init e)
      result = subscribeE-wet-via-caps
                 (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
                 (init-INV e ins 0)
                 refl               -- pathB? B Ψ root ≡ true (Measures root clause)
                 refl               -- pathSz? B root  ≡ true  ← NEW, Caps-Face:290
                 (≤-trans (s≤s z≤n) (2≤capsAt-size e ins 0))
                                    -- suc (pathLen root) = 1 ≤ 2 ≤ B ← NEW
                 (sizeE≤cap e ins)  -- sizeᵉ e ≤ B
                 (m≤m+n (fnCapᵉ e) _)
                 (caps-fuel-root e ins)
                 (init-capsOK? e ins 0)
                 (dWe≤cWid e ins)
      capsOK-out = proj₂ (proj₂ result)
  in subst (λ s → capsOK? (capsAt e s 1) sched₁ st₁ ≡ true) sl′Eq capsOK-out
