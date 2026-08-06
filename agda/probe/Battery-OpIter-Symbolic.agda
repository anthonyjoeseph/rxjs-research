------------------------------------------------------------------
-- SYMBOLIC REHEARSAL FOR opIterD≤sizeCount-root-core
-- (Verify-Budget-Sufficient/Caps-Bridge.agda:1090)
--
-- This file is the Phase-0 symbolic pass for the caps axis's
-- highest remaining single-postulate risk.  The postulate is stated
-- exactly (§ 1), reduced via sizeCount-body (§ 2), and the EXACT
-- arithmetic residual is isolated and named (§ 3).  § 4 documents
-- what the three sizeCount-body call sites teach.  § 5 states what
-- remains unknown and why.
--
-- BUILD COMMAND (from repo root):
--   cd agda && agda -i src -i probe probe/Battery-OpIter-Symbolic.agda
--
-- STATUS: GREEN — everything compiles.  opIterD≤sizeCount-root-core
-- is REDUCED to opIterD-dominated (§ 3), a pure arithmetic claim
-- about opIterD and sizeCount that (a) does not mention the evaluator,
-- (b) closes the main postulate if proven, and (c) is the exact new
-- mathematics the comment at Caps-Bridge.agda:1069 identifies.
--
-- VERDICT: REDUCED.  See the large comment at the bottom of § 3.
------------------------------------------------------------------
module Battery-OpIter-Symbolic where

open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; n≤1+n; m≤m+n; m≤n+m;
         +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-identityʳ)
open import Data.Bool    using (false)
open import Data.List    using (List; []; _∷_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import Rx.Prim      using (Source)
open import Rx.Exp
  using (Ty; Ctx; Exp; Closed; sizeᵉ; μᵉ; unfoldμ)
open import Rx.Slots     using (Slots; shared; slotsSize)
open import Rx.Evaluator
  using (sizeAt; widAt; opIterD; sLvlD; fIterD; fLvlD; lvls; dLvl;
         sLvlD-0; sLvlD-suc; opIterD-0; opIterD-suc;
         fIterD-0; fIterD-suc; fLvlD-0;
         memberSource)

-- Domain modules: bare open imports, no `using` clause.
-- None of these transitively imports Wet or Subscribe-Face.
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; capsAt; capsH; cDel; cDel-body;
         sizeCount; sizeCount-body; lvls-mono)

open import Verify-Budget-Sufficient.Caps-Nest
  using (nest; residAt; resid; nest≤; residAt-connected;
         share-step-resid; mu-1≤k; mu-step-le; k-raise)

open import Verify-Budget-Sufficient.Caps-Chain
  using (entry-to-index)

------------------------------------------------------------------
-- § 1.  THE FULL POSTULATE, STATED SYMBOLICALLY.
--
-- Copied verbatim from Caps-Bridge.agda:1090.  The goal of this
-- section is ONLY to confirm the type typechecks at symbolic e/ins.
-- Nothing is proved here — the body is a postulate.
--
-- Seven hypotheses are bundled because the proof is a structural
-- induction on `e` that needs each one at a specific operator:
--   entry-to-index  — fresh entry converts sLvlD → opIterD index
--   nest≤           — k ≤ sizeᵉ e + slotsSize ins (counting bound)
--   residAt-connected — share edge zeroes the connected slot's resid
--   share-step-resid  — share step spends the residue
--   mu-1≤k          — μ has a non-zero budget
--   mu-step-le      — μ unfold preserves the budget bound
--   k-raise         — the budget at suc J dominates the one at J
------------------------------------------------------------------

opIterD≤sizeCount-root-core-TYPECHECK :
  -- entry-to-index
  (∀ (S W d k J m : ℕ) → 2 ≤ S → suc (sizeAt S J) ≤ m →
    sLvlD S W d (suc k) J ≤ opIterD S W d k m J
   ) →
  -- nest≤
  (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
    (sl : Slots Γ) (cs : List Source) → nest e sl cs ≤ sizeᵉ e + slotsSize sl
   ) →
  -- residAt-connected
  (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
    residAt sl (toℕ i ∷ cs) i ≡ 0
   ) →
  -- share-step-resid
  (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
    (i : Fin n) {d : Closed Γ (lookup Γ i)} (k : ℕ) → sl i ≡ shared d →
    memberSource (toℕ i) cs ≡ false →
    resid sl cs ≤ k → nest d sl (toℕ i ∷ cs) ≤ k
   ) →
  -- mu-1≤k
  (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
    (sl : Slots Γ) (cs : List Source) (k : ℕ) → nest (μᵉ body) sl cs ≤ k → 1 ≤ k
   ) →
  -- mu-step-le
  (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
    (sl : Slots Γ) (cs : List Source) (k : ℕ) →
    nest (μᵉ body) sl cs ≤ k → nest (unfoldμ body) sl cs ≤ k
   ) →
  -- k-raise
  (∀ (S J : ℕ) → 1 ≤ S → suc (sizeAt S J) ≤ suc (sizeAt S (suc J))
   ) →
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
          (capsH e ins 0) (nest e ins []) (suc (sizeᵉ e)) 0
    ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)
opIterD≤sizeCount-root-core-TYPECHECK _ _ _ _ _ _ _ e ins =
  postulate-for-typecheck-only
  where postulate postulate-for-typecheck-only : _

-- GREEN check: applying the seven proven lemmas gives the non-core
-- postulate's exact body, just as Caps-Bridge.agda:1130 does.
opIterD≤sizeCount-root-ASSEMBLED :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
          (capsH e ins 0) (nest e ins []) (suc (sizeᵉ e)) 0
    ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)
opIterD≤sizeCount-root-ASSEMBLED e ins =
  opIterD≤sizeCount-root-core-TYPECHECK
    entry-to-index
    (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → nest≤ {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
    (λ {n} {Γ} → residAt-connected {n} {Γ})
    (λ {n} {Γ} → share-step-resid {n} {Γ})
    (λ {n} {Γ} {t} → mu-1≤k {n} {Γ} {t})
    (λ {n} {Γ} {t} → mu-step-le {n} {Γ} {t})
    k-raise
    e ins

------------------------------------------------------------------
-- § 2.  REDUCTION VIA sizeCount-body.
--
-- sizeCount c d = lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d)
-- (Caps.agda:370, exposed by sizeCount-body).
--
-- So the main goal reduces to:
--
--   opIterD S W d k m 0 ≤ lvls S W d 0 (cDel c d)
--
-- via `≤-trans (main-arith ...) (≤-reflexive (sym (sizeCount-body c d)))`.
--
-- All three call sites of sizeCount-body follow the same pattern.
--
-- CALL SITE 1 — 2≤sizeCount (Caps.agda:865)
--   Direction: lvls → sizeCount (packaging up)
--   Code: ≤-reflexive (sym (sizeCount-body c d))
--   Content: 2 ≤ dLvl S W d 0 then lvls-mono widens the count.
--
-- CALL SITE 2 — blowup-tower/J≤P (Caps.agda:1245)
--   Direction: sizeCount → lvls (opening up)
--   Code: ≤-reflexive (sizeCount-body c m)
--   Content: then applies lvls-mono to widen cDel c m to poolCount.
--
-- CALL SITE 3 — cascadeGo-caps (Caps-Face.agda:4761)
--   Direction: lvls → sizeCount (packaging up)
--   Code: ≤-reflexive (sym (sizeCount-body c d))
--   Content: lvls S W d 0 D ≤ lvls S W d 0 (cDel c d) via lvls-mono.
--
-- LESSON: the proof of opIterD≤sizeCount-root-core follows the
-- call-site-3 pattern: prove opIterD ... 0 ≤ lvls ... 0 (cDel c d),
-- then wrap with ≤-reflexive (sym (sizeCount-body c d)).
------------------------------------------------------------------

-- GREEN: the sizeCount-body packaging typechecks exactly as above.
sizeCount-body-demo :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let c = capsAt e ins 0
      d = capsH e ins 0
  in lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d)
       ≤ sizeCount c d
sizeCount-body-demo e ins =
  ≤-reflexive (sym (sizeCount-body (capsAt e ins 0) (capsH e ins 0)))

------------------------------------------------------------------
-- § 3.  THE ARITHMETIC RESIDUAL — the EXACT claim that closes
--       opIterD≤sizeCount-root-core once the structural induction
--       is set up.
--
-- COUNTING BOUNDS: in the main postulate,
--   k = nest e ins []   and   m = suc (sizeᵉ e).
-- S = 2 + sizeᵉ e + slotsSize ins  (baseCaps, Caps-Bridge.agda:959).
-- k ≤ sizeᵉ e + slotsSize ins by nest≤.
-- sizeᵉ e + slotsSize ins ≤ 2 + sizeᵉ e + slotsSize ins = S.  ✓
-- m = suc (sizeᵉ e) ≤ 2 + sizeᵉ e ≤ S.                        ✓
--
-- These two bounds are postulated below (m≤cSize, k≤cSize).
-- Their proofs use nest≤ + standard arithmetic on baseCaps.
-- They do NOT need the heavy import chain (Caps-Bridge).
--
-- THE ARITHMETIC RESIDUAL, stated as Agda:
------------------------------------------------------------------

postulate
  -- THE ARITHMETIC CORE.  Pure claim: no expressions, no evaluator
  -- dynamics.  Given k ≤ S and m ≤ S and 2 ≤ S, the operator walk
  -- from level 0 is dominated by sizeCount (caps S W R) d.
  --
  -- This is what Caps-Bridge.agda:1069 calls "the genuinely new
  -- mathematics".  R = Caps.cReg (capsAt e ins 0) at the call site,
  -- but the claim is parametric in R (R matters only inside cDel).
  opIterD-dominated : ∀ (S W d k m R : ℕ) → 2 ≤ S → k ≤ S → m ≤ S →
    opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)

  -- Counting bounds: k and m fit under S = cSize (capsAt e ins 0).
  -- Provable from nest≤ + baseCaps formula; postulated here since
  -- the probe's purpose is the assembly shape, not these lemmas.
  m≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    suc (sizeᵉ e) ≤ Caps.cSize (capsAt e ins 0)

  k≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    nest e ins [] ≤ Caps.cSize (capsAt e ins 0)

  2≤capsAt-cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    2 ≤ Caps.cSize (capsAt e ins 0)

-- GREEN: the assembly — using the three pieces above, derive the main goal.
-- This is the exact shape opIterD≤sizeCount-root-core's proof will take.
opIterD≤sizeCount-root-core-ASSEMBLED :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
          (capsH e ins 0) (nest e ins []) (suc (sizeᵉ e)) 0
    ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)
opIterD≤sizeCount-root-core-ASSEMBLED e ins =
  let c = capsAt e ins 0
      d = capsH e ins 0
      S = Caps.cSize c
      W = Caps.cWid c
      R = Caps.cReg c
  in ≤-trans
      (opIterD-dominated S W d
         (nest e ins []) (suc (sizeᵉ e)) R
         (2≤capsAt-cSize e ins) (k≤cSize e ins) (m≤cSize e ins))
      (≤-reflexive (sym (sizeCount-body c d)))

------------------------------------------------------------------
-- WHY THE NAIVE COUNT FAILS — and what opIterD-dominated requires.
--
-- The WRONG residual: "opIterD S W d k m 0 ≤ lvls S W d 0 m"
-- (same count on both sides) is FALSE.
-- Symbolic analysis (opIterD is abstract, so this is structural):
--
-- opIterD S W d k (suc m) 0
--   = fIterD S W d k (suc (widAt S W J₂)) J₂
--     where J₀ = suc (0 + suc(sizeAt S 0) * suc(sizeAt S 0))
--              = suc (suc S * suc S) ≥ suc(S²)
--           J₂ = opIterD S W d k m (sLvlD S W d k J₀)
--
-- The FINAL output is (fLvlD)^(suc(widAt S W J₂)) J₂ where
-- J₂ ≥ suc(S²).  At J₂ ≥ suc(S²), widAt S W J₂ grows as a TOWER
-- (foldStep S w = S^(suc w), iterated), so widAt >> sizeAt >> S.
-- But lvls S W d 0 1 = dLvl S W d 0 = (fLvlD)^(suc S) 0, applying
-- fLvlD only suc S times from level 0.  One opIterD step's tail
-- massively exceeds one dLvl step.
--
-- CORRECT: the proof needs D = cDel c d, which grows doubly-exponential
-- in S (gas = suc S, with cReg ≥ S entries per recursion pass).
-- The Caps-Bridge comment calls this "comfortable".
--
-- THE PROOF ROUTE for opIterD-dominated (not yet written):
-- Induction on m, with a RESIDUAL BUDGET invariant:
--   ∀ J D → opIterD S W d k m J ≤ lvls S W d J D
--   (tracking J and remaining budget D)
-- Key step (m = suc m′):
--   (a) ONE dLvl step from J reaches J₀ = suc(J + suc(sizeAt S J)²).
--       Requires: dLvl S W d J ≥ J₀.  Open (needs explicit fLvlD bound).
--   (b) After sLvlD, IH applies with smaller D′ and larger J.
--   (c) The fIterD tail ((fLvlD)^(suc(widAt S W J₂)) J₂) fits in the
--       remaining lvls budget.  Open (most uncertain step).
--
-- The MISSING PIECE is a lemma:
--   fIterD S W d k n J ≤ lvls S W d J (something-reasonable n)
-- showing that fIterD's n-step application is dominated by some
-- number of dLvl steps.  This lemma about fLvlD/dLvl vs fIterD is
-- the exact new mathematics needed.
------------------------------------------------------------------

-- OPTIONAL sanity check: lvls-mono applies as expected.
lvls-mono-demo :
  ∀ S W d n₁ n₂ → 2 ≤ S → n₁ ≤ n₂ →
  lvls S W d 0 n₁ ≤ lvls S W d 0 n₂
lvls-mono-demo S W d n₁ n₂ 2≤S hn =
  lvls-mono n₁ n₂ 2≤S ≤-refl ≤-refl ≤-refl hn

-- END OF FILE.  Probe is GREEN.
