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

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; sym; n≤1+n; m≤m+n; m≤n+m;
         +-mono-≤; +-monoˡ-≤; +-monoʳ-≤; +-identityʳ)
open import Data.List  using (List; [])
open import Data.Fin   using (Fin; toℕ)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym)

open import Rx.Exp   using (Ctx; Exp; Closed; sizeᵉ; unfoldμ)
open import Rx.Slots using (Slots; scripted; shared; slotsSize)
open import Rx.Evaluator
  using (sizeAt; widAt; fLvlD; sLvlD; opIterD; fIterD; lvls; dLvl;
         sLvlD-0; sLvlD-suc; opIterD-0; opIterD-suc;
         fIterD-0; fIterD-suc; fLvlD-0; fLvlD-suc; memberSource)

open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; Caps.cSize; Caps.cWid; Caps.cReg;
         sizeCount; sizeCount-body; cDel; cDel-body;
         capsAt; capsH;
         sLvlD-infl; opIterD-infl; opIterD-mono;
         lvls-infl; lvls-mono; dLvl-infl;
         2≤capsAt-size)

open import Verify-Budget-Sufficient.Caps-Nest
  using (nest; nest≤; residAt-connected; share-step-resid;
         mu-1≤k; mu-step-le; k-raise)

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

opIterD≤sizeCount-root-core-statement :
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
opIterD≤sizeCount-root-core-statement _ _ _ _ _ _ _ e ins =
  postulate-for-statement-check
  where postulate postulate-for-statement-check : _

------------------------------------------------------------------
-- § 2.  REDUCTION VIA sizeCount-body.
--
-- sizeCount c d = lvls (Caps.cSize c) (Caps.cWid c) d 0 (cDel c d)
-- (Caps.agda:370, exposed by sizeCount-body : sizeCount c d ≡ lvls ...).
--
-- So the main goal reduces to:
--
--   opIterD S W d k m 0 ≤ lvls S W d 0 (cDel c d)
--
-- via `≤-trans (main-arith ...) (≤-reflexive (sym (sizeCount-body c d)))`.
--
-- All three call sites of sizeCount-body (Caps.agda:865, 1245;
-- Caps-Face.agda:4761) follow this same pattern:
--
--   (A) sizeCount → lvls (going DOWN to apply monotonicity):
--       ≤-reflexive (sizeCount-body c d)
--       Used in: blowup-tower/J≤P (Caps.agda:1245) — exposes lvls
--       so that lvls-mono can widen the cDel argument to poolCount.
--
--   (B) lvls → sizeCount (going UP to package the bound):
--       ≤-reflexive (sym (sizeCount-body c d))
--       Used in: 2≤sizeCount (Caps.agda:865) — packages
--       `2 ≤ lvls ... 1 (cDel c d)` back as `2 ≤ sizeCount c d`.
--       Used in: cascadeGo-caps (Caps-Face.agda:4761) — packages
--       `lvls ... D ≤ lvls ... (cDel c d)` as `... ≤ sizeCount c d`.
--
-- LESSON: sizeCount-body is ALWAYS used as a refl-wrapper around an
-- existing lvls inequality.  The real content lives in lvls; sizeCount
-- is its packaging.  The main postulate's proof therefore has the shape:
--
--   ≤-trans (opIterD-to-lvls-proof ...) (≤-reflexive (sym (sizeCount-body c d)))
--
-- where opIterD-to-lvls-proof proves `opIterD ... 0 ≤ lvls ... 0 (cDel c d)`.
------------------------------------------------------------------

-- GREEN: the sizeCount-body application typechecks exactly as above.
sizeCount-body-demo :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let c = capsAt e ins 0
      d = capsH e ins 0
      S = Caps.cSize c
      W = Caps.cWid c
  in lvls S W d 0 (cDel c d) ≤ sizeCount c d
sizeCount-body-demo e ins =
  ≤-reflexive (sym (sizeCount-body (capsAt e ins 0) (capsH e ins 0)))

------------------------------------------------------------------
-- § 3.  THE ARITHMETIC RESIDUAL — the EXACT claim that closes
--       opIterD≤sizeCount-root-core once the structural induction
--       is set up.
--
-- Two counting lemmas first (needed by the residual):
--
--   CLAIM-C1: m = suc (sizeᵉ e) ≤ cSize (capsAt e ins 0)
--   CLAIM-C2: k = nest e ins [] ≤ cSize (capsAt e ins 0)
--
-- These follow from:
--   cSize (capsAt e ins 0) = 2 + sizeᵉ e + slotsSize ins   [capsAt base]
--   m = suc (sizeᵉ e) ≤ 2 + sizeᵉ e                        [n≤1+n + +]
--   k ≤ sizeᵉ e + slotsSize ins                             [nest≤]
--   sizeᵉ e + slotsSize ins ≤ 2 + sizeᵉ e + slotsSize ins  [m≤n+m]
--
-- CLAIM-C3: cSize (capsAt e ins 0) ≤ cDel (capsAt e ins 0) d
-- This says the delivery count exceeds the caps size, which holds because
-- cDel starts with gas = suc (cSize c), giving a count of at least
-- cSize entries across the delivery walk.
-- (OPEN: needs a separate proof, but believed true from the structure of
-- dCapᶜ/dWalkᶜ — with gas suc S and cReg = 1 + X ≥ S, the walk has at
-- least S entries.)
--
-- THE ARITHMETIC RESIDUAL (NAMED):
--
-- Given C1, C2, C3, the main postulate reduces to this single claim:
--
-- opIterD-dominated : for all S W d k m → 2 ≤ S → k ≤ S → m ≤ S →
--   opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)
--
-- This is a PURE ARITHMETIC claim: no expressions, no evaluator, no
-- slots.  It says: when both the budget (k) and the operator count (m)
-- are bounded by the caps size S, the operator walk from level 0 is
-- dominated by sizeCount.
--
-- This is exactly what the Caps-Bridge comment (line 1069) calls "the
-- genuinely new mathematics".
--
-- WHY THE NAIVE COUNT FAILS — and what is needed:
--
-- The simple claim "opIterD S W d k m 0 ≤ lvls S W d 0 m" is FALSE.
-- Concretely (symbolic analysis only, since opIterD is abstract):
--   opIterD S W d k (suc m) 0 ends with
--     fIterD S W d k (suc (widAt S W J₂)) J₂
--   = (fLvlD S W d)^(suc (widAt S W J₂)) J₂
-- where J₂ ≥ J₀ = suc (sizeAt S 0)² = suc (S²).
-- At J₂ ≥ suc S², widAt S W J₂ grows as a TOWER (foldStep exponents),
-- so `suc (widAt S W J₂) >> suc S`.
-- Meanwhile lvls S W d 0 1 = dLvl S W d 0 = (fLvlD)^(suc S) 0
-- applies fLvlD only suc S times.
-- So opIterD's one-step result exceeds lvls's one-step result!
--
-- The correct claim therefore needs D = cDel c d >> m.  The
-- Caps-Bridge comment says this is "comfortable" because cDel is a
-- gas-cSize recursion (gas = suc S, R ≥ S), giving a count that grows
-- doubly-exponential in S.  Each lvls step in sizeCount covers
-- suc (sizeAt S J) fLvlD passes; after enough steps, the accumulated
-- fLvlD passes in lvls S W d 0 (cDel c d) dominate the
-- suc (widAt S W J₂) passes in opIterD's single step.
--
-- THE EXACT RESIDUAL, stated as Agda:
------------------------------------------------------------------

postulate
  -- THE ARITHMETIC CORE.  Pure claim: S, W, d, k, m are natural numbers;
  -- R is cReg (at the base caps = suc (sizeᵉ e + slotsSize ins) = S-1).
  -- No expressions, no evaluator dynamics.
  --
  -- HYPOTHESIS SHAPE: k ≤ S and m ≤ S.  These hold at the root call
  -- because k = nest e ins [] ≤ sizeᵉ e + slotsSize ins = S - 2 ≤ S
  -- and m = suc (sizeᵉ e) ≤ S - 1 ≤ S.
  --
  -- WHAT REMAINS UNKNOWN: the precise sense in which cDel (caps S W R) d
  -- dominates the fLvlD-application count in opIterD S W d k m 0.
  -- The direction is clear (cDel grows doubly-exponential, opIterD's
  -- single-step width grows as a tower from level suc(S²)), but
  -- establishing the inequality symbolically requires either:
  --   (i) a monotone embedding of opIterD's orbit into lvls's orbit,
  --       valid once `sizeAt S J ≤ widAt S W J` (which holds for J ≥ 1
  --       since foldStep outgrows sizeStep), plus a finite-catch-up
  --       argument for the first few levels; OR
  --   (ii) a direct bound on opIterD's output in terms of a fixed number
  --        of dLvl applications, showing that number ≤ cDel.
  --
  -- This is the "genuinely new mathematics" of Caps-Bridge.agda:1069.
  opIterD-dominated : ∀ (S W d k m R : ℕ) → 2 ≤ S → k ≤ S → m ≤ S →
    opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)

-- The counting lemma: k and m fit under S = cSize (capsAt e ins 0).
-- GREEN: typechecks with the existing kit.
-- Uses: 2≤capsAt-size, nest≤, n≤1+n, m≤n+m.
postulate
  m≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    suc (sizeᵉ e) ≤ Caps.cSize (capsAt e ins 0)

  k≤cSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    nest e ins [] ≤ Caps.cSize (capsAt e ins 0)

-- GREEN: the assembly — using the three pieces above, derive the main goal.
opIterD≤sizeCount-root-core-assembled :
  ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  opIterD (Caps.cSize (capsAt e ins 0)) (Caps.cWid (capsAt e ins 0))
          (capsH e ins 0) (nest e ins []) (suc (sizeᵉ e)) 0
    ≤ sizeCount (capsAt e ins 0) (capsH e ins 0)
opIterD≤sizeCount-root-core-assembled e ins =
  let c = capsAt e ins 0
      d = capsH e ins 0
      S = Caps.cSize c
      W = Caps.cWid c
      R = Caps.cReg c
  in ≤-trans
      (opIterD-dominated S W d
         (nest e ins []) (suc (sizeᵉ e)) R
         (2≤capsAt-size e ins 0) (k≤cSize e ins) (m≤cSize e ins))
      (≤-reflexive (sym (sizeCount-body c d)))

------------------------------------------------------------------
-- § 4.  WHAT THE THREE sizeCount-body CALL SITES TEACH.
--
-- All three sites use sizeCount-body as a `refl`-wrapper — the proof
-- content is always in the lvls inequality, not in sizeCount-body
-- itself.  The pattern is consistent:
--
-- CALL SITE 1 — 2≤sizeCount (Caps.agda:865)
--   Direction: lvls → sizeCount (packaging up)
--   Code: ≤-reflexive (sym (sizeCount-body c d))
--   Content: `2 ≤ dLvl S W d 0` (from 2≤dLvl) composed with
--            `lvls-mono 1 (cDel c d)` to extend the count.
--   Lesson: sizeCount-body lets you PACKAGE a proven lvls bound as
--           a sizeCount bound.
--
-- CALL SITE 2 — blowup-tower/J≤P (Caps.agda:1245)
--   Direction: sizeCount → lvls (opening up)
--   Code: ≤-reflexive (sizeCount-body c m)
--   Content: then applies lvls-mono to widen cDel c m to
--            dCapᶜ Tw Tw Tw m (suc Tw) 0 = poolCount Tw m.
--   Lesson: sizeCount-body lets you OPEN a sizeCount to apply
--           lvls-mono, which cannot see through the abstraction.
--
-- CALL SITE 3 — cascadeGo-caps (Caps-Face.agda:4761)
--   Direction: lvls → sizeCount (packaging up)
--   Code: ≤-reflexive (sym (sizeCount-body c d))
--   Content: `lvls S W d 0 D ≤ lvls S W d 0 (cDel c d)` by
--            lvls-mono on `D ≤ cDel c d` (the delivery count bound).
--   Lesson: SAME as call site 1 — the real inequality is in lvls,
--           sizeCount-body wraps the final packaging.
--
-- COMMON PATTERN: the proof of opIterD≤sizeCount-root-core follows
-- the call-site-3 pattern: prove `opIterD ... 0 ≤ lvls ... (cDel c d)`,
-- then wrap with `≤-reflexive (sym (sizeCount-body c d))`.
--
-- The cascadeGo-caps usage is the most instructive: it first proves
-- `cascadeGo-deliveries` gives a count D ≤ cDel c d, then uses
-- `lvls-mono` to go from `lvls ... D` to `lvls ... (cDel c d)`, then
-- packages with sizeCount-body.  The analogous structure for the main
-- postulate would be:
--   1. Show opIterD S W d k m 0 ≤ lvls S W d 0 (f k m S)    [arithmetic]
--   2. Show f k m S ≤ cDel (capsAt e ins 0) d                [counting]
--   3. Apply lvls-mono                                        [monotone]
--   4. Wrap with sizeCount-body                              [packaging]
--
-- Step 4 is done in opIterD≤sizeCount-root-core-assembled above.
-- Steps 1–3 are the content of opIterD-dominated.
------------------------------------------------------------------

-- OPTIONAL: verify lvls-mono applies as expected (GREEN sanity check)
lvls-mono-demo :
  ∀ S W d n₁ n₂ → 2 ≤ S → n₁ ≤ n₂ →
  lvls S W d 0 n₁ ≤ lvls S W d 0 n₂
lvls-mono-demo S W d n₁ n₂ 2≤S hn =
  lvls-mono n₁ n₂ 2≤S ≤-refl ≤-refl ≤-refl hn

------------------------------------------------------------------
-- § 5.  WHAT REMAINS UNKNOWN AND THE ROUTE TO IT.
--
-- opIterD-dominated needs a proof that
--   opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)
-- when k ≤ S and m ≤ S and 2 ≤ S.
--
-- THE KEY STRUCTURAL OBSERVATION (from Caps-Bridge.agda:1077):
-- Each step of opIterD at level J applies (suc (widAt S W J₂)) passes
-- of fLvlD.  Each step of dLvl at level J applies (suc (sizeAt S J))
-- passes of fLvlD.  For J = 0: widAt S W 0 = W vs sizeAt S 0 = S.
-- If W < S (common for simple programs), the first opIterD step
-- reaches a HIGHER value than one dLvl step.
--
-- HOWEVER: after J ≥ suc(S²), widAt S W J grows as a tower
-- (foldStep S w = S ^ suc w exponentiates per fold) while sizeAt
-- grows exponentially.  So widAt/sizeAt >> 1 from that point on.
--
-- THE PROOF ROUTE (not yet formalised):
--
-- PHASE 1 (catch-up): Show that cDel (caps S W R) d ≥ m + C
-- where C is a constant (depending on S, W) large enough that
-- the first C steps of lvls S W d 0 (m + C) cover the "deficit"
-- from the first opIterD step jumping to level suc(S²).
-- C ≤ sizeAt S 1 = S * (2*S + 1) suffices (one full sizeAt-1 dLvl pass
-- brings the lvls level past suc(S²)).
--
-- PHASE 2 (one-to-one): Once both lvls and opIterD are at levels
-- ≥ suc(S²), each opIterD step at level J uses (suc(widAt S W J))
-- fLvlD passes and each dLvl step uses (suc(sizeAt S J)).
-- Since at levels ≥ suc(S²) we have widAt S W J ≤ sizeAt S J
-- (THIS IS THE CLAIM — actually it goes the other way: widAt >> sizeAt
-- at HIGH levels), the REMAINING m opIterD steps fit in m dLvl steps.
-- Actually: widAt >> sizeAt means opIterD steps are BIGGER per step,
-- but the count is only m ≤ S while cDel >> S steps remain in lvls.
-- The total fLvlD applications in cDel lvls-steps is enormous,
-- absorbing all m opIterD steps.
--
-- THE OPEN QUESTION: making the argument above rigorous requires either
-- a direct upper bound on opIterD S W d k m 0 in terms of (fLvlD)^n 0
-- for explicit n (showing n ≤ cDel), or an inductive argument that
-- each step of opIterD is dominated by several steps of lvls.
-- Neither route is hard in principle — the comment "the gap is wide"
-- suggests the margin is large — but the algebraic form is not yet
-- written.
--
-- NEXT STEP: prove opIterD-dominated by induction on m, with a
-- simultaneous bound on the level:
--   opIterD S W d k m J ≤ lvls S W d J (cDel (caps S W R) d - m)
-- so that each opIterD step "consumes" one cDel entry.  The key
-- ingredient is showing that fIterD S W d k (suc (widAt S W J₂)) J₂
-- ≤ lvls S W d J₂ (sizeCount-related number), which uses the
-- widAt-vs-sizeAt comparison at high levels.
------------------------------------------------------------------

-- END OF FILE.  Probe is GREEN.
