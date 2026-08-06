------------------------------------------------------------------
-- BATTERY-HOP-PREMISE: is hop-edge's premise (iii) a second blocker?
--
-- hop-edge (Wet.agda:4052) has THREE premises:
--   (i)   2 ≤ Ŝ                                        — trivial
--   (ii)  sizeᵛ (obs u) o ≤ Ŝ                         — THE ANCHOR PROBLEM
--   (iii) hopDᵛ Ŝ (obs u) o < r                       — THIS FILE
--
-- THE QUESTION: is (iii) automatic, conditional, or false?
--
-- VERDICT: CONDITIONAL — but the condition is already BUILT INTO
-- the proof structure.  Specifically:
--
--   (A) At the *All frame, r = hopDᵉ Ŝ (mergeAllᵉ b) = suc (hopDᵉ Ŝ b).
--       This is definitional from hopDᵉ's mergeAllᵉ clause (Hop-Depth:191).
--
--   (B) `subscribeE-walk-core`'s conclusion (Measures.agda:5810) includes
--       the conjunct  `burstHopD? F (hopDᵉ F b) burst ≡ true`,
--       explicitly labelled "the hop edge's feed".  With F = Ŝ (as stated
--       at Measures.agda:3832), this says every emitted value v satisfies
--       hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b.
--
--   (C) Therefore:  hopDᵛ Ŝ u v ≤ hopDᵉ Ŝ b < suc (hopDᵉ Ŝ b) = r.
--       Premise (iii) follows in ONE step from (A) and (B) — no new lemma,
--       no new design question.  Wet.agda:4046 already recorded this:
--       "The r-drop is the emitted-value invariant (burstHopD?)".
--
-- CONSEQUENCE: (iii) is NOT a second design-level blocker beyond the
-- anchor problem.  It is a GRIND obligation inside the subscribeE-walk-core
-- proof (a DIFFICULTY item, not FALSITY).  The supporting mathematics —
-- hopD-applyFn, hopD-map-emit (Measures.agda:2765-2787) — is PROVEN.
--
-- THE ADVERSARIAL CASE: Battery-Obs-Growth's doubling scan has
-- sizeᵛ acc_k = 12·2^k − 11 (exponential in k) but hopDᵉ acc_k = k
-- (LINEAR in k).  The parent scan's hopD is suc(3^Ŝ) — EXPONENTIAL in Ŝ.
-- If (ii) holds (Ŝ ≥ sizeᵛ acc_k), then Ŝ is exponential in k, making
-- the parent's hopD doubly-exponential in k, which trivially exceeds k.
-- So (iii) fails on the adversarial case ONLY IF (ii) already fails — the
-- two premises have the SAME failure mode.
--
-- CONNECT-EDGE: no analog of (iii).  connect-edge (Wet.agda:4066) has
-- premises 2 ≤ Ŝ, a slot lookup, a freshness condition, and sizeᵉ d ≤ Ŝ.
-- The descent energy comes from U dropping STRICTLY (unconn-insert,
-- dBound-connect's U′ < U hypothesis), NOT from r.  The r and s axes
-- merely RESET (r ≤ R̂ via reach-reset, s ≤ Ŝ via reach-reset) — no
-- strict drop required on r.  There is nothing analogous to (iii) here.
--
-- PRIOR WORK ADDRESSING THIS: Hop-Descent-Probe.agda lines 202-230
-- already measured hopDᵉ V o < hopDᵉ V (mergeAllᵉ carrier) for three
-- shapes and proved emitted-fits/mul-fits as standing guards.  This file
-- adds the adversarial scan shape (Battery-Obs-Growth's acc_k) and the
-- direct burstHopD?-feed check.
--
-- ROW LABELLING (per standing rules):
-- Each row is labelled LOAD-BEARING (can fail if a definition changes) or
-- DEGENERATE (passes regardless of the interesting quantity).
-- "What would make this fail" is given for each load-bearing row.
------------------------------------------------------------------
module Battery-Hop-Premise where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤ᵇ_)
open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ty; Ctx; obs; natᵗ; _×ᵗ_;
                          Val; Exp; Fn; Tm;
                          varᵗ; fstᵗ; nat̂; strmᵗ;
                          ofᵉ; emptyᵉ; mergeAllᵉ; scanᵉ;
                          applyFn; evalTm)
open import Data.Vec using () renaming ([] to []ᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵛ)

------------------------------------------------------------------
-- § 0  SETUP
--
-- The adversarial doubling scan from Battery-Obs-Growth: same step
-- function, same accumulators.  Γ₀ has no slots so nothing external
-- can drive the fold count — the purely syntactic case.
------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ᵛ

-- step : (acc : obs natᵗ, v : natᵗ) → obs natᵗ = mergeAll (of [acc, acc])
step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ (ofᵉ (fstᵗ (varᵗ (here refl))
                             ∷ fstᵗ (varᵗ (here refl)) ∷ [])))

seed : Tm Γ₀ [] [] [] (obs natᵗ)
seed = strmᵗ emptyᵉ

src₃ : Exp Γ₀ [] [] [] natᵗ
src₃ = ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ [])

-- the accumulators, stepped forward by applyFn
acc₀ : Val Γ₀ (obs natᵗ)
acc₀ = evalTm seed

acc₁ : Val Γ₀ (obs natᵗ)
acc₁ = applyFn step (acc₀ , 0)

acc₂ : Val Γ₀ (obs natᵗ)
acc₂ = applyFn step (acc₁ , 1)

acc₃ : Val Γ₀ (obs natᵗ)
acc₃ = applyFn step (acc₂ , 2)

------------------------------------------------------------------
-- § 1  hopDᵉ OF ACCUMULATOR VALUES IS LINEAR IN k
--
-- hopDᵉ V acc_k = k for all V, because each step wraps in one
-- mergeAllᵉ (adding suc to hopD) over ofᵉ whose items have the
-- accumulator's depth (via fstᵗ/⊔).
--
-- This is V-INDEPENDENT: the scan refold (2+pm)^V factor appears
-- in the PARENT scan expression, not in the accumulated values.
--
-- Rows below are at V=4 (matching Hop-Descent-Probe's measurements).
------------------------------------------------------------------

-- DEGENERATE: hopDᵉ 4 acc₀ = 0 by definition of emptyᵉ; passes
-- regardless of the scan structure.
_ : hopDᵉ 4 acc₀ ≡ 0
_ = refl

-- LOAD-BEARING: hopDᵉ 4 acc₁ = 1.  Fails if mergeAllᵉ's clause
-- changes (suc → 0 would give 0) or if ofᵉ's ⊔ is replaced by +.
_ : hopDᵉ 4 acc₁ ≡ 1
_ = refl

-- LOAD-BEARING: hopDᵉ 4 acc₂ = 2.  Fails if the accumulator nesting
-- were flattened by a rewrite rule.
_ : hopDᵉ 4 acc₂ ≡ 2
_ = refl

-- LOAD-BEARING: hopDᵉ 4 acc₃ = 3.  This is the one that most stresses
-- (iii): Ŝ must accommodate sizeᵛ acc₃ = 85 per the anchor problem,
-- so this row confirms hopD stays linear while size grows exponentially.
_ : hopDᵉ 4 acc₃ ≡ 3
_ = refl

------------------------------------------------------------------
-- § 2  hopDᵉ OF THE PARENT SCAN IS EXPONENTIAL IN Ŝ
--
-- hopDᵉ V (scanᵉ step seed src₃) = (2 + pmᵗ V 0 step)^V * (...)
--                                  = (2+1)^4 * (1+0+0) = 81  at V=4.
--
-- At V = Ŝ ≥ 85 (the anchor problem's minimum for acc₃), the parent's
-- hopD is ≥ 3^85, which is doubly exponential in k=3.
-- The V=4 row is computable; V=85 is not (3^85 is too large to reduce).
--
-- The key gap: V=4 < 85, yet 3 < 81 already shows the mechanism.
-- The V=Ŝ=85 argument is symbolic: 3 < 3^85 + 1, which holds for all
-- k ≤ 3 and Ŝ ≥ 4 by monotonicity.
------------------------------------------------------------------

-- LOAD-BEARING: the scan coefficient is (2+1)^4 = 81.  Fails if pmᵗ
-- changes at step's variable index 0, or if the scan clause changes its
-- exponent base.
_ : hopDᵉ 4 (scanᵉ step seed src₃) ≡ 81
_ = refl

-- LOAD-BEARING: the mergeAllᵉ wrapper adds one (the *All definitional suc).
-- Fails if mergeAllᵉ's hopD clause were changed to the identity.
_ : hopDᵉ 4 (mergeAllᵉ (scanᵉ step seed src₃)) ≡ 82
_ = refl

------------------------------------------------------------------
-- § 3  PREMISE (iii) HOLDS AT V=4 FOR ALL k=0..3
--
-- burstHopD? V (hopDᵉ V b) burst ≡ true iff for each emitted value v,
--   hopDev? V (hopDᵉ V b) (value v) ≡ hopDᵛ V u v ≤ᵇ hopDᵉ V b ≡ true.
--
-- Here b = scanᵉ step seed src₃ and the emitted v = acc_k.
-- The strict form for hop-edge is: hopDᵉ V acc_k < r
-- where r = hopDᵉ V (mergeAllᵉ b) = suc (hopDᵉ V b) — the *All adds 1.
--
-- Both ≤ᵇ (the burstHopD? feed) and the strict < are shown.
-- The ≤ᵇ rows are what burstHopD? requires; the strict row is what
-- hop-edge actually needs (r = suc (hopDᵉ b), so ≤ implies <).
------------------------------------------------------------------

-- DEGENERATE: 0 ≤ᵇ anything is always true; this only shows acc₀
-- does not fail the check.
-- DEGENERATE: 0 ≤ᵇ anything is always true; this only shows acc₀
-- does not fail the check.
hop-feed-acc₀ : (0 ≤ᵇ hopDᵉ 4 (scanᵉ step seed src₃)) ≡ true  -- 0 ≤ᵇ 81
hop-feed-acc₀ = refl

-- LOAD-BEARING: 1 ≤ᵇ 81.  Fails if hopDᵉ acc₁ were ≥ 82.
hop-feed-acc₁ : (hopDᵉ 4 acc₁ ≤ᵇ hopDᵉ 4 (scanᵉ step seed src₃)) ≡ true  -- 1 ≤ᵇ 81
hop-feed-acc₁ = refl

-- LOAD-BEARING: 2 ≤ᵇ 81.
hop-feed-acc₂ : (hopDᵉ 4 acc₂ ≤ᵇ hopDᵉ 4 (scanᵉ step seed src₃)) ≡ true  -- 2 ≤ᵇ 81
hop-feed-acc₂ = refl

-- LOAD-BEARING: 3 ≤ᵇ 81.  The most adversarial row: the deepest
-- accumulator against its parent's hopD bound.  Would fail if the
-- scan's (2+pm)^V factor were ≤ 2 (i.e., V were 0 and k were 3).
hop-feed-acc₃ : (hopDᵉ 4 acc₃ ≤ᵇ hopDᵉ 4 (scanᵉ step seed src₃)) ≡ true  -- 3 ≤ᵇ 81
hop-feed-acc₃ = refl

-- THE STRICT ROW (the actual hop-edge premise (iii)):
-- hopDᵉ 4 acc₃ < hopDᵉ 4 (mergeAllᵉ (scanᵉ step seed src₃))
-- = 3 < 82  because r = suc (81) = 82 at the *All frame.
--
-- LOAD-BEARING: fails if hopDᵉ acc₃ ≥ hopDᵉ (mergeAllᵉ parent).
-- Equivalently: fails if the *All's definitional suc were absent.
hop-iii-strict : (suc (hopDᵉ 4 acc₃) ≤ᵇ hopDᵉ 4 (mergeAllᵉ (scanᵉ step seed src₃))) ≡ true
hop-iii-strict = refl  -- suc 3 = 4 ≤ᵇ 82

------------------------------------------------------------------
-- § 4  THE MECHANISM IN ONE PLACE
--
-- This section makes the discharge route explicit for (iii).
--
-- STEP A: r = hopDᵉ Ŝ (mergeAllᵉ b) = suc (hopDᵉ Ŝ b).
--   Definitional from Hop-Depth:191 (the mergeAllᵉ/concatAllᵉ/...
--   clause: hopDᵉ V (mergeAllᵉ e) = suc (hopDᵉ V e)).
--
-- STEP B: burstHopD? Ŝ (hopDᵉ Ŝ b) gives v ≤ hopDᵉ Ŝ b for each v.
--   This is a conjunct of subscribeE-walk-core (Measures.agda:5810).
--   Its proof reduces to hopD-map-emit (Measures.agda:2780) for mapᵉ
--   and hopD-subΘ for general substitution — both PROVEN.
--
-- STEP C: v ≤ hopDᵉ Ŝ b < suc (hopDᵉ Ŝ b) = r.  QED.
--
-- The discharge is a two-line argument at the *All clause, using
-- the walk hypothesis and the definitional equation.  No new lemma
-- is needed beyond what subscribeE-walk-core already provides.
--
-- Formally stated as a type that documents the argument:
-- (would be an actual proof if burstHopD? were available here,
--  but importing Measures would make this probe heavyweight; the
--  refl rows above provide the evidence instead)
------------------------------------------------------------------

-- The scan parent's hopD is strictly greater than each acc's hopD at V=4.
-- This witnesses that no acc_k in the adversarial scan can block (iii)
-- once the anchor (ii) is solved.
scan-parent-dominates-acc₃ : (hopDᵉ 4 acc₃ ≤ᵇ hopDᵉ 4 (mergeAllᵉ (scanᵉ step seed src₃))) ≡ true
scan-parent-dominates-acc₃ = refl  -- 3 ≤ᵇ 82

------------------------------------------------------------------
-- § 5  CONNECT-EDGE HAS NO ANALOG OF (iii)
--
-- connect-edge (Wet.agda:4066):
--   (i)   2 ≤ Ŝ
--   (ii)  sl i ≡ shared d   (slot lookup — always satisfiable)
--   (iii-analog?) memberSource (toℕ i) cs ≡ false  (freshness guard)
--   (iv)  sizeᵉ d ≤ Ŝ                              (size anchor — (ii) here)
--
-- The descent in dBound-connect is:
--   U′ < U  (unconn strictly drops)
--   r′ ≤ R̂  (r RESETS, not strictly descends)
--   s′ ≤ Ŝ  (s RESETS, not strictly descends)
--
-- There is NO condition of the form hopDᵉ Ŝ d < r on connect-edge.
-- The r and s axes just reset to ≤ R̂ and ≤ Ŝ respectively, sourced
-- from reach-reset's two components (Measures.agda:1812-1815):
--   reach-reset Ŝ h d (sizeᵉ d ≤ Ŝ) = (syncSizeᵉ d ≤ Ŝ, hopDᵉ Ŝ d ≤ hopR Ŝ)
--
-- The second component `hopDᵉ Ŝ d ≤ hopR Ŝ` satisfies `r′ ≤ R̂` (since R̂ = hopR Ŝ).
-- This is NOT a strictness condition — it is a reset bound.  U is what drops strictly.
--
-- BOTTOM LINE: for connect-edge, burstHopD? has NO role to play.
-- The only unresolved obligation on connect-edge is the anchor (sizeᵉ d ≤ Ŝ)
-- — the SAME anchor problem as for hop-edge's (ii), on a slot definition d.
--
-- The connect route for Ŝ (via capsAt / sizeCapAt at the slot's level)
-- is the SAME design question as the hop route.
--
-- Arithmetic witness: the reset values are ≤-bounded, not <-bounded.
-- No computation is needed to confirm the absence of a hop condition.
------------------------------------------------------------------
