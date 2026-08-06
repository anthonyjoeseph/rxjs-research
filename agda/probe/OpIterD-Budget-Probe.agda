------------------------------------------------------------------
-- OPITERD-BUDGET PROBE (2026-08-06)
--
-- Attack on tier-1 postulate #6 `opIterD-budget` in
-- Verify-Budget-Sufficient/Op-Dominance.agda (line 81).
--
-- RESULT: REFUTATION.  The postulate is FALSE as stated.
-- The missing hypothesis is `1 ≤ R`.
--
-- § 1  THE REFUTATION — symbolic, no computation, applies for
--      ALL S W d k m satisfying the stated side conditions.
--
-- At R = 0:
--   cDel (caps S W 0) d  =  0
--     (dCapᶜ receives regAt S 0 J = 0, so the walk is empty)
--   ⟹  lvls S W d 0 (cDel (caps S W 0) d)  =  lvls S W d 0 0  =  0
--
--   Meanwhile LHS = lvls S W d (climb S W d k m)
--                                (suc (widAt S W (climb S W d k m)))
--     has the form  dLvl S W d X,  and  2≤dLvl  gives  dLvl S W d X ≥ 2
--     unconditionally.
--
--   So LHS ≥ 2 > 0 = RHS.  The stated inequality is false.
--
-- PROBE ROW TABLE:
--   Row A: R=0, ALL S≥2/k≤S/suc m≤S.  LOAD-BEARING — this is the
--          exact case that the postulate universally quantifies over and
--          at which it fails; removing the row removes the finding.
--          STATUS: RED (refuted).
--
-- § 2  WHAT THIS MEANS
--
-- The postulate needs at least `1 ≤ R` added.  The full call chain:
--
--   opIterD-budget S W d k m R  (← add `1 ≤ R`)
--   opIterD-dominated S W d k m R  (← propagate `1 ≤ R`)
--   opIterD≤sizeCount-root-core in Caps-Bridge.agda
--     (← provide `1 ≤ Caps.cReg c` via `capsAt-reg` from Tick-Headroom,
--        which gives `2 + sz ≤ Caps.cReg (capsAt e ins id)`)
--
-- Note: editing Caps-Bridge.agda requires a separate coordinated step
-- (another worker has concurrent edits there).
--
-- § 3  STATUS AFTER THE FIX
--
-- With `1 ≤ R` added, the statement is believed true but the proof is
-- open.  The route ("residual-budget induction on m, mutual with
-- sLvlD's k-descent") is new mathematics.  Concrete computation is
-- infeasible — even for S=2/W=1/R=1/d=0 the values involve towers of
-- exponents — so further progress requires a symbolic inductive argument.
-- The m=0 base case needs a bound relating `sLvlD S W d k J₀` to the
-- first step of the `cDel` walk; the inductive step must track a
-- residual budget invariant through the `opIterD` recursion.
------------------------------------------------------------------
module OpIterD-Budget-Probe where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Evaluator
  using (lvls; dLvl; widAt)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; cDel; cDel-body; 2≤dLvl)
open import Verify-Budget-Sufficient.Op-Dominance
  using (climb)

----------------------------------------------------------------------
-- § 1a.  RHS vanishes at R=0.
--
-- LOAD-BEARING: would fail if R>0, since dCapᶜ with a non-zero
-- registry would visit at least one position, making cDel positive.
----------------------------------------------------------------------

-- dCapᶜ S W 0 d (suc S) 0 reduces to 0 by computation:
-- regAt S 0 0 = 0 * suc (0 * S) = 0, dWalkᶜ ... 0 = 0.
cDel-R0 : ∀ S W d → cDel (caps S W 0) d ≡ 0
cDel-R0 S W d = trans (cDel-body (caps S W 0) d) refl

-- Therefore lvls S W d 0 (cDel (caps S W 0) d) = lvls S W d 0 0 = 0.
rhs-R0 : ∀ S W d → lvls S W d 0 (cDel (caps S W 0) d) ≡ 0
rhs-R0 S W d = trans (cong (lvls S W d 0) (cDel-R0 S W d)) refl

----------------------------------------------------------------------
-- § 1b.  LHS is always ≥ 2.
--
-- LOAD-BEARING: would fail if the count argument were 0 rather than
-- suc (widAt ...).  The suc is structural — the postulate's count is
-- always positive — so no hypothesis on S/W/d/k/m is needed here.
----------------------------------------------------------------------

-- lvls S W d J (suc n) = dLvl S W d (lvls S W d J n), and 2≤dLvl
-- holds unconditionally.
lhs-ge2 : ∀ S W d k m →
  2 ≤ lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
lhs-ge2 S W d k m =
  2≤dLvl S W d (lvls S W d (climb S W d k m) (widAt S W (climb S W d k m)))

----------------------------------------------------------------------
-- § 1c.  THE REFUTATION.  Any instance of the original postulate
--        at R=0 yields 2 ≤ 0, which is absurd.
--
-- LOAD-BEARING: the claim that `2 ≤ 0` is absurd is the very
-- inequality that makes 0 the wrong bound.
----------------------------------------------------------------------

2≤0→⊥ : 2 ≤ 0 → ⊥
2≤0→⊥ ()

-- If the postulate held at R=0 it would give LHS ≤ 0, but LHS ≥ 2.
opIterD-budget-R0-false : ∀ S W d k m → 2 ≤ S → k ≤ S → suc m ≤ S →
  ¬ (lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
      ≤ lvls S W d 0 (cDel (caps S W 0) d))
opIterD-budget-R0-false S W d k m _ _ _ claim =
  2≤0→⊥
    (≤-trans (lhs-ge2 S W d k m)
             (subst (lvls S W d (climb S W d k m)
                         (suc (widAt S W (climb S W d k m))) ≤_)
                    (rhs-R0 S W d)
                    claim))
