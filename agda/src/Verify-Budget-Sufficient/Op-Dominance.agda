------------------------------------------------------------------
-- OP-DOMINANCE: the operator walk against the delivery count.
--
-- Consumer: `Verify-Budget-Sufficient.Op-Budget`, which turns the
-- results below into the proven `opIterD-budget` / `opIterD-dominated`.
--
-- WHAT IS PROVEN HERE, and it was the route's named open question
-- (Battery-OpIter-Symbolic § 3: "fIterD S W d k n J ≤ lvls S W d J
-- ‹bound in n› ... is the exact new mathematics needed"):
-- ‹bound in n› IS n.  `fIterD`'s recursion is literally `iterL`
-- (same step, the k argument unused), and n fLvlD-steps are dominated
-- by n dLvl-steps because one dLvl CONTAINS a leading fLvlD-step
-- (dLvl S W d J = iterL S W d (sizeAt S J) (fLvlD S W d J),
-- definitionally) and everything is monotone.  So the fIterD tail of
-- an opIterD step — route step (c), "most uncertain" — is closed.
--
-- NOTHING IS POSTULATED HERE.  Route steps (a)+(b) — the recursion's
-- CLIMB fits the budget — were the last gap, and they are proven in
-- Op-Budget as the residual-budget invariant (induction on m mutual
-- with sLvlD's k-descent), both endpoints in the SAME lvls-currency:
-- no fIterD, no fLvlD.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Op-Dominance where

open import Data.Nat using (ℕ; zero; suc; _*_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

open import Rx.Evaluator
  using (sizeAt; fLvlD; sLvlD; opIterD; fIterD; iterL; dLvl; lvls;
         fIterD-0; fIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (lvls-mono; lvls-add; iterL-infl)

-- One dLvl step contains a leading fLvlD step: definitionally,
-- dLvl S W d J = iterL S W d (suc (sizeAt S J)) J
--              = iterL S W d (sizeAt S J) (fLvlD S W d J),
-- and iterL is inflationary from there.
fLvlD-le-dLvl : ∀ S W d J → fLvlD S W d J ≤ dLvl S W d J
fLvlD-le-dLvl S W d J = iterL-infl S W d (sizeAt S J) (fLvlD S W d J)

-- n fLvlD-steps are dominated by n dLvl-steps.
iterL-le-lvls : ∀ S W d n J → 2 ≤ S → iterL S W d n J ≤ lvls S W d J n
iterL-le-lvls S W d zero    J 2≤S = ≤-refl
iterL-le-lvls S W d (suc n) J 2≤S =
  ≤-trans (iterL-le-lvls S W d n (fLvlD S W d J) 2≤S)
    (≤-trans (lvls-mono n n 2≤S ≤-refl ≤-refl (fLvlD-le-dLvl S W d J) ≤-refl)
             (≤-reflexive (sym (lvls-add S W d J 1 n))))

-- fIterD IS iterL: the k argument never steers the recursion.
fIterD-is-iterL : ∀ S W d k n J → fIterD S W d k n J ≡ iterL S W d n J
fIterD-is-iterL S W d k zero    J = fIterD-0 S W d k J
fIterD-is-iterL S W d k (suc n) J =
  trans (fIterD-suc S W d k n J) (fIterD-is-iterL S W d k n (fLvlD S W d J))

-- THE ROUTE'S NAMED MISSING PIECE, proven: ‹bound in n› = n.
fIterD-lvls : ∀ S W d k n J → 2 ≤ S → fIterD S W d k n J ≤ lvls S W d J n
fIterD-lvls S W d k n J 2≤S =
  ≤-trans (≤-reflexive (fIterD-is-iterL S W d k n J))
          (iterL-le-lvls S W d n J 2≤S)

-- The level one opIterD step's recursion reaches before its fIterD
-- tail fires — spelled out so `opIterD-budget` and the assembly speak
-- about the SAME term (it is opIterD-suc's own J₂ at J = 0).
climb : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ
climb S W d k m =
  opIterD S W d k m
    (sLvlD S W d k (suc (suc (sizeAt S 0) * suc (sizeAt S 0))))

-- WHAT MOVED OUT (2026-08-07): `opIterD-budget` and
-- `opIterD-dominated` — route steps (a)+(b) — are now PROVEN, in
-- `Verify-Budget-Sufficient.Op-Budget`, which imports this module's
-- results as finished facts.  The monolithic postulate
-- `opIterD-budget` (.Op-Budget) and its seven expression-level hypotheses are
-- gone with it: the proof is pure level arithmetic and never reaches
-- the expression level at all.
