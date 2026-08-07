------------------------------------------------------------------
-- OP-DOMINANCE: the operator walk against the delivery count.
--
-- Consumer: Caps-Bridge's `opIterD≤sizeCount-root-core` (a real
-- definition since 2026-08-06; its seven expression-level hypotheses
-- remain the kit for `opIterD-budget`'s eventual structural proof).
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
-- WHAT IS POSTULATED (`opIterD-budget`): route steps (a)+(b) — the
-- recursion's CLIMB fits the budget: from the level `climb` reaches,
-- spending `suc (widAt _ climb)` dLvl-steps still lands within
-- `lvls 0 (cDel …)`.  This is the residual-budget invariant
-- (induction on m mutual with sLvlD's k-descent), the genuinely new
-- remaining mathematics, now one postulate with both endpoints in
-- the SAME lvls-currency — no fIterD, no fLvlD.
------------------------------------------------------------------
module Verify-Budget-Sufficient.Op-Dominance where

open import Data.Bool using (false)
open import Data.Fin  using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans)
open import Data.Vec  using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans)

open import Rx.Exp   using (Ctx; Exp; Closed; sizeᵉ; μᵉ; unfoldμ)
open import Rx.Prim  using (Source)
open import Rx.Slots using (Slots; shared; slotsSize)
open import Rx.Evaluator
  using (sizeAt; widAt; fLvlD; sLvlD; opIterD; fIterD; iterL; dLvl; lvls;
         opIterD-0; opIterD-suc; fIterD-0; fIterD-suc; memberSource)
open import Verify-Budget-Sufficient.Caps
  using (Caps; caps; cDel; lvls-mono; lvls-add; iterL-infl)
open import Verify-Budget-Sufficient.Caps-Nest
  using (nest; residAt; resid; nest≤;
         residAt-connected; share-step-resid; mu-1≤k; mu-step-le; k-raise)
open import Verify-Budget-Sufficient.Caps-Chain
  using (entry-to-index)

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

postulate
  -- Route steps (a)+(b): the climb fits the budget.  From level
  -- `climb S W d k m`, spending `suc (widAt _ climb)` dLvl-steps
  -- stays within the full budget `cDel (caps S W R) d` spent from 0.
  -- The eventual proof is the residual-budget induction on m (mutual
  -- with sLvlD's k-descent).  The seven leading hypotheses are the
  -- expression-level kit that structural induction consumes —
  -- they were the hypotheses of the deleted `opIterD≤sizeCount-root-core`
  -- in Caps-Bridge.agda, now promoted here so `opIterD-budget-core` is
  -- the single assembly that wires the whole kit.  `opIterD-budget`
  -- below applies them.
  --
  -- `1 ≤ R` IS LOAD-BEARING, and the statement without it is FALSE —
  -- machine-refuted 2026-08-06, probe/OpIterD-Budget-Probe.agda §1
  -- (`opIterD-budget-R0-false`, a proven → ⊥).  At R = 0 the registry
  -- walk is empty (`regAt S 0 J = 0 * suc (J * S) = 0`), so
  -- `cDel (caps S W 0) d = 0` and the RHS collapses to
  -- `lvls S W d 0 0 = 0`; but the LHS is a `dLvl` application and
  -- `2≤dLvl` holds unconditionally, so the claim read `2 ≤ 0`.
  opIterD-budget-core :
    -- entry-to-index  (Verify-Budget-Sufficient/Caps-Chain.agda:292)
    (∀ (S W d k J m : ℕ) → 2 ≤ S → suc (sizeAt S J) ≤ m →
      sLvlD S W d (suc k) J ≤ opIterD S W d k m J
     ) →
    -- nest≤  (Verify-Budget-Sufficient/Caps-Nest.agda:143)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t)
      (sl : Slots Γ) (cs : List Source) → nest e sl cs ≤ sizeᵉ e + slotsSize sl
     ) →
    -- residAt-connected  (Verify-Budget-Sufficient/Caps-Nest.agda:129)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source) (i : Fin n) →
      residAt sl (toℕ i ∷ cs) i ≡ 0
     ) →
    -- share-step-resid  (Verify-Budget-Sufficient/Caps-Nest.agda:198)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
      (i : Fin n) {d : Closed Γ (lookup Γ i)} (k : ℕ) → sl i ≡ shared d →
      memberSource (toℕ i) cs ≡ false →
      resid sl cs ≤ k → nest d sl (toℕ i ∷ cs) ≤ k
     ) →
    -- mu-1≤k  (Verify-Budget-Sufficient/Caps-Nest.agda:232)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
      (sl : Slots Γ) (cs : List Source) (k : ℕ) → nest (μᵉ body) sl cs ≤ k → 1 ≤ k
     ) →
    -- mu-step-le  (Verify-Budget-Sufficient/Caps-Nest.agda:240)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t)
      (sl : Slots Γ) (cs : List Source) (k : ℕ) →
      nest (μᵉ body) sl cs ≤ k → nest (unfoldμ body) sl cs ≤ k
     ) →
    -- k-raise  (Verify-Budget-Sufficient/Caps-Nest.agda:390)
    (∀ (S J : ℕ) → 1 ≤ S → suc (sizeAt S J) ≤ suc (sizeAt S (suc J))
     ) →
    ∀ S W d k m R → 2 ≤ S → k ≤ S → suc m ≤ S → 1 ≤ R →
    lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
      ≤ lvls S W d 0 (cDel (caps S W R) d)

-- Applies the seven expression-level lemmas to `opIterD-budget-core`,
-- wiring entry-to-index, nest≤, residAt-connected, share-step-resid,
-- mu-1≤k, mu-step-le, k-raise as code consumers.
opIterD-budget : ∀ S W d k m R → 2 ≤ S → k ≤ S → suc m ≤ S → 1 ≤ R →
  lvls S W d (climb S W d k m) (suc (widAt S W (climb S W d k m)))
    ≤ lvls S W d 0 (cDel (caps S W R) d)
opIterD-budget = opIterD-budget-core
  entry-to-index
  (λ {n} {Γ} {Δᵍ} {Δ} {Θ} {t} → nest≤ {n} {Γ} {Δᵍ} {Δ} {Θ} {t})
  (λ {n} {Γ} → residAt-connected {n} {Γ})
  (λ {n} {Γ} → share-step-resid {n} {Γ})
  (λ {n} {Γ} {t} → mu-1≤k {n} {Γ} {t})
  (λ {n} {Γ} {t} → mu-step-le {n} {Γ} {t})
  k-raise

-- THE ASSEMBLY — the arithmetic core of opIterD≤sizeCount-root-core,
-- previously the monolithic postulate `opIterD-dominated` (probe
-- Battery-OpIter-Symbolic).  m = 0 is real; m = suc _ is the proven
-- fIterD tail (fIterD-lvls) over the postulated climb budget.
--
-- `1 ≤ R` is inherited from opIterD-budget, and only the suc case
-- spends it: at m = 0 the LHS is 0 by opIterD-0, so the R = 0
-- collapse is harmless there.  It is carried in the signature
-- regardless, because the suc case needs it and a hypothesis that
-- appears in one clause belongs to the statement.
opIterD-dominated : ∀ S W d k m R → 2 ≤ S → k ≤ S → m ≤ S → 1 ≤ R →
  opIterD S W d k m 0 ≤ lvls S W d 0 (cDel (caps S W R) d)
opIterD-dominated S W d k zero    R 2≤S hk hm hR =
  ≤-trans (≤-reflexive (opIterD-0 S W d k 0)) z≤n
opIterD-dominated S W d k (suc m) R 2≤S hk hm hR =
  ≤-trans (≤-reflexive (opIterD-suc S W d k m 0))
    (≤-trans (fIterD-lvls S W d k
                (suc (widAt S W (climb S W d k m))) (climb S W d k m) 2≤S)
             (opIterD-budget S W d k m R 2≤S hk hm hR))
