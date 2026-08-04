------------------------------------------------------------------
-- THE KEYSTONE: subscribeInner-caps's own conjunct, and where the two
-- extra rungs come from.
--
-- Twenty-four clauses of `thruConsume-caps` now project this one, so it
-- is the single obligation standing under all of them.  Its shape is
-- forced from BOTH sides and is not up for choice:
--
--   · its CONSUMER is `walk-step-suc`, whose first premise is
--     `suc (j + j₁) ≤ sLvlD S W d k (suc j)` — so the conjunct reports
--     strictly, at `suc j`, in `sLvlD`
--   · its own witness is `suc (suc (suc j₂))`, because the clause's caps
--     components live at `frameStep (j + suc (suc (suc j₂)))`: the
--     `splitBurst` square costs TWO levels (the product of burst length
--     by one emit's value count) on top of the inner subscribe's own
--     `suc j + j₂`
--
-- So the conjunct needs THREE more than the IH provides, and the IH's
-- bound is tight where it lands.  The slack is not in the IH — it is in
-- `opIterD`'s interior, and `-sadd` is what reaches it: `suc (F J) ≤ F
-- (suc J)` twice over turns the IH's report into a report two levels
-- higher, and `opIterD`'s own `J₀` excursion is more than two levels
-- above `suc j` for free (its quadratic term is positive).
--
-- § 1 fixes the index the IH must be called at.  § 2 is the assembly.
------------------------------------------------------------------
module Inner-Step-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-comm; +-suc; +-assoc; +-identityʳ;
         +-monoʳ-≤; +-mono-≤; n≤1+n; m≤m+n; m≤n+m)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; sLvlD; opIterD; fIterD; opIterD-suc; sLvlD-suc)
open import Verify-Budget-Sufficient.Caps
  using (sLvlD-infl; opIterD-infl; fIterD-infl; opIterD-mono; iterSize-infl)
open import Verify-Budget-Sufficient.Caps-Sadd using (opIterD-sadd)

------------------------------------------------------------------
-- § 1.  THE IH IS CALLED AT INDEX `sizeAt S (suc j)`, NOT AT ITS
-- SUCCESSOR.  `sLvlD S W d (suc k) (suc j)` opens into `opIterD … (suc
-- (sizeAt S (suc j))) (suc j)`, and it is the step from that index down
-- to its predecessor that exposes the `J₀` excursion the rungs are paid
-- out of.  Calling the IH at `suc (sizeAt S (suc j))` — which is what
-- the clause does today — lands it flush against the target and leaves
-- nothing over, which is exactly why the site could not be closed.
--
-- AND THE GAP IS THREE, not two — the count is worth doing carefully,
-- since getting it wrong is what a weak hole would have hidden.  The
-- conjunct's left side is `suc (j + suc (suc (suc j₂)))`, which is FOUR
-- above `j + j₂`, while the IH delivers ONE above it.  So three `-sadd`
-- steps, and `J₀` has to clear `suc j` by three.
--
-- That needs `2 ≤ suc B * suc B`, which — unlike the two-step version —
-- is NOT free: at `B = 0` the square is 1 and the bound fails.  It comes
-- from the size cap being at least 2, which `iterSize-infl` gives from
-- `2 ≤ S`, since `sizeAt S J` is `iterSize S J S`.  Stated with the
-- successors on the OUTSIDE because `_+_` recurses on its first
-- argument, which leaves a literal `j + 3` stuck on a variable.
------------------------------------------------------------------

2≤sizeAt : ∀ (S J : ℕ) → 2 ≤ S → 2 ≤ sizeAt S J
2≤sizeAt S J 2≤S = ≤-trans 2≤S (iterSize-infl S (≤-trans (s≤s z≤n) 2≤S) J S)

J₀-room : ∀ (S j : ℕ) → 2 ≤ S →
  suc (suc (suc (suc j)))
    ≤ suc (suc j + suc (sizeAt S (suc j)) * suc (sizeAt S (suc j)))
J₀-room S j 2≤S =
  s≤s (s≤s (≤-trans (≤-reflexive (sym (+-comm j 2)))
                    (+-monoʳ-≤ j sq)))
  where
  sq : 2 ≤ suc (sizeAt S (suc j)) * suc (sizeAt S (suc j))
  sq = ≤-trans (≤-trans (2≤sizeAt S (suc j) 2≤S) (n≤1+n (sizeAt S (suc j))))
               (m≤m+n (suc (sizeAt S (suc j)))
                      (sizeAt S (suc j) * suc (sizeAt S (suc j))))

------------------------------------------------------------------
-- § 2.  THE ASSEMBLY.  Target, after `sLvlD-suc` and `opIterD-suc`:
--
--     fIterD S W d k (suc (widAt S W J₂)) J₂    with
--     J₂ = opIterD S W d k B (sLvlD S W d k J₀)
--
-- and `fIterD` being inflationary means it suffices to reach `J₂`.  From
-- the IH at `opIterD … B (suc j)`, two `-sadd` steps give the same
-- transformer two levels up, § 1 puts `sLvlD … J₀` at least that high,
-- and level-monotonicity carries it the rest of the way.
------------------------------------------------------------------

inner-step : ∀ (S W d k j j₂ : ℕ) → 2 ≤ S →
  suc j + j₂ ≤ opIterD S W d k (sizeAt S (suc j)) (suc j) →
  suc (j + suc (suc (suc j₂))) ≤ sLvlD S W d (suc k) (suc j)
inner-step S W d k j j₂ 2≤S ih =
  ≤-trans (≤-trans (≤-reflexive shape) climb)
          (≤-reflexive (sym (trans (sLvlD-suc S W d k (suc j))
                                   (opIterD-suc S W d k B (suc j)))))
  where
  B  = sizeAt S (suc j)
  J₀ = suc (suc j + suc B * suc B)
  L  = sLvlD S W d k J₀
  J₂ = opIterD S W d k B L

  -- the goal's left side, regrouped as "the IH's total, plus three"
  shape : suc (j + suc (suc (suc j₂))) ≡ suc (suc (suc (suc (j + j₂))))
  shape = cong suc (trans (+-suc j (suc (suc j₂)))
                          (cong suc (trans (+-suc j (suc j₂))
                                           (cong suc (+-suc j j₂)))))

  -- three -sadd steps lift the IH's transformer three levels
  lift3 : suc (suc (suc (opIterD S W d k B (suc j))))
            ≤ opIterD S W d k B (suc (suc (suc (suc j))))
  lift3 = ≤-trans (s≤s (≤-trans (s≤s (opIterD-sadd {S} {W} {suc j} B d k 2≤S))
                                (opIterD-sadd {S} {W} {suc (suc j)} B d k 2≤S)))
                  (opIterD-sadd {S} {W} {suc (suc (suc j))} B d k 2≤S)

  -- and § 1 says `L` is at least that high, so monotonicity finishes
  climb : suc (suc (suc (suc (j + j₂)))) ≤ fIterD S W d k (suc (widAt S W J₂)) J₂
  climb =
    ≤-trans (≤-trans (≤-trans (s≤s (s≤s (s≤s ih))) lift3)
                     (opIterD-mono B B d d k k 2≤S ≤-refl ≤-refl
                        (≤-trans (J₀-room S j 2≤S) (sLvlD-infl S W d k J₀))
                        ≤-refl ≤-refl ≤-refl))
            (fIterD-infl S W d k (suc (widAt S W J₂)) J₂)
