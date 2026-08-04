------------------------------------------------------------------
-- THE THRU-OUTER FRAME AT EXHAUSTED DEPTH, and why its conjunct cannot
-- be closed from the walk's own report.
--
-- `stepFrame-caps`'s thru-outer clause is split on depth.  The `suc dep′`
-- half is ground (`frame-step`).  The `dep = zero` half — the clause's
-- own pattern is the literal `zero` — must report
--
--     j + j′ ≤ fLvlD S W 0 j
--
-- and the ONLY bound it holds on `j′` is what `thruWalk-caps` hands
-- back, namely `j + j′ ≤ sIterD S W 0 (frameBud c j) (length vals) j`.
-- So the site closes by transitivity IF AND ONLY IF the walk fits under
-- one exhausted frame:
--
--     sIterD S W 0 k m j ≤ fLvlD S W 0 j
--
-- § 1 refutes exactly that, for every positive budget and every
-- non-empty payload list — and both are positive at the call site
-- (`frameBud` is a successor, and the empty-payload case is a separate
-- clause).  It is a STRICT inequality the wrong way, so no rearrangement
-- of the transitivity recovers it.
--
-- WHY it fails is structural, not arithmetic.  `fLvlD S W zero` is the
-- fuel-exhausted clause and makes NO recursive call — that is what
-- carries the family's termination (Rx.Evaluator:764-769).  A walk at
-- depth zero, by contrast, still climbs: one payload opens `sLvlD`,
-- which at a positive budget opens `opIterD`, whose `J₀` excursion alone
-- already passes `suc (suc j)` — and then `fIterD` lays a full frame on
-- top of THAT.  A closed formula cannot dominate a term that re-enters
-- the family, so the gap is not a missing lemma.
--
-- THEREFORE the fix is a signature, not a proof: depth positivity has to
-- reach this head so the `zero` clause is absurd where a thru-outer
-- frame is stepped.  Recorded here rather than ground against, per the
-- probe-before-grind law.
------------------------------------------------------------------
module Dep0-Walk-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoˡ-≤; m≤m+n; n≤1+n)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Rx.Evaluator
  using (sizeAt; widAt; fCharge; fLvl; fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fLvlD-0; sIterD-suc; sLvlD-suc; opIterD-suc; fIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (fLvlD-infl; sIterD-infl; sLvlD-infl; opIterD-infl; fIterD-infl;
         fLvlD-mono; fCharge-mono; widAt-mono)

------------------------------------------------------------------
-- § 1.  ONE PAYLOAD AT A POSITIVE BUDGET ALREADY OVERSHOOTS THE
-- EXHAUSTED FRAME — strictly, and at every cap.
------------------------------------------------------------------

dep0-walk-overshoots : ∀ (S W k m j : ℕ) → 2 ≤ S →
  suc (fLvlD S W 0 j) ≤ sIterD S W 0 (suc k) (suc m) j
dep0-walk-overshoots S W k m j 2≤S =
  ≤-trans (≤-trans step9 climb) (≤-reflexive (sym unfold))
  where
  B  = sizeAt S (suc j)
  J₀ = suc (suc j + suc B * suc B)
  J₂ = opIterD S W 0 k B (sLvlD S W 0 k J₀)

  -- the walk's first payload, unfolded to the frame it lays down
  unfold : sIterD S W 0 (suc k) (suc m) j
             ≡ sIterD S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))
  unfold = sIterD-suc S W 0 (suc k) m j

  -- and that first payload is itself above one exhausted frame at J₂
  reach : fLvlD S W 0 J₂ ≤ sIterD S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))
  reach =
    ≤-trans (≤-trans (fIterD-infl S W 0 k (widAt S W J₂) (fLvlD S W 0 J₂))
                     (≤-reflexive (sym (fIterD-suc S W 0 k (widAt S W J₂) J₂))))
            (≤-trans (≤-reflexive
                       (sym (trans (sLvlD-suc S W 0 k (suc j))
                                   (opIterD-suc S W 0 k B (suc j)))))
                     (sIterD-infl S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))))

  -- J₂ has cleared `suc (suc j)` before any frame is laid
  ssj≤J₂ : suc (suc j) ≤ J₂
  ssj≤J₂ = ≤-trans (s≤s (s≤s (m≤m+n j (suc B * suc B))))
                   (≤-trans (sLvlD-infl S W 0 k J₀)
                            (opIterD-infl S W 0 k B (sLvlD S W 0 k J₀)))

  climb : fLvlD S W 0 (suc (suc j)) ≤ sIterD S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))
  climb = ≤-trans (fLvlD-mono 0 0 2≤S ≤-refl ≤-refl ssj≤J₂ ≤-refl) reach

  -- and one exhausted frame two levels up strictly exceeds one here.
  -- `fLvlD S W 0 J` is `(J + fCharge S W J) + suc (widAt S W J)`, and
  -- `suc (a + b) ≡ suc a + b` holds by `_+_`'s own recursion, so the
  -- strictness is just `j` against `suc (suc j)` in the left summand
  step9 : suc (fLvlD S W 0 j) ≤ fLvlD S W 0 (suc (suc j))
  step9 =
    ≤-trans (≤-trans (≤-reflexive (cong suc (fLvlD-0 S W j)))
                     (+-mono-≤ lvl wid))
            (≤-reflexive (sym (fLvlD-0 S W (suc (suc j)))))
    where
    j≤ssj : j ≤ suc (suc j)
    j≤ssj = ≤-trans (n≤1+n j) (n≤1+n (suc j))

    lvl : suc j + fCharge S W j ≤ suc (suc j) + fCharge S W (suc (suc j))
    lvl = +-mono-≤ (n≤1+n (suc j)) (fCharge-mono 2≤S ≤-refl ≤-refl j≤ssj)

    wid : suc (widAt S W j) ≤ suc (widAt S W (suc (suc j)))
    wid = s≤s (widAt-mono 2≤S ≤-refl ≤-refl j≤ssj)
