------------------------------------------------------------------
-- TWO OBSTACLES THE CONJUNCT'S REMAINING CLAUSES RUN INTO, settled here
-- before either is ground in the ~20-minute SCC.
--
-- § 1  THE FUEL-EXHAUSTED FRAME CLAUSE IS NOT PROVABLE FROM WHAT IT
--   HOLDS, and it is not a matter of finding the arithmetic.
--   `stepFrame-caps`'s conjunct is `j + j′ ≤ fLvlD S W dep j`; the depth
--   split its thru-outer clause needs (`fLvlD S W (suc d) J` unfolds to
--   the payload walk at `d`) leaves a `dep = 0` clause whose only receipt
--   is the walk's, at `sIterD S W 0 …`.  And that receipt's target is
--   STRICTLY LARGER than the goal: § 1 proves
--
--       suc (fLvlD S W 0 j) ≤ sIterD S W 0 (suc k) (suc m) j
--
--   so no monotone transport from the receipt to the goal can exist, at
--   any k and m a frame actually presents (the refreshed budget is a
--   successor by construction, and a frame with no payloads reports 0).
--   The clause therefore needs the case to be UNREACHABLE — i.e. a
--   hypothesis tying `dep` to the gas the clique already carries, which
--   is the obligation Rx.Evaluator records as owed ("the story index
--   dominating the depth an instant reaches").
--
--   AND RELOCATING THE SPLIT DOES NOT HELP.  Exactly one edge of the
--   cycle can spend the fuel, because `fIterD`/`opIterD`/`sIterD` all
--   pass `d` through and only `fLvlD S W (suc d)` steps it.  Stating the
--   frame conjunct at `suc dep` instead moves the decrement to
--   subscribeInner → subscribeE, whose base case is false the same way.
--   § 1b is that second row.
--
-- § 2  subscribeInner's THREE RUNGS ARE AFFORDABLE, but only if its IH
--   is minted at the PAYLOAD's size rather than at the level's cap.  The
--   clause reports `suc (suc (suc j₂))` while its IH bounds `suc j + j₂`,
--   so three units have to come from somewhere; at the cap there is
--   nothing left over, and at `suc (sizeᵉ o)` there are spare operator
--   arcs.  One spare arc is worth at least one unit (§ 2a), the room is
--   there (§ 2c), and three arcs cover the clause (§ 2b).
------------------------------------------------------------------
module Fuel-Room-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-mono-≤; +-monoʳ-≤; *-mono-≤;
         *-distribˡ-+; *-identityʳ; +-comm; +-assoc; m≤m+n; m≤n+m; n≤1+n)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)

open import Rx.Evaluator
  using (sizeAt; widAt; fLvl; fLvlD; sIterD; sLvlD; opIterD; fIterD;
         fIterD-suc; sIterD-suc; sLvlD-suc; opIterD-suc; iterSize)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; iterSize-infl;
         fLvlD-mono; sIterD-infl; sLvlD-infl; opIterD-infl; fIterD-infl;
         opIterD-mono; sLvlD-mono)
open import Verify-Budget-Sufficient.Caps-Sadd
  using (fLvlD-sadd; opIterD-sadd)
open import Verify-Budget-Sufficient.Caps-Nest using (sizeAt-suc; core)

------------------------------------------------------------------
-- § 1.  THE WALK'S RECEIPT AT ZERO FUEL EXCEEDS THE FRAME'S GOAL.
--
-- `sIterD S W 0 (suc k) (suc m) j` reaches `sLvlD S W 0 (suc k) (suc j)`,
-- which is a whole `opIterD` sweep at level `suc j`, which reaches an
-- `fIterD` whose first step is `fLvlD S W 0` at a level ABOVE `suc j`.
-- `fLvlD S W 0` is monotone and +1-superadditive, so the composite is
-- already past `suc (fLvlD S W 0 j)`.  Zero fuel does not make the family
-- degenerate — only `fLvlD`'s own clause bottoms out; every other
-- transformer still recurses on k and m at d = 0
------------------------------------------------------------------

zero-fuel-walk-exceeds : ∀ (S W k m j : ℕ) → 2 ≤ S →
  suc (fLvlD S W 0 j) ≤ sIterD S W 0 (suc k) (suc m) j
zero-fuel-walk-exceeds S W k m j 2≤S =
  ≤-trans (≤-trans (fLvlD-sadd {S} {W} {j} 0 2≤S)
                   (≤-trans (fLvlD-mono 0 0 2≤S ≤-refl ≤-refl sucj≤X ≤-refl)
                            reach))
          (≤-reflexive (sym (sIterD-suc S W 0 (suc k) m j)))
  where
  -- the sweep the walk's first payload opens, and the level it climbs to
  J₁ = suc j
  B  = sizeAt S J₁
  J₀ = suc (J₁ + suc B * suc B)
  X  = opIterD S W 0 k (sizeAt S J₁) (sLvlD S W 0 k J₀)

  sucj≤X : suc j ≤ X
  sucj≤X = ≤-trans (≤-trans (n≤1+n J₁)
                            (≤-trans (s≤s (m≤m+n J₁ (suc B * suc B)))
                                     (sLvlD-infl S W 0 k J₀)))
                   (opIterD-infl S W 0 k (sizeAt S J₁) (sLvlD S W 0 k J₀))

  -- and the sweep's own first frame is an `fLvlD S W 0` at that level
  reach : fLvlD S W 0 X ≤ sIterD S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))
  reach =
    ≤-trans (≤-trans (fIterD-infl S W 0 k (suc (widAt S W X)) (fLvlD S W 0 X))
                     (≤-trans (≤-reflexive (sym (fIterD-suc S W 0 k (suc (widAt S W X)) X)))
                              (≤-reflexive (sym (opIterD-suc S W 0 k (sizeAt S J₁) J₁)))))
            (≤-trans (≤-reflexive (sym (sLvlD-suc S W 0 k J₁)))
                     (sIterD-infl S W 0 (suc k) m (sLvlD S W 0 (suc k) (suc j))))

------------------------------------------------------------------
-- § 1b.  AND THE OTHER PLACEMENT OF THE DECREMENT HAS THE SAME BASE.
-- If the frame conjunct is stated at `suc dep`, the decrement lands on
-- subscribeInner → subscribeE: a payload's entry at fuel `d` would have
-- to be met by a subscribe reporting at `suc d`.  At `d = 0` that asks a
-- fuel-1 sweep to fit inside a fuel-0 one, which is the wrong direction —
-- the family is monotone in the fuel, so the SMALLER fuel is the smaller
-- number, and there is nothing to spend
zero-fuel-entry-wrong-way : ∀ (S W k J : ℕ) → 2 ≤ S →
  opIterD S W 0 k (suc (sizeAt S J)) J ≤ opIterD S W 1 k (suc (sizeAt S J)) J
zero-fuel-entry-wrong-way S W k J 2≤S =
  opIterD-mono (suc (sizeAt S J)) (suc (sizeAt S J)) 0 1 k k 2≤S
    ≤-refl ≤-refl ≤-refl (z≤n) ≤-refl ≤-refl

------------------------------------------------------------------
-- § 2.  THE SPARE-ARC FAMILY, and the room subscribeInner needs.
--
-- § 2a  ONE SPARE OPERATOR ARC IS WORTH AT LEAST ONE UNIT.  An arc
-- subscribes at a level ABOVE the one it started at (`J₀ = suc (J + …)`)
-- and then pushes frames, so the sweep with one more arc left dominates
-- the sweep without it, strictly
------------------------------------------------------------------

spare-arc : ∀ (S W d k m J : ℕ) → 2 ≤ S →
  suc (opIterD S W d k m J) ≤ opIterD S W d k (suc m) J
spare-arc S W d k m J 2≤S =
  ≤-trans (≤-trans (opIterD-sadd {S} {W} {J} m d k 2≤S)
                   (≤-trans (opIterD-mono m m d d k k 2≤S ≤-refl ≤-refl sucJ≤ ≤-refl
                               ≤-refl ≤-refl)
                            (fIterD-infl S W d k (suc (widAt S W X)) X)))
          (≤-reflexive (sym (opIterD-suc S W d k m J)))
  where
  B  = sizeAt S J
  J₀ = suc (J + suc B * suc B)
  X  = opIterD S W d k m (sLvlD S W d k J₀)
  sucJ≤ : suc J ≤ sLvlD S W d k J₀
  sucJ≤ = ≤-trans (s≤s (m≤m+n J (suc B * suc B))) (sLvlD-infl S W d k J₀)

-- § 2b  THREE OF THEM COVER THE CLAUSE.  subscribeInner reports
-- `suc (suc (suc j₂))` against an IH that bounds `suc j + j₂`, so the
-- three folds it charges for the `splitBurst` square are exactly three
-- spare arcs
spare-arc-3 : ∀ (S W d k m J : ℕ) → 2 ≤ S →
  suc (suc (suc (opIterD S W d k m J))) ≤ opIterD S W d k (suc (suc (suc m))) J
spare-arc-3 S W d k m J 2≤S =
  ≤-trans (s≤s (s≤s (spare-arc S W d k m J 2≤S)))
          (≤-trans (s≤s (spare-arc S W d k (suc m) J 2≤S))
                   (spare-arc S W d k (suc (suc m)) J 2≤S))

-- § 2c  AND THE ROOM IS THERE: the payload's own size sits three arcs
-- below the level cap the entry mints at, because one size level at least
-- doubles.  `sizeAt S (suc j)` is `S * suc (2 * sizeAt S j)`, and at
-- `2 ≤ S` that is `≥ 2 + 4 * sizeAt S j`
arc-room : ∀ (S j : ℕ) → 2 ≤ S →
  suc (suc (suc (sizeAt S j))) ≤ sizeAt S (suc j)
arc-room S j 2≤S =
  ≤-trans step (≤-reflexive (sym (sizeAt-suc S j)))
  where
  x   = sizeAt S j
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  1≤x : 1 ≤ x
  1≤x = ≤-trans 1≤S (iterSize-infl S 1≤S j S)
  -- 3 + x ≤ 2 * suc (2 * x) ≤ S * suc (2 * x)
  two : suc (suc (suc x)) ≤ 2 * suc (2 * x)
  two = ≤-trans (s≤s (s≤s (s≤s (≤-trans (m≤m+n x x)
                                  (≤-reflexive (cong (x +_) (sym (+-identityʳ x))))))))
                (≤-reflexive (sym (trans (cong (λ z → suc (2 * x) + z)
                                              (*-identityʳ (suc (2 * x))))
                                        (help x))))
    where
    help : ∀ (y : ℕ) → suc (2 * y) + suc (2 * y) ≡ 2 * suc (2 * y)
    help y = trans (cong (suc (2 * y) +_) (sym (+-identityʳ (suc (2 * y)))))
                   refl
  step : suc (suc (suc x)) ≤ S * suc (2 * x)
  step = ≤-trans two (*-mono-≤ 2≤S ≤-refl)
