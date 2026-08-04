------------------------------------------------------------------
-- WHICH TRANSFORMER `subscribeE-caps` REPORTS IN, and why it is not the
-- one the member's entry is priced by.
--
-- Step C was scoped as "add a conjunct".  Before forty-two clauses are
-- rewritten it is worth checking that the conjunct can actually be
-- CHAINED, because the composition gate's operator step consumes its
-- source's receipt in a particular shape and a subscribe is entered in a
-- different one.
--
--   ENTRY.  A fresh subscribe at level J on budget `suc k` is priced by
--     `sLvlD S W d (suc k) J`, which is `opIterD S W d k (suc (sizeAt S J)) J`
--     — an operator sweep long enough for the whole chain, since a
--     chain is no longer than the size cap.
--
--   WALK.  `op-step` consumes its SOURCE's receipt at
--     `opIterD S W d k m (suc j)` — the sweep with m operators LEFT — and
--     concludes at `opIterD S W d k (suc m) j`.  m descends by one per
--     operator.
--
-- So the recursive call inside an operator clause is not a fresh entry:
-- it is the same sweep with one fewer operator to go.  § 1 shows the two
-- shapes do NOT convert in the direction the grind would need, and § 2
-- shows the residual index is what makes them meet — which means the
-- conjunct carries an INDEX, and Step C threads a third number through
-- the chain members the way Step A threaded the first two.
------------------------------------------------------------------
module Chain-Index-Probe where

open import Data.Nat  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; n≤1+n)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; sLvlD; opIterD; sLvlD-suc; sLvlD-0;
         opIterD-0; opIterD-suc)
open import Verify-Budget-Sufficient.Caps
  using (opIterD-mono; opIterD-infl; fIterD-infl; sizeAt-mono)

------------------------------------------------------------------
-- § 1.  THE ENTRY SHAPE DOES NOT FEED THE WALK.
--
-- If `subscribeE-caps` reported its receipt at the entry transformer,
-- an operator clause would have to turn
--
--     j′ ≤ sLvlD S W d bud (suc j)      (what the recursive call gives)
-- into
--     j′ ≤ opIterD S W d k m (suc j)    (what `op-step` demands)
--
-- and at `bud = suc k` the first IS `opIterD S W d k (suc (sizeAt S (suc j))) (suc j)`.
-- So the conversion needs `suc (sizeAt S (suc j)) ≤ m` — the sweep the
-- callee was priced for must fit inside the operators the CALLER has
-- left.  It does not: m descends along the chain while the entry sweep
-- is sized for a whole one.
------------------------------------------------------------------

Entry-Feeds-Walk : Set
Entry-Feeds-Walk = ∀ (S W d k m j : ℕ) →
  sLvlD S W d (suc k) (suc j) ≤ opIterD S W d k m (suc j)

-- refuted at the smallest instance there is: one operator left, and an
-- entry sweep that is priced for `suc (sizeAt 2 1)` = 5 of them.  At
-- m = 0 the walk transformer is the identity, so the entry — which is
-- inflationary and strictly past the level — cannot fit inside it
entry-feeds-walk-absurd : Entry-Feeds-Walk → ⊥
entry-feeds-walk-absurd H =
  absurd (subst (2 ≤_) id0 (≤-trans two≤entry (H 2 1 0 0 0 0)))
  where
  J₀ : ℕ
  J₀ = suc (1 + suc (sizeAt 2 1) * suc (sizeAt 2 1))

  X : ℕ
  X = opIterD 2 1 0 0 (sizeAt 2 1) (sLvlD 2 1 0 0 J₀)

  ≤-refl′ : ∀ {a b : ℕ} → a ≡ b → a ≤ b
  ≤-refl′ refl = ≤-refl

  -- at zero operators left the walk transformer is the identity, so the
  -- conversion the grind would need reads `entry ≤ suc j`
  id0 : opIterD 2 1 0 0 0 1 ≡ 1
  id0 = opIterD-0 2 1 0 0 1

  -- while the entry sweep passes the level strictly: its first operator
  -- opens at `suc (J + …)`, already 2 above zero, and every transformer
  -- above that is inflationary
  two≤entry : 2 ≤ sLvlD 2 1 0 1 1
  two≤entry =
    ≤-trans (≤-trans (≤-trans (s≤s (s≤s z≤n)) (≤-refl′ (sym (sLvlD-0 2 1 0 J₀))))
                     (opIterD-infl 2 1 0 0 (sizeAt 2 1) (sLvlD 2 1 0 0 J₀)))
            (≤-trans (fIterD-infl 2 1 0 0 (suc (widAt 2 1 X)) X)
                     (≤-refl′ (sym (trans (sLvlD-suc 2 1 0 0 1)
                                          (opIterD-suc 2 1 0 0 (sizeAt 2 1) 1)))))

  absurd : 2 ≤ 1 → ⊥
  absurd (s≤s ())

------------------------------------------------------------------
-- § 2.  WITH THE INDEX, THEY MEET — and the meeting is one
-- `opIterD-mono` step, not a new lemma.  A callee that reports at m
-- operators feeds a caller that has `suc m`, which is exactly the
-- gate's own step; and a FRESH entry instantiates the index at
-- `suc (sizeAt S J)` and converts by the clause equation.
------------------------------------------------------------------

-- the walk direction: fewer operators left is a smaller sweep
index-mono : ∀ (S W d k m m′ J : ℕ) → 2 ≤ S → m ≤ m′ →
  opIterD S W d k m J ≤ opIterD S W d k m′ J
index-mono S W d k m m′ J 2≤S hm =
  opIterD-mono m m′ d d k k 2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl hm

-- and the entry direction: a fresh subscribe IS the sweep at the index
-- the size cap licenses, by the clause equation alone
entry-is-sweep : ∀ (S W d k J : ℕ) →
  sLvlD S W d (suc k) J ≡ opIterD S W d k (suc (sizeAt S J)) J
entry-is-sweep = sLvlD-suc

-- so a chain member's conjunct is `opIterD S W dep bud m j` with m the
-- operators it has left, and the member that is ENTERED fresh converts
-- once, at the site that also spends the budget descent
entry-to-index : ∀ (S W d k J m : ℕ) → 2 ≤ S → suc (sizeAt S J) ≤ m →
  sLvlD S W d (suc k) J ≤ opIterD S W d k m J
entry-to-index S W d k J m 2≤S hm =
  ≤-trans (≤-reflexive′ (entry-is-sweep S W d k J))
          (index-mono S W d k (suc (sizeAt S J)) m J 2≤S hm)
  where
  ≤-reflexive′ : ∀ {a b : ℕ} → a ≡ b → a ≤ b
  ≤-reflexive′ refl = ≤-refl
