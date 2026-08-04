------------------------------------------------------------------
-- THE ONE CLAUSE THAT REPORTS A WITNESS FOR THE CARDINALITY ALONE, and
-- what its conjunct actually costs.
--
-- `thruConsume-caps`'s concat-queue push is the only clique clause whose
-- witness is `1` rather than `0` or a callee's: `widNode` bounds the
-- queue's LENGTH, so growing it by one has to be paid for with a level.
-- Its conjunct is therefore
--
--     suc (j + 1) ≤ sLvlD S W dep bud (suc j)
--
-- and that is NOT an instance of `inner-nil` — it needs room STRICTLY
-- above `suc j`, where the nil lemma only reaches `suc j` itself.
--
-- § 1 shows the statement is FALSE without a positive budget, so the
-- clause cannot close by inflation alone.  § 2 gets the budget's
-- positivity from a hypothesis the head already carries.  § 3 is the
-- strict step, which is `opIterD-infl`'s own `suc m` chain minus its
-- first link.  § 4 assembles them at the clause's exact goal.
--
-- NOTE the transformers are `abstract` (Rx.Evaluator:730), so NOTHING
-- here reduces: every step opens a clause equation by hand, exactly as
-- .Caps-Chain's header says.  An earlier draft of this probe tried to
-- refute § 1 by pattern-matching `s≤s` against `sLvlD S W d 0 1` and got
-- stuck on the unification — that stuckness IS the abstractness.
------------------------------------------------------------------
module Queue-Push-Probe where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; +-comm; n≤1+n; m≤m+n; n≮n)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong; subst)

open import Rx.Evaluator
  using (sizeAt; widAt; sLvlD; opIterD; fIterD; opIterD-suc; sLvlD-suc; sLvlD-0)
open import Verify-Budget-Sufficient.Caps
  using (sLvlD-infl; opIterD-infl; fIterD-infl)

------------------------------------------------------------------
-- § 1.  WITHOUT A POSITIVE BUDGET THE CONJUNCT IS FALSE.  `sLvlD S W d
-- zero J` is `J` on the nose, so at `bud = 0` the goal asks
-- `suc (suc j) ≤ suc j`.  Recording this as a real refutation rather
-- than a remark: it is the reason the clause needs § 2 at all, and it
-- rules out closing this site the way the other 20 in the head close.
------------------------------------------------------------------

zero-bud-refutes : ∀ (S W d j : ℕ) →
  suc (j + 1) ≤ sLvlD S W d 0 (suc j) → ⊥
zero-bud-refutes S W d j h =
  n≮n (suc j)
      (subst (λ y → suc y ≤ suc j) (+-comm j 1)
             (subst (λ x → suc (j + 1) ≤ x) (sLvlD-0 S W d (suc j)) h))

------------------------------------------------------------------
-- § 2.  AND THE BUDGET IS POSITIVE, from the head's own `nest`
-- hypothesis.  Every clique head carries `nest o sl cs ≤ bud`, and
-- `nest e sl cs = syncSizeᵉ e + resid sl cs` with every `syncSizeᵉ`
-- base case at least 1.  So one `≤-trans` on a positivity fact turns
-- the hypothesis into `1 ≤ bud`, which is all the clause needs — it
-- never looks at what the budget IS.
--
-- Stated over an abstract witness of positivity so the probe does not
-- depend on `syncSizeᵉ`'s clause list.
------------------------------------------------------------------

bud-pos : ∀ (nst bud : ℕ) → 1 ≤ nst → nst ≤ bud → 1 ≤ bud
bud-pos nst bud 1≤n n≤b = ≤-trans 1≤n n≤b

------------------------------------------------------------------
-- § 3.  THE STRICT STEP.  `opIterD-infl`'s `suc m` branch proves
-- `J ≤ opIterD …` by first weakening `J ≤ suc J` and then climbing;
-- every link after that first one is already about `suc J`.  Dropping
-- the link gives the strict bound, with no new arithmetic.
------------------------------------------------------------------

opIterD-strict : ∀ (S W d k m J : ℕ) → suc J ≤ opIterD S W d k (suc m) J
opIterD-strict S W d k m J =
  let J₀ = suc (J + suc (sizeAt S J) * suc (sizeAt S J))
      J₂ = opIterD S W d k m (sLvlD S W d k J₀)
  in ≤-trans (≤-trans (≤-trans (s≤s (m≤m+n J (suc (sizeAt S J) * suc (sizeAt S J))))
                               (≤-trans (sLvlD-infl S W d k J₀)
                                        (opIterD-infl S W d k m (sLvlD S W d k J₀))))
                      (fIterD-infl S W d k (suc (widAt S W J₂)) J₂))
             (≤-reflexive (sym (opIterD-suc S W d k m J)))

------------------------------------------------------------------
-- § 4.  THE CLAUSE'S GOAL, assembled.  `sLvlD`'s positive-budget
-- equation opens into an `opIterD` whose index is `suc (sizeAt S (suc
-- j))` — already a successor, so § 3 applies with no side condition —
-- and `j + 1 ≡ suc j` is the `lvl` the clause already proves for its
-- caps component.
------------------------------------------------------------------

queue-push : ∀ (S W d bud j : ℕ) → 1 ≤ bud →
  suc (j + 1) ≤ sLvlD S W d bud (suc j)
queue-push S W d (suc b) j _ =
  subst (λ y → suc y ≤ sLvlD S W d (suc b) (suc j)) (sym (+-comm j 1))
        (≤-trans (opIterD-strict S W d b (sizeAt S (suc j)) (suc j))
                 (≤-reflexive (sym (sLvlD-suc S W d b (suc j)))))
