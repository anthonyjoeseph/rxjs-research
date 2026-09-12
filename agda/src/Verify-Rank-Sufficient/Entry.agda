------------------------------------------------------------------
-- THE ENTRY INVARIANT: the motive both settled peels are stated
-- against.
--
-- The evaluator's guards do not compare a term against its own
-- measure; they compare it against the TRIPLE THE WITNESS STANDS AT,
-- which is a separate quantity the machine seeds and re-seeds.  So a
-- peel lemma cannot be a fact about syntax alone — it needs to know
-- how the triple relates to the term about to be subscribed, and that
-- relation is what this module names.
--
-- IT IS A PAIR OF INEQUALITIES AND NOT A PAIR OF EQUATIONS, and the
-- two components are loose for DIFFERENT reasons.  The sync component
-- is re-seeded only where a μ peels, while `subscribeE` steps into an
-- operator's argument carrying the SAME witness — so by the time the
-- walk reaches a `μᵉ`, the component is the reading of some ENCLOSING
-- term and the subterm's own reading is under it.  The unconnected
-- count is re-seeded only AT a connect, while the connected list grows
-- at every connect anywhere beneath — so a caller returning from a
-- nested latch holds a count that is STALE and too large.  Never too
-- small, because nothing un-latches; that asymmetry is what makes one
-- inequality the whole of what either peel needs.
--
-- THE RANK COMPONENT IS THE NESTING, AND IT IS AN INEQUALITY FOR A
-- THIRD REASON AGAIN.  The rank peels once per `subscribeInner` hop,
-- and a hop is a `*All` layer entered — so `nestDᵉ` is what the
-- component is a bound on.  It is loose because the seed is
-- exponential in the program while the measure is linear in it, and
-- because a connect RE-SEEDS at the shared definition's own reading
-- while the caller's rank is untouched.
--
-- WHAT MAKES THIS THE CONJUNCT AND NOT A SIZE.  An emitted inner is a
-- runtime value, so no SUBTERM relation reaches it — but a `Val` at
-- `obs` IS a closed expression, so a measure does, and the one that
-- survives is the one that does not grow under μ-unfolding.  A bound
-- on `sizeᵉ` fails there outright: `unfoldμ body` is larger than
-- `μᵉ body` while the witness keeps its rank.  `nestDᵉ` truncates at
-- the `deferᵉ` gate, so unfolding leaves it EQUAL.  What it does NOT
-- buy is the HOP: an inner a burst carries does not read under its
-- emitter, so this component bounds the subject a walk is entered ON
-- and nothing the run goes on to emit, and a peel at a hop has to be
-- paid out of the seed's exponential slack rather than by comparing
-- two readings of syntax.
--
-- REFUTED: `Refuted.Burst-Nesting` — the inner-under-emitter reading,
--   at a scan whose step re-wraps its accumulator in one merge layer:
--   the program reads 1 and its burst reads 3.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Entry where

open import Data.List using (List; [])
open import Data.Nat using (ℕ; zero; suc; _+_; _^_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n;
  m^n>0; +-mono-≤; +-identityʳ)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; sizeᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Strat-Order using (Tri)
open import Rx.Nest-Depth using (nestDᵉ; nestDᵉ≤sizeᵉ)
open import Rx.Evaluator using (unconn; rootTri)

-- the triple the machine stands at READS the term it is about to
-- subscribe: the unconnected count bounds the first component, the
-- nesting the second, the sync size the third
EntryReads : ∀ {n} {Γ : Ctx n} {u} → Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads (U , R , s) o sl cs =
  unconn sl cs ≤ U × nestDᵉ o ≤ R × syncSizeᵉ o ≤ s

-- the exponential seed is generous, and this is the only place that
-- has to be said.  It is stated over a bare numeral rather than off
-- the machine because that is all the seeding arm needs: the rank is
-- `2 ^ (…)` and the measure is under the exponent.
n≤2^n : ∀ (n : ℕ) → n ≤ 2 ^ n
n≤2^n zero    = z≤n
n≤2^n (suc n) =
  ≤-trans (s≤s (n≤2^n n))
          (≤-trans (+-mono-≤ (m^n>0 2 n) (≤-refl {2 ^ n}))
                   (≤-reflexive (cong (2 ^ n +_) (sym (+-identityʳ (2 ^ n))))))

-- the root seeds all three components at the term's own reading — two
-- by reflexivity, the rank through the size it is exponential in.
-- This is the one place the seeding has to be shown adequate.
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads (rootTri e ins) e ins []
rootTri-reads e ins =
  ≤-refl
  , ≤-trans (nestDᵉ≤sizeᵉ e)
            (≤-trans (m≤m+n (sizeᵉ e) (slotsSize ins))
                     (n≤2^n (sizeᵉ e + slotsSize ins)))
  , ≤-refl
