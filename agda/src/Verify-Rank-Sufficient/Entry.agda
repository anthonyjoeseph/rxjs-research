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

-- AND THE SEED'S SLACK DOES NOT PAY FOR THE HOP EITHER, WHICH IS WHAT
-- THIS PAIR OF CONJUNCTS IS NOW KNOWN NOT TO REACH.  The margin is
-- exponential in the program and the readings grow with the DELIVERIES,
-- so the question is what bounds the deliveries — and for a recursive
-- source the answer is the drain's FUEL, which appears in neither
-- `sizeᵉ` nor `slotsSize`.  A constant is then being outgrown by a
-- quantity that moves without the program moving, and the invariant as
-- stated is satisfied at triples from which a run reaches the dry close.
-- The conclusion is not that a further conjunct in this currency is
-- missing but that the currency is wrong: what the rank has to dominate
-- is a count of deliveries, and no reading of syntax is one.
--
-- AND THE DELIVERIES ARE NOT ALL DRAINED, SO A CONJUNCT READING THE
-- STATE HANDED IN IS DEAD TOO.  Fuel is the axis for a RECURSIVE source
-- and a re-seed at each arrival would cover it; a literal source spends
-- every delivery inside ONE cascade, where the store is empty at the
-- entry and deepens only after.  Both a `suc` and a store-reading
-- conjunct are read BEFORE the growth they would have to pay for, which
-- is the property they share and the reason one witness kills both.
-- What bounds a burst's deliveries and survives μ-unfolding is the
-- SYNCHRONOUS size — already the third component, already guarded.
--
-- REFUTED: `Refuted.Rank-Fold` — the three-conjunct form entered one
--   peel ABOVE its tightest triple, so the crossing is not an
--   off-by-one: a fold under a flattener reaches the dry close in three
--   deliveries off a literal source, with the store reading zero.
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

-- THE SEED IS ADEQUATE WHATEVER THE RUN CONTRIBUTES, because the run's
-- reading sits UNDER the exponent and only widens it.  That is what
-- makes the seeding usable away from the root: the connect and the
-- arrival both re-seed off the state they are handed, and neither has
-- to re-argue adequacy — this is the one place it is argued, and it is
-- the rank half alone, since the connect keeps its own first component.
seed-reads : ∀ {n} {Γ : Ctx n} {u} (o : Closed Γ u) (sl : Slots Γ) (m : ℕ) →
  nestDᵉ o ≤ 2 ^ (sizeᵉ o + slotsSize sl + m)
seed-reads o sl m =
  ≤-trans (nestDᵉ≤sizeᵉ o)
          (≤-trans (m≤m+n (sizeᵉ o) (slotsSize sl))
                   (≤-trans (m≤m+n (sizeᵉ o + slotsSize sl) m)
                            (n≤2^n (sizeᵉ o + slotsSize sl + m))))

-- the root contributes nothing, since nothing has been stored yet: the
-- slot payloads a run starts from are already under `slotsSize`.
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads (rootTri e ins) e ins []
rootTri-reads e ins = ≤-refl , seed-reads e ins 0 , ≤-refl
