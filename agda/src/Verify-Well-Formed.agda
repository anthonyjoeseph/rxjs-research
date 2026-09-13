-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- DRY-FREE RUN.  `The-Proof` draws `evaluate-well-formed` and nothing
-- else from this face: a canonical run's emit stream is accepted by the
-- protocol automaton, which is what lets the batcher be quantified over
-- WellFormed streams rather than arbitrary ones.
--
-- WHY THE BODY IS A SPLIT AND NOT A BARE POSTULATE.  Dry-freeness is
-- the descent's own output and is proven elsewhere; the bookkeeping is
-- this face's debt.  Stating the debt as ONE leaf conditioned on the
-- two halves' dry-freeness, and splitting the descent's conclusion
-- HERE, is what keeps the leaf a leaf: the split is performed by a real
-- lemma, so the descent's theorem is CONSUMED rather than handed to a
-- postulate as its only use — which would earn it no reachability and
-- would assert that the two are sufficient without ever checking it.
--
-- AND THE SPLIT IS THE SHAPE THE DEBT IS OWED IN, not a convenience.
-- The two halves are stepped by different machinery — a subscribe frame
-- returns its burst in one go while the drain spends one unit per
-- arrival — so a bookkeeping argument is an induction over the drain
-- seeded at whatever the burst left, and the seam is where the seed is
-- handed over.  A leaf stated over the concatenation would have to
-- rediscover that seam inside its own proof.
module Verify-Well-Formed where

open import Data.Bool using (false; true)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEmit)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; evaluate; subscribeE; drain; root;
  rootWitness; sched-init; st-init; hasDry; dryEvent)
open import Rx.Protocol using (WellFormed)
open import Verify-Rank-Sufficient using (rank-sufficient)
open import Decide using (true≢false)

------------------------------------------------------------------
-- THE SEAM, NAMED.  Both halves re-enter the same subscribe frame, so
-- naming them here is what lets the leaf below mention each without
-- restating the entry term — and `evaluate` reduces to their
-- concatenation definitionally, which is what makes the split apply to
-- the descent's own conclusion.
------------------------------------------------------------------

rootBurst : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Stream Γ t
rootBurst {n = n} e ins =
  proj₁ (subscribeE {lo = n} (rootWitness e ins) e root 0 0
          (sched-init e ins) (st-init e))

rootDrain : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → Stream Γ t
rootDrain {n = n} fuel e ins =
  drain fuel 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where
  r = subscribeE {lo = n} (rootWitness e ins) e root 0 0
        (sched-init e ins) (st-init e)

-- dry-freeness splits over a concatenation, which is the direction the
-- descent's conclusion has to be taken apart in.  The builder of the
-- same shape lives with the descent and goes the other way.
hasDry-split : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry (xs ++ ys) ≡ false →
  (hasDry xs ≡ false) × (hasDry ys ≡ false)
hasDry-split []        ys h = refl , h
hasDry-split (em ∷ xs) ys h
  with any dryEvent (InstEmit.events em)
... | true  = true≢false h
... | false = hasDry-split xs ys h

------------------------------------------------------------------
-- THE DEBT.  Everything the protocol argument needs about a run whose
-- two halves are dry-free.  It is one leaf because nothing above it has
-- yet decided the shape the bookkeeping should take — the descent it
-- rests on is still open, and a statement carved into pieces against a
-- machine whose recursion may be restated is inventory rather than
-- progress.
------------------------------------------------------------------

postulate
  burst-drain-well-formed :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
    hasDry (rootBurst e ins) ≡ false →
    hasDry (rootDrain fuel e ins) ≡ false →
    WellFormed (evaluate fuel e ins)

evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins =
  let (nodry₀ , nodry₁) =
        hasDry-split (rootBurst e ins) (rootDrain fuel e ins)
          (rank-sufficient fuel e ins)
  in burst-drain-well-formed fuel e ins nodry₀ nodry₁
