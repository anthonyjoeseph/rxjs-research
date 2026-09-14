------------------------------------------------------------------
-- THE HOP PEEL'S EDGE, AND IT IS THE ONE OF THE THREE THAT ASKS WHAT A
-- RUN DID.  `Sync-Edge` drops the sync size across a μ unfold and
-- `Connect-Edge` drops a one-way count over a fixed telescope; neither
-- consults the machine.  This peel does: `subscribeInner` is handed an
-- observable the run PRODUCED, so the drop it needs is a fact about
-- what a subscription can deliver and not about the term it was
-- entered at.
--
-- WHAT IS ACTUALLY IN DOUBT IS THE SUBSTITUTION, AND NOTHING ELSE.
-- Every clause of the measure is a join except `strmᵗ`, so wherever the
-- delivered inner is a subterm of what delivered it the drop is that
-- one `suc`.  The arm that is not is the manufactured inner: a
-- flattener over a `mapᵉ` whose template BUILDS an observable around
-- the arriving value hands out a substitution instance, and if what is
-- substituted is itself of observable type the nesting can rise.  That
-- is the whole content of the leaf below, and it is why the leaf is
-- born in the worst class rather than read as a lemma about syntax.
--
-- AND IT IS THE CIRCULARITY THE HOP LEAF'S OWN HEADER NAMES.  That
-- header records that the inner is a runtime value structurally
-- unrelated to the term the walk inducts on, so no arm of the walk
-- reaches it — which is exactly the shape a domain predicate answers,
-- since a step whose smallness is DECIDED at the site needs nothing
-- from the induction above it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Hop-Edge where

open import Data.List using (List; []; _∷_; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat using (_<_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (proj₁)
open import Induction.WellFounded using (Acc)

open import Rx.Prim using (InstEmit; InstEvent; value; Id; Tick)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; subscribeE)
open import Rx.Exp using (Ctx; Closed; Val; obs)
open import Rx.Obs-Depth using (obsDepthᵉ)

------------------------------------------------------------------
-- WHAT A BURST DELIVERS, as a flat list.  The edge below is about the
-- observables a source actually emitted, so it needs them nameable;
-- everything else a burst carries is protocol.
------------------------------------------------------------------

emitVals : ∀ {A : Set} → List (InstEvent A) → List A
emitVals []             = []
emitVals (value v ∷ es) = v ∷ emitVals es
emitVals (_ ∷ es)       = emitVals es

burstVals : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → List (Val Γ u)
burstVals ems = concatMap (λ em → emitVals (InstEmit.events em)) ems

------------------------------------------------------------------
-- THE EDGE.  What a flattener hands `subscribeInner` is strictly
-- shallower in this measure than the source that delivered it.
--
-- THE EMISSION HYPOTHESIS IS THE STATEMENT, NOT A GUARD ON IT.  Over an
-- arbitrary `o` the inequality is refutable in one line — pick a deeper
-- term — so a form quantifying the inner freely asserts nothing about
-- this machine and everything about none.  What makes it a claim is
-- that `o` came OUT of `b`, and the whole doubt is whether a run can
-- deliver an observable nested deeper than the one it was reading.
--
-- AND IT IS STATED OVER THE SOURCE AND NOT OVER THE FLATTENER, because
-- the flattener's own clause is the identity here — `mergeAllᵉ` joins
-- nothing onto its source — so a statement against `mergeAllᵉ b` would
-- be the same inequality wearing a constructor, and the arm that
-- actually produces the inner is the source's.
------------------------------------------------------------------

postulate
  hop-drops : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri} {lo}
    (ac : Acc _≺_ τ)
    (b : Closed Γ (obs u))            -- the flattener's source
    (κ : Path Γ lo (obs u) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e)
    (o : Val Γ (obs u))               -- an observable it DELIVERED
    → o ∈ burstVals (proj₁ (subscribeE ac b κ id now sched st))
    → obsDepthᵉ o < obsDepthᵉ b

------------------------------------------------------------------
-- THE GUARD, WHICH IS WHAT THE PEEL SPENDS.  `subscribeInner` tests the
-- delivered inner against the component it is standing at, and the
-- entry invariant is what says the source is written under that
-- component — so the negative arm is closed by composing the drop with
-- the invariant, exactly as the other two peels close theirs.  It is
-- the whole of what this module owes the machine: the rank arrives as a
-- bound on the SOURCE and leaves as a strict bound on the INNER.
------------------------------------------------------------------

hop-guard : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri} {lo} {r}
  (ac : Acc _≺_ τ)
  (b : Closed Γ (obs u))
  (κ : Path Γ lo (obs u) t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e)
  (o : Val Γ (obs u))
  → o ∈ burstVals (proj₁ (subscribeE ac b κ id now sched st))
  → obsDepthᵉ b ≤ r
  → obsDepthᵉ o < r
hop-guard ac b κ id now sched st o mem hb =
  ≤-trans (hop-drops ac b κ id now sched st o mem) hb
