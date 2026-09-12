-- THE ENTRY INVARIANT DOES NOT REACH THE RANK, AND THE OPERATOR LEAF IS
-- FALSE BECAUSE OF IT.
--
-- `EntryReads` carries two conjuncts — the unconnected count under the
-- triple's first component, the expression's syncSize under its third —
-- and says nothing whatever about the second.  That was a deliberate
-- reading: the rank is about an emitted INNER, a runtime value
-- structurally unrelated to the term being subscribed, so no equation on
-- syntax reaches it.  What follows from the silence is that the operator
-- leaf quantifies over a triple whose rank is ZERO, and at rank zero the
-- inner-subscribe clause does not subscribe anything: it returns the dry
-- close outright.  So the leaf is refuted by the smallest operator that
-- subscribes an inner inside its own subscribe frame, entered at a
-- triple the invariant is perfectly happy with.
--
-- WHAT THIS KILLS IS THE STATEMENT, NOT THE READING.  Every run the
-- evaluator actually performs enters at `rootTri`, whose rank is
-- `2 ^ (sizeᵉ e + slotsSize sl)` and so is never zero; the top-line claim
-- is untouched.  What is dead is deriving it from a lemma universally
-- quantified over the triple, because the seeding is the only thing
-- keeping the rank off the floor and the invariant is where seeding
-- facts are supposed to travel.  The repair is a third conjunct, and
-- this witness is what licenses adding one rather than weakening a
-- statement to fit a proof.
--
-- AND THE SAME HOLE IS OPEN ONE DOOR ALONG: the drain leaf quantifies
-- over an arbitrary schedule and an arbitrary evaluator state, and
-- re-seeds its rank from the program alone, so an adversarial registry
-- holding a path with more stacked `*All` frames than `2 ^ sizeᵉ e`
-- peels the same clause from the other side.  That one needs a reached
-- state rather than a written one, so it is not witnessed here.
module Refuted.Rank-Entry where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; natᵗ; strmᵗ; nat̂; ofᵉ; mergeAllᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE; root;
  sched-init; st-init; hasDry)
open import Verify-Rank-Sufficient.Dry using (opShape)
open import Verify-Rank-Sufficient.Entry using (EntryReads)

----------------------------------------------------------------------
-- THE STATEMENT, RESTATED HERE RATHER THAN IMPORTED.  A refutation that
-- applies the postulate is evidence about whatever that postulate says
-- today; written out, this one is evidence about the form it was taken
-- against, and a restatement that adds the missing conjunct makes the
-- witness below fail to typecheck rather than quietly agree with it.
----------------------------------------------------------------------

DryOperator : Set
DryOperator = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
  (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
  EntryReads τ o (Sched.slots sched) (EvalSt.connectedShares st) →
  hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

----------------------------------------------------------------------
-- THE ADVERSARIAL ENTRY.  The context is empty, so the unconnected
-- count is zero and its conjunct is satisfied at U = 0 — the tightest
-- the invariant can be asked for.  The syncSize conjunct is satisfied by
-- reflexivity.  The rank is set to zero, which no conjunct forbids, and
-- that is the whole of the finding.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

-- the smallest operator that subscribes an inner during its own
-- subscribe frame: a merge over a synchronous one-element outer whose
-- single value IS an observable
prog : Closed Γ₀ natᵗ
prog = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ []))

opShape-prog : opShape prog ≡ true
opShape-prog = refl

τ₀ : Tri
τ₀ = 0 , 0 , syncSizeᵉ prog

ac₀ : Acc _≺_ τ₀
ac₀ = ≺-wellFounded τ₀

reads₀ : EntryReads τ₀ prog (Sched.slots (sched-init prog ins₀))
                            (EvalSt.connectedShares (st-init prog))
reads₀ = z≤n , ≤-refl

burst₀ : Stream Γ₀ natᵗ
burst₀ = proj₁ (subscribeE ac₀ prog root 0 0 (sched-init prog ins₀) (st-init prog))

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl` RATHER THAN COMPUTED INSIDE THE ⊥.  The
-- burst is one emit long and its one event is the dry close, so the
-- figure moves the moment either side of the comparison does — which is
-- what makes this witness fail loudly instead of silently agreeing with
-- a repaired statement.
----------------------------------------------------------------------

dry₀ : hasDry burst₀ ≡ true
dry₀ = refl

dry-operator-false : DryOperator → ⊥
dry-operator-false h
  with trans (sym (h ac₀ prog root 0 0 (sched-init prog ins₀) (st-init prog)
                     opShape-prog reads₀))
             dry₀
... | ()
