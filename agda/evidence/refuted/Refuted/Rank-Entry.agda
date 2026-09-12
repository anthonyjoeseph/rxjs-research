-- THE ENTRY INVARIANT DOES NOT REACH THE RANK, AND THE OPERATOR LEAF IS
-- FALSE BECAUSE OF IT.
--
-- An entry invariant carrying two conjuncts — the unconnected count
-- under the triple's first component, the expression's syncSize under
-- its third — says nothing whatever about the second.  The reading that
-- licensed the silence is that the rank is about an emitted INNER, a
-- runtime value taken to be structurally unrelated to the term being
-- subscribed, so that no measure of syntax reaches it.  What follows
-- from the silence is that the operator leaf quantifies over a triple
-- whose rank is ZERO, and at rank zero the inner-subscribe clause does
-- not subscribe anything: it returns the dry close outright.  So the
-- leaf is refuted by the smallest operator that subscribes an inner
-- inside its own subscribe frame, entered at a triple that invariant is
-- perfectly happy with.
--
-- WHAT THIS KILLS IS THE STATEMENT, NOT THE READING.  Every run the
-- evaluator actually performs enters at `rootTri`, whose rank is the
-- program's own hop reading and so is zero only where the program can
-- enter nothing; the top-line claim is untouched.  What is dead is
-- deriving it from a lemma universally quantified over the triple,
-- because the entry is the only thing keeping the rank off the floor
-- and the invariant is where entry facts are supposed to travel.  The
-- repair is a third conjunct, and this witness is what licenses adding
-- one rather than weakening a statement to fit a proof.
--
-- AND THE SAME HOLE IS OPEN ONE DOOR ALONG: the drain leaf quantifies
-- over an arbitrary schedule and an arbitrary evaluator state, and
-- re-enters from the arrival and the store alone, so an adversarial
-- registry holding a chain with more stacked `*All` frames than the
-- program reads peels the same clause from the other side.  That one is
-- witnessed in `Refuted.Drain-Reachable`, which is what the fit
-- hypothesis was added to answer.
module Refuted.Rank-Entry where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Id; Tick; Source)
open import Rx.Exp using (Ctx; Closed; natᵗ; strmᵗ; nat̂; ofᵉ; mergeAllᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE; root;
  sched-init; st-init; hasDry; unconn)
open import Verify-Rank-Sufficient.Dry using (opShape)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED — the invariant
-- along with the leaf standing on it.  A refutation that applies the
-- postulate is evidence about whatever that postulate says today;
-- written out, this one is evidence about the form it was taken
-- against, and an invariant that adds the missing conjunct makes the
-- witness below fail to typecheck rather than quietly agree with it.
-- Which is what happened: the shared invariant carries the rank
-- conjunct this witness bought, and the two-conjunct form survives only
-- here, as the thing refuted.
----------------------------------------------------------------------

EntryReads₂ : ∀ {n} {Γ : Ctx n} {u} → Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads₂ (U , R , s) o sl cs =
  unconn sl cs ≤ U × syncSizeᵉ o ≤ s

DryOperator : Set
DryOperator = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
  (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
  EntryReads₂ τ o (Sched.slots sched) (EvalSt.connectedShares st) →
  hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

----------------------------------------------------------------------
-- THE ADVERSARIAL ENTRY.  The context is empty, so the unconnected
-- count is zero and its conjunct is satisfied at U = 0 — the tightest
-- the invariant can be asked for.  The syncSize conjunct is satisfied by
-- reflexivity.  The rank is set to zero, which no conjunct forbids, and
-- that is the whole of the finding.
----------------------------------------------------------------------

-- THE STORE BOUND the schedule below is built at.  `evaluate` builds
-- its schedule at the fuel it then hands the drain, so a witness is
-- about a RUN only when the two agree; nothing here drains, so what the
-- bound has to be is one a run could carry rather than one chosen to
-- make the crossing easier.  A LARGER bound only enlarges the rank the
-- root would enter at, and the rank this witness picks is zero, so the
-- finding is independent of it.
SB : ℕ
SB = 30

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

reads₀ : EntryReads₂ τ₀ prog (Sched.slots (sched-init SB prog ins₀))
                             (EvalSt.connectedShares (st-init prog))
reads₀ = z≤n , ≤-refl

burst₀ : Stream Γ₀ natᵗ
burst₀ = proj₁ (subscribeE ac₀ prog root 0 0 (sched-init SB prog ins₀) (st-init prog))

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
  with trans (sym (h ac₀ prog root 0 0 (sched-init SB prog ins₀) (st-init prog)
                     opShape-prog reads₀))
             dry₀
... | ()
