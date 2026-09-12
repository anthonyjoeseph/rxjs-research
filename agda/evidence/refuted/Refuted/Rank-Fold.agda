-- THE RANK CONJUNCT DOES NOT SURVIVE A FOLD, SO THE THREE-CONJUNCT
-- ENTRY INVARIANT IS STILL NOT ENOUGH FOR THE OPERATOR LEAF.
--
-- The invariant bounds `nestDᵉ o` by the triple's rank, and that was
-- bought by a witness entering at rank ZERO — with the conjunct in
-- place, a rank of zero is refused for every shape the leaf admits,
-- since each carries at least the layer its own inner is entered
-- through.  What the conjunct does NOT do is scale with the run.  It
-- reads the TERM, the term is charged for its step function once, and a
-- fold applies that step once per delivery — so the rank is pinned to
-- the syntax while the values the run produces are pinned to the
-- deliveries, and a source one literal longer is already one deeper
-- than the syntax knows about.
--
-- THE WITNESS IS A FOLD UNDER A FLATTENER, AND IT IS PITCHED PAST THE
-- TWO REPAIRS A TIGHTER ONE WOULD INVITE.  A scan whose step re-wraps
-- its accumulator in one `*All` layer emits values reading one, then
-- two, then three; a `mergeAllᵉ` over it subscribes each, which is the
-- hop the rank peels at.  The program reads TWO and the triple is
-- entered at THREE, so the conjunct holds with a peel to spare and the
-- crossing is not an off-by-one — entering at the term's own reading is
-- the tighter witness and the weaker finding, since a `suc` in the
-- conjunct would answer it.  The source is a literal list, so every
-- delivery lands inside ONE subscribe cascade: no arrival is drained,
-- and the store reads ZERO at the entry the statement is made at.  That
-- is the second repair killed — a conjunct reading the state HANDED IN
-- cannot pay for growth that happens after it is read.
--
-- WHAT IT KILLS AND WHAT IT LEAVES.  It kills deriving the leaf from an
-- invariant whose rank conjunct reads a MEASURE OF SYNTAX, for every
-- such measure and not merely for this one: the counterexample scales by
-- lengthening the source, which moves the deliveries and leaves the term
-- fixed.  The top-line claim is untouched, because a run enters at
-- `rootTri`, whose rank is exponential in the very literals that produce
-- the deliveries.  So the repair is not a fourth conjunct of the same
-- kind but a conjunct denominated in the SEED: what the invariant must
-- carry down is that the rank still dominates what the run can deliver,
-- and the μ clause is the edge that decides which form of it can be
-- re-established, since unfolding grows the size while the witness keeps
-- its rank.  The one measure that survives BOTH edges is already the
-- third component — a burst's deliveries are its synchronous size, and
-- that is the quantity the μ guard re-seeds and compares.
--
-- THE MEASURE AND THE INVARIANT ARE BOTH IMPORTED, for the reason the
-- sibling witness states: the claim is about the form `src` carries
-- today, so a local copy would go on refuting a shape that has been
-- repaired.  A fourth conjunct makes the reading below fail to
-- typecheck, which is the loud failure this trades the local copy for.
module Refuted.Rank-Fold where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; nat̂; strmᵗ; varᵗ;
  fstᵗ; ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Stream; Path; Sched; EvalSt; subscribeE; root;
  sched-init; st-init; hasDry)
open import Rx.Nest-Depth using (nestDᵉ)
open import Verify-Rank-Sufficient.Dry using (opShape)
open import Verify-Rank-Sufficient.Entry using (EntryReads)

----------------------------------------------------------------------
-- THE STATEMENT, at the form the operator leaf carries today.  It is
-- the live `EntryReads` and the live `opShape`, so a repair to either
-- lands here as a type error rather than as a witness that quietly goes
-- on agreeing.
----------------------------------------------------------------------

DryOperator : Set
DryOperator = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
  (ac : Acc _≺_ τ) (o : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) → opShape o ≡ true →
  EntryReads τ o (Sched.slots sched) (EvalSt.connectedShares st) →
  hasDry (proj₁ (subscribeE ac o κ id now sched st)) ≡ false

----------------------------------------------------------------------
-- THE PROGRAM.  The step hands its own accumulator back inside one
-- flattening layer, which is the shape that grows a reading ALONG a
-- run; the source is three literals, which is the shortest source that
-- outruns a rank seeded one above the term's own reading, and lengthening
-- it outruns any fixed offset.  The flattener at the root is what
-- turns the grown accumulator into a SUBJECT, since a value the store
-- merely holds is never entered and never peels anything.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

fold : Closed Γ₀ (obs natᵗ)
fold = scanᵉ step (strmᵗ emptyᵉ) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

prog : Closed Γ₀ natᵗ
prog = mergeAllᵉ nothing fold

opShape-prog : opShape prog ≡ true
opShape-prog = refl

----------------------------------------------------------------------
-- THE ENTRY, ONE PEEL ABOVE THE INVARIANT'S TIGHTEST.  The rank is the
-- program's reading PLUS ONE, so the conjunct holds with slack and the
-- crossing cannot be read as an off-by-one; the unconnected count is
-- zero over the empty context and the syncSize holds by reflexivity.
----------------------------------------------------------------------

_ : nestDᵉ prog ≡ 2
_ = refl

τ₀ : Tri
τ₀ = 0 , 3 , syncSizeᵉ prog

ac₀ : Acc _≺_ τ₀
ac₀ = ≺-wellFounded τ₀

reads₀ : EntryReads τ₀ prog (Sched.slots (sched-init prog ins₀))
                            (EvalSt.connectedShares (st-init prog))
reads₀ = z≤n , s≤s (s≤s z≤n) , ≤-refl

burst₀ : Stream Γ₀ natᵗ
burst₀ = proj₁ (subscribeE ac₀ prog root 0 0 (sched-init prog ins₀) (st-init prog))

----------------------------------------------------------------------
-- THE CROSSING.  Pinned by `refl` outside the ⊥ so that it moves
-- visibly if either side does — the third accumulator reads three, one
-- more than the peels left, and the dry close is what comes back.
----------------------------------------------------------------------

dry₀ : hasDry burst₀ ≡ true
dry₀ = refl

dry-operator-fold-false : DryOperator → ⊥
dry-operator-fold-false h
  with trans (sym (h ac₀ prog root 0 0 (sched-init prog ins₀) (st-init prog)
                     opShape-prog reads₀))
             dry₀
... | ()
