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
-- IT IS A TRIPLE OF INEQUALITIES AND NOT OF EQUATIONS, and the
-- components are loose for DIFFERENT reasons.  The sync component
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
-- THE RANK COMPONENT IS THE OBSERVABLE NESTING, AND IT IS A FACT ABOUT
-- THE TERM RATHER THAN ABOUT THE RUN.  The evaluator enters at
-- `obsDepthᵉ` of what it is about to subscribe, so the conjunct says a
-- SUBTERM is written no deeper than the term the entry was seeded from
-- — and `subscribeE` descends carrying the witness unchanged, so every
-- descent is one projection of a join.  Nothing is pre-paid, which is
-- what makes the seed adequate by construction: a figure dominating a
-- TERM is satisfied by its subterms, while a figure dominating a RUN
-- had to be guessed and was refuted.
--
-- WHAT MAKES THIS THE CONJUNCT AND NOT A SIZE.  An emitted inner is a
-- runtime value, so no SUBTERM relation reaches it — but a `Val` at
-- `obs` IS a closed expression, so a measure does, and the one that
-- survives is the one that does not grow under μ-unfolding.  A bound
-- on the syntax's size fails there outright: `unfoldμ body` is larger
-- than `μᵉ body` while the witness keeps its rank.  `obsDepthᵉ` reads
-- a guarded occurrence as zero and reads `μᵉ` through, so unfolding
-- leaves it EQUAL — and that equation is PROVEN rather than assumed,
-- since the syntax admits no unguarded self-reference under a written
-- observable.
--
-- AND THE READING IS NO LONGER A COMPONENT OF THE TRIPLE AT ALL, which
-- is the change this module carries.  The rank used to order the
-- recursion AND bound what the walk may read; the second job cannot be
-- done by syntax, since a reading prices what a subtree will EMIT and a
-- fold multiplies that once per delivery.  So the carried face takes a
-- bound of its own, quantified where the walk is stated and constrained
-- by nothing the machine chooses.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE DROP IS DEFINITIONAL ONLY DOWNWARD, AND THE ROUTE OUT OF THIS
-- CONJUNCT ON THE OTHER SIDE IS THE STRENGTHENED RETURN TYPE — which
-- is OPEN.  The burst walk carries its emissions' hop content beside
-- them, invariant in the motive, so the hop edge spends that report
-- rather than a fact about an arbitrary inner.  A frame's own emissions
-- are not subterms of the term it entered on — a fold builds its
-- accumulator at RUN time, one fresh layer per refold — so the conjunct
-- holding where `subscribeE` descends never implied it where a frame
-- hands a value OUT; the two directions are separate questions and this
-- is the statement that answers the second.
--
-- WHAT MAKES IT PAYABLE IS THAT THE ITERATING CLAUSE TRACKS THE REFOLD
-- AND THE OLD SLOPE DID NOT.  Under a reading blind to source length the
-- carried depth climbed one per literal against a flat bound, so a
-- longer source crossed any bound and the report was refuted outright —
-- and refuted at exactly the pairs the dry marker crossed at, which said
-- the report and the guard were one statement rather than two.  They
-- still are, and that is now the half in its favour: the environment
-- reading prices the refold by ITERATING over it, so on the doubling
-- fold family that killed the route the two sides agree EXACTLY at every
-- source length measured — one, two, three and four literals, term
-- reading and carried reading equal at each.  A route re-opened on a
-- tight instantiation rather than on a slack one, so no margin is doing
-- the work.
--
-- DEAD ROUTE: the SYNTACTIC NESTING as the conjunct, which is what
--   this component read while the rank was a seed.  It cannot be
--   restated onto the depth reading and it cannot be kept beside it: a
--   `deferᵉ` body reads ZERO in hop — that cut is what makes the
--   measure survive unfolding — while its nesting is positive, so the
--   two orders disagree on the one constructor the recursion goes
--   through.  Whatever the nesting was buying has to be bought from
--   the reading or not at all.
-- DEAD ROUTE: ANY conjunct charging a step function ONCE, which is
--   what every unparameterised measure of syntax does.  A `scanᵉ`
--   applies its step once per delivery, so one three-line program run
--   against three literals and against thirty has one reading and two
--   depths — the crossing scales with the source and no clause of a
--   syntax-only measure repairs it.  What survives is a clause that
--   ITERATES, and the count it iterates over is read off the source's
--   own delivery component rather than taken as a parameter.  The
--   witness was a scan whose step re-wraps its accumulator in one merge
--   layer: read in NESTING, the program comes back 1 and its burst 3.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Entry where

open import Data.List using (List; [])
open import Data.Nat using (_≤_; _⊔′_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m⊔n; m≤n⊔m; ⊔≡⊔′)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; _×ᵗ_; syncSizeᵉ; mapᵉ; takeᵉ; scanᵉ; natᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ)
open import Rx.Evaluator using (unconn; rootTri)

-- the triple the machine stands at READS the term it is about to
-- subscribe: the unconnected count bounds the first component, the
-- observable nesting the second, the sync size the third
EntryReads : ∀ {n} {Γ : Ctx n} {u} →
             Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads (U , R , s) o sl cs =
  unconn sl cs ≤ U × obsDepthᵉ o ≤ R × syncSizeᵉ o ≤ s

-- the root contributes nothing, since nothing has been stored yet and
-- no value has been delivered: the entry is the program's own nesting
-- joined with zero, so all three conjuncts are reflexivity up to that
-- unit.  Adequacy of a SEED used to be argued here and is not argued
-- anywhere now — there is no seed, so there is nothing to be adequate.
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads (rootTri e ins) e ins []
rootTri-reads e ins = ≤-refl , m≤m⊔n (obsDepthᵉ e) 0 , ≤-refl

-- WHAT A DESCENT INTO A SUBTERM COSTS, AND UNDER THIS MEASURE IT IS
-- NOTHING ANYWHERE.  Every clause is a join over its children, so a
-- subterm reads under its term by one projection of that join and no
-- conjunct has to be re-established.  The three flatteners and the two
-- binders are DEFINITIONAL — a `*All` reads exactly its source here,
-- which is the change: the `suc` that used to sit on the flattener now
-- sits at `strmᵗ`, where an observable is actually written.
--
-- AND THAT IS WHY THE ENTRY SIDE STOPPED BEING THE EXPENSIVE HALF.  A
-- `suc` on the flattener meant every descent through one had to be paid
-- for out of the component, so the seed had to dominate a run; a `suc`
-- at the written head means the descent is free and the payment happens
-- once, at the hop, against the term that delivered the inner.
hop-mapᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t}
  (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s) →
  obsDepthᵉ b ≤ obsDepthᵉ (mapᵉ f b)
hop-mapᵉ f b = m≤n⊔m _ _

hop-takeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
  (c : Tm Γ Δᵍ Δ Θ natᵗ) (b : Exp Γ Δᵍ Δ Θ t) →
  obsDepthᵉ b ≤ obsDepthᵉ (takeᵉ c b)
hop-takeᵉ c b = m≤n⊔m _ _

hop-scanᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t}
  (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s) →
  obsDepthᵉ b ≤ obsDepthᵉ (scanᵉ f z b)
hop-scanᵉ f z b = m≤n⊔m _ _

------------------------------------------------------------------
-- THE SAME DESCENT IN THE READING, WHICH IS NOW A SEPARATE QUANTITY
-- AND NOT A COMPONENT OF THE TRIPLE.  The rank used to do two jobs —
-- order the recursion and bound what the walk is allowed to read — and
-- the two came apart the moment the rank became syntactic: a reading
-- prices what a subtree will EMIT and no syntactic figure dominates
-- that.  So the carried face takes a bound of its own, quantified
-- where the walk is stated, and these are what re-establish it at a
-- subterm.  Splitting them is what makes each side provable: the rank
-- conjunct is now definitional at every flattener, and the reading
-- conjunct is charged only where the reading actually grows.
--
-- THE JOIN'S RIGHT UNIT, in the strict-comparison spelling the
-- reading's step clauses are written in.  The stdlib proves this of
-- `_⊔_` and proves the two operators equal; nothing states it of the
-- primed one directly.
⊔′-right : ∀ m n → n ≤ m ⊔′ n
⊔′-right m n = ≤-trans (m≤n⊔m m n) (≤-reflexive (⊔≡⊔′ m n))

-- a `takeᵉ` needs no entry here, since its clause IS its subterm's
-- reading, and the three flatteners need none either, since each reads
-- `suc` of it
read-mapᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃)
  (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s) →
  depthᵉ ψ b ≤ depthᵉ ψ (mapᵉ f b)
read-mapᵉ ψ f b = ⊔′-right _ _

read-scanᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃)
  (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s) →
  depthᵉ ψ b ≤ depthᵉ ψ (scanᵉ f z b)
read-scanᵉ ψ f z b = ⊔′-right _ _
