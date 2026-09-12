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
-- THE RANK COMPONENT IS THE DEPTH READING, AND IT IS THE SAME QUANTITY
-- ON BOTH SIDES.  The evaluator enters at `depthᵉ` of the term it is
-- about to subscribe, so the conjunct says the walk's own reading of a
-- SUBTERM sits under the reading the entry was seeded from — and
-- `subscribeE` descends into subterms carrying the witness unchanged,
-- which is exactly where the slack is spent.  A `*All` node reads
-- `suc` of its source, so the hop edge's drop is definitional rather
-- than an obligation between a run and a budget.
--
-- AND THE READING TAKES NO PARAMETER BUT THE SLOT ENVIRONMENT, which
-- is what the iterated fold clause bought.  A conjunct quantified over
-- a number the machine chooses is a conjunct whose truth depends on
-- that choice, and the choice `evaluate` made was refuted.  What is
-- read here is a function of the term and the telescope alone, so
-- there is nothing left for a seeding to get wrong.
--
-- WHAT MAKES THIS THE CONJUNCT AND NOT A SIZE.  An emitted inner is a
-- runtime value, so no SUBTERM relation reaches it — but a `Val` at
-- `obs` IS a closed expression, so a measure does, and the one that
-- survives is the one that does not grow under μ-unfolding.  A bound
-- on the syntax's size fails there outright: `unfoldμ body` is larger
-- than `μᵉ body` while the witness keeps its rank.  `depthᵉ` cuts at
-- the `deferᵉ` gate and reads `μᵉ` through, so unfolding leaves it
-- EQUAL.
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
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n;
  m≤n⊔m; ⊔≡⊔′)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; _×ᵗ_; syncSizeᵉ; mapᵉ; scanᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (unconn; rootTri)

-- the triple the machine stands at READS the term it is about to
-- subscribe: the unconnected count bounds the first component, the
-- depth reading the second, the sync size the third
EntryReads : ∀ {n} {Γ : Ctx n} {u} →
             Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads (U , R , s) o sl cs =
  unconn sl cs ≤ U × depthᵉ (slotRd sl) o ≤ R × syncSizeᵉ o ≤ s

-- the root contributes nothing, since nothing has been stored yet and
-- no value has been delivered: the entry is the program's own reading
-- plus zero, so all three conjuncts are reflexivity up to that unit.
-- Adequacy of a SEED used to be argued here and is not argued anywhere
-- now — there is no seed, so there is nothing to be adequate.
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads (rootTri e ins) e ins []
rootTri-reads e ins = ≤-refl , m≤m+n (depthᵉ (slotRd ins) e) 0 , ≤-refl

-- WHAT A DESCENT INTO A SUBTERM COSTS, at the two shapes where the
-- measure does more than pass its argument through.  Both are one fact
-- twice, and under the iterated clause both are the SAME `⊔′`: a map
-- and a scan each join their template's own depth onto the source's,
-- so the source reads under the term by the join's right unit and
-- nothing has to be spent to re-establish the conjunct.  A `takeᵉ`
-- needs no entry here, since its clause IS its subterm's reading, and
-- the three flatteners need none either, since each reads `suc` of it.
--
-- THESE USED TO BE THE PLACE A COEFFICIENT EARNED ITSELF, and they are
-- not any more, which is the visible half of what the environment
-- bought.  A closed-form clause multiplies its source's reading by a
-- slope, so a template that DROPS its argument sends that reading to
-- zero and the clause stops dominating its own source — the `⊔′ 1` and
-- the base-two power existed to rule that out.  A join has no slope to
-- go to zero, so a dropping template is priced at its own depth and
-- the source's survives underneath regardless.
-- the join's right unit, in the strict-comparison spelling the
-- reading's step clauses are written in.  The stdlib proves this of
-- `_⊔_` and proves the two operators equal; nothing states it of the
-- primed one directly, and both clauses below are exactly it.
⊔′-right : ∀ m n → n ≤ m ⊔′ n
⊔′-right m n = ≤-trans (m≤n⊔m m n) (≤-reflexive (⊔≡⊔′ m n))

hop-mapᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃)
  (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s) →
  depthᵉ ψ b ≤ depthᵉ ψ (mapᵉ f b)
hop-mapᵉ ψ f b = ⊔′-right _ _

hop-scanᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd₃)
  (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s) →
  depthᵉ ψ b ≤ depthᵉ ψ (scanᵉ f z b)
hop-scanᵉ ψ f z b = ⊔′-right _ _
