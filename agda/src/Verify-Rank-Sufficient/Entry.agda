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
-- THE RANK COMPONENT IS THE HOP READING, AND IT IS THE SAME QUANTITY
-- ON BOTH SIDES.  The evaluator now enters at `hopDᵉ` of the term it
-- is about to subscribe, so the conjunct says the walk's own reading
-- of a SUBTERM sits under the reading the entry was seeded from — and
-- `subscribeE` descends into subterms carrying the witness unchanged,
-- which is exactly where the slack is spent.  A `*All` node reads
-- `suc` of its source, so the hop edge's drop is definitional rather
-- than an obligation between a run and a budget.
--
-- WHAT MAKES THIS THE CONJUNCT AND NOT A SIZE.  An emitted inner is a
-- runtime value, so no SUBTERM relation reaches it — but a `Val` at
-- `obs` IS a closed expression, so a measure does, and the one that
-- survives is the one that does not grow under μ-unfolding.  A bound
-- on the syntax's size fails there outright: `unfoldμ body` is larger
-- than `μᵉ body` while the witness keeps its rank.  `hopDᵉ` cuts at the
-- `deferᵉ` gate and reads `μᵉ` through, so unfolding leaves it EQUAL.
--
-- AND THE DROP IS DEFINITIONAL ONLY DOWNWARD, WHICH IS EXACTLY WHERE
-- THE ROUTE OUT OF THIS CONJUNCT WAS GOING TO GO.  A frame's own
-- emissions are not subterms of the term it entered on: a fold builds
-- its accumulator at RUN time, one fresh layer per refold, while the
-- clause reading that fold is charged nothing for what it folds over.
-- So the conjunct holds where `subscribeE` descends and fails where a
-- frame hands a value OUT, and the two directions are not one fact.
--
-- REFUTED: `Refuted.Root-Refold` — the strengthened return type, which
--   would have had the burst walk carry its emissions' hop content
--   beside them, invariant in the motive, so the hop edge could spend
--   that report rather than a fact about an arbitrary inner.  The
--   carried reading climbs one per source literal while the reading the
--   frame was entered at is blind to source length, so the two cross
--   and a longer source crosses any bound.  They cross at exactly the
--   pairs the dry marker crosses at, which is the half that decides
--   it: the report is not a weaker obligation payable while the
--   seeding is repaired alongside it, it is the same statement.
--
-- DEAD ROUTE: the SYNTACTIC NESTING as the conjunct, which is what
--   this component read while the rank was a seed.  It cannot be
--   restated onto the hop reading and it cannot be kept beside it: a
--   `deferᵉ` body reads ZERO in hop — that cut is what makes the
--   measure survive unfolding — while its nesting is positive, so the
--   two orders disagree on the one constructor the recursion goes
--   through.  Whatever the nesting was buying has to be bought from
--   the reading or not at all.
-- DEAD ROUTE: ANY conjunct charging a step function ONCE, which is
--   what every unparameterised measure of syntax does.  A `scanᵉ`
--   applies its step once per delivery, so one three-line program run
--   against three literals and against thirty has one reading and two
--   depths — the crossing scales with the source and no clause repairs
--   it, since a term cannot be asked for a count that has not happened
--   yet.  What survives is a rate that MULTIPLIES per fold, and the
--   fold count is a property of the STORE, which is the whole reason
--   this conjunct is V-parameterised rather than a measure of `o`
--   alone.  The witness was a scan whose step re-wraps its accumulator
--   in one merge layer: read in NESTING, the program comes back 1 and
--   its burst 3.  It is not restatable in the live currency — at a
--   store bound large enough to run anything the scan clause's own
--   power makes the hop-currency form true — so what it killed was the
--   unparameterised reading and it went with that measure.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Entry where

open import Data.List using (List; [])
open import Data.Nat using (ℕ; _+_; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; m≤m+n;
  m≤n+m; m≤n⊔m; ⊔≡⊔′; m^n>0; *-mono-≤; *-identityˡ)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (sym)

open import Rx.Prim using (Source)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; _×ᵗ_; syncSizeᵉ; mapᵉ; scanᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri)
open import Rx.Hop-Depth using (hopDᵉ; pmᵗ)
open import Rx.Slot-Hop using (slotHop)
open import Rx.Evaluator using (unconn; rootTri)

-- the environment every reading in this face is taken at.  It is the
-- schedule's telescope read at the run's own store bound, and it is
-- named because a caller free to choose it can choose the constant
-- zero — a reading `Rx.Slot-Hop` records as false rather than coarse.
slotsη : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → Fin n → ℕ
slotsη V sl = slotHop V sl

-- the triple the machine stands at READS the term it is about to
-- subscribe: the unconnected count bounds the first component, the
-- hop reading the second, the sync size the third
EntryReads : ∀ {n} {Γ : Ctx n} {u} →
             ℕ → Tri → Closed Γ u → Slots Γ → List Source → Set
EntryReads V (U , R , s) o sl cs =
  unconn sl cs ≤ U × hopDᵉ V (slotsη V sl) o ≤ R × syncSizeᵉ o ≤ s

-- the root contributes nothing, since nothing has been stored yet and
-- no value has been delivered: the entry is the program's own reading
-- plus zero, so all three conjuncts are reflexivity up to that unit.
-- Adequacy of a SEED used to be argued here and is not argued anywhere
-- now — there is no seed, so there is nothing to be adequate.
rootTri-reads : ∀ {n} {Γ : Ctx n} {t} (V : ℕ) (e : Closed Γ t) (ins : Slots Γ) →
  EntryReads V (rootTri V e ins) e ins []
rootTri-reads V e ins = ≤-refl , m≤m+n (hopDᵉ V (slotsη V ins) e) 0 , ≤-refl

-- WHAT A DESCENT INTO A SUBTERM COSTS, at the two shapes where the
-- measure does more than pass its argument through.  Both are one fact
-- twice: the clause is AFFINE in the subterm's own reading with a
-- coefficient of at least one, so the subterm reads under the term and
-- nothing has to be spent to re-establish the conjunct.  A `takeᵉ`
-- needs no entry here, since its clause IS its subterm's reading, and
-- the three flatteners need none either, since each reads `suc` of it.
--
-- THE COEFFICIENT IS WHERE THE `⊔′ 1` AND THE BASE-TWO POWER EARN
-- THEMSELVES, and it is the one thing these two lines check.  A
-- template that DROPS its argument has slope zero, and a coefficient of
-- zero would send the subterm's reading to a product of zero — the
-- clause would stop dominating its own source.  `⊔′ 1` at a map and a
-- base of at least two at a scan are exactly what rule that out.
hop-mapᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (V : ℕ) (η : Fin n → ℕ)
  (f : Fn Γ Δᵍ Δ Θ s t) (b : Exp Γ Δᵍ Δ Θ s) →
  hopDᵉ V η b ≤ hopDᵉ V η (mapᵉ f b)
hop-mapᵉ V η f b =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityˡ (hopDᵉ V η b))))
                   (*-mono-≤ (≤-trans (m≤n⊔m (pmᵗ V 0 f) 1)
                                      (≤-reflexive (⊔≡⊔′ (pmᵗ V 0 f) 1)))
                             ≤-refl))
          (m≤n+m _ _)

hop-scanᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (V : ℕ) (η : Fin n → ℕ)
  (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (b : Exp Γ Δᵍ Δ Θ s) →
  hopDᵉ V η b ≤ hopDᵉ V η (scanᵉ f z b)
hop-scanᵉ V η f z b =
  ≤-trans (≤-trans (m≤n+m _ _) (≤-reflexive (sym (*-identityˡ _))))
          (*-mono-≤ (m^n>0 (2 + pmᵗ V 0 f) V) ≤-refl)
