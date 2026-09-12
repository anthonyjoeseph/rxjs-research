-- A BURST DOES NOT READ UNDER ITS EMITTER, AND A SCAN IS WHY.
--
-- The rank peels once per inner-subscribe hop, and the hop enters a
-- value the burst carried.  So re-establishing the entry invariant
-- across that peel needs an emitted inner to read STRICTLY under the
-- expression that emitted it — the one claim the nesting measure was
-- shaped to deliver, and the reason its list clause takes a max rather
-- than a sum.  The max is not enough, because a list is not where the
-- growth is.
--
-- A `scanᵉ` THREADS ITS OWN OUTPUT BACK IN.  A step function that
-- wraps its accumulator in one `*All` layer emits a value one layer
-- deeper than the value before it, so the k-th delivery of a
-- synchronous source reads k.  The measure charges the step function
-- ONCE, because it is a measure of syntax and the fold count is not in
-- the syntax: one three-line program run against a source of three
-- deliveries and against a source of thirty has one reading and two
-- depths.  No clause repairs that — a term cannot be asked for a count
-- that has not happened yet — so the finding is not that the scan
-- clause is mis-weighted but that NO measure of the emitter bounds the
-- burst.
--
-- WHAT THIS KILLS IS THE ROUTE, NOT THE INVARIANT.  The rank conjunct
-- is true at the root, where the entry reads the program itself; it
-- survives a connect, which re-reads the connected expression, and the
-- μ peel, which is an equality of readings.  The inner hop is the one
-- edge whose subject is a RUNTIME value rather than a subterm, and this
-- witness says that edge has no re-establishment reading syntax against
-- syntax — not at this measure and not at any measure charging a step
-- function once.  What pays for it has to price the FOLD COUNT, which
-- is a property of the store rather than of the term.
--
-- THE MEASURE IS IMPORTED RATHER THAN LOCALISED, DELIBERATELY.  A
-- refutation normally restates the currency it refutes, so that a
-- repair enlarging the measure cannot quietly turn the crossing into an
-- equality.  Here the measure IS the subject: the claim is that the
-- nesting measure `src` defines does not bound a burst, and a local
-- copy would go on being evidence about a measure `src` no longer has.
-- The loud failure that localising buys is bought instead by the two
-- figures below, both pinned by `refl` and both spent in the ⊥ — move
-- either side and this file goes red naming the number.
module Refuted.Burst-Nesting where

open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _≤_; _⊔_; s≤s)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick; InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt;
  subscribeE; sched-init; st-init; rootWitness)
open import Rx.Nest-Depth using (nestDᵉ)

----------------------------------------------------------------------
-- HOW DEEP A BURST READS.  A burst of observables carries closed
-- expressions, so the measure applies to its payloads unchanged; two
-- payloads abreast cost what the deeper costs, matching the list clause
-- the measure itself uses, so the reading below is the friendliest one
-- available to the statement being refuted.
----------------------------------------------------------------------

evNest : ∀ {n} {Γ : Ctx n} {u} → List (InstEvent (Closed Γ u)) → ℕ
evNest []             = 0
evNest (value v ∷ es) = nestDᵉ v ⊔ evNest es
evNest (_ ∷ es)       = evNest es

burstNest : ∀ {n} {Γ : Ctx n} {u} → Stream Γ (obs u) → ℕ
burstNest []         = 0
burstNest (em ∷ ems) = evNest (InstEmit.events em) ⊔ burstNest ems

----------------------------------------------------------------------
-- THE STATEMENT, IN ITS WEAKEST FORM.  The peel needs the inner to read
-- STRICTLY under its emitter; what is refuted here is the non-strict
-- comparison, which is weaker and so kills the strict one with it.  The
-- accessibility witness and the triple are quantified over because the
-- walk holds arbitrary ones, and the witness below picks the root's —
-- so this is refuted at a run the evaluator actually performs, not at a
-- triple chosen to break it.
----------------------------------------------------------------------

BurstUnderEmitter : Set
BurstUnderEmitter = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ : Tri}
  (ac : Acc _≺_ τ) (o : Closed Γ (obs u)) (κ : Path Γ (obs u) t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  burstNest (proj₁ (subscribeE ac o κ id now sched st)) ≤ nestDᵉ o

----------------------------------------------------------------------
-- THE WITNESS.  The accumulator starts at the empty observable and the
-- step hands it back inside one merge layer, so the deliveries read
-- one, two, three while the program reads one — the step function's
-- single layer, charged once.
----------------------------------------------------------------------

-- THE STORE BOUND the run below is taken at.  `evaluate` builds its
-- schedule at the fuel it then hands the drain, so a witness is about a
-- RUN only when the two agree — and the bound is what the root enters
-- at, so choosing it small would truncate the very cascade this file
-- measures.  Chosen generously for that reason, not tightly.
SB : ℕ
SB = 30

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

prog : Closed Γ₀ (obs natᵗ)
prog = scanᵉ step (strmᵗ emptyᵉ) (ofᵉ (nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ []))

burst₀ : Stream Γ₀ (obs natᵗ)
burst₀ = proj₁ (subscribeE (rootWitness SB prog ins₀) prog root 0 0
                  (sched-init SB prog ins₀) (st-init prog))

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl` AND SPENT IN THE ⊥.  Three against
-- one, and the gap grows with the source: a fourth delivery reads four
-- against the same program.
----------------------------------------------------------------------

nest-prog : nestDᵉ prog ≡ 1
nest-prog = refl

nest-burst : burstNest burst₀ ≡ 3
nest-burst = refl

burst-under-emitter-false : BurstUnderEmitter → ⊥
burst-under-emitter-false h =
  cross nest-burst nest-prog
        (h (rootWitness SB prog ins₀) prog root 0 0
           (sched-init SB prog ins₀) (st-init prog))
  where
    cross : ∀ {a b} → a ≡ 3 → b ≡ 1 → a ≤ b → ⊥
    cross refl refl (s≤s ())
