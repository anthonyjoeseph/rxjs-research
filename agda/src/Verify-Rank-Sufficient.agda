------------------------------------------------------------------
-- THE EVALUATOR NEVER GETS STUCK: no run of any program emits the dry
-- marker.
--
-- `evaluate` descends on an accessibility witness, and three of its
-- clauses are guarded by a decidable comparison that can fail — the
-- share connect's unconnected count, the inner subscribe's rank, the μ
-- unfold's syncSize.  A failing guard is not an error: the clause
-- returns a `dry` emit and the run continues, so exhaustion is VISIBLE
-- in the output rather than fatal.  This says the guards never fail at
-- the triple the evaluator actually enters at, which is what makes the
-- descent discipline invisible to every statement above it.
--
-- IT IS THE WHOLE OF WHAT THE DESCENT COSTS, and stating it in one line
-- is the point.  Its type mentions no witness, no triple and no order:
-- `evaluate` seeds its own entry, so every consumer sees a total
-- function on `Fuel`, and this is the only place the seeding has to be
-- shown adequate.  A statement anywhere above that had to know which
-- triple a subterm runs at would be a statement the descent had leaked
-- into.
--
-- WHAT IS OWED IS TWO LEAVES, AND THEY SPLIT THE RUN RATHER THAN THE
-- THREE GUARDS.  A run is the root subscribe followed by the drain, and
-- the subscription walk's own dry-freedom is proven clause by clause in
-- `Verify-Rank-Sufficient.Dry` — both settled peels included, each as
-- the `no` arm of the machine's own decision, refuted out of the entry
-- invariant.  What is left is the OPERATOR SHELF, where the walk holds
-- its witness fixed and re-enters through a burst, and the DRAIN LOOP,
-- which is every arrival after the first frame.  Neither is a guard
-- reading: nothing goes dry at a `mapᵉ` node or at a schedule pop, so
-- what the two of them wait on is dry-freedom of the burst pipeline —
-- one induction over a different family, and where the rank peel is
-- spent.
--
-- THE RANDOM SWEEP REACHES THE REGION, and that is a number rather than a
-- claim.  `QuickCheck` emits `μᵉ`, `varᵉ` and `deferᵉ` with the binder
-- scopes carried as INDICES, so a synchronous self-reference is not a
-- program it can write down and be rejected for; and its recursion is
-- linear by grammar, since a body reading its own var twice respawns per
-- tick and real rxjs hangs on that program too.  Every case reads `hasDry`
-- off the run, so a failing seed is now a counterexample to one of the two
-- leaves rather than to anything stated here.  Twenty seeds at depth four
-- and five at depth five — 4500 programs, a third of them carrying a live
-- recursion — report no dry run.  IT IS MEASURED, NOT RECHECKED: a
-- compiled binary's row discharges nothing, and what it buys is the
-- coverage doubt, which was that the three peels had been reached only at
-- shapes one author chose.
------------------------------------------------------------------
module Verify-Rank-Sufficient where

open import Data.Bool using (false)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Fuel; Id)
open import Rx.Exp   using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; evaluate; drain; hasDry;
  subscribeE; rootWitness; root; sched-init; st-init)
open import Verify-Rank-Sufficient.Dry using (subscribe-dry-free)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-++)
open import Verify-Rank-Sufficient.Entry using (rootTri-reads)

-- THE DRAIN IS THE SECOND HALF OF A RUN AND THE HALF THAT RECURSES.  The
-- root subscribe returns one burst and a schedule; everything after it is
-- this loop pulling one arrival at a time and cascading it to quiescence,
-- so every unfolding past the first, every later connect, and every
-- emitted inner is reached from in here.  The loop's OWN recursion owes
-- nothing — it descends on `Fuel`, and the cascade underneath it descends
-- on the telescope position, a premise a shared slot carries in its own
-- type — so what this leaf is about is the guarded peels a cascade
-- re-enters through, and not the descent of either loop.
--
-- AND THE SCHEDULE AND THE STATE ARRIVE UNCONSTRAINED, WHICH IS A GAP AND
-- NOT A GENERALITY.  Both are universally quantified here, and the rank the
-- cascade descends on is re-seeded from the PROGRAM alone — the chain step
-- mints `rootWitness` off `e` and the schedule's slots, so the seed is
-- `2 ^ (sizeᵉ e + slotsSize sl)`.  Nothing in the hypotheses relates a
-- registry entry to `e`, so a state holding a path with more stacked `*All`
-- frames than that seed peels the inner-subscribe clause to zero and the
-- cascade emits the dry close, exactly as the operator leaf does from the
-- other side.  What the conclusion needs and no hypothesis carries is that
-- the state is one a run of `e` could have REACHED; the row is therefore
-- SHAPE, and the restatement is an invariant on `EvalSt` rather than a
-- fourth argument, since every producer must then supply it and every
-- consumer re-establish it.
--
-- PROBED: `Probed.Descent` — twelve recursive programs, every one green,
--   taken against the DRAIN of each run rather than the whole of it.  What
--   they cover, guard by guard: the μ peel at every program, since all
--   twelve are `μᵉ` and the drain is where the unfolding repeats; the
--   connect peel at the five carrying a slot, `shared` and `scripted`
--   both, one of them a diamond reaching the share twice in an instant;
--   and the RANK peel at the recursive self-reference, which is an emitted
--   inner that unfolds to its own emitter, at μ nested directly in μ, and
--   at a share holding a recursion — the shape whose nesting the guard
--   cannot read off the term it compares.  Each row pins its drain's EVENT
--   COUNT beside it, so none is `false` by an empty stream.  THE BOUNDARY:
--   one fuel, hand-written programs, μ nested two deep and no deeper.
--   These rows are `refl` pins and buy exactly the twelve shapes they
--   name, which is why the coverage past them is bought by an instrument
--   that is not a pin.

postulate
  drain-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (drain fuel nextId sched st) ≡ false

-- THE ASSEMBLY, AND THE ONLY THING IT ADDS IS THE SEEDING.  `evaluate`
-- concatenates its root burst with its drain, so dryness of the run is
-- dryness of neither half; the burst's is the subscription walk at the
-- root, entered at `rootTri`, and `rootTri-reads` is what says that
-- triple reads the program it is about to subscribe.  That reflexivity is
-- the one place the entry seeding has to be shown adequate, and it is
-- here rather than in the walk because the walk never sees it.
rank-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
rank-sufficient {Γ = Γ} {t = t} fuel e ins =
  hasDry-++ (proj₁ ent) (drain fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent)))
    (subscribe-dry-free (rootWitness e ins) e root 0 0 (sched-init e ins)
      (st-init e) (rootTri-reads e ins))
    (drain-dry-free fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent)))
  where
  ent : Stream Γ t × Sched Γ × EvalSt e
  ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)
