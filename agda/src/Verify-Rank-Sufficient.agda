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
open import Data.Fin using (Fin)
open import Data.Nat using (ℕ)
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
open import Verify-Rank-Sufficient.Hop using (hopFits)

-- THE THREE PEELS ARE NOT THREE GRINDS OF ONE SIZE, AND THE ASYMMETRY IS
-- THE SCHEDULE OF THIS TIER.  Two of them are one line over a fact about
-- SYNTAX, and the evaluator's own guard is the statement: the μ peel wants
-- the unfolded body's syncSize under the size it entered at, which is the
-- order's μ constructor applied to an unfold equation; the connect peel
-- wants the unconnected count to drop when a fresh share joins the
-- connected list, which is the order's connect constructor applied to an
-- insertion lemma, under a freshness premise the machine establishes for
-- itself before the clause fires.  The RANK peel's own ≺-witness is the
-- hop constructor handed its own hypothesis and so says NOTHING — every
-- gram of that reading is establishing the hypothesis.  That prediction is
-- now confirmed rather than argued: the two cheap peels landed as the
-- walk's own arms, and what is left open is exactly the third.

-- NOTHING HERE IS CIRCULAR, which was the standing doubt against replacing
-- a counter with an order.  Of the three peels only the rank one asks what
-- a RUN did.  The μ peel reads its own body, an equation on syntax; the
-- connect peel reads the slot telescope, which is unchanged across a run,
-- so its premise is an equation too rather than an invariant something has
-- to preserve.  Neither settled peel needed the descent to have gone well
-- in order to say that its own edge drops.  What both needed is the entry
-- invariant — that the triple the evaluator stands at reads the term it is
-- about to subscribe — and that is why the invariant was the thing to
-- state first and the peels were its cheap arms.

-- THE RANK READING'S SHAPE IS A STRENGTHENING RATHER THAN A FOURTH
-- MEASURE, and that is the plan for the one leaf still open.  The inner is
-- a runtime VALUE — an observable a sibling call emitted — structurally
-- unrelated to the term the caller was subscribing, so no equation on
-- syntax reaches it.  What does reach it is where it came FROM: it rode a
-- burst some subscribe produced, so its nesting can travel as a
-- strengthened RETURN TYPE on the burst-producing functions, invariant in
-- the motive, rather than as a measure nobody has.  Ordinary induction,
-- and the thing to get right is the strengthening and not arithmetic.
--
-- AND THE SEED IS EXPONENTIAL WHILE THE PEEL IS ONE PER HOP, so what is
-- owed is that the count is never SPENT rather than any comparison of two
-- quantities.  An entry is `2 ^ (sizeᵉ e + slotsSize sl + m)`, where `m` is
-- zero at the root and the arriving value's nesting joined with the store's
-- at every arrival after it — so one nesting layer costs one doubling, and
-- a route is dead exactly when a single entry has to pay for growth it
-- cannot see.  `Refuted.Sync-Count` is where the last additive candidate
-- for that currency died.

-- TWO CORRECTIONS AGAINST THE GENERATION THIS ARGUMENT WAS RECOVERED FROM,
-- because its apparatus is the obvious thing to reach for and neither half
-- transports.  The FLATTENING does not: a fold of the triple into one ℕ
-- existed so that a counter could dominate the order structurally, and this
-- evaluator descends on the order ITSELF, so the fold and every cap feeding
-- it are apparatus for a machine that is gone.  And the CURRENCY moved —
-- the generation before this one carried a hop DEPTH under its own cap,
-- which answers a different question from a rank that peels one per hop.
-- Its rows are a lead to read, never a statement to cite.

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
-- NOT A GENERALITY.  Both are universally quantified here and nothing in
-- the hypotheses relates either to `e`.  The STORE half of that costs
-- nothing now: the cascade re-seeds per ARRIVAL rather than off the root,
-- and `arrivalWitness` enters at the value's nesting joined with
-- `stNest`, so a registry no run could have built is bounded by the same
-- expression as one a run produced, and the arbitrary store is a
-- generality after all.  What no seed reads is what happens AFTER it is
-- minted: one arrival's chain fold can deliver many times, a fold
-- deepens its accumulator by the step's own reading per delivery, and the
-- entry was taken once.  Whether that ever reaches the dry close is the
-- question the operator leaf answers YES to from the other side, and it
-- is the one this row could not put until a cascade had been
-- instantiated rather than argued about.

-- AND THE CASCADE DOES NOT OUTGROW ITS ENTRY, WHICH IS WHY THIS ROW IS
-- NOT THE OPERATOR ROW UNDER ANOTHER NAME.  A cascade is ONE INSTANT,
-- and both axes a term does not read are tick-gated: an arrival is a
-- tick by construction, and a recursion re-enters only through
-- `deferᵉ`, whose body is pending at `suc now`.  So what a single entry
-- has to cover is the deliveries a term can produce SYNCHRONOUSLY — and
-- a fold's reading gains one layer per delivery while the seed doubles
-- per symbol of the term producing them.  Linear against exponential in
-- the one parameter that moves both, which is the same shape the
-- arrival rows found ACROSS entries; so the denomination the paragraph
-- above asks for is the seed the machine already mints, and what is
-- left in this row is the unconstrained schedule alone.
--
-- AND WHAT LICENCES THE HYPOTHESIS IS THAT THE UNCONDITIONAL FORM IS
-- FALSE, WHICH IS THE ONLY THING THAT DOES.  Adding one otherwise
-- trades tracked debt for untracked debt, so a statement that might
-- still hold outright may not acquire one — and the two witnesses below
-- close that off, the second of them against the obvious weaker repair.
-- `hopFits` is the quantity they say is absent:
-- a chain's own remaining-hop content, read off the very frames the
-- witness exploits, against the rank the entry seeds.  It is quantified
-- over every V and η, so the statement is false if the fit at the naive
-- reading does not already carry the run — which makes this refutable
-- at a concrete registry rather than merely unproven.
--
-- REFUTED: `Refuted.Drain-Reachable` — the form as written, at a store
--   whose root term is the EMPTY observable.  A chain is a `Path` typed
--   by the context and the root type alone, so it carries no index
--   tying it to the program; a `map-f` frame applies whatever function
--   the registry's author wrote, and `foldPath` threads ONE witness
--   through every frame without re-seeding at any of them.  A plain
--   numeral arrives at nesting zero, a store whose only node holds an
--   empty queue adds zero, and the frame hands back a tower the
--   `thru-outer` behind it then subscribes.  The gap is not a rate: it
--   is unbounded at every seed, since the tower is written one level
--   deeper at no cost to any quantity the entry reads.
-- REFUTED: `Refuted.Drain-Reachable` — and the same witness kills the
--   form CONDITIONED on the coherence record, which is what says the
--   repair is not a hypothesis.  Every field is satisfied at that
--   state: the counts agree, the element types gate the one entry in,
--   the protocol sits at its initial watermark with no open instant,
--   the merge node's counter matches a chain contributing no inner
--   instance, and an empty context has no hot slot to keep live.  The
--   record constrains the registry's COUNTS and TYPES, while the depth
--   is a property of a chain's FRAMES — so what is missing is a tie
--   between a registration's frames and the program being run, which
--   has no home in the record as it stands.
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
-- PROBED: `Probed.Seed` — one row past the subscribe frame, at a scan
--   re-wrapping its accumulator over a scripted source with an async
--   tail.  The burst carries a reading of one and the DRAIN carries
--   three, against a seed of `2 ^ 14` that the slot's own data is counted
--   into — the half a literal source cannot show, since it delivers
--   entirely inside the frame.  THE BOUNDARY: one slot, one fold, and a
--   state reached by RUNNING, so the arbitrary schedule and store this
--   statement quantifies over are as uninstantiated as they were.
-- PROBED: `Probed.Fuel-Growth` — six drains of ONE run, differing in
--   FUEL alone, at a fold whose source is a recursion, so how many
--   arrivals happen is the drain's business and not the term's.  Both
--   readings of the term hold still across the six while the carried
--   nesting is the fuel plus one: the rate is ONE per arrival, exactly,
--   and it is the quantity an arrival's own entry reads.  THE BOUNDARY:
--   one delivery lands per arrival, so every layer the rows count is
--   paid for by a fresh entry and none of them reaches a burst
--   delivering many times inside one cascade.
-- PROBED: `Probed.Cascade-Growth` — that last region, instantiated.  An
--   empty synchronous slot part and one late value put the entire run
--   under a SINGLE arrival; the value is mapped to a literal observable
--   and flattened, so one entry buys the inner's whole length.  Three
--   layers at one unit of fuel and still three at two — so the layers
--   are one cascade's and not a queue drained one arrival per unit —
--   then six under one entry as the source gains three literals, while
--   the seed moves from `2 ^ 20` to `2 ^ 23`.  THE BOUNDARY: the inner
--   is a literal and the flattener a merge, so no row reaches a cascade
--   whose inner is itself a recursion — which the gate above says
--   cannot lengthen one, and which nothing here instantiates.
-- PROBED: `Probed.Fit-Preserved` — the fit at states the DRAIN produced,
--   which every receipt above is silent about.  `stepOnce` is the loop's
--   own step with the emit stream dropped — the same pull, the same
--   cascade, the same instant counter — so a row reads the pair the
--   recursion would have been handed rather than one written by hand.
--   Nine rows over three recursive programs at one, two and three
--   arrivals, each spending the decision procedure on the comparison, so
--   a fit the k-th arrival destroyed leaves its row unsolvable instead of
--   letting it through.  The finding is stronger than preservation: the
--   left side does not MOVE — two across the plain recursion, three
--   across both nested ones, against rank exponents of eleven, nineteen
--   and twenty-eight — while the registration counter climbs at every
--   step on every program, which is what separates a flat reading from a
--   stepper that had become a fixed point.  THE BOUNDARY: three arrivals,
--   the naive reading, a merge only, and nothing here reaches the
--   late-slot cascade the receipt above instantiates.

postulate
  drain-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (nextId : Id) (V : ℕ) (η : Fin n → ℕ)
    (sched : Sched Γ) (st : EvalSt e) →
    hopFits V η sched st →
    hasDry (drain fuel nextId sched st) ≡ false

-- THE FIT AT THE DOOR.  `evaluate` hands the drain the state its root
-- subscribe left, so this is the one arrival-free instance the
-- assembly needs, and it is a leaf rather than a hypothesis because
-- nothing above it is free to choose the state.  It takes no fuel: the
-- entry state is what the subscribe frame produced, and the drain has
-- not run yet.
--
-- PROBED: `Probed.Descent` — the root entry of three recursive
--   programs, each a `refl`-free row whose witness is the decision
--   procedure on the comparison itself, so a premise FALSE at the
--   point would leave the row's implicit unsolvable rather than let it
--   pass.  The three are plain recursion, μ nested directly in μ, and a
--   share holding a recursion referenced from inside a second one —
--   which is the shape whose nesting the rank guard cannot read off the
--   term it compares, and so the one a fit read off the term alone
--   would be expected to miss.  THE BOUNDARY: entry states only, at the
--   naive reading `V = 0` and `η` constantly zero; nothing here reaches
--   a state the drain itself produced, and nothing instantiates a
--   nonzero slot reading.
postulate
  entry-hop-fits : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
    (ins : Slots Γ) →
    let ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
                (st-init e)
    in hopFits 0 (λ _ → 0) (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))

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
    (drain-dry-free fuel 1 0 (λ _ → 0) (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))
      (entry-hop-fits e ins))
  where
  ent : Stream Γ t × Sched Γ × EvalSt e
  ent = subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)
