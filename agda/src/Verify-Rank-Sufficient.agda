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
-- `evaluate` builds its own entry out of the program and the telescope,
-- so every consumer sees a total function on `Fuel`, and this is the
-- only place that entry has to be shown adequate.  A statement anywhere
-- above that had to know which triple a subterm runs at would be a
-- statement the descent had leaked into.
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
open import Data.Nat using (zero; suc; z≤n)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (Fuel; Id)
open import Rx.Exp   using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Arrival; evaluate; drain;
  hasDry; cascade; sched-next; subscribeE; rootWitness; root; sched-init;
  st-init; chainsOf; cascadeLatch)
open import Rx.Inputs-Below using (below-ctx)
open import Verify-Rank-Sufficient.Dry using (subscribe-dry-free)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-++)
open import Verify-Rank-Sufficient.Entry using (rootTri-reads)
open import Verify-Rank-Sufficient.Fits using (ArrivalFits; DrainFits)
open import Verify-Rank-Sufficient.Fold-Path using (cascadeGo-dry-free)
open import Verify-Rank-Sufficient.Path-Fits using (DrainHop; drainFits)

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
-- AND THERE IS NO LONGER A SECOND QUANTITY TO COMPARE AGAINST, which is
-- what the strengthening is FOR.  The entry's rank IS the hop reading, so
-- the peel and the thing it peels are denominated alike and the whole of
-- what is owed is that an emitted inner reads under its emitter.  Every
-- route this row used to describe was an attempt to relate two currencies
-- — a counter over SYNTAX against growth a RUN produces — and each died
-- the same way, the run multiplying where the seed merely doubled.
--
-- DEAD ROUTE: a rank SEEDED off the term, in every form it was tried:
--   a power of two in the program's syntactic size plus the slot
--   telescope's, at each entry, and the additive
--   candidates before it.  A seed grows with the SYNTAX while what has
--   to be dominated is what the run DELIVERS, which a fold multiplies
--   once per delivery; and a size seed cannot survive the μ clause at
--   all, since an unfolding is larger than its redex while the witness
--   keeps its rank.  `Refuted.Sync-Count` is where the last additive
--   candidate for that currency died.
-- DEAD ROUTE: the apparatus of the generation this argument was
--   recovered from — a FOLD of the triple into one ℕ, and the caps
--   feeding it.  It existed so a counter could dominate the order
--   structurally; this evaluator descends on the order ITSELF, so there
--   is nothing for a fold to dominate.  Its rows are a lead to read,
--   never a statement to cite: the currency moved too, that generation
--   carrying a hop DEPTH under its own cap, which answers a different
--   question from a rank that peels one per hop.

-- ONE ARRIVAL'S CASCADE, UNDER THE OBLIGATIONS ITS OWN CHAINS CARRY.
-- The loop above owes nothing — it descends on `Fuel` and hands each
-- arrival the conjunct the premise already holds for it — so this is
-- where the guarded peels a cascade re-enters through are paid for, and
-- it is the only place a drain step can go dry.
--
-- THE PREMISE IS PER TEMPLATE AND NAMES NO STATE QUANTITY, WHICH IS
-- WHAT THE WITNESSES BELOW COST.  Four successive readings of a
-- registry against the program each died at the same two programs, and
-- the fourth is a sub-case of the third rather than a smaller region —
-- the sequence had stopped subdividing and started confirming.  So what
-- is asked here is not that some quantity the state holds be large
-- enough; it is that every frame the run installed satisfy the shelf's
-- own obligation at the payload that frame is handed.  `ArrivalFits` is
-- that conjunction, and nothing in it reads a registry's depth.
--
-- AND THE STEP BETWEEN TWO ARRIVALS IS ASKED OF NOBODY, WHICH IS THE
-- WHOLE OF WHY THIS SHAPE IS AVAILABLE WHERE SIX OTHERS WERE NOT.
-- Every dead reading needed a fit PRESERVED across a cascade, and each
-- died proving it.  `DrainFits` recurses on the allowance instead,
-- taking each arrival's conjunct at the very pair that arrival's
-- cascade returns, so what a cascade does to the registry is the door's
-- problem and never this leaf's.
--
-- WHAT IS LEFT UNPAID IS THE FLATTENER AND THE FAN-OUT, AND THE
-- PREMISE SAYS WHICH.  Three of the frame obligations collapse to the
-- unconditional form the shelf already proves, since a map, a scan and
-- a take read neither bound.  What survives is `thru-outer`, whose walk
-- ends in the rank peel, and `share-sink`, where a chain hands its
-- values to registrations no frame above it can see — which is why the
-- sink carries an obligation of its own rather than a trivially true
-- clause that would have made the composition false at the first
-- diamond.
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
-- DEAD ROUTE: the fit's PRESERVATION across one cascade, and it is dead
--   on both readings that were tried.  A flattener over a gate, behind a
--   second gate, over a slot whose values all arrive late: carried one
--   against a term reading of one at the door, carried TWO against the
--   same one after a single arrival.  Strip the outer gate and the
--   reading is EXACT at the same states — two against two, three against
--   three — which rules out the chain manufacturing depth and rules out
--   the arithmetic being wrong, and leaves the one clause that declines
--   to look.  One more flattener reads three against one, so the gap is
--   a rate in the program's own size rather than an off-by-one.  And the
--   WIDEST state-readable bound does not repair it: joining the store
--   and the schedule's pending bodies to the term holds at the door and
--   holds for the right reason — the pending reading is two and three
--   there, exactly the figures the registry reaches one arrival later —
--   then reads ZERO one step on, against a registry still carrying the
--   frame, because the arrival that installs the frame is the arrival
--   that consumes the pending entry predicting it.  So the quantity is
--   HISTORICAL rather than a property of any state, and no larger
--   right-hand side recovers it.
-- DEAD ROUTE: and the machine can no longer be asked, which is the
--   second finding and the reason the witness that carried the first is
--   gone rather than re-run.  Both programs are behind a gate, the
--   nesting measure cuts a gate to zero, and the guard therefore enters
--   at zero and refuses the first hop under it — so every one of those
--   states is reached only after the run has gone dry, the registry is
--   empty, and the crossings cannot be taken at all.  They are not
--   repaired; they are unreachable until the seed is, and re-running
--   them is work the seed's repair unblocks rather than work that is
--   owed now.
-- DEAD ROUTE: the third candidate, and the one with the best claim: the
--   rank an ARRIVAL enters at, which is a SUM rather than a join, so the
--   arithmetic killing the join does not touch it and it is what the
--   chain fold actually descends on.  It had room at the door on both
--   programs — three against one, four against one, because the payload
--   about to arrive reads deep — and one arrival later BOTH variable
--   summands read ZERO, the payload spent and the flattener's queue
--   empty, so the seed collapsed onto the term's own reading while the
--   registry kept the frame the arrival installed.  The deeper program
--   read three against the same one, so this gap is a rate too.
-- DEAD ROUTE: and the narrowing the route below was read as forbidding,
--   tested rather than assumed: the chains ONE arrival reaches, priced
--   against the value that arrival actually carries, which is the
--   smallest left side a drain step could justify and is strictly under
--   the one above.  It held EXACTLY at both doors — three against three,
--   four against four — and crossed one arrival later at the same two
--   states, because neither narrowing does any work there.  The filter
--   reaches ONE chain and it is the deep one; the arriving value reads
--   ZERO, so the seed is the floor.  Those two rows are the content:
--   they say the information a step has over a state is not the missing
--   information, which no reading of the registry could have shown.
-- DEAD ROUTE: BOUNDING THE REGISTRY IS THE DEAD MECHANISM, NOT ANY ONE OF
--   THE STATEMENTS ABOVE.  Four successive candidates for what holds at a
--   drain step — the term's reading, the widest state-readable join, the
--   arrival's own seed, and the step's own filtered spend — are each
--   refuted at the same two programs, and the fourth is a sub-case of the
--   third rather than a smaller region, so the sequence has stopped
--   subdividing and started confirming.  The mechanism is wrong because
--   the registry prices what a chain COULD spend given an
--   arbitrarily deep value, and no state carries what value will arrive;
--   a fold spends what the value it is HANDED makes it spend.  So a
--   fourth reading of the registry is not the repair, and the premise is
--   owed to the frame shelf that already states its obligations per
--   template, against the payload each one is given.
-- DEAD ROUTE: AND SO IS WIDENING THE PREMISE WITH WHAT THE STATE CARRIES
--   FORWARD, which is the one repair the route above leaves looking open.
--   An arrival is seeded at the term's reading PLUS the join of the value
--   it carries with the store, so a quantity the state carries forward is
--   already INSIDE the grant rather than missing from it — and at the
--   crossing both summands of that join read NOUGHT, pinned beside the
--   grant by the fourth candidate above, so the grant has collapsed onto
--   the term's own figure and there is nothing a carried quantity could
--   have covered.  What moves is the LEFT: the spend climbs one per
--   flattener while the grant holds still.
-- RECOVERY: git show 8085eed:agda/evidence/probed/Probed/ restores the
--   six probes this restatement expired.  The HARNESS is what is worth
--   having back and the verdicts are not: `stepOnce` is the drain's own
--   step with the emit stream dropped, which is how a row reaches a
--   state the loop itself produced rather than one written by hand, and
--   `cascLive` is a family every one of whose deliveries leaves a
--   registration live when the cascade ends.  Their rows priced a
--   registry at a state, and a premise quantifying over states has no
--   such row.
-- RECOVERY: git show 3b82cd5:agda/evidence/refuted/Refuted/ restores the
--   three witnesses the dead routes above were taken from — the registry
--   join, the arrival's seed, and the step's filtered spend.  They are
--   what the door's repair has to be checked against: each states its
--   currency locally, so restoring one and re-running it says whether the
--   crossing comes back or whether removing the refusing arm moved only
--   who owes the proof.  What the sha holds is the currencies, stated
--   locally by each witness.
-- RECOVERY: git show 11c6fcf:agda/evidence/probed/Probed/ restores the
--   five probes the hop guard emptied, two of them FORKS at this very
--   statement: one separating a payload reading from a state maximum
--   over three gated ladders, the other composing a chain against the
--   arrival's own figure.  Both stand between candidate MEASURES, so
--   what they separate stops being a question the moment the arrival's
--   own derivation is a premise rather than a figure — recover them for
--   the real-evaluator plumbing, which is most of what they cost, and
--   not for the separations.

-- AND THE CASCADE IS A BODY NOW, WHICH IS WHERE THE DEAD MECHANISM
-- ABOVE ENDS.  Everything the four refuted readings were trying to buy
-- is bought by the chain fold instead: the finish touches no emit, so
-- the whole of the conclusion is the chain list's, and the premise is
-- the fold's own recursion over that list.
cascade-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id) (sched : Sched Γ) (st : EvalSt e) →
  ArrivalFits nextId a sched st →
  hasDry (proj₁ (cascade a nextId sched st)) ≡ false
cascade-dry-free a nextId sched st fits =
  cascadeGo-dry-free a nextId (chainsOf a st) sched (cascadeLatch a st) fits

-- AND THE ALLOWANCE LOOP IS A BODY, WHICH IS WHAT THE PER-TEMPLATE
-- PREMISE BOUGHT.  The premise recurses on the allowance exactly as the
-- loop does, so each arrival's conjunct is handed to the leaf that
-- serves that arrival and the tail is handed to the recursive call.
-- Nothing here re-establishes anything: the step between two arrivals
-- is where every refuted reading died, and it is not stated.
drain-dry-free : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  DrainFits fuel nextId sched st →
  hasDry (drain fuel nextId sched st) ≡ false
drain-dry-free zero    nextId sched st fits = refl
drain-dry-free (suc k) nextId sched st fits with sched-next sched | fits
... | inj₁ _            | _            = refl
... | inj₂ (a , sched′) | (hd , tl) =
      hasDry-++ (proj₁ (cascade a nextId sched′ st))
        (drain k (suc nextId) (proj₁ (proj₂ (cascade a nextId sched′ st)))
          (proj₂ (proj₂ (cascade a nextId sched′ st))))
        (cascade-dry-free a nextId sched′ st hd)
        (drain-dry-free k (suc nextId)
          (proj₁ (proj₂ (cascade a nextId sched′ st)))
          (proj₂ (proj₂ (cascade a nextId sched′ st))) tl)

-- THE FIT AT THE DOOR.  `evaluate` hands the drain the state its root
-- subscribe left, so this is the one instance the assembly needs, and
-- it is a leaf rather than a hypothesis because nothing above it is
-- free to choose the state.
--
-- AND IT TAKES THE ALLOWANCE, WHICH IS WHAT A HEREDITARY PREMISE
-- COSTS.  `DrainFits` carries one conjunct per arrival the fuel serves,
-- each at the pair that arrival's cascade returns, so the door cannot
-- discharge it without walking the loop the conclusion walks.  That is
-- the obligation the refuted readings were trying to buy off with a
-- single preservation step; it has not gone away, it has moved to the
-- one place where the state is not arbitrary — the entry the machine
-- itself minted out of the program and the telescope.
--
-- AND IT IS NO LONGER A LEAF, WHICH IS WHAT THE CHAIN WALK BOUGHT.
-- The whole of the fit is now built: the allowance recursion, the
-- arrival's chain list and each chain's own certificate are bodies, so
-- what is left is a premise in a DIFFERENT CURRENCY — how many
-- flatteners a registered chain carries, against what the program
-- reads.  Dryness is not mentioned in it at all, which is the point of
-- the trade: the statement that remains is arithmetic over a count the
-- path itself computes rather than a claim about what a run emits.
--
-- PROBED: `Probed.Door-Fits` — one arrival, at a chain with no frame,
--   at chains carrying ONE, TWO and THREE flatteners over a template,
--   and at a GATE whose body is subscribed a tick out.  Every counting
--   row holds by EQUALITY, and the margin stays nil across the three
--   rungs rather than merely non-negative, so a reading that charged a
--   flattener once for a ladder against a count charging per rung
--   crosses at the third.  The gate's row is tight in all three terms
--   at once — a payload reading two, one flattener, a rank of three —
--   which is the only point where the payload half constrains
--   anything.  NOT covered: a second arrival, or the allowance beyond
--   its first step.
--
--   AND ONE SHAPE IS UNREACHABLE RATHER THAN UNCOVERED, WHICH IS THE
--   PROBE'S OWN FINDING: an arrival AT THIS POINT reaches exactly ONE
--   chain.  A fan-out over a SHARE and the same fan-out over a
--   SCRIPTED slot give byte-identical figures, both reporting one
--   chain carrying nought flatteners, so the chain recursion's cons
--   case is not a shape the door has — whatever fan-out a program
--   carries is registered on the sink and entered from there.  No
--   probe can reach that arm here, and a repair that let a second
--   chain through would move both rows at once.
postulate
  entry-drain-hop : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
    (ins : Slots Γ) →
    let ent = subscribeE {lo = n} (rootWitness e ins) e root 0 0
                (sched-init e ins) (st-init e)
    in DrainHop fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))

entry-drain-fits : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
  (ins : Slots Γ) →
  let ent = subscribeE {lo = n} (rootWitness e ins) e root 0 0
              (sched-init e ins) (st-init e)
  in DrainFits fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))
entry-drain-fits {n = n} fuel e ins =
  drainFits fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))
    (entry-drain-hop fuel e ins)
  where
  ent = subscribeE {lo = n} (rootWitness e ins) e root 0 0
          (sched-init e ins) (st-init e)

-- NOTHING BELOW THIS LINE IS THE MACHINE'S TO CHOOSE, AND THAT IS WHAT
-- THE ITERATED FOLD CLAUSE BOUGHT.  The fit at the door takes the
-- program and the telescope and no third quantity, and both drain
-- halves read their environment off the schedule, so the reading every
-- peel is stated against is a function of the program alone.  A
-- conclusion about `evaluate` is then a claim about what was written
-- rather than about a number the door happened to mint.
--
-- DEAD ROUTE: a reading whose fold clause is parameterised by a REFOLD
--   BOUND the machine seeds, which is what this statement compared
--   against while that clause exponentiated.  All `evaluate` has to
--   hand such a clause is a count of ARRIVALS, and a refold happens per
--   DELIVERY — so a cascade delivering entirely inside one subscribe
--   frame refolds once per literal of its source while consuming no
--   allowance at all, and the run emits `dried` at a source long
--   enough.  Neither repair available from outside the clause works: a
--   larger allowance moves the crossing rather than removing it, since
--   the source that crosses is lengthened for free, and no other
--   quantity the door can see counts deliveries either.  The count has
--   to come from the SOURCE's own reading, which is what an iterating
--   clause takes it from.

-- THE ASSEMBLY, AND THE ONLY THING IT ADDS IS THE SEEDING.  `evaluate`
-- concatenates its root burst with its drain, so dryness of the run is
-- dryness of neither half; the burst's is the subscription walk at the
-- root, entered at `rootTri`, and `rootTri-reads` is what says that
-- triple reads the program it is about to subscribe.  That reflexivity is
-- the one place the entry seeding has to be shown adequate, and it is
-- here rather than in the walk because the walk never sees it.
--
-- AND IT IS NOT ADEQUATE, WHICH IS WHY THIS BODY STANDS ON A LEAF THAT IS
-- FALSE RATHER THAN MERELY UNPROVEN.  The seed reads the program, the
-- guard spends it against an inner the run HANDS OUT, and substituting a
-- value of observable type into a template goes through `reify` — which
-- at that type is `strmᵗ`, so an instance is written one deeper than its
-- template while every clause of the measure joins.  The repair is not
-- available from this end: a summing map clause closes the wrapping
-- template and not the fold, whose step deepens once per DELIVERY, so
-- what a frame emits has to be priced by something the machine carries.
-- Until it is, the burst half of this concatenation is the false one.
--
-- AND THE WIDEST WITNESS SUBSTITUTES NOTHING, WHICH IS WHAT SAYS THE
-- MEASURE IS THE WRONG APPARATUS RATHER THAN A CLAUSE SHORT.  The
-- nesting cuts a gate to ZERO without reading its body, and that is
-- exactly the clause making it survive μ-unfolding — so the clause the
-- recursion edge is bought with is the clause that starves the seed.  A
-- gate's body is subscribed at an ARRIVAL, whose re-seed joins the value
-- carried with the store's reading and mentions no body still pending,
-- so nothing anywhere in the run holds that figure.  What terminates
-- here is not in doubt: all three programs run to completion in ordinary
-- rxjs, so what the witnesses below kill is this MEASURE and never the
-- totality it was introduced to witness.
--
-- DEAD ROUTE: moving the debt to a leaf — postulating the descent's
--   domain, or the accessibility itself, and deleting the three arms
--   that test a reading and emit the marker on the negative answer.  It
--   is the obvious repair once the reading is refuted, and it is dead
--   for a reason nothing about the measure shows: the root witness is
--   well-foundedness APPLIED to the triple, a real proof, and the
--   evaluator REDUCES through it.  Every probe's `refl`, the bug cache
--   and the oracle all compute through that witness, so a postulated
--   domain gets stuck at the first pattern match and takes the whole
--   evidence apparatus with it.  What is dead is the LEAF, and only the
--   leaf: a domain DEFINED beside the current evaluator computes nothing
--   and breaks nothing, and one PROVEN inhabited reduces exactly as the
--   root witness does today.  So the arms come out at the cutover and
--   not before it, and the dead route is a constraint on ORDER rather
--   than a verdict on the apparatus.
-- REFUTED: `Refuted.Dry-Wrap` — this statement, at three programs: one
--   per half of the substitution repair, and one behind a gate that
--   neither half reaches.
rank-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
rank-sufficient {n = n} {Γ = Γ} {t = t} fuel e ins =
  hasDry-++ (proj₁ ent) (drain fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent)))
    (proj₁ (subscribe-dry-free (rootWitness e ins) e (below-ctx e) root 0 0
      (sched-init e ins) (st-init e) (rootTri-reads e ins) ≤-refl z≤n))
    (drain-dry-free fuel 1 (proj₁ (proj₂ ent)) (proj₂ (proj₂ ent))
      (entry-drain-fits fuel e ins))
  where
  ent : Stream Γ t × Sched Γ × EvalSt e
  ent = subscribeE {lo = n} (rootWitness e ins) e root 0 0
          (sched-init e ins) (st-init e)
