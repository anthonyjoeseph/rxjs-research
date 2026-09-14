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
-- THE RANDOM SWEEP REACHES THE REGION, and that is a number rather than a
-- claim.  `QuickCheck` emits `μᵉ`, `varᵉ` and `deferᵉ` with the binder
-- scopes carried as INDICES, so a synchronous self-reference is not a
-- program it can write down and be rejected for; and its recursion is
-- linear by grammar, since a body reading its own var twice respawns per
-- tick and real rxjs hangs on that program too.  Twenty seeds at depth
-- four and five at depth five — 4500 programs, a third of them carrying
-- a live recursion — report no dry run.  IT IS MEASURED, NOT RECHECKED:
-- a compiled binary's row discharges nothing, and what it buys is the
-- coverage doubt, which was that the three peels had been reached only
-- at shapes one author chose.
------------------------------------------------------------------
module Verify-Rank-Sufficient where

open import Data.Bool using (false)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim  using (Fuel; Id; Tick)
open import Rx.Exp   using (Ctx; Closed; syncSizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt;
  subscribeE; drain; evaluate; rootWitness; sched-init; st-init; hasDry)
open import Rx.Evaluator.Domain using (evaluate⇓; eval-run; subscribeE⇓; drain⇓)
open import Verify-Rank-Sufficient.Dry-Emits using (hasDry-++)

-- THE DOMAIN IS WHERE THE WHOLE OF THE KNOWN FALSITY NOW SITS, AND
-- THAT CONCENTRATION IS WHAT THE RELATION BOUGHT.  No constructor of
-- any of its twenty families returns a dry burst — the relation
-- mirrors the clauses that DESCEND and says nothing about the arms
-- that give up — so an inhabitant at a run's own output is exactly a
-- certificate that no guard refused.  The two leaves below carry that
-- risk between them and nothing else under this module does: every
-- other leaf is an ordinary induction over a relation, provable today.
--
-- SO THEY ARE FALSE AS LONG AS THE ARMS ARE THERE, AND THAT IS THE
-- SCHEDULE RATHER THAN A DEFECT.  A program behind a gate runs dry at
-- the current evaluator, so today no derivation exists at its output
-- and neither can be proven at all.  They come true at the cutover
-- — the arms deleted, the guards replaced by the relation's own
-- premises — and until then what they measure is exactly how much of
-- the top line the door is costing.
--
-- DEAD ROUTE: postulating the descent's domain — the accessibility
--   itself, or a `Dom` predicate the evaluator pattern-matches on —
--   and deleting the three arms in the same edit.  The root witness is
--   well-foundedness APPLIED to the triple, a real proof, and the
--   evaluator REDUCES through it: every probe's `refl`, the bug cache
--   and the oracle all compute through that witness, so a postulated
--   domain gets stuck at the first pattern match and takes the whole
--   evidence apparatus with it.  What is dead is the LEAF and only the
--   leaf — a domain DEFINED beside the evaluator computes nothing and
--   breaks nothing — so this is a constraint on ORDER: the relation
--   lands first and the arms come out against it.

-- THE ENTRY INVARIANT, AND THE ONLY THING IT STANDS ON IS THAT THE
-- UNCONDITIONAL FORM IS DEAD.  A totality claim quantified freely
-- over the witness says a derivation exists at every entry, and three
-- of the machine's clauses read a component of that entry against the
-- TERM — so a caller free to pick the triple can starve a guard at a
-- program with nothing hard in it.  This is what relates the two ends,
-- and it is the one shape of hypothesis this repo admits without a
-- restatement's cost being a laundering: the conditioned statement is
-- the true one replacing a false one.
--
-- IT CARRIES ONE CONJUNCT AND IS EXPECTED TO GROW TO THREE, WHICH IS
-- THE CONVERGENCE RATHER THAN AN OMISSION.  One guard per component:
-- the μ unfold reads the synchronous size, the hop reads the rank, the
-- share connect reads the unconnected count.  Only the first is
-- stateable today — the other two are readings the carried report is
-- being written to supply — and each lands the day its own witness
-- forces it, so the predicate grows against a `⊥` rather than by
-- guess.  The root satisfies this one definitionally: `evaluate` seeds
-- the third component from the program's own size.
--
-- REFUTED: `Refuted.Totality-Entry` — the statement below WITHOUT this
--   premise, at a `μ` over a one-shot source entered at the zero
--   triple.  The witness claims the unfolding's size beside the run's
--   dryness, so it reports the one number the guard reads against the
--   one the caller chose.
EntryOK : ∀ {n} {Γ : Ctx n} {u} → Closed Γ u → Tri → Set
EntryOK b (_ , _ , sz) = syncSizeᵉ b ≤ sz

-- THE SUBSCRIBE CYCLE'S HALF, AND IT CARRIES THE TWO GUARDS THE
-- RELATION DOES NOT INDEX.  The hop's test became a sub-derivation and
-- so is answered by whoever builds one; the μ unfold's `syncSize`
-- comparison and the share connect's unconnected count are not
-- functions of any argument this statement takes, so they are
-- discharged here and nowhere above.  It takes the accessibility
-- witness explicitly because the evaluator still descends on one, and
-- the statement is about THAT machine rather than about the one the
-- cutover leaves.
--
-- PROBED: `Probed.Nodry-Halves` — two sources, a one-shot and a mapped
--   one, each derivation built by hand and held to the triple the
--   evaluator itself returns, so what the rows decide is whether the
--   relation MIRRORS the clause: the burst, the schedule left behind
--   and the state written must all be the ones the helpers compute.
--   The mapped row reaches through the event split and the retag.
--   Nothing here reaches a share, a flattener, a node store or the μ
--   unfold, so neither guard this statement carries is covered.
postulate
  subscribeE⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
    (κ : Path Γ lo u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    subscribeE⇓ {e = e} b κ id now sched st
      (subscribeE {e = e} ac b κ id now sched st)

-- THE ARRIVAL CYCLE'S HALF, WHICH DESCENDS ON THE FUEL AND SO CARRIES
-- NO GUARD AT ALL.  Its two base clauses are unconditional and its step
-- re-enters the subscribe cycle through a cascade, so what this leaf is
-- really waiting on is its sibling — which is why the two are separate
-- postulates rather than one: a derivation for the drain is an ordinary
-- fuel induction the moment the subscribe half exists.
--
-- PROBED: `Probed.Nodry-Halves` — one arrival, at the schedule and
--   registry the root subscribe actually left rather than at a state
--   written by hand, and held to the stream `drain` itself returns. It
--   covers the step arm over a root chain and the out-of-fuel tail; the
--   cancelled cascade and every chain carrying a frame are not reached.
postulate
  drain⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
    drain⇓ {e = e} fuel id sched st (drain {e = e} fuel id sched st)

-- AND THE TOTALITY CLAIM IS AN ASSEMBLY, WHICH IS WHAT UNBLOCKS EVERY
-- SOCKET UNDER IT.  A run is its root subscribe followed by its drain
-- and `eval-run` is exactly that shape, so the composition is CHECKED
-- rather than asserted: the two leaves' arguments are the ones
-- `evaluate` itself passes, and a leaf restated at a different entry
-- stops fitting here instead of months later.  Held as a bare postulate
-- it was also a wiring wall — a lemma whose only use is being handed to
-- a postulate earns no route home, so nothing proven about a frame's
-- emissions could land until this body existed to spend it.
evaluate⇓-total : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t)
  (ins : Slots Γ) → evaluate⇓ fuel e ins (evaluate fuel e ins)
evaluate⇓-total {n = n} fuel e ins =
  eval-run (subscribeE⇓-total {lo = n} (rootWitness e ins) e ≤-refl root 0 0
              (sched-init e ins) (st-init e))
           (drain⇓-total fuel 1 _ _)

-- THE SUBSCRIBE HALF, AN INDUCTION OVER THE RELATION AND NOT OVER THE
-- DESCENT.  A derivation is a finite tree whose constructors are the
-- clauses that emitted, so dryness of its output is a fact about which
-- emits those clauses BUILD — `init`, `value`, `close … exhausted`, a
-- plumbing retag — and the shelf next door proves each of those shapes
-- carries no dry event.  Nothing in the statement mentions a triple, a
-- rank or an order, which is why it is separated from the leaf above
-- rather than proven with it: the relation is what converted an
-- arithmetic obligation into a list induction.
--
-- PROBED: `Probed.Nodry-Halves` — four sources, each closing its burst
--   through a different helper: the one-shot, the empty, the refused
--   take, and a mapped source whose close reaches the caller through
--   the event split and retag.  Every row is load-bearing on the CLOSE
--   and none of them on the values, since `hasDry` reads only the
--   event.  The twelve families are otherwise uncovered — nothing here
--   reaches a share, a flattener or a node store.
postulate
  subscribeE⇓-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {b : Closed Γ u} {κ : Path Γ lo u t} {id now sched st}
    {burst : Stream Γ u} {sched′ st′} →
    subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
    hasDry burst ≡ false

-- THE DRAIN HALF, THE SAME FACT OVER THE OTHER CYCLE.  An arrival is
-- dispatched down every chain the registry admits and the results are
-- concatenated, so again the question is which emits the clauses build
-- and never which triple they stood at.  It is stated beside its
-- sibling rather than with it because the two cycles are separate
-- inductions — `eval-run` is exactly the constructor that splits them.
--
-- PROBED: `Probed.Nodry-Halves` — one arrival delivered down a root
--   chain, at the schedule and registry the root subscribe actually
--   left rather than at a state written out by hand.  It is the last
--   of its source, so the row covers the completion the cascade closes
--   on.  The cancelled arm and every chain carrying a frame are NOT
--   covered.
postulate
  drain⇓-nodry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    {fuel id sched st} {rest : Stream Γ t} →
    drain⇓ {e = e} fuel id sched st rest → hasDry rest ≡ false

-- A RUN IS ITS ROOT SUBSCRIBE FOLLOWED BY ITS DRAIN, AND THE RELATION
-- SAYS SO IN ONE CONSTRUCTOR.  The split the old tower spent a module
-- establishing is now the shape of `eval-run` itself, so this body is
-- the concatenation lemma applied to the two halves and nothing else.
evaluate⇓-nodry : ∀ {n} {Γ : Ctx n} {t} {fuel} {e : Closed Γ t}
  {ins : Slots Γ} {out : Stream Γ t} →
  evaluate⇓ fuel e ins out → hasDry out ≡ false
evaluate⇓-nodry (eval-run {burst = b} {rest = r} s d) =
  hasDry-++ b r (subscribeE⇓-nodry s) (drain⇓-nodry d)

-- THE TOP LINE, AND THE ONLY THING IT ADDS IS THE INSTANTIATION.  The
-- totality leaf hands a derivation at the run's own output and the
-- induction above reads dryness off it, so the seeding argument that
-- used to live here — which triple the root stands at, and whether it
-- reads the program — is not stated anywhere: the relation's entry
-- constructor IS the machine's entry, and a derivation at the output
-- is a claim about the run rather than about a number the door minted.
--
-- REFUTED: `Refuted.Dry-Wrap` — this statement, at three programs: one
--   per half of the substitution repair, and one behind a gate that
--   neither half reaches.  The witness pins `hasDry ≡ true` by `refl`
--   against the evaluator as it stands, so it is a refutation of the
--   CURRENT machine and not of the claim being aimed at — which is
--   what makes deleting the arms the repair and a cleverer measure
--   not one.
rank-sufficient :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (evaluate fuel e ins) ≡ false
rank-sufficient fuel e ins = evaluate⇓-nodry (evaluate⇓-total fuel e ins)
