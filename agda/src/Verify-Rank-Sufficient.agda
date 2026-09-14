------------------------------------------------------------------
-- EVERY RUN OF EVERY PROGRAM IS A DERIVATION.  `evaluate⇓-total` is
-- this tower's top line, and it is what the machine's three deleted
-- comparisons became: an obligation owed here rather than a question
-- answered there.
--
-- WHAT IT REPLACES IS SMALLER THAN IT, WHICH IS WHY THE REPLACEMENT IS
-- NOT A LOSS.  The claim this module used to make was that no run emits
-- the stuck marker — a statement about one emit, provable only because
-- no constructor of the relation builds that emit.  Totality is the
-- general form: relate the run to a derivation and every such claim
-- follows at once, for the marker and for anything else no clause
-- writes.  It is also the only form still stateable, since the marker
-- is not a term any more.
--
-- AND THE COST LANDS ON `evaluate` RATHER THAN HERE, WHICH IS THE PART
-- TO CARRY BEFORE READING FURTHER.  The machine no longer re-establishes
-- its own order, so it is not accepted on its own: the three edges are
-- `Rx.Evaluator.Doorless`'s facts, and spending them is what a builder
-- does.  Nothing below may reach for a pragma instead — that is a
-- soundness hole this mandate does not authorise, and the whole point
-- of moving the arithmetic was to put its failure somewhere a check can
-- see it.
--
-- THE RANDOM SWEEP REACHED THE REGION WHILE THE COMPARISONS WERE STILL
-- THERE, and that is a number rather than a claim.  `QuickCheck` emits
-- `μᵉ`, `varᵉ` and `deferᵉ` with the binder scopes carried as INDICES,
-- so a synchronous self-reference is not a program it can write down and
-- be rejected for; and its recursion is linear by grammar, since a body
-- reading its own var twice respawns per tick and real rxjs hangs on
-- that program too.  Twenty seeds at depth four and five at depth five —
-- 4500 programs, a third of them carrying a live recursion — reported no
-- stuck run.  IT IS MEASURED, NOT RECHECKED: a compiled binary's row
-- discharges nothing, and what it bought was the coverage doubt, which
-- was that the three peels had been reached only at shapes one author
-- chose.  What it says now is that those peels take their positive
-- branch on every program the sweep can write — so the premises the
-- builder owes are not vacuously demanding.
------------------------------------------------------------------
module Verify-Rank-Sufficient where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Nat using (_≤_; _<_; suc; _+_; _⊔_; _<?_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; m≤n+m; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Rx.Prim  using (Fuel; Id; Tick; InstEmit; InstEvent;
  init; value; close; handoff; complete)
open import Rx.Exp   using (Ctx; Closed; Ty; Val; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; syncSizeᵉ; evalTm; unfoldμ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Obs-Depth using (obsDepthᵉ; unfoldμ-no-deeper)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ltS)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Evaluator using (Stream; Path; root; Sched; EvalSt; Frame; AllOp; NodeId; NodeState;
  map-f; take-f; scan-f; from-inner; thru-outer; _↠_;
  scan-st; take-st; mergeAll-st; switch-st; exhaust-st; lookupNode; splitEvents;
  subscribeE; pushBurst; stepFrame; thruWalk; thruConsume; innerReact;
  subscribeAll; drain; evaluate; sched-init; st-init;
  subscribeInner)
open import Rx.Evaluator.Doorless using (rootWitness)
open import Rx.Evaluator.Domain using (evaluate⇓; eval-run; subscribeE⇓;
  pushBurst⇓; stepFrame⇓; thruWalk⇓; thruConsume⇓; innerReact⇓;
  subscribeAll⇓; drain⇓; subscribeInner⇓;
  subs-of; subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan;
  subs-merge-all; subs-switch-all; subs-exhaust-all; subs-μ; subs-defer;
  step-map; step-scan; step-scan-nil; step-take; step-from-inner; step-thru-outer;
  walk-nil; walk-cons; push-nil; push-cons)
-- the five frames, stated together at the full axis set.  This module is
-- the whole of what `subscribe-carried`'s structural clauses spend, and
-- every one of them spends `pushBurst-carried` — so a frame that turns
-- out to need a fourth axis is a type error HERE, at all five clauses,
-- rather than a green statement that is quietly wrong at one of them.
open import Verify-Rank-Sufficient.Push-Carried using (Pay; Pout-of;
  pushBurst-carried)

-- THE DOMAIN IS WHERE THE WHOLE OF THE KNOWN FALSITY NOW SITS, AND
-- THAT CONCENTRATION IS WHAT THE RELATION BOUGHT.  No constructor of
-- any of its twenty families returns a dry burst — the relation
-- mirrors the clauses that DESCEND and says nothing about the arms
-- that give up — so an inhabitant at a run's own output is exactly a
-- certificate that no guard refused.  The two leaves below carry that
-- risk between them and nothing else under this module does: every
-- other leaf is an ordinary induction over a relation, provable today.
--
-- AND THEY WERE FALSE WHILE THE ARMS STOOD, WHICH IS WHY THE DELETION
-- CAME FIRST AND NOT AFTER THEM.  A program behind a guard ran dry, so
-- no derivation existed at its output and no amount of grinding could
-- have produced one — the leaves were not hard, they were untrue.  What
-- the deletion changed is not their difficulty but their truth value,
-- and it is the only change that could have.
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
-- IT CARRIES TWO CONJUNCTS AND IS EXPECTED TO GROW TO THREE, WHICH IS
-- THE CONVERGENCE RATHER THAN AN OMISSION.  One guard per component:
-- the μ unfold reads the synchronous size, the hop reads the rank, the
-- share connect reads the unconnected count.  The third is a reading
-- nothing has forced a shape for yet, and each lands the day its own
-- witness forces it, so the predicate grows against a `⊥` rather than
-- by guess.  The root satisfies both of these out of its own seeding:
-- `evaluate` builds the entry from the program's size and depth.
--
-- AND THE RANK CONJUNCT IS WHAT MAKES THE HOP'S PREMISE PAYABLE, which
-- is why it is here rather than threaded into a signature.  A value a
-- frame hands on is bounded by the depth of the TERM the burst came
-- from, so the statement that pays `HandedOK` needs the entry to bound
-- that depth — and the hop's own re-entry satisfies the conjunct
-- definitionally, since it drops the rank to the inner's own reading.
--
-- REFUTED: git show ba1285b:agda/evidence/refuted/Refuted/Totality-Entry.agda
--   — the statement below WITHOUT this premise, at a `μ` over a one-shot
--   source entered at the zero triple, claiming the unfolding's size
--   beside the run's dryness.  It is at a sha because `src` can no
--   longer state it: the run reads no triple and emits no marker, so
--   neither number the witness put side by side still exists.
EntryOK : ∀ {n} {Γ : Ctx n} {u} → Closed Γ u → Tri → Set
EntryOK b (_ , r , sz) = syncSizeᵉ b ≤ sz × obsDepthᵉ b ≤ r

-- CARRYING THE ENTRY INVARIANT DOWN A FRAME, WHICH IS THE WHOLE OF THE
-- ARITHMETIC THE SUBSCRIBE INDUCTION NEEDS.  `syncSizeᵉ` counts the
-- constructor and the frame's own term before it reaches the source,
-- so a term's inner expression measures strictly below it and the
-- invariant survives every structural descent with room to spare.  The
-- only place a step is not structural is the μ peel, and that one is
-- paid by the unfolding's own measure rather than here.
entry-under : ∀ {c sz} → suc c ≤ sz → c ≤ sz
entry-under le = ≤-trans (n≤1+n _) le

entry-inner : ∀ {a b sz} → suc (a + b) ≤ sz → b ≤ sz
entry-inner {a} {b} le = ≤-trans (m≤n+m b a) (entry-under le)

-- and the rank's own descent, which is a join rather than a successor:
-- every structural clause reads its frame's term BESIDE the source's
-- depth, so the source is a summand and the bound passes through
entry-depth : ∀ {a c r} → a ⊔ c ≤ r → c ≤ r
entry-depth {a} {c} le = ≤-trans (m≤n⊔m a c) le

-- and the two shapes every structural clause takes, so a call site
-- spends one name rather than splitting the pair by hand.  A framed
-- clause carries its frame's term in BOTH components — summed in the
-- size, joined in the depth — while a flattener carries none, so its
-- rank passes through untouched.
inner-ok : ∀ {a b c d sz r} → (suc (a + b) ≤ sz) × (c ⊔ d ≤ r) → (b ≤ sz) × (d ≤ r)
inner-ok (s , p) = entry-inner s , entry-depth p

under-ok : ∀ {b c sz r} → (suc b ≤ sz) × (c ≤ r) → (b ≤ sz) × (c ≤ r)
under-ok (s , p) = entry-under s , p

-- WHAT A CLAUSE IS HANDED, WHICH IS A SEPARATE PREDICATE AND NOT A
-- FOURTH CONJUNCT UP THERE.  The entry invariant speaks about the TERM
-- a subscribe enters at; the hop reads a runtime VALUE that arrives
-- later and is structurally unrelated to that term, so no reading of
-- the program can supply it.  This says exactly what the guard reads —
-- every value the clause receives is written shallower than the rank it
-- is standing at — and it is the one shape of hypothesis this repo
-- admits without a restatement being a laundering.
--
-- AND IT READS THE VALUE'S TYPE, WHICH IS THE DIFFERENCE BETWEEN A
-- PROPERTY OF BURSTS AND A DEMAND ON THE ENTRY.  The bound exists to pay
-- ONE guard — the hop's, which compares an OBSERVABLE against the rank —
-- and an observable reaches a frame as the payload of a `strmᵗ`, the one
-- head the reading charges a successor for.  So the strictness is real
-- exactly where it is spent.  Asked flat, of every value at every type,
-- it reads a numeral at nought and demands nought be strictly below the
-- rank, which is a claim about the caller and not about the burst.
--
-- SO THE CLAUSES MIRROR THE READING'S OWN, RATHER THAN STOPPING AT THE
-- OBSERVABLE HEAD.  A pair or an injection can carry an observable a
-- later projection hands to a hop, so ⊤ at those types would weaken the
-- premise exactly where a frame is free to recover the value — and
-- recursing costs nothing, since the reading already recurses there and
-- the two then correspond clause for clause.
--
-- REFUTED: git show ba1285b:agda/evidence/refuted/Refuted/Hop-Unconditioned.agda
--   — the hop leaf below WITHOUT this premise, at the emptiest inner
--   there is entered at a rank of nought.  What it established survives
--   the cutover and is why this premise is here: the repair relates the
--   two ends rather than reading either more carefully.  It is at a sha
--   because the guard it was strict against is gone.
--
-- REFUTED: `Refuted.Carried-Unranked` — the FLAT reading, asked of every
--   value at every type, at a one-shot source of one numeral entered at
--   the rank the root itself builds. That witness is as far from the
--   risky region as a program gets, which is what says the repair is the
--   type split rather than a hypothesis about the program.
ValOK : ∀ {n} {Γ : Ctx n} (u : Ty) → Tri → Val Γ u → Set
ValOK unitᵗ    _ _           = ⊤
ValOK boolᵗ    _ _           = ⊤
ValOK natᵗ     _ _           = ⊤
ValOK (s ×ᵗ t) τ (a , b)     = ValOK s τ a × ValOK t τ b
ValOK (s +ᵗ t) τ (inj₁ a)    = ValOK s τ a
ValOK (s +ᵗ t) τ (inj₂ b)    = ValOK t τ b
ValOK (obs t)  (_ , r , _) o = obsDepthᵉ o < r

HandedOK : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → Tri → Set
HandedOK {u = u} vs τ = All (ValOK u τ) vs

-- AND THE SAME OVER A BURST, WHICH IS WHERE THOSE VALUES COME FROM.  A
-- push cycle steps one frame per emit and hands that frame the emit's
-- own values, so the premise travels as a property of the whole burst
-- and is split, emit by emit, by the induction that walks it.  Nothing
-- here reads the schedule or the store: the burst is already built when
-- the cycle starts, which is what makes a single `All` sufficient.
--
-- AND IT IS STATED OVER THE EVENTS RATHER THAN OVER THE SPLIT, WHICH IS
-- FORCED AND NOT A PREFERENCE.  The splitter is polymorphic in the type
-- of the bookkeeping half it retags into, and a predicate reading only
-- its first component leaves that parameter free — an unsolved meta at
-- the definition, and two applications at DIFFERENT retag types that no
-- longer agree on an open list.  Reading the events directly names no
-- such parameter, and `split-handed` below carries the property across
-- the splitter at whatever type the call site pins.
EventOK : ∀ {n} {Γ : Ctx n} {u} → Tri → InstEvent (Val Γ u) → Set
EventOK {u = u} τ (value v) = ValOK u τ v
EventOK _ (init _)    = ⊤
EventOK _ (close _ _) = ⊤
EventOK _ (handoff _) = ⊤
EventOK _ complete    = ⊤

BurstOK : ∀ {n} {Γ : Ctx n} {s} → Stream Γ s → Tri → Set
BurstOK bs τ = All (λ em → All (EventOK τ) (InstEmit.events em)) bs

-- the splitter keeps every `value` payload and drops the rest, so a
-- property of the events is a property of the values it grafts — proven
-- over the retag type the call site pins rather than over a chosen one,
-- since the two halves are independent and only the first is read here
split-handed : ∀ {n} {Γ : Ctx n} {u} {A : Set} {τ}
             → (es : List (InstEvent (Val Γ u)))
             → All (EventOK τ) es
             → HandedOK {Γ = Γ} (proj₁ (splitEvents {A = A} es)) τ
split-handed []              []ᵃ        = []ᵃ
split-handed (value v  ∷ es) (p ∷ᵃ ps) = p ∷ᵃ split-handed es ps
split-handed (init _   ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (close _ _ ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (handoff _ ∷ es) (_ ∷ᵃ ps) = split-handed es ps
split-handed (complete ∷ es) (_ ∷ᵃ ps) = split-handed es ps

-- THE ONE CONSTRUCTOR WHOSE CLAUSE READS A COMPONENT THE ENTRY
-- INVARIANT DOES NOT YET SPEAK ABOUT.  A slot subscription splits six
-- ways — floor, share, spent script, live script, and a cold source
-- with or without a tail — and the share arm's connect compares the
-- UNCONNECTED COUNT against the triple's first component, answering the
-- negative case dry.  So this leaf is refutable exactly as its parent
-- was, and by a witness of the same shape: a program over a share,
-- entered at a first component below what the slots hold.  It is stated
-- unconditionally on purpose — the refutation is what says which
-- conjunct `EntryOK` grows, and a conjunct guessed ahead of one would
-- be a premise nothing forced.
--
-- PROBED: `Probed.Nodry-Halves` — the live-script arm only, at a hot
--   slot entered below the root's floor, so the row pins the floor
--   comparison and the registration that lowers the path by that
--   comparison's own witness.  NOT covered, and the gap is the whole
--   risk: the SHARE arm, where the connect reads the unconnected count;
--   nor the spent script, nor either cold arm.
postulate
  subscribeE⇓-input-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {τ : Tri} (ac : Acc _≺_ τ) (i : Fin n) → EntryOK {Γ = Γ} (input i) τ →
    (κ : Path Γ lo (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    subscribeE⇓ {e = e} (input i) κ id now sched st
      (subscribeE {e = e} (input i) κ id now sched st)

-- THE HOP, LOCALISED TO THE ONE CLAUSE THAT TAKES A VALUE AND
-- SUBSCRIBES IT.  A `thru-outer` frame is handed values that ARE inner
-- observables, and the walk consumes them one at a time; each consume
-- re-enters the subscribe cycle at a term the caller never wrote down,
-- which is why the machine tests a rank here and answers the negative
-- case dry.  Everything above this in the push cycle is list plumbing —
-- so this leaf and its sibling are where the whole of that cycle's
-- falsity now sits, and the statement they are missing is a bound on
-- what a frame's own outputs read.
--
-- AND THE PREMISE IS WHAT IS LEFT OF ITS FALSITY, SINCE THE GUARD CAN
-- NOW ONLY REFUSE WHERE `HandedOK` IS UNPAYABLE.  The value is shallower
-- than the rank by hypothesis, so the subscribing arm's comparison
-- succeeds; what the statement still owes is the arm that ENQUEUES and
-- the two operators that read a different node state.
--
-- REFUTED: git show ba1285b:agda/evidence/refuted/Refuted/Hop-Unconditioned.agda
--   — this statement WITHOUT the premise, at the emptiest inner there is
--   entered at a rank of nought.  The relation never had an arm building
--   the marker the machine answered with, which is the half of the
--   finding the cutover kept; the machine's half is at the sha.
--
-- PROBED: `Probed.Nodry-Halves` — the DROP arm only, entered at a node
--   id nothing installed, so the row pins that the clause hands its
--   schedule and store straight back.  NOT covered, and it is the whole
--   risk: the subscribing arm, where the rank test lives; the enqueue
--   arm; and both other operators.
postulate
  thruConsume⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId)
    (κ : Path Γ lo u t) (id : Id) (now : Tick) (o : Val Γ (obs u)) →
    HandedOK {Γ = Γ} (o ∷ []) τ → (sched : Sched Γ) (st : EvalSt e) →
    thruConsume⇓ {e = e} op nid κ id now o sched st
      (thruConsume {e = e} op nid κ id now o sched st)

-- ─────────────────────────────────────────────────────────────────────
-- KILLING THE DOOR.  Coarse statements only — none of the four below is
-- claimed to typecheck as written, and the shapes are what the next
-- session should argue with rather than the syntax.
-- ─────────────────────────────────────────────────────────────────────

-- THE DOOR IS `subscribeInner`'s RANK TEST, AND KILLING IT IS PROVING
-- ITS NEGATIVE ARM UNREACHABLE — not weakening it, not measuring it
-- better.  The machine compares `obsDepthᵉ o <? r` and answers the `no`
-- case by minting an instance and closing it `dried`.  That arm is the
-- only site in the whole subscribe cycle that builds the marker from a
-- rank, and `subscribeInner⇓` has exactly one constructor, which
-- demands a real sub-derivation at the arriving value.  So a derivation
-- at the machine's own result CANNOT EXIST unless the comparison
-- succeeded: the leaf below is not a statement about the door, it is
-- the statement that kills it.
--
-- AND THE PREMISE ALREADY IS THE COMPARISON, WHICH IS WHY THIS IS
-- NEAR-DEFINITIONAL RATHER THAN ARITHMETIC.  `ValOK (obs u) (_ , r , _)`
-- unfolds to `obsDepthᵉ o < r` and the guard tests `obsDepthᵉ o <? r`:
-- one currency, one inequality, so the `no` arm dies by `⊥-elim`
-- against the hypothesis and nothing about depth is owed.  Every
-- syntactic candidate that died did so trying to PRICE this comparison;
-- the premise route does not price it, it assumes it and pushes the
-- obligation to whoever hands the value over.
postulate
  subscribeInner⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (allNid : NodeId)
    (κ : Path Γ lo u t) (id : Id) (now : Tick) (o : Val Γ (obs u)) →
    HandedOK {Γ = Γ} (o ∷ []) τ → (sched : Sched Γ) (st : EvalSt e) →
    subscribeInner⇓ {e = e} op allNid κ id now o sched st
      (subscribeInner {e = e} op allNid κ id now o sched st)

-- THE EXTRACTION, WRITTEN OUT BECAUSE IT IS THE WHOLE OF THE ARGUMENT
-- AND READS AS A TRIVIALITY.  It is what the leaf above will `with` on
-- to refute the guard, and stating it separately is what keeps the
-- refutation from being reargued at each of the three consume families.
hop-guard : ∀ {n} {Γ : Ctx n} {u} {U r sz} (o : Val Γ (obs u))
          → HandedOK {Γ = Γ} (o ∷ []) (U , r , sz)
          → obsDepthᵉ o < r
hop-guard o (h ∷ᵃ []ᵃ) = h

-- AND THE OBLIGATION THIS LEG CANNOT DISCHARGE ON ITS OWN, WHICH IS THE
-- REASON THE NEXT LEG IS THE NEXT LEG.  Every call reaching the door
-- arrives from a burst the subscribe cycle produced, so the premise is
-- payable only where something says a burst's values are shallower than
-- the rank — which is `subscribe-carried`, and its second refutation
-- says that statement has to quantify over the SCHEDULE.  Stated here
-- rather than proven here on purpose: assembly first, leaves second.
postulate
  burst-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
    (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    BurstOK {Γ = Γ} (proj₁ (subscribeE {e = e} b κ id now sched st)) τ

-- THE SAME EDGE FROM THE OTHER SIDE: an inner subscription that has
-- already been made, reacting to what it delivers.  It reaches the
-- subscribe cycle through the flattener's own bookkeeping rather than
-- through a fresh value, so it carries no rank test of its own — what
-- it inherits is the store the walk left, which is the second half of
-- the same missing statement.
--
-- PROBED: `Probed.Nodry-Halves` — the UNFINISHED arm only, where the
--   values are handed back untouched and the frame is reported
--   unfinished, so the row fails on a dropped value or a flag carried
--   through.  NOT covered: the finishing arm, which reads the registry
--   and re-enters the cycle through `innerFinish`.
postulate
  innerReact⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ lo s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sched : Sched Γ) (st : EvalSt e) (fin : Bool) →
    innerReact⇓ {e = e} op allNid inst κ id now vals sched st fin
      (innerReact {e = e} op allNid inst κ id now vals sched st fin)

-- THE WALK IS A LIST INDUCTION AND NOTHING ELSE, which is the point of
-- separating it from the consume below it: the values a `thru-outer`
-- frame receives are folded left to right, each consume threading the
-- schedule and store into the next, and the outputs concatenate.  No
-- guard is read here at all.
thruWalk⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (nid : NodeId)
  (κ : Path Γ lo u t) (id : Id) (now : Tick) (os : List (Val Γ (obs u))) →
  HandedOK {Γ = Γ} os τ → (sched : Sched Γ) (st : EvalSt e) →
  thruWalk⇓ {e = e} op nid κ id now os sched st
    (thruWalk {e = e} op nid κ id now os sched st)
thruWalk⇓-total ac op nid κ id now []       hk        sched st = walk-nil
thruWalk⇓-total ac op nid κ id now (o ∷ os) (h ∷ᵃ hs) sched st =
  walk-cons (thruConsume⇓-total ac op nid κ id now o (h ∷ᵃ []ᵃ) sched st)
            (thruWalk⇓-total ac op nid κ id now os hs _ _)

-- THE FIVE FRAMES, THREE OF WHICH ANSWER OUT OF THEIR OWN CLAUSE.  Map
-- applies its function to the list, take defers wholesale to the
-- dispatcher the relation copies verbatim, and scan reads a node whose
-- stored type is compared against the frame's — the arms where that
-- read fails all return the empty step, which is one constructor.  The
-- two that are not answered here are the two that subscribe.
stepFrame⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fr : Frame Γ s u)
  (κ : Path Γ lo u t) (vals : List (Val Γ s)) →
  HandedOK {Γ = Γ} vals τ → (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  stepFrame⇓ {e = e} id now fr κ vals fin sched st
    (stepFrame {e = e} id now fr κ vals fin sched st)
stepFrame⇓-total ac id now (map-f fn) κ vals hk fin sched st = step-map
stepFrame⇓-total ac id now (take-f nid) κ vals hk fin sched st = step-take
stepFrame⇓-total ac id now (from-inner op allNid inst) κ vals hk fin sched st =
  step-from-inner (innerReact⇓-total ac op allNid inst κ id now vals sched st fin)
stepFrame⇓-total ac id now (thru-outer op nid) κ vals hk fin sched st =
  step-thru-outer (thruWalk⇓-total ac op nid κ id now vals hk sched st)
stepFrame⇓-total {u = u} ac id now (scan-f fn nid) κ vals hk fin sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing                    = step-scan-nil
... | just (take-st _)           = step-scan-nil
... | just (mergeAll-st _ _ _ _) = step-scan-nil
... | just (switch-st _ _)       = step-scan-nil
... | just (exhaust-st _ _)      = step-scan-nil
... | just (scan-st {w} acv) with w ≟ᵗ u
...   | yes refl = step-scan eq refl
...   | no  _    = step-scan-nil

-- AND THE CYCLE ITSELF IS THE OUTER LIST INDUCTION.  Each emit is
-- split, stepped and reassembled under its own envelope, and the
-- envelope is copied by the constructor rather than recomputed — so the
-- only content is that the split the clause performs is the split the
-- premise names, which is `refl`.
pushBurst⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ lo u t) (burst : Stream Γ s) →
  BurstOK {Γ = Γ} burst τ → (sched : Sched Γ) (st : EvalSt e) →
  pushBurst⇓ {e = e} id now f κ burst sched st
    (pushBurst {e = e} id now f κ burst sched st)
pushBurst⇓-total ac id now f κ []         bk        sched st = push-nil
pushBurst⇓-total ac id now f κ (em ∷ ems) (b ∷ᵃ bs) sched st =
  push-cons refl
    (stepFrame⇓-total ac id now f κ
      (proj₁ (splitEvents (InstEmit.events em)))
      (split-handed (InstEmit.events em) b)
      (proj₂ (proj₂ (splitEvents (InstEmit.events em)))) sched st)
    (pushBurst⇓-total ac id now f κ ems bs _ _)

-- THE FLATTENERS' SHARED WRAPPER, WHICH IS A NODE INSTALL FOLLOWED BY
-- THE TWO CYCLES ABOVE.  It is a leaf rather than a body only because
-- its two halves are, and it takes the entry invariant at its own outer
-- term because that is what its subscribe half will ask for.  Nothing
-- distinguishes the three operators here — they differ in the state
-- installed, which no clause of either cycle reads.
--
-- PROBED: `Probed.Nodry-Halves` — the merge flattener over an outer
--   that hands it no observable, which reaches the wrapper's own
--   plumbing and nothing beyond it: the node id the install writes is
--   the one the frame is built at, so a second mint or a frame built at
--   the pre-mint counter fails the row.  NOT covered: any walk with a
--   value in it, hence no inner subscribe and no hop; and neither of
--   the other two operators.
postulate
  subscribeAll⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (ns : NodeState Γ)
    (b : Closed Γ (obs u)) → EntryOK b τ → (κ : Path Γ lo u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    subscribeAll⇓ {e = e} op ns b κ id now sched st
      (subscribeAll {e = e} op ns b κ id now sched st)

-- WHAT A SUBSCRIBE HANDS ON, WHICH IS THE STATEMENT THAT PAYS THE HOP'S
-- PREMISE AND THE ONE PLACE THE TWO CURRENCIES MEET.  A framed clause
-- pushes the burst its SOURCE produced, so the values a frame receives
-- are the source's emissions — and the entry invariant bounds the
-- source's own depth, which is what makes the conclusion stateable from
-- the hypotheses rather than from the call site.
--
-- THE INEQUALITY IS STRICT AND THAT IS THE MECHANISM, NOT A MARGIN.  An
-- observable arrives in a burst as the value of a `strmᵗ`, which the
-- reading charges a successor for — so an emitted observable is written
-- STRICTLY below the term that emitted it, and the hop's strict guard is
-- exactly the comparison this discharges.  A non-strict reading would
-- make the statement false at a source that emits itself.
--
-- AND IT IS FALSE AS WRITTEN, AT THE ONE CLAUSE WHERE ITS HYPOTHESIS
-- SPEAKS ABOUT A SYMBOL.  A slot reference is priced at nought on
-- purpose — costing it would need the staged fixpoint a slot environment
-- carries — so the entry invariant at a reference constrains nothing,
-- while the burst the clause returns is the DEFINITION's.  The connect
-- re-seeds the rank at that definition's own nesting and so never makes
-- the comparison itself, which is why the descent is sound and this
-- statement is not.  The conjunct owed is over the SCHEDULE: the slots
-- the telescope holds are written below the rank.  Until that lands the
-- statement stays at full strength rather than being conditioned on
-- whatever today's callers happen to supply.
--
-- AND IT IS NO LONGER A LEAF, WHICH IS THE LEG.  A subscribe's burst is
-- its SOURCE's burst pushed through the frames its own term installs, so
-- every structural clause is `pushBurst-carried` at that clause's frame
-- and nothing about the frames is asserted here.  What is left over is
-- the three things no frame answers — a source's own burst, a
-- flattener's walk, and the slot conjunct the second witness below
-- names — and those are the leaves.  The five frames themselves are
-- `Verify-Rank-Sufficient.Push-Carried`, stated together at the full
-- axis set rather than one axis at a time as each one fell.
--
-- REFUTED: `Refuted.Carried-Unranked` — the FLAT reading of the
--   conclusion, asked of every value at every type, at a one-shot source
--   of one numeral entered at the rank the root itself builds. Answered
--   by the type split `ValOK` now carries.
--
-- REFUTED: `Refuted.Carried-Shared` — the reading that survived it, at a
--   slot whose shared definition writes an observable. The two figures
--   claimed there are the gap: the definition reads one, the reference
--   standing for it reads nought, so no repair reading the term can
--   close it.
subscribe-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
  (κ : Path Γ lo u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  BurstOK {Γ = Γ} (proj₁ (subscribeE {e = e} b κ id now sched st)) τ
subscribe-carried ac (input i) ok κ id now sched st =
  source-carried ac i ok κ id now sched st
subscribe-carried ac (ofᵉ ts) ok κ id now sched st = of-carried ts ok
subscribe-carried ac emptyᵉ ok κ id now sched st = []ᵃ
subscribe-carried ac (mapᵉ f b) ok κ id now sched st =
  burst-widen (pushBurst-carried ac id now (map-f f) κ _ (payOf τ) (rankOf τ)
                 (subscribe-carried ac b (inner-ok ok) (map-f f ↠ κ) id now sched st)
                 ≤-refl)
subscribe-carried ac (takeᵉ count b) ok κ id now sched st =
  burst-widen (pushBurst-carried ac id now (take-f _) κ _ (payOf τ) (rankOf τ)
                 (subscribe-carried ac b (inner-ok ok) (take-f _ ↠ κ) id now _ _)
                 ≤-refl)
subscribe-carried ac (scanᵉ f seed b) ok κ id now sched st =
  burst-widen (pushBurst-carried ac id now (scan-f f _) κ _ (payOf τ) (rankOf τ)
                 (subscribe-carried ac b (inner-ok ok) (scan-f f _ ↠ κ) id now _ _)
                 ≤-refl)
subscribe-carried ac (mergeAllᵉ lim b) ok κ id now sched st =
  all-carried ac mergeAllᵒ b (under-ok ok) κ id now sched st
subscribe-carried ac (switchAllᵉ b) ok κ id now sched st =
  all-carried ac switchᵒ b (under-ok ok) κ id now sched st
subscribe-carried ac (exhaustAllᵉ b) ok κ id now sched st =
  all-carried ac exhaustᵒ b (under-ok ok) κ id now sched st
subscribe-carried {τ = _ , _ , sz} (acc rec) (μᵉ body) ok κ id now sched st
  with syncSizeᵉ (unfoldμ body) <? sz
... | no ¬p = ⊥-elim (¬p (≤-trans (unfoldμ-shrinks body) (proj₁ ok)))
... | yes p =
      subscribe-carried (rec (ltS p)) (unfoldμ body)
        (≤-refl , ≤-trans (unfoldμ-no-deeper body) (proj₂ ok))
        κ id now sched st
subscribe-carried ac (varᵉ ()) ok κ id now sched st
subscribe-carried ac (deferᵉ body) ok κ id now sched st = []ᵃ

-- THE THREE RESIDUES, AND EACH IS A DIFFERENT KIND OF THING — which is
-- the product of writing the body: before it, all three were inside one
-- postulate and none of them was nameable.
--
--   `source-carried` is the one `Refuted.Carried-Shared` killed the term
--   reading of: a slot reference is priced at nought while the burst the
--   clause returns is the DEFINITION's, so what is owed is over the
--   SCHEDULE — the slots the telescope holds are written below the rank.
--   It is the conjunct `EntryOK` is expected to grow.
--
--   `of-carried` is a literal's own payloads against the rank the
--   reading charges the `strmᵗ` a successor for.  Arithmetic, and the
--   only one of the three with no risk in it.
--
--   `all-carried` is the flattener's walk, and it is where the DOOR's
--   premise is actually paid: the values a `thru-outer` frame receives
--   are inner observables, and `thru-outer-frame-carried` is the
--   statement that they are written strictly shallower than the rank.
postulate
  source-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo}
    {τ : Tri} (ac : Acc _≺_ τ) (i : Fin n) → EntryOK {Γ = Γ} (input i) τ →
    (κ : Path Γ lo (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    BurstOK {Γ = Γ} (proj₁ (subscribeE {e = e} (input i) κ id now sched st)) τ

  of-carried : ∀ {n} {Γ : Ctx n} {u} {τ : Tri} (ts : Timed Γ u) →
    EntryOK {Γ = Γ} (ofᵉ ts) τ → BurstOK {Γ = Γ} (ofBurst ts) τ

  all-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
    {τ : Tri} (ac : Acc _≺_ τ) (op : AllOp) (b : Closed Γ (obs u)) →
    EntryOK b τ → (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    BurstOK {Γ = Γ}
      (proj₁ (subscribeAll {e = e} op _ b κ id now sched st)) τ

-- the two adapters between this module's `Tri`-shaped bound and the
-- family's PAIR-shaped one.  They exist because the family is stated at
-- the pair — which is what the refutations bought — while the entry
-- invariant is stated at the triple, and the triple's lower half IS the
-- pair.  Widening is the join at the emit length, which is monotone.
postulate
  payOf : Tri → Pay
  rankOf : Tri → ℕ
  burst-widen : ∀ {n} {Γ : Ctx n} {s} {bs : Stream Γ s} {τ k} →
    BurstOK bs (Pout-of τ k) → BurstOK {Γ = Γ} bs τ

-- THE SUBSCRIBE CYCLE'S HALF, AND IT IS AN INDUCTION RATHER THAN A LEAF
-- BECAUSE THE ENTRY INVARIANT IS WHAT MAKES ONE WRITEABLE.  Every
-- structural clause recurses at the same witness on a term the measure
-- counts strictly below, and the μ peel — the one step that is not
-- structural, since the unfolding is larger than the term it replaces —
-- steps the witness instead and re-establishes the invariant at the
-- unfolding's own size.  What the invariant buys at that clause is the
-- guard: the evaluator compares the unfolding's measure against the
-- entry's third component and answers dry when it fails, and the
-- premise says it cannot.
--
-- SO THE RISK LEFT UNDER THIS BODY IS THREE LEAVES AND NO LONGER A
-- GUARD.  Two of the machine's three non-indexed comparisons are now
-- inside `subscribeE⇓-input-total` — the share connect's — and inside
-- the push cycle — the hop's; the third is discharged here.  That is
-- the convergence the entry invariant was minted for: the same risk,
-- localised to the two clauses that actually read a component, at
-- statements small enough to instantiate.
subscribeE⇓-total : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) → EntryOK b τ →
  (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  subscribeE⇓ {e = e} b κ id now sched st
    (subscribeE {e = e} b κ id now sched st)
subscribeE⇓-total ac (input i) ok κ id now sched st =
  subscribeE⇓-input-total ac i ok κ id now sched st
subscribeE⇓-total ac (ofᵉ ts) ok κ id now sched st = subs-of refl
subscribeE⇓-total ac emptyᵉ ok κ id now sched st = subs-empty refl
subscribeE⇓-total ac (mapᵉ f b) ok κ id now sched st =
  subs-map (subscribeE⇓-total ac b (inner-ok ok) (map-f f ↠ κ) id now sched st)
           (pushBurst⇓-total ac id now (map-f f) κ _
              (subscribe-carried ac b (inner-ok ok) (map-f f ↠ κ) id now sched st) _ _)
subscribeE⇓-total ac (takeᵉ count b) ok κ id now sched st
  with evalTm count in eq
... | 0     = subs-take-zero eq refl
... | suc k =
      subs-take-suc eq refl
        (subscribeE⇓-total ac b (inner-ok ok) (take-f _ ↠ κ) id now _ _)
        (pushBurst⇓-total ac id now (take-f _) κ _
           (subscribe-carried ac b (inner-ok ok) (take-f _ ↠ κ) id now _ _) _ _)
subscribeE⇓-total ac (scanᵉ f seed b) ok κ id now sched st =
  subs-scan refl
    (subscribeE⇓-total ac b (inner-ok ok) (scan-f f _ ↠ κ) id now _ _)
    (pushBurst⇓-total ac id now (scan-f f _) κ _
       (subscribe-carried ac b (inner-ok ok) (scan-f f _ ↠ κ) id now _ _) _ _)
subscribeE⇓-total ac (mergeAllᵉ lim b) ok κ id now sched st =
  subs-merge-all (subscribeAll⇓-total ac _ _ b (under-ok ok) κ id now sched st)
subscribeE⇓-total ac (switchAllᵉ b) ok κ id now sched st =
  subs-switch-all (subscribeAll⇓-total ac _ _ b (under-ok ok) κ id now sched st)
subscribeE⇓-total ac (exhaustAllᵉ b) ok κ id now sched st =
  subs-exhaust-all (subscribeAll⇓-total ac _ _ b (under-ok ok) κ id now sched st)
subscribeE⇓-total {τ = _ , _ , sz} (acc rec) (μᵉ body) ok κ id now sched st
  with syncSizeᵉ (unfoldμ body) <? sz
... | no ¬p = ⊥-elim (¬p (≤-trans (unfoldμ-shrinks body) (proj₁ ok)))
... | yes p =
      subs-μ (subscribeE⇓-total (rec (ltS p)) (unfoldμ body)
                (≤-refl , ≤-trans (unfoldμ-no-deeper body) (proj₂ ok))
                κ id now sched st)
subscribeE⇓-total ac (varᵉ ()) ok κ id now sched st
subscribeE⇓-total ac (deferᵉ body) ok κ id now sched st =
  subs-defer refl refl refl

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
  eval-run (subscribeE⇓-total {lo = n} (rootWitness e ins) e
              (≤-refl , m≤m⊔n _ _) root 0 0
              (sched-init e ins) (st-init e))
           (drain⇓-total fuel 1 _ _)

-- AND WHAT USED TO SIT BELOW THIS IS NOT A WEAKER THEOREM, IT IS NO
-- THEOREM AT ALL, WHICH IS WHAT THE WHOLE TIER WAS FOR.  The claim was
-- that the run emits no dry marker, and it was proven by induction over
-- the relation: dryness of an output is a fact about which emits the
-- constructors BUILD, and none of them builds that one.  The induction
-- was sound and its conclusion is now unstateable, because the emit it
-- quantified over cannot be written — the clause that built it, the
-- burst helper it went through and the predicate that read it are all
-- out of `Rx.Evaluator`.  A predicate with no inhabitant to exclude is
-- not a fact about the run; the deletion is the fact about the run.
--
-- SO THE TOP LINE IS THE TOTALITY CLAIM ABOVE, AND THAT IS A STRICTLY
-- LARGER STATEMENT THAN THE ONE IT REPLACES.  `evaluate⇓-total` says
-- every run is a derivation — which subsumes every claim of the form
-- "the run does not emit X" for every X no constructor builds, the
-- marker included, without any of them being stated.  What it costs is
-- that `evaluate` is no longer accepted on its own: the three edges it
-- descends on are `Rx.Evaluator.Doorless`'s facts, and the obligation
-- to spend them is this tower's.
--
-- DEAD ROUTE: keeping the predicate and proving it `false` of every
--   run, so that the theorem's STATEMENT survives the cutover.  It
--   needs the marker's constructor kept in the evaluator to be
--   mentionable at all, so the arm stays reachable and the refutation
--   that reaches it stays green — the statement is preserved by
--   preserving exactly the thing that makes it false.
