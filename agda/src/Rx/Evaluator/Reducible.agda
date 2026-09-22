------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS.
------------------------------------------------------------------

-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- expression to its subscription derivation may not mention that
-- derivation's own type in a negative position, so the candidate
-- cannot be an inductive family over the domain relation.  Defined by
-- recursion on `Ty` it never needs to be: `Red (obs u)` mentions
-- `Red u` at a strictly smaller type and `subscribeE⇓` only
-- positively.
--
-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the carrier as a plain index with no precondition, so the
-- candidate can demand subscribability in EVERY state -- which is what
-- lets a flattener's hop subscribe its inner in whatever state the
-- outer delivery reached, with nothing about the store to re-establish
-- first.  What IS threaded is a predicate the arm never looks inside:
-- it comes in, every write the arm makes is above the floor it was
-- given, and it goes back out.
--
-- AND THE ENVIRONMENT IS CARRIED RATHER THAN SUBSTITUTED, WHICH IS
-- WHAT MAKES THE WHOLE SUBSTITUTION LAYER UNNECESSARY.  An observable
-- value IS a body paired with the environment it closed over, so the
-- expression face concludes about that pair directly and no lemma
-- relating a peel to a substitution is owed anywhere.
module Rx.Evaluator.Reducible where

open import Data.Bool using (Bool; true; false; if_then_else_; T; _∧_)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; _+_; _<ᵇ_)
open import Data.Nat.Induction using (<-wellFounded)
open import Data.Nat.Properties using (_<?_; ≮⇒≥; ≤-refl; ≤-trans; m≤n+m; m≤m+n; <ᵇ⇒<)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim using (Tick; PlainEvent; valueᵖ; completeᵖ; hot; cold)
open import Rx.Slots using (scripted; shared)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ; obs; _≟ᵗ_;
  Ctx; Closed; Val; Exp; Tm; FnClo; applyClo; Env; []ᵉ; _∷ᵉ_; evalWith; foldVals;
  lookupEnv; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ;
  mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  isData; unfoldμ;
  varᵗ; unit̂; bool̂; nat̂; nilᵗ; consᵗ; foldᵗ; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ;
  caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ; eqᵘ; ltᵖ; notᵖ;
  inputsBelowᵉ; inputsBelowᵗ; inputsBelowᵗˢ)
open import Rx.Exp.Guarded using (gsizeᵉ; gsizeᵗ; gsizeᵗˢ; gsize-unfoldμ)
open import Rx.Inputs-Below using (ib-unfoldμ; ib-topᵉ)
open import Rx.Mint using (nodeᵏ; regᵏ; sourceᵏ; freshId; setAt)
open import Decide using (∧ˡ; ∧ʳ)
open import Rx.Evaluator using (Stream; Burst; Sched; EvalSt; Path; Frame; _↠[_]_;
  W; Pushed; Subbed; schW; stW; allDone; batchTake; batchStep;
  map-f; take-f; scan-f; batchSync-f; from-inner; thru-outer; share-sink;
  mergeAllᵒ; switchᵒ; exhaustᵒ; AllOp; NodeId; NodeState;
  cell-st; take-st; batchSync-st; mergeAll-st; switch-st; exhaust-st;
  takeVals; takeDispatch; scanVals; scanDispatch; batchVals;
  lookupNode; installNode; oneShotBurst; spentBurst; memberSource;
  splitEvents; splitBurst; consumeUsable; hasRoom; switchKill; thruWrap;
  register; atSlot; lowerFloor; burstCompleted)
open import Rx.Evaluator.Freshness using (lookup-set; PreservedBelow; nodeCt)
open import Rx.Evaluator.Freshness.Preserve using (subscribeE-preserves)
open import Rx.Evaluator.Domain using (subscribeE⇓; pushAll⇓; pushVals⇓; foldPath⇓;
  stepFrame⇓;
  step-map; step-scan; step-take; step-batchSync; push-nil; push-cons;
  subs-of; subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan;
  subs-batchSync; subs-mint; subs-defer; subs-floor; subs-hot-done; subs-hot-live;
  subs-cold-sync; subs-cold-async; subs-μ; sub-all; subs-merge-all;
  subs-switch-all; subs-exhaust-all; thruConsume⇓; thruWalk⇓;
  step-thru-outer; inner; consume-all-sub; consume-all-enqueue; consume-all-nil;
  consume-switch-sub; consume-switch-nil; consume-exhaust-sub; consume-exhaust-nil;
  walk-nil; walk-cons; subs-shared; slot-spent; slot-join; slot-connect;
  connect-live; connect-died)

-- A PLAIN EVENT CARRIES A PAYLOAD ONLY IN ITS VALUE ARM; the end
-- carries none and so constrains nothing.
EvSat : ∀ {A : Set} → (A → Set) → PlainEvent A → Set
EvSat P (valueᵖ v) = P v
EvSat P completeᵖ  = ⊤

-- …and a STREAM satisfies a predicate when every value any of its
-- bursts ever carries does.  Taking the predicate as a parameter is
-- what keeps `Red`'s recursion structural: the recursive occurrence is
-- `Red u` applied at a strictly smaller type, not a call at the type
-- being defined.
StreamSat : ∀ {A : Set} → (A → Set) → List (List (PlainEvent A)) → Set
StreamSat P = All (All (EvSat P))

-- A STATE PREDICATE, AND THE ONLY REASON IT IS SPELLED OUT RATHER THAN
-- WRITTEN INLINE: it ranges over every root the candidate might be
-- asked about, because the candidate's own arm quantifies over those.
StPred : ∀ {n} → Ctx n → Set₁
StPred Γ = ∀ {t} {e : Closed Γ t} → EvalSt e → Set

-- WHAT A STATE PREDICATE OWES, AND IT IS ONE THING.  Everything the
-- candidate's arms write outside a sink is written at a node they have
-- just minted, so a predicate about nodes minted EARLIER survives all
-- of it; the freshness face already concludes exactly that, in exactly
-- this vocabulary, so the hypothesis is discharged at every call site
-- by a lemma rather than by an argument.
Stable : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → ℕ → (EvalSt e → Set) → Set
Stable {e = e} φ Q =
  ∀ {st st′ : EvalSt e} → PreservedBelow φ st st′ → Q st → Q st′

-- ONE PUSH INTO A PATH, WHICH IS WHAT A SUBSCRIPTION IS NOW HANDED
-- INSTEAD OF A LIST TO HAND BACK.  The fold is the unit rather than the
-- emission, because that is the granularity the relation's own step
-- arm works at: a frame is stepped once per fold, and a sink for a
-- longer path is the shorter one with a step in front of it.
Sink : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
     → (Val Γ u → Set) → (EvalSt e → Set) → Path Γ lo u t → Set
Sink {Γ = Γ} {e = e} {u = u} P Q κ =
  ∀ (now : Tick) {vals : List (Val Γ u)} → All P vals
  → (fin : Bool) (w : W e) → Q (stW w)
  → Σ (Pushed e) λ r → foldPath⇓ {e = e} now κ vals fin w r × Q (stW (proj₂ r))

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the pair
-- the whole argument turns on -- a subscription derivation in every
-- state, and the guarantee that everything that derivation emits is
-- itself reducible at the element type.
Red : ∀ {n} {Γ : Ctx n} → StPred Γ → (t : Ty) → Val Γ t → Set
Red Q unitᵗ     _        = ⊤
Red Q boolᵗ     _        = ⊤
Red Q natᵗ      _        = ⊤
Red Q uniqᵗ     _        = ⊤
Red Q (s ×ᵗ t)  (a , b)  = Red Q s a × Red Q t b
Red Q (s +ᵗ t)  (inj₁ a) = Red Q s a
Red Q (s +ᵗ t)  (inj₂ b) = Red Q t b
Red Q (listᵗ t) vs       = All (Red Q t) vs
Red {Γ = Γ} Q (obs u) b =
  ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (φ : ℕ)
  → Stable {e = e} φ Q
  → Sink {e = e} (Red Q u) Q κ
  → (now : Tick) (w : W e) → φ ≤ nodeCt (schW w) → Q (stW w)
  → Σ (Subbed e) λ r → subscribeE⇓ {e = e} b κ now w r × Q (stW (proj₂ r))

-- WHAT A PUSHING CARRIER DOES TO THIS STATEMENT, AND THE CHEAP HALF IS
-- THE VISIBLE ONE.  A subscription that pushes emits at the ROOT type,
-- so there is no element-typed column left to conclude anything about
-- and the satisfaction half has nowhere to live.  It moves onto the
-- PATH: the arm takes a fold-builder for the path it is handed, which
-- is the same obligation read from the other end, and every arm that
-- used to split a returned burst instead extends that builder by one
-- frame.  None of that is a research question.

-- THE EXPENSIVE HALF IS THE STORE, AND IT IS WHERE THE CARRIER CHANGE
-- LANDS.  Under a push the subscribe cycle REACHES the fold, and the
-- fold reaches a flattener's drain -- so a parked inner is taken back
-- out of the store inside the very subscribe call that parked it, and
-- the candidate at that inner is APPLIED to build its subscription
-- rather than carried alongside one.  Under a batching carrier the
-- drain hung off a completion the caller delivered after the subscribe
-- had returned, which is why it sat below this module and cost nothing.
--
-- AND TWO SIBLING OBLIGATIONS ARE NOT THE SAME COST, WHICH IS WORTH
-- SAYING BEFORE EITHER IS PRICED.  A fold's cell and a bracket's buffer
-- are read back inside a subscribe for the same reason the queue is,
-- but what they produce is a CLAIM about a list some total function has
-- already computed.  The evaluator is a projection of this proof, so a
-- stuck claim on a computed list leaves the run computing and a stuck
-- subscription does not.
--
-- DEAD ROUTE: a leaf for the queue's own obligation.  It typechecks and
--   it stops the evaluator running, which is the one thing the
--   differential harness measures -- the applied side of the candidate
--   is where the run's values come from.
--
-- DEAD ROUTE: reaching for the fundamental theorem at VALUES.  It is
--   total and it settles every store read in one call, which is exactly
--   what it does for the arrival spine today.  Under a push it is a
--   MEMBER of the cycle it would be answering -- the fold reaches it and
--   it reaches the fold -- and the value it is asked about came out of a
--   store rather than out of a subterm, so nothing descends.
--
-- DEAD ROUTE: an invariant on the store written into this recursion.
--   The arm recurses on the element type; a store predicate reaches the
--   candidate at whatever type a node happens to hold, which stands in
--   no relation to it, so the recursion is not structural.  Leaving the
--   predicate ABSTRACT does not save it either: the proof needs it
--   STABLE under writes to nodes the abstraction hides, and an abstract
--   predicate grants no stability.  Requiring stability as a side
--   hypothesis is the same statement one layer out.
--
-- DEAD ROUTE: moving the fan-out OUT of the subscribe cycle, so that the
--   arm never reaches the registry at all.  Measured in the pushing
--   reference rather than argued: a flattener reads its own completion
--   at the moment its subscribe RETURNS, so a fan-out queued past that
--   point arrives at a node that has already declared itself finished
--   and its values are dropped.  That is the burst carrier's own defect
--   reintroduced by another door, and deferring the completion with it
--   is the carrier question over again.
--
-- DEAD ROUTE: a registry invariant mutually recursive with this
--   candidate.  Its calls land at whatever types the registry happens
--   to hold, which no measure orders against the type this recursion
--   runs on.  Making the candidate INDUCTIVE rather than a recursion
--   does not save it either: the invariant would stand in a hypothesis,
--   so the occurrence is negative.

-- AND THE REGISTRY OBLIGATION IS BORN AND SPENT INSIDE ONE CALL, WHICH
-- IS WHY IT NEED NOT BE IN THIS STATEMENT AT ALL.  A sink exists only as
-- the root-ward path of a slot's DEF, a def is subscribed only where the
-- slot is connected, and a slot connects once -- so a fan-out reached
-- from inside a subscribe fires only while that slot's own connect is on
-- the stack, and the rows it admits are the ones that same cascade
-- registered.  Nothing older can be there to push to.  The obligation is
-- therefore generated at each registration, where the registering
-- subscribe still holds the candidate for the path it is registering,
-- and consumed at the dispatch a few frames later; it is an invariant of
-- the CONSTRUCTION rather than of the store, so it is carried by the
-- proof and not by the type.  What that leaves open is a MEASURE for the
-- cycle the dispatch closes, which is a different question from whether
-- the arm can be written down.

-- THE FLATTENER'S HALF COSTS NOTHING AND THE SHARE'S IS THE WHOLE
-- QUESTION, WHICH IS NOT HOW IT LOOKED FROM THE STATEMENT.  A merge's
-- queue holds values at the type this arm is already recursing through,
-- so the conjunct saying they are reducible is ordinary structural
-- recursion and lands in `Set` beside every other arm -- no level, and
-- no predicate quantified inside the arm.  A SHARE's sink is the one
-- that does not: it pushes into paths read out of the REGISTRY, and a
-- frame along one of those stands at a type the arm never names, so an
-- invariant covering them reaches the candidate at types standing in no
-- relation to the one being recursed on.  A fold's cell is the same
-- shape read at a different node, and both are paid the same way.

-- AND THE FOLD'S CELL IS WHAT IS LEFT, WHICH IS A STATE OBLIGATION THE
-- SINK ITSELF CREATES.  A fold reads its accumulator back out of a node
-- and emits it, so its sink can only hand reducible values on if that
-- node already holds one.  Under a carrier that handed a finished list
-- back, the node was written AFTER the source's subscription had
-- returned, so the obligation was re-established at one state by a
-- preservation argument and never questioned in between.  Under a push
-- the writes are interleaved with the subscription that provokes them,
-- and the only writer of that node is the sink -- so what the sink owes
-- is not a fact about a state but a fact it carries THROUGH the
-- subscription it is passed into.
--
-- AND NO KNOWN SHAPE CARRIES IT, WHICH IS A FACT ABOUT THE CARRIER AND
-- NOT ABOUT THIS MODULE.  Every route tried reaches the same wall from a
-- different side: the obligation names the candidate at the accumulator
-- type of a fold on a QUANTIFIED path, so it stands in no relation to
-- the type this recursion runs on.  The six are recorded below because
-- each looks like the obvious repair for the one before it, and the last
-- is the one the other four were waiting on.
--
-- THE CARRIER IS NOT NEGOTIABLE, AND THAT IS A MEASUREMENT RATHER THAN
-- AN ARGUMENT.  The push is what the semantics IS: a share's subscriber
-- set has to be re-read BETWEEN two values of one synchronous emission,
-- because a flattener subscribed by the first must receive the second.
-- A batching carrier reads it once per emission and cannot.  So the
-- statement this module is trying to prove is a statement about a
-- subscribe cycle that re-enters, and the routes below are the price of
-- that rather than a sign that the carrier is wrong.
--
-- AND WHAT A REPAIR HAS TO ADD IS AN INDEX, WHICH IS WHY NONE OF THE SIX
-- IS IT.  Two weakenings read as the repair and neither is one.  Stop
-- re-establishing the predicate in the conclusion and the candidate is
-- contravariant, which is the direction a fold wants -- but a sink is a
-- HYPOTHESIS that names the predicate, so the negative occurrence there
-- is a positive one here and the mix survives.  Drop the predicate
-- instead and the sink has no precondition to stand on, since the frames
-- it steps read the very cells in question.  The statement is therefore
-- one that ASSUMES a store fact and RE-ESTABLISHES it while the fact
-- names the candidate, and the shape that makes that well-founded is an
-- index: what comes out sits one below what went in.
--
-- DEAD ROUTE: quantifying the predicate inside the arm.  It is
--   IMPREDICATIVE and no level assignment repairs it: the predicate that
--   gets instantiated says a stored value is reducible, so it lives one
--   level above the candidate, while quantifying over it puts the
--   candidate one level above it.
--
-- DEAD ROUTE: taking the predicate as a PARAMETER of the candidate, so
--   that every recursive occurrence is at the same one and the caller
--   instantiates.  It is predicative and it is still refuted, by the arm
--   that would do the instantiating: a fold subscribes its body at the
--   predicate it was handed CONJOINED with its own cell's obligation, so
--   it needs the body's candidate at the strengthened predicate while the
--   environment in hand carries the candidate at the weaker one.  No
--   transport exists in either direction -- the predicate stands in the
--   observable arm at BOTH signs, as what a sink may assume and as what
--   the subscription must re-establish -- so an implication between the
--   two predicates moves nothing.
--
-- DEAD ROUTE: strengthening the induction hypothesis to hold at EVERY
--   predicate, which is the repair the transport failure asks for.  It
--   is the first route again one step out: a candidate quantified over
--   state predicates lives above them, and the predicate a fold
--   instantiates at is the one naming the candidate.
--
-- DEAD ROUTE: a STRUCTURAL candidate at values -- reducibility of a
--   closure read as reducibility of its environment, which is a
--   recursion on the value and so needs no predicate at all.  The store
--   obligation lands in it cleanly and the flattener's hop does not:
--   subscribing an arriving observable is exactly what a structural
--   reading cannot supply, and recovering it is the fundamental theorem
--   at an expression drawn from a store rather than from a subterm.
--
-- DEAD ROUTE: indexing the candidate by the root program instead of by
--   a predicate, on the reading that every observable value a run builds
--   is a `strmᵗ` body drawn from a finite set fixed before the run.  The
--   reading is false and `Refuted.Domain-Predicate` says why in one
--   line: a fold's output is built by SUBSTITUTION into a template, so
--   the arriving observable is an instance of a subterm and not a
--   subterm, related to nothing in hand structurally or numerically.  It
--   is the same wall a numeric rank hit, which is the point -- how the
--   descent is denominated was never what was missing.
--
-- DEAD ROUTE: a carrier that does not re-enter a fold's own frame, so
--   that none of the four is needed.  Refuted by measurement rather than
--   by descent: across a 500-case draw a batching carrier is wrong on
--   exactly the rows that read one shared slot as BOTH a flattener's
--   outer and its inner, never with a wrong value or a wrong order and
--   always with no output at all, while the pushing one is right on
--   every row.  Deferring the subscribe into a queue does remove the
--   re-entrancy, and it reorders the output: an inner's synchronous
--   values precede the outer's next value, so a stack that keeps that
--   order interleaves the writes exactly as the inline push does.

-- THE SAME CARRIER REFUTES THE FRESHNESS FACE'S UNCONDITIONAL FORM, and
-- the two findings are one fact read from two ends.  A subscription now
-- STEPS the frames of its own continuation, so it writes the nodes
-- those frames name, and `subscribeE-preserves` without a premise about
-- the path is false at exactly the fold this arm is about.  The premise
-- it gains is the one its frame-level members already carry.

-- A SPENT SOURCE'S BURST is an end and nothing else, so every
-- predicate holds of it for want of anything to hold of.
StreamSat-spent : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                → StreamSat P (spentBurst {Γ = Γ} {u = u})
StreamSat-spent = (tt ∷ []) ∷ []

-- A MAPPING FRAME APPLIES ITS CLOSURE TO EVERY ARRIVING VALUE, so what
-- it produces is reducible exactly when the closure sends reducible to
-- reducible.  That is the only thing a frame wants from the term face,
-- and it has to be stated as a HYPOTHESIS rather than reached by a
-- call: the fundamental theorem at terms is a member of the recursion
-- at the foot of this module, so a walk declared above it cannot name
-- it.
RedFn : ∀ {n} {Γ : Ctx n} → StPred Γ → ∀ {s u} → FnClo Γ s u → Set
RedFn {Γ = Γ} Q {s = s} {u = u} fn =
  ∀ {v : Val Γ s} → Red Q s v → Red Q u (applyClo fn v)

-- WHAT A FRAME'S OWN NODE MUST HOLD, AND THREE FRAMES ASK.  The node
-- census says the rest read a store carrying no payload -- a count, a
-- flag, an identifier -- so their obligation is the trivial one and
-- costs a `tt` at every site.  The other three hold VALUES that leave
-- the frame again: a fold's cell, a merge's queue of the arrivals it
-- refused, and a bracket's buffer of the group it is still filling.
-- Under a push all three are read back inside the very subscribe that
-- wrote them, because a completion now arrives before the subscribe has
-- returned; a carrier handing a finished list back read them only
-- afterwards, which is why two of these arms used to be trivial.
--
-- AND THEY ARE NOT THE SAME COST, WHICH THE STATEMENT SHOWS.  The queue
-- and the buffer hold values at the type the sink extending that frame
-- is already carrying a candidate for, so their conjuncts are
-- discharged from what the arm has in hand.  The cell holds a value at
-- the frame's OUTPUT type, which stands in no relation to anything the
-- sink names -- so it is the one with nowhere to be carried, and the
-- refutations above are all about it.  The three arms are stated
-- together anyway because the split is the finding: it says the cost is
-- the fold's alone, not the carrier's across the board.
-- DEAD ROUTE: carrying this in the STATE RECORD instead, as a field
--   beside the nodes.  It closes a definitional cycle rather than an
--   import cycle: the candidate's observable arm is indexed by the
--   subscription relation, which is itself indexed by the state
--   record, so a field of that record naming the candidate is
--   circular however the modules are cut.  Parameterising the state
--   record over an abstract node predicate is that same cycle
--   DEFERRED -- the instantiation ties the knot, and the executable
--   face pays a threaded parameter it only ever meets at the trivial
--   predicate.  And a SYNTACTIC invariant saying a stored value is the
--   denotation of a closed term is VACUOUS: reflection is total, so
--   every value is one and the pairing carries no information.

-- AND IT NAMES A SINGLE NODE RATHER THAN THE TABLE, WHICH IS WHAT
-- SURVIVES THE REFUTATIONS ABOVE.  The fold's arm knows the identifier
-- it just minted; an obligation about the whole table would oblige every
-- other writer for nothing, and it is the writes by OTHERS that have to
-- pass through untouched.  Whatever carries the fold's cell will be
-- stated at one node for that reason.
RedNode : ∀ {n} {Γ : Ctx n} → StPred Γ → ∀ {t} {e : Closed Γ t} {s u}
        → Frame Γ s u → EvalSt e → Set
RedNode {Γ = Γ} Q (scan-f fn nid) st =
  ∀ {w} {a : Val Γ w}
  → lookupNode nid (EvalSt.nodes st) ≡ just (cell-st a) → Red Q w a
RedNode {Γ = Γ} Q (thru-outer op nid) st =
  ∀ {v : Ty} {lim act od} {q : List (Val Γ (obs v))}
  → lookupNode nid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od)
  → All (Red Q (obs v)) q
RedNode {Γ = Γ} Q (batchSync-f nid) st =
  ∀ {v : Ty} {sync} {buf : List (Val Γ v)}
  → lookupNode nid (EvalSt.nodes st) ≡ just (batchSync-st sync buf)
  → All (Red Q v) buf
RedNode Q (map-f fn)                  st = ⊤
RedNode Q (take-f nid)                st = ⊤
RedNode Q (from-inner op allNid inst) st = ⊤

-- A VALUE ENVIRONMENT IS REDUCIBLE WHEN EVERY ENTRY IS.  Terms are
-- open in a Θ telescope and a frame's closure pairs a term with one
-- such environment, so the fundamental theorem at terms has to be
-- stated under an environment rather than at closed terms alone.
RedEnv : ∀ {n} {Γ : Ctx n} → StPred Γ → ∀ {Θ : List Ty} → Env Γ Θ → Set
RedEnv Q []ᵉ                  = ⊤
RedEnv Q (_∷ᵉ_ {s = t} v vs)  = Red Q t v × RedEnv Q vs

-- ONE FRAME STEPPED: what arrived at it, and the candidate carried
-- across to what leaves.  This is where a frame's own node is both
-- SPENT and RE-ESTABLISHED, which is the shape that lets a sink built
-- over this step hand its caller the predicate back -- the one place
-- in the module that has to say anything about a store at all.
RedStep : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s u lo}
        → Tick → Frame Γ s u → Path Γ lo u t
        → List (Val Γ s) → Bool → W e → Set
RedStep {Γ = Γ} Q {e = e} {u = u} now f κ vals fin w =
  Σ (List (Val Γ u) × Bool × Bool × W e) λ r →
    stepFrame⇓ {e = e} now f κ vals fin w r × All (Red Q u) (proj₁ r)
      × RedNode Q f (stW (proj₂ (proj₂ (proj₂ r))))

-- A SPLIT TAKES THE VALUE COLUMN OUT OF A BURST, and nothing else, so
-- whatever held of every value the burst carried holds of every value
-- the split hands back.  The end carries no payload, so it simply
-- leaves the column.
satSplitEvents : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                 (es : Burst Γ u) → All (EvSat P) es
               → All P (proj₁ (splitEvents es))
satSplitEvents []               []       = []
satSplitEvents (valueᵖ _ ∷ es)  (p ∷ ps) = p ∷ satSplitEvents es ps
satSplitEvents (completeᵖ ∷ es) (_ ∷ ps) = satSplitEvents es ps

satSplitBurst : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set}
                (str : Stream Γ u) → StreamSat P str
              → All P (proj₁ (splitBurst str))
satSplitBurst []         []       = []
satSplitBurst (b ∷ bs) (q ∷ qs) =
  ++⁺ (satSplitEvents b q) (satSplitBurst bs qs)

-- AND THE WRAP AROUND THE WALK NEVER TOUCHES THAT COLUMN.  What it
-- decides is whether the operator is finished and what its node then
-- holds, both of which the candidate is silent about; the values pass
-- through every arm unchanged.  Spelling the arms out is the price of
-- the machine reading its own store: a catch-all in the definition
-- does not reduce against a catch-all in a proof.
thruWrap-vals : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
                (op : AllOp) (nid : NodeId) (fin : Bool)
                {vs : List (Val Γ u)}
                {sched′ : Sched Γ} {st′ : EvalSt e}
              → proj₁ (thruWrap {e = e} op nid fin (vs , sched′ , st′)) ≡ vs
thruWrap-vals mergeAllᵒ nid false = refl
thruWrap-vals switchᵒ   nid false = refl
thruWrap-vals exhaustᵒ  nid false = refl
thruWrap-vals mergeAllᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals switchᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
thruWrap-vals exhaustᵒ nid true {st′ = st′}
  with lookupNode nid (EvalSt.nodes st′)
... | nothing                    = refl
... | just (cell-st _)           = refl
... | just (take-st _)           = refl
... | just (batchSync-st _)      = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl

-- CONSUMING ONE ARRIVING OBSERVABLE, and walking a list of them.
-- These are the flattener's two halves of `RedStep`, stated separately
-- for the same reason the machine states them separately: what a
-- consume decides is whether the observable is taken at all, and every
-- operator answers that off the store.
--
-- AND NEITHER CARRIES A VALUE COLUMN ANY MORE, which is the carrier
-- paying off where it was expected to cost.  An inner's values reach
-- the root down the inner's OWN path, so a consume hands its caller a
-- state and nothing else, and the satisfaction half that used to be
-- stated here is discharged where the inner is subscribed instead.
-- What is left to carry is the state predicate, which every arm passes
-- through untouched.
RedConsume : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {u lo}
           → AllOp → NodeId → Path Γ lo u t → Tick
           → Val Γ (obs u) → W e → Set
RedConsume {Γ = Γ} Q {e = e} {u = u} op nid κ now o w =
  Σ (W e) λ w′ → thruConsume⇓ {e = e} op nid κ now o w w′ × Q (stW w′)

RedWalk : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {u lo}
        → AllOp → NodeId → Path Γ lo u t → Tick
        → List (Val Γ (obs u)) → W e → Set
RedWalk {Γ = Γ} Q {e = e} {u = u} op nid κ now vals w =
  Σ (W e) λ w′ → thruWalk⇓ {e = e} op nid κ now vals w w′ × Q (stW w′)

-- THE HOP IS PAID FOR BY THE ARRIVING VALUE'S OWN CANDIDATE, which is
-- what makes this a body rather than a leaf.  A subscribe arm hands
-- the observable down at a `from-inner` frame and subscribes it there;
-- the candidate quantifies over every carrier, so the freshly-counted
-- schedule this arm builds is one of them by construction and no
-- invariant is threaded.  Every OTHER arm subscribes nothing at all --
-- a refused arrival is queued, an unusable store collapses -- so the
-- state it hands back is the one it was given and the predicate rides
-- through.
--
-- AND THE INNER NEEDS A SINK OF ITS OWN, which is what the extra
-- argument is: an inner emits down its own path and that path is this
-- one with the operator's frame in front, so the hop can only be taken
-- by something already holding the sink for the path below.
red-consume : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {u lo}
              (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t) (φ : ℕ)
            → Stable {e = e} φ Q
            → Sink {e = e} (Red Q u) Q κ
            → (now : Tick) {o : Val Γ (obs u)} → Red Q (obs u) o
            → (w : W e) → φ ≤ nodeCt (schW w) → Q (stW w)
            → RedConsume Q {e = e} op nid κ now o w
red-consume {u = u} mergeAllᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (switch-st _ _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (exhaust-st _ _) =
      _ , consume-all-nil (cong (consumeUsable mergeAllᵒ u) eq) , []
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u in eqw
...   | no _ =
        _ , consume-all-nil
              (trans (cong (consumeUsable mergeAllᵒ u) eq) (cong ⌊_⌋ eqw)) , []
...   | yes refl with hasRoom lim act in eqr
...     | false = _ , consume-all-enqueue eq eqr , []
...     | true =
          let ((burst , _ , _) , d , ss) =
                ro (from-inner mergeAllᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠[ ≤-refl ] κ) now
                   (record sched
                      { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched)))
                                 (Sched.mint sched) })
                   st
          in _ , consume-all-sub eq eqr (inner refl d refl)
               , satSplitBurst burst ss

red-consume {u = u} switchᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (exhaust-st _ _) =
      _ , consume-switch-nil (cong (consumeUsable switchᵒ u) eq) , []
... | just (switch-st cur od) with switchKill cur sched st in eqk
...   | (sched₁ , st₁) =
        let ((burst , _ , _) , d , ss) =
              ro (from-inner switchᵒ nid (freshId nodeᵏ (Sched.mint sched₁)) ↠[ ≤-refl ] κ) now
                 (record sched₁
                    { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched₁)))
                               (Sched.mint sched₁) })
                 st₁
        in _ , consume-switch-sub eq eqk (inner refl d refl)
             , satSplitBurst burst ss

red-consume {u = u} exhaustᵒ nid κ now ro sched st
  with lookupNode nid (EvalSt.nodes st) in eq
... | nothing =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (cell-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (take-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (batchSync-st _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (mergeAll-st _ _ _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (switch-st _ _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st true _) =
      _ , consume-exhaust-nil (cong (consumeUsable exhaustᵒ u) eq) , []
... | just (exhaust-st false od) =
      let ((burst , _ , _) , d , ss) =
            ro (from-inner exhaustᵒ nid (freshId nodeᵏ (Sched.mint sched)) ↠[ ≤-refl ] κ) now
               (record sched
                  { mint = setAt nodeᵏ (suc (freshId nodeᵏ (Sched.mint sched)))
                             (Sched.mint sched) })
               st
      in _ , consume-exhaust-sub eq (inner refl d refl)
           , satSplitBurst burst ss

-- THE WALK IS THE CONSUME THREADED, and the column it returns is the
-- concatenation of the columns each arrival produced.
red-walk : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {u lo}
           (op : AllOp) (nid : NodeId) (κ : Path Γ lo u t) (φ : ℕ)
         → Stable {e = e} φ Q
         → Sink {e = e} (Red Q u) Q κ
         → φ ≤ nid
         → (now : Tick) {vals : List (Val Γ (obs u))}
         → All (Red Q (obs u)) vals
         → (w : W e) → φ ≤ nodeCt (schW w) → Q (stW w)
         → RedWalk Q {e = e} op nid κ now vals w

-- THE FLATTENING WALK, AND THE NODE IT READS OWES NOTHING.  Every
-- value it produces is an inner subscribed out of the arriving batch,
-- and the census at `NodeState` says the nodes it consults carry no
-- payload to confuse that -- so this frame's node obligation is the
-- trivial one and the whole content is the value column.
--
-- AND THE QUEUE IT PUSHES INTO IS READ BACK BEFORE THIS CALL RETURNS,
-- WHICH IS THE CARRIER AND NOT THE OPERATOR.  A refused arrival is
-- enqueued and the read is the DRAIN, which hangs off an inner's
-- completion -- and a completion now arrives while the subscribe that
-- provoked it is still on the stack.  So the entry this face stores is
-- one it has to be able to take out again, and the obligation is on the
-- node rather than on the caller.  What makes it cheap is the TYPE: the
-- queue holds observables at the element type this frame is already
-- carrying a candidate for.
red-thru : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {u lo}
           (now : Tick) (op : AllOp) (nid : NodeId)
           (κ : Path Γ lo u t) (φ : ℕ)
         → Stable {e = e} φ Q
         → Sink {e = e} (Red Q u) Q κ
         → φ ≤ nid
         → {vals : List (Val Γ (obs u))} → All (Red Q (obs u)) vals → (fin : Bool)
         → (w : W e) → φ ≤ nodeCt (schW w) → Q (stW w)
         → RedStep Q {e = e} now (thru-outer op nid) κ vals fin w

-- The end carries no payload, so a burst's values are the only thing
-- to check and a burst with none is satisfied outright.
satEvents : ∀ {A : Set} {P : A → Set} {vals : List A} {rest : List (PlainEvent A)}
          → All P vals → All (EvSat P) rest
          → All (EvSat P) (map valueᵖ vals ++ rest)
satEvents []       ar = ar
satEvents (p ∷ ps) ar = p ∷ satEvents ps ar

satOneShot : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} {vals}
           → All P vals → StreamSat P (oneShotBurst {Γ = Γ} {u = u} vals)
satOneShot ps = satEvents ps (tt ∷ []) ∷ []

-- EVERY VALUE OF A DATA TYPE IS REDUCIBLE, AND THAT IS WHY THE SLOT
-- ARM IS SHORT.  The candidate is trivial at each data former and
-- uninhabitable at `obs`, so the recursion here is the same one `Red`
-- itself runs -- it just has to be SAID, because a slot's element type
-- is `lookup Γ i` and no reduction fires on a neutral index.  What
-- carries it is the side condition every scripted slot already holds.
-- THE PRODUCT AND SUM ARMS OF `isData` GUARD ON THE LEFT FACTOR, so
-- the witness has to be taken apart before either side can be used.
-- It sits ABOVE rather than between the signature and the clauses
-- because a declaration placed there would join the block below: the
-- dev loop stubs a multi-member block, so keeping these out of one is
-- what keeps them checked for real, termination included.
T-if : ∀ (b c : Bool) → T (if b then c else false) → T b × T c
T-if true  c ok = tt , ok
T-if false c ()

red-data : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) (u : Ty) → T (isData u) → (v : Val Γ u)
         → Red {Γ = Γ} Q u v
redDatas : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) (u : Ty) → T (isData u) → (vs : List (Val Γ u))
         → All (Red {Γ = Γ} Q u) vs

red-data Q unitᵗ    _  _       = tt
red-data Q natᵗ     _  _       = tt
red-data Q boolᵗ    _  _       = tt
red-data Q uniqᵗ    _  _       = tt
red-data Q (listᵗ u) ok vs     = redDatas Q u ok vs
red-data Q (s ×ᵗ t) ok (a , b) =
  let (o₁ , o₂) = T-if (isData s) (isData t) ok
  in red-data Q s o₁ a , red-data Q t o₂ b
red-data Q (s +ᵗ t) ok (inj₁ a) = red-data Q s (proj₁ (T-if (isData s) (isData t) ok)) a
red-data Q (s +ᵗ t) ok (inj₂ b) = red-data Q t (proj₂ (T-if (isData s) (isData t) ok)) b
red-data Q (obs u)  () _

redDatas Q u ok []       = []
redDatas Q u ok (v ∷ vs) = red-data Q u ok v ∷ redDatas Q u ok vs

-- The cold-with-a-tail arm emits its synchronous values with nothing
-- after them, so it wants the values alone rather than `satEvents`'
-- append.
satValues : ∀ {A : Set} {P : A → Set} {vals : List A}
          → All P vals → All (EvSat P) (map valueᵖ vals)
satValues []       = []
satValues (p ∷ ps) = p ∷ satValues ps

-- AND A FRAME OWES IT WHEREVER IT APPLIES ONE, WHICH IS TWO OF THE
-- SIX.  The mapping frame applies its closure to what arrived; the
-- fold applies its own to the pair of the stored accumulator and what
-- arrived, so it owes the same thing -- what it additionally needs,
-- the first component of that pair being reducible, is the store
-- obligation beside this one rather than anything about the closure.
RedFrame : ∀ {n} {Γ : Ctx n} → StPred Γ → ∀ {s u} → Frame Γ s u → Set
RedFrame Q (map-f fn)                  = RedFn Q fn
RedFrame Q (scan-f fn nid)             = RedFn Q fn
RedFrame Q (take-f nid)                = ⊤
RedFrame Q (batchSync-f nid)           = ⊤
RedFrame Q (from-inner op allNid inst) = ⊤
RedFrame Q (thru-outer op nid)         = ⊤

redMapVals : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {s u} (fn : FnClo Γ s u) → RedFn Q fn
           → {vals : List (Val Γ s)} → All (Red Q s) vals
           → All (Red Q u) (map (applyClo fn) vals)
redMapVals Q fn rf []       = []
redMapVals Q fn rf (p ∷ ps) = rf p ∷ redMapVals Q fn rf ps

-- A TRUNCATION CANNOT INVENT A VALUE, WHICH IS WHY THE TAKE ARM NEEDS
-- NOTHING FROM THE STORE.  The node a take installs holds a COUNT, and
-- the dispatch's value column is a prefix of the burst it was handed --
-- on the cut path and the non-cut path alike, and at a stuck lookup the
-- column is empty.  So the arriving candidates are the departing ones
-- and the store decides only HOW MANY survive.  This is the contrast
-- that pins what a fold's accumulator is actually missing: that cell
-- holds a VALUE, and no hypothesis here says anything about it.
redTakeVals : ∀ {n} {Γ : Ctx n} {s} {P : Val Γ s → Set} (k : ℕ)
              {vals : List (Val Γ s)} → All P vals
            → All P (proj₁ (takeVals k vals))
redTakeVals zero          rv        = []
redTakeVals (suc k)       []        = []
redTakeVals (suc zero)    (p ∷ ps)  = p ∷ []
redTakeVals (suc (suc k)) (p ∷ ps)  = p ∷ redTakeVals (suc k) ps

redTakeDispatch : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s}
                  (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                → All (Red Q s) vals
                → All (Red Q s)
                    (proj₁ (takeDispatch {e = e} nid vals fin sched st m))
redTakeDispatch Q nid {vals} fin sched st (just (take-st k)) rv
  with proj₂ (proj₂ (takeVals k vals))
... | true  = redTakeVals k rv
... | false = redTakeVals k rv
redTakeDispatch Q nid fin sched st (just (cell-st _))           rv = []
redTakeDispatch Q nid fin sched st (just (batchSync-st _ _))    rv = []
redTakeDispatch Q nid fin sched st (just (mergeAll-st _ _ _ _)) rv = []
redTakeDispatch Q nid fin sched st (just (switch-st _ _))       rv = []
redTakeDispatch Q nid fin sched st (just (exhaust-st _ _))      rv = []
redTakeDispatch Q nid fin sched st nothing                      rv = []

red-take : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s lo}
           (now : Tick) (nid : NodeId) (κ : Path Γ lo s t)
           {vals : List (Val Γ s)} → All (Red Q s) vals → (fin : Bool)
           (w : W e)
         → RedStep Q {e = e} now (take-f nid) κ vals fin w
red-take Q now nid κ rv fin (out , sched , st) =
  _ , step-take refl
    , redTakeDispatch Q nid fin sched st (lookupNode nid (EvalSt.nodes st)) rv
    , tt

-- THE BRACKET REGROUPS AND INVENTS NOTHING, so its whole obligation is
-- that a group's head and its tail are the arriving values they were
-- taken from.  The grouped arm is where the product arm of the
-- candidate and its list arm meet, and both halves come from the one
-- walk that arrived.
redBatchVals : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {s} (sync : Bool)
               {vals : List (Val Γ s)} → All (Red Q s) vals
             → All (Red Q (s ×ᵗ listᵗ s)) (batchVals sync vals)
redBatchVals Q sync  []       = []
redBatchVals Q true  (p ∷ ps) = (p , ps) ∷ []
redBatchVals Q false (p ∷ ps) = (p , []) ∷ redBatchVals Q false ps

-- the buffer read back is the one written, so its payload is that payload
tie-batch : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {w w′} {sync sync′}
            {xs : List (Val Γ w)} {ys : List (Val Γ w′)}
          → _≡_ {A = Maybe (NodeState Γ)}
              (just (batchSync-st sync xs)) (just (batchSync-st sync′ ys))
          → All (Red Q w) xs → All (Red Q w′) ys
tie-batch Q refl r = r

-- ONE READING OF THE BRACKET'S NODE, WHICH IS WHERE ITS BUFFER IS BOTH
-- SPENT AND REFILLED.  With the bit up nothing leaves and what arrived
-- is appended; with it down the arrivals leave as singleton groups and
-- the node is not written at all.  Either way the obligation going out
-- is the one coming in with the arrival's own candidates appended,
-- which is an append and not an argument.
redBatchStep : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s}
               (nid : NodeId) {vals : List (Val Γ s)} (fin : Bool)
               (st : EvalSt e) (m : Maybe (NodeState Γ))
             → lookupNode nid (EvalSt.nodes st) ≡ m
             → RedNode Q {e = e} (batchSync-f nid) st
             → All (Red Q s) vals
             → All (Red Q (s ×ᵗ listᵗ s))
                 (proj₁ (batchStep {e = e} nid vals fin st m))
               × RedNode Q {e = e} (batchSync-f nid)
                   (proj₂ (proj₂ (batchStep {e = e} nid vals fin st m)))
redBatchStep Q {s = s} nid {vals} fin st (just (batchSync-st {t = w} sync buf)) eq rn rv
  with w ≟ᵗ s
... | no  _    = [] , rn
... | yes refl with sync
...   | false = redBatchVals Q false rv , rn
...   | true  =
        [] , λ eq′ → tie-batch Q (trans (sym (lookup-set nid
                                                (batchSync-st true (buf ++ vals))
                                                (EvalSt.nodes st)))
                                        eq′)
                       (++⁺ (tie-batch Q eq rn) rv)
redBatchStep Q nid fin st (just (cell-st _))             eq rn rv = [] , rn
redBatchStep Q nid fin st (just (take-st _))             eq rn rv = [] , rn
redBatchStep Q nid fin st (just (mergeAll-st _ _ _ _))   eq rn rv = [] , rn
redBatchStep Q nid fin st (just (switch-st _ _))         eq rn rv = [] , rn
redBatchStep Q nid fin st (just (exhaust-st _ _))        eq rn rv = [] , rn
redBatchStep Q nid fin st nothing                        eq rn rv = [] , rn

red-batchSync : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s lo}
                (now : Tick) (nid : NodeId) (κ : Path Γ lo (s ×ᵗ listᵗ s) t)
                {vals : List (Val Γ s)} → All (Red Q s) vals → (fin : Bool)
                (w : W e) → RedNode Q {e = e} (batchSync-f nid) (stW w)
              → RedStep Q {e = e} now (batchSync-f nid) κ vals fin w
red-batchSync Q now nid κ rv fin (out , sched , st) rn =
  let (rvs , rn′) = redBatchStep Q nid fin st
                      (lookupNode nid (EvalSt.nodes st)) refl rn rv
  in _ , step-batchSync refl , rvs , rn′

-- A FOLD IS ITS ACCUMULATOR THREADED ALONG THE BATCH, and so is the
-- claim about it: each output IS the next accumulator, so one walk
-- delivers both the candidate at every emitted value and the candidate
-- at what gets written back.
redScanVals : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {s u}
              (fn : FnClo Γ (u ×ᵗ s) u) → RedFn Q fn
            → {a : Val Γ u} → Red Q u a
            → {vals : List (Val Γ s)} → All (Red Q s) vals
            → All (Red Q u) (proj₁ (scanVals fn a vals))
              × Red Q u (proj₂ (scanVals fn a vals))
redScanVals Q fn rf ra []       = [] , ra
redScanVals Q fn rf ra (p ∷ ps) =
  let (qs , last) = redScanVals Q fn rf (rf (ra , p)) ps
  in rf (ra , p) ∷ qs , last

-- the cell read back is the one written, so its payload is that payload
tie-scan : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {w w′} {x : Val Γ w} {y : Val Γ w′}
         → _≡_ {A = Maybe (NodeState Γ)} (just (cell-st x)) (just (cell-st y))
         → Red Q w x → Red Q w′ y
tie-scan Q refl r = r

-- AND THE ONE THING THE FOLD'S NODE OBLIGATION CANNOT ESTABLISH FOR
-- ITSELF: that the accumulator installed just before a subscription is
-- the one still standing when the push happens.  A node is keyed by an
-- identifier drawn from the run's own counter, the fold installs at the
-- counter's current value and subscribes with it advanced, and a
-- subscription writes no node below the counter it started at -- so the
-- accumulator is untouched for structural reasons rather than by any
-- property of the candidate.  The floor spent here is the advanced
-- counter itself, which is the tightest one the fold can offer and the
-- only one under which its own node is strictly below.
red-scan-installed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo Θ}
           (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
           {a : Val Γ u} → Red u a
         → ∀ {b : Exp Γ [] [] Θ s} {ρ : Env Γ Θ} {κ : Path Γ lo u t} {now}
         → (sched : Sched Γ) (st : EvalSt e)
         → {sched₂ : Sched Γ} {st₁ : EvalSt e} {burst : Stream Γ s}
         → subscribeE⇓ {e = e} (Θ , b , ρ) (scan-f fn nid ↠[ ≤-refl ] κ) now
             (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
             (installNode nid (cell-st a) st)
             (burst , sched₂ , st₁)
         → RedNode {e = e} (scan-f fn nid) st₁
red-scan-installed fn nid {a} ra sched st d eq =
  tie-scan (trans (sym (trans (PreservedBelow.below
                                 (subscribeE-preserves (suc nid) ≤-refl d)
                                 nid ≤-refl)
                              (lookup-set nid (cell-st a) (EvalSt.nodes st))))
                  eq)
           ra

-- ONE READING OF THE CELL, WHICH IS WHERE BOTH HALVES ARE PAID.  The
-- dispatch it mirrors branches on a lookup the goal does not mention,
-- so the reading is taken as a parameter and pinned by an equation --
-- and that equation is what lets the obligation coming IN be spent on
-- the accumulator that was found, before the obligation going OUT is
-- re-established against the accumulator that replaces it.
redScanDispatch : ∀ {n} {Γ : Ctx n} (Q : StPred Γ) {t} {e : Closed Γ t} {s u}
                  (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
                  {vals : List (Val Γ s)} (fin : Bool)
                  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ))
                → lookupNode nid (EvalSt.nodes st) ≡ m
                → RedNode Q {e = e} (scan-f fn nid) st → RedFn Q fn
                → All (Red Q s) vals
                → All (Red Q u)
                    (proj₁ (scanDispatch {e = e} fn nid vals fin sched st m))
                  × RedNode Q {e = e} (scan-f fn nid)
                      (proj₂ (proj₂ (proj₂
                        (scanDispatch {e = e} fn nid vals fin sched st m))))
redScanDispatch Q {u = u} fn nid {vals} fin sched st (just (cell-st {w} a)) eq rn rf rv
  with w ≟ᵗ u
... | no  _    = [] , rn
... | yes refl =
      let (outs , last) = redScanVals Q fn rf (rn eq) rv
      in outs , λ eq′ → tie-scan Q (trans (sym (lookup-set nid
                                      (cell-st (proj₂ (scanVals fn a vals)))
                                      (EvalSt.nodes st)))
                                    eq′)
                          last
redScanDispatch Q fn nid fin sched st nothing                      eq rn rf rv = [] , rn
redScanDispatch Q fn nid fin sched st (just (take-st _))           eq rn rf rv = [] , rn
redScanDispatch Q fn nid fin sched st (just (batchSync-st _ _))    eq rn rf rv = [] , rn
redScanDispatch Q fn nid fin sched st (just (mergeAll-st _ _ _ _)) eq rn rf rv = [] , rn
redScanDispatch Q fn nid fin sched st (just (switch-st _ _))       eq rn rf rv = [] , rn
redScanDispatch Q fn nid fin sched st (just (exhaust-st _ _))      eq rn rf rv = [] , rn

-- A SCAN READS ITS ACCUMULATOR BACK OUT OF A CELL, AND EMITS IT --
-- which is what the node obligation beside the frame's closure is for.
-- Most of the dispatch's readings write nothing and emit nothing, so
-- the obligation they hand back is the one they were given; the cell
-- folds, and there the two halves of the walk above are exactly the two
-- things owed -- the batch that leaves and the accumulator that stays.
red-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (fn : FnClo Γ (u ×ᵗ s) u) (nid : NodeId)
           (κ : Path Γ lo u t) → RedFn fn
         → {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
         → (sched : Sched Γ) (st : EvalSt e)
         → RedNode {e = e} (scan-f fn nid) st
         → RedStep {e = e} now (scan-f fn nid) κ vals fin sched st
red-scan now fn nid κ rf rv fin sched st rn =
  let (rvs , rn′) = redScanDispatch fn nid fin sched st
                       (lookupNode nid (EvalSt.nodes st)) refl rn rf rv
  in _ , step-scan , rvs , rn′

-- STEPPING ONE FRAME, DISPATCHED ON THE FRAME, AND ONLY EVER A SOURCE
-- FRAME.  The mapping arm is a body because nothing about it is
-- stateful; the others each read a node this face installed earlier,
-- which is the one thing the candidate's quantification over every
-- state does not hand back.  The inner's own frame is not answered for
-- at all: `srcFrame` says in a type that a push cycle is only entered
-- from a source former, so it arrives here never, and a leaf stated for
-- it would have been a claim about a run this face cannot reach.
red-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {vals : List (Val Γ s)} → All (Red s) vals → (fin : Bool)
           (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedStep {e = e} now f κ vals fin sched st
red-step now (map-f fn) sv rf κ rv fin sched st rn =
  _ , step-map , redMapVals fn rf rv , tt
red-step now (scan-f fn nid) sv rf κ rv fin sched st rn =
  red-scan now fn nid κ rf rv fin sched st rn
red-step now (take-f nid) sv rf κ rv fin sched st rn =
  red-take now nid κ rv fin sched st
red-step now (batchSync-f nid) sv rf κ rv fin sched st rn =
  red-batchSync now nid κ rv fin sched st
red-step now (from-inner op allNid inst) () rf κ rv fin sched st rn
red-step now (thru-outer op nid) sv rf κ rv fin sched st rn =
  red-thru now op nid κ rv fin sched st

-- a frame's completion flag becomes at most one event
satFin : ∀ {A : Set} {P : A → Set} (b : Bool)
       → All (EvSat P) (if b then completeᵖ ∷ [] else [])
satFin true  = tt ∷ []
satFin false = []

-- PUSHING A STREAM THROUGH A FRAME IS A WALK, AND THE WALK IS A BODY.
-- Each burst is split, stepped and reassembled; the candidate travels
-- on the values alone, which is why the reassembly costs one append of
-- an end and one real obligation.
red-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
           (now : Tick) (f : Frame Γ s u) → srcFrame f → RedFrame f
         → (κ : Path Γ lo u t)
           {burst : Stream Γ s} → StreamSat (Red s) burst
         → (sched : Sched Γ) (st : EvalSt e) → RedNode f st
         → RedPush {e = e} now f κ burst sched st
red-push now f sv rf κ {[]}     []       sched st rn = _ , push-nil , []
red-push now f sv rf κ {b ∷ bs} (p ∷ ps) sched st rn =
  let ((vals′ , fin′ , sched₁ , st₁) , d , rv , rn₁) =
        red-step now f sv rf κ (satSplitEvents b p)
          (proj₂ (splitEvents b)) sched st rn
      ((rest , sched₂ , st₂) , dr , sr) = red-push now f sv rf κ ps sched₁ st₁ rn₁
  in _ , push-cons refl d dr
       , satEvents rv (satFin fin′) ∷ sr

-- an entry of a reducible environment is reducible
redLookup : ∀ {n} {Γ : Ctx n} {Θ t} (ρ : Env Γ Θ) → RedEnv ρ
          → (x : t ∈ Θ) → Red t (lookupEnv ρ x)
redLookup (v ∷ᵉ vs) (p , ps) (here refl) = p
redLookup (v ∷ᵉ vs) (p , ps) (there x)   = redLookup vs ps x

-- THE LIST FOLD'S ACCUMULATOR LOOP, WITH THE STEP TAKEN AS A
-- HYPOTHESIS.  The step is one instance of the term face at an
-- environment two entries longer, and it does not vary along the list,
-- so the walk over the list is an ordinary recursion outside the
-- theorem's own cycle.
redFoldVals : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Tm Γ [] [] (s ∷ u ∷ Θ) u)
              (ρ : Env Γ Θ)
            → (∀ {x : Val Γ s} {ac : Val Γ u} → Red s x → Red u ac
                 → Red u (evalWith f (x ∷ᵉ ac ∷ᵉ ρ)))
            → {vs : List (Val Γ s)} → All (Red s) vs
            → {ac : Val Γ u} → Red u ac
            → Red u (foldVals f ρ vs ac)
redFoldVals f ρ step []       rac = rac
redFoldVals f ρ step (p ∷ ps) rac = redFoldVals f ρ step ps (step p rac)

-- THE BODY, AND WHAT PAYS FOR IT.  The expression face and the term
-- face are ONE recursion: a term embeds an expression and an operator
-- carries terms, so neither can be a leaf beside the other without
-- claiming the whole theorem.  Both recurse on the ACCESSIBILITY of
-- the guarded size, which counts an operator's spine and the terms it
-- carries and stops at the gate; every call below hands on a strictly
-- smaller size, the fixpoint arm included.
--
-- THE ONE ARM WITH NO SUBTERM IS THE μ, AND THE SYNTAX PAYS FOR IT.
-- An unfolding is no subterm of its fixpoint and sits at the same
-- type, so neither the syntax nor the candidate's own type recursion
-- reaches it.  What does is the size: the μ former spends a unit, the
-- gate the μ variable must sit behind is where the size stops looking,
-- and the unfolding therefore has exactly the size the body had.
--
-- THE CEILING IS A MEASURE COMPONENT, NOT A HYPOTHESIS.  The walk
-- carries a stratum `k` with the guard `T (inputsBelowᵉ k b)` and an
-- `Acc` on it, ordered ABOVE the g-size accessibility.  A term step
-- holds the ceiling and shrinks the size; the SHARED-SLOT step drops
-- the ceiling to the slot's own index -- which its `ok` field licenses
-- -- and lets the size go free.  That is what funds the descent into a
-- definition drawn from the slot table rather than from the term, and
-- an input's g-size being zero is why nothing smaller could.  Nothing
-- of it reaches `reducible`, which instantiates the ceiling at the
-- context's own size out of `ib-topᵉ`.
mutual
  redExpAcc : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t)
              (ρ : Env Γ Θ) → RedEnv ρ
            → (k : ℕ) → T (inputsBelowᵉ k b) → Acc _<_ k
            → Acc _<_ (gsizeᵉ b) → Red {Γ = Γ} (obs t) (Θ , b , ρ)
  redExpAcc (input i) ρ rρ k ok aK a = red-input i ρ k ok aK
  redExpAcc (ofᵉ ts) ρ rρ k ok aK (acc rs) κ now sched st =
    _ , subs-of , satOneShot (redTmsAcc ts ρ rρ k ok aK (rs ≤-refl))
  redExpAcc emptyᵉ ρ rρ k ok aK a κ now sched st =
    _ , subs-empty , satOneShot []
  redExpAcc (mapᵉ {s = s} f b) ρ rρ k ok aK (acc rs) κ now sched st =
    let okf = ∧ˡ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        okb = ∧ʳ (inputsBelowᵗ k f) (inputsBelowᵉ k b) ok
        ((burst , sched₁ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ f))))
            (map-f (_ , f , ρ) ↠[ ≤-refl ] κ) now sched st
        (r , p , sat′) =
          red-push now (map-f (_ , f , ρ)) tt
            (redFnAcc f ρ rρ k okf aK
              (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵉ b)))))
            κ sat sched₁ st₁ tt
    in r , subs-map d p , sat′
  redExpAcc (takeᵉ c b) ρ rρ k ok aK (acc rs) κ now sched st
    with evalWith c ρ in ceq
  ... | zero  = _ , subs-take-zero ceq , satOneShot []
  ... | suc j =
    let okb = ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵉ k b) ok
        nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (m≤n+m (gsizeᵉ b) (gsizeᵗ c))))
            (take-f nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (take-st (suc j)) st)
        (r , p , sat′) = red-push now (take-f nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-take-suc ceq refl d p , sat′
  redExpAcc (batchSyncᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (batchSync-f nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (batchSync-st true) st)
        ((out , sched₃ , st₂) , p , sat′) =
          red-push now (batchSync-f nid) tt tt κ sat sched₂ st₁ tt
    in _ , subs-batchSync refl d p , sat′
  redExpAcc (scanᵉ {s = s} {t = u} f z b) ρ rρ k ok aK (acc rs) κ now sched st =
    let zbe = inputsBelowᵗ k z ∧ inputsBelowᵉ k b
        okf = ∧ˡ (inputsBelowᵗ k f) zbe ok
        rest = ∧ʳ (inputsBelowᵗ k f) zbe ok
        okz = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        okb = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵉ k b) rest
        nid = freshId nodeᵏ (Sched.mint sched)
        rf  = redFnAcc f ρ rρ k okf aK
                (rs (s≤s (m≤m+n (gsizeᵗ f) (gsizeᵗ z + gsizeᵉ b))))
        rz  = redTmAcc z ρ rρ k okz aK
                (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵉ b))
                                  (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k okb aK
            (rs (s≤s (≤-trans (m≤n+m (gsizeᵉ b) (gsizeᵗ z))
                              (m≤n+m (gsizeᵗ z + gsizeᵉ b) (gsizeᵗ f)))))
            (scan-f (_ , f , ρ) nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (cell-st (evalWith z ρ)) st)
        (r , p , sat′) =
          red-push now (scan-f (_ , f , ρ) nid) tt rf
            κ sat sched₂ st₁ (red-scan-installed (_ , f , ρ) nid rz sched st d)
    in r , subs-scan refl d p , sat′
  redExpAcc (mergeAllᵉ lim b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer mergeAllᵒ nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (mergeAll-st lim 0 [] false) st)
        (r , p , sat′) =
          red-push now (thru-outer mergeAllᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-merge-all (sub-all refl d p) , sat′
  redExpAcc (switchAllᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer switchᵒ nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (switch-st nothing false) st)
        (r , p , sat′) =
          red-push now (thru-outer switchᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-switch-all (sub-all refl d p) , sat′
  redExpAcc (exhaustAllᵉ b) ρ rρ k ok aK (acc rs) κ now sched st =
    let nid = freshId nodeᵏ (Sched.mint sched)
        ((burst , sched₂ , st₁) , d , sat) =
          redExpAcc b ρ rρ k ok aK (rs ≤-refl)
            (thru-outer exhaustᵒ nid ↠[ ≤-refl ] κ) now
            (record sched { mint = setAt nodeᵏ (suc nid) (Sched.mint sched) })
            (installNode nid (exhaust-st false false) st)
        (r , p , sat′) =
          red-push now (thru-outer exhaustᵒ nid) tt tt κ sat sched₂ st₁ tt
    in r , subs-exhaust-all (sub-all refl d p) , sat′
  redExpAcc (μᵉ body) ρ rρ k ok aK (acc rs) κ now sched st =
    let (r , d , sat) =
          redExpAcc (unfoldμ body) ρ rρ k (ib-unfoldμ k body ok) aK
            (rs (subst (_< suc (gsizeᵉ body))
                       (sym (gsize-unfoldμ body)) ≤-refl))
            κ now sched st
    in r , subs-μ d , sat
  redExpAcc (varᵉ ()) ρ rρ k ok aK a
  redExpAcc (deferᵉ body) ρ rρ k ok aK a κ now sched st =
    _ , subs-defer refl refl refl refl , []
  redExpAcc (mintᵉ body) ρ rρ k ok aK (acc rs) κ now sched st =
    let src = freshId sourceᵏ (Sched.mint sched)
        (r , d , sat) =
          redExpAcc body (src ∷ᵉ ρ) (tt , rρ) k ok aK (rs ≤-refl) κ now
            (record sched
               { mint = setAt sourceᵏ (suc src) (Sched.mint sched) })
            st
    in r , subs-mint refl d , sat

  -- THE SLOT ARM, WHICH IS SEVERAL SUB-ARMS OF PROTOCOL AND ONE THAT
  -- SPENDS THE CEILING.  It mirrors the machine's own case split on
  -- the slot exactly, because the derivation it must produce is the
  -- one the machine produces; what is new is the satisfaction beside
  -- it, and at a scripted slot that is `red-data` at every value the
  -- script carries.  The ceiling's accessibility is taken apart here
  -- rather than passed on, since `toℕ i < k` is exactly what the
  -- expression face's guard reduces to at this former.
  red-input : ∀ {n} {Γ : Ctx n} {Θ} (i : Fin n) (ρ : Env Γ Θ) (k : ℕ)
            → T (toℕ i <ᵇ k) → Acc _<_ k
            → Red {Γ = Γ} (obs (lookup Γ i)) (Θ , input i , ρ)
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      with toℕ i <? lo
  ... | no  ¬below = _ , subs-floor (≮⇒≥ ¬below) , StreamSat-spent
  ... | yes below  with Sched.slots sched i in slEq
  ...   | scripted {ok = okD} (hot async)
          with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ...     | true  = _ , subs-hot-done below slEq doneEq , StreamSat-spent
  ...     | false = _ , subs-hot-live below slEq doneEq refl , []
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | scripted {ok = okD} (cold sync []) =
        _ , subs-cold-sync below slEq , satOneShot (redDatas _ okD sync)
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | scripted {ok = okD} (cold sync (d ∷ ds)) =
        _ , subs-cold-async below slEq refl refl refl
          , satValues (redDatas _ okD sync) ∷ []
  red-input {Γ = Γ} i ρ k ok (acc rsK) {lo = lo} κ now sched st
      | yes below | shared d {ok = okd} =
        red-input-shared i d (rsK (<ᵇ⇒< (toℕ i) k ok)) ρ
          κ below now sched slEq st

  -- THE SLOT SUB-ARM THE OTHERS ARE NOT.  A share's definition is an
  -- arbitrary expression standing in no relation to `input i`, so it
  -- cannot be reached by any descent on the TERM.  The telescope's own
  -- side condition is what reaches it instead: a slot's definition may
  -- reference only inputs STRICTLY BELOW that slot, so the definition
  -- is charged against the ceiling `toℕ i`, which the caller's
  -- accessibility has just been taken apart to supply.  The other
  -- sub-arms emit nothing, or values that are DATA by the slot's own
  -- side condition, so `red-data` closes their satisfaction outright;
  -- this one's values are the definition's, which is what the
  -- recursion returns and what the connect hands straight back.
  red-input-shared : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo Θ}
      (i : Fin n) (d : Closed Γ (lookup Γ i))
      {okd : T (inputsBelowᵉ (toℕ i) d)}
    → Acc _<_ (toℕ i)
    → (ρ : Env Γ Θ)
      (κ : Path Γ lo (lookup Γ i) t) (below : toℕ i < lo)
      (now : Tick) (sched : Sched Γ)
    → Sched.slots sched i ≡ shared d {ok = okd}
    → (st : EvalSt e)
    → Σ (Stream Γ (lookup Γ i) × Sched Γ × EvalSt e) λ r →
        subscribeE⇓ {e = e} (Θ , input i , ρ) κ now sched st r
          × StreamSat (Red (lookup Γ i)) (proj₁ r)
  red-input-shared {Γ = Γ} i d {okd} aI ρ κ below now sched slEq st
      with memberSource (toℕ i) (EvalSt.completedSources st) in doneEq
  ... | true =
        _ , subs-shared {κ = κ} {below = below} slEq
              (slot-spent {κ = κ} {below = below} doneEq)
          , StreamSat-spent
  ... | false
        with memberSource (toℕ i) (EvalSt.connectedShares st) in connEq
  ...   | true =
          _ , subs-shared {κ = κ} {below = below} slEq
                (slot-join {κ = κ} {below = below} doneEq connEq refl)
            , []
  ...   | false
          with redExpAcc d []ᵉ tt (toℕ i) okd aI
                 (<-wellFounded (gsizeᵉ d))
                 (share-sink i ≤-refl) now
                 (record sched
                    { mint = setAt regᵏ (suc (freshId regᵏ (Sched.mint sched)))
                               (Sched.mint sched) })
                 (register (freshId regᵏ (Sched.mint sched)) (atSlot i)
                   (lowerFloor below κ)
                   (record st
                     { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))
  ...     | ((burst , sched₁ , st₂) , dv , dsat)
            with burstCompleted burst in compEq
  ...       | false =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect {κ = κ} {below = below} doneEq connEq
                      (connect-live {κ = κ} {below = below} refl dv compEq))
                , dsat
  ...       | true =
              _ , subs-shared {κ = κ} {below = below} slEq
                    (slot-connect {κ = κ} {below = below} doneEq connEq
                      (connect-died {κ = κ} {below = below} refl dv compEq))
                , dsat

  -- THE FUNDAMENTAL THEOREM AT TERMS, which is where the embedding
  -- former hands the recursion back to the expression face.
  redTmAcc : ∀ {n} {Γ : Ctx n} {Θ u} (tm : Tm Γ [] [] Θ u)
             (ρ : Env Γ Θ) → RedEnv ρ
           → (k : ℕ) → T (inputsBelowᵗ k tm) → Acc _<_ k
           → Acc _<_ (gsizeᵗ tm) → Red u (evalWith tm ρ)
  redTmAcc (varᵗ x) ρ rρ k ok aK a = redLookup ρ rρ x
  redTmAcc unit̂     ρ rρ k ok aK a = tt
  redTmAcc (bool̂ b) ρ rρ k ok aK a = tt
  redTmAcc (nat̂ j)  ρ rρ k ok aK a = tt
  redTmAcc nilᵗ     ρ rρ k ok aK a = []
  redTmAcc (consᵗ x xs) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ xs))))
    ∷ redTmAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ xs) (gsizeᵗ x))))
  redTmAcc (foldᵗ l z f) ρ rρ k ok aK (acc rs) =
    let zfe  = inputsBelowᵗ k z ∧ inputsBelowᵗ k f
        okl  = ∧ˡ (inputsBelowᵗ k l) zfe ok
        rest = ∧ʳ (inputsBelowᵗ k l) zfe ok
        okz  = ∧ˡ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
        okf  = ∧ʳ (inputsBelowᵗ k z) (inputsBelowᵗ k f) rest
    in redFoldVals f ρ
         (λ {x} {ac} rx rac →
            redTmAcc f (x ∷ᵉ ac ∷ᵉ ρ) (rx , rac , rρ) k okf aK
              (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ f) (gsizeᵗ z))
                                (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
         (redTmAcc l ρ rρ k okl aK
           (rs (s≤s (m≤m+n (gsizeᵗ l) (gsizeᵗ z + gsizeᵗ f)))))
         (redTmAcc z ρ rρ k okz aK
           (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ z) (gsizeᵗ f))
                             (m≤n+m (gsizeᵗ z + gsizeᵗ f) (gsizeᵗ l))))))
  redTmAcc (pairᵗ x y) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗ y))))
    , redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗ y) (gsizeᵗ x))))
  redTmAcc (fstᵗ q) ρ rρ k ok aK (acc rs) =
    proj₁ (redTmAcc q ρ rρ k ok aK (rs ≤-refl))
  redTmAcc (sndᵗ q) ρ rρ k ok aK (acc rs) =
    proj₂ (redTmAcc q ρ rρ k ok aK (rs ≤-refl))
  redTmAcc (inlᵗ x) ρ rρ k ok aK (acc rs) = redTmAcc x ρ rρ k ok aK (rs ≤-refl)
  redTmAcc (inrᵗ x) ρ rρ k ok aK (acc rs) = redTmAcc x ρ rρ k ok aK (rs ≤-refl)
  redTmAcc (caseᵗ sc l r) ρ rρ k ok aK (acc rs)
    with ∧ˡ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
       | ∧ʳ (inputsBelowᵗ k sc) (inputsBelowᵗ k l ∧ inputsBelowᵗ k r) ok
  ... | oksc | rest
    with evalWith sc ρ
       | redTmAcc sc ρ rρ k oksc aK
           (rs (s≤s (m≤m+n (gsizeᵗ sc) (gsizeᵗ l + gsizeᵗ r))))
  ... | inj₁ x | q =
    redTmAcc l (x ∷ᵉ ρ) (q , rρ) k
      (∧ˡ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ l) (gsizeᵗ r))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  ... | inj₂ y | q =
    redTmAcc r (y ∷ᵉ ρ) (q , rρ) k
      (∧ʳ (inputsBelowᵗ k l) (inputsBelowᵗ k r) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ r) (gsizeᵗ l))
                        (m≤n+m (gsizeᵗ l + gsizeᵗ r) (gsizeᵗ sc)))))
  redTmAcc (ifᵗ c x y) ρ rρ k ok aK (acc rs)
    with ∧ʳ (inputsBelowᵗ k c) (inputsBelowᵗ k x ∧ inputsBelowᵗ k y) ok
  ... | rest with evalWith c ρ
  ... | true  =
    redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤m+n (gsizeᵗ x) (gsizeᵗ y))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  ... | false =
    redTmAcc y ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗ k y) rest) aK
      (rs (s≤s (≤-trans (m≤n+m (gsizeᵗ y) (gsizeᵗ x))
                        (m≤n+m (gsizeᵗ x + gsizeᵗ y) (gsizeᵗ c)))))
  redTmAcc (primᵗ add x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ sub x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ mul x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ eqᵖ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ eqᵘ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ ltᵖ x)  ρ rρ k ok aK a = tt
  redTmAcc (primᵗ notᵖ x) ρ rρ k ok aK a = tt
  redTmAcc (strmᵗ e) ρ rρ k ok aK (acc rs) = redExpAcc e ρ rρ k ok aK (rs ≤-refl)

  redTmsAcc : ∀ {n} {Γ : Ctx n} {Θ u} (ts : List (Tm Γ [] [] Θ u))
              (ρ : Env Γ Θ) → RedEnv ρ
            → (k : ℕ) → T (inputsBelowᵗˢ k ts) → Acc _<_ k
            → Acc _<_ (gsizeᵗˢ ts)
            → All (Red u) (map (λ tm → evalWith tm ρ) ts)
  redTmsAcc []       ρ rρ k ok aK a = []
  redTmsAcc (x ∷ xs) ρ rρ k ok aK (acc rs) =
      redTmAcc x ρ rρ k (∧ˡ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤m+n (gsizeᵗ x) (gsizeᵗˢ xs))))
    ∷ redTmsAcc xs ρ rρ k (∧ʳ (inputsBelowᵗ k x) (inputsBelowᵗˢ k xs) ok) aK
        (rs (s≤s (m≤n+m (gsizeᵗˢ xs) (gsizeᵗ x))))

  -- A FRAME'S CLOSURE APPLIED is the term face at one more entry, and
  -- with the environment carried rather than substituted that is all
  -- it is -- no transport, no lemma, the two statements are the same
  -- statement.
  redFnAcc : ∀ {n} {Γ : Ctx n} {Θ s u} (f : Tm Γ [] [] (s ∷ Θ) u)
             (ρ : Env Γ Θ) → RedEnv ρ
           → (k : ℕ) → T (inputsBelowᵗ k f) → Acc _<_ k
           → Acc _<_ (gsizeᵗ f) → RedFn {Γ = Γ} {s = s} {u = u} (_ , f , ρ)
  redFnAcc f ρ rρ k ok aK a {v} p = redTmAcc f (v ∷ᵉ ρ) (p , rρ) k ok aK a

-- THE TOP LINE: every closure whose environment is reducible is
-- itself reducible, which is the face above with both accessibilities
-- seeded at their own subjects.
reducible : ∀ {n} {Γ : Ctx n} {Θ t} (b : Exp Γ [] [] Θ t) (ρ : Env Γ Θ)
          → RedEnv ρ → Red {Γ = Γ} (obs t) (Θ , b , ρ)
reducible b ρ rρ =
  redExpAcc b ρ rρ _ (ib-topᵉ b) (<-wellFounded _) (<-wellFounded (gsizeᵉ b))

-- AND EVERY RUNTIME VALUE IS REDUCIBLE, WHICH IS THE ONE THING A
-- CLOSURE CARRIER COSTS.  A value at observable type IS a body paired
-- with an environment, and an entry of that environment at observable
-- type is another such value -- so nothing could be claimed of the
-- pair that is not already claimed of its entries, and the descent is
-- on the VALUE rather than on the type.  This is why no site that
-- meets a stored observable has to thread a reducibility premise: it
-- re-establishes the claim here, once.
mutual
  red-val : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → Red t v
  red-val unitᵗ     v           = tt
  red-val boolᵗ     v           = tt
  red-val natᵗ      v           = tt
  red-val uniqᵗ     v           = tt
  red-val (s ×ᵗ u)  (a , b)     = red-val s a , red-val u b
  red-val (s +ᵗ u)  (inj₁ a)    = red-val s a
  red-val (s +ᵗ u)  (inj₂ b)    = red-val u b
  red-val (listᵗ s) []          = []
  red-val (listᵗ s) (x ∷ xs)    = red-val s x ∷ red-val (listᵗ s) xs
  red-val (obs u)   (Θ , b , ρ) = reducible b ρ (red-env ρ)

  red-env : ∀ {n} {Γ : Ctx n} {Θ : List Ty} (ρ : Env Γ Θ) → RedEnv ρ
  red-env []ᵉ                 = tt
  red-env (_∷ᵉ_ {s = s} v vs) = red-val s v , red-env vs
