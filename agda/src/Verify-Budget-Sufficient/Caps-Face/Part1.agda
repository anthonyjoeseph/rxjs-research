------------------------------------------------------------------
-- STRATUM DOCUMENTATION, INHERITED FROM THE DELETED `Caps-Face` UMBRELLA.
-- That module held nothing but an `open import ... public` re-export,
-- which is now illegal — a name is imported from where it is DEFINED — so
-- the umbrella went and its prose came here, this file being the
-- stratum's bottom rung.  Consumers import the Parts directly now;
-- nothing was proven or unproven by the move.
------------------------------------------------------------------
-- STRATUM 2a of Verify-Budget-Sufficient: THE CAPS FACE (round 4).
--
-- Everything STATED IN TERMS OF the per-instant cap recurrence: the state
-- predicate capsOK?, the in-flight predicates (valCaps? / eventCaps? /
-- burstCaps? / obsCaps?), the frame face and the cascade companions,
-- caps-tick DERIVED from those, and the reachability cluster
-- (reach-resets) that pays round 3's debt.
--
-- THE SUBSCRIBE CLIQUE LIVES IN .Subscribe-Face.  The
-- caps face itself (subscribeE-caps), the twelve companions mutual with
-- it, and the four delivery leaves that call it are a SUFFIX of this
-- module — reverse-reachability from the clique reaches nothing else
-- here, and stepFrame-FACE never calls stepFrame-CAPS — so they are now
-- a module of their own that imports this one by name.  The ~45-clause
-- subscribe grind therefore re-checks 1.9k lines, not this file's 6.5k
-- (18 minutes cold).
--
-- THE RECURRENCE ITSELF LIVES IN .Caps — the Caps
-- triple, sizeStep / foldStep / iterSize / iterFold / frameStep /
-- frameBlowup with their monotonicity toolkit, capsAt, and the supply
-- lemmas that read a level off it.  .Wet reads those and nothing else
-- here, so with them inside this module every proof edit here re-checked
-- .Wet and Verify-Well-Formed for nothing.  This is the .Keeps-Ring
-- precedent applied a second time; see .Caps's own head.
--
-- THE ROUND-5 GATE IS STILL THE TYPE.  frameBlowup : Caps → Caps cannot
-- read the ledger, the receipt, or E, because they are not arguments.
--
-- This module is a SIBLING of .Wet, not a layer over it: the wet family
-- never mentions the caps FACE (checked), so the two are independent
-- extensions of .Caps and an edit here does not re-check the wet family.
--
-- Named Caps-Face rather than Caps because .Caps is now a real module and
-- the record it defines is named Caps.  It sits over .Caps, hence over
-- .Keeps-Ring, whose slotsEq is what transports a width bound across a
-- sub-call (valCaps? and its relatives read Sched.slots, and the caller
-- reports at the callee's post sched).

-- SPLIT INTO Part1..Part7 to bound per-edit recheck time.  There is no
-- umbrella module over them — one could only re-export, and a name is
-- imported from where it is DEFINED — so consumers import the Parts.

-- STRATUM 2a of Verify-Budget-Sufficient: THE CAPS FACE (round 4).
--
-- Everything STATED IN TERMS OF the per-instant cap recurrence: the state
-- predicate capsOK?, the in-flight predicates (valCaps? / eventCaps? /
-- burstCaps? / obsCaps?), the frame face and the cascade companions,
-- caps-tick DERIVED from those, and the reachability cluster
-- (reach-resets) that pays round 3's debt.
--
-- THE SUBSCRIBE CLIQUE LIVES IN .Subscribe-Face.  The
-- caps face itself (subscribeE-caps), the twelve companions mutual with
-- it, and the four delivery leaves that call it are a SUFFIX of this
-- module — reverse-reachability from the clique reaches nothing else
-- here, and stepFrame-FACE never calls stepFrame-CAPS — so they are now
-- a module of their own that imports this one by name.  The ~45-clause
-- subscribe grind therefore re-checks 1.9k lines, not this file's 6.5k
-- (18 minutes cold).
--
-- THE RECURRENCE ITSELF LIVES IN .Caps — the Caps
-- triple, sizeStep / foldStep / iterSize / iterFold / frameStep /
-- frameBlowup with their monotonicity toolkit, capsAt, and the supply
-- lemmas that read a level off it.  .Wet reads those and nothing else
-- here, so with them inside this module every proof edit here re-checked
-- .Wet and Verify-Well-Formed for nothing.  This is the .Keeps-Ring
-- precedent applied a second time; see .Caps's own head.
--
-- THE ROUND-5 GATE IS STILL THE TYPE.  frameBlowup : Caps → Caps cannot
-- read the ledger, the receipt, or E, because they are not arguments.
--
-- This module is a SIBLING of .Wet, not a layer over it: the wet family
-- never mentions the caps FACE (checked), so the two are independent
-- extensions of .Caps and an edit here does not re-check the wet family.
--
-- Named Caps-Face rather than Caps because .Caps is now a real module and
-- the record it defines is named Caps.  It sits over .Caps, hence over
-- .Keeps-Ring, whose slotsEq is what transports a width bound across a
-- sub-call (valCaps? and its relatives read Sched.slots, and the caller
-- reports at the callee's post sched).
module Verify-Budget-Sufficient.Caps-Face.Part1 where

open import Data.Bool    using (Bool; true; false; _∧_; if_then_else_; T)
open import Data.Maybe   using (Maybe)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-reflexive; +-suc; +-identityʳ; +-comm; +-assoc; +-monoˡ-≤; *-monoˡ-≤;
  *-monoʳ-≤; m≤m+n; m≤n+m; n≤1+n; +-mono-≤; m≤m*n; ^-monoʳ-≤; *-assoc; *-identityʳ; <⇒≤;
  ^-monoˡ-≤; ^-*-assoc; ^-distribˡ-+-*; *-mono-≤; +-monoʳ-≤; m≤m⊔n; m≤n⊔m; ⊔-lub; *-identityˡ;
  *-distribˡ-+)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; map)
open import Data.Bool.ListAction using (all)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Tick; Source; InstEmit; _at_from_as_; InstEvent; init; value; close; handoff; complete; Timed;
  after_,_; hot; cold)
open import Rx.Exp       using (Ty; natᵗ; unitᵗ; boolᵗ; _×ᵗ_; _+ᵗ_; obs; isData; Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ; syncSizeᵛ; Exp; Tm; Fn; varᵗ; unit̂;
  bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; add; sub; mul; eqᵖ;
  ltᵖ; notᵖ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; evalWith; evalTm; applyFn)
open import Rx.Frame-Width using (entryCeil; pWᵉ; pWᵛ; dWᵉ; outWᵉ; innWᵉ; innWᵗ; innWᵗˢ; pmOᵉ; pmOᵗ; pmIᵉ; pmIᵗ; pmIᵗˢ; _∈ᵇ_; outWⱽ;
  innWⱽ; innWᵗⱽ; innWᵗˢⱽ; pmIᵗⱽ; slotPW; slotsPW; slotsPWgo; slotIW; slotsIW; slotsIWgo)
open import Rx.Evaluator using (capsBase; Sched; EvalSt; LiveSource; RegId; Chain; NodeState; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; root; share-sink; _↠_; Frame; map-f; scan-f; take-f; from-inner; thru-outer;
  Stream; Path; sizeStep; iterSize; foldStep; iterFold)
open import Rx.Slots using (scripted; shared; Slot; Slots; slotSize; slotsSize; inputSize)
open import Rx.Clos-Size using (closSizeᵉ; closSize≤mulᵉ)
open import Rx.Slot-Clos using (slotClos; slotClosD; slotsClos; σAt)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted so that a grind here no longer
--     re-checks .Wet — see that module's head.
--   · .Deliveries is the ledger stratum: where EvalSt.delivered moves
--     and where it provably does not, plus delivN and its composition
--     laws.  delivN is the currency the cascade conjuncts are stated in.
--   · .Delivery-Walk maps the delivery clique onto the LEVEL walk —
--     foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ,
--     cascadeGo ↦ dWalkᶜ — RELATIVE to one frame's face at the level it
--     RUNS at, which it takes as a record of hypotheses rather than
--     postulating.  `walkH` below instantiates that record and
--     `cascadeGo-deliveries` is the theorem it buys.
open import Verify-Budget-Sufficient.Caps using
  (_⊑ᶜ_; 2≤capsAt-size; caps; Caps; capsAt; capsAt-base-size; capsH;
   cSize≤frameBlowup; frameStep; frameStep-wid-suc;
   iterFold-infl; iterFold-mono-count; iterFold-suc; iterSize-2^; iterSize-infl;
   iterSize-mono-count; iterSize-suc; size≤sizeCount; sizeCount; sizeStep-infl)
open import Verify-Budget-Sufficient.Measures using
  (2X≡X+X; all-++-intro; all-impl;
                                                      EnvSize; envSize-lookup; envSize-widen;
                                                      fᵢ≤sum-tab; n<2^n; n≤slotsSize;
                                                      pathLen; size-subΘᵉ; sizeᵗ-pos;
                                                      syncSize≤sizeᵉ;
                                                      parkRoom; parkRoom-widen;
                                                      stBounded-widen; stBounded?; ∧-true)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over.  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers

------------------------------------------------------------------
-- THE REACHABILITY CLUSTER — round 3's remaining debt, and the answer
-- round3b-ledger-reset-absurd demands.
--
-- That refutation says the reset caps may not be the ledger.  So they
-- come from REACHABILITY instead: a bound on what a run can actually
-- reach, computed from the program and the clock rather than from how
-- far the size ledger has been allowed to climb.
--
-- ONE SOURCE, THREE ROLES — structural rather than a discipline to be
-- remembered.  With C the instant's cap (Caps below):
--
--     Ŝ = Caps.cSize C           the s′ reset at hop and connect edges
--     F = Caps.cSize C           hopD's index, off the store anchor
--     R̂ = hopR (Caps.cSize C)    the r reset at connect edges
--
-- F cannot drift to a different, unaudited source because it IS Ŝ, and
-- none of the three needs a new definition: hopR already exists and
-- hopD-cap already turns a size bound into a hop bound at the same
-- index.  reach-resets below is that, proven.
--
-- The remaining question was only ever what to instantiate them AT.  A
-- fixed-height tower was tried and refuted (deepScan); the Caps
-- recurrence below is the replacement.
------------------------------------------------------------------

-- the frame-width half of the state predicate.  NOT widthOK? — that
-- was ofW, a per-NODE width (deleted with the width walk),
-- and om-is-not-a-frame-budget is the counterexample to conflating
-- the two
widLive : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → LiveSource Γ → Bool
widLive {n = n} W sl l =
  all (λ tv → pWᵛ n sl (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ W)
      (LiveSource.pending l)

-- THE FLATTEN CLAUSE CARRIES A CARDINALITY as well as the pointwise
-- bound, and it has to: `mergeAllDrain` subscribes one inner per queued
-- observable, so the drain's receipt is a sum over the queue, and
-- NOTHING else in the tree bounds how long that queue is — the
-- hypothesis mergeAllDrain-caps is given admits a queue of any length at
-- all, and so does an `all` (Rung-Count-Probe § 2, both rows).  One
-- level of width pays for one cons, with the same `suc w ≤ foldStep S w`
-- margin the count receipts already spend
widNode : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
widNode {n = n} W sl (scan-st {t} v)   = pWᵛ n sl t v ≤ᵇ W
widNode {n = n} W sl (mergeAll-st _ _ q _) =
  all (λ o → pWᵉ n sl o ≤ᵇ W) q ∧ (length q ≤ᵇ W)
widNode W sl (take-st _)               = true
widNode W sl (switch-st _ _)           = true
widNode W sl (exhaust-st _ _)          = true

-- THE CHAIN HALF, and why cSize has to cover it.  A chain's map-f /
-- scan-f frames carry STEP FUNCTIONS, and `sizeStep` below reads a step
-- function's size as its multiplier — so a size cap that bounds only
-- stored values leaves the multiplier unbounded.  This is `regsB?`'s
-- size conjunct without the Ψ half, which capsOK? has no use for.
--
-- Measured (State-Blowup-Probe): step functions in chains do NOT grow —
-- 10, 10, 10, 10 across pA's cascades — because subscribeE installs a
-- syntactic subterm of what was already in the store.  So cSize covers
-- them without a fourth field and, crucially, WITHOUT the ledger:
-- round3b-ledger-reset-absurd stays unavailable
-- top-level (not a where block) so subscribeE-caps can name pathSz? in
-- its hypothesis: the continuation κ a subscribe walks under must
-- already be size-bounded, or a huge step function in κ would be
-- registered at the leaf.  This is the honest form — the naive version
-- without the κ hypothesis is FALSE, since κ = scan-f BIG ↠ root over a
-- tiny b registers BIG
frameSz? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameSz? B (map-f fn)         = sizeᵗ fn ≤ᵇ B
frameSz? B (scan-f fn _)      = sizeᵗ fn ≤ᵇ B
frameSz? B (take-f _)         = true
frameSz? B (from-inner _ _ _) = true
frameSz? B (thru-outer _ _)   = true


-- AND HOW MANY FRAMES — the j-budget probe's finding, and the second
-- conjunct cSize has to carry.  A payload grows once PER FRAME it
-- crosses (a map-f crossing is the same size-subΘᵉ substitution a fold
-- is), so the chain LENGTH is a factor in one cascade's event count, and
-- nothing else in Caps sees it.  J-Budget-Probe's pM family pins cSize,
-- cWid and cReg at 7, 1, 1 while its cascades store 15 … 4371 — the
-- length is the ONLY quantity that moves — so tickFits-absurd refutes
-- every count computed from the triple until the triple bounds it.
--
-- The quantity is `pathLen`, already defined above for the walk's length
-- ledger, and that is not a coincidence: subscribeE-walk already carries
-- this invariant in the same shape (`pathLen κ + G ≤ ℓ` in, `regsLen? ℓ`
-- out), so the conjunct the caps face needs is the ℓ ledger read at
-- ℓ := cSize rather than a new mechanism.  It reads the chain and
-- nothing else: no ledger, no receipt, no E.
--
-- Measured (J-Budget-Probe): a chain's length is fixed by the root
-- subscribe and untouched by cascades — 3 ↦ 9 across the family at
-- instant 0, still 9 after two cascades — and it sits well under the
-- entry measure, so a per-instant recurrence can carry it
-- BOTH conjuncts, in ONE recursive walk: each frame's step function is
-- bounded, and so is the length of every suffix — the outermost of which
-- is the whole chain's, so this says exactly `pathLen p ≤ B`.
--
-- It has to be written recursively rather than as `frames ∧ length`: a
-- non-matching definition unfolds on a NEUTRAL path, so every type
-- mentioning a registered chain grows the body instead of staying stuck,
-- and J-Budget-Probe OOMs at 13 GB on precisely that

-- AND THE WALKED PATH AND THE REGISTRY ARE PRICED AT DIFFERENT
-- NUMBERS, WHICH IS A FACT ABOUT THE TWO USES AND NOT ABOUT THE TWO
-- CONJUNCTS.  The path in hand is read at the PROGRAM'S CAP, because
-- its frames have to pay for what they emit and one level buys only
-- `S + S·L` against a duplicator that is quadratic in what it is
-- capped by -- `Refuted.Frame-Step-Size-Level` names that crossing.
-- The REGISTRY is read at a climbing level instead, and must be:
-- a subscribing frame registers a chain longer than the one it was
-- walking, by the inner's own operator count, so a fixed reading of
-- it is refuted outright by `Refuted.Chain-Step-Regs-Cap`.
--
-- SO THE PREDICATE IS RIGHT AS IT STANDS AND THE OBLIGATION IS ON ITS
-- CALLERS: price the walked path at the cap, the registry at the
-- level, and never carry one number for both.  One level covers one
-- chain's growth -- `sizeStep S L` is `S·(1+2L)`, which dominates
-- `L + S` for every positive cap -- so the registry side climbs by a
-- DETERMINED count and not by a witness chosen after the fact.  The
-- walk face on this spine already reads it exactly that way; what
-- does not is the cascade's own chain door, which is where the
-- refuted fixed reading survived.

-- AND THE TWO NUMBERS CANNOT BE MADE INDEPENDENT, WHICH CLOSES THE
-- ONE REPAIR THE SINK HOP HAD LEFT.  The reading above invites a
-- split: carry a LENGTH cap beside the syntax cap, let a subscribe
-- add to the first alone, and a fan-out then costs levels additively
-- rather than by a whole `sizeStep`.  What forbids it is WHICH
-- observable gets registered.  `thruConsume` hands `subscribeInner`
-- the value flowing down the path, not the arrival that entered the
-- instant -- so the operator count pushed onto the registered chain is
-- the DERIVED value's, and a derived value is exactly what the size
-- ledger has been inflating frame by frame.  The length increment is
-- therefore bounded by the size level and by nothing smaller, so a
-- second number tracks the first instead of escaping it.
--
-- SO NEITHER OF THE TWO REPAIRS `Refuted.Sink-Level-Range` NAMED IS
-- OPEN, and what is owed is a mechanism rather than a ledger: the walk
-- carries a receipt about the path it is on, a sink spends it on paths
-- it is not on, and every bridge tried so far has been a cap big
-- enough to cover both.  That the higher-order case reaches this at
-- all is not incidental -- a map producing observables under a
-- flatten is the shape this campaign exists for.
pathSz? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathSz? B root           = true
pathSz? B (share-sink i) = true
pathSz? B (f ↠ p)        = frameSz? B f ∧ ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p)

regsSz? : ∀ {n} {Γ : Ctx n} {t} → ℕ → List (RegId × Source × Chain Γ t) → Bool
regsSz? B = all (λ en → pathSz? B (proj₂ (proj₂ (proj₂ en))))

-- THE CAP READ AGAINST THE ARRIVAL'S CLOSURE, which is the shape the
-- arr-keyed descent needs and the one `nestValOK?` deliberately does
-- not have: that predicate is a fact about a VALUE alone, while the
-- key a subscription is charged at sees through the telescope the
-- value may reference.  The two coincide on a slot-free arrival.
-- AND THE FLAT SLOT MEASURE CANNOT STAND IN FOR IT, which is worth
-- saying because that measure is the one the caps face already carries
-- as a standing premise and the obvious candidate for generalising this
-- key away.  `closSizeᵉ` reads `input i` as `slotClos i`, so a
-- definition naming a slot TWICE pays for it twice, and a telescope in
-- which each definition doubles its predecessor is closed under
-- `inputsBelowᵉ`: the closure measure is multiplicative in the
-- telescope's depth where `slotsSize` is a flat sum of written sizes.
-- Four such slots already read 27 against 98.  So `slotsSize sl ≤
-- Caps.cSize c` does not imply this predicate, and the two premises are
-- independent rather than one subsuming the other.

-- AND WHETHER THE CAP THE TOP INSTANTIATES CAN SATISFY IT IS OPEN, AND
-- SYMBOLIC-OR-NOTHING.  Every consumer of this key takes it as a
-- premise, so nothing owes a proof today; what is owed at the top is
-- that `capsAt`'s own size admits the telescope, and by the paragraph
-- above that number has to beat a measure exponential in the
-- telescope's depth.  THE MEASURING ROUTE IS CLOSED: `capsAt`'s size is
-- `iterSize` at a count the caps counting family produces, and that
-- family is the one the harness quarantines as unreachable by
-- measurement -- native code at the smallest arguments, no value -- so
-- no probe, row or `refl` pin can decide it.  What is left is
-- arithmetic already in the tree: `exp-iterSize` puts `2 ^ k` under
-- that size, so the question reduces to whether the count dominates the
-- slot depth, and that is a statement about the counting family rather
-- than about this predicate.  `capsOK?` is where it
-- is carried, so the top-level consumer that owes the answer is the
-- instant loop rather than the walk.


-- AND THE SAME READING FOLDED OVER A WHOLE SUBSCRIPTION, event by
-- event, which is the shape the caps face already states its own
-- arrival predicate in.  Only a `value` carries an arrival, so every
-- other event reads as true outright -- the fold is a filter with the
-- closure reading attached, not a second traversal.

nestClosOK? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → Val Γ (obs u) → Bool
nestClosOK? c sl o = closSizeᵉ (slotClos sl) o ≤ᵇ Caps.cSize c

nestClosOK?ᵛ : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → (u : Ty) → Val Γ u → Bool
nestClosOK?ᵛ c sl unitᵗ    _        = true
nestClosOK?ᵛ c sl boolᵗ    _        = true
nestClosOK?ᵛ c sl natᵗ     _        = true
nestClosOK?ᵛ c sl (s ×ᵗ t) (a , b)  = nestClosOK?ᵛ c sl s a ∧ nestClosOK?ᵛ c sl t b
nestClosOK?ᵛ c sl (s +ᵗ t) (inj₁ a) = nestClosOK?ᵛ c sl s a
nestClosOK?ᵛ c sl (s +ᵗ t) (inj₂ b) = nestClosOK?ᵛ c sl t b
nestClosOK?ᵛ c sl (obs t)  o        = nestClosOK? c sl o

-- THE CLOSURE READING OF WHAT THE SCHEDULE IS HOLDING, and it sits
-- beside the width one because it is the same shape of fact about the
-- same queue -- a per-element bound over `Sched.live`.  What it reads
-- is not the value's own syntax but its size THROUGH the slot
-- telescope, which is a strictly stronger reading: the deficit is per
-- reference, so a value the size cap admits carries the deficit up with
-- it and no caps receipt at any cap implies this one.
--
-- SO IT IS CARRIED RATHER THAN DERIVED, which is why it is a conjunct
-- and not a lemma.  Every consumer that subscribes a value it took off
-- that queue needs the reading, and the only statement that can supply
-- it to ALL of them is one every producer re-establishes -- the
-- hypothesis-in-a-signature form obliges whoever happens to call today
-- and nobody else.
--
-- AND THE NODE TABLE IS NOT HERE, WHICH IS A FINDING AND NOT A CHOICE
-- OF SCOPE.  The one node the reading would be about is a mergeAll's
-- parked queue, and the site that writes it is the gate-shut arm of the
-- inner consume, which holds only the WRITTEN size of the observable it
-- parks.  Supplying the closure reading there means carrying it on
-- every observable the walk delivers, and the walk EMITS observables as
-- well as receiving them -- so the premise would have to be
-- re-established on the output of every arm, which is the sum the flat
-- frame reading was killed on.
-- DEAD ROUTE: deriving the parked queue's reading from the caps
--   receipts in hand at the park site.  `valCaps?` bounds the written
--   size against the level's cap, and one level of the frame multiplies
--   by the base size and doubles -- but `closSizeᵉ` is multiplicative in
--   the TELESCOPE's depth, which no number the frame steps through
--   mentions, so no fixed number of levels closes the gap.
closLive : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → LiveSource Γ → Bool
closLive c sl l =
  all (λ tv → nestClosOK?ᵛ c sl (LiveSource.elemTy l) (proj₂ tv))
      (LiveSource.pending l)

closSt? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Caps → Sched Γ → EvalSt e → Bool
closSt? c sched st = all (closLive c (Sched.slots sched)) (Sched.live sched)

capsOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Caps → Sched Γ → EvalSt e → Bool
capsOK? c sched st =
  stBounded? (Caps.cSize c) sched st
  ∧ regsSz? (Caps.cSize c) (EvalSt.registry st)
  ∧ all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched)
  ∧ all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
        (EvalSt.nodes st)
  ∧ (length (EvalSt.registry st) ≤ᵇ Caps.cReg c)
  ∧ all (λ kv → parkRoom (Caps.cSize c) (slotsSize (Sched.slots sched))
                         (proj₂ kv))
        (EvalSt.nodes st)
  ∧ closSt? c sched st

------------------------------------------------------------------
-- capsOK? IS MONOTONE IN THE CAPS.  The widening the induction performs
-- everywhere: a subscribe reports growth frameStep j ↦ frameStep (j+j′),
-- and capsOK? at the smaller caps must weaken to the larger.  Each
-- conjunct is a `≤ᵇ` bound weakened through `all-impl`, exactly as the
-- walk face's pathB?-widen does for its own predicate.
------------------------------------------------------------------

-- the step function's size bound weakens frame by frame
pathSz?-widen : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) {B B′ : ℕ} →
  B ≤ B′ → pathSz? B p ≡ true → pathSz? B′ p ≡ true
pathSz?-widen root           le h = refl
pathSz?-widen (share-sink i) le h = refl
pathSz?-widen (map-f fn ↠ p) {B} le h
  with ∧-true (sizeᵗ fn ≤ᵇ B) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
... | hl , hp = ∧-intro (≤ᵇ-widen (sizeᵗ fn) le hf)
                  (∧-intro (≤ᵇ-widen (suc (pathLen p)) le hl) (pathSz?-widen p le hp))
pathSz?-widen (scan-f fn _ ↠ p) {B} le h
  with ∧-true (sizeᵗ fn ≤ᵇ B) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h
... | hf , hr with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hr
... | hl , hp = ∧-intro (≤ᵇ-widen (sizeᵗ fn) le hf)
                  (∧-intro (≤ᵇ-widen (suc (pathLen p)) le hl) (pathSz?-widen p le hp))
pathSz?-widen (take-f _ ↠ p) {B} le h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | hl , hp = ∧-intro (≤ᵇ-widen (suc (pathLen p)) le hl) (pathSz?-widen p le hp)
pathSz?-widen (from-inner _ _ _ ↠ p) {B} le h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | hl , hp = ∧-intro (≤ᵇ-widen (suc (pathLen p)) le hl) (pathSz?-widen p le hp)
pathSz?-widen (thru-outer _ _ ↠ p) {B} le h
  with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) h
... | hl , hp = ∧-intro (≤ᵇ-widen (suc (pathLen p)) le hl) (pathSz?-widen p le hp)

regsSz?-widen : ∀ {n} {Γ : Ctx n} {t}
  (rs : List (RegId × Source × Chain Γ t)) {B B′ : ℕ} →
  B ≤ B′ → regsSz? B rs ≡ true → regsSz? B′ rs ≡ true
regsSz?-widen rs le =
  all-impl _ _ (λ en → pathSz?-widen (proj₂ (proj₂ (proj₂ en))) le) rs

widLive-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (l : LiveSource Γ) {W W′ : ℕ} →
  W ≤ W′ → widLive W sl l ≡ true → widLive W′ sl l ≡ true
widLive-widen {n = n} sl l le =
  all-impl _ _ (λ tv → ≤ᵇ-widen (pWᵛ n sl (LiveSource.elemTy l) (proj₂ tv)) le)
           (LiveSource.pending l)

widNode-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (ns : NodeState Γ) {W W′ : ℕ} →
  W ≤ W′ → widNode W sl ns ≡ true → widNode W′ sl ns ≡ true
widNode-widen {n = n} sl (scan-st {t} v)   le h = ≤ᵇ-widen (pWᵛ n sl t v) le h
widNode-widen {n = n} sl (mergeAll-st _ _ q _) {W} {W′} le h
  with ∧-true (all (λ o → pWᵉ n sl o ≤ᵇ W) q) (length q ≤ᵇ W) h
... | hall , hlen =
  ∧-intro (all-impl _ _ (λ o → ≤ᵇ-widen (pWᵉ n sl o) le) q hall)
          (≤ᵇ-widen (length q) le hlen)
widNode-widen sl (take-st _)     le h = refl
widNode-widen sl (switch-st _ _) le h = refl
widNode-widen sl (exhaust-st _ _) le h = refl

-- AND BOTH ARRIVAL BOOLEANS WIDEN WITH THE CAP, which is what lets a
-- caller read a bound at the level the walk reports and spend it at
-- the join its own arm needs.  The size field is the only one the
-- arrival cap moves, and every reading here is against it.
nestClosOK?ᵛ-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (u : Ty) (v : Val Γ u)
  {c c′ : Caps} → c ⊑ᶜ c′ →
  nestClosOK?ᵛ c sl u v ≡ true → nestClosOK?ᵛ c′ sl u v ≡ true
nestClosOK?ᵛ-widen sl unitᵗ    v        le h = refl
nestClosOK?ᵛ-widen sl boolᵗ    v        le h = refl
nestClosOK?ᵛ-widen sl natᵗ     v        le h = refl
nestClosOK?ᵛ-widen sl (s ×ᵗ t) (a , b)  le h =
  ∧-intro (nestClosOK?ᵛ-widen sl s a le (proj₁ (∧-true _ _ h)))
          (nestClosOK?ᵛ-widen sl t b le (proj₂ (∧-true _ _ h)))
nestClosOK?ᵛ-widen sl (s +ᵗ t) (inj₁ a) le h = nestClosOK?ᵛ-widen sl s a le h
nestClosOK?ᵛ-widen sl (s +ᵗ t) (inj₂ b) le h = nestClosOK?ᵛ-widen sl t b le h
nestClosOK?ᵛ-widen sl (obs t)  o        le h =
  ≤ᵇ-widen (closSizeᵉ (slotClos sl) o) (proj₁ le) h

-- AND A DATA TYPE READS AS TRUE OUTRIGHT, which is what a scripted
-- slot's live entry needs: `isData` is exactly the absence of `obs`, and
-- every other arm of the reading is `true` by its clause.
nestClosOK?ᵛ-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) →
  T (isData u) → (v : Val Γ u) → nestClosOK?ᵛ c sl u v ≡ true
nestClosOK?ᵛ-data c sl unitᵗ    ok v = refl
nestClosOK?ᵛ-data c sl boolᵗ    ok v = refl
nestClosOK?ᵛ-data c sl natᵗ     ok v = refl
nestClosOK?ᵛ-data c sl (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = ∧-intro (nestClosOK?ᵛ-data c sl s (subst T (sym eqs) tt) a)
                      (nestClosOK?ᵛ-data c sl u ok b)
... | false = ⊥-elim ok
nestClosOK?ᵛ-data c sl (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = nestClosOK?ᵛ-data c sl s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
nestClosOK?ᵛ-data c sl (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = nestClosOK?ᵛ-data c sl u ok b
... | false = ⊥-elim ok
nestClosOK?ᵛ-data c sl (obs u)  ok v = ⊥-elim ok

-- and the same over a pending list, stated at the ELEMENT TYPE rather
-- than at the entry.  A caller holding a live source only through the
-- record's projections cannot let Agda solve the entry from the goal --
-- `closLive` reduces THROUGH `elemTy` and `pending`, so unification is
-- against projections of a meta and blocks -- and the entry a caller
-- like the hot-slot initialiser has is a literal it would otherwise
-- have to spell out.
closLive-pend : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) →
  T (isData u) → (ps : List (Tick × Val Γ u)) →
  all (λ tv → nestClosOK?ᵛ c sl u (proj₂ tv)) ps ≡ true
closLive-pend c sl u ok []             = refl
closLive-pend c sl u ok ((tk , v) ∷ r) =
  ∧-intro (nestClosOK?ᵛ-data c sl u ok v) (closLive-pend c sl u ok r)

-- and the same over a live entry's whole pending list
closLive-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (l : LiveSource Γ) →
  T (isData (LiveSource.elemTy l)) → closLive c sl l ≡ true
closLive-data c sl l ok =
  closLive-pend c sl (LiveSource.elemTy l) ok (LiveSource.pending l)

closLive-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (l : LiveSource Γ) {c c′ : Caps} →
  c ⊑ᶜ c′ →
  closLive c sl l ≡ true → closLive c′ sl l ≡ true
closLive-widen sl l le =
  all-impl _ _ (λ tv → nestClosOK?ᵛ-widen sl (LiveSource.elemTy l) (proj₂ tv) le)
           (LiveSource.pending l)

-- THE VALUE READING OF THE CLOSURE KEY, AND IT IS A MAX RATHER THAN A
-- SUM.  That is not a choice: `nestClosOK?ᵛ` is a CONJUNCTION over the
-- observable leaves of a value, so the one number it compares against
-- the cap is the largest leaf, and a data leaf carries no observable
-- and therefore no closure at all.  Stating the measure makes the
-- predicate an inequality, which is what an arithmetic bound can be
-- spent against; the predicate itself is a Bool and nothing composes
-- with it.
closSizeᵛ : ∀ {n} {Γ : Ctx n} (σ : Fin n → ℕ) (u : Ty) → Val Γ u → ℕ
closSizeᵛ σ unitᵗ    _        = 0
closSizeᵛ σ boolᵗ    _        = 0
closSizeᵛ σ natᵗ     _        = 0
closSizeᵛ σ (s ×ᵗ t) (a , b)  = closSizeᵛ σ s a ⊔ closSizeᵛ σ t b
closSizeᵛ σ (s +ᵗ t) (inj₁ a) = closSizeᵛ σ s a
closSizeᵛ σ (s +ᵗ t) (inj₂ b) = closSizeᵛ σ t b
closSizeᵛ σ (obs t)  o        = closSizeᵉ σ o

-- and it DECIDES the predicate: at an observable the comparison is the
-- predicate's own leaf clause, and at a pair ⊔ is the conjunction
closSizeᵛ-OK : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  closSizeᵛ (slotClos sl) u v ≤ Caps.cSize c → nestClosOK?ᵛ c sl u v ≡ true
closSizeᵛ-OK c sl unitᵗ    v        h = refl
closSizeᵛ-OK c sl boolᵗ    v        h = refl
closSizeᵛ-OK c sl natᵗ     v        h = refl
closSizeᵛ-OK c sl (s ×ᵗ t) (a , b)  h =
  ∧-intro (closSizeᵛ-OK c sl s a (≤-trans (m≤m⊔n _ _) h))
          (closSizeᵛ-OK c sl t b (≤-trans (m≤n⊔m _ _) h))
closSizeᵛ-OK c sl (s +ᵗ t) (inj₁ a) h = closSizeᵛ-OK c sl s a h
closSizeᵛ-OK c sl (s +ᵗ t) (inj₂ b) h = closSizeᵛ-OK c sl t b h
closSizeᵛ-OK c sl (obs t)  o        h = T⇒≡true _ (≤⇒≤ᵇ h)

-- THE CLOSURE IS THE PLAIN SIZE TIMES A CEILING ON THE TELESCOPE, at
-- the VALUE level.  `Rx.Clos-Size` proves the expression half against
-- the SYNC size; the plain size dominates that, so a caller holding
-- nothing but a size receipt and a slot ceiling -- which is exactly
-- what a caps arrival carries -- can read a closure bound off it.  The
-- price is one factor of the ceiling, and a single frame level pays it
-- because a level MULTIPLIES by the cap.
closSizeᵛ≤mul : ∀ {n} {Γ : Ctx n} (σ : Fin n → ℕ) (M : ℕ) →
  (∀ i → σ i ≤ M) → 1 ≤ M → (u : Ty) (v : Val Γ u) →
  closSizeᵛ σ u v ≤ M * sizeᵛ u v
closSizeᵛ≤mul σ M hσ 1≤M unitᵗ    v        = z≤n
closSizeᵛ≤mul σ M hσ 1≤M boolᵗ    v        = z≤n
closSizeᵛ≤mul σ M hσ 1≤M natᵗ     v        = z≤n
closSizeᵛ≤mul σ M hσ 1≤M (s ×ᵗ t) (a , b)  =
  ⊔-lub (≤-trans (closSizeᵛ≤mul σ M hσ 1≤M s a)
                 (*-monoʳ-≤ M (≤-trans (m≤m+n _ _) (n≤1+n _))))
        (≤-trans (closSizeᵛ≤mul σ M hσ 1≤M t b)
                 (*-monoʳ-≤ M (≤-trans (m≤n+m _ _) (n≤1+n _))))
closSizeᵛ≤mul σ M hσ 1≤M (s +ᵗ t) (inj₁ a) =
  ≤-trans (closSizeᵛ≤mul σ M hσ 1≤M s a) (*-monoʳ-≤ M (n≤1+n _))
closSizeᵛ≤mul σ M hσ 1≤M (s +ᵗ t) (inj₂ b) =
  ≤-trans (closSizeᵛ≤mul σ M hσ 1≤M t b) (*-monoʳ-≤ M (n≤1+n _))
closSizeᵛ≤mul σ M hσ 1≤M (obs t)  o        =
  ≤-trans (closSize≤mulᵉ σ M hσ 1≤M o) (*-monoʳ-≤ M (syncSize≤sizeᵉ o))





capsOK?-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c c′ : Caps) (sched : Sched Γ) (st : EvalSt e) →
  c ⊑ᶜ c′ → capsOK? c sched st ≡ true → capsOK? c′ sched st ≡ true
capsOK?-mono c c′ sched st le@(sz≤ , wd≤ , rg≤) h
  with ∧-true _ _ h
... | hSt , hRest with ∧-true _ _ hRest
... | hRg , hRest2 with ∧-true _ _ hRest2
... | hWL , hRest3 with ∧-true _ _ hRest3
... | hWN , hRest4 with ∧-true _ _ hRest4
... | hLen , hRest5 with ∧-true _ _ hRest5
... | hPk , hCL =
  ∧-intro (stBounded-widen sz≤ sched st hSt)
  (∧-intro (regsSz?-widen (EvalSt.registry st) sz≤ hRg)
  (∧-intro (all-impl _ _ (λ l → widLive-widen (Sched.slots sched) l wd≤)
                     (Sched.live sched) hWL)
  (∧-intro (all-impl _ _ (λ kv → widNode-widen (Sched.slots sched) (proj₂ kv) wd≤)
                     (EvalSt.nodes st) hWN)
  (∧-intro (≤ᵇ-widen (length (EvalSt.registry st)) rg≤ hLen)
  (∧-intro (all-impl _ _ (λ kv → parkRoom-widen sz≤ (proj₂ kv))
                     (EvalSt.nodes st) hPk)
           (all-impl _ _ (λ l → closLive-widen (Sched.slots sched) l le)
                     (Sched.live sched) hCL))))))

------------------------------------------------------------------
-- THE SYNTAX-LINEAR EVAL RECEIPT — ONE iterSize FOLD PER SYNTAX NODE.
--
-- Eval-Growth-Probe refutes the AFFINE reading of the five evaluation
-- obligations on every axis it names, and none of the refutations is by
-- a constant: §1's `seedDbl` doubles a VALUE every six syntax nodes, so
-- one j (`sizeStep S S`, the cap read at the term's own size) is beaten
-- at k = 13 and a 4× slackened cap only survives to k = 16; §2's
-- `fnDbl` beats `sizeStep S s` at k = 6, on a value of size 127.
--
-- What the same probe MEASURES as the replacement is §3: `iterSize`
-- runs away much faster than the ladder does — j′ ≤ 3 closes a value of
-- 33 million out of a term of size 145 — so the receipt the cluster
-- carries is ONE FOLD PER SYNTAX NODE, `j′ = sizeᵗ tm`.
--
-- This is that bound, proven.  `sizeStep S` dominates the growth of ONE
-- constructor's evaluation for every constructor, so its j-fold iterate
-- dominates a term of j nodes.  Clause by clause:
--
--   varᵗ / literals   a lookup or a constant; inflationary is enough
--   pairᵗ             `suc (s + s) ≤ S * suc (2 s)` — the one clause
--                     that genuinely doubles, and the one `sizeStep`'s
--                     `2 *` is shaped for
--   fstᵗ / sndᵗ       a projection SHRINKS, an injection adds one
--   inlᵗ / inrᵗ
--   caseᵗ             the branch runs over an environment extended with
--                     the SCRUTINEE's value, so the caps compound — and
--                     the compounding is exactly iterSize's own
--                     composition law, iterSize-+.  This is the clause
--                     the naive linear bound dies on, and the reason the
--                     receipt counts NODES rather than depth
--   ifᵗ               both branches see the UNextended environment
--   primᵗ             a nat or a bool: size 1
--   strmᵗ             the substitution clause, and the only one that
--                     needs the multiplier at all — size-subΘᵉ bounds it
--                     by `sizeᵉ e * suc (2 V)`.  The FACTOR IS PAID FOR
--                     BY THE BODY'S OWN NODES rather than by the cap:
--                     `suc (sizeᵉ e)` folds are available here and each
--                     at least doubles (iterSize-2^), so `sizeᵉ e` of
--                     them cover a factor of `sizeᵉ e`.
--
-- THAT LAST POINT IS WHAT MAKES THE LEMMA USABLE.  It needs NO
-- hypothesis relating the term's size to S, so it instantiates at
-- S = Caps.cSize c — the base frameStep actually iterates at — while
-- each clause's own size hypothesis reads the STEPPED cap
-- `Caps.cSize (frameStep j c)`, which is far larger.  A lemma stated
-- with `sizeᵗ tm ≤ S` would be unusable there: iterating at the stepped
-- base outruns iterating at cSize c, so the receipt would not join the
-- frameStep sum.
------------------------------------------------------------------

-- iterSize COMPOSES: a folds then b more is a + b folds.  The caseᵗ
-- clause is this law and nothing else
iterSize-+ : ∀ (S a b s : ℕ) →
  iterSize S (a + b) s ≡ iterSize S b (iterSize S a s)
iterSize-+ S zero    b s = refl
iterSize-+ S (suc a) b s = iterSize-+ S a b (sizeStep S s)

-- and is monotone in the SEED as well as in the count
sizeStep-mono-s : ∀ (S : ℕ) {s s′ : ℕ} → s ≤ s′ → sizeStep S s ≤ sizeStep S s′
sizeStep-mono-s S le = *-monoʳ-≤ S (s≤s (*-monoʳ-≤ 2 le))

iterSize-mono-s : ∀ (S k : ℕ) {s s′ : ℕ} → s ≤ s′ →
  iterSize S k s ≤ iterSize S k s′
iterSize-mono-s S zero    le = le
iterSize-mono-s S (suc k) le = iterSize-mono-s S k (sizeStep-mono-s S le)

-- so k folds off a nonzero seed reach k
k≤iterSize : ∀ (S k s : ℕ) → 1 ≤ S → 1 ≤ s → k ≤ iterSize S k s
k≤iterSize S k s hS 1≤s =
  ≤-trans (<⇒≤ (n<2^n k))
  (≤-trans (≤-reflexive (sym (*-identityʳ (2 ^ k))))
  (≤-trans (*-monoʳ-≤ (2 ^ k) 1≤s) (iterSize-2^ S k s hS)))

-- the three one-fold facts the clauses consume
one≤sizeStep : ∀ (S s : ℕ) → 1 ≤ S → 1 ≤ sizeStep S s
one≤sizeStep S s hS =
  ≤-trans (m≤m*n 1 (suc (2 * s))) (*-monoˡ-≤ (suc (2 * s)) hS)

pair≤sizeStep : ∀ (S s : ℕ) → 1 ≤ S → suc (s + s) ≤ sizeStep S s
pair≤sizeStep S s hS =
  ≤-trans (s≤s (≤-reflexive (cong (s +_) (sym (+-identityʳ s)))))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) hS))

-- SPENDING THE NODE: a bound at `sizeStep S (iterSize S k s)` is a
-- bound at `iterSize S (suc k) s`.  Every clause below ends here
step-node : ∀ (S k s x : ℕ) →
  x ≤ sizeStep S (iterSize S k s) → x ≤ iterSize S (suc k) s
step-node S k s x h = subst (x ≤_) (sym (iterSize-suc S k s)) h

-- THE BOUND.  Structural induction on the term; every constructor
-- spends exactly one fold, and caseᵗ re-enters at the grown seed
evalWith-iterSize : ∀ {n} {Γ : Ctx n} {Θ t} (S V : ℕ) → 1 ≤ S →
  (tm : Tm Γ [] [] Θ t) (env : All (Val Γ) Θ) → EnvSize V env →
  sizeᵛ t (evalWith tm env) ≤ iterSize S (sizeᵗ tm) V
evalWith-iterSize S V hS (varᵗ x) env hσ =
  ≤-trans (envSize-lookup V env hσ x) (sizeStep-infl S V hS)
evalWith-iterSize S V hS unit̂     env hσ = one≤sizeStep S V hS
evalWith-iterSize S V hS (bool̂ _) env hσ = one≤sizeStep S V hS
evalWith-iterSize S V hS (nat̂ _)  env hσ = one≤sizeStep S V hS
evalWith-iterSize S V hS (pairᵗ a b) env hσ =
  step-node S (sizeᵗ a + sizeᵗ b) V _
    (≤-trans (s≤s (+-mono-≤ ihA ihB)) (pair≤sizeStep S M hS))
  where
  M   = iterSize S (sizeᵗ a + sizeᵗ b) V
  ihA = ≤-trans (evalWith-iterSize S V hS a env hσ)
                (iterSize-mono-count S V hS (m≤m+n (sizeᵗ a) (sizeᵗ b)))
  ihB = ≤-trans (evalWith-iterSize S V hS b env hσ)
                (iterSize-mono-count S V hS (m≤n+m (sizeᵗ b) (sizeᵗ a)))
evalWith-iterSize S V hS (fstᵗ p) env hσ
  with evalWith p env | evalWith-iterSize S V hS p env hσ
... | (a , b) | ihp =
  step-node S (sizeᵗ p) V _
    (≤-trans (≤-trans (≤-trans (m≤m+n (sizeᵛ _ a) (sizeᵛ _ b)) (n≤1+n _)) ihp)
             (sizeStep-infl S (iterSize S (sizeᵗ p) V) hS))
evalWith-iterSize S V hS (sndᵗ p) env hσ
  with evalWith p env | evalWith-iterSize S V hS p env hσ
... | (a , b) | ihp =
  step-node S (sizeᵗ p) V _
    (≤-trans (≤-trans (≤-trans (m≤n+m (sizeᵛ _ b) (sizeᵛ _ a)) (n≤1+n _)) ihp)
             (sizeStep-infl S (iterSize S (sizeᵗ p) V) hS))
evalWith-iterSize S V hS (inlᵗ a) env hσ =
  step-node S (sizeᵗ a) V _
    (≤-trans (s≤s (≤-trans (evalWith-iterSize S V hS a env hσ)
                           (m≤m+n M M)))
             (pair≤sizeStep S M hS))
  where M = iterSize S (sizeᵗ a) V
evalWith-iterSize S V hS (inrᵗ a) env hσ =
  step-node S (sizeᵗ a) V _
    (≤-trans (s≤s (≤-trans (evalWith-iterSize S V hS a env hσ)
                           (m≤m+n M M)))
             (pair≤sizeStep S M hS))
  where M = iterSize S (sizeᵗ a) V
evalWith-iterSize S V hS (caseᵗ {s = s} sc l r) env hσ
  with evalWith sc env | evalWith-iterSize S V hS sc env hσ
... | inj₁ a | ihsc =
  step-node S (sizeᵗ sc + sizeᵗ l + sizeᵗ r) V _
    (≤-trans (≤-trans BR (iterSize-mono-count S V hS
                            (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))))
             (sizeStep-infl S _ hS))
  where
  Msc : ℕ
  Msc = iterSize S (sizeᵗ sc) V
  ha : sizeᵛ s a ≤ Msc
  ha = ≤-trans (n≤1+n (sizeᵛ s a)) ihsc
  BR = subst (sizeᵛ _ (evalWith l (a ∷ᵃ env)) ≤_)
             (sym (iterSize-+ S (sizeᵗ sc) (sizeᵗ l) V))
             (evalWith-iterSize S Msc hS l (a ∷ᵃ env)
                (ha , envSize-widen (iterSize-infl S hS (sizeᵗ sc) V) env hσ))
... | inj₂ b | ihsc =
  step-node S (sizeᵗ sc + sizeᵗ l + sizeᵗ r) V _
    (≤-trans (≤-trans BR (iterSize-mono-count S V hS
                            (+-monoˡ-≤ (sizeᵗ r) (m≤m+n (sizeᵗ sc) (sizeᵗ l)))))
             (sizeStep-infl S _ hS))
  where
  Msc : ℕ
  Msc = iterSize S (sizeᵗ sc) V
  hb : sizeᵛ _ b ≤ Msc
  hb = ≤-trans (n≤1+n (sizeᵛ _ b)) ihsc
  BR = subst (sizeᵛ _ (evalWith r (b ∷ᵃ env)) ≤_)
             (sym (iterSize-+ S (sizeᵗ sc) (sizeᵗ r) V))
             (evalWith-iterSize S Msc hS r (b ∷ᵃ env)
                (hb , envSize-widen (iterSize-infl S hS (sizeᵗ sc) V) env hσ))
evalWith-iterSize S V hS (ifᵗ c a b) env hσ with evalWith c env
... | true  =
  step-node S (sizeᵗ c + sizeᵗ a + sizeᵗ b) V _
    (≤-trans (≤-trans (evalWith-iterSize S V hS a env hσ)
                      (iterSize-mono-count S V hS
                        (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                 (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))))
             (sizeStep-infl S _ hS))
... | false =
  step-node S (sizeᵗ c + sizeᵗ a + sizeᵗ b) V _
    (≤-trans (≤-trans (evalWith-iterSize S V hS b env hσ)
                      (iterSize-mono-count S V hS
                        (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
             (sizeStep-infl S _ hS))
evalWith-iterSize S V hS (primᵗ add arg)  env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (primᵗ sub arg)  env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (primᵗ mul arg)  env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (primᵗ eqᵖ arg)  env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (primᵗ ltᵖ arg)  env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (primᵗ notᵖ arg) env hσ =
  step-node S (sizeᵗ arg) V _ (one≤sizeStep S (iterSize S (sizeᵗ arg) V) hS)
evalWith-iterSize S V hS (strmᵗ e) []ᵃ hσ =
  k≤iterSize S (sizeᵉ e) (sizeStep S V) hS (one≤sizeStep S V hS)
evalWith-iterSize S V hS (strmᵗ e) (v ∷ᵃ vs) hσ =
  ≤-trans (size-subΘᵉ V [] (v ∷ᵃ vs) e hσ)
          (≤-trans (*-mono-≤ (<⇒≤ (n<2^n (sizeᵉ e))) X≤step)
                   (iterSize-2^ S (sizeᵉ e) (sizeStep S V) hS))
  where
  X≤step : suc (2 * V) ≤ sizeStep S V
  X≤step = ≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * V)))))
                   (*-monoˡ-≤ (suc (2 * V)) hS)

-- THE TWO FACES THE CLUSTER CONSUMES.  `applyFn` reads the receipt off
-- the STEP FUNCTION's syntax with the payload's size as the seed;
-- `evalTm` reads it off a closed term with an empty seed
applyFn-iterSize : ∀ {n} {Γ : Ctx n} {s u} (S V : ℕ) → 1 ≤ S →
  (fn : Fn Γ [] [] [] s u) (v : Val Γ s) → sizeᵛ s v ≤ V →
  sizeᵛ u (applyFn fn v) ≤ iterSize S (sizeᵗ fn) V
applyFn-iterSize S V hS fn v hv =
  evalWith-iterSize S V hS fn (v ∷ᵃ []ᵃ) (hv , tt)

evalTm-iterSize : ∀ {n} {Γ : Ctx n} {u} (S : ℕ) → 1 ≤ S →
  (z : Tm Γ [] [] [] u) → sizeᵛ u (evalTm z) ≤ iterSize S (sizeᵗ z) 0
evalTm-iterSize S hS z = evalWith-iterSize S 0 hS z []ᵃ tt

-- WHAT REPLACES caps-frame, AND WHY IT LIVES ON THE WALK FACE'S RECEIPT
-- RATHER THAN BESIDE IT.
--
-- caps-frame claimed SAME-LEVEL preservation and is refuted (see
-- caps-frame-boundary-absurd and the memo below).  The mechanism it
-- needed already exists one module-section away: subscribeE-walkS does
-- not claim its cap is preserved either — it concludes
-- `INV? Ψ (capᴱ W E′)`, the invariant at a GROWN cap, and reports the
-- growth as a receipt `E ≤ E′` composed along the walk by ≤-trans.  It
-- is PROVEN in that form.
--
-- So caps preservation is not a second face; it is one more component of
-- that receipt.  `j` rides alongside `E′` and is threaded by exactly the
-- same discipline — additively rather than multiplicatively, because it
-- counts folds.  Two accounting mechanisms for one growth was the smell;
-- this is the one mechanism.
--
-- AND IT IS NOT A SECOND LEDGER, which is the thing to check: `j` is
-- bounded by cWid * cReg * cSize, a quantity read off Caps, never off E or the
-- receipt.  `frameStep : ℕ → Caps → Caps` still cannot see the ledger,
-- so the round-5 gate is intact.  The two roles stay separate on
-- purpose: `INV? … (capᴱ W E′)` is the ledger-indexed state invariant,
-- while capsOK?'s cSize is what feeds Ŝ / R̂ / F — and THAT is the one
-- round3b-ledger-reset-absurd forbids from being ledger-derived.
------------------------------------------------------------------
-- IN-FLIGHT BOUNDS, CAPS SIDE.  `capsOK?` bounds the STATE; a walk also
-- carries values and events between frames, and those need the same two
-- numbers — the size against cSize, the FRAME WIDTH against cWid.  This
-- is valB?/eventB?/burstB? with (B, Ψ) replaced by the caps: the size
-- half is common, the second half is a width rather than a weight,
-- because that is what one fold's count is read off.
--
-- The slots come from the Sched the bound is stated at.  Slots never
-- change, so a value bounded before a step is bounded after it at the
-- same numbers, and no separate slots parameter is needed
------------------------------------------------------------------

-- THEY TAKE THE SLOT TELESCOPE, NOT THE Sched.  The width half reads
-- Sched.slots and nothing else, and the difference is not cosmetic: a
-- companion's hypotheses are stated at its ENTRY sched and its
-- conclusions describe values carried out past a sub-call's POST sched,
-- so with a Sched parameter every composition would owe a transport
-- across two schedules of a NEUTRAL application that does not reduce
-- (eventCaps? c sched′ ev is stuck unless ev is a `value`, so `rewrite`
-- on the slots cannot fire).  With Slots the same transport is one
-- subst, and the slot telescope is fixed anyway — .Keeps-Ring's slotsEq
-- is exactly that fact, and the delivery clique's own slots corollaries
-- are proven below
valCaps? : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → (u : Ty) → Val Γ u → Bool
valCaps? {n = n} c sl u v =
  (sizeᵛ u v ≤ᵇ Caps.cSize c) ∧ (pWᵛ n sl u v ≤ᵇ Caps.cWid c)

-- ONE NUMBER, READ ON THE SYNC SPINE, which is the currency the nest
-- face's grant is keyed in: substitution's charge is blind to what a
-- `deferᵉ` gate hides, and a μ-unfolding moves the full size while
-- leaving this reading exactly where it was.
--
-- AND IT IS ONE NUMBER RATHER THAN THE PAIR ITS CAPS SIBLING CARRIES,
-- because a syntactic width cannot survive the walk's own μ recursion:
-- `dWᵉ (unfoldμ body) ≤ dWᵉ (μᵉ body)` is FALSE, and the note on
-- `unfoldμ-caps` carries the witness and why no constant repairs it.
-- The nest walk was never spending this half -- the width it actually
-- charges is `descW`, which is semantic and prices the unfolding by
-- construction -- so the conjunct was an unpayable premise on every
-- head, and dropping it STRENGTHENS every statement that took it.
nestValOK? : ∀ {n} {Γ : Ctx n} → Caps → (u : Ty) → Val Γ u → Bool
nestValOK? c u v = syncSizeᵛ u v ≤ᵇ Caps.cSize c

eventCaps? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → InstEvent (Val Γ u) → Bool
eventCaps? {u = u} c sl (value v) = valCaps? c sl u v
eventCaps? c sl (init _)    = true
eventCaps? c sl (close _ _) = true
eventCaps? c sl (handoff _) = true
eventCaps? c sl complete    = true

burstCaps? : ∀ {n} {Γ : Ctx n} {u} → Caps → Slots Γ → Stream Γ u → Bool
burstCaps? c sl = all (λ em → all (eventCaps? c sl) (InstEmit.events em))

-- (b) THE BURST'S CARDINALITY — how many emits, and how many payloads
-- inside each — and it is a SECOND predicate rather than two more
-- conjuncts of burstCaps?, because the two sides of the machine want
-- different things from a burst.
--
-- THE DELIVERY SIDE CONCATENATES and so cannot carry a count at all:
-- shareGo-caps runs burstCaps?-++ over one registration's output and the
-- rest of the ring, and no cardinality survives `++` — `length xs ≤ n`
-- and `length ys ≤ n` say nothing whatever about `length (xs ++ ys)`.
-- Putting the count inside burstCaps? would therefore break the share
-- leaves, and it would be breaking them for nothing: nothing on the
-- delivery side iterates per emit.
--
-- THE SUBSCRIBE SIDE NEVER CONCATENATES — pushBurst maps a burst
-- emit-for-emit — so it can carry a count, and it MUST, because both of
-- Sub-Charge-Probe § 5's iteration counts are cardinalities of exactly
-- this burst.  `op-step`'s pushBurst premise iterates fIterD over
-- `suc (widAt S W A)` frames and pushBurst-caps spends one frame per
-- EMIT; `frame-step`'s walk premise iterates sIterD over
-- `suc (widAt S W j)` payloads and pushBurst-caps hands stepFrame-caps
-- one payload per `value` event INSIDE the emit.  Those are the two
-- counts (b1) and (b2), and this is the one predicate that states both.
--
-- IT IS STATED AT THE PRE-LEVEL, which is what makes it a lemma parallel
-- to subscribeE-caps rather than a third conjunct of its Σ.  The count
-- is wanted at `suc (widAt S W A)` for A the level the subscribe LEFT,
-- and `Caps.cWid (frameStep j c)` is `widAt (Caps.cSize c) (Caps.cWid c) j`
-- by refl, so a bound at the entry level implies the one at the exit
-- level by widAt-mono alone.  No existential has to be shared.
valCountᵉ : ∀ {A : Set} → List (InstEvent A) → ℕ
valCountᵉ []              = 0
valCountᵉ (value _   ∷ es) = suc (valCountᵉ es)
valCountᵉ (init _    ∷ es) = valCountᵉ es
valCountᵉ (close _ _ ∷ es) = valCountᵉ es
valCountᵉ (handoff _ ∷ es) = valCountᵉ es
valCountᵉ (complete  ∷ es) = valCountᵉ es

burstCount? : ∀ {n} {Γ : Ctx n} {u} → Caps → Stream Γ u → Bool
burstCount? c str =
  (length str ≤ᵇ suc (Caps.cWid c))
  ∧ all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c)) str

-- observables in a mergeAll queue: the caps side of mergeAllDrain's
-- `all (λ o → sizeᵉ o ≤ᵇ …)` pair
obsCaps? : ∀ {n} {Γ : Ctx n} {s} → Caps → Slots Γ → Closed Γ s → Bool
obsCaps? {n = n} c sl o =
  (sizeᵉ o ≤ᵇ Caps.cSize c) ∧ (pWᵉ n sl o ≤ᵇ Caps.cWid c)

------------------------------------------------------------------
-- THE SLOT TELESCOPE, INSIDE THE CAP — the side condition that ties
-- `c` to `sl`, and the second of the two things the caps tree was
-- blocked on.
--
-- capsOK? bounds the STATE and says nothing about the slots, but a
-- subscribe on `input i` reads slot data straight out of the telescope:
-- a shared slot's def is subscribed WHOLE, and a scripted slot's values
-- become payloads now and LiveSource pendings later.  So
-- subscribeE-input-caps needs every one of them under cSize, and an
-- abstract `c` gives it nothing.
--
-- The connection exists at the top — capsAt's base is
-- `2 + sizeᵉ e + slotsSize sl` — and this is that connection turned into
-- a decidable side condition, threaded UNCHANGED (slots never change
-- during a run; the slotsEq telescope is exactly that fact) and supplied
-- once by slotsCaps?-capsAt below, which the recurrence proves rather
-- than assumes — the same discipline 2≤capsAt-size already follows.
--
-- Written as a RECURSIVE walk over the index list rather than as
-- `all … ∘ tabulate`, for pathSz?'s reason: a non-matching definition
-- unfolds on a neutral telescope, so every type mentioning it would grow
-- its body instead of staying stuck, and that is what OOMs
------------------------------------------------------------------

-- BOTH AXES, since the deferᵉ repair, and the width axis has TWO
-- CONJUNCTS since the eval cluster's width half.  The size half is
-- unchanged; the pW half exists because a shared slot's DEF is
-- subscribed whole at a connect, and a def may bury a defer — whose
-- parked body capsOK? then demands a width for.
--
-- THE innW HALF IS THE ONE THE WIDTH INDUCTION READS.  Every
-- eval-cluster member concludes valCaps?, whose width conjunct is
-- `pWᵛ ≤ cWid`, and the induction that supplies it descends the
-- RESULT's syntax with all three width measures at once — and stops
-- dead at `input i`, whose innWᵉ descends into the slot's def while
-- `sizeᵉ (input i)` is 1.  pW cannot be made to bound it:
-- Eval-Growth-Probe's §8 `iwDef` is a def with pW 0 and innW 3, and the
-- gap widens with the of-list, because innW reads the STEP FUNCTION's
-- embedded observables while outW/dW read the source's.
--
-- Scripted slots still need nothing on this axis: their element type is
-- data, so pWᵛ is identically zero there
slotCaps? : ∀ {n} {Γ : Ctx n} {k u} → ℕ → ℕ → Slots Γ → Slot Γ k u → Bool
slotCaps? {u = u} B W sl (scripted (hot async)) =
  all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
  ∧ (inputSize (hot async) ≤ᵇ B)
slotCaps? {u = u} B W sl (scripted (cold sync async)) =
  all (λ v → sizeᵛ u v ≤ᵇ B) sync
  ∧ (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
     ∧ (inputSize (cold sync async) ≤ᵇ B))
slotCaps? {n = n} {k = k} B W sl (shared d) =
  (sizeᵉ d ≤ᵇ B)
  ∧ ((pWᵉ n sl d ≤ᵇ W)
     ∧ ((innWᵉ n sl d ≤ᵇ W) ∧ (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B)))

slotsGo? : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Slots Γ → List (Fin n) → Bool
slotsGo? B W sl []       = true
slotsGo? B W sl (i ∷ is) = slotCaps? B W sl (sl i) ∧ slotsGo? B W sl is

slotsCaps? : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Slots Γ → Bool
slotsCaps? {n = n} B W sl = slotsGo? B W sl (tabulate {n = n} (λ i → i))

slotCaps?-widen : ∀ {n} {Γ : Ctx n} {k u} (sl : Slots Γ) (s : Slot Γ k u)
  {B B′ W W′ : ℕ} →
  B ≤ B′ → W ≤ W′ → slotCaps? B W sl s ≡ true → slotCaps? B′ W′ sl s ≡ true
slotCaps?-widen {u = u} sl (scripted (hot async)) {B} le lw h =
  ∧-intro (all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async
             (proj₁ split))
          (≤ᵇ-widen (inputSize (hot async)) le (proj₂ split))
  where
  split = ∧-true (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async)
                 (inputSize (hot async) ≤ᵇ B) h
slotCaps?-widen {u = u} sl (scripted (cold sync async)) {B} le lw h =
  ∧-intro (all-impl _ _ (λ v → ≤ᵇ-widen (sizeᵛ u v) le) sync (proj₁ split₁))
          (∧-intro (all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async
                      (proj₁ split₂))
                   (≤ᵇ-widen (inputSize (cold sync async)) le (proj₂ split₂)))
  where
  split₁ = ∧-true (all (λ v → sizeᵛ u v ≤ᵇ B) sync)
                  (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
                     ∧ (inputSize (cold sync async) ≤ᵇ B)) h
  split₂ = ∧-true (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async)
                  (inputSize (cold sync async) ≤ᵇ B) (proj₂ split₁)
slotCaps?-widen {n = n} {k = k} sl (shared d) {B} {B′} {W} {W′} le lw h =
  ∧-intro (≤ᵇ-widen (sizeᵉ d) le (proj₁ split₁))
          (∧-intro (≤ᵇ-widen (pWᵉ n sl d) lw (proj₁ split₂))
                   (∧-intro (≤ᵇ-widen (innWᵉ n sl d) lw (proj₁ split₃))
                            (≤ᵇ-widen (suc (closSizeᵉ (σAt sl k) d)) le
                              (proj₂ split₃))))
  where
  split₁ = ∧-true (sizeᵉ d ≤ᵇ B)
                  ((pWᵉ n sl d ≤ᵇ W)
                     ∧ ((innWᵉ n sl d ≤ᵇ W)
                        ∧ (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B))) h
  split₂ = ∧-true (pWᵉ n sl d ≤ᵇ W)
                  ((innWᵉ n sl d ≤ᵇ W)
                     ∧ (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B)) (proj₂ split₁)
  split₃ = ∧-true (innWᵉ n sl d ≤ᵇ W)
                  (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B) (proj₂ split₂)

-- one slot's condition, read out of the telescope's
slotsGo?-tab : ∀ {n m} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ)
  (f : Fin m → Fin n) (i : Fin m) →
  slotsGo? B W sl (tabulate f) ≡ true → slotCaps? B W sl (sl (f i)) ≡ true
slotsGo?-tab B W sl f Fin.zero h =
  proj₁ (∧-true (slotCaps? B W sl (sl (f Fin.zero)))
                (slotsGo? B W sl (tabulate (λ k → f (Fin.suc k)))) h)
slotsGo?-tab B W sl f (Fin.suc i) h =
  slotsGo?-tab B W sl (λ k → f (Fin.suc k)) i
    (proj₂ (∧-true (slotCaps? B W sl (sl (f Fin.zero)))
                   (slotsGo? B W sl (tabulate (λ k → f (Fin.suc k)))) h))

slotsCaps?-lookup : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) (i : Fin n) →
  slotsCaps? B W sl ≡ true → slotCaps? B W sl (sl i) ≡ true
slotsCaps?-lookup B W sl i h = slotsGo?-tab B W sl (λ k → k) i h


------------------------------------------------------------------
-- AND WHY IT HOLDS AT capsAt: every payload a slot carries is a
-- summand of that slot's slotSize, every slotSize is a summand of
-- slotsSize, and slotsSize is a summand of the recurrence's base.
------------------------------------------------------------------

-- EVERY SLOT COSTS AT LEAST ONE, so the slot COUNT is under the caps'
-- own size — the supply behind the `n ≤ cSize` hypothesis the delivery
-- bound now carries.  `cDel`'s gas index is `suc (cSize c)` while the
-- evaluator's dispatch gas is the literal `n` (chainStep seeds it), and
-- nothing in capsOK? relates the two: the relation is a fact about the
-- SLOT TELESCOPE, and it is true at every level because capsAt's base
-- contains slotsSize as a summand and iterSize only grows it
-- (1≤slotSize / n≤sum-tab / n≤slotsSize live in .Measures, which
-- slotHop-sup also reads them from; they are in scope here by name.)
n≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  n ≤ Caps.cSize (capsAt e sl id)
n≤capsAt-size e sl id =
  ≤-trans (≤-trans (n≤slotsSize sl) (m≤n+m (slotsSize sl) (2 + sizeᵉ e)))
          (capsAt-base-size e sl id)

-- SEALED, and this is not optional: the consumer instantiates the
-- walk's gas to the cap the bound below fixes, so a transparent body
-- puts the `iterSize` exponential inside every statement carrying
-- that gas.  The helpers are hoisted rather than left in a `where`
-- because the seal has to sit at the top level to hold them out of
-- the types.
private
  gasB : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) → Caps
  gasB {n = n} e sl = caps (2 + sizeᵉ e + slotsSize sl + slotsClos sl)
                           (suc (entryCeil n sl e))
                           (suc (sizeᵉ e + slotsSize sl))

  four-clears : ∀ (x m : ℕ) → m ≤ x → 4 + x + m + m ≤ 4 * (2 + x)
  four-clears x m h =
    ≤-trans (≤-reflexive (trans (+-assoc (4 + x) m m) (+-assoc 4 x (m + m))))
    (≤-trans (+-mono-≤ (m≤m+n 4 4)
                (+-monoʳ-≤ x
                   (≤-trans (+-mono-≤ h h)
                            (+-monoʳ-≤ x (m≤m+n x (x + 0))))))
             (≤-reflexive (sym (*-distribˡ-+ 4 2 x))))

  4≤2^K : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) →
    4 ≤ 2 ^ sizeCount (gasB e sl) (capsBase e sl)
  4≤2^K e sl = ^-monoʳ-≤ 2 (≤-trans (s≤s (s≤s z≤n))
                   (size≤sizeCount (gasB e sl) (capsBase e sl)
                      (s≤s (s≤s z≤n)) (s≤s z≤n)))

abstract
  -- THE BASE ONCE THE BLOWUP HAS RUN, WITH ROOM FOR THE NESTING, which
  -- is what the delivery walk's round floor is seeded from.  A nested round is
  -- entered at one less gas AND one less ledger than the round above
  -- it, so a floor that carries the gas reproduces itself across a
  -- nesting for free; what that costs is paid here, at the seed, where
  -- the constants have to clear the initial gas as well as themselves.
  -- The dispatch gas is the literal slot count and the base already
  -- contains the slot telescope as a summand, so the whole floor is at
  -- most four times the base -- and the exponential clears the factor
  -- of four because `frameBlowup`'s count is itself at least the cap.
  capsAt-round-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
    4 + (sizeᵉ e + slotsSize sl) + n + n ≤ Caps.cSize (capsAt e sl id)
  capsAt-round-size {n = n} e sl zero =
    ≤-trans (four-clears (sizeᵉ e + slotsSize sl) n
               (≤-trans (n≤slotsSize sl) (m≤n+m (slotsSize sl) (sizeᵉ e))))
    (≤-trans (*-monoˡ-≤ (2 + (sizeᵉ e + slotsSize sl)) (4≤2^K e sl))
    (≤-trans (*-monoʳ-≤ (2 ^ sizeCount (gasB e sl) (capsBase e sl))
                (≤-trans (≤-reflexive (sym (+-assoc 2 (sizeᵉ e) (slotsSize sl))))
                         (m≤m+n (2 + sizeᵉ e + slotsSize sl) (slotsClos sl))))
             (iterSize-2^ (Caps.cSize (gasB e sl))
                (sizeCount (gasB e sl) (capsBase e sl))
                (Caps.cSize (gasB e sl)) (s≤s z≤n))))
  capsAt-round-size e sl (suc id) =
    ≤-trans (capsAt-round-size e sl id)
            (cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
               (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

-- and over a mapped list, which is the shape inputSize sums in
all-≤-sum : ∀ {A : Set} (f : A → ℕ) (xs : List A) (B : ℕ) →
  sum (map f xs) ≤ B → all (λ x → f x ≤ᵇ B) xs ≡ true
all-≤-sum f []       B h = refl
all-≤-sum f (x ∷ xs) B h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (f x) (sum (map f xs))) h)))
          (all-≤-sum f xs B (≤-trans (m≤n+m (sum (map f xs)) (f x)) h))

-- the width axis's counterpart of `fᵢ≤sum-tab` (.Measures): a summand never
-- exceeds the ⊔-collect, over the same tabulated index
slotsPWgo-tab : ∀ {n m} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ)
  (f : Fin m → Fin n) (i : Fin m) →
  slotPW j sl (sl (f i)) ≤ slotsPWgo j sl (tabulate f)
slotsPWgo-tab j sl f Fin.zero    = m≤m⊔n _ _
slotsPWgo-tab j sl f (Fin.suc i) =
  ≤-trans (slotsPWgo-tab j sl (λ k → f (Fin.suc k)) i) (m≤n⊔m _ _)

slotsPW-lb : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (i : Fin n) →
  slotPW j sl (sl i) ≤ slotsPW j sl
slotsPW-lb j sl i = slotsPWgo-tab j sl (λ k → k) i

-- and the same two, on the inner-width collector the innW conjunct
-- consumes
slotsIWgo-tab : ∀ {n m} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ)
  (f : Fin m → Fin n) (i : Fin m) →
  slotIW j sl (sl (f i)) ≤ slotsIWgo j sl (tabulate f)
slotsIWgo-tab j sl f Fin.zero    = m≤m⊔n _ _
slotsIWgo-tab j sl f (Fin.suc i) =
  ≤-trans (slotsIWgo-tab j sl (λ k → f (Fin.suc k)) i) (m≤n⊔m _ _)

slotsIW-lb : ∀ {n} {Γ : Ctx n} (j : ℕ) (sl : Slots Γ) (i : Fin n) →
  slotIW j sl (sl i) ≤ slotsIW j sl
slotsIW-lb j sl i = slotsIWgo-tab j sl (λ k → k) i

-- ONE SLOT, AT ITS OWN MEASURE: slotSize and slotPW are by construction
-- big enough for everything the slot holds, on their own axis
slotCaps?-self : ∀ {n} {Γ : Ctx n} {k u} (sl : Slots Γ) (s : Slot Γ k u) →
  slotCaps? (slotSize s ⊔ slotClosD (σAt sl k) s)
            (slotPW n sl s ⊔ slotIW n sl s) sl s ≡ true
slotCaps?-self {u = u} sl (scripted (hot async)) =
  ∧-intro (all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _
             (≤-trans (n≤1+n _)
                      (m≤m⊔n (inputSize (hot async)) (inputSize (hot async)))))
          (T⇒≡true _ (≤⇒≤ᵇ (m≤n⊔m (inputSize (hot async)) (inputSize (hot async)))))
slotCaps?-self {u = u} sl (scripted (cold sync async)) =
  ∧-intro (all-≤-sum (sizeᵛ u) sync _
             (≤-trans (≤-trans (m≤m+n _ _) (n≤1+n _))
                      (m≤m⊔n (inputSize (cold sync async))
                             (inputSize (cold sync async)))))
          (∧-intro (all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _
                      (≤-trans (≤-trans (m≤n+m _ _) (n≤1+n _))
                               (m≤m⊔n (inputSize (cold sync async))
                                      (inputSize (cold sync async)))))
                   (T⇒≡true _ (≤⇒≤ᵇ (m≤n⊔m (inputSize (cold sync async))
                                            (inputSize (cold sync async))))))
slotCaps?-self {n = n} {k = k} sl (shared d) =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (m≤m⊔n (sizeᵉ d) (suc (closSizeᵉ (σAt sl k) d)))))
          (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (m≤m⊔n (pWᵉ n sl d) (innWᵉ n sl d))))
                   (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (m≤n⊔m (pWᵉ n sl d) (innWᵉ n sl d))))
                            (T⇒≡true _
                              (≤⇒≤ᵇ (m≤n⊔m (sizeᵉ d)
                                            (suc (closSizeᵉ (σAt sl k) d)))))))

-- ONE SLOT'S STAGED CLOSURE READING, out of its own pricing.  This is
-- the projection the defer park spends: the environment it has to
-- dominate is `slotClos`, and every slot of it is priced by the very
-- predicate the walk already threads.
slotCaps?-clos : ∀ {n} {Γ : Ctx n} {k u} (sl : Slots Γ) (s : Slot Γ k u)
  (B W : ℕ) → slotCaps? B W sl s ≡ true → slotClosD (σAt sl k) s ≤ B
slotCaps?-clos {u = u} sl (scripted (hot async)) B W h =
  ≤ᵇ⇒≤ (inputSize (hot async)) B
    (T-to (proj₂ (∧-true (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async)
                         (inputSize (hot async) ≤ᵇ B) h)))
slotCaps?-clos {u = u} sl (scripted (cold sync async)) B W h =
  ≤ᵇ⇒≤ (inputSize (cold sync async)) B
    (T-to (proj₂ (∧-true (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async)
                         (inputSize (cold sync async) ≤ᵇ B)
      (proj₂ (∧-true (all (λ v → sizeᵛ u v ≤ᵇ B) sync)
                     (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
                        ∧ (inputSize (cold sync async) ≤ᵇ B)) h)))))
slotCaps?-clos {n = n} {k = k} sl (shared d) B W h =
  ≤ᵇ⇒≤ (suc (closSizeᵉ (σAt sl k) d)) B (T-to (proj₂ split₃))
  where
  split₁ = ∧-true (sizeᵉ d ≤ᵇ B)
                  ((pWᵉ n sl d ≤ᵇ W)
                     ∧ ((innWᵉ n sl d ≤ᵇ W)
                        ∧ (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B))) h
  split₂ = ∧-true (pWᵉ n sl d ≤ᵇ W)
                  ((innWᵉ n sl d ≤ᵇ W)
                     ∧ (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B)) (proj₂ split₁)
  split₃ = ∧-true (innWᵉ n sl d ≤ᵇ W)
                  (suc (closSizeᵉ (σAt sl k) d) ≤ᵇ B) (proj₂ split₂)

slotsCaps?-clos : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) (i : Fin n) →
  slotsCaps? B W sl ≡ true → slotClos sl i ≤ B
slotsCaps?-clos B W sl i h =
  slotCaps?-clos sl (sl i) B W (slotsCaps?-lookup B W sl i h)

slotsGo?-bound : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) (is : List (Fin n)) →
  (∀ (i : Fin n) → slotCaps? B W sl (sl i) ≡ true) → slotsGo? B W sl is ≡ true
slotsGo?-bound B W sl []       h = refl
slotsGo?-bound B W sl (i ∷ is) h = ∧-intro (h i) (slotsGo?-bound B W sl is h)

-- THE WHOLE TELESCOPE, from the two numbers capsAt's base already
-- contains
slotsCaps?-bound : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) →
  slotsSize sl ≤ B → slotsClos sl ≤ B → slotsPW n sl ≤ W → slotsIW n sl ≤ W →
  slotsCaps? B W sl ≡ true
slotsCaps?-bound {n = n} B W sl h hc hw hi =
  slotsGo?-bound B W sl (tabulate {n = n} (λ i → i))
    (λ i → slotCaps?-widen sl (sl i)
             (⊔-lub (≤-trans (fᵢ≤sum-tab (λ k → slotSize (sl k)) i) h)
                    (≤-trans (fᵢ≤sum-tab (λ k → slotClos sl k) i) hc))
             (⊔-lub (≤-trans (slotsPW-lb n sl i) hw)
                    (≤-trans (slotsIW-lb n sl i) hi))
             (slotCaps?-self sl (sl i)))

-- AND THE SAME TELESCOPE UNDER A LARGER PAIR OF NUMBERS, which is what
-- a walk needs and the bound above does not give: the slots are fixed
-- for a whole instant while the CAP the walk reports at steps, so a
-- statement carrying the slot caps has to carry them forward to the
-- stepped cap rather than re-derive them there.  Both axes widen,
-- because the frame step moves the size and the fold moves the width.
slotsCaps?-widen : ∀ {n} {Γ : Ctx n} (B B′ W W′ : ℕ) (sl : Slots Γ) →
  B ≤ B′ → W ≤ W′ → slotsCaps? B W sl ≡ true → slotsCaps? B′ W′ sl ≡ true
slotsCaps?-widen {n = n} B B′ W W′ sl le lw h =
  slotsGo?-bound B′ W′ sl (tabulate {n = n} (λ i → i))
    (λ i → slotCaps?-widen sl (sl i) le lw (slotsCaps?-lookup B W sl i h))

------------------------------------------------------------------
-- THE WIDTH HALF OF THE EVAL CLUSTER — ONE foldStep PER SYNTAX NODE.
--
-- Every one of the five evaluation obligations concludes `valCaps?`,
-- whose second conjunct is a WIDTH, and none of them carries a width
-- hypothesis that reaches it: an evaluated value is FRESH SYNTAX, so
-- its width has to come out of its SIZE.  That is affordable exactly
-- because the two recurrences are different heights — `sizeStep` is
-- multiplicative and `foldStep S w = S ^ suc w` is exponential — so the
-- folds a size receipt already buys pay for the width outright.  Three
-- pieces:
--
--   wid-iterFold        the width lemma: every width measure of an
--                       expression is bounded by ONE foldStep per
--                       syntax node, off a leaf bound M for the slot
--                       telescope.  Eval-Growth-Probe §7 reads the
--                       recurrence clause by clause — mapᵉ and the
--                       *All family fit in one fold, `scanᵉ` needs two,
--                       and its three children guarantee three.
--   pWᵛ-iterFold        the same on a runtime VALUE, whose obs
--                       components ARE expressions of exactly the size
--                       sizeᵛ reports.
--   valCaps?-fromSize   the bridge: a value bounded on the size axis at
--                       level `j + a` is bounded on BOTH at
--                       `j + (a + suc K)`, K the size cap there.
--
-- AND THE LEAF IS WHERE THE TELESCOPE COMES IN.  `input i` is a leaf of
-- the syntax (`sizeᵉ (input i) = 1`) whose width measures descend into
-- the slot instead, so the induction stops dead there unless the slot
-- side condition supplies them — which is why slotCaps? carries an innW
-- conjunct beside its pW one (Eval-Growth-Probe §8: a def with pW 0 and
-- innW 3, so no W read off pW alone bounds it).
------------------------------------------------------------------

-- iterFold COMPOSES, exactly as iterSize does: a folds then b more is
-- a + b folds
iterFold-+ : ∀ (S a b w : ℕ) →
  iterFold S (a + b) w ≡ iterFold S b (iterFold S a w)
iterFold-+ S zero    b w = refl
iterFold-+ S (suc a) b w = iterFold-+ S a b (foldStep S w)

-- ONE FOLD ABSORBS A `suc` ON THE SEED, which is the whole reason the
-- leaf bound may be read one above the width cap
suc≤foldStep : ∀ (S w : ℕ) → 2 ≤ S → suc w ≤ foldStep S w
suc≤foldStep S w hS = ≤-trans (<⇒≤ (n<2^n (suc w))) (^-monoˡ-≤ (suc w) hS)

-- ONE LEVEL OF WIDTH DOMINATES ONE MORE QUEUE ITEM, with the same
-- `suc w ≤ foldStep S w` margin the count receipts spend.  This is what
-- makes the cardinality conjunct affordable: the push is the ONLY write
-- to a concat queue that grows it (Rung-Count-Probe § 5 reads all four
-- off the evaluator — birth and re-park install `[]`, the outer-done
-- mark leaves q alone, the drain only shortens), so exactly one row
-- does arithmetic and one level pays for it
wid-suc-step : ∀ (c : Caps) (L : ℕ) → 2 ≤ Caps.cSize c →
  suc (Caps.cWid (frameStep L c)) ≤ Caps.cWid (frameStep (suc L) c)
wid-suc-step c L hS =
  subst (λ x → suc (Caps.cWid (frameStep L c)) ≤ x)
        (sym (frameStep-wid-suc c L))
        (suc≤foldStep (Caps.cSize c) (Caps.cWid (frameStep L c)) hS)

-- THE QUEUE'S LENGTH, PEELED OFF THE NODE READING.  `widNode`'s merge
-- arm is the only conjunct anywhere that reads a queue's length, and
-- this is the half of it that does.  Peeled here rather than at a use
-- site because the RESULT type pins the second Bool, leaving only the
-- first to solve -- and because `n` is in scope, so the width side needs
-- no underscore (one there sends Agda inverting `_≤ᵇ_` to depth 50).
widNode-len : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ) {u}
              (lim : Maybe ℕ) (a : ℕ) (q : List (Closed Γ u)) (b : Bool) →
              widNode W sl (mergeAll-st lim a q b) ≡ true →
              (length q ≤ᵇ W) ≡ true
widNode-len {n = n} W sl lim a q b h =
  proj₂ (∧-true (all (λ o′ → pWᵉ n sl o′ ≤ᵇ W) q) (length q ≤ᵇ W) h)

widNode-push : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (L : ℕ) (sl : Slots Γ)
  (lim : Maybe ℕ) (q : List (Closed Γ s)) (o : Closed Γ s) (act : ℕ) (od : Bool) →
  2 ≤ Caps.cSize c →
  widNode (Caps.cWid (frameStep L c)) sl (mergeAll-st lim act q od) ≡ true →
  (pWᵉ n sl o ≤ᵇ Caps.cWid (frameStep L c)) ≡ true →
  widNode (Caps.cWid (frameStep (suc L) c)) sl (mergeAll-st lim act (q ++ o ∷ []) od)
    ≡ true
widNode-push {n = n} c L sl lim q o act od hS hq ho
  with ∧-true (all (λ x → pWᵉ n sl x ≤ᵇ Caps.cWid (frameStep L c)) q)
              (length q ≤ᵇ Caps.cWid (frameStep L c)) hq
... | hall , hlen = ∧-intro pw card
  where
  W  = Caps.cWid (frameStep L c)
  W′ = Caps.cWid (frameStep (suc L) c)

  wide : W ≤ W′
  wide = ≤-trans (n≤1+n W) (wid-suc-step c L hS)

  pw : all (λ x → pWᵉ n sl x ≤ᵇ W′) (q ++ o ∷ []) ≡ true
  pw = all-++-intro (λ x → pWᵉ n sl x ≤ᵇ W′) q (o ∷ [])
         (all-impl _ _ (λ x → ≤ᵇ-widen (pWᵉ n sl x) wide) q hall)
         (∧-intro (≤ᵇ-widen (pWᵉ n sl o) wide ho) refl)

  card : (length (q ++ o ∷ []) ≤ᵇ W′) ≡ true
  card = T⇒≡true (length (q ++ o ∷ []) ≤ᵇ W′)
           (≤⇒≤ᵇ (≤-trans (≤-reflexive (trans (length-++ q) (+-comm (length q) 1)))
                          (≤-trans (s≤s (≤ᵇ⇒≤ (length q) W (T-to hlen)))
                                   (wid-suc-step c L hS))))

-- and iterFold is monotone in the SEED as well as in the count
foldStep-mono-w : ∀ (S : ℕ) {w w′ : ℕ} → 2 ≤ S → w ≤ w′ →
  foldStep S w ≤ foldStep S w′
foldStep-mono-w (suc (suc S)) (s≤s (s≤s _)) le = ^-monoʳ-≤ (suc (suc S)) (s≤s le)

iterFold-mono-w : ∀ (S k : ℕ) → 2 ≤ S → {w w′ : ℕ} → w ≤ w′ →
  iterFold S k w ≤ iterFold S k w′
iterFold-mono-w S zero    hS le = le
iterFold-mono-w S (suc k) hS le = iterFold-mono-w S k hS (foldStep-mono-w S hS le)

-- THE LIFT.  A width read at the seed `suc W` — the leaf bound the slot
-- telescope supplies — is a width read at the cap `suc q` folds on.
-- This is the one arithmetic step the five members' width halves are
iterFold-lift : ∀ (S W K q : ℕ) → 2 ≤ S →
  iterFold S K (suc W) ≤ iterFold S (suc q + K) W
iterFold-lift S W K q hS =
  ≤-trans (iterFold-mono-w S K hS
             (≤-trans (suc≤foldStep S W hS)
                      (iterFold-infl S hS q (foldStep S W))))
          (≤-reflexive (sym (iterFold-+ S (suc q) K W)))

-- the index arithmetic the bridge lands on
+-shuffle : ∀ (j a K : ℕ) → j + (a + suc K) ≡ suc (j + a) + K
+-shuffle j a K =
  trans (cong (j +_) (+-suc a K))
        (trans (+-suc j (a + K)) (cong suc (sym (+-assoc j a K))))

-- WHAT AN `input` LEAF PRESENTS TO THE WIDTH INDUCTION.  Context
-- polymorphic because the induction crosses a `deferᵉ`, which moves Δᵍ
-- into Δ, and a `μᵉ`, which extends it
SlotWid : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ → Set
SlotWid {n = n} {Γ = Γ} sl M =
  ∀ {Δᵍ Δ Θ : List Ty} (i : Fin n) →
    (outWᵉ n sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i) ≤ M)
    × (innWᵉ n sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i) ≤ M)
    × (dWᵉ n sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i) ≤ M)

------------------------------------------------------------------
-- THE WIDTH LEMMA, PROVEN, in the shape Eval-Growth-Probe §7's clause
-- analysis forces: the induction is organised at the MAX of a node's
-- children rather than at their running sum, so every non-scanᵉ node
-- spends ONE foldStep and `scanᵉ` spends TWO — funded by the three
-- children a scanᵉ node carries, each at least one syntax node.  The
-- receipt is still j′ = sizeᵉ, syntax-linear.
--
-- FIVE MEASURES AT ONCE, because the clauses cross-reference: innW's
-- mapᵉ clause reads pmI, its scanᵉ clause reads outW in an EXPONENT,
-- and pmO's *All clause reads both.  Wᴱ / Wᵀ / Wᴸ bundle them under one
-- number, which is the whole content of "arrives at each node with all
-- its children's measures already bounded by ONE accumulated M".
--
-- THE ARITHMETIC IS TWO OBLIGATIONS.  At the children's bound T (which
-- is ≥ 4 at every internal node, since one fold off a leaf bound of at
-- least 1 is already S ^ 2):
--
--   one fold    2 T² ≤ S ^ suc T          every clause but scanᵉ
--   two folds   T ^ T (3T+1) ≤ S ^ suc (S ^ suc T)      scanᵉ
--
-- and both reduce to ONE engine, `sq≤pow`: a square is under an
-- exponential from 4 on.
------------------------------------------------------------------

sqStep : ∀ (t : ℕ) → suc t * suc t ≡ t * t + suc (2 * t)
sqStep = solve 1 (λ a → (con 1 :+ a) :* (con 1 :+ a)
                      := a :* a :+ (con 1 :+ con 2 :* a)) refl

linStep : ∀ (t : ℕ) → suc (2 * suc t) ≡ suc (2 * t) + 2
linStep = solve 1 (λ a → con 1 :+ con 2 :* (con 1 :+ a)
                       := (con 1 :+ con 2 :* a) :+ con 2) refl


-- the engine, with the linear fact it needs carried alongside
sq-exp : ∀ (k : ℕ) →
  ((4 + k) * (4 + k) ≤ 2 ^ (4 + k)) × (suc (2 * (4 + k)) ≤ 2 ^ (4 + k))
sq-exp zero    = ≤ᵇ⇒≤ 16 16 tt , ≤ᵇ⇒≤ 9 16 tt
sq-exp (suc k) = SQ , LIN
  where
  t   = 4 + k
  ih  = sq-exp k
  half : 2 ^ suc t ≡ 2 ^ t + 2 ^ t
  half = 2X≡X+X (2 ^ t)
  two≤ : 2 ≤ 2 ^ t
  two≤ = ≤-trans (≤ᵇ⇒≤ 2 4 tt) (^-monoʳ-≤ 2 (≤ᵇ⇒≤ 2 t tt))
  SQ : suc t * suc t ≤ 2 ^ suc t
  SQ = ≤-trans (≤-reflexive (sqStep t))
               (≤-trans (+-mono-≤ (proj₁ ih) (proj₂ ih)) (≤-reflexive (sym half)))
  LIN : suc (2 * suc t) ≤ 2 ^ suc t
  LIN = ≤-trans (≤-reflexive (linStep t))
                (≤-trans (+-mono-≤ (proj₂ ih) two≤) (≤-reflexive (sym half)))

sq≤pow : ∀ (t : ℕ) → 4 ≤ t → t * t ≤ 2 ^ t
sq≤pow (suc zero)                     (s≤s ())
sq≤pow (suc (suc zero))               (s≤s (s≤s ()))
sq≤pow (suc (suc (suc zero)))         (s≤s (s≤s (s≤s ())))
sq≤pow (suc (suc (suc (suc k))))      _ = proj₁ (sq-exp k)

-- A1: ONE fold dominates every clause but scanᵉ.  Each of them is a
-- sum or a ⊔ of at most two products of the children's bound, so
-- `2 T²` covers them all
one-fold : ∀ (S Tb : ℕ) → 2 ≤ S → 4 ≤ Tb → 2 * (Tb * Tb) ≤ foldStep S Tb
one-fold S Tb hS hT =
  ≤-trans (*-monoʳ-≤ 2 (sq≤pow Tb hT)) (^-monoˡ-≤ (suc Tb) hS)

-- A2: TWO folds dominate the scanᵉ clause, whose innW reads
--   (pmIᵗ 0 f ⊔ 1) ^ outWᵉ e * (innWᵗ f + innWᵗ z + innWᵉ e + 1)
-- and is therefore Tb ^ Tb * (3 Tb + 1) at the children's bound
two-folds : ∀ (S Tb : ℕ) → 2 ≤ S → 4 ≤ Tb →
  Tb ^ Tb * (3 * Tb + 1) ≤ foldStep S (foldStep S Tb)
two-folds S Tb hS hT =
  ≤-trans (*-mono-≤ powT lin)
  (≤-trans (≤-reflexive (sym (^-distribˡ-+-* 2 (Tb * Tb) (2 + Tb))))
  (≤-trans (^-monoˡ-≤ (Tb * Tb + (2 + Tb)) hS)
           (powʳ S hS expfit)))
  where
  powʳ : ∀ (X : ℕ) → 2 ≤ X → ∀ {a b} → a ≤ b → X ^ a ≤ X ^ b
  powʳ (suc zero)    (s≤s ()) le
  powʳ (suc (suc X)) _        le = ^-monoʳ-≤ (suc (suc X)) le
  T≤2^T : Tb ≤ 2 ^ Tb
  T≤2^T = <⇒≤ (n<2^n Tb)
  powT : Tb ^ Tb ≤ 2 ^ (Tb * Tb)
  powT = ≤-trans (^-monoˡ-≤ Tb T≤2^T) (≤-reflexive (^-*-assoc 2 Tb Tb))
  four : ∀ x → 3 * x + x ≡ 4 * x
  four = solve 1 (λ a → con 3 :* a :+ a := con 4 :* a) refl
  lin : 3 * Tb + 1 ≤ 2 ^ (2 + Tb)
  lin = ≤-trans (≤-trans (+-monoʳ-≤ (3 * Tb) (≤-trans (s≤s z≤n) hT))
                         (≤-reflexive (four Tb)))
        (≤-trans (*-monoʳ-≤ 4 T≤2^T) (≤-reflexive (*-assoc 2 2 (2 ^ Tb))))
  expfit : Tb * Tb + (2 + Tb) ≤ suc (foldStep S Tb)
  expfit =
    ≤-trans (+-mono-≤ (sq≤pow Tb hT) (s≤s (n<2^n Tb)))
    (≤-trans (≤-reflexive (+-suc (2 ^ Tb) (2 ^ Tb)))
             (s≤s (≤-trans (≤-reflexive (sym (2X≡X+X (2 ^ Tb))))
                           (^-monoˡ-≤ (suc Tb) hS))))

------------------------------------------------------------------
-- THE INDUCTION.
------------------------------------------------------------------

powʳ1 : ∀ (X : ℕ) → 1 ≤ X → ∀ {a b} → a ≤ b → X ^ a ≤ X ^ b
powʳ1 (suc X) _ le = ^-monoʳ-≤ (suc X) le

k≤iterFold : ∀ (S k w : ℕ) → 2 ≤ S → k ≤ iterFold S k w
k≤iterFold S zero    w hS = z≤n
k≤iterFold S (suc k) w hS =
  subst (suc k ≤_) (sym (iterFold-suc S k w))
        (≤-trans (s≤s (k≤iterFold S k w hS))
                 (suc≤foldStep S (iterFold S k w) hS))

len≤sizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
  length ts ≤ sizeᵗˢ ts
len≤sizeᵗˢ []       = z≤n
len≤sizeᵗˢ (y ∷ ys) = +-mono-≤ (sizeᵗ-pos y) (len≤sizeᵗˢ ys)

-- 4 ≤ the children's bound, which is what the arithmetic core wants
4≤iterFold : ∀ (S M m : ℕ) → 2 ≤ S → 1 ≤ M → 1 ≤ m → 4 ≤ iterFold S m M
4≤iterFold S M (suc m) hS hM _ =
  ≤-trans (≤-trans (≤-trans (≤ᵇ⇒≤ 4 4 tt) (^-monoʳ-≤ 2 (s≤s hM)))
                   (^-monoˡ-≤ (suc M) hS))
          (iterFold-infl S hS m (foldStep S M))

-- everything ONE fold has to dominate, at the children's bound Tb
one-fits : ∀ (S Tb x : ℕ) → 2 ≤ S → 4 ≤ Tb → x ≤ Tb * Tb + Tb * Tb → x ≤ foldStep S Tb
one-fits S Tb x hS hT h =
  ≤-trans (≤-trans h (≤-reflexive (sym (2X≡X+X (Tb * Tb))))) (one-fold S Tb hS hT)

T≤TT : ∀ (Tb : ℕ) → 1 ≤ Tb → Tb ≤ Tb * Tb
T≤TT Tb hT = ≤-trans (≤-reflexive (sym (*-identityʳ Tb))) (*-monoʳ-≤ Tb hT)


Wᴱ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Slots Γ → ℕ → Exp Γ Δᵍ Δ Θ t → Set
Wᴱ {n = n} sl M e = (outWᵉ n sl e ≤ M) × (innWᵉ n sl e ≤ M)
                  × ((k : ℕ) → pmOᵉ n sl k e ≤ M) × ((k : ℕ) → pmIᵉ n sl k e ≤ M)

Wᵀ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Slots Γ → ℕ → Tm Γ Δᵍ Δ Θ t → Set
Wᵀ {n = n} sl M tm = (innWᵗ n sl tm ≤ M)
                   × ((k : ℕ) → pmOᵗ n sl k tm ≤ M) × ((k : ℕ) → pmIᵗ n sl k tm ≤ M)

Wᴸ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Slots Γ → ℕ → List (Tm Γ Δᵍ Δ Θ t) → Set
Wᴸ {n = n} sl M ts = (innWᵗˢ n sl ts ≤ M) × ((k : ℕ) → pmIᵗˢ n sl k ts ≤ M)

Wᴱ-mono : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) {M M′ : ℕ}
  (e : Exp Γ Δᵍ Δ Θ t) → M ≤ M′ → Wᴱ sl M e → Wᴱ sl M′ e
Wᴱ-mono sl e le (a , b , c , d) =
  ≤-trans a le , ≤-trans b le , (λ k → ≤-trans (c k) le) , (λ k → ≤-trans (d k) le)

Wᵀ-mono : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) {M M′ : ℕ}
  (tm : Tm Γ Δᵍ Δ Θ t) → M ≤ M′ → Wᵀ sl M tm → Wᵀ sl M′ tm
Wᵀ-mono sl tm le (a , c , d) =
  ≤-trans a le , (λ k → ≤-trans (c k) le) , (λ k → ≤-trans (d k) le)

Wᴸ-mono : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) {M M′ : ℕ}
  (ts : List (Tm Γ Δᵍ Δ Θ t)) → M ≤ M′ → Wᴸ sl M ts → Wᴸ sl M′ ts
Wᴸ-mono sl ts le (a , d) = ≤-trans a le , (λ k → ≤-trans (d k) le)

node1 : ∀ (S M m N : ℕ) → 2 ≤ S → suc m ≤ N →
  foldStep S (iterFold S m M) ≤ iterFold S N M
node1 S M m N hS le =
  ≤-trans (≤-reflexive (sym (iterFold-suc S m M))) (iterFold-mono-count S M hS le)

node2 : ∀ (S M m N : ℕ) → 2 ≤ S → suc (suc m) ≤ N →
  foldStep S (foldStep S (iterFold S m M)) ≤ iterFold S N M
node2 S M m N hS le =
  ≤-trans (≤-reflexive (sym (trans (iterFold-suc S (suc m) M)
                                   (cong (foldStep S) (iterFold-suc S m M)))))
          (iterFold-mono-count S M hS le)

thr : ∀ (x : ℕ) → x + x + x + 1 ≡ 3 * x + 1
thr = solve 1 (λ a → a :+ a :+ a :+ con 1 := con 3 :* a :+ con 1) refl

thr3 : ∀ (x : ℕ) → x + x + x ≡ 3 * x
thr3 = solve 1 (λ a → a :+ a :+ a := con 3 :* a) refl

-- suc of the ⊔ of two positives is under their sum, and likewise three
max2-suc : ∀ (a b : ℕ) → 1 ≤ a → 1 ≤ b → suc (a ⊔ b) ≤ a + b
max2-suc a b ha hb = ⊔-lub p q
  where
  p : suc a ≤ a + b
  p = ≤-trans (≤-reflexive (sym (+-comm a 1))) (+-monoʳ-≤ a hb)
  q : suc b ≤ a + b
  q = +-monoˡ-≤ b ha

max3-suc : ∀ (a b c : ℕ) → 1 ≤ a → 1 ≤ b → 1 ≤ c → suc (a ⊔ b ⊔ c) ≤ a + b + c
max3-suc a b c ha hb hc =
  ≤-trans (max2-suc (a ⊔ b) c (≤-trans ha (m≤m⊔n a b)) hc)
          (+-monoˡ-≤ c (⊔-lub (m≤m+n a b) (m≤n+m b a)))

------------------------------------------------------------------
-- THE FUEL COLUMN.  outWᵉ and innWᵉ take their `input` clauses FIRST,
-- so their case trees split on the slot fuel at the root and every
-- other clause is STUCK at a variable fuel — which is what a structural
-- induction over the syntax has.  (dWᵉ takes `input` last for exactly
-- this reason; the comment on it in Rx.Frame-Width says so.)  Rather
-- than reorder a measure the whole design reads, the induction below
-- unsticks each constructor once, here.
------------------------------------------------------------------

module Red {n} {Γ : Ctx n} {vs : List (Fin n)} where
  oW-of : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    outWⱽ q vs sl (ofᵉ ts) ≡ length ts
  oW-of zero    sl ts = refl
  oW-of (suc _) sl ts = refl

  oW-empty : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} →
    outWⱽ q vs sl (emptyᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {t = t}) ≡ 0
  oW-empty zero    sl  = refl
  oW-empty (suc _) sl  = refl

  oW-map : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ s t) (e : Exp Γ Δᵍ Δ Θ s) →
    outWⱽ q vs sl (mapᵉ f e) ≡ outWⱽ q vs sl e
  oW-map zero    sl f e = refl
  oW-map (suc _) sl f e = refl

  oW-take : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (c : Tm Γ Δᵍ Δ Θ natᵗ) (e : Exp Γ Δᵍ Δ Θ t) →
    outWⱽ q vs sl (takeᵉ c e) ≡ outWⱽ q vs sl e
  oW-take zero    sl c e = refl
  oW-take (suc _) sl c e = refl

  oW-scan : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (e : Exp Γ Δᵍ Δ Θ s) →
    outWⱽ q vs sl (scanᵉ f z e) ≡ outWⱽ q vs sl e
  oW-scan zero    sl f z e = refl
  oW-scan (suc _) sl f z e = refl

  oW-mergeAll : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (lim : Maybe ℕ) (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWⱽ q vs sl (mergeAllᵉ lim e) ≡ outWⱽ q vs sl e * innWⱽ q vs sl e
  oW-mergeAll zero    sl lim e = refl
  oW-mergeAll (suc _) sl lim e = refl

  oW-switch : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWⱽ q vs sl (switchAllᵉ e) ≡ outWⱽ q vs sl e * innWⱽ q vs sl e
  oW-switch zero    sl e = refl
  oW-switch (suc _) sl e = refl

  oW-exhaust : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWⱽ q vs sl (exhaustAllᵉ e) ≡ outWⱽ q vs sl e * innWⱽ q vs sl e
  oW-exhaust zero    sl e = refl
  oW-exhaust (suc _) sl e = refl

  oW-μ : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ (t ∷ Δᵍ) Δ Θ t) →
    outWⱽ q vs sl (μᵉ e) ≡ outWⱽ q vs sl e
  oW-μ zero    sl e = refl
  oW-μ (suc _) sl e = refl

  oW-var : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (x : t ∈ Δ) →
    outWⱽ q vs sl (varᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Θ = Θ} x) ≡ 0
  oW-var zero    sl x = refl
  oW-var (suc _) sl x = refl

  oW-defer : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ [] (Δᵍ ++ Δ) Θ t) →
    outWⱽ q vs sl (deferᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} e) ≡ 0
  oW-defer zero    sl e = refl
  oW-defer (suc _) sl e = refl

  iW-of : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    innWⱽ q vs sl (ofᵉ ts) ≡ innWᵗˢⱽ q vs sl ts
  iW-of zero    sl ts = refl
  iW-of (suc _) sl ts = refl

  iW-empty : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} →
    innWⱽ q vs sl (emptyᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {t = t}) ≡ 0
  iW-empty zero    sl  = refl
  iW-empty (suc _) sl  = refl

  iW-map : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ s t) (e : Exp Γ Δᵍ Δ Θ s) →
    innWⱽ q vs sl (mapᵉ f e) ≡ innWᵗⱽ q vs sl f + (pmIᵗⱽ q vs sl 0 f ⊔ 1) * innWⱽ q vs sl e
  iW-map zero    sl f e = refl
  iW-map (suc _) sl f e = refl

  iW-take : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (c : Tm Γ Δᵍ Δ Θ natᵗ) (e : Exp Γ Δᵍ Δ Θ t) →
    innWⱽ q vs sl (takeᵉ c e) ≡ innWⱽ q vs sl e
  iW-take zero    sl c e = refl
  iW-take (suc _) sl c e = refl

  iW-scan : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ s t} (f : Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t) (z : Tm Γ Δᵍ Δ Θ t) (e : Exp Γ Δᵍ Δ Θ s) →
    innWⱽ q vs sl (scanᵉ f z e) ≡ (pmIᵗⱽ q vs sl 0 f ⊔ 1) ^ outWⱽ q vs sl e * (innWᵗⱽ q vs sl f + innWᵗⱽ q vs sl z + innWⱽ q vs sl e + 1)
  iW-scan zero    sl f z e = refl
  iW-scan (suc _) sl f z e = refl

  iW-mergeAll : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (lim : Maybe ℕ) (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    innWⱽ q vs sl (mergeAllᵉ lim e) ≡ innWⱽ q vs sl e
  iW-mergeAll zero    sl lim e = refl
  iW-mergeAll (suc _) sl lim e = refl

  iW-switch : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    innWⱽ q vs sl (switchAllᵉ e) ≡ innWⱽ q vs sl e
  iW-switch zero    sl e = refl
  iW-switch (suc _) sl e = refl

  iW-exhaust : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    innWⱽ q vs sl (exhaustAllᵉ e) ≡ innWⱽ q vs sl e
  iW-exhaust zero    sl e = refl
  iW-exhaust (suc _) sl e = refl

  iW-μ : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ (t ∷ Δᵍ) Δ Θ t) →
    innWⱽ q vs sl (μᵉ e) ≡ innWⱽ q vs sl e
  iW-μ zero    sl e = refl
  iW-μ (suc _) sl e = refl

  iW-var : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (x : t ∈ Δ) →
    innWⱽ q vs sl (varᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Θ = Θ} x) ≡ 0
  iW-var zero    sl x = refl
  iW-var (suc _) sl x = refl

  iW-defer : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ [] (Δᵍ ++ Δ) Θ t) →
    innWⱽ q vs sl (deferᵉ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} e) ≡ 0
  iW-defer zero    sl e = refl
  iW-defer (suc _) sl e = refl

------------------------------------------------------------------
-- AND THE VISITED-SET ORDER, the second axis the same induction walks.
-- A bigger visited set is a SHORTER descent, so it is ANTITONE: the
-- measure at `i ∷ vs` sits under the measure at `vs`, because the
-- revisit clause hands back 0 where the unmarked one descends.  `Sub`
-- is the ⊆ the induction threads, and the only two instances the tree
-- ever needs are `Sub [] vs` (vacuous) and its closure under a shared
-- slot's own index.
------------------------------------------------------------------

Sub : ∀ {n} → List (Fin n) → List (Fin n) → Set
Sub {n} vs vs′ = (k : Fin n) → k ∈ᵇ vs ≡ true → k ∈ᵇ vs′ ≡ true

-- stated UNFOLDED, both of them: `Sub` is a Π under a definition, and
-- the LHS checker will not split past a pattern whose type is one
Sub-[] : ∀ {n} {vs : List (Fin n)} (k : Fin n) → k ∈ᵇ [] ≡ true → k ∈ᵇ vs ≡ true
Sub-[] k ()

Sub-∷ : ∀ {n} (i : Fin n) {vs vs′ : List (Fin n)} → Sub vs vs′ →
  (k : Fin n) → k ∈ᵇ (i ∷ vs) ≡ true → k ∈ᵇ (i ∷ vs′) ≡ true
Sub-∷ i {vs} {vs′} hv k = go (toℕ k ≡ᵇ toℕ i)
  where
  go : ∀ (b : Bool) → (if b then true else k ∈ᵇ vs) ≡ true
                    → (if b then true else k ∈ᵇ vs′) ≡ true
  go true  _  = refl
  go false h  = hv k h

