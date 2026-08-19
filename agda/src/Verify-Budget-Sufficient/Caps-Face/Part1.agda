-- STRATUM 2a of Verify-Budget-Sufficient: THE CAPS FACE (round 4).
--
-- Everything STATED IN TERMS OF the per-instant cap recurrence: the state
-- predicate capsOK?, the in-flight predicates (valCaps? / eventCaps? /
-- burstCaps? / obsCaps?), the frame face and the cascade companions,
-- caps-tick DERIVED from those, and the reachability cluster
-- (reach-resets) that pays round 3's debt.
--
-- THE SUBSCRIBE CLIQUE LEFT ON 2026-08-03, for .Subscribe-Face.  The
-- caps face itself (subscribeE-caps), the twelve companions mutual with
-- it, and the four delivery leaves that call it are a SUFFIX of this
-- module — reverse-reachability from the clique reaches nothing else
-- here, and stepFrame-FACE never calls stepFrame-CAPS — so they are now
-- a module of their own that imports this one public.  The ~45-clause
-- subscribe grind therefore re-checks 1.9k lines, not this file's 6.5k
-- (18 minutes cold).
--
-- THE RECURRENCE ITSELF LIVES IN .Caps as of 2026-08-01 — the Caps
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

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _∸_; _≤_; _<_;
                                _⊔_; _≤ᵇ_; _<ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl;
                                       ≤-reflexive; <-≤-trans; ≤-pred;
                                       +-suc; +-identityʳ;
                                       +-comm; +-assoc; +-monoʳ-<;
                                       +-monoˡ-<; +-monoˡ-≤;
                                       *-monoˡ-≤; *-monoʳ-≤;
                                       m⊔n≤o⇒m≤o; m⊔n≤o⇒n≤o; ⊔-mono-≤;
                                       *-suc; m≤m+n; m≤n+m; n≤1+n;
                                       m≤n⇒m<n∨m≡n; +-mono-≤; m≤m*n;
                                       ^-monoʳ-≤; *-assoc;
                                       +-mono-<-≤; +-mono-≤-<; ≡⇒≡ᵇ;
                                       *-distribʳ-+; *-distribˡ-+; *-identityʳ; <⇒≤;
                                       ^-monoˡ-≤; ^-*-assoc;
                                       ^-distribˡ-+-*; *-mono-≤;
                                       +-monoʳ-≤; *-comm;
                                       m≤m⊔n; m≤n⊔m; ⊔-lub; *-zeroʳ; *-identityˡ;
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡)
open import Data.Empty   using (⊥; ⊥-elim)
open import Data.Nat.Induction  using (<-wellFounded)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; concat; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.Bool.Properties using (∨-zeroʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++; length-map)
open import Data.List.Membership.Propositional.Properties
  using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import Rx.Prim      using (Fuel; Tick; Id; Source; InstEmit;
                                _at_from_as_; EmitKind; subscribe;
                                InstEvent; init; value; close; handoff;
                                complete; exhausted; delivery;
                                Gas; g0; gs; gasDouble; gasPow2; gasTower; gasPad;
                                Timed; after_,_; ObservableInput; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; isData;
                                Ctx; Closed; Val; sizeᵉ; sizeᵗ; sizeᵗˢ; sizeᵛ;
                                syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ;
                                shellSizeᵉ; innerᵉ; innerᵗ; innerᵗˢ;
                                subΘExp; subΘTm; subΘTms;
                                varIx;
                                renExp; renTm; renTms; Ren∈; ext∈; ++Ren;
                                wkExp; wkTm; reify;
                                Exp; Tm; Fn; varᵗ; unit̂; bool̂; nat̂; pairᵗ;
                                fstᵗ; sndᵗ; inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ;
                                strmᵗ; add; sub; mul; eqᵖ; ltᵖ; notᵖ;
                                input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                                mergeAllᵉ; concatAllᵉ; switchAllᵉ;
                                exhaustAllᵉ; μᵉ; varᵉ; deferᵉ;
                                elimGExp; elimGTm; elimGTms;
                                elimDExp; elimDTm; elimDTms;
                                compare∈; _⊟_; ⊟-++ˡ; ⊟-++ʳ; unfoldμ;
                                evalWith; evalTm; applyFn; lookupEnv)
open import Rx.Frame-Width using (pWᵉ; pWᵛ; dWᵉ; dWᵗ; dWᵗˢ; dWᵛ; outWᵛ;
                                outWᵉ; innWᵉ; innWᵗ; innWᵗˢ;
                                pmOᵉ; pmOᵗ; pmIᵉ; pmIᵗ; pmIᵗˢ;
                                _∈ᵇ_; outWⱽ; innWⱽ; innWᵗⱽ; innWᵗˢⱽ;
                                pmOⱽ; pmOᵗⱽ; pmIⱽ; pmIᵗⱽ; pmIᵗˢⱽ;
                                dWⱽ; dWᵗⱽ; dWᵗˢⱽ;
                                slotPW; slotsPW; slotsPWgo;
                                slotIW; slotsIW; slotsIWgo;
                                slotsPW≤entryCeil; slotsIW≤entryCeil)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; LiveSource;
                                Slot; scripted; shared; resolve; mkHot;
                                arrVal; scanVals; memberSource;
                                slotSize; inputSize;
                                RegId; Chain;
                                NodeState; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                oneShotBurst; installNode; setNode; lookupNode;
                                NodeId;
                                root; share-sink; _↠_; Frame; AllOp;
                                map-f; scan-f; take-f; from-inner;
                                thru-outer; Stream;
                                sched-init; st-init; sched-next;
                                schedHeadOf; schedGo; schedEarlier;
                                cascadeLatch; cascadeFinish; sweepLive;
                                takeVals; takeDispatch; cutThrough; pathHasNode;
                                dropSource; arrSource; chainsOf; chainsGo; cascadeGo;
                                Path; arrTy;
                                subscribeE; stepFrame; pushBurst;
                                subscribeInner; chainStep; subscribeAll;
                                mintNode; mintSource; mintOrdinal; register;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ;
                                splitEvents; splitBurst; retagEvents;
                                mergeBump; switchKill;
                                thruConsume; thruWalk; thruWrap;
                                concatDrain; innerFinish; innerReact;
                                sizeAt;
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                dryBurst;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize; fCharge; regAt;
                                sizeStep; iterSize; foldStep; iterFold;
                                fLvl; fLvlD; iterL; dLvl; lvls;
                                sIterD; sLvlD)

-- .Delivery-Walk re-exports BOTH prerequisites of the cascade
-- conjuncts and adds the walk itself:
--
--   · .Caps holds the recurrence (Caps / frameStep / frameBlowup /
--     capsAt and their supply lemmas) and re-exports .Keeps-Ring, hence
--     .Measures.  Extracted 2026-08-01 so that a grind here no longer
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
open import Verify-Budget-Sufficient.Delivery-Walk public
-- the nesting measure the subscribe budget descends on, and the frame
-- row that supplies it.  Re-exported, so the clique names one module
open import Verify-Budget-Sufficient.Caps-Nest public
-- the depth mirror: `depthInner` is the fuel `thruOuter-face-core`'s
-- new hypothesis ranges over (see below, ~6307).  The rest of the family
-- carries THE DEPTH PREMISE down the frame chain, and it threads by
-- IDENTITY because the mirror is definitionally equal at every hop:
--   depthFrame … (from-inner op allNid inst) … fin = depthReact … fin
--   depthReact … true  = depthFin … (lookupNode allNid (EvalSt.nodes st))
--   depthReact … false = 0
-- so each face passes its premise straight to the next and the absorbed
-- branch needs nothing at all
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFrame; depthReact; depthFin; depthWalk; depthCascade;
         depthConsume)
-- arithmetic lemmas consumed by thruOuter-face-core's walk helpers
open import Verify-Budget-Sufficient.Caps-Chain
  using (walk-nil; inner-nil; walk-index; frame-step; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd using (walk-step-suc)

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

-- the frame-width half of the state predicate.  NOT widthOK? — that is
-- ofW, a per-NODE width, and om-is-not-a-frame-budget is the
-- counterexample to conflating the two
widLive : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → LiveSource Γ → Bool
widLive {n = n} W sl l =
  all (λ tv → pWᵛ n sl (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ W)
      (LiveSource.pending l)

-- THE CONCAT CLAUSE CARRIES A CARDINALITY as well as the pointwise
-- bound, and it has to: `concatDrain` subscribes one inner per queued
-- observable, so the drain's receipt is a sum over the queue, and
-- NOTHING else in the tree bounds how long that queue is — the
-- hypothesis concatDrain-caps is given admits a queue of any length at
-- all, and so does an `all` (Rung-Count-Probe § 2, both rows).  One
-- level of width pays for one cons, with the same `suc w ≤ foldStep S w`
-- margin the count receipts already spend
widNode : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
widNode {n = n} W sl (scan-st {t} v)   = pWᵛ n sl t v ≤ᵇ W
widNode {n = n} W sl (concat-st q _ _) =
  all (λ o → pWᵉ n sl o ≤ᵇ W) q ∧ (length q ≤ᵇ W)
widNode W sl (take-st _)               = true
widNode W sl (merge-st _ _)            = true
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
pathSz? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathSz? B root           = true
pathSz? B (share-sink i) = true
pathSz? B (f ↠ p)        = frameSz? B f ∧ ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p)

regsSz? : ∀ {n} {Γ : Ctx n} {t} → ℕ → List (RegId × Source × Chain Γ t) → Bool
regsSz? B = all (λ en → pathSz? B (proj₂ (proj₂ (proj₂ en))))

capsOK? : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Caps → Sched Γ → EvalSt e → Bool
capsOK? c sched st =
  stBounded? (Caps.cSize c) sched st
  ∧ regsSz? (Caps.cSize c) (EvalSt.registry st)
  ∧ all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched)
  ∧ all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
        (EvalSt.nodes st)
  ∧ (length (EvalSt.registry st) ≤ᵇ Caps.cReg c)

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
widNode-widen {n = n} sl (concat-st q _ _) {W} {W′} le h
  with ∧-true (all (λ o → pWᵉ n sl o ≤ᵇ W) q) (length q ≤ᵇ W) h
... | hall , hlen =
  ∧-intro (all-impl _ _ (λ o → ≤ᵇ-widen (pWᵉ n sl o) le) q hall)
          (≤ᵇ-widen (length q) le hlen)
widNode-widen sl (take-st _)     le h = refl
widNode-widen sl (merge-st _ _)  le h = refl
widNode-widen sl (switch-st _ _) le h = refl
widNode-widen sl (exhaust-st _ _) le h = refl

capsOK?-mono : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c c′ : Caps) (sched : Sched Γ) (st : EvalSt e) →
  c ⊑ᶜ c′ → capsOK? c sched st ≡ true → capsOK? c′ sched st ≡ true
capsOK?-mono c c′ sched st (sz≤ , wd≤ , rg≤) h
  with ∧-true _ _ h
... | hSt , hRest with ∧-true _ _ hRest
... | hRg , hRest2 with ∧-true _ _ hRest2
... | hWL , hRest3 with ∧-true _ _ hRest3
... | hWN , hLen =
  ∧-intro (stBounded-widen sz≤ sched st hSt)
  (∧-intro (regsSz?-widen (EvalSt.registry st) sz≤ hRg)
  (∧-intro (all-impl _ _ (λ l → widLive-widen (Sched.slots sched) l wd≤)
                     (Sched.live sched) hWL)
  (∧-intro (all-impl _ _ (λ kv → widNode-widen (Sched.slots sched) (proj₂ kv) wd≤)
                     (EvalSt.nodes st) hWN)
           (≤ᵇ-widen (length (EvalSt.registry st)) rg≤ hLen))))

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

-- EACH FOLD AT LEAST DOUBLES.  This is the whole of what the strmᵗ
-- clause needs: a body of k nodes buys a factor of 2 ^ k, which covers
-- the `sizeᵉ e` multiplier size-subΘᵉ charges for substituting into it
iterSize-2^ : ∀ (S k s : ℕ) → 1 ≤ S → 2 ^ k * s ≤ iterSize S k s
iterSize-2^ S zero    s hS = ≤-reflexive (*-identityˡ s)
iterSize-2^ S (suc k) s hS =
  ≤-trans (≤-reflexive shape)
          (≤-trans (*-monoʳ-≤ (2 ^ k) 2s≤step)
                   (iterSize-2^ S k (sizeStep S s) hS))
  where
  shape : 2 ^ suc k * s ≡ 2 ^ k * (2 * s)
  shape = solve 2 (λ a b → (con 2 :* a) :* b := a :* (con 2 :* b))
                refl (2 ^ k) s
  2s≤step : 2 * s ≤ sizeStep S s
  2s≤step = ≤-trans (n≤1+n (2 * s))
                    (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                             (*-monoˡ-≤ (suc (2 * s)) hS))

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

-- observables in a concat queue: the caps side of concatDrain's
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
slotCaps? {u = u} B W sl (scripted (cold sync async)) =
  all (λ v → sizeᵛ u v ≤ᵇ B) sync
  ∧ all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
slotCaps? {n = n} B W sl (shared d) =
  (sizeᵉ d ≤ᵇ B) ∧ ((pWᵉ n sl d ≤ᵇ W) ∧ (innWᵉ n sl d ≤ᵇ W))

slotsGo? : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Slots Γ → List (Fin n) → Bool
slotsGo? B W sl []       = true
slotsGo? B W sl (i ∷ is) = slotCaps? B W sl (sl i) ∧ slotsGo? B W sl is

slotsCaps? : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Slots Γ → Bool
slotsCaps? {n = n} B W sl = slotsGo? B W sl (tabulate {n = n} (λ i → i))

slotCaps?-widen : ∀ {n} {Γ : Ctx n} {k u} (sl : Slots Γ) (s : Slot Γ k u)
  {B B′ W W′ : ℕ} →
  B ≤ B′ → W ≤ W′ → slotCaps? B W sl s ≡ true → slotCaps? B′ W′ sl s ≡ true
slotCaps?-widen {u = u} sl (scripted (hot async)) le lw h =
  all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async h
slotCaps?-widen {u = u} sl (scripted (cold sync async)) le lw h =
  ∧-intro (all-impl _ _ (λ v → ≤ᵇ-widen (sizeᵛ u v) le) sync
             (proj₁ (∧-true _ _ h)))
          (all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async
             (proj₂ (∧-true _ _ h)))
slotCaps?-widen {n = n} sl (shared d) {B} {B′} {W} {W′} le lw h =
  ∧-intro (≤ᵇ-widen (sizeᵉ d) le (proj₁ split₁))
          (∧-intro (≤ᵇ-widen (pWᵉ n sl d) lw (proj₁ split₂))
                   (≤ᵇ-widen (innWᵉ n sl d) lw (proj₂ split₂)))
  where
  split₁ = ∧-true (sizeᵉ d ≤ᵇ B)
                  ((pWᵉ n sl d ≤ᵇ W) ∧ (innWᵉ n sl d ≤ᵇ W)) h
  split₂ = ∧-true (pWᵉ n sl d ≤ᵇ W) (innWᵉ n sl d ≤ᵇ W) (proj₂ split₁)

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

-- a summand never exceeds the sum, over a tabulated index
sum-tabulate-lb : ∀ {n} (f : Fin n → ℕ) (i : Fin n) → f i ≤ sum (tabulate f)
sum-tabulate-lb {suc n} f Fin.zero    = m≤m+n (f Fin.zero) _
sum-tabulate-lb {suc n} f (Fin.suc i) =
  ≤-trans (sum-tabulate-lb (λ k → f (Fin.suc k)) i) (m≤n+m _ _)

-- EVERY SLOT COSTS AT LEAST ONE, so the slot COUNT is under the caps'
-- own size — the supply behind the `n ≤ cSize` hypothesis the delivery
-- bound now carries.  `cDel`'s gas index is `suc (cSize c)` while the
-- evaluator's dispatch gas is the literal `n` (chainStep seeds it), and
-- nothing in capsOK? relates the two: the relation is a fact about the
-- SLOT TELESCOPE, and it is true at every level because capsAt's base
-- contains slotsSize as a summand and iterSize only grows it
-- (1≤slotSize / n≤sum-tab / n≤slotsSize MOVED DOWN to .Measures
-- 2026-08-19, where slotHop-sup also needs them.  They are still in
-- scope here, through this module's `public` import chain.)
n≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  n ≤ Caps.cSize (capsAt e sl id)
n≤capsAt-size e sl id =
  ≤-trans (≤-trans (n≤slotsSize sl) (m≤n+m (slotsSize sl) (2 + sizeᵉ e)))
          (capsAt-base-size e sl id)

-- and over a mapped list, which is the shape inputSize sums in
all-≤-sum : ∀ {A : Set} (f : A → ℕ) (xs : List A) (B : ℕ) →
  sum (map f xs) ≤ B → all (λ x → f x ≤ᵇ B) xs ≡ true
all-≤-sum f []       B h = refl
all-≤-sum f (x ∷ xs) B h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (f x) (sum (map f xs))) h)))
          (all-≤-sum f xs B (≤-trans (m≤n+m (sum (map f xs)) (f x)) h))

-- the width axis's counterpart of sum-tabulate-lb: a summand never
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
  slotCaps? (slotSize s) (slotPW n sl s ⊔ slotIW n sl s) sl s ≡ true
slotCaps?-self {u = u} sl (scripted (hot async)) =
  all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _ (n≤1+n _)
slotCaps?-self {u = u} sl (scripted (cold sync async)) =
  ∧-intro (all-≤-sum (sizeᵛ u) sync _
             (≤-trans (m≤m+n _ _) (n≤1+n _)))
          (all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _
             (≤-trans (m≤n+m _ _) (n≤1+n _)))
slotCaps?-self {n = n} sl (shared d) =
  ∧-intro (T⇒≡true (sizeᵉ d ≤ᵇ sizeᵉ d) (≤⇒≤ᵇ (≤-refl {sizeᵉ d})))
          (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (m≤m⊔n (pWᵉ n sl d) (innWᵉ n sl d))))
                   (T⇒≡true _ (≤⇒≤ᵇ (m≤n⊔m (pWᵉ n sl d) (innWᵉ n sl d)))))

slotsGo?-bound : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) (is : List (Fin n)) →
  (∀ (i : Fin n) → slotCaps? B W sl (sl i) ≡ true) → slotsGo? B W sl is ≡ true
slotsGo?-bound B W sl []       h = refl
slotsGo?-bound B W sl (i ∷ is) h = ∧-intro (h i) (slotsGo?-bound B W sl is h)

-- THE WHOLE TELESCOPE, from the two numbers capsAt's base already
-- contains
slotsCaps?-bound : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) →
  slotsSize sl ≤ B → slotsPW n sl ≤ W → slotsIW n sl ≤ W →
  slotsCaps? B W sl ≡ true
slotsCaps?-bound {n = n} B W sl h hw hi =
  slotsGo?-bound B W sl (tabulate {n = n} (λ i → i))
    (λ i → slotCaps?-widen sl (sl i)
             (≤-trans (sum-tabulate-lb (λ k → slotSize (sl k)) i) h)
             (⊔-lub (≤-trans (slotsPW-lb n sl i) hw)
                    (≤-trans (slotsIW-lb n sl i) hi))
             (slotCaps?-self sl (sl i)))

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

widNode-push : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (L : ℕ) (sl : Slots Γ)
  (q : List (Closed Γ s)) (o : Closed Γ s) (act od : Bool) →
  2 ≤ Caps.cSize c →
  widNode (Caps.cWid (frameStep L c)) sl (concat-st q act od) ≡ true →
  (pWᵉ n sl o ≤ᵇ Caps.cWid (frameStep L c)) ≡ true →
  widNode (Caps.cWid (frameStep (suc L) c)) sl (concat-st (q ++ o ∷ []) act od)
    ≡ true
widNode-push {n = n} c L sl q o act od hS hq ho
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

-- AND THE DRAIN ONLY EVER SHORTENS, which is the row that reinstalls
-- the residue.  `concatDrain` returns `[]` when it runs the queue out,
-- the recursive residue when the head completed, and the TAIL when it
-- did not — never anything longer than what it was given, so the
-- cardinality conjunct survives the reinstall by widening alone
concatDrain-qlen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  length (proj₁ (proj₂ (proj₂ (proj₂ (concatDrain g allNid κ id now q sched st)))))
    ≤ length q
concatDrain-qlen g allNid κ id now []      sched st = z≤n
concatDrain-qlen g allNid κ id now (o ∷ q) sched st
  with subscribeInner g concatᵒ allNid κ id now o sched st
... | _ , vs , bs , false , sched₁ , st₁ = n≤1+n (length q)
... | _ , vs , bs , true  , sched₁ , st₁ =
  ≤-trans (concatDrain-qlen g allNid κ id now q sched₁ st₁) (n≤1+n (length q))


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

ite≤ : ∀ (b : Bool) {N : ℕ} → 1 ≤ N → (if b then 1 else 0) ≤ N
ite≤ true  h = h
ite≤ false h = z≤n

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

  oW-merge : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWⱽ q vs sl (mergeAllᵉ e) ≡ outWⱽ q vs sl e * innWⱽ q vs sl e
  oW-merge zero    sl e = refl
  oW-merge (suc _) sl e = refl

  oW-concat : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWⱽ q vs sl (concatAllᵉ e) ≡ outWⱽ q vs sl e * innWⱽ q vs sl e
  oW-concat zero    sl e = refl
  oW-concat (suc _) sl e = refl

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

  iW-merge : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    innWⱽ q vs sl (mergeAllᵉ e) ≡ innWⱽ q vs sl e
  iW-merge zero    sl e = refl
  iW-merge (suc _) sl e = refl

  iW-concat : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    innWⱽ q vs sl (concatAllᵉ e) ≡ innWⱽ q vs sl e
  iW-concat zero    sl e = refl
  iW-concat (suc _) sl e = refl

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

