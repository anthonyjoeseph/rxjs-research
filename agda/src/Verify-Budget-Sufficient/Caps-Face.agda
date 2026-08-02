-- STRATUM 2a of Verify-Budget-Sufficient: THE CAPS FACE (round 4).
--
-- Everything STATED IN TERMS OF the per-instant cap recurrence: the state
-- predicate capsOK?, the in-flight predicates (valCaps? / eventCaps? /
-- burstCaps? / obsCaps?), the caps face itself (subscribeE-caps) and the
-- companion tree it is decomposed into, caps-tick DERIVED from the
-- cascade companions, and the reachability cluster (reach-resets) that
-- pays round 3's debt.
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
module Verify-Budget-Sufficient.Caps-Face where

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
open import Data.List    using (List; []; _∷_; _++_; all; any; length;
                                sum; tabulate; concat; map)
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
open import Data.List.Properties using (length-++)
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
                                shellsᵉ; shellsᵛ;
                                subΘExp; subΘTm; subΘTms;
                                plugsᵉ; plugsᵗ; plugsᵗˢ;
                                occsᵉ; occsᵗ; occsᵗˢ; varIx;
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
                                dWⱽ; dWᵗⱽ; dWᵗˢⱽ; pWⱽ;
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
                                sharedPlumb; sharedConnect; subscribeSharedSlot;
                                burstCompleted;
                                shareLatch; shareAdmit; shareFinish; shareGo;
                                dryBurst;
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize; fCharge; regAt;
                                sizeStep; iterSize; foldStep; iterFold)

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
--   · .Delivery-Walk maps the delivery clique onto dCap / dWalk —
--     foldPath ↦ dCap, dispatchShare ↦ dCap, shareGo ↦ dWalk,
--     cascadeGo ↦ dWalk — RELATIVE to one frame's mint budget, which it
--     takes as a record of hypotheses rather than postulating.  See
--     cascadeGo-deliveries below for what instantiating it still needs.
open import Verify-Budget-Sufficient.Delivery-Walk public

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

widNode : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
widNode {n = n} W sl (scan-st {t} v)   = pWᵛ n sl t v ≤ᵇ W
widNode {n = n} W sl (concat-st q _ _) = all (λ o → pWᵉ n sl o ≤ᵇ W) q
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
widNode-widen {n = n} sl (concat-st q _ _) le h =
  all-impl _ _ (λ o → ≤ᵇ-widen (pWᵉ n sl o) le) q h
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

S≤sizeStep : ∀ (S s : ℕ) → S ≤ sizeStep S s
S≤sizeStep S s = m≤m*n S (suc (2 * s))

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
slotCaps? : ∀ {n} {Γ : Ctx n} {u} → ℕ → ℕ → Slots Γ → Slot Γ u → Bool
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

slotCaps?-widen : ∀ {n} {Γ : Ctx n} {u} (sl : Slots Γ) (s : Slot Γ u)
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

slotsGo?-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (is : List (Fin n))
  {B B′ W W′ : ℕ} →
  B ≤ B′ → W ≤ W′ → slotsGo? B W sl is ≡ true → slotsGo? B′ W′ sl is ≡ true
slotsGo?-widen sl []       le lw h = refl
slotsGo?-widen sl (i ∷ is) le lw h =
  ∧-intro (slotCaps?-widen sl (sl i) le lw (proj₁ (∧-true _ _ h)))
          (slotsGo?-widen sl is le lw (proj₂ (∧-true _ _ h)))

slotsCaps?-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) {B B′ W W′ : ℕ} →
  B ≤ B′ → W ≤ W′ → slotsCaps? B W sl ≡ true → slotsCaps? B′ W′ sl ≡ true
slotsCaps?-widen {n = n} sl le lw = slotsGo?-widen sl (tabulate {n = n} (λ i → i)) le lw

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
1≤slotSize : ∀ {n} {Γ : Ctx n} {t} (s : Slot Γ t) → 1 ≤ slotSize s
1≤slotSize (scripted (hot _))    = s≤s z≤n
1≤slotSize (scripted (cold _ _)) = s≤s z≤n
1≤slotSize (shared d)            = sizeᵉ-pos d

n≤sum-tab : ∀ {n} (f : Fin n → ℕ) → (∀ (i : Fin n) → 1 ≤ f i) →
  n ≤ sum (tabulate f)
n≤sum-tab {zero}  f h = z≤n
n≤sum-tab {suc n} f h =
  +-mono-≤ (h Fin.zero) (n≤sum-tab (λ k → f (Fin.suc k)) (λ k → h (Fin.suc k)))

n≤slotsSize : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → n ≤ slotsSize sl
n≤slotsSize sl = n≤sum-tab (λ i → slotSize (sl i)) (λ i → 1≤slotSize (sl i))

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
slotCaps?-self : ∀ {n} {Γ : Ctx n} {u} (sl : Slots Γ) (s : Slot Γ u) →
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

dbl : ∀ (y : ℕ) → 2 * y ≡ y + y
dbl = solve 1 (λ a → con 2 :* a := a :+ a) refl

-- the engine, with the linear fact it needs carried alongside
sq-exp : ∀ (k : ℕ) →
  ((4 + k) * (4 + k) ≤ 2 ^ (4 + k)) × (suc (2 * (4 + k)) ≤ 2 ^ (4 + k))
sq-exp zero    = ≤ᵇ⇒≤ 16 16 tt , ≤ᵇ⇒≤ 9 16 tt
sq-exp (suc k) = SQ , LIN
  where
  t   = 4 + k
  ih  = sq-exp k
  half : 2 ^ suc t ≡ 2 ^ t + 2 ^ t
  half = dbl (2 ^ t)
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
             (s≤s (≤-trans (≤-reflexive (sym (dbl (2 ^ Tb))))
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
  ≤-trans (≤-trans h (≤-reflexive (sym (dbl (Tb * Tb))))) (one-fold S Tb hS hT)

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

------------------------------------------------------------------
-- ONE foldStep PER SYNTAX NODE, TWO AT scanᵉ.
------------------------------------------------------------------

module _ (S M : ℕ) (hS : 2 ≤ S) (hM : 1 ≤ M) where

  mutual
    widᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → Wᴱ sl (iterFold S (sizeᵉ e) M) e
    widᵉ {n = n} sl hI (input i) =
      ≤-trans (proj₁ (hI i)) INFL , ≤-trans (proj₁ (proj₂ (hI i))) INFL
      , (λ k → z≤n) , (λ k → z≤n)
      where INFL = foldStep-infl S M hS
    widᵉ {n = n} sl hI emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty n sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty n sl)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} sl hI (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var n sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var n sl x)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} sl hI (deferᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-defer n sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer n sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    widᵉ {n = n} sl hI (ofᵉ ts) =
      ≤-trans (≤-reflexive (Red.oW-of n sl ts))
              (up (≤-trans (len≤sizeᵗˢ ts) (k≤iterFold S (sizeᵗˢ ts) M hS)))
      , ≤-trans (≤-reflexive (Red.iW-of n sl ts)) (up (proj₁ IH))
      , (λ k → z≤n) , (λ k → up (proj₂ IH k))
      where
      IH = widᵗˢ sl hI ts
      up : ∀ {x} → x ≤ iterFold S (sizeᵗˢ ts) M → x ≤ iterFold S (suc (sizeᵗˢ ts)) M
      up h = ≤-trans (≤-trans h (foldStep-infl S _ hS))
                     (node1 S M (sizeᵗˢ ts) (suc (sizeᵗˢ ts)) hS ≤-refl)
    widᵉ {n = n} sl hI (mapᵉ f e) =
      ≤-trans (≤-reflexive (Red.oW-map n sl f e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-map n sl f e)) (FIT INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → FIT (PMI k))
      where
      m   = sizeᵗ f ⊔ sizeᵉ e
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM (≤-trans (sizeᵗ-pos f) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ f) (sizeᵉ e)))
              (widᵗ sl hI f)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ f) (sizeᵉ e)))
              (widᵉ sl hI e)
      step = node1 S M m (suc (sizeᵗ f + sizeᵉ e)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ f) (sizeᵉ e)) (m≤n+m (sizeᵉ e) (sizeᵗ f))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ f + sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵗ f + sizeᵉ e)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      INN : innWᵗ n sl f + (pmIᵗ n sl 0 f ⊔ 1) * innWᵉ n sl e ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (proj₁ IHf) (T≤TT Tb 1≤T))
                     (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T) (proj₁ (proj₂ IHe)))
      PMI : ∀ k → pmIᵗ n sl (suc k) f + (pmIᵗ n sl 0 f ⊔ 1) * pmIᵉ n sl k e
                    ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (proj₂ (proj₂ IHf) (suc k)) (T≤TT Tb 1≤T))
                       (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T)
                                 (proj₂ (proj₂ (proj₂ IHe)) k))
    widᵉ {n = n} sl hI (takeᵉ c e) =
      ≤-trans (≤-reflexive (Red.oW-take n sl c e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-take n sl c e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵗ c + sizeᵉ e)) hS
               (s≤s (m≤n+m (sizeᵉ e) (sizeᵗ c)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c + sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵉ {n = n} sl hI (mergeAllᵉ e) =
      allClause sl hI e (mergeAllᵉ e) (Red.oW-merge n sl e) (Red.iW-merge n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (concatAllᵉ e) =
      allClause sl hI e (concatAllᵉ e) (Red.oW-concat n sl e) (Red.iW-concat n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (switchAllᵉ e) =
      allClause sl hI e (switchAllᵉ e) (Red.oW-switch n sl e) (Red.iW-switch n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (exhaustAllᵉ e) =
      allClause sl hI e (exhaustAllᵉ e) (Red.oW-exhaust n sl e) (Red.iW-exhaust n sl e)
                (λ k → refl) (λ k → refl)
    widᵉ {n = n} sl hI (μᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-μ n sl e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-μ n sl e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵉ {n = n} sl hI (scanᵉ f z e) =
      ≤-trans (≤-reflexive (Red.oW-scan n sl f z e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-scan n sl f z e)) (FIT2 INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k)) , (λ k → FIT2 (PMI k))
      where
      m   = sizeᵗ f ⊔ sizeᵗ z ⊔ sizeᵉ e
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos f) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e)))) (widᵗ sl hI f)
      IHz = Wᵀ-mono sl z (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e)))) (widᵗ sl hI z)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ f ⊔ sizeᵗ z) (sizeᵉ e))) (widᵉ sl hI e)
      Σ3    = sizeᵗ f + sizeᵗ z + sizeᵉ e
      step2 = node2 S M m (suc Σ3) hS
                (s≤s (max3-suc (sizeᵗ f) (sizeᵗ z) (sizeᵉ e)
                        (sizeᵗ-pos f) (sizeᵗ-pos z) (sizeᵉ-pos e)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc Σ3) M
      up0 h = ≤-trans (≤-trans (≤-trans h (foldStep-infl S Tb hS))
                               (foldStep-infl S (foldStep S Tb) hS)) step2
      FIT2 : ∀ {x} → x ≤ Tb ^ Tb * (3 * Tb + 1) → x ≤ iterFold S (suc Σ3) M
      FIT2 h = ≤-trans (≤-trans h (two-folds S Tb hS hT)) step2
      base≤ : pmIᵗ n sl 0 f ⊔ 1 ≤ Tb
      base≤ = ⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T
      pw : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e ≤ Tb ^ Tb
      pw = ≤-trans (^-monoˡ-≤ (outWᵉ n sl e) base≤) (powʳ1 Tb 1≤T (proj₁ IHe))
      INN : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
              * (innWᵗ n sl f + innWᵗ n sl z + innWᵉ n sl e + 1)
            ≤ Tb ^ Tb * (3 * Tb + 1)
      INN = *-mono-≤ pw
              (≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                           (proj₁ (proj₂ IHe)))
                                 (≤-refl {1}))
                       (≤-reflexive (thr Tb)))
      PMI : ∀ k → (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
                    * (pmIᵗ n sl (suc k) f + pmIᵗ n sl k z + pmIᵉ n sl k e)
                  ≤ Tb ^ Tb * (3 * Tb + 1)
      PMI k = *-mono-≤ pw
                (≤-trans (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                             (proj₂ (proj₂ IHz) k))
                                   (proj₂ (proj₂ (proj₂ IHe)) k))
                         (≤-trans (≤-reflexive (thr3 Tb)) (m≤m+n (3 * Tb) 1)))

    -- the four *All nodes, which share a clause: the reduction
    -- equations come in as arguments so the four differ only in which
    -- constructor they name
    allClause : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ (obs t)) (E : Exp Γ Δᵍ Δ Θ t) →
      outWᵉ n sl E ≡ outWᵉ n sl e * innWᵉ n sl e →
      innWᵉ n sl E ≡ innWᵉ n sl e →
      ((k : ℕ) → pmOᵉ n sl k E
                   ≡ outWᵉ n sl e * pmIᵉ n sl k e + pmOᵉ n sl k e * innWᵉ n sl e) →
      ((k : ℕ) → pmIᵉ n sl k E ≡ pmIᵉ n sl k e) →
      Wᴱ sl (iterFold S (suc (sizeᵉ e)) M) E
    allClause {n = n} sl hI e E eo ei ep eq =
      ≤-trans (≤-reflexive eo)
              (FIT (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                            (m≤m+n (Tb * Tb) (Tb * Tb))))
      , ≤-trans (≤-reflexive ei) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → ≤-trans (≤-reflexive (ep k))
                 (FIT (+-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                                (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                          (proj₁ (proj₂ IHe))))))
      , (λ k → ≤-trans (≤-reflexive (eq k)) (up0 (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      Tb    = iterFold S (sizeᵉ e) M
      hT   = 4≤iterFold S M (sizeᵉ e) hS hM (sizeᵉ-pos e)
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step

    widᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (tm : Tm Γ Δᵍ Δ Θ t) → Wᵀ sl (iterFold S (sizeᵗ tm) M) tm
    widᵗ sl hI (varᵗ x) =
      z≤n , (λ k → z≤n)
      , (λ k → ite≤ _ (≤-trans (≤ᵇ⇒≤ 1 4 tt) (4≤iterFold S M 1 hS hM ≤-refl)))
    widᵗ sl hI unit̂        = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (bool̂ _)    = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (nat̂ _)     = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (primᵗ _ a) = z≤n , (λ k → z≤n) , (λ k → z≤n)
    widᵗ sl hI (pairᵗ a b) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      m   = sizeᵗ a ⊔ sizeᵗ b
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI a)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI b)
      step = node1 S M m (suc (sizeᵗ a + sizeᵗ b)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ a) (sizeᵗ b)) (m≤n+m (sizeᵗ b) (sizeᵗ a))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ a + sizeᵗ b)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ sl hI (fstᵗ p) = unary sl hI p
    widᵗ sl hI (sndᵗ p) = unary sl hI p
    widᵗ sl hI (inlᵗ p) = unary sl hI p
    widᵗ sl hI (inrᵗ p) = unary sl hI p
    widᵗ sl hI (strmᵗ e) =
      up0 (proj₁ IHe) , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      where
      Tb    = iterFold S (sizeᵉ e) M
      IHe  = widᵉ sl hI e
      step = node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ sl hI (ifᵗ c a b) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      m   = sizeᵗ a ⊔ sizeᵗ b
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI a)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))
              (widᵗ sl hI b)
      step = node1 S M m (suc (sizeᵗ c + sizeᵗ a + sizeᵗ b)) hS
               (s≤s (⊔-lub (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                    (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                           (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c + sizeᵗ a + sizeᵗ b)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    widᵗ {n = n} sl hI (caseᵗ s l r) =
      FIT INN , (λ k → FIT (PMO k)) , (λ k → FIT (PMI k))
      where
      m   = sizeᵗ s ⊔ sizeᵗ l ⊔ sizeᵗ r
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos s) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHs = Wᵀ-mono sl s (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ s) (sizeᵗ l)) (m≤m⊔n _ (sizeᵗ r)))) (widᵗ sl hI s)
      IHl = Wᵀ-mono sl l (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ s) (sizeᵗ l)) (m≤m⊔n _ (sizeᵗ r)))) (widᵗ sl hI l)
      IHr = Wᵀ-mono sl r (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ s ⊔ sizeᵗ l) (sizeᵗ r))) (widᵗ sl hI r)
      step = node1 S M m (suc (sizeᵗ s + sizeᵗ l + sizeᵗ r)) hS
               (s≤s (⊔-lub (⊔-lub (≤-trans (m≤m+n (sizeᵗ s) (sizeᵗ l))
                                           (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r)))
                                  (≤-trans (m≤n+m (sizeᵗ l) (sizeᵗ s))
                                           (m≤m+n (sizeᵗ s + sizeᵗ l) (sizeᵗ r))))
                           (m≤n+m (sizeᵗ r) (sizeᵗ s + sizeᵗ l))))
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb →
            x ≤ iterFold S (suc (sizeᵗ s + sizeᵗ l + sizeᵗ r)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      C≤ : pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1 ≤ Tb
      C≤ = ⊔-lub (⊔-lub (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) 1≤T
      INN : (innWᵗ n sl l ⊔ innWᵗ n sl r)
              + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * innWᵗ n sl s
            ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (⊔-lub (proj₁ IHl) (proj₁ IHr)) (T≤TT Tb 1≤T))
                     (*-mono-≤ C≤ (proj₁ IHs))
      PMO : ∀ k → pmOᵗ n sl (suc k) l ⊔ pmOᵗ n sl (suc k) r
                    ⊔ (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmOᵗ n sl k s
                  ≤ Tb * Tb + Tb * Tb
      PMO k = ⊔-lub (≤-trans (⊔-lub (proj₁ (proj₂ IHl) (suc k))
                                    (proj₁ (proj₂ IHr) (suc k)))
                             (≤-trans (T≤TT Tb 1≤T) (m≤m+n _ _)))
                    (≤-trans (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)) (m≤m+n _ _))
      PMI : ∀ k → (pmIᵗ n sl (suc k) l ⊔ pmIᵗ n sl (suc k) r)
                    + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmIᵗ n sl k s
                  ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (⊔-lub (proj₂ (proj₂ IHl) (suc k))
                                       (proj₂ (proj₂ IHr) (suc k)))
                                (T≤TT Tb 1≤T))
                       (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k))

    unary : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (p : Tm Γ Δᵍ Δ Θ t) →
      (innWᵗ n sl p ≤ iterFold S (suc (sizeᵗ p)) M)
      × ((k : ℕ) → pmOᵗ n sl k p ≤ iterFold S (suc (sizeᵗ p)) M)
      × ((k : ℕ) → pmIᵗ n sl k p ≤ iterFold S (suc (sizeᵗ p)) M)
    unary sl hI p =
      up0 (proj₁ IH) , (λ k → up0 (proj₁ (proj₂ IH) k))
      , (λ k → up0 (proj₂ (proj₂ IH) k))
      where
      Tb    = iterFold S (sizeᵗ p) M
      IH   = widᵗ sl hI p
      step = node1 S M (sizeᵗ p) (suc (sizeᵗ p)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ p)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step

    widᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (ts : List (Tm Γ Δᵍ Δ Θ t)) → Wᴸ sl (iterFold S (sizeᵗˢ ts) M) ts
    widᵗˢ sl hI []       = z≤n , (λ k → z≤n)
    widᵗˢ sl hI (y ∷ ys) =
      ⊔-lub (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-lub (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = Wᵀ-mono sl y (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)))
               (widᵗ sl hI y)
      IHys = Wᴸ-mono sl ys (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)))
               (widᵗˢ sl hI ys)

  -- THE PARKED HALF.  dW is a plain ⊔-collect with one exception —
  -- `dWᵉ (deferᵉ e) = outWᵉ e ⊔ dWᵉ e`, the clause the family exists for
  -- — so it costs no fold anywhere and reads the delivered half above
  -- at the defer
  mutual
    wdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ n sl e ≤ iterFold S (sizeᵉ e) M
    wdᵉ sl hI (input i) = ≤-trans (proj₂ (proj₂ (hI i))) (foldStep-infl S M hS)
    wdᵉ sl hI emptyᵉ    = z≤n
    wdᵉ sl hI (varᵉ x)  = z≤n
    wdᵉ sl hI (ofᵉ ts)  =
      ≤-trans (wdᵗˢ sl hI ts)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗˢ ts) (suc (sizeᵗˢ ts)) hS ≤-refl))
    wdᵉ sl hI (deferᵉ e) =
      ≤-trans (⊔-lub (proj₁ (widᵉ sl hI e)) (wdᵉ sl hI e))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl))
    wdᵉ sl hI (mapᵉ f e) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI f) (mono (m≤m⊔n (sizeᵗ f) (sizeᵉ e))))
                     (≤-trans (wdᵉ sl hI e) (mono (m≤n⊔m (sizeᵗ f) (sizeᵉ e)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ f ⊔ sizeᵉ e) (suc (sizeᵗ f + sizeᵉ e)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ f) (sizeᵉ e))
                                     (m≤n+m (sizeᵉ e) (sizeᵗ f))))))
      where mono = iterFold-mono-count S M hS
    wdᵉ sl hI (takeᵉ c e) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI c) (mono (m≤m⊔n (sizeᵗ c) (sizeᵉ e))))
                     (≤-trans (wdᵉ sl hI e) (mono (m≤n⊔m (sizeᵗ c) (sizeᵉ e)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ c ⊔ sizeᵉ e) (suc (sizeᵗ c + sizeᵉ e)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ c) (sizeᵉ e))
                                     (m≤n+m (sizeᵉ e) (sizeᵗ c))))))
      where mono = iterFold-mono-count S M hS
    wdᵉ sl hI (scanᵉ f z e) =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wdᵗ sl hI f) (mono up-f))
                            (≤-trans (wdᵗ sl hI z) (mono up-z)))
                     (≤-trans (wdᵉ sl hI e) (mono up-e)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ f + sizeᵗ z + sizeᵉ e)) hS
                         (≤-trans (max3-suc (sizeᵗ f) (sizeᵗ z) (sizeᵉ e)
                                     (sizeᵗ-pos f) (sizeᵗ-pos z) (sizeᵉ-pos e))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ f ⊔ sizeᵗ z ⊔ sizeᵉ e
      mono = iterFold-mono-count S M hS
      up-f = ≤-trans (m≤m⊔n (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e))
      up-z = ≤-trans (m≤n⊔m (sizeᵗ f) (sizeᵗ z)) (m≤m⊔n _ (sizeᵉ e))
      up-e = m≤n⊔m (sizeᵗ f ⊔ sizeᵗ z) (sizeᵉ e)
    wdᵉ sl hI (mergeAllᵉ e)   = pass sl hI e
    wdᵉ sl hI (concatAllᵉ e)  = pass sl hI e
    wdᵉ sl hI (switchAllᵉ e)  = pass sl hI e
    wdᵉ sl hI (exhaustAllᵉ e) = pass sl hI e
    wdᵉ sl hI (μᵉ e)          = pass sl hI e

    pass : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ n sl e ≤ iterFold S (suc (sizeᵉ e)) M
    pass sl hI e =
      ≤-trans (wdᵉ sl hI e)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e) (suc (sizeᵉ e)) hS ≤-refl))

    wdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗ n sl tm ≤ iterFold S (sizeᵗ tm) M
    wdᵗ sl hI (varᵗ x)  = z≤n
    wdᵗ sl hI unit̂      = z≤n
    wdᵗ sl hI (bool̂ _)  = z≤n
    wdᵗ sl hI (nat̂ _)   = z≤n
    wdᵗ sl hI (strmᵗ e) = pass sl hI e
    wdᵗ sl hI (fstᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (sndᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (inlᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (inrᵗ p)  = passᵗ sl hI p
    wdᵗ sl hI (primᵗ _ p) = passᵗ sl hI p
    wdᵗ sl hI (pairᵗ a b) =
      ≤-trans (⊔-lub (≤-trans (wdᵗ sl hI a) (mono (m≤m⊔n (sizeᵗ a) (sizeᵗ b))))
                     (≤-trans (wdᵗ sl hI b) (mono (m≤n⊔m (sizeᵗ a) (sizeᵗ b)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ a ⊔ sizeᵗ b) (suc (sizeᵗ a + sizeᵗ b)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ a) (sizeᵗ b))
                                     (m≤n+m (sizeᵗ b) (sizeᵗ a))))))
      where mono = iterFold-mono-count S M hS
    wdᵗ sl hI (caseᵗ s l r) = three sl hI s l r
    wdᵗ sl hI (ifᵗ c a b)   = three sl hI c a b

    passᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (p : Tm Γ Δᵍ Δ Θ t) → dWᵗ n sl p ≤ iterFold S (suc (sizeᵗ p)) M
    passᵗ sl hI p =
      ≤-trans (wdᵗ sl hI p)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ p) (suc (sizeᵗ p)) hS ≤-refl))

    three : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ₁ Θ₂ Θ₃ t u v} (sl : Slots Γ) → SlotWid sl M →
      (a : Tm Γ Δᵍ Δ Θ₁ t) (b : Tm Γ Δᵍ Δ Θ₂ u) (c : Tm Γ Δᵍ Δ Θ₃ v) →
      dWᵗ n sl a ⊔ dWᵗ n sl b ⊔ dWᵗ n sl c
        ≤ iterFold S (suc (sizeᵗ a + sizeᵗ b + sizeᵗ c)) M
    three sl hI a b c =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wdᵗ sl hI a) (mono up-a))
                            (≤-trans (wdᵗ sl hI b) (mono up-b)))
                     (≤-trans (wdᵗ sl hI c) (mono up-c)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ a + sizeᵗ b + sizeᵗ c)) hS
                         (≤-trans (max3-suc (sizeᵗ a) (sizeᵗ b) (sizeᵗ c)
                                     (sizeᵗ-pos a) (sizeᵗ-pos b) (sizeᵗ-pos c))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ a ⊔ sizeᵗ b ⊔ sizeᵗ c
      mono = iterFold-mono-count S M hS
      up-a = ≤-trans (m≤m⊔n (sizeᵗ a) (sizeᵗ b)) (m≤m⊔n _ (sizeᵗ c))
      up-b = ≤-trans (m≤n⊔m (sizeᵗ a) (sizeᵗ b)) (m≤m⊔n _ (sizeᵗ c))
      up-c = m≤n⊔m (sizeᵗ a ⊔ sizeᵗ b) (sizeᵗ c)

    wdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) → SlotWid sl M →
      (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢ n sl ts ≤ iterFold S (sizeᵗˢ ts) M
    wdᵗˢ sl hI []       = z≤n
    wdᵗˢ sl hI (y ∷ ys) =
      ⊔-lub (≤-trans (wdᵗ sl hI y)
                     (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y) (sizeᵗˢ ys))))
            (≤-trans (wdᵗˢ sl hI ys)
                     (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys) (sizeᵗ y))))

-- THE LEMMA, assembled
wid-iterFold : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
  (outWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
  × (innWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
  × (dWᵉ n sl e ≤ iterFold S (sizeᵉ e) M)
wid-iterFold S M hS hM sl hI e =
  proj₁ (widᵉ S M hS hM sl hI e)
  , proj₁ (proj₂ (widᵉ S M hS hM sl hI e))
  , wdᵉ S M hS hM sl hI e

------------------------------------------------------------------
-- AND THE TELESCOPE SUPPLIES THE LEAF, at ONE above the width cap.
-- The shared branch is slotCaps?'s pW and innW conjuncts read one
-- CONNECT down — `outWᵉ (suc j) sl (input i)` is `outWᵉ j sl d`, one
-- fuel below what the conjunct states — and the scripted branch is the
-- constant 1 that outWᵉ / innWᵉ hand back for a data payload, which is
-- what the `suc` pays for.
------------------------------------------------------------------

-- THE MEASURES ARE MONOTONE IN THE SLOT FUEL AND ANTITONE IN THE
-- VISITED SET, and it is ONE induction because only the `input` clauses
-- read either.  More fuel means a deeper descent into the slot
-- telescope; a bigger visited set means a shorter one, since a revisit
-- hands back 0.  Every other clause is a ⊔, a sum, a product or an
-- exponential of the children, all monotone in all of them.
--
-- BOTH AXES AT ONCE is what the leaf needs.  The slot side condition is
-- stated at the ENTRY form (`vs = []`, since capsOK? bounds a STORED
-- value and a stored value carries no record of which connect put it
-- there), while the width induction meets an `input` leaf one CONNECT
-- below it AND with that slot's own index already marked.  The bridge
-- is therefore `q ≤ q′` together with `Sub vs′ vs`, and `Sub [] _` is
-- vacuous — which is exactly the instance slotsCaps?-slotWid uses.
module _ {n} {Γ : Ctx n} (sl : Slots Γ) where

  MonoE : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → Exp Γ Δᵍ Δ Θ t → Set
  MonoE q vs q′ vs′ e = (outWⱽ q vs sl e ≤ outWⱽ q′ vs′ sl e)
               × (innWⱽ q vs sl e ≤ innWⱽ q′ vs′ sl e)
               × ((k : ℕ) → pmOⱽ q vs sl k e ≤ pmOⱽ q′ vs′ sl k e)
               × ((k : ℕ) → pmIⱽ q vs sl k e ≤ pmIⱽ q′ vs′ sl k e)

  MonoT : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → Tm Γ Δᵍ Δ Θ t → Set
  MonoT q vs q′ vs′ tm = (innWᵗⱽ q vs sl tm ≤ innWᵗⱽ q′ vs′ sl tm)
                × ((k : ℕ) → pmOᵗⱽ q vs sl k tm ≤ pmOᵗⱽ q′ vs′ sl k tm)
                × ((k : ℕ) → pmIᵗⱽ q vs sl k tm ≤ pmIᵗⱽ q′ vs′ sl k tm)

  MonoL : ∀ {Δᵍ Δ Θ t} → ℕ → List (Fin n) → ℕ → List (Fin n) → List (Tm Γ Δᵍ Δ Θ t) → Set
  MonoL q vs q′ vs′ ts = (innWᵗˢⱽ q vs sl ts ≤ innWᵗˢⱽ q′ vs′ sl ts)
                × ((k : ℕ) → pmIᵗˢⱽ q vs sl k ts ≤ pmIᵗˢⱽ q′ vs′ sl k ts)

  mutual
    monoᵉ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → MonoE q vs q′ vs′ e
    monoᵉ q {q′} le hv (ofᵉ ts) =
      ≤-reflexive (trans (Red.oW-of q sl ts) (sym (Red.oW-of q′ sl ts)))
      , ≤-trans (≤-reflexive (Red.iW-of q sl ts))
                (≤-trans (proj₁ (monoᵗˢ q le hv ts))
                         (≤-reflexive (sym (Red.iW-of q′ sl ts))))
      , (λ k → z≤n)
      , (λ k → proj₂ (monoᵗˢ q le hv ts) k)
    monoᵉ q {q′} le hv emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty q sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty q sl)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var q sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var q sl x)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv {Δᵍ} {Δ} {Θ} (deferᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-defer q sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer q sl {Δᵍ} {Δ} {Θ} e)) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ q {q′} le hv (mapᵉ f e) =
      ≤-trans (≤-reflexive (Red.oW-map q sl f e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-map q′ sl f e))))
      , ≤-trans (≤-reflexive (Red.iW-map q sl f e))
                (≤-trans (+-mono-≤ (proj₁ IHf)
                            (*-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl)
                                      (proj₁ (proj₂ IHe))))
                         (≤-reflexive (sym (Red.iW-map q′ sl f e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → +-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                 (*-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl)
                           (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      IHf = monoᵗ q le hv f
      IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (takeᵉ c e) =
      ≤-trans (≤-reflexive (Red.oW-take q sl c e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-take q′ sl c e))))
      , ≤-trans (≤-reflexive (Red.iW-take q sl c e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-take q′ sl c e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le {vs} {vs′} hv (scanᵉ f z e) =
      ≤-trans (≤-reflexive (Red.oW-scan q sl f z e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-scan q′ sl f z e))))
      , ≤-trans (≤-reflexive (Red.iW-scan q sl f z e))
                (≤-trans (*-mono-≤ POW
                            (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                                (proj₁ (proj₂ IHe)))
                                      ≤-refl))
                         (≤-reflexive (sym (Red.iW-scan q′ sl f z e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → *-mono-≤ POW
                 (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                     (proj₂ (proj₂ IHz) k))
                           (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      IHf = monoᵗ q le hv f
      IHz = monoᵗ q le hv z
      IHe = monoᵉ q le hv e
      POW : (pmIᵗⱽ q vs sl 0 f ⊔ 1) ^ outWⱽ q vs sl e
              ≤ (pmIᵗⱽ q′ vs′ sl 0 f ⊔ 1) ^ outWⱽ q′ vs′ sl e
      POW = ≤-trans (^-monoˡ-≤ (outWⱽ q vs sl e)
                      (⊔-mono-≤ (proj₂ (proj₂ IHf) 0) ≤-refl))
                    (powʳ1 (pmIᵗⱽ q′ vs′ sl 0 f ⊔ 1)
                           (m≤n⊔m (pmIᵗⱽ q′ vs′ sl 0 f) 1) (proj₁ IHe))
    monoᵉ q {q′} le hv (mergeAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-merge q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-merge q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-merge q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-merge q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (concatAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-concat q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-concat q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-concat q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-concat q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (switchAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-switch q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-switch q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-switch q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-switch q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (exhaustAllᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-exhaust q sl e))
              (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                       (≤-reflexive (sym (Red.oW-exhaust q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-exhaust q sl e))
                (≤-trans (proj₁ (proj₂ IHe))
                         (≤-reflexive (sym (Red.iW-exhaust q′ sl e))))
      , (λ k → +-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                        (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                  (proj₁ (proj₂ IHe))))
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵉ q {q′} le hv (μᵉ e) =
      ≤-trans (≤-reflexive (Red.oW-μ q sl e))
              (≤-trans (proj₁ IHe) (≤-reflexive (sym (Red.oW-μ q′ sl e))))
      , ≤-trans (≤-reflexive (Red.iW-μ q sl e))
                (≤-trans (proj₁ (proj₂ IHe)) (≤-reflexive (sym (Red.iW-μ q′ sl e))))
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₂ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    -- THE ONLY CLAUSE THAT READS THE FUEL, and the only place the
    -- induction descends on it rather than on the syntax
    monoᵉ zero {q′} le hv (input i) = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    monoᵉ (suc q) {suc q′} (s≤s le) {vs} {vs′} hv (input i) with i ∈ᵇ vs′ in eq′
    -- the RIGHT side has already entered this slot, so the left has too
    ... | true rewrite hv i eq′ = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    ... | false with i ∈ᵇ vs
    -- only the LEFT has: a revisit delivers nothing, and 0 bounds all
    ...   | true  = z≤n , z≤n , (λ k → z≤n) , (λ k → z≤n)
    ...   | false with sl i
    ...     | scripted _ = ≤-refl , ≤-refl , (λ k → z≤n) , (λ k → z≤n)
    ...     | shared d   = proj₁ IH , proj₁ (proj₂ IH) , (λ k → z≤n) , (λ k → z≤n)
      where IH = monoᵉ q le {i ∷ vs} {i ∷ vs′} (Sub-∷ i {vs′} {vs} hv) d

    monoᵗ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → MonoT q vs q′ vs′ tm
    monoᵗ q {q′} le hv (varᵗ x)   = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv unit̂       = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (bool̂ _)   = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (nat̂ _)    = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (primᵗ _ a) = ≤-refl , (λ k → ≤-refl) , (λ k → ≤-refl)
    monoᵗ q {q′} le hv (pairᵗ a b) =
      ⊔-mono-≤ (proj₁ IHa) (proj₁ IHb)
      , (λ k → ⊔-mono-≤ (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k))
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k))
      where
      IHa = monoᵗ q le hv a
      IHb = monoᵗ q le hv b
    monoᵗ q {q′} le hv (fstᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (sndᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (inlᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (inrᵗ p) = monoᵗ q le hv p
    monoᵗ q {q′} le hv (ifᵗ c a b) =
      ⊔-mono-≤ (proj₁ IHa) (proj₁ IHb)
      , (λ k → ⊔-mono-≤ (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k))
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k))
      where
      IHa = monoᵗ q le hv a
      IHb = monoᵗ q le hv b
    monoᵗ q {q′} le hv (strmᵗ e) =
      proj₁ IHe , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      , (λ k → proj₁ (proj₂ (proj₂ IHe)) k)
      where IHe = monoᵉ q le hv e
    monoᵗ q {q′} le hv (caseᵗ s l r) =
      +-mono-≤ (⊔-mono-≤ (proj₁ IHl) (proj₁ IHr)) (*-mono-≤ C≤ (proj₁ IHs))
      , (λ k → ⊔-mono-≤ (⊔-mono-≤ (proj₁ (proj₂ IHl) (suc k))
                                  (proj₁ (proj₂ IHr) (suc k)))
                        (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)))
      , (λ k → +-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHl) (suc k))
                                  (proj₂ (proj₂ IHr) (suc k)))
                        (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k)))
      where
      IHs = monoᵗ q le hv s
      IHl = monoᵗ q le hv l
      IHr = monoᵗ q le hv r
      C≤ = ⊔-mono-≤ (⊔-mono-≤ (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) ≤-refl

    monoᵗˢ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → MonoL q vs q′ vs′ ts
    monoᵗˢ q {q′} le hv []       = ≤-refl , (λ k → ≤-refl)
    monoᵗˢ q {q′} le hv (y ∷ ys) =
      ⊔-mono-≤ (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-mono-≤ (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = monoᵗ q le hv y
      IHys = monoᵗˢ q le hv ys

  -- and the parked half, which reads the delivered one at a defer
  mutual
    monoᴰᵉ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (e : Exp Γ Δᵍ Δ Θ t) → dWⱽ q vs sl e ≤ dWⱽ q′ vs′ sl e
    monoᴰᵉ q le hv (ofᵉ ts)        = monoᴰᵗˢ q le hv ts
    monoᴰᵉ q le hv emptyᵉ          = z≤n
    monoᴰᵉ q le hv (varᵉ x)        = z≤n
    monoᴰᵉ q le hv (mapᵉ f e)      = ⊔-mono-≤ (monoᴰᵗ q le hv f) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (takeᵉ c e)     = ⊔-mono-≤ (monoᴰᵗ q le hv c) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (scanᵉ f z e)   =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv f) (monoᴰᵗ q le hv z)) (monoᴰᵉ q le hv e)
    monoᴰᵉ q le hv (mergeAllᵉ e)   = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (concatAllᵉ e)  = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (switchAllᵉ e)  = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (exhaustAllᵉ e) = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (μᵉ e)          = monoᴰᵉ q le hv e
    monoᴰᵉ q le hv (deferᵉ e)      =
      ⊔-mono-≤ (proj₁ (monoᵉ q le hv e)) (monoᴰᵉ q le hv e)
    monoᴰᵉ zero    le hv (input i) = z≤n
    monoᴰᵉ (suc q) (s≤s le) {vs} {vs′} hv (input i) with i ∈ᵇ vs′ in eq′
    ... | true rewrite hv i eq′ = z≤n
    ... | false with i ∈ᵇ vs
    ...   | true  = z≤n
    ...   | false with sl i
    ...     | scripted _ = z≤n
    ...     | shared d   = monoᴰᵉ q le {i ∷ vs} {i ∷ vs′} (Sub-∷ i {vs′} {vs} hv) d

    monoᴰᵗ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗⱽ q vs sl tm ≤ dWᵗⱽ q′ vs′ sl tm
    monoᴰᵗ q le hv (varᵗ x)     = z≤n
    monoᴰᵗ q le hv unit̂         = z≤n
    monoᴰᵗ q le hv (bool̂ _)     = z≤n
    monoᴰᵗ q le hv (nat̂ _)      = z≤n
    monoᴰᵗ q le hv (pairᵗ a b)  = ⊔-mono-≤ (monoᴰᵗ q le hv a) (monoᴰᵗ q le hv b)
    monoᴰᵗ q le hv (fstᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (sndᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (inlᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (inrᵗ p)     = monoᴰᵗ q le hv p
    monoᴰᵗ q le hv (primᵗ _ a)  = monoᴰᵗ q le hv a
    monoᴰᵗ q le hv (strmᵗ e)    = monoᴰᵉ q le hv e
    monoᴰᵗ q le hv (caseᵗ s l r) =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv s) (monoᴰᵗ q le hv l)) (monoᴰᵗ q le hv r)
    monoᴰᵗ q le hv (ifᵗ c a b) =
      ⊔-mono-≤ (⊔-mono-≤ (monoᴰᵗ q le hv c) (monoᴰᵗ q le hv a)) (monoᴰᵗ q le hv b)

    monoᴰᵗˢ : ∀ (q : ℕ) {q′ : ℕ} → q ≤ q′ → ∀ {vs vs′ : List (Fin n)} → Sub vs′ vs →
      ∀ {Δᵍ Δ Θ t} (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢⱽ q vs sl ts ≤ dWᵗˢⱽ q′ vs′ sl ts
    monoᴰᵗˢ q le hv []       = z≤n
    monoᴰᵗˢ q le hv (y ∷ ys) = ⊔-mono-≤ (monoᴰᵗ q le hv y) (monoᴰᵗˢ q le hv ys)

------------------------------------------------------------------
-- THE LEAF, off the slot side condition.
------------------------------------------------------------------

slotsCaps?-slotWid : ∀ {n} {Γ : Ctx n} (B W : ℕ) (sl : Slots Γ) →
  slotsCaps? B W sl ≡ true → SlotWid sl (suc W)
slotsCaps?-slotWid {n = suc m} B W sl h i
  with sl i | slotsCaps?-lookup B W sl i h
... | scripted _ | _  = s≤s z≤n , s≤s z≤n , z≤n
... | shared d   | sd =
  ≤-trans (≤-trans (proj₁ (monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d))
                   (≤-trans (m≤m⊔n (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw))
          (n≤1+n W)
  , ≤-trans (≤-trans (proj₁ (proj₂ (monoᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d))) iw)
            (n≤1+n W)
  , ≤-trans (≤-trans (monoᴰᵉ sl m (n≤1+n m) {i ∷ []} {[]} (Sub-[] {vs = i ∷ []}) d)
                     (≤-trans (m≤n⊔m (outWᵉ (suc m) sl d) (dWᵉ (suc m) sl d)) pw))
            (n≤1+n W)
  where
  split₁ = ∧-true (sizeᵉ d ≤ᵇ B)
             ((pWᵉ (suc m) sl d ≤ᵇ W) ∧ (innWᵉ (suc m) sl d ≤ᵇ W)) sd
  split₂ = ∧-true (pWᵉ (suc m) sl d ≤ᵇ W) (innWᵉ (suc m) sl d ≤ᵇ W)
             (proj₂ split₁)
  pw : pWᵉ (suc m) sl d ≤ W
  pw = ≤ᵇ⇒≤ (pWᵉ (suc m) sl d) W (T-to (proj₁ split₂))
  iw : innWᵉ (suc m) sl d ≤ W
  iw = ≤ᵇ⇒≤ (innWᵉ (suc m) sl d) W (T-to (proj₂ split₂))

------------------------------------------------------------------
-- THE WIDTH FACE OF THE EVALUATOR — the piece that makes every
-- receipt in the cluster SYNTAX-COUNTED.
--
-- The five members all have to bound the width of a value the
-- evaluator just built.  Reading that width off the value's SIZE
-- (which is what the first landing did) costs a fold count equal to
-- that size — iterFold is a TOWER in its count, so nothing smaller
-- dominates it — and the only bound on an evaluated value's size is
-- the RUNNING size cap.  That is where the old `+ suc K` came from,
-- and it made an instant's total j self-referential.
--
-- The route that is syntax-counted reads the width off the WIDTH: an
-- evaluated value's obs components are the term's own obs subterms
-- with the environment plugged in, so their widths come from the
-- term's syntax with the plugged widths as the SEED — one foldStep
-- per syntax node of the TERM, exactly wid-iterFold's count, with the
-- environment entering the seed and never the count.
--
-- FOUR PIECES, all ground: the plug's own measures (a reified value,
-- weakened in — renaming invariance plus the two slopes vanishing
-- because it is Θ-closed), wid-subΘ (wid-iterFold's induction on a
-- substitution instance), evalWith-iterFold (the evaluator's own
-- recursion over it), and wid-lift (the seed lift the members spend
-- their one extra fold on).
------------------------------------------------------------------

-- what an environment presents to the induction: every plugged value
-- is under the same leaf bound the slot telescope is under
EnvW : ∀ {n} {Γ : Ctx n} {Θ} → Slots Γ → ℕ → All (Val Γ) Θ → Set
EnvW sl M []ᵃ                        = ⊤
EnvW {n = n} sl M (_∷ᵃ_ {x = t} v σ) = (pWᵛ n sl t v ≤ M) × EnvW sl M σ

envW-lookup : ∀ {n} {Γ : Ctx n} {Θ t} (M : ℕ) (sl : Slots Γ)
  (σ : All (Val Γ) Θ) → EnvW sl M σ → (z : t ∈ Θ) →
  pWᵛ n sl t (lookupEnv σ z) ≤ M
envW-lookup M sl (v ∷ᵃ σ) (hv , hσ) (here refl) = hv
envW-lookup M sl (v ∷ᵃ σ) (hv , hσ) (there z)   = envW-lookup M sl σ hσ z

envW-mono : ∀ {n} {Γ : Ctx n} {Θ} {M M′ : ℕ} (sl : Slots Γ)
  (σ : All (Val Γ) Θ) → M ≤ M′ → EnvW sl M σ → EnvW sl M′ σ
envW-mono sl []ᵃ      le hσ         = tt
envW-mono sl (v ∷ᵃ σ) le (hv , hσ) = ≤-trans hv le , envW-mono sl σ le hσ

-- the leaf bound only ever needs widening, which is all the seed
-- juggling below does
SlotWid-mono : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) {M M′ : ℕ} → M ≤ M′ →
  SlotWid sl M → SlotWid sl M′
SlotWid-mono sl le hI i = ≤-trans (proj₁ (hI i)) le
                        , ≤-trans (proj₁ (proj₂ (hI i))) le
                        , ≤-trans (proj₂ (proj₂ (hI i))) le

-- a pair's parked width is its components', which is what a scan rung
-- hands the step function and what the projections read back
pWᵛ-pair : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) →
  pWᵛ n sl (s ×ᵗ u) (a , b) ≤ pWᵛ n sl s a ⊔ pWᵛ n sl u b
pWᵛ-pair {n = n} sl s u a b =
  ⊔-lub (⊔-lub (≤-trans (m≤m⊔n (outWᵛ n sl s a) (dWᵛ n sl s a)) (m≤m⊔n P Q))
               (≤-trans (m≤m⊔n (outWᵛ n sl u b) (dWᵛ n sl u b)) (m≤n⊔m P Q)))
        (⊔-lub (≤-trans (m≤n⊔m (outWᵛ n sl s a) (dWᵛ n sl s a)) (m≤m⊔n P Q))
               (≤-trans (m≤n⊔m (outWᵛ n sl u b) (dWᵛ n sl u b)) (m≤n⊔m P Q)))
  where
  P = pWᵛ n sl s a
  Q = pWᵛ n sl u b

pWᵛ-fst : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) → pWᵛ n sl s a ≤ pWᵛ n sl (s ×ᵗ u) (a , b)
pWᵛ-fst {n = n} sl s u a b =
  ⊔-lub (≤-trans (m≤m⊔n (outWᵛ n sl s a) (outWᵛ n sl u b))
                 (m≤m⊔n (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))
        (≤-trans (m≤m⊔n (dWᵛ n sl s a) (dWᵛ n sl u b))
                 (m≤n⊔m (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))

pWᵛ-snd : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (s u : Ty)
  (a : Val Γ s) (b : Val Γ u) → pWᵛ n sl u b ≤ pWᵛ n sl (s ×ᵗ u) (a , b)
pWᵛ-snd {n = n} sl s u a b =
  ⊔-lub (≤-trans (m≤n⊔m (outWᵛ n sl s a) (outWᵛ n sl u b))
                 (m≤m⊔n (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))
        (≤-trans (m≤n⊔m (dWᵛ n sl s a) (dWᵛ n sl u b))
                 (m≤n⊔m (outWᵛ n sl s a ⊔ outWᵛ n sl u b) _))

-- a renaming the width slopes can see through: it moves a Θ variable
-- without moving its de Bruijn INDEX, which is what pmI reads
IxPres : ∀ {Θ Θ′ : List Ty} → Ren∈ Θ Θ′ → Set
IxPres {Θ} ρ = ∀ {u} (x : u ∈ Θ) → varIx (ρ x) ≡ varIx x

ext∈-IxPres : ∀ {Θ Θ′ s} {ρ : Ren∈ Θ Θ′} → IxPres ρ → IxPres (ext∈ {s = s} ρ)
ext∈-IxPres hp (here refl) = refl
ext∈-IxPres hp (there x)   = cong suc (hp x)

∅-IxPres : ∀ {Θ : List Ty} → IxPres {[]} {Θ} (λ ())
∅-IxPres ()

-- the shape every outW / innW clause lands in, since those two split on
-- the slot fuel and do not reduce at a variable one
bridge : ∀ {A : Set} {x y u v : A} → x ≡ u → y ≡ v → u ≡ v → x ≡ y
bridge p q r = trans p (trans r (sym q))

-- and a slot leaf weighs the same in any binder context: the measures
-- read the slot, never the telescope it sits under
module Irr {n} {Γ : Ctx n} where
  oW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    outWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ outWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  oW-input zero    sl i = refl
  oW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

  iW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    innWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ innWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  iW-input zero    sl i = refl
  iW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

  dW-input : ∀ (q : ℕ) (sl : Slots Γ) {Δᵍ Δ Θ Δᵍ′ Δ′ Θ′ : List Ty} (i : Fin n) →
    dWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i)
      ≡ dWᵉ q sl (input {Γ = Γ} {Δᵍ = Δᵍ′} {Δ = Δ′} {Θ = Θ′} i)
  dW-input zero    sl i = refl
  dW-input (suc q) sl i with sl i
  ... | scripted _ = refl
  ... | shared d   = refl

------------------------------------------------------------------
-- THE FIVE WIDTH MEASURES ARE RENAMING-INVARIANT, at an
-- index-preserving Θ renaming.  Renaming maps every constructor 1-1
-- and only `pmIᵗ`'s varᵗ clause reads an index at all — the caseW-ren /
-- shellSize-ren shape, four measures at once because they cross-refer
------------------------------------------------------------------

mutual
  ren-oWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) →
    outWᵉ q sl (renExp ρg ρd ρt e) ≡ outWᵉ q sl e
  ren-oWᵉ q sl ρg ρd ρt hp (input i)   = Irr.oW-input q sl i
  ren-oWᵉ q sl ρg ρd ρt hp (varᵉ x)    = bridge (Red.oW-var q sl _) (Red.oW-var q sl x) refl
  ren-oWᵉ q sl ρg ρd ρt hp emptyᵉ      = bridge (Red.oW-empty q sl) (Red.oW-empty q sl) refl
  ren-oWᵉ q sl ρg ρd ρt hp (deferᵉ e)  =
    bridge (Red.oW-defer q sl _) (Red.oW-defer q sl e) refl
  ren-oWᵉ q sl ρg ρd ρt hp (ofᵉ ts)    =
    bridge (Red.oW-of q sl _) (Red.oW-of q sl ts) (len-renTms ρg ρd ρt ts)
  ren-oWᵉ q sl ρg ρd ρt hp (mapᵉ f e)  =
    bridge (Red.oW-map q sl _ _) (Red.oW-map q sl f e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    bridge (Red.oW-take q sl _ _) (Red.oW-take q sl c e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    bridge (Red.oW-scan q sl _ _ _) (Red.oW-scan q sl f z e)
           (ren-oWᵉ q sl ρg ρd ρt hp e)
  ren-oWᵉ q sl ρg ρd ρt hp (mergeAllᵉ e) =
    bridge (Red.oW-merge q sl _) (Red.oW-merge q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (concatAllᵉ e) =
    bridge (Red.oW-concat q sl _) (Red.oW-concat q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (switchAllᵉ e) =
    bridge (Red.oW-switch q sl _) (Red.oW-switch q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) =
    bridge (Red.oW-exhaust q sl _) (Red.oW-exhaust q sl e)
           (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-iWᵉ q sl ρg ρd ρt hp e))
  ren-oWᵉ q sl ρg ρd ρt hp (μᵉ e) =
    bridge (Red.oW-μ q sl _) (Red.oW-μ q sl e)
           (ren-oWᵉ q sl (ext∈ ρg) ρd ρt hp e)

  ren-iWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) →
    innWᵉ q sl (renExp ρg ρd ρt e) ≡ innWᵉ q sl e
  ren-iWᵉ q sl ρg ρd ρt hp (input i)  = Irr.iW-input q sl i
  ren-iWᵉ q sl ρg ρd ρt hp (varᵉ x)   = bridge (Red.iW-var q sl _) (Red.iW-var q sl x) refl
  ren-iWᵉ q sl ρg ρd ρt hp emptyᵉ     = bridge (Red.iW-empty q sl) (Red.iW-empty q sl) refl
  ren-iWᵉ q sl ρg ρd ρt hp (deferᵉ e) =
    bridge (Red.iW-defer q sl _) (Red.iW-defer q sl e) refl
  ren-iWᵉ q sl ρg ρd ρt hp (ofᵉ ts)   =
    bridge (Red.iW-of q sl _) (Red.iW-of q sl ts) (ren-iWᵗˢ q sl ρg ρd ρt hp ts)
  ren-iWᵉ q sl ρg ρd ρt hp (mapᵉ f e) =
    bridge (Red.iW-map q sl _ _) (Red.iW-map q sl f e)
           (cong₂ _+_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
                      (cong₂ _*_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) 0 f))
                                 (ren-iWᵉ q sl ρg ρd ρt hp e)))
  ren-iWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    bridge (Red.iW-take q sl _ _) (Red.iW-take q sl c e)
           (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    bridge (Red.iW-scan q sl _ _ _) (Red.iW-scan q sl f z e)
           (cong₂ _*_ (cong₂ _^_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) 0 f))
                                 (ren-oWᵉ q sl ρg ρd ρt hp e))
                      (cong (_+ 1)
                        (cong₂ _+_ (cong₂ _+_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt)
                                                 (ext∈-IxPres hp) f)
                                              (ren-iWᵗ q sl ρg ρd ρt hp z))
                                   (ren-iWᵉ q sl ρg ρd ρt hp e))))
  ren-iWᵉ q sl ρg ρd ρt hp (mergeAllᵉ e) =
    bridge (Red.iW-merge q sl _) (Red.iW-merge q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (concatAllᵉ e) =
    bridge (Red.iW-concat q sl _) (Red.iW-concat q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (switchAllᵉ e) =
    bridge (Red.iW-switch q sl _) (Red.iW-switch q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) =
    bridge (Red.iW-exhaust q sl _) (Red.iW-exhaust q sl e) (ren-iWᵉ q sl ρg ρd ρt hp e)
  ren-iWᵉ q sl ρg ρd ρt hp (μᵉ e) =
    bridge (Red.iW-μ q sl _) (Red.iW-μ q sl e) (ren-iWᵉ q sl (ext∈ ρg) ρd ρt hp e)

  ren-pOᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    pmOᵉ q sl k (renExp ρg ρd ρt e) ≡ pmOᵉ q sl k e
  ren-pOᵉ q sl ρg ρd ρt hp k (input i)  = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (varᵉ x)   = refl
  ren-pOᵉ q sl ρg ρd ρt hp k emptyᵉ     = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (deferᵉ e) = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (ofᵉ ts)   = refl
  ren-pOᵉ q sl ρg ρd ρt hp k (mapᵉ f e)   = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (takeᵉ c e)  = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (scanᵉ f z e) = ren-pOᵉ q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (mergeAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (concatAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (switchAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (exhaustAllᵉ e) = allPO q sl ρg ρd ρt hp k e
  ren-pOᵉ q sl ρg ρd ρt hp k (μᵉ e) = ren-pOᵉ q sl (ext∈ ρg) ρd ρt hp k e

  allPO : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ (obs t)) →
    outWᵉ q sl (renExp ρg ρd ρt e) * pmIᵉ q sl k (renExp ρg ρd ρt e)
      + pmOᵉ q sl k (renExp ρg ρd ρt e) * innWᵉ q sl (renExp ρg ρd ρt e)
    ≡ outWᵉ q sl e * pmIᵉ q sl k e + pmOᵉ q sl k e * innWᵉ q sl e
  allPO q sl ρg ρd ρt hp k e =
    cong₂ _+_ (cong₂ _*_ (ren-oWᵉ q sl ρg ρd ρt hp e) (ren-pIᵉ q sl ρg ρd ρt hp k e))
              (cong₂ _*_ (ren-pOᵉ q sl ρg ρd ρt hp k e) (ren-iWᵉ q sl ρg ρd ρt hp e))

  ren-pIᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (e : Exp Γ Δᵍ Δ Θ t) →
    pmIᵉ q sl k (renExp ρg ρd ρt e) ≡ pmIᵉ q sl k e
  ren-pIᵉ q sl ρg ρd ρt hp k (input i)  = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (varᵉ x)   = refl
  ren-pIᵉ q sl ρg ρd ρt hp k emptyᵉ     = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (deferᵉ e) = refl
  ren-pIᵉ q sl ρg ρd ρt hp k (ofᵉ ts)   = ren-pIᵗˢ q sl ρg ρd ρt hp k ts
  ren-pIᵉ q sl ρg ρd ρt hp k (mapᵉ f e) =
    cong₂ _+_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) f)
              (cong₂ _*_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                         (ext∈-IxPres hp) 0 f))
                         (ren-pIᵉ q sl ρg ρd ρt hp k e))
  ren-pIᵉ q sl ρg ρd ρt hp k (takeᵉ c e) = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (scanᵉ f z e) =
    cong₂ _*_ (cong₂ _^_ (cong (_⊔ 1) (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                         (ext∈-IxPres hp) 0 f))
                         (ren-oWᵉ q sl ρg ρd ρt hp e))
              (cong₂ _+_ (cong₂ _+_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt)
                                       (ext∈-IxPres hp) (suc k) f)
                                    (ren-pIᵗ q sl ρg ρd ρt hp k z))
                         (ren-pIᵉ q sl ρg ρd ρt hp k e))
  ren-pIᵉ q sl ρg ρd ρt hp k (mergeAllᵉ e)   = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (concatAllᵉ e)  = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (switchAllᵉ e)  = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (exhaustAllᵉ e) = ren-pIᵉ q sl ρg ρd ρt hp k e
  ren-pIᵉ q sl ρg ρd ρt hp k (μᵉ e) = ren-pIᵉ q sl (ext∈ ρg) ρd ρt hp k e

  ren-iWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (tm : Tm Γ Δᵍ Δ Θ t) → innWᵗ q sl (renTm ρg ρd ρt tm) ≡ innWᵗ q sl tm
  ren-iWᵗ q sl ρg ρd ρt hp (varᵗ x)    = refl
  ren-iWᵗ q sl ρg ρd ρt hp unit̂        = refl
  ren-iWᵗ q sl ρg ρd ρt hp (bool̂ _)    = refl
  ren-iWᵗ q sl ρg ρd ρt hp (nat̂ _)     = refl
  ren-iWᵗ q sl ρg ρd ρt hp (primᵗ _ a) = refl
  ren-iWᵗ q sl ρg ρd ρt hp (pairᵗ a b) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp a) (ren-iWᵗ q sl ρg ρd ρt hp b)
  ren-iWᵗ q sl ρg ρd ρt hp (fstᵗ p) = ren-iWᵗ q sl ρg ρd ρt hp p
  ren-iWᵗ q sl ρg ρd ρt hp (sndᵗ p) = ren-iWᵗ q sl ρg ρd ρt hp p
  ren-iWᵗ q sl ρg ρd ρt hp (inlᵗ a) = ren-iWᵗ q sl ρg ρd ρt hp a
  ren-iWᵗ q sl ρg ρd ρt hp (inrᵗ a) = ren-iWᵗ q sl ρg ρd ρt hp a
  ren-iWᵗ q sl ρg ρd ρt hp (ifᵗ c a b) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp a) (ren-iWᵗ q sl ρg ρd ρt hp b)
  ren-iWᵗ q sl ρg ρd ρt hp (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) l)
                         (ren-iWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 l)
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 r))
                            refl)
                         (ren-iWᵗ q sl ρg ρd ρt hp s))
  ren-iWᵗ q sl ρg ρd ρt hp (strmᵗ e) = ren-oWᵉ q sl ρg ρd ρt hp e

  ren-pOᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (tm : Tm Γ Δᵍ Δ Θ t) → pmOᵗ q sl k (renTm ρg ρd ρt tm) ≡ pmOᵗ q sl k tm
  ren-pOᵗ q sl ρg ρd ρt hp k (varᵗ x)    = refl
  ren-pOᵗ q sl ρg ρd ρt hp k unit̂        = refl
  ren-pOᵗ q sl ρg ρd ρt hp k (bool̂ _)    = refl
  ren-pOᵗ q sl ρg ρd ρt hp k (nat̂ _)     = refl
  ren-pOᵗ q sl ρg ρd ρt hp k (primᵗ _ a) = refl
  ren-pOᵗ q sl ρg ρd ρt hp k (pairᵗ a b) =
    cong₂ _⊔_ (ren-pOᵗ q sl ρg ρd ρt hp k a) (ren-pOᵗ q sl ρg ρd ρt hp k b)
  ren-pOᵗ q sl ρg ρd ρt hp k (fstᵗ p) = ren-pOᵗ q sl ρg ρd ρt hp k p
  ren-pOᵗ q sl ρg ρd ρt hp k (sndᵗ p) = ren-pOᵗ q sl ρg ρd ρt hp k p
  ren-pOᵗ q sl ρg ρd ρt hp k (inlᵗ a) = ren-pOᵗ q sl ρg ρd ρt hp k a
  ren-pOᵗ q sl ρg ρd ρt hp k (inrᵗ a) = ren-pOᵗ q sl ρg ρd ρt hp k a
  ren-pOᵗ q sl ρg ρd ρt hp k (ifᵗ c a b) =
    cong₂ _⊔_ (ren-pOᵗ q sl ρg ρd ρt hp k a) (ren-pOᵗ q sl ρg ρd ρt hp k b)
  ren-pOᵗ q sl ρg ρd ρt hp k (caseᵗ s l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-pOᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) l)
                         (ren-pOᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 l)
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 r))
                            refl)
                         (ren-pOᵗ q sl ρg ρd ρt hp k s))
  ren-pOᵗ q sl ρg ρd ρt hp k (strmᵗ e) = ren-pOᵉ q sl ρg ρd ρt hp k e

  ren-pIᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (tm : Tm Γ Δᵍ Δ Θ t) → pmIᵗ q sl k (renTm ρg ρd ρt tm) ≡ pmIᵗ q sl k tm
  ren-pIᵗ q sl ρg ρd ρt hp k (varᵗ x) =
    cong (λ i → if i ≡ᵇ k then 1 else 0) (hp x)
  ren-pIᵗ q sl ρg ρd ρt hp k unit̂        = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (bool̂ _)    = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (nat̂ _)     = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (primᵗ _ a) = refl
  ren-pIᵗ q sl ρg ρd ρt hp k (pairᵗ a b) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k a) (ren-pIᵗ q sl ρg ρd ρt hp k b)
  ren-pIᵗ q sl ρg ρd ρt hp k (fstᵗ p) = ren-pIᵗ q sl ρg ρd ρt hp k p
  ren-pIᵗ q sl ρg ρd ρt hp k (sndᵗ p) = ren-pIᵗ q sl ρg ρd ρt hp k p
  ren-pIᵗ q sl ρg ρd ρt hp k (inlᵗ a) = ren-pIᵗ q sl ρg ρd ρt hp k a
  ren-pIᵗ q sl ρg ρd ρt hp k (inrᵗ a) = ren-pIᵗ q sl ρg ρd ρt hp k a
  ren-pIᵗ q sl ρg ρd ρt hp k (ifᵗ c a b) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k a) (ren-pIᵗ q sl ρg ρd ρt hp k b)
  ren-pIᵗ q sl ρg ρd ρt hp k (caseᵗ s l r) =
    cong₂ _+_ (cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) l)
                         (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) (suc k) r))
              (cong₂ _*_ (cong₂ _⊔_ (cong₂ _⊔_
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 l)
                            (ren-pIᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) 0 r))
                            refl)
                         (ren-pIᵗ q sl ρg ρd ρt hp k s))
  ren-pIᵗ q sl ρg ρd ρt hp k (strmᵗ e) = ren-pOᵉ q sl ρg ρd ρt hp k e

  ren-iWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → innWᵗˢ q sl (renTms ρg ρd ρt ts) ≡ innWᵗˢ q sl ts
  ren-iWᵗˢ q sl ρg ρd ρt hp []       = refl
  ren-iWᵗˢ q sl ρg ρd ρt hp (y ∷ ys) =
    cong₂ _⊔_ (ren-iWᵗ q sl ρg ρd ρt hp y) (ren-iWᵗˢ q sl ρg ρd ρt hp ys)

  ren-pIᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (k : ℕ) (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    pmIᵗˢ q sl k (renTms ρg ρd ρt ts) ≡ pmIᵗˢ q sl k ts
  ren-pIᵗˢ q sl ρg ρd ρt hp k []       = refl
  ren-pIᵗˢ q sl ρg ρd ρt hp k (y ∷ ys) =
    cong₂ _⊔_ (ren-pIᵗ q sl ρg ρd ρt hp k y) (ren-pIᵗˢ q sl ρg ρd ρt hp k ys)

------------------------------------------------------------------
-- AND A RENAMING THAT REACHES NO INDEX `k` KILLS BOTH SLOPES — the
-- pm-ren0 shape, for the two width slopes.  A plug is Θ-closed, so it
-- is renamed in by `(λ ())` and every k is unreached
------------------------------------------------------------------

zeroSum : ∀ (a b : ℕ) → a * 0 + 0 * b ≡ 0
zeroSum a b = trans (+-identityʳ (a * 0)) (*-zeroʳ a)

mutual
  pO-ren0ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmOᵉ q sl k (renExp ρg ρd ρt e) ≡ 0
  pO-ren0ᵉ q k sl ρg ρd ρt h (input i)  = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (varᵉ x)   = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h emptyᵉ     = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (deferᵉ e) = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (ofᵉ ts)   = refl
  pO-ren0ᵉ q k sl ρg ρd ρt h (mapᵉ f e)    = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (takeᵉ c e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (scanᵉ f z e) = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (μᵉ e) = pO-ren0ᵉ q k sl (ext∈ ρg) ρd ρt h e
  pO-ren0ᵉ q k sl ρg ρd ρt h (mergeAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))
  pO-ren0ᵉ q k sl ρg ρd ρt h (concatAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))
  pO-ren0ᵉ q k sl ρg ρd ρt h (switchAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))
  pO-ren0ᵉ q k sl ρg ρd ρt h (exhaustAllᵉ e)
    rewrite pI-ren0ᵉ q k sl ρg ρd ρt h e | pO-ren0ᵉ q k sl ρg ρd ρt h e =
    zeroSum (outWᵉ q sl (renExp ρg ρd ρt e)) (innWᵉ q sl (renExp ρg ρd ρt e))

  pI-ren0ᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (e : Exp Γ Δᵍ Δ Θ t) → pmIᵉ q sl k (renExp ρg ρd ρt e) ≡ 0
  pI-ren0ᵉ q k sl ρg ρd ρt h (input i)  = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (varᵉ x)   = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h emptyᵉ     = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (deferᵉ e) = refl
  pI-ren0ᵉ q k sl ρg ρd ρt h (ofᵉ ts)   = pI-ren0ᵗˢ q k sl ρg ρd ρt h ts
  pI-ren0ᵉ q k sl ρg ρd ρt h (takeᵉ c e)   = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (mergeAllᵉ e)   = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (concatAllᵉ e)  = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (switchAllᵉ e)  = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (exhaustAllᵉ e) = pI-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (μᵉ e) = pI-ren0ᵉ q k sl (ext∈ ρg) ρd ρt h e
  pI-ren0ᵉ q k sl ρg ρd ρt h (mapᵉ f e)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pI-ren0ᵉ q k sl ρg ρd ρt h e =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) f) ⊔ 1)
  pI-ren0ᵉ q k sl ρg ρd ρt h (scanᵉ f z e)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) f
          | pI-ren0ᵗ q k sl ρg ρd ρt h z
          | pI-ren0ᵉ q k sl ρg ρd ρt h e =
    *-zeroʳ ((pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) f) ⊔ 1)
               ^ outWᵉ q sl (renExp ρg ρd ρt e))

  pO-ren0ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmOᵗ q sl k (renTm ρg ρd ρt tm) ≡ 0
  pO-ren0ᵗ q k sl ρg ρd ρt h (varᵗ x)    = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h unit̂        = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (bool̂ _)    = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (nat̂ _)     = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (primᵗ _ a) = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (fstᵗ p)    = pO-ren0ᵗ q k sl ρg ρd ρt h p
  pO-ren0ᵗ q k sl ρg ρd ρt h (sndᵗ p)    = pO-ren0ᵗ q k sl ρg ρd ρt h p
  pO-ren0ᵗ q k sl ρg ρd ρt h (inlᵗ a)    = pO-ren0ᵗ q k sl ρg ρd ρt h a
  pO-ren0ᵗ q k sl ρg ρd ρt h (inrᵗ a)    = pO-ren0ᵗ q k sl ρg ρd ρt h a
  pO-ren0ᵗ q k sl ρg ρd ρt h (strmᵗ e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pO-ren0ᵗ q k sl ρg ρd ρt h (pairᵗ a b)
    rewrite pO-ren0ᵗ q k sl ρg ρd ρt h a | pO-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (ifᵗ c a b)
    rewrite pO-ren0ᵗ q k sl ρg ρd ρt h a | pO-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pO-ren0ᵗ q k sl ρg ρd ρt h (caseᵗ s l r)
    rewrite pO-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) l
          | pO-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) r
          | pO-ren0ᵗ q k sl ρg ρd ρt h s =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) l)
             ⊔ pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) r) ⊔ 1)

  pI-ren0ᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (tm : Tm Γ Δᵍ Δ Θ t) → pmIᵗ q sl k (renTm ρg ρd ρt tm) ≡ 0
  pI-ren0ᵗ q k sl ρg ρd ρt h (varᵗ x)    = ifNeq (varIx (ρt x)) k (h x)
  pI-ren0ᵗ q k sl ρg ρd ρt h unit̂        = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (bool̂ _)    = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (nat̂ _)     = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (primᵗ _ a) = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (fstᵗ p)    = pI-ren0ᵗ q k sl ρg ρd ρt h p
  pI-ren0ᵗ q k sl ρg ρd ρt h (sndᵗ p)    = pI-ren0ᵗ q k sl ρg ρd ρt h p
  pI-ren0ᵗ q k sl ρg ρd ρt h (inlᵗ a)    = pI-ren0ᵗ q k sl ρg ρd ρt h a
  pI-ren0ᵗ q k sl ρg ρd ρt h (inrᵗ a)    = pI-ren0ᵗ q k sl ρg ρd ρt h a
  pI-ren0ᵗ q k sl ρg ρd ρt h (strmᵗ e)   = pO-ren0ᵉ q k sl ρg ρd ρt h e
  pI-ren0ᵗ q k sl ρg ρd ρt h (pairᵗ a b)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h a | pI-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (ifᵗ c a b)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h a | pI-ren0ᵗ q k sl ρg ρd ρt h b = refl
  pI-ren0ᵗ q k sl ρg ρd ρt h (caseᵗ s l r)
    rewrite pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) l
          | pI-ren0ᵗ q (suc k) sl ρg ρd (ext∈ ρt) (ext-≢ k ρt h) r
          | pI-ren0ᵗ q k sl ρg ρd ρt h s =
    *-zeroʳ (pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) l)
             ⊔ pmIᵗ q sl 0 (renTm ρg ρd (ext∈ ρt) r) ⊔ 1)

  pI-ren0ᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q k : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) →
    (∀ {u} (x : u ∈ Θ) → varIx (ρt x) ≡ k → ⊥) →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → pmIᵗˢ q sl k (renTms ρg ρd ρt ts) ≡ 0
  pI-ren0ᵗˢ q k sl ρg ρd ρt h []       = refl
  pI-ren0ᵗˢ q k sl ρg ρd ρt h (y ∷ ys)
    rewrite pI-ren0ᵗ q k sl ρg ρd ρt h y | pI-ren0ᵗˢ q k sl ρg ρd ρt h ys = refl

-- the parked half of the same fact
mutual
  ren-dWᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (e : Exp Γ Δᵍ Δ Θ t) → dWᵉ q sl (renExp ρg ρd ρt e) ≡ dWᵉ q sl e
  ren-dWᵉ q sl ρg ρd ρt hp (input i)  = Irr.dW-input q sl i
  ren-dWᵉ q sl ρg ρd ρt hp emptyᵉ     = refl
  ren-dWᵉ q sl ρg ρd ρt hp (varᵉ x)   = refl
  ren-dWᵉ q sl ρg ρd ρt hp (ofᵉ ts)   = ren-dWᵗˢ q sl ρg ρd ρt hp ts
  ren-dWᵉ q sl ρg ρd ρt hp (mapᵉ f e) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
              (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (takeᵉ c e) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp c) (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (scanᵉ f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) f)
                         (ren-dWᵗ q sl ρg ρd ρt hp z))
              (ren-dWᵉ q sl ρg ρd ρt hp e)
  ren-dWᵉ q sl ρg ρd ρt hp (mergeAllᵉ e)   = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (concatAllᵉ e)  = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (switchAllᵉ e)  = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (exhaustAllᵉ e) = ren-dWᵉ q sl ρg ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (μᵉ e) = ren-dWᵉ q sl (ext∈ ρg) ρd ρt hp e
  ren-dWᵉ q sl ρg ρd ρt hp (deferᵉ e) =
    cong₂ _⊔_ (ren-oWᵉ q sl (λ ()) (++Ren ρg ρd) ρt hp e)
              (ren-dWᵉ q sl (λ ()) (++Ren ρg ρd) ρt hp e)

  ren-dWᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (tm : Tm Γ Δᵍ Δ Θ t) → dWᵗ q sl (renTm ρg ρd ρt tm) ≡ dWᵗ q sl tm
  ren-dWᵗ q sl ρg ρd ρt hp (varᵗ x) = refl
  ren-dWᵗ q sl ρg ρd ρt hp unit̂     = refl
  ren-dWᵗ q sl ρg ρd ρt hp (bool̂ _) = refl
  ren-dWᵗ q sl ρg ρd ρt hp (nat̂ _)  = refl
  ren-dWᵗ q sl ρg ρd ρt hp (pairᵗ a b) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp a) (ren-dWᵗ q sl ρg ρd ρt hp b)
  ren-dWᵗ q sl ρg ρd ρt hp (fstᵗ p)    = ren-dWᵗ q sl ρg ρd ρt hp p
  ren-dWᵗ q sl ρg ρd ρt hp (sndᵗ p)    = ren-dWᵗ q sl ρg ρd ρt hp p
  ren-dWᵗ q sl ρg ρd ρt hp (inlᵗ a)    = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (inrᵗ a)    = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (primᵗ _ a) = ren-dWᵗ q sl ρg ρd ρt hp a
  ren-dWᵗ q sl ρg ρd ρt hp (ifᵗ c a b) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp c) (ren-dWᵗ q sl ρg ρd ρt hp a))
              (ren-dWᵗ q sl ρg ρd ρt hp b)
  ren-dWᵗ q sl ρg ρd ρt hp (caseᵗ s l r) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp s)
                         (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) l))
              (ren-dWᵗ q sl ρg ρd (ext∈ ρt) (ext∈-IxPres hp) r)
  ren-dWᵗ q sl ρg ρd ρt hp (strmᵗ e) = ren-dWᵉ q sl ρg ρd ρt hp e

  ren-dWᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t} (q : ℕ) (sl : Slots Γ)
    (ρg : Ren∈ Δᵍ Δᵍ′) (ρd : Ren∈ Δ Δ′) (ρt : Ren∈ Θ Θ′) → IxPres ρt →
    (ts : List (Tm Γ Δᵍ Δ Θ t)) → dWᵗˢ q sl (renTms ρg ρd ρt ts) ≡ dWᵗˢ q sl ts
  ren-dWᵗˢ q sl ρg ρd ρt hp []       = refl
  ren-dWᵗˢ q sl ρg ρd ρt hp (y ∷ ys) =
    cong₂ _⊔_ (ren-dWᵗ q sl ρg ρd ρt hp y) (ren-dWᵗˢ q sl ρg ρd ρt hp ys)

------------------------------------------------------------------
-- THE PLUG.  A substituted variable becomes the reified value, weakened
-- in: its two width faces are the VALUE's, and both its slopes vanish
-- because it is Θ-closed
------------------------------------------------------------------

plug-iW : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) →
  innWᵗ n sl (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≤ pWᵛ n sl t v
plug-iW {n = n} sl unitᵗ v = z≤n
plug-iW {n = n} sl boolᵗ v = z≤n
plug-iW {n = n} sl natᵗ  v = z≤n
plug-iW {n = n} sl (s ×ᵗ u) (a , b) =
  ⊔-lub (≤-trans (plug-iW {n = n} sl s a) (pWᵛ-fst sl s u a b))
        (≤-trans (plug-iW {n = n} sl u b) (pWᵛ-snd sl s u a b))
plug-iW {n = n} sl (s +ᵗ u) (inj₁ a) = plug-iW {n = n} sl s a
plug-iW {n = n} sl (s +ᵗ u) (inj₂ b) = plug-iW {n = n} sl u b
plug-iW {n = n} sl (obs u)  e =
  ≤-trans (≤-reflexive (ren-oWᵉ n sl (λ ()) (λ ()) (λ ()) ∅-IxPres e))
          (m≤m⊔n (outWᵉ n sl e) (dWᵉ n sl e))

plug-dW : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) →
  dWᵗ n sl (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≤ pWᵛ n sl t v
plug-dW {n = n} sl unitᵗ v = z≤n
plug-dW {n = n} sl boolᵗ v = z≤n
plug-dW {n = n} sl natᵗ  v = z≤n
plug-dW {n = n} sl (s ×ᵗ u) (a , b) =
  ⊔-lub (≤-trans (plug-dW {n = n} sl s a) (pWᵛ-fst sl s u a b))
        (≤-trans (plug-dW {n = n} sl u b) (pWᵛ-snd sl s u a b))
plug-dW {n = n} sl (s +ᵗ u) (inj₁ a) = plug-dW {n = n} sl s a
plug-dW {n = n} sl (s +ᵗ u) (inj₂ b) = plug-dW {n = n} sl u b
plug-dW {n = n} sl (obs u)  e =
  ≤-trans (≤-reflexive (ren-dWᵉ n sl (λ ()) (λ ()) (λ ()) ∅-IxPres e))
          (m≤n⊔m (outWᵉ n sl e) (dWᵉ n sl e))

plug-pO : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (k : ℕ) (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) → pmOᵗ n sl k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≡ 0
plug-pO {n = n} k sl t v = pO-ren0ᵗ n k sl (λ ()) (λ ()) (λ ()) (λ ()) (reify v)

plug-pI : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} (k : ℕ) (sl : Slots Γ) (t : Ty)
  (v : Val Γ t) → pmIᵗ n sl k (wkTm {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (reify v)) ≡ 0
plug-pI {n = n} k sl t v = pI-ren0ᵗ n k sl (λ ()) (λ ()) (λ ()) (λ ()) (reify v)

------------------------------------------------------------------
-- THE SAME INDUCTION, ON A SUBSTITUTION INSTANCE.  subΘExp commutes
-- with every constructor, so every clause is the one above with the
-- subterms substituted — the count stays the ORIGINAL syntax's size
------------------------------------------------------------------

module _ (S M : ℕ) (hS : 2 ≤ S) (hM : 1 ≤ M) where

  mutual
    wsᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      Wᴱ sl (iterFold S (sizeᵉ e) M) (subΘExp Θloc σ e)
    wsᵉ {n = n} sl hI Θloc σ hσ (input i) =
      ≤-trans (proj₁ (hI i)) INFL , ≤-trans (proj₁ (proj₂ (hI i))) INFL
      , (λ k → z≤n) , (λ k → z≤n)
      where INFL = foldStep-infl S M hS
    wsᵉ {n = n} sl hI Θloc σ hσ emptyᵉ =
      ≤-trans (≤-reflexive (Red.oW-empty n sl)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-empty n sl)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (varᵉ x) =
      ≤-trans (≤-reflexive (Red.oW-var n sl x)) z≤n
      , ≤-trans (≤-reflexive (Red.iW-var n sl x)) z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (deferᵉ e₀) =
      ≤-trans (≤-reflexive (Red.oW-defer n sl (subΘExp Θloc σ e₀))) z≤n
      , ≤-trans (≤-reflexive (Red.iW-defer n sl (subΘExp Θloc σ e₀))) z≤n
      , (λ k → z≤n) , (λ k → z≤n)
    wsᵉ {n = n} sl hI Θloc σ hσ (ofᵉ ts₀) =
      ≤-trans (≤-reflexive (trans (Red.oW-of n sl (subΘTms Θloc σ ts₀))
                                  (len-subΘTms Θloc σ ts₀)))
              (up (≤-trans (len≤sizeᵗˢ ts₀) (k≤iterFold S (sizeᵗˢ ts₀) M hS)))
      , ≤-trans (≤-reflexive (Red.iW-of n sl (subΘTms Θloc σ ts₀))) (up (proj₁ IH))
      , (λ k → z≤n) , (λ k → up (proj₂ IH k))
      where
      IH = wsᵗˢ sl hI Θloc σ hσ ts₀
      up : ∀ {x} → x ≤ iterFold S (sizeᵗˢ ts₀) M → x ≤ iterFold S (suc (sizeᵗˢ ts₀)) M
      up h = ≤-trans (≤-trans h (foldStep-infl S _ hS))
                     (node1 S M (sizeᵗˢ ts₀) (suc (sizeᵗˢ ts₀)) hS ≤-refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (mapᵉ {s = s} f₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-map n sl f e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-map n sl f e)) (FIT INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → FIT (PMI k))
      where
      f   = subΘTm (s ∷ Θloc) σ f₀
      e   = subΘExp Θloc σ e₀
      m   = sizeᵗ f₀ ⊔ sizeᵉ e₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM (≤-trans (sizeᵗ-pos f₀) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ f₀) (sizeᵉ e₀)))
              (wsᵗ sl hI (s ∷ Θloc) σ hσ f₀)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ f₀) (sizeᵉ e₀)))
              (wsᵉ sl hI Θloc σ hσ e₀)
      step = node1 S M m (suc (sizeᵗ f₀ + sizeᵉ e₀)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ f₀) (sizeᵉ e₀)) (m≤n+m (sizeᵉ e₀) (sizeᵗ f₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ f₀ + sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc (sizeᵗ f₀ + sizeᵉ e₀)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      INN : innWᵗ n sl f + (pmIᵗ n sl 0 f ⊔ 1) * innWᵉ n sl e ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (proj₁ IHf) (T≤TT Tb 1≤T))
                     (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T) (proj₁ (proj₂ IHe)))
      PMI : ∀ k → pmIᵗ n sl (suc k) f + (pmIᵗ n sl 0 f ⊔ 1) * pmIᵉ n sl k e
                    ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (proj₂ (proj₂ IHf) (suc k)) (T≤TT Tb 1≤T))
                       (*-mono-≤ (⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T)
                                 (proj₂ (proj₂ (proj₂ IHe)) k))
    wsᵉ {n = n} sl hI Θloc σ hσ (takeᵉ c₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-take n sl c e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-take n sl c e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      c    = subΘTm Θloc σ c₀
      e    = subΘExp Θloc σ e₀
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵗ c₀ + sizeᵉ e₀)) hS
               (s≤s (m≤n+m (sizeᵉ e₀) (sizeᵗ c₀)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c₀ + sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵉ {n = n} sl hI Θloc σ hσ (mergeAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (mergeAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-merge n sl _) (Red.iW-merge n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (concatAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (concatAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-concat n sl _) (Red.iW-concat n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (switchAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (switchAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-switch n sl _) (Red.iW-switch n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (exhaustAllᵉ e₀) =
      wsAll sl (sizeᵉ e₀) (sizeᵉ-pos e₀) (subΘExp Θloc σ e₀)
            (exhaustAllᵉ (subΘExp Θloc σ e₀)) (wsᵉ sl hI Θloc σ hσ e₀)
            (Red.oW-exhaust n sl _) (Red.iW-exhaust n sl _) (λ k → refl) (λ k → refl)
    wsᵉ {n = n} sl hI Θloc σ hσ (μᵉ e₀) =
      ≤-trans (≤-reflexive (Red.oW-μ n sl e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-μ n sl e)) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₂ (proj₂ (proj₂ IHe)) k))
      where
      e    = subΘExp Θloc σ e₀
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵉ {n = n} sl hI Θloc σ hσ (scanᵉ {s = s} {t = t} f₀ z₀ e₀) =
      ≤-trans (≤-reflexive (Red.oW-scan n sl f z e)) (up0 (proj₁ IHe))
      , ≤-trans (≤-reflexive (Red.iW-scan n sl f z e)) (FIT2 INN)
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k)) , (λ k → FIT2 (PMI k))
      where
      f   = subΘTm ((t ×ᵗ s) ∷ Θloc) σ f₀
      z   = subΘTm Θloc σ z₀
      e   = subΘExp Θloc σ e₀
      m   = sizeᵗ f₀ ⊔ sizeᵗ z₀ ⊔ sizeᵉ e₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos f₀) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHf = Wᵀ-mono sl f (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))))
              (wsᵗ sl hI ((t ×ᵗ s) ∷ Θloc) σ hσ f₀)
      IHz = Wᵀ-mono sl z (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))))
              (wsᵗ sl hI Θloc σ hσ z₀)
      IHe = Wᴱ-mono sl e (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ f₀ ⊔ sizeᵗ z₀) (sizeᵉ e₀))) (wsᵉ sl hI Θloc σ hσ e₀)
      Σ3    = sizeᵗ f₀ + sizeᵗ z₀ + sizeᵉ e₀
      step2 = node2 S M m (suc Σ3) hS
                (s≤s (max3-suc (sizeᵗ f₀) (sizeᵗ z₀) (sizeᵉ e₀)
                        (sizeᵗ-pos f₀) (sizeᵗ-pos z₀) (sizeᵉ-pos e₀)))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc Σ3) M
      up0 h = ≤-trans (≤-trans (≤-trans h (foldStep-infl S Tb hS))
                               (foldStep-infl S (foldStep S Tb) hS)) step2
      FIT2 : ∀ {x} → x ≤ Tb ^ Tb * (3 * Tb + 1) → x ≤ iterFold S (suc Σ3) M
      FIT2 h = ≤-trans (≤-trans h (two-folds S Tb hS hT)) step2
      base≤ : pmIᵗ n sl 0 f ⊔ 1 ≤ Tb
      base≤ = ⊔-lub (proj₂ (proj₂ IHf) 0) 1≤T
      pw : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e ≤ Tb ^ Tb
      pw = ≤-trans (^-monoˡ-≤ (outWᵉ n sl e) base≤) (powʳ1 Tb 1≤T (proj₁ IHe))
      INN : (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
              * (innWᵗ n sl f + innWᵗ n sl z + innWᵉ n sl e + 1)
            ≤ Tb ^ Tb * (3 * Tb + 1)
      INN = *-mono-≤ pw
              (≤-trans (+-mono-≤ (+-mono-≤ (+-mono-≤ (proj₁ IHf) (proj₁ IHz))
                                           (proj₁ (proj₂ IHe)))
                                 (≤-refl {1}))
                       (≤-reflexive (thr Tb)))
      PMI : ∀ k → (pmIᵗ n sl 0 f ⊔ 1) ^ outWᵉ n sl e
                    * (pmIᵗ n sl (suc k) f + pmIᵗ n sl k z + pmIᵉ n sl k e)
                  ≤ Tb ^ Tb * (3 * Tb + 1)
      PMI k = *-mono-≤ pw
                (≤-trans (+-mono-≤ (+-mono-≤ (proj₂ (proj₂ IHf) (suc k))
                                             (proj₂ (proj₂ IHz) k))
                                   (proj₂ (proj₂ (proj₂ IHe)) k))
                         (≤-trans (≤-reflexive (thr3 Tb)) (m≤m+n (3 * Tb) 1)))

    -- the four *All nodes, which share a clause.  Parameterised by the
    -- child's own bound rather than computing it, so that the count is
    -- the ORIGINAL syntax's size and the child is the substituted one
    wsAll : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) (m : ℕ) → 1 ≤ m →
      (e : Exp Γ Δᵍ Δ Θ (obs t)) (E : Exp Γ Δᵍ Δ Θ t) →
      Wᴱ sl (iterFold S m M) e →
      outWᵉ n sl E ≡ outWᵉ n sl e * innWᵉ n sl e →
      innWᵉ n sl E ≡ innWᵉ n sl e →
      ((k : ℕ) → pmOᵉ n sl k E
                   ≡ outWᵉ n sl e * pmIᵉ n sl k e + pmOᵉ n sl k e * innWᵉ n sl e) →
      ((k : ℕ) → pmIᵉ n sl k E ≡ pmIᵉ n sl k e) →
      Wᴱ sl (iterFold S (suc m) M) E
    wsAll {n = n} sl m 1≤m e E IHe eo ei ep eq =
      ≤-trans (≤-reflexive eo)
              (FIT (≤-trans (*-mono-≤ (proj₁ IHe) (proj₁ (proj₂ IHe)))
                            (m≤m+n (Tb * Tb) (Tb * Tb))))
      , ≤-trans (≤-reflexive ei) (up0 (proj₁ (proj₂ IHe)))
      , (λ k → ≤-trans (≤-reflexive (ep k))
                 (FIT (+-mono-≤ (*-mono-≤ (proj₁ IHe) (proj₂ (proj₂ (proj₂ IHe)) k))
                                (*-mono-≤ (proj₁ (proj₂ (proj₂ IHe)) k)
                                          (proj₁ (proj₂ IHe))))))
      , (λ k → ≤-trans (≤-reflexive (eq k)) (up0 (proj₂ (proj₂ (proj₂ IHe)) k)))
      where
      Tb   = iterFold S m M
      hT   = 4≤iterFold S M m hS hM 1≤m
      step = node1 S M m (suc m) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc m) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb → x ≤ iterFold S (suc m) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step

    wsᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      Wᵀ sl (iterFold S (sizeᵗ tm) M) (subΘTm Θloc σ tm)
    wsᵗ {n = n} sl hI Θloc σ hσ (varᵗ x) with ∈-++⁻ Θloc x
    ... | inj₁ y =
      z≤n , (λ k → z≤n)
      , (λ k → ite≤ _ (≤-trans (≤ᵇ⇒≤ 1 4 tt) (4≤iterFold S M 1 hS hM ≤-refl)))
    ... | inj₂ z =
      ≤-trans (plug-iW sl _ (lookupEnv σ z))
              (≤-trans (envW-lookup M sl σ hσ z) (iterFold-infl S hS 1 M))
      , (λ k → ≤-trans (≤-reflexive (plug-pO k sl _ (lookupEnv σ z))) z≤n)
      , (λ k → ≤-trans (≤-reflexive (plug-pI k sl _ (lookupEnv σ z))) z≤n)
    wsᵗ sl hI Θloc σ hσ unit̂        = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (bool̂ _)    = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (nat̂ _)     = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (primᵗ _ a) = z≤n , (λ k → z≤n) , (λ k → z≤n)
    wsᵗ sl hI Θloc σ hσ (pairᵗ a₀ b₀) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      a   = subΘTm Θloc σ a₀
      b   = subΘTm Θloc σ b₀
      m   = sizeᵗ a₀ ⊔ sizeᵗ b₀
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ a₀)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ b₀)
      step = node1 S M m (suc (sizeᵗ a₀ + sizeᵗ b₀)) hS
               (s≤s (⊔-lub (m≤m+n (sizeᵗ a₀) (sizeᵗ b₀)) (m≤n+m (sizeᵗ b₀) (sizeᵗ a₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ a₀ + sizeᵗ b₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ sl hI Θloc σ hσ (fstᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (sndᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (inlᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (inrᵗ p₀) =
      wsUnary sl (sizeᵗ p₀) (subΘTm Θloc σ p₀) (wsᵗ sl hI Θloc σ hσ p₀)
    wsᵗ sl hI Θloc σ hσ (strmᵗ e₀) =
      up0 (proj₁ IHe) , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      , (λ k → up0 (proj₁ (proj₂ (proj₂ IHe)) k))
      where
      Tb   = iterFold S (sizeᵉ e₀) M
      IHe  = wsᵉ sl hI Θloc σ hσ e₀
      step = node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵉ e₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ sl hI Θloc σ hσ (ifᵗ c₀ a₀ b₀) =
      up0 (⊔-lub (proj₁ IHa) (proj₁ IHb))
      , (λ k → up0 (⊔-lub (proj₁ (proj₂ IHa) k) (proj₁ (proj₂ IHb) k)))
      , (λ k → up0 (⊔-lub (proj₂ (proj₂ IHa) k) (proj₂ (proj₂ IHb) k)))
      where
      a   = subΘTm Θloc σ a₀
      b   = subΘTm Θloc σ b₀
      m   = sizeᵗ a₀ ⊔ sizeᵗ b₀
      Tb   = iterFold S m M
      IHa = Wᵀ-mono sl a (iterFold-mono-count S M hS (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ a₀)
      IHb = Wᵀ-mono sl b (iterFold-mono-count S M hS (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))
              (wsᵗ sl hI Θloc σ hσ b₀)
      step = node1 S M m (suc (sizeᵗ c₀ + sizeᵗ a₀ + sizeᵗ b₀)) hS
               (s≤s (⊔-lub (≤-trans (m≤n+m (sizeᵗ a₀) (sizeᵗ c₀))
                                    (m≤m+n (sizeᵗ c₀ + sizeᵗ a₀) (sizeᵗ b₀)))
                           (m≤n+m (sizeᵗ b₀) (sizeᵗ c₀ + sizeᵗ a₀))))
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc (sizeᵗ c₀ + sizeᵗ a₀ + sizeᵗ b₀)) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step
    wsᵗ {n = n} sl hI Θloc σ hσ (caseᵗ {s = s} {t = t} s₀ l₀ r₀) =
      FIT INN , (λ k → FIT (PMO k)) , (λ k → FIT (PMI k))
      where
      sc  = subΘTm Θloc σ s₀
      l   = subΘTm (s ∷ Θloc) σ l₀
      r   = subΘTm (t ∷ Θloc) σ r₀
      m   = sizeᵗ s₀ ⊔ sizeᵗ l₀ ⊔ sizeᵗ r₀
      Tb   = iterFold S m M
      hT  = 4≤iterFold S M m hS hM
              (≤-trans (≤-trans (sizeᵗ-pos s₀) (m≤m⊔n _ _)) (m≤m⊔n _ _))
      1≤T = ≤-trans (≤ᵇ⇒≤ 1 4 tt) hT
      IHs = Wᵀ-mono sl sc (iterFold-mono-count S M hS
              (≤-trans (m≤m⊔n (sizeᵗ s₀) (sizeᵗ l₀)) (m≤m⊔n _ (sizeᵗ r₀))))
              (wsᵗ sl hI Θloc σ hσ s₀)
      IHl = Wᵀ-mono sl l (iterFold-mono-count S M hS
              (≤-trans (m≤n⊔m (sizeᵗ s₀) (sizeᵗ l₀)) (m≤m⊔n _ (sizeᵗ r₀))))
              (wsᵗ sl hI (s ∷ Θloc) σ hσ l₀)
      IHr = Wᵀ-mono sl r (iterFold-mono-count S M hS
              (m≤n⊔m (sizeᵗ s₀ ⊔ sizeᵗ l₀) (sizeᵗ r₀)))
              (wsᵗ sl hI (t ∷ Θloc) σ hσ r₀)
      step = node1 S M m (suc (sizeᵗ s₀ + sizeᵗ l₀ + sizeᵗ r₀)) hS
               (s≤s (⊔-lub (⊔-lub (≤-trans (m≤m+n (sizeᵗ s₀) (sizeᵗ l₀))
                                           (m≤m+n (sizeᵗ s₀ + sizeᵗ l₀) (sizeᵗ r₀)))
                                  (≤-trans (m≤n+m (sizeᵗ l₀) (sizeᵗ s₀))
                                           (m≤m+n (sizeᵗ s₀ + sizeᵗ l₀) (sizeᵗ r₀))))
                           (m≤n+m (sizeᵗ r₀) (sizeᵗ s₀ + sizeᵗ l₀))))
      FIT : ∀ {x} → x ≤ Tb * Tb + Tb * Tb →
            x ≤ iterFold S (suc (sizeᵗ s₀ + sizeᵗ l₀ + sizeᵗ r₀)) M
      FIT h = ≤-trans (one-fits S Tb _ hS hT h) step
      C≤ : pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1 ≤ Tb
      C≤ = ⊔-lub (⊔-lub (proj₂ (proj₂ IHl) 0) (proj₂ (proj₂ IHr) 0)) 1≤T
      INN : (innWᵗ n sl l ⊔ innWᵗ n sl r)
              + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * innWᵗ n sl sc
            ≤ Tb * Tb + Tb * Tb
      INN = +-mono-≤ (≤-trans (⊔-lub (proj₁ IHl) (proj₁ IHr)) (T≤TT Tb 1≤T))
                     (*-mono-≤ C≤ (proj₁ IHs))
      PMO : ∀ k → pmOᵗ n sl (suc k) l ⊔ pmOᵗ n sl (suc k) r
                    ⊔ (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmOᵗ n sl k sc
                  ≤ Tb * Tb + Tb * Tb
      PMO k = ⊔-lub (≤-trans (⊔-lub (proj₁ (proj₂ IHl) (suc k))
                                    (proj₁ (proj₂ IHr) (suc k)))
                             (≤-trans (T≤TT Tb 1≤T) (m≤m+n _ _)))
                    (≤-trans (*-mono-≤ C≤ (proj₁ (proj₂ IHs) k)) (m≤m+n _ _))
      PMI : ∀ k → (pmIᵗ n sl (suc k) l ⊔ pmIᵗ n sl (suc k) r)
                    + (pmIᵗ n sl 0 l ⊔ pmIᵗ n sl 0 r ⊔ 1) * pmIᵗ n sl k sc
                  ≤ Tb * Tb + Tb * Tb
      PMI k = +-mono-≤ (≤-trans (⊔-lub (proj₂ (proj₂ IHl) (suc k))
                                       (proj₂ (proj₂ IHr) (suc k)))
                                (T≤TT Tb 1≤T))
                       (*-mono-≤ C≤ (proj₂ (proj₂ IHs) k))

    wsUnary : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (sl : Slots Γ) (m : ℕ)
      (p : Tm Γ Δᵍ Δ Θ t) → Wᵀ sl (iterFold S m M) p →
      (innWᵗ n sl p ≤ iterFold S (suc m) M)
      × ((k : ℕ) → pmOᵗ n sl k p ≤ iterFold S (suc m) M)
      × ((k : ℕ) → pmIᵗ n sl k p ≤ iterFold S (suc m) M)
    wsUnary sl m p IH =
      up0 (proj₁ IH) , (λ k → up0 (proj₁ (proj₂ IH) k))
      , (λ k → up0 (proj₂ (proj₂ IH) k))
      where
      Tb   = iterFold S m M
      step = node1 S M m (suc m) hS ≤-refl
      up0 : ∀ {x} → x ≤ Tb → x ≤ iterFold S (suc m) M
      up0 h = ≤-trans (≤-trans h (foldStep-infl S Tb hS)) step

    wsᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
      Wᴸ sl (iterFold S (sizeᵗˢ ts) M) (subΘTms Θloc σ ts)
    wsᵗˢ sl hI Θloc σ hσ []       = z≤n , (λ k → z≤n)
    wsᵗˢ sl hI Θloc σ hσ (y₀ ∷ ys₀) =
      ⊔-lub (proj₁ IHy) (proj₁ IHys)
      , (λ k → ⊔-lub (proj₂ (proj₂ IHy) k) (proj₂ IHys k))
      where
      IHy  = Wᵀ-mono sl (subΘTm Θloc σ y₀)
               (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y₀) (sizeᵗˢ ys₀)))
               (wsᵗ sl hI Θloc σ hσ y₀)
      IHys = Wᴸ-mono sl (subΘTms Θloc σ ys₀)
               (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys₀) (sizeᵗ y₀)))
               (wsᵗˢ sl hI Θloc σ hσ ys₀)

  -- THE PARKED HALF of the same, and it reads the delivered half above
  -- at the defer exactly as wdᵉ does
  mutual
    wsdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      dWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M
    wsdᵉ sl hI Θloc σ hσ (input i) =
      ≤-trans (proj₂ (proj₂ (hI i))) (foldStep-infl S M hS)
    wsdᵉ sl hI Θloc σ hσ emptyᵉ    = z≤n
    wsdᵉ sl hI Θloc σ hσ (varᵉ x)  = z≤n
    wsdᵉ sl hI Θloc σ hσ (ofᵉ ts₀) =
      ≤-trans (wsdᵗˢ sl hI Θloc σ hσ ts₀)
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗˢ ts₀) (suc (sizeᵗˢ ts₀)) hS ≤-refl))
    wsdᵉ sl hI Θloc σ hσ (deferᵉ e₀) =
      ≤-trans (⊔-lub (proj₁ (wsᵉ sl hI Θloc σ hσ e₀)) (wsdᵉ sl hI Θloc σ hσ e₀))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵉ e₀) (suc (sizeᵉ e₀)) hS ≤-refl))
    wsdᵉ sl hI Θloc σ hσ (mapᵉ {s = s} f₀ e₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI (s ∷ Θloc) σ hσ f₀)
                              (mono (m≤m⊔n (sizeᵗ f₀) (sizeᵉ e₀))))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀)
                              (mono (m≤n⊔m (sizeᵗ f₀) (sizeᵉ e₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ f₀ ⊔ sizeᵉ e₀) (suc (sizeᵗ f₀ + sizeᵉ e₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ f₀) (sizeᵉ e₀))
                                     (m≤n+m (sizeᵉ e₀) (sizeᵗ f₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵉ sl hI Θloc σ hσ (takeᵉ c₀ e₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ c₀)
                              (mono (m≤m⊔n (sizeᵗ c₀) (sizeᵉ e₀))))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀)
                              (mono (m≤n⊔m (sizeᵗ c₀) (sizeᵉ e₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ c₀ ⊔ sizeᵉ e₀) (suc (sizeᵗ c₀ + sizeᵉ e₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ c₀) (sizeᵉ e₀))
                                     (m≤n+m (sizeᵉ e₀) (sizeᵗ c₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵉ sl hI Θloc σ hσ (scanᵉ {s = s} {t = t} f₀ z₀ e₀) =
      ≤-trans (⊔-lub (⊔-lub (≤-trans (wsdᵗ sl hI ((t ×ᵗ s) ∷ Θloc) σ hσ f₀)
                                     (mono up-f))
                            (≤-trans (wsdᵗ sl hI Θloc σ hσ z₀) (mono up-z)))
                     (≤-trans (wsdᵉ sl hI Θloc σ hσ e₀) (mono up-e)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (sizeᵗ f₀ + sizeᵗ z₀ + sizeᵉ e₀)) hS
                         (≤-trans (max3-suc (sizeᵗ f₀) (sizeᵗ z₀) (sizeᵉ e₀)
                                     (sizeᵗ-pos f₀) (sizeᵗ-pos z₀) (sizeᵉ-pos e₀))
                                  (n≤1+n _))))
      where
      m    = sizeᵗ f₀ ⊔ sizeᵗ z₀ ⊔ sizeᵉ e₀
      mono = iterFold-mono-count S M hS
      up-f = ≤-trans (m≤m⊔n (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))
      up-z = ≤-trans (m≤n⊔m (sizeᵗ f₀) (sizeᵗ z₀)) (m≤m⊔n _ (sizeᵉ e₀))
      up-e = m≤n⊔m (sizeᵗ f₀ ⊔ sizeᵗ z₀) (sizeᵉ e₀)
    wsdᵉ sl hI Θloc σ hσ (mergeAllᵉ e₀)   = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (concatAllᵉ e₀)  = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (switchAllᵉ e₀)  = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (exhaustAllᵉ e₀) = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵉ sl hI Θloc σ hσ (μᵉ e₀)          = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)

    -- one node's worth of fold, off the child's own bound
    wsPass : ∀ {x : ℕ} (m : ℕ) → x ≤ iterFold S m M → x ≤ iterFold S (suc m) M
    wsPass m h =
      ≤-trans h (≤-trans (foldStep-infl S _ hS) (node1 S M m (suc m) hS ≤-refl))

    wsdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (tm : Tm Γ Δᵍ Δ (Θloc ++ Θsub) t) →
      dWᵗ n sl (subΘTm Θloc σ tm) ≤ iterFold S (sizeᵗ tm) M
    wsdᵗ {n = n} sl hI Θloc σ hσ (varᵗ x) with ∈-++⁻ Θloc x
    ... | inj₁ y = z≤n
    ... | inj₂ z =
      ≤-trans (plug-dW sl _ (lookupEnv σ z))
              (≤-trans (envW-lookup M sl σ hσ z) (iterFold-infl S hS 1 M))
    wsdᵗ sl hI Θloc σ hσ unit̂     = z≤n
    wsdᵗ sl hI Θloc σ hσ (bool̂ _) = z≤n
    wsdᵗ sl hI Θloc σ hσ (nat̂ _)  = z≤n
    wsdᵗ sl hI Θloc σ hσ (strmᵗ e₀) = wsPass (sizeᵉ e₀) (wsdᵉ sl hI Θloc σ hσ e₀)
    wsdᵗ sl hI Θloc σ hσ (fstᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (sndᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (inlᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (inrᵗ p₀)  = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (primᵗ _ p₀) = wsPass (sizeᵗ p₀) (wsdᵗ sl hI Θloc σ hσ p₀)
    wsdᵗ sl hI Θloc σ hσ (pairᵗ a₀ b₀) =
      ≤-trans (⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ a₀)
                              (mono (m≤m⊔n (sizeᵗ a₀) (sizeᵗ b₀))))
                     (≤-trans (wsdᵗ sl hI Θloc σ hσ b₀)
                              (mono (m≤n⊔m (sizeᵗ a₀) (sizeᵗ b₀)))))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M (sizeᵗ a₀ ⊔ sizeᵗ b₀) (suc (sizeᵗ a₀ + sizeᵗ b₀)) hS
                         (s≤s (⊔-lub (m≤m+n (sizeᵗ a₀) (sizeᵗ b₀))
                                     (m≤n+m (sizeᵗ b₀) (sizeᵗ a₀))))))
      where mono = iterFold-mono-count S M hS
    wsdᵗ sl hI Θloc σ hσ (caseᵗ {s = s} {t = t} s₀ l₀ r₀) =
      wsThree (sizeᵗ s₀) (sizeᵗ l₀) (sizeᵗ r₀)
              (sizeᵗ-pos s₀) (sizeᵗ-pos l₀) (sizeᵗ-pos r₀)
              (wsdᵗ sl hI Θloc σ hσ s₀) (wsdᵗ sl hI (s ∷ Θloc) σ hσ l₀)
              (wsdᵗ sl hI (t ∷ Θloc) σ hσ r₀)
    wsdᵗ sl hI Θloc σ hσ (ifᵗ c₀ a₀ b₀) =
      wsThree (sizeᵗ c₀) (sizeᵗ a₀) (sizeᵗ b₀)
              (sizeᵗ-pos c₀) (sizeᵗ-pos a₀) (sizeᵗ-pos b₀)
              (wsdᵗ sl hI Θloc σ hσ c₀) (wsdᵗ sl hI Θloc σ hσ a₀)
              (wsdᵗ sl hI Θloc σ hσ b₀)

    wsThree : ∀ {x y w : ℕ} (ma mb mc : ℕ) → 1 ≤ ma → 1 ≤ mb → 1 ≤ mc →
      x ≤ iterFold S ma M → y ≤ iterFold S mb M → w ≤ iterFold S mc M →
      x ⊔ y ⊔ w ≤ iterFold S (suc (ma + mb + mc)) M
    wsThree ma mb mc pa pb pc ha hb hc =
      ≤-trans (⊔-lub (⊔-lub (≤-trans ha (mono up-a)) (≤-trans hb (mono up-b)))
                     (≤-trans hc (mono up-c)))
              (≤-trans (foldStep-infl S _ hS)
                       (node1 S M m (suc (ma + mb + mc)) hS
                         (≤-trans (max3-suc ma mb mc pa pb pc) (n≤1+n _))))
      where
      m    = ma ⊔ mb ⊔ mc
      mono = iterFold-mono-count S M hS
      up-a = ≤-trans (m≤m⊔n ma mb) (m≤m⊔n _ mc)
      up-b = ≤-trans (m≤n⊔m ma mb) (m≤m⊔n _ mc)
      up-c = m≤n⊔m (ma ⊔ mb) mc

    wsdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (sl : Slots Γ) → SlotWid sl M →
      (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
      (ts : List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) t)) →
      dWᵗˢ n sl (subΘTms Θloc σ ts) ≤ iterFold S (sizeᵗˢ ts) M
    wsdᵗˢ sl hI Θloc σ hσ []         = z≤n
    wsdᵗˢ sl hI Θloc σ hσ (y₀ ∷ ys₀) =
      ⊔-lub (≤-trans (wsdᵗ sl hI Θloc σ hσ y₀)
                     (iterFold-mono-count S M hS (m≤m+n (sizeᵗ y₀) (sizeᵗˢ ys₀))))
            (≤-trans (wsdᵗˢ sl hI Θloc σ hσ ys₀)
                     (iterFold-mono-count S M hS (m≤n+m (sizeᵗˢ ys₀) (sizeᵗ y₀))))

-- THE PIECE THE ROUTE RESTS ON, PROVEN: plugging an M-bounded
-- environment leaves both width faces under one foldStep per node of
-- the ORIGINAL syntax.  subΘExp commutes with every constructor, so
-- every clause's arithmetic is the one wid-iterFold already runs; the
-- two leaves that move are `varᵗ`, where a plug lands and the
-- induction's leaf bound is already M, and the plug itself, whose
-- measures are the plugged value's and whose slopes vanish because it
-- is Θ-closed
wid-subΘ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (Θloc : List Ty) (σ : All (Val Γ) Θsub) → EnvW sl M σ →
  (e : Exp Γ Δᵍ Δ (Θloc ++ Θsub) t) →
  (outWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M)
  × (dWᵉ n sl (subΘExp Θloc σ e) ≤ iterFold S (sizeᵉ e) M)
wid-subΘ S M hS hM sl hI Θloc σ hσ e =
  proj₁ (wsᵉ S M hS hM sl hI Θloc σ hσ e) , wsdᵉ S M hS hM sl hI Θloc σ hσ e

-- AND THE EVALUATOR, one foldStep per syntax node of the term.  The
-- caseᵗ clause is the one that moves the seed: the scrutinee's value is
-- pushed on the environment, so the branch runs at the seed the
-- scrutinee's own receipt bought, and the two counts ADD — which is
-- exactly what `sizeᵗ (caseᵗ s l r)` already pays for
evalWith-iterFold : ∀ {n} {Γ : Ctx n} {Θ u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) → EnvW sl M env →
  pWᵛ n sl u (evalWith tm env) ≤ iterFold S (sizeᵗ tm) M
evalWith-iterFold S M hS hM sl hI (varᵗ x) env hσ =
  ≤-trans (envW-lookup M sl env hσ x) (iterFold-infl S hS 1 M)
evalWith-iterFold S M hS hM sl hI unit̂     env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (bool̂ b) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (nat̂ k)  env hσ = z≤n
evalWith-iterFold {n = n} S M hS hM sl hI (pairᵗ {s = s} {t = u} a b) env hσ =
  ≤-trans (pWᵛ-pair sl s u (evalWith a env) (evalWith b env))
          (⊔-lub (≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
                    (iterFold-mono-count S M hS
                       (≤-trans (m≤m+n (sizeᵗ a) (sizeᵗ b)) (n≤1+n _))))
                 (≤-trans (evalWith-iterFold S M hS hM sl hI b env hσ)
                    (iterFold-mono-count S M hS
                       (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ a)) (n≤1+n _)))))
evalWith-iterFold {n = n} S M hS hM sl hI (fstᵗ {s = s} {t = u} p) env hσ
  with evalWith p env | evalWith-iterFold S M hS hM sl hI p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (pWᵛ-fst sl s u a b) ih)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ p)))
evalWith-iterFold {n = n} S M hS hM sl hI (sndᵗ {s = s} {t = u} p) env hσ
  with evalWith p env | evalWith-iterFold S M hS hM sl hI p env hσ
... | (a , b) | ih =
  ≤-trans (≤-trans (pWᵛ-snd sl s u a b) ih)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ p)))
evalWith-iterFold S M hS hM sl hI (inlᵗ a) env hσ =
  ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ a)))
evalWith-iterFold S M hS hM sl hI (inrᵗ a) env hσ =
  ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
          (iterFold-mono-count S M hS (n≤1+n (sizeᵗ a)))
evalWith-iterFold S M hS hM sl hI (primᵗ add  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ sub  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ mul  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ eqᵖ  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ ltᵖ  a) env hσ = z≤n
evalWith-iterFold S M hS hM sl hI (primᵗ notᵖ a) env hσ = z≤n
evalWith-iterFold {n = n} S M hS hM sl hI (strmᵗ e) []ᵃ hσ =
  ⊔-lub (≤-trans (proj₁ (wid-iterFold S M hS hM sl hI e))
                 (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
        (≤-trans (proj₂ (proj₂ (wid-iterFold S M hS hM sl hI e)))
                 (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
evalWith-iterFold {n = n} S M hS hM sl hI (strmᵗ e) (v ∷ᵃ vs) hσ =
  ⊔-lub (≤-trans (proj₁ SUB) (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
        (≤-trans (proj₂ SUB) (iterFold-mono-count S M hS (n≤1+n (sizeᵉ e))))
  where SUB = wid-subΘ S M hS hM sl hI [] (v ∷ᵃ vs) hσ e
evalWith-iterFold S M hS hM sl hI (ifᵗ c a b) env hσ
  with evalWith c env
... | true  = ≤-trans (evalWith-iterFold S M hS hM sl hI a env hσ)
                (iterFold-mono-count S M hS
                   (≤-trans (≤-trans (m≤n+m (sizeᵗ a) (sizeᵗ c))
                                     (m≤m+n (sizeᵗ c + sizeᵗ a) (sizeᵗ b)))
                            (n≤1+n _)))
... | false = ≤-trans (evalWith-iterFold S M hS hM sl hI b env hσ)
                (iterFold-mono-count S M hS
                   (≤-trans (m≤n+m (sizeᵗ b) (sizeᵗ c + sizeᵗ a))
                            (n≤1+n _)))
evalWith-iterFold {n = n} S M hS hM sl hI (caseᵗ {s = s} {t = u} sc l r) env hσ
  with evalWith sc env | evalWith-iterFold S M hS hM sl hI sc env hσ
... | inj₁ x | ih =
  ≤-trans (evalWith-iterFold S M₁ hS
             (≤-trans hM (iterFold-infl S hS (sizeᵗ sc) M)) sl
             (SlotWid-mono sl (iterFold-infl S hS (sizeᵗ sc) M) hI)
             l (x ∷ᵃ env)
             (ih , envW-mono sl env (iterFold-infl S hS (sizeᵗ sc) M) hσ))
          (≤-trans (≤-reflexive (sym (iterFold-+ S (sizeᵗ sc) (sizeᵗ l) M)))
                   (iterFold-mono-count S M hS
                      (≤-trans (m≤m+n (sizeᵗ sc + sizeᵗ l) (sizeᵗ r))
                               (n≤1+n _))))
  where M₁ = iterFold S (sizeᵗ sc) M
... | inj₂ y | ih =
  ≤-trans (evalWith-iterFold S M₁ hS
             (≤-trans hM (iterFold-infl S hS (sizeᵗ sc) M)) sl
             (SlotWid-mono sl (iterFold-infl S hS (sizeᵗ sc) M) hI)
             r (y ∷ᵃ env)
             (ih , envW-mono sl env (iterFold-infl S hS (sizeᵗ sc) M) hσ))
          (≤-trans (≤-reflexive (sym (iterFold-+ S (sizeᵗ sc) (sizeᵗ r) M)))
                   (iterFold-mono-count S M hS
                      (≤-trans (+-monoˡ-≤ (sizeᵗ r) (m≤m+n (sizeᵗ sc) (sizeᵗ l)))
                               (n≤1+n _))))
  where M₁ = iterFold S (sizeᵗ sc) M

-- THE TWO FACES THE CLUSTER CONSUMES, the width mirrors of
-- applyFn-iterSize / evalTm-iterSize: a closed term evaluates under the
-- telescope's own leaf bound, and a step function under that bound
-- raised to cover its payload
evalTm-iterFold : ∀ {n} {Γ : Ctx n} {u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (z : Tm Γ [] [] [] u) →
  pWᵛ n sl u (evalTm z) ≤ iterFold S (sizeᵗ z) M
evalTm-iterFold S M hS hM sl hI z = evalWith-iterFold S M hS hM sl hI z []ᵃ tt

applyFn-iterFold : ∀ {n} {Γ : Ctx n} {s u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (fn : Fn Γ [] [] [] s u) (v : Val Γ s) → pWᵛ n sl s v ≤ M →
  pWᵛ n sl u (applyFn fn v) ≤ iterFold S (sizeᵗ fn) M
applyFn-iterFold S M hS hM sl hI fn v hv =
  evalWith-iterFold S M hS hM sl hI fn (v ∷ᵃ []ᵃ) (hv , tt)

-- THE SEED LIFT, and it is the whole of the syntax-counted width half:
-- a width read `a` folds above the RUNNING width cap is a width at
-- `suc a` levels on.  One fold absorbs the seed's `suc`; the other `a`
-- are the syntax's own
wid-lift : ∀ (c : Caps) (j a : ℕ) → 2 ≤ Caps.cSize c → ∀ {x} →
  x ≤ iterFold (Caps.cSize c) a (suc (Caps.cWid (frameStep j c))) →
  x ≤ Caps.cWid (frameStep (j + suc a) c)
wid-lift c j a 2≤S {x} h =
  ≤-trans h
    (≤-trans (iterFold-mono-w S a 2≤S
                (≤-trans (suc≤foldStep S (iterFold S j W) 2≤S)
                         (≤-reflexive (sym (iterFold-suc S j W)))))
      (≤-reflexive (trans (sym (iterFold-+ S (suc j) a W))
                          (cong (λ y → iterFold S y W) (shuffle j a)))))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  shuffle : ∀ (j a : ℕ) → suc j + a ≡ j + suc a
  shuffle j a = trans (cong suc (+-comm j a))
                      (trans (cong suc (+-comm a j)) (sym (+-suc j a)))

-- the width bridge the μ edge still runs on: its conclusion is a raw
-- dWᵉ on SYNTAX (the unfolding is a syntactic transform of the
-- program), so the count is syntactic and the cap is never read
expWid-fromSize : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (c : Caps) (j a k : ℕ)
  (sl : Slots Γ) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (e : Exp Γ Δᵍ Δ Θ t) → sizeᵉ e ≤ k →
  dWᵉ n sl e ≤ Caps.cWid (frameStep (j + (a + suc k)) c)
expWid-fromSize {n = n} c j a k sl 2≤S slC e hk =
  subst (λ x → dWᵉ n sl e ≤ iterFold S x W) (sym (+-shuffle j a k))
    (≤-trans (≤-trans (proj₂ (proj₂ (wid-iterFold S (suc W) 2≤S (s≤s z≤n) sl
                                       (slotsCaps?-slotWid S W sl slC) e)))
                      (iterFold-mono-count S (suc W) 2≤S hk))
             (iterFold-lift S W k (j + a) 2≤S))
  where
  S = Caps.cSize c
  W = Caps.cWid c

------------------------------------------------------------------
-- THE WIDENING TOOLKIT, stated here rather than inlined per clause.
--
-- Every clause of the companion tree below runs two or more sub-calls in
-- sequence, and the SECOND one's hypotheses are stated at the first
-- one's OUTPUT level: a bound established at frameStep j has to be read
-- at frameStep (j + j₁), and a value carried out of the first call at
-- frameStep (j + j₁) has to be reported at frameStep ((j + j₁) + j₂).
-- That is the only arithmetic the tree needs — the receipts compose by
-- +-assoc, not by iterating frameStep — so the whole obligation is
-- monotonicity, once per predicate, at ⊑ᶜ.
--
-- Note what is NOT here: a frameStep-COMPOSITION law,
-- frameStep (j + j′) c ≡ frameStep j′ (frameStep j c).  It is FALSE, and
-- not marginally.  frameStep reads its step base S off the ARGUMENT's
-- cSize, so the right-hand side iterates at S = cSize (frameStep j c)
-- while the left iterates at S = cSize c; and the cReg component is
-- linear rather than iterated, cReg c * suc ((j + j′) * S) against
-- cReg c * suc (j * S) * suc (j′ * S).  Neither side is a rewriting of
-- the other.  The tree is shaped to never need it: every companion
-- takes (c , j) rather than a stepped cap, so a sub-call at a later
-- level is the SAME c with a bigger j, and bigger-j is exactly
-- frameStep-mono-j.
------------------------------------------------------------------

⊑ᶜ-refl : ∀ (c : Caps) → c ⊑ᶜ c
⊑ᶜ-refl c = ≤-refl , ≤-refl , ≤-refl

⊑ᶜ-trans : ∀ {a b c : Caps} → a ⊑ᶜ b → b ⊑ᶜ c → a ⊑ᶜ c
⊑ᶜ-trans (s₁ , w₁ , r₁) (s₂ , w₂ , r₂) =
  ≤-trans s₁ s₂ , ≤-trans w₁ w₂ , ≤-trans r₁ r₂

-- THE SHAPE THE CLAUSES ACTUALLY USE: spending more folds only widens.
-- Every companion reports `j + j′`, so this is the widening from a
-- sub-call's entry level to its exit level, with no arithmetic at the
-- call site
frameStep-⊑-+ : ∀ (c : Caps) → 2 ≤ Caps.cSize c → ∀ (j j′ : ℕ) →
  frameStep j c ⊑ᶜ frameStep (j + j′) c
frameStep-⊑-+ c hS j j′ = frameStep-mono-j c hS (m≤m+n j j′)

------------------------------------------------------------------
-- THE ABSORPTION MECHANIC — what replaces the joint bound, and the one
-- piece of arithmetic the *All edge runs on.
--
-- Joint-Probe measured `pathLen κ + sizeᵉ b ≤ cSize` FALSE at the tight
-- admissible cSize on all seventeen families, and adm + 1 EXACTLY on
-- every family carrying a scan: the payload being subscribed IS the
-- stored accumulator, so its size alone already attains the cap and any
-- chain at all overshoots.  No constant slackening survives that, so the
-- joint form is gone and the subscribe side carries the two bounds the
-- delivery side can actually supply, `suc (pathLen κ) ≤ cSize` and
-- `sizeᵉ b ≤ cSize`, SEPARATELY.
--
-- WHY THE INDUCTION STILL CLOSES.  Each *All hop extends the chain by
-- ONE from-inner frame and PAYS ONE j for it.  One j at least doubles
-- cSize — frameStep-size-suc says the next level is
-- `sizeStep S B = S * suc (2 B)`, which for S ≥ 1 dominates `suc B` —
-- so the +1 the frame adds fits under the stepped cap with room, and
-- the receipt joins the sum exactly like the fold receipts do.  The
-- chain grows by one per hop and the cap grows by a factor per hop, so
-- the two do not race.
------------------------------------------------------------------

sucB≤sizeStep : ∀ (S B : ℕ) → 1 ≤ S → suc B ≤ sizeStep S B
sucB≤sizeStep S B hS =
  ≤-trans (s≤s (s≤2s B))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * B)))))
                   (*-monoˡ-≤ (suc (2 * B)) hS))

-- ONE HOP: a chain that fits at level j, extended by one frame, fits at
-- level suc j.  This is the whole content of the repair
frameStep-chain-suc : ∀ (c : Caps) (j k : ℕ) → 2 ≤ Caps.cSize c →
  suc k ≤ Caps.cSize (frameStep j c) →
  suc (suc k) ≤ Caps.cSize (frameStep (suc j) c)
frameStep-chain-suc c j k 2≤S h =
  subst (suc (suc k) ≤_) (sym (frameStep-size-suc c j))
    (≤-trans (s≤s h)
             (sucB≤sizeStep (Caps.cSize c) (Caps.cSize (frameStep j c))
                (≤-trans (s≤s z≤n) 2≤S)))

-- and `2 ≤ cSize` survives every level, which the degenerate chains
-- (root, share-sink — both of length zero) need to discharge their own
-- `1 ≤ cSize`
2≤frameStep-size : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  2 ≤ Caps.cSize (frameStep j c)
2≤frameStep-size c j h =
  ≤-trans h (iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h) j (Caps.cSize c))

frameSz?-widen : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B B′ : ℕ} →
  B ≤ B′ → frameSz? B f ≡ true → frameSz? B′ f ≡ true
frameSz?-widen (map-f fn)      le h = ≤ᵇ-widen (sizeᵗ fn) le h
frameSz?-widen (scan-f fn _)   le h = ≤ᵇ-widen (sizeᵗ fn) le h
frameSz?-widen (take-f _)      le h = refl
frameSz?-widen (from-inner _ _ _) le h = refl
frameSz?-widen (thru-outer _ _)   le h = refl

valCaps?-widen : ∀ {n} {Γ : Ctx n} {c c′ : Caps} (sl : Slots Γ)
  (u : Ty) (v : Val Γ u) →
  c ⊑ᶜ c′ → valCaps? c sl u v ≡ true → valCaps? c′ sl u v ≡ true
valCaps?-widen {n = n} {c = c} sl u v (sz≤ , wd≤ , _) h
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵛ u v) sz≤ hsz)
                          (≤ᵇ-widen (pWᵛ n sl u v) wd≤ hwd)

-- the two halves of valCaps?, which are literally boundedNode's and
-- widNode's scan-st clauses, so a stored accumulator reads either way
valCaps?-size : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true
valCaps?-size {n = n} c sl u v h =
  proj₁ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

valCaps?-wid : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (pWᵛ n sl u v ≤ᵇ Caps.cWid c) ≡ true
valCaps?-wid {n = n} c sl u v h =
  proj₂ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (pWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

valsCaps?-widen : ∀ {n} {Γ : Ctx n} {c c′ : Caps} (sl : Slots Γ)
  (u : Ty) (vs : List (Val Γ u)) →
  c ⊑ᶜ c′ → all (valCaps? c sl u) vs ≡ true
          → all (valCaps? c′ sl u) vs ≡ true
valsCaps?-widen sl u vs le =
  all-impl _ _ (λ v → valCaps?-widen sl u v le) vs

eventCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (ev : InstEvent (Val Γ u)) →
  c ⊑ᶜ c′ → eventCaps? c sl ev ≡ true → eventCaps? c′ sl ev ≡ true
eventCaps?-widen {u = u} sl (value v) le h = valCaps?-widen sl u v le h
eventCaps?-widen sl (init _)    le h = refl
eventCaps?-widen sl (close _ _) le h = refl
eventCaps?-widen sl (handoff _) le h = refl
eventCaps?-widen sl complete    le h = refl

eventsCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (evs : List (InstEvent (Val Γ u))) →
  c ⊑ᶜ c′ → all (eventCaps? c sl) evs ≡ true
          → all (eventCaps? c′ sl) evs ≡ true
eventsCaps?-widen sl evs le =
  all-impl _ _ (λ ev → eventCaps?-widen sl ev le) evs

burstCaps?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (sl : Slots Γ)
  (str : Stream Γ u) →
  c ⊑ᶜ c′ → burstCaps? c sl str ≡ true → burstCaps? c′ sl str ≡ true
burstCaps?-widen sl str le =
  all-impl _ _ (λ em → eventsCaps?-widen sl (InstEmit.events em) le) str

obsCaps?-widen : ∀ {n} {Γ : Ctx n} {s} {c c′ : Caps} (sl : Slots Γ)
  (o : Closed Γ s) →
  c ⊑ᶜ c′ → obsCaps? c sl o ≡ true → obsCaps? c′ sl o ≡ true
obsCaps?-widen {n = n} {c = c} sl o (sz≤ , wd≤ , _) h
  with ∧-true (sizeᵉ o ≤ᵇ Caps.cSize c) (pWᵉ n sl o ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵉ o) sz≤ hsz)
                          (≤ᵇ-widen (pWᵉ n sl o) wd≤ hwd)

obsListCaps?-widen : ∀ {n} {Γ : Ctx n} {s} {c c′ : Caps} (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  c ⊑ᶜ c′ → all (obsCaps? c sl) q ≡ true
          → all (obsCaps? c′ sl) q ≡ true
obsListCaps?-widen sl q le =
  all-impl _ _ (λ o → obsCaps?-widen sl o le) q

-- rebracketing a two-step receipt.  (j + j₁) + j₂ is what the clauses
-- build; j + (j₁ + j₂) is what they must report
frameStep-+assoc-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j a b : ℕ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep ((j + a) + b) c) sched st ≡ true →
  capsOK? (frameStep (j + (a + b)) c) sched st ≡ true
frameStep-+assoc-caps c j a b sched st =
  subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (+-assoc j a b)

frameStep-+assoc-burst : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j a b : ℕ)
  (sl : Slots Γ) (str : Stream Γ u) →
  burstCaps? (frameStep ((j + a) + b) c) sl str ≡ true →
  burstCaps? (frameStep (j + (a + b)) c) sl str ≡ true
frameStep-+assoc-burst c j a b sl str =
  subst (λ x → burstCaps? (frameStep x c) sl str ≡ true) (+-assoc j a b)

-- pathSz? and regsSz? read cSize alone, so they widen at ⊑ᶜ too — same
-- lemmas as above, projected
pathSz?-⊑ : ∀ {n} {Γ : Ctx n} {s t} {c c′ : Caps} (p : Path Γ s t) →
  c ⊑ᶜ c′ → pathSz? (Caps.cSize c) p ≡ true → pathSz? (Caps.cSize c′) p ≡ true
pathSz?-⊑ p (sz≤ , _ , _) = pathSz?-widen p sz≤

pathsSz?-⊑ : ∀ {n} {Γ : Ctx n} {s t} {A : Set} {c c′ : Caps}
  (ps : List (A × Path Γ s t)) →
  c ⊑ᶜ c′ → all (λ rp → pathSz? (Caps.cSize c) (proj₂ rp)) ps ≡ true
          → all (λ rp → pathSz? (Caps.cSize c′) (proj₂ rp)) ps ≡ true
pathsSz?-⊑ ps le = all-impl _ _ (λ rp → pathSz?-⊑ (proj₂ rp) le) ps

frameSz?-⊑ : ∀ {n} {Γ : Ctx n} {s u} {c c′ : Caps} (f : Frame Γ s u) →
  c ⊑ᶜ c′ → frameSz? (Caps.cSize c) f ≡ true → frameSz? (Caps.cSize c′) f ≡ true
frameSz?-⊑ f (sz≤ , _ , _) = frameSz?-widen f sz≤

-- the burst constructors the delivery clique assembles its emits from
burstCaps?-∷ : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
  all (eventCaps? c sl) (InstEmit.events em) ≡ true →
  burstCaps? c sl str ≡ true →
  burstCaps? c sl (em ∷ str) ≡ true
burstCaps?-∷ c sl em str he hst = ∧-intro he hst

burstCaps?-++ : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (xs ys : Stream Γ u) →
  burstCaps? c sl xs ≡ true → burstCaps? c sl ys ≡ true →
  burstCaps? c sl (xs ++ ys) ≡ true
burstCaps?-++ c sl xs ys hx hy =
  all-++-intro (λ em → all (eventCaps? c sl) (InstEmit.events em)) xs ys hx hy

-- THE SLOT TRANSPORT.  Everything above is at a fixed telescope; this
-- is what moves a bound from one Sched's telescope to another's, and
-- it is a plain subst precisely because the predicates take Slots
valsCaps?-slots : ∀ {n} {Γ : Ctx n} {c : Caps} {sl sl′ : Slots Γ}
  (u : Ty) (vs : List (Val Γ u)) → sl′ ≡ sl →
  all (valCaps? c sl u) vs ≡ true → all (valCaps? c sl′ u) vs ≡ true
valsCaps?-slots {c = c} u vs eq = subst (λ x → all (valCaps? c x u) vs ≡ true) (sym eq)

eventsCaps?-slots : ∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
  (evs : List (InstEvent (Val Γ u))) → sl′ ≡ sl →
  all (eventCaps? c sl) evs ≡ true → all (eventCaps? c sl′) evs ≡ true
eventsCaps?-slots {c = c} evs eq = subst (λ x → all (eventCaps? c x) evs ≡ true) (sym eq)

burstCaps?-slots : ∀ {n} {Γ : Ctx n} {u} {c : Caps} {sl sl′ : Slots Γ}
  (str : Stream Γ u) → sl′ ≡ sl →
  burstCaps? c sl str ≡ true → burstCaps? c sl′ str ≡ true
burstCaps?-slots {c = c} str eq = subst (λ x → burstCaps? c x str ≡ true) (sym eq)

obsListCaps?-slots : ∀ {n} {Γ : Ctx n} {s} {c : Caps} {sl sl′ : Slots Γ}
  (q : List (Closed Γ s)) → sl′ ≡ sl →
  all (obsCaps? c sl) q ≡ true → all (obsCaps? c sl′) q ≡ true
obsListCaps?-slots {c = c} q eq = subst (λ x → all (obsCaps? c x) q ≡ true) (sym eq)

-- and the two event-list constructors the delivery clique builds emits
-- from: a payload list becomes `value` events, a completion flag becomes
-- at most a `complete`
mapValue-caps : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ)
  (u : Ty) (vs : List (Val Γ u)) →
  all (valCaps? c sl u) vs ≡ true → all (eventCaps? c sl) (map value vs) ≡ true
mapValue-caps c sl u []       h = refl
mapValue-caps c sl u (v ∷ vs) h with ∧-true (valCaps? c sl u v) (all (valCaps? c sl u) vs) h
... | hv , hvs = ∧-intro hv (mapValue-caps c sl u vs hvs)

finList-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ) (b : Bool) →
  all (eventCaps? {n = n} {Γ = Γ} {u = u} c sl)
      (if b then complete ∷ [] else []) ≡ true
finList-caps c sl true  = refl
finList-caps c sl false = refl

closeList-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (src : Source) (b : Bool) →
  all (eventCaps? {n = n} {Γ = Γ} {u = u} c sl)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-caps c sl src true  = refl
closeList-caps c sl src false = refl

------------------------------------------------------------------
-- THE DELIVERY CLIQUE'S SLOTS COROLLARIES.
--
-- .Keeps-Ring covers the subscribe side.  foldPath / dispatchShare /
-- shareGo are the DELIVERY side, and the caps clauses below need
-- exactly their slotsEq: an in-flight bound established before a
-- sub-call is stated at the entry telescope, and the clause has to
-- report it after the sub-call has moved the Sched.
--
-- Only the slots half is proven.  The connected-shares half of KeepsC
-- is the wet ledger's business (sharedConnect-unconn); nothing on the
-- caps side reads it, and half a record is not worth carrying.
--
-- The recursion mirrors the evaluator's own, which is why it
-- terminates: foldPath descends the chain, hands off to dispatchShare
-- at a share sink, which spends one dispatch gas into shareGo, which
-- folds each admitted registration back through foldPath.  shareLatch,
-- shareAdmit and shareFinish move the registry, the live set and the
-- dying/completed ledgers and never the telescope, so they cost a refl.
------------------------------------------------------------------

foldPath-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))
    ≡ Sched.slots sched

dispatchShare-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))
    ≡ Sched.slots sched

shareGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots
    (proj₁ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))
    ≡ Sched.slots sched

foldPath-slots sf gas id now envSrc root vals evs fin sched st = refl
foldPath-slots sf gas id now envSrc (share-sink i) vals evs fin sched st =
  dispatchShare-slots sf gas id now i vals fin sched st
foldPath-slots sf gas id now envSrc (f ↠ p) vals evs fin sched st =
  trans (foldPath-slots sf gas id now envSrc p
           (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step)))
           (proj₁ (proj₂ (proj₂ (proj₂ step))))
           (proj₂ (proj₂ (proj₂ (proj₂ step)))))
        (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))
  where
  step = stepFrame sf id now f p vals fin sched st

dispatchShare-slots sf zero    id now i vals fin   sched st = refl
dispatchShare-slots sf (suc gas) id now i vals false sched st =
  shareGo-slots sf gas id now i vals false
    (shareAdmit i (EvalSt.registry st)) sched st
dispatchShare-slots sf (suc gas) id now i vals true  sched st =
  shareGo-slots sf gas id now i vals true
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st)

shareGo-slots sf gas id now i vals fin []              sched st = refl
shareGo-slots sf gas id now i vals fin ((rid , p) ∷ ps) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-slots sf gas id now i vals fin ps sched st
... | false =
  trans (shareGo-slots sf gas id now i vals fin ps
           (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)))
        (foldPath-slots sf gas id now (toℕ i) p vals
           (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀)
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  FP  = foldPath sf gas id now (toℕ i) p vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀

------------------------------------------------------------------
-- THE FRAME FACE, FORWARD-DECLARED.
--
-- AND EVERY COMPANION NAMES ITS TELESCOPE.  `sl` with
-- `Sched.slots sched ≡ sl` rather than reading Sched.slots off each
-- Sched in sight: the in-flight predicates are stated at one fixed
-- telescope, so a sub-call's outputs and the caller's conclusion are
-- already at the same index and the whole composition costs ONE
-- `trans` against the sub-call's slots corollary, instead of a
-- transport per carried bound.  caps-tick was already written this
-- way; the tree now matches it.

-- EVERY COMPANION CARRIES `2 ≤ Caps.cSize c`, and it is not decoration.
-- The tree's only arithmetic is widening a sub-result from frameStep j
-- to frameStep (j + j′), which is frameStep-mono-j — and that has a
-- side condition, because foldStep S is inflationary only for S ≥ 2
-- (w ≤ S ^ suc w fails at S = 1).  S is cSize c, so the condition is
-- `2 ≤ Caps.cSize c`.  It is threaded UNCHANGED (c never moves inside
-- a frame, only j does) and supplied once at the top by
-- 2≤capsAt-size, which the recurrence proves rather than assumes.
-- THE CHAIN HYPOTHESIS IS SEPARATE FROM THE SIZE ONE, and that is the
-- joint-bound repair (Joint-Probe, 2026-07-31).  What stood here was
-- `pathLen κ + sizeᵉ b ≤ cSize` — a JOINT bound the delivery side
-- cannot supply, since it carries the two separately and their sum can
-- be twice the cap.  Joint-Probe measured the joint form false at the
-- tight admissible cSize on all seventeen families, and adm + 1
-- EXACTLY on every scan family: the payload being subscribed IS the
-- stored accumulator, so it alone attains the cap and any chain at all
-- overshoots.  No slackening survives that.  The pair below is what
-- foldPath-caps already splits out of pathSz?, and the +1 each *All
-- hop adds is absorbed by the j that hop pays — frameStep-chain-suc.
-- (a) THE REPAIRED FRAME FACE: a subscribe consumes some number of
-- folds and reports how many.  j′ folds spent means the caps advance
-- from frameStep j to frameStep (j + j′), never staying put.
--
-- SURVEYED, NOT ATTEMPTED (2026-07-31), now that every COMPANION is
-- ground and this is the only caps face left.  Three things it needs
-- that are not clause work, recorded so the next leg starts from a
-- statement rather than from a grind:
--
-- (i)  TWO COMPANIONS DO NOT EXIST YET.  Seven of the thirteen clauses
--      end in `pushBurst fuel id now f κ burst …` (mapᵉ, takeᵉ, scanᵉ)
--      or in `subscribeAll` (the four *All heads), and neither has a
--      caps companion.  Both look like ordinary grinds — pushBurst is
--      foldPath's `↠` clause per emit, over the now-ground
--      stepFrame-caps, and subscribeAll is mintNode + installNode +
--      this face at `thru-outer op nid ↠ κ` + pushBurst, one more
--      instance of the same one-j-per-hop absorption
--      (frameStep-chain-suc) subscribeInner-caps runs on.
--
-- (ii) TWO CLAUSES BUILD VALUES BY EVALUATION, and land where
--      mapFrame-caps / scanFrame-caps already are.  `ofᵉ ts` bursts
--      `map evalTm ts` and `scanᵉ f seed b` installs
--      `scan-st (evalTm seed)`; evalWith-size is a TOWER in the term's
--      syntax, so neither is `sizeᵛ ≤ sizeᵗ` and both want an
--      existential j′ of their own.  `μᵉ body` is the same shape once
--      more — unfoldμ is LARGER than the μ (only syncSizeᵉ is
--      preserved, syncSize-unfoldμ; sizeᵉ is not) — so its recursive
--      call has no size hypothesis until one is stated.
--
-- (iii) THE ONE THAT WAS A STATEMENT-LEVEL GAP, NOW REPAIRED (the
--      parked-width ruling, 2026-07-31).  `deferᵉ body` PARKS AN
--      OBSERVABLE ON THE SCHEDULE: its clause adds a LiveSource at
--      `elemTy = obs u` with `pending = (suc now , body)`, so
--      capsOK?'s widLive conjunct demands a WIDTH for the body — and
--      `outWᵉ (deferᵉ e) = 0` by definition (a defer crosses a tick,
--      and that semantics is load-bearing on the wet side), so no
--      outW-derived entry measure supplied it.
--
--      THE REPAIR IS SUPPLY-SIDE AND CAPS-SIDE ONLY.  Rx.Frame-Width
--      gains dW — the PARKED width, ⊔-collecting every deferᵉ
--      subterm's `outWᵉ body ⊔ dWᵉ body` — and pW = outW ⊔ dW.  The
--      caps side reads pW (widLive, widNode, valCaps?, obsCaps?), the
--      wet side keeps outW untouched, and capsAt's base pays for both
--      through the ENTRY CEILING it now carries.
--
--      AND THE TELESCOPE CONJUNCT IS dW, NOT pW, which is the one
--      place the ruling's shape had to be sharpened in the making.
--      `dWᵉ n sl (deferᵉ body) = pWᵉ n sl body` EXACTLY, so a dW
--      hypothesis serves the defer clause with nothing to spare — and
--      it DESCENDS, which pW does not: `outWᵉ (mergeAllᵉ e)` is
--      `outWᵉ e * innWᵉ e`, which is 0 at `innWᵉ e = 0` (take
--      `e = ofᵉ (strmᵗ emptyᵉ ∷ [])`: outW 1, innW 0), so a pW
--      hypothesis at `mergeAllᵉ e` says nothing about `e` and the
--      *All clause could not recurse.  dW is a plain ⊔-collect through
--      every constructor, so every structural descent is m≤m⊔n.  Every
--      supplier still works, because all three supply pW ≥ dW: payload
--      paths from valCaps?'s width half, the root from the base, and
--      sharedConnect from slotsCaps?, which gains a width half at pW
--      on its shared branch
--
-- AND IT IS NO LONGER A POSTULATE: it is FORWARD-DECLARED here (so the
-- companion tree below can call it, exactly as foldPath-caps and its
-- clique are declared before they are defined) and GROUND at the end
-- of the file, on pushBurst-caps, subscribeAll-caps and the three
-- evaluation obligations named there
-- the two bookends of `cascade` and the chain snapshot are no longer
-- postulated either: they are GROUND below, on the same two filter
-- lemmas the share leaves use.

subscribeE-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeE g b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

------------------------------------------------------------------
-- (b) THE CASCADE COMPANION, AND THE BUDGET CLAIM, AS AN ASSEMBLY.
--
-- This is the most refutation-scarred statement in the file: three
-- counts have failed it — `cWid * cReg` (tickFits-absurd), then
-- `cWid * cReg * cSize` (nested shares beat it exponentially), then
-- `2 ^ cReg * cSize`, whose middle step Mint-Loop-Probe measured false.
-- Each time the failure was at ROUTE level and each time it was found by
-- running something rather than by proving something.  So the conjunct is
-- not stated as one opaque claim here; it is DECOMPOSED first, with the
-- pieces postulated, so that the next failure lands on a named statement
-- instead of three clauses into a grind.
--
-- THE THREE PIECES.  Write `D` for the deliveries a cascade makes — one
-- per registration it folds into, which is exactly what its own ledger
-- counts, since every delivering clause of `cascadeGo` and `shareGo`
-- conses one `rid` onto `delivered`.  Then
--
--   (i)  cascadeGo-charge      j ≤ D * cSize
--   (ii) cascadeGo-deliveries  D ≤ cDel c, the delivery RECURSION
--
-- and `cascadeGo-caps` below is their product, by arithmetic and nothing
-- else.  (i) is the per-delivery charge: every fold is a frame on some
-- delivery's chain, and a chain is shorter than cSize by pathSz?'s own
-- length conjunct — this is the half the induction already carries, in
-- the shape `foldPath-caps` reports it.  (ii) is the delivery bound, and
-- it is where all the difficulty is.
--
-- (ii) HAS NOW BEEN WRONG THREE TIMES, and the third correction is the
-- only one that was PREDICTED before it was measured.  The history:
--
--   · `2 ^ cReg` — refuted, because `shareAdmit` reads the registry as
--     of the dispatch, so the DAG the paths run through is the END
--     registry.  Mint-Loop-Probe's three-level lean ladder at k = 2
--     delivers 176 out of an entry registry of 7.
--   · `2 ^ cReg * 2 ^ cReg` — the pair story (pre-state registrations
--     visited × an index for the minted ones gone through).  Both
--     decompositions of the second coordinate were measured false
--     (fibreCap ≤ cSize: 4 against 3; fibreCap ≤ 2 ^ cReg: 576 against
--     512), so the conjunct was stated whole and gated on
--     Mint-Loop-Probe's rows and nothing else.
--   · AND THE WHOLE SQUARE IS FALSE.  Delivery-Law-Prediction.md
--     derived the delivery recurrence from the evaluator's structure
--     and committed the L = 5 rows BEFORE measuring them; every
--     checkable row then matched EXACTLY (3 D values, 2 increments, 3
--     fire vectors, 3 delivery splits, 6 generation counts, 3 cReg, 3
--     cSize, 2 mPre).  The law puts D(5,5) at 4514934 against
--     `4 ^ cReg = 4194304`.
--
-- AND THE 2-TOWER `2 ^ (2 ^ cReg)` IS GONE TOO, not because a row
-- breached it — none does — but because NOTHING CAN PROVE IT, and the
-- reason is arithmetic rather than route-finding.  Every route to a
-- bound reading cReg alone rests on the same two facts,
--
--     R ≤ cReg + Q · D          D ≤ (1 + R) ^ (1 + n)
--
-- i.e. `D ≤ (1 + cReg + Q · D) ^ (1 + n)`, whose right-hand side
-- outgrows its left at EVERY D.  The pair bounds nothing, and no
-- CLOSED F repairs it: F would have to satisfy
-- `F ≥ (1 + cReg + Q · F) ^ (1 + n)`, and no natural number does.  So
-- the delivery bound stops being a formula and becomes a RECURSION,
-- `cDel` (.Caps), read off the same two facts SEQUENTIALLY — the walk
-- is one chain at a time, and the registry a chain sees is the entry
-- registry plus the mints of the deliveries ALREADY MADE.  That is the
-- ordering fact the mint loop natively obeys, and recursion on
-- (dispatch gas, walk position) is well-founded exactly where the
-- closed form was circular.
--
-- THE PROOF ROUTE IS THE HOLE, and the one that was named here — the
-- generation-ancestry injection into subsets of the fire schedule — is
-- REFUTED, by rows that are now in the repo rather than by a failed
-- grind.  The amplifier family it was gated on has since been measured
-- (Mint-Loop-Shapes MEASUREMENT 9): a minting scan INSIDE a shared def
-- makes mints beget FIRES, and pB's slot 0 fires 3 / 7 / 11 / 12 times
-- where the pure share DAG dispatches it 2.  Fires are not
-- entry-computable, so they cannot carry the exponent, and the subset
-- half is dead for the reason MEASUREMENT 8(d) already gives for every
-- subset injection.  The full refutation, the closed delivery
-- recurrence that survives it, and the two closed forms that DO follow
-- from that recurrence (neither of which closes against a bound reading
-- cReg alone) are written at the postulate itself, below.
--
-- THE FEEDBACK LOOP BEHIND ALL OF THIS IS MEASURED AND DOES NOT TOWER
-- IN THE NESTING DEPTH.  Mint-Loop-Probe: deliveries SATURATE in k (5
-- flat at one shared level; 20, 26, 27, 27 at two; 50 … 269 at three)
-- because a minted registration is only reachable by dispatches that
-- come after it and how many remain is fixed by the PRE-STATE DAG.  j
-- saturates too, but LATER — 58, 226, 548, 912, 1164, 1268, 1291 —
-- because nesting keeps lengthening the chains after it has stopped
-- widening them.  The mid-cascade subscription that drives the loop is
-- real rxjs, not an evaluator artifact: a subscriber added mid-cascade
-- misses the in-flight emission and receives the cascade's later ones,
-- checked against rxjs 7.8 at the probe's head.
--
-- AND (i) IS THE FACE THAT IS NOW SUSPECT, not (ii).  `j ≤ D * cSize`
-- charges cSize per delivery, but the receipt scanFrame-caps actually
-- pays is `suc (length vals * suc (sizeᵗ fn))` — one fold per node of
-- the step function PER PAYLOAD — and `length vals` is a BURST WIDTH,
-- which nothing entry-readable bounds.  It cannot be paid by cWid:
-- Width-Count-Probe proves a count reading cWid iterates the tower
-- function once per instant, which destroys capsAt-tower's linear
-- height and caps-fuel-root with it.  Nor by an entry width:
-- Frame-Work-Probe measures a frame's payload count climbing the width
-- ladder across arrivals (2 ↦ 8).  Where the width factor is paid for
-- is the open question this face carries, and it is a design ruling
-- rather than a clause grind.
--
-- caps-tick is then a COROLLARY rather than a sibling face: widen the
-- reported level to the endpoint by frameStep-mono-j, and the endpoint
-- IS capsAt (suc id) by capsAt-suc-full
------------------------------------------------------------------

------------------------------------------------------------------
-- WHAT THE WALK READS OFF THE CAPS: three tiny lemmas and one new
-- ledger, all of them plumbing for the instantiation below.
--
-- `valsCaps?` is `valCaps?` lifted to a burst: every payload under the
-- caps, AND the burst no wider than the width cap.  The width conjunct
-- is not decoration — it is the one thing that makes a per-frame mint
-- budget finite at all, because a `thru-outer` frame subscribes once
-- per payload (thruWalk) and so mints in proportion to its burst
-- width.  Without it the frame budget is false rather than unproven,
-- for any fixed budget whatsoever.  It is the same width factor
-- cascadeGo-charge pays per delivery, charged in the same place: at
-- the ENTRY caps.
------------------------------------------------------------------

valsCaps? : ∀ {n} {Γ : Ctx n} {s} → Caps → Slots Γ → List (Val Γ s) → Bool
valsCaps? {s = s} c sl vs =
  all (valCaps? c sl s) vs ∧ (length vs ≤ᵇ suc (Caps.cWid c))

-- pathSz?'s length conjunct, read back out: the OUTERMOST one bounds
-- the whole chain, and root / share-sink have no length at all
pathSz?-len : ∀ {n} {Γ : Ctx n} {u t} (B : ℕ) (p : Path Γ u t) →
  pathSz? B p ≡ true → pathLen p ≤ B
pathSz?-len B root           h = z≤n
pathSz?-len B (share-sink i) h = z≤n
pathSz?-len B (f ↠ p)        h =
  ≤ᵇ⇒≤ (suc (pathLen p)) B
    (T-to (proj₁ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                   (proj₂ (∧-true (frameSz? B f)
                                  ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h)))))

pathSz?-tail : ∀ {n} {Γ : Ctx n} {s u t} (B : ℕ)
  (f : Frame Γ s u) (p : Path Γ u t) →
  pathSz? B (f ↠ p) ≡ true → pathSz? B p ≡ true
pathSz?-tail B f p h =
  proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
          (proj₂ (∧-true (frameSz? B f)
                         ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) h)))

postulate
  -- (i) THE PER-DELIVERY CHARGE, IN THE NEW CURRENCY.  The receipt the
  -- induction actually builds, charged to the cascade's own delivery
  -- ledger rather than to a count: every fold is a frame on some
  -- delivery's chain, and pathSz?'s length conjunct caps a chain at
  -- cSize.
  --
  -- AND THE WIDTH FACTOR IS REAL, which is what changed.  `j ≤ D * cSize`
  -- was measured FALSE by Charge-Probe — progW breaches at 47 against 40
  -- — because `scanFrame-caps`'s receipt is
  -- `suc (length vals * suc (sizeᵗ fn))`, one fold per node of the step
  -- function PER PAYLOAD, and `length vals` is a burst width.  The form
  -- below is the one that fits all 21 Instant-Height rows, worst ratio
  -- 0.16, with cWid standing in for the arrival's payload width.
  -- Reading cWid used to be forbidden (it would have destroyed
  -- capsAt-tower's LINEAR height); the height is a recurrence now, so
  -- the prohibition is gone with the closed form
  cascadeGo-charge : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? c sched st ≡ true →
    valCaps? c sl (arrTy a) (arrVal a) ≡ true →
    all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
    length chains ≤ Caps.cReg c →
    let r = cascadeGo a id chains sched st
    in Σ ℕ λ j → (j ≤ delivN st (proj₂ (proj₂ r)) * Caps.cSize c
                        * suc (suc (Caps.cWid c) * suc (Caps.cSize c)))
       × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

-- (ii) THE DELIVERY BOUND, WHOLE, AND AS A RECURSION.  One cascade's
-- deliveries against `cDel c = dCap (chargeW c) (suc cSize) cReg` —
-- the gas-indexed walk of .Caps, not a closed form.  Both closed
-- forms it replaces are dead: the squared-subset `4 ^ cReg` is FALSE
-- (the delivery law, committed before the L = 5 rows were measured
-- and then matching every checkable one exactly, puts D(5,5) at
-- 4514934 against 4 ^ 11 = 4194304), and the 2-tower
-- `2 ^ (2 ^ cReg)` that replaced it is UNPROVABLE — see the
-- self-reference above, which is a property of the two facts and not
-- of any route through them.
--
-- THE ROUTE THAT WAS NAMED HERE IS REFUTED BY ROWS ALREADY IN THE
-- REPO, and it is refuted before any clause of it was ground.  It
-- read: a minted registration's mint-edge ancestry is a SUBSET of the
-- fire schedule (generation g ↦ g-subsets, which is what the binomial
-- counts are), and the fires are bounded by the PRE-STATE DAG.  Both
-- halves fail:
--
--   · THE SUBSET HALF.  Mint-Loop-Shapes' MEASUREMENT 8(d) ruling —
--     "every subset-injection route is dead for the delivery bound,
--     whether or not the bound is true" — applies to this injection
--     too, since it is one.  The surviving inverted-pair leg proves
--     `D ≤ 2 ^ R_end`, and R_end is 261 against an entry cReg of 7
--     (254 mints on a 269-delivery cascade), so it proves 2 ^ 261
--     against a demand of 2 ^ 128.
--   · THE FIRES HALF.  "Fires are bounded by the pre-state DAG" was
--     the lean ladders' property, and MEASUREMENT 9 — the amplifier
--     family, `pB` / `insB`, a minting scan INSIDE a shared def — is
--     the family where it stops holding.  pB's slot 0 fires 3 times
--     at cascade 0 and 7, 11, 12 times at cascade 1 for k = 0, 1, 2,
--     where the share DAG alone dispatches it 2 times.  Mints beget
--     fires; the fire count is not entry-computable, so it cannot
--     carry the exponent.
--
-- WHAT IS ESTABLISHED, AND IS ROUTE-INDEPENDENT: the delivery ledger
-- obeys a CLOSED RECURSION with exactly one unbounded input.
-- `EvalSt.delivered` is consed at exactly two sites in the evaluator
-- — shareGo's uncancelled clause and cascadeGo's — and dispatchShare
-- is called from exactly one, foldPath's `share-sink` clause.  So,
-- writing Dfp for one foldPath's deliveries at dispatch gas g,
--
--     D(cascadeGo)     = Σ over uncancelled chains of (1 + Dfp n)
--     Dfp g root       = 0
--     Dfp g (f ↠ p)    = Dfp g p            -- stepFrame delivers nothing
--     Dfp g (sink i)   = Dds g
--     Dds 0            = 0
--     Dds (suc g)      = Σ over shareAdmit i (registry AS OF NOW)
--                          of (1 + Dfp g)
--
-- THAT RECURSION IS NO LONGER A READING OF THE SOURCE: it is proven,
-- line for line, in .Deliveries § D — foldPath-root-N / foldPath-frame-N
-- / foldPath-sink-N / dispatchShare-zero-N / dispatchShare-suc-N /
-- shareGo-skip-N / shareGo-cons-N / cascadeGo-skip-N /
-- cascadeGo-cons-N, over the ledger order `_⊑ᵈ_` and its composition
-- laws (delivN-split, delivN-cons).  The `↠` line is an equality and
-- not an inequality because the WHOLE stepFrame clique preserves
-- `EvalSt.delivered` (.Deliveries § B, fifteen mutually recursive
-- functions, no postulate); Mint-Loop-Frames' refl pins of `mJdel`
-- against `mFolds` at 5, 20 and 50 were the measured evidence for that
-- and are now a redundant cross-check.  Two closed forms follow, and
-- NEITHER closes against a bound that reads cReg alone:
--
--   (α) the depth form.  The share telescope orders the shares along
--       any fire path strictly, and dispatch gas caps the depth at n,
--       so D ≤ cReg * (1 + Rmax) ^ n with Rmax the registry length at
--       its peak.  Needs n * log Rmax ≤ 2 ^ cReg.
--   (β) the subset form.  D ≤ 2 ^ Rmax.  Needs Rmax ≤ 2 ^ cReg, which
--       is the 261-against-128 row above.
--
-- and Rmax ≤ cReg + (mints), mints ≈ D, so (α) READ AS A CLOSED FORM
-- is the self-referential `D ≤ cReg * (1 + cReg + Q · D) ^ n` and
-- bounds nothing — for any Q, any n, and any bound in its place.
--
-- AND THAT IS WHY THE STATEMENT ITSELF MOVED.  The damper is the
-- ORDERING fact Mint-Loop-Shapes names — a minted registration is
-- reachable only by dispatches that come AFTER it — so the bound is
-- written as the walk that fact describes rather than as a number the
-- walk is compared against.  `cDel c` is (α) done SEQUENTIALLY: the
-- top walk has cReg chains, each subtree runs at one dispatch gas
-- less, and the registry a chain sees is the entry registry plus
-- `chargeW c` mints for each delivery ALREADY MADE.  The proof is
-- then a schedule-indexed induction on the same two indices the
-- definition recurses on, with .Deliveries' § D equations supplying
-- the delivery counting.
--
-- THE ROWS ALL FIT WITH ENORMOUS MARGIN, which is the least
-- interesting thing about it: `cDel` at pL⁴'s entry caps
-- (cReg 9, cSize 3, gas 6) already exceeds every D in the repo, and
-- the deepest lean rung is D = 41510 at cReg = 11.  The margin was
-- never the problem; the self-reference was
--
-- AND THE WALK IS NOW PROVEN — the whole of it except ONE fact, which
-- is a design question rather than a grind.  .Delivery-Walk maps the
-- clique onto the recursion, with no postulate of its own:
--
--   foldPath      ↦ dCap  Q gas R      (dCap's gas IS the dispatch gas)
--   dispatchShare ↦ dCap  Q gas R
--   shareGo       ↦ dWalk Q gas R (length ps)
--   cascadeGo     ↦ dWalk Q n   R (length chains)
--
-- over .Deliveries' § D equations, `dWalk-front` (the walk decomposes
-- from the FRONT exactly as it does from the back — an equality, so
-- the change of direction the head-first evaluator forces costs
-- nothing), and a per-frame mint budget.  Instantiated at
-- Qf = cSize * suc cWid and B = cSize it gives exactly this
-- conjunct, since `chargeW c = cSize * suc (suc cWid * suc cSize)`
-- dominates `Qf * suc B` and `n ≤ cSize` (the hypothesis above)
-- lifts the evaluator's dispatch gas to cDel's index.
--
-- AND THE ONE FACT IT IS STILL RELATIVE TO IS A PER-FRAME FACE — at a
-- level the frame can honestly be charged at.  That fact is
-- `stepFrame-face` (below), and this conjunct is now a THEOREM off it:
-- see the instantiation at the end of the share-bookkeeping section.
--
-- CHARGING THAT FACE AT THE ENTRY CAPS IS REFUTED (2026-08-02).  Two
-- axioms — `stepFrame-entry-caps` and `stepFrame-entry-mint` — briefly
-- stood here and made this conjunct a theorem; both asserted SAME-LEVEL
-- preservation (post-state and output burst back under the entry `c`
-- the frame started from), and `agda/probe/Entry-Caps-Refuted.agda`
-- (make entry-caps-refuted, seconds) is a machine-checked
-- `Entry-Caps → ⊥`.  It falls on the cheapest frame there is, a
-- `map-f`, which touches no state at all: a map frame's output is
-- `map (applyFn fn) vals` and `applyFn` GROWS a value — `pairᵗ x x`
-- has size 3 and takes a payload of size 3 to one of size 7 — so at
-- `c = caps 3 1 1` every hypothesis holds by `refl` and the conclusion
-- computes to `false`.  That is `frameStep`'s own header ("same-level
-- preservation is false, so the face must report growth"),
-- `caps-frame-boundary-absurd`, and cascadeGo-wet's fold-threading
-- note, all saying one thing: a frame may not be charged at the level
-- it started from.
--
-- SO THE WALK CARRIES THE LEVEL.  `cDel c` is `dCapᶜ` at level 0 (.Caps):
-- a frame costs the receipt read at the level it RUNS at, a delivery
-- ITERATES that over its chain, and the registry a dispatch fans out
-- over is `capsOK?`'s own fifth conjunct read at the level.  The
-- delivery bound then follows from ONE per-frame face in the shape the
-- ground `stepFrame-caps` already reports in

cascadeGo-deliveries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
    ≤ cDel c

-- THE ASSEMBLY, ground: the conjunct is the three pieces multiplied out
cascadeGo-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j → (j ≤ sizeCount c)
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-caps c a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB =
  proj₁ CH
    , ≤-trans (proj₁ (proj₂ CH))
              (*-monoˡ-≤ (suc (suc (Caps.cWid c) * suc (Caps.cSize c)))
                 (*-monoˡ-≤ (Caps.cSize c)
                    (cascadeGo-deliveries c a id chains sl sched st
                       2≤S 1≤R slC slEq inv vC pS n≤S lenB)))
    , proj₂ (proj₂ CH)
  where
  CH = cascadeGo-charge c a id chains sl sched st 2≤S slEq inv vC pS lenB

------------------------------------------------------------------
-- THE SUBSCRIBE-SIDE COMPANION TREE, transcribed from subscribeE-walkS's
-- clique one for one.  That walk already solved the structural problem —
-- which companions exist, what each threads, how their results compose —
-- so the caps induction inherits the same tree with (INV?, E′-receipt)
-- swapped for (capsOK?, j-receipt): the pre-state and every input bound
-- read at `frameStep j c`, the post-state and every output bound at
-- `frameStep (j + j′) c`, composed ADDITIVELY by +-assoc where the wet
-- side composes by ≤-trans, and widened by capsOK?-mono ∘ frameStep-mono-j
-- wherever two sub-results meet at different levels.
--
-- Stated all at once, before any clause is ground, so that a change to
-- the shape changes it HERE — cheaply — rather than invalidating a pile
-- of finished clause proofs.
------------------------------------------------------------------

slotsCaps?-capsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  slotsCaps? (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) sl ≡ true
slotsCaps?-capsAt {n = n} e sl id =
  slotsCaps?-bound (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) sl
    (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id))
    (≤-trans (≤-trans (slotsPW≤entryCeil n sl e) (n≤1+n _))
             (capsAt-base-wid e sl id))
    (≤-trans (≤-trans (slotsIW≤entryCeil n sl e) (n≤1+n _))
             (capsAt-base-wid e sl id))

------------------------------------------------------------------
-- caps-tick, DERIVED.  This is the joint the whole round was about, and
-- it is now three lines of assembly over the companions rather than a
-- face of its own: latch, fold the snapshot chains (which reports a j
-- and, crucially, that the j FITS), widen that level to the endpoint,
-- and the endpoint is capsAt (suc id) by definition.
--
-- The arrival's own bounds are a hypothesis rather than a derivation:
-- `a` is handed in by the scheduler, and the per-instant induction that
-- consumes this reads it off sched-next's live source, which capsOK?'s
-- widLive/stBounded? conjuncts already bound
------------------------------------------------------------------

-- the two conjuncts caps-tick reads back out of capsOK?, extracted with
-- their result types pinned so ∧-true's booleans are determined
capsOK?-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
    (stBounded? (Caps.cSize c) sched st ≡ true)
  × (regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true)
  × (all (widLive (Caps.cWid c) (Sched.slots sched)) (Sched.live sched) ≡ true)
  × (all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
         (EvalSt.nodes st) ≡ true)
  × ((length (EvalSt.registry st) ≤ᵇ Caps.cReg c) ≡ true)
capsOK?-parts c sched st h with ∧-true _ _ h
... | h0 , r1 with ∧-true _ _ r1
... | h1 , r2 with ∧-true _ _ r2
... | h2 , r3 with ∧-true _ _ r3
... | h3 , h4 = h0 , h1 , h2 , h3 , h4

capsOK?-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true
capsOK?-regs c sched st h = proj₁ (proj₂ (capsOK?-parts c sched st h))

capsOK?-count : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → length (EvalSt.registry st) ≤ Caps.cReg c
capsOK?-count c sched st h =
  ≤ᵇ⇒≤ (length (EvalSt.registry st)) (Caps.cReg c)
       (T-to (proj₂ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st h))))))

------------------------------------------------------------------
-- THE SHARE BOOKKEEPING, caps side — three leaves the dispatch clause
-- consumes and nothing else does.  Two are refl-level (capsOK? reads
-- Sched.live, Sched.slots, EvalSt.nodes and EvalSt.registry, and
-- neither the latch nor the delivered ledger touches any of them);
-- shareFinish is the one with content, because it drops a source's
-- registrations and sweeps its live entry, and both have to be shown
-- to only SHRINK what capsOK? bounds.
------------------------------------------------------------------

-- latching a completing share records it in completedSources/dying,
-- which capsOK? does not read
shareLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (i : Fin n) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true → capsOK? c sched (shareLatch i fin st) ≡ true
shareLatch-caps c i false sched st h = h
shareLatch-caps c i true  sched st h = h

-- and marking a registration delivered is the same kind of nothing
capsOK?-delivered : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { delivered = rid ∷ EvalSt.delivered st }) ≡ true
capsOK?-delivered c rid sched st h = h

-- THE FINISH FILTER, shared by the share's and the cascade's.  Both
-- ends of a completing source do the same two things — drop its
-- registrations, sweep its live entry — and every one of capsOK?'s five
-- conjuncts survives by the two generic filter lemmas: the registry
-- shrinks (regsSz? by dropSource-all, the count by dropSource-len), the
-- live list shrinks (stBounded?'s live half and widLive by
-- sweepLive-all), the nodes and the slots are untouched
dropSweep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { live = sweepLive (dropSource src (EvalSt.registry st))
                                             (Sched.live sched) })
            (record st { registry = dropSource src (EvalSt.registry st) }) ≡ true
dropSweep-caps c src sched st inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ (∧-true _ _ h0)))
                     (proj₂ (∧-true _ _ h0)))
    (∧-intro (dropSource-all (λ en → pathSz? (Caps.cSize c)
                                       (proj₂ (proj₂ (proj₂ en))))
                src (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = dropSource src (EvalSt.registry st)
  P    = capsOK?-parts c sched st inv
  h0   = proj₁ P
  h1   = proj₁ (proj₂ P)
  h2   = proj₁ (proj₂ (proj₂ P))
  h3   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4   = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- the admitted snapshot is a SUBLIST of the registry — its own filter
-- rather than dropSource's, because it also has to match the chain's
-- element type against the share's — so its chains inherit the
-- registry's size bound
shareAdmit-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (i : Fin n)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  all (λ rp → pathSz? B (proj₂ rp)) (shareAdmit i rs) ≡ true
shareAdmit-caps B i [] h = refl
shareAdmit-caps {Γ = Γ} B i ((rid , s , (u , p)) ∷ r) h
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-caps B i r (proj₂ (∧-true _ _ h))
... | true  | no  _    = shareAdmit-caps B i r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (shareAdmit-caps B i r (proj₂ (∧-true _ _ h)))

-- finishing a completing share drops the source's registrations and
-- sweeps its live entry.  Both are the generic filters, so all five of
-- capsOK?'s conjuncts survive by the same two lemmas: the registry
-- shrinks (regsSz? by dropSource-all, the count by dropSource-len) and
-- the live list shrinks (stBounded?'s live half and widLive by
-- sweepLive-all).  The nodes and the burst are untouched
shareFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (i : Fin n) (fin : Bool) (sl : Slots Γ)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  capsOK? c (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) ≡ true →
  burstCaps? c sl (proj₁ out) ≡ true →
  let r = shareFinish i fin out
  in (capsOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? c sl (proj₁ r) ≡ true)
shareFinish-caps c i false sl out inv bc = inv , bc
shareFinish-caps c i true sl (emits , sched′ , st′) inv bc =
  dropSweep-caps c (toℕ i) sched′ st′ inv , bc

------------------------------------------------------------------
-- THE DELIVERY BOUND, GROUND — on ONE per-frame face, at the level the
-- frame RUNS at.
--
-- .Delivery-Walk proves the whole mapping of the delivery clique onto
-- `dCapᶜ` / `dWalkᶜ` relative to `Walk-Hyps`; this is that record,
-- instantiated, plus three lines of arithmetic.
--
--   OK J = the slot telescope is fixed, and capsOK? at `frameStep J c`
--   Pb J = pathSz? (cSize (frameStep J c)) — whose registry ledger IS
--          capsOK?'s regsSz? conjunct, so the walk's ledger costs the
--          caller nothing, and whose length conjunct (pathSz?-len) is
--          the chain cap the delivery charge iterates over
--   Vb J = valsCaps? (frameStep J c) sl, the burst ledger
--   S, W, R = the entry caps' three fields, and every reading the walk
--          makes of them — sizeAt / widAt / regAt / fCharge — is
--          `frameStep J c`'s own field, by refl
--
-- The closure facts are the share bookkeeping just above; the two
-- widenings are pathSz?-widen and valsCaps?-widen along ⊑ᶜ, at
-- frameStep-mono-j; the registry reading is capsOK?-count.  What is left
-- is ONE frame, and it is the postulate below.
------------------------------------------------------------------

-- the OK predicate the walk threads: capsOK? at the CURRENT level, plus
-- the slot telescope the burst ledger is written against
walkOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) → ℕ → Sched Γ → EvalSt e → Set
walkOK c sl J sched st =
  (Sched.slots sched ≡ sl) × (capsOK? (frameStep J c) sched st ≡ true)

-- the one closure fact with content: the finish drops a source's
-- registrations and sweeps its live entry, and neither touches slots
walkOK-finish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (J : ℕ) (i : Fin n) (fin : Bool)
  (out : Stream Γ t × Sched Γ × EvalSt e) →
  walkOK c sl J (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) →
  walkOK c sl J (proj₁ (proj₂ (shareFinish i fin out)))
                (proj₂ (proj₂ (shareFinish i fin out)))
walkOK-finish c sl J i false out                    h = h
walkOK-finish c sl J i true  (emits , sched′ , st′) h =
  proj₁ h , dropSweep-caps (frameStep J c) (toℕ i) sched′ st′ (proj₂ h)

-- the burst ledger widens with the level: the payloads by
-- valsCaps?-widen, the width conjunct because cWid grows
valsCaps?-lvl : ∀ {n} {Γ : Ctx n} {s} (c c′ : Caps) (sl : Slots Γ)
  (vs : List (Val Γ s)) → c ⊑ᶜ c′ →
  valsCaps? c sl vs ≡ true → valsCaps? c′ sl vs ≡ true
valsCaps?-lvl {s = s} c c′ sl vs le h =
  ∧-intro (valsCaps?-widen sl s vs le
             (proj₁ (∧-true (all (valCaps? c sl s) vs)
                            (length vs ≤ᵇ suc (Caps.cWid c)) h)))
          (≤ᵇ-widen (length vs) (s≤s (proj₁ (proj₂ le)))
             (proj₂ (∧-true (all (valCaps? c sl s) vs)
                            (length vs ≤ᵇ suc (Caps.cWid c)) h)))

postulate
  -- ONE FRAME, AT THE LEVEL IT RUNS AT — the only hole the delivery
  -- bound now stands on, and the shape the ground companion already
  -- reports in.
  --
  -- WHAT IS ALREADY PROVEN, AND IS NOT RESTATED HERE FOR FUN.
  -- `stepFrame-caps` (below, ground, six clauses over the whole frame
  -- clique) IS this statement minus two conjuncts: same hypotheses,
  -- same existential j′, same `capsOK? (frameStep (j + j′) c)` on the
  -- post-state, same `all (valCaps? (frameStep (j + j′) c) sl u)` on the
  -- output burst.  What it does NOT report is
  --
  --   (a) A BOUND ON j′.  Its Σ is unbounded, and the walk needs the
  --       growth to fit the level's own per-frame receipt
  --       `fCharge S W j = suc (suc cWid * suc cSize)` read at
  --       `frameStep j c`.  That IS the receipt the frame lemmas build
  --       — mapFrame-caps and scanFrame-caps both return
  --       `suc (sizeᵗ fn)`, and `sizeᵗ fn ≤ cSize` is frameSz?'s own
  --       conjunct — but the number is not in the statement, so it
  --       cannot be read back out of it.
  --   (b) THE WIDTH CONJUNCT of the burst ledger, `length (out) ≤ᵇ
  --       suc cWid` at the new level.  `valsCaps?` carries it because
  --       the mint budget needs it (a `thru-outer` frame subscribes once
  --       per payload), and no companion currently reports an output
  --       WIDTH at all.
  --
  -- WHY IT IS NOT THE REFUTED AXIOM.  `stepFrame-entry-caps` asserted
  -- the post-state and the output burst were back under the caps the
  -- frame STARTED at; this reports them at `frameStep (j + j′) c`, the
  -- level the frame's own folds grew to, which is exactly what
  -- `stepFrame-caps` proves.  The refuting witness satisfies this face
  -- with room: at `c = caps 3 1 1` the map-f frame's receipt is
  -- `suc (sizeᵗ dup) = 4`, inside `fCharge 3 1 0 = 9`, its output value
  -- has size 7 inside `cSize (frameStep 4 c) = 4665`, and its one
  -- payload is inside `suc cWid`.
  --
  -- WHAT WOULD REFUTE IT: one frame, run under `capsOK? (frameStep j c)`
  -- with a chain inside `pathSz? (cSize (frameStep j c))` and a burst
  -- inside `valsCaps? (frameStep j c) sl`, whose smallest admissible
  -- growth index exceeds `fCharge`, or whose output burst is wider than
  -- `suc (cWid (frameStep (j + j′) c))` for every admissible j′.  The
  -- corner to aim at is `thru-outer`, which subscribes once per payload:
  -- Frame-Work-Probe measures its per-frame payload count climbing 6 ↦
  -- 120 across arrivals, against a cWid that `wid-dominates-120` puts at
  -- ≥ 1024 one cascade in
  stepFrame-face : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (j : ℕ) (sl : Slots Γ) (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) (f ↠ κ) ≡ true →
    valsCaps? (frameStep j c) sl vals ≡ true →
    let r = stepFrame g id now f κ vals fin sched st
    in Σ ℕ λ j′ →
       (j′ ≤ fCharge (Caps.cSize c) (Caps.cWid c) j)
       × (capsOK? (frameStep (j + j′) c)
                  (proj₁ (proj₂ (proj₂ (proj₂ r))))
                  (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

walkH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Caps) (sl : Slots Γ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Walk-Hyps e (Caps.cSize c) (Caps.cWid c) (Caps.cReg c)
walkH c sl 2≤S 1≤R slC = record
  { OK        = walkOK c sl
  ; Pb        = λ J p → pathSz? (Caps.cSize (frameStep J c)) p
  ; Vb        = λ J vs → valsCaps? (frameStep J c) sl vs
  ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p h
  ; p-tail    = λ J f p h → pathSz?-tail (Caps.cSize (frameStep J c)) f p h
  ; p-widen   = λ le p h → pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le)) h
  ; v-widen   = λ le vs h → valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le) h
  ; ok-reg    = λ J sched st ok → capsOK?-count (frameStep J c) sched st (proj₂ ok)
  ; ok-cons   = λ J rid sched st ok →
                  proj₁ ok , capsOK?-delivered (frameStep J c) rid sched st (proj₂ ok)
  ; ok-latch  = λ J i fin sched st ok →
                  proj₁ ok , shareLatch-caps (frameStep J c) i fin sched st (proj₂ ok)
  ; ok-finish = λ J i fin out ok → walkOK-finish c sl J i fin out ok
  ; sf-step   = λ J sf id now f path′ vals fin sched st ok hP hV hL →
                  let r  = stepFrame sf id now f path′ vals fin sched st
                      FC = stepFrame-face c J sl sf id now f path′ vals fin sched st
                             2≤S 1≤R (proj₁ ok) slC (proj₂ ok) hP hV in
                  proj₁ FC
                  , proj₁ (proj₂ FC)
                  , ( trans (KeepsC.slotsEq
                               (stepFrame-keeps sf id now f path′ vals fin sched st))
                            (proj₁ ok)
                    , proj₁ (proj₂ (proj₂ FC)) )
                  , proj₂ (proj₂ (proj₂ FC))
                  , capsOK?-regs (frameStep (J + proj₁ FC) c)
                      (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))
                      (proj₁ (proj₂ (proj₂ FC)))
  }

-- and the bound itself: the walk at level 0, then three widenings — the
-- dispatch gas to cDel's index (n ≤ cSize), the walk length to the
-- registry cap (length chains ≤ cReg), and dCapᶜ's own unfolding, which
-- is what `cDel` abbreviates
cascadeGo-deliveries {n = n} {e = e} c a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB =
  ≤-trans (W.Res.cnt (W.cascadeGo-go 0 a id chains sched st
             ((slEq , invʲ) , capsOK?-regs c sched st inv)
             pS (∧-intro (∧-intro vC refl) refl)))
    (≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                (regAt (Caps.cSize c) (Caps.cReg c) 0)
                2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
             (≤-reflexive (sym (cDel-body c))))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) 2≤S
                  (walkH c sl 2≤S 1≤R slC)

------------------------------------------------------------------
-- GRINDING THE TREE, most uncertain first: subscribeInner-caps, the
-- self-feeding edge.  The inner observable is drawn from a BURST
-- PAYLOAD rather than from the syntax, so every hypothesis it hands to
-- subscribeE-caps comes off valCaps? — its size from the cSize half,
-- its chain from κ extended by the from-inner frame.  If the caps face
-- were going to fail to close on itself, it would fail here.
--
-- It does not.  The clause is two lines: out of gas, nothing happens
-- (j′ = 0, a dry close, no values); with gas, subscribeE-caps at the
-- extended path, then split the burst.
--
-- AND THIS IS WHERE THE HOP PAYS ITS j.  Under the old joint bound the
-- clause consumed `suc (pathLen κ) + sizeᵛ (obs u) o ≤ cSize` and built
-- the extended chain's hypotheses out of its slack — free, and false on
-- real runs (Joint-Probe).  Now it recurses at level `suc j` instead:
-- one j buys `sizeStep S B ≥ suc B`, which is the one extra frame, and
-- the receipt comes back as `suc j₂` rather than `j₂` — `+-suc` is the
-- only arithmetic the change costs, three times, once per output.
------------------------------------------------------------------

-- capsOK? reads slots, live and the store — never the node counter, so
-- minting an instance id is free (record eta makes this refl)
capsOK?-nextNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (k : NodeId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { nextNode = k }) st ≡ true
capsOK?-nextNode c k sched st h = h

-- splitting one emit's events, and a whole burst, at the caps
splitEvents-vals-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? c sl) es ≡ true →
  all (valCaps? c sl s) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-caps c sl []              h = refl
splitEvents-vals-caps c sl (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h)))
splitEvents-vals-caps c sl (init _    ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (close _ _ ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (handoff _ ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))
splitEvents-vals-caps c sl (complete  ∷ es) h =
  splitEvents-vals-caps c sl es (proj₂ (∧-true _ _ h))

splitEvents-bk-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? c sl) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-caps c sl []               = refl
splitEvents-bk-caps {u = u} c sl (value _  ∷ es) = splitEvents-bk-caps {u = u} c sl es
splitEvents-bk-caps {u = u} c sl (init _   ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (close _ _ ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (handoff _ ∷ es) =
  ∧-intro refl (splitEvents-bk-caps {u = u} c sl es)
splitEvents-bk-caps {u = u} c sl (complete ∷ es) = splitEvents-bk-caps {u = u} c sl es

splitBurst-vals-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ s) →
  burstCaps? c sl str ≡ true →
  all (valCaps? c sl s) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-caps c sl []         h = refl
splitBurst-vals-caps {Γ = Γ} {u = u} c sl (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-caps c sl (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-caps {u = u} c sl ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-caps : ∀ {n} {Γ : Ctx n} {s u : Ty} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ s) →
  all (eventCaps? c sl) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-caps c sl []         = refl
splitBurst-bk-caps {Γ = Γ} {u = u} c sl (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-caps {u = u} c sl (InstEmit.events em))
    (splitBurst-bk-caps {u = u} c sl ems)

subscribeInner-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
-- OUT OF GAS: a dry close and nothing else.  The only state change is
-- the instance counter, which capsOK? does not read
subscribeInner-caps c j g0 op allNid κ id now o sl sched st 2≤S 1≤R slEq slC inv vC pC lC =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (record sched { nextNode = suc (Sched.nextNode sched) }) st ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched)) sched st inv)
    , refl , refl
-- WITH GAS: the inner is subscribed under one more frame, at the same
-- instant, and at ONE MORE j.  Its size hypothesis is valCaps?'s cSize
-- half (sizeᵛ (obs u) IS sizeᵉ), widened by the step; its chain
-- hypothesis is κ's, one frame longer, which is frameStep-chain-suc
subscribeInner-caps {n = n} {Γ = Γ} {t = t} {u = u} c j (gs fuel) op allNid κ id now o
                    sl sched st 2≤S 1≤R slEq slC inv vC pC lC =
  suc j₂ , R1 , R2 , R3
  where
  B      = Caps.cSize (frameStep j c)
  B′     = Caps.cSize (frameStep (suc j) c)
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  κ′     = from-inner op allNid (Sched.nextNode sched) ↠ κ
  szo    : sizeᵉ o ≤ B
  szo    = ≤ᵇ⇒≤ (sizeᵛ (obs u) o) B (T-to (proj₁ (∧-true _ _ vC)))
  -- THE PARKED-WIDTH HALF, and it is already in hand: valCaps?'s width
  -- half is `pWᵛ n sl (obs u) o ≤ cWid`, which IS `outWᵉ o ⊔ dWᵉ o`, so
  -- the dW conjunct subscribeE-caps asks for is the right disjunct
  wdo    : dWᵉ n sl o ≤ Caps.cWid (frameStep j c)
  wdo    = ≤-trans (m≤n⊔m _ (dWᵉ n sl o))
                   (≤ᵇ⇒≤ (pWᵛ n sl (obs u) o) (Caps.cWid (frameStep j c))
                         (T-to (valCaps?-wid (frameStep j c) sl (obs u) o vC)))
  pC′    : pathSz? B′ κ′ ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                        (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                      (pathSz?-⊑ κ step⊑ pC))
  IH     = subscribeE-caps c (suc j) fuel o κ′ id now sl sched₀ st 2≤S 1≤R slEq slC
             (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
                (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                  sched st inv))
             (≤-trans szo (proj₁ step⊑))
             (≤-trans wdo (proj₁ (proj₂ step⊑))) pC′
             (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₂     = proj₁ IH
  SUB    = proj₁ (proj₂ IH)
  BC     = proj₂ (proj₂ IH)
  res    = subscribeE fuel o κ′ id now sched₀ st
  burst  = proj₁ res
  VS     = proj₁ (splitBurst {A = Val Γ t} burst)
  BS     = proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))
  R1 : capsOK? (frameStep (j + suc j₂) c)
                (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true
  R1 = subst (λ x → capsOK? (frameStep x c)
                      (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
             (sym (+-suc j j₂)) SUB
  R2 : all (valCaps? (frameStep (j + suc j₂) c) sl u) VS ≡ true
  R2 = subst (λ x → all (valCaps? (frameStep x c) sl u) VS ≡ true)
             (sym (+-suc j j₂))
             (splitBurst-vals-caps {s = u} {u = t} (frameStep (suc j + j₂) c)
                sl burst BC)
  R3 : all (eventCaps? (frameStep (j + suc j₂) c) sl) BS ≡ true
  R3 = subst (λ x → all (eventCaps? (frameStep x c) sl) BS ≡ true)
             (sym (+-suc j j₂))
             (splitBurst-bk-caps {s = u} {u = t} (frameStep (suc j + j₂) c)
                sl burst)

------------------------------------------------------------------
-- THE SHARED-SLOT PAIR, GROUND — and the second side condition the
-- tree needs.
--
-- REGISTERING COSTS EXACTLY ONE j, and it is the first clause anywhere
-- in the tree that spends a fold on the cReg dimension rather than on
-- cSize or cWid.  The registry gains one entry, so the count conjunct
-- needs one more unit of headroom; frameStep-reg-suc says one j buys
-- `cReg c * cSize c` of it — which is at least one exactly when the cap
-- admits a registration at all.
--
-- SO THE REGISTERING COMPANIONS CARRY `1 ≤ Caps.cReg c`, alongside
-- `2 ≤ Caps.cSize c`, and it is not decoration either: at cReg c = 0 the
-- statement is FALSE, since cReg (frameStep j c) is `0 * suc (j * S)` =
-- 0 at every j and a registry of length one cannot fit under it.  It is
-- threaded UNCHANGED (c never moves inside a frame) and is supplied at
-- the top by 1≤capsAt-reg below, which the recurrence proves rather than
-- assumes — the same discipline 2≤capsAt-size already follows.  The
-- delivery clique never registers, so it does not carry it.
------------------------------------------------------------------

register-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  capsOK? (frameStep (suc j) c) sched (register src κ st) ≡ true
register-caps {u = u} c j src κ sched st 2≤S 1≤R inv pC =
    ∧-intro h0
    (∧-intro (all-++-intro (λ en → pathSz? (Caps.cSize (frameStep (suc j) c))
                                     (proj₂ (proj₂ (proj₂ en))))
                (EvalSt.registry st) ((EvalSt.nextReg st , src , u , κ) ∷ [])
                h1 (∧-intro (pathSz?-⊑ κ (frameStep-mono-j c 2≤S (n≤1+n j)) pC) refl))
    (∧-intro h2
    (∧-intro h3 COUNT)))
  where
  inv′ = capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st
           (frameStep-mono-j c 2≤S (n≤1+n j)) inv
  P    = capsOK?-parts (frameStep (suc j) c) sched st inv′
  h0   = proj₁ P
  h1   = proj₁ (proj₂ P)
  h2   = proj₁ (proj₂ (proj₂ P))
  h3   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  1≤RS : 1 ≤ Caps.cReg c * Caps.cSize c
  1≤RS = ≤-trans (≤-reflexive refl) (*-mono-≤ 1≤R (≤-trans (s≤s z≤n) 2≤S))
  COUNT : (length (EvalSt.registry st ++ (EvalSt.nextReg st , src , u , κ) ∷ [])
             ≤ᵇ Caps.cReg (frameStep (suc j) c)) ≡ true
  COUNT = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (≤-reflexive (length-++ (EvalSt.registry st)))
      (≤-trans (+-mono-≤ (capsOK?-count (frameStep j c) sched st inv) 1≤RS)
               (≤-reflexive (frameStep-reg-suc c j)))))

-- a share's connect burst is re-kinded on the way up, and eventCaps?
-- does not read the kind
sharedPlumb-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (sl : Slots Γ)
  (str : Stream Γ u) →
  burstCaps? c sl str ≡ true → burstCaps? c sl (sharedPlumb str) ≡ true
sharedPlumb-caps c sl []         h = refl
sharedPlumb-caps c sl (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-caps c sl ems (proj₂ (∧-true _ _ h)))

-- dropping a source's registrations without sweeping the live set: the
-- registry shrinks and nothing else moves
dropOnly-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { registry = dropSource src (EvalSt.registry st) })
    ≡ true
dropOnly-caps c src sched st inv =
    ∧-intro h0
    (∧-intro (dropSource-all (λ en → pathSz? (Caps.cSize c)
                                       (proj₂ (proj₂ (proj₂ en))))
                src (EvalSt.registry st) h1)
    (∧-intro h2
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (dropSource-len src (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- `j + 1` and `j + suc k` against the shapes register-caps and
-- subscribeE-caps hand back
j+1 : ∀ (j : ℕ) → j + 1 ≡ suc j
j+1 j = trans (+-suc j 0) (cong suc (+-identityʳ j))

-- THE CONNECT.  One registration for the joining subscriber, then the
-- def is subscribed under `share-sink i` — a chain of LENGTH ZERO, so
-- its own chain hypothesis is `1 ≤ cSize` and nothing else has to be
-- found for it.  That is why this edge composed even under the old
-- joint bound, and it composes unchanged under the separate pair
sharedConnect-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl d ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
-- OUT OF GAS: a dry close and nothing else
sharedConnect-caps {Γ = Γ} c j g0 i d κ id now sl sched st 2≤S 1≤R slEq slC inv szd wdd pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (dryBurst {A = Val Γ (lookup Γ i)} id) ≡ true)
            (sym (+-identityʳ j)) refl
sharedConnect-caps {Γ = Γ} c j (gs fuel′) i d κ id now sl sched st
                   2≤S 1≤R slEq slC inv szd wdd pC lC
  with burstCompleted (proj₁ (subscribeE fuel′ d (share-sink i) id now sched
                               (register (toℕ i) κ
                                 (record st { connectedShares =
                                                toℕ i ∷ EvalSt.connectedShares st }))))
... | true  =
  suc j₂ , subst (λ x → capsOK? (frameStep x c) sched₁ DROP ≡ true) (sym (+-suc j j₂))
             (dropOnly-caps (frameStep (suc (j + j₂)) c) (toℕ i) sched₁
                (record st₂ { completedSources = toℕ i ∷ EvalSt.completedSources st₂ })
                SUB)
          , subst (λ x → burstCaps? (frameStep x c) sl
                           (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                              at id from toℕ i as subscribe) ∷ sharedPlumb burst)
                             ≡ true)
                  (sym (+-suc j j₂))
                  (∧-intro refl (sharedPlumb-caps (frameStep (suc (j + j₂)) c) sl burst BC))
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S))
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₂ (proj₂ IH)
  res = subscribeE fuel′ d (share-sink i) id now sched st₁
  burst = proj₁ res
  sched₁ = proj₁ (proj₂ res)
  st₂ = proj₂ (proj₂ res)
  DROP = record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                    ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
... | false =
  suc j₂ , subst (λ x → capsOK? (frameStep x c) sched₁ st₂ ≡ true) (sym (+-suc j j₂)) SUB
          , subst (λ x → burstCaps? (frameStep x c) sl
                           (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                              ∷ sharedPlumb burst) ≡ true)
                  (sym (+-suc j j₂))
                  (∧-intro refl (sharedPlumb-caps (frameStep (suc (j + j₂)) c) sl burst BC))
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S))
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₂ (proj₂ IH)
  res = subscribeE fuel′ d (share-sink i) id now sched st₁
  burst = proj₁ res
  sched₁ = proj₁ (proj₂ res)
  st₂ = proj₂ (proj₂ res)

-- THE JOIN.  A spent share answers with a one-shot close, a live one
-- registers (one j), and an unconnected one connects
sharedSlot-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl d ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
sharedSlot-caps {Γ = Γ} c j g i d κ id now sl sched st 2≤S 1≤R slEq slC inv szd wdd pC lC
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                        at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (+-identityʳ j)) refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
...   | false = sharedConnect-caps c j g i d κ id now sl sched st
                  2≤S 1≤R slEq slC inv szd wdd pC lC

------------------------------------------------------------------
-- GRINDING stepFrame-caps, THE CLAUSE THAT PAYS A j.
--
-- Five clauses, and they split cleanly in two.  THREE ARE STRUCTURAL —
-- take-f is a filter on the payload list plus a registry cut, from-inner
-- and thru-outer delegate to innerFinish-caps and thruWalk-caps and then
-- do node bookkeeping — so they spend no folds at all and are ground
-- here.  TWO ARE ARITHMETIC: map-f and scan-f are the sites where a
-- value is actually built, by `applyFn`, and what they cost is the
-- subject of stepFrame-value-caps below.
--
-- The leaves first, in the order the clauses consume them.
------------------------------------------------------------------

-- setNode's caps face.  Measures has the size half (setNode-bounded);
-- this is the width half, the same three-line induction
setNode-widNode : ∀ {n} {Γ : Ctx n} (W : ℕ) (sl : Slots Γ)
  (nid : NodeId) (ns : NodeState Γ) (nodes : List (NodeId × NodeState Γ)) →
  widNode W sl ns ≡ true →
  all (λ kv → widNode W sl (proj₂ kv)) nodes ≡ true →
  all (λ kv → widNode W sl (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-widNode W sl nid ns []             bn h = ∧-intro bn refl
setNode-widNode W sl nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-widNode W sl nid ns r bn (proj₂ (∧-true _ _ h)))

-- so installing one bounded node keeps all five conjuncts: the registry,
-- the live set and the slot telescope are untouched
capsOK?-setNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedNode (Caps.cSize c) ns ≡ true →
  widNode (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { nodes = setNode nid ns (EvalSt.nodes st) }) ≡ true
capsOK?-setNode {Γ = Γ} c nid ns sched st bn wn inv =
    ∧-intro (∧-intro (proj₁ hL)
                     (setNode-bounded (Caps.cSize c) nid ns (EvalSt.nodes st) bn
                        (proj₂ hL)))
    (∧-intro h1
    (∧-intro h2
    (∧-intro (setNode-widNode (Caps.cWid c) (Sched.slots sched) nid ns
                (EvalSt.nodes st) wn h3)
             h4)))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- take's cut is dropSweep's sibling: cutThrough is a filter on the
-- registry (by node membership rather than by source), its closes carry
-- no payload, and the live set is swept against what it kept
cutThrough-regsSz : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsSz? B reg ≡ true → regsSz? B (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regsSz B nid d wm dy []                    h = refl
cutThrough-regsSz B nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regsSz B nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | _ | ih = ih
... | false | _ | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closes-caps : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (sl : Slots Γ)
  (nid : NodeId) (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventCaps? c sl) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closes-caps c sl nid d wm dy []                     = refl
cutThrough-closes-caps c sl nid d wm dy ((rid , src , ch) ∷ r)
  with pathHasNode nid (proj₂ ch) | cutThrough nid d wm dy r
     | cutThrough-closes-caps c sl nid d wm dy r
... | false | _ | ih = ih
... | true  | _ | ih with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

-- the cut's whole state move, in one lemma: registry filtered, live
-- swept against the survivors, and one node overwritten
cutSweep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (ns : NodeState Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedNode (Caps.cSize c) ns ≡ true →
  widNode (Caps.cWid c) (Sched.slots sched) ns ≡ true →
  capsOK? c sched st ≡ true →
  let kept = proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                               (EvalSt.dying st) (EvalSt.registry st))
  in capsOK? c (record sched { live = sweepLive kept (Sched.live sched) })
               (record st { registry  = kept
                          ; cancelled = proj₂ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                                       (EvalSt.regWatermark st)
                                                       (EvalSt.dying st)
                                                       (EvalSt.registry st)))
                                        ++ EvalSt.cancelled st
                          ; nodes     = setNode nid ns (EvalSt.nodes st) }) ≡ true
cutSweep-caps {Γ = Γ} c nid ns sched st bn wn inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ hL))
                     (setNode-bounded (Caps.cSize c) nid ns (EvalSt.nodes st) bn
                        (proj₂ hL)))
    (∧-intro (cutThrough-regsSz (Caps.cSize c) nid (EvalSt.delivered st)
                (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro (setNode-widNode (Caps.cWid c) (Sched.slots sched) nid ns
                (EvalSt.nodes st) wn h3)
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (cutThrough-len nid (EvalSt.delivered st)
                                          (EvalSt.regWatermark st) (EvalSt.dying st)
                                          (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = proj₁ (cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                           (EvalSt.dying st) (EvalSt.registry st))
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- take passes a PREFIX of what it was given, so its payload bound is
-- inherited rather than paid for
takeVals-caps : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (k : ℕ) (vals : List (Val Γ s)) →
  all (valCaps? c sl s) vals ≡ true →
  all (valCaps? c sl s) (proj₁ (takeVals k vals)) ≡ true
takeVals-caps c sl zero          vals      h = refl
takeVals-caps c sl (suc k)       []        h = refl
takeVals-caps c sl (suc zero)    (v ∷ vs)  h = ∧-intro (proj₁ (∧-true _ _ h)) refl
takeVals-caps c sl (suc (suc k)) (v ∷ vs)  h =
  ∧-intro (proj₁ (∧-true _ _ h))
          (takeVals-caps c sl (suc k) vs (proj₂ (∧-true _ _ h)))

-- THE take-f CLAUSE, and it spends no folds: j′ = 0 either way
takeDispatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) (mns : Maybe (NodeState Γ)) →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  all (valCaps? c sl s) vals ≡ true →
  let r = takeDispatch {t = t} nid vals fin sched st mns
  in (capsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
        ≡ true)
     × (all (valCaps? c sl s) (proj₁ r) ≡ true)
     × (all (eventCaps? c sl) (proj₁ (proj₂ r)) ≡ true)
takeDispatch-caps c nid vals fin sl sched st (just (take-st k)) slEq inv vC
  with proj₂ (proj₂ (takeVals k vals))
... | true  = cutSweep-caps c nid (take-st zero) sched st refl refl inv
            , takeVals-caps c sl k vals vC
            , subst (λ x → all (eventCaps? c x)
                             (proj₁ (proj₂ (cutThrough nid (EvalSt.delivered st)
                                              (EvalSt.regWatermark st) (EvalSt.dying st)
                                              (EvalSt.registry st)))) ≡ true)
                    slEq
                    (cutThrough-closes-caps c (Sched.slots sched) nid
                       (EvalSt.delivered st) (EvalSt.regWatermark st)
                       (EvalSt.dying st) (EvalSt.registry st))
... | false = capsOK?-setNode c nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                sched st refl refl inv
            , takeVals-caps c sl k vals vC
            , refl
takeDispatch-caps c nid vals fin sl sched st nothing slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (scan-st _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (merge-st _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (concat-st _ _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (switch-st _ _)) slEq inv vC = inv , refl , refl
takeDispatch-caps c nid vals fin sl sched st (just (exhaust-st _ _)) slEq inv vC = inv , refl , refl

-- reading a node back out at the caps, so a clause that REINSTALLS one
-- (thruWrap sets only the `done` flag) can show the payload it keeps is
-- still bounded.  Mirrors Wet's lookupNode-B
NodeCaps : ∀ {n} {Γ : Ctx n} → Caps → Slots Γ → Maybe (NodeState Γ) → Set
NodeCaps c sl nothing   = ⊤
NodeCaps c sl (just ns) =
  (boundedNode (Caps.cSize c) ns ≡ true) × (widNode (Caps.cWid c) sl ns ≡ true)

lookupNode-caps : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) nodes ≡ true →
  all (λ kv → widNode (Caps.cWid c) sl (proj₂ kv)) nodes ≡ true →
  NodeCaps c sl (lookupNode nid nodes)
lookupNode-caps c sl nid []            hb hw = tt
lookupNode-caps c sl nid ((k , s) ∷ r) hb hw with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ hb) , proj₁ (∧-true _ _ hw)
... | false = lookupNode-caps c sl nid r (proj₂ (∧-true _ _ hb)) (proj₂ (∧-true _ _ hw))

-- the two projections of capsOK? the node ring needs
capsOK?-nodeSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st) ≡ true
capsOK?-nodeSz {Γ = Γ} c sched st h =
  proj₂ (∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
                (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
                (proj₁ (capsOK?-parts c sched st h)))

capsOK?-nodeWid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  all (λ kv → widNode (Caps.cWid c) (Sched.slots sched) (proj₂ kv))
      (EvalSt.nodes st) ≡ true
capsOK?-nodeWid c sched st h = proj₁ (proj₂ (proj₂ (proj₂ (capsOK?-parts c sched st h))))

-- THE thru-outer WRAP: the walk has already run, and all this does is
-- stamp `done` on the node it found, keeping that node's payload.  No
-- values are built, so no folds are spent
thruWrap-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (op : AllOp) (nid : NodeId) (fin : Bool) (sl : Slots Γ)
  (out : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  capsOK? c (proj₁ (proj₂ (proj₂ out))) (proj₂ (proj₂ (proj₂ out))) ≡ true →
  all (valCaps? c sl u) (proj₁ out) ≡ true →
  all (eventCaps? c sl) (proj₁ (proj₂ out)) ≡ true →
  let r = thruWrap op nid fin out
  in (capsOK? c (proj₁ (proj₂ (proj₂ (proj₂ r))))
                (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valCaps? c sl u) (proj₁ r) ≡ true)
     × (all (eventCaps? c sl) (proj₁ (proj₂ r)) ≡ true)
thruWrap-caps c op nid false sl (vs , bs , sd , st) inv vC eC = inv , vC , eC
thruWrap-caps c mergeᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps c (Sched.slots sd) nid (EvalSt.nodes st)
         (capsOK?-nodeSz c sd st inv) (capsOK?-nodeWid c sd st inv)
... | just (merge-st k od) | (bn , wn) =
      capsOK?-setNode c nid (merge-st k true) sd st refl refl inv , vC , eC
... | nothing              | _ = inv , vC , eC
... | just (scan-st _)     | _ = inv , vC , eC
... | just (take-st _)     | _ = inv , vC , eC
... | just (concat-st _ _ _) | _ = inv , vC , eC
... | just (switch-st _ _) | _ = inv , vC , eC
... | just (exhaust-st _ _) | _ = inv , vC , eC
thruWrap-caps c concatᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps c (Sched.slots sd) nid (EvalSt.nodes st)
         (capsOK?-nodeSz c sd st inv) (capsOK?-nodeWid c sd st inv)
... | just (concat-st q act od) | (bn , wn) =
      capsOK?-setNode c nid (concat-st q act true) sd st bn wn inv , vC , eC
... | nothing              | _ = inv , vC , eC
... | just (scan-st _)     | _ = inv , vC , eC
... | just (take-st _)     | _ = inv , vC , eC
... | just (merge-st _ _)  | _ = inv , vC , eC
... | just (switch-st _ _) | _ = inv , vC , eC
... | just (exhaust-st _ _) | _ = inv , vC , eC
thruWrap-caps c switchᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) =
      capsOK?-setNode c nid (switch-st cur true) sd st refl refl inv , vC , eC
... | nothing              = inv , vC , eC
... | just (scan-st _)     = inv , vC , eC
... | just (take-st _)     = inv , vC , eC
... | just (merge-st _ _)  = inv , vC , eC
... | just (concat-st _ _ _) = inv , vC , eC
... | just (exhaust-st _ _) = inv , vC , eC
thruWrap-caps c exhaustᵒ nid true sl (vs , bs , sd , st) inv vC eC
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act od) =
      capsOK?-setNode c nid (exhaust-st act true) sd st refl refl inv , vC , eC
... | nothing              = inv , vC , eC
... | just (scan-st _)     = inv , vC , eC
... | just (take-st _)     = inv , vC , eC
... | just (merge-st _ _)  = inv , vC , eC
... | just (concat-st _ _ _) = inv , vC , eC
... | just (switch-st _ _) = inv , vC , eC

------------------------------------------------------------------
-- THE *All OUTER EDGE, GROUND: thruConsume-caps and thruWalk-caps.
--
-- These are the two companions the joint bound blocked.  thruConsume
-- was always provable — its hypotheses are subscribeInner-caps's
-- verbatim — and what its CALLER owed it was a joint bound it did not
-- have.  Under the separate pair the two line up exactly: thruWalk
-- carries `suc (pathLen κ) ≤ cSize` and hands that same conjunct down,
-- per payload, unchanged.
--
-- The per-op node bookkeeping stores nothing the caps do not already
-- bound: merge's counter and switch's current-inner carry no payload,
-- exhaust's flag none either, and concatAll's queue stores the payload
-- VERBATIM — so its bound is the valCaps? already in hand, appended to
-- the queue's own by all-++-intro.  switchAll's cut is the only clause
-- that moves the registry, and it is cutSweep-caps without the node.
------------------------------------------------------------------

-- merge's counter is a node both bounds accept unconditionally, so
-- bumping it is a setNode of something already bounded
capsOK?-mergeBump : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (nid : NodeId) (done : Bool) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (record st { nodes = mergeBump nid done (EvalSt.nodes st) }) ≡ true
capsOK?-mergeBump c nid done sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od) =
      capsOK?-setNode c nid (merge-st (if done then k else suc k) od) sched st
        refl refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

-- switchAll's cut: registry filtered, live swept against the survivors,
-- the cancelled ledger grown — and capsOK? reads none of the last
switchKill-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  let r = switchKill {t = t} cur sched st
  in capsOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
switchKill-caps c nothing  sched st inv = inv
switchKill-caps {Γ = Γ} c (just v) sched st inv =
    ∧-intro (∧-intro (sweepLive-all (boundedLive (Caps.cSize c)) kept
                        (Sched.live sched) (proj₁ hL))
                     (proj₂ hL))
    (∧-intro (cutThrough-regsSz (Caps.cSize c) v (EvalSt.delivered st)
                (EvalSt.regWatermark st) (EvalSt.dying st) (EvalSt.registry st) h1)
    (∧-intro (sweepLive-all (widLive (Caps.cWid c) (Sched.slots sched)) kept
                (Sched.live sched) h2)
    (∧-intro h3
             (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (cutThrough-len v (EvalSt.delivered st)
                                          (EvalSt.regWatermark st) (EvalSt.dying st)
                                          (EvalSt.registry st))
                                       (≤ᵇ⇒≤ _ _ (T-to h4))))))))
  where
  kept = proj₁ (cutThrough v (EvalSt.delivered st) (EvalSt.regWatermark st)
                           (EvalSt.dying st) (EvalSt.registry st))
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- the cut's closes carry no payload
switchKill-closes-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sl : Slots Γ) (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  all (eventCaps? c sl) (proj₁ (switchKill {t = t} {e = e} cur sched st)) ≡ true
switchKill-closes-caps c sl nothing  sched st = refl
switchKill-closes-caps c sl (just v) sched st =
  cutThrough-closes-caps c sl v (EvalSt.delivered st) (EvalSt.regWatermark st)
    (EvalSt.dying st) (EvalSt.registry st)

thruConsume-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = thruConsume g op nid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MERGE: subscribe, then bump the active-inner counter
thruConsume-caps c j g mergeᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC inv vC pC lC =
  j′ , capsOK?-mergeBump (frameStep (j + j′) c) nid
         (proj₁ (proj₂ (proj₂ (proj₂ R))))
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₂ (proj₂ (proj₂ SI))
  where
  SI = subscribeInner-caps c j g mergeᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC inv vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g mergeᵒ nid κ id now o sched st

-- CONCAT: park the payload if an inner is running, otherwise subscribe
-- it and reinstall an empty queue
thruConsume-caps {n = n} {u = u} c j g concatᵒ nid κ id now o sl sched st
                 2≤S 1≤R slEq slC inv vC pC lC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing                | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (merge-st _ _)    | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st _ _)   | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st _ _)  | _ = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (concat-st {w} q false od) | (bn , wn) =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid (concat-st {t = u} [] (not done) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₂ (proj₂ (proj₂ SI))
  where
  SI = subscribeInner-caps c j g concatᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC inv vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g concatᵒ nid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ R)))
... | just (concat-st {w} q true od) | (bn , wn) with w ≟ᵗ u
...   | no _ = 0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
                         (sym (+-identityʳ j)) inv
             , refl , refl
...   | yes refl =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode nid (concat-st (q ++ o ∷ []) true od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) nid (concat-st (q ++ o ∷ []) true od)
               sched st BN WN inv)
    , refl , refl
  where
  BN = all-++-intro (λ x → sizeᵉ x ≤ᵇ Caps.cSize (frameStep j c)) q (o ∷ [])
         bn (∧-intro (valCaps?-size (frameStep j c) sl (obs u) o vC) refl)
  WN = all-++-intro (λ x → pWᵉ n (Sched.slots sched) x ≤ᵇ Caps.cWid (frameStep j c))
         q (o ∷ []) wn
         (∧-intro (subst (λ y → (pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                         (sym slEq) (valCaps?-wid (frameStep j c) sl (obs u) o vC))
                  refl)

-- SWITCH: cut the outgoing inner, subscribe the new one, record it
thruConsume-caps c j g switchᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC inv vC pC lC
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (merge-st _ _)    = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (concat-st _ _ _) = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st _ _)  = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st cur od) =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ R))) then nothing
                     else just (proj₁ R)) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , all-++-intro (eventCaps? (frameStep (j + j′) c) sl)
         (proj₁ KILL) _
         (switchKill-closes-caps (frameStep (j + j′) c) sl cur sched st)
         (proj₂ (proj₂ (proj₂ SI)))
  where
  KILL = switchKill cur sched st
  sched₁ = proj₁ (proj₂ KILL)
  st₁    = proj₂ (proj₂ KILL)
  SI = subscribeInner-caps c j g switchᵒ nid κ id now o sl sched₁ st₁
         2≤S 1≤R (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq) slC
         (switchKill-caps (frameStep j c) cur sched st inv) vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g switchᵒ nid κ id now o sched₁ st₁

-- EXHAUST: drop while busy, otherwise subscribe and latch
thruConsume-caps c j g exhaustᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC inv vC pC lC
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (merge-st _ _)    = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (concat-st _ _ _) = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st _ _)   = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st true od)  = 0 , ZI , refl , refl
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st false od) =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ R))))) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₂ (proj₂ (proj₂ SI))
  where
  SI = subscribeInner-caps c j g exhaustᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC inv vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g exhaustᵒ nid κ id now o sched st

-- THE WALK: one payload at a time, receipts adding exactly as the
-- delivery clique's do
thruWalk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  all (valCaps? (frameStep j c) sl (obs u)) vals ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = thruWalk g op nid κ id now vals sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
thruWalk-caps c j g op nid κ id now [] sl sched st 2≤S 1≤R slEq slC inv pC vC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl
thruWalk-caps {u = u} c j g op nid κ id now (o ∷ os) sl sched st
              2≤S 1≤R slEq slC inv pC vC lC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂
        (proj₁ (proj₂ (proj₂ REST))) (proj₂ (proj₂ (proj₂ REST)))
        (proj₁ (proj₂ IH))
    , subst (λ x → all (valCaps? (frameStep x c) sl u)
                     (proj₁ TC ++ proj₁ REST) ≡ true) (+-assoc j j₁ j₂)
        (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl u)
           (proj₁ TC) (proj₁ REST)
           (valsCaps?-widen sl u (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
              (proj₁ (proj₂ (proj₂ HD))))
           (proj₁ (proj₂ (proj₂ IH))))
    , subst (λ x → all (eventCaps? (frameStep x c) sl)
                     (proj₁ (proj₂ TC) ++ proj₁ (proj₂ REST)) ≡ true) (+-assoc j j₁ j₂)
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl (proj₁ (proj₂ TC))
              (frameStep-⊑-+ c 2≤S (j + j₁) j₂) (proj₂ (proj₂ (proj₂ HD))))
           (proj₂ (proj₂ (proj₂ IH))))
  where
  HD  = thruConsume-caps c j g op nid κ id now o sl sched st
          2≤S 1≤R slEq slC inv (proj₁ (∧-true _ _ vC)) pC lC
  j₁  = proj₁ HD
  TC  = thruConsume g op nid κ id now o sched st
  sd₁ = proj₁ (proj₂ (proj₂ TC))
  st₁ = proj₂ (proj₂ (proj₂ TC))
  IH  = thruWalk-caps c (j + j₁) g op nid κ id now os sl sd₁ st₁
          2≤S 1≤R
          (trans (KeepsC.slotsEq (thruConsume-keeps g op nid κ id now o sched st))
                 slEq)
          slC (proj₁ (proj₂ HD))
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
          (valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)
             (proj₂ (∧-true _ _ vC)))
          (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
  j₂   = proj₁ IH
  REST = thruWalk g op nid κ id now os sd₁ st₁

------------------------------------------------------------------
-- concatAll's DRAIN and the *All FINISH, ground.  The queue is the one
-- node whose stored observables the size conjunct bounds directly —
-- `obsCaps?` IS `valCaps? … (obs s)`, definitionally — so the residue
-- goes back into the node with the bound it came out with, and the
-- drain's receipts add exactly as thruWalk's do.
------------------------------------------------------------------

-- the queue's two halves, as boundedNode and widNode read them
obsList-nodeSz : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (obsCaps? c sl) q ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q ≡ true
obsList-nodeSz c sl []      h = refl
obsList-nodeSz {n = n} c sl (o ∷ q) h
  with ∧-true (obsCaps? c sl o) (all (obsCaps? c sl) q) h
... | h1 , h2 =
  ∧-intro (proj₁ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize c)
                         (pWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeSz c sl q h2)

-- and back again, which is how the drained residue re-enters the node
obsList-intro : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q ≡ true →
  all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true →
  all (obsCaps? c sl) q ≡ true
obsList-intro c sl []      hsz hwd = refl
obsList-intro {n = n} c sl (x ∷ q) hsz hwd
  with ∧-true (sizeᵉ x ≤ᵇ Caps.cSize c)
              (all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q) hsz
     | ∧-true (pWᵉ n sl x ≤ᵇ Caps.cWid c)
              (all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q) hwd
... | s1 , s2 | w1 , w2 = ∧-intro (∧-intro s1 w1) (obsList-intro c sl q s2 w2)

obsList-nodeWid : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (obsCaps? c sl) q ≡ true →
  all (λ o → pWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true
obsList-nodeWid c sl []      h = refl
obsList-nodeWid {n = n} c sl (o ∷ q) h
  with ∧-true (obsCaps? c sl o) (all (obsCaps? c sl) q) h
... | h1 , h2 =
  ∧-intro (proj₂ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize c)
                         (pWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeWid c sl q h2)

concatDrain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  all (obsCaps? (frameStep j c) sl) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl s)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (obsCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
concatDrain-caps c j g allNid κ id now [] sl sched st 2≤S 1≤R slEq slC inv pC lC qC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl , refl
concatDrain-caps {s = s} c j g allNid κ id now (o ∷ q) sl sched st
                 2≤S 1≤R slEq slC inv pC lC qC
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-caps c j g concatᵒ allNid κ id now o sl sched st
         2≤S 1≤R slEq slC inv (proj₁ (∧-true _ _ qC)) pC lC
     | KeepsC.slotsEq (subscribeInner-keeps g concatᵒ allNid κ id now o sched st)
-- the inner stays open: it becomes the active one and the rest of the
-- queue is parked, still bounded
... | (inst , vs , bs , false , sched₁ , st₁) | (j₁ , SUB , VC , EC) | sEq =
  j₁ , SUB , VC , EC
     , obsListCaps?-widen sl q (frameStep-⊑-+ c 2≤S j j₁) (proj₂ (∧-true _ _ qC))
-- the inner completed synchronously: drain on, and the two receipts add
... | (inst , vs , bs , true , sched₁ , st₁) | (j₁ , SUB , VC , EC) | sEq =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂
        (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ REST)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ REST)))))
        (proj₁ (proj₂ IH))
    , subst (λ x → all (valCaps? (frameStep x c) sl s) (vs ++ proj₁ REST) ≡ true)
            (+-assoc j j₁ j₂)
            (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl s) vs (proj₁ REST)
               (valsCaps?-widen sl s vs (frameStep-⊑-+ c 2≤S (j + j₁) j₂) VC)
               (proj₁ (proj₂ (proj₂ IH))))
    , subst (λ x → all (eventCaps? (frameStep x c) sl)
                     (bs ++ proj₁ (proj₂ REST)) ≡ true)
            (+-assoc j j₁ j₂)
            (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl) bs
               (proj₁ (proj₂ REST))
               (eventsCaps?-widen sl bs (frameStep-⊑-+ c 2≤S (j + j₁) j₂) EC)
               (proj₁ (proj₂ (proj₂ (proj₂ IH)))))
    , subst (λ x → all (obsCaps? (frameStep x c) sl)
                     (proj₁ (proj₂ (proj₂ (proj₂ REST)))) ≡ true)
            (+-assoc j j₁ j₂)
            (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  where
  IH   = concatDrain-caps c (j + j₁) g allNid κ id now q sl sched₁ st₁
           2≤S 1≤R (trans sEq slEq) slC SUB
           (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
           (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
           (obsListCaps?-widen sl q (frameStep-⊑-+ c 2≤S j j₁)
              (proj₂ (∧-true _ _ qC)))
  j₂   = proj₁ IH
  REST = concatDrain g allNid κ id now q sched₁ st₁

-- the clauses of innerFinish that neither emit nor step: a mistyped or
-- missing node, and every op/node pair the evaluator's catch-all covers
innerFinish-zero : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl s) vals ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) []
          ≡ true)
innerFinish-zero c j sl vals sched st inv vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

innerFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl s)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MERGE: decrement the active-inner counter, which carries no payload
innerFinish-caps c j g mergeᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od) =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (merge-st (pred k) od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (merge-st (pred k) od)
               sched st refl refl inv)
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
... | nothing                = innerFinish-zero c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero c j sl vals sched st inv vC
... | just (switch-st _ _)   = innerFinish-zero c j sl vals sched st inv vC
... | just (exhaust-st _ _)  = innerFinish-zero c j sl vals sched st inv vC

-- CONCAT: drain the queue and reinstall the residue, which comes back
-- from concatDrain-caps with the very bound the node needs
innerFinish-caps {n = n} {s = s} c j g concatᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) allNid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing              | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (scan-st _)     | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (take-st _)     | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (merge-st _ _)  | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (switch-st _ _) | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (exhaust-st _ _) | _ = innerFinish-zero c j sl vals sched st inv vC
... | just (concat-st {w} q act od) | (bn , wn) with w ≟ᵗ s
...   | no _     = innerFinish-zero c j sl vals sched st inv vC
...   | yes refl =
  j′ , capsOK?-setNode (frameStep (j + j′) c) allNid
         (concat-st (proj₁ (proj₂ (proj₂ (proj₂ DR)))) (proj₁ (proj₂ (proj₂ DR))) od)
         sd₁ st₁
         (obsList-nodeSz (frameStep (j + j′) c) sl
            (proj₁ (proj₂ (proj₂ (proj₂ DR)))) RES)
         (subst (λ y → all (λ x → pWᵉ n y x ≤ᵇ Caps.cWid (frameStep (j + j′) c))
                         (proj₁ (proj₂ (proj₂ (proj₂ DR)))) ≡ true)
                (sym (trans (KeepsC.slotsEq
                              (concatDrain-keeps g allNid κ id now q sched st)) slEq))
                (obsList-nodeWid (frameStep (j + j′) c) sl
                   (proj₁ (proj₂ (proj₂ (proj₂ DR)))) RES))
         (proj₁ (proj₂ CD))
     , all-++-intro (valCaps? (frameStep (j + j′) c) sl s) vals (proj₁ DR)
         (valsCaps?-widen sl s vals (frameStep-⊑-+ c 2≤S j j′) vC)
         (proj₁ (proj₂ (proj₂ CD)))
     , proj₁ (proj₂ (proj₂ (proj₂ CD)))
  where
  CD  = concatDrain-caps c j g allNid κ id now q sl sched st
          2≤S 1≤R slEq slC inv pC lC
          (obsList-intro (frameStep j c) sl q bn
             (subst (λ y → all (λ o → pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) q
                             ≡ true)
                    slEq wn))
  j′  = proj₁ CD
  RES = proj₂ (proj₂ (proj₂ (proj₂ CD)))
  DR  = concatDrain g allNid κ id now q sched st
  sd₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR))))

-- SWITCH: clear the current-inner slot if this was it
innerFinish-caps c j g switchᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (merge-st _ _)    = innerFinish-zero c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero c j sl vals sched st inv vC
... | just (exhaust-st _ _)  = innerFinish-zero c j sl vals sched st inv vC
... | just (switch-st nothing od) = innerFinish-zero c j sl vals sched st inv vC
... | just (switch-st (just cur) od) with cur ≡ᵇ inst
...   | false = innerFinish-zero c j sl vals sched st inv vC
...   | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (switch-st nothing od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (switch-st nothing od)
               sched st refl refl inv)
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

-- EXHAUST: clear the busy flag
innerFinish-caps c j g exhaustᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero c j sl vals sched st inv vC
... | just (merge-st _ _)    = innerFinish-zero c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero c j sl vals sched st inv vC
... | just (switch-st _ _)   = innerFinish-zero c j sl vals sched st inv vC
... | just (exhaust-st act od) =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (exhaust-st false od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (exhaust-st false od)
               sched st refl refl inv)
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

------------------------------------------------------------------
-- THE SLOT EDGE, GROUND: subscribeE-input-caps, and both of the two
-- blockages that stopped it are gone.
--
-- Its four branches:
--
--   scripted (hot _)   A spent script answers with a
--                      one-shot close; a live one registers, which is
--                      register-caps and one j.  Needs nothing new.
--   shared d           needs `sizeᵉ d ≤ cSize` for sharedSlot-caps.
--   scripted (cold …)  oneShotBurst carries the slot's own sync
--                      values, and the async tail becomes a LiveSource
--                      whose pendings capsOK? bounds by cSize and
--                      cWid.  Both are slot data.
--
-- BLOCKAGE 1 — THE JOINT BOUND — IS RESOLVED, by the design ruling of
-- 2026-07-31, and the evidence is Joint-Probe.  What blocked here (and
-- at thruWalk / concatDrain / innerFinish) was that subscribeE-caps
-- demanded `pathLen κ + sizeᵉ b ≤ cSize` while the delivery side
-- carries the two bounds SEPARATELY.  The natural-looking repair —
-- thread round 3's ℓ ledger through the delivery clique too — was
-- gated first, and the gate came back negative: Joint-Probe measures
-- the joint sum against the TIGHT admissible cSize on seventeen
-- families and it is violated on every one, at adm + 1 EXACTLY on
-- every family carrying a scan.  A subscribed payload that IS the
-- stored accumulator already attains the cap by itself, so any chain
-- on top overshoots and no constant slackening of the ledger survives.
-- So the JOINT FORM went, not the delivery side: subscribeE-caps now
-- asks for `suc (pathLen κ) ≤ cSize` and `sizeᵉ b ≤ cSize` separately,
-- which is exactly what foldPath-caps already splits out of pathSz?.
-- The induction still closes because each *All hop PAYS ONE j for the
-- from-inner frame it adds, and one j at least doubles cSize
-- (frameStep-chain-suc), so a +1 chain extension is absorbed with
-- room.  The extra receipt rides in the same sum the fold receipts do.
--
-- BLOCKAGE 2 — `c` NOT TIED TO `sl` — IS REPAIRED AT THE TELESCOPE.
-- capsAt's base is `2 + sizeᵉ e + slotsSize sl`, so the connection
-- exists at the top and used to be thrown away by the time a companion
-- was stated at an abstract `c`: nothing bounded a slot def or a
-- scripted value, since `d` is `Sched.slots sched i` and capsOK? never
-- mentions slotsSize.  `slotsCaps? (Caps.cSize c) sl` is that
-- connection as a decidable side condition, threaded unchanged through
-- the whole tree exactly as `2 ≤ Caps.cSize c` and `1 ≤ Caps.cReg c`
-- are (slots never change, so it is a constant), and supplied by
-- slotsCaps?-capsAt.  What is left here is the CLAUSE: the shared
-- branch reads its `d` out of it, and the cold branch its sync values
-- and async pendings.
--
-- AND THE WIDTH HALF IS FREE, which is why slotsCaps? carries sizes
-- only.  A scripted slot's element type is DATA — the `ok` proof the
-- `scripted` constructor carries is exactly `T (isData t)` — and pWᵛ
-- is identically zero on a data type, since only its `obs` clause reads
-- a width at all.  So a scripted value's width bound is refl and the
-- side condition never has to mention cWid.  A shared slot's def is
-- handed to sharedSlot-caps, which asks for its size and nothing else.
------------------------------------------------------------------
-- THE DELIVERY CLIQUE — foldPath / dispatchShare / shareGo /
-- chainStep — is no longer postulated: it is GROUND, below the block,
-- on stepFrame-caps and the three share-bookkeeping leaves.  Neither
-- is the *All edge: subscribeInner-caps, thruConsume-caps,
-- thruWalk-caps, concatDrain-caps and innerFinish-caps are all ground
-- below, once the joint bound stopped blocking them.

-- a data type has no observable inside it, so it has neither a
-- delivered nor a parked frame width — which is what still makes the
-- scripted half of the slot side condition a size-only predicate.  Both
-- axes need their own induction: pWᵛ is a join of two structural
-- recursions, and at a pair the joins interleave
outWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → outWᵛ k sl u v ≡ 0
outWᵛ-data k sl unitᵗ ok v = refl
outWᵛ-data k sl boolᵗ ok v = refl
outWᵛ-data k sl natᵗ  ok v = refl
outWᵛ-data k sl (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = cong₂ _⊔_ (outWᵛ-data k sl s (subst T (sym eqs) tt) a)
                        (outWᵛ-data k sl u ok b)
... | false = ⊥-elim ok
outWᵛ-data k sl (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = outWᵛ-data k sl s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
outWᵛ-data k sl (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = outWᵛ-data k sl u ok b
... | false = ⊥-elim ok
outWᵛ-data k sl (obs u) ok v = ⊥-elim ok

dWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → dWᵛ k sl u v ≡ 0
dWᵛ-data k sl unitᵗ ok v = refl
dWᵛ-data k sl boolᵗ ok v = refl
dWᵛ-data k sl natᵗ  ok v = refl
dWᵛ-data k sl (s ×ᵗ u) ok (a , b) with isData s in eqs
... | true  = cong₂ _⊔_ (dWᵛ-data k sl s (subst T (sym eqs) tt) a)
                        (dWᵛ-data k sl u ok b)
... | false = ⊥-elim ok
dWᵛ-data k sl (s +ᵗ u) ok (inj₁ a) with isData s in eqs
... | true  = dWᵛ-data k sl s (subst T (sym eqs) tt) a
... | false = ⊥-elim ok
dWᵛ-data k sl (s +ᵗ u) ok (inj₂ b) with isData s
... | true  = dWᵛ-data k sl u ok b
... | false = ⊥-elim ok
dWᵛ-data k sl (obs u) ok v = ⊥-elim ok

pWᵛ-data : ∀ {n} {Γ : Ctx n} (k : ℕ) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → pWᵛ k sl u v ≡ 0
pWᵛ-data k sl u ok v =
  cong₂ _⊔_ (outWᵛ-data k sl u ok v) (dWᵛ-data k sl u ok v)

valCaps?-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true → valCaps? c sl u v ≡ true
valCaps?-data {n = n} c sl u ok v h =
  ∧-intro h (subst (λ x → (x ≤ᵇ Caps.cWid c) ≡ true)
                   (sym (pWᵛ-data n sl u ok v)) refl)

valsCaps?-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (vs : List (Val Γ u)) → all (λ v → sizeᵛ u v ≤ᵇ Caps.cSize c) vs ≡ true →
  all (valCaps? c sl u) vs ≡ true
valsCaps?-data c sl u ok []       h = refl
valsCaps?-data c sl u ok (v ∷ vs) h
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c)
              (all (λ x → sizeᵛ u x ≤ᵇ Caps.cSize c) vs) h
... | h1 , h2 = ∧-intro (valCaps?-data c sl u ok v h1)
                        (valsCaps?-data c sl u ok vs h2)

-- resolving a delta-encoded tail against an anchor keeps the values, so
-- it keeps their bounds
resolve-caps : ∀ {n} {Γ : Ctx n} {u} (B : ℕ) (anchor : Tick)
  (ds : List (Timed (Val Γ u))) →
  all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) ds ≡ true →
  all (λ tv → sizeᵛ u (proj₂ tv) ≤ᵇ B) (resolve anchor ds) ≡ true
resolve-caps B anchor []                  h = refl
resolve-caps {u = u} B anchor ((after w , v) ∷ r) h
  with ∧-true (sizeᵛ u v ≤ᵇ B)
              (all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) r) h
... | h1 , h2 = ∧-intro h1 (resolve-caps B (anchor + suc w) r h2)

resolve-wid-data : ∀ {n} {Γ : Ctx n} {u} (W : ℕ) (sl : Slots Γ) → T (isData u) →
  (ps : List (Tick × Val Γ u)) →
  all (λ tv → pWᵛ n sl u (proj₂ tv) ≤ᵇ W) ps ≡ true
resolve-wid-data W sl ok []             = refl
resolve-wid-data {n = n} {u = u} W sl ok ((tk , v) ∷ ps) =
  ∧-intro (subst (λ x → (x ≤ᵇ W) ≡ true) (sym (pWᵛ-data n sl u ok v)) refl)
          (resolve-wid-data W sl ok ps)

-- a fresh cold's live entry, bounded on both halves
capsOK?-addLive : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (l : LiveSource Γ) (sched : Sched Γ) (st : EvalSt e) →
  boundedLive (Caps.cSize c) l ≡ true →
  widLive (Caps.cWid c) (Sched.slots sched) l ≡ true →
  capsOK? c sched st ≡ true →
  capsOK? c (record sched { live = l ∷ Sched.live sched }) st ≡ true
capsOK?-addLive {Γ = Γ} c l sched st bl wl inv =
    ∧-intro (∧-intro (∧-intro bl (proj₁ hL)) (proj₂ hL))
    (∧-intro h1
    (∧-intro (∧-intro wl h2)
    (∧-intro h3 h4)))
  where
  P  = capsOK?-parts c sched st inv
  h0 = proj₁ P
  hL = ∧-true (all (boundedLive {Γ = Γ} (Caps.cSize c)) (Sched.live sched))
              (all (λ kv → boundedNode (Caps.cSize c) (proj₂ kv)) (EvalSt.nodes st))
              h0
  h1 = proj₁ (proj₂ P)
  h2 = proj₁ (proj₂ (proj₂ P))
  h3 = proj₁ (proj₂ (proj₂ (proj₂ P)))
  h4 = proj₂ (proj₂ (proj₂ (proj₂ P)))

-- and cSize only ever grows with j, which is what widens a slot bound
-- stated at `c` to the level a clause reports at
cSize≤frameStep : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameStep j c)
cSize≤frameStep c j h =
  iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h) j (Caps.cSize c)

-- and the width axis of the same, which is what widens the slot
-- telescope's parked-width half to the level a clause reports at
cWid≤frameStep : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cWid c ≤ Caps.cWid (frameStep j c)
cWid≤frameStep c j h = iterFold-infl (Caps.cSize c) h j (Caps.cWid c)

subscribeE-input-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
subscribeE-input-caps {n = n} {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC inv pC lC
  with Sched.slots sched i
     | subst (λ y → slotCaps? (Caps.cSize c) (Caps.cWid c) sl (y i) ≡ true) (sym slEq)
             (slotsCaps?-lookup (Caps.cSize c) (Caps.cWid c) sl i slC)
-- SHARED: the def's size, and — since the parked-width repair — its
-- parked width, are the two things sharedSlot-caps asks for.  Both come
-- straight out of the slot telescope's own side condition
... | shared d | sd =
  sharedSlot-caps c j g i d κ id now sl sched st 2≤S 1≤R slEq slC inv
    (≤-trans (≤ᵇ⇒≤ (sizeᵉ d) (Caps.cSize c)
                (T-to (proj₁ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c)
                                     ((pWᵉ n sl d ≤ᵇ Caps.cWid c)
                                        ∧ (innWᵉ n sl d ≤ᵇ Caps.cWid c)) sd))))
             (cSize≤frameStep c j 2≤S))
    (≤-trans (m≤n⊔m _ (dWᵉ n sl d))
      (≤-trans (≤ᵇ⇒≤ (pWᵉ n sl d) (Caps.cWid c)
                  (T-to (proj₁ (∧-true (pWᵉ n sl d ≤ᵇ Caps.cWid c)
                                       (innWᵉ n sl d ≤ᵇ Caps.cWid c)
                          (proj₂ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c)
                                         ((pWᵉ n sl d ≤ᵇ Caps.cWid c)
                                            ∧ (innWᵉ n sl d ≤ᵇ Caps.cWid c)) sd))))))
               (cWid≤frameStep c j 2≤S)))
    pC lC
-- HOT SCRIPT: spent, or one more registration
... | scripted (hot async) | sd
  with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                        at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (+-identityʳ j)) refl
...   | false =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j)) refl
-- COLD, NO TAIL: a one-shot burst of the slot's own sync values, and
-- nothing goes into the state but a source counter capsOK? does not read
subscribeE-input-caps {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC inv pC lC
  | scripted {ok} (cold sync []) | sd =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (proj₂ (oneShotBurst sync id sched)) st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (proj₁ (oneShotBurst sync id sched)) ≡ true)
            (sym (+-identityʳ j))
            (∧-intro (∧-intro refl
                        (all-++-intro (eventCaps? (frameStep j c) sl)
                           (map value sync) _
                           (mapValue-caps (frameStep j c) sl (lookup Γ i) sync SY)
                           refl))
                     refl)
  where
  SY = valsCaps?-data (frameStep j c) sl (lookup Γ i) ok sync
         (all-impl (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c)
                   (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize (frameStep j c))
                   (λ v → ≤ᵇ-widen (sizeᵛ (lookup Γ i) v)
                            (cSize≤frameStep c j 2≤S)) sync
            (proj₁ (∧-true (all (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c) sync)
                           true sd)))
-- COLD WITH A TAIL: a fresh source, a live entry for the async pendings,
-- and one registration
subscribeE-input-caps {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC inv pC lC
  | scripted {ok} (cold sync (dd ∷ ds)) | sd =
  1 , subst (λ x → capsOK? (frameStep x c) SCHED₃ (register SRC κ st) ≡ true)
            (sym (j+1 j))
            (capsOK?-addLive (frameStep (suc j) c) NEW SCHED₂ (register SRC κ st)
               BL WL (register-caps c j SRC κ sched st 2≤S 1≤R inv pC))
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j))
            (∧-intro (∧-intro refl
                        (mapValue-caps (frameStep (suc j) c) sl (lookup Γ i) sync SY))
                     refl)
  where
  SRC    = Sched.nextSource sched
  SCHED₂ = record (record sched { nextSource = suc (Sched.nextSource sched) })
                  { nextOrdinal = suc (Sched.nextOrdinal sched) }
  NEW    = record { source = SRC ; ordinal = Sched.nextOrdinal sched
                  ; elemTy = lookup Γ i ; pending = resolve now (dd ∷ ds) }
  SCHED₃ = record SCHED₂ { live = NEW ∷ Sched.live SCHED₂ }
  sdp    = ∧-true (all (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c) sync)
                  (all (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv) ≤ᵇ Caps.cSize c)
                       (dd ∷ ds)) sd
  SY = valsCaps?-data (frameStep (suc j) c) sl (lookup Γ i) ok sync
         (all-impl (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c)
                   (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize (frameStep (suc j) c))
                   (λ v → ≤ᵇ-widen (sizeᵛ (lookup Γ i) v)
                            (cSize≤frameStep c (suc j) 2≤S)) sync (proj₁ sdp))
  BL = resolve-caps (Caps.cSize (frameStep (suc j) c)) now (dd ∷ ds)
         (all-impl (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv) ≤ᵇ Caps.cSize c)
                   (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv)
                             ≤ᵇ Caps.cSize (frameStep (suc j) c))
                   (λ tv → ≤ᵇ-widen (sizeᵛ (lookup Γ i) (Timed.val tv))
                             (cSize≤frameStep c (suc j) 2≤S)) (dd ∷ ds)
            (proj₂ sdp))
  WL = resolve-wid-data (Caps.cWid (frameStep (suc j) c)) (Sched.slots sched) ok
         (resolve now (dd ∷ ds))

-- THE from-inner CLAUSE: absorb, or finish.  Both the `fin = false` and
-- the absorbed branch are the identity on the state; only the finish
-- delegates, and it delegates to innerFinish-caps verbatim
innerReact-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl s) (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
innerReact-caps c j g op allNid inst κ id now vals false sl sched st
                2≤S 1≤R slEq slC inv pS lC vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
innerReact-caps c j g op allNid inst κ id now vals true sl sched st
                2≤S 1≤R slEq slC inv pS lC vC
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → all (valCaps? (frameStep x c) sl _) vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
... | false = innerFinish-caps c j g op allNid inst κ id now vals sl sched st
                2≤S 1≤R slEq slC inv pS lC vC

------------------------------------------------------------------
-- AND THE TWO CLAUSES THAT DO BUILD VALUES, GROUND — over the size
-- receipt and the width bridge above.
--
-- map-f and scan-f are the only clauses of stepFrame that call
-- `applyFn`, and `applyFn fn v` is `evalWith fn (v ∷ [])`: not a
-- substitution but an EVALUATION.  That distinction is the whole
-- content of these two statements, and it is why they are not
-- one-liners off size-subΘᵉ the way `sizeStep`'s comment reads.
--
-- WHAT sizeStep IS READ OFF, AND WHAT applyFn ACTUALLY DOES.  sizeStep
-- S s = S * suc (2 * s) is exactly size-subΘᵉ's bound, `sizeᵉ f * suc
-- (2 * V)` — the cost of PLUGGING an env of size V into a template of
-- size f.  evalWith does more than plug: its `caseᵗ` clause evaluates
-- the scrutinee and extends the environment WITH THE RESULTING VALUE,
-- so the env a later `strmᵗ` closes over is not the caller's env.  The
-- shape that exploits it:
--
--     caseᵗ (inlᵗ (pairᵗ x x)) (caseᵗ (inlᵗ (pairᵗ v₀ v₀)) (… ) _) _
--
-- nested d deep, each level pairing the binding introduced by the level
-- above with itself.  `sizeᵗ fn` is Θ(d); the value it computes from an
-- input of size 1 is Θ(2 ^ d).  So NO j′ = 1 works: one sizeStep is
-- linear in the cap and the clause is exponential in the step
-- function's syntax.  .Measures' own bounds say the same thing without
-- the counterexample — evalWith-size is `(2 + 2 * V) ^ (3 ^ sizeᵗ fn)`,
-- a tower, and evalWith-sharp only moves the exponent to
-- `3 ^ caseWᵗ fn`.
--
-- AND THAT IS WHAT applyFn-iterSize PAYS, PROVEN: the receipt is one
-- fold per node of the STEP FUNCTION, `sizeᵗ fn`, with the payload's
-- own size as the seed — Eval-Growth-Probe §6 gates it at the worst
-- admissible base S = 1 on the very family above.  What is NOT true is
-- that the receipt is one fold per FRAME.
--
-- SO THE COST MOVES, IT DOES NOT VANISH, AND IT LANDS ON
-- cascadeGo-charge — `j ≤ D * cSize`, one delivery's frames times a
-- per-frame charge of cSize.  A single map-f frame over a case-nested
-- step function needs a j′ exponential in cSize, so `D * cSize` is
-- short by an exponential on that program.  This is flagged rather than
-- patched: cascadeGo-charge is the OTHER half of the budget claim and
-- changing it is a design ruling, not a clause grind.  The two
-- statements below are stated so that the difficulty has a NAME and a
-- boundary — no state, no recursion, no mutual induction, just
-- applyFn — instead of being buried in the hub clause
------------------------------------------------------------------

-- ONE map-f FRAME, GROUND AND SYNTAX-COUNTED.  Every payload is mapped
-- independently, so nothing composes and the whole list costs one
-- clause's worth of folds: applyFn-iterSize reads the SIZE receipt off
-- the step function's syntax with the payload's own size as the seed,
-- and applyFn-iterFold reads the WIDTH receipt off the same syntax with
-- the payload's own WIDTH as the seed.  j′ = suc (sizeᵗ fn) — one fold
-- per node of the step function, and ONE more that absorbs the seed
mapFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ →
    all (valCaps? (frameStep (j + j′) c) sl u) (map (applyFn fn) vals) ≡ true
mapFrame-caps {Γ = Γ} {s = s} {u = u} c j sl fn vals 2≤S slC fS vC =
  suc a , go vals vC
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  B   = Caps.cSize (frameStep j c)
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗ fn
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  sz : (v : Val Γ s) → valCaps? (frameStep j c) sl s v ≡ true →
       sizeᵛ u (applyFn fn v) ≤ Caps.cSize (frameStep (j + suc a) c)
  sz v hv =
    ≤-trans (≤-trans (applyFn-iterSize S B 1≤S fn v
                        (≤ᵇ⇒≤ (sizeᵛ s v) B
                           (T-to (valCaps?-size (frameStep j c) sl s v hv))))
                     (≤-reflexive (sym (iterSize-+ S j a S))))
            (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a)))
  wd : (v : Val Γ s) → valCaps? (frameStep j c) sl s v ≡ true →
       pWᵛ _ sl u (applyFn fn v) ≤ Caps.cWid (frameStep (j + suc a) c)
  wd v hv =
    wid-lift c j a 2≤S
      (applyFn-iterFold S M 2≤S (s≤s z≤n) sl slW fn v
        (≤-trans (≤ᵇ⇒≤ (pWᵛ _ sl s v) V
                   (T-to (valCaps?-wid (frameStep j c) sl s v hv)))
                 (n≤1+n V)))
  go : (vs : List (Val Γ s)) → all (valCaps? (frameStep j c) sl s) vs ≡ true →
       all (valCaps? (frameStep (j + suc a) c) sl u)
           (map (applyFn fn) vs) ≡ true
  go []       h = refl
  go (v ∷ vs) h
    with ∧-true (valCaps? (frameStep j c) sl s v)
                (all (valCaps? (frameStep j c) sl s) vs) h
  ... | hd , tl =
    ∧-intro (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (sz v hd))) (T⇒≡true _ (≤⇒≤ᵇ (wd v hd))))
            (go vs tl)

-- ONE scan-f FRAME'S SIZE LADDER.  Here the folds DO compose — scanVals
-- threads the accumulator, so payload i is `applyFn` applied i times —
-- and each rung costs one PAIRING plus one step function: the arriving
-- payload is paired with the stored accumulator before the step runs,
-- which is exactly one sizeStep, so a rung is `suc (sizeᵗ fn)` folds and
-- the whole list is `length vals` of them
scanVals-size : ∀ {n} {Γ : Ctx n} {s u} (S B : ℕ) → 2 ≤ S →
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  sizeᵛ u ac0 ≤ B →
  all (λ v → sizeᵛ s v ≤ᵇ B) vals ≡ true →
  (all (λ w → sizeᵛ u w ≤ᵇ iterSize S (length vals * suc (sizeᵗ fn)) B)
       (proj₁ (scanVals fn ac0 vals)) ≡ true)
  × (sizeᵛ u (proj₂ (scanVals fn ac0 vals))
       ≤ iterSize S (length vals * suc (sizeᵗ fn)) B)
scanVals-size S B hS fn ac0 []       hac0 h = refl , hac0
scanVals-size {s = s} {u = u} S B hS fn ac0 (v ∷ vs) hac0 h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ HEAD)) (proj₁ IH′) , proj₂ IH′
  where
  F    = sizeᵗ fn
  B₁   = iterSize S (suc F) B
  1≤S  = ≤-trans (s≤s z≤n) hS
  split = ∧-true (sizeᵛ s v ≤ᵇ B) (all (λ x → sizeᵛ s x ≤ᵇ B) vs) h
  hv   : sizeᵛ s v ≤ B
  hv   = ≤ᵇ⇒≤ (sizeᵛ s v) B (T-to (proj₁ split))
  hac0′ : sizeᵛ u (applyFn fn (ac0 , v)) ≤ B₁
  hac0′ = applyFn-iterSize S (sizeStep S B) 1≤S fn (ac0 , v)
            (≤-trans (s≤s (+-mono-≤ hac0 hv)) (pair≤sizeStep S B 1≤S))
  hvs  = all-impl (λ x → sizeᵛ s x ≤ᵇ B) (λ x → sizeᵛ s x ≤ᵇ B₁)
           (λ x → ≤ᵇ-widen (sizeᵛ s x) (iterSize-infl S 1≤S (suc F) B))
           vs (proj₂ split)
  IH   = scanVals-size S B₁ hS fn (applyFn fn (ac0 , v)) vs hac0′ hvs
  eq   : iterSize S (length vs * suc F) B₁
           ≡ iterSize S (suc F + length vs * suc F) B
  eq   = sym (iterSize-+ S (suc F) (length vs * suc F) B)
  IH′  = subst (λ X →
                  (all (λ w → sizeᵛ u w ≤ᵇ X)
                       (proj₁ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≡ true)
                  × (sizeᵛ u (proj₂ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≤ X))
               eq IH
  HEAD : sizeᵛ u (applyFn fn (ac0 , v))
           ≤ iterSize S (suc F + length vs * suc F) B
  HEAD = ≤-trans hac0′
           (subst (B₁ ≤_) eq (iterSize-infl S 1≤S (length vs * suc F) B₁))

-- the same ladder ON THE WIDTH AXIS, and at the SAME count: a rung
-- pairs the arriving payload with the stored accumulator (one fold)
-- and steps it (one per node of the step function), with the widths
-- entering as SEEDS
scanVals-wid : ∀ {n} {Γ : Ctx n} {s u} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  pWᵛ n sl u ac0 ≤ M →
  all (λ v → pWᵛ n sl s v ≤ᵇ M) vals ≡ true →
  (all (λ w → pWᵛ n sl u w ≤ᵇ iterFold S (length vals * suc (sizeᵗ fn)) M)
       (proj₁ (scanVals fn ac0 vals)) ≡ true)
  × (pWᵛ n sl u (proj₂ (scanVals fn ac0 vals))
       ≤ iterFold S (length vals * suc (sizeᵗ fn)) M)
scanVals-wid S M hS hM sl hI fn ac0 []       hac0 h = refl , hac0
scanVals-wid {n = n} {s = s} {u = u} S M hS hM sl hI fn ac0 (v ∷ vs) hac0 h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ HEAD)) (proj₁ IH′) , proj₂ IH′
  where
  F    = sizeᵗ fn
  M₁   = iterFold S (suc F) M
  split = ∧-true (pWᵛ n sl s v ≤ᵇ M) (all (λ x → pWᵛ n sl s x ≤ᵇ M) vs) h
  hv   : pWᵛ n sl s v ≤ M
  hv   = ≤ᵇ⇒≤ (pWᵛ n sl s v) M (T-to (proj₁ split))
  hac0′ : pWᵛ n sl u (applyFn fn (ac0 , v)) ≤ M₁
  hac0′ = ≤-trans (applyFn-iterFold S M hS hM sl hI fn (ac0 , v)
                     (≤-trans (pWᵛ-pair sl u s ac0 v) (⊔-lub hac0 hv)))
                  (iterFold-mono-count S M hS (n≤1+n F))
  hI₁ : SlotWid sl M₁
  hI₁ = SlotWid-mono sl (iterFold-infl S hS (suc F) M) hI
  hvs  = all-impl (λ x → pWᵛ n sl s x ≤ᵇ M) (λ x → pWᵛ n sl s x ≤ᵇ M₁)
           (λ x → ≤ᵇ-widen (pWᵛ n sl s x) (iterFold-infl S hS (suc F) M))
           vs (proj₂ split)
  IH   = scanVals-wid S M₁ hS (≤-trans hM (iterFold-infl S hS (suc F) M))
           sl hI₁ fn (applyFn fn (ac0 , v)) vs hac0′ hvs
  eq   : iterFold S (length vs * suc F) M₁
           ≡ iterFold S (suc F + length vs * suc F) M
  eq   = sym (iterFold-+ S (suc F) (length vs * suc F) M)
  IH′  = subst (λ X →
                  (all (λ w → pWᵛ n sl u w ≤ᵇ X)
                       (proj₁ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≡ true)
                  × (pWᵛ n sl u (proj₂ (scanVals fn (applyFn fn (ac0 , v)) vs)) ≤ X))
               eq IH
  HEAD : pWᵛ n sl u (applyFn fn (ac0 , v))
           ≤ iterFold S (suc F + length vs * suc F) M
  HEAD = ≤-trans hac0′
           (subst (M₁ ≤_) eq (iterFold-infl S hS (length vs * suc F) M₁))

-- the two ladders' conclusions are read off one list, so they are
-- joined before the widening
all-∧ : ∀ {A : Set} (p q : A → Bool) (xs : List A) →
  all p xs ≡ true → all q xs ≡ true → all (λ x → p x ∧ q x) xs ≡ true
all-∧ p q []       hp hq = refl
all-∧ p q (x ∷ xs) hp hq =
  ∧-intro (∧-intro (proj₁ (∧-true (p x) (all p xs) hp))
                   (proj₁ (∧-true (q x) (all q xs) hq)))
          (all-∧ p q xs (proj₂ (∧-true (p x) (all p xs) hp))
                        (proj₂ (∧-true (q x) (all q xs) hq)))

-- ONE scan-f FRAME, GROUND AND SYNTAX-COUNTED.  The accumulator has to
-- come back bounded too, because it is reinstalled.
-- j′ = suc (length vals * suc (sizeᵗ fn))
scanFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac0 : Val Γ u) (vals : List (Val Γ s)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
  valCaps? (frameStep j c) sl u ac0 ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  Σ ℕ λ j′ →
    (all (valCaps? (frameStep (j + j′) c) sl u)
         (proj₁ (scanVals fn ac0 vals)) ≡ true)
    × (valCaps? (frameStep (j + j′) c) sl u (proj₂ (scanVals fn ac0 vals)) ≡ true)
scanFrame-caps {n = n} {Γ = Γ} {s = s} {u = u} c j sl fn ac0 vals 2≤S slC fS aC vC =
  suc a
    , all-impl (λ w → (sizeᵛ u w ≤ᵇ iterSize S a B) ∧ (pWᵛ n sl u w ≤ᵇ iterFold S a M))
               (valCaps? (frameStep (j + suc a) c) sl u)
               (λ w hw → mk w (proj₁ (∧-true (sizeᵛ u w ≤ᵇ iterSize S a B)
                                             (pWᵛ n sl u w ≤ᵇ iterFold S a M) hw))
                              (proj₂ (∧-true (sizeᵛ u w ≤ᵇ iterSize S a B)
                                             (pWᵛ n sl u w ≤ᵇ iterFold S a M) hw)))
               (proj₁ (scanVals fn ac0 vals))
               (all-∧ (λ w → sizeᵛ u w ≤ᵇ iterSize S a B)
                      (λ w → pWᵛ n sl u w ≤ᵇ iterFold S a M)
                      (proj₁ (scanVals fn ac0 vals)) (proj₁ SV) (proj₁ SW))
    , mk (proj₂ (scanVals fn ac0 vals))
         (T⇒≡true _ (≤⇒≤ᵇ (proj₂ SV))) (T⇒≡true _ (≤⇒≤ᵇ (proj₂ SW)))
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  B   = Caps.cSize (frameStep j c)
  V   = Caps.cWid (frameStep j c)
  a   = length vals * suc (sizeᵗ fn)
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  mk : (w : Val Γ u) → (sizeᵛ u w ≤ᵇ iterSize S a B) ≡ true →
       (pWᵛ n sl u w ≤ᵇ iterFold S a M) ≡ true →
       valCaps? (frameStep (j + suc a) c) sl u w ≡ true
  mk w h1 h2 =
    ∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ
        (≤-trans (≤-trans (≤ᵇ⇒≤ (sizeᵛ u w) (iterSize S a B) (T-to h1))
                          (≤-reflexive (sym (iterSize-+ S j a S))))
                 (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
      (T⇒≡true _ (≤⇒≤ᵇ
        (wid-lift c j a 2≤S (≤ᵇ⇒≤ (pWᵛ n sl u w) (iterFold S a M) (T-to h2)))))
  SV = scanVals-size S B 2≤S fn ac0 vals
         (≤ᵇ⇒≤ (sizeᵛ u ac0) B
            (T-to (valCaps?-size (frameStep j c) sl u ac0 aC)))
         (all-impl (valCaps? (frameStep j c) sl s) (λ v → sizeᵛ s v ≤ᵇ B)
            (λ v → valCaps?-size (frameStep j c) sl s v) vals vC)
  SW = scanVals-wid S M 2≤S (s≤s z≤n) sl slW fn ac0 vals
         (≤-trans (≤ᵇ⇒≤ (pWᵛ n sl u ac0) V
                    (T-to (valCaps?-wid (frameStep j c) sl u ac0 aC)))
                  (n≤1+n V))
         (all-impl (valCaps? (frameStep j c) sl s) (λ v → pWᵛ n sl s v ≤ᵇ M)
            (λ v hv → ≤ᵇ-widen (pWᵛ n sl s v) (n≤1+n V)
                        (valCaps?-wid (frameStep j c) sl s v hv))
            vals vC)

------------------------------------------------------------------
-- stepFrame-caps, GROUND.  Five clauses over the four leaves above and
-- the two value postulates; the only arithmetic is widening the entry
-- invariant to the reported level.
--
-- ONE HYPOTHESIS HAD TO BE ADDED, and it was missing rather than
-- optional: `suc (pathLen κ) ≤ cSize (frameStep j c)`.  The thru-outer
-- clause hands κ to thruWalk-caps, which requires exactly that conjunct,
-- and the postulated face carried only `pathSz? … κ` — which says every
-- PROPER SUFFIX of κ is short, and says nothing about κ itself.  The
-- caller already has it: foldPath-caps splits `pathSz? B (f ↠ p)` into
-- `frameSz? B f`, `suc (pathLen p) ≤ᵇ B` and `pathSz? B p`, and was
-- discarding the middle one.  So the repair costs the call site one
-- `≤ᵇ⇒≤` and nothing else — no new obligation anywhere in the tree
------------------------------------------------------------------

-- the six clauses where the node lookup misses or mismatches: the
-- evaluator emits nothing and touches nothing
stepFrame-zero-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (u : Ty) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u) [] ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) [] ≡ true)
stepFrame-zero-caps c j u sl sched st inv =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl

stepFrame-scan-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) (scan-f fn nid) ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-caps {s = s} {u = u} c j g id now fn nid κ vals fin sl sched st
                    2≤S slC slEq inv fS pS vC
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing                | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (take-st _)       | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (merge-st _ _)    | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (concat-st _ _ _) | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (switch-st _ _)   | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (exhaust-st _ _)  | _ = stepFrame-zero-caps c j u sl sched st inv
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = stepFrame-zero-caps c j u sl sched st inv
...   | yes refl =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (scan-st (proj₂ run)) sched st
         (valCaps?-size (frameStep (j + j′) c) sl _ (proj₂ run) (proj₂ (proj₂ SC)))
         (subst (λ x → widNode (Caps.cWid (frameStep (j + j′) c)) x
                         (scan-st (proj₂ run)) ≡ true)
                (sym slEq)
                (valCaps?-wid (frameStep (j + j′) c) sl _ (proj₂ run)
                   (proj₂ (proj₂ SC))))
         (capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
            (frameStep-⊑-+ c 2≤S j j′) inv)
     , proj₁ (proj₂ SC)
     , refl
  where
  run = scanVals fn ac vals
  SC  = scanFrame-caps c j sl fn ac vals 2≤S slC fS
          (∧-intro (proj₁ nb)
                   (subst (λ x → (pWᵛ _ x u ac ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                          slEq (proj₂ nb)))
          vC
  j′  = proj₁ SC

stepFrame-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  all (valCaps? (frameStep j c) sl s) vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) sl u)
            (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MAP: nothing touches the state, so the invariant is only widened
stepFrame-caps c j g id now (map-f fn) κ vals fin sl sched st 2≤S 1≤R slEq slC inv fS pS lC vC =
  j′ , capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
         (frameStep-⊑-+ c 2≤S j j′) inv
     , proj₂ MP
     , refl
  where
  MP = mapFrame-caps c j sl fn vals 2≤S slC fS vC
  j′ = proj₁ MP

-- SCAN: its own top-level lemma, as in the wet family — the nested
-- `with` on the stored accumulator's type cannot be elaborated inside a
-- clause of the general frame case
stepFrame-caps c j g id now (scan-f fn nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC inv fS pS lC vC =
  stepFrame-scan-caps c j g id now fn nid κ vals fin sl sched st 2≤S slC slEq inv fS pS vC

-- TAKE: a prefix and a cut, no folds
stepFrame-caps c j g id now (take-f nid) κ vals fin sl sched st 2≤S 1≤R slEq slC inv fS pS lC vC =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ (proj₂ (proj₂ TD))))
                     (proj₂ (proj₂ (proj₂ (proj₂ TD)))) ≡ true)
            (sym (+-identityʳ j)) (proj₁ TDc)
    , subst (λ x → all (valCaps? (frameStep x c) sl _) (proj₁ TD) ≡ true)
            (sym (+-identityʳ j)) (proj₁ (proj₂ TDc))
    , subst (λ x → all (eventCaps? (frameStep x c) sl) (proj₁ (proj₂ TD)) ≡ true)
            (sym (+-identityʳ j)) (proj₂ (proj₂ TDc))
  where
  TD  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  TDc = takeDispatch-caps (frameStep j c) nid vals fin sl sched st
          (lookupNode nid (EvalSt.nodes st)) slEq inv vC

-- FROM-INNER and THRU-OUTER: the two *All edges, delegated whole
stepFrame-caps c j g id now (from-inner op allNid inst) κ vals fin sl sched st
               2≤S 1≤R slEq slC inv fS pS lC vC =
  innerReact-caps c j g op allNid inst κ id now vals fin sl sched st
    2≤S 1≤R slEq slC inv pS lC vC

stepFrame-caps c j g id now (thru-outer op nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC inv fS pS lC vC =
  j′ , proj₁ WR , proj₁ (proj₂ WR) , proj₂ (proj₂ WR)
  where
  TW = thruWalk-caps c j g op nid κ id now vals sl sched st
         2≤S 1≤R slEq slC inv pS vC lC
  j′ = proj₁ TW
  WK = thruWalk g op nid κ id now vals sched st
  WR = thruWrap-caps (frameStep (j + j′) c) op nid fin sl WK
         (proj₁ (proj₂ TW)) (proj₁ (proj₂ (proj₂ TW))) (proj₂ (proj₂ (proj₂ TW)))

------------------------------------------------------------------
-- THE TWO SUBSCRIBE-SIDE COMPANIONS f1a03c4'S SURVEY FOUND MISSING.
--
-- pushBurst is foldPath's `↠` clause once per EMIT rather than once per
-- frame: split the emit, step it through the one frame just built, and
-- reassemble under the same envelope.  So it runs on exactly the same
-- three pieces — splitEvents' two halves, the ground stepFrame-caps, and
-- the additive receipt — and the only new leaf is that a RETAGGED event
-- list carries no values, hence no bound.
--
-- subscribeAll is then mintNode + installNode + subscribeE at
-- `thru-outer op nid ↠ κ` + pushBurst.  It is the same one-j-per-hop
-- absorption subscribeInner-caps runs on: the chain gains one frame and
-- the recursion pays one j for it (frameStep-chain-suc), so the
-- extension fits under the stepped cap with room.  The initial node
-- state's two bounds are hypotheses rather than derivations — the four
-- *All heads supply them by `refl`, since every one of merge-st,
-- concat-st [], switch-st and exhaust-st is trivially bounded on both
-- axes.
------------------------------------------------------------------

-- a retagged event list is value-free by construction, so every caps
-- conjunct on it is `refl`
retagEvents-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (sl : Slots Γ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventCaps? {u = u} c sl) (retagEvents {B = Val Γ u} es) ≡ true
retagEvents-caps c sl []                  = refl
retagEvents-caps {u = u} c sl (value _   ∷ es) = retagEvents-caps {u = u} c sl es
retagEvents-caps {u = u} c sl (init _    ∷ es) =
  ∧-intro refl (retagEvents-caps {u = u} c sl es)
retagEvents-caps {u = u} c sl (close _ _ ∷ es) =
  ∧-intro refl (retagEvents-caps {u = u} c sl es)
retagEvents-caps {u = u} c sl (handoff _ ∷ es) =
  ∧-intro refl (retagEvents-caps {u = u} c sl es)
retagEvents-caps {u = u} c sl (complete  ∷ es) =
  ∧-intro refl (retagEvents-caps {u = u} c sl es)

pushBurst-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t) (str : Stream Γ s)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  burstCaps? (frameStep j c) sl str ≡ true →
  let r = pushBurst g id now f κ str sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
pushBurst-caps {u = u} c j g id now f κ [] sl sched st
               2≤S 1≤R slEq slC inv fS pS lC bC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
pushBurst-caps {Γ = Γ} {s = s} {u = u} c j g id now f κ (em ∷ ems) sl sched st
               2≤S 1≤R slEq slC inv fS pS lC bC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl
        (((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST)
        (∧-intro EMIT (proj₂ (proj₂ IH)))
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ u} E
  eC   = proj₁ (∧-true _ _ bC)
  SF   = stepFrame-caps c j g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sl sched st
           2≤S 1≤R slEq slC inv fS pS lC
           (splitEvents-vals-caps {u = u} (frameStep j c) sl E eC)
  j₁   = proj₁ SF
  step = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  ⊑₁   = frameStep-⊑-+ c 2≤S j j₁
  IH   = pushBurst-caps c (j + j₁) g id now f κ ems sl sd₁ st₁ 2≤S 1≤R
           (trans (KeepsC.slotsEq
                    (stepFrame-keeps g id now f κ (proj₁ sp)
                       (proj₂ (proj₂ sp)) sched st))
                  slEq)
           slC
           (proj₁ (proj₂ SF))
           (frameSz?-widen f (proj₁ ⊑₁) fS)
           (pathSz?-⊑ κ ⊑₁ pS)
           (≤-trans lC (proj₁ ⊑₁))
           (burstCaps?-widen sl ems ⊑₁ (proj₂ (∧-true _ _ bC)))
  j₂   = proj₁ IH
  REST = pushBurst g id now f κ ems sd₁ st₁
  ⊑₂   = frameStep-⊑-+ c 2≤S (j + j₁) j₂
  EMIT : all (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
             (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                ++ map value (proj₁ step)
                ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           ≡ true
  EMIT = all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ sp)) _
           (splitEvents-bk-caps {u = u} (frameStep ((j + j₁) + j₂) c) sl E)
           (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
              (retagEvents (proj₁ (proj₂ step))) _
              (retagEvents-caps {u = u} (frameStep ((j + j₁) + j₂) c) sl
                 (proj₁ (proj₂ step)))
              (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
                 (map value (proj₁ step)) _
                 (mapValue-caps (frameStep ((j + j₁) + j₂) c) sl u (proj₁ step)
                    (valsCaps?-widen sl u (proj₁ step) ⊑₂
                       (proj₁ (proj₂ (proj₂ SF)))))
                 (finList-caps (frameStep ((j + j₁) + j₂) c) sl
                    (proj₁ (proj₂ (proj₂ step))))))

-- THE *All HEAD.  One j for the thru-outer frame the chain gains, then
-- the burst is pushed back through that same frame
subscribeAll-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  boundedNode (Caps.cSize (frameStep (suc j) c)) ns ≡ true →
  widNode (Caps.cWid (frameStep (suc j) c)) sl ns ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeAll g op ns b κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
subscribeAll-caps {Γ = Γ} {t = t} {u = u} c j g op ns b κ id now sl sched st
                  2≤S 1≤R slEq slC inv bn wn szb wdb pC lC =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₂ (proj₂ PBc)))
  where
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid ns st
  κ′     = thru-outer op nid ↠ κ
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B′     = Caps.cSize (frameStep (suc j) c)
  pC′ : pathSz? B′ κ′ ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  inv₀ : capsOK? (frameStep (suc j) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc j) c) nid ns sched₀ st bn
           (subst (λ y → widNode (Caps.cWid (frameStep (suc j) c)) y ns ≡ true)
                  (sym slEq) wn)
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  SUB = subscribeE-caps c (suc j) g b κ′ id now sl sched₀ st₀ 2≤S 1≤R slEq slC inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₁  = proj₁ SUB
  res = subscribeE g b κ′ id now sched₀ st₀
  PBc = pushBurst-caps c (suc j + j₁) g id now (thru-outer op nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq (subscribeE-keeps g b κ′ id now sched₀ st₀)) slEq)
          slC (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁)
             (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          (proj₂ (proj₂ SUB))
  j₂  = proj₁ PBc
  PB  = pushBurst g id now (thru-outer op nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

------------------------------------------------------------------
-- THE THREE CLAUSES subscribeE-caps CANNOT DISCHARGE IN PLACE, GROUND
-- BESIDE IT.
--
-- Two of subscribeE's clauses BUILD VALUES BY EVALUATION and one
-- REBUILDS ITS OWN SYNTAX, and all three land exactly where
-- mapFrame-caps / scanFrame-caps already are: `evalTm` is `evalWith`
-- with an empty environment, an EVALUATION rather than a substitution,
-- and evalWith-size is a TOWER in the term's syntax (evalWith-sharp
-- only moves the exponent to `3 ^ caseWᵗ`).  So none of the three is
-- `sizeᵛ ≤ sizeᵗ` and each wants an existential j′ of its own — which
-- is affordable, because iterSize runs away faster than the clause
-- does, and is the same reason the two frame members are true.
--
-- Stated as tightly as the clauses consume them, so the difficulty has
-- a NAME and a boundary — no state, no recursion, no chain, just the
-- evaluator's own arithmetic — instead of being buried in the hub.
--
-- THE μ CLAUSE IS THE ONE THAT IS NOT ABOUT evalTm — and it is the one
-- that cost a refuted draft.  `unfoldμ body` is LARGER than `μᵉ body`
-- on the size axis, and the width axis was assumed stable and is not:
-- see the note on unfoldμ-caps below, and Hop-Descent-Probe's μwide,
-- which measures 0 ↦ 6.  Both halves now come off ONE size receipt:
-- size-unfoldμ (the μ's size squared) for the size, and the width
-- bridge above for the width.
------------------------------------------------------------------

-- `ofᵉ ts` bursts `map evalTm ts`, GROUND AND SYNTAX-COUNTED.  Both
-- halves of valCaps? are owed and each comes off its OWN receipt at the
-- same count: evalTm-iterSize spends one iterSize fold per syntax node
-- from an empty environment, evalTm-iterFold one foldStep per syntax
-- node from the telescope's leaf bound.  j′ = suc (sizeᵗˢ ts)
evalTms-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (ts : List (Tm Γ [] [] [] u)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗˢ ts ≤ Caps.cSize (frameStep j c) →
  dWᵗˢ n sl ts ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → all (valCaps? (frameStep (j + j′) c) sl u)
                 (map (λ tm → evalTm tm) ts) ≡ true
evalTms-caps {n = n} {Γ = Γ} {u = u} c j sl ts 2≤S slC szb wdb =
  suc a , go ts ≤-refl
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗˢ ts
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)
  one : (tm : Tm Γ [] [] [] u) → sizeᵗ tm ≤ a →
        valCaps? (frameStep (j + suc a) c) sl u (evalTm tm) ≡ true
  one tm h =
    ∧-intro
      (T⇒≡true _ (≤⇒≤ᵇ
        (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S tm)
                            (≤-trans (iterSize-mono-count S 0 1≤S h)
                                     (iterSize-mono-s S a z≤n)))
                          (≤-reflexive (sym (iterSize-+ S j a S))))
                 (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
      (T⇒≡true _ (≤⇒≤ᵇ
        (wid-lift c j a 2≤S
          (≤-trans (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW tm)
                   (iterFold-mono-count S M 2≤S h)))))
  go : (vs : List (Tm Γ [] [] [] u)) → sizeᵗˢ vs ≤ a →
       all (valCaps? (frameStep (j + suc a) c) sl u)
           (map (λ tm → evalTm tm) vs) ≡ true
  go []       h = refl
  go (y ∷ ys) h =
    ∧-intro (one y (≤-trans (m≤m+n (sizeᵗ y) (sizeᵗˢ ys)) h))
            (go ys (≤-trans (m≤n+m (sizeᵗˢ ys) (sizeᵗ y)) h))

-- `scanᵉ f seed b` installs `scan-st (evalTm seed)`: the same statement
-- for one term, and the accumulator has to come back bounded on both
-- axes because capsOK? reads it on both.  j′ = suc (sizeᵗ z)
evalSeed-caps : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (z : Tm Γ [] [] [] u) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵗ z ≤ Caps.cSize (frameStep j c) →
  dWᵗ n sl z ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → valCaps? (frameStep (j + j′) c) sl u (evalTm z) ≡ true
evalSeed-caps {n = n} {u = u} c j sl z 2≤S slC szz wdz =
  suc a
    , ∧-intro
        (T⇒≡true _ (≤⇒≤ᵇ
          (≤-trans (≤-trans (≤-trans (evalTm-iterSize S 1≤S z)
                              (iterSize-mono-s S a z≤n))
                            (≤-reflexive (sym (iterSize-+ S j a S))))
                   (iterSize-mono-count S S 1≤S (+-monoʳ-≤ j (n≤1+n a))))))
        (T⇒≡true _ (≤⇒≤ᵇ
          (wid-lift c j a 2≤S (evalTm-iterFold S M 2≤S (s≤s z≤n) sl slW z))))
  where
  S   = Caps.cSize c
  W   = Caps.cWid c
  V   = Caps.cWid (frameStep j c)
  a   = sizeᵗ z
  M   = suc V
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  slW : SlotWid sl M
  slW = SlotWid-mono sl (s≤s (iterFold-infl S 2≤S j W))
                     (slotsCaps?-slotWid S W sl slC)

-- `μᵉ body` subscribes `unfoldμ body`, and BOTH AXES MOVE.  The size
-- axis was always going to: the unfolding is larger than the μ (only
-- syncSizeᵉ is preserved — syncSize-unfoldμ) by an amount no syntactic
-- measure in the file bounds.
--
-- THE WIDTH AXIS MOVES TOO, and the first draft of this said it did
-- not.  `dWᵉ (unfoldμ body) ≤ dWᵉ (μᵉ body)` reads plausible — the
-- plug lands at `varᵉ` positions and dWᵉ is 0 there — and it is
-- FALSE, refuted by Hop-Descent-Probe's μwide (0 ↦ 6).  hopD survives
-- an unfold because Δᵍ variables are reachable only under deferᵉ and
-- hopD CUTS a defer to 0; dW's whole reason to exist is that it does
-- NOT cut there, so the plug lands exactly where dW is looking and
-- exposes the μ's own outW — which dW does not bound.  Nor is it off
-- by a constant: k copies of the var in the template multiply through
-- innW's slope, so any true bound is affine in the plug's width with
-- the pmO/pmI coefficients, i.e. the hopD-subΘ machinery.
--
-- So the two axes are stated TOGETHER, at ONE existential j′ (which
-- is what the recursive call needs — both hypotheses at the same
-- level), and the width half is derived from the SIZE hypothesis the
-- telescope already carries rather than from the width one.  That is
-- affordable for the same reason the two frame postulates are:
-- iterFold is a tower in the cap and outW of an expression is a tower
-- in its size, so a large enough j′ covers it
unfoldμ-caps : ∀ {n} {Γ : Ctx n} {t} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵉ (μᵉ body) ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl (μᵉ body) ≤ Caps.cWid (frameStep j c) →
  Σ ℕ λ j′ → (sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + j′) c))
           × (dWᵉ n sl (unfoldμ body) ≤ Caps.cWid (frameStep (j + j′) c))
unfoldμ-caps c j sl body 2≤S slC szb wdb =
  (m + suc (m * m))
    , ≤-trans SZ (iterSize-mono-count S S 1≤S
                    (+-monoʳ-≤ j (m≤m+n m (suc (m * m)))))
    , expWid-fromSize c j m (m * m) sl 2≤S slC (unfoldμ body)
        (size-unfoldμ body)
  where
  S   = Caps.cSize c
  B   = Caps.cSize (frameStep j c)
  m   = sizeᵉ (μᵉ body)
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  -- QUADRATIC, AND ONE ROUND OF DOUBLING PER NODE CLEARS IT: unfolding
  -- plants the whole μ at each of the body's global-var positions
  -- (size-unfoldμ, the shared prerequisite in .Keeps-Ring), so the
  -- growth is the μ's size SQUARED — and iterSize at least doubles per
  -- fold (iterSize-2^), so the μ's OWN SIZE many folds cover the factor
  -- of m the squaring costs.  Both halves are counted in syntax: the
  -- unfolding IS syntax, so its width needs no cap read either
  quad : m * m ≤ iterSize S m B
  quad = ≤-trans (*-mono-≤ (<⇒≤ (n<2^n m)) szb) (iterSize-2^ S m B 1≤S)
  SZ : sizeᵉ (unfoldμ body) ≤ Caps.cSize (frameStep (j + m) c)
  SZ = ≤-trans (≤-trans (size-unfoldμ body) quad)
               (≤-reflexive (sym (iterSize-+ S j m S)))

------------------------------------------------------------------
-- subscribeE-caps, GROUND — the assembly knot, closed.
--
-- Thirteen clauses, and with the defer gap repaired they are all
-- instances of machinery that already exists:
--
--   input i          subscribeE-input-caps, whole
--   ofᵉ / emptyᵉ     a one-shot burst; the values off evalTms-caps
--   mapᵉ / takeᵉ /   subscribe the source under ONE more frame, then
--   scanᵉ            pushBurst — one j for the frame
--                    (frameStep-chain-suc), the receipts add
--   the four *All    subscribeAll-caps, whole; the initial node states
--                    are bounded by refl on both axes
--   μᵉ               one fuel, one unfolding, the two obligations above
--   varᵉ             impossible in a closed expression
--   deferᵉ           the clause the parked width exists for: install,
--                    mint, PARK, register.  One j for the registration,
--                    and the LiveSource's width bound IS the telescope's
--                    dW conjunct, since `dWᵉ (deferᵉ body)` is
--                    `pWᵉ body` exactly
------------------------------------------------------------------

-- SLOT: delegated whole
subscribeE-caps c j g (input i) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  subscribeE-input-caps c j g i κ bid now sl sched st 2≤S 1≤R slEq slC inv pC lC

-- LITERALS: one shot, and the payloads come off evalTms-caps.  The
-- state is untouched; only the source counter moves, which capsOK?
-- does not read
subscribeE-caps {n = n} {u = u} c j g (ofᵉ ts) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  j₀ , capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st
         (frameStep-⊑-+ c 2≤S j j₀) inv
     , ∧-intro (∧-intro refl
                  (all-++-intro (eventCaps? (frameStep (j + j₀) c) sl)
                     (map value (map (λ tm → evalTm tm) ts)) _
                     (mapValue-caps (frameStep (j + j₀) c) sl u
                        (map (λ tm → evalTm tm) ts) (proj₂ EV))
                     refl))
               refl
  where
  EV = evalTms-caps c j sl ts 2≤S slC (≤-trans (n≤1+n (sizeᵗˢ ts)) szb) wdb
  j₀ = proj₁ EV

subscribeE-caps {u = u} c j g emptyᵉ κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl

-- MAP: one more frame on the chain, so one j, then the burst comes back
-- through that same frame
subscribeE-caps {n = n} {t = t} {u = u} c j g (mapᵉ f b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₂ (proj₂ PBc)))
  where
  step⊑ = frameStep-mono-j c 2≤S (n≤1+n j)
  B′    = Caps.cSize (frameStep (suc j) c)
  szsum : sizeᵗ f + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum = ≤-trans (n≤1+n (sizeᵗ f + sizeᵉ b)) szb
  szf   = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵉ b)) szsum
  szb′  = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) szsum
  fS′ : frameSz? B′ (map-f f) ≡ true
  fS′ = T⇒≡true (sizeᵗ f ≤ᵇ B′) (≤⇒≤ᵇ (≤-trans szf (proj₁ step⊑)))
  pC′ : pathSz? B′ (map-f f ↠ κ) ≡ true
  pC′ = ∧-intro fS′
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  SUB = subscribeE-caps c (suc j) g b (map-f f ↠ κ) bid now sl sched st
          2≤S 1≤R slEq slC
          (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st step⊑ inv)
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl f) (dWᵉ n sl b)) (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₁  = proj₁ SUB
  res = subscribeE g b (map-f f ↠ κ) bid now sched st
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c (suc j + j₁) g bid now (map-f f) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (map-f f ↠ κ) bid now sched st)) slEq)
          slC (proj₁ (proj₂ SUB))
          (frameSz?-widen (map-f f) (proj₁ ⊑₁) fS′)
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₂ (proj₂ SUB))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (map-f f) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- TAKE: `take 0` never subscribes its source — a spent one-shot, exactly
-- emptyᵉ.  Otherwise a node is installed (trivially bounded on both
-- axes) and the source runs under one more frame
subscribeE-caps {n = n} {u = u} c j g (takeᵉ cnt b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC
  with evalTm cnt
... | zero =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl
... | suc k =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₂ (proj₂ PBc)))
  where
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid (take-st (suc k)) st
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B′     = Caps.cSize (frameStep (suc j) c)
  szsum : sizeᵗ cnt + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum = ≤-trans (n≤1+n (sizeᵗ cnt + sizeᵉ b)) szb
  szb′  = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ cnt)) szsum
  pC′ : pathSz? B′ (take-f nid ↠ κ) ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                   (pathSz?-⊑ κ step⊑ pC))
  inv₀ : capsOK? (frameStep (suc j) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc j) c) nid (take-st (suc k)) sched₀ st
           refl refl
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  SUB = subscribeE-caps c (suc j) g b (take-f nid ↠ κ) bid now sl sched₀ st₀
          2≤S 1≤R slEq slC inv₀
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl cnt) (dWᵉ n sl b))
                   (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₁  = proj₁ SUB
  res = subscribeE g b (take-f nid ↠ κ) bid now sched₀ st₀
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c (suc j + j₁) g bid now (take-f nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (take-f nid ↠ κ) bid now sched₀ st₀)) slEq)
          slC (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₂ (proj₂ SUB))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (take-f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- SCAN: the accumulator is BUILT, by evalTm, so the node's two bounds
-- come off evalSeed-caps and cost a receipt of their own before the
-- source is even subscribed
subscribeE-caps {n = n} {u = u} c j g (scanᵉ f z b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  j₀ + suc (j₁ + j₂)
    , frameStep-+assoc-caps c j j₀ (suc (j₁ + j₂))
        (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB))
        (subst (λ x → capsOK? (frameStep x c)
                        (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
               (sym (+-suc (j + j₀) (j₁ + j₂)))
               (frameStep-+assoc-caps c (suc (j + j₀)) j₁ j₂
                  (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc))))
    , frameStep-+assoc-burst c j j₀ (suc (j₁ + j₂)) sl (proj₁ PB)
        (subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
               (sym (+-suc (j + j₀) (j₁ + j₂)))
               (frameStep-+assoc-burst c (suc (j + j₀)) j₁ j₂ sl (proj₁ PB)
                  (proj₂ (proj₂ PBc))))
  where
  szsum : sizeᵗ f + sizeᵗ z + sizeᵉ b ≤ Caps.cSize (frameStep j c)
  szsum = ≤-trans (n≤1+n (sizeᵗ f + sizeᵗ z + sizeᵉ b)) szb
  szfz  = ≤-trans (m≤m+n (sizeᵗ f + sizeᵗ z) (sizeᵉ b)) szsum
  szf   = ≤-trans (m≤m+n (sizeᵗ f) (sizeᵗ z)) szfz
  szz   = ≤-trans (m≤n+m (sizeᵗ z) (sizeᵗ f)) szfz
  szb′  = ≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f + sizeᵗ z)) szsum
  SD = evalSeed-caps c j sl z 2≤S slC szz
         (≤-trans (m≤n⊔m (dWᵗ n sl f) (dWᵗ n sl z))
           (≤-trans (m≤m⊔n (dWᵗ n sl f ⊔ dWᵗ n sl z) (dWᵉ n sl b)) wdb))
  j₀    = proj₁ SD
  ⊑₀    = frameStep-⊑-+ c 2≤S j j₀
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid (scan-st (evalTm z)) st
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n (j + j₀))
  B′     = Caps.cSize (frameStep (suc (j + j₀)) c)
  VW = valCaps?-widen sl _ (evalTm z) step⊑ (proj₂ SD)
  pC′ : pathSz? B′ (scan-f f nid ↠ κ) ≡ true
  pC′ = ∧-intro (T⇒≡true (sizeᵗ f ≤ᵇ B′)
                  (≤⇒≤ᵇ (≤-trans szf (≤-trans (proj₁ ⊑₀) (proj₁ step⊑)))))
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                     (≤⇒≤ᵇ (≤-trans lC (≤-trans (proj₁ ⊑₀) (proj₁ step⊑)))))
                   (pathSz?-⊑ κ step⊑ (pathSz?-⊑ κ ⊑₀ pC)))
  inv₀ : capsOK? (frameStep (suc (j + j₀)) c) sched₀ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep (suc (j + j₀)) c) nid (scan-st (evalTm z))
           sched₀ st
           (valCaps?-size (frameStep (suc (j + j₀)) c) sl _ (evalTm z) VW)
           (subst (λ y → widNode (Caps.cWid (frameStep (suc (j + j₀)) c)) y
                           (scan-st (evalTm z)) ≡ true)
                  (sym slEq)
                  (valCaps?-wid (frameStep (suc (j + j₀)) c) sl _ (evalTm z) VW))
           (capsOK?-mono (frameStep j c) (frameStep (suc (j + j₀)) c) sched₀ st
              (⊑ᶜ-trans ⊑₀ step⊑)
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  SUB = subscribeE-caps c (suc (j + j₀)) g b (scan-f f nid ↠ κ) bid now sl
          sched₀ st₀ 2≤S 1≤R slEq slC inv₀
          (≤-trans szb′ (≤-trans (proj₁ ⊑₀) (proj₁ step⊑)))
          (≤-trans (m≤n⊔m (dWᵗ n sl f ⊔ dWᵗ n sl z) (dWᵉ n sl b))
             (≤-trans wdb (≤-trans (proj₁ (proj₂ ⊑₀)) (proj₁ (proj₂ step⊑)))))
          pC′
          (frameStep-chain-suc c (j + j₀) (pathLen κ) 2≤S
             (≤-trans lC (proj₁ ⊑₀)))
  j₁  = proj₁ SUB
  res = subscribeE g b (scan-f f nid ↠ κ) bid now sched₀ st₀
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc (j + j₀)) j₁
  PBc = pushBurst-caps c (suc (j + j₀) + j₁) g bid now (scan-f f nid) κ
          (proj₁ res) sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (scan-f f nid ↠ κ) bid now sched₀ st₀))
                 slEq)
          slC (proj₁ (proj₂ SUB))
          (frameSz?-widen (scan-f f nid) (proj₁ ⊑₁)
             (proj₁ (∧-true _ _ pC′)))
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ (pathSz?-⊑ κ ⊑₀ pC)))
          (≤-trans (≤-trans lC (≤-trans (proj₁ ⊑₀) (proj₁ step⊑))) (proj₁ ⊑₁))
          (proj₂ (proj₂ SUB))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (scan-f f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- THE FOUR *All HEADS: subscribeAll-caps, whole.  Every initial node
-- state is bounded on both axes by refl
subscribeE-caps {n = n} c j g (mergeAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  subscribeAll-caps c j g mergeᵒ (merge-st 0 false) b κ bid now sl sched st
    2≤S 1≤R slEq slC inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} {u = u} c j g (concatAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  subscribeAll-caps c j g concatᵒ (concat-st {t = u} [] false false) b κ bid now
    sl sched st 2≤S 1≤R slEq slC inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} c j g (switchAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  subscribeAll-caps c j g switchᵒ (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R slEq slC inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} c j g (exhaustAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  subscribeAll-caps c j g exhaustᵒ (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC

-- μ: out of gas is a dry close; with gas, ONE unfolding — larger than
-- the μ on the size axis (unfoldμ-size buys the room) and no larger on
-- the width axis (dW-unfoldμ)
subscribeE-caps {u = u} c j g0 (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (dryBurst {A = Val _ u} bid) ≡ true)
            (sym (+-identityʳ j)) refl
subscribeE-caps {n = n} c j (gs fuel) (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  j₀ + j₁
    , frameStep-+assoc-caps c j j₀ j₁ (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₀ j₁ sl (proj₁ res) (proj₂ (proj₂ IH))
  where
  US = unfoldμ-caps c j sl body 2≤S slC szb wdb
  j₀ = proj₁ US
  ⊑₀ = frameStep-⊑-+ c 2≤S j j₀
  IH = subscribeE-caps c (j + j₀) fuel (unfoldμ body) κ bid now sl sched st
         2≤S 1≤R slEq slC
         (capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st ⊑₀ inv)
         (proj₁ (proj₂ US))
         (proj₂ (proj₂ US))
         (pathSz?-⊑ κ ⊑₀ pC)
         (≤-trans lC (proj₁ ⊑₀))
  j₁ = proj₁ IH
  res = subscribeE fuel (unfoldμ body) κ bid now sched st

subscribeE-caps c j g (varᵉ ()) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC

-- DEFER: the clause the parked width exists for.  Install the merge
-- node, mint the source and ordinal, PARK the body as a one-element
-- pending, and register the thru-outer chain — one j, for the
-- registration.  The LiveSource's width bound IS the telescope's dW
-- conjunct: `dWᵉ (deferᵉ body)` is `pWᵉ body`, definitionally
subscribeE-caps {n = n} {Γ = Γ} {u = u} c j g (deferᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC inv szb wdb pC lC =
  1 , subst (λ x → capsOK? (frameStep x c) SCHED₄
                     (register SRC (thru-outer mergeᵒ nid ↠ κ) st₀) ≡ true)
            (sym (j+1 j))
            (capsOK?-addLive (frameStep (suc j) c) NEW SCHED₃
               (register SRC (thru-outer mergeᵒ nid ↠ κ) st₀) BL WL REG)
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (((init SRC ∷ []) at bid from SRC as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
  where
  nid    = Sched.nextNode sched
  SRC    = Sched.nextSource sched
  st₀    = installNode nid (merge-st 0 false) st
  SCHED₃ = record (record (record sched { nextNode = suc (Sched.nextNode sched) })
                          { nextSource = suc (Sched.nextSource sched) })
                  { nextOrdinal = suc (Sched.nextOrdinal sched) }
  NEW    = record { source = SRC ; ordinal = Sched.nextOrdinal sched
                  ; elemTy = obs u ; pending = (suc now , body) ∷ [] }
  SCHED₄ = record SCHED₃ { live = NEW ∷ Sched.live SCHED₃ }
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B      = Caps.cSize (frameStep j c)
  pC′ : pathSz? B (thru-outer mergeᵒ nid ↠ κ) ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B) (≤⇒≤ᵇ lC)) pC)
  inv₀ : capsOK? (frameStep j c) SCHED₃ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep j c) nid (merge-st 0 false) SCHED₃ st
           refl refl inv
  REG : capsOK? (frameStep (suc j) c) SCHED₃
          (register SRC (thru-outer mergeᵒ nid ↠ κ) st₀) ≡ true
  REG = register-caps c j SRC (thru-outer mergeᵒ nid ↠ κ) SCHED₃ st₀
          2≤S 1≤R inv₀ pC′
  BL : boundedLive (Caps.cSize (frameStep (suc j) c)) NEW ≡ true
  BL = ∧-intro (T⇒≡true (sizeᵉ body ≤ᵇ Caps.cSize (frameStep (suc j) c))
                 (≤⇒≤ᵇ (≤-trans (≤-trans (n≤1+n (sizeᵉ body)) szb) (proj₁ step⊑))))
               refl
  WL : widLive (Caps.cWid (frameStep (suc j) c)) (Sched.slots SCHED₃) NEW ≡ true
  WL = ∧-intro (subst (λ y → (pWᵛ n y (obs u) body
                                ≤ᵇ Caps.cWid (frameStep (suc j) c)) ≡ true)
                      (sym slEq)
                      (T⇒≡true (pWᵛ n sl (obs u) body
                                  ≤ᵇ Caps.cWid (frameStep (suc j) c))
                        (≤⇒≤ᵇ (≤-trans wdb (proj₁ (proj₂ step⊑))))))
               refl

------------------------------------------------------------------
-- THE DELIVERY CLIQUE, GROUND.  foldPath / dispatchShare / shareGo,
-- mutually recursive on the evaluator's own measure, plus chainStep as
-- the arrival's entry point.
--
-- WHERE THE RECEIPTS COME FROM, clause by clause:
--
--   root         j′ = 0.  Nothing steps; the emit is assembled from
--                bounds already in hand (mapValue-caps, finList-caps).
--   share-sink   j′ = dispatchShare's.  The chain's own handoff emit is
--                built at the ENTRY level and widened once.
--   f ↠ p        j′ = j₁ + j₂, one frame then the rest of the chain.
--                This is the additive composition the whole tree is
--                shaped around: the receipts add, they do not iterate,
--                and +-assoc is the only arithmetic (frameStep-+assoc
--                below).
--
-- Every hypothesis handed down is either already at the sub-call's
-- level or widened by frameStep-⊑-+, and every telescope obligation is
-- one `trans` against the slots corollary above.
------------------------------------------------------------------

foldPath-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
  (envSrc : Source) (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
  all (valCaps? (frameStep j c) sl u) vals ≡ true →
  all (eventCaps? (frameStep j c) sl) evs ≡ true →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

dispatchShare-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  all (valCaps? (frameStep j c) sl (lookup Γ i)) vals ≡ true →
  let r = dispatchShare {t = t} sf gas id now i vals fin sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

shareGo-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  all (λ rp → pathSz? (Caps.cSize (frameStep j c)) (proj₂ rp)) ps ≡ true →
  all (valCaps? (frameStep j c) sl (lookup Γ i)) vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

-- ROOT: the chain's sink.  Nothing steps, so j′ = 0 and the only work
-- is assembling one emit out of bounds already in hand
foldPath-caps c j sf gas id now envSrc root vals evs fin sl sched st
              2≤S 1≤R slEq slC inv pS vC eC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (((evs ++ map value vals
                            ++ (if fin then complete ∷ [] else []))
                        at id from envSrc as delivery) ∷ []) ≡ true)
            (sym (+-identityʳ j))
            (∧-intro (all-++-intro (eventCaps? (frameStep j c) sl) evs _ eC
                       (all-++-intro (eventCaps? (frameStep j c) sl)
                          (map value vals) _
                          (mapValue-caps (frameStep j c) sl _ vals vC)
                          (finList-caps (frameStep j c) sl fin)))
                     refl)

-- SHARE SINK: the chain emits its own (valueless) handoff and the share
-- fans out.  The handoff emit is built at the entry level and widened
-- to the fan-out's exit level exactly once
foldPath-caps c j sf gas id now envSrc (share-sink i) vals evs fin sl sched st
              2≤S 1≤R slEq slC inv pS vC eC =
  j₁ , proj₁ (proj₂ DS)
     , ∧-intro (all-++-intro (eventCaps? (frameStep (j + j₁) c) sl) evs _
                  (eventsCaps?-widen sl evs (frameStep-⊑-+ c 2≤S j j₁) eC)
                  refl)
               (proj₂ (proj₂ DS))
  where
  DS = dispatchShare-caps c j sf gas id now i vals fin sl sched st
         2≤S 1≤R slEq slC inv vC
  j₁ = proj₁ DS

-- ONE FRAME, THEN THE REST OF THE CHAIN.  j₁ pays the frame, j₂ the
-- tail, and the clause reports j₁ + j₂ — the additive composition,
-- rebracketed by +-assoc and nothing else
foldPath-caps c j sf gas id now envSrc (f ↠ p) vals evs fin sl sched st
              2≤S 1≤R slEq slC inv pS vC eC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl (proj₁ REST) (proj₂ (proj₂ IH))
  where
  B    = Caps.cSize (frameStep j c)
  pS1  = ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) pS
  pS2  = ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) (proj₂ pS1)
  SF   = stepFrame-caps c j sf id now f p vals fin sl sched st
           2≤S 1≤R slEq slC inv (proj₁ pS1) (proj₂ pS2)
           (≤ᵇ⇒≤ _ _ (T-to (proj₁ pS2))) vC
  j₁   = proj₁ SF
  step = stepFrame sf id now f p vals fin sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  IH   = foldPath-caps c (j + j₁) sf gas id now envSrc p
           (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step))) sl sd₁ st₁
           2≤S 1≤R
           (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))
                  slEq)
           slC
           (proj₁ (proj₂ SF))
           (pathSz?-⊑ p (frameStep-⊑-+ c 2≤S j j₁) (proj₂ pS2))
           (proj₁ (proj₂ (proj₂ SF)))
           (all-++-intro (eventCaps? (frameStep (j + j₁) c) sl) evs _
              (eventsCaps?-widen sl evs (frameStep-⊑-+ c 2≤S j j₁) eC)
              (proj₂ (proj₂ (proj₂ SF))))
  j₂   = proj₁ IH
  REST = foldPath sf gas id now envSrc p (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step))) sd₁ st₁

-- DISPATCH: latch first (a completing def closes before it delivers),
-- fan out, then finish.  The dispatch gas is the telescope bound and
-- never runs out on a real run, so the zero clause is the evaluator's
-- own unreachable branch
dispatchShare-caps {t = t} c j sf zero id now i vals fin sl sched st
                   2≤S 1≤R slEq slC inv vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
dispatchShare-caps c j sf (suc gas) id now i vals fin sl sched st 2≤S 1≤R slEq slC inv vC =
  j₁ , proj₁ FIN , proj₂ FIN
  where
  st₀ = shareLatch i fin st
  GO  = shareGo-caps c j sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sl sched st₀
          2≤S 1≤R slEq slC (shareLatch-caps (frameStep j c) i fin sched st inv)
          (shareAdmit-caps (Caps.cSize (frameStep j c)) i (EvalSt.registry st)
             (capsOK?-regs (frameStep j c) sched st inv))
          vC
  j₁  = proj₁ GO
  out = shareGo sf gas id now i vals fin (shareAdmit i (EvalSt.registry st))
          sched st₀
  FIN = shareFinish-caps (frameStep (j + j₁) c) i fin sl out
          (proj₁ (proj₂ GO)) (proj₂ (proj₂ GO))

-- FAN-OUT: one registration at a time.  A cancelled chain delivers
-- nothing and costs nothing; a survivor folds, and the two receipts add
shareGo-caps {t = t} c j sf gas id now i vals fin [] sl sched st
             2≤S 1≤R slEq slC inv pS vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
shareGo-caps {Γ = Γ} c j sf gas id now i vals fin ((rid , p) ∷ ps) sl sched st
             2≤S 1≤R slEq slC inv pS vC
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-caps c j sf gas id now i vals fin ps sl sched st
                2≤S 1≤R slEq slC inv (proj₂ (∧-true _ _ pS)) vC
... | false =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl (proj₁ FP ++ proj₁ REST)
        (burstCaps?-++ (frameStep ((j + j₁) + j₂) c) sl (proj₁ FP) (proj₁ REST)
           (burstCaps?-widen sl (proj₁ FP)
              (frameStep-⊑-+ c 2≤S (j + j₁) j₂) (proj₂ (proj₂ HD)))
           (proj₂ (proj₂ IH)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  cl  = if fin then close (toℕ i) exhausted ∷ [] else []
  HD  = foldPath-caps c j sf gas id now (toℕ i) p vals cl fin sl sched st₀
          2≤S 1≤R slEq slC (capsOK?-delivered (frameStep j c) rid sched st inv)
          (proj₁ (∧-true _ _ pS)) vC
          (closeList-caps (frameStep j c) sl (toℕ i) fin)
  j₁  = proj₁ HD
  FP  = foldPath sf gas id now (toℕ i) p vals cl fin sched st₀
  IH  = shareGo-caps c (j + j₁) sf gas id now i vals fin ps sl
          (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
          2≤S 1≤R
          (trans (foldPath-slots sf gas id now (toℕ i) p vals cl fin sched st₀)
                 slEq)
          slC
          (proj₁ (proj₂ HD))
          (pathsSz?-⊑ ps (frameStep-⊑-+ c 2≤S j j₁) (proj₂ (∧-true _ _ pS)))
          (valsCaps?-widen sl (lookup Γ i) vals (frameStep-⊑-+ c 2≤S j j₁) vC)
  j₂  = proj₁ IH
  REST = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))

-- one arrival into one chain: foldPath seeded with the payload, the
-- source's close if it is spent, and the completion flag
chainStep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
  valCaps? (frameStep j c) sl (arrTy a) (arrVal a) ≡ true →
  let r = chainStep id a path sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
chainStep-caps {n = n} {e = e} c j id a path sl sched st 2≤S 1≤R slEq slC inv pS vC =
  foldPath-caps c j (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sl sched st
    2≤S 1≤R slEq slC inv pS (∧-intro vC refl)
    (closeList-caps (frameStep j c) sl (arrSource a) (Arrival.isLast a))

------------------------------------------------------------------
-- THE CASCADE BOOKENDS AND THE CHAIN SNAPSHOT, ground.  Nothing here
-- is a caps argument: latching resets per-cascade scratch capsOK? does
-- not read, finishing is the same drop-and-sweep the share's finish is,
-- and the snapshot is a filter of the registry.
------------------------------------------------------------------

-- the latch resets delivered/cancelled/regWatermark/dying and may add
-- to completedSources — none of the five conjuncts sees any of them
cascadeLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (cascadeLatch a st) ≡ true
cascadeLatch-caps c a sched st h with Arrival.isLast a
... | true  = h
... | false = h

cascadeFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  let r = cascadeFinish a sched st
  in capsOK? c (proj₁ r) (proj₂ r) ≡ true
cascadeFinish-caps c a sched st h with Arrival.isLast a
... | false = h
... | true  = dropSweep-caps c (arrSource a) sched st h

-- the snapshot is chainsGo's filter: source matches and the chain's
-- element type is the arrival's.  Same shape as shareAdmit's
chainsGo-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsGo a rs) ≡ true
chainsGo-caps B a [] h = refl
chainsGo-caps B a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (chainsGo-caps B a r (proj₂ (∧-true _ _ h)))

chainsOf-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
  regsSz? B (EvalSt.registry st) ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsOf a st) ≡ true
chainsOf-caps B a st = chainsGo-caps B a (EvalSt.registry st)

chainsGo-length : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  length (chainsGo a rs) ≤ length rs
chainsGo-length a [] = z≤n
chainsGo-length a ((rid , s , (u , p)) ∷ r)
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | no  _    = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | yes refl = s≤s (chainsGo-length a r)

chainsOf-length : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  length (chainsOf a st) ≤ length (EvalSt.registry st)
chainsOf-length a st = chainsGo-length a (EvalSt.registry st)

caps-tick : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  let r = cascade a nextId sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-tick {e = e} sl id a nextId sched st slEq pre val =
  cascadeFinish-caps (capsAt e sl (suc id)) a (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
    (capsOK?-mono (frameStep j c) (capsAt e sl (suc id))
                  (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
                  (frameStep-mono-j c (2≤capsAt-size e sl id) jFits)
                  (proj₂ (proj₂ GO)))
  where
  c    = capsAt e sl id
  st₀  = cascadeLatch a st
  GO   = cascadeGo-caps c a nextId (chainsOf a st) sl sched st₀
           (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)
           (slotsCaps?-capsAt e sl id) slEq
           (cascadeLatch-caps c a sched st pre) val
           (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
           (n≤capsAt-size e sl id)
           (≤-trans (chainsOf-length a st) (capsOK?-count c sched st pre))
  GOr   = cascadeGo a nextId (chainsOf a st) sched st₀
  j     = proj₁ GO
  jFits = proj₁ (proj₂ GO)

------------------------------------------------------------------
-- REFUTED: caps-frame AS STATED IS FALSE, TWICE OVER.  Both halves are
-- statement-level — the face is uninstantiable, not merely unproven —
-- and the same disease class as the original vacuity.
--
-- (1) THE BOUNDARY FOLD.  caps-frame's hypothesis admits a state
-- satisfying capsOK? with ZERO slack and a `b` whose size is exactly the
-- level's cSize, and demands capsOK? at the SAME level afterwards.  But
-- the subscribe frame itself folds: subscribeE's scanᵉ clause
-- (Rx/Evaluator.agda:958) installs `scan-st (evalTm seed)` and runs the
-- source's sync burst through pushBurst with the scan-f frame, and
-- dispatch updates that node once per synchronous payload.  A cap-sized
-- `b` with one duplicating fold therefore lands at sizeStep C C, above
-- C — and the arithmetic below is uniform in C, so specialising C to
-- capsAt's own tower does not escape it.
--
-- State-Blowup-Probe's framePreserves-absurd is the concrete witness:
-- pRs, whose size is 19 and whose initial state is bounded by 19, leaves
-- a size-30 node after its own root subscribe.  (The root subscribe is
-- one of caps-frame's own instances: κ = root, id = 0, level 0.)
--
-- (2) THE MID-CASCADE HYPOTHESIS, an independent defect.  caps-tick says
-- a whole cascade moves the state from level id to level suc id, so
-- mid-drain states live strictly BETWEEN the two levels.  A proof of
-- caps-tick must apply caps-frame at every inner subscribe inside that
-- cascade, and there are exactly two such call sites:
--
--   · subscribeInner   (Rx/Evaluator.agda:531) — a *All consuming an
--     obs payload mid-cascade, reached from stepFrame
--   · sharedConnect    (Rx/Evaluator.agda:871) — a shared slot's lazy
--     connect, which subscribes the def mid-cascade
--
-- At both, earlier chains in the SAME cascade have already grown the
-- store, so the level-id hypothesis is simply unavailable.  Even had (1)
-- survived, the face could not feed the induction it exists for.
--
-- THE REPAIR SHAPE UNDER EVALUATION (not yet taken on faith — it owes
-- its own probe): make the mid-instant states explicit with a
-- CONSUMED-ITERATION index.  One parametric face against level suc id
-- whose pre-state is bounded by frameBlowup partially applied — k of the
-- 2 ^ cReg * cSize iterations still unspent — and a subscribeE with fold
-- count j consuming j of k.  caps-frame and caps-tick then become the
-- two ENDPOINTS (k = full, k = 0) of a single face rather than siblings,
-- and (2) dissolves because a mid-cascade state is just a smaller k.
--
-- AND THE THING TO CHECK BEFORE BUILDING IT: this is structurally the
-- same bookkeeping the walk face's E′ receipt already does.  Two
-- parallel accounting mechanisms for one growth is a smell; if E′ can
-- carry the iteration count, caps preservation falls out of the walk
-- face instead of standing beside it as a second ledger.
------------------------------------------------------------------

-- the arithmetic obstruction behind (1), UNIFORM IN C: one fold from a
-- cap-sized value on a cap-sized step function always overflows the cap,
-- whatever the cap is.  This is why no choice of level rescues
-- same-level preservation
caps-frame-boundary-absurd : ∀ (C : ℕ) → 1 ≤ C → sizeStep C C ≤ C → ⊥
caps-frame-boundary-absurd C hC h = <-irrefl refl (<-≤-trans C<step h)
  where
  1≤2C : 1 ≤ 2 * C
  1≤2C = ≤-trans hC (m≤m+n C (C + 0))

  0<prod : 0 < C * (2 * C)
  0<prod = *-mono-≤ hC 1≤2C

  C<step : C < sizeStep C C
  C<step = subst (C <_) (sym (*-suc C (2 * C)))
                 (subst (_< C + C * (2 * C)) (+-identityʳ C)
                        (+-monoʳ-< C 0<prod))

------------------------------------------------------------------
-- WHAT WAS HERE, AND WHY IT IS GONE (2026-08-01).  regsSz?-subscribeE,
-- "the chain half of ANY repaired face" — a fixed cap C, a registry
-- bounded by it, an expression of size ≤ C subscribed under a κ with
-- `pathSz? C κ` and `suc (pathLen κ) ≤ C`, concluding the registry is
-- still bounded by C.
--
-- IT IS FALSE, and agda/probe/Chain-Half-Probe.agda computes the
-- counterexample: at C = 5, a κ of four map-f frames (both hypotheses
-- TIGHT) and `mapᵉ f (mapᵉ f (input 0))` (sizeᵉ exactly 5) register a
-- chain of length SIX.  subscribeE pushes one frame per shell of what
-- it walks, and `suc (pathLen κ) ≤ C` buys room for exactly one.
--
-- The defect is the FIXED cap, not the descent.  subscribeE-caps
-- carries the identical two hypotheses and is GROUND, because it
-- reports at `frameStep (j + j′) c` and one j at least doubles cSize
-- (frameStep-size-suc) — so the frame a hop pushes is paid for by the
-- j that hop spends.  A statement with no j has nothing to pay with,
-- and no repair of its hypotheses helps: the joint form
-- `pathLen κ + sizeᵉ b ≤ C` that would make it inductive is the one
-- Joint-Probe refuted at the tight admissible cSize, and it would in
-- any case not survive an *All hop, where the chain grows by the
-- SHELLS OF A PAYLOAD rather than of the syntax.
--
-- AND IT WAS REDUNDANT.  `capsOK?`'s second conjunct IS `regsSz?`, so
-- the ground subscribeE-caps already hands the chain half back at the
-- level it reports.  The postulate had no consumer in the tree.
------------------------------------------------------------------

------------------------------------------------------------------
-- WHAT WAS HERE, AND WHY IT IS GONE.  A fixed-height reach cap —
-- foldBudget, reachCap, reach-covers — built on the measured claim that
-- a reachable observable's tower has its HEIGHT fixed by the syntax and
-- only its BASE growing with the instant count.
--
-- deepScan refuted it: a scan whose step function contains a scan over
-- the accumulator towers ONCE PER FOLD, and folds grow one per instant,
-- so the height grows with `id`.  The machine-checked account, with the
-- recurrence and the payload counts, is the deepScan section of
-- agda/probe/Frame-Work-Probe.agda.  The Caps recurrence above is the
-- replacement; git history is the archive for the rest.
------------------------------------------------------------------

-- WHY cSize AND cWid ARE SEPARATE FIELDS, machine-checked so that nobody
-- collapses them.  The tempting move is to carry size only and derive
-- width from it — the way hopD-sizeᵉ derives hop depth from szB of size,
-- which is exactly why cHop is NOT a field.  THAT ROUTE IS CIRCULAR for
-- width.  outW is not polynomial in size: pWᵉ (mergeAllᵉ e)
-- is pWᵉ e * innWᵉ e and innWᵉ towers at a scanᵉ, so any size-to-width
-- bound is at least exponential, and the cap would have to dominate an
-- exponential of itself.
--
-- The non-circular route is to iterate them TOGETHER, which is what the
-- Caps recurrence does: one instant's folds are counted by the current
-- width and each fold costs one foldStep, so the next width comes from
-- the current width and the current cascade count — never from the size.
--
-- This is the fourth time this loop has been available in this proof
-- (walk-hyps-absurd, hop-anchor-absurd, round3b-ledger-reset-absurd, and
-- now here), so it gets a witness rather than a warning
reach-via-size-absurd : ∀ (C : ℕ) → 2 ^ C ≤ C → ⊥
reach-via-size-absurd C h = <-irrefl refl (<-≤-trans (n<2^n C) h)

-- THE WIRING, proven rather than postulated: a value inside the cap
-- discharges BOTH of the walk's reset obligations at once.  This is what
-- makes the cluster one object instead of three coincidences, and it is
-- why F needs no separate justification — it is Ŝ
reach-resets : ∀ (C : ℕ) → 2 ≤ C →
  ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u} (o : Exp Γ Δᵍ Δ Θ u) → sizeᵉ o ≤ C →
  (syncSizeᵉ o ≤ C) × (hopDᵉ C o ≤ hopR C)
reach-resets C hC o h = ≤-trans (syncSize≤sizeᵉ o) h , hopD-cap C o hC h

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.
