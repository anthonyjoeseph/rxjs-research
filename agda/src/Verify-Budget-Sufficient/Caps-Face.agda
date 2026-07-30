-- STRATUM 2a of Verify-Budget-Sufficient: THE CAPS FACE (round 4).
--
-- The per-instant cap recurrence and everything stated in terms of it:
-- the Caps triple, the state predicate capsOK?, the in-flight predicates
-- (valCaps? / eventCaps? / burstCaps? / obsCaps?), the step functions
-- (sizeStep / foldStep / iterSize / iterFold / frameStep / frameBlowup)
-- with their monotonicity toolkit, the caps face itself
-- (subscribeE-caps, regsSz?-subscribeE) and the companion tree it is
-- decomposed into, caps-tick DERIVED from the cascade companions, and
-- the reachability cluster (reach-resets) that pays round 3's debt.
--
-- THE ROUND-5 GATE IS STILL THE TYPE.  frameBlowup : Caps → Caps cannot
-- read the ledger, the receipt, or E, because they are not arguments.
--
-- This module is a SIBLING of .Wet, not a layer over it: the wet family
-- never mentions Caps (checked), so the two are independent extensions
-- of .Measures and an edit here does not re-check the wet family.
--
-- Named Caps-Face rather than Caps so the module name cannot shadow the
-- record it defines.  It sits over .Keeps-Ring, whose slotsEq is what
-- transports a width bound across a sub-call (valCaps? and its relatives
-- read Sched.slots, and the caller reports at the callee's post sched).
module Verify-Budget-Sufficient.Caps-Face where

open import Data.Bool    using (Bool; true; false; T; _∧_; _∨_; not;
                                if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _<_;
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
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
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
                                dropSource; arrSource; chainsOf; cascadeGo;
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
                                foldPath; dispatchShare; arrTick;
                                aliveThroughᶠ;
                                cascade; drain; evaluate;
                                hasDry; dryEvent; sameSource;
                                budgetAt; slotsSize)

open import Verify-Budget-Sufficient.Keeps-Ring public

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

------------------------------------------------------------------
-- ROUND 4: PER-INSTANT CAPS, BY RECURRENCE ON THE INSTANT.
--
-- deepScan killed the fixed-height cap (see the refutation below).  What
-- replaces it is NOT a bigger closed formula — it is a recurrence:
--
--     Caps 0        = the entry measure (program + slot telescope)
--     Caps (suc id) = frameBlowup (Caps id)
--
-- with frameBlowup the worst one instant's cascades can do to a state
-- already inside a given cap.  deepScan itself says what that has to
-- cover: within a frame, fold counts are bounded by current WIDTHS, and
-- each fold adds a tower level, so frameBlowup is a tower of height ~its
-- argument and Caps is Ackermann-flavoured in id.  That is acceptable —
-- it is computable, and it is entry-determined GIVEN id, which was
-- always a budget parameter (sizeBudgetAt already takes it).
--
-- WHY THE OLD PRESERVABILITY OBJECTION DOES NOT APPLY.  The fixed-height
-- shape was justified by "an invariant whose height climbs per instant
-- cannot be preserved by a per-frame induction".  That conflated frame
-- crossings with TICK crossings.  Within one frame `id` is FROZEN: every
-- hop, connect and μ edge of a single walk happens at one instant, so
-- the walk face takes its caps as ordinary fixed numbers however they
-- depend on id.  The height climbs only at tick boundaries — which is
-- exactly where the top-level per-instant induction hands over anyway.
-- That is why the face below has TWO halves and only one of them moves.
--
-- THE ROUND-5 GATE IS THE TYPE.  `frameBlowup : Caps → Caps` cannot read
-- the ledger, the receipt, or E, because they are not arguments.  If any
-- within-frame quantity turns out to be boundable ONLY by the ledger,
-- round3b-ledger-reset-absurd fires again and that is a stop-and-report,
-- not a signature to widen.
--
-- THE TUPLE, and why hop rank is not in it: cSize and cWid are
-- independent — reach-via-size-absurd shows width cannot be derived from
-- size — and cReg counts the cascades whose blowups compose within one
-- instant.  Hop rank IS derivable, from cSize by hopD-cap, which is what
-- reach-resets proves; carrying it would be a synonym.
------------------------------------------------------------------

record Caps : Set where
  constructor caps
  field
    cSize : ℕ      -- every reachable value's size
    cWid  : ℕ      -- every reachable observable's FRAME width
    cReg  : ℕ      -- live registrations, hence cascades, in one instant

-- the frame-width half of the state predicate.  NOT widthOK? — that is
-- ofW, a per-NODE width, and om-is-not-a-frame-budget is the
-- counterexample to conflating the two
widLive : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → LiveSource Γ → Bool
widLive {n = n} W sl l =
  all (λ tv → outWᵛ n sl (LiveSource.elemTy l) (proj₂ tv) ≤ᵇ W)
      (LiveSource.pending l)

widNode : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → NodeState Γ → Bool
widNode {n = n} W sl (scan-st {t} v)   = outWᵛ n sl t v ≤ᵇ W
widNode {n = n} W sl (concat-st q _ _) = all (λ o → outWᵉ n sl o ≤ᵇ W) q
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
-- top-level (not a where block) so regsSz?-subscribeE below can name
-- pathSz? in its hypothesis: the continuation κ a subscribe walks under
-- must already be size-bounded, or a huge step function in κ would be
-- registered at the leaf.  This is the honest form — the naive lemma
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

-- ONE FOLD's worst case on a width — AND WHY IT READS THE SIZE.
--
-- The earlier `2 ^ suc w` was gated against deepScan's PAYLOAD count and
-- is refuted against the quantity capsOK? actually bounds: one fold
-- takes deepScan's stored width 1 ↦ 6 where it allowed 4
-- (State-Blowup-Probe).  The reason is structural — `innWᵉ (scanᵉ f z e)`
-- puts the source's width in an EXPONENT whose base is read off the step
-- function's syntax — so the per-fold multiplier is a property of `f`,
-- and cSize is the only thing in Caps that bounds a step function.
--
-- Note this is a strict GENERALISATION: at S = 2 it is exactly the old
-- step, so Frame-Work-Probe's 2 / 6 / 126 gates still read as before
foldStep : ℕ → ℕ → ℕ
foldStep S w = S ^ suc w

iterFold : ℕ → ℕ → ℕ → ℕ
iterFold S zero    w = w
iterFold S (suc k) w = iterFold S k (foldStep S w)

-- ONE FOLD's worst case on a SIZE, straight off size-subΘᵉ: a fold
-- substitutes the accumulator into the step function, and
-- size-subΘᵉ bounds that by `sizeᵉ f * suc (2 * V)` with V the env cap.
-- Both `sizeᵉ f` and V are ≤ cSize, hence S in both positions
sizeStep : ℕ → ℕ → ℕ
sizeStep S s = S * suc (2 * s)

iterSize : ℕ → ℕ → ℕ → ℕ
iterSize S zero    s = s
iterSize S (suc k) s = iterSize S k (sizeStep S s)

-- THE WORST ONE INSTANT CAN DO, and a function of Caps ALONE — the
-- signature is the round-5 gate, not a comment about one.
--
-- All three components share ONE iteration count, `cWid * cReg * cSize`:
-- folds per cascade are bounded by the current width, cascades in an
-- instant by the registration count, and the frames one payload crosses
-- inside a cascade by the chain-length conjunct of pathSz? (the
-- j-budget probe; the count without that third factor is refuted by
-- tickFits-absurd).  The cWid factor is why sizeBlowup must read
-- cWid — pR and pRs have identical step functions and differ only in
-- how many times it runs per frame, 3 ↦ 12 against 3 ↦ 30, so a fixed
-- number of size steps undershoots one of them (State-Blowup-Probe).
--
-- regBlowup is ADDITIVE in the sources, not multiplicative: pR2's two
-- live inputs take the registry 1 ↦ 3, one new registration per
-- referenced source, because a fold subscribes each reference once.  Its
-- cSize factor is exactly that reference count — a fold can subscribe no
-- more references than its step function mentions — and pR2 is why it is
-- there: with `cReg * suc cWid` alone the measured 1 ↦ 3 does not fit
-- j FOLDS' WORTH, so a frame's PROGRESS is explicit rather than
-- all-or-nothing.  This is the repair caps-frame's refutation forces:
-- same-level preservation is false, so the face must report growth, and
-- the honest index of growth inside a frame is the fold count.
--
-- The two endpoints are exactly what caps-frame and caps-tick were each
-- trying to be on their own — j = 0 is frame entry, j = the full count is
-- the tick boundary — so they stop being siblings and become the ends of
-- one measure.  A mid-cascade state, which had no level at all before,
-- is just a smaller j
frameStep : ℕ → Caps → Caps
frameStep j c =
  caps (iterSize (Caps.cSize c) j (Caps.cSize c))
       (iterFold (Caps.cSize c) j (Caps.cWid c))
       (Caps.cReg c * suc (j * Caps.cSize c))

-- THE COUNT, and its third factor.  `cWid * cReg` was refuted outright:
-- J-Budget-Probe's pM family fixes the whole triple at (7, 1, 1) and
-- still stores 15 … 4371 in one cascade, so no count read off the triple
-- can work until the triple bounds the CHAIN LENGTH — which is what
-- pathSz?'s pathLen conjunct now does.  With that, the three factors are
-- exactly the three dimensions of one cascade's event count:
--
--     emissions (cWid)  ×  chains (cReg)  ×  chain length (cSize)
--
-- The third reads cSize because that is where the length conjunct puts
-- it, not because a length is a size: `pathLen p ≤ᵇ cSize` is a separate
-- conjunct of the same field, and at pM 6 the two genuinely differ (a
-- 9-frame chain in a state whose largest term measures 7)
frameBlowup : Caps → Caps
frameBlowup c = frameStep (Caps.cWid c * Caps.cReg c * Caps.cSize c) c

-- the entry endpoint, by computation
frameStep-0 : ∀ (c : Caps) → frameStep 0 c ≡ c
frameStep-0 (caps s w r) = cong (λ x → caps s w x) (*-identityʳ r)

------------------------------------------------------------------
-- THE ARITHMETIC CORE OF THE REPAIR, proven ahead of subscribeE-caps
-- because it is the piece that would kill the shape if it failed: does
-- frameStep's per-j increment DOMINATE one fold applied to frameStep j?
-- The induction consumes exactly this at every clause.  All three
-- dimensions reduce to "iterating a fixed step commutes", iter-f (suc j)
-- = f (iter-f j), because sizeStep S / foldStep S apply the SAME S each
-- time — the whole reason S is read off cSize once rather than per fold.
------------------------------------------------------------------

-- SIZE.  iterSize S j is the j-fold composition of (sizeStep S), so one
-- more step at the OUTSIDE equals one more at the inside
iterSize-suc : ∀ (S j s : ℕ) → iterSize S (suc j) s ≡ sizeStep S (iterSize S j s)
iterSize-suc S zero    s = refl
iterSize-suc S (suc j) s = iterSize-suc S j (sizeStep S s)

-- so a size-step on the state at frameStep j lands within frameStep (suc j)
frameStep-size-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cSize (frameStep (suc j) c) ≡ sizeStep (Caps.cSize c) (Caps.cSize (frameStep j c))
frameStep-size-suc c j = iterSize-suc (Caps.cSize c) j (Caps.cSize c)

-- WIDTH.  identically for foldStep
iterFold-suc : ∀ (S j w : ℕ) → iterFold S (suc j) w ≡ foldStep S (iterFold S j w)
iterFold-suc S zero    w = refl
iterFold-suc S (suc j) w = iterFold-suc S j (foldStep S w)

frameStep-wid-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cWid (frameStep (suc j) c) ≡ foldStep (Caps.cSize c) (Caps.cWid (frameStep j c))
frameStep-wid-suc c j = iterFold-suc (Caps.cSize c) j (Caps.cWid c)

-- REGISTRATIONS.  the cReg dimension is linear in j, so one more j buys
-- exactly cReg * cSize more headroom — enough for the registrations one
-- fold mints, which is at most the step function's reference count ≤ cSize
frameStep-reg-suc : ∀ (c : Caps) (j : ℕ) →
  Caps.cReg (frameStep j c) + Caps.cReg c * Caps.cSize c
    ≡ Caps.cReg (frameStep (suc j) c)
frameStep-reg-suc (caps s w r) j =
  begin
    r * suc (j * s) + r * s
  ≡⟨ cong (_+ r * s) (*-suc r (j * s)) ⟩
    (r + r * (j * s)) + r * s
  ≡⟨ +-assoc r (r * (j * s)) (r * s) ⟩
    r + (r * (j * s) + r * s)
  ≡⟨ cong (r +_) (sym (*-distribˡ-+ r (j * s) s)) ⟩
    r + r * (j * s + s)
  ≡⟨ cong (λ x → r + r * x) (+-comm (j * s) s) ⟩
    r + r * (suc j * s)
  ≡⟨ sym (*-suc r (suc j * s)) ⟩
    r * suc (suc j * s)
  ∎
  where open ≡-Reasoning

-- BY RECURRENCE, never in closed form.
--
-- THE BASE CASE PAYS FOR ITS OWN FRAME.  The root subscribe IS a frame:
-- a synchronous source folds inside it, so the state handed to instant 0
-- has already grown.  pRs ends its root frame at size 30 where the bare
-- syntactic measure allows 25 (State-Blowup-Probe), so the base is one
-- frameBlowup above the syntax — exactly what caps-frame already says
-- about every other frame
capsAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → (id : ℕ) → Caps
capsAt {n = n} e sl zero =
  frameBlowup (caps (2 + sizeᵉ e + slotsSize sl)
                    (suc (outWᵉ n sl e))
                    (suc (sizeᵉ e + slotsSize sl)))
capsAt e sl (suc id) = frameBlowup (capsAt e sl id)

------------------------------------------------------------------
-- capsOK? IS MONOTONE IN THE CAPS.  The widening the induction performs
-- everywhere: a subscribe reports growth frameStep j ↦ frameStep (j+j′),
-- and capsOK? at the smaller caps must weaken to the larger.  Each
-- conjunct is a `≤ᵇ` bound weakened through `all-impl`, exactly as the
-- walk face's pathB?-widen does for its own predicate.
------------------------------------------------------------------

-- caps ordering: pointwise on the three fields
_⊑ᶜ_ : Caps → Caps → Set
c ⊑ᶜ c′ = (Caps.cSize c ≤ Caps.cSize c′)
        × (Caps.cWid  c ≤ Caps.cWid  c′)
        × (Caps.cReg  c ≤ Caps.cReg  c′)

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
  all-impl _ _ (λ tv → ≤ᵇ-widen (outWᵛ n sl (LiveSource.elemTy l) (proj₂ tv)) le)
           (LiveSource.pending l)

widNode-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (ns : NodeState Γ) {W W′ : ℕ} →
  W ≤ W′ → widNode W sl ns ≡ true → widNode W′ sl ns ≡ true
widNode-widen {n = n} sl (scan-st {t} v)   le h = ≤ᵇ-widen (outWᵛ n sl t v) le h
widNode-widen {n = n} sl (concat-st q _ _) le h =
  all-impl _ _ (λ o → ≤ᵇ-widen (outWᵉ n sl o) le) q h
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
-- frameStep IS MONOTONE IN j — the last toolkit piece.  The induction
-- lifts a sub-result at frameStep (j + a) to frameStep (j + b) for
-- a ≤ b (via capsOK?-mono), which needs frameStep j c ⊑ᶜ frameStep j′ c
-- for j ≤ j′.  Each iterated component is inflationary because its step
-- is: sizeStep needs 1 ≤ S, foldStep needs 2 ≤ S — and cSize (which is
-- S) is ≥ 2 for every real cap (the base is 2 + sizeᵉ + …).
------------------------------------------------------------------

-- SIZE: sizeStep is inflationary for S ≥ 1, and iterating it only grows
s≤2s : ∀ (s : ℕ) → s ≤ 2 * s
s≤2s s = m≤m+n s (s + 0)

sizeStep-infl : ∀ (S s : ℕ) → 1 ≤ S → s ≤ sizeStep S s
sizeStep-infl S s hS =
  ≤-trans (≤-trans (s≤2s s) (n≤1+n (2 * s)))
          (≤-trans (≤-reflexive (sym (*-identityˡ (suc (2 * s)))))
                   (*-monoˡ-≤ (suc (2 * s)) hS))
  -- 1 * suc(2s) is definitionally suc(2s), so *-identityˡ closes the gap

iterSize-infl : ∀ (S : ℕ) → 1 ≤ S → ∀ (k s : ℕ) → s ≤ iterSize S k s
iterSize-infl S hS zero    s = ≤-refl
iterSize-infl S hS (suc k) s =
  ≤-trans (sizeStep-infl S s hS) (iterSize-infl S hS k (sizeStep S s))

iterSize-mono-count : ∀ (S s : ℕ) → 1 ≤ S → ∀ {j j′ : ℕ} → j ≤ j′ →
  iterSize S j s ≤ iterSize S j′ s
iterSize-mono-count S s hS {j′ = j′} z≤n      = iterSize-infl S hS j′ s
iterSize-mono-count S s hS           (s≤s le)  = iterSize-mono-count S (sizeStep S s) hS le

-- WIDTH: foldStep is inflationary for S ≥ 2 (w < 2^w ≤ 2^(1+w) ≤ S^(1+w))
foldStep-infl : ∀ (S w : ℕ) → 2 ≤ S → w ≤ foldStep S w
foldStep-infl S w hS =
  ≤-trans (<⇒≤ (n<2^n w))
          (≤-trans (^-monoʳ-≤ 2 (n≤1+n w))    -- 2^w ≤ 2^(suc w)
                   (^-monoˡ-≤ (suc w) hS))     -- 2^(suc w) ≤ S^(suc w)

iterFold-infl : ∀ (S : ℕ) → 2 ≤ S → ∀ (k w : ℕ) → w ≤ iterFold S k w
iterFold-infl S hS zero    w = ≤-refl
iterFold-infl S hS (suc k) w =
  ≤-trans (foldStep-infl S w hS) (iterFold-infl S hS k (foldStep S w))

iterFold-mono-count : ∀ (S w : ℕ) → 2 ≤ S → ∀ {j j′ : ℕ} → j ≤ j′ →
  iterFold S j w ≤ iterFold S j′ w
iterFold-mono-count S w hS {j′ = j′} z≤n      = iterFold-infl S hS j′ w
iterFold-mono-count S w hS           (s≤s le)  = iterFold-mono-count S (foldStep S w) hS le

-- REG: linear, monotone in j always
frameStep-reg-mono : ∀ (c : Caps) {j j′ : ℕ} → j ≤ j′ →
  Caps.cReg (frameStep j c) ≤ Caps.cReg (frameStep j′ c)
frameStep-reg-mono (caps s w r) le =
  *-monoʳ-≤ r (s≤s (*-monoˡ-≤ s le))

frameStep-mono-j : ∀ (c : Caps) → 2 ≤ Caps.cSize c → ∀ {j j′ : ℕ} → j ≤ j′ →
  frameStep j c ⊑ᶜ frameStep j′ c
frameStep-mono-j c hS le =
    iterSize-mono-count (Caps.cSize c) (Caps.cSize c) (≤-trans (s≤s z≤n) hS) le
  , iterFold-mono-count (Caps.cSize c) (Caps.cWid c) hS le
  , frameStep-reg-mono c le

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
  (sizeᵛ u v ≤ᵇ Caps.cSize c) ∧ (outWᵛ n sl u v ≤ᵇ Caps.cWid c)

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
  (sizeᵉ o ≤ᵇ Caps.cSize c) ∧ (outWᵉ n sl o ≤ᵇ Caps.cWid c)

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
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (outWᵛ n sl u v ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵛ u v) sz≤ hsz)
                          (≤ᵇ-widen (outWᵛ n sl u v) wd≤ hwd)

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
  with ∧-true (sizeᵉ o ≤ᵇ Caps.cSize c) (outWᵉ n sl o ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵉ o) sz≤ hsz)
                          (≤ᵇ-widen (outWᵉ n sl o) wd≤ hwd)

obsListCaps?-widen : ∀ {n} {Γ : Ctx n} {s} {c c′ : Caps} (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  c ⊑ᶜ c′ → all (obsCaps? c sl) q ≡ true
          → all (obsCaps? c′ sl) q ≡ true
obsListCaps?-widen sl q le =
  all-impl _ _ (λ o → obsCaps?-widen sl o le) q

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

postulate
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
  -- (a) THE REPAIRED FRAME FACE: a subscribe consumes some number of
  -- folds and reports how many.  j′ folds spent means the caps advance
  -- from frameStep j to frameStep (j + j′), never staying put
  subscribeE-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    pathLen κ + sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

  -- (b) THE CASCADE COMPANION, and the budget claim itself.  One
  -- cascade spends j folds and j fits the count — that inequality IS
  -- what the j-budget probe was run to settle, and it is stated here
  -- rather than buried, because `cWid * cReg` failed it (tickFits-absurd)
  -- and only the three-factor count survives.
  --
  -- caps-tick is then a COROLLARY rather than a sibling face: widen the
  -- reported level to the endpoint by frameStep-mono-j, and the endpoint
  -- IS capsAt (suc id) by capsAt-suc-full
  cascadeGo-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
    in Σ ℕ λ j → (j ≤ Caps.cWid c * Caps.cReg c * Caps.cSize c)
       × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

  -- the two bookends of `cascade`, which touch the registry and the live
  -- set but never a value: latching clears the per-cascade scratch,
  -- finishing DROPS the spent source's entries and sweeps its live entry.
  -- Both can only shrink what capsOK? bounds
  cascadeLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    capsOK? c sched (cascadeLatch a st) ≡ true

  cascadeFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    let r = cascadeFinish a sched st
    in capsOK? c (proj₁ r) (proj₂ r) ≡ true

  -- the cascade's chain snapshot is a SUBLIST of the registry, so both
  -- of cascadeGo-caps's chain hypotheses come straight off capsOK?
  chainsOf-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
    regsSz? B (EvalSt.registry st) ≡ true →
    all (λ rc → pathSz? B (proj₂ rc)) (chainsOf a st) ≡ true

  chainsOf-length : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (st : EvalSt e) →
    length (chainsOf a st) ≤ length (EvalSt.registry st)

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

postulate
  -- a share's connect re-enters subscribeE, so this joins the clique
  subscribeE-input-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    let r = subscribeE g (input i) κ id now sched st
    in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

  -- THE DELIVERY CLIQUE — foldPath / dispatchShare / shareGo /
  -- chainStep — is no longer postulated: it is GROUND, below the block,
  -- on stepFrame-caps and the three share-bookkeeping leaves.
  -- the shared-slot pair: the slot's def is subscribed at connect, which
  -- is a second entry into the walk at the SAME instant
  sharedSlot-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ d ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    pathLen κ + sizeᵉ d ≤ Caps.cSize (frameStep j c) →
    let r = subscribeSharedSlot g i d κ id now sched st
    in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

  sharedConnect-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ d ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    pathLen κ + sizeᵉ d ≤ Caps.cSize (frameStep j c) →
    let r = sharedConnect g i d κ id now sched st
    in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

  -- THE SELF-FEEDING EDGE, and the most uncertain companion in the tree:
  -- the inner observable is drawn from a BURST PAYLOAD, so its size
  -- hypothesis comes from valCaps?'s cSize half rather than from the
  -- syntax, and re-enters subscribeE-caps as `sizeᵉ o ≤ cSize`.  The
  -- chain it is subscribed under is κ extended by one from-inner frame,
  -- which is where its length hypothesis has to come from
  thruConsume-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    valCaps? (frameStep j c) sl (obs u) o ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) + sizeᵛ (obs u) o ≤ Caps.cSize (frameStep j c) →
    let r = thruConsume g op nid κ id now o sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
       × (all (valCaps? (frameStep (j + j′) c) sl u)
              (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)

  thruWalk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
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

  -- ONE FRAME, and the clause that pays a j: map-f and scan-f both
  -- substitute into a step function, which is one sizeStep and one
  -- foldStep — exactly what frameStep's per-j increment dominates
  -- (frameStep-size-suc / frameStep-wid-suc)
  stepFrame-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
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

  -- concatAll's queue, the one node whose STORED observables the size
  -- conjunct bounds directly, so its residue is reported alongside
  concatDrain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (j : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
    (id : Id) (now : Tick) (q : List (Closed Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
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

  innerFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
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

-- the tick endpoint, by definition rather than by arithmetic: this is
-- what makes caps-tick the j = full case of (a) rather than a
-- separate claim
frameStep-full : ∀ (c : Caps) →
  frameStep (Caps.cWid c * Caps.cReg c * Caps.cSize c) c ≡ frameBlowup c
frameStep-full c = refl

-- and the recurrence's own step, so capsAt (suc id) IS the full endpoint
capsAt-suc-full : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsAt e sl (suc id)
    ≡ frameStep (Caps.cWid (capsAt e sl id) * Caps.cReg (capsAt e sl id)
                   * Caps.cSize (capsAt e sl id))
                (capsAt e sl id)
capsAt-suc-full e sl id = refl

------------------------------------------------------------------
-- 2 ≤ cSize AT EVERY LEVEL — frameStep-mono-j's side condition, which
-- the recurrence supplies rather than assumes.  The base is `2 + …` and
-- iterSize only grows it (sizeStep is inflationary for S ≥ 1), so the
-- property is inherited by every frameBlowup
------------------------------------------------------------------

2≤frameBlowup-size : ∀ (c : Caps) → 2 ≤ Caps.cSize c → 2 ≤ Caps.cSize (frameBlowup c)
2≤frameBlowup-size c h =
  ≤-trans h (iterSize-infl (Caps.cSize c) (≤-trans (s≤s z≤n) h)
               (Caps.cWid c * Caps.cReg c * Caps.cSize c) (Caps.cSize c))

2≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ≤ Caps.cSize (capsAt e sl id)
2≤capsAt-size {n = n} e sl zero =
  2≤frameBlowup-size (caps (2 + sizeᵉ e + slotsSize sl) (suc (outWᵉ n sl e))
                           (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
2≤capsAt-size e sl (suc id) =
  2≤frameBlowup-size (capsAt e sl id) (2≤capsAt-size e sl id)

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

postulate
  -- the admitted snapshot is a SUBLIST of the registry, so its chains
  -- inherit the registry's size bound (the caps twin of shareAdmit-B)
  shareAdmit-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (i : Fin n)
    (rs : List (RegId × Source × Chain Γ t)) →
    regsSz? B rs ≡ true →
    all (λ rp → pathSz? B (proj₂ rp)) (shareAdmit i rs) ≡ true

  -- finishing a completing share drops the source's registrations and
  -- sweeps its live entry: the registry shrinks (so regsSz? and the
  -- length conjunct survive) and the live list shrinks (so widLive and
  -- stBounded? survive).  The burst is untouched
  shareFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (i : Fin n) (fin : Bool) (sl : Slots Γ)
    (out : Stream Γ t × Sched Γ × EvalSt e) →
    Sched.slots (proj₁ (proj₂ out)) ≡ sl →
    capsOK? c (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) ≡ true →
    burstCaps? c sl (proj₁ out) ≡ true →
    let r = shareFinish i fin out
    in (capsOK? c (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? c sl (proj₁ r) ≡ true)

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

foldPath-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
  (envSrc : Source) (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
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
  Sched.slots sched ≡ sl →
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
  Sched.slots sched ≡ sl →
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
              2≤S slEq inv pS vC eC =
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
              2≤S slEq inv pS vC eC =
  j₁ , proj₁ (proj₂ DS)
     , ∧-intro (all-++-intro (eventCaps? (frameStep (j + j₁) c) sl) evs _
                  (eventsCaps?-widen sl evs (frameStep-⊑-+ c 2≤S j j₁) eC)
                  refl)
               (proj₂ (proj₂ DS))
  where
  DS = dispatchShare-caps c j sf gas id now i vals fin sl sched st
         2≤S slEq inv vC
  j₁ = proj₁ DS

-- ONE FRAME, THEN THE REST OF THE CHAIN.  j₁ pays the frame, j₂ the
-- tail, and the clause reports j₁ + j₂ — the additive composition,
-- rebracketed by +-assoc and nothing else
foldPath-caps c j sf gas id now envSrc (f ↠ p) vals evs fin sl sched st
              2≤S slEq inv pS vC eC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl (proj₁ REST) (proj₂ (proj₂ IH))
  where
  B    = Caps.cSize (frameStep j c)
  pS1  = ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) pS
  pS2  = ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) (proj₂ pS1)
  SF   = stepFrame-caps c j sf id now f p vals fin sl sched st
           2≤S slEq inv (proj₁ pS1) (proj₂ pS2) vC
  j₁   = proj₁ SF
  step = stepFrame sf id now f p vals fin sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  IH   = foldPath-caps c (j + j₁) sf gas id now envSrc p
           (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step))) sl sd₁ st₁
           2≤S
           (trans (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))
                  slEq)
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
                   2≤S slEq inv vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
dispatchShare-caps c j sf (suc gas) id now i vals fin sl sched st 2≤S slEq inv vC =
  j₁ , proj₁ FIN , proj₂ FIN
  where
  st₀ = shareLatch i fin st
  GO  = shareGo-caps c j sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sl sched st₀
          2≤S slEq (shareLatch-caps (frameStep j c) i fin sched st inv)
          (shareAdmit-caps (Caps.cSize (frameStep j c)) i (EvalSt.registry st)
             (capsOK?-regs (frameStep j c) sched st inv))
          vC
  j₁  = proj₁ GO
  out = shareGo sf gas id now i vals fin (shareAdmit i (EvalSt.registry st))
          sched st₀
  FIN = shareFinish-caps (frameStep (j + j₁) c) i fin sl out
          (trans (shareGo-slots sf gas id now i vals fin
                    (shareAdmit i (EvalSt.registry st)) sched st₀)
                 slEq)
          (proj₁ (proj₂ GO)) (proj₂ (proj₂ GO))

-- FAN-OUT: one registration at a time.  A cancelled chain delivers
-- nothing and costs nothing; a survivor folds, and the two receipts add
shareGo-caps {t = t} c j sf gas id now i vals fin [] sl sched st
             2≤S slEq inv pS vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
shareGo-caps {Γ = Γ} c j sf gas id now i vals fin ((rid , p) ∷ ps) sl sched st
             2≤S slEq inv pS vC
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-caps c j sf gas id now i vals fin ps sl sched st
                2≤S slEq inv (proj₂ (∧-true _ _ pS)) vC
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
          2≤S slEq (capsOK?-delivered (frameStep j c) rid sched st inv)
          (proj₁ (∧-true _ _ pS)) vC
          (closeList-caps (frameStep j c) sl (toℕ i) fin)
  j₁  = proj₁ HD
  FP  = foldPath sf gas id now (toℕ i) p vals cl fin sched st₀
  IH  = shareGo-caps c (j + j₁) sf gas id now i vals fin ps sl
          (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
          2≤S
          (trans (foldPath-slots sf gas id now (toℕ i) p vals cl fin sched st₀)
                 slEq)
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
  Sched.slots sched ≡ sl →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
  valCaps? (frameStep j c) sl (arrTy a) (arrVal a) ≡ true →
  let r = chainStep id a path sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
chainStep-caps {n = n} {e = e} c j id a path sl sched st 2≤S slEq inv pS vC =
  foldPath-caps c j (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sl sched st
    2≤S slEq inv pS (∧-intro vC refl)
    (closeList-caps (frameStep j c) sl (arrSource a) (Arrival.isLast a))

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
           (2≤capsAt-size e sl id) slEq
           (cascadeLatch-caps c a sched st pre) val
           (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
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
-- cWid * cReg * cSize iterations still unspent — and a subscribeE with fold
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

-- STEP 3 of the repair, stated now because it is independent of how the
-- repair lands: the chain half of ANY repaired face consumes exactly
-- this, and it is the load-bearing structural fact behind the measured
-- 10, 10, 10, 10.  Every frame subscribeE installs carries a step
-- function that is a SUBTERM of the expression being subscribed — the
-- map-f/scan-f clauses pass `f` straight through from mapᵉ/scanᵉ — so a
-- registry bounded by C stays bounded by C as long as the subscribed
-- expression is.
--
-- BOTH conjuncts of pathSz? need a hypothesis, and for opposite reasons.
-- The frame half needs `sizeᵉ b ≤ C` and `pathSz? C κ` because the leaf
-- registers the whole of κ under the frames it pushed: the naive lemma
-- is FALSE, since κ = scan-f BIG ↠ root over a tiny b registers BIG.
-- The LENGTH half needs slack rather than mere boundedness — the
-- descent lengthens the chain by one frame per shell of b, so the
-- registered chain is as long as `pathLen κ + sizeᵉ b` and a κ already
-- AT the cap would overflow it.  That slack is what the caller pays for
-- with a j: one frameStep at least doubles cSize (sizeStep C s ≥ 2 s for
-- C ≥ 1), which covers the sum
postulate
  regsSz?-subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (C : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    regsSz? C (EvalSt.registry st) ≡ true →
    sizeᵉ b ≤ C →
    pathSz? C κ ≡ true →           -- the continuation is already bounded
    pathLen κ + sizeᵉ b ≤ C →      -- and the chain it will GROW into fits
    let r = subscribeE g b κ bid now sched st
    in regsSz? C (EvalSt.registry (proj₂ (proj₂ r))) ≡ true

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
-- width.  outW is not polynomial in size: outWᵉ (mergeAllᵉ e)
-- is outWᵉ e * innWᵉ e and innWᵉ towers at a scanᵉ, so any size-to-width
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
