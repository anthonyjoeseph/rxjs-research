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
-- All three components share ONE iteration count, `j`, and this
-- function does not name it: `frameStep` is parametric in the count and
-- every lemma about it below is too, so replacing the count (which has
-- now happened twice) touches `frameBlowup` and nothing else.
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

-- THE COUNT, and it is EXPONENTIAL in cReg — the second correction this
-- number has taken, each from a probe rather than from the proof.
--
--   · `cWid * cReg` was refuted by J-Budget-Probe: its pM family fixes
--     the whole triple at (7, 1, 1) and still stores 15 … 4371 in one
--     cascade, so no count read off the triple can work until the triple
--     bounds the CHAIN LENGTH — which pathSz?'s pathLen conjunct does.
--   · `cWid * cReg * cSize` was then refuted by Fold-Count-Probe, and
--     not by a factor: nested shares make ONE cascade's delivery count
--     exponential in the number of shared slots (2 ^ (k+2) - 2) while
--     every component of the triple stays linear (registrations 2k + 2,
--     cSize and cWid constant).  2 ^ k passes 12k + 6 for good at k = 7.
--
-- THE SHAPE THAT SURVIVES, derived from the share DAG rather than
-- guessed, and REPAIRED once since: the first derivation had a false
-- middle step and Mint-Loop-Probe caught it.
--
-- A delivery is a path r₁ → r₂ → … through the registration DAG —
-- `foldPath` walks a chain without branching and `dispatchShare` fans out
-- to every registration `shareAdmit` returns — and the path is simple,
-- since a repeat would be a cycle in the slot graph, which the slot defs
-- fix at entry.  A DAG on R nodes carries at most `2 ^ R - 1` paths, one
-- per subset.  The step that FAILS is reading R as cReg:
--
--     deliveries ≤ 2 ^ cReg          -- FALSE, and measured false
--
-- The R of that count is the registry AT THE END of the cascade, not at
-- entry, because `shareAdmit` reads the live registry; a fold that mints
-- on a shared slot adds a node mid-traversal.  Mint-Loop-Probe's
-- three-level lean ladder at k = 2 delivers 176 times out of an ENTRY
-- registry of 7, and 2 ^ 7 = 128.  So the excess is real, `D * cSize`
-- is itself over `2 ^ cReg * cSize`, and the whole paths-times-frames
-- route through that middle step is gone.
--
-- WHAT SURVIVES IS THE SAME INJECTION WITH A SECOND COORDINATE.  A
-- delivery is sent not to the set of registrations it visits but to the
-- PAIR (the pre-state registrations it visits, an index for which minted
-- registrations it went through).  The first coordinate ranges over
-- subsets of the entry registry — `2 ^ cReg` of them.
--
-- THE SECOND COORDINATE IS NOT BOUNDED BY cSize, and that was the second
-- thing measured false here.  It was first stated so, on the reasoning
-- that a mint is born of a subscribe inside ONE frame and a frame's step
-- function can name no more sources than its own syntax holds.
-- Mint-Loop-Probe's MEASUREMENT 6 computes the coordinate directly — the
-- fibre of a pre-state class — and gets 4 against a cSize of 3 on the
-- lean two-level ladder and 8 against 3 on the lean three-level one.
-- The lean families exist for exactly this: they keep the delivery
-- structure and shrink the syntax the cap is read off.
--
-- SO BOTH COORDINATES RANGE OVER SUBSETS OF THE ENTRY REGISTRY.  A
-- delivery is determined by the pre-state registrations it visits
-- together with the pre-state registrations whose dispatches minted the
-- ones it visits — every mint happens during some delivery and every
-- delivery bottoms out at a pre-state chain, so the second coordinate is
-- pre-state data too.  That is a story and not yet a proof: it does not
-- on its own show the recursion bottoms out.  It gives
--
--     deliveries ≤ 2 ^ cReg * 2 ^ cReg    frames per delivery ≤ cSize
--
-- and the count is their product: `2 ^ cReg * 2 ^ cReg * cSize`.
-- MEASUREMENT 6 gates both coordinates (22 against 128, 13 against 32)
-- and MEASUREMENT 5 gates the product against j itself.
--
-- The bound is over SUBSETS of registrations, not over branchings, so
-- m-ary fan-in does not beat it: extra fan-in only adds edges, and the
-- transitive tournament already has them all.
--
-- WHEN THE FIRST COORDINATE IS PROVEN RATHER THAN GATED, the lemma to
-- reach for is the INVERTED PAIR, not "one per subset" — the latter is
-- the corollary.  The injection is `paths ↪ subsets`, sending a path to
-- the SET of registrations it visits, and what has to be shown is that
-- the map is injective: two distinct traversals of the SAME set would
-- have to disagree on the order of some pair, and a pair inverted between
-- two reachability-respecting orders is a cycle, which the DAG forbids.
-- Note the nodes are the REGISTRATIONS, not the slots — `merge(s1, s1)`
-- registers twice on one slot and so contributes two nodes — which is
-- why parallel fan-in never collapses into a shared node and the
-- one-per-subset count survives it.
--
-- The SECOND coordinate is the damper, and it is the one without a
-- formal counterpart, and splitting it off as its own coordinate was
-- tried and abandoned: see `cascadeGo-deliveries` below, which now
-- states the delivery bound whole.
--
-- cWid IS GONE, and it was never a factor of this count — it bounds how
-- WIDE one emitted observable is, not how many times a cascade iterates.
-- Fold-Count-Probe's diamond makes that concrete: `mWid` there is ZERO
-- while the cascade really delivers eight times, so the old product was
-- identically 0 on a program with real work to do.  The duty cWid was
-- carrying (pR vs pRs, 3 ↦ 12 against 3 ↦ 30) belongs to the per-fold
-- `foldStep` / `sizeStep` gates, which is where State-Blowup-Probe
-- checks it.
--
-- The cSize factor still reads cSize because that is where the length
-- conjunct puts it, not because a length is a size: `pathLen p ≤ᵇ cSize`
-- is a separate conjunct of the same field, and at pM 6 the two
-- genuinely differ (a 9-frame chain in a state whose largest term
-- measures 7).
--
-- STILL INSIDE THE ROUND-5 GATE: the count reads the Caps triple and
-- nothing else, so round3b-ledger-reset-absurd stays unavailable
frameBlowup : Caps → Caps
frameBlowup c = frameStep (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) c

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

slotCaps? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Slot Γ u → Bool
slotCaps? {u = u} B (scripted (hot async)) =
  all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
slotCaps? {u = u} B (scripted (cold sync async)) =
  all (λ v → sizeᵛ u v ≤ᵇ B) sync
  ∧ all (λ tv → sizeᵛ u (Timed.val tv) ≤ᵇ B) async
slotCaps? B (shared d) = sizeᵉ d ≤ᵇ B

slotsGo? : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → List (Fin n) → Bool
slotsGo? B sl []       = true
slotsGo? B sl (i ∷ is) = slotCaps? B (sl i) ∧ slotsGo? B sl is

slotsCaps? : ∀ {n} {Γ : Ctx n} → ℕ → Slots Γ → Bool
slotsCaps? {n = n} B sl = slotsGo? B sl (tabulate {n = n} (λ i → i))

slotCaps?-widen : ∀ {n} {Γ : Ctx n} {u} (s : Slot Γ u) {B B′ : ℕ} →
  B ≤ B′ → slotCaps? B s ≡ true → slotCaps? B′ s ≡ true
slotCaps?-widen {u = u} (scripted (hot async)) le h =
  all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async h
slotCaps?-widen {u = u} (scripted (cold sync async)) le h =
  ∧-intro (all-impl _ _ (λ v → ≤ᵇ-widen (sizeᵛ u v) le) sync
             (proj₁ (∧-true _ _ h)))
          (all-impl _ _ (λ tv → ≤ᵇ-widen (sizeᵛ u (Timed.val tv)) le) async
             (proj₂ (∧-true _ _ h)))
slotCaps?-widen (shared d) le h = ≤ᵇ-widen (sizeᵉ d) le h

slotsGo?-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (is : List (Fin n)) {B B′ : ℕ} →
  B ≤ B′ → slotsGo? B sl is ≡ true → slotsGo? B′ sl is ≡ true
slotsGo?-widen sl []       le h = refl
slotsGo?-widen sl (i ∷ is) le h =
  ∧-intro (slotCaps?-widen (sl i) le (proj₁ (∧-true _ _ h)))
          (slotsGo?-widen sl is le (proj₂ (∧-true _ _ h)))

slotsCaps?-widen : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) {B B′ : ℕ} →
  B ≤ B′ → slotsCaps? B sl ≡ true → slotsCaps? B′ sl ≡ true
slotsCaps?-widen {n = n} sl le = slotsGo?-widen sl (tabulate {n = n} (λ i → i)) le

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

-- and over a mapped list, which is the shape inputSize sums in
all-≤-sum : ∀ {A : Set} (f : A → ℕ) (xs : List A) (B : ℕ) →
  sum (map f xs) ≤ B → all (λ x → f x ≤ᵇ B) xs ≡ true
all-≤-sum f []       B h = refl
all-≤-sum f (x ∷ xs) B h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (f x) (sum (map f xs))) h)))
          (all-≤-sum f xs B (≤-trans (m≤n+m (sum (map f xs)) (f x)) h))

-- ONE SLOT, AT ITS OWN MEASURE: slotSize is by construction big enough
-- for everything the slot holds
slotCaps?-self : ∀ {n} {Γ : Ctx n} {u} (s : Slot Γ u) → slotCaps? (slotSize s) s ≡ true
slotCaps?-self {u = u} (scripted (hot async)) =
  all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _ (n≤1+n _)
slotCaps?-self {u = u} (scripted (cold sync async)) =
  ∧-intro (all-≤-sum (sizeᵛ u) sync _
             (≤-trans (m≤m+n _ _) (n≤1+n _)))
          (all-≤-sum (λ tv → sizeᵛ u (Timed.val tv)) async _
             (≤-trans (m≤n+m _ _) (n≤1+n _)))
slotCaps?-self (shared d) = T⇒≡true (sizeᵉ d ≤ᵇ sizeᵉ d) (≤⇒≤ᵇ (≤-refl {sizeᵉ d}))

slotsGo?-bound : ∀ {n} {Γ : Ctx n} (B : ℕ) (sl : Slots Γ) (is : List (Fin n)) →
  (∀ (i : Fin n) → slotCaps? B (sl i) ≡ true) → slotsGo? B sl is ≡ true
slotsGo?-bound B sl []       h = refl
slotsGo?-bound B sl (i ∷ is) h = ∧-intro (h i) (slotsGo?-bound B sl is h)

-- THE WHOLE TELESCOPE, from the one number capsAt's base already
-- contains
slotsCaps?-bound : ∀ {n} {Γ : Ctx n} (B : ℕ) (sl : Slots Γ) →
  slotsSize sl ≤ B → slotsCaps? B sl ≡ true
slotsCaps?-bound {n = n} B sl h =
  slotsGo?-bound B sl (tabulate {n = n} (λ i → i))
    (λ i → slotCaps?-widen (sl i)
             (≤-trans (sum-tabulate-lb (λ k → slotSize (sl k)) i) h)
             (slotCaps?-self (sl i)))

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
  with ∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (outWᵛ n sl u v ≤ᵇ Caps.cWid c) h
... | hsz , hwd = ∧-intro (≤ᵇ-widen (sizeᵛ u v) sz≤ hsz)
                          (≤ᵇ-widen (outWᵛ n sl u v) wd≤ hwd)

-- the two halves of valCaps?, which are literally boundedNode's and
-- widNode's scan-st clauses, so a stored accumulator reads either way
valCaps?-size : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true
valCaps?-size {n = n} c sl u v h =
  proj₁ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (outWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

valCaps?-wid : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) (v : Val Γ u) →
  valCaps? c sl u v ≡ true → (outWᵛ n sl u v ≤ᵇ Caps.cWid c) ≡ true
valCaps?-wid {n = n} c sl u v h =
  proj₂ (∧-true (sizeᵛ u v ≤ᵇ Caps.cSize c) (outWᵛ n sl u v ≤ᵇ Caps.cWid c) h)

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
  -- (iii) AND THE ONE THAT IS A STATEMENT-LEVEL GAP: `deferᵉ body`
  --      PARKS AN OBSERVABLE ON THE SCHEDULE.  Its clause adds a
  --      LiveSource at `elemTy = obs u` with `pending = (suc now , body)`,
  --      so capsOK?'s widLive conjunct demands
  --      `outWᵉ n sl body ≤ Caps.cWid (frameStep j c)` — a WIDTH bound on
  --      the subscribed expression.  This face's telescope has no width
  --      hypothesis at all, and the obvious source is not there either:
  --      `outWᵉ j sl (deferᵉ e) = 0` BY DEFINITION (Rx.Frame-Width — a
  --      defer crosses a tick), so the enclosing expression's width says
  --      nothing about the parked body's.  The scripted-slot branch of
  --      subscribeE-input-caps escaped the width question because a
  --      scripted element type is DATA and outWᵛ is identically zero
  --      there; a defer's payload is `obs`, and it does not escape.
  --
  --      So subscribeE-caps needs a third conjunct,
  --      `outWᵉ n sl b ≤ Caps.cWid (frameStep j c)`, and that is a
  --      telescope change to the assembly knot: it threads back through
  --      every caller (subscribeInner-caps and thruWalk-caps can supply
  --      it from valCaps?'s own width half, which they already carry),
  --      and it REOPENS the slot side condition on the width axis —
  --      sharedConnect subscribes a slot DEF, and slotsCaps? is
  --      size-only precisely because nothing needed widths until now.
  --      Recorded, not made: it is one ruling, not a clause grind
  subscribeE-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) sl ≡ true →
    capsOK? (frameStep j c) sched st ≡ true →
    sizeᵉ b ≤ Caps.cSize (frameStep j c) →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    let r = subscribeE g b κ bid now sched st
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
       × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

  -- the two bookends of `cascade` and the chain snapshot are no longer
  -- postulated either: they are GROUND below, on the same two filter
  -- lemmas the share leaves use.

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
--   (ii) cascadeGo-deliveries  D ≤ 2 ^ cReg * 2 ^ cReg
--
-- and `cascadeGo-caps` below is their product, by arithmetic and nothing
-- else.  (i) is the per-delivery charge: every fold is a frame on some
-- delivery's chain, and a chain is shorter than cSize by pathSz?'s own
-- length conjunct — this is the half the induction already carries, in
-- the shape `foldPath-caps` reports it.  (ii) is the delivery bound, and
-- it is where all the difficulty is.
--
-- (ii) WAS SPLIT AND THE SPLIT DIED, twice, in one session — which is
-- what stating it as an assembly was for.  The split sent a delivery to
-- the PAIR (which pre-state registrations its path visits, an index for
-- which minted ones it went through), with `preClasses ≤ 2 ^ cReg` on the
-- first coordinate and a DAMPER on the second.  Mint-Loop-Probe gave both
-- coordinates definitions and measured them:
--
--   · `fibreCap ≤ cSize` — the reasoning was that a mint happens inside
--     ONE frame and a frame's step function names no more sources than
--     its syntax holds.  Measured 4 against a cSize of 3 on the lean
--     two-level ladder.  Refuted.
--   · `fibreCap ≤ 2 ^ cReg` — the reasoning was that every mint happens
--     during some delivery and every delivery bottoms out at a pre-state
--     chain, so the second coordinate is pre-state data too.  It ATTAINS
--     128 against 128 on the three-level ladder and then reaches 576
--     against a cap of 512 on the four-level one.  Refuted.
--
-- AND THE FIRST COORDINATE IS FINE, which is what makes the split
-- pointless rather than merely unlucky.  `preClasses` measures 4, 10, 22,
-- 46 for entry registries of 3, 5, 7, 9 — about `2 ^ (cReg / 2)`, and
-- invariant in the nesting depth, because the pre-state classes really
-- are fixed by the pre-state DAG.  So D is (something small) times
-- (something the size of D): the split renames the problem instead of
-- decomposing it, and the second factor inherits every difficulty the
-- first was supposed to remove.  The delivery bound is therefore stated
-- WHOLE, and it is the single place the mint loop has to be beaten.
--
-- WHAT THE EVIDENCE FOR (ii) IS — AND IT IS WEAKER THAN THIS COMMENT
-- USED TO SAY.  The bound HOLDS on every row Mint-Loop-Probe and
-- Mint-Loop-Frames measure; no measurement refutes it.  That is all it
-- holds by.
--
-- The claim that stood here — that the margin GROWS as the ladder
-- deepens, citing D / (2 ^ cReg * 2 ^ cReg) at 0.078, 0.026, 0.016,
-- 0.0097 — is FALSE, and it is instance 4 of Mint-Loop-Probe's STANDING
-- WARNING — DO NOT EXTRAPOLATE FROM SHALLOW ROWS, at that file's head.
-- Those four numbers compared each ladder at whatever k it had then been
-- swept to, and the four-level ladder had only been swept to k = 2.
-- Swept to k = 5 it spends 0.10056 — the WORST ratio in either file,
-- worse than the ONE-level ladder's 0.078 — so the sequence is
-- 0.078, 0.026, 0.016, 0.10056 and there is no trend in it at all.
-- `D * 10 ≤ 2 ^ cReg * 2 ^ cReg` is false at L = 4.
--
-- AND THE DEEPEST AFFORDABLE ROW IS NOT SATURATED.  L = 3 has flattened
-- by k = 5 (under 1 % per rung), but L = 4's per-rung growth runs 4.37,
-- 3.51, 2.72, 2.16, 1.77 — decelerating, and still buying 77 % at the
-- last rung either harness can compute.  k = 6 was killed at 40 minutes
-- and 12.4 GB.  So the spend is at a tenth of budget while still
-- climbing, and the per-level trend (L = 3 saturated at 0.016, L = 4
-- unsaturated at ≥ 0.10) points the wrong way: a breach at L = 5 or
-- L = 6 is expected rather than excluded.
--
-- STATUS: (ii) IS UNPROVEN AND SUSPECT, and the grind on it is FROZEN by
-- design ruling — this conjunct, `preClasses`-style splits, and fibre
-- caps are not to be attacked, and L = 5 is not to be measured, until
-- the delivery recurrence has been DERIVED from the evaluator's
-- structure and used to PREDICT the L = 5 rows.  Measuring them first
-- would spend the only out-of-sample test the derivation has.
--
-- THE FEEDBACK LOOP BEHIND ALL OF THIS IS MEASURED AND DOES NOT TOWER.
-- Read naively the recursion is vicious — D ≤ 2 ^ R_end with R_end ≤ R₀ +
-- D * mints has no closed bound — and family G only sampled its base
-- rung.  Mint-Loop-Probe closes it: a scan under a share whose step
-- re-subscribes that share, nested k deep, so a minted chain itself
-- mints.  Deliveries SATURATE in k (5 flat at one shared level; 20, 26,
-- 27, 27 at two; 50 … 269 at three) because a minted registration is
-- only reachable by dispatches that come after it and how many remain is
-- fixed by the PRE-STATE DAG.  j saturates too, but LATER — 58, 226,
-- 548, 912, 1164, 1268, 1291 — because nesting keeps lengthening the
-- chains after it has stopped widening them, so the count/budget ratio
-- has an interior peak at k = 3 rather than falling monotonically.  The
-- mid-cascade subscription that drives the loop is real rxjs, not an
-- evaluator artifact: a subscriber added mid-cascade misses the
-- in-flight emission and receives the cascade's later ones, checked
-- against rxjs 7.8 at the probe's head.
--
-- caps-tick is then a COROLLARY rather than a sibling face: widen the
-- reported level to the endpoint by frameStep-mono-j, and the endpoint
-- IS capsAt (suc id) by capsAt-suc-full
------------------------------------------------------------------

-- the deliveries a cascade makes, off the evaluator's own ledger
delivN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → EvalSt e → ℕ
delivN st st′ = length (EvalSt.delivered st′) ∸ length (EvalSt.delivered st)

postulate
  -- (i) THE PER-DELIVERY CHARGE.  The receipt the induction actually
  -- builds, charged to the cascade's own delivery ledger rather than to
  -- a count: every fold is a frame on some delivery's chain, and
  -- pathSz?'s length conjunct caps a chain at cSize
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
    in Σ ℕ λ j → (j ≤ delivN st (proj₂ (proj₂ r)) * Caps.cSize c)
       × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

  -- (ii) THE DELIVERY BOUND, WHOLE.  One cascade's deliveries against
  -- subsets of the entry registry, squared.  This is the mint loop's
  -- one remaining hiding place: `shareAdmit` reads the registry as of
  -- the dispatch, so the DAG the paths run through is the END registry,
  -- and nothing here bounds that by cReg.  Two decompositions of this
  -- statement have been measured false; it stands on Mint-Loop-Probe's
  -- gate and on nothing else.
  --
  -- AND THE ROUTE TO IT IS NOT AN INJECTION.  Mint-Loop-Shapes measures
  -- R_end and the answer is that MINTS TRACK DELIVERIES — 254 mints on a
  -- 269-delivery cascade, leaving a registry of 261 against an entry cReg
  -- of 7.  The inverted-pair argument still proves `D ≤ 2 ^ R_end`, but
  -- at R_end = 261 against a budget of 2 ^ 18 that is not a usable
  -- bound, and no subset injection can be, whether or not this statement
  -- is true.  What is left is what the damper natively is: an ORDERING
  -- fact.  A minted registration is reachable only by dispatches that
  -- come after it, so the proof wants a schedule-indexed induction on a
  -- decreasing remaining-dispatch potential — different machinery from
  -- every route tried on this conjunct so far
  cascadeGo-deliveries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (c : Caps) (a : Arrival Γ) (id : Id)
    (chains : List (RegId × Path Γ (arrTy a) t))
    (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    length chains ≤ Caps.cReg c →
    delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
      ≤ 2 ^ Caps.cReg c * 2 ^ Caps.cReg c

-- THE ASSEMBLY, ground: the conjunct is the three pieces multiplied out
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
  in Σ ℕ λ j → (j ≤ 2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c)
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-caps c a id chains sl sched st 2≤S slEq inv vC pS lenB =
  proj₁ CH
    , ≤-trans (proj₁ (proj₂ CH))
              (*-monoˡ-≤ (Caps.cSize c)
                 (cascadeGo-deliveries c a id chains sched st inv lenB))
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

-- the tick endpoint, by definition rather than by arithmetic: this is
-- what makes caps-tick the j = full case of (a) rather than a
-- separate claim
frameStep-full : ∀ (c : Caps) →
  frameStep (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) c ≡ frameBlowup c
frameStep-full c = refl

-- and the recurrence's own step, so capsAt (suc id) IS the full endpoint
capsAt-suc-full : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  capsAt e sl (suc id)
    ≡ frameStep (2 ^ Caps.cReg (capsAt e sl id) * 2 ^ Caps.cReg (capsAt e sl id)
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
               (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) (Caps.cSize c))

2≤capsAt-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 ≤ Caps.cSize (capsAt e sl id)
2≤capsAt-size {n = n} e sl zero =
  2≤frameBlowup-size (caps (2 + sizeᵉ e + slotsSize sl) (suc (outWᵉ n sl e))
                           (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
2≤capsAt-size e sl (suc id) =
  2≤frameBlowup-size (capsAt e sl id) (2≤capsAt-size e sl id)

-- 1 ≤ cReg AT EVERY LEVEL, the registering companions' side condition,
-- and the recurrence proves it the same way: the base's cReg is a `suc`,
-- and frameBlowup's cReg is `cReg c * suc (…)`, which never drops below
-- cReg c
1≤frameBlowup-reg : ∀ (c : Caps) → 1 ≤ Caps.cReg c → 1 ≤ Caps.cReg (frameBlowup c)
1≤frameBlowup-reg c h = ≤-trans h (m≤m*n (Caps.cReg c) _)

1≤capsAt-reg : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  1 ≤ Caps.cReg (capsAt e sl id)
1≤capsAt-reg {n = n} e sl zero =
  1≤frameBlowup-reg (caps (2 + sizeᵉ e + slotsSize sl) (suc (outWᵉ n sl e))
                          (suc (sizeᵉ e + slotsSize sl)))
    (s≤s z≤n)
1≤capsAt-reg e sl (suc id) =
  1≤frameBlowup-reg (capsAt e sl id) (1≤capsAt-reg e sl id)

------------------------------------------------------------------
-- AND THE SLOT SIDE CONDITION AT EVERY LEVEL, supplied by the
-- recurrence rather than assumed.  This is what ties `c` to `sl`: the
-- base cSize CONTAINS slotsSize as a summand, iterSize only grows it,
-- so every slot's payloads sit under every level's cSize.
------------------------------------------------------------------

cSize≤frameBlowup : ∀ (c : Caps) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cSize (frameBlowup c)
cSize≤frameBlowup c h =
  iterSize-infl (Caps.cSize c) h
    (2 ^ Caps.cReg c * 2 ^ Caps.cReg c * Caps.cSize c) (Caps.cSize c)

capsAt-base-size : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  2 + sizeᵉ e + slotsSize sl ≤ Caps.cSize (capsAt e sl id)
capsAt-base-size {n = n} e sl zero =
  cSize≤frameBlowup (caps (2 + sizeᵉ e + slotsSize sl) (suc (outWᵉ n sl e))
                          (suc (sizeᵉ e + slotsSize sl)))
    (≤-trans (s≤s z≤n) (≤-trans (m≤m+n 2 (sizeᵉ e)) (m≤m+n (2 + sizeᵉ e) (slotsSize sl))))
capsAt-base-size e sl (suc id) =
  ≤-trans (capsAt-base-size e sl id)
          (cSize≤frameBlowup (capsAt e sl id)
             (≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)))

-- THE TOP-LEVEL SUPPLY, the counterpart of 2≤capsAt-size and
-- 1≤capsAt-reg.  It is what the cascade face hands the tree once
-- cascadeGo-charge carries the side condition too; the companions below
-- thread it from there down to subscribeE-input-caps unchanged
slotsCaps?-capsAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  slotsCaps? (Caps.cSize (capsAt e sl id)) sl ≡ true
slotsCaps?-capsAt e sl id =
  slotsCaps?-bound (Caps.cSize (capsAt e sl id)) sl
    (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id))

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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
subscribeInner-caps {Γ = Γ} {t = t} {u = u} c j (gs fuel) op allNid κ id now o
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
  pC′    : pathSz? B′ κ′ ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                        (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                      (pathSz?-⊑ κ step⊑ pC))
  IH     = subscribeE-caps c (suc j) fuel o κ′ id now sl sched₀ st 2≤S 1≤R slEq slC
             (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
                (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                  sched st inv))
             (≤-trans szo (proj₁ step⊑)) pC′
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
-- OUT OF GAS: a dry close and nothing else
sharedConnect-caps {Γ = Γ} c j g0 i d κ id now sl sched st 2≤S 1≤R slEq slC inv szd pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (dryBurst {A = Val Γ (lookup Γ i)} id) ≡ true)
            (sym (+-identityʳ j)) refl
sharedConnect-caps {Γ = Γ} c j (gs fuel′) i d κ id now sl sched st
                   2≤S 1≤R slEq slC inv szd pC lC
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
sharedSlot-caps {Γ = Γ} c j g i d κ id now sl sched st 2≤S 1≤R slEq slC inv szd pC lC
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
                  2≤S 1≤R slEq slC inv szd pC lC

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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  WN = all-++-intro (λ x → outWᵉ n (Sched.slots sched) x ≤ᵇ Caps.cWid (frameStep j c))
         q (o ∷ []) wn
         (∧-intro (subst (λ y → (outWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
                         (outWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeSz c sl q h2)

-- and back again, which is how the drained residue re-enters the node
obsList-intro : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q ≡ true →
  all (λ o → outWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true →
  all (obsCaps? c sl) q ≡ true
obsList-intro c sl []      hsz hwd = refl
obsList-intro {n = n} c sl (x ∷ q) hsz hwd
  with ∧-true (sizeᵉ x ≤ᵇ Caps.cSize c)
              (all (λ o → sizeᵉ o ≤ᵇ Caps.cSize c) q) hsz
     | ∧-true (outWᵉ n sl x ≤ᵇ Caps.cWid c)
              (all (λ o → outWᵉ n sl o ≤ᵇ Caps.cWid c) q) hwd
... | s1 , s2 | w1 , w2 = ∧-intro (∧-intro s1 w1) (obsList-intro c sl q s2 w2)

obsList-nodeWid : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ)
  (q : List (Closed Γ s)) →
  all (obsCaps? c sl) q ≡ true →
  all (λ o → outWᵉ n sl o ≤ᵇ Caps.cWid c) q ≡ true
obsList-nodeWid c sl []      h = refl
obsList-nodeWid {n = n} c sl (o ∷ q) h
  with ∧-true (obsCaps? c sl o) (all (obsCaps? c sl) q) h
... | h1 , h2 =
  ∧-intro (proj₂ (∧-true (sizeᵉ o ≤ᵇ Caps.cSize c)
                         (outWᵉ n sl o ≤ᵇ Caps.cWid c) h1))
          (obsList-nodeWid c sl q h2)

concatDrain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
         (subst (λ y → all (λ x → outWᵉ n y x ≤ᵇ Caps.cWid (frameStep (j + j′) c))
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
             (subst (λ y → all (λ o → outWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) q
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
-- `scripted` constructor carries is exactly `T (isData t)` — and outWᵛ
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

-- a data type has no observable inside it, so it has no frame width —
-- which is what makes the slot side condition a size-only predicate
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

valCaps?-data : ∀ {n} {Γ : Ctx n} (c : Caps) (sl : Slots Γ) (u : Ty) → T (isData u) →
  (v : Val Γ u) → (sizeᵛ u v ≤ᵇ Caps.cSize c) ≡ true → valCaps? c sl u v ≡ true
valCaps?-data {n = n} c sl u ok v h =
  ∧-intro h (subst (λ x → (x ≤ᵇ Caps.cWid c) ≡ true)
                   (sym (outWᵛ-data n sl u ok v)) refl)

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
  all (λ tv → outWᵛ n sl u (proj₂ tv) ≤ᵇ W) ps ≡ true
resolve-wid-data W sl ok []             = refl
resolve-wid-data {n = n} {u = u} W sl ok ((tk , v) ∷ ps) =
  ∧-intro (subst (λ x → (x ≤ᵇ W) ≡ true) (sym (outWᵛ-data n sl u ok v)) refl)
          (resolve-wid-data W sl ok ps)

-- one slot's condition, read out of the telescope's
slotsGo?-tab : ∀ {n m} {Γ : Ctx n} (B : ℕ) (sl : Slots Γ)
  (f : Fin m → Fin n) (i : Fin m) →
  slotsGo? B sl (tabulate f) ≡ true → slotCaps? B (sl (f i)) ≡ true
slotsGo?-tab B sl f Fin.zero h =
  proj₁ (∧-true (slotCaps? B (sl (f Fin.zero)))
                (slotsGo? B sl (tabulate (λ k → f (Fin.suc k)))) h)
slotsGo?-tab B sl f (Fin.suc i) h =
  slotsGo?-tab B sl (λ k → f (Fin.suc k)) i
    (proj₂ (∧-true (slotCaps? B (sl (f Fin.zero)))
                   (slotsGo? B sl (tabulate (λ k → f (Fin.suc k)))) h))

slotsCaps?-lookup : ∀ {n} {Γ : Ctx n} (B : ℕ) (sl : Slots Γ) (i : Fin n) →
  slotsCaps? B sl ≡ true → slotCaps? B (sl i) ≡ true
slotsCaps?-lookup B sl i h = slotsGo?-tab B sl (λ k → k) i h

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

subscribeE-input-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) sl ≡ true →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
subscribeE-input-caps {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC inv pC lC
  with Sched.slots sched i
     | subst (λ y → slotCaps? (Caps.cSize c) (y i) ≡ true) (sym slEq)
             (slotsCaps?-lookup (Caps.cSize c) sl i slC)
-- SHARED: the def's size is the one thing sharedSlot-caps asks for
... | shared d | sd =
  sharedSlot-caps c j g i d κ id now sl sched st 2≤S 1≤R slEq slC inv
    (≤-trans (≤ᵇ⇒≤ (sizeᵉ d) (Caps.cSize c) (T-to sd)) (cSize≤frameStep c j 2≤S))
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
-- AND THE TWO CLAUSES THAT DO BUILD VALUES, POSTULATED — with what the
-- grind found out about what they can cost.
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
-- THE STATEMENTS ARE STILL TRUE, because j′ is EXISTENTIAL and
-- iterSize runs away faster than the clause does: sizeStep S s ≥ 2 + 4s
-- for S ≥ 2, so iterSize S j′ s ≥ 4 ^ j′ * s and a j′ of order
-- 3 ^ cSize covers the tower.  What is NOT true is that the receipt is
-- one fold per frame.
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

postulate
  -- ONE map-f FRAME.  Every payload is mapped independently, so nothing
  -- composes and the whole list costs one clause's worth of folds
  mapFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
    (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
    2 ≤ Caps.cSize c →
    (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
    all (valCaps? (frameStep j c) sl s) vals ≡ true →
    Σ ℕ λ j′ →
      all (valCaps? (frameStep (j + j′) c) sl u) (map (applyFn fn) vals) ≡ true

  -- ONE scan-f FRAME.  Here the folds DO compose — scanVals threads the
  -- accumulator, so payload i is `applyFn` applied i times — and the
  -- accumulator has to come back bounded too, because it is reinstalled
  scanFrame-caps : ∀ {n} {Γ : Ctx n} {s u} (c : Caps) (j : ℕ) (sl : Slots Γ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (acc : Val Γ u) (vals : List (Val Γ s)) →
    2 ≤ Caps.cSize c →
    (sizeᵗ fn ≤ᵇ Caps.cSize (frameStep j c)) ≡ true →
    valCaps? (frameStep j c) sl u acc ≡ true →
    all (valCaps? (frameStep j c) sl s) vals ≡ true →
    Σ ℕ λ j′ →
      (all (valCaps? (frameStep (j + j′) c) sl u)
           (proj₁ (scanVals fn acc vals)) ≡ true)
      × (valCaps? (frameStep (j + j′) c) sl u (proj₂ (scanVals fn acc vals)) ≡ true)

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
                    2≤S slEq inv fS pS vC
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
  SC  = scanFrame-caps c j sl fn ac vals 2≤S fS
          (∧-intro (proj₁ nb)
                   (subst (λ x → (outWᵛ _ x u ac ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  MP = mapFrame-caps c j sl fn vals 2≤S fS vC
  j′ = proj₁ MP

-- SCAN: its own top-level lemma, as in the wet family — the nested
-- `with` on the stored accumulator's type cannot be elaborated inside a
-- clause of the general frame case
stepFrame-caps c j g id now (scan-f fn nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC inv fS pS lC vC =
  stepFrame-scan-caps c j g id now fn nid κ vals fin sl sched st 2≤S slEq inv fS pS vC

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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
  slotsCaps? (Caps.cSize c) sl ≡ true →
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
-- The LENGTH half needs the chain to have room to GROW, since the
-- descent lengthens it by one frame per shell of b.  It used to ask for
-- `pathLen κ + sizeᵉ b ≤ C`, the joint form Joint-Probe refuted; what it
-- asks for now is the same pair the face does, and the descent's growth
-- is paid for one frame at a time by the j each hop spends
postulate
  regsSz?-subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (C : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    regsSz? C (EvalSt.registry st) ≡ true →
    sizeᵉ b ≤ C →
    pathSz? C κ ≡ true →           -- the continuation is already bounded
    suc (pathLen κ) ≤ C →          -- and the chain it will GROW into fits
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
