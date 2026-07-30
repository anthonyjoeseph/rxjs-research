-- THE PROOF (in progress) of budget sufficiency: the seeded sync
-- budget never runs dry on a canonical run — the old TERMINATING
-- pragma's claim, decomposed.
--
-- Architecture: an instant-indexed size invariant.  The only things
-- that grow across a run are the runtime values stored in the
-- machine (schedule pendings, scan accumulators, concat queues);
-- everything else is fixed program syntax.  Both fuel demand and
-- stored-value sizes TOWER (chained obs-typed scans exponentiate at
-- each story — the 2026-07-19 attack, see syncBudget's comment in
-- Rx.Evaluator), so the Gas budget is a tower and sizeBudgetAt is
-- its ℕ shadow for the ≤ᵇ-decidable store invariant.
--
--   stBounded? B          — every stored value's size ≤ B (decidable)
--   INV at instant id     — stBounded? (sizeBudgetAt … id)
--   subscribeE-wet        — THE WET CONTRACT (stated; the induction)
--   cascadeGo-wet         — the chain fold stays wet, lands bounded
--   burst-wet (PROVEN)    — the contract at the root + seed-covers
--   cascade-dry (PROVEN)  — latch + fold core + finish, composed
--   drain-dry (PROVEN)    — the fuel loop composes cascades
--   budget-sufficient     — (PROVEN from the above) the whole run
--
-- PROVEN: pop-slots/pop-bounded (inverting schedGo, hoisted for
-- exactly this), the cascade's structural ring (latch/sweep/finish/
-- mono), sync-linearity (plugs-len/occs/inner-len-subΘ), the seed
-- inequality (prod≤3pow/seed-covers — the tower dominance
-- arithmetic at instant 0, discharging the burst cores from the
-- contract), cascade-dry, drain-dry, and the theorem.
--
-- AND THE HOP MEASURE, in full (2026-07-27..29).  dBound's `r` is
-- hopD, a remaining-hop count; the emitted-value invariant the *All
-- clause consumes — every value a burst carries is no deeper than what
-- was subscribed — is proven end to end, with no postulate in its
-- chain: pm-subΘ, hopD-subΘᵉ/ᵗ/ᵗˢ (hopD is AFFINE in a substituted
-- value's depth), hopD-evalWith, hopD-applyFn, hopD-map-emit.  Getting
-- the measure's coefficient right took three machine-checked
-- refutations; see the hop-descent memo below and
-- agda/probe/Hop-Descent-Probe.agda.
--
-- READ THIS FIRST (2026-07-29).  subscribeE-walk has been refuted
-- TWICE in one day, and the second refutation is the live one.
--
--   walk-hyps-absurd    the 2026-07-24 face was VACUOUS: one V served
--                       as both the demand anchor and the store
--                       ceiling, and those two roles contradict.
--   hop-anchor-absurd   the anchor split (demand at the call's own
--                       entry bound capᴱ W E) removes the vacuity but
--                       does NOT close the hop edge: a call and its
--                       hop child then sit at DIFFERENT anchors, the
--                       child's anchor exceeds the parent's d, and the
--                       child's demand exceeds it in turn.
--
-- ROUND 3 IS NOW THE FACE (walk-hyps-round3b + the restated
-- subscribeE-walk), and it COLLAPSED to a single measure on the way in.
-- Anthony's DAG carried a work index G and a separate fuel demand d;
-- both turned out to need the same reset caps at a hop edge, so they
-- stand or fall together and are now one number.  G is the fuel budget,
-- the descent order, and walkCap's index at once, with every cap in it
-- — the s′ reset Ŝ, the r reset R̂, the hop index F — fixed at ENTRY
-- rather than at the ledger.  F is threaded UNCHANGED into the hop
-- child, so parent and child finally read the same index, and the hop
-- edge that killed round 2 is dBound-hop verbatim.
--
-- Two further hypotheses had to move, each forced by its own
-- machine-checked absurdity rather than by taste:
--   · round3-old-ell-absurd — `pathLen κ + d ≤ ℓ` carried the SAME loop
--     routed through ℓ (walkCap's base is (3+Ω)·suc ℓ).  Now
--     `pathLen κ + G ≤ ℓ`.
--   · round3-anchor-indexed-absurd — the work index may not be measured
--     at the anchor, which is what forces `r` off hopDᵉ's V-index.
--
-- NO NEW POSTULATE.  The work index is not a new measure at all — it
-- is dBound at entry caps, so Ŝ, R̂ and F are ordinary ℕ parameters
-- carried like Ψ, Ω and ℓ.  What they cost instead is ONE semantic
-- debt, named by round3b-ledger-reset-absurd: the caps may not be the
-- ledger.  There has to be an entry-determined bound on the size of an
-- observable a run can REACH, or the measure re-anchors at capᴱ and
-- dies as rounds 1 and 2 did.  agda/probe/Frame-Work-Probe.agda is the
-- evidence such a bound exists — the fold count is the source's
-- per-frame payload count, which bottoms out in ofᵉ list lengths — and
-- also the warning about its size: it is an iterated exponential in the
-- nesting depth, so it is a tower and must not be written as anything
-- shaped like `3 + Ω`.
--
-- TWENTY-TWO POSTULATES REMAIN, and the number going UP is the plan
-- rather than a regression.  They are: the three walk faces
-- (subscribeE-wet, cascadeGo-wet, subscribeE-walk), the caps face
-- subscribeE-caps with its chain-half lemma regsSz?-subscribeE, the five
-- cascade companions caps-tick is assembled from (cascadeGo-caps — which
-- carries the BUDGET CLAIM itself — plus cascadeLatch-caps,
-- cascadeFinish-caps, chainsOf-caps, chainsOf-length), and twelve of the
-- thirteen subscribe-side companions transcribed from subscribeE-walkS's
-- clique.  frameBlowup is fully defined: no gaps inside it.
--
-- The thirteenth, subscribeInner-caps, is PROVEN — the grind's first
-- clause, taken first because it was the most uncertain: the *All edge
-- where the inner observable comes off a burst payload rather than the
-- syntax, so every hypothesis it feeds back into subscribeE-caps has to
-- come from valCaps? and from κ extended by one frame.  It closes.
--
-- The whole tree is STATED BEFORE ANY CLAUSE IS GROUND, which is the
-- outside-in rule applied at this joint: a change to the shape then
-- changes it here, cheaply, instead of invalidating a pile of finished
-- clause proofs.  Two things follow immediately, and both are the point.
--
-- caps-tick is NOT among the twenty-three — it is derived, four lines of
-- assembly over the cascade companions.  And the joint the round was
-- about (does one cascade's fold count FIT the recurrence's iteration
-- budget?) is now a named conjunct of cascadeGo-caps rather than
-- something hidden inside a face — with the j-budget probe saying which
-- count it has to fit, since `cWid * cReg` is refuted outright.
--
-- caps-frame, likewise, was refuted as uninstantiable (same-level
-- preservation is false: the subscribe frame itself folds) and split
-- into subscribeE-caps, which reports its growth as a fold count, plus
-- the chain-half lemma any repaired face consumes.  Trading false
-- postulates for true ones is progress; the number is not the metric.
--
-- ROUND 4 (2026-07-29): the caps are defined BY RECURRENCE on the
-- instant, Caps (suc id) = frameBlowup (Caps id), after deepScan refuted
-- every fixed-height shape.  All three components of frameBlowup are
-- defined and gated in State-Blowup-Probe, which measures capsOK?'s own
-- conjuncts off a real run — and in doing so refuted three parts of the
-- first round-4 draft: foldStep (gated against payload counts, too small
-- for the outWᵛ it actually bounds, so it now reads cSize), outWᵉ's
-- scripted clause (0, collapsing every scripted program's width cap),
-- and the base case (which now pays for its own root frame).  Round 3's face is
-- untouched — it was only ever missing something to instantiate Ŝ, R̂, F
-- at.  The two real cores are subscribeE-wet and
-- cascadeGo-wet — the termination content proper: fuel-accounting
-- induction over the subscription machine's clauses (the three
-- decrement edges each consume one hasAtLeast-peel against
-- dBound-μ/-hop/-connect; everything between is structural), and the
-- fold's threading invariant (see cascadeGo-wet's memo).  The third is
-- subscribeE-walk, the joint wet/dry/length face they are stated
-- against.  The reachability cluster is what supplies its three entry
-- caps Ŝ, R̂, F — one measure in three roles, so F cannot drift to an
-- unaudited source (reach-resets, PROVEN, is that wiring).
-- PROVEN 2026-07-29: hopD-size (the hop measure is now
-- derived end to end), and the walk's two bookkeeping companions
-- subscribeE-slots and subscribeE-connected-mono — one joint `Keeps`
-- induction over subscribeE's whole clique.  SPLICED: Verify-Well-Formed imports
-- budget-sufficient from here instead of postulating it.

-- ─── MODULE MAP (2026-07-30) ──────────────────────────────────────
-- This file was one 12,687-line module; a full re-check cost ~22
-- minutes, and that is the dev loop's dominant cost now that the caps
-- face is being ground clause by clause.  It is split along the strata
-- that were already stable.  Agda caches each module's interface, so a
-- clause committed here re-checks only this file.
--
--   .Measures    the measures — gas, dBound, hopD, seed arithmetic,
--                size/fnCap/ofW, INV?/widthOK?, the walk face and its
--                four absurdity records
--   .Keeps-Ring  the shared structural prerequisite: stepping the
--                evaluator keeps the slot telescope and the connected
--                shares (KeepsC), plus the share-boundary facts
--   .Caps-Face   round 4's per-instant cap recurrence, the caps face
--                and its companion tree, caps-tick, reach-resets
--   .Wet         the wet family, the width family, and the theorem
--                (burst-wet, cascade-dry, drain-dry, budget-sufficient)
--
-- .Caps-Face and .Wet are SIBLINGS over .Keeps-Ring, not a stack: the wet
-- family never mentions Caps, so grinding the caps face leaves it (and
-- Verify-Well-Formed, which imports budget-sufficient from .Wet) alone.
--
-- This file is the ACTIVE GRIND, and re-exports all three so every
-- existing importer and probe sees the same names it always did.
-- ──────────────────────────────────────────────────────────────────
module Verify-Budget-Sufficient where

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
                                complete; exhausted;
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

open import Verify-Budget-Sufficient.Measures   public
open import Verify-Budget-Sufficient.Keeps-Ring public
open import Verify-Budget-Sufficient.Caps-Face  public
open import Verify-Budget-Sufficient.Wet        public

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
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) (Sched.slots sched) (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) + sizeᵛ (obs u) o ≤ Caps.cSize (frameStep j c) →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valCaps? (frameStep (j + j′) c) (Sched.slots sched) u)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) (Sched.slots sched))
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
-- OUT OF GAS: a dry close and nothing else.  The only state change is
-- the instance counter, which capsOK? does not read
subscribeInner-caps c j g0 op allNid κ id now o sched st 2≤S inv vC pC lC =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (record sched { nextNode = suc (Sched.nextNode sched) }) st ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched)) sched st inv)
    , refl , refl
-- WITH GAS: the inner is subscribed under one more frame, at the same
-- instant.  Its size hypothesis is valCaps?'s cSize half (sizeᵛ (obs u)
-- IS sizeᵉ), and its chain hypotheses are κ's, one frame longer — which
-- is exactly what the extra summand in lC pays for
subscribeInner-caps {t = t} {u = u} c j (gs fuel) op allNid κ id now o sched st
                    2≤S inv vC pC lC =
  j′ , SUB
     , splitBurst-vals-caps {s = u} {u = t} (frameStep (j + j′) c)
         (Sched.slots sched) burst BC
     , splitBurst-bk-caps {s = u} {u = t} (frameStep (j + j′) c)
         (Sched.slots sched) burst
  where
  B      = Caps.cSize (frameStep j c)
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  κ′     = from-inner op allNid (Sched.nextNode sched) ↠ κ
  szo    : sizeᵉ o ≤ B
  szo    = ≤ᵇ⇒≤ (sizeᵛ (obs u) o) B (T-to (proj₁ (∧-true _ _ vC)))
  pC′    : pathSz? B κ′ ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B)
                        (≤⇒≤ᵇ (≤-trans (m≤m+n (suc (pathLen κ)) (sizeᵉ o)) lC)))
                      pC)
  IH     = subscribeE-caps c j fuel o κ′ id now sched₀ st 2≤S
             (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                               sched st inv)
             szo pC′ lC
  j′     = proj₁ IH
  SUB    = proj₁ (proj₂ IH)
  BC     = proj₂ (proj₂ IH)
  res    = subscribeE fuel o κ′ id now sched₀ st
  burst  = proj₁ res
