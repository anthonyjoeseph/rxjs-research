-- STRATUM 2a-ii of Verify-Budget-Sufficient: THE SUBSCRIBE FACE.
--
-- The subscribe clique, carved out of .Caps-Face (2026-08-03).  Thirteen
-- definitions in ONE mutual block — subscribeE-caps and the companion
-- tree it is decomposed into (subscribeInner, sharedConnect, sharedSlot,
-- thruConsume, thruWalk, concatDrain, innerFinish, subscribeE-input,
-- innerReact, stepFrame-caps, pushBurst, subscribeAll) — plus the four
-- delivery leaves that CALL it (foldPath-caps, dispatchShare-caps,
-- shareGo-caps, chainStep-caps) and pushBurst's private retagEvents-caps.
--
-- WHY IT MOVED.  Nothing here is imported by anything else in .Caps-Face:
-- reverse-reachability from the clique lands on exactly those four
-- delivery leaves, and stepFrame-FACE does not call stepFrame-CAPS, so
-- the whole cascade side (cascadeGo-caps, walkH, caps-tick, reach-resets)
-- is upstream-independent.  The clique is therefore a SUFFIX of the caps
-- face, and a suffix can be its own module: this one imports .Caps-Face
-- public, so every name the rest of the tree reads is still in scope
-- through it, and a clause edit in the subscribe grind re-checks THIS
-- module only instead of .Caps-Face's eighteen minutes.
--
-- This is the .Caps / .Keeps-Ring precedent applied a third time, in the
-- other direction: .Caps was peeled off the FRONT (shared upstream),
-- this is peeled off the BACK (unshared downstream).
module Verify-Budget-Sufficient.Subscribe-Face where

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
                                sizeStep; iterSize; foldStep; iterFold;
                                fLvl; fLvlD; iterL; dLvl; lvls)

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
open import Verify-Budget-Sufficient.Caps-Face public

------------------------------------------------------------------
-- THE COUNT, FOLDED IN (2026-08-03) — and the two placeholders that
-- hold its place while the caps half stays real.
--
-- .Subscribe-Count is gone.  It said nothing: its one export was a Σ
-- whose only conjunct was upward-closed in the witness, so `0 , TODO`
-- would have discharged it and no consumer could have been the wiser.
-- The receipt is stated HERE instead, level-locked to the caps receipt,
-- because every consumer needs both at ONE level and the two families
-- turned out not to be separable after all: stepFrame-caps's payload
-- premise is `valsCaps?` — caps AND cardinality in one predicate — and
-- pushBurst-caps can only supply it from an input count, so the count
-- is an argument of the clique, not a sibling of it.
--
-- WHAT IS ACTUALLY OPEN, and it is exactly these two.  Every caps
-- conjunct in this file is ground; the NEW conjuncts — burst emit/value
-- counts, and the length half of `valsCaps?` — are not, and stand on
-- these placeholders alone.  A grep for `TODO-` is the remaining debt,
-- to the line: TWELVE count sites and `valsIn`.  The other ten count
-- sites are already DISCHARGED, by `refl`: a clause whose burst is a
-- literal one-emit envelope carrying no values (`dryBurst`, the spent
-- and register answers, `oneShotBurst []`, pushBurst's empty stream)
-- has both conjuncts reduce — `1 ≤ᵇ suc W` is `0 ≤ᵇ W` is `true` and
-- `valCountᵉ` of an init/close/complete run is `0` — at EVERY `c`, so
-- the count costs those clauses nothing at all.
--
-- HOW THEY COME OFF, in the order Phase 2 will take them:
--
--   · THE EMIT COUNT is structural.  pushBurst is 1:1 (one envelope per
--     input emit), the leaves mint exactly one, and `sharedConnect` is
--     the sole grower — by one, prepending its own `init` envelope —
--     which the `suc` in its witness already pays for.
--   · THE PAYLOAD COUNT is stepFrame's output length: map-f preserves
--     it, scan-f is one out per in, take-f is a prefix.
--   · THE THREE CONCATENATING CLAUSES LAST — thruWalk's cons,
--     concatDrain's drain-on, innerFinish's concat — because those
--     output a SUM of two counts and a sum does NOT fit the width they
--     came in under.  That is Concat-Sum-Probe's finding, machine
--     checked both concretely and structurally, and the repair is
--     already landed below: each of the three reports `suc (…)` rather
--     than `(…)`, buying one more fold, and `2 * suc W ≤ foldStep S W`
--     for `2 ≤ S` clears the sum with room.  The charge is PER CONS, so
--     the induction needs no cardinality hypothesis on the walked list
--
-- THE MARGIN IS NOT TIGHT, which is why one fold is enough and not two.
-- Concat-Sum-Probe's two worst rows, both machine-checked: `cWid
-- (frameStep 1 (caps 9 1 1)) ≡ 81` against a sum of `8 + 8 ≤ 82`, and
-- `cWid (frameStep 2 (caps 2 1 1)) ≡ 32` against `5 + 5 ≤ 33`.  The
-- summands are each at most `suc W` and one fold takes `W` to `S ^ suc
-- W ≥ 2 ^ suc W ≥ 2 * suc W`, so the doubling is covered outright.
--
-- FINDING, FOR THE (a) PASS AND NOT FOR THIS LEG (per the ruling of
-- 2026-08-03; recorded, not designed for).  Charging a fold PER CONS
-- means the level a concat clause reports at grows with the length of
-- the list it walked, and (a) — bounding `j′` by `fLvlD` — has to know
-- that growth does not outrun the iterator.  The first question (a)
-- should ask is whether the count conjuncts landing HERE already close
-- it: `vals` and `q` are unbounded UPSTREAM, but at the point a concat
-- clause runs, the walked list arrived inside a receipt whose count
-- conjunct bounds its length at that receipt's own level, and fLvlD's
-- iterators read `widAt` at CLIMBED levels rather than entry syntax.
-- Whether those two facts meet is (a)'s opening move, not this leg's
------------------------------------------------------------------

postulate
  TODO-count : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (str : Stream Γ u) →
    burstCount? c str ≡ true
  TODO-len : ∀ {A : Set} (c : Caps) (xs : List A) →
    (length xs ≤ᵇ suc (Caps.cWid c)) ≡ true

-- the payload ledger, unpacked and packed.  `valsCaps?` is the caps
-- half every clause already proves conjoined with the length half, so a
-- clause either splits one apart to feed a .Caps-Face helper (which
-- still takes the cardinality-free form) or puts one back together to
-- report.  `valsIn` is the SOLE consumer of TODO-len
valsOf : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ) (vs : List (Val Γ s)) →
  valsCaps? c sl vs ≡ true → all (valCaps? c sl s) vs ≡ true
valsOf {s = s} c sl vs h =
  proj₁ (∧-true (all (valCaps? c sl s) vs) (length vs ≤ᵇ suc (Caps.cWid c)) h)

valsIn : ∀ {n} {Γ : Ctx n} {s} (c : Caps) (sl : Slots Γ) (vs : List (Val Γ s)) →
  all (valCaps? c sl s) vs ≡ true → valsCaps? c sl vs ≡ true
valsIn c sl vs h = ∧-intro h (TODO-len c vs)

-- ONE MORE FOLD, CHARGED PER CONS.  The three concatenating clauses
-- report `suc (j₁ + j₂)` where the additive ones report `j₁ + j₂`, so
-- what they hold at `(j + j₁) + j₂` has to travel one rung further than
-- +-assoc alone would take it.  This is that rung: `(j + j₁) + j₂ ≤
-- j + suc (j₁ + j₂)`, rebracketed and bumped, then frameStep-mono-j
frameStep-+suc : ∀ (c : Caps) (j a b : ℕ) → 2 ≤ Caps.cSize c →
  frameStep ((j + a) + b) c ⊑ᶜ frameStep (j + suc (a + b)) c
frameStep-+suc c j a b 2≤S =
  frameStep-mono-j c 2≤S
    (≤-trans (≤-reflexive (+-assoc j a b))
      (≤-trans (n≤1+n (j + (a + b)))
               (≤-reflexive (sym (+-suc j (a + b))))))

-- burstCount? WIDENS.  Both conjuncts are `_ ≤ᵇ suc (cWid c)` and ⊑ᶜ
-- gives `cWid c ≤ cWid c′`, so the whole predicate rides the order —
-- the lemma that reconciles a count receipt with a caps receipt taken
-- at a lower level
burstCount?-widen : ∀ {n} {Γ : Ctx n} {u} {c c′ : Caps} (str : Stream Γ u) →
  c ⊑ᶜ c′ → burstCount? c str ≡ true → burstCount? c′ str ≡ true
burstCount?-widen {c = c} str (_ , wd≤ , _) h
  with ∧-true (length str ≤ᵇ suc (Caps.cWid c))
              (all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c)) str)
              h
... | hlen , hval =
  ∧-intro (≤ᵇ-widen (length str) (s≤s wd≤) hlen)
          (all-impl _ _
             (λ em → ≤ᵇ-widen (valCountᵉ (InstEmit.events em)) (s≤s wd≤)) str hval)

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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeE g b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)

------------------------------------------------------------------
-- (b), THE COUNT, IS THE THIRD CONJUNCT, AND IT IS LEVEL-LOCKED TO THE
-- OTHER TWO.  It cannot be an entry-level sibling: `sharedConnect`
-- PREPENDS its own `init` envelope onto the def's whole burst
-- (.Rx.Evaluator, both non-dry branches), so a ladder of k nested
-- shares hands back k+1 emits, and NOTHING in the entry hypotheses
-- bounds k — `slotsCaps?` reads each shared def POINTWISE (sizeᵉ, pWᵉ,
-- innWᵉ) and a ladder of `input` holds every one of them at 1 however
-- long it gets (Share-Count-Probe, two rows, both ⊥ at `caps 2 1 1`).
-- So it reports the SAME j′ the caps do, and it rides the same witness.
--
-- AND IT CANNOT BE A SEPARATE FAMILY EITHER.  stepFrame-caps's payload
-- premise below is `valsCaps?` — the caps AND the cardinality in one
-- predicate — because that is what the frame face consumes; the only
-- thing that can supply it is `splitEvents-valsCaps`, whose second
-- hypothesis is `valCountᵉ es ≤ suc (Caps.cWid c)`; and the only caller
-- is pushBurst-caps, which has nothing but its INPUT burst.  So the
-- count has to be an argument of this clique, not a consumer of it

subscribeInner-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
-- OUT OF GAS: a dry close and nothing else.  The only state change is
-- the instance counter, which capsOK? does not read
subscribeInner-caps c j g0 op allNid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC =
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
                    sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC =
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
  IH     = subscribeE-caps c (suc j) fuel o κ′ id now sl sched₀ st 2≤S 1≤R slEq slC slSz
             (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
                (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                  sched st inv))
             (≤-trans szo (proj₁ step⊑))
             (≤-trans wdo (proj₁ (proj₂ step⊑))) pC′
             (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₂     = proj₁ IH
  SUB    = proj₁ (proj₂ IH)
  BC     = proj₁ (proj₂ (proj₂ IH))
  res    = subscribeE fuel o κ′ id now sched₀ st
  burst  = proj₁ res
  VS     = proj₁ (splitBurst {A = Val Γ t} burst)
  BS     = proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))
  R1 : capsOK? (frameStep (j + suc j₂) c)
                (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true
  R1 = subst (λ x → capsOK? (frameStep x c)
                      (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
             (sym (+-suc j j₂)) SUB
  R2 : valsCaps? (frameStep (j + suc j₂) c) sl VS ≡ true
  R2 = valsIn (frameStep (j + suc j₂) c) sl VS
         (subst (λ x → all (valCaps? (frameStep x c) sl u) VS ≡ true)
                (sym (+-suc j j₂))
                (splitBurst-vals-caps {s = u} {u = t} (frameStep (suc j + j₂) c)
                   sl burst BC))
  R3 : all (eventCaps? (frameStep (j + suc j₂) c) sl) BS ≡ true
  R3 = subst (λ x → all (eventCaps? (frameStep x c) sl) BS ≡ true)
             (sym (+-suc j j₂))
             (splitBurst-bk-caps {s = u} {u = t} (frameStep (suc j + j₂) c)
                sl burst)

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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl d ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
-- OUT OF GAS: a dry close and nothing else
sharedConnect-caps {Γ = Γ} c j g0 i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv szd wdd pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (dryBurst {A = Val Γ (lookup Γ i)} id) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl
sharedConnect-caps {Γ = Γ} c j (gs fuel′) i d κ id now sl sched st
                   2≤S 1≤R slEq slC slSz inv szd wdd pC lC
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
          , TODO-count (frameStep (j + suc j₂) c)
              (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC slSz
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S))
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₁ (proj₂ (proj₂ IH))
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
          , TODO-count (frameStep (j + suc j₂) c)
              (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                 ∷ sharedPlumb burst)
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC slSz
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S))
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₁ (proj₂ (proj₂ IH))
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ d ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl d ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
sharedSlot-caps {Γ = Γ} c j g i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv szd wdd pC lC
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                        at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl
... | false with memberSource (toℕ i) (EvalSt.connectedShares st)
...   | true  =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
    , refl
...   | false = sharedConnect-caps c j g i d κ id now sl sched st
                  2≤S 1≤R slEq slC slSz inv szd wdd pC lC

thruConsume-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = thruConsume g op nid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MERGE: subscribe, then bump the active-inner counter
thruConsume-caps c j g mergeᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC =
  j′ , capsOK?-mergeBump (frameStep (j + j′) c) nid
         (proj₁ (proj₂ (proj₂ (proj₂ R))))
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₂ (proj₂ (proj₂ SI))
  where
  SI = subscribeInner-caps c j g mergeᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC slSz inv vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g mergeᵒ nid κ id now o sched st

-- CONCAT: park the payload if an inner is running, otherwise subscribe
-- it and reinstall an empty queue
thruConsume-caps {n = n} {u = u} c j g concatᵒ nid κ id now o sl sched st
                 2≤S 1≤R slEq slC slSz inv vC pC lC
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
         2≤S 1≤R slEq slC slSz inv vC pC lC
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
thruConsume-caps c j g switchᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC
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
         2≤S 1≤R (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq) slC slSz
         (switchKill-caps (frameStep j c) cur sched st inv) vC pC lC
  j′ = proj₁ SI
  R  = subscribeInner g switchᵒ nid κ id now o sched₁ st₁

-- EXHAUST: drop while busy, otherwise subscribe and latch
thruConsume-caps c j g exhaustᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC
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
         2≤S 1≤R slEq slC slSz inv vC pC lC
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = thruWalk g op nid κ id now vals sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
thruWalk-caps c j g op nid κ id now [] sl sched st 2≤S 1≤R slEq slC slSz inv pC vC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl
-- ONE MORE FOLD THAN THE ADDITIVE CLAUSES, and Concat-Sum-Probe is why:
-- the output is `proj₁ TC ++ proj₁ REST`, a SUM of two counts, and a sum
-- does not fit the width its two summands came in under.  `suc (j₁ + j₂)`
-- buys the extra rung, charged per cons so no cardinality hypothesis on
-- `os` is needed
thruWalk-caps {u = u} c j g op nid κ id now (o ∷ os) sl sched st
              2≤S 1≤R slEq slC slSz inv pC vC lC =
  suc (j₁ + j₂)
    , capsOK?-mono (frameStep ((j + j₁) + j₂) c) (frameStep (j + suc (j₁ + j₂)) c)
        (proj₁ (proj₂ (proj₂ REST))) (proj₂ (proj₂ (proj₂ REST)))
        ⊑ˢ (proj₁ (proj₂ IH))
    , valsIn (frameStep (j + suc (j₁ + j₂)) c) sl (proj₁ TC ++ proj₁ REST)
        (valsCaps?-widen sl u (proj₁ TC ++ proj₁ REST) ⊑ˢ
           (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl u)
              (proj₁ TC) (proj₁ REST)
              (valsCaps?-widen sl u (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                 (valsOf (frameStep (j + j₁) c) sl (proj₁ TC)
                    (proj₁ (proj₂ (proj₂ HD)))))
              (valsOf (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                 (proj₁ (proj₂ (proj₂ IH))))))
    , eventsCaps?-widen sl (proj₁ (proj₂ TC) ++ proj₁ (proj₂ REST)) ⊑ˢ
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl (proj₁ (proj₂ TC))
              (frameStep-⊑-+ c 2≤S (j + j₁) j₂) (proj₂ (proj₂ (proj₂ HD))))
           (proj₂ (proj₂ (proj₂ IH))))
  where
  vCa = valsOf (frameStep j c) sl (o ∷ os) vC
  HD  = thruConsume-caps c j g op nid κ id now o sl sched st
          2≤S 1≤R slEq slC slSz inv (proj₁ (∧-true _ _ vCa)) pC lC
  j₁  = proj₁ HD
  TC  = thruConsume g op nid κ id now o sched st
  sd₁ = proj₁ (proj₂ (proj₂ TC))
  st₁ = proj₂ (proj₂ (proj₂ TC))
  IH  = thruWalk-caps c (j + j₁) g op nid κ id now os sl sd₁ st₁
          2≤S 1≤R
          (trans (KeepsC.slotsEq (thruConsume-keeps g op nid κ id now o sched st))
                 slEq)
          slC slSz (proj₁ (proj₂ HD))
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
          (valsIn (frameStep (j + j₁) c) sl os
             (valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)
                (proj₂ (∧-true _ _ vCa))))
          (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
  j₂   = proj₁ IH
  REST = thruWalk g op nid κ id now os sd₁ st₁
  ⊑ˢ   = frameStep-+suc c j j₁ j₂ 2≤S

concatDrain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (q : List (Closed Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  all (obsCaps? (frameStep j c) sl) q ≡ true →
  let r = concatDrain g allNid κ id now q sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (obsCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
concatDrain-caps c j g allNid κ id now [] sl sched st 2≤S 1≤R slEq slC slSz inv pC lC qC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl , refl
concatDrain-caps {s = s} c j g allNid κ id now (o ∷ q) sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC qC
  with subscribeInner g concatᵒ allNid κ id now o sched st
     | subscribeInner-caps c j g concatᵒ allNid κ id now o sl sched st
         2≤S 1≤R slEq slC slSz inv (proj₁ (∧-true _ _ qC)) pC lC
     | KeepsC.slotsEq (subscribeInner-keeps g concatᵒ allNid κ id now o sched st)
-- the inner stays open: it becomes the active one and the rest of the
-- queue is parked, still bounded
... | (inst , vs , bs , false , sched₁ , st₁) | (j₁ , SUB , VC , EC) | sEq =
  j₁ , SUB , VC , EC
     , obsListCaps?-widen sl q (frameStep-⊑-+ c 2≤S j j₁) (proj₂ (∧-true _ _ qC))
-- the inner completed synchronously: drain on, and the two receipts add
-- PLUS ONE — `vs ++ proj₁ REST` is a SUM of two counts, so this clause
-- pays the extra fold Concat-Sum-Probe showed the sum needs
... | (inst , vs , bs , true , sched₁ , st₁) | (j₁ , SUB , VC , EC) | sEq =
  suc (j₁ + j₂)
    , capsOK?-mono (frameStep ((j + j₁) + j₂) c) (frameStep (j + suc (j₁ + j₂)) c)
        (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ REST)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ REST)))))
        ⊑ˢ (proj₁ (proj₂ IH))
    , valsIn (frameStep (j + suc (j₁ + j₂)) c) sl (vs ++ proj₁ REST)
        (valsCaps?-widen sl s (vs ++ proj₁ REST) ⊑ˢ
           (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl s) vs (proj₁ REST)
              (valsCaps?-widen sl s vs (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                 (valsOf (frameStep (j + j₁) c) sl vs VC))
              (valsOf (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                 (proj₁ (proj₂ (proj₂ IH))))))
    , eventsCaps?-widen sl (bs ++ proj₁ (proj₂ REST)) ⊑ˢ
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl) bs
           (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl bs (frameStep-⊑-+ c 2≤S (j + j₁) j₂) EC)
           (proj₁ (proj₂ (proj₂ (proj₂ IH)))))
    , obsListCaps?-widen sl (proj₁ (proj₂ (proj₂ (proj₂ REST)))) ⊑ˢ
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  where
  IH   = concatDrain-caps c (j + j₁) g allNid κ id now q sl sched₁ st₁
           2≤S 1≤R (trans sEq slEq) slC slSz SUB
           (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
           (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
           (obsListCaps?-widen sl q (frameStep-⊑-+ c 2≤S j j₁)
              (proj₂ (∧-true _ _ qC)))
  j₂   = proj₁ IH
  REST = concatDrain g allNid κ id now q sched₁ st₁
  ⊑ˢ   = frameStep-+suc c j j₁ j₂ 2≤S

-- .Caps-Face's innerFinish-zero still speaks the cardinality-free
-- payload form, and .Caps-Face is not touched this leg, so its twenty-odd
-- call sites below go through this one adapter: unpack with valsOf on the
-- way in, repack with valsIn on the way out
innerFinish-zero′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (sl : Slots Γ) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (frameStep j c) sched st ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl vals ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) []
          ≡ true)
innerFinish-zero′ {t = t} c j sl vals sched st inv vC =
  proj₁ Z , proj₁ (proj₂ Z)
    , valsIn (frameStep (j + proj₁ Z) c) sl vals (proj₁ (proj₂ (proj₂ Z)))
    , proj₂ (proj₂ (proj₂ Z))
  where
  Z = innerFinish-zero {t = t} c j sl vals sched st inv
        (valsOf (frameStep j c) sl vals vC)

innerFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MERGE: decrement the active-inner counter, which carries no payload
innerFinish-caps c j g mergeᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | just (merge-st k od) =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (merge-st (pred k) od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (merge-st (pred k) od)
               sched st refl refl inv)
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
... | nothing                = innerFinish-zero′ c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero′ c j sl vals sched st inv vC
... | just (switch-st _ _)   = innerFinish-zero′ c j sl vals sched st inv vC
... | just (exhaust-st _ _)  = innerFinish-zero′ c j sl vals sched st inv vC

-- CONCAT: drain the queue and reinstall the residue, which comes back
-- from concatDrain-caps with the very bound the node needs
innerFinish-caps {n = n} {s = s} c j g concatᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) allNid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
... | nothing              | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (scan-st _)     | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (take-st _)     | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (merge-st _ _)  | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (switch-st _ _) | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (exhaust-st _ _) | _ = innerFinish-zero′ c j sl vals sched st inv vC
... | just (concat-st {w} q act od) | (bn , wn) with w ≟ᵗ s
...   | no _     = innerFinish-zero′ c j sl vals sched st inv vC
-- `vals ++ proj₁ DR` is the third SUM, so this clause too reports one
-- fold beyond what concatDrain handed back
...   | yes refl =
  suc j′ , capsOK?-mono (frameStep (j + j′) c) (frameStep (j + suc j′) c) sd₁ ST₁ ⊑ˢ
         (capsOK?-setNode (frameStep (j + j′) c) allNid
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
            (proj₁ (proj₂ CD)))
     , valsIn (frameStep (j + suc j′) c) sl (vals ++ proj₁ DR)
         (valsCaps?-widen sl s (vals ++ proj₁ DR) ⊑ˢ
            (all-++-intro (valCaps? (frameStep (j + j′) c) sl s) vals (proj₁ DR)
               (valsCaps?-widen sl s vals (frameStep-⊑-+ c 2≤S j j′)
                  (valsOf (frameStep j c) sl vals vC))
               (valsOf (frameStep (j + j′) c) sl (proj₁ DR)
                  (proj₁ (proj₂ (proj₂ CD))))))
     , eventsCaps?-widen sl (proj₁ (proj₂ DR)) ⊑ˢ
         (proj₁ (proj₂ (proj₂ (proj₂ CD))))
  where
  CD  = concatDrain-caps c j g allNid κ id now q sl sched st
          2≤S 1≤R slEq slC slSz inv pC lC
          (obsList-intro (frameStep j c) sl q bn
             (subst (λ y → all (λ o → pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) q
                             ≡ true)
                    slEq wn))
  j′  = proj₁ CD
  ⊑ˢ  = frameStep-mono-j c 2≤S
          (≤-trans (n≤1+n (j + j′)) (≤-reflexive (sym (+-suc j j′))))
  RES = proj₂ (proj₂ (proj₂ (proj₂ CD)))
  DR  = concatDrain g allNid κ id now q sched st
  sd₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  ST₁ = record st₁
          { nodes = setNode allNid
                      (concat-st (proj₁ (proj₂ (proj₂ (proj₂ DR))))
                                 (proj₁ (proj₂ (proj₂ DR))) od)
                      (EvalSt.nodes st₁) }

-- SWITCH: clear the current-inner slot if this was it
innerFinish-caps c j g switchᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero′ c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (merge-st _ _)    = innerFinish-zero′ c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero′ c j sl vals sched st inv vC
... | just (exhaust-st _ _)  = innerFinish-zero′ c j sl vals sched st inv vC
... | just (switch-st nothing od) = innerFinish-zero′ c j sl vals sched st inv vC
... | just (switch-st (just cur) od) with cur ≡ᵇ inst
...   | false = innerFinish-zero′ c j sl vals sched st inv vC
...   | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (switch-st nothing od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (switch-st nothing od)
               sched st refl refl inv)
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

-- EXHAUST: clear the busy flag
innerFinish-caps c j g exhaustᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero′ c j sl vals sched st inv vC
... | just (scan-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (take-st _)       = innerFinish-zero′ c j sl vals sched st inv vC
... | just (merge-st _ _)    = innerFinish-zero′ c j sl vals sched st inv vC
... | just (concat-st _ _ _) = innerFinish-zero′ c j sl vals sched st inv vC
... | just (switch-st _ _)   = innerFinish-zero′ c j sl vals sched st inv vC
... | just (exhaust-st act od) =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (exhaust-st false od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (exhaust-st false od)
               sched st refl refl inv)
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl

subscribeE-input-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (j : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
subscribeE-input-caps {n = n} {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC slSz inv pC lC
  with Sched.slots sched i
     | subst (λ y → slotCaps? (Caps.cSize c) (Caps.cWid c) sl (y i) ≡ true) (sym slEq)
             (slotsCaps?-lookup (Caps.cSize c) (Caps.cWid c) sl i slC)
-- SHARED: the def's size, and — since the parked-width repair — its
-- parked width, are the two things sharedSlot-caps asks for.  Both come
-- straight out of the slot telescope's own side condition
... | shared d | sd =
  sharedSlot-caps c j g i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv
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
    , refl
...   | false =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j)) refl
    , refl
-- COLD, NO TAIL: a one-shot burst of the slot's own sync values, and
-- nothing goes into the state but a source counter capsOK? does not read
subscribeE-input-caps {Γ = Γ} c j g i κ id now sl sched st
                      2≤S 1≤R slEq slC slSz inv pC lC
  | scripted {ok} (cold sync []) | sd =
  1 , subst (λ x → capsOK? (frameStep x c)
                     (proj₂ (oneShotBurst sync id sched)) st ≡ true)
            (sym (j+1 j))
            (capsOK?-mono (frameStep j c) (frameStep (suc j) c)
               (proj₂ (oneShotBurst sync id sched)) st step⊑ inv)
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (proj₁ (oneShotBurst sync id sched)) ≡ true)
            (sym (j+1 j))
            (burstCaps?-widen sl (proj₁ (oneShotBurst sync id sched)) step⊑
              (∧-intro (∧-intro refl
                          (all-++-intro (eventCaps? (frameStep j c) sl)
                             (map value sync) _
                             (mapValue-caps (frameStep j c) sl (lookup Γ i) sync SY)
                             refl))
                       refl))
    , TODO-count (frameStep (j + 1) c)
        (proj₁ (oneShotBurst sync id sched))
  where
  step⊑ = frameStep-mono-j c 2≤S (n≤1+n j)
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
                      2≤S 1≤R slEq slC slSz inv pC lC
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
    , TODO-count (frameStep (j + 1) c)
        (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
innerReact-caps c j g op allNid inst κ id now vals false sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
innerReact-caps c j g op allNid inst κ id now vals true sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl
... | false = innerFinish-caps c j g op allNid inst κ id now vals sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC

stepFrame-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (j : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  let r = stepFrame g id now f κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)

-- MAP: nothing touches the state, so the invariant is only widened
stepFrame-caps {u = u} c j g id now (map-f fn) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC =
  j′ , capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
         (frameStep-⊑-+ c 2≤S j j′) inv
     , valsIn (frameStep (j + j′) c) sl (map (applyFn fn) vals) (proj₂ MP)
     , refl
  where
  MP = mapFrame-caps c j sl fn vals 2≤S slC fS
         (valsOf (frameStep j c) sl vals vC)
  j′ = proj₁ MP

-- SCAN: its own top-level lemma, as in the wet family — the nested
-- `with` on the stored accumulator's type cannot be elaborated inside a
-- clause of the general frame case
stepFrame-caps c j g id now (scan-f fn nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC =
  proj₁ SC , proj₁ (proj₂ SC)
    , valsIn (frameStep (j + proj₁ SC) c) sl
        (proj₁ (stepFrame g id now (scan-f fn nid) κ vals fin sched st))
        (proj₁ (proj₂ (proj₂ SC)))
    , proj₂ (proj₂ (proj₂ SC))
  where
  SC = stepFrame-scan-caps c j g id now fn nid κ vals fin sl sched st
         2≤S slC slEq inv fS pS (valsOf (frameStep j c) sl vals vC)

-- TAKE: a prefix and a cut, no folds
stepFrame-caps c j g id now (take-f nid) κ vals fin sl sched st 2≤S 1≤R slEq slC slSz inv fS pS lC vC =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ (proj₂ (proj₂ TD))))
                     (proj₂ (proj₂ (proj₂ (proj₂ TD)))) ≡ true)
            (sym (+-identityʳ j)) (proj₁ TDc)
    , subst (λ x → valsCaps? (frameStep x c) sl (proj₁ TD) ≡ true)
            (sym (+-identityʳ j))
            (valsIn (frameStep j c) sl (proj₁ TD) (proj₁ (proj₂ TDc)))
    , subst (λ x → all (eventCaps? (frameStep x c) sl) (proj₁ (proj₂ TD)) ≡ true)
            (sym (+-identityʳ j)) (proj₂ (proj₂ TDc))
  where
  TD  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  TDc = takeDispatch-caps (frameStep j c) nid vals fin sl sched st
          (lookupNode nid (EvalSt.nodes st)) slEq inv
          (valsOf (frameStep j c) sl vals vC)

-- FROM-INNER and THRU-OUTER: the two *All edges, delegated whole
stepFrame-caps c j g id now (from-inner op allNid inst) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC =
  innerReact-caps c j g op allNid inst κ id now vals fin sl sched st
    2≤S 1≤R slEq slC slSz inv pS lC vC

stepFrame-caps c j g id now (thru-outer op nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC =
  j′ , proj₁ WR
     , valsIn (frameStep (j + j′) c) sl (proj₁ (thruWrap op nid fin WK))
         (proj₁ (proj₂ WR))
     , proj₂ (proj₂ WR)
  where
  TW = thruWalk-caps c j g op nid κ id now vals sl sched st
         2≤S 1≤R slEq slC slSz inv pS vC lC
  j′ = proj₁ TW
  WK = thruWalk g op nid κ id now vals sched st
  WR = thruWrap-caps (frameStep (j + j′) c) op nid fin sl WK
         (proj₁ (proj₂ TW))
         (valsOf (frameStep (j + j′) c) sl (proj₁ WK)
            (proj₁ (proj₂ (proj₂ TW))))
         (proj₂ (proj₂ (proj₂ TW)))

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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  frameSz? (Caps.cSize (frameStep j c)) f ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  burstCaps? (frameStep j c) sl str ≡ true →
  burstCount? (frameStep j c) str ≡ true →
  let r = pushBurst g id now f κ str sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
pushBurst-caps {u = u} c j g id now f κ [] sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC bC cC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
    , refl
pushBurst-caps {Γ = Γ} {s = s} {u = u} c j g id now f κ (em ∷ ems) sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC bC cC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl
        (((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST)
        (∧-intro EMIT (proj₁ (proj₂ (proj₂ IH))))
    , TODO-count (frameStep (j + (j₁ + j₂)) c)
        (((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST)
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ u} E
  eC   = proj₁ (∧-true _ _ bC)
  cntW = suc (Caps.cWid (frameStep j c))
  cntP : InstEmit (Val Γ s) → Bool
  cntP em′ = valCountᵉ (InstEmit.events em′) ≤ᵇ cntW
  cCv  = proj₂ (∧-true (length (em ∷ ems) ≤ᵇ cntW) (all cntP (em ∷ ems)) cC)
  cntE = ≤ᵇ⇒≤ (valCountᵉ E) cntW
           (T-to (proj₁ (∧-true (cntP em) (all cntP ems) cCv)))
  SF   = stepFrame-caps c j g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sl sched st
           2≤S 1≤R slEq slC slSz inv fS pS lC
           (splitEvents-valsCaps {u = u} (frameStep j c) sl E eC cntE)
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
           slC slSz
           (proj₁ (proj₂ SF))
           (frameSz?-widen f (proj₁ ⊑₁) fS)
           (pathSz?-⊑ κ ⊑₁ pS)
           (≤-trans lC (proj₁ ⊑₁))
           (burstCaps?-widen sl ems ⊑₁ (proj₂ (∧-true _ _ bC)))
           (TODO-count (frameStep (j + j₁) c) ems)
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
                       (valsOf (frameStep (j + j₁) c) sl (proj₁ step)
                          (proj₁ (proj₂ (proj₂ SF))))))
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
  slotsSize sl ≤ Caps.cSize c →
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
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
subscribeAll-caps {Γ = Γ} {t = t} {u = u} c j g op ns b κ id now sl sched st
                  2≤S 1≤R slEq slC slSz inv bn wn szb wdb pC lC =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₁ (proj₂ (proj₂ PBc))))
    , TODO-count (frameStep (j + suc (j₁ + j₂)) c) (proj₁ PB)
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
  SUB = subscribeE-caps c (suc j) g b κ′ id now sl sched₀ st₀ 2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
  j₁  = proj₁ SUB
  res = subscribeE g b κ′ id now sched₀ st₀
  PBc = pushBurst-caps c (suc j + j₁) g id now (thru-outer op nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq (subscribeE-keeps g b κ′ id now sched₀ st₀)) slEq)
          slC slSz (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁)
             (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₂ (proj₂ (proj₂ SUB)))
  j₂  = proj₁ PBc
  PB  = pushBurst g id now (thru-outer op nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

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
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  subscribeE-input-caps c j g i κ bid now sl sched st 2≤S 1≤R slEq slC slSz inv pC lC

-- LITERALS: one shot, and the payloads come off evalTms-caps.  The
-- state is untouched; only the source counter moves, which capsOK?
-- does not read
subscribeE-caps {n = n} {u = u} c j g (ofᵉ ts) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  j₀ , capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st
         (frameStep-⊑-+ c 2≤S j j₀) inv
     , ∧-intro (∧-intro refl
                  (all-++-intro (eventCaps? (frameStep (j + j₀) c) sl)
                     (map value (map (λ tm → evalTm tm) ts)) _
                     (mapValue-caps (frameStep (j + j₀) c) sl u
                        (map (λ tm → evalTm tm) ts) (proj₂ EV))
                     refl))
               refl
     , TODO-count (frameStep (j + j₀) c)
         (proj₁ (oneShotBurst (map (λ tm → evalTm tm) ts) bid sched))
  where
  EV = evalTms-caps c j sl ts 2≤S slC (≤-trans (n≤1+n (sizeᵗˢ ts)) szb) wdb
  j₀ = proj₁ EV

subscribeE-caps {u = u} c j g emptyᵉ κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl

-- MAP: one more frame on the chain, so one j, then the burst comes back
-- through that same frame
subscribeE-caps {n = n} {t = t} {u = u} c j g (mapᵉ f b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-caps c (suc j) j₁ j₂
               (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) (proj₁ (proj₂ PBc)))
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-burst c (suc j) j₁ j₂ sl (proj₁ PB)
               (proj₁ (proj₂ (proj₂ PBc))))
    , TODO-count (frameStep (j + suc (j₁ + j₂)) c) (proj₁ PB)
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
          2≤S 1≤R slEq slC slSz
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
          slC slSz (proj₁ (proj₂ SUB))
          (frameSz?-widen (map-f f) (proj₁ ⊑₁) fS′)
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₂ (proj₂ (proj₂ SUB)))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (map-f f) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- TAKE: `take 0` never subscribes its source — a spent one-shot, exactly
-- emptyᵉ.  Otherwise a node is installed (trivially bounded on both
-- axes) and the source runs under one more frame
subscribeE-caps {n = n} {u = u} c j g (takeᵉ cnt b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC
  with evalTm cnt
... | zero =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl
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
               (proj₁ (proj₂ (proj₂ PBc))))
    , TODO-count (frameStep (j + suc (j₁ + j₂)) c) (proj₁ PB)
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
          2≤S 1≤R slEq slC slSz inv₀
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
          slC slSz (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₂ (proj₂ (proj₂ SUB)))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (take-f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- SCAN: the accumulator is BUILT, by evalTm, so the node's two bounds
-- come off evalSeed-caps and cost a receipt of their own before the
-- source is even subscribed
subscribeE-caps {n = n} {u = u} c j g (scanᵉ f z b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
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
                  (proj₁ (proj₂ (proj₂ PBc)))))
    , TODO-count (frameStep (j + (j₀ + suc (j₁ + j₂))) c) (proj₁ PB)
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
          sched₀ st₀ 2≤S 1≤R slEq slC slSz inv₀
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
          slC slSz (proj₁ (proj₂ SUB))
          (frameSz?-widen (scan-f f nid) (proj₁ ⊑₁)
             (proj₁ (∧-true _ _ pC′)))
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ (pathSz?-⊑ κ ⊑₀ pC)))
          (≤-trans (≤-trans lC (≤-trans (proj₁ ⊑₀) (proj₁ step⊑))) (proj₁ ⊑₁))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₂ (proj₂ (proj₂ SUB)))
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (scan-f f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- THE FOUR *All HEADS: subscribeAll-caps, whole.  Every initial node
-- state is bounded on both axes by refl
subscribeE-caps {n = n} c j g (mergeAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  subscribeAll-caps c j g mergeᵒ (merge-st 0 false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} {u = u} c j g (concatAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  subscribeAll-caps c j g concatᵒ (concat-st {t = u} [] false false) b κ bid now
    sl sched st 2≤S 1≤R slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} c j g (switchAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  subscribeAll-caps c j g switchᵒ (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
subscribeE-caps {n = n} c j g (exhaustAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  subscribeAll-caps c j g exhaustᵒ (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC

-- μ: out of gas is a dry close; with gas, ONE unfolding — larger than
-- the μ on the size axis (unfoldμ-size buys the room) and no larger on
-- the width axis (dW-unfoldμ)
subscribeE-caps {u = u} c j g0 (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (dryBurst {A = Val _ u} bid) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl
subscribeE-caps {n = n} c j (gs fuel) (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  j₀ + j₁
    , frameStep-+assoc-caps c j j₀ j₁ (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₀ j₁ sl (proj₁ res)
        (proj₁ (proj₂ (proj₂ IH)))
    , TODO-count (frameStep (j + (j₀ + j₁)) c) (proj₁ res)
  where
  US = unfoldμ-caps c j sl body 2≤S slC szb wdb
  j₀ = proj₁ US
  ⊑₀ = frameStep-⊑-+ c 2≤S j j₀
  IH = subscribeE-caps c (j + j₀) fuel (unfoldμ body) κ bid now sl sched st
         2≤S 1≤R slEq slC slSz
         (capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st ⊑₀ inv)
         (proj₁ (proj₂ US))
         (proj₂ (proj₂ US))
         (pathSz?-⊑ κ ⊑₀ pC)
         (≤-trans lC (proj₁ ⊑₀))
  j₁ = proj₁ IH
  res = subscribeE fuel (unfoldμ body) κ bid now sched st

subscribeE-caps c j g (varᵉ ()) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC

-- DEFER: the clause the parked width exists for.  Install the merge
-- node, mint the source and ordinal, PARK the body as a one-element
-- pending, and register the thru-outer chain — one j, for the
-- registration.  The LiveSource's width bound IS the telescope's dW
-- conjunct: `dWᵉ (deferᵉ body)` is `pWᵉ body`, definitionally
subscribeE-caps {n = n} {Γ = Γ} {u = u} c j g (deferᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC =
  1 , subst (λ x → capsOK? (frameStep x c) SCHED₄
                     (register SRC (thru-outer mergeᵒ nid ↠ κ) st₀) ≡ true)
            (sym (j+1 j))
            (capsOK?-addLive (frameStep (suc j) c) NEW SCHED₃
               (register SRC (thru-outer mergeᵒ nid ↠ κ) st₀) BL WL REG)
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (((init SRC ∷ []) at bid from SRC as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
    , refl
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  all (λ rp → pathSz? (Caps.cSize (frameStep j c)) (proj₂ rp)) ps ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  let r = shareGo sf gas id now i vals fin ps sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

-- ROOT: the chain's sink.  Nothing steps, so j′ = 0 and the only work
-- is assembling one emit out of bounds already in hand
foldPath-caps c j sf gas id now envSrc root vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC =
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
                          (mapValue-caps (frameStep j c) sl _ vals
                             (valsOf (frameStep j c) sl vals vC))
                          (finList-caps (frameStep j c) sl fin)))
                     refl)

-- SHARE SINK: the chain emits its own (valueless) handoff and the share
-- fans out.  The handoff emit is built at the entry level and widened
-- to the fan-out's exit level exactly once
foldPath-caps c j sf gas id now envSrc (share-sink i) vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC =
  j₁ , proj₁ (proj₂ DS)
     , ∧-intro (all-++-intro (eventCaps? (frameStep (j + j₁) c) sl) evs _
                  (eventsCaps?-widen sl evs (frameStep-⊑-+ c 2≤S j j₁) eC)
                  refl)
               (proj₂ (proj₂ DS))
  where
  DS = dispatchShare-caps c j sf gas id now i vals fin sl sched st
         2≤S 1≤R slEq slC slSz inv vC
  j₁ = proj₁ DS

-- ONE FRAME, THEN THE REST OF THE CHAIN.  j₁ pays the frame, j₂ the
-- tail, and the clause reports j₁ + j₂ — the additive composition,
-- rebracketed by +-assoc and nothing else
foldPath-caps c j sf gas id now envSrc (f ↠ p) vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl (proj₁ REST) (proj₂ (proj₂ IH))
  where
  B    = Caps.cSize (frameStep j c)
  pS1  = ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) pS
  pS2  = ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) (proj₂ pS1)
  SF   = stepFrame-caps c j sf id now f p vals fin sl sched st
           2≤S 1≤R slEq slC slSz inv (proj₁ pS1) (proj₂ pS2)
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
           slC slSz
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
                   2≤S 1≤R slEq slC slSz inv vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
dispatchShare-caps c j sf (suc gas) id now i vals fin sl sched st 2≤S 1≤R slEq slC slSz inv vC =
  j₁ , proj₁ FIN , proj₂ FIN
  where
  st₀ = shareLatch i fin st
  GO  = shareGo-caps c j sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sl sched st₀
          2≤S 1≤R slEq slC slSz (shareLatch-caps (frameStep j c) i fin sched st inv)
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
             2≤S 1≤R slEq slC slSz inv pS vC =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
shareGo-caps {Γ = Γ} c j sf gas id now i vals fin ((rid , p) ∷ ps) sl sched st
             2≤S 1≤R slEq slC slSz inv pS vC
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-caps c j sf gas id now i vals fin ps sl sched st
                2≤S 1≤R slEq slC slSz inv (proj₂ (∧-true _ _ pS)) vC
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
          2≤S 1≤R slEq slC slSz (capsOK?-delivered (frameStep j c) rid sched st inv)
          (proj₁ (∧-true _ _ pS)) vC
          (closeList-caps (frameStep j c) sl (toℕ i) fin)
  j₁  = proj₁ HD
  FP  = foldPath sf gas id now (toℕ i) p vals cl fin sched st₀
  IH  = shareGo-caps c (j + j₁) sf gas id now i vals fin ps sl
          (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
          2≤S 1≤R
          (trans (foldPath-slots sf gas id now (toℕ i) p vals cl fin sched st₀)
                 slEq)
          slC slSz
          (proj₁ (proj₂ HD))
          (pathsSz?-⊑ ps (frameStep-⊑-+ c 2≤S j j₁) (proj₂ (∧-true _ _ pS)))
          (valsCaps?-lvl (frameStep j c) (frameStep (j + j₁) c) sl vals
             (frameStep-⊑-+ c 2≤S j j₁) vC)
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
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) path ≡ true →
  valCaps? (frameStep j c) sl (arrTy a) (arrVal a) ≡ true →
  let r = chainStep id a path sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
chainStep-caps {n = n} {e = e} c j id a path sl sched st 2≤S 1≤R slEq slC slSz inv pS vC =
  foldPath-caps c j (budgetAt e (Sched.slots sched) id) n id (arrTick a)
    (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sl sched st
    2≤S 1≤R slEq slC slSz inv pS (∧-intro (∧-intro vC refl) refl)
    (closeList-caps (frameStep j c) sl (arrSource a) (Arrival.isLast a))
