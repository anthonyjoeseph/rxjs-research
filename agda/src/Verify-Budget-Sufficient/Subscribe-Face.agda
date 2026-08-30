-- STRATUM 2a-ii of Verify-Budget-Sufficient: THE SUBSCRIBE FACE.

-- The subscribe clique, carved out of .Caps-Face.  Thirteen
-- definitions in ONE mutual block — subscribeE-caps and the companion
-- tree it is decomposed into (subscribeInner, sharedConnect, sharedSlot,
-- thruConsume, thruWalk, mergeAllDrain, innerFinish, subscribeE-input,
-- innerReact, stepFrame-caps, pushBurst, subscribeAll) — plus the three
-- delivery leaves that CALL it (foldPath-caps, dispatchShare-caps,
-- shareGo-caps) and pushBurst's private retagEvents-caps.

-- WHY IT MOVED.  Nothing here is imported by anything else in .Caps-Face:
-- reverse-reachability from the clique lands on exactly those three
-- delivery leaves, and stepFrame-FACE does not call stepFrame-CAPS, so
-- the whole cascade side (cascadeGo-caps, walkH, caps-tick, reach-resets)
-- is upstream-independent.  The clique is therefore a SUFFIX of the caps
-- face, and a suffix can be its own module: consumers name what they
-- need from .Caps-Face directly, and a clause edit in the subscribe
-- grind re-checks THIS
-- module only instead of .Caps-Face's eighteen minutes.

-- This is the .Caps / .Keeps-Ring precedent applied a third time, in the
-- other direction: .Caps was peeled off the FRONT (shared upstream),
-- this is peeled off the BACK (unshared downstream).

-- TIMING, measured (--profile=definitions then --profile=internal,
-- genuinely dirty solo check): 927s total, and the cost is NOT the proofs —
-- every definition here typechecks in ~18s combined (largest: subscribeE-caps
-- 2.9s).  The bill is POSITIVITY 779s (86%) and Termination.Graph 92s (10%),
-- both whole-mutual-block analyses.  Consequences, so nobody re-derives them:
--   * The 779s is the OCCURRENCE/POLARITY graph, not the strict-positivity
--     verdict, and it CANNOT BE SWITCHED OFF.  A NO_POSITIVITY_CHECK pragma
--     is invalid on a function-only block (InvalidNoPositivityCheckPragma, it
--     is a no-op); `--no-positivity-check` on the command line is REJECTED
--     (written without pragma delimiters on purpose: `make unsafe-check` greps
--     for the delimited form and does not strip comments, so quoting a pragma
--     verbatim in prose FAILS THE GATE, which has happened)
--     outright because agda-stdlib is --safe (EXIT=42 in 267ms); and as a
--     per-module OPTIONS pragma it is accepted but measured 805s vs 779s —
--     NO SAVING.  Do not re-attempt any of these three.
--   * The TELESCOPES are not the cost either: all 19 clique signatures as bare
--     postulates check in 9.0s (5.3s of that merely deserializing imports).
--     Record-bundling the hypothesis kit would buy nothing measurable.
--   * MUTUAL-BLOCK MEMBERSHIP is the whole cost, and it is steeply superlinear:
--     ONE real body in the block puts Positivity at 3.0s, fifteen put it at
--     779s.  The 904-line prelude below (~45 lemmas, each its own trivial
--     block) checks in 7.8s.
--   * The block cannot be split much: 13 of the 15 members form ONE genuine
--     SCC (four independent cycles traced).  Only `innerFinish-zero′` and
--     `retagEvents-caps` are pure callees and could be hoisted out, 15 -> 13.
--   * What DOES work: check one member's real body against its siblings as
--     POSTULATES — 17.7s, and 4 such checks run in parallel in 14s at ~120 MB
--     each.  This is what `make agda-dev` is being built on.
--   * AGDA 2.8.0 + stdlib v2.3 cuts this module's solo dirty check from 927s
--     to 384s — Positivity 779s -> 300s, a 2.6x cut, measured like-for-like
--     (solo, warm deps, 1 module).  Whole repo green under 2.8 (40 modules,
--     EXIT=0).  This is the ONLY lever found that reduces the pass itself; it
--     does not remove the need for the stub loop, since 384s is still minutes.
-- See typecheck-performance-numbers.md for the numbers, the plan, and the traps.
module Verify-Budget-Sufficient.Subscribe-Face where

open import Data.Bool    using (Bool; true; false; T; _∧_; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; _⊔_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤ᵇ⇒≤; ≤⇒≤ᵇ; ≤-trans; ≤-refl; ≤-reflexive; ≤-pred; +-suc; +-identityʳ; +-comm; +-assoc;
  +-monoˡ-≤; *-monoʳ-≤; *-suc; m≤m+n; m≤n+m; n≤1+n; +-mono-≤; ^-monoʳ-≤; *-identityʳ;
  ^-monoˡ-≤; ^-distribˡ-+-*; *-mono-≤; +-monoʳ-≤; m≤m⊔n; m≤n⊔m)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.List.Properties using (length-++; length-map)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)

open import Rx.Prim      using (Tick; Id; Source; InstEmit; _at_from_as_; subscribe; InstEvent; init; value; close; handoff;
  complete; exhausted; delivery; Gas; g0; gs; Timed; after_,_; hot; cold)
open import Rx.Exp       using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; _≟ᵗ_; inputsBelowᵉ; Ctx; Closed; Val; sizeᵉ; sizeᵗ;
  sizeᵗˢ; sizeᵛ; Fn; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ; evalTm; applyFn)
open import Rx.Frame-Width using (pWᵉ; pWᵛ; dWᵉ; dWᵗ)
open import Rx.Evaluator using (Sched; EvalSt; resolve; memberSource; RegId; NodeState; scan-st; take-st;
  mergeAll-st; switch-st; exhaust-st; hasRoom; oneShotBurst; installNode; setNode; lookupNode; NodeId;
  root; share-sink; _↠_; Frame; AllOp; map-f; scan-f; take-f; from-inner; thru-outer; Stream;
  takeDispatch; dropSource; Path; subscribeE; stepFrame; pushBurst; subscribeInner;
  subscribeAll; register; mergeAllᵒ; switchᵒ; exhaustᵒ; splitEvents; splitBurst;
  retagEvents; switchKill; thruConsume; thruWalk; thruWrap; mergeAllDrain; innerFinish;
  innerReact; sharedPlumb; sharedConnect; subscribeSharedSlot; burstCompleted; shareLatch;
  shareAdmit; shareGo; dryBurst; foldPath; dispatchShare; aliveThroughᶠ; sizeStep; iterSize;
  foldStep; iterFold; fLvlD; sizeAt; sIterD; sLvlD; opIterD; fIterD; sLvlD-suc)
open import Rx.Slots using (inputSize; scripted; shared; Slots; slotSize; slotsSize)
open import Rx.MergeAll-Laws using (drain-queue-shrinks; drain-queue-all)
open import Rx.Clos-Size using (closSize≤mulᵉ)
open import Rx.Slot-Clos using (slotClos)

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
open import Verify-Budget-Sufficient.Caps-Face.Part5 using
  (capsOK?-addLive; cSize≤frameStep; cWid≤frameStep; face-charge1; face-vals;
   innerFinish-zero; mapFrame-caps; resolve-caps; resolve-wid-data;
   scanVals-len; stepFrame-scan-caps; takeDispatch-len; valsCaps?-data)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-delivered; capsOK?-mergeAllBump; capsOK?-nextNode; capsOK?-nodeSz;
   capsOK?-nodeWid; capsOK?-regs; capsOK?-setNode; dropOnly-caps;
   foldPath-slots; frameBud; j+1; lookupNode-caps;
   capsOK?-nodePark; parkList-push; mList?; mList?-head;
   mList?-keeps; mList?-tail; obsList-intro; obsList-nodeSz; obsList-nodeWid;
   obsList→mList-strict; register-caps; shareAdmit-caps; sharedPlumb-caps;
   shareFinish-caps; shareLatch-caps; splitBurst-bk-caps; splitBurst-vals-caps;
   splitEvents-bk-caps; splitEvents-len; splitEvents-valsCaps; switchKill-caps;
   switchKill-closes-caps; takeDispatch-caps; thruWrap-caps; valsCaps?;
   valsCaps?-lvl; valsCaps→mList-strict)
open import Verify-Budget-Sufficient.Measures using
  (2X≡X+X; all-++-intro; all-impl; lookupNode-park;
                                                      boundedLive; boundedNode; parkRoom; fᵢ≤sum-tab;
                                                      n<2^n; pathLen; sizeᵉ-pos; syncSize≤sizeᵉ; ∧-true)
open import Verify-Budget-Sufficient.Caps-Nest using
  (exhaust-step; mergeAll-step; map-step; mu-step; nest; nest-keeps;
   resid; scan-step; share-step; switch-step; take-step)
open import Verify-Budget-Sufficient.Caps using
  (1≤pow≤; _⊑ᶜ_; Caps; frameStep; frameStep-mono-j; frameStep-size-suc;
   frameStep-wid-suc; iterFold-mono-count; iterFold-suc; iterSize-suc)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; capsOK?-mono;
   eventCaps?; frameSz?; k≤iterFold; len≤sizeᵗˢ; obsCaps?; pathSz?; slotCaps?;
   slotsCaps?; slotsCaps?-lookup; suc≤foldStep; valCaps?; valCountᵉ; widLive;
   widNode; widNode-push; nestClosOK?; closLive; closLive-data; slotsCaps?-clos)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (2≤frameStep-size; burstCaps?-++; burstCaps?-widen; closeList-caps;
   eventsCaps?-widen; finList-caps; frameStep-+assoc-burst;
   frameStep-+assoc-caps; frameStep-chain-suc; frameStep-size-strict-suc;
   frameStep-⊑-+; frameSz?-widen; mapValue-caps; obsListCaps?-widen;
   pathsSz?-⊑; pathSz?-⊑; valCaps?-size; valCaps?-wid; valCaps?-widen;
   valsCaps?-widen; ⊑ᶜ-trans)
open import Verify-Budget-Sufficient.Caps-Term using
  (evalSeed-caps; evalTms-caps; unfoldμ-caps)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (concat-fits; dbl-suc; double≤foldStep; frameStep-+suc; lenWiden;
   thruWrap-vals; valsIn; valsLen; valsOf)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (mergeAllDrain-keeps; KeepsC; stepFrame-keeps; subscribeE-keeps;
   subscribeInner-keeps; switchKill-keeps; thruConsume-keeps)
-- the composition gate, and `chain-desc`: the supply an operator clause
-- spends when it splits its index and hands the source the predecessor
open import Verify-Budget-Sufficient.Caps-Chain using
  (burst-index; burst-nil; burst-step; chain-desc; concat-frame; connect-step; defer-step;
  frame-nil; frame-recv; frame-step; inner-nil; inner-step; leaf-lvl; of-step; op-step;
  op-step-eval; op-step-mu; op-step-share; queue-push; walk-index; walk-nil; walk-none)
-- the `suc` the per-cons fold charge puts on a walk's reported witness
open import Verify-Budget-Sufficient.Caps-Sadd using (walk-step-suc)
-- THE DEPTH MIRROR (Unit 3): one head per evaluator head on the subscribe
-- path, threading the new `dpt` hypothesis this module's clique carries
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthInner; depthWalk; depthConsume; depthDrain; depthFrame; depthBurst;
  depthFin; depthReact; depthShSlot; depthConn; depthFold; depthDisp; depthShareGo; lub3-m;
  lub3-r)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)

------------------------------------------------------------------
-- THE COUNT, FOLDED IN — and now DISCHARGED, so the
-- placeholders that held its place are gone.
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

-- NOTHING IS OPEN.  Every caps conjunct in this file is ground and so
-- are the NEW ones — burst emit/value counts, and the length half of
-- `valsCaps?`.  A grep for `postulate` in this module now returns
-- nothing.  Ten of the twenty-two count sites fell out by `refl` alone:
-- a clause whose burst is a literal one-emit envelope carrying no
-- values (`dryBurst`, the spent and register answers, `oneShotBurst []`,
-- pushBurst's empty stream) has both conjuncts reduce — `1 ≤ᵇ suc W` is
-- `0 ≤ᵇ W` is `true` and `valCountᵉ` of an init/close/complete run is
-- `0` — at EVERY `c`, so the count costs those clauses nothing at all.

-- HOW THE OTHER TWELVE CAME OFF, in the order Phase 2 took them:
--
--   · THE EMIT COUNT is structural.  pushBurst is 1:1 (one envelope per
--     input emit), the leaves mint exactly one, and `sharedConnect` is
--     the sole grower — by one, prepending its own `init` envelope —
--     which the `suc` in its witness already pays for.
--   · THE PAYLOAD COUNT is stepFrame's output length: map-f preserves
--     it (`length-map`), scan-f is one out per in (`stepFrame-scan-len`,
--     via .Caps-Face's `scanVals-len`), take-f is a prefix
--     (`takeDispatch-len`), and thru's outer wrap does not touch the
--     value list at all (`thruWrap-vals`, `refl` in every node case).
--   · THE THREE CONCATENATING CLAUSES LAST — thruWalk's cons,
--     the mergeAll drain's step, innerFinish's drain — because those
--     output a SUM of two counts and a sum does NOT fit the width they
--     came in under.  That is Concat-Sum-Probe's finding, machine
--     checked both concretely and structurally, and the repair is
--     already landed below: each of the three reports `suc (…)` rather
--     than `(…)`, buying one more fold, and `2 * suc W ≤ foldStep S W`
--     for `2 ≤ S` clears the sum with room.  The charge is PER CONS, so
--     the induction needs no cardinality hypothesis on the walked list
--   · SUBSCRIBEINNER IS THE ONE PRODUCT.  `splitBurst` concatenates the
--     values of EVERY emit in the burst, so its output length is a burst
--     length TIMES a per-emit count — the only clause in the file whose
--     length half multiplies rather than adds.  It pays TWO folds
--     (`suc j₂ ⇒ suc (suc (suc j₂))`), via `mul-fits`/`sq-fold`.  ONE
--     fold is arithmetically enough — `(W+1)² ≤ suc (2 ^ suc W)` holds
--     at every W, with EQUALITY at W = 2 (9 ≤ 9) — but proving that
--     needs a case split on the small rows, whereas two folds clear it
--     outright from `suc W ≤ 2 ^ W` twice.  Two rungs are cheap here and
--     the tightening is available if a later leg ever wants it.

-- THE MARGIN IS NOT TIGHT, which is why one fold is enough and not two.
-- Concat-Sum-Probe's two worst rows, both machine-checked: `cWid
-- (frameStep 1 (caps 9 1 1)) ≡ 81` against a sum of `8 + 8 ≤ 82`, and
-- `cWid (frameStep 2 (caps 2 1 1)) ≡ 32` against `5 + 5 ≤ 33`.  The
-- summands are each at most `suc W` and one fold takes `W` to `S ^ suc
-- W ≥ 2 ^ suc W ≥ 2 * suc W`, so the doubling is covered outright.

-- FINDING, FOR THE (a) PASS AND NOT FOR THIS LEG (recorded, not
-- designed for).  Charging a fold PER CONS
-- means the level a concatenating clause reports at grows with the length of
-- the list it walked, and (a) — bounding `j′` by `fLvlD` — has to know
-- that growth does not outrun the iterator.  The first question (a)
-- should ask is whether the count conjuncts landing HERE already close
-- it: `vals` and `q` are unbounded UPSTREAM, but at the point a concatenating
-- clause runs, the walked list arrived inside a receipt whose count
-- conjunct bounds its length at that receipt's own level, and fLvlD's
-- iterators read `widAt` at CLIMBED levels rather than entry syntax.
-- Whether those two facts meet is (a)'s opening move, not this leg's
------------------------------------------------------------------

-- the payload ledger, unpacked and packed.  `valsCaps?` is the caps
-- half every clause already proves conjoined with the length half, so a
-- clause either splits one apart to feed a .Caps-Face helper (which
-- still takes the cardinality-free form) or puts one back together to
-- report.  Both halves are .Caps-Face's `valsCaps?-parts`; only the
-- packing direction is new, and it now takes the cardinality it used to
-- postulate



-- a cardinality rides the caps order exactly as the two receipts do:
-- ⊑ᶜ's middle component IS `cWid ≤ cWid`

-- ONE MORE FOLD, CHARGED PER CONS.  The three concatenating clauses
-- report `suc (j₁ + j₂)` where the additive ones report `j₁ + j₂`, so
-- what they hold at `(j + j₁) + j₂` has to travel one rung further than
-- +-assoc alone would take it.  This is that rung: `(j + j₁) + j₂ ≤
-- j + suc (j₁ + j₂)`, rebracketed and bumped, then frameStep-mono-j

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

-- the count receipt, unpacked and packed — the same two moves valsOf
-- and valsIn make for the payload ledger, on the burst's two conjuncts
countLen : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (str : Stream Γ u) →
  burstCount? c str ≡ true → length str ≤ suc (Caps.cWid c)
countLen c str h =
  ≤ᵇ⇒≤ (length str) (suc (Caps.cWid c))
    (T-to (proj₁ (∧-true (length str ≤ᵇ suc (Caps.cWid c))
                         (all (λ em → valCountᵉ (InstEmit.events em)
                                        ≤ᵇ suc (Caps.cWid c)) str) h)))

countVals : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (str : Stream Γ u) →
  burstCount? c str ≡ true →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c)) str ≡ true
countVals c str h =
  proj₂ (∧-true (length str ≤ᵇ suc (Caps.cWid c))
                (all (λ em → valCountᵉ (InstEmit.events em)
                               ≤ᵇ suc (Caps.cWid c)) str) h)

countIn : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (str : Stream Γ u) →
  length str ≤ suc (Caps.cWid c) →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c)) str ≡ true →
  burstCount? c str ≡ true
countIn c str hl ha =
  ∧-intro (T⇒≡true (length str ≤ᵇ suc (Caps.cWid c)) (≤⇒≤ᵇ hl)) ha

-- and a burst's tail is a burst: one fewer emit, the same per-emit
-- bound.  pushBurst's induction hypothesis is exactly this
burstCount?-tail : ∀ {n} {Γ : Ctx n} {u} (c : Caps)
  (em : InstEmit (Val Γ u)) (str : Stream Γ u) →
  burstCount? c (em ∷ str) ≡ true → burstCount? c str ≡ true
burstCount?-tail c em str h =
  countIn c str
    (≤-trans (n≤1+n (length str)) (countLen c (em ∷ str) h))
    (proj₂ (∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ suc (Caps.cWid c))
                   (all (λ em′ → valCountᵉ (InstEmit.events em′)
                                   ≤ᵇ suc (Caps.cWid c)) str)
                   (countVals c (em ∷ str) h)))

------------------------------------------------------------------
-- THE COUNT'S ARITHMETIC (ported from probe/Count-Grind-Probe and
-- probe/Concat-Sum-Probe).  Four facts, and the count is
-- exactly their consequence:
--
--   § 1  A SIZE FITS UNDER A WIDTH THREE FOLDS UP, and not one fold
--        up.  `cSize (frameStep j c) ≤ cWid (frameStep (suc j) c)` is
--        FALSE — `caps 2 0 r` at j = 1 has size `sizeStep 2 2 ≡ 10`
--        against width `2 ^ 3 ≡ 8`, the sole counterexample in
--        S ∈ [2,10), W ∈ [0,8), j ∈ [0,10) — so the leaves that bound a
--        payload by a SIZE (a script's `sync` list, an `ofᵉ` term list)
--        pay three.  Three and not two because `3 ≤ iterFold S (j + 3) W`
--        is free from `k≤iterFold`, where two would need a fact about
--        the second iterate.
--   § 2  AN EMIT'S VALUE COUNT IS COMPUTED, not bounded: `splitEvents`'s
--        backchannel and `retagEvents` both drop every `value`, so a
--        pushed envelope carries exactly `length vals` of them, and a
--        `oneShotBurst` exactly its own list's length.
--   § 3  pushBurst IS 1:1 and sharedPlumb IS A `map`, so the emit half
--        travels unchanged through both; only sharedConnect's prepended
--        `init` envelope grows it, by one, which one fold covers.
--   § 4  A LIST IS NO LONGER THAN THE SIZE THAT COUNTS IT — every value
--        weighs at least one — which is how a leaf's payload reaches
--        `slotsSize sl ≤ cSize c` at all.
------------------------------------------------------------------

-- § 1.  THE SIZE→WIDTH BRIDGE.


sucX≤2X : ∀ (X : ℕ) → 1 ≤ X → suc X ≤ 2 * X
sucX≤2X X h = ≤-trans (+-monoˡ-≤ X h) (≤-reflexive (sym (2X≡X+X X)))

-- the base of the bridge, at S = 2: `suc (2 * R) ≤ 2 ^ R` from R = 3
-- (7 ≤ 8) up, by doubling both sides
suc2≤pow2 : ∀ (m : ℕ) → suc (2 * (3 + m)) ≤ 2 ^ (3 + m)
suc2≤pow2 zero    = s≤s (s≤s (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))))
suc2≤pow2 (suc m) = ≤-trans step (*-monoʳ-≤ 2 (suc2≤pow2 m))
  where
  k : ℕ
  k = 3 + m
  1≤2k : 1 ≤ 2 * k
  1≤2k = s≤s z≤n
  step : suc (2 * suc k) ≤ 2 * suc (2 * k)
  step = ≤-trans (≤-reflexive (cong suc (*-suc 2 k)))
           (≤-trans (+-monoʳ-≤ 2 (sucX≤2X (2 * k) 1≤2k))
                    (≤-reflexive (sym (*-suc 2 (2 * k)))))

suc2≤pow : ∀ (S R : ℕ) → 2 ≤ S → 3 ≤ R → suc (2 * R) ≤ S ^ R
suc2≤pow S zero                  2≤S ()
suc2≤pow S (suc zero)            2≤S (s≤s ())
suc2≤pow S (suc (suc zero))      2≤S (s≤s (s≤s ()))
suc2≤pow S (suc (suc (suc m)))   2≤S _ =
  ≤-trans (suc2≤pow2 m) (^-monoˡ-≤ (3 + m) 2≤S)

-- ONE SIZE STEP IS DOMINATED BY ONE FOLD STEP, given three folds of
-- headroom: `S * suc (2 * s) ≤ S * S ^ R` whenever `s ≤ R` and `3 ≤ R`
sizeStep≤foldStep : ∀ (S s R : ℕ) → 2 ≤ S → 3 ≤ R → s ≤ R →
  sizeStep S s ≤ foldStep S R
sizeStep≤foldStep S s R 2≤S 3≤R s≤R =
  *-monoʳ-≤ S (≤-trans (s≤s (*-monoʳ-≤ 2 s≤R)) (suc2≤pow S R 2≤S 3≤R))


-- and the bridge itself, by induction on j against the SAME j three
-- folds up.  The base is `S ≤ S * S ^ W ≤ iterFold S 3 W`
sizeBelowWid : ∀ (S W j : ℕ) → 2 ≤ S → iterSize S j S ≤ iterFold S (j + 3) W
sizeBelowWid S W zero 2≤S =
  ≤-trans (≤-trans (≤-reflexive (sym (*-identityʳ S)))
                   (*-monoʳ-≤ S (1≤pow≤ S W (≤-trans (s≤s z≤n) 2≤S))))
          (iterFold-mono-count S W 2≤S {1} {3} (s≤s z≤n))
sizeBelowWid S W (suc j) 2≤S =
  ≤-trans (≤-reflexive (iterSize-suc S j S))
    (≤-trans (sizeStep≤foldStep S (iterSize S j S) (iterFold S (j + 3) W)
                2≤S 3≤R (sizeBelowWid S W j 2≤S))
             (≤-reflexive (sym (iterFold-suc S (j + 3) W))))
  where
  3≤R : 3 ≤ iterFold S (j + 3) W
  3≤R = ≤-trans (m≤n+m 3 j) (k≤iterFold S (j + 3) W 2≤S)

frameStep-size≤wid : ∀ (c : Caps) (j : ℕ) → 2 ≤ Caps.cSize c →
  Caps.cSize (frameStep j c) ≤ Caps.cWid (frameStep (j + 3) c)
frameStep-size≤wid c j 2≤S = sizeBelowWid (Caps.cSize c) (Caps.cWid c) j 2≤S

-- the leaf's own rung, which needs no folds at all: the ENTRY size sits
-- under the width one fold up, because `S ≤ S * S ^ W`
size≤widAt1 : ∀ (c : Caps) → 1 ≤ Caps.cSize c →
  Caps.cSize c ≤ Caps.cWid (frameStep 1 c)
size≤widAt1 c 1≤S =
  ≤-trans (≤-reflexive (sym (*-identityʳ (Caps.cSize c))))
          (*-monoʳ-≤ (Caps.cSize c) (1≤pow≤ (Caps.cSize c) (Caps.cWid c) 1≤S))

-- § 2.  THE EMIT'S VALUE COUNT, computed rather than bounded.

valCountᵉ-++ : ∀ {A : Set} (xs ys : List (InstEvent A)) →
  valCountᵉ (xs ++ ys) ≡ valCountᵉ xs + valCountᵉ ys
valCountᵉ-++ []               ys = refl
valCountᵉ-++ (value _   ∷ xs) ys = cong suc (valCountᵉ-++ xs ys)
valCountᵉ-++ (init _    ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (close _ _ ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (handoff _ ∷ xs) ys = valCountᵉ-++ xs ys
valCountᵉ-++ (complete  ∷ xs) ys = valCountᵉ-++ xs ys

valCountᵉ-mapValue : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) →
  valCountᵉ (map value vs) ≡ length vs
valCountᵉ-mapValue []       = refl
valCountᵉ-mapValue (v ∷ vs) = cong suc (valCountᵉ-mapValue vs)

-- retagEvents DROPS every value — it is the plumbing projection — and
-- splitEvents's backchannel is the same filter
valCountᵉ-retag : ∀ {A B : Set} (es : List (InstEvent A)) →
  valCountᵉ (retagEvents {A = A} {B = B} es) ≡ 0
valCountᵉ-retag []                      = refl
valCountᵉ-retag {B = B} (value _   ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (init _    ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (close _ _ ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (handoff _ ∷ es) = valCountᵉ-retag {B = B} es
valCountᵉ-retag {B = B} (complete  ∷ es) = valCountᵉ-retag {B = B} es

valCountᵉ-bk : ∀ {n} {Γ : Ctx n} {s} {A : Set} (es : List (InstEvent (Val Γ s))) →
  valCountᵉ (proj₁ (proj₂ (splitEvents {A = A} es))) ≡ 0
valCountᵉ-bk []                      = refl
valCountᵉ-bk {A = A} (value _   ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (init _    ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (close _ _ ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (handoff _ ∷ es) = valCountᵉ-bk {A = A} es
valCountᵉ-bk {A = A} (complete  ∷ es) = valCountᵉ-bk {A = A} es

valCountᵉ-fin : ∀ {A : Set} (b : Bool) →
  valCountᵉ {A = A} (if b then complete ∷ [] else []) ≡ 0
valCountᵉ-fin true  = refl
valCountᵉ-fin false = refl

-- SO A PUSHED ENVELOPE CARRIES EXACTLY ITS PAYLOAD.  This is the whole
-- per-emit half of the count for pushBurst: backchannel 0, retag 0,
-- terminator 0, and `map value vs` exactly `length vs`
pushEmit-count : ∀ {n} {Γ : Ctx n} {s u} {A : Set}
  (es : List (InstEvent (Val Γ s))) (evs : List (InstEvent A))
  (vs : List (Val Γ u)) (b : Bool) →
  valCountᵉ (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))
              ++ retagEvents {A = A} {B = Val Γ u} evs
              ++ map value vs
              ++ (if b then complete ∷ [] else []))
    ≡ length vs
pushEmit-count {Γ = Γ} {u = u} {A = A} es evs vs b =
  trans (valCountᵉ-++ (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) _)
  (trans (cong (_+ valCountᵉ (retagEvents {A = A} {B = Val Γ u} evs
                                ++ map value vs
                                ++ (if b then complete ∷ [] else [])))
               (valCountᵉ-bk {A = Val Γ u} es))
  (trans (valCountᵉ-++ (retagEvents {A = A} {B = Val Γ u} evs) _)
  (trans (cong (_+ valCountᵉ (map value vs ++ (if b then complete ∷ [] else [])))
               (valCountᵉ-retag {A = A} {B = Val Γ u} evs))
  (trans (valCountᵉ-++ (map value vs) (if b then complete ∷ [] else []))
  (trans (cong (valCountᵉ (map value vs) +_) (valCountᵉ-fin {A = Val Γ u} b))
  (trans (+-identityʳ (valCountᵉ (map value vs)))
         (valCountᵉ-mapValue vs)))))))

oneShot-count : ∀ {n} {Γ : Ctx n} {u} (vs : List (Val Γ u)) (src : ℕ) →
  valCountᵉ (init src ∷ map value vs ++ close src exhausted ∷ complete ∷ [])
    ≡ length vs
oneShot-count vs src =
  trans (valCountᵉ-++ (map value vs) (close src exhausted ∷ complete ∷ []))
  (trans (+-identityʳ (valCountᵉ (map value vs)))
         (valCountᵉ-mapValue vs))

-- § 3.  pushBurst IS LENGTH-PRESERVING; sharedPlumb IS A `map`.

pushBurst-len : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (str : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) →
  length (proj₁ (pushBurst g id now f κ str sched st)) ≡ length str
pushBurst-len g id now f κ [] sched st = refl
pushBurst-len {Γ = Γ} {u = u} g id now f κ (em ∷ ems) sched st =
  cong suc (pushBurst-len g id now f κ ems
              (proj₁ (proj₂ (proj₂ (proj₂ SF))))
              (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  where
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  SF = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

sharedPlumb-len : ∀ {n} {Γ : Ctx n} {u} (str : Stream Γ u) →
  length (sharedPlumb str) ≡ length str
sharedPlumb-len []         = refl
sharedPlumb-len (em ∷ ems) = cong suc (sharedPlumb-len ems)

sharedPlumb-count : ∀ {n} {Γ : Ctx n} {u} (N : ℕ) (str : Stream Γ u) →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ N) str ≡ true →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ N) (sharedPlumb str) ≡ true
sharedPlumb-count N []         h = refl
sharedPlumb-count N (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ N)
                         (all (λ em′ → valCountᵉ (InstEmit.events em′) ≤ᵇ N) ems) h))
          (sharedPlumb-count N ems
             (proj₂ (∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ N)
                            (all (λ em′ → valCountᵉ (InstEmit.events em′) ≤ᵇ N) ems) h)))

-- § 4.  A LIST IS NO LONGER THAN THE SIZE THAT COUNTS IT.
-- (`len≤sizeᵗˢ`, the term-list form, is already in .Caps-Face.)

1≤sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (v : Val Γ t) → 1 ≤ sizeᵛ t v
1≤sizeᵛ unitᵗ    _        = s≤s z≤n
1≤sizeᵛ boolᵗ    _        = s≤s z≤n
1≤sizeᵛ natᵗ     _        = s≤s z≤n
1≤sizeᵛ (s ×ᵗ t) (a , b)  = s≤s z≤n
1≤sizeᵛ (s +ᵗ t) (inj₁ a) = s≤s z≤n
1≤sizeᵛ (s +ᵗ t) (inj₂ b) = s≤s z≤n
1≤sizeᵛ (obs t)  e        = sizeᵉ-pos e

len≤sum-sizeᵛ : ∀ {n} {Γ : Ctx n} (t : Ty) (vs : List (Val Γ t)) →
  length vs ≤ sum (map (sizeᵛ t) vs)
len≤sum-sizeᵛ t []       = z≤n
len≤sum-sizeᵛ t (v ∷ vs) = +-mono-≤ (1≤sizeᵛ t v) (len≤sum-sizeᵛ t vs)

len≤inputSize : ∀ {n} {Γ : Ctx n} (t : Ty) (sync : List (Val Γ t))
  (async : List (Timed (Val Γ t))) →
  length sync ≤ inputSize {Γ = Γ} {t = t} (cold sync async)
len≤inputSize t sync async =
  ≤-trans (≤-trans (len≤sum-sizeᵛ t sync) (m≤m+n _ _)) (n≤1+n _)

slotSize≤slotsSize : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n) →
  slotSize (sl i) ≤ slotsSize sl
slotSize≤slotsSize sl i = fᵢ≤sum-tab (λ k → slotSize (sl k)) i

-- § 5.  THE CONCAT ARITHMETIC (ported from probe/Concat-Sum-Probe).
-- `suc w ≤ 2 ^ w` doubles to `2 * suc w ≤ S ^ suc w = foldStep S w`, so
-- two receipts at one level add to one receipt a fold up

-- `2*suc≤2^suc` and `dbl-suc` are .Caps-Face/Part6's, imported by name
-- ; they were verbatim here too until dup-check saw them.



suc-fits : ∀ (c : Caps) (L a : ℕ) → 2 ≤ Caps.cSize c →
  a ≤ suc (Caps.cWid (frameStep L c)) →
  suc a ≤ suc (Caps.cWid (frameStep (suc L) c))
suc-fits c L a hS ha =
  subst (λ x → suc a ≤ suc x) (sym (frameStep-wid-suc c L))
    (s≤s (≤-trans ha (suc≤foldStep (Caps.cSize c) (Caps.cWid (frameStep L c)) hS)))

-- rebracketing the COUNT receipt, the third sibling of
-- frameStep-+assoc-caps and frameStep-+assoc-burst
frameStep-+assoc-count : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j a b : ℕ)
  (str : Stream Γ u) →
  burstCount? (frameStep ((j + a) + b) c) str ≡ true →
  burstCount? (frameStep (j + (a + b)) c) str ≡ true
frameStep-+assoc-count c j a b str =
  subst (λ x → burstCount? (frameStep x c) str ≡ true) (+-assoc j a b)

-- § 6.  THE SQUARE, AND THE ONE CLAUSE THAT PAYS IT.
--
-- subscribeInner splits a whole BURST: `splitBurst` concatenates the
-- payloads of every emit, so its output is bounded by the burst's
-- LENGTH times the per-emit value count — and both of those are the
-- same `suc (cWid)`.  That is a PRODUCT, the only one in the file; §5's
-- sum needs one fold, a square needs TWO.
--
-- One fold is in fact arithmetically enough — `(W+1)² ≤ suc (2 ^ suc
-- W)` holds for every W, with EQUALITY at W = 2 (9 ≤ 9) — but proving
-- it wants a case split on the small rows, where two folds clear it
-- outright from `suc W ≤ 2 ^ W` used twice.  So subscribeInner reports
-- two rungs, not one, and the margin is recorded rather than shaved

sq-pow : ∀ (w : ℕ) → suc w * suc w ≤ 2 ^ (w + w)
sq-pow w = ≤-trans (*-mono-≤ (n<2^n w) (n<2^n w))
                   (≤-reflexive (sym (^-distribˡ-+-* 2 w w)))

sq-fold : ∀ (S w : ℕ) → 2 ≤ S → suc w * suc w ≤ suc (foldStep S (foldStep S w))
sq-fold S w hS =
  ≤-trans (sq-pow w)
    (≤-trans (^-monoʳ-≤ 2 w+w≤)
      (≤-trans (^-monoˡ-≤ (suc (foldStep S w)) hS)
               (n≤1+n (foldStep S (foldStep S w)))))
  where
  w+w≤ : w + w ≤ suc (foldStep S w)
  w+w≤ = ≤-trans (+-mono-≤ (n≤1+n w) (n≤1+n w))
           (≤-trans (≤-reflexive (dbl-suc w))
                    (≤-trans (double≤foldStep S w hS) (n≤1+n (foldStep S w))))

mul-fits : ∀ (c : Caps) (L a b : ℕ) → 2 ≤ Caps.cSize c →
  a ≤ suc (Caps.cWid (frameStep L c)) → b ≤ suc (Caps.cWid (frameStep L c)) →
  a * b ≤ suc (Caps.cWid (frameStep (suc (suc L)) c))
mul-fits c L a b hS ha hb =
  subst (λ x → a * b ≤ suc x)
        (sym (trans (frameStep-wid-suc c (suc L))
                    (cong (foldStep (Caps.cSize c)) (frameStep-wid-suc c L))))
        (≤-trans (*-mono-≤ ha hb)
                 (sq-fold (Caps.cSize c) (Caps.cWid (frameStep L c)) hS))

-- and the count the square is charged against: splitBurst's payload
-- list is the concatenation of the per-emit ones, so its length is at
-- most one emit's bound taken `length str` times
splitBurst-len : ∀ {n} {Γ : Ctx n} {s u : Ty} (N : ℕ) (str : Stream Γ s) →
  all (λ em → valCountᵉ (InstEmit.events em) ≤ᵇ N) str ≡ true →
  length (proj₁ (splitBurst {A = Val Γ u} str)) ≤ length str * N
splitBurst-len N []         h = z≤n
splitBurst-len {Γ = Γ} {u = u} N (em ∷ ems) h =
  ≤-trans (≤-reflexive
             (length-++ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em)))))
          (+-mono-≤ HEAD (splitBurst-len {u = u} N ems (proj₂ hp)))
  where
  hp = ∧-true (valCountᵉ (InstEmit.events em) ≤ᵇ N)
              (all (λ em′ → valCountᵉ (InstEmit.events em′) ≤ᵇ N) ems) h
  HEAD : length (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) ≤ N
  HEAD = ≤-trans (≤-reflexive (splitEvents-len {A = Val Γ u} (InstEmit.events em)))
                 (≤ᵇ⇒≤ (valCountᵉ (InstEmit.events em)) N (T-to (proj₁ hp)))

-- THE TWO LENGTH REPORTS .Caps-Face DOES NOT ALREADY HAVE.  scanVals,
-- takeVals and takeDispatch are all measured there; the outer *All
-- wrap and the scan frame's node dispatch are not, and both are pure
-- pass-throughs on the payload — thruWrap only sets a completion flag,
-- and scan's dispatch either scans or emits nothing

stepFrame-scan-len : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (nid : NodeId) (κ : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  length (proj₁ (stepFrame g id now (scan-f fn nid) κ vals fin sched st))
    ≤ length vals
stepFrame-scan-len {u = u} g id now fn nid κ vals fin sched st
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = z≤n
... | just (take-st _)       = z≤n
... | just (mergeAll-st _ _ _ _)    = z≤n
... | just (switch-st _ _)   = z≤n
... | just (exhaust-st _ _)  = z≤n
... | just (scan-st {w} ac) with w ≟ᵗ u
...   | no _     = z≤n
...   | yes refl = ≤-reflexive (scanVals-len fn ac vals)


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
-- joint-bound repair (Joint-Probe).  What stood here was
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

-- SURVEYED, NOT ATTEMPTED, now that every COMPANION is
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
--      parked-width ruling).  `deferᵉ body` PARKS AN
--      OBSERVABLE ON THE SCHEDULE: its clause adds a LiveSource at
--      `elemTy = obs u` with `pending = (suc now , body)`, so
--      capsOK?'s widLive conjunct demands a WIDTH for the body — and
--      `outWᵉ (deferᵉ e) = 0` by definition (a defer crosses a tick,
--      and that semantics is load-bearing on the wet side), so no
--      outW-derived entry measure supplied it.

--      THE REPAIR IS SUPPLY-SIDE AND CAPS-SIDE ONLY.  Rx.Frame-Width
--      gains dW — the PARKED width, ⊔-collecting every deferᵉ
--      subterm's `outWᵉ body ⊔ dWᵉ body` — and pW = outW ⊔ dW.  The
--      caps side reads pW (widLive, widNode, valCaps?, obsCaps?), the
--      wet side keeps outW untouched, and capsAt's base pays for both
--      through the ENTRY CEILING it now carries.

--      AND THE TELESCOPE CONJUNCT IS dW, NOT pW, which is the one
--      place the ruling's shape had to be sharpened in the making.
--      `dWᵉ n sl (deferᵉ body) = pWᵉ n sl body` EXACTLY, so a dW
--      hypothesis serves the defer clause with nothing to spare — and
--      it DESCENDS, which pW does not: `outWᵉ (mergeAllᵉ lim e)` is
--      `outWᵉ e * innWᵉ e`, which is 0 at `innWᵉ e = 0` (take
--      `e = ofᵉ (strmᵗ emptyᵉ ∷ [])`: outW 1, innW 0), so a pW
--      hypothesis at `mergeAllᵉ lim e` says nothing about `e` and the
--      *All clause could not recurse.  dW is a plain ⊔-collect through
--      every constructor, so every structural descent is m≤m⊔n.  Every
--      supplier still works, because all three supply pW ≥ dW: payload
--      paths from valCaps?'s width half, the root from the base, and
--      sharedConnect from slotsCaps?, which gains a width half at pW
--      on its shared branch

-- AND IT IS NO LONGER A POSTULATE: it is FORWARD-DECLARED here (so the
-- companion tree below can call it, exactly as foldPath-caps and its
-- clique are declared before they are defined) and GROUND at the end
-- of the file, on pushBurst-caps, subscribeAll-caps and the three
-- evaluation obligations named there
-- the two bookends of `cascade` and the chain snapshot are no longer
-- postulated either: they are GROUND below, on the same two filter
-- lemmas the share leaves use.

-- THE OPERATOR COUNT arrives with the hypothesis `op-step` forces, and
-- every site supplies it outright — there is no scaffolding here.  Two
-- shapes carry it: a CHAIN EDGE splits its index and hands the source the
-- predecessor (`chain-desc`, .Caps-Chain § 3), and a FRESH ENTRY mints
-- the index at the new level's size cap and pays one `s≤s` on the size
-- hypothesis it already holds.  The μ unfolding is the second kind, not
-- the first: it subscribes a LARGER term, which is why `op-step-mu`
-- consumes it at `sLvlD` rather than at `opIterD`.

------------------------------------------------------------------
-- THE LEVEL CONJUNCT, AND HOW THE DEPTH FUEL CLOSED IT.
--
-- Every head below reports the LEVEL it leaves, in the one transformer
-- its arc of the family's clause cycle forces
-- (`git show 109757a^:agda/probe/Chain-Supply-Probe.agda` § 4).  The heads are
-- forward-declared, so the conjunct could not land head by head: the
-- SHAPES all landed at once and the PROOFS landed per clause.  They are
-- all in now — a leaf (`emptyᵉ`, `takeᵉ 0`, the dry closes), a chain edge
-- (`mapᵉ`), the μ unfolding, one payload of `thruWalk`, one emit of
-- `pushBurst`, one frame of `stepFrame`'s thru-outer, and one drain of
-- `innerFinish`'s drain.  No deferred level placeholder survives, and
-- there is no postulate in this module.
--
-- WHAT THE LAST TWO SITES NEEDED, since it was diagnosed as a budget
-- problem for a while and was not one.  Both were the SAME question:
-- `innerFinish-caps` and `innerReact-caps` are generic in `dep`, while
-- `fLvlD` at zero and at a successor are unrelated formulas, so a walk
-- result cannot discharge a generic-depth frame conjunct at all.  The
-- answer is the DEPTH MIRROR (.Caps-Depth): a hypothesis
-- `depthX … ≤ dep` that reduces, in each clause's own pattern context,
-- to a `⊔` of its callees' mirrors.  Two arcs carry a `suc` — this
-- module's `stepFrame-caps` thru-outer and `innerFinish-caps` drain —
-- and at those two the clause SPLITS `dep`: `zero` is absurd because the
-- mirror put a `suc` there, and `suc dep′` runs the callee one level
-- lower.  Every other clause projects its hypothesis through the lattice
-- and spends nothing.
--
-- THE PAYLOAD EDGE'S SPLIT IS NOW PAID, and how is worth keeping.  The
-- four walk heads take the PREDECESSOR of the budget they report at:
-- each holds `bud` and reports at `suc bud`, so `subscribeInner-caps`
-- can hand `subscribeE-caps` its own `bud` unchanged and the two meet
-- where `inner-step` needs them.  Nothing had to be renamed or matched —
-- `inner-step` is proven for an abstract `k` and concludes at `suc k`,
-- which is why the nesting level costs a `suc` on the CONJUNCT rather
-- than a weakening of every hypothesis.  The strictness lands in exactly
-- one place: `stepFrame-caps`'s thru-outer hands the walk `sizeAt S (suc
-- j)`, whose successor IS `frameBud c j` by plain definition, and
-- `valsCaps→mList-strict` supplies the payload bound there, and
-- `obsList→mList-strict` does the same for the mergeAll drain's queue.
------------------------------------------------------------------

-- THE PARKED DEFER'S CLOSURE READING.  A defer parks its body on the
-- live queue, so the queue's closure conjunct is owed for a term the
-- subscribe holds only the WRITTEN size of -- and the two measures
-- part company exactly at `input`, where the written size is one
-- symbol and the reading is the whole definition the telescope holds.
--
-- WHAT PAYS FOR THE GAP IS THE SLOT PRICING PREDICATE, which every
-- statement on this path already threads: it prices each slot's own
-- STAGED reading against the same cap, so the environment the reading
-- runs under is dominated by the cap uniformly, and a domination
-- lemma multiplies it straight through the sync size.  One frame level
-- then pays the sync-to-written step, because a level multiplies by
-- the base size and doubles.
-- REFUTED: `Refuted.Nest-Clos-Stratified`, which is why the pricing
--   predicate has to carry that conjunct rather than the flat size
--   alone: a stratified telescope whose every stage names the stage
--   below it twice is admitted by the flat pricing at a cap of seven
--   while the staged reading doubles per stage, so the deficit is
--   exponential in the SLOT COUNT -- a quantity no level of the frame
--   mentions, and therefore one no fixed number of levels can buy.

defer-park-clos : ∀ {n} {Γ : Ctx n} {u} (c : Caps) (j : ℕ) (sl : Slots Γ)
  (o : Val Γ (obs u)) →
  2 ≤ Caps.cSize c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  sizeᵉ o ≤ Caps.cSize (frameStep j c) →
  nestClosOK? (frameStep (suc j) c) sl o ≡ true
defer-park-clos c j sl o 2≤S slC hsz =
  T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (closSize≤mulᵉ (slotClos sl) S
                (λ i → slotsCaps?-clos S (Caps.cWid c) sl i slC)
                (≤-trans (s≤s z≤n) 2≤S) o)
    (≤-trans (*-monoʳ-≤ S
                (≤-trans (≤-trans (syncSize≤sizeᵉ o) hsz)
                         (≤-trans (m≤m+n Sⱼ (Sⱼ + 0)) (n≤1+n (Sⱼ + (Sⱼ + 0))))))
             (≤-reflexive (sym (frameStep-size-suc c j))))))
  where
  S  = Caps.cSize c
  Sⱼ = Caps.cSize (frameStep j c)

subscribeE-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (dep bud ops j : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
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
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  -- THE OPERATOR COUNT'S OWN HYPOTHESIS.  `op-step` concludes at
  -- `suc ops`, so an operator clause can only report if its index is a
  -- successor; this is what licenses the split, and it is free at every
  -- supplier (Chain-Supply-Probe § 1: a frame's size cap IS `sizeAt` at
  -- that level, so a fresh entry at `suc (sizeAt S j)` pays one `s≤s`,
  -- and § 2: a chain edge descends with room to spare)
  suc (sizeᵉ b) ≤ ops →
  depthE g b κ bid now sched st ≤ dep →
  let r = subscribeE g b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- AND THE LEVEL IT LEAVES: a subscribe is an OPERATOR SWEEP with
     -- `ops` operators left to enter, and it never climbs past the sweep
     × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)

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
  (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId)
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
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ id now o sched st ≤ dep →
  let r = subscribeInner g op allNid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
     -- A PAYLOAD'S OWN ENTRY, and it is reported STRICTLY: the inner is
     -- subscribed under one more frame, at `suc j`, and the walk that
     -- consumes it charges one fold per cons (`walk-step-suc`)
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
-- OUT OF GAS: a dry close and nothing else.  The only state change is
-- the instance counter, which capsOK? does not read
subscribeInner-caps c dep bud j g0 op allNid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (record sched { nextNode = suc (Sched.nextNode sched) }) st ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched)) sched st inv)
    , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
-- WITH GAS: the inner is subscribed under one more frame, at the same
-- instant, and at ONE MORE j.  Its size hypothesis is valCaps?'s cSize
-- half (sizeᵛ (obs u) IS sizeᵉ), widened by the step; its chain
-- hypothesis is κ's, one frame longer, which is frameStep-chain-suc
subscribeInner-caps {n = n} {Γ = Γ} {t = t} {u = u} c dep bud j (gs fuel) op allNid κ id now o
                    sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt =
  suc (suc (suc j₂)) , R1 , R2 , R3
    -- THE KEYSTONE.  Twenty-five clauses of `thruConsume-caps` project
    -- this one, and its witness is forced from both sides: the caps
    -- components live at `frameStep (j + suc (suc (suc j₂)))` because the
    -- `splitBurst` square costs two levels, and the consumer wants a
    -- STRICT report at `suc j`.  So the goal sits four above the IH's one,
    -- and a payload subscribe spends the nesting level that makes `suc
    -- bud` meet the IH's `bud`
    , inner-step (Caps.cSize c) (Caps.cWid c) dep bud j j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
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
  -- THE INDEX IS THE CAP ITSELF, not its successor.  Called at the
  -- successor the IH lands flush against the target with nothing over,
  -- which is exactly why this site could not be closed; one index lower
  -- exposes `opIterD`'s own `J₀` excursion, which is where the payload
  -- edge's three rungs are paid from (.Caps-Chain § 5)
  IH     = subscribeE-caps c dep bud (Caps.cSize (frameStep (suc j) c)) (suc j) fuel o κ′ id now sl sched₀ st 2≤S 1≤R slEq slC slSz
             (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
                (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                  sched st inv))
             (≤-trans szo (proj₁ step⊑))
             (≤-trans wdo (proj₁ (proj₂ step⊑))) pC′
             (frameStep-chain-suc c j (pathLen κ) 2≤S lC) nst
             -- and the lower index costs STRICTNESS here: `s≤s` on the
             -- widened `szo` would only reach the cap's successor
             (frameStep-size-strict-suc c j (sizeᵉ o) (≤-trans (s≤s z≤n) 2≤S) szo)
             dpt
  j₂     = proj₁ IH
  SUB    = proj₁ (proj₂ IH)
  BC     = proj₁ (proj₂ (proj₂ IH))
  CNT    = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  res    = subscribeE fuel o κ′ id now sched₀ st
  burst  = proj₁ res
  VS     = proj₁ (splitBurst {A = Val Γ t} burst)
  BS     = proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))
  -- THE SQUARE, AND THE TWO RUNGS IT COSTS.  `splitBurst` concatenates
  -- the payloads of EVERY emit, so the output count is the burst's
  -- LENGTH times one emit's value count — and the count receipt bounds
  -- both by the same `suc (cWid C₀)`.  That is a PRODUCT, the only one
  -- in the file, and §6 pays two folds for it where §5's sum pays one
  L₀ = suc j + j₂
  C₀ = frameStep L₀ c
  C₃ = frameStep (suc (suc L₀)) c
  ⊑₂ : C₀ ⊑ᶜ C₃
  ⊑₂ = frameStep-mono-j c 2≤S {L₀} {suc (suc L₀)}
         (≤-trans (n≤1+n L₀) (n≤1+n (suc L₀)))
  lvl : j + suc (suc (suc j₂)) ≡ suc (suc (suc (j + j₂)))
  lvl = trans (+-suc j (suc (suc j₂)))
          (trans (cong suc (+-suc j (suc j₂)))
                 (cong suc (cong suc (+-suc j j₂))))
  LENV : length VS ≤ suc (Caps.cWid C₃)
  LENV = ≤-trans (splitBurst-len {u = t} (suc (Caps.cWid C₀)) burst
                    (countVals C₀ burst CNT))
                 (mul-fits c L₀ (length burst) (suc (Caps.cWid C₀)) 2≤S
                    (countLen C₀ burst CNT) ≤-refl)
  R1 : capsOK? (frameStep (j + suc (suc (suc j₂))) c)
                (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true
  R1 = subst (λ x → capsOK? (frameStep x c)
                      (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
             (sym lvl)
             (capsOK?-mono C₀ C₃ (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ⊑₂ SUB)
  R2 : valsCaps? (frameStep (j + suc (suc (suc j₂))) c) sl VS ≡ true
  R2 = subst (λ x → valsCaps? (frameStep x c) sl VS ≡ true) (sym lvl)
             (valsIn C₃ sl VS
                (splitBurst-vals-caps {s = u} {u = t} C₃ sl burst
                   (burstCaps?-widen sl burst ⊑₂ BC))
                LENV)
  R3 : all (eventCaps? (frameStep (j + suc (suc (suc j₂))) c) sl) BS ≡ true
  R3 = subst (λ x → all (eventCaps? (frameStep x c) sl) BS ≡ true)
             (sym lvl)
             (splitBurst-bk-caps {s = u} {u = t} C₃ sl burst)

-- THE CONNECT.  One registration for the joining subscriber, then the
-- def is subscribed under `share-sink i` — a chain of LENGTH ZERO, so
-- its own chain hypothesis is `1 ≤ cSize` and nothing else has to be
-- found for it.  That is why this edge composed even under the old
-- joint bound, and it composes unchanged under the separate pair
sharedConnect-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
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
  nest d sl (toℕ i ∷ EvalSt.connectedShares st) ≤ bud →
  depthConn g i d κ id now sched st ≤ dep →
  let r = sharedConnect g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- AND THE LEVEL: a share connect is a FRESH ENTRY, so it reports the
     -- whole level sweep rather than an operator index — and at `suc bud`,
     -- because connecting a slot SPENDS a nesting level exactly as the μ
     -- unfolding and the payload subscribe do
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
-- OUT OF GAS: a dry close and nothing else
sharedConnect-caps {Γ = Γ} c dep bud j g0 i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv szd wdd pC lC nst dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (dryBurst {A = Val Γ (lookup Γ i)} id) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
sharedConnect-caps {Γ = Γ} c dep bud j (gs fuel′) i d κ id now sl sched st
                   2≤S 1≤R slEq slC slSz inv szd wdd pC lC nst dpt
  with burstCompleted (proj₁ (subscribeE fuel′ d (share-sink i) id now sched
                               (register (toℕ i) κ
                                 (record st { connectedShares =
                                                toℕ i ∷ EvalSt.connectedShares st }))))
... | true  =
  suc (suc j₂)
    , subst (λ x → capsOK? (frameStep x c) sched₁ DROP ≡ true) (sym lvl)
        (capsOK?-mono C1 C2 sched₁ DROP bmp
           (dropOnly-caps C1 (toℕ i) sched₁
              (record st₂ { completedSources = toℕ i ∷ EvalSt.completedSources st₂ })
              SUB))
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                        at id from toℕ i as subscribe) ∷ sharedPlumb burst)
                       ≡ true)
            (sym lvl)
            (∧-intro refl
               (sharedPlumb-caps C2 sl burst (burstCaps?-widen sl burst bmp BC)))
    , subst (λ x → burstCount? (frameStep x c)
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                        at id from toℕ i as subscribe) ∷ sharedPlumb burst)
                       ≡ true)
            (sym lvl) COUNT
    -- ONE PREPENDED EMIT above the sweep the IH reports, which is the
    -- payload edge's square minus a rung
    , connect-step (Caps.cSize c) (Caps.cWid c) dep bud j j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c dep bud (Caps.cSize (frameStep (suc j) c)) (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC slSz
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S)) nst
          (frameStep-size-strict-suc c j (sizeᵉ d) (≤-trans (s≤s z≤n) 2≤S) szd)
          dpt
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₁ (proj₂ (proj₂ IH))
  res = subscribeE fuel′ d (share-sink i) id now sched st₁
  burst = proj₁ res
  sched₁ = proj₁ (proj₂ res)
  st₂ = proj₂ (proj₂ res)
  DROP = record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                    ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
  CNT = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  C1  = frameStep (suc (j + j₂)) c
  C2  = frameStep (suc (suc (j + j₂))) c
  -- the connect PREPENDS its own emit, so the burst is one longer than
  -- the one the IH counted; one more fold buys the room
  bmp : C1 ⊑ᶜ C2
  bmp = frameStep-mono-j c 2≤S (n≤1+n (suc (j + j₂)))
  lvl : j + suc (suc j₂) ≡ suc (suc (j + j₂))
  lvl = trans (+-suc j (suc j₂)) (cong suc (+-suc j j₂))
  LEN : length (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                   at id from toℕ i as subscribe) ∷ sharedPlumb burst)
          ≤ suc (Caps.cWid C2)
  LEN = suc-fits c (suc (j + j₂)) (length (sharedPlumb burst)) 2≤S
          (subst (λ x → x ≤ suc (Caps.cWid C1)) (sym (sharedPlumb-len burst))
                 (countLen C1 burst CNT))
  COUNT : burstCount? C2
            (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                at id from toℕ i as subscribe) ∷ sharedPlumb burst) ≡ true
  COUNT = countIn C2 (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                         at id from toℕ i as subscribe) ∷ sharedPlumb burst) LEN
            (∧-intro refl
               (sharedPlumb-count (suc (Caps.cWid C2)) burst
                  (all-impl _ _
                     (λ em → ≤ᵇ-widen (valCountᵉ (InstEmit.events em))
                               (s≤s (proj₁ (proj₂ bmp))))
                     burst (countVals C1 burst CNT))))
... | false =
  suc (suc j₂)
    , subst (λ x → capsOK? (frameStep x c) sched₁ st₂ ≡ true) (sym lvl)
        (capsOK?-mono C1 C2 sched₁ st₂ bmp SUB)
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                        ∷ sharedPlumb burst) ≡ true)
            (sym lvl)
            (∧-intro refl
               (sharedPlumb-caps C2 sl burst (burstCaps?-widen sl burst bmp BC)))
    , subst (λ x → burstCount? (frameStep x c)
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                        ∷ sharedPlumb burst) ≡ true)
            (sym lvl) COUNT
    , connect-step (Caps.cSize c) (Caps.cWid c) dep bud j j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  where
  st₀ = record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }
  st₁ = register (toℕ i) κ st₀
  IH  = subscribeE-caps c dep bud (Caps.cSize (frameStep (suc j) c)) (suc j) fuel′ d (share-sink i) id now sl sched st₁
          2≤S 1≤R slEq slC slSz
          (register-caps c j (toℕ i) κ sched st₀ 2≤S 1≤R inv pC)
          (≤-trans szd (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))))
          (≤-trans wdd (proj₁ (proj₂ (frameStep-mono-j c 2≤S (n≤1+n j)))))
          refl
          (≤-trans (s≤s z≤n) (2≤frameStep-size c (suc j) 2≤S)) nst
          (frameStep-size-strict-suc c j (sizeᵉ d) (≤-trans (s≤s z≤n) 2≤S) szd)
          dpt
  j₂  = proj₁ IH
  SUB = proj₁ (proj₂ IH)
  BC  = proj₁ (proj₂ (proj₂ IH))
  res = subscribeE fuel′ d (share-sink i) id now sched st₁
  burst = proj₁ res
  sched₁ = proj₁ (proj₂ res)
  st₂ = proj₂ (proj₂ res)
  CNT = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  C1  = frameStep (suc (j + j₂)) c
  C2  = frameStep (suc (suc (j + j₂))) c
  bmp : C1 ⊑ᶜ C2
  bmp = frameStep-mono-j c 2≤S (n≤1+n (suc (j + j₂)))
  lvl : j + suc (suc j₂) ≡ suc (suc (j + j₂))
  lvl = trans (+-suc j (suc j₂)) (cong suc (+-suc j j₂))
  LEN : length (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                  ∷ sharedPlumb burst)
          ≤ suc (Caps.cWid C2)
  LEN = suc-fits c (suc (j + j₂)) (length (sharedPlumb burst)) 2≤S
          (subst (λ x → x ≤ suc (Caps.cWid C1)) (sym (sharedPlumb-len burst))
                 (countLen C1 burst CNT))
  COUNT : burstCount? C2
            (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
               ∷ sharedPlumb burst) ≡ true
  COUNT = countIn C2 (((init (toℕ i) ∷ []) at id from toℕ i as subscribe)
                        ∷ sharedPlumb burst) LEN
            (∧-intro refl
               (sharedPlumb-count (suc (Caps.cWid C2)) burst
                  (all-impl _ _
                     (λ em → ≤ᵇ-widen (valCountᵉ (InstEmit.events em))
                               (s≤s (proj₁ (proj₂ bmp))))
                     burst (countVals C1 burst CNT))))

-- THE JOIN.  A spent share answers with a one-shot close, a live one
-- registers (one j), and an unconnected one connects
sharedSlot-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
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
  {ok : T (inputsBelowᵉ (toℕ i) d)} → sl i ≡ shared d {ok = ok} →
  suc (resid sl (EvalSt.connectedShares st)) ≤ bud →
  depthShSlot g i d κ id now sched st ≤ dep →
  let r = subscribeSharedSlot g i d κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- AND THE LEVEL, at the budget the SLOT holds rather than one above:
     -- connecting spends the level, so this head hands the connect its
     -- predecessor and gets the sweep back at its own `bud`
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep bud (suc j))
-- the empty budget is ruled out by the residue hypothesis itself: a
-- subscribe at `input i` carries `suc (resid …) ≤ bud` unconditionally
sharedSlot-caps c dep zero j g i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv szd wdd pC lC seq () dpt
sharedSlot-caps {Γ = Γ} c dep (suc bud′) j g i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv szd wdd pC lC seq nst dpt
  with memberSource (toℕ i) (EvalSt.completedSources st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                        at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud′) j
... | false with memberSource (toℕ i) (EvalSt.connectedShares st) in freshEq
...   | true  =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
    -- the registration is a level, and the budget's positivity is now
    -- free rather than earned: the head matched it as a successor
    , refl , queue-push (Caps.cSize c) (Caps.cWid c) dep (suc bud′) j (s≤s z≤n)
-- THE CONNECT SPENDS THE LEVEL, so the callee runs at the PREDECESSOR and
-- hands its sweep back at `suc bud′` — this head's own budget.  That is
-- what `share-step` is for
...   | false = sharedConnect-caps c dep bud′ j g i d κ id now sl sched st
                  2≤S 1≤R slEq slC slSz inv szd wdd pC lC
                  (share-step sl (EvalSt.connectedShares st) i bud′ seq freshEq nst)
                  dpt

thruConsume-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
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
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthConsume g op nid κ id now o sched st ≤ dep →
  let r = thruConsume g op nid κ id now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     -- the inside of one payload, so it reports in subscribeInner's shape
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))

-- FLATTEN: subscribe and bump the live count while a lane is free,
-- park the payload when none is
thruConsume-caps {n = n} {u = u} c dep bud j g mergeAllᵒ nid κ id now o sl sched st
                 2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
     | lookupNode-park (Caps.cSize (frameStep j c))
         (slotsSize (Sched.slots sched)) nid (EvalSt.nodes st)
         (capsOK?-nodePark (frameStep j c) sched st inv)
... | nothing                | _ | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       | _ | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       | _ | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st _ _)   | _ | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st _ _)  | _ | _ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (mergeAll-st {w} lim act q od) | (bn , wn) | pk with w ≟ᵗ u
...   | no _ = 0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
                         (sym (+-identityʳ j)) inv
             , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
-- A LANE IS FREE: subscribe, then bump the counter the drain reads.
-- The queue rides through untouched, which is why the bump's receipt is
-- the lookup's and no longer `refl`
...   | yes refl with hasRoom lim act
...     | true =
  j′ , capsOK?-mergeAllBump (frameStep (j + j′) c) nid
         (proj₁ (proj₂ (proj₂ (proj₂ R))))
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ (proj₂ SI)))
     , proj₂ (proj₂ (proj₂ (proj₂ SI)))
  where
  SI = subscribeInner-caps c dep bud j g mergeAllᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
  j′ = proj₁ SI
  R  = subscribeInner g mergeAllᵒ nid κ id now o sched st
-- THE ONE WRITE THAT GROWS THE QUEUE, and therefore the one
-- clause of the clique that reports a witness for no other reason than
-- the cardinality conjunct.  `widNode` bounds the queue's LENGTH by the
-- level's width as well as its contents pointwise, so the cons has to be
-- paid for: one level takes cWid to `foldStep`, which dominates
-- `suc cWid` with room, and the witness goes 0 ↦ 1.  Nothing else in the
-- clause needs the extra level — both value and event lists are empty
-- here, so their conjuncts are `refl` at any caps
...     | false =
  1 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym lvl)
            (capsOK?-setNode (frameStep (suc j) c)
               nid (mergeAll-st lim act (q ++ o ∷ []) od)
               sched st BN PK WN
               (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st
                  (frameStep-mono-j c 2≤S (n≤1+n j)) inv))
    , refl , refl
    -- and its positivity is now FREE: the head reports at `suc bud`, so
    -- the budget this needs to be positive is a literal successor and the
    -- `1≤nest` route it used to take is dead
    , queue-push (Caps.cSize c) (Caps.cWid c) dep (suc bud) j (s≤s z≤n)
  where
  lvl : j + 1 ≡ suc j
  lvl = +-comm j 1

  BN = all-++-intro (λ x → sizeᵉ x ≤ᵇ Caps.cSize (frameStep (suc j) c)) q (o ∷ [])
         (all-impl _ _ (λ x → ≤ᵇ-widen (sizeᵉ x)
                                (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))) q bn)
         (∧-intro (≤ᵇ-widen (sizeᵉ o) (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))
                    (valCaps?-size (frameStep j c) sl (obs u) o vC))
                  refl)
  WN = widNode-push c j (Sched.slots sched) lim q o act od 2≤S wn
         (subst (λ y → (pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                (sym slEq) (valCaps?-wid (frameStep j c) sl (obs u) o vC))
  PK = subst (λ y → all (λ x → 3 + (sizeᵉ x + slotsSize y)
                                 ≤ᵇ Caps.cSize (frameStep (suc j) c))
                        (q ++ o ∷ []) ≡ true)
             (sym slEq)
             (parkList-push c j sl q o 2≤S slSz
                (≤ᵇ⇒≤ (sizeᵉ o) (Caps.cSize (frameStep j c))
                      (T-to (valCaps?-size (frameStep j c) sl (obs u) o vC)))
                (subst (λ y → all (λ x → 3 + (sizeᵉ x + slotsSize y)
                                           ≤ᵇ Caps.cSize (frameStep j c)) q ≡ true)
                       slEq pk))

-- SWITCH: cut the outgoing inner, subscribe the new one, record it
thruConsume-caps c dep bud j g switchᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
  with lookupNode nid (EvalSt.nodes st) | dpt
... | nothing                | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (mergeAll-st _ _ _ _) | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st _ _)  | dpt′ = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st cur od) | dpt′ =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ R))) then nothing
                     else just (proj₁ R)) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , all-++-intro (eventCaps? (frameStep (j + j′) c) sl)
         (proj₁ KILL) _
         (switchKill-closes-caps (frameStep (j + j′) c) sl cur sched st)
         (proj₁ (proj₂ (proj₂ (proj₂ SI))))
     , proj₂ (proj₂ (proj₂ (proj₂ SI)))
  where
  KILL = switchKill cur sched st
  sched₁ = proj₁ (proj₂ KILL)
  st₁    = proj₂ (proj₂ KILL)
  SI = subscribeInner-caps c dep bud j g switchᵒ nid κ id now o sl sched₁ st₁
         2≤S 1≤R (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq) slC slSz
         (switchKill-caps (frameStep j c) cur sched st inv) vC pC lC
         (nest-keeps o sl _ _ bud
            (KeepsC.connMono (switchKill-keeps cur sched st)) nst)
         dpt′
  j′ = proj₁ SI
  R  = subscribeInner g switchᵒ nid κ id now o sched₁ st₁

-- EXHAUST: drop while busy, otherwise subscribe and latch
thruConsume-caps c dep bud j g exhaustᵒ nid κ id now o sl sched st 2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (scan-st _)       = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (take-st _)       = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (mergeAll-st _ _ _ _) = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (switch-st _ _)   = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st true od)  = 0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
... | just (exhaust-st false od) =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ R))))) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ (proj₂ SI)))
     , proj₂ (proj₂ (proj₂ (proj₂ SI)))
  where
  SI = subscribeInner-caps c dep bud j g exhaustᵒ nid κ id now o sl sched st
         2≤S 1≤R slEq slC slSz inv vC pC lC nst dpt
  j′ = proj₁ SI
  R  = subscribeInner g exhaustᵒ nid κ id now o sched st

-- THE WALK: one payload at a time, receipts adding exactly as the
-- delivery clique's do
thruWalk-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (nid : NodeId)
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
  mList? bud sl (EvalSt.connectedShares st) vals ≡ true →
  depthWalk g op nid κ id now vals sched st ≤ dep →
  let r = thruWalk g op nid κ id now vals sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     -- ONE PAYLOAD AT A TIME, so the walk's index is the payload count
     × (j + j′ ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) j)
thruWalk-caps c dep bud j g op nid κ id now [] sl sched st 2≤S 1≤R slEq slC slSz inv pC vC lC nst dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl , walk-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
-- ONE MORE FOLD THAN THE ADDITIVE CLAUSES, and Concat-Sum-Probe is why:
-- the output is `proj₁ TC ++ proj₁ REST`, a SUM of two counts, and a sum
-- does not fit the width its two summands came in under.  `suc (j₁ + j₂)`
-- buys the extra rung, charged per cons so no cardinality hypothesis on
-- `os` is needed
thruWalk-caps {u = u} c dep bud j g op nid κ id now (o ∷ os) sl sched st
              2≤S 1≤R slEq slC slSz inv pC vC lC nst dpt =
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
        (subst (λ x → length (proj₁ TC ++ proj₁ REST)
                        ≤ suc (Caps.cWid (frameStep x c)))
               (sym lvlW)
               (concat-fits c ((j + j₁) + j₂) (proj₁ TC) (proj₁ REST) 2≤S
                  (lenWiden (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                     (valsLen (frameStep (j + j₁) c) sl (proj₁ TC)
                        (proj₁ (proj₂ (proj₂ HD)))))
                  (valsLen (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                     (proj₁ (proj₂ (proj₂ IH))))))
    , eventsCaps?-widen sl (proj₁ (proj₂ TC) ++ proj₁ (proj₂ REST)) ⊑ˢ
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl (proj₁ (proj₂ TC))
              (frameStep-⊑-+ c 2≤S (j + j₁) j₂) (proj₁ (proj₂ (proj₂ (proj₂ HD)))))
           (proj₁ (proj₂ (proj₂ (proj₂ IH)))))
    -- ONE PAYLOAD, and the head is spent in the STRICT form: that is what
    -- thruConsume-caps reports, and `walk-step-suc` is `walk-step` with
    -- the `suc` this clause's per-cons fold charge puts on the witness
    , walk-step-suc (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length os) j j₁ j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ HD))))
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  where
  vCa = valsOf (frameStep j c) sl (o ∷ os) vC
  HD  = thruConsume-caps c dep bud j g op nid κ id now o sl sched st
          2≤S 1≤R slEq slC slSz inv (proj₁ (∧-true _ _ vCa)) pC lC
          (mList?-head bud sl _ o os nst)
          (≤-trans (m≤m⊔n _ _) dpt)
  j₁  = proj₁ HD
  TC  = thruConsume g op nid κ id now o sched st
  sd₁ = proj₁ (proj₂ (proj₂ TC))
  st₁ = proj₂ (proj₂ (proj₂ TC))
  IH  = thruWalk-caps c dep bud (j + j₁) g op nid κ id now os sl sd₁ st₁
          2≤S 1≤R
          (trans (KeepsC.slotsEq (thruConsume-keeps g op nid κ id now o sched st))
                 slEq)
          slC slSz (proj₁ (proj₂ HD))
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
          (valsIn (frameStep (j + j₁) c) sl os
             (valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)
                (proj₂ (∧-true _ _ vCa)))
             (lenWiden os (frameStep-⊑-+ c 2≤S j j₁)
                (≤-trans (n≤1+n (length os))
                         (valsLen (frameStep j c) sl (o ∷ os) vC))))
          (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
          (mList?-keeps bud sl _ _ os
             (KeepsC.connMono (thruConsume-keeps g op nid κ id now o sched st))
             (mList?-tail bud sl _ o os nst))
          (≤-trans (m≤n⊔m _ _) dpt)
  j₂   = proj₁ IH
  REST = thruWalk g op nid κ id now os sd₁ st₁
  ⊑ˢ   = frameStep-+suc c j j₁ j₂ 2≤S
  lvlW : j + suc (j₁ + j₂) ≡ suc ((j + j₁) + j₂)
  lvlW = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))

mergeAllDrain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
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
  mList? bud sl (EvalSt.connectedShares st) q ≡ true →
  depthDrain g allNid κ id now q sched st ≤ dep →
  let r = mergeAllDrain g allNid κ id now lim act q sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (obsCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     -- a drain is a WALK over the parked queue, indexed by its length
     × (j + j′ ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length q) j)
mergeAllDrain-caps c dep bud j g allNid κ id now lim act [] sl sched st 2≤S 1≤R slEq slC slSz inv pC lC qC nst dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl , refl , walk-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
-- THE GATE IS SHUT: nothing is subscribed and the queue comes back the
-- one that went in, so the residue's bound is the entry hypothesis and
-- the level does not move at any queue length
mergeAllDrain-caps {s = s} c dep bud j g allNid κ id now lim act (o ∷ q) sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC qC nst dpt
  with hasRoom lim act
... | false =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , refl , refl
    , subst (λ x → all (obsCaps? (frameStep x c) sl) (o ∷ q) ≡ true)
            (sym (+-identityʳ j)) qC
    , walk-none (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc (length q)) j
-- A LANE IS FREE.  The walk no longer STOPS at an inner that stays open
-- — that inner spends a lane and the drain carries on — so there is one
-- step clause where concat had two, and it is concat's: the two receipts
-- add, and `vs ++ proj₁ REST` is a SUM of two counts, so the clause pays
-- the extra fold Concat-Sum-Probe showed the sum needs
... | true
  with subscribeInner g mergeAllᵒ allNid κ id now o sched st in SIeq
     | subscribeInner-caps c dep bud j g mergeAllᵒ allNid κ id now o sl sched st
         2≤S 1≤R slEq slC slSz inv (proj₁ (∧-true _ _ qC)) pC lC
         (mList?-head bud sl _ o q nst)
         (≤-trans (m≤m⊔n _ _) dpt)
     | KeepsC.slotsEq (subscribeInner-keeps g mergeAllᵒ allNid κ id now o sched st)
     | KeepsC.connMono (subscribeInner-keeps g mergeAllᵒ allNid κ id now o sched st)
...   | (inst , vs , bs , done , sched₁ , st₁) | (j₁ , SUB , VC , EC , LV) | sEq | cMono =
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
        (subst (λ x → length (vs ++ proj₁ REST)
                        ≤ suc (Caps.cWid (frameStep x c)))
               (sym lvlW)
               (concat-fits c ((j + j₁) + j₂) vs (proj₁ REST) 2≤S
                  (lenWiden vs (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                     (valsLen (frameStep (j + j₁) c) sl vs VC))
                  (valsLen (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST)
                     (proj₁ (proj₂ (proj₂ IH))))))
    , eventsCaps?-widen sl (bs ++ proj₁ (proj₂ REST)) ⊑ˢ
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl) bs
           (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl bs (frameStep-⊑-+ c 2≤S (j + j₁) j₂) EC)
           (proj₁ (proj₂ (proj₂ (proj₂ IH)))))
    , obsListCaps?-widen sl (proj₁ (proj₂ (proj₂ (proj₂ REST)))) ⊑ˢ
        (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
    -- ONE PAYLOAD AND THE DRAIN BEHIND IT.  The witness is `suc (j₁ +
    -- j₂)` because the sum of the two counts pays one extra fold, and
    -- `walk-step-suc` is the step that spends the inner's STRICT report
    -- verbatim — no weakening here, unlike the branch above
    , walk-step-suc (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length q) j j₁ j₂ 2≤S
        LV (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  where
  IH   = mergeAllDrain-caps c dep bud (j + j₁) g allNid κ id now lim
           (if done then act else suc act) q sl sched₁ st₁
           2≤S 1≤R (trans sEq slEq) slC slSz SUB
           (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
           (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
           (obsListCaps?-widen sl q (frameStep-⊑-+ c 2≤S j j₁)
              (proj₂ (∧-true _ _ qC)))
           (mList?-keeps bud sl _ _ q cMono (mList?-tail bud sl _ o q nst))
           -- `sched₁`/`st₁` came off the `with`-pattern on `subscribeInner
           -- ...`, not off a transparent `where`-binding, so `dpt`'s own
           -- reduction (which re-invokes `subscribeInner` symbolically via
           -- the mirror's `r`) does not unify with them by mere reduction —
           -- the `with`'s helper-function boundary makes that opaque.
           -- `SIeq` (the `in`-recorded equation) bridges the two
           (subst (λ p → depthDrain g allNid κ id now q (proj₁ p) (proj₂ p) ≤ dep)
                  (cong (λ x → proj₂ (proj₂ (proj₂ (proj₂ x)))) SIeq)
                  (≤-trans (m≤n⊔m _ _) dpt))
  j₂   = proj₁ IH
  REST = mergeAllDrain g allNid κ id now lim (if done then act else suc act) q sched₁ st₁
  ⊑ˢ   = frameStep-+suc c j j₁ j₂ 2≤S
  lvlW : j + suc (j₁ + j₂) ≡ suc ((j + j₁) + j₂)
  lvlW = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))

-- .Caps-Face's innerFinish-zero still speaks the cardinality-free
-- payload form, and .Caps-Face is not touched this leg, so its twenty-odd
-- call sites below go through this one adapter: unpack with valsOf on the
-- way in, repack with valsIn on the way out
innerFinish-zero′ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (dep j : ℕ) (sl : Slots Γ) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c) sched st ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl vals ≡ true)
     × (all (eventCaps? {n = n} {Γ = Γ} {u = t} (frameStep (j + j′) c) sl) []
          ≡ true)
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)
innerFinish-zero′ {t = t} c dep j sl vals sched st 2≤S inv vC =
  proj₁ Z , proj₁ (proj₂ Z)
    , face-vals c j (proj₁ Z) sl vals 2≤S (proj₁ (proj₂ (proj₂ Z)))
        (valsLen (frameStep j c) sl vals vC)
    , proj₂ (proj₂ (proj₂ Z))
    , frame-nil (Caps.cSize c) (Caps.cWid c) dep j
  where
  Z = innerFinish-zero {t = t} c j sl vals sched st inv
        (valsOf (frameStep j c) sl vals vC)

innerFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
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
  frameBud c j ≤ bud →
  depthFin g op allNid inst κ id now vals sched st
    (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
  let r = innerFinish g op allNid inst κ id now vals sched st
            (lookupNode allNid (EvalSt.nodes st))
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     -- the inside of ONE frame, so it reports in stepFrame's shape
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)

-- FLATTEN: decrement the live count, drain the queue and reinstall the
-- residue, which comes back from mergeAllDrain-caps with the very bound
-- the node needs.  At an unbounded limit the queue is empty and the
-- drain degenerates to the decrement the merge face used to state alone
innerFinish-caps {n = n} {s = s} c dep bud j g mergeAllᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC fb dpt
  with lookupNode allNid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) allNid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
     | lookupNode-park (Caps.cSize (frameStep j c))
         (slotsSize (Sched.slots sched)) allNid (EvalSt.nodes st)
         (capsOK?-nodePark (frameStep j c) sched st inv)
... | nothing              | _ | _ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (scan-st _)     | _ | _ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (take-st _)     | _ | _ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (switch-st _ _) | _ | _ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (exhaust-st _ _) | _ | _ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (mergeAll-st {w} lim act q od) | (bn , wn) | pk with w ≟ᵗ s | dpt
...   | no _     | dpt′ = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
-- `vals ++ proj₁ DR` is the third SUM, so this clause too reports one
-- fold beyond what the drain handed back.
--
-- AND THIS IS THE SECOND ARC THAT SPENDS DEPTH FUEL — the only one
-- outside `stepFrame-caps`'s thru-outer.  `depthFinC`'s `yes refl` arm is
-- `suc (depthDrain …)` (.Caps-Depth), so `dpt′` reads `suc _ ≤ dep`: at
-- `zero` this branch is unreachable, and at `suc dep′` the drain runs one
-- level lower.  The split has to sit BELOW the type dispatch, because the
-- `no` arm spends nothing and must stay reachable at `dep = zero`
...   | yes refl | dpt′ with dep | dpt′
...     | zero     | ()
...     | suc dep′ | s≤s dpt″ =
  suc j′ , capsOK?-mono (frameStep (j + j′) c) (frameStep (j + suc j′) c) sd₁ ST₁ ⊑ˢ
         (capsOK?-setNode (frameStep (j + j′) c) allNid
            (mergeAll-st lim (proj₁ (proj₂ (proj₂ DR))) (proj₁ (proj₂ (proj₂ (proj₂ DR)))) od)
            sd₁ st₁
            (obsList-nodeSz (frameStep (j + j′) c) sl
               (proj₁ (proj₂ (proj₂ (proj₂ DR)))) RES)
            qPark
            (∧-intro
               (subst (λ y → all (λ x → pWᵉ n y x ≤ᵇ Caps.cWid (frameStep (j + j′) c))
                               (proj₁ (proj₂ (proj₂ (proj₂ DR)))) ≡ true)
                      (sym (trans (KeepsC.slotsEq
                                    (mergeAllDrain-keeps g allNid κ id now lim (pred act) q sched st))
                                  slEq))
                      (obsList-nodeWid (frameStep (j + j′) c) sl
                         (proj₁ (proj₂ (proj₂ (proj₂ DR)))) RES))
               qCard)
            (proj₁ (proj₂ CD)))
     , valsIn (frameStep (j + suc j′) c) sl (vals ++ proj₁ DR)
         (valsCaps?-widen sl s (vals ++ proj₁ DR) ⊑ˢ
            (all-++-intro (valCaps? (frameStep (j + j′) c) sl s) vals (proj₁ DR)
               (valsCaps?-widen sl s vals (frameStep-⊑-+ c 2≤S j j′)
                  (valsOf (frameStep j c) sl vals vC))
               (valsOf (frameStep (j + j′) c) sl (proj₁ DR)
                  (proj₁ (proj₂ (proj₂ CD))))))
         (subst (λ x → length (vals ++ proj₁ DR)
                         ≤ suc (Caps.cWid (frameStep x c)))
                (sym (+-suc j j′))
                (concat-fits c (j + j′) vals (proj₁ DR) 2≤S
                   (lenWiden vals (frameStep-⊑-+ c 2≤S j j′)
                      (valsLen (frameStep j c) sl vals vC))
                   (valsLen (frameStep (j + j′) c) sl (proj₁ DR)
                      (proj₁ (proj₂ (proj₂ CD))))))
     , eventsCaps?-widen sl (proj₁ (proj₂ DR)) ⊑ˢ
         (proj₁ (proj₂ (proj₂ (proj₂ CD))))
     -- the drain reported in `sIterD` at the budget this frame RE-READ, so
     -- its `k` is `frameBud c j` on the nose and `concat-frame`'s own `hk`
     -- is `≤-refl`.  The `suc` on `j′` is the frame's slot, and
     -- `concat-frame` pays for it out of the room the queue did not use
     , concat-frame (Caps.cSize c) (Caps.cWid c) dep′
         (suc (sizeAt (Caps.cSize c) (suc j))) (length q) j j′ 2≤S
         (≤ᵇ⇒≤ (length q) (Caps.cWid (frameStep j c)) (T-to wnLen))
         ≤-refl
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ CD)))))
  where
  wnAll = proj₁ (∧-true (all (λ o → pWᵉ n (Sched.slots sched) o
                                      ≤ᵇ Caps.cWid (frameStep j c)) q)
                        (length q ≤ᵇ Caps.cWid (frameStep j c)) wn)
  wnLen = proj₂ (∧-true (all (λ o → pWᵉ n (Sched.slots sched) o
                                      ≤ᵇ Caps.cWid (frameStep j c)) q)
                        (length q ≤ᵇ Caps.cWid (frameStep j c)) wn)
  qObs = obsList-intro (frameStep j c) sl q bn
           (subst (λ y → all (λ o → pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) q
                           ≡ true)
                  slEq wnAll)
  -- THE DRAIN RUNS AT THE REFRESHED BUDGET, exactly as `stepFrame-caps`'s
  -- thru-outer clause hands `thruWalk-caps` `sizeAt S (suc j)`.  That is
  -- what the spent unit of depth fuel buys, and it is why the queue's
  -- `mList?` comes from `obsList→mList-strict` — which is STATED at this
  -- budget — rather than from the inherited `bud` via `mList?-widen`: a
  -- bound in the larger transformer would not meet `frameBud c j`
  CD  = mergeAllDrain-caps c dep′ (sizeAt (Caps.cSize c) (suc j)) j g allNid κ
          id now lim (pred act) q sl sched st
          2≤S 1≤R slEq slC slSz inv pC lC qObs
          (obsList→mList-strict c j sl _ q (≤-trans (s≤s z≤n) 2≤S) slSz qObs)
          dpt″
  j′  = proj₁ CD
  ⊑ˢ  = frameStep-mono-j c 2≤S
          (≤-trans (n≤1+n (j + j′)) (≤-reflexive (sym (+-suc j j′))))
  RES = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ CD))))
  DR  = mergeAllDrain g allNid κ id now lim (pred act) q sched st
  sd₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ DR))))
  ST₁ = record st₁
          { nodes = setNode allNid
                      (mergeAll-st lim (proj₁ (proj₂ (proj₂ DR)))
                                  (proj₁ (proj₂ (proj₂ (proj₂ DR)))) od)
                      (EvalSt.nodes st₁) }
  -- AND THE RESIDUE IS A SUFFIX, which is what the parked-term conjunct
  -- needs and the length reading cannot give: the room the entry queue
  -- had is the room the residue has, and the only move is the widening
  -- to the level the drain reports at
  qPark : all (λ x → 3 + (sizeᵉ x + slotsSize (Sched.slots sd₁))
                       ≤ᵇ Caps.cSize (frameStep (j + j′) c))
              (proj₁ (proj₂ (proj₂ (proj₂ DR)))) ≡ true
  qPark =
    subst (λ y → all (λ x → 3 + (sizeᵉ x + slotsSize y)
                              ≤ᵇ Caps.cSize (frameStep (j + j′) c))
                     (proj₁ (proj₂ (proj₂ (proj₂ DR)))) ≡ true)
          (sym (KeepsC.slotsEq
                 (mergeAllDrain-keeps g allNid κ id now lim (pred act) q sched st)))
          (all-impl _ _
            (λ x → ≤ᵇ-widen (3 + (sizeᵉ x + slotsSize (Sched.slots sched)))
                     (proj₁ (frameStep-⊑-+ c 2≤S j j′)))
            (proj₁ (proj₂ (proj₂ (proj₂ DR))))
            (drain-queue-all
              (λ x → 3 + (sizeᵉ x + slotsSize (Sched.slots sched))
                       ≤ᵇ Caps.cSize (frameStep j c))
              g allNid κ id now lim (pred act) q sched st pk))

  -- THE DRAIN'S RESIDUE IS SHORTER THAN THE QUEUE IT CAME FROM, so the
  -- cardinality conjunct the reinstall owes is the entry one, widened
  qCard : (length (proj₁ (proj₂ (proj₂ (proj₂ DR))))
             ≤ᵇ Caps.cWid (frameStep (j + j′) c)) ≡ true
  qCard = T⇒≡true _ (≤⇒≤ᵇ
    (≤-trans (drain-queue-shrinks g allNid κ id now lim (pred act) q sched st)
             (≤-trans (≤ᵇ⇒≤ (length q) (Caps.cWid (frameStep j c)) (T-to wnLen))
                      (proj₁ (proj₂ (frameStep-⊑-+ c 2≤S j j′))))))

-- SWITCH: clear the current-inner slot if this was it
innerFinish-caps c dep bud j g switchᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC fb dpt
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (scan-st _)       = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (take-st _)       = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (mergeAll-st _ _ _ _)    = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (exhaust-st _ _)  = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (switch-st nothing od) = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (switch-st (just cur) od) with cur ≡ᵇ inst
...   | false = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
...   | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (switch-st nothing od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (switch-st nothing od)
               sched st refl refl refl inv)
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl , frame-nil (Caps.cSize c) (Caps.cWid c) dep j

-- EXHAUST: clear the busy flag
innerFinish-caps c dep bud j g exhaustᵒ allNid inst κ id now vals sl sched st
                 2≤S 1≤R slEq slC slSz inv pC lC vC fb dpt
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (scan-st _)       = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (take-st _)       = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (mergeAll-st _ _ _ _)    = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (switch-st _ _)   = innerFinish-zero′ c dep j sl vals sched st 2≤S inv vC
... | just (exhaust-st act od) =
  0 , subst (λ x → capsOK? (frameStep x c) sched
                     (record st { nodes = setNode allNid (exhaust-st false od)
                                            (EvalSt.nodes st) }) ≡ true)
            (sym (+-identityʳ j))
            (capsOK?-setNode (frameStep j c) allNid (exhaust-st false od)
               sched st refl refl refl inv)
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl , frame-nil (Caps.cSize c) (Caps.cWid c) dep j

subscribeE-input-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  suc (resid sl (EvalSt.connectedShares st)) ≤ bud →
  depthE g (input i) κ id now sched st ≤ dep →
  let r = subscribeE g (input i) κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- the same sweep the slot edge reports, forwarded: every clause here
     -- either delegates to it or moves the level by at most one
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep bud (suc j))
subscribeE-input-caps {n = n} {Γ = Γ} c dep bud j g i κ id now sl sched st
                      2≤S 1≤R slEq slC slSz inv pC lC nst dpt
  with Sched.slots sched i in slotEq
     | subst (λ y → slotCaps? (Caps.cSize c) (Caps.cWid c) sl (y i) ≡ true) (sym slEq)
             (slotsCaps?-lookup (Caps.cSize c) (Caps.cWid c) sl i slC)
     -- the slot's OWN size, abstracted alongside the slot: a cold leaf
     -- counts its sync values, and a list is no longer than the size
     -- that counts it.  `slSz` speaks of `sl i` and the `with` matches on
     -- `Sched.slots sched i`, so the bound has to travel through slEq
     -- HERE, before abstraction, or the clause never sees it
     | subst (λ y → slotSize (y i) ≤ Caps.cSize c) (sym slEq)
             (≤-trans (slotSize≤slotsSize sl i) slSz)
     | dpt
-- SHARED: the def's size, and — since the parked-width repair — its
-- parked width, are the two things sharedSlot-caps asks for.  Both come
-- straight out of the slot telescope's own side condition
... | shared d | sd | sz | dpt′ =
  sharedSlot-caps c dep bud j g i d κ id now sl sched st 2≤S 1≤R slEq slC slSz inv
    (≤-trans (≤ᵇ⇒≤ (sizeᵉ d) (Caps.cSize c)
                (T-to (proj₁ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c) _ sd))))
             (cSize≤frameStep c j 2≤S))
    (≤-trans (m≤n⊔m _ (dWᵉ n sl d))
      (≤-trans (≤ᵇ⇒≤ (pWᵉ n sl d) (Caps.cWid c)
                  (T-to (proj₁ (∧-true (pWᵉ n sl d ≤ᵇ Caps.cWid c) _
                          (proj₂ (∧-true (sizeᵉ d ≤ᵇ Caps.cSize c) _ sd))))))
               (cWid≤frameStep c j 2≤S)))
    pC lC
    -- the slot equation, taken AT the `with` that consumes the scrutinee:
    -- after abstraction the connection between `sl i` and `shared d` is
    -- gone, and it is the one fact `resid-connect` cannot do without
    (trans (sym (cong (λ y → y i) slEq)) slotEq)
    nst dpt′
-- HOT SCRIPT: spent, or one more registration
... | scripted (hot async) | sd | sz | dpt′
  with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                        at id from toℕ i as subscribe) ∷ []) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep bud j
...   | false =
  1 , subst (λ x → capsOK? (frameStep x c) sched (register (toℕ i) κ st) ≡ true)
            (sym (j+1 j)) (register-caps c j (toℕ i) κ sched st 2≤S 1≤R inv pC)
    , subst (λ x → burstCaps? {u = lookup Γ i} (frameStep x c) sl
                     (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j)) refl
    , refl , queue-push (Caps.cSize c) (Caps.cWid c) dep bud j
               (≤-trans (s≤s z≤n) nst)
-- COLD, NO TAIL: a one-shot burst of the slot's own sync values, and
-- nothing goes into the state but a source counter capsOK? does not read
subscribeE-input-caps {Γ = Γ} c dep bud j g i κ id now sl sched st
                      2≤S 1≤R slEq slC slSz inv pC lC nst dpt
  | scripted {ok} (cold sync []) | sd | sz | dpt′ =
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
    , subst (λ x → burstCount? (frameStep x c)
                     (proj₁ (oneShotBurst sync id sched)) ≡ true)
            (sym (j+1 j)) COUNT
    , queue-push (Caps.cSize c) (Caps.cWid c) dep bud j (≤-trans (s≤s z≤n) nst)
  where
  step⊑ = frameStep-mono-j c 2≤S (n≤1+n j)
  SY = valsCaps?-data (frameStep j c) sl (lookup Γ i) ok sync
         (all-impl (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c)
                   (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize (frameStep j c))
                   (λ v → ≤ᵇ-widen (sizeᵛ (lookup Γ i) v)
                            (cSize≤frameStep c j 2≤S)) sync
            (proj₁ (∧-true (all (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c) sync)
                           _ sd)))
  -- THE COUNT.  One emit, so the length half is `1 ≤ suc _`; and that
  -- emit carries exactly the slot's sync values, whose count the slot
  -- telescope already bounds by cSize — which fits under the width one
  -- fold up (§1 at j = 0).  No fold is bought, so the witness stays 1
  CWD : Caps.cSize c ≤ Caps.cWid (frameStep (suc j) c)
  CWD = ≤-trans (size≤widAt1 c (≤-trans (s≤s z≤n) 2≤S))
                (proj₁ (proj₂ (frameStep-mono-j c 2≤S {1} {suc j} (s≤s z≤n))))
  LENB : length sync ≤ suc (Caps.cWid (frameStep (suc j) c))
  LENB = ≤-trans (≤-trans (≤-trans (len≤inputSize (lookup Γ i) sync []) sz) CWD)
                 (n≤1+n (Caps.cWid (frameStep (suc j) c)))
  COUNT : burstCount? (frameStep (suc j) c)
            (proj₁ (oneShotBurst sync id sched)) ≡ true
  COUNT = countIn (frameStep (suc j) c) (proj₁ (oneShotBurst sync id sched))
            (s≤s z≤n)
            (∧-intro
              (subst (λ x → (x ≤ᵇ suc (Caps.cWid (frameStep (suc j) c))) ≡ true)
                     (sym (oneShot-count sync (Sched.nextSource sched)))
                     (T⇒≡true (length sync
                                 ≤ᵇ suc (Caps.cWid (frameStep (suc j) c)))
                              (≤⇒≤ᵇ LENB)))
              refl)
-- COLD WITH A TAIL: a fresh source, a live entry for the async pendings,
-- and one registration
subscribeE-input-caps {Γ = Γ} c dep bud j g i κ id now sl sched st
                      2≤S 1≤R slEq slC slSz inv pC lC nst dpt
  | scripted {ok} (cold sync (dd ∷ ds)) | sd | sz | dpt′ =
  1 , subst (λ x → capsOK? (frameStep x c) SCHED₃ (register SRC κ st) ≡ true)
            (sym (j+1 j))
            (capsOK?-addLive (frameStep (suc j) c) NEW SCHED₂ (register SRC κ st)
               BL WL CL (register-caps c j SRC κ sched st 2≤S 1≤R inv pC))
    , subst (λ x → burstCaps? (frameStep x c) sl
                     (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j))
            (∧-intro (∧-intro refl
                        (mapValue-caps (frameStep (suc j) c) sl (lookup Γ i) sync SY))
                     refl)
    , subst (λ x → burstCount? (frameStep x c)
                     (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
                       ≡ true)
            (sym (j+1 j)) COUNT
    , queue-push (Caps.cSize c) (Caps.cWid c) dep bud j (≤-trans (s≤s z≤n) nst)
  where
  SRC    = Sched.nextSource sched
  SCHED₂ = record (record sched { nextSource = suc (Sched.nextSource sched) })
                  { nextOrdinal = suc (Sched.nextOrdinal sched) }
  NEW    = record { source = SRC ; ordinal = Sched.nextOrdinal sched
                  ; elemTy = lookup Γ i ; pending = resolve now (dd ∷ ds) }
  SCHED₃ = record SCHED₂ { live = NEW ∷ Sched.live SCHED₂ }
  sdp    = ∧-true (all (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c) sync) _ sd
  sdp₂   = ∧-true (all (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv) ≤ᵇ Caps.cSize c)
                       (dd ∷ ds)) _ (proj₂ sdp)
  SY = valsCaps?-data (frameStep (suc j) c) sl (lookup Γ i) ok sync
         (all-impl (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize c)
                   (λ v → sizeᵛ (lookup Γ i) v ≤ᵇ Caps.cSize (frameStep (suc j) c))
                   (λ v → ≤ᵇ-widen (sizeᵛ (lookup Γ i) v)
                            (cSize≤frameStep c (suc j) 2≤S)) sync (proj₁ sdp))
  CL : closLive (frameStep (suc j) c) (Sched.slots SCHED₂) NEW ≡ true
  CL = closLive-data (frameStep (suc j) c) (Sched.slots SCHED₂) NEW ok
  BL = resolve-caps (Caps.cSize (frameStep (suc j) c)) now (dd ∷ ds)
         (all-impl (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv) ≤ᵇ Caps.cSize c)
                   (λ tv → sizeᵛ (lookup Γ i) (Timed.val tv)
                             ≤ᵇ Caps.cSize (frameStep (suc j) c))
                   (λ tv → ≤ᵇ-widen (sizeᵛ (lookup Γ i) (Timed.val tv))
                             (cSize≤frameStep c (suc j) 2≤S)) (dd ∷ ds)
            (proj₁ sdp₂))
  WL = resolve-wid-data (Caps.cWid (frameStep (suc j) c)) (Sched.slots sched) ok
         (resolve now (dd ∷ ds))
  -- THE COUNT, exactly as in the no-tail clause: one emit, and it carries
  -- the sync prefix only — the async tail goes to the live set, not the
  -- burst — so `length sync` is still what has to fit
  CWD : Caps.cSize c ≤ Caps.cWid (frameStep (suc j) c)
  CWD = ≤-trans (size≤widAt1 c (≤-trans (s≤s z≤n) 2≤S))
                (proj₁ (proj₂ (frameStep-mono-j c 2≤S {1} {suc j} (s≤s z≤n))))
  LENB : length sync ≤ suc (Caps.cWid (frameStep (suc j) c))
  LENB = ≤-trans (≤-trans (≤-trans (len≤inputSize (lookup Γ i) sync (dd ∷ ds)) sz)
                          CWD)
                 (n≤1+n (Caps.cWid (frameStep (suc j) c)))
  COUNT : burstCount? (frameStep (suc j) c)
            (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
              ≡ true
  COUNT = countIn (frameStep (suc j) c)
            (((init SRC ∷ map value sync) at id from SRC as subscribe) ∷ [])
            (s≤s z≤n)
            (∧-intro
              (subst (λ x → (x ≤ᵇ suc (Caps.cWid (frameStep (suc j) c))) ≡ true)
                     (sym (valCountᵉ-mapValue sync))
                     (T⇒≡true (length sync
                                 ≤ᵇ suc (Caps.cWid (frameStep (suc j) c)))
                              (≤⇒≤ᵇ LENB)))
              refl)

-- THE from-inner CLAUSE: absorb, or finish.  Both the `fin = false` and
-- the absorbed branch are the identity on the state; only the finish
-- delegates, and it delegates to innerFinish-caps verbatim
innerReact-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
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
  frameBud c j ≤ bud →
  depthReact g op allNid inst κ id now vals sched st fin ≤ dep →
  let r = innerReact g op allNid inst κ id now vals sched st fin
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
     -- the inside of ONE frame too
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)
innerReact-caps c dep bud j g op allNid inst κ id now vals false sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC fb dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl , frame-nil (Caps.cSize c) (Caps.cWid c) dep j
innerReact-caps c dep bud j g op allNid inst κ id now vals true sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC fb dpt
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true) (sym (+-identityʳ j)) inv
    , subst (λ x → valsCaps? (frameStep x c) sl vals ≡ true)
            (sym (+-identityʳ j)) vC
    , refl , frame-nil (Caps.cSize c) (Caps.cWid c) dep j
... | false = innerFinish-caps c dep bud j g op allNid inst κ id now vals sl sched st
                2≤S 1≤R slEq slC slSz inv pS lC vC fb dpt

stepFrame-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (c : Caps) (dep bud j : ℕ) (g : Gas) (id : Id) (now : Tick)
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
  frameBud c j ≤ bud →
  depthFrame g id now f κ vals fin sched st ≤ dep →
  let r = stepFrame g id now f κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ r)) ≡ true)
     -- ONE FRAME, and no index: a frame is a single arc of the cycle, and
     -- it is the ONE arc that spends a unit of depth fuel — its payload
     -- walk runs at `dep` minus one, on the REFRESHED budget
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)

-- MAP: nothing touches the state, so the invariant is only widened
stepFrame-caps {u = u} c dep bud j g id now (map-f fn) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC fb dpt =
  j′ , capsOK?-mono (frameStep j c) (frameStep (j + j′) c) sched st
         (frameStep-⊑-+ c 2≤S j j′) inv
     , face-vals c j j′ sl (map (applyFn fn) vals) 2≤S (proj₂ MP)
         (≤-trans (≤-reflexive (length-map (applyFn fn) vals))
                  (valsLen (frameStep j c) sl vals vC))
     , refl
     -- ONE FOLD PER NODE of the step function, and `mapFrame-caps`'s
     -- witness reduces to exactly that, so the receipt is read off `fS`
     -- here rather than reported through the callee's Σ
     , frame-recv (Caps.cSize c) (Caps.cWid c) dep j j′
         (face-charge1 c j (sizeᵗ fn)
            (≤ᵇ⇒≤ (sizeᵗ fn) (Caps.cSize (frameStep j c)) (T-to fS)))
  where
  MP = mapFrame-caps c j sl fn vals 2≤S slC fS
         (valsOf (frameStep j c) sl vals vC)
  j′ = proj₁ MP

-- SCAN: its own top-level lemma, as in the wet family — the nested
-- `with` on the stored accumulator's type cannot be elaborated inside a
-- clause of the general frame case
stepFrame-caps c dep bud j g id now (scan-f fn nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC fb dpt =
  proj₁ SC , proj₁ (proj₂ SC)
    , face-vals c j (proj₁ SC) sl
        (proj₁ (stepFrame g id now (scan-f fn nid) κ vals fin sched st))
        2≤S (proj₁ (proj₂ (proj₂ SC)))
        (≤-trans (stepFrame-scan-len g id now fn nid κ vals fin sched st)
                 (valsLen (frameStep j c) sl vals vC))
    -- NOTE the shift: `SC` grew a fourth conjunct, so what used to be
    -- the bare events fact is now the head of a PAIR
    , proj₁ (proj₂ (proj₂ (proj₂ SC)))
    -- a scan's receipt is a PRODUCT and cannot be read off the call
    -- site — seven of the callee's eight clauses charge nothing and one
    -- charges the folds — so it is reported, and spent here
    , frame-recv (Caps.cSize c) (Caps.cWid c) dep j (proj₁ SC)
        (proj₂ (proj₂ (proj₂ (proj₂ SC))))
  where
  SC = stepFrame-scan-caps c j g id now fn nid κ vals fin sl sched st
         2≤S slC slEq inv fS pS
         (valsLen (frameStep j c) sl vals vC)
         (valsOf (frameStep j c) sl vals vC)

-- TAKE: a prefix and a cut, no folds
stepFrame-caps c dep bud j g id now (take-f nid) κ vals fin sl sched st 2≤S 1≤R slEq slC slSz inv fS pS lC vC fb dpt =
  0 , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ (proj₂ (proj₂ TD))))
                     (proj₂ (proj₂ (proj₂ (proj₂ TD)))) ≡ true)
            (sym (+-identityʳ j)) (proj₁ TDc)
    , subst (λ x → valsCaps? (frameStep x c) sl (proj₁ TD) ≡ true)
            (sym (+-identityʳ j))
            (valsIn (frameStep j c) sl (proj₁ TD) (proj₁ (proj₂ TDc))
               (≤-trans (takeDispatch-len nid vals fin sched st
                           (lookupNode nid (EvalSt.nodes st)))
                        (valsLen (frameStep j c) sl vals vC)))
    , subst (λ x → all (eventCaps? (frameStep x c) sl) (proj₁ (proj₂ TD)) ≡ true)
            (sym (+-identityʳ j)) (proj₂ (proj₂ TDc)) , frame-nil (Caps.cSize c) (Caps.cWid c) dep j
  where
  TD  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))
  TDc = takeDispatch-caps (frameStep j c) nid vals fin sl sched st
          (lookupNode nid (EvalSt.nodes st)) slEq inv
          (valsOf (frameStep j c) sl vals vC)

-- FROM-INNER and THRU-OUTER: the two *All edges, delegated whole
stepFrame-caps c dep bud j g id now (from-inner op allNid inst) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC fb dpt =
  innerReact-caps c dep bud j g op allNid inst κ id now vals fin sl sched st
    2≤S 1≤R slEq slC slSz inv pS lC vC fb dpt

-- and THIS is where the DEPTH FUEL splits, and the only place it does.
--
-- At `dep = zero` the clause is UNREACHABLE, which is the entire reason
-- the mirror exists.  `depthFrame`'s thru-outer arm is `suc (depthWalk …)`
-- (.Caps-Depth), so the hypothesis here reads `suc _ ≤ zero`.  It has to
-- be unreachable rather than merely hard: `fLvlD S W zero J` is a closed
-- formula making no recursive call — that is what carries the family's
-- termination — and a depth-zero walk STRICTLY overshoots it, so no
-- rearrangement closes this clause and only a hypothesis can retire it
-- (measured by a probe module since DELETED)
stepFrame-caps c zero bud j g id now (thru-outer op nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC fb ()

-- and at `suc dep′` the fuel is spent: `fLvlD S W (suc d) J` unfolds to
-- the payload walk at `d` — a frame is the one arc of the cycle that
-- re-reads the budget, and that re-read is what the fuel pays for.  So the
-- walk is handed `dep` minus one AND the REFRESHED budget `frameBud c j`,
-- which is what `valsCaps→mList` supplies on the nose (the `mList?-widen`
-- that used to slacken it to the inherited `bud` is gone: a bound in the
-- LARGER transformer is no use here).  Its payload count meets
-- `frame-step`'s `suc (widAt S W j)` by `walk-index` on `valsCaps?`'s own
-- length conjunct
stepFrame-caps c (suc dep′) bud j g id now (thru-outer op nid) κ vals fin sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC vC fb dpt =
  j′ , proj₁ WR
     , valsIn (frameStep (j + j′) c) sl (proj₁ (thruWrap op nid fin WK))
         (proj₁ (proj₂ WR))
         (subst (λ x → length x ≤ suc (Caps.cWid (frameStep (j + j′) c)))
                (sym (thruWrap-vals op nid fin WK))
                (valsLen (frameStep (j + j′) c) sl (proj₁ WK)
                   (proj₁ (proj₂ (proj₂ TW)))))
     , proj₂ (proj₂ WR)
     , frame-step (Caps.cSize c) (Caps.cWid c) dep′ j 0 j′ 2≤S z≤n
         (subst (λ x → x + j′
                         ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep′
                             (frameBud c j) (suc (Caps.cWid (frameStep j c))) x)
                (sym (+-identityʳ j))
                (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ TW))))
                   (walk-index (Caps.cSize c) (Caps.cWid c) dep′ (frameBud c j)
                      (length vals) j j 2≤S
                      (valsLen (frameStep j c) sl vals vC))))
  where
  TW = thruWalk-caps c dep′ (sizeAt (Caps.cSize c) (suc j)) j g op nid κ id now vals sl sched st
         2≤S 1≤R slEq slC slSz inv pS vC lC
         (valsCaps→mList-strict c j sl _ vals (≤-trans (s≤s z≤n) 2≤S) slSz
            (valsOf (frameStep j c) sl vals vC))
         (≤-pred dpt)
  j′ = proj₁ TW
  WK = thruWalk g op nid κ id now vals sched st
  WR = thruWrap-caps (frameStep (j + j′) c) op nid fin sl WK
         (proj₁ (proj₂ TW))
         (valsOf (frameStep (j + j′) c) sl (proj₁ WK)
            (proj₁ (proj₂ (proj₂ TW))))
         (proj₁ (proj₂ (proj₂ (proj₂ TW))))

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
-- *All heads supply them by `refl`, since mergeAll-st with an empty
-- queue, switch-st and exhaust-st are all trivially bounded on both
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
  (c : Caps) (dep bud j : ℕ) (g : Gas) (id : Id) (now : Tick)
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
  depthBurst g id now f κ str sched st ≤ dep →
  let r = pushBurst g id now f κ str sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- ONE FRAME PER EMIT, so the index is the emit count — which is why
     -- the third conjunct above has to be in this Σ and not downstream
     × (j + j′ ≤ fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j)
pushBurst-caps {u = u} c dep bud j g id now f κ [] sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC bC cC dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
    , refl , burst-nil (Caps.cSize c) (Caps.cWid c) dep bud j
pushBurst-caps {Γ = Γ} {t = t} {s = s} {u = u} c dep bud j g id now f κ (em ∷ ems) sl sched st
               2≤S 1≤R slEq slC slSz inv fS pS lC bC cC dpt =
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
    , frameStep-+assoc-count c j j₁ j₂
        (((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST)
        COUNT
    -- ONE EMIT: the frame it steps through — `stepFrame-caps` reports the
    -- level that frame LEAVES — then the rest of the burst from there.
    -- `burst-step` is the gate's fIterD row and this is the clause it
    -- exists for; the index descends with the emit list
    , burst-step (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j j₁ j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ SF))))
        (proj₂ (proj₂ (proj₂ (proj₂ IH))))
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
  SF   = stepFrame-caps c dep (frameBud c j) j g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sl sched st
           2≤S 1≤R slEq slC slSz inv fS pS lC
           (splitEvents-valsCaps {u = u} (frameStep j c) sl E eC cntE) ≤-refl
           (≤-trans (m≤m⊔n _ _) dpt)
  j₁   = proj₁ SF
  step = stepFrame g id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  ⊑₁   = frameStep-⊑-+ c 2≤S j j₁
  IH   = pushBurst-caps c dep bud (j + j₁) g id now f κ ems sl sd₁ st₁ 2≤S 1≤R
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
           (burstCount?-widen ems ⊑₁ (burstCount?-tail (frameStep j c) em ems cC))
           (≤-trans (m≤n⊔m _ _) dpt)
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
  -- THE COUNT.  pushBurst is 1:1, so the emit half is the input's own
  -- length widened; and the pushed envelope carries EXACTLY the values
  -- stepFrame emitted (backchannel, retag and terminator are all
  -- value-free), so the per-emit half is the payload ledger's own
  -- length conjunct.  Neither needs a fold: no fold, no witness move
  ⊑ⱼ : frameStep j c ⊑ᶜ frameStep ((j + j₁) + j₂) c
  ⊑ⱼ = frameStep-mono-j c 2≤S (≤-trans (m≤m+n j j₁) (m≤m+n (j + j₁) j₂))
  HEADV : valCountᵉ (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                       ++ map value (proj₁ step)
                       ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ length (proj₁ step)
  HEADV = pushEmit-count {Γ = Γ} {s = s} {u = u} {A = Val Γ t}
            E (proj₁ (proj₂ step)) (proj₁ step) (proj₁ (proj₂ (proj₂ step)))
  HEADB : (valCountᵉ (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                        ++ map value (proj₁ step)
                        ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
             ≤ᵇ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))) ≡ true
  HEADB = subst (λ x → (x ≤ᵇ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))) ≡ true)
                (sym HEADV)
                (≤ᵇ-widen (length (proj₁ step)) (s≤s (proj₁ (proj₂ ⊑₂)))
                   (proj₂ (∧-true
                     (all (valCaps? (frameStep (j + j₁) c) sl u) (proj₁ step))
                     (length (proj₁ step)
                        ≤ᵇ suc (Caps.cWid (frameStep (j + j₁) c)))
                     (proj₁ (proj₂ (proj₂ SF))))))
  LEN : length ((((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                     ++ map value (proj₁ step)
                     ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
                   at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
                  ∷ proj₁ REST))
          ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))
  LEN = subst (λ x → suc x ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c)))
              (sym (pushBurst-len g id now f κ ems sd₁ st₁))
              (≤-trans (countLen (frameStep j c) (em ∷ ems) cC)
                       (s≤s (proj₁ (proj₂ ⊑ⱼ))))
  COUNT : burstCount? (frameStep ((j + j₁) + j₂) c)
            ((((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                  ++ map value (proj₁ step)
                  ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
                at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
               ∷ proj₁ REST))
            ≡ true
  COUNT = countIn (frameStep ((j + j₁) + j₂) c)
            ((((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                  ++ map value (proj₁ step)
                  ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
                at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
               ∷ proj₁ REST))
            LEN
            (∧-intro HEADB
               (countVals (frameStep ((j + j₁) + j₂) c) (proj₁ REST)
                  (proj₁ (proj₂ (proj₂ (proj₂ IH))))))

-- THE *All HEAD.  One j for the thru-outer frame the chain gains, then
-- the burst is pushed back through that same frame
subscribeAll-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (dep bud ops j : ℕ) (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  boundedNode (Caps.cSize (frameStep (suc j) c)) ns ≡ true →
  parkRoom (Caps.cSize (frameStep (suc j) c)) (slotsSize sl) ns ≡ true →
  widNode (Caps.cWid (frameStep (suc j) c)) sl ns ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  dWᵉ n sl b ≤ Caps.cWid (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  -- THE INDEX HYPOTHESIS, and it is stated about the *All TERM rather
  -- than about its source: this head is where the operator's `op-step`
  -- actually sits, and its four callers delegate their whole body to it,
  -- so it inherits their index and their hypothesis verbatim.  Every
  -- *All constructor's size is `suc (sizeᵉ b)` (Rx.Exp), which is
  -- why the caller's `suc (sizeᵉ (mergeAllᵉ lim b)) ≤ ops` reads as this
  suc (suc (sizeᵉ b)) ≤ ops →
  depthAll g op ns b κ id now sched st ≤ dep →
  let r = subscribeAll g op ns b κ id now sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     -- it IS an operator, so it reports in subscribeE's shape at the
     -- index it inherits from its four callers
     × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
-- and THIS is where the index splits.  `op-step` concludes at `suc m`,
-- so the head that spends it needs its own index to be a successor; at
-- zero the hypothesis is `suc (suc (sizeᵉ b)) ≤ zero`, uninhabited by
-- constructor, so the clause is absurd and costs one line
subscribeAll-caps {Γ = Γ} {t = t} {u = u} c dep bud zero j g op ns b κ id now sl sched st
                  2≤S 1≤R slEq slC slSz inv bn pk wn szb wdb pC lC nst () dpt
subscribeAll-caps {Γ = Γ} {t = t} {u = u} c dep bud (suc ops′) j g op ns b κ id now sl sched st
                  2≤S 1≤R slEq slC slSz inv bn pk wn szb wdb pC lC nst hidx dpt =
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
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-count c (suc j) j₁ j₂ (proj₁ PB)
               (proj₁ (proj₂ (proj₂ (proj₂ PBc)))))
    -- ONE OPERATOR, and the *All edge spends it exactly as a chain edge
    -- does: the source's conjunct verbatim at the predecessor index the
    -- split bought, and pushBurst's converted once by `burst-index`
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
                    (countLen (frameStep (suc j + j₁) c) (proj₁ res)
                       (proj₁ (proj₂ (proj₂ (proj₂ SUB)))))))
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
           (subst (λ y → parkRoom (Caps.cSize (frameStep (suc j) c))
                           (slotsSize y) ns ≡ true)
                  (sym slEq) pk)
           (subst (λ y → widNode (Caps.cWid (frameStep (suc j) c)) y ns ≡ true)
                  (sym slEq) wn)
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  -- the source takes the PREDECESSOR, and `chain-desc` at `hd := 0` is
  -- its hypothesis: a *All constructor is headless, so the clause's
  -- `suc (suc (sizeᵉ b)) ≤ suc ops′` gives `suc (sizeᵉ b) ≤ ops′` outright
  SUB = subscribeE-caps c dep bud ops′ (suc j) g b κ′ id now sl sched₀ st₀ 2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC) nst
          (chain-desc 0 (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
  j₁  = proj₁ SUB
  res = subscribeE g b κ′ id now sched₀ st₀
  PBc = pushBurst-caps c dep bud (suc j + j₁) g id now (thru-outer op nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq (subscribeE-keeps g b κ′ id now sched₀ st₀)) slEq)
          slC slSz (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁)
             (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₁ (proj₂ (proj₂ (proj₂ SUB))))
          (≤-trans (m≤n⊔m _ _) dpt)
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
-- THE SLOT EDGE, and it was never a ruling.  A fresh entry reports the
-- whole level SWEEP rather than an operator index, and `op-step-share`
-- converts exactly that into this clause's `opIterD … ops j` — needing
-- nothing of `ops` but that it be a successor, which `hidx` gives.  The
-- old comment here claimed the sweep "cannot be converted" because a
-- fresh entry's index is the level's whole size cap; that is precisely the
-- obstruction `op-step-entry`'s quadratic room dissolves, and it already
-- dissolves it for the structurally identical μ edge below.
--
-- The witness gains a `suc` because the sweep is spent through the share
-- gate, so the three carried receipts move up one level with it
subscribeE-caps c dep bud zero j g (input i) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps c dep bud (suc ops′) j g (input i) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  suc (proj₁ IN)
    , subst (λ y → capsOK? (frameStep y c)
                     (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
            (sym lvl)
            (capsOK?-mono (frameStep (j + proj₁ IN) c)
                          (frameStep (suc (j + proj₁ IN)) c)
                          (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ⊑₁
                          (proj₁ (proj₂ IN)))
    , subst (λ y → burstCaps? (frameStep y c) sl (proj₁ res) ≡ true)
            (sym lvl)
            (burstCaps?-widen sl (proj₁ res) ⊑₁ (proj₁ (proj₂ (proj₂ IN))))
    , subst (λ y → burstCount? (frameStep y c) (proj₁ res) ≡ true)
            (sym lvl)
            (burstCount?-widen (proj₁ res) ⊑₁ (proj₁ (proj₂ (proj₂ (proj₂ IN)))))
    , op-step-share (Caps.cSize c) (Caps.cWid c) dep bud ops′ j (proj₁ IN) 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ IN))))
  where
  IN  = subscribeE-input-caps c dep bud j g i κ bid now sl sched st 2≤S 1≤R slEq slC slSz inv pC lC nst dpt
  res = subscribeE g (input i) κ bid now sched st
  ⊑₁  = frameStep-mono-j c 2≤S (n≤1+n (j + proj₁ IN))
  lvl : j + suc (proj₁ IN) ≡ suc (j + proj₁ IN)
  lvl = +-suc j (proj₁ IN)

-- LITERALS: one shot, and the payloads come off evalTms-caps.  The
-- state is untouched; only the source counter moves, which capsOK?
-- does not read
-- and it SPLITS the index, like every clause with a positive witness:
-- `op-step-entry` concludes at a successor, and at `ops = zero` the
-- conjunct is false outright, so `hidx` is the absurdity that rules the
-- empty index out
subscribeE-caps {n = n} {u = u} c dep bud zero j g (ofᵉ ts) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} {u = u} c dep bud (suc ops′) j g (ofᵉ ts) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  j₀ + 3 , capsOK?-mono (frameStep j c) (frameStep (j + (j₀ + 3)) c) sched st
             (frameStep-⊑-+ c 2≤S j (j₀ + 3)) inv
         , ∧-intro (∧-intro refl
                      (all-++-intro (eventCaps? (frameStep (j + (j₀ + 3)) c) sl)
                         (map value (map (λ tm → evalTm tm) ts)) _
                         (mapValue-caps (frameStep (j + (j₀ + 3)) c) sl u
                            (map (λ tm → evalTm tm) ts)
                            (valsCaps?-widen sl u (map (λ tm → evalTm tm) ts) ⊑₃
                               (proj₂ EV)))
                         refl))
                   refl
         , COUNT
         -- A LITERAL BURST subscribes nothing, so this is an ENTRY with a
         -- receipt and no tail — not an `op-step` shape at all.  `szb` is
         -- its room premise on the nose, since `sizeᵉ (ofᵉ ts)` IS `j₀`
         , of-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₀ 2≤S szb
  where
  EV = evalTms-caps c j sl ts 2≤S slC (≤-trans (n≤1+n (sizeᵗˢ ts)) szb) wdb
  j₀ = proj₁ EV
  -- THE COUNT, AND THE ONE WITNESS MOVE §1 BUYS.  A literal's burst
  -- carries one value per term, so its count is bounded by the entry
  -- SIZE — and a size only fits under a width THREE folds up (the
  -- `caps 2 0 r` row kills one fold).  So this clause reports j₀ + 3
  -- where it used to report j₀, and every other receipt rides along
  ⊑₃ : frameStep (j + j₀) c ⊑ᶜ frameStep (j + (j₀ + 3)) c
  ⊑₃ = frameStep-mono-j c 2≤S (+-monoʳ-≤ j (m≤m+n j₀ 3))
  ⊑₄ : frameStep (j + 3) c ⊑ᶜ frameStep (j + (j₀ + 3)) c
  ⊑₄ = frameStep-mono-j c 2≤S (+-monoʳ-≤ j (m≤n+m 3 j₀))
  WB : Caps.cSize (frameStep j c) ≤ Caps.cWid (frameStep (j + (j₀ + 3)) c)
  WB = ≤-trans (frameStep-size≤wid c j 2≤S) (proj₁ (proj₂ ⊑₄))
  LENB : length ts ≤ suc (Caps.cWid (frameStep (j + (j₀ + 3)) c))
  LENB = ≤-trans (≤-trans (len≤sizeᵗˢ ts)
                          (≤-trans (≤-trans (n≤1+n (sizeᵗˢ ts)) szb) WB))
                 (n≤1+n (Caps.cWid (frameStep (j + (j₀ + 3)) c)))
  COUNT : burstCount? (frameStep (j + (j₀ + 3)) c)
            (proj₁ (oneShotBurst (map (λ tm → evalTm tm) ts) bid sched)) ≡ true
  COUNT = countIn (frameStep (j + (j₀ + 3)) c)
            (proj₁ (oneShotBurst (map (λ tm → evalTm tm) ts) bid sched))
            (s≤s z≤n)
            (∧-intro
              (subst (λ x →
                        (x ≤ᵇ suc (Caps.cWid (frameStep (j + (j₀ + 3)) c))) ≡ true)
                     (sym (trans (oneShot-count (map (λ tm → evalTm tm) ts)
                                    (Sched.nextSource sched))
                                 (length-map (λ tm → evalTm tm) ts)))
                     (T⇒≡true (length ts
                                 ≤ᵇ suc (Caps.cWid (frameStep (j + (j₀ + 3)) c)))
                              (≤⇒≤ᵇ LENB)))
              refl)

subscribeE-caps {u = u} c dep bud ops j g emptyᵉ κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl
    -- A LEAF: no operator is entered, so the level does not move and the
    -- sweep being inflationary is the whole proof
    , refl , leaf-lvl (Caps.cSize c) (Caps.cWid c) dep bud ops j

-- MAP: one more frame on the chain, so one j, then the burst comes back
-- through that same frame
subscribeE-caps {n = n} {t = t} {u = u} c dep bud zero j g (mapᵉ f b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} {t = t} {u = u} c dep bud (suc ops′) j g (mapᵉ f b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
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
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-count c (suc j) j₁ j₂ (proj₁ PB)
               (proj₁ (proj₂ (proj₂ (proj₂ PBc)))))
    -- ONE OPERATOR.  The source's conjunct is spent VERBATIM — it reported
    -- at the predecessor index, which is what the split bought — and
    -- pushBurst's is at the emit count, converted once by `burst-index` on
    -- the length `burstCount?` already carries.  No arithmetic of its own
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
                    (countLen (frameStep (suc j + j₁) c) (proj₁ res)
                       (proj₁ (proj₂ (proj₂ (proj₂ SUB)))))))
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
  SUB = subscribeE-caps c dep bud ops′ (suc j) g b (map-f f ↠ κ) bid now sl sched st
          2≤S 1≤R slEq slC slSz
          (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st step⊑ inv)
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl f) (dWᵉ n sl b)) (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC) (map-step _ _ sl _ bud nst)
          (chain-desc (sizeᵗ f) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
  j₁  = proj₁ SUB
  res = subscribeE g b (map-f f ↠ κ) bid now sched st
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c dep bud (suc j + j₁) g bid now (map-f f) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (map-f f ↠ κ) bid now sched st)) slEq)
          slC slSz (proj₁ (proj₂ SUB))
          (frameSz?-widen (map-f f) (proj₁ ⊑₁) fS′)
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₁ (proj₂ (proj₂ (proj₂ SUB))))
          (≤-trans (m≤n⊔m _ _) dpt)
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (map-f f) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- TAKE: `take 0` never subscribes its source — a spent one-shot, exactly
-- emptyᵉ.  Otherwise a node is installed (trivially bounded on both
-- axes) and the source runs under one more frame
subscribeE-caps {n = n} {u = u} c dep bud zero j g (takeᵉ cnt b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} {u = u} c dep bud (suc ops′) j g (takeᵉ cnt b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt
  with evalTm cnt | dpt
... | zero | dpt′ =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (proj₁ (oneShotBurst {u = u} [] bid sched)) ≡ true)
            (sym (+-identityʳ j)) refl
    -- `take 0` subscribes nothing: a leaf, however long the source is
    , refl , leaf-lvl (Caps.cSize c) (Caps.cWid c) dep bud (suc ops′) j
... | suc k | dpt′ =
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
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
            (sym (+-suc j (j₁ + j₂)))
            (frameStep-+assoc-count c (suc j) j₁ j₂ (proj₁ PB)
               (proj₁ (proj₂ (proj₂ (proj₂ PBc)))))
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S
        (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
                    (countLen (frameStep (suc j + j₁) c) (proj₁ res)
                       (proj₁ (proj₂ (proj₂ (proj₂ SUB)))))))
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
           refl refl refl
           (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  SUB = subscribeE-caps c dep bud ops′ (suc j) g b (take-f nid ↠ κ) bid now sl sched₀ st₀
          2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb′ (proj₁ step⊑))
          (≤-trans (m≤n⊔m (dWᵗ n sl cnt) (dWᵉ n sl b))
                   (≤-trans wdb (proj₁ (proj₂ step⊑))))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC) (take-step _ _ sl _ bud nst)
          (chain-desc (sizeᵗ cnt) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt′)
  j₁  = proj₁ SUB
  res = subscribeE g b (take-f nid ↠ κ) bid now sched₀ st₀
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc j) j₁
  PBc = pushBurst-caps c dep bud (suc j + j₁) g bid now (take-f nid) κ (proj₁ res)
          sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) 2≤S 1≤R
          (trans (KeepsC.slotsEq
                   (subscribeE-keeps g b (take-f nid ↠ κ) bid now sched₀ st₀)) slEq)
          slC slSz (proj₁ (proj₂ SUB)) refl
          (pathSz?-⊑ κ ⊑₁ (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑)) (proj₁ ⊑₁))
          (proj₁ (proj₂ (proj₂ SUB)))
          (proj₁ (proj₂ (proj₂ (proj₂ SUB))))
          (≤-trans (m≤n⊔m _ _) dpt′)
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (take-f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- SCAN: the accumulator is BUILT, by evalTm, so the node's two bounds
-- come off evalSeed-caps and cost a receipt of their own before the
-- source is even subscribed
subscribeE-caps {n = n} {u = u} c dep bud zero j g (scanᵉ f z b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} {u = u} c dep bud (suc ops′) j g (scanᵉ f z b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
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
    , frameStep-+assoc-count c j j₀ (suc (j₁ + j₂)) (proj₁ PB)
        (subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true)
               (sym (+-suc (j + j₀) (j₁ + j₂)))
               (frameStep-+assoc-count c (suc (j + j₀)) j₁ j₂ (proj₁ PB)
                  (proj₁ (proj₂ (proj₂ (proj₂ PBc))))))
    -- SCAN is the eval-receipt shape: the seed's own receipt first, then
    -- the source and its burst exactly as `mapᵉ` spends them
    , op-step-eval (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₀ j₁ j₂ 2≤S
        (s≤s szz)
        (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ PBc))))
                 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
                    (length (proj₁ res)) (suc (j + j₀) + j₁) (suc (j + j₀) + j₁) 2≤S
                    (countLen (frameStep (suc (j + j₀) + j₁) c) (proj₁ res)
                       (proj₁ (proj₂ (proj₂ (proj₂ SUB)))))))
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
           refl
           (subst (λ y → widNode (Caps.cWid (frameStep (suc (j + j₀)) c)) y
                           (scan-st (evalTm z)) ≡ true)
                  (sym slEq)
                  (valCaps?-wid (frameStep (suc (j + j₀)) c) sl _ (evalTm z) VW))
           (capsOK?-mono (frameStep j c) (frameStep (suc (j + j₀)) c) sched₀ st
              (⊑ᶜ-trans ⊑₀ step⊑)
              (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                                sched st inv))
  SUB = subscribeE-caps c dep bud ops′ (suc (j + j₀)) g b (scan-f f nid ↠ κ) bid now sl
          sched₀ st₀ 2≤S 1≤R slEq slC slSz inv₀
          (≤-trans szb′ (≤-trans (proj₁ ⊑₀) (proj₁ step⊑)))
          (≤-trans (m≤n⊔m (dWᵗ n sl f ⊔ dWᵗ n sl z) (dWᵉ n sl b))
             (≤-trans wdb (≤-trans (proj₁ (proj₂ ⊑₀)) (proj₁ (proj₂ step⊑)))))
          pC′
          (frameStep-chain-suc c (j + j₀) (pathLen κ) 2≤S
             (≤-trans lC (proj₁ ⊑₀))) (scan-step f z b sl _ bud nst)
          (chain-desc (sizeᵗ f + sizeᵗ z) (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
  j₁  = proj₁ SUB
  res = subscribeE g b (scan-f f nid ↠ κ) bid now sched₀ st₀
  ⊑₁  = frameStep-⊑-+ c 2≤S (suc (j + j₀)) j₁
  PBc = pushBurst-caps c dep bud (suc (j + j₀) + j₁) g bid now (scan-f f nid) κ
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
          (proj₁ (proj₂ (proj₂ (proj₂ SUB))))
          (≤-trans (m≤n⊔m _ _) dpt)
  j₂  = proj₁ PBc
  PB  = pushBurst g bid now (scan-f f nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))

-- THE FOUR *All HEADS: subscribeAll-caps, whole.  Every initial node
-- state is bounded on both axes by refl
-- none of the four splits its index.  Each delegates its WHOLE body to
-- subscribeAll-caps, so the two share a conclusion and must therefore
-- share an index — the `op-step` that consumes the source and the pushed
-- frames sits INSIDE the delegate, and so does the split.  The
-- hypothesis passes through untouched: `sizeᵉ (mergeAllᵉ lim b)` is
-- `suc (sizeᵉ b)`, which is what the delegate asks for
subscribeE-caps {n = n} {u = u} c dep bud ops j g (mergeAllᵉ lim b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  subscribeAll-caps c dep bud ops j g mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b κ bid now
    sl sched st 2≤S 1≤R slEq slC slSz inv refl refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC (mergeAll-step lim _ sl _ bud nst) hidx dpt
subscribeE-caps {n = n} c dep bud ops j g (switchAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  subscribeAll-caps c dep bud ops j g switchᵒ (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (switch-step _ sl _ bud nst) hidx dpt
subscribeE-caps {n = n} c dep bud ops j g (exhaustAllᵉ b) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  subscribeAll-caps c dep bud ops j g exhaustᵒ (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R slEq slC slSz inv refl refl refl (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (exhaust-step _ sl _ bud nst) hidx dpt

-- μ: out of gas is a dry close; with gas, ONE unfolding — larger than
-- the μ on the size axis (unfoldμ-size buys the room) and no larger on
-- the width axis (dW-unfoldμ)
subscribeE-caps {u = u} c dep bud ops j g0 (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (dryBurst {A = Val _ u} bid) ≡ true)
            (sym (+-identityʳ j)) refl
    , refl , leaf-lvl (Caps.cSize c) (Caps.cWid c) dep bud ops j
-- and THIS is where the BUDGET splits, which the level conjunct is what
-- forces.  `op-step-mu` consumes the unfolding at `sLvlD S W dep bud …`
-- while the unfolding's own subscribe reports at
-- `opIterD S W dep bud′ (suc (sizeAt S …)) …`, and `sLvlD-suc` identifies
-- the two only when `bud ≡ suc bud′`: a μ unfolding SPENDS a nesting
-- level.  `mu-step` is that spend (syncSizeᵉ drops by one across the μ
-- edge).  Both zero clauses are
-- absurd by CONSTRUCTOR: at `ops = 0` the index hypothesis reads
-- `suc (sizeᵉ (μᵉ body)) ≤ 0`, and at `bud = 0` the nesting hypothesis
-- reads `nest (μᵉ body) sl cs ≤ 0` with a μ's nest a successor
subscribeE-caps {n = n} c dep bud zero j (gs fuel) (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} c dep zero (suc ops′) j (gs fuel) (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC () hidx dpt
subscribeE-caps {n = n} c dep (suc bud′) (suc ops′) j (gs fuel) (μᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  j₀ + j₁
    , frameStep-+assoc-caps c j j₀ j₁ (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₀ j₁ sl (proj₁ res)
        (proj₁ (proj₂ (proj₂ IH)))
    , frameStep-+assoc-count c j j₀ j₁ (proj₁ res)
        (proj₁ (proj₂ (proj₂ (proj₂ IH))))
    , op-step-mu (Caps.cSize c) (Caps.cWid c) dep (suc bud′) ops′ j
        (sizeᵉ (μᵉ body)) j₁ 2≤S szb
        (≤-trans (proj₂ (proj₂ (proj₂ (proj₂ IH))))
                 (≤-reflexive (sym (sLvlD-suc (Caps.cSize c) (Caps.cWid c)
                                     dep bud′ (j + j₀)))))
  where
  US = unfoldμ-caps c j sl body 2≤S slC szb wdb
  j₀ = proj₁ US
  ⊑₀ = frameStep-⊑-+ c 2≤S j j₀
  -- the unfolding is a FRESH ENTRY, not a chain edge: it subscribes a
  -- LARGER term, which is why `op-step-mu` consumes it at `sLvlD` rather
  -- than at `opIterD`, and why the index is MINTED at the new level's
  -- size cap instead of descending from `ops`.  So the supply is one
  -- `s≤s` on the size hypothesis the unfolding receipt already gives
  IH = subscribeE-caps c dep bud′ (suc (Caps.cSize (frameStep (j + j₀) c)))
         (j + j₀) fuel (unfoldμ body) κ bid now sl sched st
         2≤S 1≤R slEq slC slSz
         (capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st ⊑₀ inv)
         (proj₁ (proj₂ US))
         (proj₂ (proj₂ US))
         (pathSz?-⊑ κ ⊑₀ pC)
         (≤-trans lC (proj₁ ⊑₀)) (mu-step body sl _ bud′ nst)
         (s≤s (proj₁ (proj₂ US)))
         dpt
  j₁ = proj₁ IH
  res = subscribeE fuel (unfoldμ body) κ bid now sched st

subscribeE-caps c dep bud ops j g (varᵉ ()) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt

-- DEFER: the clause the parked width exists for.  Install the mergeAll
-- node, mint the source and ordinal, PARK the body as a one-element
-- pending, and register the thru-outer chain — one j, for the
-- registration.  The LiveSource's width bound IS the telescope's dW
-- conjunct: `dWᵉ (deferᵉ body)` is `pWᵉ body`, definitionally
subscribeE-caps {n = n} {Γ = Γ} {u = u} c dep bud zero j g (deferᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst () dpt
subscribeE-caps {n = n} {Γ = Γ} {u = u} c dep bud (suc ops′) j g (deferᵉ body) κ bid now sl sched st
                2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt =
  1 , subst (λ x → capsOK? (frameStep x c) SCHED₄
                     (register SRC (thru-outer mergeAllᵒ nid ↠ κ) st₀) ≡ true)
            (sym (j+1 j))
            (capsOK?-addLive (frameStep (suc j) c) NEW SCHED₃
               (register SRC (thru-outer mergeAllᵒ nid ↠ κ) st₀) BL WL CL REG)
    , subst (λ x → burstCaps? {u = u} (frameStep x c) sl
                     (((init SRC ∷ []) at bid from SRC as subscribe) ∷ []) ≡ true)
            (sym (j+1 j)) refl
    -- THE PARKED BODY is an entry whose receipt is the registration, and
    -- `share-fits` already pays its room — one registration sits inside
    -- the quadratic excursion at every cap
    , refl , defer-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j 2≤S
  where
  nid    = Sched.nextNode sched
  SRC    = Sched.nextSource sched
  st₀    = installNode nid (mergeAll-st {t = u} nothing 0 [] false) st
  SCHED₃ = record (record (record sched { nextNode = suc (Sched.nextNode sched) })
                          { nextSource = suc (Sched.nextSource sched) })
                  { nextOrdinal = suc (Sched.nextOrdinal sched) }
  NEW    = record { source = SRC ; ordinal = Sched.nextOrdinal sched
                  ; elemTy = obs u ; pending = (suc now , body) ∷ [] }
  SCHED₄ = record SCHED₃ { live = NEW ∷ Sched.live SCHED₃ }
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B      = Caps.cSize (frameStep j c)
  pC′ : pathSz? B (thru-outer mergeAllᵒ nid ↠ κ) ≡ true
  pC′ = ∧-intro refl
          (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B) (≤⇒≤ᵇ lC)) pC)
  inv₀ : capsOK? (frameStep j c) SCHED₃ st₀ ≡ true
  inv₀ = capsOK?-setNode (frameStep j c) nid (mergeAll-st {t = u} nothing 0 [] false) SCHED₃ st
           refl refl refl inv
  REG : capsOK? (frameStep (suc j) c) SCHED₃
          (register SRC (thru-outer mergeAllᵒ nid ↠ κ) st₀) ≡ true
  REG = register-caps c j SRC (thru-outer mergeAllᵒ nid ↠ κ) SCHED₃ st₀
          2≤S 1≤R inv₀ pC′
  BL : boundedLive (Caps.cSize (frameStep (suc j) c)) NEW ≡ true
  BL = ∧-intro (T⇒≡true (sizeᵉ body ≤ᵇ Caps.cSize (frameStep (suc j) c))
                 (≤⇒≤ᵇ (≤-trans (≤-trans (n≤1+n (sizeᵉ body)) szb) (proj₁ step⊑))))
               refl
  CL : closLive (frameStep (suc j) c) (Sched.slots SCHED₃) NEW ≡ true
  CL = ∧-intro (subst (λ y → nestClosOK? (frameStep (suc j) c) y body ≡ true)
                      (sym slEq)
                      (defer-park-clos c j sl body 2≤S slC
                         (≤-trans (n≤1+n (sizeᵉ body)) szb)))
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
  (c : Caps) (dep bud j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick)
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
  depthFold sf gas id now envSrc path vals evs fin sched st ≤ dep →
  let r = foldPath sf gas id now envSrc path vals evs fin sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

dispatchShare-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (dep bud j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  depthDisp sf gas id now i vals fin sched st ≤ dep →
  let r = dispatchShare {t = t} sf gas id now i vals fin sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

shareGo-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (dep bud j : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
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
  depthShareGo sf gas id now i vals fin ps sched st ≤ dep →
  let r = shareGo sf gas id now i vals fin ps sched st
  in Σ ℕ λ j′ → (capsOK? (frameStep (j + j′) c)
                          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)

-- ROOT: the chain's sink.  Nothing steps, so j′ = 0 and the only work
-- is assembling one emit out of bounds already in hand
foldPath-caps c dep bud j sf gas id now envSrc root vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC dpt =
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
foldPath-caps c dep bud j sf gas id now envSrc (share-sink i) vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC dpt =
  j₁ , proj₁ (proj₂ DS)
     , ∧-intro (all-++-intro (eventCaps? (frameStep (j + j₁) c) sl) evs _
                  (eventsCaps?-widen sl evs (frameStep-⊑-+ c 2≤S j j₁) eC)
                  refl)
               (proj₂ (proj₂ DS))
  where
  DS = dispatchShare-caps c dep bud j sf gas id now i vals fin sl sched st
         2≤S 1≤R slEq slC slSz inv vC dpt
  j₁ = proj₁ DS

-- ONE FRAME, THEN THE REST OF THE CHAIN.  j₁ pays the frame, j₂ the
-- tail, and the clause reports j₁ + j₂ — the additive composition,
-- rebracketed by +-assoc and nothing else
foldPath-caps c dep bud j sf gas id now envSrc (f ↠ p) vals evs fin sl sched st
              2≤S 1≤R slEq slC slSz inv pS vC eC dpt =
  j₁ + j₂
    , frameStep-+assoc-caps c j j₁ j₂ (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST))
        (proj₁ (proj₂ IH))
    , frameStep-+assoc-burst c j j₁ j₂ sl (proj₁ REST) (proj₂ (proj₂ IH))
  where
  B    = Caps.cSize (frameStep j c)
  pS1  = ∧-true (frameSz? B f) ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) pS
  pS2  = ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) (proj₂ pS1)
  SF   = stepFrame-caps c dep (frameBud c j) j sf id now f p vals fin sl sched st
           2≤S 1≤R slEq slC slSz inv (proj₁ pS1) (proj₂ pS2)
           (≤ᵇ⇒≤ _ _ (T-to (proj₁ pS2))) vC ≤-refl (≤-trans (m≤m⊔n _ _) dpt)
  j₁   = proj₁ SF
  step = stepFrame sf id now f p vals fin sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  IH   = foldPath-caps c dep bud (j + j₁) sf gas id now envSrc p
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
              (proj₁ (proj₂ (proj₂ (proj₂ SF)))))
           (≤-trans (m≤n⊔m _ _) dpt)
  j₂   = proj₁ IH
  REST = foldPath sf gas id now envSrc p (proj₁ step) (evs ++ proj₁ (proj₂ step))
           (proj₁ (proj₂ (proj₂ step))) sd₁ st₁

-- DISPATCH: latch first (a completing def closes before it delivers),
-- fan out, then finish.  The dispatch gas is the telescope bound and
-- never runs out on a real run, so the zero clause is the evaluator's
-- own unreachable branch
dispatchShare-caps {t = t} c dep bud j sf zero id now i vals fin sl sched st
                   2≤S 1≤R slEq slC slSz inv vC dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
dispatchShare-caps c dep bud j sf (suc gas) id now i vals fin sl sched st 2≤S 1≤R slEq slC slSz inv vC dpt =
  j₁ , proj₁ FIN , proj₂ FIN
  where
  st₀ = shareLatch i fin st
  GO  = shareGo-caps c dep bud j sf gas id now i vals fin
          (shareAdmit i (EvalSt.registry st)) sl sched st₀
          2≤S 1≤R slEq slC slSz (shareLatch-caps (frameStep j c) i fin sched st inv)
          (shareAdmit-caps (Caps.cSize (frameStep j c)) i (EvalSt.registry st)
             (capsOK?-regs (frameStep j c) sched st inv))
          vC dpt
  j₁  = proj₁ GO
  out = shareGo sf gas id now i vals fin (shareAdmit i (EvalSt.registry st))
          sched st₀
  FIN = shareFinish-caps (frameStep (j + j₁) c) i fin sl out
          (proj₁ (proj₂ GO)) (proj₂ (proj₂ GO))

-- FAN-OUT: one registration at a time.  A cancelled chain delivers
-- nothing and costs nothing; a survivor folds, and the two receipts add
shareGo-caps {t = t} c dep bud j sf gas id now i vals fin [] sl sched st
             2≤S 1≤R slEq slC slSz inv pS vC dpt =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , subst (λ x → burstCaps? {u = t} (frameStep x c) sl [] ≡ true)
            (sym (+-identityʳ j)) refl
shareGo-caps {Γ = Γ} c dep bud j sf gas id now i vals fin ((rid , p) ∷ ps) sl sched st
             2≤S 1≤R slEq slC slSz inv pS vC dpt
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareGo-caps c dep bud j sf gas id now i vals fin ps sl sched st
                2≤S 1≤R slEq slC slSz inv (proj₂ (∧-true _ _ pS)) vC
                (≤-trans (m≤m⊔n _ _) dpt)
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
  -- hoisted above the depth bounds, which read it: an unsignatured
  -- `where` definition has to precede its uses
  FP  = foldPath sf gas id now (toℕ i) p vals cl fin sched st₀
  -- `depthShareGo`'s cons clause is the mirror's only THREE-callee clause,
  -- `dA ⊔ (dB ⊔ dC)`, and each of the two recursive consumers below needs
  -- one summand.  The bounds are bound HERE by name because `lub3-*`
  -- cannot infer them — `_⊔_` is a defined function, so there is nothing
  -- to invert.  These three transcribe that clause verbatim (its `st₁` is
  -- our `st₀`, its `closes` our `cl`, its `r` our `FP`)
  dA  = depthShareGo sf gas id now i vals fin ps sched st
  dB  = depthFold sf gas id now (toℕ i) p vals cl fin sched st₀
  dC  = depthShareGo sf gas id now i vals fin ps
          (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
  HD  = foldPath-caps c dep bud j sf gas id now (toℕ i) p vals cl fin sl sched st₀
          2≤S 1≤R slEq slC slSz (capsOK?-delivered (frameStep j c) rid sched st inv)
          (proj₁ (∧-true _ _ pS)) vC
          (closeList-caps (frameStep j c) sl (toℕ i) fin)
          (lub3-m dA dB dC dpt)
  j₁  = proj₁ HD
  IH  = shareGo-caps c dep bud (j + j₁) sf gas id now i vals fin ps sl
          (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))
          2≤S 1≤R
          (trans (foldPath-slots sf gas id now (toℕ i) p vals cl fin sched st₀)
                 slEq)
          slC slSz
          (proj₁ (proj₂ HD))
          (pathsSz?-⊑ ps (frameStep-⊑-+ c 2≤S j j₁) (proj₂ (∧-true _ _ pS)))
          (valsCaps?-lvl (frameStep j c) (frameStep (j + j₁) c) sl vals
             (frameStep-⊑-+ c 2≤S j j₁) vC)
          (lub3-r dA dB dC dpt)
  j₂  = proj₁ IH
  REST = shareGo sf gas id now i vals fin ps (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP))

