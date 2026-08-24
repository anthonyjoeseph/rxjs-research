-- THE COLLAPSED WALK — the E-into-j restatement, executing
-- the ruling in Wet/Part6's GAP 4 header ("THE NESTING BUDGET IS THE
-- GAS").  The wet walk's running position is a caps LEVEL j — frameStep
-- iterated on the entry caps — and the capᴱ W E ledger is RETIRED from
-- the walk face entirely.  This is the only surviving route: the ledger
-- composition is machine-refuted at both ends (`wet-ceiling-absurd`
-- way-out, `wet-ell-absurd` way-in, Wet/Part6), and the two refutations
-- dissolve together under this collapse.

-- WHY ITS OWN MODULE.  The wet stratum (.Wet) and the caps face
-- (.Subscribe-Face) are deliberate siblings — neither imports the other
-- — and this statement is the one artifact that reads BOTH vocabularies
-- (INV?/dBound/hasAtLeast from the wet side, capsOK?/frameStep/opIterD
-- from the caps side).  It sits where .Caps-Bridge sits, one arrow
-- above each; .Caps-Bridge consumes it.

-- THE STATEMENT IS subscribeE-caps ⊗ THE WET CONTENT, ONE Σ.  The caps
-- half (hypotheses and the first four conclusion conjuncts) is
-- `subscribeE-caps`'s own face VERBATIM (.Subscribe-Face, GROUND) —
-- same prelims, same level index, same charge `j + j′ ≤ opIterD S W dep
-- bud ops j`.  That is deliberate: the level-threading pattern is
-- PROVEN through the whole mutual block there, so the grind adds wet
-- conjuncts to a skeleton that already walks, instead of inventing a
-- second walk.  The two halves must share ONE witness j′ — two separate
-- Σs could not be joined — which is why the caps conjuncts are
-- restated here rather than consumed as a black box.

-- THE RULING'S "VERIFY FIRST" ITEM, EXECUTED (census, all
-- consumers of the old walk's conclusion traced): the old mintCount /
-- burstLen conjuncts do NOT reappear in wet flavour.  Their jobs are
-- the level machinery's own conjuncts, already carried here — registry
-- growth is capsOK?'s fifth conjunct (`length registry ≤ cReg
-- (frameStep J c)`), burst size is burstCount? at the same level — and
-- the census verdict is that NO consumer needs them at a caps level or
-- in mint flavour (they fed only the old walk's own induction; the
-- outer lenOK is sourced from caps-tick via capsOK?-count +
-- B2-cReg≤cSize, not from the walk).  The Ω width trio (widthOK? /
-- ofWᵉ ≤ Ω / pathΩ?) went WITH the ledger: Ω fed only walkCap's base,
-- and the caps side carries width as dWᵉ ≤ cWid.  Its proofs are gone
-- (.Measures carries the record); `ofWᵉ` itself stays, and this module
-- is what spends it.

-- WHAT SURVIVES UNCHANGED: the dry half.  The demand `dBound Ŝ R̂ U
-- (hopDᵉ F b) (syncSizeᵉ b) ≤ G` at the ENTRY-COMPUTABLE reset caps,
-- the gas `g hasAtLeast suc G`, and the length ledger `pathLen κ + G ≤
-- ℓ` / regsLen? — with ℓ now FREE, decoupled from Ŝ exactly as the
-- ruling says (`wet-ell-absurd` killed the ℓ := Ŝ pin, not the
-- ledger; the outer instantiation floats ℓ to pathLen κ + G ⊔ the
-- registry bound).

-- THE LANDING.  The outer face needs INV? at Ŝ = sizeCapAt e sl
-- (suc id).  The walk lands INV? at cSize (frameStep (j + j′) c); the
-- charge conjunct bounds j + j′ by opIterD, and the lift to Ŝ is the
-- SAME chain `sub-charge-capsOK-lift` already walks one stratum up
-- (.Caps-Bridge): opIterD-dominated → sizeCount-body → sizeCount-mono-d
-- over depOK → capsAt-suc-full → frameStep-mono-j, plus INV?'s upward
-- monotonicity in B (a lemma the core's grind owes; INV? weakens
-- upward conjunct by conjunct).

-- RECOVERY: git show eb11caf:agda/src/Verify-Budget-Sufficient/Measures.agda
--   restores the old ledger walk (subscribeE-walk, subscribeE-walk-core,
--   its 20 sub-postulates and the round-3 DAG) — deleted the day this
--   landed, because its composition with the core was refuted for every
--   parameter choice, not because its clauses were wrong.

-- THE VOCABULARY AND THE SHELF ARE TWO MODULES BELOW THIS ONE, and the
-- reason is the mutual block that remains: a block is an indivisible
-- checking unit, so anything left beside it is re-checked on every
-- focused check of any member.  The statement telescopes prove nothing
-- and the shelf lemmas are not in the cycle, so both are pure cost
-- here and free one arrow down.  What stays is the dispatch itself, the
-- statements only IT reads, and the outer assemblies that spend it.
-- Both live one arrow down now, and consumers name what they need from
-- there directly, so the split shows up in their import lists.

module Verify-Budget-Sufficient.Walk-Level where

open import Data.Bool    using (Bool; true; false; _∨_; not; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _*_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-reflexive; ≤-pred; m≤m+n; m≤n+m; n≤1+n; +-suc; +-assoc; +-comm; +-mono-≤;
  +-monoʳ-≤; *-mono-≤; +-identityʳ; m≤m⊔n; m≤n⊔m; ≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Source; value; complete; InstEmit; _at_from_as_; Gas; g0; gs)
open import Rx.Exp       using (obs; Ctx; Closed; Val; Exp; _≟ᵗ_; sizeᵉ; sizeᵛ; syncSizeᵉ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ;
  scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; unfoldμ)
open import Rx.Frame-Width using (dWᵉ; pWᵉ; pWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵛ; hopD-unfoldμ)
open import Rx.Slot-Hop  using (slotHop)
open import Rx.Evaluator using (Sched; EvalSt; RegId; Chain; Path; _↠_; Stream; subscribeE; subscribeAll; AllOp; mergeAllᵒ;
  switchᵒ; exhaustᵒ; NodeState; mergeAll-st; switch-st; exhaust-st; scan-st; hasRoom;
  take-st; splitBurst; hasDry; dryEvent; opIterD; fIterD; fLvlD; sLvlD; sIterD; sizeAt;
  sLvlD-suc; sIterD-suc; fLvlD-suc; widAt; thru-outer; from-inner; pushBurst; stepFrame;
  subscribeInner; splitEvents; retagEvents; thruConsume; thruWalk; thruWrap; switchKill;
  lookupNode; setNode; installNode; NodeId)
open import Rx.Slots using (Slots; slotsSize)

-- the wet stratum: INV?, dBound, hasAtLeast, regsLen?, pathLen, the gas
-- edges, sizeCapAt, capsAt/capsH/frameStep/Caps (via .Caps), the
-- Keeps ring, and every companion the core is narrowed over
open import Verify-Budget-Sufficient.Measures using
  (_hasAtLeast_; all-++-intro; all-impl;
                                                      applyFn-size; boundedLive; boundedNode;
                                                      budget-covers; burstB?; burstB?-widen;
                                                      burstHopD?; connect-anchor; dBound;
                                                      eventB?; fnCap-unfoldμ; fnCapLive;
                                                      fnCapNode; fnCapᵉ; fnCapᵛ;
                                                      hasAtLeast-mono; hasAtLeast-pad;
                                                      hasAtLeast-peel; hopD-map-emit;
                                                      hopDev?; hopR; inner-unfoldμ;
                                                      INV-parts; INV?; mapValue-B;
                                                      oneShot-tail-dry; pathB?; pathB?-widen;
                                                      pathLen; regsLen?; seed-covers;
                                                      shellSize-unfoldμ; splitEvents-bk-B;
                                                      splitEvents-vals-B; syncSize≤sizeᵉ;
                                                      unconn; unconn-cons-≤; valB?;
                                                      valsB?-widen; ΨAt; ∧-true; ∨-false;
                                                      szB)
open import Verify-Budget-Sufficient.Wet.Part6 using
  (connect-edge; hop-edge; hop-step-gives; hop-step-needs; mu-edge; sizeCapAt;
   unconn-keeps)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; obs-slot-shared; share-live-novals; share-spent-novals;
   sharedConnect-unconn; stepFrame-keeps; subscribeE-keeps; subscribeE-slots;
   switchKill-keeps; thruConsume-keeps)
open import Verify-Budget-Sufficient.Wet.Part1 using
  (INV?-widen; lookupNode-B; mergeAllBump-INV; splitBurst-vals-B)
open import Verify-Budget-Sufficient.Wet.Part2 using
  (finList-B)
-- the caps face: only the five predicates the statement reads there
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstCaps?; burstCount?; capsOK?; capsOK?-mono; eventCaps?; pathSz?; slotsCaps?; valCaps?;
  valCountᵉ; widNode; widNode-push)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-mergeAllBump; capsOK?-nextNode; capsOK?-nodeSz; capsOK?-nodeWid; capsOK?-regs;
  capsOK?-setNode; frameBud; lookupNode-caps; mList?; mList?-head; mList?-keeps; mList?-tail;
  pathSz?-len; slotsCaps?-capsAt; splitBurst-bk-caps; splitBurst-vals-caps;
  splitEvents-bk-caps; splitEvents-valsCaps; switchKill-caps; switchKill-closes-caps;
  thruWrap-caps; valsCaps?; valsCaps→mList-strict)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (burstCaps?-widen; eventsCaps?-widen; finList-caps; frameStep-chain-suc;
   frameStep-size-strict-suc; frameStep-⊑-+; mapValue-caps; pathSz?-⊑;
   valCaps?-size; valCaps?-wid; valsCaps?-widen)
-- the chain-charge algebra subscribeE-caps' own *All head spends
open import Verify-Budget-Sufficient.Caps-Chain
  using (chain-desc; op-step; burst-index; burst-nil; burst-step;
         op-step-mu; quad-arith;
         op-desc; push-desc; frame-desc; tail-desc;
         walk-desc; inner-desc;
         inner-nil; inner-step; walk-nil;
         frame-step; walk-index; queue-push)
open import Verify-Budget-Sufficient.Caps-Sadd
  using (walk-step-suc)
-- the transformer monotonicity/inflation family, cited directly by the
-- loop faces' ceiling conversions
open import Verify-Budget-Sufficient.Caps
  using (opIterD-mono; sIterD-mono; sLvlD-infl; B2-cReg≤cSize; capsAt-base-size; 1≤capsAt-reg;
  2≤capsAt-size; _⊑ᶜ_; Caps; capsAt; capsAt-suc-full; capsH; frameStep; frameStep-0;
  frameStep-mono-j; sizeCount; sizeCount-body)
-- proven projections and per-emit plumbing off the caps push face —
-- pieces, never the face itself (the wet twin re-walks its skeleton
-- so both halves share one witness)
open import Verify-Budget-Sufficient.Subscribe-Face
  using (subscribeE-caps; countLen; countVals; countIn; pushEmit-count;
         pushBurst-len; retagEvents-caps;
         burstCount?-widen; burstCount?-tail;
         splitBurst-len; mul-fits)
open import Verify-Budget-Sufficient.Caps-Face.Part7 using
  (unfoldμ-caps)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (concat-fits; frameStep-+suc; lenWiden; thruWrap-vals; valsIn; valsLen;
   valsOf)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthE; depthAll; depthBurst; depthFrame; depthInner; depthConsume; depthWalk)
open import Verify-Budget-Sufficient.Caps-Nest
  using (nest-keeps; mu-step; exhaust-step; mergeAll-step; nest;
         switch-step)
open import Verify-Budget-Sufficient.Op-Budget
  using (opIterD-dominated)
open import Verify-Budget-Sufficient.Walk-Level.Arms using
  (input-wet-core; walk-defer)
open import Verify-Budget-Sufficient.Walk-Level.Parts using
  (any-++-false; burstHopD?-widen; dBound-mono-r; dBound-mono-U; finList-dry;
   finList-hop; hasAtLeast-peel-gs; INV?-install; INV?-setNode;
   INV?-switchKill; mapValue-dry; mapValue-hop; retagEvents-B; retagEvents-dry;
   retagEvents-hop; splitBurst-nodry; splitBurst-vals-hop; splitEvents-bk-dry;
   splitEvents-bk-hop; splitEvents-vals-hop; switchKill-closes-nodry;
   switchKill-regsLen; thruWrap-INV; thruWrap-pass; walk-empty; walk-map;
   walk-of; walk-scan; walk-take)
open import Verify-Budget-Sufficient.Walk-Level.Statement using
  (inputᶜ; mu-lvl-desc; WalkLevel; WalkLevelCore; WalkStmt)
open import Decide using (T-to; T⇒≡true; ∧-intro; ≤ᵇ-widen)



------------------------------------------------------------------
-- THE INPUT CLAUSE'S WET RESIDUE.  walk-input is assembled below; this
-- is the half the caps face cannot give.

-- THE η PARAMETERISATION EXISTS FOR THIS STATEMENT'S SHAPE, and a machine
-- refutation is why.  The unparameterised form
-- bounded the connect burst's hop by `hopDᵉ V (input i)`, which was
-- 0 at every V — while `sharedConnect` passes the slot def's burst up
-- with its values UNTOUCHED, so an obs-typed slot whose def emits
-- `strmᵗ (mergeAllᵉ nothing emptyᵉ)` put a hop-1 value against a bound of 0.
-- Demand-Probe series W discharges every hypothesis and derives ⊥; no
-- entry hypothesis excluded it, because slotsCaps? is size/width and
-- INV? is size/fnCap — the hop channel for slot defs was UNGUARDED.

-- ROUTE (b) WAS TAKEN: hopD is now parameterised by an input
-- environment η (Rx.Hop-Depth), and the walk face instantiates it at
-- the HONEST one, `slotHop F sl` (Rx.Slot-Hop), for which
-- `hopDᵉ F (slotHop F sl) (input i) = slotHop F sl i` = the def's own
-- hop.  That number is well defined because the slot telescope is
-- STRATIFIED (`Rx.Slots`: a shared def reads only strictly smaller
-- indices), and `slotHop-fix` is the equation this clause spends:
-- at `sl i ≡ shared d`, the bound at `input i` IS `hopDᵉ F (slotHop
-- F sl) d`, which is exactly the burst the connect branch forwards.
-- Routes (a) — a slots-hop cap in INV? — and (c) — ground-only slot
-- types — were rejected: (a) leaves the *All hop descent unfunded for
-- shared carriers (the strict-drop argument reads the carrier's own
-- hopDᵉ, which a smuggled def value exceeds), and (c) is a spec change.

-- THE REPAIR IS A REPAIR, NOT A WEAKENED TEST — measured on the
-- refutation's own program, flipped: at the obs-typed shared slot whose def emits
-- strmᵗ (mergeAllᵉ nothing emptyᵉ), the hop conjunct is now `true` at every
-- measurement index and every non-dry gas, and the OLD bound is pinned
-- still rejecting the SAME burst — so the repair is a repair, not a
-- weakened test.  slotHop-fix is pinned at that program too, so the
-- fixpoint is exercised rather than assumed.
-- COVERED: the hop conjunct, at the exact region the refutation
-- reached; slotHop-cap's quantitative margin (series S, the amplifier
-- telescope); and the staged fixpoint at slot indices ABOVE zero
-- (series T — series W's fixpoint row sits at slot 0, where
-- `ηAt V sl 0 = λ _ → 0` makes both of slotHop-fix's postulates
-- vacuous, so the staging recursion was untested until T pinned
-- `slotHop V sl i ≡ hopDᵉ V (slotHop V sl) d` by refl at i = 1 and
-- i = 2, with the off-by-one alternative pinned as a live contrast).

-- THE OTHER FOUR CONJUNCTS RUN, at the series W program, co-instantiated — INV?, burstB?,
-- hasDry and regsLen? all `true` against one exit state, with B tight
-- (B = 5 holds, B = 4 fails on slotsSize; B = 1 fails burstB? on the
-- emitted value's sizeᵉ = 2) and hasDry pinned at series V's OWN gas
-- term rather than cited from series W's, since that program dries one
-- gas step down and the terms are not interchangeable by inspection.

-- NOT COVERED BY THE PROBES, and while the face was open this was its
-- FALSITY region: series V holds TWO
-- axes flat — Ψ = 0 at every row (the def is mergeAllᵉ nothing emptyᵉ, so
-- slotsFnCap insᵂ = 0) and the exit registry is EMPTY (sharedConnect's
-- burstCompleted branch drops the one entry), so regsLen? is vacuous
-- there and the Ψ conjuncts of INV?/burstB? are satisfied by 0 ≤ 0.

-- THE Ψ AXIS WAS NOT AN ARBITRARY GAP — IT IS WHERE THE REFUTATION WOULD
-- HAVE RECURRED, HAD THE FACE STAYED OPEN.  It did not; what follows is
-- why, and it is the reason the face is ground rather than parked.  `fnCapᵉ (input i) = 0` (.Measures) is
-- CONSTANT and unparameterised: structurally the very clause shape that
-- was machine-refuted for hop, where `hopDᵉ V η (input i)` was constant
-- 0 until an obs-typed shared slot's def was shown to emit values the
-- constant did not account for.  fnCapᵉ is positive on scanᵉ/mapᵉ with
-- a function-valued term, so a shared slot whose def carries one is
-- exactly the analogue of the refuting program.

-- THE RISK HISTORY, and it is HISTORY: the face is a real definition on
-- every clause and holds no live postulate, so no risk class applies to it
-- any more.  What follows is kept because it says what the probes reached
-- and what they could not, which is a fact about the evidence rather than a
-- claim about an open statement.

-- CLASS LOWERED FALSITY → DIFFICULTY.  What earned it, and
-- what did NOT:
--   · the conjunct that was actually REFUTED is repaired and the repair is
--     PROVEN — slotHop-fix rests on no postulate — and it is pinned at the
--     refutation's own program with the old bound still rejecting the same
--     burst, so it is a repair rather than a weakened test;
--   · the Ψ axis, where that refutation's shape would have recurred, is
--     closed by PROOF (caseW-subΘ, fnCap-subΘᵉ) — see below;
--   · hasDry is probed across several programs and gas terms, with a
--     boundary row pinning it TRUE one gas step down so the green rows are
--     known to sit past the dry boundary; its six funding lemmas
--     (connect-edge, sharedConnect-unconn, unconn-cons-≤, obs-slot-shared,
--     connect-anchor, unconn-keeps) are proven definitions;
--   · INV?/burstB? carry negative controls on BOTH axes; regsLen? is
--     non-degenerate via series REG.
-- NOT part of the case: the Ψ/Ψ2/Ψ3 probe series, which were deleted for
-- being structurally unable to refute.  The class rests on the proofs.

-- PROBE RESIDUE, and while the face was open it was what would have
-- re-raised the class: every probe is a small program.  Deeper telescopes,
-- scripted/shared mixes, and μ-nesting inside a slot def are uncovered, so
-- a surprise would have come from a fact about those shapes that no probe
-- touched.  The proof closes all of them; the boundary is recorded because
-- a reader restating any of this inherits the probes, not the proof.

-- THE Ψ AXIS IS ANSWERED, AND BY PROOF RATHER THAN BY PROBE.
-- Two lemmas in .Measures, both already proven, close the smuggle:
--   · `caseW-subΘ` / `caseW-ren` (W1) — caseWᵗ is substitution- and
--     renaming-INVARIANT, because reify images contain no caseᵗ at all and
--     subΘ rewrites only var positions.  So although caseWᵗ (caseᵗ s l r)
--     is ADDITIVE — the one clause in the family that is — evaluation never
--     feeds it a case-heavy substituend, and the count cannot be multiplied
--     by plugging a case-heavy value into a duplicated variable.
--   · `fnCap-subΘᵉ` (W2) — EnvFnCap Ψ σ → fnCapᵉ e ≤ Ψ →
--     fnCapᵉ (subΘExp Θloc σ e) ≤ Ψ.  Evaluation cannot lift fnCap past Ψ.
-- Together: a value emitted anywhere in the telescope carries fnCap ≤ Ψ, so
-- `fnCapᵉ (input i) = 0` is SAFE despite looking like the refuted hop clause.

-- AND THAT IS THE REAL DISANALOGY WITH HOP.  No lemma of this kind could
-- exist for hop: hop genuinely depends on the slot environment, which is
-- exactly why the repair had to parameterise the input clause by η.  fnCap
-- has a preservation theorem; hop does not.  (`ΨAt e sl = fnCapᵉ e +
-- slotsFnCap sl` summing rather than ⊔-ing the telescope is a second, weaker
-- reason — it covers a def that reads ANOTHER input without a staged
-- fixpoint — but the substitution lemmas are what actually settle it.)

-- METHOD NOTE, worth more than the result: three probe series (Ψ, Ψ2, Ψ3)
-- were commissioned to test this before anyone grepped .Measures for a
-- substitution lemma.  The receipts are real but they were never the cheapest
-- route, and none of them COULD have refuted — in every series the emitted
-- value is a subterm of its own def, where the ⊔-fold bounds it structurally.
-- Grep for the fact before designing the experiment.

-- WHY THE SPLIT IS EXACT.  WalkStmt's first thirteen hypotheses ARE
-- subscribeE-caps' hypothesis list verbatim, and its first four
-- conjuncts ARE subscribeE-caps' Σ verbatim (.Subscribe-Face) — the
-- module header has said so since the statement was written, and it is
-- literally true, so the caps half of EVERY walk clause is a delegation
-- rather than a re-derivation.  What no caps call can supply is the wet
-- five, and for `input i` those are what the share/connect edge owes:
-- subscribeSharedSlot's third branch is `sharedConnect`, one of the
-- three gas peels, and the demand drop that funds it is connect-edge's
-- (U strictly drops on the connectedShares insert, both child measures
-- reset at the anchor).

-- IT TAKES THE CAPS RECEIPTS AS HYPOTHESES, AND THAT IS THE POINT: j′
-- is BOUND by the caps call at the assembly site, so this postulate
-- cannot be satisfied by inflating the witness.  Stated with a free j′
-- and no caps receipts it would be upward-closed and vacuous — the
-- failure mode CLAUDE.md's Σ-receipt rule names, and the one that
-- machine-refuted the exit-level count face.

-- THE MUTUAL LANDING IS DONE.  input-wet is a real definition
-- over input-wet-core, which RECEIVES the walk face at the peeled fuel, so
-- the induction this clause needs can now be written.  `make gate-heavy` accepts
-- the recursion: zero TerminationIssue.

-- IT TOOK THREE SHAPES, AND THE TWO THAT FAILED ARE WHY THE THIRD IS WRITTEN
-- THE WAY IT IS.  Do not simplify it back:
--   · PASS walkFace ITSELF (`input-wet = input-wet-core walkFace`).  Typechecks;
--     `make gate-heavy` then rejects the whole walk group on termination, and the
--     call it names is not this clause's but a PRE-EXISTING one —
--     `stepThru-walk … (proj₁ (sp …)) …`, projections of the with-abstracted
--     `sp`.  Handing the core an unrestricted walk face means the checker must
--     assume it can be re-entered at the SAME gas, so the loop never decreases.
--     The group's termination had been relying on walkFace sitting outside its
--     cycle; definition order was never the blocker, as this header used to say.
--   · PASS A PEELED LAMBDA AT TYPE WalkLevel (`λ … _ κ′ … → walkFace … fuel …`,
--     discarding the lambda's own gas).  Never reaches termination — it is
--     ILL-TYPED.  WalkStmt's conclusion is gas-INDEXED, a Σ about
--     `subscribeE g b κ …`, so a body computed at `fuel` cannot inhabit a type
--     demanding the binder's `g`.  "A walk face at the peeled fuel" is simply
--     not a term of type WalkLevel.

-- WHAT MADE IT WORK: give that phrase a type.  WalkTail factors the statement
-- from κ onwards with the gas as a PARAMETER; WalkStmt keeps its old argument
-- order over it (so none of its 23 call sites, nor Demand-Probe's
-- instantiations, had to move) and WalkStmtAt pins the gas up front.  Then
-- `WalkLevelAt fuel` is nameable, `walkFace` PARTIALLY APPLIED inhabits it with
-- no lambda at all, and `peelGas` in input-wet-core's type carries the peel —
-- so at `gs fuel` the type reduces to `WalkLevelAt fuel` and the call site
-- shows the structural decrease the checker was looking for.

-- ONE MEASUREMENT WORTH KEEPING: declaring walkFace's signature far from its
-- clauses sweeps every definition in between into the mutual block — 47
-- members, 33 of them in no cycle at all.  Relocating input-wet/walk-input
-- adjacent to the dispatch gives exactly the 14 that genuinely cycle, and the
-- tight block type-checks FASTER than the status quo (28.7 s against 37.9 s).
-- `make agda-dev ARGS='--list <file>'` shows this for free.

-- THE PROVEN TEMPLATE IS `subscribeE-input-caps` (.Subscribe-Face), and it
-- is worth naming because it settles the SHAPE of the missing induction
-- rather than leaving it to be rediscovered.  It is the caps twin of this
-- statement and it has THREE clauses — one per subscribeSharedSlot branch —
-- so the wet induction is three clauses too, not one.  Its second and third
-- clauses are where `len≤inputSize` and the LENB chain do the work, which is
-- the same bookkeeping the wet side's hasDry conjunct needs.

-- THE BLOCKER THIS HEADER USED TO NAME IS GONE (corrected).  It
-- said walkFace was a plain definition sitting after the postulate block, so
-- nothing could call it, and that making walkFace and the walk-* clauses
-- MUTUAL was "the real prerequisite".  That refactor LANDED —
-- it is the mutual-landing paragraph above, in this same header — and the
-- paragraph describing it as still owed was never removed.  The walk face is
-- available: `input-wet-core` takes `WalkLevelAt (peelGas g)` and passes it
-- to `input-wet-shared` as `wl` (the shared dispatch clause below).  So the
-- prerequisite is met and the eight PROVEN lemmas named below are in scope;
-- what remains is the induction that spends them, and nothing structural is
-- in its way.

-- Two paragraphs of one header disagreeing is the "lying comment" forbidden
-- state, and this is what it costs: the stale half reads as a work order for
-- a refactor already done, which is a session's worth of misdirection aimed
-- squarely at whoever picks this up next.

-- EXPECTED TO PAY IT when it is ground: connect-edge (the demand drop),
-- sharedConnect-unconn and unconn-cons-≤ (the U bookkeeping either side
-- of the insert), obs-slot-shared and connect-anchor (the child's reset
-- caps), unconn-keeps (U never rises across the child's own work), and
-- the two share-novals lemmas for the hasDry conjunct on the two
-- non-connecting branches.  All eight are PROVEN and in scope; what is
-- missing is the induction that spends them, which needs walkFace at
-- the peeled fuel and therefore this postulate's own mutual landing.
------------------------------------------------------------------
------------------------------------------------------------------
-- THE HOP-EDGE CHAIN, LEAF FIRST — subscribeInner-walk, its one-frame
-- consumer stepThru-walk, and the REAL push face over them.  Each is
-- its caps twin ⊗ the wet content on one witness, the discipline the
-- whole module runs on.

-- ⚠ DEAD ROUTE, and it shaped this whole section: A
--   FRAME-GENERIC WET PUSH FACE IS FALSE.  The first statement of this
--   face (one postulate `pushBurst-walk`, generic in `f : Frame Γ s u`,
--   committed 9fb13d3) carried a uniform hop conjunct — input receipts
--   at r̂, output at suc r̂ — and that is REFUTABLE BY CONSTRUCTION at
--   f := map-f: a step function that wraps its input two mergeAll levels
--   deep sends a value of hop exactly r̂ to hop r̂ + 2 > suc r̂, with every
--   hypothesis satisfiable (frameB? bounds the fn's SIZE and WEIGHT,
--   never its hop growth).  The caps face is frame-generic because caps
--   measures are; THE HOP LEDGER IS FRAME-SPECIFIC.  pushBurst has four
--   call sites (thru-outer, map-f, take-f, scan-f — Rx.Evaluator), so
--   the repair is one wet push face PER FRAME KIND, this one thru-outer's.
--   Two of the chain frames' faces are now authored — `pushTake-wet` at
--   the identity index and `pushMap-wet` at hopD-map-emit's — leaving
--   scan-f's, whose index is the exponential one.
------------------------------------------------------------------

-- THE LEAF — the wet face of subscribeInner, WHERE THE GAS PEEL IS.
-- subscribeInner-caps' hypothesis list and Σ verbatim (.Subscribe-Face,
-- PROVEN both clauses, including the strict sLvlD report), ⊗ the wet
-- content.  Σ-content: the strict level bound is the one downward
-- conjunct; the hop/dry/regsLen? conjuncts are j′-free.

-- WHAT IS NAILED DOWN BY THE STATEMENT ALONE: subscribeInner's g0 arm
-- is the evaluator's ONE remaining dry mint under this face
-- (`close drySource dried`, Rx.Evaluator) — and the gas hypothesis
-- `g hasAtLeast suc G` HAS NO CONSTRUCTOR AT g0, so the mint is
-- unreachable by type, exactly as the μ mint is at walkFace's absurd
-- clause.  Both of the machine's dry mints are now excluded by the
-- same one-line shape; what remains everywhere else is PRESERVATION.

-- THE gs ROUTE, EXECUTED (the body at the end of the
-- mutual block): peel the gas at the matched constructor
-- (hasAtLeast-peel-gs); walkFace o — the mutual walk at the inner,
-- legitimate because the peel descends the gas, the same induction
-- subscribeE-caps' subscribeInner clause runs — at level suc j under
-- κ′ = from-inner op allNid inst ↠ κ; the walk's burst conjuncts feed
-- the vs/bs receipts through the splitBurst square (caps twins from
-- .Subscribe-Face; wet vals splitBurst-vals-B, hop splitBurst-vals-hop,
-- dry splitBurst-nodry — all in this module's kit).  The demand:
-- hop-step-gives at the descended index — hopDᵛ F o ≤ r̂ (hypothesis)
-- and the dBound monos — funds the inner walk's demand STRICTLY below
-- suc r̂'s, and that ONE unit also pays the from-inner frame's ℓ
-- extension: the +1/+1 lockstep, in the telescope.

-- THE LIVE EDGE IS CLOSED AT THE STATEMENT (the
-- reset-anchor pins): the face used to quantify Ŝ freely with NO
-- hypothesis linking the level cap to it, which made the demand
-- funding unprovable and possibly false — hop-step-gives' premise
-- needs suc (syncSizeᵉ o) ≤ ŝ + suc Ŝ, the receipts bound syncSizeᵉ o
-- only by the LEVEL cap (valB?'s size half + reach-reset, .Measures),
-- and hop-step-needs (machine-checked, .Wet/Part6) proves the link is
-- NECESSARY for any r-drop funding, so no cleverer proof could have
-- avoided it.  The repair is the threaded ceiling the old header
-- predicted: `2 ≤ Ŝ`, `F ≡ Ŝ`, `R̂ ≡ hopR Ŝ`, and
-- `cSize (frameStep L̂ c) ≤ Ŝ` at the face's own budget — refl/lemma
-- at the true instantiation (entry-ceiling; GAP 2's ruling and
-- caps-tick supply it), converted between faces by the Caps-Chain
-- descents.  With the link in the telescope the gs body's funding is
-- hop-edge (proven) at the receipt-derived size bound; what remains is
-- assembly against the caps twin, not a coincidence bet.
-- (Demand-Probe series Q probed the OLD unlinked statement: the safe
-- region green, the crossing region multi-hour; a crossing-region
-- refutation would confirm the pin was needed, and its green would
-- not have certified the unlinked face.  Burst-Walk's SiNodry states
-- the DELIVERY-side leaf, hasDry only, PROVEN there by consuming the
-- finished walk face; this statement is the SUBSCRIBE-side leaf the
-- walk face itself consumes.  Same evaluator function, opposite
-- direction of dependency.)

-- PAYABILITY (census): the ceiling conversion the gs body
-- owes the inner walkFace call — its own `sLvlD S W dep (suc bud)
-- (suc j) ≤ L̂` into the inner's `opIterD … (suc j) ≤ L̂` — is
-- DEFINITIONAL.  sLvlD-suc (Rx.Evaluator, refl):
--   sLvlD S W d (suc k) J ≡ opIterD S W d k (suc (sizeAt S J)) J
-- so the leaf's budget IS the inner sweep's budget at ops :=
-- suc (sizeAt S (suc j)); and `Caps.cSize (frameStep j c)` UNFOLDS to
-- `sizeAt (Caps.cSize c) j` (both are iterSize S j S), so the inner's
-- actual ops `suc (sizeᵉ o)` sits under the pinned one by szb +
-- sizeAt-mono (.Caps, proven) over j ≤ suc j.  The tower was built
-- for this edge; nothing new is owed here.
SubscribeInnerWalk : Set
SubscribeInnerWalk = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (op : AllOp) (allNid : NodeId)
  (κ : Path Γ u t) (bid : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthInner g op allNid κ bid now o sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  valB? (Caps.cSize (frameStep j c)) Ψ (obs u) o ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  hopDᵛ F (slotHop F sl) (obs u) o ≤ r̂ →
  -- the reset-anchor pins, at this face's own budget.  THE LIVE EDGE
  -- CLOSES HERE: the ceiling converts o's valB?/valCaps? size receipt
  -- (at cSize (frameStep j c), j under the budget under L̂) into
  -- hop-edge's `sizeᵛ o ≤ Ŝ` premise, which is the exact syncSize
  -- headroom hop-step-needs proves the gas peel REQUIRES.
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j) ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeInner g op allNid κ bid now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
              (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ (proj₂ r)) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl)
            (proj₁ (proj₂ (proj₂ r))) ≡ true)
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
             (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u)
            (proj₁ (proj₂ r)) ≡ true)
     × (all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) (proj₁ (proj₂ r)) ≡ true)
     × (any dryEvent (proj₁ (proj₂ (proj₂ r))) ≡ false)
     × (regsLen? ℓ (EvalSt.registry
          (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))) ≡ true)

-- ONE thru-outer FRAME — stepFrame-caps' Σ at f := thru-outer op nid
-- (its frameSz? hypothesis is definitionally true there and is
-- dropped), ⊗ the wet content.  The vs it emits are inner-burst values,
-- so their hop receipts stay AT r̂ — no growth through this frame; the
-- push face widens once at its consumer.
StepThruWalk : Set
StepThruWalk = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (bid : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  valsCaps? (frameStep j c) sl vals ≡ true →
  frameBud c j ≤ bud →
  depthFrame g bid now (thru-outer op nid) κ vals fin sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  all (valB? (Caps.cSize (frameStep j c)) Ψ (obs u)) vals ≡ true →
  all (λ o → hopDᵛ F (slotHop F sl) (obs u) o ≤ᵇ r̂) vals ≡ true →
  -- the reset-anchor pins, at this face's own budget (the -core owes
  -- each loop element the leaf's sLvlD form, a frame-step descent)
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  fLvlD (Caps.cSize c) (Caps.cWid c) dep j ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = stepFrame g bid now (thru-outer op nid) κ vals fin sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ (proj₂ r))))
              (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
     × (j + j′ ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ (proj₂ r))))
             (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u) (proj₁ r) ≡ true)
     × (all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) (proj₁ r) ≡ true)
     × (any dryEvent (proj₁ (proj₂ r)) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r))))) ≡ true)

-- EX-POSTULATES: subscribeInner-walk and the loop it
-- feeds are REAL — forward-declared here, ground after subscribeAll-walk
-- at the end of the mutual block, mirroring the caps clique's own
-- recursion (subscribeInner-caps → subscribeE-caps at the peeled fuel,
-- .Subscribe-Face, PROVEN — the termination precedent).  The old
-- `stepThru-walk-core : SubscribeInnerWalk → StepThruWalk` wiring is
-- GONE and could not have survived: passing a mutual member UNAPPLIED
-- to a postulate is invisible to the termination checker, so the gas
-- peel it hides can never license the cycle.  The loop's consumption of
-- the leaf is an APPLIED call now (thruConsume-walk's per-op SI), which
-- is exactly what the checker needs.
--
-- The bodies are the caps twins ⊗ the wet content, per this module's
-- discipline; the lockstep arithmetic (one demand unit pays the gas
-- peel AND the path-frame extension) lands in subscribeInner-walk's gs
-- clause, where subscribeAll-walk's body already spends the same unit
-- for the thru-outer frame.
subscribeInner-walk : SubscribeInnerWalk

-- THE μ GAS PEEL, GROUND — body after walkFace, which it calls at the
-- peeled fuel exactly as subscribeInner-walk does.  Declared HERE, with
-- its fellow mutual members rather than beside its clause siblings up
-- in the postulate block: the whole block's signatures must sit below
-- SubscribeInnerWalk, and a forward declaration hoisted above it puts
-- the block's own vocabulary out of scope.
walk-mu : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (body : Exp Γ (u ∷ []) [] [] u) → WalkStmt {e = e} (μᵉ body)

-- one payload of the walk — thruConsume-caps' hypothesis list verbatim
-- (subscribeInner-caps' own, as there), ⊗ the wet content
thruConsume-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (bid : Id) (now : Tick) (o : Val Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  valCaps? (frameStep j c) sl (obs u) o ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest o sl (EvalSt.connectedShares st) ≤ bud →
  depthConsume g op nid κ bid now o sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  valB? (Caps.cSize (frameStep j c)) Ψ (obs u) o ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  hopDᵛ F (slotHop F sl) (obs u) o ≤ r̂ →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j) ≤ L̂ →
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = thruConsume g op nid κ bid now o sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
     × (suc (j + j′) ≤ sLvlD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (suc j))
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u) (proj₁ r) ≡ true)
     × (all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) (proj₁ r) ≡ true)
     × (any dryEvent (proj₁ (proj₂ r)) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (proj₂ r)))) ≡ true)

-- the walk itself — thruWalk-caps' hypothesis list ⊗ the wet content;
-- reports in the sIterD shape its caps twin does
thruWalk-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (bid : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  valsCaps? (frameStep j c) sl vals ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  mList? bud sl (EvalSt.connectedShares st) vals ≡ true →
  depthWalk g op nid κ bid now vals sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  all (valB? (Caps.cSize (frameStep j c)) Ψ (obs u)) vals ≡ true →
  all (λ o → hopDᵛ F (slotHop F sl) (obs u) o ≤ᵇ r̂) vals ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) j ≤ L̂ →
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = thruWalk g op nid κ bid now vals sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c)
              (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (all (eventCaps? (frameStep (j + j′) c) sl) (proj₁ (proj₂ r)) ≡ true)
     × (j + j′ ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length vals) j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r))) ≡ true)
     × (all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u) (proj₁ r) ≡ true)
     × (all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) (proj₁ r) ≡ true)
     × (any dryEvent (proj₁ (proj₂ r)) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ (proj₂ r)))) ≡ true)

stepThru-walk : StepThruWalk

-- THE PUSH FACE AT thru-outer, REAL — pushBurst-caps' proven proof
-- (.Subscribe-Face) step for step, wet conjuncts threaded through:
-- per emit, split the events, step the values through the one frame
-- (stepThru-walk), recurse on the tail from the stepped state, and
-- reassemble the envelope with the per-segment plumbing above.  The
-- input hop receipts arrive at r̂ and LEAVE at r̂ — the thru frame does
-- not grow hops — so the composite's suc is paid by the consumer's one
-- widening, never here.
pushThru-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j : ℕ)
  (g : Gas) (bid : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (κ : Path Γ u t) (str : Stream Γ (obs u))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  burstCaps? (frameStep j c) sl str ≡ true →
  burstCount? (frameStep j c) str ≡ true →
  depthBurst g bid now (thru-outer op nid) κ str sched st ≤ dep →
  -- the wet half at the level
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  burstB? (Caps.cSize (frameStep j c)) Ψ str ≡ true →
  burstHopD? F (slotHop F sl) r̂ str ≡ true →
  hasDry str ≡ false →
  -- the reset-anchor pins, at this face's own budget
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j ≤ L̂ →
  -- the dry half
  unconn sl (EvalSt.connectedShares st) ≤ U →
  dBound Ŝ R̂ U (suc r̂) ŝ ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = pushBurst g bid now (thru-outer op nid) κ str sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     × (j + j′ ≤ fIterD (Caps.cSize c) (Caps.cWid c) dep bud (length str) j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) r̂ (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g bid now op nid κ [] sl sched st
  2≤S 1≤R hCR slEq slC slSz inv pS lC bC cC dpt invW pB bB bH hDry s2 fS rS ceil lb hU dmd gas lℓ rgs =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , refl
    , refl
    , burst-nil (Caps.cSize c) (Caps.cWid c) dep bud j
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
            (sym (+-identityʳ j)) invW
    , refl
    , refl
    , refl
    , rgs
pushThru-walk {n = n} {Γ = Γ} {t = t} {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g bid now op nid κ (em ∷ ems) sl sched st
  2≤S 1≤R hCR slEq slC slSz inv pS lC bC cC dpt invW pB bB bH hDry s2 fS rS ceil lb hU dmd gas lℓ rgs =
  j₁ + j₂
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST)) ≡ true) EQA W1
    , subst (λ x → burstCaps? (frameStep x c) sl OUT ≡ true) EQA
            (∧-intro EMIT W2)
    , subst (λ x → burstCount? (frameStep x c) OUT ≡ true) EQA COUNT
    , burst-step (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j j₁ j₂ 2≤S
        S4 W4
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ REST)) (proj₂ (proj₂ REST)) ≡ true) EQA W5
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ OUT ≡ true) EQA
            (∧-intro EMITB W6)
    , ∧-intro EMITH W7
    , cong₂ _∨_ EMITD W8
    , W9
  where
  E    = InstEmit.events em
  sp   = splitEvents {A = Val Γ u} E
  step = stepFrame g bid now (thru-outer op nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ step)))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ step)))
  -- caps receipts for this emit, verbatim from the caps proof
  eC   = proj₁ (∧-true _ _ bC)
  cntW = suc (Caps.cWid (frameStep j c))
  cntP : InstEmit (Val Γ (obs u)) → Bool
  cntP em′ = valCountᵉ (InstEmit.events em′) ≤ᵇ cntW
  cCv  = proj₂ (∧-true (length (em ∷ ems) ≤ᵇ cntW) (all cntP (em ∷ ems)) cC)
  cntE = ≤ᵇ⇒≤ (valCountᵉ E) cntW
           (T-to (proj₁ (∧-true (cntP em) (all cntP ems) cCv)))
  -- wet receipts for this emit
  eB   = proj₁ (∧-true _ _ bB)
  eH   = proj₁ (∧-true _ _ bH)
  dSp  = ∨-false (any dryEvent E) (hasDry ems) hDry
  SF   = stepThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep (frameBud c j) j g bid now op nid κ
           (proj₁ sp) (proj₂ (proj₂ sp)) sl sched st
           2≤S 1≤R hCR slEq slC slSz inv pS lC
           (splitEvents-valsCaps {u = u} (frameStep j c) sl E eC cntE)
           ≤-refl
           -- both ⊔ arguments spelled out: _⊔_ matches on BOTH sides,
           -- so the tail as a meta is a stuck constraint, not a hole
           -- the unifier can fill
           (≤-trans (m≤m⊔n
              (depthFrame g bid now (thru-outer op nid) κ
                 (proj₁ sp) (proj₂ (proj₂ sp)) sched st)
              (depthBurst g bid now (thru-outer op nid) κ ems sd₁ st₁)) dpt)
           invW pB
           (splitEvents-vals-B {u = u} (Caps.cSize (frameStep j c)) Ψ E eB)
           (splitEvents-vals-hop {u = u} F (slotHop F sl) r̂ E eH)
           s2 fS rS ceil
           (≤-trans (frame-desc (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j) lb)
           hU dmd gas lℓ rgs
  j₁   = proj₁ SF
  S1   = proj₁ (proj₂ SF)
  S2   = proj₁ (proj₂ (proj₂ SF))
  S3   = proj₁ (proj₂ (proj₂ (proj₂ SF)))
  S4   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SF))))
  S5   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF)))))
  S6   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))
  S7   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF)))))))
  S8   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))))
  S9   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SF))))))))
  ⊑₁   = frameStep-⊑-+ c 2≤S j j₁
  KS   = stepFrame-keeps g bid now (thru-outer op nid) κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  sl₁eq : Sched.slots sd₁ ≡ sl
  sl₁eq = trans (KeepsC.slotsEq KS) slEq
  UK₁ : unconn sl (EvalSt.connectedShares st₁) ≤ U
  UK₁ = ≤-trans
          (subst₂ (λ y z → unconn y (EvalSt.connectedShares st₁)
                             ≤ unconn z (EvalSt.connectedShares st))
                  sl₁eq slEq
                  (unconn-keeps sched st sd₁ st₁ KS))
          hU
  IH   = pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud (j + j₁) g bid now op nid κ ems sl sd₁ st₁
           2≤S 1≤R hCR sl₁eq slC slSz
           S1
           (pathSz?-⊑ κ ⊑₁ pS)
           (≤-trans lC (proj₁ ⊑₁))
           (burstCaps?-widen sl ems ⊑₁ (proj₂ (∧-true _ _ bC)))
           (burstCount?-widen ems ⊑₁ (burstCount?-tail (frameStep j c) em ems cC))
           (≤-trans (m≤n⊔m _ _) dpt)
           S5
           (pathB?-widen κ (proj₁ ⊑₁) pB)
           (burstB?-widen ems (proj₁ ⊑₁) (proj₂ (∧-true _ _ bB)))
           (proj₂ (∧-true _ _ bH))
           (proj₂ dSp)
           s2 fS rS ceil
           (≤-trans (tail-desc (Caps.cSize c) (Caps.cWid c) dep bud (length ems) j j₁
                       2≤S S4)
                    lb)
           UK₁ dmd gas lℓ
           S9
  j₂   = proj₁ IH
  W1   = proj₁ (proj₂ IH)
  W2   = proj₁ (proj₂ (proj₂ IH))
  W3   = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  W4   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  W5   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  W6   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
  W7   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
  W8   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  W9   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  REST = pushBurst g bid now (thru-outer op nid) κ ems sd₁ st₁
  OUT  = ((proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
             ++ map value (proj₁ step)
             ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
           at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
          ∷ proj₁ REST
  EQA : (j + j₁) + j₂ ≡ j + (j₁ + j₂)
  EQA = +-assoc j j₁ j₂
  ⊑₂  = frameStep-⊑-+ c 2≤S (j + j₁) j₂
  ⊑ⱼ  = frameStep-mono-j c 2≤S (≤-trans (m≤m+n j j₁) (m≤m+n (j + j₁) j₂))
  B″  = Caps.cSize (frameStep ((j + j₁) + j₂) c)
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
                       (valsOf (frameStep (j + j₁) c) sl (proj₁ step) S2)))
                 (finList-caps (frameStep ((j + j₁) + j₂) c) sl
                    (proj₁ (proj₂ (proj₂ step))))))
  EMITB : all (eventB? B″ Ψ)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITB = all-++-intro (eventB? B″ Ψ) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-B {u = u} B″ Ψ E)
            (all-++-intro (eventB? B″ Ψ) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-B B″ Ψ (proj₁ (proj₂ step)))
               (all-++-intro (eventB? B″ Ψ) (map value (proj₁ step)) _
                  (mapValue-B B″ Ψ u (proj₁ step)
                     (valsB?-widen u (proj₁ step) (proj₁ ⊑₂) S6))
                  (finList-B {u = u} B″ Ψ (proj₁ (proj₂ (proj₂ step))))))
  EMITH : all (hopDev? F (slotHop F sl) r̂)
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ true
  EMITH = all-++-intro (hopDev? F (slotHop F sl) r̂) (proj₁ (proj₂ sp)) _
            (splitEvents-bk-hop {u = u} F (slotHop F sl) r̂ E)
            (all-++-intro (hopDev? F (slotHop F sl) r̂) (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-hop F (slotHop F sl) r̂ (proj₁ (proj₂ step)))
               (all-++-intro (hopDev? F (slotHop F sl) r̂) (map value (proj₁ step)) _
                  (mapValue-hop F (slotHop F sl) r̂ (proj₁ step) S7)
                  (finList-hop {n = n} {Γ = Γ} {u = u} F (slotHop F sl) r̂
                     (proj₁ (proj₂ (proj₂ step))))))
  EMITD : any dryEvent
              (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                 ++ map value (proj₁ step)
                 ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ false
  EMITD = any-++-false dryEvent (proj₁ (proj₂ sp)) _
            (splitEvents-bk-dry {u = u} E (proj₁ dSp))
            (any-++-false dryEvent (retagEvents (proj₁ (proj₂ step))) _
               (retagEvents-dry (proj₁ (proj₂ step)) S8)
               (any-++-false dryEvent (map value (proj₁ step)) _
                  (mapValue-dry (proj₁ step))
                  (finList-dry {A = Val Γ u} (proj₁ (proj₂ (proj₂ step))))))
  HEADV : valCountᵉ (proj₁ (proj₂ sp) ++ retagEvents (proj₁ (proj₂ step))
                       ++ map value (proj₁ step)
                       ++ (if proj₁ (proj₂ (proj₂ step)) then complete ∷ [] else []))
            ≡ length (proj₁ step)
  HEADV = pushEmit-count {Γ = Γ} {s = obs u} {u = u} {A = Val Γ t}
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
                     S2)))
  LEN : length OUT ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c))
  LEN = subst (λ x → suc x ≤ suc (Caps.cWid (frameStep ((j + j₁) + j₂) c)))
              (sym (pushBurst-len g bid now (thru-outer op nid) κ ems sd₁ st₁))
              (≤-trans (countLen (frameStep j c) (em ∷ ems) cC)
                       (s≤s (proj₁ (proj₂ ⊑ⱼ))))
  COUNT : burstCount? (frameStep ((j + j₁) + j₂) c) OUT ≡ true
  COUNT = countIn (frameStep ((j + j₁) + j₂) c) OUT LEN
            (∧-intro HEADB
               (countVals (frameStep ((j + j₁) + j₂) c) (proj₁ REST) W3))

-- THE *All DELEGATE — subscribeAll-caps ⊗ the wet content, one Σ,
-- exactly as WalkStmt is subscribeE-caps ⊗ the same content, and REAL:
-- the body (below walkFace — the two are mutual, the recursion
-- decreasing at walkFace (opᵉ b) → … → walkFace b) mirrors
-- subscribeAll-caps' proven proof step for step.  mint → install
-- (capsOK?-setNode / INV?-install) → the recursive walk on b at
-- κ′ = thru-outer op nid ↠ κ, funded by hop-step-gives (the composite
-- demand at suc/suc measures yields the source's demand STRICTLY
-- smaller, the spent unit paying the ℓ extension exactly — the unit
-- subscribeE-inner-nodry-pLen lacks) → pushThru-walk over the
-- returned burst (REAL, above — its hop receipts return AT hopDᵉ F b,
-- and the composite conjunct's suc is one widening here) → op-step for
-- the level charge.  The hop-edge chain below it is REAL too
-- : subscribeInner-walk, thruConsume-walk, thruWalk-walk
-- and stepThru-walk are all ground at the end of this mutual block, so
-- this face's walk residue is the CLAUSE postulates alone.
--
-- The hypothesis list is subscribeAll-caps' own, verbatim and in its
-- order, then the wet half with the composite's measures in REDUCED
-- form — suc (hopDᵉ F b), suc (syncSizeᵉ b), fnCapᵉ b,
-- suc (suc (sizeᵉ b)) — because every *All constructor computes to
-- exactly those, so the four heads pass their hypotheses through
-- untouched (the caps precedent: "inherits their index and their
-- hypothesis verbatim").
--
-- ONE wet hypothesis is new, fnCapNode Ψ ns: INV?'s fnCapBounded?
-- conjunct reads EvalSt.nodes, which installNode extends, so the Ψ
-- half of the install must be funded.  (The SIZE half rides the caps
-- boundedNode hypothesis already in the list — stBounded? reads the
-- same node list.)  All three heads supply it by refl: switch-st and
-- exhaust-st are `true` outright, mergeAll-st with an empty queue is
-- `all _ []`.
subscribeAll-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j : ℕ)
  (g : Gas) (op : AllOp) (ns : NodeState Γ)
  (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
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
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (suc (sizeᵉ b)) ≤ ops →
  depthAll g op ns b κ bid now sched st ≤ dep →
  -- the wet half, WalkStmt's own
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  fnCapNode Ψ ns ≡ true →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  -- the reset-anchor pins, WalkStmt's own (the budget is the same
  -- opIterD, so the heads pass all five through verbatim)
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  -- the dry half, at the composite's own measures (each *All
  -- constructor computes to exactly this suc/suc form)
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (suc (hopDᵉ F (slotHop F sl) b)) (suc (syncSizeᵉ b)) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeAll g op ns b κ bid now sched st
  in Σ ℕ λ j′ →
     (capsOK? (frameStep (j + j′) c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
     × (burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true)
     × (j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j)
     × (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (suc (hopDᵉ F (slotHop F sl) b)) (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)

-- THE FOUR *All HEADS, REAL: each delegates its whole body to
-- subscribeAll-walk, exactly as subscribeE-caps' four heads delegate
-- to subscribeAll-caps — the node bounds (caps AND wet) are refl at
-- every initial state, the size hypothesis sheds the constructor's
-- suc, the nest hypothesis steps by the Caps-Nest lemma, and every
-- other hypothesis passes through untouched because the *All measures
-- compute (sizeᵉ/hopDᵉ/syncSizeᵉ to suc, fnCapᵉ/dWᵉ to themselves,
-- depthE to depthAll at this op and state).
walk-mergeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (lim : Maybe ℕ) (b : Closed Γ (obs u)) → WalkStmt {e = e} (mergeAllᵉ lim b)
walk-mergeAll {u = u} lim b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g mergeAllᵒ
    (mergeAll-st {t = u} lim 0 [] false) b κ bid now sl sched st
    2≤S 1≤R hCR slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (mergeAll-step lim _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

walk-switchAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (switchAllᵉ b)
walk-switchAll b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g switchᵒ
    (switch-st nothing false) b κ bid now sl sched st
    2≤S 1≤R hCR slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (switch-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs

walk-exhaustAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (b : Closed Γ (obs u)) → WalkStmt {e = e} (exhaustAllᵉ b)
walk-exhaustAll b c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g exhaustᵒ
    (exhaust-st false false) b κ bid now sl sched st
    2≤S 1≤R hCR slEq slC slSz inv refl refl
    (≤-trans (n≤1+n (sizeᵉ b)) szb) wdb pC lC
    (exhaust-step _ sl _ bud nst) hidx dpt
    invW fnC refl pB s2 fS rS ceil lb dmd gas lℓ rgs




-- THE MUTUAL LANDING.  input-wet-core is handed a walk face AT THE PEELED
-- FUEL — `walkFace` partially applied, which inhabits WalkLevelAt directly.
-- Passing walkFace ITSELF instead was tried and fails termination (the
-- checker must then assume any gas, and the loop through the walk group
-- never decreases); passing a peeled lambda at type WalkLevel was tried and
-- is ill-typed, since WalkStmt's conclusion is gas-indexed.  Both notes are
-- at the dead-route block above.  This shape is the one that has a chance:
-- the type carries the peel, so the call site shows the decrease.
--
-- g0 is absurd exactly as the μ clause is — `g hasAtLeast suc G` has no
-- constructor there, so the connect is unreachable.
-- forward-declared so input-wet below can name it; clauses at the dispatch
walkFace : WalkLevel


input-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ : ℕ)
  (g : Gas) (i : Fin n) (b : Closed Γ (lookup Γ i))
  (κ : Path Γ (lookup Γ i) t)
  (bid : Id) (now : Tick) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  -- b is BOUND, not applied: the measures below take a general
  -- `Exp Γ Δᵍ Δ Θ t`, and only a binder pins those three contexts to
  -- `[]` — an alias of type `Closed Γ _` does not, so writing
  -- `sizeᵉ (input i)` here leaves an unsolved meta per measure.
  b ≡ inputᶜ i →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep j c) sched st ≡ true →
  sizeᵉ b ≤ Caps.cSize (frameStep j c) →
  pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
  nest b sl (EvalSt.connectedShares st) ≤ bud →
  suc (sizeᵉ b) ≤ ops →
  depthE g b κ bid now sched st ≤ dep →
  INV? Ψ (Caps.cSize (frameStep j c)) sched st ≡ true →
  fnCapᵉ b ≤ Ψ →
  pathB? (Caps.cSize (frameStep j c)) Ψ κ ≡ true →
  2 ≤ Ŝ →
  F ≡ Ŝ →
  R̂ ≡ hopR Ŝ →
  Caps.cSize (frameStep L̂ c) ≤ Ŝ →
  opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j ≤ L̂ →
  dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
         (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b) ≤ G →
  g hasAtLeast suc G →
  pathLen κ + G ≤ ℓ →
  regsLen? ℓ (EvalSt.registry st) ≡ true →
  let r = subscribeE g b κ bid now sched st
  in capsOK? (frameStep (j + j′) c)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     burstCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true →
     burstCount? (frameStep (j + j′) c) (proj₁ r) ≡ true →
     j + j′ ≤ opIterD (Caps.cSize c) (Caps.cWid c) dep bud ops j →
     (INV? Ψ (Caps.cSize (frameStep (j + j′) c))
            (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (Caps.cSize (frameStep (j + j′) c)) Ψ (proj₁ r) ≡ true)
     × (burstHopD? F (slotHop F sl) (hopDᵉ F (slotHop F sl) b)
                   (proj₁ r) ≡ true)
     × (hasDry (proj₁ r) ≡ false)
     × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
input-wet c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g0 i b κ bid now sl sched st
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
input-wet c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ (gs fuel) i b κ bid now sl sched st =
  input-wet-core c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ (gs fuel)
    (λ b′ c′ Ψ′ F′ Ŝ′ R̂′ G′ ℓ′ L̂′ dep′ bud′ ops′ j″ → walkFace b′ c′ Ψ′ F′ Ŝ′ R̂′ G′ ℓ′ L̂′ dep′ bud′ ops′ j″ fuel)
    i b κ bid now sl sched st




-- THE INPUT CLAUSE, GROUND.  Caps half delegated to the proven face at
-- ITS witness; wet half at the SAME witness, which is what makes the
-- two receipts one receipt rather than two independent Σs.
walk-input : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) → WalkStmt {e = e} (input i)
walk-input i c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g κ bid now sl sched st
           2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt
           invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  j′ , C1 , C2 , C3 , C4
     , proj₁ WET
     , proj₁ (proj₂ WET)
     , proj₁ (proj₂ (proj₂ WET))
     , proj₁ (proj₂ (proj₂ (proj₂ WET)))
     , proj₂ (proj₂ (proj₂ (proj₂ WET)))
  where
  CAPS = subscribeE-caps c dep bud ops j g (input i) κ bid now sl sched st
           2≤S 1≤R slEq slC slSz inv szb wdb pC lC nst hidx dpt
  j′ = proj₁ CAPS
  C1 = proj₁ (proj₂ CAPS)
  C2 = proj₁ (proj₂ (proj₂ CAPS))
  C3 = proj₁ (proj₂ (proj₂ (proj₂ CAPS)))
  C4 = proj₂ (proj₂ (proj₂ (proj₂ CAPS)))
  WET = input-wet c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j j′ g i (input i) κ
          bid now sl sched st refl
          2≤S 1≤R hCR slEq slC slSz inv szb pC lC nst hidx dpt
          invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs
          C1 C2 C3 C4

-- THE DISPATCH, real from day one: match the subscribed expression,
-- hand the clause its own obligation.  Two clauses are PROVEN outright:
-- varᵉ (a closed term has no value variables) and μᵉ at g0 — the μ dry
-- mint, subscribeE's ONLY dry emit, is unreachable because
-- `g0 hasAtLeast suc G` has no constructor.  So `hasDry ≡ false` needs
-- no postulate at the one clause of subscribeE that emits dryness:
-- what remains is showing the recursive clauses PRESERVE it.
walkFace (input i)       = walk-input i
walkFace (ofᵉ ts)        = walk-of ts
walkFace emptyᵉ          = walk-empty
walkFace (mapᵉ f b)      c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g =
  walk-map g f b
    (λ c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ →
       walkFace b c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ g)
    c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j
walkFace (takeᵉ cnt b)   c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g =
  walk-take g cnt b
    (λ c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ →
       walkFace b c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ g)
    c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j
walkFace (scanᵉ f z b) c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g =
  walk-scan g f z b
    (λ c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ →
       walkFace b c′ Ψ′ F′ Ŝ′ R̂′ G″ ℓ′ L̂′ dep′ bud′ ops′ j″ g)
    c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j
walkFace (mergeAllᵉ lim b) = walk-mergeAll lim b
walkFace (switchAllᵉ b)  = walk-switchAll b
walkFace (exhaustAllᵉ b) = walk-exhaustAll b
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g0 κ bid now sl sched st
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ()
walkFace (μᵉ body) c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j (gs fuel) κ bid now sl sched st =
  walk-mu body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j (gs fuel) κ bid now sl sched st
walkFace (varᵉ ())
walkFace (deferᵉ body)   = walk-defer body

------------------------------------------------------------------
-- THE μ CLAUSE, GROUND.  subscribeE (gs fuel) (μᵉ body) IS
-- subscribeE fuel (unfoldμ body) — DEFINITIONALLY, one clause of the
-- evaluator (.Rx/Evaluator) — so the result term is literally the
-- recursive call's and every conjunct transports without a subst on
-- the burst itself.  What moves is the MEASURE, and that is the whole
-- content of the clause:
--
--   · the demand DROPS by one across the unfold (mu-edge: hopD is
--     EQUAL either side, syncSize strictly shrinks), and that one unit
--     pays the gas peel — the same lockstep shape subscribeInner-walk's
--     gs clause spends, but bought by the μ edge rather than the hop;
--   · the LEVEL is minted rather than descended, because the unfolding
--     is a fresh entry subscribing a LARGER term (size-unfoldμ is
--     quadratic, not a decrease) — op-step-mu opens the quadratic room
--     and mu-lvl-desc carries the L̂ ceiling into it;
--   · depth is UNCHANGED: depthE (gs fuel) (μᵉ body) is definitionally
--     depthE fuel (unfoldμ body) (.Caps-Depth), so `dpt` passes straight
--     through with no transport at all.
--
-- Three of the four clauses are absurd by CONSTRUCTOR, exactly as the
-- caps twin's are: g0 has no `hasAtLeast suc G`, `ops = 0` contradicts
-- the index hypothesis, and `bud = 0` contradicts the nesting one (a
-- μ's nest is a successor).
------------------------------------------------------------------
walk-mu body c Ψ F Ŝ R̂ G ℓ L̂ dep bud ops j g0 κ bid now sl sched st
        2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt
        invW fnC pB s2 fS rS ceil lb dmd ()
walk-mu body c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j (gs fuel) κ bid now sl sched st
        2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst () dpt
        invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs
walk-mu body c Ψ F Ŝ R̂ G ℓ L̂ dep zero (suc ops′) j (gs fuel) κ bid now sl sched st
        2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC () hidx dpt
        invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs
walk-mu {n = n} body c Ψ F Ŝ R̂ G ℓ L̂ dep (suc bud′) (suc ops′) j (gs fuel)
        κ bid now sl sched st
        2≤S 1≤R hCR slEq slC slSz inv szb wdb pC lC nst hidx dpt
        invW fnC pB s2 fS rS ceil lb dmd gas lℓ rgs =
  j₀ + j₁
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true) EQ S1
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ res) ≡ true) EQ S2
    , subst (λ x → burstCount? (frameStep x c) (proj₁ res) ≡ true) EQ S3
    -- the unfolding is a FRESH ENTRY, so its receipt is consumed at
    -- sLvlD and op-step-mu converts it — subscribeE-caps' own move
    , op-step-mu (Caps.cSize c) (Caps.cWid c) dep (suc bud′) ops′ j
        (sizeᵉ (μᵉ body)) j₁ 2≤S szb
        (≤-trans S4
                 (≤-reflexive (sym (sLvlD-suc (Caps.cSize c) (Caps.cWid c)
                                      dep bud′ (j + j₀)))))
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true) EQ S5
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ (proj₁ res) ≡ true) EQ S6
    -- the ONE wet transport this clause needs: the IH reports hops at
    -- the unfolding's index, and hopD is equal across the unfold
    , subst (λ x → burstHopD? F (slotHop F sl) x (proj₁ res) ≡ true) (hopD-unfoldμ F (slotHop F sl) body) S7
    , S8 , S9
  where
  U   = unconn sl (EvalSt.connectedShares st)
  US  = unfoldμ-caps c j sl body 2≤S slC szb wdb
  j₀  = proj₁ US
  hJ₀ : j + j₀ ≤ suc (j + suc (Caps.cSize (frameStep j c)) * suc (Caps.cSize (frameStep j c)))
  hJ₀ = ≤-trans
    (+-monoʳ-≤ j
       (≤-trans (+-mono-≤ szb (s≤s (*-mono-≤ szb szb)))
                (quad-arith (Caps.cSize (frameStep j c)))))
    (n≤1+n _)
  ⊑₀  = frameStep-⊑-+ c 2≤S j j₀
  -- the unfolding's demand: hopD equal (hopD-unfoldμ), syncSize strictly
  -- smaller (unfoldμ-shrinks) — mu-edge fuses the pair
  G′  : ℕ
  G′  = dBound Ŝ R̂ U (hopDᵉ Ŝ (slotHop Ŝ sl) (unfoldμ body)) (syncSizeᵉ (unfoldμ body))
  dmdŜ : dBound Ŝ R̂ U (hopDᵉ Ŝ (slotHop Ŝ sl) (μᵉ body)) (syncSizeᵉ (μᵉ body)) ≤ G
  dmdŜ = subst (λ x → dBound Ŝ R̂ U (hopDᵉ x (slotHop x sl) (μᵉ body))
                        (syncSizeᵉ (μᵉ body)) ≤ G) fS dmd
  sucG′≤G : suc G′ ≤ G
  sucG′≤G = ≤-trans (mu-edge Ŝ R̂ U (slotHop Ŝ sl) body) dmdŜ
  G′≤G : G′ ≤ G
  G′≤G = ≤-trans (n≤1+n G′) sucG′≤G
  IH = walkFace (unfoldμ body) c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud′
         (suc (Caps.cSize (frameStep (j + j₀) c))) (j + j₀) fuel
         κ bid now sl sched st
         2≤S 1≤R hCR slEq slC slSz
         (capsOK?-mono (frameStep j c) (frameStep (j + j₀) c) sched st ⊑₀ inv)
         (proj₁ (proj₂ US))
         (proj₂ (proj₂ US))
         (pathSz?-⊑ κ ⊑₀ pC)
         (≤-trans lC (proj₁ ⊑₀))
         (mu-step body sl _ bud′ nst)
         (s≤s (proj₁ (proj₂ US)))
         -- depthE (gs fuel) (μᵉ body) IS depthE fuel (unfoldμ body)
         dpt
         (INV?-widen sched st (proj₁ ⊑₀) invW)
         (subst (λ x → x ≤ Ψ) (sym (fnCap-unfoldμ body)) fnC)
         (pathB?-widen κ (proj₁ ⊑₀) pB)
         s2 fS rS ceil
         (≤-trans (mu-lvl-desc c dep bud′ ops′ j j₀ 2≤S hJ₀) lb)
         (subst (λ x → dBound Ŝ R̂ U (hopDᵉ x (slotHop x sl) (unfoldμ body))
                         (syncSizeᵉ (unfoldμ body)) ≤ G′) (sym fS) ≤-refl)
         (hasAtLeast-mono sucG′≤G (hasAtLeast-peel-gs gas))
         (≤-trans (+-monoʳ-≤ (pathLen κ) G′≤G) lℓ)
         rgs
  j₁  = proj₁ IH
  S1  = proj₁ (proj₂ IH)
  S2  = proj₁ (proj₂ (proj₂ IH))
  S3  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  S4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  S5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  S6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
  S7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
  S8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  S9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  res = subscribeE fuel (unfoldμ body) κ bid now sched st
  EQ  : (j + j₀) + j₁ ≡ j + (j₀ + j₁)
  EQ  = +-assoc j j₀ j₁

-- THE *All BODY — subscribeAll-caps' proven proof, step for step, with
-- the wet conjuncts threaded through.  ops splits exactly as there: at
-- zero the index hypothesis `suc (suc (sizeᵉ b)) ≤ zero` is uninhabited,
-- and the successor clause spends op-step's one operator.
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud zero j g op ns b κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv bn wn szb wdb pC lC nst ()
subscribeAll-walk c Ψ F Ŝ R̂ G ℓ L̂ dep bud (suc ops′) j g op ns b κ bid now sl sched st
  2≤S 1≤R hCR slEq slC slSz inv bn wn szb wdb pC lC nst hidx dpt invW fnC fnN pB s2 fS rS ceil lb dmd gas lℓ rgs =
  suc (j₁ + j₂)
    , subst (λ x → capsOK? (frameStep x c)
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true) EQ W1
    , subst (λ x → burstCaps? (frameStep x c) sl (proj₁ PB) ≡ true) EQ W2
    , subst (λ x → burstCount? (frameStep x c) (proj₁ PB) ≡ true) EQ W3
    -- ONE OPERATOR, spent exactly as the caps head spends it: the
    -- source's conjunct at the predecessor index, and the push face's
    -- fIterD charge converted once by burst-index
    , op-step (Caps.cSize c) (Caps.cWid c) dep bud ops′ j j₁ j₂ 2≤S S4
        (≤-trans W4 (burst-index (Caps.cSize c) (Caps.cWid c) dep bud
           (length (proj₁ res)) (suc j + j₁) (suc j + j₁) 2≤S
           (countLen (frameStep (suc j + j₁) c) (proj₁ res) S3)))
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                     (proj₁ (proj₂ PB)) (proj₂ (proj₂ PB)) ≡ true) EQ W5
    , subst (λ x → burstB? (Caps.cSize (frameStep x c)) Ψ (proj₁ PB) ≡ true) EQ W6
    -- the push face reports hop receipts AT hopDᵉ F b (the thru frame
    -- does not grow hops); the composite conjunct's suc is one widening
    , burstHopD?-widen F (slotHop F sl) (hopDᵉ F (slotHop F sl) b) (suc (hopDᵉ F (slotHop F sl) b)) (proj₁ PB)
        (n≤1+n (hopDᵉ F (slotHop F sl) b)) W7
    , W8 , W9
  where
  nid    = Sched.nextNode sched
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid ns st
  κ′     = thru-outer op nid ↠ κ
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  B′     = Caps.cSize (frameStep (suc j) c)
  U      = unconn sl (EvalSt.connectedShares st)
  -- the source's demand, one hop-step below the composite's: the spent
  -- unit pays the thru-outer path extension in ℓ exactly
  G′     = dBound Ŝ R̂ U (hopDᵉ F (slotHop F sl) b) (syncSizeᵉ b)
  sucG′≤G : suc G′ ≤ G
  sucG′≤G = ≤-trans (hop-step-gives Ŝ R̂ U (hopDᵉ F (slotHop F sl) b)
                       (suc (syncSizeᵉ b)) (syncSizeᵉ b)
                       (m≤m+n (suc (syncSizeᵉ b)) (suc Ŝ)))
                    dmd
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
  invW′ : INV? Ψ B′ sched₀ st₀ ≡ true
  invW′ = INV?-install Ψ (Caps.cSize (frameStep j c)) B′ nid ns sched sched₀ st
            (proj₁ step⊑) refl refl bn fnN invW
  SUB = walkFace b c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc j) g κ′ bid now sl sched₀ st₀
          2≤S 1≤R hCR slEq slC slSz inv₀
          (≤-trans szb (proj₁ step⊑))
          (≤-trans wdb (proj₁ (proj₂ step⊑)))
          pC′
          (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
          nst
          (chain-desc 0 (sizeᵉ b) ops′ hidx)
          (≤-trans (m≤m⊔n _ _) dpt)
          invW′ fnC
          (pathB?-widen κ (proj₁ step⊑) pB)
          s2 fS rS ceil
          (≤-trans (op-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′ j 2≤S) lb)
          ≤-refl
          (hasAtLeast-mono (≤-trans sucG′≤G (n≤1+n G)) gas)
          (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                   (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
          rgs
  j₁  = proj₁ SUB
  S1  = proj₁ (proj₂ SUB)
  S2  = proj₁ (proj₂ (proj₂ SUB))
  S3  = proj₁ (proj₂ (proj₂ (proj₂ SUB)))
  S4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))
  S5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))
  S6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))
  S7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB)))))))
  S8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  S9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SUB))))))))
  res = subscribeE g b κ′ bid now sched₀ st₀
  KP  = subscribeE-keeps g b κ′ bid now sched₀ st₀
  sl₂eq : Sched.slots (proj₁ (proj₂ res)) ≡ sl
  sl₂eq = trans (KeepsC.slotsEq KP) slEq
  -- shares only connect during the walk, so the caller's unconn count
  -- weakens to the post-walk one
  UK : unconn sl (EvalSt.connectedShares (proj₂ (proj₂ res))) ≤ U
  UK = subst₂ (λ y z → unconn y (EvalSt.connectedShares (proj₂ (proj₂ res)))
                         ≤ unconn z (EvalSt.connectedShares st))
              sl₂eq slEq
              (unconn-keeps sched₀ st₀ (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) KP)
  PBW = pushThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U (hopDᵉ F (slotHop F sl) b) (suc (syncSizeᵉ b))
          dep bud (suc j + j₁) g bid now op nid
          κ (proj₁ res) sl (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
          2≤S 1≤R hCR sl₂eq slC slSz
          S1
          (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S (suc j) j₁) (pathSz?-⊑ κ step⊑ pC))
          (≤-trans (≤-trans lC (proj₁ step⊑))
                   (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁)))
          S2 S3
          (≤-trans (m≤n⊔m _ _) dpt)
          S5
          (pathB?-widen κ
             (≤-trans (proj₁ step⊑) (proj₁ (frameStep-⊑-+ c 2≤S (suc j) j₁))) pB)
          S6 S7 S8
          s2 fS rS ceil
          (≤-trans (push-desc (Caps.cSize c) (Caps.cWid c) dep bud ops′
                      (length (proj₁ res)) j j₁ 2≤S S4
                      (countLen (frameStep (suc j + j₁) c) (proj₁ res) S3))
                   lb)
          UK dmd gas lℓ S9
  j₂  = proj₁ PBW
  W1  = proj₁ (proj₂ PBW)
  W2  = proj₁ (proj₂ (proj₂ PBW))
  W3  = proj₁ (proj₂ (proj₂ (proj₂ PBW)))
  W4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))
  W5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW)))))
  W6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))
  W7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW)))))))
  W8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))))
  W9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ PBW))))))))
  PB  = pushBurst g bid now (thru-outer op nid) κ (proj₁ res)
          (proj₁ (proj₂ res)) (proj₂ (proj₂ res))
  EQ : (suc j + j₁) + j₂ ≡ j + suc (j₁ + j₂)
  EQ = trans (cong suc (+-assoc j j₁ j₂)) (sym (+-suc j (j₁ + j₂)))

------------------------------------------------------------------
-- THE LEAF, GROUND — subscribeInner-caps' two clauses ⊗ the wet
-- content.  g0: the gas hypothesis `g0 hasAtLeast suc G` has no
-- constructor, so the evaluator's one remaining dry mint is
-- unreachable by type and the whole clause is absurd.  gs: THE
-- LOCKSTEP, in the telescope at last — one r-drop of the demand
-- (hop-edge's arithmetic, spelled with hop-step-gives and the two
-- dBound monos) funds the gas peel AND the from-inner frame's ℓ
-- extension, the same single unit subscribeAll-walk's body already
-- spends on the thru-outer frame.  The inner run is the mutual
-- walkFace at the PEELED fuel — the caps twin's own induction
-- (subscribeInner-caps → subscribeE-caps, .Subscribe-Face) — and the
-- vs/bs receipts come back through the splitBurst square: caps twins
-- from .Subscribe-Face, wet vals from splitBurst-vals-B, hop from
-- splitBurst-vals-hop, dry from splitBurst-nodry, regs verbatim.
------------------------------------------------------------------
subscribeInner-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g0 op allNid κ bid now o
                    sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
                    invW vB pB hR s2 fS rS ceil lb hU dmd ()
subscribeInner-walk {n = n} {Γ = Γ} {t = t} {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ
                    dep bud j (gs fuel) op allNid κ bid now o sl sched st
                    2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
                    invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs =
  suc (suc (suc j₂)) , R1 , R2 , R3
    , inner-step (Caps.cSize c) (Caps.cWid c) dep bud j j₂ 2≤S S4
    , R5 , R6 , R7 , R8 , S9
  where
  S      = Caps.cSize c
  W      = Caps.cWid c
  B      = Caps.cSize (frameStep j c)
  B′     = Caps.cSize (frameStep (suc j) c)
  step⊑  = frameStep-mono-j c 2≤S (n≤1+n j)
  sched₀ = record sched { nextNode = suc (Sched.nextNode sched) }
  κ′     = from-inner op allNid (Sched.nextNode sched) ↠ κ
  szo    : sizeᵉ o ≤ B
  szo    = ≤ᵇ⇒≤ (sizeᵛ (obs u) o) B (T-to (proj₁ (∧-true _ _ vC)))
  wdo    : dWᵉ n sl o ≤ Caps.cWid (frameStep j c)
  wdo    = ≤-trans (m≤n⊔m _ (dWᵉ n sl o))
                   (≤ᵇ⇒≤ (pWᵛ n sl (obs u) o) (Caps.cWid (frameStep j c))
                         (T-to (valCaps?-wid (frameStep j c) sl (obs u) o vC)))
  pC′    : pathSz? B′ κ′ ≡ true
  pC′    = ∧-intro refl
             (∧-intro (T⇒≡true (suc (pathLen κ) ≤ᵇ B′)
                        (≤⇒≤ᵇ (≤-trans lC (proj₁ step⊑))))
                      (pathSz?-⊑ κ step⊑ pC))
  inv₀ : capsOK? (frameStep (suc j) c) sched₀ st ≡ true
  inv₀ = capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched₀ st step⊑
           (capsOK?-nextNode (frameStep j c) (suc (Sched.nextNode sched))
                             sched st inv)
  -- the nextNode bump is invisible to INV? (it reads live and slots,
  -- both definitionally unchanged by the record update)
  invW′ : INV? Ψ B′ sched₀ st ≡ true
  invW′ = INV?-widen sched₀ st (proj₁ step⊑) invW
  fnCo : fnCapᵉ o ≤ Ψ
  fnCo = ≤ᵇ⇒≤ (fnCapᵉ o) Ψ (T-to (proj₂ (∧-true (sizeᵛ (obs u) o ≤ᵇ B)
                                                (fnCapᵛ (obs u) o ≤ᵇ Ψ) vB)))
  pB′ : pathB? B′ Ψ κ′ ≡ true
  pB′ = ∧-intro refl (pathB?-widen κ (proj₁ step⊑) pB)
  -- the level index never outruns its own budget, so the size receipt
  -- reaches the anchor through the ceiling
  j≤L̂ : j ≤ L̂
  j≤L̂ = ≤-trans (n≤1+n j)
                (≤-trans (sLvlD-infl S W dep (suc bud) (suc j)) lb)
  szŜ : sizeᵛ (obs u) o ≤ Ŝ
  szŜ = ≤-trans szo (≤-trans (proj₁ (frameStep-mono-j c 2≤S j≤L̂)) ceil)
  -- THE LOCKSTEP UNIT: the r-drop from suc r̂ to the inner's own hop
  -- rank funds one gas peel and one path frame, exactly
  G′ = dBound Ŝ R̂ (unconn sl (EvalSt.connectedShares st))
              (hopDᵉ F (slotHop F sl) o) (syncSizeᵉ o)
  sucG′≤G : suc G′ ≤ G
  sucG′≤G =
    ≤-trans (s≤s (≤-trans (dBound-mono-U Ŝ R̂ (hopDᵉ F (slotHop F sl) o) (syncSizeᵉ o) hU)
                          (dBound-mono-r Ŝ R̂ U (syncSizeᵉ o) hR)))
            (≤-trans (hop-step-gives Ŝ R̂ U r̂ ŝ (syncSizeᵉ o)
                        (≤-trans (s≤s (≤-trans (syncSize≤sizeᵉ o) szŜ))
                                 (m≤n+m (suc Ŝ) ŝ)))
                     dmd)
  ops′ = Caps.cSize (frameStep (suc j) c)
  budg : opIterD S W dep bud ops′ (suc j) ≤ L̂
  budg = ≤-trans (≤-trans (opIterD-mono ops′ (suc ops′) dep dep bud bud
                             2≤S ≤-refl ≤-refl ≤-refl ≤-refl ≤-refl
                             (n≤1+n ops′))
                          (≤-reflexive (sym (sLvlD-suc S W dep bud (suc j)))))
                 lb
  IH = walkFace o c Ψ F Ŝ R̂ G′ ℓ L̂ dep bud ops′ (suc j) fuel κ′ bid now
         sl sched₀ st
         2≤S 1≤R hCR slEq slC slSz inv₀
         (≤-trans szo (proj₁ step⊑))
         (≤-trans wdo (proj₁ (proj₂ step⊑)))
         pC′
         (frameStep-chain-suc c j (pathLen κ) 2≤S lC)
         nst
         (frameStep-size-strict-suc c j (sizeᵉ o) (≤-trans (s≤s z≤n) 2≤S) szo)
         dpt
         invW′ fnCo pB′
         s2 fS rS ceil budg
         ≤-refl
         (hasAtLeast-mono sucG′≤G (hasAtLeast-peel-gs gas))
         (≤-trans (≤-reflexive (sym (+-suc (pathLen κ) G′)))
                  (≤-trans (+-monoʳ-≤ (pathLen κ) sucG′≤G) lℓ))
         rgs
  j₂  = proj₁ IH
  S1  = proj₁ (proj₂ IH)
  S2  = proj₁ (proj₂ (proj₂ IH))
  S3  = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  S4  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  S5  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  S6  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
  S7  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
  S8  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  S9  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  res   = subscribeE fuel o κ′ bid now sched₀ st
  burst = proj₁ res
  VS    = proj₁ (splitBurst {A = Val Γ t} burst)
  BS    = proj₁ (proj₂ (splitBurst {A = Val Γ t} burst))
  L₀ = suc j + j₂
  C₀ = frameStep L₀ c
  C₃ = frameStep (suc (suc L₀)) c
  ⊑₂ = frameStep-mono-j c 2≤S {L₀} {suc (suc L₀)}
         (≤-trans (n≤1+n L₀) (n≤1+n (suc L₀)))
  lvl : j + suc (suc (suc j₂)) ≡ suc (suc (suc (j + j₂)))
  lvl = trans (+-suc j (suc (suc j₂)))
          (trans (cong suc (+-suc j (suc j₂)))
                 (cong suc (cong suc (+-suc j j₂))))
  LENV : length VS ≤ suc (Caps.cWid C₃)
  LENV = ≤-trans (splitBurst-len {u = t} (suc (Caps.cWid C₀)) burst
                    (countVals C₀ burst S3))
                 (mul-fits c L₀ (length burst) (suc (Caps.cWid C₀)) 2≤S
                    (countLen C₀ burst S3) ≤-refl)
  R1 : capsOK? (frameStep (j + suc (suc (suc j₂))) c)
                (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true
  R1 = subst (λ x → capsOK? (frameStep x c)
                      (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
             (sym lvl)
             (capsOK?-mono C₀ C₃ (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ⊑₂ S1)
  R2 : valsCaps? (frameStep (j + suc (suc (suc j₂))) c) sl VS ≡ true
  R2 = subst (λ x → valsCaps? (frameStep x c) sl VS ≡ true) (sym lvl)
             (valsIn C₃ sl VS
                (splitBurst-vals-caps {s = u} {u = t} C₃ sl burst
                   (burstCaps?-widen sl burst ⊑₂ S2))
                LENV)
  R3 : all (eventCaps? (frameStep (j + suc (suc (suc j₂))) c) sl) BS ≡ true
  R3 = subst (λ x → all (eventCaps? (frameStep x c) sl) BS ≡ true)
             (sym lvl)
             (splitBurst-bk-caps {s = u} {u = t} C₃ sl burst)
  R5 : INV? Ψ (Caps.cSize (frameStep (j + suc (suc (suc j₂))) c))
             (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true
  R5 = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c))
                        (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) ≡ true)
             (sym lvl)
             (INV?-widen (proj₁ (proj₂ res)) (proj₂ (proj₂ res)) (proj₁ ⊑₂) S5)
  R6 : all (valB? (Caps.cSize (frameStep (j + suc (suc (suc j₂))) c)) Ψ u)
           VS ≡ true
  R6 = subst (λ x → all (valB? (Caps.cSize (frameStep x c)) Ψ u) VS ≡ true)
             (sym lvl)
             (splitBurst-vals-B {s = u} {u = t} (Caps.cSize C₃) Ψ burst
                (burstB?-widen burst (proj₁ ⊑₂) S6))
  R7 : all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) VS ≡ true
  R7 = splitBurst-vals-hop {s = u} {u = t} F (slotHop F sl) r̂ burst
         (burstHopD?-widen F (slotHop F sl) (hopDᵉ F (slotHop F sl) o) r̂ burst hR S7)
  R8 : any dryEvent BS ≡ false
  R8 = splitBurst-nodry burst S8

------------------------------------------------------------------
-- ONE PAYLOAD — thruConsume-caps' clauses ⊗ the wet content.  mergeAll
-- subscribes and bumps while a lane is free and parks when none is;
-- switch cuts then subscribes; exhaust drops while busy.  Every node
-- write goes through INV?-setNode/-mergeAllBump; switch's registry cut
-- goes through the cutThrough kit above.
------------------------------------------------------------------
thruConsume-walk {n = n} {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g mergeAllᵒ
                 nid κ bid now o sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC
                 lC nst dpt invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-caps (frameStep j c) (Sched.slots sched) nid (EvalSt.nodes st)
         (capsOK?-nodeSz (frameStep j c) sched st inv)
         (capsOK?-nodeWid (frameStep j c) sched st inv)
     | lookupNode-B (Caps.cSize (frameStep j c)) Ψ nid (EvalSt.nodes st)
         (proj₂ (∧-true (all (boundedLive (Caps.cSize (frameStep j c)))
                             (Sched.live sched))
                        (all (λ kv → boundedNode (Caps.cSize (frameStep j c))
                                       (proj₂ kv)) (EvalSt.nodes st))
                        (proj₁ (INV-parts Ψ (Caps.cSize (frameStep j c))
                                  sched st invW))))
         (proj₂ (∧-true (all (fnCapLive Ψ) (Sched.live sched))
                        (all (λ kv → fnCapNode Ψ (proj₂ kv)) (EvalSt.nodes st))
                        (proj₁ (proj₂ (INV-parts Ψ (Caps.cSize (frameStep j c))
                                         sched st invW)))))
... | nothing                | _ | _ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (scan-st _)       | _ | _ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (take-st _)       | _ | _ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (switch-st _ _)   | _ | _ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (exhaust-st _ _)  | _ | _ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (mergeAll-st {w} lim act q od) | (bn , wn) | (bnW , fnW) with w ≟ᵗ u
...   | no _ =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
            (sym (+-identityʳ j)) invW
    , refl , refl , refl , rgs
-- A LANE IS FREE — subscribe and bump the live count.  This is where
-- the merge face's whole clause went: its node write was the bump and
-- nothing else, which is exactly what the gate's true arm does now
...   | yes refl with hasRoom lim act
...     | true =
  j′ , capsOK?-mergeAllBump (frameStep (j + j′) c) nid done sd₁ st₁ S1
     , proj₁ (proj₂ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ (proj₂ SI)))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI))))
     , mergeAllBump-INV Ψ (Caps.cSize (frameStep (j + j′) c)) nid done sd₁ st₁
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))))
     , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))))
  where
  SI = subscribeInner-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g mergeAllᵒ nid κ
         bid now o sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
         invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs
  j′   = proj₁ SI
  S1   = proj₁ (proj₂ SI)
  R    = subscribeInner g mergeAllᵒ nid κ bid now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ R)))
  sd₁  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R))))
  st₁  = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R))))
-- THE PARK — the one write that grows the queue.  The caps side is the
-- caps clause verbatim; the wet side's queue bound comes from the
-- state's own INV? through the lookup (fnW), extended with the
-- payload's valB? receipt, which is level-free on the Ψ half
...     | false =
  1 , subst (λ x → capsOK? (frameStep x c) sched st₊ ≡ true) (sym lvl1) capsPark
    , refl , refl
    , queue-push (Caps.cSize c) (Caps.cWid c) dep (suc bud) j (s≤s z≤n)
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st₊ ≡ true)
            (sym lvl1) invPark
    , refl , refl , refl , rgs
  where
  st₊ = record st { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                              (EvalSt.nodes st) }
  lvl1 : j + 1 ≡ suc j
  lvl1 = +-comm j 1
  BN = all-++-intro (λ x → sizeᵉ x ≤ᵇ Caps.cSize (frameStep (suc j) c)) q (o ∷ [])
         (all-impl _ _ (λ x → ≤ᵇ-widen (sizeᵉ x)
                                (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))) q bn)
         (∧-intro (≤ᵇ-widen (sizeᵉ o) (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j)))
                    (valCaps?-size (frameStep j c) sl (obs u) o vC))
                  refl)
  WN = widNode-push c j (Sched.slots sched) lim q o act od 2≤S wn
         (subst (λ y → (pWᵉ n y o ≤ᵇ Caps.cWid (frameStep j c)) ≡ true)
                (sym slEq) (valCaps?-wid (frameStep j c) sl (obs u) o vC))
  capsPark = capsOK?-setNode (frameStep (suc j) c)
               nid (mergeAll-st lim act (q ++ o ∷ []) od)
               sched st BN WN
               (capsOK?-mono (frameStep j c) (frameStep (suc j) c) sched st
                  (frameStep-mono-j c 2≤S (n≤1+n j)) inv)
  FN : fnCapNode Ψ (mergeAll-st lim act (q ++ o ∷ []) od) ≡ true
  FN = all-++-intro (λ x → fnCapᵉ x ≤ᵇ Ψ) q (o ∷ []) fnW
         (∧-intro (proj₂ (∧-true (sizeᵛ (obs u) o ≤ᵇ Caps.cSize (frameStep j c))
                                 (fnCapᵛ (obs u) o ≤ᵇ Ψ) vB))
                  refl)
  invPark = INV?-setNode Ψ (Caps.cSize (frameStep (suc j) c))
              nid (mergeAll-st lim act (q ++ o ∷ []) od) sched st BN FN
              (INV?-widen sched st
                 (proj₁ (frameStep-mono-j c 2≤S (n≤1+n j))) invW)

thruConsume-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g switchᵒ nid κ bid now o
                 sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
                 invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs
  with lookupNode nid (EvalSt.nodes st) | dpt
... | nothing                | dpt′ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (scan-st _)       | dpt′ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (take-st _)       | dpt′ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (mergeAll-st _ _ _ _) | dpt′ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (exhaust-st _ _)  | dpt′ =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
-- THE CUT — the caps clause verbatim on its side; on the wet side the
-- registry filter and the live sweep go through the cutThrough kit,
-- and the closes it prepends are dry-free by construction
... | just (switch-st cur od) | dpt′ =
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
         (proj₁ (proj₂ (proj₂ (proj₂ SI))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI))))
     , INV?-setNode Ψ (Caps.cSize (frameStep (j + j′) c)) nid
         (switch-st (if proj₁ (proj₂ (proj₂ (proj₂ R))) then nothing
                     else just (proj₁ R)) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))))
     , any-++-false dryEvent (proj₁ KILL) _
         (switchKill-closes-nodry cur sched st)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))))))
     , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))))
  where
  KILL   = switchKill cur sched st
  sched₁ = proj₁ (proj₂ KILL)
  st₁    = proj₂ (proj₂ KILL)
  hU′ : unconn sl (EvalSt.connectedShares st₁) ≤ U
  hU′ = ≤-trans
          (subst₂ (λ y z → unconn y (EvalSt.connectedShares st₁)
                             ≤ unconn z (EvalSt.connectedShares st))
                  (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq)
                  slEq
                  (unconn-keeps sched st sched₁ st₁
                     (switchKill-keeps cur sched st)))
          hU
  SI = subscribeInner-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g switchᵒ nid κ
         bid now o sl sched₁ st₁ 2≤S 1≤R hCR
         (trans (KeepsC.slotsEq (switchKill-keeps cur sched st)) slEq) slC slSz
         (switchKill-caps (frameStep j c) cur sched st inv) vC pC lC
         (nest-keeps o sl _ _ bud
            (KeepsC.connMono (switchKill-keeps cur sched st)) nst)
         dpt′
         (INV?-switchKill Ψ (Caps.cSize (frameStep j c)) cur sched st invW)
         vB pB hR s2 fS rS ceil lb
         hU′ dmd gas lℓ
         (switchKill-regsLen ℓ cur sched st rgs)
  j′ = proj₁ SI
  R  = subscribeInner g switchᵒ nid κ bid now o sched₁ st₁

thruConsume-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g exhaustᵒ nid κ bid now o
                 sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
                 invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs
  with lookupNode nid (EvalSt.nodes st)
... | nothing                =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (scan-st _)       =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (take-st _)       =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (mergeAll-st _ _ _ _) =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (switch-st _ _)   =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (exhaust-st true od)  =
  0 , ZI , refl , refl , inner-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , ZW , refl , refl , refl , rgs
  where
  ZI = subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
             (sym (+-identityʳ j)) inv
  ZW = subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
             (sym (+-identityʳ j)) invW
... | just (exhaust-st false od) =
  j′ , capsOK?-setNode (frameStep (j + j′) c) nid
         (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ R))))) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl (proj₁ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ SI))
     , proj₁ (proj₂ (proj₂ (proj₂ SI)))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ SI))))
     , INV?-setNode Ψ (Caps.cSize (frameStep (j + j′) c)) nid
         (exhaust-st (not (proj₁ (proj₂ (proj₂ (proj₂ R))))) od)
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ R)))))
         refl refl
         (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI)))))))
     , proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))))
     , proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ SI))))))))
  where
  SI = subscribeInner-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g exhaustᵒ nid κ
         bid now o sl sched st 2≤S 1≤R hCR slEq slC slSz inv vC pC lC nst dpt
         invW vB pB hR s2 fS rS ceil lb hU dmd gas lℓ rgs
  j′ = proj₁ SI
  R  = subscribeInner g exhaustᵒ nid κ bid now o sched st

------------------------------------------------------------------
-- THE WALK — thruWalk-caps ⊗ the wet content: one payload at a time,
-- the head through thruConsume-walk, the tail from the stepped state,
-- receipts re-established from the head's own Σ and the Keeps ring
------------------------------------------------------------------
thruWalk-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g op nid κ bid now []
              sl sched st 2≤S 1≤R hCR slEq slC slSz inv pC vC lC nst dpt
              invW pB vBs hops s2 fS rS ceil lb hU dmd gas lℓ rgs =
  0 , subst (λ x → capsOK? (frameStep x c) sched st ≡ true)
            (sym (+-identityʳ j)) inv
    , refl , refl , walk-nil (Caps.cSize c) (Caps.cWid c) dep (suc bud) j
    , subst (λ x → INV? Ψ (Caps.cSize (frameStep x c)) sched st ≡ true)
            (sym (+-identityʳ j)) invW
    , refl , refl , refl , rgs
thruWalk-walk {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g op nid κ bid now
              (o ∷ os) sl sched st 2≤S 1≤R hCR slEq slC slSz inv pC vC lC nst dpt
              invW pB vBs hops s2 fS rS ceil lb hU dmd gas lℓ rgs =
  suc (j₁ + j₂)
    , capsOK?-mono (frameStep ((j + j₁) + j₂) c) (frameStep (j + suc (j₁ + j₂)) c)
        (proj₁ (proj₂ (proj₂ REST))) (proj₂ (proj₂ (proj₂ REST)))
        ⊑ˢ W1
    , valsIn (frameStep (j + suc (j₁ + j₂)) c) sl (proj₁ TC ++ proj₁ REST)
        (valsCaps?-widen sl u (proj₁ TC ++ proj₁ REST) ⊑ˢ
           (all-++-intro (valCaps? (frameStep ((j + j₁) + j₂) c) sl u)
              (proj₁ TC) (proj₁ REST)
              (valsCaps?-widen sl u (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                 (valsOf (frameStep (j + j₁) c) sl (proj₁ TC) H2))
              (valsOf (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST) W2)))
        (subst (λ x → length (proj₁ TC ++ proj₁ REST)
                        ≤ suc (Caps.cWid (frameStep x c)))
               (sym lvlW)
               (concat-fits c ((j + j₁) + j₂) (proj₁ TC) (proj₁ REST) 2≤S
                  (lenWiden (proj₁ TC) (frameStep-⊑-+ c 2≤S (j + j₁) j₂)
                     (valsLen (frameStep (j + j₁) c) sl (proj₁ TC) H2))
                  (valsLen (frameStep ((j + j₁) + j₂) c) sl (proj₁ REST) W2)))
    , eventsCaps?-widen sl (proj₁ (proj₂ TC) ++ proj₁ (proj₂ REST)) ⊑ˢ
        (all-++-intro (eventCaps? (frameStep ((j + j₁) + j₂) c) sl)
           (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST))
           (eventsCaps?-widen sl (proj₁ (proj₂ TC))
              (frameStep-⊑-+ c 2≤S (j + j₁) j₂) H3)
           W3)
    , walk-step-suc (Caps.cSize c) (Caps.cWid c) dep (suc bud) (length os)
        j j₁ j₂ 2≤S H4 W4
    , INV?-widen (proj₁ (proj₂ (proj₂ REST))) (proj₂ (proj₂ (proj₂ REST)))
        (proj₁ ⊑ˢ) W5
    , valsB?-widen u (proj₁ TC ++ proj₁ REST) (proj₁ ⊑ˢ)
        (all-++-intro (valB? (Caps.cSize (frameStep ((j + j₁) + j₂) c)) Ψ u)
           (proj₁ TC) (proj₁ REST)
           (valsB?-widen u (proj₁ TC)
              (proj₁ (frameStep-⊑-+ c 2≤S (j + j₁) j₂)) H6)
           W6)
    , all-++-intro (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) (proj₁ TC) (proj₁ REST) H7 W7
    , any-++-false dryEvent (proj₁ (proj₂ TC)) (proj₁ (proj₂ REST)) H8 W8
    , W9
  where
  vCa = valsOf (frameStep j c) sl (o ∷ os) vC
  vBh = ∧-true (valB? (Caps.cSize (frameStep j c)) Ψ (obs u) o)
               (all (valB? (Caps.cSize (frameStep j c)) Ψ (obs u)) os) vBs
  hph = ∧-true (hopDᵛ F (slotHop F sl) (obs u) o ≤ᵇ r̂)
               (all (λ x → hopDᵛ F (slotHop F sl) (obs u) x ≤ᵇ r̂) os) hops
  TC  = thruConsume g op nid κ bid now o sched st
  sd₁ = proj₁ (proj₂ (proj₂ TC))
  st₁ = proj₂ (proj₂ (proj₂ TC))
  TCK = thruConsume-keeps g op nid κ bid now o sched st
  HD = thruConsume-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud j g op nid κ bid now o
         sl sched st 2≤S 1≤R hCR slEq slC slSz inv
         (proj₁ (∧-true _ _ vCa)) pC lC
         (mList?-head bud sl _ o os nst)
         (≤-trans (m≤m⊔n
            (depthConsume g op nid κ bid now o sched st)
            (depthWalk g op nid κ bid now os sd₁ st₁)) dpt)
         invW (proj₁ vBh) pB
         (≤ᵇ⇒≤ (hopDᵛ F (slotHop F sl) (obs u) o) r̂ (T-to (proj₁ hph)))
         s2 fS rS ceil
         (≤-trans (walk-desc (Caps.cSize c) (Caps.cWid c) dep (suc bud)
                     (length os) j) lb)
         hU dmd gas lℓ rgs
  j₁ = proj₁ HD
  H1 = proj₁ (proj₂ HD)
  H2 = proj₁ (proj₂ (proj₂ HD))
  H3 = proj₁ (proj₂ (proj₂ (proj₂ HD)))
  H4 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ HD))))
  H5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ HD)))))
  H6 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ HD))))))
  H7 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ HD)))))))
  H8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ HD))))))))
  H9 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ HD))))))))
  hU′ : unconn sl (EvalSt.connectedShares st₁) ≤ U
  hU′ = ≤-trans
          (subst₂ (λ y z → unconn y (EvalSt.connectedShares st₁)
                             ≤ unconn z (EvalSt.connectedShares st))
                  (trans (KeepsC.slotsEq TCK) slEq) slEq
                  (unconn-keeps sched st sd₁ st₁ TCK))
          hU
  TAILPIN : sIterD (Caps.cSize c) (Caps.cWid c) dep (suc bud)
              (length os) (j + j₁) ≤ L̂
  TAILPIN = ≤-trans
              (≤-trans (sIterD-mono (length os) (length os) dep dep
                          (suc bud) (suc bud) 2≤S ≤-refl ≤-refl
                          (≤-trans (n≤1+n (j + j₁)) H4) ≤-refl ≤-refl ≤-refl)
                       (≤-reflexive (sym (sIterD-suc (Caps.cSize c)
                          (Caps.cWid c) dep (suc bud) (length os) j))))
              lb
  IH = thruWalk-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep bud (j + j₁) g op nid κ bid now
         os sl sd₁ st₁
         2≤S 1≤R hCR (trans (KeepsC.slotsEq TCK) slEq) slC slSz
         H1
         (pathSz?-⊑ κ (frameStep-⊑-+ c 2≤S j j₁) pC)
         (valsIn (frameStep (j + j₁) c) sl os
            (valsCaps?-widen sl (obs u) os (frameStep-⊑-+ c 2≤S j j₁)
               (proj₂ (∧-true _ _ vCa)))
            (lenWiden os (frameStep-⊑-+ c 2≤S j j₁)
               (≤-trans (n≤1+n (length os))
                        (valsLen (frameStep j c) sl (o ∷ os) vC))))
         (≤-trans lC (proj₁ (frameStep-⊑-+ c 2≤S j j₁)))
         (mList?-keeps bud sl _ _ os
            (KeepsC.connMono TCK)
            (mList?-tail bud sl _ o os nst))
         (≤-trans (m≤n⊔m
            (depthConsume g op nid κ bid now o sched st)
            (depthWalk g op nid κ bid now os sd₁ st₁)) dpt)
         H5
         (pathB?-widen κ (proj₁ (frameStep-⊑-+ c 2≤S j j₁)) pB)
         (valsB?-widen (obs u) os (proj₁ (frameStep-⊑-+ c 2≤S j j₁))
            (proj₂ vBh))
         (proj₂ hph)
         s2 fS rS ceil
         TAILPIN
         hU′ dmd gas lℓ H9
  j₂ = proj₁ IH
  W1 = proj₁ (proj₂ IH)
  W2 = proj₁ (proj₂ (proj₂ IH))
  W3 = proj₁ (proj₂ (proj₂ (proj₂ IH)))
  W4 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ IH))))
  W5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))
  W6 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))
  W7 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH)))))))
  W8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  W9 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ IH))))))))
  REST = thruWalk g op nid κ bid now os sd₁ st₁
  ⊑ˢ   = frameStep-+suc c j j₁ j₂ 2≤S
  lvlW : j + suc (j₁ + j₂) ≡ suc ((j + j₁) + j₂)
  lvlW = trans (+-suc j (j₁ + j₂)) (cong suc (sym (+-assoc j j₁ j₂)))

------------------------------------------------------------------
-- THE FRAME — stepFrame-caps' thru-outer clause ⊗ the wet content.
-- The depth fuel splits here and only here: at zero the mirror's suc
-- makes the clause unreachable; at suc the walk runs one level lower
-- at the REFRESHED budget, and the wrap's bookkeeping is crossed with
-- thruWrap-caps (caps), thruWrap-INV (wet), and the pass-through
-- equalities (vals/events/registry)
------------------------------------------------------------------
stepThru-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ zero bud j g bid now op nid κ vals fin
              sl sched st 2≤S 1≤R hCR slEq slC slSz inv pC lC vC fb ()
stepThru-walk {u = u} c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ (suc dep′) bud j g bid now op nid
              κ vals fin sl sched st 2≤S 1≤R hCR slEq slC slSz inv pC lC vC fb dpt
              invW pB vBs hops s2 fS rS ceil lb hU dmd gas lℓ rgs =
  j′ , proj₁ WR
     , valsIn (frameStep (j + j′) c) sl (proj₁ (thruWrap op nid fin WK))
         (proj₁ (proj₂ WR))
         (subst (λ x → length x ≤ suc (Caps.cWid (frameStep (j + j′) c)))
                (sym (thruWrap-vals op nid fin WK))
                (valsLen (frameStep (j + j′) c) sl (proj₁ WK) T2))
     , proj₂ (proj₂ WR)
     , frame-step (Caps.cSize c) (Caps.cWid c) dep′ j 0 j′ 2≤S z≤n
         (subst (λ x → x + j′
                         ≤ sIterD (Caps.cSize c) (Caps.cWid c) dep′
                             (frameBud c j) (suc (Caps.cWid (frameStep j c))) x)
                (sym (+-identityʳ j))
                (≤-trans T4
                   (walk-index (Caps.cSize c) (Caps.cWid c) dep′ (frameBud c j)
                      (length vals) j j 2≤S
                      (valsLen (frameStep j c) sl vals vC))))
     , thruWrap-INV Ψ (Caps.cSize (frameStep (j + j′) c)) op nid fin WK T5
     , subst (λ x → all (valB? (Caps.cSize (frameStep (j + j′) c)) Ψ u) x
                      ≡ true)
             (sym (thruWrap-vals op nid fin WK)) T6
     , subst (λ x → all (λ v → hopDᵛ F (slotHop F sl) u v ≤ᵇ r̂) x ≡ true)
             (sym (thruWrap-vals op nid fin WK)) T7
     , subst (λ x → any dryEvent x ≡ false)
             (sym (proj₁ (thruWrap-pass op nid fin WK))) T8
     , subst (λ x → regsLen? ℓ x ≡ true)
             (sym (proj₂ (thruWrap-pass op nid fin WK))) T9
  where
  WALKPIN : sIterD (Caps.cSize c) (Caps.cWid c) dep′
              (suc (sizeAt (Caps.cSize c) (suc j))) (length vals) j ≤ L̂
  WALKPIN = ≤-trans
              (≤-trans (sIterD-mono (length vals)
                          (suc (widAt (Caps.cSize c) (Caps.cWid c) j))
                          dep′ dep′
                          (suc (sizeAt (Caps.cSize c) (suc j)))
                          (suc (sizeAt (Caps.cSize c) (suc j)))
                          2≤S ≤-refl ≤-refl
                          (m≤m+n j _)
                          ≤-refl ≤-refl
                          (valsLen (frameStep j c) sl vals vC))
                       (≤-reflexive (sym (fLvlD-suc (Caps.cSize c)
                          (Caps.cWid c) dep′ j))))
              lb
  TW = thruWalk-walk c Ψ F Ŝ R̂ G ℓ L̂ U r̂ ŝ dep′
         (sizeAt (Caps.cSize c) (suc j)) j g op nid κ bid now vals
         sl sched st
         2≤S 1≤R hCR slEq slC slSz inv pC vC lC
         (valsCaps→mList-strict c j sl _ vals (≤-trans (s≤s z≤n) 2≤S) slSz
            (valsOf (frameStep j c) sl vals vC))
         (≤-pred dpt)
         invW pB vBs hops s2 fS rS ceil
         WALKPIN
         hU dmd gas lℓ rgs
  j′ = proj₁ TW
  T1 = proj₁ (proj₂ TW)
  T2 = proj₁ (proj₂ (proj₂ TW))
  T3 = proj₁ (proj₂ (proj₂ (proj₂ TW)))
  T4 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ TW))))
  T5 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ TW)))))
  T6 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ TW))))))
  T7 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ TW)))))))
  T8 = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ TW))))))))
  T9 = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ TW))))))))
  WK = thruWalk g op nid κ bid now vals sched st
  WR = thruWrap-caps (frameStep (j + j′) c) op nid fin sl WK
         T1
         (valsOf (frameStep (j + j′) c) sl (proj₁ WK) T2)
         T3

-- EX-POSTULATE: the core is the dispatch.  Its 21 route
-- hypotheses are bound and awaiting their clauses — each clause
-- postulate's header names the ones expected to pay it, and a clause
-- grind spends them from module scope, shedding nothing here until the
-- family is real.
subscribeE-walk-level-core : WalkLevelCore
subscribeE-walk-level-core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = walkFace

subscribeE-walk-level : WalkLevel
subscribeE-walk-level =
  subscribeE-walk-level-core
    mu-edge hop-edge connect-edge hop-step-gives hop-step-needs unconn-keeps
    sharedConnect-unconn obs-slot-shared
    -- these two must be instantiated EXPLICITLY: `splitBurst` computes on
    -- the literal event list, so the reduced statement no longer mentions
    -- Γ or u and Agda cannot solve those implicits from the expected type.
    (λ {n} {Γ} {u} {A} → share-live-novals {n} {Γ} {u} {A})
    (λ {n} {Γ} {u} {A} → share-spent-novals {n} {Γ} {u} {A})
    hasAtLeast-pad hasAtLeast-peel seed-covers budget-covers oneShot-tail-dry
    connect-anchor hopD-map-emit applyFn-size unconn-cons-≤
    shellSize-unfoldμ inner-unfoldμ walk-desc inner-desc

-- THE OUTER WET FACE, as a type.
WetOuter : Set
WetOuter =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     pathSz? B κ ≡ true →
     suc (pathLen κ) ≤ B →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ (slotHop Ŝ sl) b) (syncSizeᵉ b)) →
     capsOK? (capsAt e sl id) sched st ≡ true →
     dWᵉ n sl b ≤ Caps.cWid (capsAt e sl id) →
     3 + nest b sl (EvalSt.connectedShares st) ≤ B →       -- nestOK
     suc (sizeᵉ b) ≤ B →                                   -- opsOK
     depthE g b κ id now sched st ≤ capsH e sl id →        -- depOK
     let r = subscribeE g b κ id now sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

------------------------------------------------------------------
-- THE OUTER FACE, ASSEMBLED — ex-postulate.
--
-- `subscribeE-wet-core` used to be a postulate over the walk face and
-- 19 route lemmas.  Writing the assembly showed it is pure PLUMBING:
-- instantiate the walk at the entry caps and lift its landing.  The
-- instantiation is
--
--   c := capsAt e sl id     j := 0        Ψ := ΨAt e sl
--   F , Ŝ := sizeCapAt e sl (suc id)      R̂ := hopR Ŝ
--   G := the demand         dep := capsH e sl id
--   bud := nest b sl …      ops := suc (sizeᵉ b)
--   ℓ := B + (pathLen κ + G)
--
-- and `sizeCapAt e sl id` IS `Caps.cSize (capsAt e sl id)` by
-- definition, so the size-indexed entry hypotheses transport by `refl`
-- and only the whole-Caps one needs `frameStep-0`.
--
-- WHY ℓ CARRIES A `B +`, since the obvious `ℓ := pathLen κ + G` is
-- WRONG and the assembly is what catches it: `dBound Ŝ R̂ U r s`
-- degenerates to `s` when the hop index and the unconnected count are
-- both 0 (a program with no hops and no shares), and `syncSizeᵉ b` is
-- nowhere near the tower `B`.  So the entry registry — bounded by `B`
-- through capsOK? — would not fit under `pathLen κ + G`, and the
-- ledger hypothesis would be unsatisfiable at exactly the shapes the
-- probe series calls degenerate.  Adding `B` is what makes the entry
-- weakening go through, and costs the landing nothing.
------------------------------------------------------------------

-- ENTRY, (i) is `slotsCaps?-capsAt` (Caps-Face/Part4) as it stands — the
-- slot store fits the caps its own recurrence is built from.  There is no
-- local eta-alias for it here: `Id` and `ℕ` are the same type, so an
-- alias would be one fact under two names.

-- ENTRY, (ii): and its total size does too.  Companion of
-- `size≤sizeCapAt` (.Wet/Part6, PROVEN) for the slot summand.
-- Proof: slotsSize sl ≤ 2 + sizeᵉ e + slotsSize sl (m≤n+m) ≤ cSize(capsAt) (capsAt-base-size).
entry-slotsSize : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → slotsSize sl ≤ Caps.cSize (capsAt e sl id)
entry-slotsSize e sl id =
  ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)

-- ENTRY, (iv): capsOK?'s registry conjunct as a path-length bound.
-- capsOK? carries regsSz? (pathSz? per chain); pathSz?-len extracts pathLen ≤ B.
capsOK⇒regsLen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  regsLen? (Caps.cSize c) (EvalSt.registry st) ≡ true
capsOK⇒regsLen c sched st h =
  all-impl _ _
    (λ en hSz → T⇒≡true _ (≤⇒≤ᵇ (pathSz?-len _ (proj₂ (proj₂ (proj₂ en))) hSz)))
    (EvalSt.registry st)
    (capsOK?-regs c sched st h)

-- ENTRY, (v): regsLen? weakens upward in the bound.
regsLen?-mono : ∀ {n} {Γ : Ctx n} {t} (m ℓ : ℕ)
  (rs : List (RegId × Source × Chain Γ t)) → m ≤ ℓ →
  regsLen? m rs ≡ true → regsLen? ℓ rs ≡ true
regsLen?-mono m ℓ rs m≤ℓ h =
  all-impl _ _ (λ en → ≤ᵇ-widen (pathLen (proj₂ (proj₂ (proj₂ en)))) m≤ℓ) rs h

-- THE SAME CEILING AT ANY LEVEL THE ENTRY BUDGET REACHES, which is the
-- generalisation the landing lift needs: entry-ceiling is this at
-- `j′ := L₀` with a `≤-refl`, and nothing in the chain ever depended on
-- `j′` BEING L₀ — only on its sitting under it.  Reading the two side
-- by side is what showed wet-landing-lift was assemblable rather than
-- hard: the walk hands back a level bounded by the same opIterD term,
-- so one `≤-trans` covers the gap.
-- NOT SEALED, deliberately.  It was sealed for one build on the
-- theory that wet-landing-lift's body unfolding into the opIterD tower was
-- what cost Walk-Level its memory.  That was wrong: the FIRST build, with
-- both this and wet-landing-lift unsealed, cleared Walk-Level and died
-- later in VWF.  Sealing is a CONSUMER-side fix and this module is the
-- producer, so the seal bought nothing here and its duplicated signature
-- cost real memory.  entry-ceiling below consumes it unsealed.
entry-ceiling-at : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) {u} (b : Closed Γ u) (cs : List Source) (j′ : ℕ) →
  3 + nest b sl cs ≤ Caps.cSize (capsAt e sl id) →     -- nestOK
  suc (sizeᵉ b) ≤ Caps.cSize (capsAt e sl id) →        -- opsOK
  j′ ≤ opIterD (Caps.cSize (capsAt e sl id))
               (Caps.cWid (capsAt e sl id))
               (capsH e sl id) (nest b sl cs) (suc (sizeᵉ b)) 0 →
  Caps.cSize (frameStep j′ (capsAt e sl id)) ≤ sizeCapAt e sl (suc id)
entry-ceiling-at e sl id b cs j′ nestOK opsOK j′≤L₀ = proj₁ lift-⊑
  where
  c   = capsAt e sl id
  hS  = 2≤capsAt-size e sl id
  L₀  = opIterD (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
                (nest b sl cs) (suc (sizeᵉ b)) 0
  j≤full : L₀ ≤ sizeCount c (capsH e sl id)
  j≤full =
    ≤-trans (opIterD-dominated (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
                (nest b sl cs) (suc (sizeᵉ b)) (Caps.cReg c)
                hS nestOK opsOK (1≤capsAt-reg e sl id))
            (≤-reflexive (sym (sizeCount-body c (capsH e sl id))))
  lift-⊑ : frameStep j′ c ⊑ᶜ capsAt e sl (suc id)
  lift-⊑ = subst (λ x → frameStep j′ c ⊑ᶜ x)
                 (sym (capsAt-suc-full e sl id))
                 (frameStep-mono-j c hS (≤-trans j′≤L₀ j≤full))

-- ENTRY, (iii): the reset cap ceils the walk — no level the entry budget can
-- reach outgrows the NEXT instant's size cap.  Discharged: the
-- chain is opIterD-dominated → sizeCount-body → capsAt-suc-full →
-- frameStep-mono-j (identical to sub-charge-capsOK-lift's route, .Caps-Bridge,
-- without the final capsOK?-mono step — we only need the size projection).
-- WetOuter's nestOK/opsOK supply the two size bounds opIterD-dominated needs.
entry-ceiling : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) {u} (b : Closed Γ u) (cs : List Source) →
  3 + nest b sl cs ≤ Caps.cSize (capsAt e sl id) →     -- nestOK
  suc (sizeᵉ b) ≤ Caps.cSize (capsAt e sl id) →        -- opsOK
  Caps.cSize (frameStep (opIterD (Caps.cSize (capsAt e sl id))
                                 (Caps.cWid (capsAt e sl id))
                                 (capsH e sl id) (nest b sl cs)
                                 (suc (sizeᵉ b)) 0)
                        (capsAt e sl id))
    ≤ sizeCapAt e sl (suc id)
entry-ceiling e sl id b cs nestOK opsOK =
  entry-ceiling-at e sl id b cs _ nestOK opsOK ≤-refl

-- THE LANDING LIFT, DISCHARGED — ex-postulate, and it was
-- the last FALSITY-classed row in this file that was not the walk face
-- itself.  Its header used to say the content "is sub-charge-capsOK-lift's
-- chain plus INV?'s upward monotonicity in B", and that sentence was a
-- work order: every piece it named is proven and in scope, so the
-- statement is an ASSEMBLY, not a lemma.
--
--   · the walk lands INV? at its own level's cap, cSize (frameStep j′ c),
--     and its own Σ bounds j′ by the entry opIterD term (`lvl`);
--   · entry-ceiling-at carries any such j′ up to sizeCapAt e sl (suc id)
--     — that is entry-ceiling generalised off `j′ := L₀`, which is the
--     one step that had to be invented here;
--   · INV?-widen (.Wet/Part1) raises the B index;
--   · subscribeE-slots (.Keeps-Ring) transports the Ψ and size indices,
--     since slots never change across a run.

-- IT GAINED nestOK/opsOK, AND THAT IS A RESTATEMENT, NOT A CONVENIENCE.
-- The justification is not "the call site has them" (CLAUDE.md rejects
-- that reason outright): it is that without them the statement looks
-- FALSE.  The only route from `j′ ≤ opIterD …` to the next instant's cap
-- runs through opIterD-dominated, whose whole content is that the budget
-- term is dominated by sizeCount — and it is dominated only when the nest
-- and ops bounds hold.  Drop them and nothing bounds j′ against the
-- ceiling at all.
-- SEALED, AND THE SEAL IS LOAD-BEARING — established by measurement, not by
-- the rule.  This was a POSTULATE the wet spine consumed as an
-- axiom; discharging it lets Verify-Well-Formed unfold the body, and VWF then
-- dies exactly where CLAUDE.md records its three prior instances.

-- IT WAS CONFIRMED THE EXPENSIVE WAY, and the sequence is kept because the
-- wrong turn is the instructive part:
--   · first VWF death had a 3.8 GB competing agda beside a 7.3 GB build —
--     11.1 GB against ~12 GB free — so CONTENTION was a sufficient
--     explanation, and the seal looked possibly unnecessary;
--   · unsealed and re-run on a QUIET machine: Walk-Level cleared, and
--     Verify-Well-Formed.Part13 still died `Killed: 9` at 3.7 GB entering the
--     module, with nothing else running.  That is the seal's justification —
--     contention was ruled OUT by experiment, not argued away.

-- THE TYPE IS A SYNONYM, AND THAT IS NOT COSMETIC.  Sealing needs private-impl
-- + abstract-alias, because the body's untyped `where r = …` is something a
-- plain `abstract` block rejects — and that idiom needs the signature at BOTH
-- sites.  This type binds a `subscribeE` run in a `let` and applies INV? at its
-- projections, so writing it twice makes Agda elaborate all of that twice.
-- Naming it once is what keeps the seal affordable; it is the same idiom the
-- file already uses for WalkLevel / WetOuter, and Burst-Walk for InnerNodryFuel.

-- TWO THINGS THAT ARE **NOT** THE FIX, both tried:
--   · sealing entry-ceiling-at as well, on the theory that the body unfolding
--     into the opIterD tower was the cost — no effect, reverted; entry-ceiling
--     has consumed it unsealed.  Sealing is a CONSUMER-side
--     fix and this module is the producer.
--   · reading a dev-green as evidence.  Every state above was `agda-dev` GREEN.
--     What carried the signal was the RATIO to the module's recorded best in
--     typecheck-performance-numbers.md (5.5 s → 38.4 s), not the absolute time.
WetLandingLift : Set
WetLandingLift = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (j′ : ℕ) →
  let sl = Sched.slots sched
      r  = subscribeE g b κ id now sched st
  in 3 + nest b sl (EvalSt.connectedShares st)
       ≤ Caps.cSize (capsAt e sl id) →                 -- nestOK
     suc (sizeᵉ b) ≤ Caps.cSize (capsAt e sl id) →     -- opsOK
     depthE g b κ id now sched st ≤ capsH e sl id →
     0 + j′ ≤ opIterD (Caps.cSize (capsAt e sl id))
                      (Caps.cWid (capsAt e sl id))
                      (capsH e sl id)
                      (nest b sl (EvalSt.connectedShares st))
                      (suc (sizeᵉ b)) 0 →
     INV? (ΨAt e sl)
          (Caps.cSize (frameStep (0 + j′) (capsAt e sl id)))
          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true →
     INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
          (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true

private
  wet-landing-lift-go : WetLandingLift
  -- NOT `rewrite`: that abstracts over EVERY occurrence of the run's
  -- slots, including the ones INV?'s own unfolding regenerates from its
  -- `sched` argument, which severs them from that argument and leaves a
  -- pointwise `Sched.slots r i != Sched.slots sched i`.  The motive below
  -- moves exactly the two index positions (Ψ and the size cap) and leaves
  -- the state arguments alone.
  wet-landing-lift-go {e = e} g b κ id now sched st j′ nestOK opsOK depOK lvl invL =
    subst (λ sl′ → INV? (ΨAt e sl′) (sizeCapAt e sl′ (suc id))
                        (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
          (sym (subscribeE-slots g b κ id now sched st))
          (INV?-widen (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
             (entry-ceiling-at e (Sched.slots sched) id b
                (EvalSt.connectedShares st) j′ nestOK opsOK lvl)
             invL)
    where r = subscribeE g b κ id now sched st

abstract
  wet-landing-lift : WetLandingLift
  wet-landing-lift = wet-landing-lift-go

subscribeE-wet-core : WalkLevel → WetOuter
subscribeE-wet-core wl {n} {Γ} {t} {e} {u} g b κ id now sched st
                    inv pB pS pLen szB fcB gas cOK dW nestOK opsOK depOK =
    dry
  , wet-landing-lift g b κ id now sched st j′ nestOK opsOK depOK lvl invL
  where
  sl = Sched.slots sched
  c  = capsAt e sl id
  Ψ  = ΨAt e sl
  B  = sizeCapAt e sl id
  Ŝ  = sizeCapAt e sl (suc id)
  G  = dBound Ŝ (hopR Ŝ) (unconn sl (EvalSt.connectedShares st))
               (hopDᵉ Ŝ (slotHop Ŝ sl) b) (syncSizeᵉ b)
  ℓ  = B + (pathLen κ + G)

  cOK0 : capsOK? (frameStep 0 c) sched st ≡ true
  cOK0 = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) cOK

  regs : regsLen? ℓ (EvalSt.registry st) ≡ true
  regs = regsLen?-mono B ℓ (EvalSt.registry st) (m≤m+n B (pathLen κ + G))
           (capsOK⇒regsLen c sched st cOK)

  L₀ = opIterD (Caps.cSize c) (Caps.cWid c) (capsH e sl id)
               (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0

  W = wl b c Ψ Ŝ Ŝ (hopR Ŝ) G ℓ L₀ (capsH e sl id)
         (nest b sl (EvalSt.connectedShares st)) (suc (sizeᵉ b)) 0
         g κ id now sl sched st
         (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id) (B2-cReg≤cSize e sl id) refl
         (slotsCaps?-capsAt e sl id) (entry-slotsSize e sl id)
         cOK0 szB dW pS pLen ≤-refl ≤-refl depOK
         inv fcB pB
         -- the reset-anchor pins at the entry: the F/R̂ equations are
         -- refl by the instantiation, 2 ≤ Ŝ is the next instant's own
         -- entry floor, and the ceiling is entry-ceiling at L̂ := the
         -- entry budget itself (so the budget pin is ≤-refl)
         (2≤capsAt-size e sl (suc id)) refl refl
         (entry-ceiling e sl id b (EvalSt.connectedShares st) nestOK opsOK) ≤-refl
         ≤-refl gas (m≤n+m (pathLen κ + G) B) regs

  -- the Σ's nine conjuncts, named rather than counted: capsOK?,
  -- burstCaps?, burstCount?, the opIterD level bound, INV?, burstB?,
  -- burstHopD?, hasDry, regsLen?
  j′ = proj₁ W
  p2 = proj₂ W
  p3 = proj₂ p2
  p4 = proj₂ p3
  p5 = proj₂ p4
  p6 = proj₂ p5
  p7 = proj₂ p6
  p8 = proj₂ p7
  p9 = proj₂ p8

  lvl  = proj₁ p5
  invL = proj₁ p6
  dry  = proj₁ p9

subscribeE-wet : WetOuter
subscribeE-wet = subscribeE-wet-core subscribeE-walk-level

