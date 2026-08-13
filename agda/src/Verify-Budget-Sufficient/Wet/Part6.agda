-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, part 6 of 6.
--
-- blocks 74-103: the dBound arithmetic and the closing invariants.
--
-- Split from Verify-Budget-Sufficient.Wet on 2026-08-12.  The three
-- multi-member blocks (36/13/5 members, genuine cycles) each get their
-- own module so an edit re-checks one part instead of 4.7k lines.
-- Consumers import the Wet umbrella and are unaffected.

module Verify-Budget-Sufficient.Wet.Part6 where


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
                                       suc-injective; <-irrefl; ≡ᵇ⇒≡;
                                       +-cancelʳ-≤)
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
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ;
                                 pm-elimGᵉ; pm-elimGᵗ; pm-elimGᵗˢ;
                                 hopD-elimGᵉ; hopD-elimGᵗ; hopD-elimGᵗˢ;
                                 hopD-unfoldμ)
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
                                dropSource; arrSource; chainsOf; chainsGo;
                                cascadeGo;
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
                                budgetAt; slotsSize; capsHgo; capsBase)

-- .Caps re-exports .Keeps-Ring (which re-exports .Measures), so this one
-- import carries the whole stratum below.  It is here for `Caps` /
-- `capsAt` / the supply lemmas only — this module reads NOTHING from the
-- caps FACE, which is why the recurrence was extracted out of it.
open import Verify-Budget-Sufficient.Caps public

------------------------------------------------------------------
-- the Keeps ring and the share-boundary facts moved to
-- .Keeps-Ring: the caps face needs slotsEq too, and a shared
-- prerequisite must not sit inside one of the two faces.
------------------------------------------------------------------
------------------------------------------------------------------
-- the walk contracts, store half — the SHAPE the clause grind
-- threads (receipts E′ ≤ E · spendᴱ … attach with the cost
-- instrumentation; the landing stays in the cores below).  Stated
-- against the frozen instant base W and a ledger position E ≥ 3.
------------------------------------------------------------------


open import Verify-Budget-Sufficient.Wet.Part5 public

------------------------------------------------------------------
-- THE WET CORES — THE ASSEMBLY, TRANSCRIBED (2026-08-01), AND THE
-- THREE STATEMENT-LEVEL GAPS IT FOUND.  Outside-in, at this joint:
-- the companion tree the wet induction would walk was written down
-- BEFORE any clause was ground — and writing it down is what found
-- the gaps.  They are cured below, in one pass, against the caps
-- recurrence.
--
-- THE COMPANION TREE.  The wet induction needs no new tree.  It is
-- subscribeE-walkS's, clause for clause, with the wet payload (hasDry
-- ≡ false, and one hasAtLeast peel per gas edge) carried alongside the
-- store payload each member already threads.  Transcribed, with what
-- each member threads and which of the three gas edges it owns:
--
--   subscribeE-walkS      THE WALK, thirteen clauses.  `input` →
--     -input-wet; of/empty are one-shots (one eval edge, no gas);
--     map/take/scan are install-INV + the IH + pushBurst-wet (no gas);
--     the four *Alls → subscribeAll-wet; μᵉ g0 is the dry stub and
--     μᵉ (gs fuel) is THE μ EDGE (re-enter on unfoldμ at the ×2 copy
--     edge); varᵉ is absurd; deferᵉ → -defer-wet (mint source +
--     ordinal, addLive-INV).
--   subscribeAll-wet      mint node, install-INV, the IH under
--     `thru-outer op nid ↠ κ`, pushBurst-wet.  Spends no gas itself —
--     a *All's gas is spent one level down, at subscribeInner.
--   subscribeE-input-wet  five shapes over ONE slot, cut out of the
--     telescope by slotSize-at / slotFnCap-at.  cold-without-tail is a
--     ledger-free one-shot; cold-with-tail and hot are register-INV
--     (the ×2 length edge); shared → sharedSlot-wet.
--   sharedSlot-wet        completed → nothing; already connected → one
--     register-INV; otherwise → sharedConnect-wet.
--   sharedConnect-wet     THE CONNECT EDGE.  g0 is the dry stub; gs
--     peels one, latches connectedShares (connectShare-INV), registers
--     (register-INV), walks the stored def at `share-sink i`, and
--     lands through connectWrap-wet.
--   pushBurst-wet         splitBurst, stepFrame-wet, retag.
--   stepFrame-wet         map-f is the ledger rule itself (×3^(suc Ψ));
--     scan-f → -scan-wet; take-f → -take-wet; from-inner →
--     -fromInner-wet (absorb, or innerFinish-wet); thru-outer →
--     -thruOuter-wet.
--   thruWalk-wet          one thruConsume-wet per emitted outer value.
--   thruConsume-wet       the per-op node bookkeeping around the hop:
--     merge's bump, concat's queue and drain, switch's kill, exhaust's
--     flag.
--   subscribeInner-wet    THE HOP EDGE.  g0 is the dry stub; gs peels
--     one and re-enters the walk on the inner observable VALUE under
--     `from-inner op allNid inst ↠ κ`.
--   concatDrain-wet / innerFinish-wet / thruWrap-wet   structural.
--
--   and one level out, the delivery clique: cascadeGo-walk →
--   chainStep-wet → foldPath-wet → (at share-sink) dispatchShare-wet →
--   shareGo-wet → foldPath-wet.  It spends NO gas at all: a burst
--   leaves subscribeE through a FRAME and is never re-entered through
--   a path (the Keeps memo's clique boundary, same reason).
--
-- So the structural half transcribes exactly.  What did NOT transcribe
-- was the two cores' own faces — and that is what is repaired here.
--
-- ================================================================
-- THE RESTATEMENT (2026-08-01): THE WET STACK ANCHORS AT capsAt
-- ================================================================
--
-- This is the convergence the caps campaign existed for.  Round 3b's
-- Ŝ / R̂ / F were always waiting for an ENTRY-COMPUTABLE reach bound —
-- round3b-ledger-reset-absurd is the proof that nothing ledger-shaped
-- can serve — and capsAt is it: a recurrence on the program syntax and
-- the slot telescope alone, with no reference to E, to capᴱ, or to any
-- quantity the walk's own work moves.
--
-- GAP 1 — THE INVARIANT WAS THE WRONG ONE, IN AND OUT.  Both cores
-- carried `stBounded? B`: two conjuncts, live pendings and node
-- stores.  Every member of the companion tree above, and the only face
-- anywhere that produces `hasDry ≡ false` (subscribeE-walk), carries
-- `INV? Ψ B` — SIX conjuncts: stBounded?, fnCapBounded?, registry
-- cardinality, regsB?, slotsSize, slotsFnCap.  Neither direction
-- closed: `stBounded? V` says nothing about a stored value's fn
-- weight, the registry's cardinality, or a registered chain's frames
-- (IN), and a stBounded?-only conclusion cannot re-seed an INV?-shaped
-- hypothesis (OUT), so drain-dry → cascade-dry → the cascade face did
-- not compose.  And subscribeE-wet's κ was completely unconstrained, where
-- every member needs `pathB? B Ψ κ` (register-INV consumes it to keep
-- regsB?).
--
--   CURED.  Both cores now carry INV? Ψ B in AND out, at
--   (Ψ, B) = (ΨAt e sl, sizeCapAt e sl ·) — a fn-cap seed that never
--   grows and a size cap that rides the caps recurrence per instant —
--   plus `pathB? B Ψ κ` on subscribeE-wet's continuation.
--   cascade-dry's conclusion is now LITERALLY drain-dry's next-instant
--   hypothesis, with no residue.
--
-- GAP 2 — THE DEMAND'S RESET CAPS WERE THE LEDGER.  subscribeE-wet
-- measured its demand at V = sizeBudgetAt e slots id — the instant's
-- STORE bound — in every cap role at once: dBound's V, R as hopR V,
-- hopD's index, and (through `sizeᵉ b ≤ V`) the entry size.  But the
-- hop child is drawn from a MID-walk burst, and mid-walk values
-- outgrow V (a scan frame folds every value with no fuel peel), so the
-- only stated bound on such a value was the walk's own ledger ceiling
-- capᴱ W E′ — whose permitted range grows with the walk's work, which
-- grows with the demand, which is ≥ suc V by sucV≤d.  That is exactly
-- the shape round3b-ledger-reset-absurd refutes.
--
--   CURED.  Ŝ is read off capsAt — `Caps.cSize (capsAt e sl ·)`,
--   abbreviated sizeCapAt below — and R̂ = hopR Ŝ, F = Ŝ.  The wiring
--   is reach-resets (.Caps-Face, PROVEN): from `sizeᵉ o ≤ C` at
--   `2 ≤ C` it yields BOTH `syncSizeᵉ o ≤ C` and `hopDᵉ C o ≤ hopR C`,
--   which is why F needs no separate justification — it IS Ŝ, and why
--   hop rank is not a Caps field (it is derivable from cSize; carrying
--   it would be a synonym).  The mid-walk growth objection dissolves
--   the same way it did on the caps side: the walk carries its own
--   progress index (the walk face's G, the caps face's j) while the
--   ANCHORS stay entry-fixed.
--
--   WHICH LEVEL, AND WHY — the hop edge picks it.  The entry
--   hypotheses (INV?, pathB?, sizeᵉ b) read level `id`; the reset caps
--   Ŝ / R̂ / F and the landing invariant read level `suc id`.
--   hop-step-needs (below, machine-checked) says an r-drop of one buys
--   EXACTLY `s + suc Ŝ` of syncSize headroom, so a hop child `o` owes
--
--       suc (syncSizeᵉ o) ≤ syncSizeᵉ b + suc Ŝ
--
--   and not one unit more.  `o` is drawn from a MID-instant burst, and
--   a mid-instant value is bounded by the instant's ENDPOINT caps
--   level, not by its entry level — caps-tick is exactly that shape
--   (capsAt id in, capsAt (suc id) out, every mid-cascade state at an
--   intermediate `frameStep j` between them).  So Ŝ := sizeCapAt e sl
--   (suc id), whence `sizeᵉ o ≤ Ŝ` gives `syncSizeᵉ o ≤ Ŝ` by
--   reach-resets and `suc Ŝ ≤ syncSizeᵉ b + suc Ŝ` closes the owed
--   inequality with the whole of syncSizeᵉ b as slack.  Reading Ŝ at
--   level `id` would NOT close it: the mid-instant inner is not
--   bounded there.  No pre-blowup base and no partial frameStep level
--   is needed — the two endpoints of one instant suffice.
--
-- GAP 3 — THE ARRIVAL WAS UNBOUNDED, AND THE POP RING COULD NOT BOUND
-- IT.  The cascade face quantified over `chains` and over `a` with no
-- bound on either.  cascadeGo-walk needs `all (λ rc → pathB? …)
-- chains` (which is INV?'s regsB? conjunct, so GAP 1 supplies it
-- through chainsOf-B below) and, separately, `valB? … (arrTy a)
-- (arrVal a)`.  Nothing bounded a POPPED arrival's value:
-- schedHeadOf-bounded and pop-bounded both keep the TAIL and drop the
-- popped element on the floor.
--
--   CURED at the statement.  The cascade face gains the arrival
--   hypothesis, and the companion that supplies it is NAMED:
--   pop-head-bounded, the head-KEEPING schedGo inversion (the popped
--   arrival was a pending of a live source, so stBounded?'s pendings
--   half bounds it).  Stated here, consumed by drain-dry; NOT proven
--   this leg.
--
-- WHAT THE WALK FACE'S PARAMETERS BECOME.  subscribeE-walk
-- (.Measures) is NOT restated: its eight caps are universally
-- quantified ℕs, so the capsAt instantiation is a choice of arguments
-- and nothing about the face resists it.  The map, recorded here so it
-- is not re-derived:
--
--   Ŝ  ←  Caps.cSize (capsAt e sl (suc id))            (= sizeCapAt)
--   R̂  ←  hopR Ŝ         — DERIVED from cSize by reach-resets, not a
--                          Caps field; hop rank is derivable, which is
--                          why there is no cHop
--   F  ←  Ŝ              — same object; reach-resets' second component
--                          is stated at index C = Ŝ
--   ℓ  ←  REFUTED AT Ŝ (2026-08-13).  The reading below is right about
--                          where the LENGTH ledger lives, and wrong
--                          about the level.  The walk also demands
--                          `pathLen κ + G ≤ ℓ`, and G is the demand
--                          MEASURED AT Ŝ, so `sucV≤d` (.Measures:6476)
--                          gives `suc Ŝ ≤ G` under the same
--                          one-hop-or-one-share side condition GAP 4
--                          runs on.  Then `pathLen κ + G ≥ G > Ŝ`, and
--                          ℓ := Ŝ cannot hold.  THIS IS GAP 4'S LOOP ON
--                          THE WAY IN: any parameter the map pins to Ŝ
--                          inherits the refutation, because the demand
--                          measured at Ŝ exceeds Ŝ.  GAP 4 is the W/E
--                          instance; this is the ℓ instance.  And the
--                          two compose the wrong way — `walkCap Ω ℓ G`
--                          is what the way-out ceiling is exponential
--                          in, so raising ℓ to satisfy this hypothesis
--                          RAISES the ceiling GAP 4 already refutes.
--                          (was: the caps face already reads path
--                          LENGTH at cSize — pathSz?'s
--                          `suc (pathLen p) ≤ᵇ B` conjunct is the ℓ
--                          ledger at ℓ := cSize, its own memo says so)
--   Ω  ←  NOT a Caps field.  ΩAt e sl.  cWid is the FRAME width
--                          (widLive / widNode); Ω is the per-NODE ofW
--                          width (widthOK?), and om-is-not-a-frame-
--                          budget is the counterexample to conflating
--                          them.  Ω needs no recurrence: the one width
--                          mint in the machine is ofᵉ and ΩAt already
--                          dominates it, which is why the width walk
--                          is proven with no running position.
--   Ψ  ←  NOT a Caps field.  ΨAt e sl.  Ψ never grows (caseW is
--                          substitution-invariant), so no recurrence.
--   W, E ← the walk's OWN ledger.  The joint this map left open —
--                            capᴱ W (E · 3^(suc Ψ · walkCap Ω ℓ G))
--                              ≤ sizeCapAt e sl (suc id)
--                          — was recorded here as "arithmetic, not
--                          statement-level".  IT IS NEITHER: it is
--                          REFUTED, by walk-hyps-absurd at V := Ŝ.  See
--                          GAP 4 below (wet-ceiling-absurd).  So the
--                          "two parallel accounting mechanisms for one
--                          growth is a smell" note at the end of
--                          .Caps-Face is not a smell but an
--                          obstruction, and collapsing E into j is not
--                          a follow-up but the only surviving route.
--
-- cascadeGo-level and cascadeGo-deliveries (.Caps-Face) are both
-- THEOREMS as of 2026-08-03, and design-owned.  Nothing restated here
-- consumes either of them.
------------------------------------------------------------------

-- THE EXACT SLACK AT A ONE-STEP HOP, so GAP 2's level choice is a
-- number and not a worry.  At a FIXED anchor Ŝ an r-drop of one buys
-- exactly `s + Ŝ` of syncSize headroom — necessary and sufficient,
-- both directions.  The whole content is *-suc: dBound's second
-- summand grows by exactly suc Ŝ per unit of r.
dBound-suc-r : ∀ (V R U r s : ℕ) →
  dBound V R U (suc r) s ≡ (s + suc V) + suc V * (r + suc R * U)
dBound-suc-r V R U r s =
  trans (cong (s +_) (*-suc (suc V) (r + suc R * U)))
        (sym (+-assoc s (suc V) (suc V * (r + suc R * U))))

hop-step-gives : ∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
  suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
hop-step-gives V R U r s s′ h =
  ≤-trans (+-monoˡ-≤ (suc V * (r + suc R * U)) h)
          (≤-reflexive (sym (dBound-suc-r V R U r s)))

hop-step-needs : ∀ (V R U r s s′ : ℕ) →
  suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
hop-step-needs V R U r s s′ h =
  +-cancelʳ-≤ (suc V * (r + suc R * U)) (suc s′) (s + suc V)
    (≤-trans h (≤-reflexive (dBound-suc-r V R U r s)))

------------------------------------------------------------------
-- THE μ EDGE's r SIDE — hopD IS EQUAL ACROSS AN UNFOLD.  hopD-unfoldμ
-- lives in Rx.Hop-Depth; imported above and used by mu-edge below.
--

------------------------------------------------------------------
-- THE THREE GAS EDGES, PACKAGED.  Each one is "the machine's own step
-- fact, the dBound descent lemma, and the reset supply" fused into the
-- single inequality a clause proof applies with nothing left to
-- compute.  Everything else in the wet induction is structural
-- threading; this is the termination content.
------------------------------------------------------------------

-- (1) THE μ EDGE.  r is fixed (hopD-unfoldμ), s strictly drops
-- (unfoldμ-shrinks), U is untouched — an unfold moves no state at all.
mu-edge : ∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
  suc (dBound Ŝ R̂ U (hopDᵉ Ŝ (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
    ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ (μᵉ body)) (syncSizeᵉ (μᵉ body))
mu-edge Ŝ R̂ U body
  rewrite hopD-unfoldμ Ŝ body =
  dBound-μ {Ŝ} {R̂} {U} {hopDᵉ Ŝ body}
           {syncSizeᵉ (unfoldμ body)} {syncSizeᵉ (μᵉ body)}
           (unfoldμ-shrinks body)

-- (2) THE HOP EDGE, at the entry-fixed anchor.  The r-drop is the
-- emitted-value invariant (burstHopD?) against the *All frame's
-- DEFINITIONAL `suc`; the s reset is `reach-reset`'s first component —
-- CALLED now, not inlined (.Measures, where the pair is stated once), so
-- this module still reads nothing from the caps FACE.  hop-step-needs
-- says the slack is exact: an r-drop of one buys `s + suc Ŝ`, and
-- `suc Ŝ` alone already covers it.
hop-edge : ∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) → 2 ≤ Ŝ →
  (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ (obs u) o < r →
  suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ (obs u) o) (syncSizeᵉ o))
    ≤ dBound Ŝ (hopR Ŝ) U r s
hop-edge Ŝ U r s 2≤Ŝ o szo r′<r =
  dBound-hop {Ŝ} {hopR Ŝ} {U} {hopDᵉ Ŝ o} {r} {syncSizeᵉ o} {s}
             r′<r (proj₁ (reach-reset Ŝ 2≤Ŝ o szo))

-- (3) THE CONNECT EDGE.  U strictly drops (unconn-insert, behind the
-- machine's own `memberSource … ≡ false` guard), and BOTH of the
-- child's measures reset at the anchor, because a shared slot's def is
-- cap-sized entry syntax — `reach-reset`'s two components, CALLED now
-- rather than inlined.  Its tuple is (sync , hop) and dBound-connect
-- wants hop first, hence the swap.
connect-edge : ∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
  (sl : Slots Γ) (cs : List Source) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
  memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
  suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs)) (hopDᵉ Ŝ d) (syncSizeᵉ d))
    ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
connect-edge Ŝ r s 2≤Ŝ sl cs i {d} eqi fresh szd =
  dBound-connect {Ŝ} {hopR Ŝ} {unconn sl (toℕ i ∷ cs)} {unconn sl cs}
                 {hopDᵉ Ŝ d} {r} {syncSizeᵉ d} {s}
                 (unconn-insert sl cs i eqi fresh)
                 (proj₂ pair)
                 (proj₁ pair)
  where
  pair = reach-reset Ŝ 2≤Ŝ d szd

-- AND U NEVER RISES BETWEEN THE EDGES.  Every structural companion of
-- the subscribe clique threads the demand's U component past arbitrary
-- machine work, and this is the whole of what that costs: the Keeps
-- ring says the slots are literally unchanged and connectedShares only
-- grows, and unconn is antitone in the latter.  Instantiate at any
-- member of the clique's *-keeps family.
unconn-keeps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
  Keeps sched st sched′ st′ →
  unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
    ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
unconn-keeps sched st sched′ st′ K =
  subst (λ sl → unconn sl (EvalSt.connectedShares st′)
                  ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st))
        (sym (KeepsC.slotsEq K))
        (unconn-antitone (Sched.slots sched)
                         (EvalSt.connectedShares st)
                         (EvalSt.connectedShares st′)
                         (KeepsC.connMono K))

------------------------------------------------------------------
-- THE ONE ANCHOR.  Every cap the wet stack measures with is this
-- number at one of two instant levels: the store invariant's B, the
-- demand's s′ reset Ŝ, the r reset's base (R̂ = hopR Ŝ) and the hop
-- index F.  Entry-computable by construction — capsAt is a recurrence
-- on the syntax and the slot telescope alone.
------------------------------------------------------------------

sizeCapAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Id → ℕ
sizeCapAt e sl id = Caps.cSize (capsAt e sl id)

2≤sizeCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → 2 ≤ sizeCapAt e sl id
2≤sizeCapAt = 2≤capsAt-size

-- one instant is one frameBlowup, and a blowup never shrinks the size
-- cap: the two levels a core reads are ordered
sizeCapAt-mono : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeCapAt e sl id ≤ sizeCapAt e sl (suc id)
sizeCapAt-mono e sl id =
  cSize≤frameBlowup (capsAt e sl id) (capsH e sl id)
    (≤-trans (s≤s z≤n) (2≤sizeCapAt e sl id))

-- the program's own size sits under the cap at every instant (capsAt's
-- base is `2 + sizeᵉ e + slotsSize sl`, one frameBlowup down)
size≤sizeCapAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) → sizeᵉ e ≤ sizeCapAt e sl id
size≤sizeCapAt e sl id =
  ≤-trans (≤-trans (m≤n+m (sizeᵉ e) 2) (m≤m+n (2 + sizeᵉ e) (slotsSize sl)))
          (capsAt-base-size e sl id)

------------------------------------------------------------------
-- GAP 4 (2026-08-01, found grinding the gas edges): THE LEDGER CANNOT
-- DELIVER subscribeE-wet's LANDING LEVEL, AND THAT IS NOT AN OPEN
-- ARITHMETIC DEBT — IT IS REFUTED.
--
-- The restatement's parameter map (above) leaves exactly one thing to
-- the follow-up, and calls it "arithmetic, not statement-level":
--
--     capᴱ W (E · 3^(suc Ψ · walkCap Ω ℓ G)) ≤ sizeCapAt e sl (suc id)
--
-- That inequality is the ONLY route from subscribeE-walk's conclusion
-- (INV? at the ledger position capᴱ W E′, with E′ bounded ABOVE by the
-- receipt and by nothing else) to subscribeE-wet's conclusion (INV? at
-- the caps level).  INV? weakens upward in B, so the core's landing
-- needs its ledger ceiling UNDER Ŝ, and the receipt's ceiling is the
-- only upper bound on E′ the face provides.
--
-- IT IS THE SAME THREE-EDGE LOOP the round-1 vacuity died of, and it
-- needs no new witness: walk-hyps-absurd (.Measures) IS the refutation,
-- at V := Ŝ, R := hopR Ŝ, d := G.  The edges, spelled out:
--
--   · suc Ŝ ≤ G          the demand is measured AT Ŝ, and one
--                        unconnected share or one remaining hop puts
--                        it past its own anchor  (sucV≤d)
--   · G ≤ X              walkCap's index dominates the demand it is
--                        indexed by                (d≤walkArg)
--   · X < capᴱ W X ≤ Ŝ   the ceiling, and capᴱ is exponential (n<2^n)
--
-- so Ŝ < Ŝ.  The side condition `1 ≤ r + suc R̂ · U` is not a
-- restriction worth caring about: it fails only when the call has NO
-- gas edge left at all (no unconnected share, no hop), i.e. exactly
-- when the wet contract has no content.
--
-- WHAT THIS DOES NOT SAY.  It does not refute subscribeE-wet, and it
-- does not refute subscribeE-walk.  It refutes the COMPOSITION: the
-- ledger receipt cannot be the supplier of the caps-level landing, for
-- any Ψ, W, Ω, ℓ, E, G.  Collapsing E into j is therefore not an
-- optimisation — it is the only surviving route, and the two
-- accounting mechanisms cannot be joined at the receipt.
--
-- WHAT IS LEFT, then, and it is where the next design ruling belongs.
-- The other candidate supplier is the caps face, which already lands a
-- whole cascade from capsAt id to capsAt (suc id) (caps-tick, ground).
-- Two things stand between it and this core:
--
--   (a) NO SUBSCRIBE-LEVEL CHARGE.  subscribeE-caps reports at
--       `frameStep (j + j′) c` with j′ existentially produced and
--       UNBOUNDED.  cascadeGo-level budgets a cascade's j (`lvls`, one
--       dLvl per delivery); nothing budgets a bare subscribe's, so
--       burst-wet's own landing (root subscribe, capsAt 0 → capsAt 1)
--       has no supplier either.  The missing companion is a
--       subscribeE-level analogue of `fLvl`, and it is NAMED here
--       rather than assumed.  It is the SAME hole the two *All frame
--       faces wait on (.Caps-Face, conjunct (a) there), seen from the
--       wet side — one companion would close both.
--       AND THE COMPANION IS NOT A CLOSED FORM (measured,
--       agda/probe/Sub-Charge-Probe.agda): a subscribe installs frames
--       and a frame subscribes one inner per payload, so the subscribe
--       charge and the frame charge are MUTUALLY RECURSIVE and no
--       function of (S, W, J) closes the loop — the same failure
--       `dCapᶜ` took on the delivery side, and the same repair, a
--       recursion on a nesting budget.  The gas escape that would have
--       killed any level reading (a synchronous μ fixpoint, re-entering
--       subscribeE once per unfolding against a `budgetAt` three tower
--       stories above `capsAt`) is closed BY TYPING: `deferᵉ` is the
--       sole gate moving Δᵍ into scope, so a μ's self-reference costs a
--       TICK.  The hierarchy is probed and gated; what it waits on is
--       the nesting budget's instantiation, which is a ruling.
--   (b) capsOK? IS NOT INV?.  They share stBounded? and nothing else:
--       INV? adds fnCapBounded?, regsB?, slotsFnCap and reads registry
--       cardinality at cSize where capsOK? reads it at cReg.  Four
--       conjuncts of the wet predicate have no caps-side counterpart.
--
-- Both are statement-level and both are face-level, so per the
-- outside-in rule the clause grind stops here rather than guessing at
-- them: the gas edges themselves are ground above and wait on this.
------------------------------------------------------------------

wet-ceiling-absurd : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) (Ψ W Ω ℓ E G U r s : ℕ) → 3 ≤ E →
  1 ≤ r + suc (hopR (sizeCapAt e sl (suc id))) * U →
  dBound (sizeCapAt e sl (suc id)) (hopR (sizeCapAt e sl (suc id))) U r s ≤ G →
  capᴱ W (E * 3 ^ (suc Ψ * walkCap Ω ℓ G)) ≤ sizeCapAt e sl (suc id) →
  ⊥
wet-ceiling-absurd e sl id Ψ W Ω ℓ E G U r s 3≤E 1≤ dem ceil =
  walk-hyps-absurd Ψ W Ω (sizeCapAt e sl (suc id)) ℓ
                   (hopR (sizeCapAt e sl (suc id))) U r s G E 3≤E 1≤ dem ceil

------------------------------------------------------------------
-- THE CASCADE BOOKENDS ON THE INV? FACE — the caps face's
-- cascadeLatch-caps / cascadeFinish-caps, at the wet predicate.  The
-- latch touches only per-cascade scratch no conjunct reads; the finish
-- is the same drop-and-sweep shareFinish-INV already runs.
------------------------------------------------------------------

cascadeLatch-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched (cascadeLatch a st) ≡ true
cascadeLatch-INV Ψ B a sched st inv with Arrival.isLast a
... | true  = inv
... | false = inv

cascadeFinish-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  INV? Ψ B (proj₁ (cascadeFinish a sched st))
           (proj₂ (cascadeFinish a sched st)) ≡ true
cascadeFinish-INV Ψ B a sched st inv with Arrival.isLast a
... | false = inv
... | true  =
  ∧-intro (∧-intro (sweepLive-bounded B kept (Sched.live sched)
                     (stB-live B sched st sb))
                   (stB-nodes B sched st sb))
  (∧-intro (∧-intro (sweepLive-fnCap Ψ kept (Sched.live sched)
                      (fcB-live Ψ sched st fc))
                    (fcB-nodes Ψ sched st fc))
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans (dropSource-len (arrSource a) (EvalSt.registry st))
                       (≤ᵇ⇒≤ _ _ (T-to rl)))))
  (∧-intro (dropSource-regs B Ψ (arrSource a) (EvalSt.registry st) rb)
  (∧-intro ss sf))))
  where
  kept = dropSource (arrSource a) (EvalSt.registry st)
  P    = INV-parts Ψ B sched st inv
  sb   = proj₁ P
  fc   = proj₁ (proj₂ P)
  rl   = proj₁ (proj₂ (proj₂ P))
  rb   = proj₁ (proj₂ (proj₂ (proj₂ P)))
  ss   = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ P))))
  sf   = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ P))))

-- the chain snapshot inherits its bounds from the registry — GAP 3's
-- FIRST half, discharged from INV?'s regsB? conjunct rather than
-- postulated (the caps face's chainsGo-caps, at pathB?)
chainsGo-B : ∀ {n} {Γ : Ctx n} {t} (B Ψ : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsB? B Ψ rs ≡ true →
  all (λ rc → pathB? B Ψ (proj₂ rc)) (chainsGo a rs) ≡ true
chainsGo-B B Ψ a [] h = refl
chainsGo-B B Ψ a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (chainsGo-B B Ψ a r (proj₂ (∧-true _ _ h)))

chainsOf-B : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (B Ψ : ℕ)
  (a : Arrival Γ) (st : EvalSt e) →
  regsB? B Ψ (EvalSt.registry st) ≡ true →
  all (λ rc → pathB? B Ψ (proj₂ rc)) (chainsOf a st) ≡ true
chainsOf-B B Ψ a st = chainsGo-B B Ψ a (EvalSt.registry st)

postulate
  -- THE WET CONTRACT, restated 2026-08-01 against the caps recurrence
  -- (GAP 1 + GAP 2 above).  From a machine within instant `id`'s caps
  -- level, subscribing a cap-sized value under a cap-bounded
  -- continuation with fuel for its demand — the demand measured at the
  -- ENTRY-COMPUTABLE reset caps Ŝ = sizeCapAt e sl (suc id),
  -- R̂ = hopR Ŝ, F = Ŝ, never at the ledger — neither dries nor escapes
  -- instant (suc id)'s caps level.
  --
  -- To be ground clause by clause through the mutual block
  -- (subscribeE / stepFrame / pushBurst / subscribeAll /
  -- subscribeInner / subscribeSharedSlot), each decrement edge
  -- consuming one hasAtLeast peel against dBound-μ / dBound-hop /
  -- dBound-connect, with hop-step-gives supplying the hop edge's
  -- syncSize headroom from reach-resets at Ŝ.  The internal walk
  -- threads the stronger mid-instant invariant (subscribeE-walk, at
  -- the parameter map recorded above); only this outer face is fixed
  -- here.
  --
  -- ASSEMBLY (2026-08-06): narrowed over exactly the facts this
  -- postulate's own header says it is to be ground from — the three
  -- packaged gas edges, the hasAtLeast peel, hop-step-gives' syncSize
  -- headroom, and the internal walk (subscribeE-walk) the header names
  -- as threading the mid-instant invariant — plus the Keeps-Ring share
  -- boundary facts and the .Measures budget/size faces the clause grind
  -- consumes.  Every hypothesis is already proven, so this is neither
  -- stronger nor weaker than the postulate it replaces.
  --
  -- TIER 0, SECOND — after `cascadeGo-nodry` (.Burst-Walk § 8, the
  -- anchor) resolves.  Given the walk this is "the outer instantiation", but
  -- the instantiation must manufacture the walk's G/ℓ/Ω entry data
  -- from INV? alone, and that INV?/capᴱ flavour conversion is
  -- UNCHECKED — a named, specific unverified step, not general unease,
  -- with maximal blast radius: both branches of `budget-sufficient`
  -- consume this face.  It takes `subscribeE-walk` as a finished fact,
  -- so the walk's own sub-postulate residue does not block it.
  subscribeE-wet-core :
    -- subscribeE-walk  (Verify-Budget-Sufficient/Measures.agda:6125)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (Ψ W Ω ℓ F Ŝ R̂ G : ℕ) (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
      (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
      3 ≤ E →
      INV? Ψ (capᴱ W E) sched st ≡ true →
      sizeᵉ b ≤ capᴱ W E → fnCapᵉ b ≤ Ψ →
      pathB? (capᴱ W E) Ψ κ ≡ true →
      widthOK? Ω sched st ≡ true → ofWᵉ b ≤ Ω → pathΩ? Ω κ ≡ true →
      dBound Ŝ R̂ (unconn (Sched.slots sched) (EvalSt.connectedShares st))
             (hopDᵉ F b) (syncSizeᵉ b) ≤ G →
      g hasAtLeast suc G →
      pathLen κ + G ≤ ℓ →
      regsLen? ℓ (EvalSt.registry st) ≡ true →
      let r = subscribeE g b κ id now sched st
      in Σ ℕ λ E′ → (E ≤ E′)
         × (E′ ≤ E * 3 ^ (suc Ψ * walkCap Ω ℓ G))
         × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
         × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
         × (burstHopD? F (hopDᵉ F b) (proj₁ r) ≡ true)
         × (hasDry (proj₁ r) ≡ false)
         × (mintCount (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
              ≤ mintCount sched st + walkCap Ω ℓ G)
         × (burstLen (proj₁ r) ≤ walkCap Ω ℓ G)
         × (regsLen? ℓ (EvalSt.registry (proj₂ (proj₂ r))) ≡ true)
     ) →
    -- mu-edge  (Verify-Budget-Sufficient/Wet.agda:4036)
    (∀ {n} {Γ : Ctx n} {t} (Ŝ R̂ U : ℕ) (body : Exp Γ (t ∷ []) [] [] t) →
      suc (dBound Ŝ R̂ U (hopDᵉ Ŝ (unfoldμ body)) (syncSizeᵉ (unfoldμ body)))
        ≤ dBound Ŝ R̂ U (hopDᵉ Ŝ (μᵉ body)) (syncSizeᵉ (μᵉ body))
     ) →
    -- hop-edge  (Verify-Budget-Sufficient/Wet.agda:4052)
    (∀ {n} {Γ : Ctx n} {u} (Ŝ U r s : ℕ) → 2 ≤ Ŝ →
      (o : Val Γ (obs u)) → sizeᵛ (obs u) o ≤ Ŝ → hopDᵛ Ŝ (obs u) o < r →
      suc (dBound Ŝ (hopR Ŝ) U (hopDᵛ Ŝ (obs u) o) (syncSizeᵉ o))
        ≤ dBound Ŝ (hopR Ŝ) U r s
     ) →
    -- connect-edge  (Verify-Budget-Sufficient/Wet.agda:4066)
    (∀ {n} {Γ : Ctx n} (Ŝ r s : ℕ) → 2 ≤ Ŝ →
      (sl : Slots Γ) (cs : List Source) (i : Fin n)
      {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      memberSource (toℕ i) cs ≡ false → sizeᵉ d ≤ Ŝ →
      suc (dBound Ŝ (hopR Ŝ) (unconn sl (toℕ i ∷ cs)) (hopDᵉ Ŝ d) (syncSizeᵉ d))
        ≤ dBound Ŝ (hopR Ŝ) (unconn sl cs) r s
     ) →
    -- hop-step-gives  (Verify-Budget-Sufficient/Wet.agda:3877)
    (∀ (V R U r s s′ : ℕ) → suc s′ ≤ s + suc V →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s
     ) →
    -- hop-step-needs  (Verify-Budget-Sufficient/Wet.agda:3883)
    (∀ (V R U r s s′ : ℕ) →
      suc (dBound V R U r s′) ≤ dBound V R U (suc r) s → suc s′ ≤ s + suc V
     ) →
    -- unconn-keeps  (Verify-Budget-Sufficient/Wet.agda:4087)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (sched : Sched Γ) (st : EvalSt e) (sched′ : Sched Γ) (st′ : EvalSt e) →
      Keeps sched st sched′ st′ →
      unconn (Sched.slots sched′) (EvalSt.connectedShares st′)
        ≤ unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- sharedConnect-unconn  (Verify-Budget-Sufficient/Keeps-Ring.agda:1016)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
      (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
      (sched : Sched Γ) (st : EvalSt e) {dd : Closed Γ (lookup Γ i)} →
      Sched.slots sched i ≡ shared dd →
      memberSource (toℕ i) (EvalSt.connectedShares st) ≡ false →
      unconn (Sched.slots (proj₁ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
             (EvalSt.connectedShares
               (proj₂ (proj₂ (sharedConnect (gs fuel) i d κ id now sched st))))
      < unconn (Sched.slots sched) (EvalSt.connectedShares st)
     ) →
    -- obs-slot-shared  (Verify-Budget-Sufficient/Keeps-Ring.agda:464)
    (∀ {n} {Γ : Ctx n} {u} (s : Slot Γ (obs u)) →
      Σ (Closed Γ (obs u)) λ d → s ≡ shared d
     ) →
    -- share-live-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda:473)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ []) at id from s as subscribe) ∷ [])) ≡ []
     ) →
    -- share-spent-novals  (Verify-Budget-Sufficient/Keeps-Ring.agda:478)
    (∀ {n} {Γ : Ctx n} {u} {A : Set} (s : Source) (id : Id) →
      proj₁ (splitBurst {Γ = Γ} {u = u} {A = A}
              (((init s ∷ close s exhausted ∷ complete ∷ []) at id from s as subscribe) ∷ []))
        ≡ []
     ) →
    -- hasAtLeast-pad  (Verify-Budget-Sufficient/Measures.agda:222)
    (∀ (m : ℕ) (g : Gas) {n} → n ≤ m → gasPad m g hasAtLeast n
     ) →
    -- hasAtLeast-peel  (Verify-Budget-Sufficient/Measures.agda:268)
    (∀ {g : Gas} {m : ℕ} → g hasAtLeast suc m →
      Σ Gas (λ g′ → (g ≡ gs g′) × (g′ hasAtLeast m))
     ) →
    -- seed-covers  (Verify-Budget-Sufficient/Measures.agda:3113)
    (∀ (sz U : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * 1) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * 1 * 1) + towerℕ ((7 + sz) * 2)
     ) →
    -- budget-covers  (Verify-Budget-Sufficient/Measures.agda:3400)
    (∀ (sz U id : ℕ) → U ≤ sz →
      let V = towerℕ ((4 + sz) * suc (suc id)) in
      suc (suc V * suc (hopR V) * suc U)
        ≤ 2 ^ (sz * suc id * suc id) + towerℕ ((7 + sz) * suc (suc id))
     ) →
    -- oneShot-tail-dry  (Verify-Budget-Sufficient/Measures.agda:3367)
    (∀ {n} {Γ : Ctx n} {u} (vals : List (Val Γ u)) (src : Source) →
      any dryEvent (map value vals ++ close src exhausted ∷ complete ∷ []) ≡ false
     ) →
    -- connect-anchor  (Verify-Budget-Sufficient/Measures.agda:1847)
    (∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
      (id : Id) (i : Fin n) {d : Closed Γ (lookup Γ i)} → sl i ≡ shared d →
      let V = sizeBudgetAt e sl id in
      (hopDᵉ V d ≤ hopR V) × (syncSizeᵉ d ≤ V)
     ) →
    -- hopD-map-emit  (Verify-Budget-Sufficient/Measures.agda:2780)
    (∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u} (V : ℕ)
      (f : Tm Γ Δᵍ Δ (s ∷ Θ) u) (b : Exp Γ Δᵍ Δ Θ s) (v : Val Γ s) →
      (f₀ : Fn Γ [] [] [] s u) → hopDᵗ V f₀ ≤ hopDᵗ V f → pmᵗ V 0 f₀ ≤ pmᵗ V 0 f →
      hopDᵛ V s v ≤ hopDᵉ V b →
      hopDᵛ V u (applyFn f₀ v) ≤ hopDᵉ V (mapᵉ f b)
     ) →
    -- applyFn-size  (Verify-Budget-Sufficient/Measures.agda:3647)
    (∀ {n} {Γ : Ctx n} {s t} (V : ℕ)
      (fn : Fn Γ [] [] [] s t) (v : Val Γ s) → sizeᵛ s v ≤ V →
      sizeᵛ t (applyFn fn v) ≤ (2 + 2 * V) ^ (3 ^ sizeᵗ fn)
     ) →
    -- unconn-cons-≤  (Verify-Budget-Sufficient/Measures.agda:1217)
    (∀ {n} {Γ : Ctx n} (sl : Slots Γ) (cs : List Source)
      (s : Source) → unconn sl (s ∷ cs) ≤ unconn sl cs
     ) →
    -- shellSize-unfoldμ  (Verify-Budget-Sufficient/Measures.agda:1100)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      shellSizeᵉ (unfoldμ body) ≡ shellSizeᵉ body
     ) →
    -- inner-unfoldμ  (Verify-Budget-Sufficient/Measures.agda:1104)
    (∀ {n} {Γ : Ctx n} {t} (body : Exp Γ (t ∷ []) [] [] t) →
      innerᵉ (unfoldμ body) ≡ innerᵉ body
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
    let sl = Sched.slots sched
        Ψ  = ΨAt e sl
        B  = sizeCapAt e sl id
        Ŝ  = sizeCapAt e sl (suc id)
    in INV? Ψ B sched st ≡ true →
       pathB? B Ψ κ ≡ true →
       sizeᵉ b ≤ B →
       fnCapᵉ b ≤ Ψ →
       g hasAtLeast
         suc (dBound Ŝ (hopR Ŝ)
                     (unconn sl (EvalSt.connectedShares st))
                     (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
       let r = subscribeE g b κ id now sched st
       in (hasDry (proj₁ r) ≡ false)
          × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                  (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)

-- the wet face, assembled over its core.  (The cascade-level face
-- that used to sit beside it is gone: the 2026-08-12 mirror census
-- found its INV? half already proven at `cascade-wet-via-caps`
-- (.Caps-Bridge) and moved its dry half to `cascadeGo-nodry`
-- (.Burst-Walk § 8) — RECOVERY: git show 9b48235 restores the old
-- two-conjunct core.)
subscribeE-wet : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  let sl = Sched.slots sched
      Ψ  = ΨAt e sl
      B  = sizeCapAt e sl id
      Ŝ  = sizeCapAt e sl (suc id)
  in INV? Ψ B sched st ≡ true →
     pathB? B Ψ κ ≡ true →
     sizeᵉ b ≤ B →
     fnCapᵉ b ≤ Ψ →
     g hasAtLeast
       suc (dBound Ŝ (hopR Ŝ)
                   (unconn sl (EvalSt.connectedShares st))
                   (hopDᵉ Ŝ b) (syncSizeᵉ b)) →
     let r = subscribeE g b κ id now sched st
     in (hasDry (proj₁ r) ≡ false)
        × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
                (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) (suc id))
                (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
subscribeE-wet =
  subscribeE-wet-core subscribeE-walk
    mu-edge hop-edge connect-edge hop-step-gives hop-step-needs unconn-keeps
    sharedConnect-unconn obs-slot-shared
    -- these two must be instantiated EXPLICITLY: `splitBurst` computes on
    -- the literal event list, so the reduced statement no longer mentions
    -- Γ or u and Agda cannot solve those implicits from the expected type.
    (λ {n} {Γ} {u} {A} → share-live-novals {n} {Γ} {u} {A})
    (λ {n} {Γ} {u} {A} → share-spent-novals {n} {Γ} {u} {A})
    hasAtLeast-pad hasAtLeast-peel seed-covers budget-covers oneShot-tail-dry
    connect-anchor hopD-map-emit applyFn-size unconn-cons-≤
    shellSize-unfoldμ inner-unfoldμ

------------------------------------------------------------------
-- THE POP RING ON THE SIX-CONJUNCT FACE — PROVEN.  .Measures has the
-- stBounded? projections (schedHeadOf-bounded / schedGo-bounded /
-- pop-bounded); what the wet predicate needs on top is the SAME
-- induction at fnCapLive, and the head-KEEPING variant, which nothing
-- had: every existing inversion keeps the TAIL and drops the popped
-- element on the floor, so none of them bounds the arrival drain-dry
-- hands to cascade-dry.
--
-- The fnCap mirrors sit here rather than in .Measures for the reason
-- sweepLive-fnCap does: they exist for the wet face only, and the size
-- face has no use for them.
------------------------------------------------------------------

schedHeadOf-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  fnCapLive Ψ l ≡ true → fnCapLive Ψ l′ ≡ true
schedHeadOf-fnCap Ψ l eq bnd with LiveSource.pending l | eq | bnd
... | (t , v) ∷ ps | refl | bnd′ = proj₂ (∧-true _ _ bnd′)

schedGo-fnCap : ∀ {n} {Γ : Ctx n} (Ψ : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (fnCapLive Ψ) ls ≡ true → all (fnCapLive Ψ) ls′ ≡ true
schedGo-fnCap Ψ (l ∷ ls) eq bnd
  with ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) bnd
... | bl , bls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-fnCap Ψ (l ∷ ls) refl bnd | bl , bls | inj₁ _ | inj₂ (a′ , ls″) =
  ∧-intro bl (schedGo-fnCap Ψ ls eqR bls)
schedGo-fnCap Ψ (l ∷ ls) refl bnd | bl , bls | inj₂ (a″ , l′) | inj₁ _ =
  ∧-intro (schedHeadOf-fnCap Ψ l eqH bl) bls
schedGo-fnCap Ψ (l ∷ ls) eq bnd | bl , bls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = ∧-intro (schedHeadOf-fnCap Ψ l eqH bl) bls
... | false | refl = ∧-intro bl (schedGo-fnCap Ψ ls eqR bls)

pop-fnCap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  fnCapBounded? Ψ sched st ≡ true → fnCapBounded? Ψ sched′ st ≡ true
pop-fnCap Ψ sched st eq bnd
  with ∧-true (all (fnCapLive Ψ) (Sched.live sched)) _ bnd
... | bls , bns with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      ∧-intro (schedGo-fnCap Ψ (Sched.live sched) eqL bls) bns

-- the TAIL half, whole: the two store faces by their own inversions,
-- the two registry conjuncts untouched (the pop writes only `live`),
-- and the two slot conjuncts transported along pop-slots
pop-INV : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? Ψ B sched st ≡ true → INV? Ψ B sched′ st ≡ true
pop-INV Ψ B sched st eq inv with INV-parts Ψ B sched st inv
... | sb , fc , rl , rb , ss , sf =
  ∧-intro (pop-bounded B sched st eq sb)
  (∧-intro (pop-fnCap Ψ sched st eq fc)
  (∧-intro rl
  (∧-intro rb
  (∧-intro (subst (λ sl → (slotsSize sl ≤ᵇ B) ≡ true)
                  (sym (pop-slots sched eq)) ss)
           (subst (λ sl → (slotsFnCap sl ≤ᵇ Ψ) ≡ true)
                  (sym (pop-slots sched eq)) sf)))))

-- GAP 3's NAMED COMPANION, PROVEN.  The popped arrival IS the head of
-- some live source's pending list, so stBounded?'s pendings half and
-- fnCapBounded?'s live half bound it between them — one induction over
-- schedGo carrying BOTH faces at once, since valB? is their conjunction
-- and a second pass would repeat the same case tree
schedHeadOf-head : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (l : LiveSource Γ)
  {a : Arrival Γ} {l′ : LiveSource Γ} →
  schedHeadOf l ≡ inj₂ (a , l′) →
  boundedLive B l ≡ true → fnCapLive Ψ l ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
schedHeadOf-head B Ψ l eq bs bf with LiveSource.pending l | eq | bs | bf
... | (t , v) ∷ ps | refl | bs′ | bf′ =
  ∧-intro (proj₁ (∧-true (sizeᵛ (LiveSource.elemTy l) v ≤ᵇ B) _ bs′))
          (proj₁ (∧-true (fnCapᵛ (LiveSource.elemTy l) v ≤ᵇ Ψ) _ bf′))

schedGo-head : ∀ {n} {Γ : Ctx n} (B Ψ : ℕ) (ls : List (LiveSource Γ))
  {a : Arrival Γ} {ls′ : List (LiveSource Γ)} →
  schedGo ls ≡ inj₂ (a , ls′) →
  all (boundedLive B) ls ≡ true → all (fnCapLive Ψ) ls ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
schedGo-head B Ψ (l ∷ ls) eq bs bf
  with ∧-true (boundedLive B l) (all (boundedLive B) ls) bs
     | ∧-true (fnCapLive Ψ l) (all (fnCapLive Ψ) ls) bf
... | bl , bls | fl , fls with schedHeadOf l in eqH | schedGo ls in eqR
schedGo-head B Ψ (l ∷ ls) refl bs bf
  | bl , bls | fl , fls | inj₁ _ | inj₂ (a′ , ls″) =
  schedGo-head B Ψ ls eqR bls fls
schedGo-head B Ψ (l ∷ ls) refl bs bf
  | bl , bls | fl , fls | inj₂ (a″ , l′) | inj₁ _ =
  schedHeadOf-head B Ψ l eqH bl fl
schedGo-head B Ψ (l ∷ ls) eq bs bf
  | bl , bls | fl , fls | inj₂ (a″ , l′) | inj₂ (a′ , ls″)
  with schedEarlier a″ a′ | eq
... | true  | refl = schedHeadOf-head B Ψ l eqH bl fl
... | false | refl = schedGo-head B Ψ ls eqR bls fls

pop-head-bounded : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ B : ℕ) (sched : Sched Γ) (st : EvalSt e)
  {a : Arrival Γ} {sched′ : Sched Γ} →
  sched-next sched ≡ inj₂ (a , sched′) →
  INV? Ψ B sched st ≡ true →
  valB? B Ψ (arrTy a) (arrVal a) ≡ true
pop-head-bounded Ψ B sched st eq inv with INV-parts Ψ B sched st inv
... | sb , fc , _ with schedGo (Sched.live sched) in eqL | eq
... | inj₂ (a″ , ls) | refl =
      schedGo-head B Ψ (Sched.live sched) eqL
        (stB-live B sched st sb) (fcB-live Ψ sched st fc)

------------------------------------------------------------------
-- THE SEED ON THE SIX-CONJUNCT FACE AT THE CAPS LEVEL — PROVEN.
-- the stBounded? projection used to live here as `init-bounded`, read
-- against sizeBudgetAt; it was DELETED 2026-08-09 with the rest of #7's
-- superseded scaffold (git is the archive) because
-- capsAt-base-size relocates the same mkHot argument to
-- `Caps.cSize (capsAt …)`, the registry conjuncts are refl at st-init
-- (the registry is []), and the two slot conjuncts come from
-- capsAt-base-size and from ΨAt's own definition (`fnCapᵉ e + slotsFnCap`
-- dominates its second summand).
------------------------------------------------------------------

-- the fnCap face of one hot slot's initial pendings, off resolve-measure
-- at fnCapᵛ.  No `n≤1+n` here: inputFnCap has no `suc` to pay for,
-- because a script's own syntax carries no fn weight of its own
mkHot-fnCap : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (Ψ : ℕ) (i : Fin n) →
  slotFnCap (ins i) ≤ Ψ → all (fnCapLive Ψ) (mkHot ins i) ≡ true
mkHot-fnCap {Γ = Γ} ins Ψ i h with ins i | h
... | scripted (hot async) | h′ =
      ∧-intro (resolve-measure (fnCapᵛ (lookup Γ i)) Ψ 0 async h′) refl
... | scripted (cold _ _)  | _ = refl
... | shared _             | _ = refl

init-INV : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (id : Id) →
  INV? (ΨAt e ins) (sizeCapAt e ins id)
       (sched-init e ins) (st-init e) ≡ true
init-INV {n = n} e ins id =
  ∧-intro (∧-intro (all-concat-tab (boundedLive B) (mkHot ins) perSlotSz) refl)
  (∧-intro (∧-intro (all-concat-tab (fnCapLive Ψ) (mkHot ins) perSlotFc) refl)
  (∧-intro refl
  (∧-intro refl
  (∧-intro (T⇒≡true _ (≤⇒≤ᵇ slotsOK))
           (T⇒≡true _ (≤⇒≤ᵇ (m≤n+m (slotsFnCap ins) (fnCapᵉ e))))))))
  where
  B = sizeCapAt e ins id
  Ψ = ΨAt e ins
  slotsOK : slotsSize ins ≤ B
  slotsOK = ≤-trans (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
                    (capsAt-base-size e ins id)
  perSlotSz : ∀ i → all (boundedLive B) (mkHot ins i) ≡ true
  perSlotSz i = mkHot-bounded ins B i
                  (≤-trans (fᵢ≤sum-tab (λ j → slotSize (ins j)) i) slotsOK)
  perSlotFc : ∀ i → all (fnCapLive Ψ) (mkHot ins i) ≡ true
  perSlotFc i = mkHot-fnCap ins Ψ i
                  (≤-trans (fᵢ≤sum-tab (λ j → slotFnCap (ins j)) i)
                           (m≤n+m (slotsFnCap ins) (fnCapᵉ e)))

------------------------------------------------------------------
-- THE ROOT'S FUEL, at the moved anchor — PROVEN, and it is now an
-- IDENTITY rather than a height comparison.  `capsAt-tower` (.Caps)
-- lands `sizeCapAt e ins 1` under `towerℕ (capsH e ins 1)`; `prod≤3pow`
-- costs exactly THREE more stories (the (1+V)(1+R)(1+U) product with
-- R = hopR V); and `budgetAt`'s gas tower is DEFINED at height
-- `3 + capsHt sz 1` — the same recurrence, plus those same three.  That
-- is the point of a recurrence-defined budget: domination is by
-- construction, and the only arithmetic left is the ≤ that says the pad
-- summand does not get in the way.
------------------------------------------------------------------

-- ABSTRACT, and deliberately: this is the ONE member of the burst
-- chain that went from postulate to definition, and an unfoldable
-- body here is a body Verify-Well-Formed's `with` on
-- budget-sufficient can be asked to reduce.  Nothing needs to see
-- through it — every consumer wants the hasAtLeast, never its proof.
abstract
  caps-fuel-root : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
    budgetAt e ins 0 hasAtLeast
      suc (dBound (sizeCapAt e ins 1) (hopR (sizeCapAt e ins 1))
                  (unconn ins []) (hopDᵉ (sizeCapAt e ins 1) e)
                  (syncSizeᵉ e))
  caps-fuel-root e ins =
    hasAtLeast-mono demand (budget-hasAtLeast sz (capsBase e ins) 0)
    where
    sz : ℕ
    sz = sizeᵉ e + slotsSize ins
    V  : ℕ
    V  = sizeCapAt e ins 1
    U  : ℕ
    U  = unconn ins []
    6≤V : 6 ≤ V
    6≤V = 6≤capsAt-size e ins 0
    sz≤V : sizeᵉ e ≤ V
    sz≤V = size≤sizeCapAt e ins 1
    U≤V : U ≤ V
    U≤V = ≤-trans (unconn≤slots ins [])
                  (≤-trans (m≤n+m (slotsSize ins) (2 + sizeᵉ e))
                           (capsAt-base-size e ins 1))
    s≤V : syncSizeᵉ e ≤ V
    s≤V = ≤-trans (syncSize≤sizeᵉ e) sz≤V
    r≤R : hopDᵉ V e ≤ hopR V
    r≤R = hopD-cap V e (≤-trans (≤ᵇ⇒≤ 2 6 _) 6≤V) sz≤V
    demand : suc (dBound V (hopR V) U (hopDᵉ V e) (syncSizeᵉ e))
               ≤ 2 ^ (sz * 1 * 1) + towerℕ (3 + capsHgo (capsBase e ins) 1)
    demand =
      ≤-trans (s≤s (dBound-bound s≤V r≤R))
      (≤-trans (prod≤3pow V U 6≤V U≤V)
      (≤-trans (tower-3 (capsH e ins 1) V (proj₁ (capsAt-tower e ins 1)))
               (m≤n+m (towerℕ (3 + capsHgo (capsBase e ins) 1)) (2 ^ (sz * 1 * 1)))))

------------------------------------------------------------------
-- the burst cores — the contract instantiated at the root.  The root
-- subscribes the program itself from the initial machine: init-INV
-- seeds the six-conjunct invariant at the caps level, root is a
-- bounded continuation for free, the program is its own size witness
-- through capsAt's base, and caps-fuel-root covers the demand.
------------------------------------------------------------------

burst-wet : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in (hasDry (proj₁ r) ≡ false)
     × (INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
             (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) 1)
             (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
burst-wet e ins =
  subscribeE-wet (budgetAt e ins 0) e root 0 0
                 (sched-init e ins) (st-init e)
                 (init-INV e ins 0) refl
                 (size≤sizeCapAt e ins 0)
                 (m≤m+n (fnCapᵉ e) (slotsFnCap ins))
                 (caps-fuel-root e ins)

burst-dry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  hasDry (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                            (sched-init e ins) (st-init e))) ≡ false
burst-dry e ins = proj₁ (burst-wet e ins)

burst-bounded : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  let r = subscribeE (budgetAt e ins 0) e root 0 0
                     (sched-init e ins) (st-init e)
  in INV? (ΨAt e (Sched.slots (proj₁ (proj₂ r))))
          (sizeCapAt e (Sched.slots (proj₁ (proj₂ r))) 1)
          (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
burst-bounded e ins = proj₂ (burst-wet e ins)

-- `cascade-dry`, `drain-dry`, `budget-sufficient` MOVED to
-- `.Caps-Bridge` (the 2026-08-05 upside-down ruling) — caps-threaded
-- there, consuming `cascade-wet-via-caps`.  `burst-wet`/`burst-dry`/
-- `burst-bounded`/`pop-INV`/`pop-head-bounded` stay here: `.Caps-Bridge`
-- consumes all five unchanged as the INV?-only half of its own burst
-- and pop.
