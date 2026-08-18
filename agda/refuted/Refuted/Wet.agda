-- ══════════════════════════════════════════════════════════════════
-- WET: the ceiling and the ℓ-ledger, both refuted
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
--
-- THIS TREE IS OUTSIDE `agda/src` ON PURPOSE (Anthony, 2026-08-18).
-- Keeping a dead route in `src` forces `src` to keep whatever machinery
-- makes the route STATE-able, and that machinery is otherwise deletable:
-- these two files held seven definitions alive in Measures for no other
-- reason.  So refutations live here, are checked by `make refuted`, and
-- are NOT subject to the wiring law — nothing in `src` may import them.
-- They do not change, so `src` refers to them in COMMENTS (`-- REFUTED:`).
-- ══════════════════════════════════════════════════════════════════
module Refuted.Wet where

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
                                inputsBelowᵉ;
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
open import Rx.Frame-Width using (outWᵉ; outWᵛ)
open import Rx.Hop-Depth using (hopDᵉ; hopDᵗ; hopDᵗˢ; hopDᵛ; pmᵉ; pmᵗ; pmᵗˢ;
                                 pm-elimGᵉ; pm-elimGᵗ; pm-elimGᵗˢ;
                                 hopD-elimGᵉ; hopD-elimGᵗ; hopD-elimGᵗˢ;
                                 hopD-unfoldμ)
open import Rx.Slot-Hop using (slotHop)
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
open import Verify-Budget-Sufficient.Caps public
open import Verify-Budget-Sufficient.Wet.Part5 public

open import Verify-Budget-Sufficient.Wet.Part6
open import Refuted.Anchor

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
--       the burst face's own landing (root subscribe, capsAt 0 → capsAt 1)
--       has no supplier either.  The missing companion is a
--       subscribeE-level analogue of `fLvl`, and it is NAMED here
--       rather than assumed.  It is the SAME hole the two *All frame
--       faces wait on (.Caps-Face, conjunct (a) there), seen from the
--       wet side — one companion would close both.
--       AND THE COMPANION IS NOT A CLOSED FORM (measured,
--       Sub-Charge-Probe (DELETED; git history)): a subscribe installs frames
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
--
-- RULED 2026-08-13 (design session): THE NESTING BUDGET IS THE GAS.
-- The one instantiation (a) waited on is ruled, and the ℓ finding in
-- the parameter map above is what forced the ruling's shape:
--
--   · The charge companion recurses on the hasAtLeast PEEL COUNT,
--     mirroring subscribeE's own gas recursion.  Within one peel
--     level, frame work is non-recursive and the caps face's
--     per-frame counting already bounds it; every subscribe → frame →
--     subscribe re-entry costs exactly one peel, because
--     subscribeInner / sharedConnect / μ are the machine's only peel
--     sites and deferᵉ crosses a tick (closed by typing, above).
--     MEASURED 2026-08-13 (Verify-Budget-Sufficient/Demand-Probe):
--     demand is additive — one peel per *All layer, per μ, per first
--     connect; zero for defer; payload-driven layers add linearly
--     (h* = k+1 single-wrap, 2k+1 double-wrap).  Subscribe-time
--     region only; the delivery region stays unprobed (cascadeGo
--     mints its own gas), so this receipt AIMS the restatement and
--     moves no risk class.  The companion's total is then
--     entry-computable through G (dBound at the reset caps Ŝ), and
--     the supply half is the seed-covers / budget-covers class,
--     already stated and consumed below.
--   · The walk restates its running position as a LEVEL j —
--     frameStep iterates on capsAt e sl id — retiring the capᴱ W E
--     ledger.  The landing becomes j_total ≤ capsH e sl id, which is
--     caps-tick's own one-instant blowup, ground on the caps side.
--   · ℓ THEREBY DECOUPLES FROM Ŝ.  Freed from walkCap's exponential
--     consumption, ℓ floats to pathLen κ + G ⊔ the registry bound,
--     where `suc Ŝ ≤ G` is harmless.  Both refutations — the way-out
--     ceiling (wet-ceiling-absurd) and the way-in ℓ pin
--     (wet-ell-absurd, below) — dissolve at one stroke, which is the
--     sign they were ONE obstruction: the exponential way-out is what
--     pinned ℓ down to Ŝ; the demand is what pushes ℓ up past it.
--   · VERIFY FIRST in the restatement: the mintCount / burstLen
--     conjuncts must re-index to the level machinery (cReg-driven
--     per-level counting), not to walkCap Ω ℓ G.  If any consumer
--     needs them at a caps level, the loop re-enters exactly there —
--     that is the restatement's first falsity check, before any
--     clause is ground.
--   · (b) is unchanged by this ruling: the four INV? conjuncts with
--     no caps counterpart stay explicit hypotheses on the outer face
--     (the Caps-Bridge pattern — free at the call site).
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

-- THE WAY-IN INSTANCE (2026-08-13): pinning the walk's length ledger ℓ
-- to the caps anchor is refuted by the same loop, with no walkCap and
-- no ceiling needed — the demand measured AT Ŝ already exceeds Ŝ
-- whenever the contract has content, so `pathLen κ + G ≤ Ŝ` cannot
-- hold.  This is what generalises GAP 4 past its W/E instance: ANY
-- walk parameter pinned to Ŝ inherits this, because sucV≤d is about
-- the demand and the anchor alone.  Ruling in GAP 4's header.
wet-ell-absurd : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
  (id : Id) (p U r s G : ℕ) →
  1 ≤ r + suc (hopR (sizeCapAt e sl (suc id))) * U →
  dBound (sizeCapAt e sl (suc id)) (hopR (sizeCapAt e sl (suc id))) U r s ≤ G →
  p + G ≤ sizeCapAt e sl (suc id) →
  ⊥
wet-ell-absurd e sl id p U r s G 1≤ dem len =
  <-irrefl refl
    (≤-trans (sucV≤d (sizeCapAt e sl (suc id))
                     (hopR (sizeCapAt e sl (suc id))) U r s G 1≤ dem)
             (≤-trans (m≤n+m G p) len))
