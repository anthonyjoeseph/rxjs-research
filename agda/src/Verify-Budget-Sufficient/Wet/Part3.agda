-- STRATUM 2b of Verify-Budget-Sufficient: THE WET FAMILY, part 3 of 6.
--
-- blocks 32-71: the cascade walk and its single-member companions,
-- consuming the wet block above as finished facts.
--
-- Split from Verify-Budget-Sufficient.Wet on 2026-08-12.  The three
-- multi-member blocks (36/13/5 members, genuine cycles) each get their
-- own module so an edit re-checks one part instead of 4.7k lines.
-- Consumers import the Wet umbrella and are unaffected.

module Verify-Budget-Sufficient.Wet.Part3 where


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
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; _++_; length; tabulate; concat; map)
open import Data.Bool.ListAction using (all; any)
open import Data.Nat.ListAction  using (sum)
open import Data.Fin     using (Fin; toℕ)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Maybe   using (Maybe; nothing; just)
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
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


open import Verify-Budget-Sufficient.Wet.Part2 public

------------------------------------------------------------------
-- THE FOLD DECOMPOSITION, PROVEN: cascadeGo threads the walk
-- invariant chain by chain over chainStep-wet.  This is the
-- structure the cascade fold-threading memo demanded — per-cascade growth
-- threads through the fold at a moving ledger position, with the
-- registry cardinality rider (INV?'s length conjunct) available at
-- the latch for the eventual receipt arithmetic.  Not consumed yet:
-- the cascade dry face keeps riding the landing core below until the
-- quantitative debt (memo (3)) closes.
------------------------------------------------------------------

cascadeGo-walk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ψ W : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) (E : ℕ) →
  3 ≤ E →
  INV? Ψ (capᴱ W E) sched st ≡ true →
  all (λ rc → pathB? (capᴱ W E) Ψ (proj₂ rc)) chains ≡ true →
  valB? (capᴱ W E) Ψ (arrTy a) (arrVal a) ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ E′ → (E ≤ E′)
     × (INV? Ψ (capᴱ W E′) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstB? (capᴱ W E′) Ψ (proj₁ r) ≡ true)
cascadeGo-walk Ψ W a id [] sched st E 3≤E inv chB vB =
  E , ≤-refl , inv , refl
cascadeGo-walk Ψ W a id ((rid , c) ∷ chains) sched st E 3≤E inv chB vB
  with ∧-true (pathB? (capᴱ W E) Ψ c) _ chB
... | pc , pchains with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = cascadeGo-walk Ψ W a id chains sched st E 3≤E inv pchains vB
... | false =
  let st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
      (E₁ , E≤E₁ , inv₁ , em₁) =
        chainStep-wet Ψ W id a c sched st₀ E 3≤E inv pc vB
      cap≤ = capᴱ-mono W E≤E₁
      (E₂ , E₁≤E₂ , inv₂ , em₂) =
        cascadeGo-walk Ψ W a id chains
          (proj₁ (proj₂ (chainStep id a c sched st₀)))
          (proj₂ (proj₂ (chainStep id a c sched st₀)))
          E₁ (≤-trans 3≤E E≤E₁) inv₁
          (chainsB?-widen chains cap≤ pchains)
          (valB?-widen (arrTy a) (arrVal a) cap≤ vB)
  in E₂ , ≤-trans E≤E₁ E₁≤E₂ , inv₂ ,
     all-++-intro _ (proj₁ (chainStep id a c sched st₀)) _
       (burstB?-widen (proj₁ (chainStep id a c sched st₀))
                      (capᴱ-mono W E₁≤E₂) em₁)
       em₂

------------------------------------------------------------------
-- the three cores
------------------------------------------------------------------

------------------------------------------------------------------
-- THE PROOF DESIGN for the three cores (2026-07-19, after the tower
-- attack).  The wet contract for the mutual subscription block is one
-- strengthened induction, consumed through `hasAtLeast`:
--
--   fuel hasAtLeast need(args) → no dry × stores land bounded
--
-- and the induction that defines/bounds `need` is LEXICOGRAPHIC over
-- the three decrement edges:
--
--   1. share connect — decreases the UNCONNECTED-SLOT COUNT
--      (connectedShares latches; a def's walk can only shrink it).
--   2. μ-unfold — decreases SYNC-REACHABLE SIZE (syncSizeᵉ, deferᵉ
--      a leaf): unfoldμ substitutes `μᵉ body` only at var positions,
--      and vars are TYPE-GUARANTEED defer-gated (Δᵍ→Δ moves only at
--      deferᵉ), so the substituted copies are invisible to the
--      synchronous walk.  DISCHARGED above: syncSize-unfoldμ /
--      unfoldμ-shrinks, machine-checked.
--   3. subscribeInner — decreases the DERSHOWITZ–MANNA MULTISET of
--      SHELL sizes (2026-07-20: the SHELL DESIGN, adopted with
--      Anthony's approval, replacing the layer-derivation reading).
--      A runtime obs value IS a closed expression; its measure is
--      measureE = counts B ∘ shellsᵉ — the multiset of operator-
--      skeleton sizes of the value and every sync-reachable
--      embedded observable (Rx.Exp.shellsᵉ), a pure function of
--      syntax.  Shells count Exp constructors ONLY (Tm material
--      weightless, strmᵗ/deferᵉ leaves), which buys the design's
--      two load-bearing facts, both PROVEN above:
--        · substitution invariance (shellSize-subΘ): subΘ rewrites
--          only Tm material, so instantiation preserves every
--          shell size EXACTLY.  No inflation — an instantiated
--          template's multiset is a class-preserved copy of the
--          template's plus the plugged obs values' own shells
--          (reify-inner: a plug's footprint is void, its shells
--          join the inner multiset verbatim).
--        · free side conditions: every shell of e is ≤ sizeᵉ e
--          (shells-≤/shellsᵛ-≤) and shells number ≤ sizeᵉ e
--          (shells-len) — so stBounded?'s sizeᵛ cap bounds both
--          the classes (≤ B) and the entry sum (≤ V, the rank
--          bridge's side condition).  NO new invariant; the whole
--          Layered derivation apparatus is deleted (git: 1fbc59c).
--      The hops:
--        · embedded-value hop (subscribing a value that sits as a
--          strmᵗ subtree of the carrier — of-list literals under
--          closed evaluation, evalWith (strmᵗ e) []ᵃ = e): its
--          shellsᵉ is a CONTIGUOUS sublist of the carrier's inner
--          (innerᵗ (strmᵗ e) = shellsᵉ e), and the carrier's own
--          shell rides on top — strict sub-multiset, ≺-embed.
--        · eval/scan-produced hop (applyFn/evalWith instantiates a
--          template): by shellSize-subΘ the produced multiset =
--          the fn-body strmᵗ subtree's sub-multiset, classes on
--          the nose, ⊎ the plugged obs values' shells.  The first
--          part is the embed shape again; the plugged part is
--          where the LEDGER lives — the plugs are prior stored
--          values whose shells the global multiset already owns
--          (deliveries ≤ syntactic occurrences because subΘ
--          COPIES trees — SYNC-LINEARITY, PROVEN above:
--          plugs-lenᵉ bounds the plug cardinality by occsᵉ · V,
--          occs≤syncᵉ caps occurrences syntactically, and
--          inner-len-subΘ is the exact length bookkeeping).  The
--          multiset-level input is the subΘ multiset equation
--          (subΘ-countsᵉ, proven); subΘ-capᵉ is its All-cap
--          shadow and subΘ-shells-len its entry-sum package.
--        · share-crossing hop (a template's `input` hits a slot):
--          exits the per-value measure — it anchors against the
--          slot's own element of the GLOBAL multiset {program} ⊎
--          {slots}; that re-anchoring is the ownership half of the
--          ledger (the cascade fold-threading memo), not the per-value order.
--      (The 2026-07-19 layer-derivation design worked but carried
--      an unfixable wart: unused env entries gave layers with no
--      syntactic footprint, so the entry-sum side condition needed
--      its own invariant.  The design before THAT — lex (skeleton,
--      value size), subterm-ordered — is REFUTED: chain two
--      obs-typed scans directly, second fn λ(b,v). mergeAll(of[snd
--      x]), and the embedded-value hop lands on a first-scan ac
--      whose template is subterm-incomparable with the carrier's
--      and can dwarf it.)
--
-- THE DEMAND, closed-form and PROVEN (dBound above).  Fuel is
-- depth-consumed, so the contract carries
--
--   fuel hasAtLeast suc (dBound V R U r s)
--
-- with V the store size bound, R = (suc V)^(suc B) the store rank
-- cap (rank-lt-pow), U = unconn, r = the current value's rank, s =
-- the current expression's syncSize.  Each decrement edge consumes
-- one gs against a strictly smaller demand: dBound-μ
-- (unfoldμ-shrinks drops s), dBound-hop (rank-mono-≺ over
-- ≺-embed/≺-replace drops r, s resets ≤ V), dBound-connect
-- (unconn-insert drops U, r resets ≤ R) — all three proven, so the
-- clause proofs only apply them.  dBound < (suc V)^(B+3)·suc U:
-- one exponential story above the store bound, while the seeded
-- budget's tower gains (suc sz) stories per instant —
-- budget-hasAtLeast's tower summand dominates with room to spare,
-- and every literal-headed demand (no chained scans) is already
-- covered by the 2^(sz·(id+1)²) summand alone.
--
-- The cores below are the contract instantiated at
-- the root burst (burst-dry/-bounded) and at the chain fold
-- (the cascade fold-threading memo); the disjointness argument (each registration's
-- path owns its minted nodes, so per-cascade store traffic is
-- structure-bounded) supplies the store-boundedness half.
--
-- THE WALK INVARIANT (2026-07-20, the clause-grind session).  The
-- stated subscribeE-wet is the contract's OUTER FACE only — its
-- `sizeᵉ b ≤ V` hypothesis holds at both instantiation sites (root
-- program; stored values) but does NOT self-apply down the walk,
-- and the induction must generalize internally:
--   · μ edge: unfoldμ COPIES the closed μ, so sizeᵉ grows past any
--     fixed cap along iterated unfolds.  Thread the SHELL caps
--     instead — every shell preserved-or-stepped-down and the
--     count exactly preserved (shells-unfoldμ-cap/-len above);
--     sizeᵉ is only needed for STORABILITY, against the (tower)
--     landing budget, not against V.
--   · no fixed (V, R) survives the walk: a scan frame folds each
--     value with NO fuel peel (fuel is depth-consumed; breadth is
--     free), and each fold is one base swap (applyFn-size), so
--     mid-walk stores legitimately outgrow the entry cap V and
--     later inner subscriptions carry ranks past R.  A cap indexed
--     by REMAINING GAS fails for the same reason (folds do not
--     peel gas).
--   · the missing accounting is a per-instant BREADTH LEDGER: the
--     value-list lengths threading stepFrame/pushBurst.  SETTLED
--     2026-07-24 — see THE WALK LEDGER section above: the sharp
--     eval bound (caseW, substitution-invariant exponent) replaces
--     applyFn-size's self-inflating one, the ledger is the
--     multiplicative exponent capᴱ W₀ E with one uniform ×3^(suc Ψ)
--     rule per eval edge and ×2 per cheap edge, fold-runs cost
--     3^(suc Ψ · m) by scanVals-sharp, and INV? (store bounds +
--     fn caps + registry cardinality + chain frames) is the
--     invariant the walk contracts thread.  The count cap's DESIGN
--     closed 2026-07-24 (memo (5), THE WIDTH LEDGER, corrected to
--     the recurrence-closed walkCap form): widths are
--     substitution-invariant, so run lengths and the per-lineage
--     fold count 𝔉 anchor at walkCap — all entry-frozen.  The
--     JOINT FACE (subscribeE-walk above) states wet + dry + ledger
--     together; what remains is its clause grind and the landing
--     composition; until THAT lands, the landing halves live in
--     these two cores and nowhere else.
------------------------------------------------------------------

------------------------------------------------------------------
-- (W11-A) THE FLAT STATE LEMMAS.  Ω never moves, so each of these
-- is "invariant in, invariant out": the size side's ledger edges
-- (register-INV's ×2 length rider, the widening chains) all vanish,
-- and widthOK? has no length conjunct to pay them with.  Every
-- proof below is its fnCap counterpart with the arithmetic deleted.
------------------------------------------------------------------

-- widthOK? is a FLAT four-way ∧ (no nested stBounded?/fnCapBounded?
-- pair), so one projector serves the whole block — same reason
-- INV-parts exists: `∧-true _ _` alone leaves a stuck metavariable
WOK-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) → widthOK? Ω sched st ≡ true →
  (all (ofWLive Ω) (Sched.live sched) ≡ true)
  × (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st) ≡ true)
  × (regsΩ? Ω (EvalSt.registry st) ≡ true)
  × ((slotsOfW (Sched.slots sched) ≤ᵇ Ω) ≡ true)
WOK-parts Ω sched st h
  with ∧-true (all (ofWLive Ω) (Sched.live sched)) _ h
... | lv , r1
  with ∧-true (all (λ kv → ofWNode Ω (proj₂ kv)) (EvalSt.nodes st)) _ r1
... | nd , r2 with ∧-true (regsΩ? Ω (EvalSt.registry st)) _ r2
... | rg , sl = lv , nd , rg , sl

-- the node-install ring (mirror of setNode-bounded / setNode-fnCap)
setNode-ofW : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId) (ns : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  ofWNode Ω ns ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  all (λ kv → ofWNode Ω (proj₂ kv)) (setNode nid ns nodes) ≡ true
setNode-ofW Ω nid ns []             bn h = ∧-intro bn refl
setNode-ofW Ω nid ns ((k , s′) ∷ r) bn h with k ≡ᵇ nid
... | true  = ∧-intro bn (proj₂ (∧-true _ _ h))
... | false = ∧-intro (proj₁ (∧-true _ _ h))
                      (setNode-ofW Ω nid ns r bn (proj₂ (∧-true _ _ h)))

install-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (nid : NodeId) (ns : NodeState Γ) →
  ofWNode Ω ns ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (installNode nid ns st) ≡ true
install-width Ω sched st nid ns bn h =
  ∧-intro (proj₁ P)
  (∧-intro (setNode-ofW Ω nid ns (EvalSt.nodes st) bn (proj₁ (proj₂ P)))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- registering a chain: one entry appended, its frames bounded by
-- hypothesis.  No length rider means no ledger edge at all — the
-- single place where the width walk is strictly cheaper than the
-- size walk rather than merely equal
register-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (src : Source) (κ : Path Γ u t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → pathΩ? Ω κ ≡ true →
  widthOK? Ω sched (register src κ st) ≡ true
register-width {u = u} Ω src κ sched st h pκ =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (all-++-intro _ (EvalSt.registry st) _
              (proj₁ (proj₂ (proj₂ P))) (∧-intro pκ refl))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

addLive-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (sched : Sched Γ) (st : EvalSt e) (l : LiveSource Γ) →
  ofWLive Ω l ≡ true → widthOK? Ω sched st ≡ true →
  widthOK? Ω (record sched { live = l ∷ Sched.live sched }) st ≡ true
addLive-width Ω sched st l bl h =
  ∧-intro (∧-intro bl (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (proj₁ (proj₂ (proj₂ P))) (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- the live sweep, width face (mirror of sweepLive-bounded/-fnCap)
sweepLive-ofW : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ)
  (reg : List (RegId × Source × Chain Γ t)) (ls : List (LiveSource Γ)) →
  all (ofWLive Ω) ls ≡ true →
  all (ofWLive Ω) (sweepLive reg ls) ≡ true
sweepLive-ofW Ω = sweepLive-all (ofWLive Ω)

-- dropping a source only shrinks the registry
dropSource-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (src : Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (dropSource src reg) ≡ true
dropSource-regsΩ Ω = dropSource-all (λ en → pathΩ? Ω (proj₂ (proj₂ (proj₂ en))))

latch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { registry = dropSource src (EvalSt.registry st)
               ; completedSources = src ∷ EvalSt.completedSources st })
    ≡ true
latch-width Ω src sched st h =
  ∧-intro (proj₁ P)
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω src (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where P = WOK-parts Ω sched st h

-- completedSources / dying / delivered / connectedShares are read
-- by no conjunct of widthOK? either
shareLatch-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → widthOK? Ω sched (shareLatch i b st) ≡ true
shareLatch-width Ω i false sched st h = h
shareLatch-width Ω i true  sched st h = h

delivered-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (rid : RegId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { delivered = rid ∷ EvalSt.delivered st })
    ≡ true
delivered-width Ω rid sched st h = h

connectShare-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (src : Source) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched
    (record st { connectedShares = src ∷ EvalSt.connectedShares st }) ≡ true
connectShare-width Ω src sched st h = h

-- the admitted fan-out chains inherit their frame widths
shareAdmit-Ω : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (i : Fin n)
  (reg : List (RegId × Source × Chain Γ t)) → regsΩ? Ω reg ≡ true →
  all (λ rp → pathΩ? Ω (proj₂ rp)) (shareAdmit i reg) ≡ true
shareAdmit-Ω Ω i []                      h = refl
shareAdmit-Ω {Γ = Γ} Ω i ((rid , src , (u , q)) ∷ r) h
  with sameSource (toℕ i) src | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | no  _    = shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h))
... | true  | yes refl =
      ∧-intro (proj₁ (∧-true (pathΩ? Ω q) _ h))
              (shareAdmit-Ω Ω i r (proj₂ (∧-true (pathΩ? Ω q) _ h)))

shareFinish-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (b : Bool) (emits : Stream Γ t)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω (proj₁ (proj₂ (shareFinish i b (emits , sched , st))))
             (proj₂ (proj₂ (shareFinish i b (emits , sched , st)))) ≡ true
shareFinish-width Ω i false emits sched st h = h
shareFinish-width Ω i true  emits sched st h =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (dropSource-regsΩ Ω (toℕ i) (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P)))))
  where
  kept = dropSource (toℕ i) (EvalSt.registry st)
  P    = WOK-parts Ω sched st h

------------------------------------------------------------------
-- (W11-A′) THE BURST HELPERS.  eventΩ? only constrains `value`, so
-- every marker list is refl and the real content is the value lists.
------------------------------------------------------------------

mapValue-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) (map value vs) ≡ true
mapValue-Ω Ω u []       h = refl
mapValue-Ω Ω u (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (mapValue-Ω Ω u vs (proj₂ (∧-true _ _ h)))

finList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then complete ∷ [] else []) ≡ true
finList-Ω Ω true  = refl
finList-Ω Ω false = refl

closeList-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (src : Source) (b : Bool) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω)
      (if b then close src exhausted ∷ [] else []) ≡ true
closeList-Ω Ω src true  = refl
closeList-Ω Ω src false = refl

sharedPlumb-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (str : Stream Γ u) →
  burstΩ? Ω str ≡ true → burstΩ? Ω (sharedPlumb str) ≡ true
sharedPlumb-Ω Ω []         h = refl
sharedPlumb-Ω Ω (em ∷ ems) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (sharedPlumb-Ω Ω ems (proj₂ (∧-true _ _ h)))

-- a script's sync prefix, elementwise off the slot's ofW SUM (the
-- width seed is a sum dominating the max, exactly as ΨAt is)
sumVals-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (u : Ty) (vs : List (Val Γ u)) →
  sum (map (ofWᵛ u) vs) ≤ Ω → all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true
sumVals-Ω Ω u []       hw = refl
sumVals-Ω Ω u (v ∷ vs) hw =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (m≤m+n (ofWᵛ u v) _) hw)))
          (sumVals-Ω Ω u vs (≤-trans (m≤n+m _ (ofWᵛ u v)) hw))

-- one slot's width, projected out of widthOK?'s slots sum
slotOfW-at : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → slotOfW (Sched.slots sched i) ≤ Ω
slotOfW-at Ω i sched st h =
  ≤-trans (fᵢ≤sum-tab (λ j → slotOfW (Sched.slots sched j)) i)
          (≤ᵇ⇒≤ _ _ (T-to (proj₂ (proj₂ (proj₂ (WOK-parts Ω sched st h))))))

------------------------------------------------------------------
-- (W11-B) THE FRAME ANALYTICS.  Every fact the frames need about
-- values, nodes and the registry, at the flat width.  These are the
-- W2/W4 mirrors with the ledger stripped: no caseW rider (widths
-- are substitution-invariant, so eval never widens), no capᴱ, no E.
------------------------------------------------------------------

applyFn-ofW : ∀ {n} {Γ : Ctx n} {s t} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s t) (v : Val Γ s) →
  ofWᵛ s v ≤ Ω → ofWᵗ fn ≤ Ω → ofWᵛ t (applyFn fn v) ≤ Ω
applyFn-ofW Ω fn v hv hfn = ofW-evalWith Ω fn (v ∷ᵃ []ᵃ) (hv , tt) hfn

map-applyFn-Ω : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] s u) → ofWᵗ fn ≤ Ω →
  (vs : List (Val Γ s)) → all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (applyFn fn) vs) ≡ true
map-applyFn-Ω Ω fn hfn []       h = refl
map-applyFn-Ω {s = s} Ω fn hfn (v ∷ vs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-ofW Ω fn v
            (≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))) hfn)))
          (map-applyFn-Ω Ω fn hfn vs
            (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))

-- one fold run: the accumulator and every output stay under Ω,
-- because applyFn never widens (ofW-evalWith)
scanVals-ofW : ∀ {n} {Γ : Ctx n} {s u} (Ω : ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s)) →
  ofWᵗ fn ≤ Ω → ofWᵛ u ac ≤ Ω →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vs ≡ true →
  (ofWᵛ u (proj₂ (scanVals fn ac vs)) ≤ Ω)
  × (all (λ o → ofWᵛ u o ≤ᵇ Ω) (proj₁ (scanVals fn ac vs)) ≡ true)
scanVals-ofW Ω fn ac []       hfn hacc _ = hacc , refl
scanVals-ofW {s = s} Ω fn ac (v ∷ vs) hfn hacc h =
  proj₁ IH , ∧-intro (T⇒≡true _ (≤⇒≤ᵇ acc′OK)) (proj₂ IH)
  where
  hv     = ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h)))
  acc′OK = applyFn-ofW Ω fn (ac , v) (⊔-lub hacc hv) hfn
  IH     = scanVals-ofW Ω fn (applyFn fn (ac , v)) vs hfn acc′OK
             (proj₂ (∧-true (ofWᵛ s v ≤ᵇ Ω) _ h))

takeVals-Ω : ∀ {n} {Γ : Ctx n} {s} (Ω : ℕ) (k : ℕ) (vals : List (Val Γ s)) →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (takeVals k vals)) ≡ true
takeVals-Ω {s = s} Ω k vals h = takeVals-all (λ v → ofWᵛ s v ≤ᵇ Ω) k vals h

cutThrough-regsΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  regsΩ? Ω reg ≡ true → regsΩ? Ω (proj₁ (cutThrough nid d wm dy reg)) ≡ true
cutThrough-regsΩ Ω nid d wm dy []                    h = refl
cutThrough-regsΩ Ω nid d wm dy ((rid , src , c) ∷ r) h
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-regsΩ Ω nid d wm dy r (proj₂ (∧-true _ _ h))
... | true  | kept , closes , rids | ih = ih
... | false | kept , closes , rids | ih = ∧-intro (proj₁ (∧-true _ _ h)) ih

cutThrough-closesΩ : ∀ {n} {Γ : Ctx n} {t} (Ω : ℕ) (nid : NodeId)
  (d : List RegId) (wm : RegId) (dy : List Source)
  (reg : List (RegId × Source × Chain Γ t)) →
  all (eventΩ? Ω) (proj₁ (proj₂ (cutThrough nid d wm dy reg))) ≡ true
cutThrough-closesΩ Ω nid d wm dy []                    = refl
cutThrough-closesΩ Ω nid d wm dy ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid d wm dy r
     | cutThrough-closesΩ Ω nid d wm dy r
... | false | kept , closes , rids | ih = ih
... | true  | kept , closes , rids | ih
      with any (_≡ᵇ rid) d ∧ memberSource src dy
...   | true  = ih
...   | false = ∧-intro refl ih

-- a node lookup carries the width face of whatever it finds
NodeΩ : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeΩ Ω nothing   = ⊤
NodeΩ Ω (just ns) = ofWNode Ω ns ≡ true

lookupNode-Ω : ∀ {n} {Γ : Ctx n} (Ω : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → ofWNode Ω (proj₂ kv)) nodes ≡ true →
  NodeΩ Ω (lookupNode nid nodes)
lookupNode-Ω Ω nid []            h = tt
lookupNode-Ω Ω nid ((k , s) ∷ r) h with k ≡ᵇ nid
... | true  = proj₁ (∧-true _ _ h)
... | false = lookupNode-Ω Ω nid r (proj₂ (∧-true _ _ h))

-- splitting an emit / a whole burst
splitEvents-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) es ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitEvents {A = Val Γ u} es)) ≡ true
splitEvents-vals-Ω Ω []              h = refl
splitEvents-vals-Ω Ω (value v  ∷ es) h =
  ∧-intro (proj₁ (∧-true _ _ h)) (splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h)))
splitEvents-vals-Ω Ω (init _   ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (close _ _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (handoff _ ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))
splitEvents-vals-Ω Ω (complete ∷ es) h = splitEvents-vals-Ω Ω es (proj₂ (∧-true _ _ h))

splitEvents-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitEvents {A = Val Γ u} es))) ≡ true
splitEvents-bk-Ω Ω []              = refl
splitEvents-bk-Ω {u = u} Ω (value v  ∷ es) = splitEvents-bk-Ω {u = u} Ω es
splitEvents-bk-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (splitEvents-bk-Ω {u = u} Ω es)
splitEvents-bk-Ω {u = u} Ω (complete ∷ es) = splitEvents-bk-Ω {u = u} Ω es

splitBurst-vals-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  burstΩ? Ω str ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ (splitBurst {A = Val Γ u} str)) ≡ true
splitBurst-vals-Ω Ω []               h = refl
splitBurst-vals-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) h =
  all-++-intro _ (proj₁ (splitEvents {A = Val Γ u} (InstEmit.events em))) _
    (splitEvents-vals-Ω Ω (InstEmit.events em) (proj₁ (∧-true _ _ h)))
    (splitBurst-vals-Ω {u = u} Ω ems (proj₂ (∧-true _ _ h)))

splitBurst-bk-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ) (str : Stream Γ s) →
  all (eventΩ? Ω) (proj₁ (proj₂ (splitBurst {A = Val Γ u} str))) ≡ true
splitBurst-bk-Ω Ω []               = refl
splitBurst-bk-Ω {Γ = Γ} {u = u} Ω (em ∷ ems) =
  all-++-intro _ (proj₁ (proj₂ (splitEvents {A = Val Γ u} (InstEmit.events em)))) _
    (splitEvents-bk-Ω {u = u} Ω (InstEmit.events em))
    (splitBurst-bk-Ω {u = u} Ω ems)

-- retagging drops values, so the result is unconditionally clean
retag-Ω : ∀ {n} {Γ : Ctx n} {s u : Ty} (Ω : ℕ)
  (es : List (InstEvent (Val Γ s))) →
  all (eventΩ? {n = n} {Γ = Γ} {u = u} Ω) (retagEvents es) ≡ true
retag-Ω Ω []              = refl
retag-Ω {u = u} Ω (init _   ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (close _ _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (handoff _ ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (complete ∷ es) = ∧-intro refl (retag-Ω {u = u} Ω es)
retag-Ω {u = u} Ω (value _  ∷ es) = retag-Ω {u = u} Ω es

-- mergeAll's counter bump and switchAll's cut, width faces
mergeBump-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (nid : NodeId) (d : Bool) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  widthOK? Ω sched (record st { nodes = mergeBump nid d (EvalSt.nodes st) })
    ≡ true
mergeBump-width Ω nid d sched st inv with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k od)   = install-width Ω sched st nid
                                 (merge-st (if d then k else suc k) od) refl inv
... | nothing                = inv
... | just (scan-st _)       = inv
... | just (take-st _)       = inv
... | just (concat-st _ _ _) = inv
... | just (switch-st _ _)   = inv
... | just (exhaust-st _ _)  = inv

switchKill-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ω : ℕ)
  (cur : Maybe NodeId) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  let r = switchKill cur sched st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (all (eventΩ? Ω) (proj₁ r) ≡ true)
switchKill-width Ω nothing  sched st inv = inv , refl
switchKill-width Ω (just v) sched st inv =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (proj₁ (proj₂ P))
  (∧-intro (cutThrough-regsΩ Ω v del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  cutThrough-closesΩ Ω v del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough v del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the wrap: values and events pass through, only the *All node's
-- done flag is written back
thruWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (Ω : ℕ) (op : AllOp) (nid : NodeId) (fin : Bool)
  (vs : List (Val Γ u)) (bs : List (InstEvent (Val Γ t)))
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) vs ≡ true →
  all (eventΩ? Ω) bs ≡ true →
  let r = thruWrap op nid fin (vs , bs , sched , st)
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
thruWrap-width Ω op nid false vs bs sched st inv vΩ bΩ = inv , vΩ , bΩ
thruWrap-width Ω mergeᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (merge-st k _)    =
      install-width Ω sched st nid (merge-st k true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω concatᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | just (concat-st q act _) | nb =
      install-width Ω sched st nid (concat-st q act true) nb inv , vΩ , bΩ
... | nothing                | _ = inv , vΩ , bΩ
... | just (scan-st _)       | _ = inv , vΩ , bΩ
... | just (take-st _)       | _ = inv , vΩ , bΩ
... | just (merge-st _ _)    | _ = inv , vΩ , bΩ
... | just (switch-st _ _)   | _ = inv , vΩ , bΩ
... | just (exhaust-st _ _)  | _ = inv , vΩ , bΩ
thruWrap-width Ω switchᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      install-width Ω sched st nid (switch-st cur true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (exhaust-st _ _)  = inv , vΩ , bΩ
thruWrap-width Ω exhaustᵒ nid true vs bs sched st inv vΩ bΩ
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      install-width Ω sched st nid (exhaust-st act true) refl inv , vΩ , bΩ
... | nothing                = inv , vΩ , bΩ
... | just (scan-st _)       = inv , vΩ , bΩ
... | just (take-st _)       = inv , vΩ , bΩ
... | just (merge-st _ _)    = inv , vΩ , bΩ
... | just (concat-st _ _ _) = inv , vΩ , bΩ
... | just (switch-st _ _)   = inv , vΩ , bΩ

------------------------------------------------------------------
-- the two SELF-CONTAINED frames: scan folds under Ω (applyFn never
-- widens), take passes a prefix through and, on the cutting emit,
-- runs cutThrough + sweepLive.  Neither re-enters subscribeE, so
-- both live outside the clique.
------------------------------------------------------------------

stepFrame-scan-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  frameΩ? Ω (scan-f fn nid) ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (scan-f fn nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ u v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-scan-width {s = s} {u = u} Ω g id now fn nid κ vals fin sched st
                     inv fΩ vΩ
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-Ω Ω nid (EvalSt.nodes st)
         (proj₁ (proj₂ (WOK-parts Ω sched st inv)))
... | nothing                | _ = inv , refl , refl
... | just (take-st _)       | _ = inv , refl , refl
... | just (merge-st _ _)    | _ = inv , refl , refl
... | just (concat-st _ _ _) | _ = inv , refl , refl
... | just (switch-st _ _)   | _ = inv , refl , refl
... | just (exhaust-st _ _)  | _ = inv , refl , refl
... | just (scan-st {w} ac)  | nb with w ≟ᵗ u
...   | no _    = inv , refl , refl
...   | yes refl =
  install-width Ω sched st nid (scan-st (proj₂ run))
    (T⇒≡true _ (≤⇒≤ᵇ (proj₁ run-ok))) inv ,
  proj₂ run-ok , refl
  where
  run    = scanVals fn ac vals
  ofwfn  : ofWᵗ fn ≤ Ω
  ofwfn  = ≤ᵇ⇒≤ _ _ (T-to fΩ)
  run-ok = scanVals-ofW Ω fn ac vals ofwfn (≤ᵇ⇒≤ _ _ (T-to nb)) vΩ

stepFrame-take-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (Ω : ℕ) (g : Gas) (id : Id) (now : Tick)
  (nid : NodeId) (κ : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true →
  all (λ v → ofWᵛ s v ≤ᵇ Ω) vals ≡ true →
  let r = stepFrame g id now (take-f nid) κ vals fin sched st
  in (widthOK? Ω (proj₁ (proj₂ (proj₂ (proj₂ r))))
                 (proj₂ (proj₂ (proj₂ (proj₂ r)))) ≡ true)
     × (all (λ v → ofWᵛ s v ≤ᵇ Ω) (proj₁ r) ≡ true)
     × (all (eventΩ? Ω) (proj₁ (proj₂ r)) ≡ true)
stepFrame-take-width {s = s} Ω g id now nid κ vals fin sched st inv vΩ
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = inv , refl , refl
... | just (scan-st _)       = inv , refl , refl
... | just (merge-st _ _)    = inv , refl , refl
... | just (concat-st _ _ _) = inv , refl , refl
... | just (switch-st _ _)   = inv , refl , refl
... | just (exhaust-st _ _)  = inv , refl , refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false =
  install-width Ω sched st nid
    (take-st (proj₁ (proj₂ (takeVals k vals)))) refl inv ,
  takeVals-Ω Ω k vals vΩ , refl
...   | true =
  ∧-intro (sweepLive-ofW Ω kept (Sched.live sched) (proj₁ P))
  (∧-intro (setNode-ofW Ω nid (take-st zero) (EvalSt.nodes st) refl
              (proj₁ (proj₂ P)))
  (∧-intro (cutThrough-regsΩ Ω nid del wm dy (EvalSt.registry st)
              (proj₁ (proj₂ (proj₂ P))))
           (proj₂ (proj₂ (proj₂ P))))) ,
  takeVals-Ω Ω k vals vΩ ,
  cutThrough-closesΩ Ω nid del wm dy (EvalSt.registry st)
  where
  del  = EvalSt.delivered st
  wm   = EvalSt.regWatermark st
  dy   = EvalSt.dying st
  kept = proj₁ (cutThrough nid del wm dy (EvalSt.registry st))
  P    = WOK-parts Ω sched st inv

-- the connect's two landings, factored out of sharedConnect's `if`
connectWrap-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (Ω : ℕ) (i : Fin n) (id : Id) (c : Bool)
  (burst : Stream Γ (lookup Γ i)) (sched : Sched Γ) (st : EvalSt e) →
  widthOK? Ω sched st ≡ true → burstΩ? Ω burst ≡ true →
  let r : Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
      r = if c
          then (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
                  at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched
               , record st { registry = dropSource (toℕ i) (EvalSt.registry st)
                           ; completedSources = toℕ i ∷ EvalSt.completedSources st }
          else (((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst)
               , sched , st
  in (widthOK? Ω (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
     × (burstΩ? Ω (proj₁ r) ≡ true)
connectWrap-width Ω i id true  burst sched st inv bΩ =
  latch-width Ω (toℕ i) sched st inv ,
  ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)
connectWrap-width Ω i id false burst sched st inv bΩ =
  inv , ∧-intro refl (sharedPlumb-Ω Ω burst bΩ)

-- of-list literals: eval never widens, so each element rides the
-- list's own ofWᵗˢ max
ofVals-Ω : ∀ {n} {Γ : Ctx n} {u} (Ω : ℕ) (ts : List (Tm Γ [] [] [] u)) →
  ofWᵗˢ ts ≤ Ω →
  all (λ v → ofWᵛ u v ≤ᵇ Ω) (map (λ tm → evalTm tm) ts) ≡ true
ofVals-Ω Ω []       h = refl
ofVals-Ω Ω (y ∷ ys) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (ofW-evalWith Ω y []ᵃ tt
            (≤-trans (m≤m⊔n (ofWᵗ y) (ofWᵗˢ ys)) h))))
          (ofVals-Ω Ω ys (≤-trans (m≤n⊔m (ofWᵗ y) (ofWᵗˢ ys)) h))
