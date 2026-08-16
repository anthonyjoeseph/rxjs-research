-- THE PROOF that the evaluator's output satisfies the protocol
-- automaton: evaluate-well-formed, the primitives' half of the
-- batching sandwich (see Verify-Batch-Simultaneous.The-Proof).
--
-- Architecture: a simulation, in three layers.
--   1. Inv (CONCRETE below) relates evaluator state to automaton
--      state between cascades.
--   2. Two frame relations — BurstInv (mid-subscribe-frame) and Mid
--      (mid-cascade, indexed by the chains still to fold) — both
--      CONCRETE records now, with entry/step/exit lemmas.  Proven:
--      burst-init, burst-final.  Postulated (all believed true and
--      properly hypothesised — no known-false placeholders): the
--      step lemmas
--      (subscribeE-wf, mid-step — the per-clause preservation
--      grind), mid-init, mid-skip, mid-final.  Budget sufficiency
--      is no longer assumed here: it is imported, proven, from
--      Verify-Budget-Sufficient.
--   3. The compositions — the subscribe frame, the chain fold, the
--      fuel loop, and the theorem — are all DEFINED, glued by
--      runProtocol's distribution over ++.
module Verify-Well-Formed.Part3 where

open import Data.Bool    using (Bool; true; false; if_then_else_; _∧_; _∨_; not; T)
open import Data.Bool.Properties using (∨-assoc; ∨-comm; ∨-identityʳ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; ≤-trans; ≤-pred; m≤n+m; 1+n≰n; ≤⇒≤ᵇ; ≤ᵇ⇒≤; +-suc; +-comm; +-assoc; +-identityʳ; +-cancelʳ-≡; m+n∸n≡m)
open import Data.List    using (List; []; _∷_; _++_; length; map)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Empty   using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Relation.Nullary using (Dec; yes; no)

-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.  MOVED 2026-08-05 from .Wet (the 2026-08-05 upside-down ruling) — `budget-sufficient`'s TYPE did
-- not change, only which module proves it, so nothing else here needed
-- to move with it.
open import Verify-Budget-Sufficient.Caps-Bridge using (budget-sufficient)
open import Rx.Prim      using (Fuel; Gas; g0; gs; Tick; Id; Source; Ordinal; InstEmit;
                                InstEvent; init; value; close; handoff; complete;
                                EmitKind; delivery; subscribe; plumbing; CloseReason; exhausted;
                                dried;
                                cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; _≟ᵗ_; Val; Fn; obs; applyFn; mapᵉ;
                                unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; Tm; scanᵉ; takeᵉ; evalTm;
                                input; ofᵉ; emptyᵉ; varᵉ; deferᵉ; mergeAllᵉ; concatAllᵉ;
                                switchAllᵉ; exhaustAllᵉ; μᵉ; unfoldμ)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Slots; Stream;
                                RegId; Chain; Path; root; share-sink; _↠_; Frame;
                                map-f; scan-f; take-f; from-inner; thru-outer; AllOp;
                                mergeᵒ; concatᵒ; switchᵒ; exhaustᵒ; aliveThroughᶠ;
                                takeVals; takeDispatch; cutThrough; setNode; pathHasNode; memberSource;
                                NodeId; NodeState; lookupNode; scan-st; take-st; merge-st;
                                concat-st; switch-st; exhaust-st;
                                sched-init; st-init; sched-next; LiveSource;
                                schedGo; schedHeadOf; schedFinish; schedEarlier;
                                arrTy; arrSource; arrVal; arrTick;
                                chainsOf; chainsGo; chainStep;
                                foldPath; dispatchShare; stepFrame;
                                cascadeLatch; cascadeGo; cascadeFinish;
                                subscribeE; cascade; drain; evaluate;
                                oneShotBurst; mintSource; register; splitEvents;
                                pushBurst; scanVals; installNode; mintNode; retagEvents;
                                sameSource; dryEvent; hasDry;
                                dropSource; sweepLive; budgetAt)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init;
                                stepProtocol; runProtocol; paidUp; settle; hasOwed;
                                payOwed; paidOff; applyEvents; removeOne;
                                cancelOwed; bumpOwed; settleInstant;
                                checkFinal; Accepted; accepted; WellFormed;
                                hasValue; valsLast?)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part2 public

regTyped?-snoc : ∀ {n} {Γ : Ctx n} {t}
  (r : List (RegId × Source × Chain Γ t))
  (rid : RegId) (s : Source) (u : Ty) (p : Path Γ u t)
  (live : List (LiveSource Γ)) →
  regTyped? r live ≡ true →
  liveTypeOK? s u live ≡ true →
  regTyped? (r ++ (rid , s , u , p) ∷ []) live ≡ true
regTyped?-snoc []                        rid s u p live rt lt =
  ∧-intro lt refl
regTyped?-snoc ((rid′ , s′ , u′ , p′) ∷ r) rid s u p live rt lt =
  ∧-intro (∧-trueˡ rt) (regTyped?-snoc r rid s u p live (∧-trueʳ rt) lt)

-- one init-only registering emit: it enlists src (no close, no complete, so
-- done is untouched) and opens instant id with an empty owed table.  (init/close
-- carry only sources, so the protocol is agnostic to the emit's value type A.)
initReg-run : ∀ {A : Set} (id : Id) (src : Source) (S : ProtocolSt) →
  (ProtocolSt.current S ≡ nothing) ⊎ (ProtocolSt.current S ≡ just (id , [])) →
  ProtocolSt.horizon S ≤ id →
  runProtocol S (((init {A} src ∷ []) at id from src as subscribe) ∷ [])
    ≡ just (record { live = src ∷ ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                   ; current = just (id , []) ; done = ProtocolSt.done S })
initReg-run id src S (inj₁ ceq) hlow
  rewrite ceq | settleInstant-nothing S ceq | ≤ᵇ-true (ProtocolSt.horizon S) id hlow = refl
initReg-run id src S (inj₂ ceq) hlow
  rewrite ceq | ≡ᵇ-refl id = refl

-- the registering base clause: emit `init src` and `register src (u, κ)`.  The
-- init balances the new registration (live-matches), and the registered chain
-- is well-typed against the live schedule (reg-typed, from `ltok`).
initReg-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (src : Source) (κ : Path Γ u t) (id : Id)
  (st : EvalSt e) (sched : Sched Γ) (S : ProtocolSt) →
  BurstInv id sched st S →
  liveTypeOK? src u (Sched.live sched) ≡ true →
  Σ ProtocolSt λ S′ →
    runProtocol S (((init {Val Γ u} src ∷ []) at id from src as subscribe) ∷ []) ≡ just S′
    × BurstInv id sched (register src κ st) S′
initReg-wf {Γ = Γ} {u = u} src κ id st sched S binv ltok =
  _ , run , record
        { live-matches  = lm
        ; reg-typed     = regTyped?-snoc (EvalSt.registry st) (EvalSt.nextReg st)
                            src u κ (Sched.live sched) (BurstInv.reg-typed binv) ltok
        ; horizon-low   = BurstInv.horizon-low binv
        ; current-frame = inj₂ refl
        }
  where
  run : runProtocol S (((init {Val Γ u} src ∷ []) at id from src as subscribe) ∷ [])
        ≡ just (record { live = src ∷ ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                       ; current = just (id , []) ; done = ProtocolSt.done S })
  run = initReg-run {Val Γ u} id src S (BurstInv.current-frame binv) (BurstInv.horizon-low binv)

  lm : ∀ s → countIn s (src ∷ ProtocolSt.live S)
             ≡ countRegs s (EvalSt.registry (register src κ st))
  lm s rewrite countRegs-snoc s (EvalSt.registry st) (EvalSt.nextReg st) src u κ
    with s ≡ᵇ src
  ... | true  = trans (cong suc (BurstInv.live-matches binv s))
                      (sym (+-comm (countRegs s (EvalSt.registry st)) 1))
  ... | false = trans (BurstInv.live-matches binv s)
                      (sym (+-identityʳ (countRegs s (EvalSt.registry st))))

-- ════════════════════════════════════════════════════════════════════════
-- SUBSCRIBE-SIDE DECOMPOSITION BLUEPRINT (opened 2026-07-19)
--
-- subscribeE-wf preserves BurstInv across one subscription's burst, and yields
-- a protocol run for that burst.  BurstInv is CLEAN: fin-independent, and (as of
-- the fork resolution below) carries NO done-plumbed — live-matches is a plain
-- equality countIn s (live S) ≡ countRegs s (registry st), NO pending init/close
-- events (unlike FoldInv's SHADOW), because the burst's events are reconciled
-- into live by runProtocol, not carried.  done-plumbed is a root-exit obligation
-- (root-done-plumbed), handed to burst-final directly.
--
-- THE CENTRAL MECHANISM.  A subscription grows the registry by `register`ing a
-- source and, in the SAME burst emit, ships an `init` of that source.  runProtocol
-- applies the init to `live`, so countIn and countRegs bump in lockstep and
-- live-matches is preserved.  Symmetrically a one-shot's `close`+`complete` drain
-- what its `init` added.  Every clause below is an instance of this balance.
--
-- CLAUSE GROUPS (b : Closed Γ u = Exp Γ [] [] [] u), and their obligations:
--   · ABSURD: varᵉ () — Δ ≡ [] so t ∈ [] is uninhabited.  Proven by ().
--   · RECURSION: μᵉ — fuel-zero emits dryBurst (hasDry ≡ true, contra nodry, ⊥);
--     fuel-suc RECURSES on unfoldμ body (fuel ↓).  Structural once dry is killed.
--   · BASE (oneShotBurst / direct emit): ofᵉ, emptyᵉ, takeᵉ-zero, and input's four
--     scripted/hot branches, and deferᵉ.  Each emits one InstEmit whose events are
--     init(+values)(+close+complete) of a fresh/hot source; some also `register`.
--     Obligation `oneShotBurst-wf` + a `register`-balances-`init` lemma: runProtocol
--     on that single emit steps the automaton once (enterInstant/settle/applyEvents)
--     and re-establishes live-matches (init balances the new reg), reg-typed (the
--     registered chain is well-typed against the added live source) and current-frame
--     (the emit opens instant id).  [DONE for ofᵉ/emptyᵉ/takeᵉ-zero: oneShotBurst-wf,
--     modulo the `done S ≡ false` at-subscribe premise.  No done-plumbed and no
--     caches — both left BurstInv for the root, see the fork resolutions below.]
--   · FRAME (subscribeE b (f ↠ κ) then pushBurst f κ burst): mapᵉ (f=map-f),
--     takeᵉ-suc (mintNode+installNode, f=take-f), scanᵉ (mintNode+installNode,
--     f=scan-f).  Obligation: IH (subscribeE-wf on b, structural) gives BurstInv+run
--     for b's burst; the clause must then fold stepFrame over each emit, preserving
--     BurstInv+run.  NOTE pushBurst runs stepFrame under BurstInv, NOT FoldInv — so
--     that fold needs the burst-side twin of stepFrame-wf (same map/scan/take/wrap
--     case split, but re-establishing live-matches equality rather than SHADOW).
--     NO such helper is stated, and cannot usefully be: see the NOTE at the *All
--     gap postulates.  installNode adds a fresh scan/take node — caches-neutral.
--   · WRAP (subscribeAll = mintNode + subscribeE b (thru-outer op nid ↠ κ) + pushBurst
--     (thru-outer op nid)): mergeAllᵉ/concatAllᵉ/switchAllᵉ/exhaustAllᵉ.  Same shape
--     as FRAME with f = thru-outer op nid and a minted *All node installed at its
--     initial state — so it reuses the FRAME obligation above at f = thru-outer
--     op nid.  This is where the
--     merge coherence (root-caches) actually gets exercised (walk subscribes
--     inners) — and where the SECOND fork below says the counter cannot be kept
--     coherent emit-by-emit, only re-established at the exit.
--
-- BUILD ORDER (outside-in): PHASES 1-4 DONE; this is now a forward TYPE DECLARATION
-- (not a postulate), with the body placed after subscribeE-take-wf (~line 3100).
-- DONE: (3) oneShotBurst-wf (base clauses ofᵉ/emptyᵉ); (4) subscribeE-map-wf,
-- subscribeE-scan-wf, subscribeE-take-wf (frame clauses).  pushBurst-wf and
-- stepFrame-burst were dropped (both had `→ Set` return types — asserting nothing
-- checkable by the typechecker).  The gap postulates below cover blocked clauses
-- (map-*/scan-*/take-* shape gaps, the four *All wrap clauses,
-- subscribeE-input-wf/defer-wf/takeᵉ-wf).  dispatchShare-wf and the
-- stepFrame-wf-inner-concat/outer residues remain blocked on merge-cert.
-- TERMINATION: lexicographic (Gas, Closed Γ u) — μ drops Gas, every other recursion
-- drops Closed structurally; Agda sees it inline, mirroring subscribeE itself.
--
-- ── FORK SURFACED while landing (3) oneShotBurst-wf (2026-07-20) ─────────
-- oneShotBurst-run PROVES a base burst ALWAYS ends done ≡ true (the trailing
-- `complete` latches it).  So subscribeE-wf's output BurstInv.done-plumbed is
-- demanded at EVERY base subscribe as `allShareSunk (registry st) ≡ true`
-- (base registers nothing, so it's the FULL pre-existing registry).  That is:
--   · TRUE at the ROOT and wherever the base burst is the emitted stream: a
--     synchronous full completion leaves only share sinks live.
--   · FALSE on the INNER-recursion path.  Concrete witness (naive rxjs):
--       mergeAll(of([asyncInner, empty]))
--     stepFrame(thru-outer) folds the outer's one emit, subscribing asyncInner
--     (registers a non-share-sunk async source) THEN empty.  subscribeE(empty,
--     from-inner ↠ κ) hits the BASE clause (κ is ignored there), emits its raw
--     init/close/COMPLETE, and oneShotBurst-run flips done ≡ true — while the
--     async sibling is still a live non-share-sunk registration.  done-plumbed
--     (even a dropSource-of-empty's-src flip form: empty's src isn't registered,
--     so dropSource is identity) is violated.
--   ROOT CAUSE (same class as the dropped FoldInv.env-close/done-plumbed): the
--   inner's RAW burst carries a `complete` that the ENCLOSING thru-outer frame
--   STRIPS before emission (a merge inner completing while a sibling lives does
--   NOT complete the merge).  subscribeE-wf, applied to an inner, is claiming a
--   protocol run of a stream that is never emitted; its `done ≡ true` is an
--   artifact of reading the raw burst, not the pushed one.
--   CONSUMER: BurstInv.done-plumbed is read ONLY by burst-final (root frame-0
--   exit → Inv.done-plumbed).  It is NEVER read on the inner-recursion path.
--   So per the standing rule (input-side fields earn their existence from
--   consumers, not symmetry), done-plumbed is a ROOT-EXIT obligation, not
--   threaded through the recursive/inner BurstInv.
--   RESOLVED (2026-07-20): done-plumbed DROPPED from BurstInv.  It is now
--   re-established once, at burst-final, from the `root-done-plumbed` postulate
--   (root-returned stream's done ≡ true ⟹ registry share-sunk — the merge-
--   coherence content, to be proven when the *All wrap clauses are).  This
--   also DELETED the `allShareSunk` premise the base clause used to owe.  Fully
--   proof-side (BurstInv is not the spec); makes subscribeE-wf TRUE for inners
--   (only done-plumbed was false there).  Note kept as the rationale of record.
--
-- ── SECOND FORK, same shape, surfaced while proving cut-head-joint (2026-07-27) ─
-- BurstInv.caches asserted cachesValid of every intermediate burst state.  It is
-- FALSE there, and — unlike done-plumbed, which merely failed on one path — it
-- fails in BOTH DIRECTIONS, so no weakening rescues it:
--   · thruConsume mergeᵒ runs subscribeInner FIRST and applies mergeBump only
--     after, so for the whole of an inner's subscribe burst the inner's
--     registrations exist while activeInners has not been incremented — the
--     counter TRAILS the registry.
--   · a take-cut hands cutThrough the registry and never touches activeInners,
--     so the counter LEADS it.
-- nodeCacheOK's merge clause demands equality while the outer is registered, and
-- the outer IS registered across both (subscribeAll registers it before pushBurst).
-- Both halves were checked by computation before the field was dropped;
-- the probe that checked them is retired (2026-08-09).
--   CONSUMER: exactly as with done-plumbed — BurstInv.caches was read ONLY by
--   burst-final (root frame-0 exit → Inv.caches).
--   RESOLVED (2026-07-27): caches DROPPED from BurstInv, re-established once at
--   burst-final from the `root-caches` postulate — the settled state, by which
--   point every mergeBump has landed.  This also DELETED initReg-wf's `cok`
--   premise and cachesValid-setNode-ok (both existed only to feed the field), and
--   reduced pushBurst-scan-caches to pushBurst-scan-fixed.  root-caches is the
--   same merge-coherence content root-done-plumbed is waiting on, so the two
--   discharge together, once the *All wrap clauses acquire real proofs.
-- ════════════════════════════════════════════════════════════════════════
-- ════════════════════════════════════════════════════════════════
-- GAP POSTULATES — real gaps against the actual lemma types
-- ════════════════════════════════════════════════════════════════

-- REFUTED AND DELETED (2026-08-06): `burst-done-false` claimed
-- `BurstInv id sched st S → done S ≡ false`.  It is FALSE — BurstInv's four
-- fields never mention `done`, so the empty state with `done = true` inhabits
-- it and forces `true ≡ false`.  Machine refutation:
-- `Battery-Burst-Done (DELETED; git history)` (`burst-done-false-absurd`, a proven ⊥).
-- oneShotBurst-wf's own header (below, ~line 876) had said so all along:
-- `done ≡ false` is a subscribe-TIME fact and "BurstInv cannot carry it; it
-- must come from the walk order."  So it now comes from the walk order —
-- `subscribeE-wf` and every per-clause receipt TAKE it as the premise `deq`,
-- threaded unchanged down the spine, and `subscribe-wf` supplies `refl` at
-- `protocol-init`.  The threading was rehearsed in a probe first; that
-- rehearsal is spent and the probe is retired (2026-08-09).
postulate
  -- mapᵉ GAP 1: hasDry propagates inward through the map push.
  map-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ false

  -- mapᵉ GAP 2: pushBurst map frame preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-map-wf (~line 1920) does NOT return valsLast?;
  -- subscribeE-wf's conclusion REQUIRES it.
  map-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ true →
    valsLast? (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ true

  -- scanᵉ GAP 1: hasDry propagates inward through the scan push.
  scan-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                  (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
           ≡ false

  -- scanᵉ GAP 2: fresh scan node (with updated acc) survives subscribeE b.
  scan-nodeP : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    let nid = proj₁ (mintNode sched)
        r₀  = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
                (installNode nid (scan-st (evalTm seed)) st)
    in Σ (Val Γ u) λ acc →
         lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (scan-st acc)

  -- scanᵉ GAP 3: pushBurst scan-f preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-scan-wf (~line 2003) does NOT return valsLast?;
  -- subscribeE-wf's conclusion REQUIRES it.
  scan-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                     (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
              ≡ true →
    valsLast? (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ true

  -- BurstInv ADAPTATION (scan): mintNode / installNode don't touch registry or
  -- Sched.live, so all four BurstInv fields are preserved at the FIELD TYPE level.
  -- But Agda does NOT fire this at the record-type INDEX level — it compares whole
  -- sched / st objects, not their projections.
  -- DISCHARGED 2026-08-06 — see `scan-binv-adapt` (a real definition) below.

  -- NOTE: the takeᵉ helper obligations (BurstInv adaptation, fresh-node
  -- survival, dying-stability) are deliberately NOT stated here.  The takeᵉ
  -- clause is postulated wholesale as `subscribeE-takeᵉ-wf` below, so a
  -- helper for it would have NO CONSUMER — and an unconsumed postulate is
  -- exactly the debt-without-a-wire this file's own law forbids.  They
  -- belong inside that postulate's eventual proof, where they get one.

-- scan-binv-adapt: DISCHARGED (2026-08-06).  Was a postulate; its own comment
-- said "provable inline as record { … }" and that was right.  A scanᵉ clause
-- mints a node and installs it, and BurstInv reads NEITHER: `installNode`
-- touches only `nodes`, `mintNode` only `nextNode`, so `EvalSt.registry` and
-- `Sched.live` are unchanged and all four fields transport by record eta with
-- no rewrites.  Verified in `Battery-VWF-Prop (DELETED; git history)`.
scan-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
  (b : Closed Γ s) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  BurstInv id (proj₂ (mintNode sched))
             (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st) S
scan-binv-adapt fuel f seed b κ id now sched st S binv = record
  { live-matches  = BurstInv.live-matches  binv
  ; reg-typed     = BurstInv.reg-typed     binv
  ; horizon-low   = BurstInv.horizon-low   binv
  ; current-frame = BurstInv.current-frame binv
  }

-- ════════════════════════════════════════════════════════════════
-- PER-CLAUSE POSTULATES FOR BLOCKED CLAUSES
-- ════════════════════════════════════════════════════════════════

postulate
  -- ALL input clauses (hot/cold/shared).
  -- The shared/new subcase recurses on the def stored in the slot (gas-decrement edge).
  --
  -- ASSEMBLY (2026-08-06): narrowed over `initReg-wf`, the registering
  -- base clause every input subcase ends in — the init balances the new
  -- registration and the registered chain is well-typed against the live
  -- schedule.
  --
  -- ⚠ BLOCKED 2026-08-15, found by the leaf-only migration (PROOF-STATE
  -- tier −1).  `initReg-wf` is PASSED here and never APPLIED, so its
  -- premises are unpaid — and one of them CANNOT BE PAID at this call
  -- site as the statement stands.
  --
  -- Writing the body means splitting on `Sched.slots sched i` to mirror
  -- the evaluator (Evaluator:1400).  The hot/live arm registers
  -- `(toℕ i) κ`, which is exactly `initReg-wf`'s shape at `src := toℕ i`
  -- — so the arm is a one-liner EXCEPT for initReg-wf's `ltok`:
  --
  --     liveTypeOK? (toℕ i) (lookup Γ i) (Sched.live sched) ≡ true
  --
  -- Nothing in scope supplies it.  This postulate's own hypotheses
  -- (BurstInv, done≡false, hasDry≡false) never mention `Sched.slots`;
  -- BurstInv's four fields and Inv's seven (both .Part2) relate the
  -- registry to `live` and say nothing about `slots`; and `Sched`
  -- (Evaluator:63) is a PLAIN RECORD whose `live` and `slots` are
  -- independent, so no free-standing lemma over an arbitrary `sched`
  -- could be true — build one with a hot slot and `live = []`.
  --
  -- NOT the misplaced-call shape (CLAUDE.md): the gap is a whole absent
  -- invariant, not a fixed small index offset, and `mkHot`
  -- (Evaluator:110) establishes the fact ONLY at `sched-init`, with
  -- nothing carrying it across schedule transitions (mintSource,
  -- sweepLive, dropSource).  The repair is a reachability/well-formedness
  -- predicate on `Sched` that does not exist yet, established at
  -- sched-init and preserved by each transition — a claim-authoring call,
  -- not a grind.  Note the existing `mkHot` reasoning in .Init-Caps
  -- (widLive-mkHot) is about WIDTH bounds and does not donate this.
  subscribeE-input-wf-core :
    -- initReg-wf  (Verify-Well-Formed.agda:950)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
      (src : Source) (κ : Path Γ u t) (id : Id)
      (st : EvalSt e) (sched : Sched Γ) (S : ProtocolSt) →
      BurstInv id sched st S →
      liveTypeOK? src u (Sched.live sched) ≡ true →
      Σ ProtocolSt λ S′ →
        runProtocol S (((init {Val Γ u} src ∷ []) at id from src as subscribe) ∷ []) ≡ just S′
        × BurstInv id sched (register src κ st) S′
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (input i) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (input i) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- deferᵉ: init + register, no inner burst at subscribe time.
  subscribeE-defer-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (body : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (deferᵉ body) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (deferᵉ body) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- NOTE: no `subscribeAll-wf` helper is stated here, and that is
  -- deliberate.  A POSTULATE CANNOT CONSUME ANYTHING, so a helper written
  -- for the four *All clauses — which are themselves postulated below — is
  -- necessarily an orphan, and no wiring fixes it.  It gets a consumer only
  -- when one of those clauses acquires a real proof; state it then.

  subscribeE-mergeAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (mergeAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (mergeAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-concatAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (concatAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (concatAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-switchAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (switchAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (switchAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  subscribeE-exhaustAll-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (exhaustAllᵉ b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (exhaustAllᵉ b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- takeᵉ WHOLE CASE.
  -- WITH-ABSTRACTION NOTE: `with evalTm count in ecEq` abstracts evalTm count
  -- throughout the context.  After | suc k branch, the postulate's expected
  -- type normalises to (proj₁ (pushBurst ...)) but nodry's type stays as | evalTm
  -- — unification fails.  Entire takeᵉ case lives outside any `with evalTm`.
  -- LANDING FIX: where-clause helper with ec : ℕ and ecEq : evalTm count ≡ ec as
  -- separate non-with arguments; suc case calls subscribeE-wf fuel b (take-f nid ↠ κ).
  -- subscribeE-take-wf (~line 3060) shape verified to match; recursion termination:
  -- b is a structural subterm of takeᵉ count b.
  --
  -- ASSEMBLY (2026-08-06): narrowed over `subscribeE-take-wf`, the
  -- positive-count clause this postulate's own header points at.  That
  -- clause is declared FURTHER DOWN the file, so only the core lives
  -- here; the definition sits just after it and before this name's one
  -- consumer.
  subscribeE-takeᵉ-wf-core :
    -- subscribeE-take-wf  (Verify-Well-Formed.agda:3277)
    (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
      (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
      (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) (k : ℕ) →
      evalTm count ≡ suc k →
      BurstInv id sched st S →
      (let nid = proj₁ (mintNode sched)
           r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
                   (installNode nid (take-st (suc k)) st)
       in Σ ProtocolSt λ S′ →
            (runProtocol S (proj₁ r₀) ≡ just S′)
            × BurstInv id (proj₁ (proj₂ r₀)) (proj₂ (proj₂ r₀)) S′
            × (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (take-st (suc k)))
            × (valsLast? (proj₁ r₀) ≡ true)
            -- the cut's live/registry balance is off a dying source only; subscribeE
            -- never writes `dying` (cascadeLatch alone does), so this rides in from
            -- the enclosing cascade — free at a root subscribe, where st-init has it []
            × (∀ s → memberSource s (EvalSt.dying (proj₂ (proj₂ r₀))) ≡ false)) →
      Σ ProtocolSt λ S″ →
        (runProtocol S (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ just S″)
        × BurstInv id (proj₁ (proj₂ (subscribeE fuel (takeᵉ count b) κ id now sched st)))
                   (proj₂ (proj₂ (subscribeE fuel (takeᵉ count b) κ id now sched st))) S″
        × (valsLast? (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ true)
     ) →
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeE fuel (takeᵉ count b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

-- the input clause, assembled over its core
