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

open import Data.Bool    using (Bool; true; false)
open import Data.Bool.Properties using (∨-identityʳ)
open import Data.Fin     using (Fin; toℕ)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; suc; _≤_; _≡ᵇ_; _+_)
open import Data.Nat.Properties using (1+n≢0; +-comm; +-identityʳ)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Empty   using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)


-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.
open import Verify-Budget-Sufficient.Node-Fresh using (mint-install-survives)
open import Verify-Budget-Sufficient.Queue-Dead using (QDeadC; emptyQueue?;
  pushBurst-qd; subscribeE-qd)
open import Rx.Prim      using (Gas; g0; Tick; Id; Source; init; value; close; complete; subscribe; exhausted; Timed; hot;
  cold; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty; Val; Fn; obs; mapᵉ; natᵗ; _×ᵗ_; Tm; scanᵉ; takeᵉ; evalTm; input; emptyᵉ;
  deferᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ)
open import Rx.Evaluator using (Sched; EvalSt; RegId; Chain; Path; root; _↠_; map-f; scan-f; take-f; cutThrough;
  memberSource; NodeId; lookupNode; scan-st; take-st; st-init; LiveSource; subscribeE;
  mintSource; register; installNode; mintNode; sameSource; hasDry; subscribeSharedSlot;
  mergeAll-st; mergeAllᵒ; thru-outer;
  mintOrdinal; resolve)
open import Rx.Slots using (scripted; shared)

open import Rx.Protocol  using (ProtocolSt; countIn; runProtocol; valsLast?)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part2 using (BurstInv; countRegs-snoc; hotSlot?;
                                           oneShotBurst-wf; settleInstant-nothing)
open import Verify-Well-Formed.Part1 using (closeCount; countRegs; liveTypeOK?; regTyped?)
open import Decide using (true≢false; ∧-intro; ∧-trueʳ; ∧-trueˡ; ≡ᵇ-refl; ≤ᵇ-true)

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
        ; hot-live      = BurstInv.hot-live binv
        }
  where
  run : runProtocol S (((init {Val Γ u} src ∷ []) at id from src as subscribe) ∷ [])
        ≡ just (record { live = src ∷ ProtocolSt.live S ; horizon = ProtocolSt.horizon S
                       ; current = just (id , []) ; done = ProtocolSt.done S })
  run = initReg-run {Val Γ u} id src S (BurstInv.current-frame binv) (BurstInv.horizon-low binv)

  lm : ∀ s → memberSource s (EvalSt.dying (register src κ st)) ≡ false →
             countIn s (src ∷ ProtocolSt.live S)
             ≡ countRegs s (EvalSt.registry (register src κ st))
  lm s h rewrite countRegs-snoc s (EvalSt.registry st) (EvalSt.nextReg st) src u κ
    with s ≡ᵇ src
  ... | true  = trans (cong suc (BurstInv.live-matches binv s h))
                      (sym (+-comm (countRegs s (EvalSt.registry st)) 1))
  ... | false = trans (BurstInv.live-matches binv s h)
                      (sym (+-identityʳ (countRegs s (EvalSt.registry st))))

-- ════════════════════════════════════════════════════════════════════════
-- SUBSCRIBE-SIDE DECOMPOSITION BLUEPRINT
--
-- subscribeE-wf preserves BurstInv across one subscription's burst, and yields
-- a protocol run for that burst.  BurstInv is CLEAN: fin-independent, and (as of
-- the fork resolution below) carries NO done-plumbed — live-matches is a plain
-- equality countIn s (live S) ≡ countRegs s (registry st), NO pending init/close
-- events (unlike FoldInv's SHADOW), because the burst's events are reconciled
-- into live by runProtocol, not carried.  done-plumbed is a root-exit obligation
-- (root-done-plumbed), handed to burst-final directly.

-- THE CENTRAL MECHANISM.  A subscription grows the registry by `register`ing a
-- source and, in the SAME burst emit, ships an `init` of that source.  runProtocol
-- applies the init to `live`, so countIn and countRegs bump in lockstep and
-- live-matches is preserved.  Symmetrically a one-shot's `close`+`complete` drain
-- what its `init` added.  Every clause below is an instance of this balance.

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
--     (thru-outer op nid)): mergeAllᵉ/switchAllᵉ/exhaustAllᵉ.  Same shape
--     as FRAME with f = thru-outer op nid and a minted *All node installed at its
--     initial state — so it reuses the FRAME obligation above at f = thru-outer
--     op nid.  This is where the
--     merge coherence (root-caches) actually gets exercised (walk subscribes
--     inners) — and where the SECOND fork below says the counter cannot be kept
--     coherent emit-by-emit, only re-established at the exit.

-- A FORWARD TYPE DECLARATION and not a postulate; the body sits below, after
-- subscribeE-take-wf.  The gap postulates further down cover the blocked
-- clauses — the map-/scan-/take- shape gaps, the four *All wrap clauses,
-- subscribeE-input-wf/defer-wf/takeᵉ-wf — while dispatchShare-wf and the
-- stepFrame-wf-inner-mergeAll/outer residues are blocked on mergeAll-cert, the
-- SKETCH in Part8's establishment block rather than a Part4 postulate.
--
-- TERMINATION: lexicographic (Gas, Closed Γ u) — μ drops Gas, every other
-- recursion drops Closed structurally; Agda sees it inline, mirroring
-- subscribeE itself.
--
-- A `→ Set` return type asserts nothing the typechecker can check, which is
-- why there is no pushBurst-wf or stepFrame-burst here.

-- ── WHY done-plumbed IS A ROOT-EXIT OBLIGATION AND NOT A BurstInv FIELD ──
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
--   SO IT IS NOT A FIELD.  It is re-established once, at burst-final, from
--   the `root-done-plumbed` postulate — root-returned stream's done ≡ true ⟹
--   registry share-sunk, the merge-coherence content, provable when the *All
--   wrap clauses are.  That is what makes subscribeE-wf TRUE for inners, and
--   it is entirely proof-side: BurstInv is not the spec.

-- ── WHY caches IS A ROOT-EXIT OBLIGATION TOO, and it fails harder ──
-- BurstInv.caches asserted cachesValid of every intermediate burst state.  It is
-- FALSE there, and — unlike done-plumbed, which merely failed on one path — it
-- fails in BOTH DIRECTIONS, so no weakening rescues it:
--   · thruConsume mergeAllᵒ runs subscribeInner FIRST and applies mergeAllBump only
--     after, so for the whole of an inner's subscribe burst the inner's
--     registrations exist while activeInners has not been incremented — the
--     counter TRAILS the registry.
--   · a take-cut hands cutThrough the registry and never touches activeInners,
--     so the counter LEADS it.
-- nodeCacheOK's merge clause demands equality while the outer is registered, and
-- the outer IS registered across both (subscribeAll registers it before pushBurst).
-- Both halves were checked by computation before the field was dropped;
-- the probe that checked them is retired.
--   CONSUMER: exactly as with done-plumbed — BurstInv.caches was read ONLY by
--   burst-final (root frame-0 exit → Inv.caches).
--   SO IT IS NOT A FIELD EITHER.  It is re-established once at burst-final
--   from the `root-caches` postulate — the settled state, by which point every
--   mergeAllBump has landed.  root-caches is the same cache-coherence content
--   root-done-plumbed waits on, so the two discharge together, once the *All
--   wrap clauses acquire real proofs.
-- ════════════════════════════════════════════════════════════════════════
-- ════════════════════════════════════════════════════════════════
-- GAP POSTULATES — real gaps against the actual lemma types
-- ════════════════════════════════════════════════════════════════

-- `burst-done-false` — `BurstInv id sched st S → done S ≡ false` — IS FALSE,
-- and is not stated anywhere: BurstInv's four fields never mention `done`, so
-- the empty state with `done = true` inhabits it and forces `true ≡ false`.
--
-- REFUTED: `git show 94a5a3c^:agda/probe/Battery-Burst-Done.agda` holds
--   `burst-done-false-absurd`, a proven ⊥.
--   oneShotBurst-wf's own header had said so all along:
--   `done ≡ false` is a subscribe-TIME fact and "BurstInv cannot carry it; it
--   must come from the walk order."  So it now comes from the walk order —
--   `subscribeE-wf` and every per-clause receipt TAKE it as the premise `deq`,
--   threaded unchanged down the spine, and `subscribe-wf` supplies `refl` at
--   `protocol-init`.  The threading was rehearsed in a probe first; that
--   rehearsal is spent and the probe is retired.
postulate
  -- mapᵉ GAP 1: hasDry propagates inward through the map push.
  --
  -- ROUTE: `pushBurst-map-char` (.Part5) shows that
  -- subscribeE (mapᵉ f b) κ ... ≡ (map (reEmit (map (applyFn f))) burst, sched, st)
  -- where burst = proj₁ (subscribeE b (map-f f ↠ κ) ...).  `stepFrame (map-f f)`
  -- returns evs = [] (Rx.Evaluator), so the events of each reEmitted emit are
  -- exactly: `splitEvents(inner events).bookkeeping ++ map value vals′ ++ finFlag`.
  -- `close s dried` events are in the bookkeeping list (splitEvents-nodry,
  -- .Walk-Level) and never in map value or the finFlag (mapValue-dry :1070,
  -- finList-dry :1081).  Therefore `hasDry (map (reEmit g) burst) = hasDry burst`
  -- in both directions.  The needed direction (outer false → inner false) is the
  -- contrapositive: if inner has a dried event, so does the reEmit of it.
  --
  -- POTENTIALLY DISCHARGEABLE: all ingredients are proven.  The obstacle is that
  -- `splitEvents-nodry`, `mapValue-dry`, `finList-dry`, and `any-dry-++` all live
  -- in Walk-Level.agda, which Part3 does not import.  They could be proven inline
  -- in the body or added to a Part5 lemma accessible here.  No conceptual barrier.
  map-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ false

  -- mapᵉ GAP 2: pushBurst map frame preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-map-wf does NOT return valsLast?;
  -- subscribeE-wf's conclusion REQUIRES it.
  map-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] s u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (map-f f ↠ κ) id now sched st)) ≡ true →
    valsLast? (proj₁ (subscribeE fuel (mapᵉ f b) κ id now sched st)) ≡ true

  -- scanᵉ GAP 1: hasDry propagates inward through the scan push.
  --
  -- ROUTE: `stepFrame (scan-f fn nid)` also returns evs = []
  -- (Rx.Evaluator — the scan frame writes only to the node table, never
  -- emitting protocol events).  So the events of each pushBurst emit are
  -- `splitEvents(inner events).bookkeeping ++ map value vals′ ++ finFlag`,
  -- the same shape as the map case above.  `hasDry` is therefore preserved
  -- bidirectionally through the scan push for the same reason.
  --
  -- Unlike map-nodry-push, there is no `pushBurst-scan-char` characterization
  -- (scan threads a stateful accumulator), so the proof is a direct induction
  -- over pushBurst's definition using the same dry-preservation ingredients:
  -- `splitEvents-nodry` / `mapValue-dry` / `finList-dry` / `any-dry-++`
  -- (all Walk-Level.agda — not currently imported by Part3).  Twin of
  -- map-nodry-push and has the same import obstacle; no conceptual barrier.
  scan-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
    (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (scanᵉ f seed b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
                  (proj₂ (mintNode sched)) (installNode (proj₁ (mintNode sched)) (scan-st (evalTm seed)) st)))
           ≡ false

  -- scanᵉ GAP 3: pushBurst scan-f preserves valsLast?.
  -- REAL SHAPE MISMATCH: subscribeE-scan-wf does NOT return valsLast?;
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
  -- `scan-binv-adapt` below is the real definition that closes this.

  -- takeᵉ GAP 1: hasDry propagates inward through the take push.  Twin of
  -- scan-nodry-push, plus the `ecEq` the evaluator's `with evalTm count`
  -- needs before the outer side reduces at all.
  --
  -- ROUTE: Same structural argument as scan-nodry-push.  The `evs`
  -- from `takeDispatch` in the NON-cut case are [] (Rx.Evaluator).  In the
  -- CUT case, `evs = closes` where `closes = proj₁ (proj₂ (cutThrough ...))`.
  -- `cutThrough` (Rx.Evaluator) emits only `close src cut` or
  -- `close src cutPending` — never `close src dried`.  Therefore
  -- `any dryEvent closes = false`, so `retagEvents closes` is also dry-free by
  -- `retagEvents-dry` (.Walk-Level).  The pushBurst events are
  -- `bk ++ retagEvents closes ++ map value vals′ ++ finFlag`, all dry-free when
  -- the inner emit's events are dry-free.  Same import obstacle as scan-nodry-push
  -- (ingredients in Walk-Level, not Part3).
  --
  -- EXTRA PREMISE: `ecEq : evalTm count ≡ suc k` is needed because the evaluator
  -- case-splits on `evalTm count` (Rx.Evaluator) before the takeᵉ clause
  -- reduces.  Without it the outer hasDry does not reduce to the inner hasDry.
  take-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (fuel : Gas) (count : Tm Γ [] [] [] natᵗ) (k : ℕ) (b : Closed Γ s) (κ : Path Γ s t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    evalTm count ≡ suc k →
    hasDry (proj₁ (subscribeE fuel (takeᵉ count b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
                  (proj₂ (mintNode sched))
                  (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st)))
           ≡ false

  -- NO takeᵉ valsLast-push twin: unlike scan, `subscribeE-take-wf` already
  -- returns the valsLast? conjunct (off the proven pushBurst-take-valsLast),
  -- so the take clause's conclusion needs no bridge.

-- scanᵉ GAP 2, DISCHARGED: the freshly installed scan node
-- survives the inner `subscribeE b`.  The Σ is here only because the
-- consumer (.Part8) asks for one; the witness is `evalTm seed` on the nose,
-- since a subscribe writes nothing below the watermark it was handed.  The
-- whole route is `mint-install-survives` (.Node-Fresh) — mint, install,
-- subscribe, read the node back — which is PROVEN there, over a ring on the
-- whole of `subscribeE`; `take-node` below spends it in the same line.
scan-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (fuel : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u) (seed : Tm Γ [] [] [] u)
  (b : Closed Γ s) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r₀  = subscribeE fuel b (scan-f f nid ↠ κ) id now (proj₂ (mintNode sched))
              (installNode nid (scan-st (evalTm seed)) st)
  in Σ (Val Γ u) λ acc →
       lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (scan-st acc)
scan-node fuel f seed b κ id now sched st =
  evalTm seed
  , mint-install-survives fuel b (scan-f f (proj₁ (mintNode sched)) ↠ κ) id now
      (scan-st (evalTm seed)) sched st

-- takeᵉ GAP 2, DISCHARGED: scan-node's twin, and it needs no Σ
-- — a take node's count is spent by the take FRAME, which runs above this
-- subscription rather than inside it, so `suc k` comes back exactly.
take-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (fuel : Gas) (k : ℕ) (b : Closed Γ s) (κ : Path Γ s t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
              (installNode nid (take-st (suc k)) st)
  in lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r₀))) ≡ just (take-st (suc k))
take-node fuel k b κ id now sched st =
  mint-install-survives fuel b (take-f (proj₁ (mintNode sched)) ↠ κ) id now
    (take-st (suc k)) sched st

-- scan-binv-adapt: DISCHARGED.  Was a postulate; its own comment
-- said "provable inline as record { … }" and that was right.  A scanᵉ clause
-- mints a node and installs it, and BurstInv reads NEITHER: `installNode`
-- touches only `nodes`, `mintNode` only `nextNode`, so `EvalSt.registry` and
-- `Sched.live` are unchanged and all four fields transport by record eta with
-- no rewrites.  Verified in ``git show 1f1730e^:agda/probe/Battery-VWF-Prop.agda``.
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
  ; hot-live      = BurstInv.hot-live      binv
  }

-- take-binv-adapt: scan-binv-adapt's twin, and a REAL DEFINITION for the same
-- reason — `mintNode` writes only `nextNode` and `installNode` only `nodes`,
-- and BurstInv reads neither, so every field transports by record eta.  The
-- `live-matches` field's `dying` hypothesis rides through too: `installNode`
-- does not touch `dying` either.  Takes only what it uses (k, sched, st, S),
-- since it is a definition rather than a postulate and spare arguments are
-- just noise.
take-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (k : ℕ) (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv id sched st S →
  BurstInv id (proj₂ (mintNode sched))
             (installNode (proj₁ (mintNode sched)) (take-st (suc k)) st) S
take-binv-adapt k id sched st S binv = record
  { live-matches  = BurstInv.live-matches  binv
  ; reg-typed     = BurstInv.reg-typed     binv
  ; horizon-low   = BurstInv.horizon-low   binv
  ; current-frame = BurstInv.current-frame binv
  ; hot-live      = BurstInv.hot-live      binv
  }

-- ════════════════════════════════════════════════════════════════
-- PER-CLAUSE POSTULATES FOR BLOCKED CLAUSES
-- ════════════════════════════════════════════════════════════════

postulate
  -- ── THE INPUT CLAUSE'S ARMS ──────────────────────────────────────
  -- These three are the residue of `subscribeE-input-wf` (assembled at
  -- the foot of this file), which splits on `Sched.slots sched i` to
  -- mirror the evaluator (Rx.Evaluator).  The other two arms are NOT
  -- here because they are DISCHARGED there, by proven lemmas:
  --   · hot and live      → `initReg-wf` (above), at src := toℕ i
  --   · cold, no async    → `oneShotBurst-wf` (.Part2)
  -- Each leaf below is stated at its OWN arm's burst, not at
  -- `subscribeE … (input i) …`, so none of them can be discharged by a
  -- proof of a different arm.

  -- SHARED slot.  `subscribeSharedSlot` (Rx.Evaluator) is its own
  -- three-way split — spent share, live share, and `sharedConnect`,
  -- which RECURSES into subscribeE on the stored def at one less gas.
  -- That recursion is why this arm is a leaf and not an application:
  -- discharging it needs subscribeE-wf, which is mutual with it and
  -- lives two files down.
  subscribeSharedSlot-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    hasDry (proj₁ (subscribeSharedSlot fuel i d κ id now sched st)) ≡ false →
    Σ ProtocolSt λ S′ →
      let r = subscribeSharedSlot fuel i d κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S′)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S′
         × (valsLast? (proj₁ r) ≡ true)

  -- HOT slot already SPENT (`toℕ i ∈ completedSources`).  One emit —
  -- init, close, complete — registering nothing and leaving the
  -- schedule alone, so the close/complete drain exactly what the init
  -- added.  `oneShotBurst-wf` (.Part2) is the same balance at a FRESHLY
  -- MINTED source; this one re-inits a source that is already spent,
  -- which is why that lemma does not donate it.
  input-hot-spent-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (id : Id) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    Σ ProtocolSt λ S′ →
      runProtocol S (((init {Val Γ (lookup Γ i)} (toℕ i)
                        ∷ close (toℕ i) exhausted ∷ complete ∷ [])
                      at id from toℕ i as subscribe) ∷ []) ≡ just S′
      × BurstInv id sched st S′

  -- COLD slot WITH an async tail: per-subscription anchoring mints a
  -- fresh source AND ordinal, installs a live entry carrying the
  -- resolved tail, and registers the chain.  `initReg-wf` does not
  -- reach it — that lemma's emit is `init src ∷ []`, and this one ships
  -- the sync prefix in the SAME emit (`init src ∷ map value sync`), so
  -- the run has values to absorb and the schedule grows a live entry.
  --
  -- STRUCTURAL OBSTACLE: the emit is `(init src ∷ map value sync)
  -- at id from src as subscribe`.  `runProtocol` must handle this combined
  -- init + values emit.  `stepProtocol-faithful` (.Part5) handles value-free
  -- transforms of bursts, and `initReg-run` (above) covers `init src ∷ []` only.
  -- No lemma in the repo handles `init ∷ map value sync` in a single emit for
  -- protocol-state purposes.  The protocol is value-agnostic for the init step
  -- (values don't appear in the Owed table), but the existing proof infrastructure
  -- does not expose a "init + values = init" reduction for `runProtocol`.
  --
  -- `BurstInv` balance: `liveTypeOK? src (lookup Γ i) sched₃.live = true` requires
  -- that the freshly-added live entry (source = src, elemTy = lookup Γ i) self-
  -- certifies at the head, and that the pre-existing live list has no src entry
  -- (src is freshly minted by `mintSource`).  Same freshness argument as
  -- `subscribeE-defer-wf` below; no proved lemma for this yet.
  --
  -- Searched: `initReg-wf`, `initReg-run`, `runProtocol`, `stepProtocol-faithful`,
  -- `oneShotBurst-wf`, `liveTypeOK?`; no existing lemma covers the init+values case.
  input-cold-async-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (sync : List (Val Γ (lookup Γ i)))
    (d : Timed (Val Γ (lookup Γ i))) (ds : List (Timed (Val Γ (lookup Γ i))))
    (κ : Path Γ (lookup Γ i) t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    ProtocolSt.done S ≡ false →
    (let src    = proj₁ (mintSource sched)
         sched₁ = proj₂ (mintSource sched)
         ord    = proj₁ (mintOrdinal sched₁)
         sched₂ = proj₂ (mintOrdinal sched₁)
         sched₃ = record sched₂
                    { live = record { source  = src
                                    ; ordinal = ord
                                    ; elemTy  = lookup Γ i
                                    ; pending = resolve now (d ∷ ds) }
                             ∷ Sched.live sched₂ }
     in Σ ProtocolSt λ S′ →
          runProtocol S (((init src ∷ map value sync) at id from src as subscribe) ∷ [])
            ≡ just S′
          × BurstInv id sched₃ (register src κ st) S′)

  -- deferᵉ: init + register, no inner burst at subscribe time.
  --
  -- ROUTE: `subscribeE fuel (deferᵉ body) κ ...` reduces to
  -- (Rx.Evaluator):
  --   burst  = ((init src ∷ []) at id from src as subscribe) ∷ []
  --   sched' = sched₄ (after mintNode, mintSource, mintOrdinal, live ∷= entry)
  --   st'    = register src (thru-outer mergeAllᵒ nid ↠ κ) (installNode nid (mergeAll-st lim 0 [] false) st)
  --
  -- Three of the four conclusion conjuncts are immediate:
  --   · hasDry premise is VACUOUS: `init src` is not `close _ dried`, so
  --     `any dryEvent (init src ∷ []) = false`.
  --   · valsLast? = true by `valsLast? (em ∷ []) = true` (Rx.Protocol).
  --   · runProtocol equation: `initReg-run id src S ...`, above,
  --     applies — the emit shape matches exactly.
  --
  -- REMAINING: BurstInv id sched₄ (register src ... (installNode nid ... st)) S′.
  --   · live-matches: same balance as `initReg-wf` — `installNode` and
  --     `register` don't conflict; countRegs/countIn bump in lockstep via the
  --     init event.
  --   · reg-typed: needs `liveTypeOK? src (obs u) (Sched.live sched₄) = true`.
  --     sched₄.live = record { source=src; elemTy=obs u; ... } ∷ (rest).
  --     Head: `src ≡ᵇ src = true`, `sameTy (obs u) (obs u) = true`.  Rest:
  --     `src` is freshly minted by `mintSource`; no pre-existing live entry has
  --     source = src, so every remaining entry returns true.  This
  --     self-certification argument has no proved lemma yet.
  --   · hot-live: sched₄.slots = sched.slots (mintNode/mintSource/mintOrdinal
  --     and the live-prepend all leave slots unchanged), so HotLive sched₄ =
  --     HotLive sched definitionally.  `BurstInv.hot-live binv` supplies it.
  --   · horizon-low, current-frame: carried unchanged from `initReg-run`.
  --
  -- NOT dischargeable from `initReg-wf` directly: that lemma assumes sched is
  -- unchanged after the burst, but here sched₄ ≠ sched (it grew a live entry).
  -- The missing piece is the freshness lemma for liveTypeOK?.
  --
  -- Searched: `initReg-wf`, `liveTypeOK?`, `mintSource-hot-live`,
  -- `liveTypeOK?-sweepLive`, `liveTypeOK?-swap`; no existing lemma certifies
  -- that a freshly-minted live entry is self-typing.
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

  -- NOTE: no `subscribeAll-wf` helper is stated here for the two
  -- remaining *All clauses, and that is deliberate.  A POSTULATE CANNOT
  -- CONSUME ANYTHING, so a helper written for clauses that are
  -- themselves postulated below is necessarily an orphan, and no wiring
  -- fixes it.  It gets a consumer only when one of those clauses
  -- acquires a real proof; state it then.  The mergeAll clause has one,
  -- which is why the four leaves below exist and the switch and exhaust
  -- faces still have none.

  -- THE FLATTEN WRAP, LEAF BY LEAF.  `subscribeE (mergeAllᵉ lim b)`
  -- reduces to `subscribeAll mergeAllᵒ (mergeAll-st lim 0 [] false) b`,
  -- which mints a node, installs it, subscribes the SOURCE under a
  -- `thru-outer mergeAllᵒ nid` frame, and pushes the resulting burst
  -- back through that frame.  So the clause is the scan clause's shape
  -- with the frame and the initial node state swapped, and it splits at
  -- the same four joints: carry the invariant across the mint, carry
  -- the dry premise inward, read the node the inner burst left, and
  -- push the protocol run and `valsLast?` back out.
  --
  -- ONE STATEMENT FOR EVERY LIMIT, and the limit is why this is now
  -- worth splitting at all.  The old merge and concat faces were
  -- textually identical but for the constructor, so the collapse was a
  -- rename rather than a weakening -- the limit is a parameter these
  -- statements never read, which is exactly what lets one set of leaves
  -- cover the bounded case neither old face could express.

  -- CARRY THE INVARIANT ACROSS THE MINT.  `mintNode` writes `nextNode`
  -- and `installNode` writes `nodes`, so neither the registry nor the
  -- live list moves and every `BurstInv` field transports by eta.
  --
  -- TWIN: `scan-binv-adapt` is that transport at the same two
  --   operations, proven, and the argument does not read the node state
  --   it installs.
  mergeAll-binv-adapt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (lim : Maybe ℕ)
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    BurstInv id (proj₂ (mintNode sched))
      (installNode (proj₁ (mintNode sched)) (mergeAll-st {t = u} lim 0 [] false) st) S

  mergeAll-nodry-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (lim : Maybe ℕ)
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    hasDry (proj₁ (subscribeE fuel (mergeAllᵉ lim b) κ id now sched st)) ≡ false →
    hasDry (proj₁ (subscribeE fuel b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
                     id now (proj₂ (mintNode sched))
                     (installNode (proj₁ (mintNode sched))
                        (mergeAll-st {t = u} lim 0 [] false) st)))
           ≡ false

  mergeAll-valsLast-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (lim : Maybe ℕ)
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    valsLast? (proj₁ (subscribeE fuel b (thru-outer mergeAllᵒ (proj₁ (mintNode sched)) ↠ κ)
                        id now (proj₂ (mintNode sched))
                        (installNode (proj₁ (mintNode sched))
                           (mergeAll-st {t = u} lim 0 [] false) st)))
              ≡ true →
    valsLast? (proj₁ (subscribeE fuel (mergeAllᵉ lim b) κ id now sched st)) ≡ true

  -- THE NODE THE INNER BURST LEFT, as a SHAPE and nothing more: the
  -- wrap's node is still a `mergeAll-st` at the type it was installed
  -- at, whatever the burst did to the counter, the queue and the
  -- outer-done flag.  Limit-blind by construction, which is what lets
  -- the queue claim be a separate fact rather than a conjunct only one
  -- limit can honour.
  --
  -- TWIN: `scan-node` reads its own freshly installed node back after
  --   the inner burst and is proven, over a ring on the whole of
  --   `subscribeE` that never reads which state was installed.
  mergeAll-node-shape : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (lim : Maybe ℕ)
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    let nid = proj₁ (mintNode sched)
        r   = subscribeE fuel (mergeAllᵉ lim b) κ id now sched st
    in Σ ℕ λ act → Σ (List (Closed Γ u)) λ q → Σ Bool λ od →
         lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))
           ≡ just (mergeAll-st {t = u} lim act q od)

  -- THE PUSH BACK OUT: it
  -- takes the inner subscription's protocol receipt and, SEPARATELY,
  -- the node the finished wrap leaves behind, and returns the outer's.
  --
  -- The two hypotheses sit at DIFFERENT INSTANTS and that is deliberate.
  -- The protocol run is a fact about the inner burst, which is what the
  -- outer's run is assembled from; the node fact is about the wrap's own
  -- result, which is the state `BurstInv` in the conclusion is quantified
  -- over.  Stating the node at the inner instant instead reads as the
  -- tighter hypothesis and is in fact the DEGENERATE one -- the wrap's
  -- queue cannot have been written yet at a point before the only call
  -- that can write it.
  --
  -- TWIN: `subscribeE-scan-wf` is this same joint on the scan face and
  --   is proven -- inner receipt plus the finished node, out through the
  --   frame, invariant back in.
  subscribeE-mergeAll-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (lim : Maybe ℕ)
    (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
    (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    BurstInv id sched st S →
    (let nid = proj₁ (mintNode sched)
         r₀  = subscribeE fuel b (thru-outer mergeAllᵒ nid ↠ κ) id now
                 (proj₂ (mintNode sched))
                 (installNode nid (mergeAll-st {t = u} lim 0 [] false) st)
     in Σ ProtocolSt λ S′ →
          (runProtocol S (proj₁ r₀) ≡ just S′)
          × BurstInv id (proj₁ (proj₂ r₀)) (proj₂ (proj₂ r₀)) S′) →
    (let nid = proj₁ (mintNode sched)
         r   = subscribeE fuel (mergeAllᵉ lim b) κ id now sched st
     in Σ ℕ λ act → Σ (List (Closed Γ u)) λ q → Σ Bool λ od →
          (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))
             ≡ just (mergeAll-st {t = u} lim act q od))
          × (lim ≡ nothing → q ≡ [])) →
    Σ ProtocolSt λ S″ →
      let r = subscribeE fuel (mergeAllᵉ lim b) κ id now sched st
      in (runProtocol S (proj₁ r) ≡ just S″)
         × BurstInv id (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) S″

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

-- THE NODE THE INNER BURST LEFT, shape and queue together, which is the
-- form the wrap clause consumes.  The queue half is claimed only at an
-- unbounded limit, where it is `Rx.MergeAll-Laws.unbounded-never-parks`
-- and nothing else; a bounded run yields the shape and no promise about
-- the queue, because at a bounded limit the burst legitimately parks.
--
-- THE PREDICATE COSTS THE CONSUMER NOTHING, which was the open question
-- about the law's shape.  `emptyQueue?` cannot be an equation --
-- `NodeState` holds the queue's element type existentially, so the two
-- sides would not be at one type -- and it does not need to be: the
-- shape leaf pins the lookup at the wrap's own `u`, and `emptyQueue?`
-- at a pinned `mergeAll-st` reduces to exactly the equation wanted.  One
-- `subst` along the shape equation is the whole bridge.
-- THE QUEUE STAYS DEAD AT AN UNBOUNDED LIMIT, across the whole wrap and
-- not merely across its outer subscribe.  A real body, and the split is
-- the content: `subscribeAll` is mint, then `subscribeE` on the outer
-- under a `thru-outer` frame, then `pushBurst` of that burst back
-- through the frame.  The first half is `mint-install-survives`
-- (.Node-Fresh), PROVEN over a ring on the whole of `subscribeE` -- the
-- freshly installed node comes back untouched, so the queue reaching
-- `pushBurst` is the one that was installed.  The second half is the
-- only walk that can park, and it is the leaf.
--
-- PINNING IT AT THE FIRST HALF WAS THE BUG.  Nothing has parked before
-- `pushBurst` at ANY limit, so the claim held at `just 1` too -- the
-- limit it exists to exclude -- and read as discharged while asserting
-- nothing about the case it was minted for.
--
-- RECOVERY: `git log --diff-filter=D -- agda/evidence/probed/Probed/MergeAll-Queue.agda`
--   restores the probe that found that, with its two- and three-inner
--   corpus and the `just 1` controls that made the rows load-bearing.
--   The theorem says more than the rows ever did, so it expired with
--   its target; what survives being worth a pointer is the corpus.
unbounded-never-parks : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r   = subscribeE fuel (mergeAllᵉ nothing b) κ id now sched st
  in emptyQueue? (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r))))
unbounded-never-parks {u = u} fuel b κ id now sched st =
  QDeadC.keep (pushBurst-qd nid fuel id now (thru-outer mergeAllᵒ nid) κ
                 (proj₁ inner) (proj₁ (proj₂ inner)) (proj₂ (proj₂ inner)))
       (QDeadC.nxMono innerQ)
       (subst emptyQueue? (sym survives) refl)
  where
  nid : NodeId
  nid = proj₁ (mintNode sched)

  inner = subscribeE fuel b (thru-outer mergeAllᵒ nid ↠ κ) id now
            (proj₂ (mintNode sched))
            (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st)

  innerQ = subscribeE-qd nid fuel b (thru-outer mergeAllᵒ nid ↠ κ) id now
             (proj₂ (mintNode sched))
             (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st)

  survives = mint-install-survives fuel b (thru-outer mergeAllᵒ nid ↠ κ) id now
               (mergeAll-st {t = u} nothing 0 [] false) sched st

mergeAll-node : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (lim : Maybe ℕ)
  (fuel : Gas) (b : Closed Γ (obs u)) (κ : Path Γ u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  let nid = proj₁ (mintNode sched)
      r   = subscribeE fuel (mergeAllᵉ lim b) κ id now sched st
  in Σ ℕ λ act → Σ (List (Closed Γ u)) λ q → Σ Bool λ od →
       (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ r)))
          ≡ just (mergeAll-st {t = u} lim act q od))
       × (lim ≡ nothing → q ≡ [])
mergeAll-node lim fuel b κ id now sched st
  with mergeAll-node-shape lim fuel b κ id now sched st
... | act , q , od , shapeEq = act , q , od , shapeEq , qnil
  where
  qnil : lim ≡ nothing → q ≡ []
  qnil refl =
    subst emptyQueue? shapeEq
      (unbounded-never-parks fuel b κ id now sched st)

-- takeᵉ WHOLE CASE.  The takeᵉ
-- clause of `subscribeE-wf` (.Part8) is a real body that APPLIES
-- `subscribeE-take-wf` and `subscribeE-take0-wf`, over the residue leaves
-- `take-nodry-push` above and the real `take-node` / `take-binv-adapt`.
--
-- FINDINGS:
--   · THE WITH-ABSTRACTION TRAP IS REAL.  `with evalTm count` at the clause
--     level abstracts that term throughout the context, after which the
--     recursive call's type still mentions it unabstracted and unification
--     fails.  The landing shape is a where-helper carrying `ec` and
--     `ecEq : evalTm count ≡ ec` as ORDINARY arguments, each consumer doing
--     its own `rewrite ecEq`.
--   · THE ZERO ARM IS FREE, and a wholesale postulate would hide that —
--     `take 0` never subscribes its source (Rx.Evaluator), so
--     it is `emptyᵉ` verbatim and the PROVEN `oneShotBurst-wf` closes it.
--     Same pattern as at the cold/no-async arm.
--   · AND ONE PREMISE COULD NOT BE PAID — `subscribeE-take-wf`'s `dyF`,
--     `∀ s → memberSource s (EvalSt.dying …) ≡ false`.  Its own comment said
--     it "rides in from the enclosing cascade"; that was backwards, since
--     `cascadeLatch` SEEDS `dying` before any chain is processed
--     (Rx.Evaluator), so inside a cascade the premise is false, not free —
--     and `subscribeE-wf`, the only caller, quantifies over an arbitrary `st`
--     and holds no hypothesis about `dying`.  The first pin below refutes the
--     naive leaf outright.
--
-- THE REPAIR, AFTER THE FIRST ONE WAS ALSO REFUTED.  Re-keying `dyF` off the
-- envSrc-conditioned `FoldInv.dying-envSrc` reads well and is dead: `dyF` is
-- spent in ONE place, `cutThrough-{close-bound,live-apply}` (.Part7), whose
-- product is `BurstInv.live-matches` at the cut state — an ALL-SOURCES
-- equality — so conditioning on `s ≢ envSrc` is silent exactly where the
-- consumer must answer, and at that instance the equation is FALSE.  The
-- second and third pins below carry that.
--
-- So the question moved up to `BurstInv.live-matches` itself, and Anthony
-- ruled it: key the field off `EvalSt.dying st`, not off an
-- envSrc index — A′, the field note in .Part2.  `dyF` is then not re-keyed
-- but GONE, since what it was trying to establish became the field's own
-- hypothesis.  Its TRUE form survives as `subscribeE-dying` (.Part8):
-- PRESERVATION, not freeness, which is what makes it free at the root and
-- false in a cascade — precisely what the pins say.
--
-- WHAT A′ DOES NOT CLOSE, so that nobody reads this as finished: the dying
-- window still owes its close-landing bound.  `cutThrough-close-bound-dying`
-- and `cutThrough-live-dying` (.Part7) carry it, with the exact ledger.

-- MACHINE REFUTATION of the naive residue leaf the real body above would
-- have consumed — subscribeE-take-wf's `dyF` conjunct, stated over the same
-- arbitrary `st` its consumer quantifies over.  `EvalSt` is a plain record
-- and `dying` a free field, so ONE state with a non-empty `dying` kills it:
-- at `b = emptyᵉ` the subscribe is a one-shot that returns `st` untouched
-- (Evaluator's oneShotBurst clause), `installNode` writes only `nodes`, and
-- the conjunct at `s = 0` computes to `true ≡ false`.
--
-- The state IS hand-built, and here that is the point rather than the flaw
-- (CLAUDE.md's trap (2) is about a hand-built state read as a green
-- receipt): the statement quantifies over every `st : EvalSt e`, so a
-- constructed inhabitant refutes it outright.  Reachability is established
-- separately and does not rest on this pin — `cascadeLatch` produces
-- exactly these states (Rx.Evaluator, and .Part13's `dsrc`, which proves
-- dying-freeness there only OFF `arrSource a`).
--
-- ANONYMOUS by the bug-cache idiom: a named pin is a proven definition with
-- no consumer, and `make wiring-gate` would rightly orphan it.
_ : ∀ {n} {Γ : Ctx n} → Sched Γ →
    (∀ {n′} {Γ′ : Ctx n′} {t} {e : Closed Γ′ t} {s}
      (fuel : Gas) (b : Closed Γ′ s) (κ : Path Γ′ s t)
      (id : Id) (now : Tick) (sched : Sched Γ′) (st : EvalSt e) (k : ℕ) →
      (let nid = proj₁ (mintNode sched)
           r₀  = subscribeE fuel b (take-f nid ↠ κ) id now (proj₂ (mintNode sched))
                   (installNode nid (take-st (suc k)) st)
       in ∀ s → memberSource s (EvalSt.dying (proj₂ (proj₂ r₀))) ≡ false))
    → ⊥
_ = λ sched dyF →
      true≢false
        (dyF g0 (emptyᵉ {t = natᵗ}) root 0 0 sched
             (record (st-init (emptyᵉ {t = natᵗ})) { dying = 0 ∷ [] }) 0
             0)

-- ── AND THE PROPOSED REPAIR IS REFUTED TOO ─────────────
-- The route above says: re-key `dyF` off the envSrc-conditioned
-- `FoldInv.dying-envSrc`.  Following it to the BOTTOM of the chain
-- kills it.  `dyF` is threaded through pushBurst-take-joint and
-- cut-head-joint untouched and spent in exactly one place — the pair
-- `cutThrough-close-bound` / `cutThrough-live-apply` (.Part7) — and
-- both spend it at EVERY source, because what they must produce is
-- `∀ s → countIn s L′ ≡ countRegs s kept`, i.e. `BurstInv.live-matches`
-- at the cut state, and live-matches is an ALL-SOURCES equality.  The
-- conditioned form asserts nothing at `s ≡ envSrc`, and `s ≡ envSrc` is
-- precisely the instance a cascade makes false (cascadeLatch seeds
-- `dying` to `arrSource a ∷ []`).  So the conditioned premise is not a
-- weaker sufficient hypothesis — it is silent exactly where the
-- consumer needs an answer.  The two pins below say it as code.
--
-- FIRST: the conditioned premise really does HOLD at a cascade's
-- `dying`, so this is not a claim that the re-keying is unavailable.
_ : ∀ (envSrc s : Source) → sameSource s envSrc ≡ false →
    memberSource s (envSrc ∷ []) ≡ false
_ = λ envSrc s h → trans (∨-identityʳ (sameSource s envSrc)) h

-- SECOND: and the equation it would have to feed is FALSE at
-- `s ≡ envSrc`.  This is `cutThrough-balance` (.Part7) with its
-- dying-freeness hypothesis removed — the one thing `dyF` is ever
-- spent on.  Witness: one registration, on envSrc, whose chain runs
-- through the cut node, ALREADY DELIVERED this cascade.  `cutThrough`
-- drops it from the registry and deliberately emits NO close for it
-- (its exhausted close went out on its own emit — Evaluator's
-- `delivered ∧ memberSource src dying` guard), so the registry loses
-- an entry the close list never accounts for: 1 ≡ 0 + 0.
--
-- CONSEQUENCE, and it is a design finding rather than a missing lemma:
-- the take-cut edge cannot be re-keyed off envSrc while its consumer
-- is `BurstInv.live-matches`.  Either live-matches itself is re-keyed
-- to exclude envSrc — mirroring what `FoldInv`'s SHADOW field already
-- does deliberately (.Part8, "envSrc is excluded — its own
-- delivery/close is accounted separately") — or the envSrc instance is
-- carried by a separate accounting that pays for the skipped close.
-- That is a restatement of the well-formedness branch's CENTRAL
-- invariant, so it is a ruling, not a grind.
_ : ∀ (n : ℕ) (Γ : Ctx n) →
    (∀ {n′} {Γ′ : Ctx n′} {t}
       (s : Source) (nid : NodeId) (dlv : List RegId) (wm : RegId)
       (dying : List Source) (reg : List (RegId × Source × Chain Γ′ t)) →
     countRegs s reg
       ≡ countRegs s (proj₁ (cutThrough nid dlv wm dying reg))
         + closeCount s (proj₁ (proj₂ (cutThrough nid dlv wm dying reg))))
    → ⊥
_ = λ n Γ bal → 1+n≢0 (bal {Γ′ = Γ} {t = natᵗ} 0 0 (0 ∷ []) 0 (0 ∷ [])
                           ((0 , 0 , natᵗ , take-f 0 ↠ root) ∷ []))

-- ════════════════════════════════════════════════════════════════
-- THE INPUT CLAUSE, ASSEMBLED — a real body over three leaves
-- ════════════════════════════════════════════════════════════════
-- `initReg-wf` is APPLIED here, which pays its premises.  The hot/live arm
-- needs
--
--     liveTypeOK? (toℕ i) (lookup Γ i) (Sched.live sched) ≡ true
--
-- which nothing in scope supplies, because `Sched` (Rx.Evaluator) is a
-- plain record whose `live` and `slots` are independent and nothing
-- tied them across a schedule transition.  Anthony's ruling
-- put the fact on BurstInv/Inv/Mid as the `hot-live` field rather than
-- into this signature as a hypothesis — tracked debt, not laundered —
-- and `BurstInv.hot-live binv i (cong hotSlot? slotEq)` spends it
-- here.  See CLAUDE.md, "A POSTULATE MUST BE A LEAF".
--
-- The cold/no-async arm is `oneShotBurst` verbatim, so the proven
-- `oneShotBurst-wf` (.Part2) closes it outright.  Two of four arms are
-- discharged; the leaves are the other two plus the shared slot.
subscribeE-input-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
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
subscribeE-input-wf fuel i κ id now sched st S binv deq nodry
  with Sched.slots sched i in slotEq
... | shared d = subscribeSharedSlot-wf fuel i d κ id now sched st S binv deq nodry
... | scripted (cold sync []) =
      let (S′ , run , binv′) = oneShotBurst-wf sync id sched st S binv deq
      in S′ , run , binv′ , refl
... | scripted (cold sync (d ∷ ds)) =
      let (S′ , run , binv′) =
            input-cold-async-wf i sync d ds κ id now sched st S binv deq
      in S′ , run , binv′ , refl
... | scripted (hot h) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true =
        let (S′ , run , binv′) = input-hot-spent-wf i id sched st S binv deq
        in S′ , run , binv′ , refl
...   | false =
        let (S′ , run , binv′) =
              initReg-wf (toℕ i) κ id st sched S binv
                (BurstInv.hot-live binv i (cong hotSlot? slotEq))
        in S′ , run , binv′ , refl
