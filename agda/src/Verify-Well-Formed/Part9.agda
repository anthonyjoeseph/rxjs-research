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
module Verify-Well-Formed.Part9 where

open import Data.Bool    using (Bool; true; false)
open import Data.Fin     using (Fin)
open import Data.Vec     using (lookup)
open import Data.Nat     using (ℕ; zero; suc; _≤_; _≡ᵇ_; _+_; _∸_)
open import Data.Nat.Properties using (+-comm; +-assoc; +-identityʳ)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Bool.ListAction using (any)
open import Data.List.Properties using (++-identityʳ)
open import Data.Maybe   using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import Relation.Nullary using (yes; no)

-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.
open import Rx.Prim      using (Gas; Tick; Id; Source; InstEvent)
open import Rx.Exp       using (Ctx; Closed; _≟ᵗ_; Val; obs)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; share-sink; _↠_; Frame; map-f; scan-f; take-f; from-inner;
  thru-outer; AllOp; mergeAllᵒ; switchᵒ; exhaustᵒ; aliveThroughᶠ; takeVals; cutThrough;
  setNode; memberSource; NodeId; lookupNode; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; foldPath; stepFrame; sameSource; dropSource; sweepLive)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; runProtocol; applyEvents)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part8 using (FoldInv; foldPath-root-wf)
open import Verify-Well-Formed.Part7 using (cut-reg-typed; cutThrough-balance;
                                            cutThrough-no-init)
open import Verify-Well-Formed.Part1 using (allShareSunk; closeCount;
                                            closeCount-++; countRegs;
                                            initCount; initCount-++;
                                            lookupOwed; regTyped?;
                                            sinksToShare; UniqueOwed;
                                            zeroExcept)
open import Verify-Well-Formed.Part4 using (applyEvents-++just)
open import Decide using (force-false)

foldSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (path : Path Γ u t)
  (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → EvalSt e
foldSt sf gas id now envSrc path vals evs fin sched st =
  proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))

foldSched : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (path : Path Γ u t)
  (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Sched Γ
foldSched sf gas id now envSrc path vals evs fin sched st =
  proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))

-- FoldOut: the readoff companion to FoldInv (the POST of one chain's fold).
-- All fields reference only the OUTPUT triple (st″/sched″/S′) plus the input
-- live S (unchanged by frames) and ob′ — so they pass through the frame
-- recursion; envSrc live/registry are output deltas (see the blueprint above).
record FoldOut {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
       (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
       (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
       (ob′ : Owed) (S S′ : ProtocolSt) : Set where
  field
    -- [Mid ps.live-others] SHADOW resynced by applyEvents at the terminal emit
    live-others-out : ∀ (s : Source) → sameSource s envSrc ≡ false →
      countIn s (ProtocolSt.live S′)
        ≡ countRegs s (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
    -- [→ live-source] envSrc's live count drains by exactly its closes in the
    -- accumulated evs (the seed exhausted close, plus any take-head cut).  KEYED
    -- ON closeCount, NOT `if fin`: the `if fin` form is frame-UNSTABLE
    -- — an absorbing *All frame leaves fin′ ≡ false (from-inner react true) while
    -- the seed close still sits in evs draining envSrc, so ∸1 ≢ ∸0 across the
    -- frame.  closeCount is additive over ++, so it threads (the take-head frame
    -- that closes envSrc bumps both sides in step).  mid-step bridges closeCount
    -- envSrc evs → (if isLast a then 1 else 0) at the seed via env-close.
    live-envSrc-out : countIn envSrc (ProtocolSt.live S′)
      ≡ countIn envSrc (ProtocolSt.live S) ∸ closeCount envSrc evs
    -- [→ live-source, non-isLast] registry envSrc unchanged (frames touch inner
    -- sources; the seed exhausted defers to cascadeFinish).  no-take-head; the
    -- take-head cut edge (registry ∸ cutCloseCount envSrc) is deferred
    reg-envSrc-out : countRegs envSrc (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
      ≡ countRegs envSrc (EvalSt.registry st)
    -- [Mid ps.reg-typed]
    reg-typed-out :
      regTyped? (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))
                (Sched.live (foldSched sf gas id now envSrc path vals evs fin sched st)) ≡ true
    -- [Mid ps.horizon-low]
    horizon-out : ProtocolSt.horizon S′ ≤ id
    -- [Mid ps.ledger inj₂ + owed-unique] the delivery pays owed[envSrc] once;
    -- lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′ (applyEvents/fan-out leave
    -- owed[envSrc] alone); zeroExcept from the share diamond, UniqueOwed from
    -- bumpOwed.  mid-step ties lookupOwed envSrc ob′ to countRemaining ps
    current-out : Σ Owed λ Ov →
        (ProtocolSt.current S′ ≡ just (id , Ov))
      × (zeroExcept envSrc Ov ≡ true)
      × (UniqueOwed Ov ≡ true)
      × (lookupOwed envSrc Ov ≡ lookupOwed envSrc ob′)
    -- [Mid ps.done-plumbed] — split into the done-FLIP and the STEADY case,
    -- both keyed on frame-stable protocol states (done S / done S′ are unchanged
    -- by frames; only the terminal emit steps the automaton), per the higher
    -- model's own call.  The done-S′-keyed-with-`if fin` form is NOT
    -- establishable: that `fin` is the INPUT fin, but a *All frame ABSORBS
    -- completion (fin′ ≢ fin, from-inner `react true`), so an `if fin` field
    -- cannot pass the frame recursion.  Keying on done S / done S′ (protocol
    -- states, identical for outer (f↠path′,fin) and recursion (path′,fin′)) is
    -- frame-stable AND encodes fin-out: done S ≡ false ∧ done S′ ≡ true ⟺ this
    -- fold carried completion to root (fin-out ≡ true) under the done-nil
    -- discipline; a swallowed completion leaves done S′ ≡ false.
    --  · FLIP: completion reached root THIS instant.  Then every non-share-sunk
    --    survivor is envSrc's, so dropSource envSrc restores allShareSunk.
    --    Absorption-VACUOUS, which makes it establishable clause-by-clause:
    --    from-inner comes free from the evaluator's own `any aliveThrough ≡
    --    false` certificate; thru-outer (mergeAll-st count and queue / switch) gates
    --    on NODE counts, so it needs a node↔registry coherence fact, added
    --    minimally per wrap clause as forced (same discipline as SHADOW), NOT
    --    globally up front.
    --  · STEADY: already done coming in (done S ≡ true); the registry is fully
    --    plumbed and stepFrame only adds share-sunk inners, so the whole output
    --    registry stays all-share-sunk (⇒ the dropSource form by allShareSunk-drop,
    --    covering both isLast branches mid-step reads).
    -- GUARD (standing): if fin reaches root while a non-envSrc root-sinking
    -- registration survives, that is an evaluator completion BUG, not an
    -- invariant gap — stop and surface it.
    flip-plumbed-out : ProtocolSt.done S ≡ false → ProtocolSt.done S′ ≡ true →
      allShareSunk (dropSource envSrc
        (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st))) ≡ true
    done-plumbed-out : ProtocolSt.done S ≡ true →
      allShareSunk (EvalSt.registry (foldSt sf gas id now envSrc path vals evs fin sched st)) ≡ true

-- cutThrough per-source close/reg BALANCE (take-cut sub-obligation 2): for a
-- source s NOT in `dying`, every removed s-registration emits exactly one
-- s-close (cutThrough skips the close only on delivered ∧ dying, vacuous when
-- s ∉ dying), so the pre-cut registry count splits into the survivors plus the
-- emitted closes.  Pure induction on the registry.
-- FoldInv reads `st` ONLY through its registry (shadow / done-plumbed /
-- reg-typed; every other field is over S / evs / sched).  So a frame that
-- mutates st but leaves the registry fixed — the quiet clauses (scan-f
-- bookkeeping, take-f below its cut) — preserves FoldInv verbatim.  Since no
-- FoldInv field mentions `fin` any more (env-close and done-plumbed dropped), the
-- fin index is a phantom and is relaxed FREELY here (fin → fin′): the from-inner
-- fin-flip clauses need exactly that.  The three registry-facing fields transport
-- across the registry equality; the rest copy verbatim.
FoldInv-reg : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (envSrc : Source) (evs : List (InstEvent (Val Γ t))) (fin fin′ : Bool)
  (sched : Sched Γ) (st st′ : EvalSt e) (S : ProtocolSt) →
  EvalSt.registry st ≡ EvalSt.registry st′ →
  EvalSt.dying st ≡ EvalSt.dying st′ →
  FoldInv id envSrc evs fin sched st S → FoldInv id envSrc evs fin′ sched st′ S
FoldInv-reg id envSrc evs fin fin′ sched st st′ S req deq fi = record
  { ob = FoldInv.ob fi ; hz = FoldInv.hz fi ; ob′ = FoldInv.ob′ fi
  ; Lv = FoldInv.Lv fi ; Ov = FoldInv.Ov fi
  ; enters = FoldInv.enters fi ; pays = FoldInv.pays fi ; applies = FoldInv.applies fi
  ; shadow = λ s h → subst
      (λ r → countIn s (ProtocolSt.live S) + initCount s evs ≡ countRegs s r + closeCount s evs)
      req (FoldInv.shadow fi s h)
  ; reg-typed = subst (λ r → regTyped? r (Sched.live sched) ≡ true) req (FoldInv.reg-typed fi)
  ; horizon-low = FoldInv.horizon-low fi
  ; ov-zero = FoldInv.ov-zero fi ; ov-unique = FoldInv.ov-unique fi
  ; ov-envSrc = FoldInv.ov-envSrc fi
  ; env-init = FoldInv.env-init fi
  ; dying-envSrc = λ s h → subst (λ d → memberSource s d ≡ false) deq (FoldInv.dying-envSrc fi s h) }

-- the three NON-quiet frame clauses, still to grind, each stated PRECISELY at
-- its frame constructor (so map-f/scan-f — proven below — are no longer covered
-- by any postulate).  stepFrame's bookkeeping evs′ brackets against its registry
-- mutation, and the value transform keeps done-nil.  The delivery-side twin of
-- subscribeE-wf's per-clause grind.
--  · take-f CUT edge only: the non-cut branch is quiet and proven below; the
--    cut sub-branch drops the registry to cutThrough's `kept`, closes the
--    victims, and flips fin — stated PRECISELY at the cut result (no stepFrame
--    wrapper), so the non-cut path is no longer covered by any postulate.
--  · from-inner: fin ≡ false quiet, and fin ≡ true switch/exhaust both
--    proven below (FoldInv is fin-independent + they leave the registry fixed).
--    Only mergeAllᵒ (drain subscribes inners → registry grows) is left as a residue.
--  · thru-outer: the outer *All clause (walk subscribes the emitted inners).
--
-- take-cut is PROVEN (stepFrame-wf-take-cut below): shadow from cutThrough-balance
-- + cutThrough-no-init + the dying-envSrc field (dying holds only envSrc, so the
-- cut's per-source close/reg balance goes through); done-plumbed from allShareSunk
-- monotonicity; env-init/reg-typed structurally.  The lone residue is cut-owed —
-- the closes' applyEvents success and owed-shape (registry↔live, genuinely semantic):
postulate
  -- (3) the closes' effect on the open instant: applying the cut's closes to the
  -- fold's running (Lv,Ov) succeeds, keeping the owed shape (a close does
  -- removeOne/cancelOwed, never bumps).  (done-plumbed proven from allShareSunk
  -- monotonicity; env-close dropped with FoldInv.env-close — no longer a residue.)
  cut-owed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (envSrc : Source) (nid : NodeId)
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt)
    (fi : FoldInv id envSrc evs fin sched st S) →
    let (kept , closes , cutRids) =
          cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                     (EvalSt.dying st) (EvalSt.registry st)
    in Σ (List Source) λ Lv → Σ Owed λ Ov →
         (applyEvents closes (FoldInv.Lv fi) (FoldInv.Ov fi) (ProtocolSt.done S)
            ≡ just (Lv , Ov , ProtocolSt.done S))
       × (zeroExcept envSrc Ov ≡ true)
       × (UniqueOwed Ov ≡ true)
       × (lookupOwed envSrc Ov ≡ lookupOwed envSrc (FoldInv.ob′ fi))

  -- mergeAllᵒ + fin ≡ true ONLY.  fin ≡ false is quiet; the switch/exhaust ops
  -- at fin ≡ true leave the registry fixed (only the node counter + the now-
  -- phantom fin change) and are proven in stepFrame-wf below via FoldInv-reg.
  -- mergeAllᵒ is the lone residue: its `drain` subscribes the queued inners, so
  -- the registry grows and shadow/reg-typed genuinely change.  THE UNBOUNDED
  -- LIMIT IS NO LONGER A SEPARATE QUIET CLAUSE: it parks nothing, so its queue
  -- is empty and the drain is the counter decrement the merge face used to
  -- state on its own — one statement now covers both, and the bounded limit
  -- in between, which neither old face could express.
  stepFrame-wf-inner-mergeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (envSrc : Source)
    (allNid inst : NodeId) (path′ : Path Γ s t)
    (vals : List (Val Γ s)) (evs : List (InstEvent (Val Γ t)))
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc evs true sched st S →
    let (vals′ , evs′ , fin′ , sched₁ , st₁) = stepFrame sf id now (from-inner mergeAllᵒ allNid inst) path′ vals true sched st
    in FoldInv id envSrc (evs ++ evs′) fin′ sched₁ st₁ S

  -- thru-outer, and it STRICTLY CONTAINS the mergeAll residue above — do not
  -- pick it up first.  Read off the evaluator (Rx.Evaluator): this clause is
  -- `thruWrap op nid fin (thruWalk fuel op nid κ id now vals sched st)`, and
  -- `thruWalk` (:1166) FOLDS `thruConsume` over the value LIST, threading
  -- (sched, st) element to element.  Three consequences, none of them visible
  -- from the block comment above:
  --  · it is a LIST INDUCTION, not a single frame step.  Every other stepFrame
  --    clause moves the state once; this one moves it once per emitted inner,
  --    so FoldInv has to be re-established at each element and the statement
  --    above is only the fold's endpoint.
  --  · `thruConsume` calls `subscribeInner` on the mergeAll node's
  --    room-free arm, switch and exhaust — so the registry GROWS, which is
  --    exactly the obstacle `stepFrame-wf-inner-mergeAll` records for mergeAllᵒ,
  --    here at all three ops instead of one.
  --  · switchᵒ additionally runs `switchKill` BEFORE subscribing (:1146), so
  --    within one element the registry both shrinks and grows; the shadow and
  --    reg-typed fields see a non-monotone registry, which the mergeAll residue
  --    never has to face.
  -- So the per-element step is the mergeAll residue and the fold above it is new
  -- work on top.  Ordering it after that one is not a preference: proving this
  -- first means proving that one inline.
  stepFrame-wf-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (envSrc : Source)
    (op : AllOp) (nid : NodeId) (path′ : Path Γ u t)
    (vals : List (Val Γ (obs u))) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc evs fin sched st S →
    let (vals′ , evs′ , fin′ , sched₁ , st₁) = stepFrame sf id now (thru-outer op nid) path′ vals fin sched st
    in FoldInv id envSrc (evs ++ evs′) fin′ sched₁ st₁ S

  -- the share fan-out: one handoff emit, then one delivery per share
  -- registration (each its own foldPath) — mutually recursive with
  -- foldPath-wf.  The handoff's owed bump is repaid across the fan-out.
  dispatchShare-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i)))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
    FoldInv id envSrc evs fin sched st S →
    Σ ProtocolSt λ S′ →
      runProtocol S (proj₁ (foldPath sf gas id now envSrc (share-sink i) vals evs fin sched st))
        ≡ just S′

-- take-cut, PROVEN: assemble the cut result's FoldInv from cutThrough-balance
-- (shadow), cutThrough-no-init (env-init/shadow), the dying-envSrc field, and the
-- residue postulate cut-owed (the ledger) plus the proven cut-reg-typed (typing).
stepFrame-wf-take-cut : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (envSrc : Source) (nid : NodeId)
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  FoldInv id envSrc evs fin sched st S →
  let (kept , closes , cutRids) =
        cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                   (EvalSt.dying st) (EvalSt.registry st)
  in FoldInv id envSrc (evs ++ closes) true
       (record sched { live = sweepLive kept (Sched.live sched) })
       (record st { registry = kept
                  ; cancelled = cutRids ++ EvalSt.cancelled st
                  ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) }) S
stepFrame-wf-take-cut id envSrc nid evs fin sched st S fi = record
  { ob = FoldInv.ob fi ; hz = FoldInv.hz fi ; ob′ = FoldInv.ob′ fi
  ; Lv = Lv′ ; Ov = Ov′
  ; enters = FoldInv.enters fi ; pays = FoldInv.pays fi
  ; applies = trans (applyEvents-++just evs closes (ProtocolSt.live S)
                       (FoldInv.ob′ fi) (ProtocolSt.done S) (FoldInv.applies fi)) app
  ; shadow = shadow′
  ; reg-typed = cut-reg-typed nid sched st (FoldInv.reg-typed fi)
  ; horizon-low = FoldInv.horizon-low fi
  ; ov-zero = zx ; ov-unique = uq ; ov-envSrc = ovs
  ; env-init = trans (initCount-++ envSrc evs closes)
                     (cong₂ _+_ (FoldInv.env-init fi) (cutThrough-no-init envSrc nid dlv wm dy reg))
  ; dying-envSrc = FoldInv.dying-envSrc fi
  }
  where
  dlv = EvalSt.delivered st
  wm  = EvalSt.regWatermark st
  dy  = EvalSt.dying st
  reg = EvalSt.registry st
  kept   = proj₁ (cutThrough nid dlv wm dy reg)
  closes = proj₁ (proj₂ (cutThrough nid dlv wm dy reg))
  spec = cut-owed id envSrc nid evs fin sched st S fi
  Lv′ = proj₁ spec
  Ov′ = proj₁ (proj₂ spec)
  app = proj₁ (proj₂ (proj₂ spec))
  zx  = proj₁ (proj₂ (proj₂ (proj₂ spec)))
  uq  = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ spec))))
  ovs = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ spec))))
  shadow′ : ∀ (s : Source) → sameSource s envSrc ≡ false →
    countIn s (ProtocolSt.live S) + initCount s (evs ++ closes)
      ≡ countRegs s kept + closeCount s (evs ++ closes)
  shadow′ s h
    rewrite initCount-++ s evs closes
          | cutThrough-no-init s nid dlv wm dy reg
          | +-identityʳ (initCount s evs)
          | closeCount-++ s evs closes =
      trans (FoldInv.shadow fi s h)
            (trans (cong (_+ closeCount s evs)
                     (cutThrough-balance s nid dlv wm dy reg (FoldInv.dying-envSrc fi s h)))
                   (trans (+-assoc (countRegs s kept) (closeCount s closes) (closeCount s evs))
                          (cong (countRegs s kept +_) (+-comm (closeCount s closes) (closeCount s evs)))))

-- stepFrame-wf, the real function.  map-f is discharged outright: it emits
-- nothing (evs′ ≡ []) and leaves fin/sched/st untouched (Evaluator 501-502),
-- so with vals gone from FoldInv the value transform is irrelevant and
-- preservation is ++-identityʳ ∘ fi.  Every other frame constructor falls to
-- the catch-all, routed to the stepFrame-wf-rest postulate — peeled off one at
-- a time as the wrap clauses land.
stepFrame-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {w u}
  (sf : Gas) (id : Id) (now : Tick) (envSrc : Source)
  (f : Frame Γ w u) (path′ : Path Γ u t)
  (vals : List (Val Γ w)) (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  FoldInv id envSrc evs fin sched st S →
  let (vals′ , evs′ , fin′ , sched₁ , st₁) = stepFrame sf id now f path′ vals fin sched st
  in FoldInv id envSrc (evs ++ evs′) fin′ sched₁ st₁ S
stepFrame-wf sf id now envSrc (map-f fn) path′ vals evs fin sched st S fi
  rewrite ++-identityʳ evs = fi
-- scan-f only rewrites the accumulator node; it emits nothing and leaves the
-- registry (hence FoldInv) fixed.  Mirror stepFrame's dispatch: every node
-- shape but a type-matching scan-st is a no-op (fi verbatim); the matching
-- scan-st changes only `nodes`, transported by FoldInv-reg over refl.
stepFrame-wf {u = u} sf id now envSrc (scan-f fn nid) path′ vals evs fin sched st S fi
  with lookupNode nid (EvalSt.nodes st)
... | nothing                  rewrite ++-identityʳ evs = fi
... | just (take-st k)         rewrite ++-identityʳ evs = fi
... | just (mergeAll-st l a q od) rewrite ++-identityʳ evs = fi
... | just (switch-st ci od)   rewrite ++-identityʳ evs = fi
... | just (exhaust-st ia od)  rewrite ++-identityʳ evs = fi
... | just (scan-st {w} acc) with w ≟ᵗ u
...   | no _     rewrite ++-identityʳ evs = fi
...   | yes refl rewrite ++-identityʳ evs =
        FoldInv-reg id envSrc evs fin fin sched st _ S refl refl fi
-- take-f: like scan-f, a no-op on every node shape but a take-st; the take-st
-- non-cut branch only rewrites the remaining-count node (quiet, FoldInv-reg);
-- the cut branch drops the registry and closes victims (stepFrame-wf-take-cut).
stepFrame-wf sf id now envSrc (take-f nid) path′ vals evs fin sched st S fi
  with lookupNode nid (EvalSt.nodes st)
... | nothing                  rewrite ++-identityʳ evs = fi
... | just (scan-st acc)       rewrite ++-identityʳ evs = fi
... | just (mergeAll-st l a q od) rewrite ++-identityʳ evs = fi
... | just (switch-st ci od)   rewrite ++-identityʳ evs = fi
... | just (exhaust-st ia od)  rewrite ++-identityʳ evs = fi
... | just (take-st k) with takeVals k vals
...   | out , rem , false rewrite ++-identityʳ evs =
        FoldInv-reg id envSrc evs fin fin sched st _ S refl refl fi
...   | out , rem , true  =
        stepFrame-wf-take-cut id envSrc nid evs fin sched st S fi
-- from-inner: fin ≡ false is quiet (react false = no-op); fin ≡ true absorbs the
-- completion (the narrowed stepFrame-wf-inner residue)
stepFrame-wf sf id now envSrc (from-inner op allNid inst) path′ vals evs false sched st S fi
  rewrite ++-identityʳ evs = fi
-- from-inner fin ≡ true.  switch/exhaust leave the registry (and dying)
-- fixed — react true either absorbs (state untouched) or finish only rewrites the
-- node's own field — so with FoldInv now fin-independent, FoldInv-reg transports
-- it (st′/fin′ inferred from the reduced goal).  mergeAllᵒ drains → the residue.
stepFrame-wf sf id now envSrc (from-inner switchᵒ allNid inst) path′ vals evs true sched st S fi
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
... | false with lookupNode allNid (EvalSt.nodes st)
...   | nothing               rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (scan-st _)      rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (take-st _)      rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (mergeAll-st _ _ _ _)   rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (exhaust-st _ _) rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (switch-st nothing _)  rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (switch-st (just c) _) with c ≡ᵇ inst
...     | true  rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...     | false rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
stepFrame-wf sf id now envSrc (from-inner exhaustᵒ allNid inst) path′ vals evs true sched st S fi
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
... | false with lookupNode allNid (EvalSt.nodes st)
...   | nothing               rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (scan-st _)      rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (take-st _)      rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (mergeAll-st _ _ _ _)   rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (switch-st _ _)  rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
...   | just (exhaust-st _ _) rewrite ++-identityʳ evs = FoldInv-reg id envSrc evs true _ sched st _ S refl refl fi
stepFrame-wf sf id now envSrc (from-inner mergeAllᵒ allNid inst) path′ vals evs true sched st S fi
  = stepFrame-wf-inner-mergeAll sf id now envSrc allNid inst path′ vals evs sched st S fi
stepFrame-wf sf id now envSrc (thru-outer op nid) path′ vals evs fin sched st S fi
  = stepFrame-wf-outer sf id now envSrc op nid path′ vals evs fin sched st S fi

-- the done-discipline, as a precondition: a done automaton (root already
-- completed) admits only share-bound folds — a chain reaching the root
-- after completion would be a value-after-complete, which the protocol
-- rejects.  At root (sinksToShare = false) this forces done S ≡ false, so
-- the value list rides; it transfers unchanged through a frame and is
-- vacuous at a share-sink.
-- a hypothesis whose codomain reduces to false forces its subject false

foldPath-wf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u)) (evs : List (InstEvent (Val Γ t)))
  (fin : Bool) (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  FoldInv id envSrc evs fin sched st S →
  (ProtocolSt.done S ≡ true → sinksToShare path ≡ true) →
  Σ ProtocolSt λ S′ →
    runProtocol S (proj₁ (foldPath sf gas id now envSrc path vals evs fin sched st))
      ≡ just S′
foldPath-wf sf gas id now envSrc root vals evs fin sched st S fi ds =
  _ , foldPath-root-wf sf gas id now envSrc vals evs fin sched st S
        (FoldInv.ob fi) (FoldInv.hz fi) (FoldInv.ob′ fi) (FoldInv.Lv fi) (FoldInv.Ov fi)
        (FoldInv.enters fi) (FoldInv.pays fi) (FoldInv.applies fi) done-nil
  where
  df : ProtocolSt.done S ≡ false
  df = force-false (ProtocolSt.done S) ds
  done-nil : ProtocolSt.done S ≡ true → vals ≡ []
  done-nil deq with trans (sym df) deq
  ... | ()
foldPath-wf sf gas id now envSrc (f ↠ path′) vals evs fin sched st S fi ds =
  foldPath-wf sf gas id now envSrc path′
    (proj₁ (stepFrame sf id now f path′ vals fin sched st))
    (evs ++ proj₁ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))
    (proj₁ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st))))
    (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path′ vals fin sched st)))))
    S (stepFrame-wf sf id now envSrc f path′ vals evs fin sched st S fi) ds
foldPath-wf sf gas id now envSrc (share-sink i) vals evs fin sched st S fi ds =
  dispatchShare-wf sf gas id now envSrc i vals evs fin sched st S fi

------------------------------------------------------------------
-- The seed: Mid (head ∷ ps) ⇒ FoldInv at the chainStep seed.  The
-- "counting machine" arithmetic — a key with a positive owed is not
-- paid-off; paying it decrements the key; a source present in `live`
-- can be removed.  These are the owed/live manipulations the enter,
-- pay, and applyEvents seed fields turn on.
------------------------------------------------------------------

lookup-pos-not-allZero : ∀ (s : Source) (ow : Owed) (k : ℕ) →
  lookupOwed s ow ≡ suc k → allZero ow ≡ false
lookup-pos-not-allZero s [] k ()
lookup-pos-not-allZero s ((x , zero)  ∷ ow) k eq with s ≡ᵇ x | eq
... | true  | ()
... | false | eq′ = lookup-pos-not-allZero s ow k eq′
lookup-pos-not-allZero s ((x , suc n) ∷ ow) k eq = refl
