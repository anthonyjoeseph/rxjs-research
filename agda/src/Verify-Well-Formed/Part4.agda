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
module Verify-Well-Formed.Part4 where

open import Data.Bool    using (Bool; true; false; if_then_else_; T)
open import Data.Nat     using (ℕ; suc; _≤_; z≤n; s≤s; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (tt)
open import Data.Empty   using (⊥-elim)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; subst)


-- from .Caps-Bridge, not from the top module: the top module is the
-- active caps grind, and importing it here would put this file on that
-- clock.
open import Rx.Prim      using (Id; Source; InstEvent; init; value; close; handoff; complete; EmitKind; exhausted; dried;
  cut; cutPending; _at_from_as_)
open import Rx.Exp       using (Ctx; Closed; Ty)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; RegId; Chain; Path; root; memberSource; NodeId; NodeState; scan-st;
  take-st; mergeAll-st; switch-st; exhaust-st; sched-init; st-init; arrTy; arrSource;
  cascadeGo; subscribeE; sameSource; hasDry; dropSource; budgetAt)
open import Rx.Slots using (Slots)
open import Rx.Protocol  using (ProtocolSt; Owed; countIn; allZero; protocol-init; stepProtocol; runProtocol; paidUp; settle;
  paidOff; applyEvents; removeOne; cancelOwed; bumpOwed; settleInstant)

------------------------------------------------------------------
-- glue: runProtocol distributes over ++, and a fully-paid final
-- state is accepted
------------------------------------------------------------------

open import Verify-Well-Formed.Part1 using (allShareSunk; cachesValid; cachesValidMid; countRegs; countRemaining; lookupOwed;
  nodeCacheOK; regTyped?; sinksToShare; UniqueOwed; zeroExcept)
open import Verify-Well-Formed.Part2 using (BurstInv; CurrentPast; HotLive; Inv)
open import Decide using (just-injᵂ; n≢jᵂ; ∧-intro)

-- ════════════════════════════════════════════════════════════════
-- ONE subscription's burst preserves the frame relation (see the blueprint
-- above for the full clause-by-clause decomposition and build order).
-- Forward type declaration: body placed after subscribeE-take-wf.
-- ════════════════════════════════════════════════════════════════

-- an instant standing on an empty (or absent) owed table settles
≤-up : ∀ {a b : ℕ} → a ≤ b → a ≤ suc b
≤-up z≤n     = z≤n
≤-up (s≤s p) = s≤s (≤-up p)

paid-nothing : (S : ProtocolSt) → ProtocolSt.current S ≡ nothing →
               paidUp S ≡ true
paid-nothing S ceq with ProtocolSt.current S | ceq
... | nothing | refl = refl

paid-empty : (S : ProtocolSt) {j : Id} →
             ProtocolSt.current S ≡ just (j , []) → paidUp S ≡ true
paid-empty S ceq with ProtocolSt.current S | ceq
... | just (j , []) | refl = refl

-- leaving the frame: the open instant settles (owed never seeded ⇒
-- paid), landing Inv-related for the first arrival
--
-- `dyF` ADDED, and it is a RESTATEMENT WITH THE SANCTIONED
-- JUSTIFICATION: the unconditional form is not weakened away, it was
--
-- IT IS FREE AT THE ONLY CALL SITE, which is the point.  burst-final is
-- the root frame-0 exit (.Part8's subscribe-wf, its sole consumer), where
-- `st` is the ROOT subscribe's output over `st-init e` — and `subscribeE`
-- never writes `dying`: the field's only two writers are `shareLatch`
-- (Rx.Evaluator, reached only from dispatchShare ← foldPath) and
-- `cascadeLatch` (:1639, reached only from the cascade).  `subscribeE-dying`
-- (.Part8) is that fact, and `st-init` has `dying ≡ []`, so the premise
-- discharges by `refl`.  This is the same `dyF` the takeᵉ clause could NOT
-- pay — its original comment claimed it "free at a root subscribe", which
-- was right about the root and wrong about inners.  A′ moves it to the one
-- place it is true.
--
-- `BurstInv.live-matches` IS CONDITIONED ON NON-DYING (.Part2's field note)
-- because at a dying source the equation is FALSE — a delivered victim's
-- exhausted close rode its own emit, so the cut drops a registry entry the
-- live list never sees.  `Inv.live-matches`
--   stays ALL-SOURCES, since between cascades `cascadeFinish` has swept
--   the dying source out; this premise is what bridges the two.
burst-final : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sched : Sched Γ) (st : EvalSt e) (S : ProtocolSt) →
  BurstInv 0 sched st S →
  (∀ s → memberSource s (EvalSt.dying st) ≡ false) →
  (ProtocolSt.done S ≡ true → allShareSunk (EvalSt.registry st) ≡ true) →
  cachesValid (EvalSt.nodes st) (EvalSt.registry st) ≡ true →
  Inv 1 sched st S × (paidUp S ≡ true)
burst-final sched st S binv dyF dp cv = inv , paid (BurstInv.current-frame binv)
  where
  past : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       CurrentPast (ProtocolSt.current S) 1
  past (inj₁ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) tt
  past (inj₂ ceq) = subst (λ c → CurrentPast c 1) (sym ceq) (s≤s z≤n)

  paid : (ProtocolSt.current S ≡ nothing)
       ⊎ (ProtocolSt.current S ≡ just (0 , [])) →
       paidUp S ≡ true
  paid (inj₁ ceq) = paid-nothing S ceq
  paid (inj₂ ceq) = paid-empty S ceq

  inv : Inv 1 sched st S
  inv = record
    { live-matches = λ s → BurstInv.live-matches binv s (dyF s)
    ; reg-typed    = BurstInv.reg-typed binv
    ; horizon-low  = ≤-up (BurstInv.horizon-low binv)
    ; current-past = past (BurstInv.current-frame binv)
    ; hot-live     = BurstInv.hot-live binv
    ; done-plumbed = dp
    ; caches       = cv
    }

------------------------------------------------------------------
-- MERGE-CERT — the corrected k↔liveness coherence, this branch's
-- central design question (the anchor's tier-2 mirror).  Blocks the
-- four *All wrap receipts, stepFrame-wf-outer, and the two root-exit
-- postulates below.  The three refutations of the naive candidate
-- (`k ≡ countRegsUnder nid registry`) and the corrected measure are
-- Part8's ESTABLISHMENT block: key on from-inner allNid ≡ mnid frames
-- ONLY (the outer's thru-outer threads mnid too), dedup by inst (a
-- multi-source inner registers two chains under one bump), and
-- exclude spent registrations (finish pred-decrements k while the
-- registry entries linger to cascadeFinish).  That is exactly what
-- `Probed.Root`'s `hasAliveFromInner` / `mergeAllCertAt` compute — they
-- moved there with the probe that is their only consumer, so a
-- restatement here states its own predicate rather than inheriting
-- one whose evidence was earned against a different statement.  Do NOT
-- generalise to a global node↔registry theory, and not onto
-- dispatchShare (standing, Part8).
--
--
-- STATED AT THE SETTLED ROOT EXIT — the same conditioning as the two
-- consumers below, and the one region the refutations do not touch.
-- "Reachable" is not first-class here, so the general mid-fold form
-- enters as a threaded FoldInv field WHEN the six consumer rewrites
-- land (parked behind tier 1); this root-exit form is what the root
-- consumers read meanwhile.
------------------------------------------------------------------

-- NO `mergeAll-cert` POSTULATE LIVES HERE ANY MORE.  It existed
-- ONLY as the hypothesis of `root-caches-core` / `root-done-plumbed-core`,
-- and writing those two assemblies as real bodies showed that hypothesis
-- does not close: see the ALIVE-vs-PRESENT gap recorded on root-mergeAllCache
-- below.  `mergeAllCertAt` LEFT WITH IT, and that is the wiring law rather
-- than a tidy-up: its only consumer was the probe, so once the probe moved
-- to `agda/evidence/probed` this file held a definition no proof reached.
-- It is now `Probed.Root`'s own decision procedure — see the reachability
-- receipt in that file, which travelled with it.  A restated mergeAll-cert
-- states its predicate HERE, freshly; the probe's rows are evidence about
-- the predicate they were written against, and inheriting them across a
-- restatement is the extrapolation the probe rules forbid.
--
-- RECOVERY: git show 5cf9397:agda/src/Verify-Well-Formed/Part4.agda restores
--   the postulate as it stood.

-- the SETTLED root-exit state: the evaluator state the root subscription's
-- burst leaves behind.  Both root-exit facts below are stated at it, and it
-- is the only state at which either is claimed.
rootExitSt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) → EvalSt e
rootExitSt e ins =
  proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                           (sched-init e ins) (st-init e)))

-- ROOT-EXIT done-plumbed, migrated out of BurstInv (see the fork note).  The
-- root subscription's returned stream IS the emitted one, so its done-flip is a
-- genuine full completion — which leaves only share sinks registered.  (On the
-- inner-recursion path this is false, but done-plumbed is never read there; it
-- is consumed ONLY here, at the root frame-0 exit.)
--
-- IT IS A LEAF AND MUST STAY ONE.  `allShareSunk` is a conjunction fold
-- over the registry, so the assembly is writable: the fold's induction is
-- below and the whole residue is the PER-ENTRY leaf.  A parent taking
-- mergeAll-cert instead would have its composition checked by nobody.
-- Leaf-only also shrinks what is at risk — the residue no longer
-- quantifies over the registry, so the FALSITY region the `Probed.Root` sweep
-- could not reach is now a statement about ONE surviving entry — a size a
-- counterexample can actually be built at.
postulate
  -- one registry entry outliving a DONE root exit sinks to a share.  The
  -- `done` guard is load-bearing and measured so: `Probed.Root` reaches a state
  -- whose registry is live and where this is FALSE — with done ≡ false.
  --
  -- AND NOTHING HAS INSTANTIATED THIS STATEMENT, WHICH IS A STRONGER
  -- GAP THAN AN UNPROBED CONCLUSION.  The conclusion computes, so the
  -- obstacle is not decidability: it is that the two premises are
  -- jointly UNINHABITED over every program `Probed.Root` runs.  Each
  -- state it reaches with `done ≡ true` has a DRAINED registry, so the
  -- membership premise has no inhabitant; the one state with a live
  -- registry has `done ≡ false`, so the guard premise has none.  A
  -- point satisfying both is what a receipt for this statement costs,
  -- and until one exists the file is evidence about the GUARD rather
  -- than about the claim, which is why it declares the merge leaf as
  -- its target and not this one.  What would supply the point is a
  -- program whose root completes while a share registration survives
  -- to the root exit; the paragraph above asserts such states exist
  -- and no construction tried so far produces one.
  root-entry-sunk : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
    (S : ProtocolSt) →
    runProtocol protocol-init
      (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                         (sched-init e ins) (st-init e))) ≡ just S →
    ProtocolSt.done S ≡ true →
    (rid : RegId) (src : Source) (u : Ty) (p : Path Γ u t) →
    (rid , src , (u , p)) ∈ EvalSt.registry (rootExitSt e ins) →
    sinksToShare p ≡ true

  -- ROOT-EXIT caches, migrated out of BurstInv for the reason recorded on the
  -- record: the merge count trails the registry inside an inner's burst and
  -- leads it after a take-cut, so only the SETTLED state at the root exit — by
  -- which point every mergeAllBump has landed — satisfies cachesValid.
  --
  -- IT IS A LEAF, on the same grounds as root-entry-sunk above.
  -- `cachesValid` is a conjunction fold
  -- over the node list, so the residue is this PER-NODE leaf — and five of
  -- nodeCacheOK's six constructor clauses are `true` outright, so what is
  -- actually open here is the merge clause alone.
  --
  --
  -- AND MERGE COHERENCE — the branch's own design question — IS UNSTATED, so
  -- the invariant above has no statement to be a corollary of.  The decidable
  -- predicate such a statement would be about lives elsewhere, with its ONLY
  -- consumer, and that is the trap: a coherence stated HERE states its own
  -- predicate and inherits NONE of the evidence earned against that one,
  -- however alike the two read.  What is owed is the
  -- statement, a mid-fold `FoldInv` form of it, and the consumer rewrites
  -- that spend it.
  --
  -- DEAD ROUTE: `mergeAll-cert` (mergeAllCertAt at the root exit) does
  --   NOT discharge even the k ≡ 0 case of this clause, which is what the old
  --   `root-caches-core` hypothesis list silently claimed.  The two predicates
  --   count DIFFERENT things: `countLiveInners` is `nubLen ∘ innerInstsR`, and
  --   innerInstsP collects EVERY `from-inner _ nid j` frame on a registered
  --   path with no aliveness test at all, while mergeAllCertAt only rules out the
  --   ones with `aliveThroughᶠ`.  A registration whose path still mentions a
  --   DEAD instance of nid is therefore counted by countLiveInners and ignored
  --   by mergeAllCertAt, so cert ≡ true is consistent with countLiveInners ≢ 0.
  --   Closing this needs the separate invariant that no dead-but-present
  --   from-inner instance survives in the root-exit registry; that fact does
  --   not exist in the repo today.  The gap was invisible while this was a
  --   -core, and became a type error the moment the assembly was real.
  --
  -- PROBED: NON-VACUOUSLY (`Probed.Root`, `make probed`), in the
  --   assembled form: `cachesValid` holds at the settled root exit for seven
  --   programs whose node lists are pinned non-empty in the same file — merge
  --   (one inner, two inners, nested), concat, switch, exhaust, and
  --   take-over-merge.  That last is the region this header names as the hard
  --   one: the merge count leads the registry after a take-cut, so it is the
  --   edge a wrong cache would show at.
  --   COVERAGE BOUND: eight programs, no μ, no defer, no nesting past two
  --   levels, and a single slot context at most.
  --   TIED at four of them — this statement applied at the program and
  --   the cell, so the type is generated from it rather than restated:
  --   the one-inner shape, the BOUNDED face carrying a limit, the
  --   take-cut edge (whose merge node sits second behind the take, so
  --   the cut leaves the node the count lives on in place), and the
  --   only point whose registry is NON-EMPTY at the exit.  That last
  --   is what the other three cannot buy: elsewhere the predicate is
  --   asked about a count against a drained registry, and there it is
  --   asked about a live count of two against two surviving
  --   registrations.
  root-mergeAllCache : ∀ {n} {Γ : Ctx n} {t} {w} (e : Closed Γ t) (ins : Slots Γ)
    (nid : NodeId) (lim : Maybe ℕ) (k : ℕ) (q : List (Closed Γ w)) (od : Bool) →
    (nid , mergeAll-st lim k q od) ∈ EvalSt.nodes (rootExitSt e ins) →
    nodeCacheOK nid (mergeAll-st lim k q od)
      (EvalSt.registry (rootExitSt e ins)) ≡ true

-- the per-node residue, split on the constructor: four of nodeCacheOK's
-- five clauses are `true` outright, so the whole open content is the
-- mergeAll one -- and it is now open at EVERY limit, the old concat face
-- having been a `true` placeholder over the same count.
root-nodeCache : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (nid : NodeId) (s : NodeState Γ) →
  (nid , s) ∈ EvalSt.nodes (rootExitSt e ins) →
  nodeCacheOK nid s (EvalSt.registry (rootExitSt e ins)) ≡ true
root-nodeCache e ins nid (scan-st _)       m = refl
root-nodeCache e ins nid (take-st _)       m = refl
root-nodeCache e ins nid (switch-st _ _)   m = refl
root-nodeCache e ins nid (exhaust-st _ _)  m = refl
root-nodeCache e ins nid (mergeAll-st lim k q od) m =
  root-mergeAllCache e ins nid lim k q od m

root-done-plumbed : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
  (S : ProtocolSt) →
  runProtocol protocol-init
    (proj₁ (subscribeE (budgetAt e ins 0) e root 0 0
                       (sched-init e ins) (st-init e))) ≡ just S →
  ProtocolSt.done S ≡ true →
  allShareSunk (EvalSt.registry
    (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                              (sched-init e ins) (st-init e))))) ≡ true
root-done-plumbed {n} {Γ} {t} e ins S req deq =
  go (EvalSt.registry (rootExitSt e ins))
     (λ rid src u p m → root-entry-sunk e ins S req deq rid src u p m)
  where
  go : (r : List (RegId × Source × Chain Γ t)) →
       (∀ rid src u (p : Path Γ u t) →
          (rid , src , (u , p)) ∈ r → sinksToShare p ≡ true) →
       allShareSunk r ≡ true
  go []                          h = refl
  go ((rid , src , (u , p)) ∷ r) h =
    ∧-intro (h rid src u p (here refl))
            (go r (λ rid′ src′ u′ p′ m → h rid′ src′ u′ p′ (there m)))

root-caches : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  cachesValid
    (EvalSt.nodes (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                            (sched-init e ins) (st-init e)))))
    (EvalSt.registry (proj₂ (proj₂ (subscribeE (budgetAt e ins 0) e root 0 0
                                               (sched-init e ins) (st-init e))))) ≡ true
root-caches {n} {Γ} {t} e ins =
  go (EvalSt.nodes (rootExitSt e ins))
     (λ nid s m → root-nodeCache e ins nid s m)
  where
  go : (ns : List (NodeId × NodeState Γ)) →
       (∀ nid s → (nid , s) ∈ ns →
          nodeCacheOK nid s (EvalSt.registry (rootExitSt e ins)) ≡ true) →
       cachesValid ns (EvalSt.registry (rootExitSt e ins)) ≡ true
  go []               h = refl
  go ((nid , s) ∷ ns) h =
    ∧-intro (h nid s (here refl))
            (go ns (λ nid′ s′ m → h nid′ s′ (there m)))

-- the root subscription, composed (at the budget evaluate seeds)

------------------------------------------------------------------
-- one cascade: Mid and its entry/step/exit lemmas, the chain fold
-- composed
------------------------------------------------------------------

-- mid-cascade, CONCRETE, indexed by the chains still to fold.  Two
-- asymmetries a naive "live shadows registry" misses:
--   · for a spent (isLast) arrival the automaton runs AHEAD of the
--     registry — each delivered chain's exhausted close retires its
--     live entry on the spot, but the registry entries drop only at
--     cascadeFinish — so the arrival source's live count equals the
--     obliged remainder of the snapshot, not the registry count;
--   · the owed table exists only once the first chain emit has
--     opened the instant (seeding happens at first delivery), so the
--     ledger is a sum: not-yet-opened (the automaton still stands on
--     the previous, settled instant) or opened with owed[arrSource]
--     = the not-yet-cancelled remainder and every share paid back to
--     zero (a handoff's bump is repaid within its own chainStep).
-- fold-live carries dry-freeness for the remaining fold: Mid's
-- arguments determine every future chainStep, so the premise lives
-- here instead of infecting every step statement
record Mid {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           (a : Arrival Γ) (nextId : Id)
           (ps : List (RegId × Path Γ (arrTy a) t))
           (sched : Sched Γ) (st : EvalSt e)
           (S : ProtocolSt) : Set where
  field
    live-others  : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      countIn s (ProtocolSt.live S) ≡ countRegs s (EvalSt.registry st)
    live-source  : countIn (arrSource a) (ProtocolSt.live S)
      ≡ (if Arrival.isLast a
         then countRemaining ps (EvalSt.cancelled st)
         else countRegs (arrSource a) (EvalSt.registry st))
    reg-typed    : regTyped? (EvalSt.registry st) (Sched.live sched) ≡ true
    horizon-low  : ProtocolSt.horizon S ≤ nextId
    -- the mid-cascade carrier of Inv's `hot-live` — see that field's note
    hot-live     : HotLive sched
    ledger       :
        (CurrentPast (ProtocolSt.current S) nextId × (paidUp S ≡ true))
      ⊎ (Σ Owed λ ow →
           (ProtocolSt.current S ≡ just (nextId , ow))
         × (lookupOwed (arrSource a) ow
              ≡ countRemaining ps (EvalSt.cancelled st))
         × (zeroExcept (arrSource a) ow ≡ true))
    -- after the root completes, only share plumbing survives.  Stated over
    -- the registry cascadeFinish will KEEP (drop the arrival's source iff
    -- isLast, exactly as cascadeFinish does): a completing root chain flips
    -- `done` while its own non-share-sunk registration still sits in the
    -- registry until cascadeFinish sheds it, so the full-registry form is
    -- false in that mid-cascade window.  The load-bearing evaluator fact is
    -- that at the done-flip every non-share-sunk survivor belongs to
    -- arrSource a (a completion only reaches the root once nothing else can
    -- deliver) — so dropping arrSource restores allShareSunk.  mid-final
    -- reads this off directly in both isLast branches (it mirrors
    -- cascadeFinish); mid-init establishes it from Inv's full-registry form
    -- (identity when not isLast; allShareSunk-drop when isLast).
    done-plumbed : ProtocolSt.done S ≡ true →
      allShareSunk (if Arrival.isLast a
                    then dropSource (arrSource a) (EvalSt.registry st)
                    else EvalSt.registry st) ≡ true
    -- node-cache validity, the Mid shadow (cachesValidMid, see its defn):
    -- the ps-INDEXED form.  base = the registry cascadeFinish keeps (drop
    -- arrSource iff isLast); adjustment = mergeAdjust (the unfolded, not-
    -- cancelled, last-live-source arrSource inner-instances under each nid,
    -- the ones whose `finish` is still pending).  At ps≡[] (mid-final) the
    -- adjustment is 0 ⇒ the plain checker over the kept registry, read
    -- verbatim into Inv.caches; at mid-init (ps≡all) it adds back every
    -- arrSource inner ⇒ the plain form over the full registry, from Inv.
    -- Two watch-points drive the (postulated) mid-step transition: (W1) the
    -- last-live-source verdict shifts as delivered/cancelled grow, discharged
    -- by converting the evaluator's own `react` aliveThrough scrutinee, not
    -- the entry snapshot; (W2) a cut cancels a will-finish inst without pred-
    -- decrementing k, so the adjustment is cancelled-gated (mergeAdjust skips
    -- cancelled chains, matching cutThrough's reg-drop).  No cTotal coupling
    -- (parallel ledgers; shared substrate is only registry + delivered/
    -- cancelled/dying).
    caches       : cachesValidMid a ps (EvalSt.nodes st) st ≡ true
    fold-live    : hasDry (proj₁ (cascadeGo a nextId ps sched st)) ≡ false
    -- ADDED (owed-key uniqueness): the open instant's owed table has no
    -- repeated key, so ledger's zeroExcept + the arrival's zero remainder
    -- force allZero — the payoff mid-final reads out.  Preserved by
    -- mid-skip (same S); established by mid-init/mid-step (postulated).
    owed-unique  : ∀ (ow : Owed) →
      ProtocolSt.current S ≡ just (nextId , ow) → UniqueOwed ow ≡ true
    -- the cascade's `dying` set holds only arrSource a (cascadeLatch seeds it to
    -- [arrSource a] iff isLast, else []); fed to FoldInv.dying-envSrc at the seed.
    dying-src : ∀ (s : Source) → sameSource s (arrSource a) ≡ false →
      memberSource s (EvalSt.dying st) ≡ false
    -- SNAPSHOT↔REGISTRY: the not-yet-cancelled snapshot chains inject into the
    -- live registry entries of arrSource — a snapshot chain leaves the registry
    -- ONLY via cutThrough, which also cancels its rid, so uncancelled ⇒ still
    -- registered.  Hence countRemaining ps (the uncancelled snapshot count) is a
    -- lower bound on the current arrSource registry count.  Establishes at
    -- mid-init as an EQUALITY (cascadeLatch resets cancelled ≡ [], so
    -- countRemaining ps [] ≡ length (chainsOf a st) ≡ countRegs, via
    -- chains-count-derived); mid-skip drops a cancelled head (countRemaining
    -- unchanged by cr-skip); mid-step carries it.  Feeds countRegs-arrSrc-pos:
    -- a non-cancelled head forces countRemaining ((rid,p)∷ps) ≥ 1, so the
    -- registry carries ≥ 1 arrSource entry (the non-isLast registry positivity).
    reg-bound    : countRemaining ps (EvalSt.cancelled st)
      ≤ countRegs (arrSource a) (EvalSt.registry st)

------------------------------------------------------------------
-- Protocol foundation for foldPath-wf: a CONSTRUCTIVE stepProtocol.
-- enterInstant abstracts stepProtocol's enter/openFresh split (idle,
-- held, continue) into one Maybe (base-owed × horizon-for-go): `just`
-- means the automaton admits instant i, seeding `go` with that owed and
-- horizon.  stepProtocol-enter then rebuilds stepProtocol's result from
-- that plus the settle and applyEvents outcomes — the reverse of
-- The-Proof's stepProtocol-idle/held/cont (construction, not analysis).
------------------------------------------------------------------

openFreshᴵ : ProtocolSt → Id → Maybe (Owed × Id)
openFreshᴵ S i with settleInstant S
... | nothing = nothing
... | just hz = if hz ≤ᵇ i then just ([] , hz) else nothing

enterInstant : ProtocolSt → Id → Maybe (Owed × Id)
enterInstant S i with ProtocolSt.current S
... | nothing         = openFreshᴵ S i
... | just (j , owed) = if i ≡ᵇ j
      then (if paidOff owed then nothing else just (owed , ProtocolSt.horizon S))
      else openFreshᴵ S i

-- the horizon the automaton opens an instant with never exceeds the instant
-- id: a fresh open only admits when horizon ≤ᵇ id (the openFreshᴵ guard), and
-- a continued instant keeps horizon S, already ≤ id.  Feeds FoldOut.horizon-out.
openFreshᴵ-hz≤ : ∀ (S : ProtocolSt) (i : Id) {ob hz′} →
  openFreshᴵ S i ≡ just (ob , hz′) → hz′ ≤ i
openFreshᴵ-hz≤ S i eq with settleInstant S | eq
... | just hz | eq′ with hz ≤ᵇ i in hi | eq′
...   | true  | refl = ≤ᵇ⇒≤ hz i (subst T (sym hi) tt)

enterInstant-hz≤id : ∀ (S : ProtocolSt) (i : Id) {ob hz′} →
  enterInstant S i ≡ just (ob , hz′) → ProtocolSt.horizon S ≤ i → hz′ ≤ i
enterInstant-hz≤id S i eq hle with ProtocolSt.current S | eq
... | nothing         | eq′ = openFreshᴵ-hz≤ S i eq′
... | just (j , owed) | eq′ with i ≡ᵇ j | eq′
...   | false | eq″ = openFreshᴵ-hz≤ S i eq″
...   | true  | eq″ with paidOff owed | eq″
...     | false | refl = hle

stepProtocol-enter-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (cur : Maybe (Id × Owed))
  {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
    ≡ just (ob , hz′) →
  settle k s lv ob ≡ just ob′ →
  applyEvents es lv ob′ dn ≡ just (L , O , D) →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn })
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter-aux es i s k lv hz dn nothing entEq stEq apEq
  with hz ≤ᵇ i | entEq
... | true | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
  with i ≡ᵇ j | entEq
... | true  | e with paidOff owed | e
...   | false | refl rewrite stEq | apEq = refl
stepProtocol-enter-aux es i s k lv hz dn (just (j , owed)) entEq stEq apEq
    | false | e
  with allZero owed | e
...   | true | e′ with suc j ≤ᵇ i | e′
...     | true | refl rewrite stEq | apEq = refl

stepProtocol-enter : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S : ProtocolSt) {ob hz′ ob′} {L : List Source} {O : Owed} {D : Bool} →
  enterInstant S i ≡ just (ob , hz′) →
  settle k s (ProtocolSt.live S) ob ≡ just ob′ →
  applyEvents es (ProtocolSt.live S) ob′ (ProtocolSt.done S) ≡ just (L , O , D) →
  stepProtocol (es at i from s as k) S
    ≡ just (record { live = L ; horizon = hz′ ; current = just (i , O) ; done = D })
stepProtocol-enter es i s k S entEq stEq apEq =
  stepProtocol-enter-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) (ProtocolSt.current S) entEq stEq apEq

-- the exact converse of stepProtocol-enter: a step that succeeded must have
-- gone through enterInstant, settle and applyEvents, and its result state is
-- pinned by their outputs.  Analysis, where stepProtocol-enter is construction.
-- The branching mirrors stepProtocol's own `enter` — continue an open unpaid
-- instant, or open fresh over an idle slot / a held paid one — so each guard
-- inverted here also settles enterInstant's value on the nose (hence refl).
stepProtocol-extract-aux : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (lv : List Source) (hz : Id) (dn : Bool) (cur : Maybe (Id × Owed))
  {S′ : ProtocolSt} →
  stepProtocol (es at i from s as k)
    (record { live = lv ; horizon = hz ; current = cur ; done = dn }) ≡ just S′ →
  Σ Owed λ ob → Σ Id λ hz′ → Σ Owed λ ob′ → Σ Owed λ O →
    enterInstant (record { live = lv ; horizon = hz ; current = cur ; done = dn }) i
      ≡ just (ob , hz′)
    × settle k s lv ob ≡ just ob′
    × applyEvents es lv ob′ dn ≡ just (ProtocolSt.live S′ , O , ProtocolSt.done S′)
    × ProtocolSt.horizon S′ ≡ hz′
    × ProtocolSt.current S′ ≡ just (i , O)
stepProtocol-extract-aux es i s k lv hz dn nothing eq
  with hz ≤ᵇ i in hi | eq
... | true | eq₁ with settle k s lv [] in seq | eq₁
...   | just o₂ | eq₂ with applyEvents es lv o₂ dn in aeq | eq₂
...     | just (L , O , D) | refl =
          [] , hz , o₂ , O , refl , seq , aeq , refl , refl
stepProtocol-extract-aux es i s k lv hz dn (just (j , owed)) eq
  with i ≡ᵇ j in ij | eq
... | true | eq₁ with paidOff owed in po | eq₁
...   | false | eq₂ with settle k s lv owed in seq | eq₂
...     | just o₂ | eq₃ with applyEvents es lv o₂ dn in aeq | eq₃
...       | just (L , O , D) | refl =
            owed , hz , o₂ , O , refl , seq , aeq , refl , refl
stepProtocol-extract-aux es i s k lv hz dn (just (j , owed)) eq
    | false | eq₁
  with allZero owed in az | eq₁
... | true | eq₂ with suc j ≤ᵇ i in sj | eq₂
...   | true | eq₃ with settle k s lv [] in seq | eq₃
...     | just o₂ | eq₄ with applyEvents es lv o₂ dn in aeq | eq₄
...       | just (L , O , D) | refl =
            [] , suc j , o₂ , O , refl , seq , aeq , refl , refl

stepProtocol-extract-enter : ∀ {A : Set} (es : List (InstEvent A)) (i : Id) (s : Source)
  (k : EmitKind) (S : ProtocolSt) {S′ : ProtocolSt} →
  stepProtocol (es at i from s as k) S ≡ just S′ →
  Σ Owed λ ob → Σ Id λ hz′ → Σ Owed λ ob′ → Σ Owed λ O →
    enterInstant S i ≡ just (ob , hz′)
    × settle k s (ProtocolSt.live S) ob ≡ just ob′
    × applyEvents es (ProtocolSt.live S) ob′ (ProtocolSt.done S)
        ≡ just (ProtocolSt.live S′ , O , ProtocolSt.done S′)
    × ProtocolSt.horizon S′ ≡ hz′
    × ProtocolSt.current S′ ≡ just (i , O)
stepProtocol-extract-enter es i s k S eq =
  stepProtocol-extract-aux es i s k (ProtocolSt.live S) (ProtocolSt.horizon S)
    (ProtocolSt.done S) (ProtocolSt.current S) eq

-- applyEvents plumbing for the root emit: it splits over ++, the
-- accumulated bookkeeping (init/close only — never value/complete, which
-- splitEvents routes to the value list / done flag) leaves `done`
-- untouched, and the value list + optional complete tack on cleanly.



applyEvents-++just : ∀ {A : Set} (es₁ es₂ : List (InstEvent A))
  (lv : List Source) (o : Owed) (d : Bool) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es₁ lv o d ≡ just (L , O , D) →
  applyEvents (es₁ ++ es₂) lv o d ≡ applyEvents es₂ L O D
applyEvents-++just [] es₂ lv o d eq with just-injᵂ eq
... | refl = refl
applyEvents-++just (init x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ (x ∷ lv) o d eq
applyEvents-++just (value v ∷ es) es₂ lv o d eq with d | eq
... | false | eq′ = applyEvents-++just es es₂ lv o false eq′
... | true  | ()
applyEvents-++just (handoff x ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv (bumpOwed x (countIn x lv) o) d eq
applyEvents-++just (complete ∷ es) es₂ lv o d eq =
  applyEvents-++just es es₂ lv o true eq
applyEvents-++just (close x cutPending ∷ es) es₂ lv o d eq
  with removeOne x lv | cancelOwed x o | eq
... | just lv′ | just o′ | eq′ = applyEvents-++just es es₂ lv′ o′ d eq′
... | just lv′ | nothing | ()
... | nothing  | just o′ | ()
... | nothing  | nothing | ()
applyEvents-++just (close x cut ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()
applyEvents-++just (close x exhausted ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()
applyEvents-++just (close x dried ∷ es) es₂ lv o d eq with removeOne x lv | eq
... | just lv′ | eq′ = applyEvents-++just es es₂ lv′ o d eq′
... | nothing  | ()

-- the value list changes nothing but must not ride behind a `complete`
-- (done-nil: a done automaton delivers no value) — so it folds to identity
applyEvents-values : ∀ {A : Set} (vals : List A) (lv : List Source) (o : Owed) (d : Bool) →
  (d ≡ true → vals ≡ []) →
  applyEvents (map value vals) lv o d ≡ just (lv , o , d)
applyEvents-values []       lv o d _    = refl
applyEvents-values (v ∷ vs) lv o d cond with d | cond
... | false | _ = applyEvents-values vs lv o false (λ ())
... | true  | c with c refl
...   | ()

-- the optional trailing complete sets done exactly when fin
applyEvents-maybeComplete : ∀ {A : Set} (fin : Bool) (lv : List Source) (o : Owed) (d : Bool) →
  applyEvents {A} (if fin then complete ∷ [] else []) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-maybeComplete true  lv o d = refl
applyEvents-maybeComplete false lv o d = refl

-- the whole root tail (values then optional complete) after the evs
applyEvents-vc : ∀ {A : Set} (vals : List A) (fin : Bool)
  (lv : List Source) (o : Owed) (d : Bool) → (d ≡ true → vals ≡ []) →
  applyEvents (map value vals ++ (if fin then complete ∷ [] else [])) lv o d
    ≡ just (lv , o , (if fin then true else d))
applyEvents-vc vals fin lv o d cond =
  trans (applyEvents-++just (map value vals) (if fin then complete ∷ [] else [])
          lv o d (applyEvents-values vals lv o d cond))
        (applyEvents-maybeComplete fin lv o d)

-- ── done is monotone: once a `complete` has latched it, it stays ─────────
-- (values reject under done, so a successful run never carries a value past
-- the flip; every other event leaves done untouched, complete only sets it).
-- The subscribe-frame fold reads the CONTRAPOSITIVE: a burst whose final state
-- has done ≡ false never flipped, so done ≡ false held at every emit — exactly
-- what stepProtocol-faithful needs per step.
applyEvents-done-mono : ∀ {A : Set} (es : List (InstEvent A)) (lv : List Source)
  (o : Owed) (d : Bool) {L : List Source} {O : Owed} {D : Bool} →
  applyEvents es lv o d ≡ just (L , O , D) → d ≡ true → D ≡ true
applyEvents-done-mono [] lv o d hyp dt =
  trans (sym (cong (λ r → proj₂ (proj₂ r)) (just-injᵂ hyp))) dt
applyEvents-done-mono (init x ∷ es)    lv o d hyp dt =
  applyEvents-done-mono es (x ∷ lv) o d hyp dt
applyEvents-done-mono (value v ∷ es)   lv o d hyp dt
  rewrite dt = ⊥-elim (n≢jᵂ hyp)
applyEvents-done-mono (handoff s ∷ es)  lv o d hyp dt =
  applyEvents-done-mono es lv (bumpOwed s (countIn s lv) o) d hyp dt
applyEvents-done-mono (complete ∷ es)   lv o d hyp dt =
  applyEvents-done-mono es lv o true hyp refl
applyEvents-done-mono (close s cutPending ∷ es) lv o d hyp dt
  with removeOne s lv | cancelOwed s o | hyp
... | just lv′ | just o′ | hyp′ = applyEvents-done-mono es lv′ o′ d hyp′ dt
applyEvents-done-mono (close s cut ∷ es) lv o d hyp dt
  with removeOne s lv | hyp
... | just lv′ | hyp′ = applyEvents-done-mono es lv′ o d hyp′ dt
applyEvents-done-mono (close s exhausted ∷ es) lv o d hyp dt
  with removeOne s lv | hyp
... | just lv′ | hyp′ = applyEvents-done-mono es lv′ o d hyp′ dt
applyEvents-done-mono (close s dried ∷ es) lv o d hyp dt
  with removeOne s lv | hyp
... | just lv′ | hyp′ = applyEvents-done-mono es lv′ o d hyp′ dt

-- ── splitEvents faithfulness: pushBurst's re-emit runs like the original ──
-- pushBurst re-emits each frame emit as  bookkeeping ++ (frame values) ++
-- maybe-complete, where the bookkeeping/complete-flag come from splitEvents of
-- the incoming events.  Its protocol effect (live, owed, done) equals that of
-- the ORIGINAL events: init/close/handoff drive live/owed identically (values
-- are transparent, so removing/reordering them past bookkeeping is invisible),
-- the frame's own values are equally transparent, and a `complete` anywhere
-- collapses to one trailing `complete` (done is idempotent, and success rules
-- out any value behind it).  This is the pure core of the burst-side frame fold;
-- the frame's transformed values `vals′` are arbitrary here precisely
-- because the protocol never inspects a value payload.

-- companion, done-side: a successful applyEvents-under-done carries NO values
-- (they would reject), so the events are bookkeeping + completes; the trailing
-- complete on the re-emit restores done ≡ true
