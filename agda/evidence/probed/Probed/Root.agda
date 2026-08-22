-- ROOT-EXIT COHERENCE PROBES — the computable half of the Part4 pair.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library layout
-- makes the name `Probed.Root` unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by `Probed.Main`.
-- Receipts live in the headers of `root-caches` / `root-done-plumbed`
-- (.Part4), whose residues are the two leaves named below.
-- TARGET: root-mergeCache
-- TARGET: root-entry-sunk
--
-- WHAT IS BEING TESTED, and why it is testable at all: both postulates'
-- CONCLUSIONS are decidable Bool functions of a run — `cachesValid` and
-- `allShareSunk` over the settled root-exit state — so instantiating at
-- concrete programs either refutes them or gives a real receipt.  Their
-- former shared merge-cert HYPOTHESIS is decidable too (`mergeCertAt`), so
-- it is pinned at the same states rather than assumed.  That postulate was
-- retired when the two assemblies became real bodies (it does not
-- close their k ≡ 0 case — see Part4.root-mergeCache); the pins stay, since
-- they are the evidence base a restated merge coherence will be built on.
--
-- EVERY ROW IS LABELLED.  A row that could not have failed is not a row:
-- `cachesValid [] reg` and `allShareSunk []` are both `true` outright, so
-- a program with no nodes, or one whose registry drains, proves nothing.
-- Each load-bearing block therefore pins the SIZE of the thing being
-- quantified over, in the same file, by refl.
module Probed.Root where

open import Data.Bool using (Bool; true; false; not)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using ([]; _∷_; null)
open import Data.Nat  using (zero; suc)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Vec  using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin  using (zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot; Source)
open import Rx.Exp  using (Ctx; Closed; natᵗ; strmᵗ; nat̂; input; ofᵉ; takeᵉ; mergeAllᵉ; concatAllᵉ; switchAllᵉ;
  exhaustAllᵉ)
open import Rx.Evaluator using (subscribeE; sched-init; st-init; budgetAt; root; EvalSt; NodeId; Chain; RegId; lookupNode;
  merge-st; aliveThroughᶠ)
open import Rx.Slots using (scripted; shared; Slots)
open import Verify-Well-Formed.Part1 using (cachesValid; allShareSunk; innerInstsP)
open import Rx.Protocol using (ProtocolSt; runProtocol; protocol-init)

----------------------------------------------------------------------
-- The runner: exactly the state both postulates speak about — the
-- SETTLED root exit, `proj₂ (proj₂ (subscribeE … root 0 0 …))`.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

-- ═══ THE MERGE-CERT DECISION PROCEDURE, and it lives here because the
-- probe is its only consumer.  It sat in .Part4 while a MODULE_ROOTS
-- entry made this file read as reachable from Main; with the probes out
-- of that table the definition had no proof consumer, which is the
-- wiring law reporting the truth rather than a new problem.  A restated
-- merge-cert in .Part4 states its own predicate; these rows are evidence
-- about THIS one.
-- WHY IT SURVIVES ITS OWN COUNTEREXAMPLE SHAPE (probed;
-- the probe is deleted — this header is the receipt).  A hand-built
-- state with k = 0 and a live from-inner registration (dying /
-- delivered / cancelled all empty) makes mergeCertAt FALSE, so the
-- whole question is that shape's REACHABILITY — and the cascade
-- ordering answers it:
--   1. cascadeLatch fires FIRST, setting dying = [arrSource a] before
--      any chain is processed;
--   2. cascadeGo adds rid to delivered BEFORE calling chainStep;
--   3. so when innerFinish decrements k to 0, the spent registration
--      is dying AND delivered.  aliveThroughᶠ's liveness disjunct is
--      `not (src ∈ dying) ∨ not (rid ∈ delivered)` — false only when
--      BOTH hold — and the ordering supplies both, so
--      aliveThroughᶠ ≡ false.  The "both" is load-bearing: either
--      mark alone leaves the registration alive.
-- The bad shape is unreachable by this path.  REACHED coverage (rows
-- driven through subscribeE → cascadeLatch → cascadeGo, not
-- hand-built): the single-inner mergeAll shape, mid-cascade and
-- post-cascadeFinish — the decisive rows.  STILL UNCOVERED: the
-- multi-source inner reached only at hand-built states, concat /
-- switch / exhaust and nested *All, and the CUT route to k ≡ 0
-- (registrations also drop at take-cuts — a distinct path).

-- a registration carries an ALIVE from-inner instance of mnid: its
-- path mentions some inst via a `from-inner _ mnid inst` frame, and
-- that inst is alive (aliveThroughᶠ)
hasAliveFromInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → EvalSt e → RegId × Source × Chain Γ t → Bool
hasAliveFromInner mnid st c@(_ , _ , (_ , p)) =
  any (λ inst → aliveThroughᶠ inst st c) (innerInstsP mnid p)

-- merge-cert at one node: when merge-st sits at k ≡ 0, no registry
-- entry has an alive from-inner instance of this node.  k ≢ 0 and
-- non-merge nodes are trivially certified.
mergeCertAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → EvalSt e → Bool
mergeCertAt mnid st with lookupNode mnid (EvalSt.nodes st)
... | just (merge-st zero od) =
        not (any (hasAliveFromInner mnid st) (EvalSt.registry st))
... | _ = true

RUN : ∀ {t} (e : Closed Γ₀ t) → EvalSt e
RUN e = proj₂ (proj₂ (subscribeE (budgetAt e ins₀ 0) e root 0 0
                                  (sched-init e ins₀) (st-init e)))

----------------------------------------------------------------------
-- Programs.  P0 is the calibration; the rest each mint at least one
-- node whose counter is a WRITER-ASSERTED CACHE — which is precisely
-- what cachesValid checks against the registry as ground truth.
----------------------------------------------------------------------

P0 : Closed Γ₀ natᵗ                       -- no *All: no nodes at all
P0 = ofᵉ (nat̂ 1 ∷ [])

P1 : Closed Γ₀ natᵗ                       -- one merge-st (activeInners)
P1 = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ []))

P2 : Closed Γ₀ natᵗ                       -- merge over TWO inners
P2 = mergeAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ strmᵗ (ofᵉ (nat̂ 2 ∷ [])) ∷ []))

P3 : Closed Γ₀ natᵗ                       -- nested merge: two merge nodes
P3 = mergeAllᵉ (ofᵉ (strmᵗ P1 ∷ []))

P4 : Closed Γ₀ natᵗ                       -- concat-st (innerActive + queue)
P4 = concatAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ strmᵗ (ofᵉ (nat̂ 2 ∷ [])) ∷ []))

P5 : Closed Γ₀ natᵗ                       -- switch-st (cur)
P5 = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ strmᵗ (ofᵉ (nat̂ 2 ∷ [])) ∷ []))

P6 : Closed Γ₀ natᵗ                       -- exhaust-st (act)
P6 = exhaustAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ strmᵗ (ofᵉ (nat̂ 2 ∷ [])) ∷ []))

P7 : Closed Γ₀ natᵗ                       -- the take-cut edge the header calls out:
P7 = takeᵉ (nat̂ 1) P2                     -- take severs mid-merge, so the merge
                                          -- count LEADS the registry after the cut

----------------------------------------------------------------------
-- ROW SET A — `root-caches`'s conclusion, which is UNCONDITIONAL in
-- (e, ins).  So a single `false` here is an outright refutation of the
-- assembly and of its per-node leaf, not a hint.
----------------------------------------------------------------------

_ : cachesValid (EvalSt.nodes (RUN P0)) (EvalSt.registry (RUN P0)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P1)) (EvalSt.registry (RUN P1)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P2)) (EvalSt.registry (RUN P2)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P3)) (EvalSt.registry (RUN P3)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P4)) (EvalSt.registry (RUN P4)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P5)) (EvalSt.registry (RUN P5)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P6)) (EvalSt.registry (RUN P6)) ≡ true
_ = refl

_ : cachesValid (EvalSt.nodes (RUN P7)) (EvalSt.registry (RUN P7)) ≡ true
_ = refl

----------------------------------------------------------------------
-- NON-VACUITY FOR ROW SET A.  `cachesValid [] reg` is `true` outright,
-- so the rows above are worth nothing unless the node list is actually
-- populated at the state they read.  These pin that it is — by refl, in
-- the same file, so the two facts cannot drift apart.
--
-- P0 is the CALIBRATION and is deliberately the other way: no *All, so
-- no nodes, so its row above is DEGENERATE by construction.  It is kept
-- because a probe set with no known-empty case cannot tell "the
-- predicate holds" from "the predicate was never asked".
----------------------------------------------------------------------

_ : null (EvalSt.nodes (RUN P0)) ≡ true      -- DEGENERATE, on purpose
_ = refl

_ : null (EvalSt.nodes (RUN P1)) ≡ false     -- LOAD-BEARING from here down
_ = refl

_ : null (EvalSt.nodes (RUN P2)) ≡ false
_ = refl

_ : null (EvalSt.nodes (RUN P3)) ≡ false
_ = refl

_ : null (EvalSt.nodes (RUN P4)) ≡ false
_ = refl

_ : null (EvalSt.nodes (RUN P5)) ≡ false
_ = refl

_ : null (EvalSt.nodes (RUN P6)) ≡ false
_ = refl

_ : null (EvalSt.nodes (RUN P7)) ≡ false
_ = refl

----------------------------------------------------------------------
-- ROW SET B — `root-done-plumbed`'s conclusion, `allShareSunk` at
-- the settled root exit.
--
-- IT IS NOT PROBEABLE ON ROW SET A's PROGRAMS, and that is a finding
-- rather than an omission: those programs' registries DRAIN to empty at
-- the root exit (pinned below), and `allShareSunk [] ≡ true` outright.
-- Every row over them would be vacuous — the trap this file's header
-- names.  A live registration at the root exit needs a SHARE, and a
-- share needs a slot, so row set B runs over a one-slot context.
----------------------------------------------------------------------

_ : null (EvalSt.registry (RUN P2)) ≡ true    -- WHY row set A cannot test it
_ = refl

_ : null (EvalSt.registry (RUN P7)) ≡ true
_ = refl

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- one SHARED slot: of(1).share() — the def is live, so chains registered
-- on it end at `share-sink`, which is what `sinksToShare` is looking for
sh : Slots Γ₁
sh zero      = shared (ofᵉ (nat̂ 1 ∷ [])) {ok = tt}
sh (suc ())

RUN₁ : (e : Closed Γ₁ natᵗ) → EvalSt e
RUN₁ e = proj₂ (proj₂ (subscribeE (budgetAt e sh 0) e root 0 0
                                   (sched-init e sh) (st-init e)))

-- the README's own share program: merge(shared, shared)
S1 : Closed Γ₁ natᵗ
S1 = mergeAllᵉ (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input zero) ∷ []))

_ : null (EvalSt.registry (RUN₁ S1)) ≡ true
_ = refl
-- ^ STILL DRAINS, and the reason is the share's DEF: `of(1)` is
-- synchronous, so the share fires and completes inside the subscribe
-- frame and its registrations are gone by the root exit.  So S1's
-- allShareSunk row would be vacuous too.  A share must be over a source
-- that does NOT complete for a registration to survive to the root exit.

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- slot 0: a hot with NO events — never fires, never completes.
-- slot 1: a share over it, so chains registered on slot 1 end at
-- `share-sink` AND are still live when the root exits.
sh₂ : Slots Γ₂
sh₂ zero             = scripted {ok = tt} (hot [])
sh₂ (suc zero)       = shared (input zero) {ok = tt}
sh₂ (suc (suc ()))

RUN₂ : (e : Closed Γ₂ natᵗ) → EvalSt e
RUN₂ e = proj₂ (proj₂ (subscribeE (budgetAt e sh₂ 0) e root 0 0
                                   (sched-init e sh₂) (st-init e)))

S2 : Closed Γ₂ natᵗ
S2 = mergeAllᵉ (ofᵉ (strmᵗ (input (suc zero)) ∷ strmᵗ (input (suc zero)) ∷ []))

_ : null (EvalSt.registry (RUN₂ S2)) ≡ false   -- LOAD-BEARING at last
_ = refl

_ : allShareSunk (EvalSt.registry (RUN₂ S2)) ≡ false
_ = refl

_ : cachesValid (EvalSt.nodes (RUN₂ S2)) (EvalSt.registry (RUN₂ S2)) ≡ true
_ = refl

-- ⚠ allShareSunk is FALSE at that state.  Whether that REFUTES
-- `root-done-plumbed` turns entirely on its guard: the postulate
-- claims allShareSunk only when the root stream drives the protocol to
-- `done ≡ true`.  So compute the guard rather than assume it.
doneOf : Maybe ProtocolSt → Bool
doneOf (just S) = ProtocolSt.done S
doneOf nothing  = false

STREAM₂ : (e : Closed Γ₂ natᵗ) → _
STREAM₂ e = proj₁ (subscribeE (budgetAt e sh₂ 0) e root 0 0
                               (sched-init e sh₂) (st-init e))

_ : doneOf (runProtocol protocol-init (STREAM₂ S2)) ≡ false
_ = refl
-- ^ THE GUARD SAVES IT.  So S2 is NOT a refutation: at a state where
-- allShareSunk fails, the protocol is not done, and the postulate claims
-- nothing.  That is the most useful thing a non-refuting row can say —
-- the `done` hypothesis is LOAD-BEARING, not decoration.

-- The genuinely load-bearing region for root-done-plumbed is
-- done ≡ true AND a non-empty registry.  Candidates:
S3 : Closed Γ₂ natᵗ
S3 = takeᵉ (nat̂ 0) (input (suc zero))          -- take(0): completes at once

S4 : Closed Γ₂ natᵗ
S4 = takeᵉ (nat̂ 1) (input (suc zero))

STREAM : ∀ {t} (e : Closed Γ₀ t) → _
STREAM e = proj₁ (subscribeE (budgetAt e ins₀ 0) e root 0 0
                              (sched-init e ins₀) (st-init e))

_ : doneOf (runProtocol protocol-init (STREAM  P2))    -- CALIBRATION: the
  ∷ doneOf (runProtocol protocol-init (STREAM  P4))    -- guard IS satisfiable
  ∷ doneOf (runProtocol protocol-init (STREAM₂ S3))
  ∷ doneOf (runProtocol protocol-init (STREAM₂ S4)) ∷ []
  ≡ true ∷ true ∷ true ∷ false ∷ []
_ = refl

-- S3 reaches done ≡ true over a share — but its registry is EMPTY too.
_ : null (EvalSt.registry (RUN₂ S3)) ≡ true
_ = refl

_ : allShareSunk (EvalSt.registry (RUN₂ S3)) ≡ true   -- VACUOUS (empty registry)
_ = refl

----------------------------------------------------------------------
-- COVERAGE, STATED AS A BOUNDARY RATHER THAN A RESULT.
--
-- `root-caches`'s conclusion is COVERED non-vacuously: seven
-- programs with populated node lists, spanning merge (three shapes),
-- concat, switch, exhaust, and the take-cut edge its own header calls
-- out as the hard case.  Row set A is a real receipt.
--
-- `root-done-plumbed`'s conclusion is NOT COVERED, and no row here
-- should be read as evidence for it.  Its load-bearing region is
-- `done ≡ true` WITH a live registry, and this probe set never reached
-- it: every state with `done ≡ true` (P2, P4, S3) has a DRAINED
-- registry, making allShareSunk true vacuously, and the one state with a
-- live registry (S2) has `done ≡ false`, where the postulate claims
-- nothing.  S2 is still worth its place — allShareSunk is genuinely
-- FALSE there, so the `done` guard is load-bearing rather than
-- decorative, which is the most a non-refuting row can establish.
--
-- WHAT WOULD CLOSE IT: a program whose root completes while a share
-- registration survives to the root exit.  The postulate's own header
-- asserts such states exist ("its done-flip is a genuine full
-- completion — which leaves only share sinks registered"); this file is
-- the record that none of the obvious constructions produces one.
----------------------------------------------------------------------

-- THE FORMER SHARED HYPOTHESIS.  Both -cores took merge-cert; neither
-- assembly takes it now.  mergeCertAt is decidable, so
-- it is pinned rather than assumed — at every node id the merge programs
-- actually mint, plus one that does not exist (where mergeCertAt is true by
-- its catch-all, hence DEGENERATE).  These rows are now evidence for a
-- FUTURE statement rather than for a live hypothesis, and they are what
-- keeps mergeCertAt honest while it has no consumer in a proof.
_ : mergeCertAt 0 (RUN P1) ∷ mergeCertAt 0 (RUN P2) ∷ mergeCertAt 1 (RUN P3)
  ∷ mergeCertAt 0 (RUN P3) ∷ mergeCertAt 0 (RUN P7) ∷ mergeCertAt 0 (RUN₂ S2)
  ∷ mergeCertAt 99 (RUN P1) ∷ []
  ≡ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ true ∷ []
_ = refl
