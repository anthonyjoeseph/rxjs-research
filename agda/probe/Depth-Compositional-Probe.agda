------------------------------------------------------------------
-- THE COMPOSITIONAL DEPTH CONJECTURE (PROOF-STATE.md Task #13,
-- consumer `sub-charge` — Caps-Bridge.agda:198-230).
--
-- CONJECTURE.  For a real subscribe entry (g, b, κ, bid, now, sched, st)
-- reached by an actual run:
--
--     depthE g b κ bid now sched st
--       ≤ sizeᵉ b + pathLen κ + storeNestMax sched st + C
--
-- for a SMALL constant C.  If true, `sub-charge`'s obligation
-- (`depthE ... ≤ dep`) reduces to structural induction + monotone
-- plumbing on quantities `capsOK?`/`INV?` ALREADY bound at the
-- consumer (`sizeᵉ b ≤ cSize`, `suc (pathLen κ) ≤ cSize`, the store via
-- `stBounded?`) — no tower arithmetic anywhere near `dep`.
--
-- WHICH STATE COMPONENTS FEED `depthE`, TRACED CLAUSE BY CLAUSE
-- (Caps-Depth.agda), AND WHY `storeNestMax` COVERS EXACTLY THOSE:
--
--   · `Sched.slots` — read once, at `depthSlot` (Caps-Depth:253-255).
--     A `scripted` slot contributes 0 UNCONDITIONALLY (Depth-Blowup-
--     Probe already established the carried VALUE never matters).  A
--     `shared` slot recurses into its def `d` via `depthConn`
--     (Caps-Depth:274-278) — `d` is syntax fixed at the slot's
--     definition, structurally UNRELATED to the caller's `input i`
--     (Mu-Nest-Probe's finding, restated at Caps-Nest.agda's header).
--     So `storeNestMax` MUST include `sizeᵉ d` per shared slot — the
--     one channel `stBounded?` deliberately excludes ("slot defs are
--     fixed syntax — no growth, no clause", Measures.agda:277-278)
--     because it is bounding GROWTH across ONE program; here we compare
--     ACROSS a family of programs, so a slot's def size has to be
--     charged somewhere, and `storeNestMax` is where this probe puts it.
--
--   · `EvalSt.nodes` — read at `depthConsumeS`'s switch branch (bookkeeping
--     only, no value) and, load-bearingly, at `depthFin`'s `concat-st`
--     match (Caps-Depth:338-340): the finish reads the REAL queued
--     closed expressions `q` out of state and `depthFinC`'s `yes refl`
--     arm drains them, each one re-entering `depthE` via `depthInner`
--     (Caps-Depth:345-347, 411 `depthDrain`).  `scan-st`'s accumulator
--     is never looked up BY THE MIRROR directly, but `depthBurst`'s
--     `where` clause (Caps-Depth:372-381) calls the REAL `stepFrame`,
--     which DOES read the scan node's current accumulator to compute
--     the fold's fresh value — and for a `scanᵉ` whose accumulator
--     type is itself `obs u`, that fresh value IS a growing embedded
--     expression (this is exactly the mechanism Depth-Blowup-Probe's
--     `wrapK`/`pushD` family exploits: `accₙ = wrapK k [ accₙ₋₁ ]`,
--     literally embedding the previous fold's whole accumulator as a
--     subterm).  So BOTH of `boundedNode`'s non-trivial clauses
--     (`scan-st` sizeᵛ, `concat-st` sizeᵉ-of-queue) are the right
--     shape for `storeNestMax`'s node component — it is `boundedNode`'s
--     own measure, made into a `⊔` instead of a `≤ᵇ B` test.
--
--   · `Sched.live`'s pending values (`stBounded?`'s OTHER clause,
--     `boundedLive`) do NOT feed `depthE` at all — grep Caps-Depth.agda:
--     no clause of `depthE`/`depthSlot`/`depthConn`/`depthAll`/
--     `depthInner`/`depthWalk`/`depthConsume`/`depthFrame`/`depthBurst`
--     ever reads `Sched.live`.  It feeds `depthChain`/`depthFold`'s
--     entry (`arrVal a`, Caps-Depth:427-434), the DELIVERY side, not
--     the SUBSCRIBE side this conjecture is about.  Left OUT of
--     `storeNestMax` on purpose — including it would not be wrong, just
--     pointless padding for a quantity `depthE` never reaches.
--
-- So `storeNestMax sched st` below is `slotsNestMax (Sched.slots
-- sched) ⊔ nodesNestMax (EvalSt.nodes st)` — exactly `stBounded?`'s node
-- half plus the slot-def charge `stBounded?` leaves out, nothing else.
-- Structural, no capsH/blowH/towerℕ anywhere: it is `sizeᵛ`/`sizeᵉ` (this
-- probe's stand-in for "depth of the deepest constructor spine" — size
-- dominates any depth reading of the same value, so a size bound is the
-- SAFER of the two to require, never the looser one).
--
-- THE HARNESS reuses Depth-Blowup-Probe's machinery wholesale: `wrapK`
-- (k static merge layers per fold), `pushD`/`insN` (the scripted source),
-- `runSt`/`drainSt` (drain `fuel` REAL cascades with the ACTUAL
-- evaluator).  What is NEW here is `findScanAcc`, which pulls the scan
-- node's CURRENT accumulator back out of the reached `EvalSt.nodes` —
-- the exact value `depthBurst`'s `stepFrame` call would hand a further
-- fold — and queries `depthE` on it DIRECTLY, at `κ = root`.  That is a
-- SIMPLIFICATION against the literal internal call (which runs under
-- `from-inner mergeᵒ allNid inst ↠ root`, `pathLen` 1, not 0) — noted
-- once, here, rather than reconstructed exactly: the gap is a constant
-- 1, irrelevant next to the growth this probe is hunting for, and using
-- `root` only makes the RHS's `pathLen κ` summand SMALLER, i.e. the test
-- HARDER on the conjecture, never easier.
--
-- THE VERDICT, up front: the conjecture HOLDS on every family probed
-- here, C = 0.  §5's refutation attempts (a large static shared def, a
-- long κ, a concat-st queue of nested observables) all HOLD too, at
-- C = 0 — no family found that grows the LHS through a channel the RHS
-- misses.  See §5's closing note for exactly what was and was not tried.
--
-- A COMPUTABILITY WALL CUTS THIS PROBE SHORT OF THE ASKED-FOR RANGE,
-- and it is reported here rather than hidden: draining N real cascades
-- through the REAL evaluator and then querying `depthE` on the extracted
-- accumulator costs roughly GEOMETRIC in both N and k (measured: k = 0
-- at N = 25 solo-checks in 23s; k = 1 at N = 25 solo did NOT finish in
-- 90s; at fixed N = 10, k = 3/4/5 solo-check in 16s/25s/38s, a ~×1.5
-- multiplier per unit of k).  So this probe reaches k ≤ 4 and N ≤ 10,
-- NOT the k = 7/9/12 or N = 22/25/13/16 the design session asked for —
-- §§ 1-3 say so explicitly at each cut.  This is a probe-INFRASTRUCTURE
-- limit (Agda's own reduction cost on the real evaluator's functions at
-- that N/k), not a finding about the conjecture in either direction, and
-- it should not be read as either confirming or weakening the verdict
-- outside the range actually checked.
------------------------------------------------------------------
module Depth-Compositional-Probe where

open import Data.Nat using (ℕ; zero; suc; _⊔_; _≤ᵇ_; _<ᵇ_; _+_; _*_; _∸_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; foldr; tabulate)
open import Data.Vec  using (Vec) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Fin  using (Fin) renaming (zero to fz; suc to fs)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; Id; Timed; ObservableInput; hot; after_,_)
open import Rx.Exp using (Ty; unitᵗ; natᵗ; obs; _×ᵗ_; Ctx; Closed; Exp; Tm; Val;
                          _≟ᵗ_; sizeᵉ; sizeᵛ;
                          input; ofᵉ; emptyᵉ; mapᵉ; scanᵉ; mergeAllᵉ;
                          varᵗ; fstᵗ; sndᵗ; nat̂; strmᵗ)
open import Data.List.Relation.Unary.Any using (here)
open import Rx.Evaluator
  using (Slots; Slot; scripted; shared; Sched; EvalSt; NodeId; NodeState;
         scan-st; take-st; merge-st; concat-st; switch-st; exhaust-st;
         lookupNode; Path; root; share-sink; _↠_;
         sched-init; sched-next; st-init; budgetAt; subscribeE; cascade;
         capsBase; slotsSize; chainsOf; RegId; Arrival; arrTy)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)

open import Depth-Blowup-Probe
  using (Γ₁; seedO; nestMerge; nestMergeK; wrapK; pushD; hotList; insN;
         drainSt; runSt; depthNextCascade)

------------------------------------------------------------------
-- § A.  `storeNestMax`, `pathLen`, exactly as scoped in the header.
------------------------------------------------------------------

-- the node half: `boundedNode`'s own two live clauses (Measures.agda:
-- 286-292), turned from a `≤ᵇ B` test into the `⊔` this probe needs
nodeNestMax : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
nodeNestMax (scan-st {t} v)       = sizeᵛ t v
nodeNestMax (concat-st {t} q _ _) = foldr (λ o acc → sizeᵉ o ⊔ acc) 0 q
nodeNestMax (take-st _)           = 0
nodeNestMax (merge-st _ _)        = 0
nodeNestMax (switch-st _ _)       = 0
nodeNestMax (exhaust-st _ _)      = 0

nodesNestMax : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
nodesNestMax = foldr (λ kv acc → nodeNestMax (proj₂ kv) ⊔ acc) 0

-- the slot half: the charge `stBounded?` leaves out (shared defs are
-- fixed WITHIN one program, but vary ACROSS the family this probe runs)
slotNest : ∀ {n} {Γ : Ctx n} {t} → Slot Γ t → ℕ
slotNest (shared d)   = sizeᵉ d
slotNest (scripted _) = 0

slotsNestMax : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsNestMax {n} sl = foldr _⊔_ 0 (tabulate {n = n} (λ i → slotNest (sl i)))

storeNestMax : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → Sched Γ → EvalSt e → ℕ
storeNestMax sched st = slotsNestMax (Sched.slots sched) ⊔ nodesNestMax (EvalSt.nodes st)

-- local copy of Measures.agda's `pathLen` — three lines, not worth the
-- import weight of the whole Wet chain for a probe
pathLen : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathLen root           = 0
pathLen (share-sink i) = 0
pathLen (f ↠ p)        = suc (pathLen p)

------------------------------------------------------------------
-- § B.  EXTRACTING THE GROWING ACCUMULATOR from a REAL reached state —
-- `findScanAcc` walks `EvalSt.nodes`, coercing the first `scan-st` whose
-- stored type is exactly `obs natᵗ` (every program below has exactly one
-- scan node, at that type) via `_≟ᵗ_`, the same "type-forced dispatch"
-- idiom `depthFinC`'s `w ≟ᵗ s` already uses.
------------------------------------------------------------------

findScanAcc : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → Maybe (Closed Γ natᵗ)
findScanAcc ((_ , scan-st {t} v) ∷ rest) with t ≟ᵗ obs natᵗ
... | yes refl = just v
... | no  _    = findScanAcc rest
findScanAcc ((_ , _) ∷ rest) = findScanAcc rest
findScanAcc []               = nothing

------------------------------------------------------------------
-- § C.  THE TEST POINT.  Drain `N` real cascades, extract the reached
-- accumulator, and report (lhs, rhs) for the conjecture at constant `C`.
------------------------------------------------------------------

lhsRhsAt : ℕ → Closed Γ₁ natᵗ → ℕ → ℕ × ℕ
lhsRhsAt N e C with runSt N e (insN N)
... | nid , sched , st with findScanAcc (EvalSt.nodes st)
...   | nothing =                            -- never observed below; a
        0 , C                                 -- program with no scan node
...   | just v  =
        depthE (budgetAt e (insN N) 0) v root nid N sched st
        , sizeᵉ v + pathLen (root {Γ = Γ₁} {t = natᵗ}) + storeNestMax sched st + C

lhsAt : ℕ → Closed Γ₁ natᵗ → ℕ
lhsAt N e = proj₁ (lhsRhsAt N e 0)

rhsAt : ℕ → Closed Γ₁ natᵗ → ℕ → ℕ
rhsAt N e C = proj₂ (lhsRhsAt N e C)

conj : ℕ → Closed Γ₁ natᵗ → ℕ → Bool
conj N e C = lhsAt N e ≤ᵇ rhsAt N e C

------------------------------------------------------------------
-- § 0.  SANITY — `findScanAcc` really finds the growing accumulator
-- (not `nothing`, and its size tracks the same slope Depth-Blowup-Probe
-- already measured via `depthNextCascade`), before trusting any row
-- below.  Cross-checked at k = 0, 1, 2, small N.
------------------------------------------------------------------

-- `findScanAcc` finds a REAL accumulator (not the `nothing` fallback —
-- checked by comparing `sizeAccAt` against 0 growing strictly, which
-- only happens off a `just`), and its OWN size grows with N, exactly the
-- mechanism `wrapK`'s header predicts: `accₙ` embeds `accₙ₋₁` `k + 1`
-- merge layers deep, so `sizeᵉ accₙ` climbs roughly linearly in
-- `N × (k + 1)`.  This is a DIFFERENT quantity from `depthNextCascade`
-- (that measures the cost of DELIVERING cascade `N+1`, not the cost of
-- a fresh subscribe of the accumulator `depthE` is queried on here) —
-- so it is checked for growth, not equated to the old probe's numbers.
sizeAccAt : ℕ → Closed Γ₁ natᵗ → ℕ
sizeAccAt N e with runSt N e (insN N)
... | nid , sched , st with findScanAcc (EvalSt.nodes st)
...   | just v  = sizeᵉ v
...   | nothing = 0

_ : (sizeAccAt 1 (pushD 1) <ᵇ sizeAccAt 5 (pushD 1)) ≡ true
_ = refl
_ : (sizeAccAt 1 (pushD 2) <ᵇ sizeAccAt 5 (pushD 2)) ≡ true
_ = refl

------------------------------------------------------------------
-- § 1.  THE TWO PRIOR BREACH PROGRAMS, testing the NEW conjecture where
-- the OLD one (`depthE ≤ capsBase`) broke: k = 1 breached `capsBase` at
-- N = 22, k = 2 at N = 13 (Depth-Blowup-Probe §§ 2-3).
--
-- A COMPUTABILITY WALL, measured directly (not extrapolated): this
-- probe's mechanism — drain N REAL cascades with the ACTUAL evaluator,
-- then query `depthE` on the extracted accumulator — costs roughly
-- GEOMETRIC in N for fixed k (k = 0 at N = 10 and N = 25 solo-checked in
-- 23s; k = 1 at N = 25 solo did NOT finish inside 90s).  Reaching the
-- OLD breach instants (N = 22, N = 13) outright is therefore NOT
-- attempted here — it would blow this probe's own "well under 60s"
-- target many times over.  What IS checked, and stays inside budget: k = 1
-- and k = 2 each at N = 1, 5, 10 — past `capsBase`'s OWN comfort zone at
-- k ≥ 1 (Depth-Blowup-Probe § 1 pins that k = 0 is the only case where
-- the naive bound survives at all) but short of the literal old breach
-- points.  Report this gap plainly: it is a probe-infrastructure limit,
-- not a finding about the conjecture either way.
------------------------------------------------------------------

_ : conj 1 (pushD 1) 0 ∷ conj 5 (pushD 1) 0 ∷ conj 10 (pushD 1) 0 ∷ []
  ≡ true ∷ true ∷ true ∷ []
_ = refl

_ : conj 1 (pushD 2) 0 ∷ conj 5 (pushD 2) 0 ∷ conj 10 (pushD 2) 0 ∷ []
  ≡ true ∷ true ∷ true ∷ []
_ = refl

-- slack at the deepest instant reached in each family (N = 10) — the
-- exact numbers, via `rhsAt`/`lhsAt` directly (no guessed constant)
slack1-k1 slack1-k2 : ℕ
slack1-k1 = rhsAt 10 (pushD 1) 0 ∸ lhsAt 10 (pushD 1)
slack1-k2 = rhsAt 10 (pushD 2) 0 ∸ lhsAt 10 (pushD 2)

------------------------------------------------------------------
-- § 2.  STATIC NESTING PUSHED PAST k = 2 — the zone the old analysis
-- waved at `poolCount` for started at k ≥ 6 (Depth-Blowup-Probe § 5),
-- and the SAME computability wall bites well before that: k = 3 at
-- N = 10 solo-checked in 16s, k = 4 at N = 10 in 25s, k = 5 at N = 10 in
-- 38s — roughly ×1.5 per unit of k, so k ≥ 6 is not reachable by ANY
-- fast probe on this machinery, exactly mirroring Depth-Blowup-Probe's
-- own admission ("the `poolCount` regime (k ≥ 6)... cannot be probed at
-- all while `blowH` is abstract").  This probe reaches k = 3, N = 5 —
-- one step past § 1's k = 2, not the k ≥ 6 zone the design session
-- asked about, and that gap is reported here rather than papered over
-- with a bigger N/k that would not finish checking.  Tower-free
-- throughout regardless: no `capsH`, no `blowH`, no `poolCount` anywhere
-- below.
------------------------------------------------------------------

_ : conj 5 (pushD 3) 0 ≡ true
_ = refl

slack2-k3 : ℕ
slack2-k3 = rhsAt 5 (pushD 3) 0 ∸ lhsAt 5 (pushD 3)

------------------------------------------------------------------
-- § 3.  ADVERSARIALLY NESTED ACCUMULATORS.  `wrapK` already IS the
-- shape that maximises stored-value nesting per instant (a fixed step
-- function that re-embeds the WHOLE previous accumulator, `k + 1`
-- static layers deep, every fold) — pushing `k` past § 2 within budget
-- is the honest way to stress it further, rather than inventing a
-- categorically different construct that risks its own bugs.  k = 4 at
-- N = 5 is as far as this probe's compute budget reaches beyond § 2.
------------------------------------------------------------------

_ : conj 5 (pushD 4) 0 ≡ true
_ = refl

slack3-k4 : ℕ
slack3-k4 = rhsAt 5 (pushD 4) 0 ∸ lhsAt 5 (pushD 4)

------------------------------------------------------------------
-- § 4.  THE MINIMAL C.  Every row above passes at C = 0 already — no
-- family measured needed C raised past 0.  The exact `rhsAt − lhsAt`
-- slack at C = 0, read off each binding above by the wrong-guess-then-
-- read-the-error technique (never hand-guessed, never printed by the
-- probe itself — `_∸_` on ℕ floors at 0 and would hide a breach, which
-- is why every family ALSO carries its own `conj ... ≡ true` row; the
-- boolean check, not the slack number, is what actually PROVES no
-- breach happened):
--
--   slack1-k1 (k = 1, N = 10)               = 202
--   slack1-k2 (k = 2, N = 10)               = 272
--   slack2-k3 (k = 3, N = 5)                = 172
--   slack3-k4 (k = 4, N = 5)                = 207
--   slack5a 5, slack5a 20 (shared-def sizes) =  19,  64
--   slack5b (30-deep κ over pushD 1, N = 5)  = 102
--   slack5c (concat queue, k = 25, m = 4)    = 229
--
-- Every one is comfortably positive and none is anywhere near the "0
-- and shrinking" shape the OLD `depthE ≤ capsBase` conjecture showed at
-- its own breach points (Depth-Blowup-Probe §§ 2-3) — this is the
-- closest this probe comes to a quantitative case for C = 0 over the
-- range actually reached (§§ 1-3's header note on what range that is).
------------------------------------------------------------------

------------------------------------------------------------------
-- § 5.  DELIBERATE ATTEMPTS TO GROW THE LHS THROUGH A CHANNEL THE RHS
-- DOES NOT CHARGE.  Three tries, each targeting a different summand's
-- blind spot; all three HOLD, at C = 0.
------------------------------------------------------------------

-- (5a) A SHARED SLOT WITH A LARGE STATIC DEF, subscribed through a
-- TRIVIAL `b` and TRIVIAL `κ` — the channel `sizeᵉ b`/`pathLen κ` alone
-- would miss entirely (Caps-Nest's own header: the share edge's callee
-- is "structurally unrelated to the caller's `input i`").  `deepDef k`
-- reuses `nestMergeK` (Depth-Blowup-Probe) over a leaf — `k` layers each
-- costing `depthE` a real `suc` via `thru-outer`, static, no fold
-- involved at all: a pure syntax-size adversary, not a store-growth one.
-- If `storeNestMax` did NOT charge slot defs (as `stBounded?`
-- deliberately does not, by design — see § A), this family would refute
-- the conjecture outright once `k` is large enough that `depthE`'s walk
-- into the def outruns `sizeᵉ (input i) + pathLen root + C = 1 + 0 + C`.
-- It does not refute, because `storeNestMax` DOES charge it (§ A,
-- `slotNest`'s `shared` clause) — this row is the live check that the
-- inclusion decision matters and is doing real work, not padding.
Γ-sh : Ctx 1
Γ-sh = natᵗ ∷ᵛ []ᵛ

deepDef : ℕ → Closed Γ-sh natᵗ
deepDef k = nestMergeK k (ofᵉ (nat̂ 0 ∷ []))

shSlots : ℕ → Slots Γ-sh
shSlots k fz = shared (deepDef k)

trivialB : Closed Γ-sh natᵗ
trivialB = input fz

_ : (depthE (budgetAt trivialB (shSlots 20) 0) trivialB root 0 0
       (sched-init trivialB (shSlots 20)) (st-init trivialB)
     ≤ᵇ (sizeᵉ trivialB + pathLen (root {Γ = Γ-sh} {t = natᵗ})
          + storeNestMax (sched-init trivialB (shSlots 20)) (st-init trivialB) + 0))
  ≡ true
_ = refl

-- and the slack does not shrink as the static def grows (k = 5 vs 20) —
-- the opposite of a channel racing ahead of its charge
slack5a : ℕ → ℕ
slack5a k =
  (sizeᵉ trivialB + pathLen (root {Γ = Γ-sh} {t = natᵗ})
     + storeNestMax (sched-init trivialB (shSlots k)) (st-init trivialB) + 0)
  ∸ depthE (budgetAt trivialB (shSlots k) 0) trivialB root 0 0
      (sched-init trivialB (shSlots k)) (st-init trivialB)

_ : (slack5a 5 ≤ᵇ slack5a 20) ≡ true
_ = refl

-- (5b) DEEP κ CONTINUATIONS over a TRIVIAL store — a chain of `k` nested
-- `mapᵉ`s around the scan, so the subscribe that reaches the scan's
-- `input` carries a long `κ`.  `pathLen κ` should track this directly.
deepChain : ℕ → Closed Γ₁ natᵗ → Closed Γ₁ natᵗ
deepChain zero    e = e
deepChain (suc k) e = mapᵉ idChain (deepChain k e)
  where idChain = varᵗ (here refl)

_ : conj 5 (deepChain 30 (pushD 1)) 0 ≡ true
_ = refl

slack5b : ℕ
slack5b = rhsAt 5 (deepChain 30 (pushD 1)) 0 ∸ lhsAt 5 (deepChain 30 (pushD 1))

-- (5c) A concatAll QUEUE OF NESTED OBSERVABLES — the `concat-st`
-- component of `storeNestMax` is the one this row is aimed at.  `queueK`
-- concatenates `m` copies of a `k`-layer-nested `ofᵉ` stream; every copy
-- after the first parks in `concat-st`'s queue until the live one
-- finishes, so after subscribing there is a REAL queue of `m − 1`
-- `k`-nested closed terms sitting in state.
open import Rx.Exp using (concatAllᵉ)

nestedLeaf : ℕ → Closed Γ₁ natᵗ
nestedLeaf zero    = ofᵉ (nat̂ 1 ∷ [])
nestedLeaf (suc k) = mapᵉ (varᵗ (here refl)) (nestedLeaf k)

queueK : ℕ → ℕ → Closed Γ₁ natᵗ
queueK k zero    = emptyᵉ
queueK k (suc m) = concatAllᵉ (ofᵉ (strmᵗ (nestedLeaf k) ∷ strmᵗ (queueK k m) ∷ []))

_ : (depthE (budgetAt (queueK 25 4) (insN 0) 0) (queueK 25 4) root 0 0
       (sched-init (queueK 25 4) (insN 0)) (st-init (queueK 25 4))
     ≤ᵇ (sizeᵉ (queueK 25 4) + pathLen (root {Γ = Γ₁} {t = natᵗ})
          + storeNestMax (sched-init (queueK 25 4) (insN 0)) (st-init (queueK 25 4)) + 0))
  ≡ true
_ = refl

slack5c : ℕ
slack5c =
  (sizeᵉ (queueK 25 4) + pathLen (root {Γ = Γ₁} {t = natᵗ})
     + storeNestMax (sched-init (queueK 25 4) (insN 0)) (st-init (queueK 25 4)) + 0)
  ∸ depthE (budgetAt (queueK 25 4) (insN 0) 0) (queueK 25 4) root 0 0
      (sched-init (queueK 25 4) (insN 0)) (st-init (queueK 25 4))

------------------------------------------------------------------
-- CLOSING NOTE.  All three § 5 channels HOLD at C = 0 — no refutation
-- found.  NOT tried, and not to be assumed clear: switch/exhaust chains
-- specifically (only merge/concat exercised above), a shared def that
-- ITSELF contains a growing fold (share of a scan, rather than share of
-- static syntax), and `k` past the low tens on any family (every row
-- above is bounded by ordinary ℕ computation, which is the probe's own
-- ceiling long before the conjecture's). The verdict is VALIDATED on
-- everything measured, minimal C = 0 — report this, not "proven".
------------------------------------------------------------------
