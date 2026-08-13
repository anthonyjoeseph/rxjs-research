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
module Verify-Well-Formed.Part1 where

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

_>>=ᴹ_ : {A B : Set} → Maybe A → (A → Maybe B) → Maybe B
just a  >>=ᴹ f = f a
nothing >>=ᴹ f = nothing

runProtocol-++ : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol S (xs ++ ys)
    ≡ (runProtocol S xs >>=ᴹ λ S′ → runProtocol S′ ys)
runProtocol-++ S []       ys = refl
runProtocol-++ S (x ∷ xs) ys with stepProtocol x S
... | just S′ = runProtocol-++ S′ xs ys
... | nothing = refl

run-++-just : ∀ {A} (S : ProtocolSt) (xs ys : List (InstEmit A))
              {S₁ S₂ : ProtocolSt} →
  runProtocol S xs ≡ just S₁ → runProtocol S₁ ys ≡ just S₂ →
  runProtocol S (xs ++ ys) ≡ just S₂
run-++-just S xs ys {S₁} e₁ e₂ =
  trans (runProtocol-++ S xs ys)
        (trans (cong (λ m → m >>=ᴹ (λ S′ → runProtocol S′ ys)) e₁) e₂)

acceptPaid : (S : ProtocolSt) → paidUp S ≡ true → Accepted (checkFinal (just S))
acceptPaid S eq rewrite eq = accepted

-- dry-freeness splits over ++ (the step lemmas are conditioned on it;
-- the imported budget-sufficient supplies it for the whole seeded run)
true≢false : {A : Set} → true ≡ false → A
true≢false ()

hasDry-++ : ∀ {A : Set} (xs ys : List (InstEmit A)) →
  hasDry (xs ++ ys) ≡ false →
  (hasDry xs ≡ false) × (hasDry ys ≡ false)
hasDry-++ []        ys h = refl , h
hasDry-++ (em ∷ xs) ys h
  with any dryEvent (InstEmit.events em)
... | true  = true≢false h
... | false = hasDry-++ xs ys h

------------------------------------------------------------------
-- Inv, CONCRETE: the between-cascades simulation relation
------------------------------------------------------------------

-- registrations of s, counted off the registry (the writer's ledger
-- the automaton's live multiset must shadow)
countRegs : ∀ {n} {Γ : Ctx n} {t}
          → Source → List (RegId × Source × Chain Γ t) → ℕ
countRegs s [] = zero
countRegs s ((_ , x , _) ∷ r) =
  if s ≡ᵇ x then suc (countRegs s r) else countRegs s r

-- the pending-event ledger: how many init/close for source s sit in an
-- accumulated evs (frames add registrations + init, cuts remove + close;
-- the protocol only drains these at the terminal emit, so mid-fold the
-- registry leads live by exactly initCount ∸ closeCount — the SHADOW three-way)
initCount : ∀ {A : Set} → Source → List (InstEvent A) → ℕ
initCount s []              = zero
initCount s (init x   ∷ es) = if s ≡ᵇ x then suc (initCount s es) else initCount s es
initCount s (value _  ∷ es) = initCount s es
initCount s (close _ _ ∷ es) = initCount s es
initCount s (handoff _ ∷ es) = initCount s es
initCount s (complete ∷ es) = initCount s es

closeCount : ∀ {A : Set} → Source → List (InstEvent A) → ℕ
closeCount s []              = zero
closeCount s (close x _ ∷ es) = if s ≡ᵇ x then suc (closeCount s es) else closeCount s es
closeCount s (init _   ∷ es) = closeCount s es
closeCount s (value _  ∷ es) = closeCount s es
closeCount s (handoff _ ∷ es) = closeCount s es
closeCount s (complete ∷ es) = closeCount s es

-- (registry-dropping closes — cut/cutPending, excluding the deferred
-- `exhausted` — will be counted by a cutCloseCount helper when the take-head
-- edge of reg-envSrc-out is handled; see the FoldOut blueprint above)

-- init/close counts are additive over ++ — the frame threading fact: a frame's
-- accumulated evs is evs ++ evs′, and its envSrc counts split accordingly.
initCount-++ : ∀ {A : Set} (s : Source) (xs ys : List (InstEvent A)) →
  initCount s (xs ++ ys) ≡ initCount s xs + initCount s ys
initCount-++ s []              ys = refl
initCount-++ s (init x   ∷ xs) ys with s ≡ᵇ x
... | true  = cong suc (initCount-++ s xs ys)
... | false = initCount-++ s xs ys
initCount-++ s (value _  ∷ xs) ys = initCount-++ s xs ys
initCount-++ s (close _ _ ∷ xs) ys = initCount-++ s xs ys
initCount-++ s (handoff _ ∷ xs) ys = initCount-++ s xs ys
initCount-++ s (complete ∷ xs) ys = initCount-++ s xs ys

closeCount-++ : ∀ {A : Set} (s : Source) (xs ys : List (InstEvent A)) →
  closeCount s (xs ++ ys) ≡ closeCount s xs + closeCount s ys
closeCount-++ s []              ys = refl
closeCount-++ s (close x _ ∷ xs) ys with s ≡ᵇ x
... | true  = cong suc (closeCount-++ s xs ys)
... | false = closeCount-++ s xs ys
closeCount-++ s (init _   ∷ xs) ys = closeCount-++ s xs ys
closeCount-++ s (value _  ∷ xs) ys = closeCount-++ s xs ys
closeCount-++ s (handoff _ ∷ xs) ys = closeCount-++ s xs ys
closeCount-++ s (complete ∷ xs) ys = closeCount-++ s xs ys

-- snapshot entries still obliged to fire: not yet forgiven by a
-- cutPending (the automaton's remaining owed for the arrival source)
countRemaining : ∀ {X : Set} → List (RegId × X) → List RegId → ℕ
countRemaining []               c = zero
countRemaining ((rid , _) ∷ ps) c =
  if any (_≡ᵇ rid) c then countRemaining ps c else suc (countRemaining ps c)

-- association-list reads on the automaton's owed table
lookupOwed : Source → Owed → ℕ
lookupOwed s []            = zero
lookupOwed s ((x , n) ∷ o) = if s ≡ᵇ x then n else lookupOwed s o

-- every source but s is paid to zero (bumped shares get paid back
-- down within the very chainStep that announced them)
zeroExcept : Source → Owed → Bool
zeroExcept s []            = true
zeroExcept s ((x , n) ∷ o) =
  (if s ≡ᵇ x then true else n ≡ᵇ 0) ∧ zeroExcept s o

-- the owed table's keys never repeat (bumpOwed adds to an existing
-- entry, never a second one): with `zeroExcept s` this pins down every
-- entry, so a zero at s means the whole table is zero (allZero-clean)
notKeyOwed : Source → Owed → Bool
notKeyOwed s []            = true
notKeyOwed s ((x , _) ∷ o) = not (s ≡ᵇ x) ∧ notKeyOwed s o

UniqueOwed : Owed → Bool
UniqueOwed []            = true
UniqueOwed ((x , _) ∷ o) = notKeyOwed x o ∧ UniqueOwed o

-- a path that never reaches the root delivers no values there
sinksToShare : ∀ {n} {Γ : Ctx n} {u t} → Path Γ u t → Bool
sinksToShare root           = false
sinksToShare (share-sink i) = true
sinksToShare (f ↠ p)        = sinksToShare p

allShareSunk : ∀ {n} {Γ : Ctx n} {t}
             → List (RegId × Source × Chain Γ t) → Bool
allShareSunk []                      = true
allShareSunk ((_ , _ , (u , p)) ∷ r) = sinksToShare p ∧ allShareSunk r

------------------------------------------------------------------
-- NODE-CACHE VALIDITY (the first GLOBAL coherence field, 2026-07-19).
--
-- UNIFYING PRINCIPLE: the registry is GROUND TRUTH; node counters
-- (merge-st's activeInners, concat's innerActive, switch's cur, exhaust's
-- act) are WRITER-ASSERTED CACHES of a fact the registry already holds.
-- This field asserts cache validity WHERE THE CACHE IS STILL READABLE —
-- the same writer-asserts / reader-checks discipline as the protocol
-- itself, one level down.  It is NOT seed-provable: merge-st's k is
-- cross-cascade state (set by bumps/decrements in earlier instants,
-- summarising registrations that live across cascades), which a fold's
-- seed and emits carry no information about.  So Inv carries it between
-- cascades and its BurstInv/Mid/FoldInv shadows thread it through.
--
-- The merge counter caches the number of live inner INSTANCES under nid
-- (one instance can hold several registrations — a multi-source inner —
-- so we count DISTINCT inst indices in `from-inner _ nid inst` frames,
-- not registrations).  GUARDED by reachability: `cutThrough` removes the
-- registrations under nid without touching merge-st k (Evaluator take-f),
-- leaving the counter overcounting but HARMLESS — the merge's own chains
-- died in the same cut, so no future fold reads its gate.  So the honest
-- assertion is "IF some live registration still passes `thru-outer nid`,
-- THEN k is exact"; without the guard it is provably false after a cut,
-- with it cut-through preserves it vacuously.

-- distinct-count over ℕ (inst indices): count an element only where it
-- does not recur later in the list
elemℕ : NodeId → List NodeId → Bool
elemℕ x []       = false
elemℕ x (y ∷ ys) = (x ≡ᵇ y) ∨ elemℕ x ys

nubLen : List NodeId → ℕ
nubLen []       = 0
nubLen (x ∷ xs) = if elemℕ x xs then nubLen xs else suc (nubLen xs)

-- the inner INSTANCE indices of node nid mentioned by a frame / path /
-- registry: a `from-inner _ nid inst` contributes inst (a single path
-- mentions a given nid at most once, so per-path there is no dup; the
-- dup is ACROSS registrations of a multi-source inner, collapsed by nubLen)
innerInstsF : ∀ {n} {Γ : Ctx n} {s u} → NodeId → Frame Γ s u → List NodeId
innerInstsF nid (from-inner _ k j) = if k ≡ᵇ nid then j ∷ [] else []
innerInstsF nid _                  = []

innerInstsP : ∀ {n} {Γ : Ctx n} {s t} → NodeId → Path Γ s t → List NodeId
innerInstsP nid root           = []
innerInstsP nid (share-sink _) = []
innerInstsP nid (f ↠ p)        = innerInstsF nid f ++ innerInstsP nid p

innerInstsR : ∀ {n} {Γ : Ctx n} {t}
            → NodeId → List (RegId × Source × Chain Γ t) → List NodeId
innerInstsR nid []                    = []
innerInstsR nid ((_ , _ , (_ , p)) ∷ r) = innerInstsP nid p ++ innerInstsR nid r

countLiveInners : ∀ {n} {Γ : Ctx n} {t}
                → NodeId → List (RegId × Source × Chain Γ t) → ℕ
countLiveInners nid reg = nubLen (innerInstsR nid reg)

-- the reachability guard: does some live registration's path still pass
-- `thru-outer nid` (the OUTER chain of merge node nid)?
frameThruOuter : ∀ {n} {Γ : Ctx n} {s u} → NodeId → Frame Γ s u → Bool
frameThruOuter nid (thru-outer _ k) = k ≡ᵇ nid
frameThruOuter nid _                = false

pathThruOuter : ∀ {n} {Γ : Ctx n} {s t} → NodeId → Path Γ s t → Bool
pathThruOuter nid root           = false
pathThruOuter nid (share-sink _) = false
pathThruOuter nid (f ↠ p)        = frameThruOuter nid f ∨ pathThruOuter nid p

mergeReachable : ∀ {n} {Γ : Ctx n} {t}
               → NodeId → List (RegId × Source × Chain Γ t) → Bool
mergeReachable nid []                    = false
mergeReachable nid ((_ , _ , (_ , p)) ∷ r) = pathThruOuter nid p ∨ mergeReachable nid r

-- one clause per NodeState constructor; only merge populated today.
-- concat/switch/exhaust are the SAME cache-validity story (innerActive /
-- cur / act) and each will be forced when its wrap clause is reached —
-- given a `true` clause now so those land as clause edits, not new fields.
nodeCacheOK : ∀ {n} {Γ : Ctx n} {t}
            → NodeId → NodeState Γ → List (RegId × Source × Chain Γ t) → Bool
nodeCacheOK nid (merge-st k _)    reg = not (mergeReachable nid reg)
                                        ∨ (k ≡ᵇ countLiveInners nid reg)
nodeCacheOK nid (scan-st _)       reg = true
nodeCacheOK nid (take-st _)       reg = true
nodeCacheOK nid (concat-st _ _ _) reg = true
nodeCacheOK nid (switch-st _ _)   reg = true
nodeCacheOK nid (exhaust-st _ _)  reg = true

cachesValid : ∀ {n} {Γ : Ctx n} {t}
            → List (NodeId × NodeState Γ) → List (RegId × Source × Chain Γ t) → Bool
cachesValid []               reg = true
cachesValid ((nid , s) ∷ ns) reg = nodeCacheOK nid s reg ∧ cachesValid ns reg

------------------------------------------------------------------
-- the Mid (mid-cascade) shadow of cachesValid — the ps-INDEXED
-- pending-adjustment (see the Mid record NOTE).  During arrSource a's
-- cascade an inner's `finish` pred-decrements merge-st k while its
-- registrations linger until cascadeFinish, so k leads the raw registry.
-- The base is the registry cascadeFinish WILL keep (drop arrSource iff
-- isLast), and the adjustment adds back the arrSource inner-instances
-- under nid that have NOT yet finished — the ones still to fold.
--
-- mergeAdjust: distinct inner instances of nid drawn from the UNFOLDED,
-- NOT-CANCELLED arrSource chains ps (W2: cancelled chains skipped,
-- countRemaining-style — a cut drops their regs without pred-decrementing
-- k), KEPT only when arrSource is the inst's LAST live source (the inst
-- is absent from `dropSource arrSource registry`; a multi-source inst
-- with a surviving non-arrSource reg is absorbed, no pred k, and is
-- already held by countLiveInners of the dropSourced base — not counted
-- again here).
-- inner insts of nid from the NOT-cancelled chains ps (W2: cancelled
-- chains skipped, countRemaining-style — cutThrough dropped their regs)
collectAdjInsts : ∀ {n} {Γ : Ctx n} {s t}
                → NodeId → List RegId → List (RegId × Path Γ s t) → List NodeId
collectAdjInsts nid cx []              = []
collectAdjInsts nid cx ((rid , p) ∷ r) =
  if any (_≡ᵇ rid) cx
  then collectAdjInsts nid cx r
  else innerInstsP nid p ++ collectAdjInsts nid cx r

-- keep only insts ABSENT from `surv` (dropSource arrSource fully removed
-- them ⇒ arrSource is their last live source ⇒ they still owe a `finish`)
keepAbsent : List NodeId → List NodeId → List NodeId
keepAbsent surv []       = []
keepAbsent surv (i ∷ is) = if elemℕ i surv then keepAbsent surv is else i ∷ keepAbsent surv is

mergeAdjust : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → (a : Arrival Γ)
  → List (RegId × Path Γ (arrTy a) t) → EvalSt e → ℕ
mergeAdjust nid a ps st =
  nubLen (keepAbsent (innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st)))
                     (collectAdjInsts nid (EvalSt.cancelled st) ps))

-- per-node Mid checker: base = the kept registry (dropSource arrSource iff
-- isLast), adjustment added only when isLast (a non-final emit finishes no
-- inner, so k is unchanged and the plain form rides).  Adjustment written
-- FIRST in the sum so ps≡[] reduces `0 + …` definitionally.
nodeCacheMid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → NodeId → (a : Arrival Γ) → List (RegId × Path Γ (arrTy a) t)
  → NodeState Γ → EvalSt e → Bool
nodeCacheMid nid a ps (merge-st k _) st =
  not (mergeReachable nid
        (if Arrival.isLast a then dropSource (arrSource a) (EvalSt.registry st)
         else EvalSt.registry st))
  ∨ (k ≡ᵇ ((if Arrival.isLast a then mergeAdjust nid a ps st else 0)
             + countLiveInners nid
                 (if Arrival.isLast a then dropSource (arrSource a) (EvalSt.registry st)
                  else EvalSt.registry st)))
nodeCacheMid nid a ps (scan-st _)       st = true
nodeCacheMid nid a ps (take-st _)       st = true
nodeCacheMid nid a ps (concat-st _ _ _) st = true
nodeCacheMid nid a ps (switch-st _ _)   st = true
nodeCacheMid nid a ps (exhaust-st _ _)  st = true

cachesValidMid : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  → (a : Arrival Γ) → List (RegId × Path Γ (arrTy a) t)
  → List (NodeId × NodeState Γ) → EvalSt e → Bool
cachesValidMid a ps []               st = true
cachesValidMid a ps ((nid , s) ∷ ns) st = nodeCacheMid nid a ps s st ∧ cachesValidMid a ps ns st

-- SKIP: a cancelled head contributes nothing to the adjustment (collectAdjInsts
-- skips it), so the Mid shadow is stable when mid-skip drops it from ps.
collectAdjInsts-skip : ∀ {n} {Γ : Ctx n} {s t}
  (nid : NodeId) (cx : List RegId) (rid : RegId) (p : Path Γ s t)
  (ps : List (RegId × Path Γ s t)) →
  any (_≡ᵇ rid) cx ≡ true →
  collectAdjInsts nid cx ((rid , p) ∷ ps) ≡ collectAdjInsts nid cx ps
collectAdjInsts-skip nid cx rid p ps h rewrite h = refl

mergeAdjust-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (nid : NodeId) (a : Arrival Γ) (rid : RegId) (p : Path Γ (arrTy a) t)
  (ps : List (RegId × Path Γ (arrTy a) t)) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  mergeAdjust nid a ((rid , p) ∷ ps) st ≡ mergeAdjust nid a ps st
mergeAdjust-skip nid a rid p ps st h =
  cong (λ z → nubLen (keepAbsent (innerInstsR nid (dropSource (arrSource a) (EvalSt.registry st))) z))
       (collectAdjInsts-skip nid (EvalSt.cancelled st) rid p ps h)

cachesValidMid-skip : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (rid : RegId) (p : Path Γ (arrTy a) t)
  (ps : List (RegId × Path Γ (arrTy a) t))
  (nodes : List (NodeId × NodeState Γ)) (st : EvalSt e) →
  any (_≡ᵇ rid) (EvalSt.cancelled st) ≡ true →
  cachesValidMid a ((rid , p) ∷ ps) nodes st ≡ cachesValidMid a ps nodes st
cachesValidMid-skip a rid p ps []              st h = refl
cachesValidMid-skip a rid p ps ((nid , s) ∷ ns) st h =
  cong₂ _∧_ (nc s) (cachesValidMid-skip a rid p ps ns st h)
  where
  nc : (s : NodeState _) → nodeCacheMid nid a ((rid , p) ∷ ps) s st ≡ nodeCacheMid nid a ps s st
  nc (merge-st k od) =
    cong (λ z → not (mergeReachable nid
                       (if Arrival.isLast a then dropSource (arrSource a) (EvalSt.registry st)
                        else EvalSt.registry st))
                ∨ (k ≡ᵇ ((if Arrival.isLast a then z else 0)
                          + countLiveInners nid
                              (if Arrival.isLast a then dropSource (arrSource a) (EvalSt.registry st)
                               else EvalSt.registry st))))
         (mergeAdjust-skip nid a rid p ps st h)
  nc (scan-st _)       = refl
  nc (take-st _)       = refl
  nc (concat-st _ _ _) = refl
  nc (switch-st _ _)   = refl
  nc (exhaust-st _ _)  = refl

-- NIL: at ps≡[] the adjustment vanishes (collectAdjInsts [] ≡ []), so the Mid
-- shadow collapses to the plain checker over the kept registry — what
-- mid-final reads into Inv.caches.
cachesValidMid-nil : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nodes : List (NodeId × NodeState Γ)) (st : EvalSt e) →
  cachesValidMid a [] nodes st
    ≡ cachesValid nodes (if Arrival.isLast a
                         then dropSource (arrSource a) (EvalSt.registry st)
                         else EvalSt.registry st)
cachesValidMid-nil a []              st = refl
cachesValidMid-nil a ((nid , s) ∷ ns) st = cong₂ _∧_ (nc s) (cachesValidMid-nil a ns st)
  where
  nc : (s : NodeState _) →
       nodeCacheMid nid a [] s st
         ≡ nodeCacheOK nid s (if Arrival.isLast a
                              then dropSource (arrSource a) (EvalSt.registry st)
                              else EvalSt.registry st)
  nc (merge-st k od) with Arrival.isLast a
  ... | true  = refl
  ... | false = refl
  nc (scan-st _)       = refl
  nc (take-st _)       = refl
  nc (concat-st _ _ _) = refl
  nc (switch-st _ _)   = refl
  nc (exhaust-st _ _)  = refl

-- the registry↔schedule type-consistency invariant (replaces the old
-- one-lookahead chains-count): every registration's source-type matches
-- every live source of the same source.  Share-sunk registrations whose
-- source has no live entry are unconstrained — chainsOf only ever reads
-- entries of a SCHEDULED source, and those all trace to a LiveSource, so
-- this pins their type-check to pass (chains-count-derived below)
sameTy : Ty → Ty → Bool
sameTy s u with s ≟ᵗ u
... | yes _ = true
... | no  _ = false

liveTypeOK? : ∀ {n} {Γ : Ctx n} → Source → Ty → List (LiveSource Γ) → Bool
liveTypeOK? s u []       = true
liveTypeOK? s u (l ∷ ls) =
  (if LiveSource.source l ≡ᵇ s then sameTy u (LiveSource.elemTy l) else true)
    ∧ liveTypeOK? s u ls

regTyped? : ∀ {n} {Γ : Ctx n} {t} → List (RegId × Source × Chain Γ t)
          → List (LiveSource Γ) → Bool
regTyped? []                      live = true
regTyped? ((_ , s , (u , _)) ∷ r) live = liveTypeOK? s u live ∧ regTyped? r live

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

-- decidable type-equality is reflexive on the nose — lets stepFrame's scan-f
-- dispatch (w ≟ᵗ u) reduce when the node was installed at the matching type
≟ᵗ-refl : ∀ (u : Ty) → (u ≟ᵗ u) ≡ yes refl
≟ᵗ-refl unitᵗ    = refl
≟ᵗ-refl boolᵗ    = refl
≟ᵗ-refl natᵗ     = refl
≟ᵗ-refl (a ×ᵗ b) rewrite ≟ᵗ-refl a | ≟ᵗ-refl b = refl
≟ᵗ-refl (a +ᵗ b) rewrite ≟ᵗ-refl a | ≟ᵗ-refl b = refl
≟ᵗ-refl (obs a)  rewrite ≟ᵗ-refl a = refl

-- reading back the node you just wrote: the scan/take clauses install their node
-- then read it inside stepFrame, so this pins the lookup that dispatch depends on
lookupNode-setNode : ∀ {n} {Γ : Ctx n} (nid : NodeId) (s : NodeState Γ)
  (nodes : List (NodeId × NodeState Γ)) →
  lookupNode nid (setNode nid s nodes) ≡ just s
lookupNode-setNode nid s []             rewrite ≡ᵇ-refl nid = refl
lookupNode-setNode nid s ((k , s′) ∷ r) with k ≡ᵇ nid in keq
... | true  rewrite ≡ᵇ-refl nid = refl
... | false rewrite keq = lookupNode-setNode nid s r
