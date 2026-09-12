module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _^_; _<ᵇ_; _≡ᵇ_; _≤ᵇ_)
open import Data.Nat.Properties using (_<?_; ≤-refl)
open import Data.Nat.ListAction using (sum)
open import Induction.WellFounded using (Acc; acc)
open import Data.List    using (List; []; _∷_; _++_; map; concat; tabulate; null)
open import Data.Bool.ListAction using (any)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Tick; Fuel; Ordinal; Id; Source; Timed; after_,_; hot;
  cold; InstEvent; init; value; close; handoff; complete; cut; cutPending; exhausted; dried;
  subscribe; delivery; plumbing; InstEmit; _at_from_as_)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; _≟ᵗ_; Ctx; Val; Closed; Fn; applyFn; evalTm; unfoldμ; sizeᵉ; syncSizeᵉ; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
-- the order the subscription machine recurses on, in place of a
-- counter: one constructor per non-structural edge, and nothing
-- packed, so no edge owes a ceiling on the components it leaves alone
open import Rx.Strat-Order using (Tri; _≺_; ltU; ltR; ltS; ≺-wellFounded)

variable
  τ : Tri


------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

-- THE SLOT TELESCOPE lives in Rx.Slots and is re-exported here.  Defs
-- must reference only strictly earlier slots (a const telescope) —
-- checked by the generator/decoder, not by these types; a forward
-- reference is rejected there.
open import Rx.Slots using (scripted; shared; Slots; slotsSize)

Stream : ∀ {n} → Ctx n → Ty → Set          -- flat, canonical emission order
Stream Γ t = List (InstEmit (Val Γ t))

Grouped : ∀ {n} → Ctx n → Ty → Set         -- batchSimultaneous's output
Grouped Γ t = List (InstEmit (List (Val Γ t)))
  -- one emit per instant, still a protocol citizen (re-batchable)

------------------------------------------------------------------
-- The global scheduler
------------------------------------------------------------------

record LiveSource {n} (Γ : Ctx n) : Set where
  field source  : Source
        ordinal : Ordinal
        elemTy  : Ty
        pending : List (Tick × Val Γ elemTy)   -- absolute ticks, strictly increasing

record Sched {n} (Γ : Ctx n) : Set where
  field nextOrdinal : Ordinal          -- ordinals mint in subscription order
        nextSource  : Source           -- dynamic sources (colds, deferᵉ bodies) mint from n up
        nextNode    : ℕ                -- node instances mint in subscription order
        live        : List (LiveSource Γ)
        slots       : Slots Γ          -- scripts and shared defs, kept so subscribeE can anchor colds and connect shares

record Arrival {n} (Γ : Ctx n) : Set where
  field tick    : Tick
        ordinal : Ordinal
        source  : Source
        elemTy  : Ty
        payload : Val Γ elemTy
        isLast  : Bool                 -- final scripted value ⇒ the source completes with this arrival

arrTick : ∀ {n} {Γ : Ctx n} → Arrival Γ → Tick
arrTick = Arrival.tick

arrSource : ∀ {n} {Γ : Ctx n} → Arrival Γ → Source
arrSource = Arrival.source

arrTy : ∀ {n} {Γ : Ctx n} → Arrival Γ → Ty               -- the source's element type
arrTy = Arrival.elemTy

arrVal : ∀ {n} {Γ : Ctx n} (a : Arrival Γ) → Val Γ (arrTy a)
arrVal = Arrival.payload

sameSource : Source → Source → Bool
sameSource = _≡ᵇ_

memberSource : Source → List Source → Bool
memberSource s = any (sameSource s)

-- THE UNCONNECTED-SHARE COUNT, outermost component of the order the
-- subscription machine descends on.  A connect moves one shared slot
-- out of the count and nothing puts one back, so that edge descends on
-- a quantity the telescope itself bounds and owes no budget.
unconnAt : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → Fin n → ℕ
unconnAt sl cs i with sl i
... | shared _   = if memberSource (toℕ i) cs then 0 else 1
... | scripted _ = 0

unconn : ∀ {n} {Γ : Ctx n} → Slots Γ → List Source → ℕ
unconn sl cs = sum (tabulate (unconnAt sl cs))

-- THE ENTRY WITNESS, NAMED RATHER THAN INLINED.  Every re-entry from
-- OUTSIDE the subscription machine — the root subscribe, and each
-- arrival's chain fold — starts a fresh descent, so each supplies its
-- own accessibility at the point the program and the slots determine.
-- It is one definition because those points agree, and because every
-- well-formedness statement that quantifies over an entry has to name
-- the same triple: a statement entered at a triple nothing else uses is
-- a statement about a run the evaluator never makes.
rootTri : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Tri
rootTri e sl = unconn sl [] , 2 ^ (sizeᵉ e + slotsSize sl) , syncSizeᵉ e

rootWitness : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ)
            → Acc _≺_ (rootTri e sl)
rootWitness e sl = ≺-wellFounded (rootTri e sl)

-- delta-encoded waits → absolute ticks (gap = suc wait, so a source's
-- ticks are strictly increasing by construction)
resolve : ∀ {A : Set} → Tick → List (Timed A) → List (Tick × A)
resolve anchor []                  = []
resolve anchor ((after w , v) ∷ r) =
  (anchor + suc w , v) ∷ resolve (anchor + suc w) r

-- hots go live at anchor 0, slot i minting source AND ordinal toℕ i —
-- the convention subscribeE relies on to register hot chains.  Shared
-- slots also own source toℕ i but connect lazily, at their first
-- subscription; colds and deferᵉ bodies are registered by subscribeE
-- at subscription time, minting from nextSource/nextOrdinal
-- top-level (not sched-init-local) so the budget-sufficiency proof
-- can case-split each slot's initial LiveSource
mkHot : ∀ {n} {Γ : Ctx n} (ins : Slots Γ) (i : Fin n) → List (LiveSource Γ)
mkHot {Γ = Γ} ins i with ins i
... | scripted (hot async) = record { source = toℕ i ; ordinal = toℕ i
                                    ; elemTy = lookup Γ i ; pending = resolve 0 async } ∷ []
... | scripted (cold _ _)  = []
... | shared _             = []

sched-init : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Sched Γ
sched-init {n = n} {Γ = Γ} e ins = record
  { nextOrdinal = n ; nextSource = n ; nextNode = 0
  ; live = concat (tabulate (mkHot ins)) ; slots = ins }

-- pop the pending arrival minimal by (tick, ordinal), or report empty.
-- The workers are TOP-LEVEL (not where-local of sched-next) so
-- Verify-Well-Formed can reason about the arrival sched-next yields —
-- in particular that it carries its LiveSource's elemTy
schedEarlier : ∀ {n} {Γ : Ctx n} → Arrival Γ → Arrival Γ → Bool   -- ordinals are unique, so no tie survives
schedEarlier a a′ = (Arrival.tick a <ᵇ Arrival.tick a′)
             ∨ ((Arrival.tick a ≡ᵇ Arrival.tick a′) ∧ (Arrival.ordinal a <ᵇ Arrival.ordinal a′))

schedHeadOf : ∀ {n} {Γ : Ctx n} → LiveSource Γ → ⊤ ⊎ (Arrival Γ × LiveSource Γ)
schedHeadOf l with LiveSource.pending l
... | []           = inj₁ tt
... | (t , v) ∷ ps =
      inj₂ ( record { tick = t ; ordinal = LiveSource.ordinal l
                    ; source = LiveSource.source l
                    ; elemTy = LiveSource.elemTy l ; payload = v
                    ; isLast = null ps }
           , record l { pending = ps } )

schedGo : ∀ {n} {Γ : Ctx n} → List (LiveSource Γ) → ⊤ ⊎ (Arrival Γ × List (LiveSource Γ))
schedGo []       = inj₁ tt
schedGo (l ∷ ls) with schedHeadOf l | schedGo ls
... | inj₁ _        | inj₁ _          = inj₁ tt
... | inj₁ _        | inj₂ (a′ , ls′) = inj₂ (a′ , l ∷ ls′)
... | inj₂ (a , l′) | inj₁ _          = inj₂ (a , l′ ∷ ls)
... | inj₂ (a , l′) | inj₂ (a′ , ls′) =
      if schedEarlier a a′ then inj₂ (a , l′ ∷ ls) else inj₂ (a′ , l ∷ ls′)

schedFinish : ∀ {n} {Γ : Ctx n} → Sched Γ →
              ⊤ ⊎ (Arrival Γ × List (LiveSource Γ)) → ⊤ ⊎ (Arrival Γ × Sched Γ)
schedFinish sched (inj₁ _)        = inj₁ tt
schedFinish sched (inj₂ (a , ls)) = inj₂ (a , record sched { live = ls })

sched-next : ∀ {n} {Γ : Ctx n} → Sched Γ → ⊤ ⊎ (Arrival Γ × Sched Γ)
sched-next sched = schedFinish sched (schedGo (Sched.live sched))

------------------------------------------------------------------
-- Node state
------------------------------------------------------------------

NodeId : Set          -- a node instance in the dynamic topology,
NodeId = ℕ            -- numbered in subscription order

data NodeState {n} (Γ : Ctx n) : Set where
  scan-st    : ∀ {t} → Val Γ t → NodeState Γ    -- current accumulator
  take-st    : ℕ → NodeState Γ                  -- emissions remaining
  mergeAll-st : ∀ {t} → (limit : Maybe ℕ) (active : ℕ)
               (queued : List (Closed Γ t)) (outerDone : Bool) → NodeState Γ
               -- ONE state for every concurrency.  The two states this
               -- replaced were each a projection of it: unbounded merge kept
               -- a counter and no queue (`nothing`, q ≡ []), concat kept a
               -- queue and a one-bit counter (`just 1`, active ≤ 1).  Neither
               -- could express the middle, which is where `mergeMap(f , k)`
               -- lives, and the middle is not reachable by combining them:
               -- a bounded mergeAll assigns an arriving inner to the NEXT FREE
               -- lane, and no static partition of the outer into k merges
               -- does that.  The queue carries its element type
               -- existentially, so every read pays a `_≟ᵗ_` — the unbounded
               -- face did not pay one before and its clauses now do.
  switch-st  : (currentInner : Maybe NodeId) (outerDone : Bool) → NodeState Γ
  exhaust-st : (innerActive outerDone : Bool) → NodeState Γ

NodeSt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set
NodeSt {Γ = Γ} e = List (NodeId × NodeState Γ)   -- assoc list, subscription order

lookupNode : ∀ {n} {Γ : Ctx n} → NodeId → List (NodeId × NodeState Γ) → Maybe (NodeState Γ)
lookupNode nid []             = nothing
lookupNode nid ((k , s) ∷ r) = if k ≡ᵇ nid then just s else lookupNode nid r

setNode : ∀ {n} {Γ : Ctx n} → NodeId → NodeState Γ
        → List (NodeId × NodeState Γ) → List (NodeId × NodeState Γ)
setNode nid s []              = (nid , s) ∷ []   -- absent: install (subscribeE normally installs first)
setNode nid s ((k , s′) ∷ r) =
  if k ≡ᵇ nid then (nid , s) ∷ r else (k , s′) ∷ setNode nid s r

------------------------------------------------------------------
-- Registration chains: the dynamic topology, rootward
------------------------------------------------------------------

-- the mergeAll operator tag carries NO limit: the limit lives in the node
-- state, which every consumer already reads, and a second copy in the
-- frame is a copy that can drift from it
data AllOp : Set where
  mergeAllᵒ switchᵒ exhaustᵒ : AllOp

-- one operator the emission passes through, rootward.  deferᵉ
-- contributes NO frame (it merely relays its body), and share is not
-- an operator at all: a shared slot fans out by registry multiplicity,
-- one chain per subscriber (see share-sink / dispatchShare)
data Frame {n} (Γ : Ctx n) : Ty → Ty → Set where
  map-f      : ∀ {s u} → Fn Γ [] [] [] s u → Frame Γ s u
  scan-f     : ∀ {s u} → Fn Γ [] [] [] (u ×ᵗ s) u → NodeId → Frame Γ s u
  take-f     : ∀ {s} → NodeId → Frame Γ s s
  from-inner : ∀ {s} → AllOp → (allNode innerInstance : NodeId) → Frame Γ s s
               -- exiting a subscribed inner: the *All's own node, and
               -- this inner subscription's instance (switch kills by it)
  thru-outer : ∀ {u} → AllOp → NodeId → Frame Γ (obs u) u
               -- the value IS an inner obs: consumed, subscribed, burst grafted

data Path {n} (Γ : Ctx n) : Ty → Ty → Set where   -- source element type → root type
  root       : ∀ {t} → Path Γ t t
  share-sink : ∀ {t} (i : Fin n) → Path Γ (lookup Γ i) t
               -- the chain ends at shared slot i, not the root: its
               -- values are delivered to the share's subject and fan
               -- out to every chain registered on source toℕ i
  _↠_        : ∀ {s u t} → Frame Γ s u → Path Γ u t → Path Γ s t

Chain : ∀ {n} → Ctx n → Ty → Set   -- a registration: its source element type packed with its rootward path
Chain Γ t = Σ Ty (λ s → Path Γ s t)

frameNodes : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → List NodeId
frameNodes (map-f _)          = []
frameNodes (scan-f _ k)       = k ∷ []
frameNodes (take-f k)         = k ∷ []
frameNodes (from-inner _ k j) = k ∷ j ∷ []
frameNodes (thru-outer _ k)   = k ∷ []

pathHasNode : ∀ {n} {Γ : Ctx n} {s t} → NodeId → Path Γ s t → Bool
pathHasNode nid root           = false
pathHasNode nid (share-sink i) = false
pathHasNode nid (f ↠ p)       = any (_≡ᵇ nid) (frameNodes f) ∨ pathHasNode nid p

-- remove every registration whose chain passes through the given
-- node, emitting one close per removed registration
-- registrations carry an identity so a mid-cascade cut can name its
-- victims: a cancelled registration's snapshot chain must deliver
-- NOTHING (as in rxjs — an unsubscribed chain is silent), and its
-- close must say whether it had already paid this instant (cut) or
-- never will (cutPending, cancelling one owed count downstream)
RegId : Set
RegId = ℕ

-- the close reason is writer-asserted per victim: delivered this
-- cascade, or born since the cascade started (owing nothing) ⇒ cut;
-- a pre-existing registration cut before its delivery ⇒ cutPending.
-- A victim of a DYING source that already delivered carried its own
-- exhausted close on its own emit — no second close for it.  Also
-- returns the victims' ids for the cascade's cancelled set.
cutThrough : ∀ {n} {Γ : Ctx n} {t}
           → NodeId → List RegId → RegId → List Source
           → List (RegId × Source × Chain Γ t)
           → List (RegId × Source × Chain Γ t)
             × List (InstEvent (Val Γ t)) × List RegId
cutThrough nid delivered wm dying [] = [] , [] , []
cutThrough nid delivered wm dying ((rid , src , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid delivered wm dying r
... | true  | kept , closes , rids =
      kept
      , (if any (_≡ᵇ rid) delivered ∧ memberSource src dying
         then closes
         else close src (if any (_≡ᵇ rid) delivered ∨ (wm ≤ᵇ rid)
                         then cut else cutPending) ∷ closes)
      , rid ∷ rids
... | false | kept , closes , rids = (rid , src , c) ∷ kept , closes , rids

-- drop dead dynamic sources (no remaining registrations); hot input
-- slots (sources < n by convention) keep firing regardless, exactly
-- like a hot Subject with no subscribers
sweepLive : ∀ {n} {Γ : Ctx n} {t}
          → List (RegId × Source × Chain Γ t) → List (LiveSource Γ) → List (LiveSource Γ)
sweepLive {n = n} reg []       = []
sweepLive {n = n} reg (l ∷ ls) =
  if (LiveSource.source l <ᵇ n)
     ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ (proj₂ p))) reg
  then l ∷ sweepLive reg ls
  else sweepLive reg ls

dropSource : ∀ {n} {Γ : Ctx n} {t}
           → Source → List (RegId × Source × Chain Γ t) → List (RegId × Source × Chain Γ t)
dropSource src []                  = []
dropSource src ((rid , s , c) ∷ r) =
  if sameSource src s then dropSource src r else (rid , s , c) ∷ dropSource src r

record EvalSt {n} {Γ : Ctx n} {t} (e : Closed Γ t) : Set where
  field registry        : List (RegId × Source × Chain Γ t)   -- live registration chains, subscription order
        nextReg         : RegId         -- registration ids, minted by register
        nodes           : NodeSt e
        connectedShares : List Source   -- shared slots whose def is live (connect happens once, ever)
        completedSources : List Source  -- the completion latch: completed shares AND spent
                                        -- scripted sources (a completed Subject re-delivers
                                        -- complete to late subscribers; values are not
                                        -- re-observable, completion is)
        -- per-cascade bookkeeping (reset by cascade, shared with any
        -- dispatchShare it triggers):
        delivered       : List RegId    -- snapshot chains that have folded this cascade
        cancelled       : List RegId    -- victims cut mid-cascade: their snapshot
                                        -- chains are skipped outright (an unsubscribed
                                        -- rxjs chain delivers nothing)
        regWatermark    : RegId         -- nextReg at cascade start: registrations at or
                                        -- above it were born this cascade and owe nothing
        dying           : List Source   -- sources spending their final delivery this
                                        -- cascade (the isLast arrival, a completing
                                        -- share): their delivered registrations already
                                        -- carried their own exhausted closes, and the
                                        -- whole source's registry entries drop at finish

mintSource : ∀ {n} {Γ : Ctx n} → Sched Γ → Source × Sched Γ
mintSource sched =
  Sched.nextSource sched , record sched { nextSource = suc (Sched.nextSource sched) }

mintOrdinal : ∀ {n} {Γ : Ctx n} → Sched Γ → Ordinal × Sched Γ
mintOrdinal sched =
  Sched.nextOrdinal sched , record sched { nextOrdinal = suc (Sched.nextOrdinal sched) }

mintNode : ∀ {n} {Γ : Ctx n} → Sched Γ → NodeId × Sched Γ
mintNode sched =
  Sched.nextNode sched , record sched { nextNode = suc (Sched.nextNode sched) }

-- append: the registry stays in subscription order; the id is minted here
register : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Source → Path Γ u t → EvalSt e → EvalSt e
register {u = u} src path st =
  record st { registry = EvalSt.registry st
                           ++ (EvalSt.nextReg st , src , u , path) ∷ []
            ; nextReg  = suc (EvalSt.nextReg st) }

installNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → NodeId → NodeState Γ → EvalSt e → EvalSt e
installNode nid nodeState st =
  record st { nodes = setNode nid nodeState (EvalSt.nodes st) }

-- a source that lives and dies inside its own subscription burst
-- (ofᵉ, emptyᵉ, take 0, a cold with no async tail): init, values,
-- close, complete — one emit, nothing registered, nothing scheduled
oneShotBurst : ∀ {n} {Γ : Ctx n} {u}
             → List (Val Γ u) → Id → Sched Γ → Stream Γ u × Sched Γ
oneShotBurst vals id sched =
  let (src , sched₁) = mintSource sched
  in ((init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
       at id from src as subscribe) ∷ [] , sched₁

-- THE STUCK MARKER.  The subscription machine recurses on an
-- accessibility witness for `Rx.Strat-Order`'s lexicographic triple,
-- dropping one component at each of its three non-structural edges — a
-- share connect, an inner-value subscription, a μ unfold — while every
-- other recursion stays structural, so termination needs no pragma.
-- Two of the three drops are facts about measures the run cannot move
-- the wrong way; the third is a rank a run may exhaust, and exhausting
-- it is what this marker reports.  A dry run does NOT truncate silently: it emits a close
-- with reason `dried` — a CloseReason no machine rule ever emits —
-- so hasDry recognizes it EXACTLY, QuickCheck's WF check flags it at
-- runtime (the close's source is never inited, which the strict
-- protocol rejects on sight), and evaluate-well-formed itself demands
-- budget sufficiency (the old pragma's termination debt, reified as a
-- provable statement).  The marker is the REASON, not the source:
-- Source is an unbounded ℕ and mints are breadth-many (fuel is only
-- depth-consumed), so a burst can legally mint past any numeric
-- sentinel — a sentinel-source check would misfire on a wet run.
-- drySource survives only as the envelope's cosmetic source id.
drySource : Source
drySource = 18446744073709551615

dryBurst : ∀ {A : Set} → Id → List (InstEmit A)
dryBurst id =
  ((close drySource dried ∷ []) at id from drySource as subscribe) ∷ []

-- did the run go dry anywhere?  Verify-Well-Formed's step lemmas are
-- conditioned on `hasDry … ≡ false`, and `rank-sufficient` asserts it
-- for the seeded descent — the totality debt as a provable statement
dryEvent : ∀ {A : Set} → InstEvent A → Bool
dryEvent (close _ dried) = true
dryEvent _               = false

hasDry : ∀ {A : Set} → List (InstEmit A) → Bool
hasDry []         = false
hasDry (em ∷ ems) = any dryEvent (InstEmit.events em) ∨ hasDry ems

-- THE DESCENT DISCIPLINE, read off the clauses below.  Each of the
-- three edges that reaches a deeper subscribe drops its OWN component
-- of the triple and leaves the other two free to be re-seeded, which is
-- what a lexicographic order buys and what a single counter could not:
-- packing the three into one number is exactly what made a budget owe a
-- ceiling on the two components it was not descending on.
--
--   · `sharedConnect → subscribeE` drops the unconnected-share count;
--   · `subscribeInner → subscribeE` drops the hop rank;
--   · `subscribeE (μᵉ body) → subscribeE (unfoldμ body)` drops syncSize.
--
-- EVERY other route through the pipeline carries the witness unchanged
-- because it stays at ONE nesting level — `subscribeE` walking its own
-- operator chain (map / take / scan / the three *All), the `pushBurst →
-- stepFrame → thruWalk → thruConsume` re-entry of a burst,
-- `mergeAllDrain` off `innerFinish`, and `foldPath → dispatchShare →
-- shareGo → stepFrame`, which threads the witness unchanged through a
-- delivery.  So no path reaches `subscribeInner` at the witness it was
-- called with: the three `thruConsume` sites and the one
-- `mergeAllDrain` site are reached from a `stepFrame` running at the
-- caller's witness, and the drop happens INSIDE `subscribeInner` before
-- control reaches `subscribeE`.  `deferᵉ` is not a nesting edge at all
-- — it parks the body for `suc now`, a later instant seeded afresh.

-- AND THAT READING IS CHECKED RATHER THAN READ OFF.  `make
-- recursion-cover` cuts the edges declared below and requires every
-- cycle still standing to be declared too: cutting three edges
-- collapses BOTH of this module's multi-member recursions and exactly
-- one cycle survives, the pair that walks the expression.  A clause
-- opening a fourth edge fails that check rather than going on
-- compiling, which is the one thing Agda's own termination checker
-- cannot say — it is satisfied by the witness and silent about which
-- edges carry it.

-- THE SHARE HOP IS ITS OWN RECURSION AND DOES NOT JOIN THE TRIPLE.  Its
-- counter is a plain `ℕ` bounding the slot telescope, it peels once per
-- hop, and it reaches the frame walk one way only — nothing in the
-- subscribe recursion calls back into it.  It composes by being a
-- separate component, not by sharing a measure.

-- PEEL: subscribeInner -> subscribeE
-- PEEL: sharedConnect -> subscribeE
-- PEEL: dispatchShare -> shareGo
-- STRUCTURAL SCC: subscribeE subscribeAll

-- THE ONE DECLARATION TAKEN ON TRUST IS THAT LAST PAIR, and it is the
-- μ edge that makes it worth naming.  `subscribeE` reaches
-- `subscribeAll` and back on a strictly smaller expression at every
-- operator node, so the pair is structural — except at `μᵉ`, where the
-- body is UNFOLDED rather than descended into and the third drop lives.
-- A self-edge is invisible to a component check, so this is where the
-- check stops and syncSize starts.

-- the subscription machine: walk the target expression, minting
-- NodeIds for its operator nodes and installing their states (evalTm
-- for takeᵉ counts, scanᵉ seeds); register every internal source's
-- chains, each local path extended with the given rootward
-- continuation; anchor colds (resolve at the given tick) and deferᵉ
-- bodies (suc tick) on the schedule; and fire the sync burst NOW,
-- inside cascade `Id` (id-inheritance), emitting init per new
-- registration.  Declared here, defined after stepFrame — the two are
-- mutually recursive: the burst re-enters the pipeline one frame at a
-- time (pushBurst → stepFrame), and the *All frames subscribe inners
-- (stepFrame → subscribeInner → subscribeE)
subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
           → Acc _≺_ τ → Closed Γ u → Path Γ u t → Id → Tick
           → Sched Γ → EvalSt e
           → Stream Γ u × Sched Γ × EvalSt e

st-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → EvalSt e
st-init e = record { registry = [] ; nextReg = 0 ; nodes = []
                   ; connectedShares = [] ; completedSources = []
                   ; delivered = [] ; cancelled = [] ; regWatermark = 0
                   ; dying = [] }
  -- all populated by the root subscribeE and by lazy share connects

-- the arrival's source's live chains, in subscription order, at
-- exactly the arrival's element type: a chain is admitted only past a
-- Ty equality check, so no payload is ever read at the wrong type (a
-- mistyped registry entry — impossible by the registration invariant —
-- is dropped, never trusted)
-- TOP-LEVEL (not where-local of chainsOf) so Verify-Well-Formed can induct
-- on it against the registry — the snapshot of a's source-typed chains
chainsGo : ∀ {n} {Γ : Ctx n} {t} → (a : Arrival Γ)
         → List (RegId × Source × Chain Γ t) → List (RegId × Path Γ (arrTy a) t)
chainsGo a [] = []
chainsGo a ((rid , s , (u , p)) ∷ r) with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo a r
... | true  | no  _    = chainsGo a r
... | true  | yes refl = (rid , p) ∷ chainsGo a r

chainsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → (a : Arrival Γ) → EvalSt e → List (RegId × Path Γ (arrTy a) t)
chainsOf a st = chainsGo a (EvalSt.registry st)

-- split a subscription burst into grafted values, retagged
-- bookkeeping events, and whether the inner completed synchronously
splitEvents : ∀ {n} {Γ : Ctx n} {u} {A : Set}
            → List (InstEvent (Val Γ u))
            → List (Val Γ u) × List (InstEvent A) × Bool
splitEvents []              = [] , [] , false
splitEvents (value v  ∷ es) = let (vs , bs , c) = splitEvents es in v ∷ vs , bs , c
splitEvents (init s   ∷ es) = let (vs , bs , c) = splitEvents es in vs , init s ∷ bs , c
splitEvents (close s r ∷ es) = let (vs , bs , c) = splitEvents es in vs , close s r ∷ bs , c
splitEvents (handoff s ∷ es) = let (vs , bs , c) = splitEvents es in vs , handoff s ∷ bs , c
splitEvents (complete ∷ es) = let (vs , bs , _) = splitEvents es in vs , bs , true

splitBurst : ∀ {n} {Γ : Ctx n} {u} {A : Set}
           → Stream Γ u → List (Val Γ u) × List (InstEvent A) × Bool
splitBurst []         = [] , [] , false
splitBurst (em ∷ ems) =
  let (vs  , bs  , c ) = splitEvents (InstEmit.events em)
      (vs′ , bs′ , c′) = splitBurst ems
  in vs ++ vs′ , bs ++ bs′ , c ∨ c′

hasComplete : ∀ {A : Set} → List (InstEvent A) → Bool
hasComplete []             = false
hasComplete (complete ∷ _) = true
hasComplete (_ ∷ es)       = hasComplete es

burstCompleted : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → Bool
burstCompleted = any (λ em → hasComplete (InstEmit.events em))

-- mint the inner's exit-frame instance, subscribe it inside the
-- current instant, split its burst.  THE HOP EDGE: the inner is a
-- runtime VALUE, structurally unrelated to the caller, so the rank is
-- what descends here — and it is the one component of the triple a run
-- can exhaust, since nothing the syntax says bounds the nesting of what
-- a program emits.  The zero clause is where that shows.
subscribeInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
               → Acc _≺_ τ → AllOp → NodeId → Path Γ u t → Id → Tick
               → Val Γ (obs u) → Sched Γ → EvalSt e
               → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
subscribeInner {τ = _ , zero , _} _ op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
  in inst , [] , close drySource dried ∷ [] , false
     , record sched { nextNode = suc inst } , st
subscribeInner {τ = _ , suc r , _} (acc rec) op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE (rec (ltR {r′ = r} {s′ = syncSizeᵉ o} ≤-refl))
                   o (from-inner op allNid inst ↠ κ) id now
                   (record sched { nextNode = suc inst }) st
      (vs , bs , done) = splitBurst burst
  in inst , vs , bs , done , sched′ , st′

-- the per-frame semantics.  All recursion here is structural — the
-- deep recursion (a subscription's sync burst re-entering the
-- pipeline) lives in subscribeE.  The threaded Bool is v1's fin:
-- "this stream completes as part of THIS emit" — raised by a spent
-- source or a takeᵉ cut, absorbed and reacted to by the *All frames
-- (concatAll advances by grafting the next queued inner's flush into
-- the fin-carrying emit), turned into a `complete` event only at the
-- root.  Missing or mistyped node state (impossible by the
-- subscription invariant) degrades to forwarding nothing, never to a
-- wrong read.
-- take's emission split: pass through up to the remaining budget, reporting
-- the new remaining count and whether this burst hit the limit (didCut).
-- Top-level (not stepFrame-local) so the well-formedness proof can case-split
-- its cut flag to separate the quiet non-cut path from the cutting one.
takeVals : ∀ {n} {Γ : Ctx n} {s} → ℕ → List (Val Γ s) → List (Val Γ s) × ℕ × Bool
takeVals zero          _        = [] , zero , false
takeVals (suc k)       []       = [] , suc k , false
takeVals (suc zero)    (v ∷ _)  = v ∷ [] , zero , true
takeVals (suc (suc k)) (v ∷ vs) =
  let (out , rem , didCut) = takeVals (suc k) vs in v ∷ out , rem , didCut

-- a from-inner completion is absorbed iff some registration under this inner
-- instance is still live: its path threads `inst`, it is not cancelled, and it
-- is not an already-delivered dying-source chain.  Top-level (not from-inner-
-- local) so the well-formedness proof can case-split the absorb vs. finish paths.
aliveThroughᶠ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → NodeId → EvalSt e → (RegId × Source × Chain Γ t) → Bool
aliveThroughᶠ inst st (rid , src , (w , p)) =
  pathHasNode inst p
  ∧ not (any (_≡ᵇ rid) (EvalSt.cancelled st))
  ∧ (not (memberSource src (EvalSt.dying st))
     ∨ not (any (_≡ᵇ rid) (EvalSt.delivered st)))

-- scan's per-emit fold: one running output per input, threading the accumulator.
-- Top-level (not stepFrame-local) so the well-formedness proof can name the value
-- transform it feeds to the protocol-transparency fold.
scanVals : ∀ {n} {Γ : Ctx n} {s u} → Fn Γ [] [] [] (u ×ᵗ s) u
         → Val Γ u → List (Val Γ s) → List (Val Γ u) × Val Γ u
scanVals fn ac []       = [] , ac
scanVals fn ac (v ∷ vs) =
  let ac′           = applyFn fn (ac , v)
      (outs , last) = scanVals fn ac′ vs
  in ac′ ∷ outs , last

-- take's per-emit step, lifted out of stepFrame so the well-formedness proof
-- can reason about its reduction over a stuck node lookup.  Non-cut passes the
-- budgeted prefix through untouched (threading the remaining count); the cut
-- exhausts the budget, forces `complete`, and severs the registry (cutThrough).
takeDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             → NodeId → List (Val Γ s) → Bool → Sched Γ → EvalSt e → Maybe (NodeState Γ)
             → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
takeDispatch nid vals fin sched st (just (take-st k)) =
  if proj₂ (proj₂ (takeVals k vals))
  then (let (kept , closes , cutRids) =
              cutThrough nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                         (EvalSt.dying st) (EvalSt.registry st)
        in proj₁ (takeVals k vals) , closes , true ,
           record sched { live = sweepLive kept (Sched.live sched) } ,
           record st { registry = kept
                     ; cancelled = cutRids ++ EvalSt.cancelled st
                     ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) })
  else (proj₁ (takeVals k vals) , [] , fin , sched ,
        record st { nodes = setNode nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                                      (EvalSt.nodes st) })
takeDispatch nid vals fin sched st _ = [] , [] , fin , sched , st

-- the outer *All frame's machinery, lifted out of stepFrame so the
-- budget proof can reason about its reduction.  One walk for all four
-- ops (they differ only in the per-emit step and the wrap's node read)
-- is there a free lane?  `nothing` is rxjs's Infinity, so always
hasRoom : Maybe ℕ → ℕ → Bool
hasRoom nothing  active = true
hasRoom (just m) active = active <ᵇ m

-- bump the live count on whatever state the node holds NOW.  Re-reading
-- the table rather than writing back a count captured before the
-- subscription is not fastidiousness: the inner's own synchronous burst
-- can route back through THIS node and finish there, and a captured
-- count silently discards that drain — the freed lane is refilled and
-- then un-freed by a stale write
mergeAllBump : ∀ {n} {Γ : Ctx n} → NodeId → Bool
            → List (NodeId × NodeState Γ) → List (NodeId × NodeState Γ)
mergeAllBump nid done ns with lookupNode nid ns
... | just (mergeAll-st lim act q od) =
      setNode nid (mergeAll-st lim (if done then act else suc act) q od) ns
... | _ = ns

-- switchAll's cut: the outgoing inner's registrations are severed
switchKill : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → Maybe NodeId → Sched Γ → EvalSt e
           → List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
switchKill nothing  sched₀ st₀ = [] , sched₀ , st₀
switchKill (just v) sched₀ st₀ =
  let (kept , closes , cutRids) =
        cutThrough v (EvalSt.delivered st₀) (EvalSt.regWatermark st₀)
                   (EvalSt.dying st₀) (EvalSt.registry st₀)
  in closes ,
     record sched₀ { live = sweepLive kept (Sched.live sched₀) } ,
     record st₀ { registry = kept
                ; cancelled = cutRids ++ EvalSt.cancelled st₀ }

thruConsume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
            → Acc _≺_ τ → AllOp → NodeId → Path Γ u t → Id → Tick
            → Val Γ (obs u) → Sched Γ → EvalSt e
            → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruConsume {u = u} fuel mergeAllᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = [] , [] , sched₀ , st₀
...   | yes refl with hasRoom lim act
...     | true =
          let (_ , vs , bs , done , sched₁ , st₁) =
                subscribeInner fuel mergeAllᵒ nid κ id now o sched₀ st₀
          in vs , bs , sched₁ ,
             record st₁ { nodes = mergeAllBump nid done (EvalSt.nodes st₁) }
...     | false =
          [] , [] , sched₀ ,
          record st₀ { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                                 (EvalSt.nodes st₀) }
thruConsume fuel mergeAllᵒ nid κ id now o sched₀ st₀ | _ = [] , [] , sched₀ , st₀
thruConsume fuel switchᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (switch-st cur od) =
      let (closes , sched₁ , st₁) = switchKill cur sched₀ st₀
          (inst , vs , bs , done , sched₂ , st₂) =
            subscribeInner fuel switchᵒ nid κ id now o sched₁ st₁
      in vs , closes ++ bs , sched₂ ,
         record st₂ { nodes = setNode nid
           (switch-st (if done then nothing else just inst) od) (EvalSt.nodes st₂) }
... | _ = [] , [] , sched₀ , st₀
thruConsume fuel exhaustᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (exhaust-st true od)  = [] , [] , sched₀ , st₀   -- busy: drop
... | just (exhaust-st false od) =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner fuel exhaustᵒ nid κ id now o sched₀ st₀
      in vs , bs , sched₁ ,
         record st₁ { nodes = setNode nid (exhaust-st (not done) od) (EvalSt.nodes st₁) }
... | _ = [] , [] , sched₀ , st₀

thruWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Acc _≺_ τ → AllOp → NodeId → Path Γ u t → Id → Tick
         → List (Val Γ (obs u)) → Sched Γ → EvalSt e
         → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruWalk fuel op nid κ id now []       sched₀ st₀ = [] , [] , sched₀ , st₀
thruWalk fuel op nid κ id now (o ∷ os) sched₀ st₀ =
  let (vs  , bs  , sched₁ , st₁) = thruConsume fuel op nid κ id now o sched₀ st₀
      (vs′ , bs′ , sched₂ , st₂) = thruWalk fuel op nid κ id now os sched₁ st₁
  in vs ++ vs′ , bs ++ bs′ , sched₂ , st₂

thruWrap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → AllOp → NodeId → Bool
         → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
         → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
thruWrap op nid false (vs , bs , sched′ , st′) = vs , bs , false , sched′ , st′
thruWrap mergeAllᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st lim act q _) =
      vs , bs , (act ≡ᵇ 0) ∧ null q , sched′ ,
      record st′ { nodes = setNode nid (mergeAll-st lim act q true) (EvalSt.nodes st′) }
... | _ = vs , bs , true , sched′ , st′
thruWrap switchᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur _) =
      vs , bs , is-nothing cur , sched′ ,
      record st′ { nodes = setNode nid (switch-st cur true) (EvalSt.nodes st′) }
... | _ = vs , bs , true , sched′ , st′
thruWrap exhaustᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act _) =
      vs , bs , not act , sched′ ,
      record st′ { nodes = setNode nid (exhaust-st act true) (EvalSt.nodes st′) }
... | _ = vs , bs , true , sched′ , st′

-- the inner *All frame's machinery, lifted out of stepFrame so the
-- budget proof can reason about its reduction.  The drain walks the
-- parked queue, subscribing while a lane is free and stopping the
-- instant one is not.  This is the ONE behaviour bounded concurrency
-- adds that neither face it replaces had: unbounded merge never
-- queues, so it never drains, and concat's drain could stop only at
-- the first inner that stayed open because its capacity was one.  The
-- accumulator is the live count and NOT a flag, so the walk keeps
-- filling lanes across several parked inners in one instant, which is
-- precisely what `mergeMap(f , k)` does when several finish together

-- The count is THREADED and not re-read from the node table between
-- iterations, so a drained inner whose own synchronous burst routes
-- back through THIS node and finishes there is not seen by the rest of
-- the walk.  The face this replaced threaded a flag with the same
-- blind spot, so nothing regresses — but the loss is now quantitative
-- rather than one bit, which is what makes it worth naming: at limit 1
-- a missed self-finish costs the drain its only lane, at limit k it
-- can cost several, and the two do not fail the same way
mergeAllDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             → Acc _≺_ τ → NodeId → Path Γ s t → Id → Tick
             → Maybe ℕ → ℕ → List (Closed Γ s) → Sched Γ → EvalSt e
             → List (Val Γ s) × List (InstEvent (Val Γ t)) × ℕ
               × List (Closed Γ s) × Sched Γ × EvalSt e
mergeAllDrain fuel allNid κ id now lim act []      sched₀ st₀ =
  [] , [] , act , [] , sched₀ , st₀
mergeAllDrain fuel allNid κ id now lim act (o ∷ q) sched₀ st₀
  with hasRoom lim act
... | false = [] , [] , act , o ∷ q , sched₀ , st₀
... | true =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner fuel mergeAllᵒ allNid κ id now o sched₀ st₀
          (vs′ , bs′ , act′ , q′ , sched₂ , st₂) =
            mergeAllDrain fuel allNid κ id now lim
              (if done then act else suc act) q sched₁ st₁
      in vs ++ vs′ , bs ++ bs′ , act′ , q′ , sched₂ , st₂

innerFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            → Acc _≺_ τ → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
            → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
            → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerFinish {s = s} fuel mergeAllᵒ allNid inst κ id now vals sched st
            (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | yes refl =
      let (vs , bs , act′ , q′ , sched′ , st′) =
            mergeAllDrain fuel allNid κ id now lim (pred act) q sched st
      in vals ++ vs , bs , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched′ ,
         record st′ { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′) }
... | no _ = vals , [] , false , sched , st
innerFinish fuel switchᵒ allNid inst κ id now vals sched st (just (switch-st (just c) od)) =
  if c ≡ᵇ inst
  then (vals , [] , od , sched ,
        record st { nodes = setNode allNid (switch-st nothing od) (EvalSt.nodes st) })
  else (vals , [] , false , sched , st)
innerFinish fuel exhaustᵒ allNid inst κ id now vals sched st (just (exhaust-st act od)) =
  vals , [] , od , sched ,
  record st { nodes = setNode allNid (exhaust-st false od) (EvalSt.nodes st) }
innerFinish fuel _ allNid inst κ id now vals sched st _ = vals , [] , false , sched , st

-- a fin only completes THIS INNER once nothing under its exit frame
-- can ever deliver again: a sibling registration of the dying source
-- still queued this cascade, or any other live registration, absorbs
-- it (the TS join's open-multiset, read off the registry) — one
-- chain's exhaustion is not a multi-registration subtree's completion
innerReact : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           → Acc _≺_ τ → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
           → List (Val Γ s) → Sched Γ → EvalSt e → Bool
           → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerReact fuel op allNid inst κ id now vals sched st false =
  vals , [] , false , sched , st
innerReact fuel op allNid inst κ id now vals sched st true =
  if any (aliveThroughᶠ inst st) (EvalSt.registry st)
  then vals , [] , false , sched , st
  else innerFinish fuel op allNid inst κ id now vals sched st
         (lookupNode allNid (EvalSt.nodes st))

stepFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t
          → List (Val Γ s) → Bool → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e

stepFrame fuel id now (map-f fn) κ vals fin sched st =
  map (applyFn fn) vals , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} {u = u} fuel id now (scan-f fn nid) κ vals fin sched st
  = dispatch (lookupNode nid (EvalSt.nodes st))
  where
  dispatch : Maybe (NodeState Γ)
           → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  dispatch (just (scan-st {w} ac)) with w ≟ᵗ u
  ... | yes refl =
        let (outs , ac′) = scanVals fn ac vals
        in outs , [] , fin , sched ,
           record st { nodes = setNode nid (scan-st ac′) (EvalSt.nodes st) }
  ... | no _ = [] , [] , fin , sched , st
  dispatch _ = [] , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} fuel id now (take-f nid) κ vals fin sched st
  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

stepFrame fuel id now (from-inner op allNid inst) κ vals fin sched st
  = innerReact fuel op allNid inst κ id now vals sched st fin

stepFrame fuel id now (thru-outer op nid) κ vals fin sched st
  = thruWrap op nid fin (thruWalk fuel op nid κ id now vals sched st)

-- bookkeeping crosses payload types freely — init/close/complete
-- carry none.  A value cannot cross and is dropped; the callers only
-- ever retag event lists that stepFrame produced, which are value-free
retagEvents : ∀ {A B : Set} → List (InstEvent A) → List (InstEvent B)
retagEvents []              = []
retagEvents (init s    ∷ es) = init s    ∷ retagEvents es
retagEvents (close s r ∷ es) = close s r ∷ retagEvents es
retagEvents (handoff s ∷ es) = handoff s ∷ retagEvents es
retagEvents (complete  ∷ es) = complete  ∷ retagEvents es
retagEvents (value _   ∷ es) = retagEvents es

-- push a child subscription's sync burst through the one frame just
-- built above it: split each emit, step it, reassemble under the same
-- envelope — the burst leaves each subscription level already shaped
-- like any later emit of its source
pushBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Acc _≺_ τ → Id → Tick → Frame Γ s u → Path Γ u t
          → Stream Γ s → Sched Γ → EvalSt e
          → Stream Γ u × Sched Γ × EvalSt e
pushBurst fuel id now f κ []         sched st = [] , sched , st
pushBurst fuel id now f κ (em ∷ ems) sched st =
  let sp   = splitEvents (InstEmit.events em)
      (vals′ , evs , fin′ , sched₁ , st₁) =
        stepFrame fuel id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
      (rest , sched₂ , st₂) = pushBurst fuel id now f κ ems sched₁ st₁
  in ((proj₁ (proj₂ sp) ++ retagEvents evs ++ map value vals′
        ++ (if fin′ then complete ∷ [] else []))
       at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
       ∷ rest , sched₂ , st₂

-- the shared *All shape: mint the node, install its initial state,
-- subscribe the outer under a thru-outer frame, push the burst through
subscribeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → Acc _≺_ τ → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ u t
             → Id → Tick → Sched Γ → EvalSt e
             → Stream Γ u × Sched Γ × EvalSt e
subscribeAll fuel op initialState b κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE fuel b (thru-outer op nid ↠ κ) id now sched₁
                   (installNode nid initialState st)
  in pushBurst fuel id now (thru-outer op nid) κ burst sched₂ st₁

-- a shared slot: identity IS the index, source toℕ i (a hot's
-- convention).  All reset options are false by definition: connect at
-- the first subscription (anchoring the def's colds at that tick),
-- never disconnect (an unobserved share still burns arrivals), and
-- latch completion forever — a post-completion subscriber sees only
-- an immediate close/complete, because completion is re-observable
-- and values are not
-- the connect burst is retagged plumbing: it flows up the first
-- subscriber's frames as real protocol traffic, but its
-- registrations belong to the share (registered at share-sink,
-- surviving the subscriber) — a downstream cut or join must not
-- adopt them
sharedPlumb : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → Stream Γ u
sharedPlumb = map (λ em → record em { kind = plumbing })

-- the connect is a fuel decrement edge: the def d is a stored
-- expression, structurally unrelated to the `input i` being
-- subscribed.  Fuel is matched here, not at subscribeSharedSlot's
-- branches: joining an already-connected share costs nothing.
-- Lifted out of subscribeSharedSlot's where block so the budget
-- proof can name it (as with takeVals / thruConsume / mergeAllDrain)
sharedConnect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Acc _≺_ τ → (i : Fin n) → Closed Γ (lookup Γ i)
              → Path Γ (lookup Γ i) t → Id → Tick
              → Sched Γ → EvalSt e
              → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
sharedConnect {τ = U , _ , _} (acc rec) i d κ id now sched st
  with unconn (Sched.slots sched) (toℕ i ∷ EvalSt.connectedShares st) <? U
... | no  _ = dryBurst id , sched , st
... | yes p =
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      (burst , sched₁ , st₂) =
        subscribeE (rec (ltU {r′ = 2 ^ sizeᵉ d} {s′ = syncSizeᵉ d} p))
                   d (share-sink i) id now sched st₁
      -- the def's connect burst flows up the first subscriber's own
      -- frames (the returned burst); dispatch only serves arrivals
  in if burstCompleted burst
     then -- the def died inside its own connect burst: latch, and
          -- this registration closes in the same instant
          (((init (toℕ i) ∷ close (toℕ i) exhausted ∷ [])
             at id from toℕ i as subscribe) ∷ sharedPlumb burst)
          , sched₁ ,
          record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                     ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
     else ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ sharedPlumb burst
          , sched₁ , st₂

subscribeSharedSlot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    → Acc _≺_ τ → (i : Fin n) → Closed Γ (lookup Γ i)
                    → Path Γ (lookup Γ i) t → Id → Tick
                    → Sched Γ → EvalSt e
                    → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
subscribeSharedSlot {Γ = Γ} {e = e} fuel i d κ id now sched st =
  if memberSource (toℕ i) (EvalSt.completedSources st)
  then ((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
         at id from toℕ i as subscribe) ∷ []
       , sched , st
  else if memberSource (toℕ i) (EvalSt.connectedShares st)
  then -- live: join mid-flight, future values only
       ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
       , sched , register (toℕ i) κ st
  else sharedConnect fuel i d κ id now sched st

subscribeE {Γ = Γ} fuel (input i) κ id now sched st with Sched.slots sched i
... | shared d = subscribeSharedSlot fuel i d κ id now sched st
... | scripted (hot _) =
      if memberSource (toℕ i) (EvalSt.completedSources st)
      then -- spent script: a completed Subject — immediate
           -- close/complete, nothing registered
           ((init (toℕ i) ∷ close (toℕ i) exhausted ∷ complete ∷ [])
             at id from toℕ i as subscribe) ∷ []
           , sched , st
      else -- already live (sched-init, source = ordinal = toℕ i); just
           -- another registration — fan-out IS this multiplicity
           ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
           , sched , register (toℕ i) κ st
... | scripted (cold sync []) =
      let (burst , sched₁) = oneShotBurst sync id sched
      in burst , sched₁ , st
... | scripted (cold sync (d ∷ ds)) =
      -- per-subscription anchoring: a fresh source per subscribe, the
      -- async tail resolved against the subscription tick
      let (src , sched₁) = mintSource sched
          (ord , sched₂) = mintOrdinal sched₁
          sched₃ = record sched₂
            { live = record { source = src ; ordinal = ord
                            ; elemTy = lookup Γ i
                            ; pending = resolve now (d ∷ ds) }
                     ∷ Sched.live sched₂ }
      in ((init src ∷ map value sync) at id from src as subscribe) ∷ []
         , sched₃ , register src κ st

subscribeE fuel (ofᵉ ts) κ id now sched st =
  let (burst , sched₁) = oneShotBurst (map (λ tm → evalTm tm) ts) id sched
  in burst , sched₁ , st

subscribeE fuel emptyᵉ κ id now sched st =
  let (burst , sched₁) = oneShotBurst [] id sched
  in burst , sched₁ , st

subscribeE fuel (mapᵉ f b) κ id now sched st =
  let (burst , sched₁ , st₁) = subscribeE fuel b (map-f f ↠ κ) id now sched st
  in pushBurst fuel id now (map-f f) κ burst sched₁ st₁

subscribeE fuel (takeᵉ count b) κ id now sched st with evalTm count
... | zero =
      -- take 0 never subscribes its source (as in rxjs): a spent
      -- one-shot, exactly emptyᵉ
      let (burst , sched₁) = oneShotBurst [] id sched
      in burst , sched₁ , st
... | suc k =
      let (nid , sched₁) = mintNode sched
          (burst , sched₂ , st₁) =
            subscribeE fuel b (take-f nid ↠ κ) id now sched₁
                       (installNode nid (take-st (suc k)) st)
      in pushBurst fuel id now (take-f nid) κ burst sched₂ st₁

subscribeE fuel (scanᵉ f seed b) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE fuel b (scan-f f nid ↠ κ) id now sched₁
                   (installNode nid (scan-st (evalTm seed)) st)
  in pushBurst fuel id now (scan-f f nid) κ burst sched₂ st₁

subscribeE {u = u} fuel (mergeAllᵉ lim b) κ id now sched st =
  subscribeAll fuel mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b κ id now sched st
subscribeE fuel (switchAllᵉ b) κ id now sched st =
  subscribeAll fuel switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE fuel (exhaustAllᵉ b) κ id now sched st =
  subscribeAll fuel exhaustᵒ (exhaust-st false false) b κ id now sched st

-- one unfold per subscription; the recursive occurrences inside the
-- unfolding are deferᵉ-gated, so each re-entry costs a schedule hop —
-- no synchronous loop.  A fuel decrement edge: the unfolding is
-- larger than the μ, not a subterm
subscribeE {τ = _ , _ , sz} (acc rec) (μᵉ body) κ id now sched st
  with syncSizeᵉ (unfoldμ body) <? sz
... | no  _ = dryBurst id , sched , st
... | yes p = subscribeE (rec (ltS p)) (unfoldμ body) κ id now sched st

subscribeE fuel (varᵉ ()) κ id now sched st

-- deferᵉ is mergeAll of a one-shot scheduled outer: the body itself is
-- the pending payload (Val Γ (obs u) IS Closed Γ u), delivered at
-- suc now with isLast — the arrival's thru-outer frame subscribes it
-- under that arrival's fresh instant, wrap marks the outer done, and
-- the node completes when the body does.  Cancellation is free:
-- cutting the registration lets sweepLive collect the pending hop
subscribeE {u = u} fuel (deferᵉ body) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (src , sched₂) = mintSource sched₁
      (ord , sched₃) = mintOrdinal sched₂
      sched₄ = record sched₃
        { live = record { source = src ; ordinal = ord
                        ; elemTy = obs u
                        ; pending = (suc now , body) ∷ [] }
                 ∷ Sched.live sched₃ }
  in ((init src ∷ []) at id from src as subscribe) ∷ [] , sched₄ ,
     register src (thru-outer mergeAllᵒ nid ↠ κ)
              (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st)

-- delivery at a share boundary re-enters chain evaluation: foldPath
-- and dispatchShare are mutually recursive.  The recursion is bounded
-- by the share telescope — a chain registered on share i sinks only
-- into the root or a strictly later share — so dispatch depth never
-- exceeds n.  `gas` makes that bound structural: every dispatch
-- consumes one unit and chainStep seeds n, so the zero clamp is
-- unreachable on real registries (the telescope invariant, Inv-phase
-- work) and termination needs no pragma

-- AND THAT MAKES THIS COUNTER THE SECOND PROXY IN THE FAMILY, WITH THE
-- SAME SHAPE AS THE DESCENT AND A CHEAPER ORDER BEHIND IT.  What really
-- descends here is the telescope position: a chain on share i sinks
-- only into the root or a strictly later share, so `n - toℕ i` falls
-- at every dispatch, and the premise is `inputsBelowᵉ`, which a shared
-- slot already carries in its OWN TYPE rather than as a run fact.  So
-- this edge asks less than the subscribe edges do — those spend
-- `dBound`, whose hop half is a fact about what a run emits, while
-- this one is discharged by the syntax's well-formedness.  Both
-- counters are structural stand-ins for orders the tree already has.

-- latch completion AND mark the share dying: a delivered fan-out
-- registration's exhausted close rides its own emit, so a cut during
-- the fan-out suppresses its second close (cutThrough's
-- delivered∧dying rule); the registry entries drop at shareFinish
shareLatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → (i : Fin n) → Bool → EvalSt e → EvalSt e
shareLatch i false st₀ = st₀
shareLatch i true  st₀ =
  record st₀ { completedSources = toℕ i ∷ EvalSt.completedSources st₀
             ; dying = toℕ i ∷ EvalSt.dying st₀ }

-- the registrations this share owes an emit: source matches and the
-- chain's element type is the share's
shareAdmit : ∀ {n} {Γ : Ctx n} {t} → (i : Fin n)
           → List (RegId × Source × Chain Γ t)
           → List (RegId × Path Γ (lookup Γ i) t)
shareAdmit i [] = []
shareAdmit {Γ = Γ} i ((rid , s , (u , p)) ∷ r)
  with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
... | false | _        = shareAdmit i r
... | true  | no  _    = shareAdmit i r
... | true  | yes refl = (rid , p) ∷ shareAdmit i r

shareFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → (i : Fin n) → Bool
            → Stream Γ t × Sched Γ × EvalSt e
            → Stream Γ t × Sched Γ × EvalSt e
shareFinish i false out = out
shareFinish i true  (emits , sched′ , st′) =
  let kept = dropSource (toℕ i) (EvalSt.registry st′)
  in emits ,
     record sched′ { live = sweepLive kept (Sched.live sched′) } ,
     record st′ { registry = kept }

-- THE DISPATCH COUNTER IS THE ONE RE-ENTRY WHOSE SUFFICIENCY NOTHING
-- STATES, and that is a gap rather than a convention.  `chainStep`
-- seeds it at the context size and every share boundary peels it, on
-- the reading that a chain registered on a share can only meet shares
-- of strictly higher index — the slot telescope's own stratification,
-- lifted through the registry.  That reading is a runtime invariant
-- about what the registry holds, not a syntactic fact about the
-- program, and it is asserted in prose at the clause that fires when it
-- fails and nowhere else: no postulate carries it, so the remaining-work
-- ledger cannot see it.
--
-- AND IT IS NOT OWED TO THE DRY FACE, which is why it has stayed
-- invisible.  Exhausting this counter mints no dry event — the clause
-- returns an empty fan-out — so every statement about dryness passes
-- over it for free, and the face that would catch a silently truncated
-- delivery is the one comparing this machine to the spec.
dispatchShare : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Acc _≺_ τ  -- the witness, handed to stepFrame's re-entries
              → ℕ       -- dispatch gas, the telescope bound
              → Id → Tick → (i : Fin n)
              → List (Val Γ (lookup Γ i)) → Bool
              → Sched Γ → EvalSt e
              → Stream Γ t × Sched Γ × EvalSt e

-- a fan-out chain cancelled earlier in this cascade (an operator cut
-- named it a victim) delivers NOTHING — its close already rode the
-- cutting emit; the survivors are marked delivered as they fold.
-- Lifted out of dispatchShare's where block so the budget proof can
-- name it (as with takeVals / thruConsume / sharedConnect)
shareGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Acc _≺_ τ → ℕ → Id → Tick → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e

-- one chain, ONE emit — plus, past a share boundary, the fan-out
-- emits it causes.  Fold the value list sinkward through the frames,
-- accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
foldPath : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Acc _≺_ τ → ℕ → Id → Tick → Source → Path Γ u t
         → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
         → Sched Γ → EvalSt e
         → Stream Γ t × Sched Γ × EvalSt e
foldPath sf gas id now envSrc root vals evs fin sched st =
  ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    at id from envSrc as delivery) ∷ [] , sched , st
foldPath sf gas id now envSrc (share-sink i) vals evs fin sched st =
  -- the chain's own (valueless) emit first — announcing the handoff:
  -- share i fans out next, still inside this instant.  The share
  -- delivers vals to every chain registered on it — the diamond
  -- case, batched by construction
  let (fanout , sched₁ , st₁) = dispatchShare sf gas id now i vals fin sched st
  in (((evs ++ handoff (toℕ i) ∷ []) at id from envSrc as delivery) ∷ fanout)
     , sched₁ , st₁
foldPath sf gas id now envSrc (f ↠ path′) vals evs fin sched st =
  let (vals′ , evs′ , fin′ , sched₁ , st₁) =
        stepFrame sf id now f path′ vals fin sched st
  in foldPath sf gas id now envSrc path′ vals′ (evs ++ evs′) fin′ sched₁ st₁

-- deliver to the chains of share i, one emit per registration from
-- source toℕ i (the share's owed count), in subscription order.  A
-- completing def (fin) latches the share BEFORE the fan-out — as a
-- Subject closes before delivering its completion — so a subscriber
-- joining mid-dispatch already sees the one-shot close/complete and
-- never registers only to be dropped silently; then every snapshot
-- registration closes and the sweep collects whatever the share kept
-- alive
dispatchShare sf zero _ _ _ _ _ sched st = [] , sched , st  -- see above: unreachable
dispatchShare sf (suc gas) id now i vals fin sched st =
  shareFinish i fin
    (shareGo sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))

shareGo sf gas id now i vals fin []               sched₀ st₀ = [] , sched₀ , st₀
shareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true  = shareGo sf gas id now i vals fin ps sched₀ st₀
... | false =
  let (emits , sched₁ , st₁) =
        foldPath sf gas id now (toℕ i) p vals
                 (if fin then close (toℕ i) exhausted ∷ [] else [])
                 fin sched₀
                 (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      (rest , sched₂ , st₂) = shareGo sf gas id now i vals fin ps sched₁ st₁
  in emits ++ rest , sched₂ , st₂

-- seed one arrival into one chain: the value, plus fin and this
-- registration's close when the source is spent (isLast)
chainStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Id → (a : Arrival Γ) → Path Γ (arrTy a) t → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
chainStep {n = n} {e = e} id a path sched st =
  foldPath (rootWitness e (Sched.slots sched)) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
           (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
           (Arrival.isLast a) sched st

-- one arrival, count(source) emits: every live registration chain of
-- the arrival's source forwards EXACTLY ONE emit (possibly valueless),
-- in subscription order — any further emits a chain contributes are
-- share fan-outs, themselves one per registration of their share
-- opens the cascade's per-arrival ledger: delivered/cancelled reset,
-- the registration watermark stamped (newer registrations were born
-- this cascade and owe nothing).  A spent source (final scripted
-- value) is latched completed BEFORE its last delivery fans out — as
-- a Subject closes before delivering its completion — so a subscriber
-- joining mid-cascade already sees the one-shot close/complete; it is
-- also marked dying (each of its chains seeds its own exhausted
-- close; a cut never closes a delivered dying registration a second
-- time; its registry entries drop at cascadeFinish).  Colds and
-- deferᵉ hops get latched too, harmlessly: their sources are
-- per-subscription, never re-subscribed
cascadeLatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             → Arrival Γ → EvalSt e → EvalSt e
cascadeLatch a st₀ =
  record (if Arrival.isLast a
          then record st₀ { completedSources = arrSource a ∷ EvalSt.completedSources st₀ }
          else st₀)
    { delivered = [] ; cancelled = [] ; regWatermark = EvalSt.nextReg st₀
    ; dying = if Arrival.isLast a then arrSource a ∷ [] else [] }

-- fold the snapshot chains.  A chain cancelled earlier in this same
-- cascade (an operator cut named it a victim) delivers NOTHING — as
-- in rxjs, where the unsubscribed branch of take(1)(merge(s,s)) is
-- silent; its close (cut or cutPending) already rode the cutting emit
cascadeGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → (a : Arrival Γ) → Id
          → List (RegId × Path Γ (arrTy a) t) → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
cascadeGo a id []                   sched₀ st₀ = [] , sched₀ , st₀
cascadeGo a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true  = cascadeGo a id chains sched₀ st₀
... | false =
  let (emits , sched₁ , st₁) =
        chainStep id a c sched₀
                  (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      (rest  , sched₂ , st₂) = cascadeGo a id chains sched₁ st₁
  in emits ++ rest , sched₂ , st₂

-- the spent source's registrations drop at the end (each delivered
-- chain carried its own close; cut victims' closes rode the cutting
-- emit) and the sweep collects its live entry
cascadeFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Arrival Γ → Sched Γ → EvalSt e → Sched Γ × EvalSt e
cascadeFinish a sched′ st′ with Arrival.isLast a
... | false = sched′ , st′
... | true  =
      let kept = dropSource (arrSource a) (EvalSt.registry st′)
      in record sched′ { live = sweepLive kept (Sched.live sched′) } ,
         record st′ { registry = kept }

cascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Arrival Γ → Id → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e
cascade a id sched st =
  let (emits , sched′ , st′) =
        cascadeGo a id (chainsOf a st) sched (cascadeLatch a st)
      (sched″ , st″) = cascadeFinish a sched′ st′
  in emits , sched″ , st″

-- fuel = ARRIVALS PROCESSED; each arrival's cascade runs to
-- quiescence (never truncated mid-batch).  The root subscription's
-- burst is free: fuel 0 still yields it.
-- fuel-many arrivals, each cascading to quiescence.  Top level (not a
-- where-local of evaluate) so Verify-Well-Formed can induct on it.
-- Instant ids mint from ARRIVAL POSITION (the counter threaded here):
-- structural distinctness, strictly increasing along the stream.
drain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → Fuel → Id → Sched Γ → EvalSt e → Stream Γ t
drain zero    _      _     _  = []            -- out of fuel: truncate (only here)
drain (suc k) nextId sched st with sched-next sched
... | inj₁ _            = []                  -- schedule empty: program done
... | inj₂ (a , sched′) =
  let (out , sched″ , st′) = cascade a nextId sched′ st
  in out ++ drain k (suc nextId) sched″ st′

evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → Stream Γ t
evaluate fuel e ins =
  let (burst , sched₀ , st₀) =
        subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins) (st-init e)
  in burst ++ drain fuel 1 sched₀ st₀
