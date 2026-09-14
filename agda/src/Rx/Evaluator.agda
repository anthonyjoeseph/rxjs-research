module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _∸_; _⊔_; _<ᵇ_; _≡ᵇ_; _≤ᵇ_; _≤_; _<_; s≤s)
open import Data.Nat.Properties using (_<?_; ≤-refl; ≤-trans; ∸-monoʳ-<)
open import Data.Nat.Induction using (<-wellFounded-fast)
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
  cold; InstEvent; init; value; close; handoff; complete; cut; cutPending; exhausted;
  subscribe; delivery; plumbing; InstEmit; _at_from_as_)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; _≟ᵗ_; Ctx; Val; Closed; Fn; applyFn; evalTm; unfoldμ; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)

variable
  lo : ℕ


------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

-- THE SLOT TELESCOPE lives in Rx.Slots and is re-exported here.  Defs
-- must reference only strictly earlier slots (a const telescope) —
-- checked by the generator/decoder, not by these types; a forward
-- reference is rejected there.
open import Rx.Slots using (scripted; shared; Slots)
open import Rx.Obs-Depth using (obsDepthᵉ; obsDepthᵛ)

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

-- THE SCHEDULE CARRIES NO REFOLD BOUND, AND THAT IS WHAT THE READING
-- BOUGHT.  A reading whose fold clause names a refold COUNT has to be
-- told that count by whoever runs the term, so the count rode here — and
-- the run then had to be trusted about a number it takes from its
-- ARRIVAL allowance while a refold happens per DELIVERY.  A fold that
-- iterates over its own source's delivery count reads that number off
-- the term, so there is nothing left for the schedule to carry and
-- nothing left for a caller to pick wrong.
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

-- THE FLOOR IS AN INDEX, WHICH IS WHAT MAKES THE SHARE NEST DESCEND.
-- A chain registered on share i can only sink into a share ABOVE i —
-- the slot law read rootward, since a share's definition may name only
-- inputs strictly below it — so the fan-out's re-entry always moves
-- further up the telescope.  Carrying that as an index rather than as a
-- side predicate is the whole design: the registry's two filters
-- (`chainsGo`, `shareAdmit`) select by SOURCE, so the floor they
-- guarantee lands in the type of the list the fan-out already takes,
-- and no walk over a path has to be handed a proof alongside it.
data Path {n} (Γ : Ctx n) : ℕ → Ty → Ty → Set where   -- floor → source element type → root type
  root       : ∀ {lo t} → Path Γ lo t t
  share-sink : ∀ {lo t} (i : Fin n) → lo ≤ toℕ i → Path Γ lo (lookup Γ i) t
               -- the chain ends at shared slot i, not the root: its
               -- values are delivered to the share's subject and fan
               -- out to every chain registered on source toℕ i
  _↠_        : ∀ {lo s u t} → Frame Γ s u → Path Γ lo u t → Path Γ lo s t

Chain : ∀ {n} → Ctx n → ℕ → Ty → Set   -- a registration: its source element type packed with its rootward path
Chain Γ lo t = Σ Ty (λ s → Path Γ lo s t)

-- A CHAIN WHOSE FLOOR IS ITS OWN, which is what a registry filter can
-- hand back.  Two rows admitted by one source test need not have been
-- registered at the same place, so the floor travels WITH the path
-- rather than being pinned by the filter's own type.
AtFloor : ∀ {n} → Ctx n → Ty → Ty → Set
AtFloor Γ s t = Σ ℕ (λ lo → Path Γ lo s t)

-- WHERE A REGISTRATION SITS, AS A SHAPE RATHER THAN AS A NUMBER, and
-- the split is the finding rather than a default.  A SLOT source is
-- where the law lives: its floor is read off the index, one above it,
-- and those are the only sources a share fan-out ever dispatches at.  A
-- DYNAMIC source is minted above the context while every share it could
-- sink into is below it, so nothing about its number says where its
-- chain sinks — written as a numeric test the distinction is a Bool that
-- cannot reduce, and the floor stops arriving in the type at all.  So a
-- dynamic row STORES the floor its subscriber stood at, which is the
-- honest reading and is what keeps a cold script's chain from being
-- flattened to the floor that claims its values name no input.
data RegSrc {n} (Γ : Ctx n) : Set where
  atSlot : Fin n      → RegSrc Γ
  atDyn  : Source → ℕ → RegSrc Γ

regSource : ∀ {n} {Γ : Ctx n} → RegSrc Γ → Source
regSource (atSlot i)  = toℕ i
regSource (atDyn s _) = s

regFloor : ∀ {n} {Γ : Ctx n} → RegSrc Γ → ℕ
regFloor (atSlot i)   = suc (toℕ i)
regFloor (atDyn _ lo) = lo

-- A PATH'S FLOOR MAY BE LOWERED, which is the direction the registry
-- needs: a path whose sinks all sit above `lo` has them all above
-- anything under `lo` too.  The step and the root carry nothing, so
-- only the sink arm pays, and it pays by transitivity.
lowerFloor : ∀ {n} {Γ : Ctx n} {s t} {lo lo′} → lo′ ≤ lo
           → Path Γ lo s t → Path Γ lo′ s t
lowerFloor le root             = root
lowerFloor le (share-sink i p) = share-sink i (≤-trans le p)
lowerFloor le (f ↠ p)          = f ↠ lowerFloor le p

frameNodes : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → List NodeId
frameNodes (map-f _)          = []
frameNodes (scan-f _ k)       = k ∷ []
frameNodes (take-f k)         = k ∷ []
frameNodes (from-inner _ k j) = k ∷ j ∷ []
frameNodes (thru-outer _ k)   = k ∷ []

pathHasNode : ∀ {n} {Γ : Ctx n} {s t} → NodeId → Path Γ lo s t → Bool
pathHasNode nid root           = false
pathHasNode nid (share-sink i _) = false
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

-- A REGISTRY ROW, and the Σ is what ties the floor down.  The source is
-- not decoration beside the chain: it is what FIXES the chain's floor,
-- so the two cannot be stored apart without the invariant becoming a
-- side condition again.  Written as a Σ, `(rid , src , c)` still reads
-- as a flat triple at every site.
RegRow : ∀ {n} → Ctx n → Ty → Set
RegRow Γ t = RegId × Σ (RegSrc Γ) (λ rs → Chain Γ (regFloor rs) t)

-- the close reason is writer-asserted per victim: delivered this
-- cascade, or born since the cascade started (owing nothing) ⇒ cut;
-- a pre-existing registration cut before its delivery ⇒ cutPending.
-- A victim of a DYING source that already delivered carried its own
-- exhausted close on its own emit — no second close for it.  Also
-- returns the victims' ids for the cascade's cancelled set.
cutThrough : ∀ {n} {Γ : Ctx n} {t}
           → NodeId → List RegId → RegId → List Source
           → List (RegRow Γ t)
           → List (RegRow Γ t)
             × List (InstEvent (Val Γ t)) × List RegId
cutThrough nid delivered wm dying [] = [] , [] , []
cutThrough nid delivered wm dying ((rid , rs , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid delivered wm dying r
... | true  | kept , closes , rids =
      kept
      , (if any (_≡ᵇ rid) delivered ∧ memberSource (regSource rs) dying
         then closes
         else close (regSource rs)
                (if any (_≡ᵇ rid) delivered ∨ (wm ≤ᵇ rid)
                 then cut else cutPending) ∷ closes)
      , rid ∷ rids
... | false | kept , closes , rids = (rid , rs , c) ∷ kept , closes , rids

-- drop dead dynamic sources (no remaining registrations); hot input
-- slots (sources < n by convention) keep firing regardless, exactly
-- like a hot Subject with no subscribers
sweepLive : ∀ {n} {Γ : Ctx n} {t}
          → List (RegRow Γ t) → List (LiveSource Γ) → List (LiveSource Γ)
sweepLive {n = n} reg []       = []
sweepLive {n = n} reg (l ∷ ls) =
  if (LiveSource.source l <ᵇ n)
     ∨ any (λ p → sameSource (LiveSource.source l)
                       (regSource (proj₁ (proj₂ p)))) reg
  then l ∷ sweepLive reg ls
  else sweepLive reg ls

dropSource : ∀ {n} {Γ : Ctx n} {t}
           → Source → List (RegRow Γ t) → List (RegRow Γ t)
dropSource src []                  = []
dropSource src ((rid , s , c) ∷ r) =
  if sameSource src (regSource s) then dropSource src r
  else (rid , s , c) ∷ dropSource src r

record EvalSt {n} {Γ : Ctx n} {t} (e : Closed Γ t) : Set where
  field registry        : List (RegRow Γ t)   -- live registration chains, subscription order
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
         → (rs : RegSrc Γ) → Path Γ (regFloor rs) u t → EvalSt e → EvalSt e
register {u = u} rs path st =
  record st { registry = EvalSt.registry st
                           ++ (EvalSt.nextReg st , rs , u , path) ∷ []
            ; nextReg  = suc (EvalSt.nextReg st) }

installNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → NodeId → NodeState Γ → EvalSt e → EvalSt e
installNode nid nodeState st =
  record st { nodes = setNode nid nodeState (EvalSt.nodes st) }

-- WHAT A STORE STILL HOLDS, READ IN THE MEASURE'S OWN CURRENCY, WHICH
-- IS WHAT THE ENTRY TAKES ITS JOIN AGAINST.  A store can hold
-- observables — a parked inner in a merge queue, an accumulator a fold
-- deepened — and those are terms an arrival may still subscribe, so an
-- entry seeded off the program alone would be standing below something
-- already written down.  Reading the store in one currency is what lets
-- the entry take a join rather than owe a transfer between two.
obsStᶜˢ : ∀ {n} {Γ : Ctx n} {t} → List (Closed Γ t) → ℕ
obsStᶜˢ []       = 0
obsStᶜˢ (e ∷ es) = obsDepthᵉ e ⊔ obsStᶜˢ es

obsStⁿ : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
obsStⁿ (scan-st {t = t} v)         = obsDepthᵛ t v
obsStⁿ (take-st _)                 = 0
obsStⁿ (mergeAll-st _ _ queued _)  = obsStᶜˢ queued
obsStⁿ (switch-st _ _)             = 0
obsStⁿ (exhaust-st _ _)            = 0

obsStᴺ : ∀ {n} {Γ : Ctx n} → List (NodeId × NodeState Γ) → ℕ
obsStᴺ []             = 0
obsStᴺ ((_ , s) ∷ ns) = obsStⁿ s ⊔ obsStᴺ ns

obsSt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
obsSt st = obsStᴺ (EvalSt.nodes st)

-- a source that lives and dies inside its own subscription burst
-- (ofᵉ, emptyᵉ, take 0, a cold with no async tail): init, values,
-- close, complete — one emit, nothing registered, nothing scheduled
oneShotBurst : ∀ {n} {Γ : Ctx n} {u}
             → List (Val Γ u) → Id → Sched Γ → Stream Γ u × Sched Γ
oneShotBurst vals id sched =
  let (src , sched₁) = mintSource sched
  in ((init src ∷ map value vals ++ close src exhausted ∷ complete ∷ [])
       at id from src as subscribe) ∷ [] , sched₁

-- a source that was already spent before this subscription reached it
-- — a completed Subject, a share whose def has closed, or a slot the
-- registration's own floor test refuses.  Same shape as a one-shot with
-- no values, but the source is GIVEN rather than minted, because the
-- point is that this subscriber joins something that already has an
-- identity.
spentBurst : ∀ {A : Set} → Source → Id → List (InstEmit A)
spentBurst src id =
  ((init src ∷ close src exhausted ∷ complete ∷ []) at id from src as subscribe) ∷ []

-- THE DESCENT DISCIPLINE, AND THE MACHINE NO LONGER CARRIES IT.  Three
-- edges below reach a deeper subscribe without descending the term:
--
--   · `sharedConnect → subscribeE`, at the definition a slot stores;
--   · `subscribeInner → subscribeE`, at a runtime observable;
--   · `subscribeE (μᵉ body) → subscribeE (unfoldμ body)`.
--
-- Each used to TEST a reading and emit a marker on the negative answer,
-- which made an inadequate figure a wrong ANSWER rather than an open
-- obligation — and so put the whole measure inside the run, where every
-- syntactic candidate for it died.  The obligation is the DERIVATION's
-- now: `Rx.Evaluator.Domain` relates a call to its result with a
-- sub-derivation per edge, so an edge that cannot be justified is a
-- proof that does not exist rather than a run that emits something.
--
-- SO THIS MODULE NO LONGER TERMINATES BY ITSELF, AND THAT IS THE TRADE.
-- Agda's checker sees three non-structural calls and nothing decreasing;
-- no pragma is admissible here, so what stands in its place is
-- `Verify-Rank-Sufficient.Doorless`, whose builder returns a result
-- together with its derivation and pays the three facts at the sites
-- that hold them.  `deferᵉ` is not one of the three: it parks the body
-- for `suc now`, a later instant entered afresh.

-- AND THE EDGE SET IS CHECKED RATHER THAN READ OFF, WHICH MATTERS MORE
-- NOW THAN IT DID.  `make recursion-cover` cuts the edges declared below
-- and requires every cycle still standing to be declared too: cutting
-- three edges collapses BOTH of this module's multi-member recursions
-- and exactly one cycle survives, the pair that walks the expression.
-- While a witness was threaded, Agda was satisfied and silent about
-- which edges carried it; with no witness at all Agda is silent about
-- the whole question, so this check is the only thing that fails when a
-- clause opens a FOURTH edge — one the builder next door has no case
-- for and would never be asked to write.

-- THE SHARE HOP KEEPS ITS OWN DESCENT, AND IT IS THE SHAPE THE OTHER
-- THREE BECAME.  `Acc _<_ (n ∸ lo)` is peeled by MATCHING on
-- `floorFalls`, a proof about the sink constructor's own premise — so it
-- asks nothing, has no negative answer, and needs no arm.  It never had
-- a door to kill.  It reaches the frame walk one way only: nothing in
-- the subscribe recursion calls back into it.

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
-- AND THE BOUND RIDES ALONG AS AN IMPLICIT, WHICH IS WHAT KEEPS IT OFF
-- THE CALL SITES.  A subscription's expression may name only inputs
-- below the floor its continuation sinks at, and that is what the
-- `input i` clause spends to register one above `i`.  `T b` is `⊤`
-- wherever `b` computes, so at a concrete program Agda's eta solves the
-- argument and nothing is written; only a statement quantifying over the
-- expression carries it, which is the content.  `Rx.Inputs-Below` holds
-- the descent arm each clause spends.
subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
           → (b : Closed Γ u)
           → Path Γ lo u t → Id → Tick
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
-- AND THE SOURCE TEST IS A DECISION RATHER THAN A BOOL, which is what
-- lets the row's stored floor arrive in the caller's type.  Matching on
-- `_≡ᵇ_` selects the right rows and teaches the clause nothing, so the
-- chain comes back at a floor the caller cannot name.
chainsGo : ∀ {n} {Γ : Ctx n} {t} → (a : Arrival Γ)
         → List (RegRow Γ t) → List (RegId × AtFloor Γ (arrTy a) t)
chainsGo a [] = []
chainsGo a ((rid , s , (u , p)) ∷ r)
  with sameSource (arrSource a) (regSource s) | u ≟ᵗ arrTy a
... | false | _        = chainsGo a r
... | true  | no  _    = chainsGo a r
... | true  | yes refl = (rid , regFloor s , p) ∷ chainsGo a r

chainsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → (a : Arrival Γ) → EvalSt e → List (RegId × AtFloor Γ (arrTy a) t)
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
-- current instant, split its burst.  THE HOP EDGE, AND IT NO LONGER
-- ASKS ANYTHING.  The inner is a runtime VALUE, structurally unrelated
-- to the caller, so nothing about the caller's TERM makes it smaller —
-- which is why this clause used to compare what arrived against the
-- component it stands at and emit a marker on the negative answer.  The
-- comparison is a PREMISE now and it is owed by the derivation rather
-- than by the run: `Verify-Rank-Sufficient.Doorless.subscribeInner!`
-- spends the report where the value was produced, so there is no
-- question here to answer and no arm to answer it with.
subscribeInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
               → AllOp → NodeId → Path Γ lo u t → Id → Tick
               → Val Γ (obs u) → Sched Γ → EvalSt e
               → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
subscribeInner {lo = lo} op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE o (from-inner op allNid inst ↠ κ) id now
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
              → NodeId → EvalSt e → RegRow Γ t → Bool
aliveThroughᶠ inst st (rid , rs , (w , p)) =
  pathHasNode inst p
  ∧ not (any (_≡ᵇ rid) (EvalSt.cancelled st))
  ∧ (not (memberSource (regSource rs) (EvalSt.dying st))
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
            → AllOp → NodeId → Path Γ lo u t → Id → Tick
            → Val Γ (obs u) → Sched Γ → EvalSt e
            → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruConsume {u = u} mergeAllᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = [] , [] , sched₀ , st₀
...   | yes refl with hasRoom lim act
...     | true =
          let (_ , vs , bs , done , sched₁ , st₁) =
                subscribeInner mergeAllᵒ nid κ id now o sched₀ st₀
          in vs , bs , sched₁ ,
             record st₁ { nodes = mergeAllBump nid done (EvalSt.nodes st₁) }
...     | false =
          [] , [] , sched₀ ,
          record st₀ { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                                 (EvalSt.nodes st₀) }
thruConsume mergeAllᵒ nid κ id now o sched₀ st₀ | _ = [] , [] , sched₀ , st₀
thruConsume switchᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (switch-st cur od) =
      let (closes , sched₁ , st₁) = switchKill cur sched₀ st₀
          (inst , vs , bs , done , sched₂ , st₂) =
            subscribeInner switchᵒ nid κ id now o sched₁ st₁
      in vs , closes ++ bs , sched₂ ,
         record st₂ { nodes = setNode nid
           (switch-st (if done then nothing else just inst) od) (EvalSt.nodes st₂) }
... | _ = [] , [] , sched₀ , st₀
thruConsume exhaustᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (exhaust-st true od)  = [] , [] , sched₀ , st₀   -- busy: drop
... | just (exhaust-st false od) =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner exhaustᵒ nid κ id now o sched₀ st₀
      in vs , bs , sched₁ ,
         record st₁ { nodes = setNode nid (exhaust-st (not done) od) (EvalSt.nodes st₁) }
... | _ = [] , [] , sched₀ , st₀

thruWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → AllOp → NodeId → Path Γ lo u t → Id → Tick
         → List (Val Γ (obs u)) → Sched Γ → EvalSt e
         → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruWalk op nid κ id now []       sched₀ st₀ = [] , [] , sched₀ , st₀
thruWalk op nid κ id now (o ∷ os) sched₀ st₀ =
  let (vs  , bs  , sched₁ , st₁) = thruConsume op nid κ id now o sched₀ st₀
      (vs′ , bs′ , sched₂ , st₂) = thruWalk op nid κ id now os sched₁ st₁
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
             → NodeId → Path Γ lo s t → Id → Tick
             → Maybe ℕ → ℕ → List (Closed Γ s) → Sched Γ → EvalSt e
             → List (Val Γ s) × List (InstEvent (Val Γ t)) × ℕ
               × List (Closed Γ s) × Sched Γ × EvalSt e
mergeAllDrain allNid κ id now lim act []      sched₀ st₀ =
  [] , [] , act , [] , sched₀ , st₀
mergeAllDrain allNid κ id now lim act (o ∷ q) sched₀ st₀
  with hasRoom lim act
... | false = [] , [] , act , o ∷ q , sched₀ , st₀
... | true =
      let (_ , vs , bs , done , sched₁ , st₁) =
            subscribeInner mergeAllᵒ allNid κ id now o sched₀ st₀
          (vs′ , bs′ , act′ , q′ , sched₂ , st₂) =
            mergeAllDrain allNid κ id now lim
              (if done then act else suc act) q sched₁ st₁
      in vs ++ vs′ , bs ++ bs′ , act′ , q′ , sched₂ , st₂

innerFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
            → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
            → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerFinish {s = s} mergeAllᵒ allNid inst κ id now vals sched st
            (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | yes refl =
      let (vs , bs , act′ , q′ , sched′ , st′) =
            mergeAllDrain allNid κ id now lim (pred act) q sched st
      in vals ++ vs , bs , od ∧ (act′ ≡ᵇ 0) ∧ null q′ , sched′ ,
         record st′ { nodes = setNode allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′) }
... | no _ = vals , [] , false , sched , st
innerFinish switchᵒ allNid inst κ id now vals sched st (just (switch-st (just c) od)) =
  if c ≡ᵇ inst
  then (vals , [] , od , sched ,
        record st { nodes = setNode allNid (switch-st nothing od) (EvalSt.nodes st) })
  else (vals , [] , false , sched , st)
innerFinish exhaustᵒ allNid inst κ id now vals sched st (just (exhaust-st act od)) =
  vals , [] , od , sched ,
  record st { nodes = setNode allNid (exhaust-st false od) (EvalSt.nodes st) }
innerFinish _ allNid inst κ id now vals sched st _ = vals , [] , false , sched , st

-- a fin only completes THIS INNER once nothing under its exit frame
-- can ever deliver again: a sibling registration of the dying source
-- still queued this cascade, or any other live registration, absorbs
-- it (the TS join's open-multiset, read off the registry) — one
-- chain's exhaustion is not a multi-registration subtree's completion
innerReact : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           → AllOp → NodeId → NodeId → Path Γ lo s t → Id → Tick
           → List (Val Γ s) → Sched Γ → EvalSt e → Bool
           → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerReact op allNid inst κ id now vals sched st false =
  vals , [] , false , sched , st
innerReact op allNid inst κ id now vals sched st true =
  if any (aliveThroughᶠ inst st) (EvalSt.registry st)
  then vals , [] , false , sched , st
  else innerFinish op allNid inst κ id now vals sched st
         (lookupNode allNid (EvalSt.nodes st))

stepFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Id → Tick → Frame Γ s u → Path Γ lo u t
          → List (Val Γ s) → Bool → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e

stepFrame id now (map-f fn) κ vals fin sched st =
  map (applyFn fn) vals , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} {u = u} id now (scan-f fn nid) κ vals fin sched st
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

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} id now (take-f nid) κ vals fin sched st
  = takeDispatch nid vals fin sched st (lookupNode nid (EvalSt.nodes st))

stepFrame id now (from-inner op allNid inst) κ vals fin sched st
  = innerReact op allNid inst κ id now vals sched st fin

stepFrame id now (thru-outer op nid) κ vals fin sched st
  = thruWrap op nid fin (thruWalk op nid κ id now vals sched st)

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
          → Id → Tick → Frame Γ s u → Path Γ lo u t
          → Stream Γ s → Sched Γ → EvalSt e
          → Stream Γ u × Sched Γ × EvalSt e
pushBurst id now f κ []         sched st = [] , sched , st
pushBurst id now f κ (em ∷ ems) sched st =
  let sp   = splitEvents (InstEmit.events em)
      (vals′ , evs , fin′ , sched₁ , st₁) =
        stepFrame id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
      (rest , sched₂ , st₂) = pushBurst id now f κ ems sched₁ st₁
  in ((proj₁ (proj₂ sp) ++ retagEvents evs ++ map value vals′
        ++ (if fin′ then complete ∷ [] else []))
       at InstEmit.instant em from InstEmit.source em as InstEmit.kind em)
       ∷ rest , sched₂ , st₂

-- the shared *All shape: mint the node, install its initial state,
-- subscribe the outer under a thru-outer frame, push the burst through
subscribeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → AllOp → NodeState Γ → (b : Closed Γ (obs u))
             → Path Γ lo u t
             → Id → Tick → Sched Γ → EvalSt e
             → Stream Γ u × Sched Γ × EvalSt e
subscribeAll op initialState b κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE b (thru-outer op nid ↠ κ) id now sched₁
                   (installNode nid initialState st)
  in pushBurst id now (thru-outer op nid) κ burst sched₂ st₁

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

-- the connect is a non-structural edge: the def d is a stored
-- expression, structurally unrelated to the `input i` being
-- subscribed, so nothing about the term being walked shrinks here.
-- It is separated from `subscribeSharedSlot`'s other branches because
-- joining an already-connected share takes no edge at all, and lifted
-- out of its where block so the derivation can name it (as with
-- takeVals / thruConsume / mergeAllDrain)
sharedConnect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → (i : Fin n) → (d : Closed Γ (lookup Γ i))
              → Path Γ lo (lookup Γ i) t → toℕ i < lo → Id → Tick
              → Sched Γ → EvalSt e
              → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
-- THE CONNECT'S DESCENT IS A COUNT AND IT IS OWED ELSEWHERE NOW.
-- Connecting slot `i` puts `i` into the connected set, so the reading
-- over the slots NOT in that set drops by exactly one — provided `i`
-- was not already there, which is the branch `subscribeSharedSlot` took
-- to reach this clause.  That proviso is why the fact cannot be stated
-- free, and it is `Rx.Evaluator.Doorless.connect-edge`; the clause
-- itself reads nothing.
sharedConnect i d κ below id now sched st =
  let st₁ = register (atSlot i) (lowerFloor below κ)
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      (burst , sched₁ , st₂) =
        subscribeE d (share-sink i ≤-refl) id now sched st₁
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
                    → (i : Fin n) → (d : Closed Γ (lookup Γ i))
                    → Path Γ lo (lookup Γ i) t → toℕ i < lo → Id → Tick
                    → Sched Γ → EvalSt e
                    → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
subscribeSharedSlot {Γ = Γ} {e = e} i d κ below id now sched st =
  if memberSource (toℕ i) (EvalSt.completedSources st)
  then spentBurst (toℕ i) id , sched , st
  else if memberSource (toℕ i) (EvalSt.connectedShares st)
  then -- live: join mid-flight, future values only
       ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
       , sched , register (atSlot i) (lowerFloor below κ) st
  else sharedConnect i d κ below id now sched st

subscribeE {lo = lo} {Γ = Γ} (input i) κ id now sched st with toℕ i <? lo
... | no _ = spentBurst (toℕ i) id , sched , st
... | yes below with Sched.slots sched i
...   | shared d =
      subscribeSharedSlot i d κ below id now sched st
...   | scripted (hot _) =
      if memberSource (toℕ i) (EvalSt.completedSources st)
      then -- spent script: a completed Subject — immediate
           -- close/complete, nothing registered
           spentBurst (toℕ i) id , sched , st
      else -- already live (sched-init, source = ordinal = toℕ i); just
           -- another registration — fan-out IS this multiplicity
           ((init (toℕ i) ∷ []) at id from toℕ i as subscribe) ∷ []
           , sched , register (atSlot i) (lowerFloor below κ) st
...   | scripted (cold sync []) =
      let (burst , sched₁) = oneShotBurst sync id sched
      in burst , sched₁ , st
...   | scripted (cold sync (d ∷ ds)) =
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
         , sched₃ , register (atDyn src _) κ st

subscribeE (ofᵉ ts) κ id now sched st =
  let (burst , sched₁) = oneShotBurst (map (λ tm → evalTm tm) ts) id sched
  in burst , sched₁ , st

subscribeE emptyᵉ κ id now sched st =
  let (burst , sched₁) = oneShotBurst [] id sched
  in burst , sched₁ , st

subscribeE (mapᵉ f b) κ id now sched st =
  let (burst , sched₁ , st₁) =
        subscribeE b (map-f f ↠ κ) id now sched st
  in pushBurst id now (map-f f) κ burst sched₁ st₁

subscribeE (takeᵉ count b) κ id now sched st with evalTm count
... | zero =
      -- take 0 never subscribes its source (as in rxjs): a spent
      -- one-shot, exactly emptyᵉ
      let (burst , sched₁) = oneShotBurst [] id sched
      in burst , sched₁ , st
... | suc k =
      let (nid , sched₁) = mintNode sched
          (burst , sched₂ , st₁) =
            subscribeE b (take-f nid ↠ κ) id now sched₁
                       (installNode nid (take-st (suc k)) st)
      in pushBurst id now (take-f nid) κ burst sched₂ st₁

subscribeE (scanᵉ f seed b) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (burst , sched₂ , st₁) =
        subscribeE b (scan-f f nid ↠ κ) id now sched₁
                   (installNode nid (scan-st (evalTm seed)) st)
  in pushBurst id now (scan-f f nid) κ burst sched₂ st₁

subscribeE {u = u} (mergeAllᵉ lim b) κ id now sched st =
  subscribeAll mergeAllᵒ (mergeAll-st {t = u} lim 0 [] false) b
               κ id now sched st
subscribeE (switchAllᵉ b) κ id now sched st =
  subscribeAll switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE (exhaustAllᵉ b) κ id now sched st =
  subscribeAll exhaustᵒ (exhaust-st false false) b κ id now sched st

-- one unfold per subscription; the recursive occurrences inside the
-- unfolding are deferᵉ-gated, so each re-entry costs a schedule hop —
-- no synchronous loop.  A non-structural edge: the unfolding is larger
-- than the μ, not a subterm — and the only one of the three whose fact
-- was already proven, since `Rx.Sync-Size.unfoldμ-shrinks` speaks of
-- the term rather than of anything the run was handed.
subscribeE (μᵉ body) κ id now sched st =
  subscribeE (unfoldμ body) κ id now sched st

subscribeE (varᵉ ()) κ id now sched st

-- deferᵉ is mergeAll of a one-shot scheduled outer: the body itself is
-- the pending payload (Val Γ (obs u) IS Closed Γ u), delivered at
-- suc now with isLast — the arrival's thru-outer frame subscribes it
-- under that arrival's fresh instant, wrap marks the outer done, and
-- the node completes when the body does.  Cancellation is free:
-- cutting the registration lets sweepLive collect the pending hop
subscribeE {u = u} (deferᵉ body) κ id now sched st =
  let (nid , sched₁) = mintNode sched
      (src , sched₂) = mintSource sched₁
      (ord , sched₃) = mintOrdinal sched₂
      sched₄ = record sched₃
        { live = record { source = src ; ordinal = ord
                        ; elemTy = obs u
                        ; pending = (suc now , body) ∷ [] }
                 ∷ Sched.live sched₃ }
  in ((init src ∷ []) at id from src as subscribe) ∷ [] , sched₄ ,
     register (atDyn src _) (thru-outer mergeAllᵒ nid ↠ κ)
              (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st)

-- delivery at a share boundary re-enters chain evaluation: foldPath
-- and dispatchShare are mutually recursive, and what falls across that
-- cycle is the DISTANCE FROM THE FLOOR TO THE TOP OF THE TELESCOPE.  A
-- chain indexed at floor `lo` sinks only into the root or a share whose
-- own index is at least `lo`, and the sink constructor carries that as
-- a premise; dispatching at share i re-enters at floor `suc (toℕ i)`,
-- which is strictly above `lo`, so `n ∸ lo` strictly falls.  The
-- accessibility on `_<_` at that quantity is what the three functions
-- recurse on.
--
-- SO THE ORDER IS THE TREE'S OWN AND NOT A STAND-IN FOR IT.  This edge
-- used to spend a counter seeded at the context size, whose clamp arm
-- was reachable in the TYPE and unreachable only on a registry
-- invariant no postulate carried — a bound asserted in prose at the
-- clause that fires when it fails, and nowhere else.  Indexing the path
-- by its floor turns that invariant into the sink constructor's
-- premise, so the descent is discharged by what the registry's rows
-- ARE rather than by a fact about what a run put in them, and the clamp
-- arm has no type to be written at.

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
-- AND THE FLOOR ARRIVES HERE, which is the whole reason the source is
-- stored in a Σ with its chain: every row this returns is registered on
-- share i, so every one of them sinks STRICTLY ABOVE i, and the fan-out
-- below reads that off the list's own type rather than from a premise.
shareAdmit : ∀ {n} {Γ : Ctx n} {t} → (i : Fin n)
           → List (RegRow Γ t)
           → List (RegId × Path Γ (suc (toℕ i)) (lookup Γ i) t)
shareAdmit i []                              = []
shareAdmit i ((rid , atDyn _ _ , _)      ∷ r) = shareAdmit i r
shareAdmit {Γ = Γ} i ((rid , atSlot j , (u , p)) ∷ r)
  with i ≟ᶠ j | u ≟ᵗ lookup Γ i
... | no  _    | _        = shareAdmit i r
... | yes _    | no  _    = shareAdmit i r
... | yes refl | yes refl = (rid , p) ∷ shareAdmit i r

shareFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → (i : Fin n) → Bool
            → Stream Γ t × Sched Γ × EvalSt e
            → Stream Γ t × Sched Γ × EvalSt e
shareFinish i false out = out
shareFinish i true  (emits , sched′ , st′) =
  let kept = dropSource (toℕ i) (EvalSt.registry st′)
  in emits ,
     record sched′ { live = sweepLive kept (Sched.live sched′) } ,
     record st′ { registry = kept }

-- THE DESCENT, SPELLED WHERE THE PREMISE LIVES.  A chain whose floor is
-- at or below share i re-enters the fan-out at floor `suc (toℕ i)`,
-- strictly above it, so the distance to the top of the telescope
-- strictly falls.  The proof is stated apart from the dispatch because
-- the dispatch must peel its own witness by MATCHING, and a witness
-- peeled through an application is one the termination checker cannot
-- follow.
floorFalls : ∀ {n lo} (i : Fin n) → lo ≤ toℕ i → n ∸ suc (toℕ i) < n ∸ lo
floorFalls i below = ∸-monoʳ-< (s≤s below) (toℕ<n i)

-- THE DISPATCH STANDS AT THE CHAIN'S FLOOR AND PEELS TO THE FAN-OUT'S,
-- which is why the sink's own premise is an argument here.  A dependent
-- function type binds left to right, so a premise mentioning `i` cannot
-- precede it; everything else keeps the position the counter held.
dispatchShare : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Acc _<_ (n ∸ lo)  -- the descent, at the chain's own floor
              → Id → Tick → (i : Fin n) → lo ≤ toℕ i
              → List (Val Γ (lookup Γ i)) → Bool
              → Sched Γ → EvalSt e
              → Stream Γ t × Sched Γ × EvalSt e

-- a fan-out chain cancelled earlier in this cascade (an operator cut
-- named it a victim) delivers NOTHING — its close already rode the
-- cutting emit; the survivors are marked delivered as they fold.
-- Lifted out of dispatchShare's where block so the budget proof can
-- name it (as with takeVals / thruConsume / sharedConnect)
shareGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Acc _<_ (n ∸ lo) → Id → Tick → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e

-- one chain, ONE emit — plus, past a share boundary, the fan-out
-- emits it causes.  Fold the value list sinkward through the frames,
-- accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
foldPath : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Acc _<_ (n ∸ lo) → Id → Tick → Source → Path Γ lo u t
         → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
         → Sched Γ → EvalSt e
         → Stream Γ t × Sched Γ × EvalSt e
foldPath ac id now envSrc root vals evs fin sched st =
  ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    at id from envSrc as delivery) ∷ [] , sched , st
-- THE SINK HANDS ITS OWN PREMISE DOWN, and that premise is the whole
-- descent: the dispatch peels the witness by it rather than being
-- trusted to stay inside a count.
foldPath ac id now envSrc (share-sink i below) vals evs fin sched st =
  -- the chain's own (valueless) emit first — announcing the handoff:
  -- share i fans out next, still inside this instant.  The share
  -- delivers vals to every chain registered on it — the diamond
  -- case, batched by construction
  let (fanout , sched₁ , st₁) =
        dispatchShare ac id now i below vals fin sched st
  in (((evs ++ handoff (toℕ i) ∷ []) at id from envSrc as delivery) ∷ fanout)
     , sched₁ , st₁
foldPath ac id now envSrc (f ↠ path′) vals evs fin sched st =
  let (vals′ , evs′ , fin′ , sched₁ , st₁) =
        stepFrame id now f path′ vals fin sched st
  in foldPath ac id now envSrc path′ vals′ (evs ++ evs′) fin′ sched₁ st₁

-- deliver to the chains of share i, one emit per registration from
-- source toℕ i (the share's owed count), in subscription order.  A
-- completing def (fin) latches the share BEFORE the fan-out — as a
-- Subject closes before delivering its completion — so a subscriber
-- joining mid-dispatch already sees the one-shot close/complete and
-- never registers only to be dropped silently; then every snapshot
-- registration closes and the sweep collects whatever the share kept
-- alive
-- `shareAdmit` hands back rows indexed at `suc (toℕ i)`, so the witness
-- the fan-out is handed is this one peeled by the sink's own premise —
-- matched here rather than applied, since that is the only form the
-- termination checker reads as a descent.
dispatchShare (acc rs) id now i below vals fin sched st =
  shareFinish i fin
    (shareGo (rs (floorFalls i below)) id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st))

shareGo ac id now i vals fin []               sched₀ st₀ = [] , sched₀ , st₀
shareGo ac id now i vals fin ((rid , p) ∷ ps) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true  = shareGo ac id now i vals fin ps sched₀ st₀
... | false =
  let (emits , sched₁ , st₁) =
        foldPath ac id now (toℕ i) p vals
                 (if fin then close (toℕ i) exhausted ∷ [] else [])
                 fin sched₀
                 (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      (rest , sched₂ , st₂) = shareGo ac id now i vals fin ps sched₁ st₁
  in emits ++ rest , sched₂ , st₂

-- seed one arrival into one chain: the value, plus fin and this
-- registration's close when the source is spent (isLast)
chainStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Id → (a : Arrival Γ) → AtFloor Γ (arrTy a) t → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
chainStep {n = n} {e = e} id a (lo , path) sched st =
  foldPath (<-wellFounded-fast (n ∸ lo))
           id (arrTick a) (arrSource a) path (arrVal a ∷ [])
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
          → List (RegId × AtFloor Γ (arrTy a) t) → Sched Γ → EvalSt e
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

-- THE FUEL IS AN ARRIVAL ALLOWANCE AND NOTHING ELSE.  It bounds how
-- many arrivals `drain` will serve; the rank a subscription descends on
-- is read off the term, so no reading anywhere is relative to it.  The
-- two quantities were once one field, and they are not the same
-- quantity: `drain` spends one unit per ARRIVAL while a fold refolds
-- per DELIVERY, so a cascade delivering entirely inside one subscribe
-- frame refolds as often as its source is long against no fuel at all.
-- AND THE ROOT'S FLOOR IS THE CONTEXT SIZE, which is where the whole
-- stratification enters and where it costs nothing.  A closed term's
-- inputs are drawn from `Fin n`, so every one of them is below `n` by
-- construction; and the root path sinks into no share at all, so it
-- meets the floor vacuously.  Everything below descends from here.
--
-- AND THE ROOT NO LONGER SEEDS A RANK, WHICH IS THE WHOLE OF THE DIFF
-- AT THE TOP LINE.  The type is unchanged, so the oracle, the bug cache
-- and every protocol theorem above see nothing — which is the test that
-- the descent was never part of the semantics.  What it costs is that
-- this definition is not accepted on its own: the three edges below
-- descend on facts stated in `Rx.Evaluator.Doorless` and spent in
-- `Verify-Rank-Sufficient.Doorless`, and no pragma may stand in for
-- them here.
evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → Stream Γ t
evaluate {n = n} fuel e ins =
  let (burst , sched₀ , st₀) =
        subscribeE {lo = n} e root 0 0 (sched-init e ins)
          (st-init e)
  in burst ++ drain fuel 1 sched₀ st₀
