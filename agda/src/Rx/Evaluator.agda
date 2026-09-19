module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Fin.Properties using (toℕ<n) renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _<ᵇ_; _≡ᵇ_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List    using (List; []; _∷_; _++_; concat; tabulate; null)
open import Data.Bool.ListAction using (any)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Tick; Ordinal; Source; Timed; after_,_; hot; cold;
  PlainEvent; valueᵖ; completeᵖ)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; listᵗ; _≟ᵗ_; Ctx; Val; Closed; FnClo; applyClo)

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
open import Rx.Mint using (Mint; mint-init)

-- THE CARRIER IS PLAIN, AND THE PROTOCOL RIDES ON ITS VALUES.  What a
-- run pushes is what an rxjs subscriber sees: values in order, then an
-- end.  A simultaneity-aware program reaches this machine only through
-- the elaboration, which compiles the protocol into the VALUE type, so
-- the machine itself never handles an envelope and the mirror keeps
-- its footing — the TypeScript's operators are plain rxjs too.
Stream : ∀ {n} → Ctx n → Ty → Set          -- flat, canonical emission order
Stream Γ t = List (PlainEvent (Val Γ t))

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
  field mint        : Mint            -- every identifier the run hands out, keyed:
                                     -- ordinals in subscription order, dynamic
                                     -- sources (colds, deferᵉ bodies) from n up,
                                     -- node instances from zero
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
-- at subscription time, minting at the source and ordinal keys
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
  { mint = mint-init n
  ; live = concat (tabulate (mkHot ins)) ; slots = ins }

-- pop the pending arrival minimal by (tick, ordinal), or report empty.
-- The workers are TOP-LEVEL (not where-local of sched-next) so a proof
-- can reason about the arrival sched-next yields — in particular that
-- it carries its LiveSource's elemTy
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

-- TWO OF THE FIVE ARMS CARRY A PAYLOAD, AND THAT CENSUS IS WHAT THE
-- REDUCIBILITY FACE IS ACTUALLY WAITING ON.  A candidate defined by
-- recursion on the type says nothing about what a NODE HOLDS, so every
-- arm of `Rx.Evaluator.Reducible` that reads a node back is owed a
-- store invariant -- but only where the read produces a VALUE.  Here
-- `cell-st` holds one outright and `mergeAll-st`'s queue holds
-- observable values; `take-st`, `switch-st` and `exhaust-st` hold a count, an
-- identifier and two flags, and nothing that leaves a frame dispatching
-- on those came from anywhere but the burst that arrived.  So three of
-- the four arms need no carrier at all, and the two that do differ in
-- cost: a queue entry's reducibility arrives from the hypothesis that
-- admitted it, while an accumulator's is folded by the operator's own
-- function and has no such source.
data NodeState {n} (Γ : Ctx n) : Set where
  cell-st    : ∀ {t} → Val Γ t → NodeState Γ
               -- ONE CARRIED VALUE, AND IT IS NOT SCAN'S.  Every
               -- stateful pure-function former keeps exactly this and
               -- nothing else -- a running accumulator for the fold,
               -- the carried state for the scanning step -- so the cell
               -- is named for what it HOLDS rather than for whichever
               -- former happens to be installed over it.  The type is
               -- existential, so each read pays a `_≟ᵗ_`.
  take-st    : ℕ → NodeState Γ                  -- emissions remaining
  batchSync-st : ∀ {t} → Bool → List (Val Γ t) → NodeState Γ
               -- THE ONE BIT A PLAIN OPERATOR MAY KNOW ABOUT SYNCHRONY,
               -- AND THE BUFFER THAT BIT IS FOR.  The bit is whether
               -- this node's own subscribe call has returned: set when
               -- the node is installed, cleared at the flush, which is
               -- exactly the bracket the TypeScript `captureSync` holds
               -- open between `sync = true` and the `sync = false`
               -- after `obs.subscribe(…)` returns.
               --
               -- THE BUFFER IS WHAT A PER-VALUE MACHINE NEEDS AND A
               -- BURST-COLLECTING ONE DID NOT.  While a subscribe
               -- handed its whole output back as a list, the bracket
               -- could be honoured by GROUPING that list and the node
               -- held one bit.  Values now descend one at a time, so
               -- there is no list at the moment of grouping and the
               -- operator has to hold what arrived while its bit was
               -- up -- which is what the TypeScript does, and the
               -- reading that a burst IS a batch was only ever a fact
               -- about how this machine carried a source's output.
               -- Nothing else about the values is recorded, and
               -- nothing can be: the bit says which side of one call
               -- we are on, never where a value came from nor whether
               -- more is owed.  The element type is existential, so
               -- each read pays a `_≟ᵗ_`.
  mergeAll-st : ∀ {t} → (limit : Maybe ℕ) (active : ℕ)
               (queued : List (Val Γ (obs t))) (outerDone : Bool) → NodeState Γ
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
  map-f      : ∀ {s u} → FnClo Γ s u → Frame Γ s u
               -- the stateless step, applied once per arriving value.
               -- It OWNS NO NODE, and that is forced rather than
               -- chosen: a cell would need a seed, and the term
               -- language has no generic inhabitant to build one from.
  scan-f     : ∀ {s u} → FnClo Γ (u ×ᵗ s) u
             → NodeId → Frame Γ s u
               -- the accumulating step, applied ONCE PER ARRIVING VALUE
               -- with its cell threaded along.  Its output IS its
               -- carried state, which is what rxjs's `scan` is and why
               -- the seed lives in the cell rather than in the type.
               --
               -- Between them these two are the largest a frame can be
               -- while leaving the protocol alone: each reads no node
               -- but its own cell, mints no registration and cannot
               -- raise fin, and neither can see the frame it is
               -- stepping — which is what keeps both expressible as the
               -- plain-rxjs operators they are named after.
  take-f     : ∀ {s} → NodeId → Frame Γ s s
  batchSync-f : ∀ {s} → NodeId → Frame Γ s (s ×ᵗ listᵗ s)
               -- THE ONLY FRAME WHOSE OUTPUT TYPE IS NOT ITS INPUT'S
               -- OR A LAYER OFF IT, AND THE GROUPING IS WHY.  Values
               -- arriving inside the subscribe bracket leave as ONE
               -- value carrying all of them, head and tail, so the
               -- result is nonempty by construction and needs no `Ty`
               -- former of its own; values arriving after it leave one
               -- per singleton.  An empty subscribe burst produces no
               -- value at all rather than an empty group, which is
               -- what the TypeScript does when its burst array comes
               -- back empty.
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
frameNodes (batchSync-f k)    = k ∷ []
frameNodes (from-inner _ k j) = k ∷ j ∷ []
frameNodes (thru-outer _ k)   = k ∷ []

pathHasNode : ∀ {n} {Γ : Ctx n} {s t} → NodeId → Path Γ lo s t → Bool
pathHasNode nid root           = false
pathHasNode nid (share-sink i _) = false
pathHasNode nid (f ↠ p)       = any (_≡ᵇ nid) (frameNodes f) ∨ pathHasNode nid p

-- Registrations carry an identity so a mid-cascade cut can name its
-- victims: a cancelled registration's snapshot chain must deliver
-- NOTHING, as in rxjs, where an unsubscribed chain is silent.
RegId : Set
RegId = ℕ

-- A REGISTRY ROW, and the Σ is what ties the floor down.  The source is
-- not decoration beside the chain: it is what FIXES the chain's floor,
-- so the two cannot be stored apart without the invariant becoming a
-- side condition again.  Written as a Σ, `(rid , src , c)` still reads
-- as a flat triple at every site.
RegRow : ∀ {n} → Ctx n → Ty → Set
RegRow Γ t = RegId × Σ (RegSrc Γ) (λ rs → Chain Γ (regFloor rs) t)

-- Remove every registration whose chain passes through the given node,
-- and return the victims' ids for the cascade's cancelled set.  The
-- severing is all there is: which victim had already paid this instant
-- and which never would used to decide a close reason per victim, and a
-- plain stream carries no closes for that reason to ride on.
cutThrough : ∀ {n} {Γ : Ctx n} {t}
           → NodeId → List (RegRow Γ t)
           → List (RegRow Γ t) × List RegId
cutThrough nid [] = [] , []
cutThrough nid ((rid , rs , c) ∷ r)
  with pathHasNode nid (proj₂ c) | cutThrough nid r
... | true  | kept , rids = kept , rid ∷ rids
... | false | kept , rids = (rid , rs , c) ∷ kept , rids

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
        dying           : List Source   -- sources spending their final delivery this
                                        -- cascade (the isLast arrival, a completing
                                        -- share): their delivered registrations have
                                        -- nothing left to be asked for, and the whole
                                        -- source's registry entries drop at finish

-- append: the registry stays in subscription order.  The id is HANDED
-- IN rather than minted here, because the run has exactly one ledger
-- and it rides on the schedule, which this function is not given; the
-- caller reads `regᵏ` and advances it in the same breath, which is the
-- shape node instances already have.
register : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → RegId → (rs : RegSrc Γ) → Path Γ (regFloor rs) u t → EvalSt e → EvalSt e
register {u = u} rid rs path st =
  record st { registry = EvalSt.registry st ++ (rid , rs , u , path) ∷ [] }

installNode : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → NodeId → NodeState Γ → EvalSt e → EvalSt e
installNode nid nodeState st =
  record st { nodes = setNode nid nodeState (EvalSt.nodes st) }

st-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → EvalSt e
st-init e = record { registry = [] ; nodes = []
                   ; connectedShares = [] ; completedSources = []
                   ; delivered = [] ; cancelled = [] ; dying = [] }
  -- all populated by the root subscribeE and by lazy share connects

-- the arrival's source's live chains, in subscription order, at
-- exactly the arrival's element type: a chain is admitted only past a
-- Ty equality check, so no payload is ever read at the wrong type (a
-- mistyped registry entry — impossible by the registration invariant —
-- is dropped, never trusted)
-- TOP-LEVEL (not where-local of chainsOf) so a proof can induct on it
-- against the registry — the snapshot of a's source-typed chains
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

-- WHETHER AN EVENT IS THE END, which is the only thing anyone reads
-- off one: a share's fan-out dispatches a value to `emit` and an end
-- to `close`, and that choice is the whole of the test.
isFinᵖ : ∀ {A : Set} → PlainEvent A → Bool
isFinᵖ (valueᵖ _) = false
isFinᵖ completeᵖ  = true

-- THE PER-FRAME SEMANTICS, AND EVERY ONE OF THEM TAKES ONE VALUE.
-- The deep recursion -- a subscription's synchronous run re-entering
-- the pipeline -- lives in the subscribe cycle, and what lives here is
-- what a frame does to a single arriving value: one application, one
-- fold step, one decrement, one buffer append.  There is no list, and
-- the absence is the whole point.  A frame that was handed the whole
-- of its source's output could group it, count it, or truncate it
-- knowing how much was coming; none of those is a capability rxjs
-- gives an operator, and each was reachable here only because a
-- source was run to the end before any of it descended.
--
-- Missing or mistyped node state -- impossible by the subscription
-- invariant -- degrades to forwarding NOTHING, never to a wrong read,
-- which is why each of these returns a `Maybe` rather than a value.

-- THE STATELESS STEP, AND IT READS NO NODE AT ALL.  A map's whole
-- effect is one application, so unlike every other frame here it has
-- no dispatch: there is no cell to read, no type to decide against
-- what is installed, and so no stuck arm to state.  The frame's own
-- declaration says the same thing from the other side by owning no
-- `NodeId`.  It is not written as a function because there is nothing
-- left to write: the relation applies the closure.

-- THE ACCUMULATING STEP, WHICH IS ONE APPLICATION WITH THE CELL
-- THREADED.  The function is handed the carried state and the value
-- and hands back the next state, which is also what leaves -- so the
-- step reads the cell, applies, writes back, and emits what it wrote.
-- A cell of the wrong type emits nothing and writes nothing, stated
-- as a function so no prover can prefer that arm at a node that
-- really does hold the state.
scanStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
         → FnClo Γ (u ×ᵗ s) u → NodeId → Val Γ s → EvalSt e
         → Maybe (Val Γ u) × EvalSt e
scanStep {u = u} fn nid v st with lookupNode nid (EvalSt.nodes st)
... | just (cell-st {w} ac) with w ≟ᵗ u
...   | no  _    = nothing , st
...   | yes refl =
        let ac′ = applyClo fn (ac , v)
        in just ac′ , record st { nodes = setNode nid (cell-st ac′) (EvalSt.nodes st) }
scanStep fn nid v st | _ = nothing , st

-- TAKE, AND THE COUNT IS SPENT ONE VALUE AT A TIME BECAUSE THAT IS
-- WHAT rxjs DOES.  Real `take` was run against a four-item synchronous
-- source, against a `mergeAll` of two inner bursts, and at zero; it
-- emits the nth value and completes AFTER it, and it cuts mid-burst
-- rather than waiting for the burst to finish.  Both facts are
-- properties of a per-value decrement and neither survives a
-- budgeted-prefix reading of a whole list.  The Bool is whether THIS
-- value was the last one owed, which is where the cut happens.
takeStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → NodeId → EvalSt e → Maybe Bool × EvalSt e
takeStep nid st with lookupNode nid (EvalSt.nodes st)
... | just (take-st (suc k)) =
      just (k ≡ᵇ 0) , record st { nodes = setNode nid (take-st k) (EvalSt.nodes st) }
... | _ = nothing , st

-- THE CUT ITSELF, which take performs on the value that exhausts it:
-- the registrations threaded through this node are severed and the
-- scheduler's live sources swept of anything nothing reads any more.
cutAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      → NodeId → Sched Γ → EvalSt e → Sched Γ × EvalSt e
cutAt nid sched st =
  let (kept , cutRids) = cutThrough nid (EvalSt.registry st)
  in record sched { live = sweepLive kept (Sched.live sched) } ,
     record st { registry = kept
               ; cancelled = cutRids ++ EvalSt.cancelled st
               ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) }

-- THE BRACKET, ARRIVING SIDE.  While the bit is up the value is
-- BUFFERED and nothing leaves; once it is down every value leaves as
-- its own group of one.  That is the TypeScript's `isSync` exactly,
-- and it is the whole of what a plain operator may know about
-- synchrony.
batchSyncPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
              → NodeId → Val Γ s → EvalSt e
              → Maybe (Val Γ (s ×ᵗ listᵗ s)) × EvalSt e
batchSyncPush {s = s} nid v st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} true buf) with w ≟ᵗ s
...   | no  _    = nothing , st
...   | yes refl =
        nothing , record st { nodes = setNode nid (batchSync-st true (buf ++ v ∷ []))
                                              (EvalSt.nodes st) }
batchSyncPush nid v st | just (batchSync-st false _) = just (v , []) , st
batchSyncPush nid v st | _                           = nothing , st

-- THE BRACKET, CLOSING SIDE, AND IT IS WHERE THE GROUP IS BUILT.  The
-- subscribe call has returned, so whatever was buffered leaves as ONE
-- value carrying all of it, head and tail -- nonempty by construction,
-- which is why the result needs no `Ty` former of its own.  An empty
-- buffer produces no value at all rather than an empty group, which is
-- what the TypeScript does when its burst array comes back empty.  The
-- bit is cleared either way, so a body that emitted nothing on
-- subscribe leaves this node in the async state exactly as one that
-- emitted three does.
batchSyncFlush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
               → NodeId → EvalSt e
               → Maybe (Val Γ (s ×ᵗ listᵗ s)) × EvalSt e
batchSyncFlush {Γ = Γ} {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (batchSync-st {w} _ buf) with w ≟ᵗ s
...   | no  _    = nothing , record st { nodes = setNode nid (batchSync-st {t = s} false [])
                                                         (EvalSt.nodes st) }
...   | yes refl = grp buf , record st { nodes = setNode nid (batchSync-st {t = s} false [])
                                                         (EvalSt.nodes st) }
        where grp : List (Val Γ s) → Maybe (Val Γ (s ×ᵗ listᵗ s))
              grp []       = nothing
              grp (x ∷ xs) = just (x , xs)
batchSyncFlush {Γ = Γ} {s = s} nid st | _ =
  nothing , record st { nodes = setNode nid (batchSync-st {t = s} false []) (EvalSt.nodes st) }

-- a from-inner completion is absorbed iff some registration under this inner
-- instance is still live: its path threads `inst`, it is not cancelled, and it
-- is not an already-delivered dying-source chain.  Top-level (not from-inner-
-- local) so a proof can case-split the absorb vs. finish paths.
aliveThroughᶠ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → NodeId → EvalSt e → RegRow Γ t → Bool
aliveThroughᶠ inst st (rid , rs , (w , p)) =
  pathHasNode inst p
  ∧ not (any (_≡ᵇ rid) (EvalSt.cancelled st))
  ∧ (not (memberSource (regSource rs) (EvalSt.dying st))
     ∨ not (any (_≡ᵇ rid) (EvalSt.delivered st)))


-- IS THERE A FREE LANE?  `nothing` is rxjs's Infinity, so always.
hasRoom : Maybe ℕ → ℕ → Bool
hasRoom nothing  active = true
hasRoom (just m) active = active <ᵇ m

-- switchAll's cut: the outgoing inner's registrations are severed
switchKill : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → Maybe NodeId → Sched Γ → EvalSt e
           → Sched Γ × EvalSt e
switchKill nothing  sched₀ st₀ = sched₀ , st₀
switchKill (just v) sched₀ st₀ =
  let (kept , cutRids) = cutThrough v (EvalSt.registry st₀)
  in record sched₀ { live = sweepLive kept (Sched.live sched₀) } ,
     record st₀ { registry = kept
                ; cancelled = cutRids ++ EvalSt.cancelled st₀ }

-- WHETHER A CONSUME CLAUSE HAS A NODE IT CAN USE AT ALL, AS ONE
-- FUNCTION OF THE READING.  Each operator accepts exactly one shape of
-- stored state: a merge wants its own, at its own element type, since
-- the table carries that type existentially; a switch wants its own,
-- which holds no type to disagree about; an exhaust wants its own with
-- nothing already running, because a busy exhaust refuses the arrival
-- outright.  Every other reading -- another operator's state, a
-- mismatched element type, no node -- is the collapse, and naming the
-- collapse is what lets the relation's fallback carry a side condition
-- instead of standing free at every state.
consumeUsable : ∀ {n} {Γ : Ctx n} → AllOp → (u : Ty) → Maybe (NodeState Γ) → Bool
consumeUsable mergeAllᵒ u (just (mergeAll-st {w} _ _ _ _)) = ⌊ w ≟ᵗ u ⌋
consumeUsable switchᵒ   u (just (switch-st _ _))           = true
consumeUsable exhaustᵒ  u (just (exhaust-st false _))      = true
consumeUsable _         _ _                                = false

-- THE OUTER HAS FINISHED, RECORDED AND NOTHING ELSE.  An `*All`
-- outlives its outer for exactly as long as something is still
-- running under it, so what this does is set the bit; whether the
-- operator is now finished is a READING of the store, and the reading
-- is `allFinished` below.  Splitting the two is not tidiness: between
-- the write and the question a lane can be drained and refilled, so a
-- verdict computed at the write is a verdict about a store that no
-- longer stands.
markOuterDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → AllOp → NodeId → EvalSt e → EvalSt e
markOuterDone mergeAllᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q _) =
      record st { nodes = setNode nid (mergeAll-st lim act q true) (EvalSt.nodes st) }
... | _ = st
markOuterDone switchᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur _) =
      record st { nodes = setNode nid (switch-st cur true) (EvalSt.nodes st) }
... | _ = st
markOuterDone exhaustᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act _) =
      record st { nodes = setNode nid (exhaust-st act true) (EvalSt.nodes st) }
... | _ = st

-- AN INNER HAS FINISHED, WHICH FREES ITS LANE.  The merge drops its
-- live count; the switch clears the current inner only if this IS the
-- current one, so a late death from an already-replaced inner clears
-- nothing; the exhaust clears its flag whatever it said, since
-- clearing it is the whole point.  What a merge then does with a freed
-- lane and a nonempty queue is the relation's, because draining one
-- means SUBSCRIBING -- which is also why no verdict is returned here:
-- the question is asked after the drain, of the store the drain left.
markInnerDone : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → AllOp → NodeId → NodeId → EvalSt e → EvalSt e
markInnerDone mergeAllᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) =
      record st { nodes = setNode nid (mergeAll-st lim (pred act) q od) (EvalSt.nodes st) }
... | _ = st
markInnerDone switchᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st (just c) od) =
      if c ≡ᵇ inst
      then record st { nodes = setNode nid (switch-st nothing od) (EvalSt.nodes st) }
      else st
... | _ = st
markInnerDone exhaustᵒ nid inst st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st _ od) =
      record st { nodes = setNode nid (exhaust-st false od) (EvalSt.nodes st) }
... | _ = st

-- THE QUEUE, TAKEN OUT WHOLE AND LEFT EMPTY BEHIND.  A drain
-- subscribes, and subscribing runs arbitrary user code that can park
-- FURTHER inners on this same node, so a drain that read the queue one
-- head at a time out of the store would be walking a list the walk
-- itself extends -- with nothing decreasing.  Handing the queue over
-- bodily makes it an ORDINARY LIST the relation carries and recurses
-- on, and leaves the store's own queue holding exactly what arrived
-- DURING the drain, which is where it belongs: those arrivals are
-- later than everything being drained and must stay behind them.
-- Only a merge has a queue: a switch keeps none and an exhaust drops
-- rather than parks.
mergeAllQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
              → NodeId → EvalSt e → List (Val Γ (obs s)) × EvalSt e
mergeAllQueue {s = s} nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = [] , st
...   | yes refl =
        q , record st { nodes = setNode nid (mergeAll-st {t = s} lim act [] od)
                                        (EvalSt.nodes st) }
mergeAllQueue nid st | _ = [] , st

-- IS THERE A FREE LANE AT THIS NODE, RIGHT NOW.  Asked once per drain
-- step rather than computed at the top, because each subscribe fills a
-- lane and the inner it starts may die inside the same breath and free
-- it again.
mergeRoom : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → NodeId → EvalSt e → Bool
mergeRoom nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act _ _) = hasRoom lim act
... | _                              = false

-- THE LANE, CLAIMED.  Counted as filled BEFORE the subscribe, so an
-- inner that completes synchronously decrements a count that was
-- already raised -- which is the order `mergeMap` itself takes.
mergeAllClaim : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → NodeId → EvalSt e → EvalSt e
mergeAllClaim nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st lim act q od) =
      record st { nodes = setNode nid (mergeAll-st lim (suc act) q od)
                                  (EvalSt.nodes st) }
... | _ = st

-- WHAT THE DRAIN DID NOT REACH, PUT BACK IN FRONT.  A drain stops the
-- moment the lanes are full again, and the undrained tail is older
-- than anything parked while it ran, so it goes ahead of it.
mergeAllRestore : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
                → NodeId → List (Val Γ (obs s)) → EvalSt e → EvalSt e
mergeAllRestore {s = s} nid os st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = st
...   | yes refl =
        record st { nodes = setNode nid (mergeAll-st lim act (os ++ q) od)
                                    (EvalSt.nodes st) }
mergeAllRestore nid os st | _ = st

-- AND THE PARK, which is where a saturated merge puts an arriving
-- inner.  It queues the OBSERVABLE and not the inner's values, which
-- is what rxjs queues -- a lane that is full has not subscribed
-- anything, so there are no values to hold.
mergeAllPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             → NodeId → Val Γ (obs s) → EvalSt e → EvalSt e
mergeAllPark {s = s} nid o st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = st
...   | yes refl =
        record st { nodes = setNode nid (mergeAll-st lim act (q ++ o ∷ []) od)
                                    (EvalSt.nodes st) }
mergeAllPark nid o st | _ = st

-- IS THE OPERATOR FINISHED, READ OFF THE STORE AS IT NOW STANDS.  An
-- `*All` closes when its outer has closed AND nothing is left under
-- it, and both halves move while a cascade is running -- a drained
-- lane refills, an inner dies -- so the answer is a reading rather
-- than something a clause can carry.  A node that is not this
-- operator's reads as finished, which is the same stuck reading every
-- dispatch here takes: forward nothing, never a wrong read.
allFinished : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → AllOp → NodeId → EvalSt e → Bool
allFinished mergeAllᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (mergeAll-st _ act q od) = od ∧ (act ≡ᵇ 0) ∧ null q
... | _                             = true
allFinished switchᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od) = od ∧ is-nothing cur
... | _                       = true
allFinished exhaustᵒ nid st with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act od) = od ∧ not act
... | _                        = true

-- HAS THIS TAKE ALREADY CUT?  The count reaching zero is what severs
-- the registrations and emits the end, so a source completing AFTER
-- that must not emit a second one -- the chain is already closed, and
-- in rxjs an unsubscribed chain is silent.
takeSpent : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → NodeId → EvalSt e → Bool
takeSpent nid st with lookupNode nid (EvalSt.nodes st)
... | just (take-st zero) = true
... | _                   = false


-- a shared slot: identity IS the index, source toℕ i (a hot's
-- convention).  All reset options are false by definition: connect at
-- the first subscription (anchoring the def's colds at that tick),
-- never disconnect (an unobserved share still burns arrivals), and
-- latch completion forever — a post-completion subscriber sees only
-- an immediate close/complete, because completion is re-observable
-- and values are not
-- AND THE CONNECT BURST IS NO LONGER MARKED AS IT PASSES.  It used to
-- be retagged plumbing, so that the first subscriber's frames could
-- tell a share's own registrations (which survive it) from their own
-- and refuse to adopt them on a cut or a join.  That mark was a field
-- of the carrier; with the protocol in the values, a frame reads the
-- distinction off the registry it already consults.

-- Latch completion AND mark the share dying, so that a cut landing
-- mid-fan-out can tell a share that has already finished from one
-- still running; the registry entries drop at shareFinish.
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
-- also marked dying, so a chain that has already spent this
-- source's final delivery is not asked for another; its registry
-- entries drop at cascadeFinish.  Colds and
-- deferᵉ hops get latched too, harmlessly: their sources are
-- per-subscription, never re-subscribed
cascadeLatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             → Arrival Γ → Sched Γ → EvalSt e → EvalSt e
cascadeLatch a sched st₀ =
  record (if Arrival.isLast a
          then record st₀ { completedSources = arrSource a ∷ EvalSt.completedSources st₀ }
          else st₀)
    { delivered = [] ; cancelled = []
    ; dying = if Arrival.isLast a then arrSource a ∷ [] else [] }

-- the spent source's registrations drop at the end, and the sweep
-- collects its live entry
cascadeFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Arrival Γ → Sched Γ → EvalSt e → Sched Γ × EvalSt e
cascadeFinish a sched′ st′ with Arrival.isLast a
... | false = sched′ , st′
... | true  =
      let kept = dropSource (arrSource a) (EvalSt.registry st′)
      in record sched′ { live = sweepLive kept (Sched.live sched′) } ,
         record st′ { registry = kept }
