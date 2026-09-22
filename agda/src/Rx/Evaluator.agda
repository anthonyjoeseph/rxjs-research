module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; _+_; _<ᵇ_; _≡ᵇ_; _≤_)
open import Data.Nat.Properties using (≤-trans)
open import Data.List    using (List; []; _∷_; _++_; map; concat; tabulate; null)
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

-- A BURST IS EVERYTHING ONE INCOMING EMIT CAUSES, AND IT IS THE UNIT A
-- SUBSCRIBE HANDS BACK.  A subscription returns its whole output at
-- once, so an operator bracketing the subscribe call sees a LIST at the
-- moment of grouping and needs no bit recording which side of that call
-- it is on -- which is the one thing a per-value descent has to carry
-- and this one does not.
Burst : ∀ {n} → Ctx n → Ty → Set
Burst Γ t = List (PlainEvent (Val Γ t))

Stream : ∀ {n} → Ctx n → Ty → Set          -- bursts, in canonical order
Stream Γ t = List (Burst Γ t)

-- AN ORDERED ANSWER, AND THE ORDER IS THE WHOLE POINT.  Subscribing
-- can hand values back at the element type AND send bursts straight to
-- the root, and which of the two came first is a property of the
-- PROGRAM rather than of the carrier: the oracle's exchanged pair
-- carries the same values out of a flattener and out of a share, and
-- rxjs answers `[7,1,2]` one way round and `[1,2,7]` the other.  So no
-- fixed rule for reading a group beside a stream can be right, and the
-- order goes into the answer -- one segment per subscribe that
-- contributed, in the order they ran.
VSegs : ∀ {n} → Ctx n → Ty → Ty → Set
VSegs Γ u t = List (List (Val Γ u) × Stream Γ t)

-- THE ONE-SEGMENT ANSWER, which is what every former that cannot reach
-- the root produces and is the shape this carrier widened from.  A
-- reading of the tree that only ever meets these is reading the case
-- the exchanged pair does not separate.
oneVSeg : ∀ {n} {Γ : Ctx n} {u t} → List (Val Γ u) → VSegs Γ u t
oneVSeg vs = (vs , []) ∷ []

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

-- THREE OF THE SIX ARMS CARRY A PAYLOAD, AND THAT CENSUS IS WHAT THE
-- REDUCIBILITY FACE IS ACTUALLY WAITING ON.  A candidate defined by
-- recursion on the type says nothing about what a NODE HOLDS, so every
-- arm of `Rx.Evaluator.Reducible` that reads a node back is owed a
-- store invariant -- but only where the read produces a VALUE.  Here
-- `cell-st` holds one outright, `mergeAll-st`'s queue holds observable
-- values and `batchSync-st`'s buffer holds the group it is assembling;
-- `take-st`, `switch-st` and `exhaust-st` hold a count, an
-- identifier and two flags, and nothing that leaves a frame dispatching
-- on those came from anywhere but the burst that arrived.  So three of
-- the arms need no carrier at all, and the three that do differ in
-- cost: a queue entry's reducibility arrives from the hypothesis that
-- admitted it, an accumulator's is folded by the operator's own
-- function and has no such source, and the bracket's buffer is read
-- back at a boundary no hypothesis reaches, so that one is closed by
-- the values face, which is total.
--
-- THE QUEUE IS READ BACK AT SUCH A BOUNDARY TOO, so its cost is the
-- buffer's and not the cheap one.  The hypothesis that admitted an
-- entry belongs to a subscribe, and the read is the DRAIN, which hangs
-- off an inner's completion and can fall in any later tick -- so
-- nothing but the store itself crosses from one to the other, and the
-- store may not carry a claim.  Two of the three arms are therefore
-- closed by the values face and one by an invariant nobody has, which
-- is the opposite of the split this census first drew.
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
  batchSync-st : ∀ {s} → (sync : Bool) (burst : List (Val Γ s))
                 (srcDone : Bool) → NodeState Γ
               -- THE BIT, THE BUFFER, AND THE HELD COMPLETION -- BECAUSE
               -- THE GROUP IS CUT AT THE SUBSCRIBE BOUNDARY AND NOT AT A
               -- BURST.  A burst is what ONE incoming emit caused, and a
               -- share hands its subscribers one value per fan-out step,
               -- so the values a subscribe call produces are spread over
               -- as many bursts as the share had values: reading the
               -- group off whatever burst a frame happens to be stepping
               -- gives one group per value where the bracket wants one
               -- group.  So the frame accumulates while the bit is up and
               -- emits nothing, and the boundary flushes.
               --
               -- AND THE COMPLETION IS HELD FOR THE SAME REASON.  The
               -- flush leaves AFTER everything the source did
               -- synchronously, so a source that also ended synchronously
               -- would end the stream before its own group left.  The bit
               -- rides here and is re-emitted with the group.
               --
               -- The buffer's element type is existential, so every read
               -- pays a `_≟ᵗ_`.

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
  _↠[_]_     : ∀ {lo ℓ s u t} → Frame Γ s u → lo ≤ ℓ → Path Γ ℓ u t → Path Γ lo s t
               -- THE CONS RELAXES THE FLOOR, AND THAT IS WHAT LETS A
               -- FLATTENER KEEP ITS OWN.  The index is a LOWER bound on
               -- the path's sinks, so a tail standing at `ℓ` inhabits
               -- every `lo ≤ ℓ` and the relaxation is sound by itself.
               -- What it buys is that `lowerFloor` composes at the head
               -- instead of descending: a registration moves the OUTER
               -- floor, where the registry's measure reads it, and every
               -- floor further along survives the move.
               --
               -- It is the joining frames that need one to survive.  A
               -- flattener subscribes its inners at the floor where IT
               -- was written, and with one index for the whole path that
               -- floor is overwritten by whichever registration delivered
               -- the value -- a share's, which sees strictly fewer slots.
               -- The inner then meets `subs-floor` and ends dry instead
               -- of reading its input, which shows up as a silent program
               -- rather than as a scope error.  Every other frame builds
               -- with `≤-refl` and notices nothing.

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
lowerFloor le (f ↠[ h ] p)     = f ↠[ ≤-trans le h ] p

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
pathHasNode nid (f ↠[ _ ] p)  = any (_≡ᵇ nid) (frameNodes f) ∨ pathHasNode nid p

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

-- A SOURCE THAT LIVES AND DIES INSIDE ITS OWN SUBSCRIPTION BURST
-- (`ofᵉ`, `emptyᵉ`, `take 0`, a cold with no async tail): its values
-- and the end, as ONE burst, with nothing registered and nothing
-- scheduled.  It is pure, and that is the protocol leaving: the old
-- shape minted a source so an `init`/`close` pair had something to
-- name, and a plain carrier has neither event to carry.
oneShotBurst : ∀ {n} {Γ : Ctx n} {u} → List (Val Γ u) → Stream Γ u
oneShotBurst vals = (map valueᵖ vals ++ completeᵖ ∷ []) ∷ []

-- A source already spent before this subscription reached it — a
-- completed Subject, a share whose def has closed, or a slot the
-- registration's own floor test refuses.  The end, immediately.
spentBurst : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u
spentBurst = (completeᵖ ∷ []) ∷ []

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

-- SPLITTING A BURST INTO WHAT A FRAME STEPS AND WHAT IT REACTS TO.
-- A plain burst carries values and, at most, the end; the values are
-- what the frame transforms and the end is the `fin` bit threaded
-- alongside.  With the protocol out of the carrier there is no third
-- column: nothing has to be retagged across a payload type, because
-- nothing but a value carries one.
splitEvents : ∀ {n} {Γ : Ctx n} {u} → Burst Γ u → List (Val Γ u) × Bool
splitEvents []              = [] , false
splitEvents (valueᵖ v ∷ es) = let (vs , c) = splitEvents es in v ∷ vs , c
splitEvents (completeᵖ ∷ es) = let (vs , _) = splitEvents es in vs , true

splitBurst : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → List (Val Γ u) × Bool
splitBurst []         = [] , false
splitBurst (b ∷ bs) =
  let (vs  , c ) = splitEvents b
      (vs′ , c′) = splitBurst bs
  in vs ++ vs′ , c ∨ c′

-- THE SAME ORDERED ANSWER ONE LEVEL UP, WHERE A CONTRIBUTION IS A
-- STREAM RATHER THAN A VALUE LIST.  A subscribe hands its output back
-- as BURSTS, because the bracketing is what a `batchSync` downstream
-- reads off it, so a subscribe-side segment pairs a stream at `u` with
-- the stream that same contribution sent to the root.
Segs : ∀ {n} → Ctx n → Ty → Ty → Set
Segs Γ u t = List (Stream Γ u × Stream Γ t)

-- THE ONE-SEGMENT ANSWER, which is every subscribe that cannot reach
-- the root -- today that is all of them, since nothing on this side
-- mints a root emit until the connect is routed through the fan-out.
oneSeg : ∀ {n} {Γ : Ctx n} {u t} → Stream Γ u → Segs Γ u t
oneSeg bs = (bs , []) ∷ []

-- ONE OUTPUT BURST PER SEGMENT, WHICH IS WHERE A FLATTENER'S ORDER
-- SURVIVES THE PUSH -- AND WHERE THE BRACKETING CHANGES.  A push used
-- to answer one burst per INPUT burst, concatenating every segment's
-- values into it, which collapses two inners delivered in the same
-- burst.  That is exactly the exchanged pair's shape, so keeping them
-- apart costs them a burst each.
--
-- THE COMPLETION RIDES THE LAST SEGMENT, which is the reading closest
-- to the one burst this used to answer: at one segment the answer is
-- the old one term for term, so the only shapes that move are the ones
-- the split is for.  A drain is what still answers at several.
stepSegs : ∀ {n} {Γ : Ctx n} {u t} → VSegs Γ u t → Bool → Segs Γ u t
stepSegs [] fin =
  ((if fin then completeᵖ ∷ [] else []) ∷ [] , []) ∷ []
stepSegs ((vs , rs) ∷ []) fin =
  ((map valueᵖ vs ++ (if fin then completeᵖ ∷ [] else [])) ∷ [] , rs) ∷ []
stepSegs ((vs , rs) ∷ s ∷ ss) fin =
  (map valueᵖ vs ∷ [] , rs) ∷ stepSegs (s ∷ ss) fin

-- RESOLVING AT THE TOP, WHERE BOTH COLUMNS ARE ALREADY AT `t` AND
-- RESOLVING IS CONCATENATING.  Root stream before value stream within
-- one segment, which is the rule `foldVSegs⇓` resolves by.  A
-- flattener's step is what fills the root component, and it is the
-- frame the two readings disagree on.
resolveSegs : ∀ {n} {Γ : Ctx n} {t} → Segs Γ t t → Stream Γ t
resolveSegs []               = []
resolveSegs ((bs , rs) ∷ ss) = rs ++ bs ++ resolveSegs ss

hasComplete : ∀ {n} {Γ : Ctx n} {u} → Burst Γ u → Bool
hasComplete = any isFinᵖ
  where isFinᵖ : ∀ {A : Set} → PlainEvent A → Bool
        isFinᵖ (valueᵖ _) = false
        isFinᵖ completeᵖ  = true

burstCompleted : ∀ {n} {Γ : Ctx n} {u} → Stream Γ u → Bool
burstCompleted = any hasComplete

-- WHETHER A SEGMENTED ANSWER ENDED, WHICH IS THE ONE QUESTION THAT
-- MAY BE ASKED ACROSS SEGMENTS.  A completion is somewhere or nowhere
-- and reading it back tells you nothing about order, so this is not
-- the seam `vsegVals` is -- and it is stated as a predicate rather
-- than a flattening so that no ordered answer is handed out.
segsCompleted : ∀ {n} {Γ : Ctx n} {u t} → Segs Γ u t → Bool
segsCompleted = any (λ sg → burstCompleted (proj₁ sg))

-- DROPPING ONE LEVEL OF BRACKETING AND NOTHING ELSE.  A flattener's
-- inner is subscribed and its answer walked by a frame that wants
-- VALUES, not bursts; the segments and their root columns survive
-- one for one, so this is a change of what a segment CARRIES and
-- never of how many there are or what order they are in.
segVSegs : ∀ {n} {Γ : Ctx n} {u t} → Segs Γ u t → VSegs Γ u t
segVSegs = map (λ sg → proj₁ (splitBurst (proj₁ sg)) , proj₂ sg)

-- THE PER-FRAME SEMANTICS, AND EVERY ONE OF THEM TAKES A BURST.  A
-- subscription hands its whole output back at once, so what arrives
-- at a frame is a LIST of values that a single incoming emit caused —
-- which is exactly what an rxjs operator sees inside one synchronous
-- turn, and is why the bracket below needs no buffer.  The threaded
-- Bool is "this stream completes as part of THIS burst": raised by a
-- spent source or a take's cut, absorbed by the `*All` frames, turned
-- into a `completeᵖ` only at the root.
--
-- Missing or mistyped node state — impossible by the subscription
-- invariant — degrades to forwarding NOTHING, never to a wrong read.

-- take's emission split: pass through up to the remaining budget,
-- reporting the new remaining count and whether this burst hit the
-- limit.  Real `take` cuts MID-BURST rather than waiting for the burst
-- to finish, which is what the third component says and what the
-- dispatch below acts on.
takeVals : ∀ {n} {Γ : Ctx n} {s} → ℕ → List (Val Γ s) → List (Val Γ s) × ℕ × Bool
takeVals zero          _        = [] , zero , false
takeVals (suc k)       []       = [] , suc k , false
takeVals (suc zero)    (v ∷ _)  = v ∷ [] , zero , true
takeVals (suc (suc k)) (v ∷ vs) =
  let (out , rem , didCut) = takeVals (suc k) vs in v ∷ out , rem , didCut

-- take's whole step.  Non-cut passes the budgeted prefix through and
-- threads the remaining count; the cut exhausts the budget, forces the
-- end, and severs the registrations threaded through this node.
takeDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
             → NodeId → List (Val Γ s) → Bool → Sched Γ → EvalSt e
             → Maybe (NodeState Γ)
             → List (Val Γ s) × Bool × Sched Γ × EvalSt e
takeDispatch nid vals fin sched st (just (take-st k)) =
  if proj₂ (proj₂ (takeVals k vals))
  then (let (kept , cutRids) = cutThrough nid (EvalSt.registry st)
        in proj₁ (takeVals k vals) , true ,
           record sched { live = sweepLive kept (Sched.live sched) } ,
           record st { registry = kept
                     ; cancelled = cutRids ++ EvalSt.cancelled st
                     ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) })
  else (proj₁ (takeVals k vals) , fin , sched ,
        record st { nodes = setNode nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                                      (EvalSt.nodes st) })
takeDispatch nid vals fin sched st _ = [] , fin , sched , st

-- scan's per-value fold: one running output per input, threading the
-- accumulator.  Its output IS its carried state, which is what rxjs's
-- `scan` is and why the seed lives in the cell rather than in the type.
scanVals : ∀ {n} {Γ : Ctx n} {s u} → FnClo Γ (u ×ᵗ s) u
         → Val Γ u → List (Val Γ s) → List (Val Γ u) × Val Γ u
scanVals fn ac []       = [] , ac
scanVals fn ac (v ∷ vs) =
  let ac′           = applyClo fn (ac , v)
      (outs , last) = scanVals fn ac′ vs
  in ac′ ∷ outs , last

-- THE SCAN'S WHOLE STEP, AS ONE FUNCTION OF WHAT THE NODE HOLDS.  A
-- fold that finds no accumulator of its own element type emits nothing
-- and writes nothing.  Stating it as a function rather than as two
-- constructors is what stops a prover choosing the empty reading at a
-- node that really does hold an accumulator: the relation then has one
-- arm and no arm to prefer.
scanDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
             → FnClo Γ (u ×ᵗ s) u → NodeId → List (Val Γ s) → Bool
             → Sched Γ → EvalSt e → Maybe (NodeState Γ)
             → List (Val Γ u) × Bool × Sched Γ × EvalSt e
scanDispatch {u = u} fn nid vals fin sched st (just (cell-st {w} a))
  with w ≟ᵗ u
... | no  _    = [] , fin , sched , st
... | yes refl =
      proj₁ (scanVals fn a vals) , fin , sched ,
      record st { nodes = setNode nid (cell-st (proj₂ (scanVals fn a vals)))
                                  (EvalSt.nodes st) }
scanDispatch fn nid vals fin sched st _ = [] , fin , sched , st

-- THE BRACKET, AND THE GROUP IS THE WHOLE SUBSCRIBE CALL.  While the
-- bit is up everything that arrived leaves as ONE value carrying all
-- of it, head and tail, so the result is nonempty by construction and
-- needs no `Ty` former of its own; an empty accumulation produces no
-- value at all rather than an empty group, which is what the
-- TypeScript does when its burst array comes back empty.  Once the bit
-- is down every value leaves as its own group of one.  That is the
-- TypeScript's `isSync` exactly, and it is the whole of what a plain
-- operator may know about synchrony.
batchVals : ∀ {n} {Γ : Ctx n} {s} → Bool → List (Val Γ s)
          → List (Val Γ (s ×ᵗ listᵗ s))
batchVals _     []       = []
batchVals true  (v ∷ vs) = (v , vs) ∷ []
batchVals false (v ∷ vs) = (v , []) ∷ batchVals false vs

-- WHILE THE BIT IS UP THE FRAME EMITS NOTHING AND WRITES EVERYTHING,
-- WHICH IS THE WHOLE OF THE GROUPING RULE.  The completion goes into
-- the buffer beside the values and is withheld downstream with them,
-- so a source that ends inside the subscribe call cannot end the
-- stream ahead of its own group.  A bracket that finds no buffer of
-- its own element type emits nothing and writes nothing.
batchDispatch : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
              → NodeId → List (Val Γ s) → Bool → Sched Γ → EvalSt e
              → Maybe (NodeState Γ)
              → List (Val Γ (s ×ᵗ listᵗ s)) × Bool × Sched Γ × EvalSt e
batchDispatch {s = s} nid vals fin sched st (just (batchSync-st {w} true bur done))
  with w ≟ᵗ s
... | no  _    = [] , fin , sched , st
... | yes refl =
      [] , false , sched ,
      record st { nodes = setNode nid (batchSync-st true (bur ++ vals) (done ∨ fin))
                                  (EvalSt.nodes st) }
batchDispatch nid vals fin sched st (just (batchSync-st false _ _)) =
  batchVals false vals , fin , sched , st
batchDispatch nid vals fin sched st _ = [] , fin , sched , st

-- THE BOUNDARY, WHERE THE BIT GOES DOWN AND THE GROUP LEAVES.  This is
-- the TypeScript's second `defer`: it runs once the source's subscribe
-- call has returned, hands back the one group the call accumulated and
-- the completion it withheld, and is what the whole buffer exists for.
-- `stepSegs` is what assembles it, so the flush is bracketed exactly
-- as any other frame step's answer is.
-- WHAT THE BUFFER HOLDS, GROUPED, AND THE COMPLETION BESIDE IT.  It is
-- split from the assembly below so that the `_≟ᵗ_` every read of the
-- buffer pays sits under a `with` of its OWN: a `with` in the assembly
-- blocks the reduction the reducibility face has to see through, and
-- that face then owes an inversion of `Val` rather than a value list.
batchBuf : ∀ {n} {Γ : Ctx n} (s : Ty) → Maybe (NodeState Γ)
         → List (Val Γ (s ×ᵗ listᵗ s)) × Bool
batchBuf s (just (batchSync-st {w} _ bur done)) with w ≟ᵗ s
... | no  _    = [] , done
... | yes refl = batchVals true bur , done
batchBuf s _ = [] , false

batchClose : ∀ {n} {Γ : Ctx n} {t} (s : Ty) → Maybe (NodeState Γ)
           → Segs Γ (s ×ᵗ listᵗ s) t
batchClose {t = t} s m =
  stepSegs {u = s ×ᵗ listᵗ s} {t = t}
    (oneVSeg {u = s ×ᵗ listᵗ s} {t = t} (proj₁ (batchBuf s m)))
    (proj₂ (batchBuf s m))

-- WHAT A MERGE'S DRAIN RE-READS BETWEEN SPENDS.  rxjs's buffer is one
-- mutable array and the loop `shift`s it, so a drain that re-enters
-- mid-spend -- a shared inner reporting its death through the registry
-- while its own subscribe is still running -- walks the SAME array and
-- no item is subscribed twice.  Carrying the tail instead gives each
-- drain its own copy of it, which is how both spend it.  A node that is
-- gone, or is holding another shape, reads as a spent queue with no
-- room, so the drain stops there rather than inventing one.
drainSt : ∀ {n} {Γ : Ctx n} (s : Ty) → Maybe (NodeState Γ)
        → Maybe ℕ × ℕ × List (Val Γ (obs s)) × Bool
drainSt s (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ s
... | no  _    = just 0 , 0 , [] , false
... | yes refl = lim , act , q , od
drainSt s _ = just 0 , 0 , [] , false

-- a from-inner completion is absorbed iff some registration under this inner
-- instance is still live: its path threads `inst`, it is not cancelled, and it
-- is not an already-delivered dying-source chain.
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
-- outright.  Every other reading is the collapse, and naming the
-- collapse is what lets the relation's fallback carry a side condition
-- instead of standing free at every state.
consumeUsable : ∀ {n} {Γ : Ctx n} → AllOp → (u : Ty) → Maybe (NodeState Γ) → Bool
consumeUsable mergeAllᵒ u (just (mergeAll-st {w} _ _ _ _)) = ⌊ w ≟ᵗ u ⌋
consumeUsable switchᵒ   u (just (switch-st _ _))           = true
consumeUsable exhaustᵒ  u (just (exhaust-st false _))      = true
consumeUsable _         _ _                                = false

-- AND THE SAME QUESTION ON THE WAY BACK UP, WHERE AN INNER HAS DIED
-- AND ITS OPERATOR HAS TO FINISH IT.  A merge finishes against its own
-- node at its own element type, because that is the queue it drains; a
-- switch finishes only the inner it currently believes is running, so
-- a late death from an already-replaced inner clears nothing; an
-- exhaust finishes against its own node whatever the running flag
-- says, since clearing it is the whole point.
finishUsable : ∀ {n} {Γ : Ctx n} → AllOp → (s : Ty) → NodeId
             → Maybe (NodeState Γ) → Bool
finishUsable mergeAllᵒ s inst (just (mergeAll-st {w} _ _ _ _)) = ⌊ w ≟ᵗ s ⌋
finishUsable switchᵒ   s inst (just (switch-st (just c) _))    = c ≡ᵇ inst
finishUsable exhaustᵒ  s inst (just (exhaust-st _ _))          = true
finishUsable _         _ _    _                                = false

-- THE OUTER HAS FINISHED, RECORDED AND READ BACK IN ONE BREATH.  An
-- `*All` outlives its outer for exactly as long as something is still
-- running under it, so the bit is written and the verdict is a READING
-- of the store as it then stands — a lane can be drained and refilled
-- while the outer's own burst is still being walked, so a verdict
-- computed before the write is a verdict about a store that no longer
-- holds.
thruWrap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → AllOp → NodeId → Bool
         → Sched Γ × EvalSt e
         → Bool × Sched Γ × EvalSt e
thruWrap op nid false (sched′ , st′) = false , sched′ , st′
thruWrap mergeAllᵒ nid true (sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (mergeAll-st lim act q _) =
      (act ≡ᵇ 0) ∧ null q , sched′ ,
      record st′ { nodes = setNode nid (mergeAll-st lim act q true) (EvalSt.nodes st′) }
... | _ = true , sched′ , st′
thruWrap switchᵒ nid true (sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (switch-st cur _) =
      is-nothing cur , sched′ ,
      record st′ { nodes = setNode nid (switch-st cur true) (EvalSt.nodes st′) }
... | _ = true , sched′ , st′
thruWrap exhaustᵒ nid true (sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (exhaust-st act _) =
      not act , sched′ ,
      record st′ { nodes = setNode nid (exhaust-st act true) (EvalSt.nodes st′) }
... | _ = true , sched′ , st′


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

-- Mark the share dying, so that a cut landing mid-fan-out can tell a
-- share that has already finished from one still running; the registry
-- entries drop at shareFinish.
--
-- DYING IS SET BEFORE THE FAN-OUT AND COMPLETION IS LATCHED BETWEEN THE
-- VALUES AND THE END, and the three have to be separated because a
-- fan-out's own values create subscribers.  A share whose definition
-- completes with its values reaches here with `fin` already true, so a
-- latch taken first makes `slot-spent` the arm every re-entrant
-- subscription lands on -- the share reads as finished to the very
-- values that have not been delivered yet.  rxjs's subject is not
-- complete until after the last `next`, and a joiner arriving between
-- two of them receives the rest.  Where the latch does belong is
-- `shareSpend`.
shareDying : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → (i : Fin n) → Bool → EvalSt e → EvalSt e
shareDying i false st₀ = st₀
shareDying i true  st₀ = record st₀ { dying = toℕ i ∷ EvalSt.dying st₀ }

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

-- THE END IS DELIVERED WITH THE SHARE ALREADY CLOSED.  rxjs's subject
-- sets `isStopped` inside `complete()` BEFORE it iterates its
-- observers, so a subscription created by the completion's own fan-out
-- -- a flattener whose lane that very completion freed, subscribing the
-- source it had queued behind it -- finds the subject closed and takes
-- an immediate complete.  Latched after the fan-out instead, that
-- joiner registers on a source that will never speak again, its own
-- answer carries no end, and it holds the flattener's lane forever, so
-- everything queued behind it is lost.  The VALUES' half of the order
-- is the opposite and is argued at `shareDying`; the registry drop
-- stays last, at `shareFinish`.
shareSpend : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → (i : Fin n) → EvalSt e → EvalSt e
shareSpend i st₀ =
  record st₀ { completedSources = toℕ i ∷ EvalSt.completedSources st₀ }

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
-- this cascade and owe nothing).  THE SOURCE IS NOT CLOSED HERE, AND
-- THAT IS THE WHOLE OF THE DIFFERENCE BETWEEN THE TWO PASSES.  A
-- subject is open for the whole of its `next`, so a chain that
-- subscribes to this very source while its value is being delivered —
-- a flattener's inner, a shared def connecting — must find it LIVE and
-- get a live subscription.  Closing it up front hands that subscriber
-- an immediate completion instead, which an `exhaustAll` reads as its
-- lane freeing and a `take` reads as its source ending.
cascadeOpen : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → EvalSt e
cascadeOpen st₀ =
  record st₀ { delivered = [] ; cancelled = [] ; dying = [] }

-- closes it, BETWEEN the two passes: the spent source is latched
-- completed before its completion fans out, so a subscriber joining
-- from here on sees the one-shot close; it is also marked dying, so a
-- chain that has already spent this source's final delivery is not
-- asked for another; its registry entries drop at cascadeFinish.
-- `delivered` restarts because the end pass is its own walk over the
-- chains and `dying` is read against it; `cancelled` does NOT, because
-- a chain cut during the value pass stays cut.  Colds and deferᵉ hops
-- get latched too, harmlessly: their sources are per-subscription,
-- never re-subscribed
cascadeClose : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             → Arrival Γ → EvalSt e → EvalSt e
cascadeClose a st₁ =
  record st₁ { completedSources = arrSource a ∷ EvalSt.completedSources st₁
             ; delivered = []
             ; dying = arrSource a ∷ [] }

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
