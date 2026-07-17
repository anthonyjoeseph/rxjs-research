module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _<ᵇ_; _≡ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; map; concat; tabulate; any; null)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Tick; Fuel; Ordinal; Id; freshId; Source;
                           Timed; after_,_; ObservableInput; hot; cold;
                           InstEvent; init; value; close; complete;
                           InstEmit; _at_from_)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; _≟ᵗ_; Ctx; Val; Closed; Fn;
                           applyFn; evalTm; unfoldμ;
                           input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                           mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                           μᵉ; varᵉ; deferᵉ)


------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

-- slot i of Γ is either an external SCRIPTED input (hot/cold) or a
-- SHARED observable: an exp tree with an implicit all-resets-false
-- share() at its root.  Share identity is the de Bruijn index — the
-- binding, not the expression, exactly as a JS `const`.  Defs must
-- reference only strictly earlier slots (a const telescope) — checked
-- by the generator/decoder, not by these types; a forward reference
-- would diverge at connect time
data Slot {n} (Γ : Ctx n) (t : Ty) : Set where
  scripted : ObservableInput (Val Γ t) → Slot Γ t
  shared   : Closed Γ t → Slot Γ t

Slots : ∀ {n} → Ctx n → Set
Slots Γ = ∀ i → Slot Γ (lookup Γ i)

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

arrOrd : ∀ {n} {Γ : Ctx n} → Arrival Γ → Ordinal
arrOrd = Arrival.ordinal

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
-- at subscription time, minting from nextSource/nextOrdinal
sched-init : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Sched Γ
sched-init {n = n} {Γ = Γ} e ins = record
  { nextOrdinal = n ; nextSource = n ; nextNode = 0
  ; live = concat (tabulate mkHot) ; slots = ins }
  where
  mkHot : Fin n → List (LiveSource Γ)
  mkHot i with ins i
  ... | scripted (hot async) = record { source = toℕ i ; ordinal = toℕ i
                                      ; elemTy = lookup Γ i ; pending = resolve 0 async } ∷ []
  ... | scripted (cold _ _)  = []
  ... | shared _             = []

-- pop the pending arrival minimal by (tick, ordinal), or report empty
sched-next : ∀ {n} {Γ : Ctx n} → Sched Γ → ⊤ ⊎ (Arrival Γ × Sched Γ)
sched-next {Γ = Γ} sched = finish (go (Sched.live sched))
  where
  earlier : Arrival Γ → Arrival Γ → Bool   -- ordinals are unique, so no tie survives
  earlier a a′ = (Arrival.tick a <ᵇ Arrival.tick a′)
               ∨ ((Arrival.tick a ≡ᵇ Arrival.tick a′) ∧ (Arrival.ordinal a <ᵇ Arrival.ordinal a′))

  headOf : LiveSource Γ → ⊤ ⊎ (Arrival Γ × LiveSource Γ)
  headOf l with LiveSource.pending l
  ... | []           = inj₁ tt
  ... | (t , v) ∷ ps =
        inj₂ ( record { tick = t ; ordinal = LiveSource.ordinal l
                      ; source = LiveSource.source l
                      ; elemTy = LiveSource.elemTy l ; payload = v
                      ; isLast = null ps }
             , record l { pending = ps } )

  go : List (LiveSource Γ) → ⊤ ⊎ (Arrival Γ × List (LiveSource Γ))
  go []       = inj₁ tt
  go (l ∷ ls) with headOf l | go ls
  ... | inj₁ _        | inj₁ _          = inj₁ tt
  ... | inj₁ _        | inj₂ (a′ , ls′) = inj₂ (a′ , l ∷ ls′)
  ... | inj₂ (a , l′) | inj₁ _          = inj₂ (a , l′ ∷ ls)
  ... | inj₂ (a , l′) | inj₂ (a′ , ls′) =
        if earlier a a′ then inj₂ (a , l′ ∷ ls) else inj₂ (a′ , l ∷ ls′)

  finish : ⊤ ⊎ (Arrival Γ × List (LiveSource Γ)) → ⊤ ⊎ (Arrival Γ × Sched Γ)
  finish (inj₁ _)        = inj₁ tt
  finish (inj₂ (a , ls)) = inj₂ (a , record sched { live = ls })

------------------------------------------------------------------
-- Node state
------------------------------------------------------------------

NodeId : Set          -- a node instance in the dynamic topology,
NodeId = ℕ            -- numbered in subscription order

data NodeState {n} (Γ : Ctx n) : Set where
  scan-st    : ∀ {t} → Val Γ t → NodeState Γ    -- current accumulator
  take-st    : ℕ → NodeState Γ                  -- emissions remaining
  merge-st   : (activeInners : ℕ) (outerDone : Bool) → NodeState Γ
  concat-st  : ∀ {t} → (queued : List (Closed Γ t)) (innerActive outerDone : Bool)
             → NodeState Γ
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

data AllOp : Set where
  mergeᵒ concatᵒ switchᵒ exhaustᵒ : AllOp

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
cutThrough : ∀ {n} {Γ : Ctx n} {t}
           → NodeId → List (Source × Chain Γ t)
           → List (Source × Chain Γ t) × List (InstEvent (Val Γ t))
cutThrough nid []              = [] , []
cutThrough nid ((src , c) ∷ r) with pathHasNode nid (proj₂ c) | cutThrough nid r
... | true  | kept , closes = kept , close src ∷ closes
... | false | kept , closes = (src , c) ∷ kept , closes

-- drop dead dynamic sources (no remaining registrations); hot input
-- slots (sources < n by convention) keep firing regardless, exactly
-- like a hot Subject with no subscribers
sweepLive : ∀ {n} {Γ : Ctx n} {t}
          → List (Source × Chain Γ t) → List (LiveSource Γ) → List (LiveSource Γ)
sweepLive {n = n} reg []       = []
sweepLive {n = n} reg (l ∷ ls) =
  if (LiveSource.source l <ᵇ n)
     ∨ any (λ p → sameSource (LiveSource.source l) (proj₁ p)) reg
  then l ∷ sweepLive reg ls
  else sweepLive reg ls

dropSource : ∀ {n} {Γ : Ctx n} {t}
           → Source → List (Source × Chain Γ t) → List (Source × Chain Γ t)
dropSource src []             = []
dropSource src ((s , c) ∷ r) =
  if sameSource src s then dropSource src r else (s , c) ∷ dropSource src r

record EvalSt {n} {Γ : Ctx n} {t} (e : Closed Γ t) : Set where
  field registry        : List (Source × Chain Γ t)   -- live registration chains, subscription order
        nodes           : NodeSt e
        connectedShares : List Source   -- shared slots whose def is live (connect happens once, ever)
        completedSources : List Source  -- the completion latch: completed shares AND spent
                                        -- scripted sources (a completed Subject re-delivers
                                        -- complete to late subscribers; values are not
                                        -- re-observable, completion is)

mintSource : ∀ {n} {Γ : Ctx n} → Sched Γ → Source × Sched Γ
mintSource sched =
  Sched.nextSource sched , record sched { nextSource = suc (Sched.nextSource sched) }

mintOrdinal : ∀ {n} {Γ : Ctx n} → Sched Γ → Ordinal × Sched Γ
mintOrdinal sched =
  Sched.nextOrdinal sched , record sched { nextOrdinal = suc (Sched.nextOrdinal sched) }

mintNode : ∀ {n} {Γ : Ctx n} → Sched Γ → NodeId × Sched Γ
mintNode sched =
  Sched.nextNode sched , record sched { nextNode = suc (Sched.nextNode sched) }

-- append: the registry stays in subscription order
register : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Source → Path Γ u t → EvalSt e → EvalSt e
register {u = u} src path st =
  record st { registry = EvalSt.registry st ++ (src , u , path) ∷ [] }

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
  in ((init src ∷ map value vals ++ close src ∷ complete ∷ [])
       at id from src) ∷ [] , sched₁

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
-- (stepFrame → subscribeInner → subscribeE).  TERMINATING because
-- Agda cannot see what keeps the sync work finite — runtime
-- observables are finite syntax, and every μ re-entry sits behind a
-- deferᵉ, i.e. costs a schedule hop; discharging this pragma
-- (well-founded recursion on term size) is proof-phase work, the
-- evaluator's one admitted gap
{-# TERMINATING #-}
subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
           → Closed Γ u → Path Γ u t → Id → Tick
           → Sched Γ → EvalSt e
           → Stream Γ u × Sched Γ × EvalSt e

st-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → EvalSt e
st-init e = record { registry = [] ; nodes = []
                   ; connectedShares = [] ; completedSources = [] }
  -- all populated by the root subscribeE and by lazy share connects

-- the arrival's source's live chains, in subscription order, at
-- exactly the arrival's element type: a chain is admitted only past a
-- Ty equality check, so no payload is ever read at the wrong type (a
-- mistyped registry entry — impossible by the registration invariant —
-- is dropped, never trusted)
chainsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → (a : Arrival Γ) → EvalSt e → List (Path Γ (arrTy a) t)
chainsOf {Γ = Γ} {t = t} {e = e} a st = go (EvalSt.registry st)
  where
  go : List (Source × Chain Γ t) → List (Path Γ (arrTy a) t)
  go [] = []
  go ((s , (u , p)) ∷ r) with sameSource (arrSource a) s | u ≟ᵗ arrTy a
  ... | false | _        = go r
  ... | true  | no  _    = go r
  ... | true  | yes refl = p ∷ go r

-- split a subscription burst into grafted values, retagged
-- bookkeeping events, and whether the inner completed synchronously
splitEvents : ∀ {n} {Γ : Ctx n} {u} {A : Set}
            → List (InstEvent (Val Γ u))
            → List (Val Γ u) × List (InstEvent A) × Bool
splitEvents []              = [] , [] , false
splitEvents (value v  ∷ es) = let (vs , bs , c) = splitEvents es in v ∷ vs , bs , c
splitEvents (init s   ∷ es) = let (vs , bs , c) = splitEvents es in vs , init s ∷ bs , c
splitEvents (close s  ∷ es) = let (vs , bs , c) = splitEvents es in vs , close s ∷ bs , c
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
-- current instant, split its burst
subscribeInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
               → AllOp → NodeId → Path Γ u t → Id → Tick
               → Val Γ (obs u) → Sched Γ → EvalSt e
               → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
subscribeInner op allNid κ id now o sched st =
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
stepFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Id → Tick → Frame Γ s u → Path Γ u t
          → List (Val Γ s) → Bool → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e

stepFrame id now (map-f fn) κ vals fin sched st =
  map (applyFn fn) vals , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} {u = u} id now (scan-f fn nid) κ vals fin sched st
  = dispatch (lookupNode nid (EvalSt.nodes st))
  where
  scanVals : Val Γ u → List (Val Γ s) → List (Val Γ u) × Val Γ u
  scanVals acc []       = [] , acc
  scanVals acc (v ∷ vs) =
    let acc′          = applyFn fn (acc , v)
        (outs , last) = scanVals acc′ vs
    in acc′ ∷ outs , last

  dispatch : Maybe (NodeState Γ)
           → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  dispatch (just (scan-st {w} acc)) with w ≟ᵗ u
  ... | yes refl =
        let (outs , acc′) = scanVals acc vals
        in outs , [] , fin , sched ,
           record st { nodes = setNode nid (scan-st acc′) (EvalSt.nodes st) }
  ... | no _ = [] , [] , fin , sched , st
  dispatch _ = [] , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} id now (take-f nid) κ vals fin sched st
  = dispatch (lookupNode nid (EvalSt.nodes st))
  where
  takeVals : ℕ → List (Val Γ s) → List (Val Γ s) × ℕ × Bool
  takeVals zero          _        = [] , zero , false
  takeVals (suc k)       []       = [] , suc k , false
  takeVals (suc zero)    (v ∷ _)  = v ∷ [] , zero , true
  takeVals (suc (suc k)) (v ∷ vs) =
    let (out , rem , cut) = takeVals (suc k) vs in v ∷ out , rem , cut

  dispatch : Maybe (NodeState Γ)
           → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  dispatch (just (take-st k)) with takeVals k vals
  ... | out , rem , false =
        out , [] , fin , sched ,
        record st { nodes = setNode nid (take-st rem) (EvalSt.nodes st) }
  ... | out , _   , true  =
        let (kept , closes) = cutThrough nid (EvalSt.registry st)
        in out , closes , true ,
           record sched { live = sweepLive kept (Sched.live sched) } ,
           record st { registry = kept
                     ; nodes = setNode nid (take-st zero) (EvalSt.nodes st) }
  dispatch _ = [] , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} id now (from-inner op allNid inst) κ vals fin sched st
  = react fin
  where
  -- the completing inner's flush already rode in on vals; here the
  -- *All absorbs the completion and reacts
  drain : List (Closed Γ s) → Sched Γ → EvalSt e
        → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × List (Closed Γ s) × Sched Γ × EvalSt e
  drain []       sched₀ st₀ = [] , [] , false , [] , sched₀ , st₀
  drain (o ∷ q) sched₀ st₀ =
    let (_ , vs , bs , done , sched₁ , st₁) = subscribeInner concatᵒ allNid κ id now o sched₀ st₀
    in if done
       then (let (vs′ , bs′ , act , q′ , sched₂ , st₂) = drain q sched₁ st₁
             in vs ++ vs′ , bs ++ bs′ , act , q′ , sched₂ , st₂)
       else (vs , bs , true , q , sched₁ , st₁)

  finish : AllOp → Maybe (NodeState Γ)
         → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  finish mergeᵒ (just (merge-st k od)) =
    vals , [] , od ∧ (pred k ≡ᵇ 0) , sched ,
    record st { nodes = setNode allNid (merge-st (pred k) od) (EvalSt.nodes st) }
  finish concatᵒ (just (concat-st {w} q act od)) with w ≟ᵗ s
  ... | yes refl =
        let (vs , bs , act′ , q′ , sched′ , st′) = drain q sched st
        in vals ++ vs , bs , od ∧ not act′ ∧ null q′ , sched′ ,
           record st′ { nodes = setNode allNid (concat-st q′ act′ od) (EvalSt.nodes st′) }
  ... | no _ = vals , [] , false , sched , st
  finish switchᵒ (just (switch-st (just c) od)) =
    if c ≡ᵇ inst
    then (vals , [] , od , sched ,
          record st { nodes = setNode allNid (switch-st nothing od) (EvalSt.nodes st) })
    else (vals , [] , false , sched , st)
  finish exhaustᵒ (just (exhaust-st act od)) =
    vals , [] , od , sched ,
    record st { nodes = setNode allNid (exhaust-st false od) (EvalSt.nodes st) }
  finish _ _ = vals , [] , false , sched , st

  react : Bool → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  react false = vals , [] , false , sched , st
  react true  = finish op (lookupNode allNid (EvalSt.nodes st))

stepFrame {Γ = Γ} {t = t} {e = e} {u = u} id now (thru-outer mergeᵒ nid) κ vals fin sched st
  = wrap fin (walk vals sched st)
  where
  bump : Bool → NodeSt e → NodeSt e
  bump done ns with lookupNode nid ns
  ... | just (merge-st k od) = setNode nid (merge-st (if done then k else suc k) od) ns
  ... | _                    = ns

  walk : List (Val Γ (obs u)) → Sched Γ → EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  walk []       sched₀ st₀ = [] , [] , sched₀ , st₀
  walk (o ∷ os) sched₀ st₀ =
    let (_ , vs , bs , done , sched₁ , st₁) = subscribeInner mergeᵒ nid κ id now o sched₀ st₀
        st₂ = record st₁ { nodes = bump done (EvalSt.nodes st₁) }
        (vs′ , bs′ , sched₂ , st₃) = walk os sched₁ st₂
    in vs ++ vs′ , bs ++ bs′ , sched₂ , st₃

  wrap : Bool → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  wrap false (vs , bs , sched′ , st′) = vs , bs , false , sched′ , st′
  wrap true  (vs , bs , sched′ , st′) with lookupNode nid (EvalSt.nodes st′)
  ... | just (merge-st k _) =
        vs , bs , (k ≡ᵇ 0) , sched′ ,
        record st′ { nodes = setNode nid (merge-st k true) (EvalSt.nodes st′) }
  ... | _ = vs , bs , true , sched′ , st′

stepFrame {Γ = Γ} {t = t} {e = e} {u = u} id now (thru-outer concatᵒ nid) κ vals fin sched st
  = wrap fin (walk vals sched st)
  where
  consume : Val Γ (obs u) → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  consume o sched₀ st₀ with lookupNode nid (EvalSt.nodes st₀)
  consume o sched₀ st₀ | just (concat-st {w} q true od) with w ≟ᵗ u
  consume o sched₀ st₀ | just (concat-st {w} q true od) | yes refl =
    [] , [] , sched₀ ,
    record st₀ { nodes = setNode nid (concat-st (q ++ o ∷ []) true od) (EvalSt.nodes st₀) }
  consume o sched₀ st₀ | just (concat-st {w} q true od) | no _ =
    [] , [] , sched₀ , st₀
  consume o sched₀ st₀ | just (concat-st q false od) =
    let (_ , vs , bs , done , sched₁ , st₁) = subscribeInner concatᵒ nid κ id now o sched₀ st₀
    in vs , bs , sched₁ ,
       record st₁ { nodes = setNode nid (concat-st {t = u} [] (not done) od) (EvalSt.nodes st₁) }
  consume o sched₀ st₀ | _ = [] , [] , sched₀ , st₀

  walk : List (Val Γ (obs u)) → Sched Γ → EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  walk []       sched₀ st₀ = [] , [] , sched₀ , st₀
  walk (o ∷ os) sched₀ st₀ =
    let (vs , bs , sched₁ , st₁) = consume o sched₀ st₀
        (vs′ , bs′ , sched₂ , st₂) = walk os sched₁ st₁
    in vs ++ vs′ , bs ++ bs′ , sched₂ , st₂

  wrap : Bool → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  wrap false (vs , bs , sched′ , st′) = vs , bs , false , sched′ , st′
  wrap true  (vs , bs , sched′ , st′) with lookupNode nid (EvalSt.nodes st′)
  ... | just (concat-st q act _) =
        vs , bs , not act ∧ null q , sched′ ,
        record st′ { nodes = setNode nid (concat-st q act true) (EvalSt.nodes st′) }
  ... | _ = vs , bs , true , sched′ , st′

stepFrame {Γ = Γ} {t = t} {e = e} {u = u} id now (thru-outer switchᵒ nid) κ vals fin sched st
  = wrap fin (walk vals sched st)
  where
  kill : Maybe NodeId → Sched Γ → EvalSt e
       → List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  kill nothing  sched₀ st₀ = [] , sched₀ , st₀
  kill (just v) sched₀ st₀ =
    let (kept , closes) = cutThrough v (EvalSt.registry st₀)
    in closes ,
       record sched₀ { live = sweepLive kept (Sched.live sched₀) } ,
       record st₀ { registry = kept }

  consume : Val Γ (obs u) → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  consume o sched₀ st₀ with lookupNode nid (EvalSt.nodes st₀)
  ... | just (switch-st cur od) =
        let (closes , sched₁ , st₁) = kill cur sched₀ st₀
            (inst , vs , bs , done , sched₂ , st₂) = subscribeInner switchᵒ nid κ id now o sched₁ st₁
        in vs , closes ++ bs , sched₂ ,
           record st₂ { nodes = setNode nid
             (switch-st (if done then nothing else just inst) od) (EvalSt.nodes st₂) }
  ... | _ = [] , [] , sched₀ , st₀

  walk : List (Val Γ (obs u)) → Sched Γ → EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  walk []       sched₀ st₀ = [] , [] , sched₀ , st₀
  walk (o ∷ os) sched₀ st₀ =
    let (vs , bs , sched₁ , st₁) = consume o sched₀ st₀
        (vs′ , bs′ , sched₂ , st₂) = walk os sched₁ st₁
    in vs ++ vs′ , bs ++ bs′ , sched₂ , st₂

  wrap : Bool → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  wrap false (vs , bs , sched′ , st′) = vs , bs , false , sched′ , st′
  wrap true  (vs , bs , sched′ , st′) with lookupNode nid (EvalSt.nodes st′)
  ... | just (switch-st cur _) =
        vs , bs , is-nothing cur , sched′ ,
        record st′ { nodes = setNode nid (switch-st cur true) (EvalSt.nodes st′) }
  ... | _ = vs , bs , true , sched′ , st′

stepFrame {Γ = Γ} {t = t} {e = e} {u = u} id now (thru-outer exhaustᵒ nid) κ vals fin sched st
  = wrap fin (walk vals sched st)
  where
  consume : Val Γ (obs u) → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  consume o sched₀ st₀ with lookupNode nid (EvalSt.nodes st₀)
  ... | just (exhaust-st true od)  = [] , [] , sched₀ , st₀   -- busy: drop
  ... | just (exhaust-st false od) =
        let (_ , vs , bs , done , sched₁ , st₁) = subscribeInner exhaustᵒ nid κ id now o sched₀ st₀
        in vs , bs , sched₁ ,
           record st₁ { nodes = setNode nid (exhaust-st (not done) od) (EvalSt.nodes st₁) }
  ... | _ = [] , [] , sched₀ , st₀

  walk : List (Val Γ (obs u)) → Sched Γ → EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
  walk []       sched₀ st₀ = [] , [] , sched₀ , st₀
  walk (o ∷ os) sched₀ st₀ =
    let (vs , bs , sched₁ , st₁) = consume o sched₀ st₀
        (vs′ , bs′ , sched₂ , st₂) = walk os sched₁ st₁
    in vs ++ vs′ , bs ++ bs′ , sched₂ , st₂

  wrap : Bool → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
       → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  wrap false (vs , bs , sched′ , st′) = vs , bs , false , sched′ , st′
  wrap true  (vs , bs , sched′ , st′) with lookupNode nid (EvalSt.nodes st′)
  ... | just (exhaust-st act _) =
        vs , bs , not act , sched′ ,
        record st′ { nodes = setNode nid (exhaust-st act true) (EvalSt.nodes st′) }
  ... | _ = vs , bs , true , sched′ , st′

-- bookkeeping crosses payload types freely — init/close/complete
-- carry none.  A value cannot cross and is dropped; the callers only
-- ever retag event lists that stepFrame produced, which are value-free
retagEvents : ∀ {A B : Set} → List (InstEvent A) → List (InstEvent B)
retagEvents []              = []
retagEvents (init s   ∷ es) = init s   ∷ retagEvents es
retagEvents (close s  ∷ es) = close s  ∷ retagEvents es
retagEvents (complete ∷ es) = complete ∷ retagEvents es
retagEvents (value _  ∷ es) = retagEvents es

-- push a child subscription's sync burst through the one frame just
-- built above it: split each emit, step it, reassemble under the same
-- envelope — the burst leaves each subscription level already shaped
-- like any later emit of its source
pushBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
          → Id → Tick → Frame Γ s u → Path Γ u t
          → Stream Γ s → Sched Γ → EvalSt e
          → Stream Γ u × Sched Γ × EvalSt e
pushBurst id now f κ []         sched st = [] , sched , st
pushBurst id now f κ (em ∷ ems) sched st =
  let (vals , bookkeeping , fin) = splitEvents (InstEmit.events em)
      (vals′ , evs , fin′ , sched₁ , st₁) = stepFrame id now f κ vals fin sched st
      (rest , sched₂ , st₂) = pushBurst id now f κ ems sched₁ st₁
  in ((bookkeeping ++ retagEvents evs ++ map value vals′
        ++ (if fin′ then complete ∷ [] else []))
       at InstEmit.instant em from InstEmit.source em) ∷ rest , sched₂ , st₂

-- the shared *All shape: mint the node, install its initial state,
-- subscribe the outer under a thru-outer frame, push the burst through
subscribeAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ u t
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
subscribeSharedSlot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
                    → (i : Fin n) → Closed Γ (lookup Γ i)
                    → Path Γ (lookup Γ i) t → Id → Tick
                    → Sched Γ → EvalSt e
                    → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
subscribeSharedSlot {Γ = Γ} {e = e} i d κ id now sched st =
  if memberSource (toℕ i) (EvalSt.completedSources st)
  then ((init (toℕ i) ∷ close (toℕ i) ∷ complete ∷ []) at id from toℕ i) ∷ []
       , sched , st
  else if memberSource (toℕ i) (EvalSt.connectedShares st)
  then -- live: join mid-flight, future values only
       ((init (toℕ i) ∷ []) at id from toℕ i) ∷ [] , sched , register (toℕ i) κ st
  else connect
  where
  connect : Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
  connect =
    let st₁ = register (toℕ i) κ
                (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
        (burst , sched₁ , st₂) = subscribeE d (share-sink i) id now sched st₁
        -- the def's connect burst flows up the first subscriber's own
        -- frames (the returned burst); dispatch only serves arrivals
    in if burstCompleted burst
       then -- the def died inside its own connect burst: latch, and
            -- this registration closes in the same instant
            (((init (toℕ i) ∷ close (toℕ i) ∷ []) at id from toℕ i) ∷ burst)
            , sched₁ ,
            record st₂ { registry = dropSource (toℕ i) (EvalSt.registry st₂)
                       ; completedSources = toℕ i ∷ EvalSt.completedSources st₂ }
       else ((init (toℕ i) ∷ []) at id from toℕ i) ∷ burst , sched₁ , st₂

subscribeE {Γ = Γ} (input i) κ id now sched st with Sched.slots sched i
... | shared d = subscribeSharedSlot i d κ id now sched st
... | scripted (hot _) =
      if memberSource (toℕ i) (EvalSt.completedSources st)
      then -- spent script: a completed Subject — immediate
           -- close/complete, nothing registered
           ((init (toℕ i) ∷ close (toℕ i) ∷ complete ∷ []) at id from toℕ i) ∷ []
           , sched , st
      else -- already live (sched-init, source = ordinal = toℕ i); just
           -- another registration — fan-out IS this multiplicity
           ((init (toℕ i) ∷ []) at id from toℕ i) ∷ [] , sched , register (toℕ i) κ st
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
      in ((init src ∷ map value sync) at id from src) ∷ [] , sched₃ ,
         register src κ st

subscribeE (ofᵉ ts) κ id now sched st =
  let (burst , sched₁) = oneShotBurst (map (λ tm → evalTm tm) ts) id sched
  in burst , sched₁ , st

subscribeE emptyᵉ κ id now sched st =
  let (burst , sched₁) = oneShotBurst [] id sched
  in burst , sched₁ , st

subscribeE (mapᵉ f b) κ id now sched st =
  let (burst , sched₁ , st₁) = subscribeE b (map-f f ↠ κ) id now sched st
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

subscribeE (mergeAllᵉ b) κ id now sched st =
  subscribeAll mergeᵒ (merge-st 0 false) b κ id now sched st
subscribeE {u = u} (concatAllᵉ b) κ id now sched st =
  subscribeAll concatᵒ (concat-st {t = u} [] false false) b κ id now sched st
subscribeE (switchAllᵉ b) κ id now sched st =
  subscribeAll switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE (exhaustAllᵉ b) κ id now sched st =
  subscribeAll exhaustᵒ (exhaust-st false false) b κ id now sched st

-- one unfold per subscription; the recursive occurrences inside the
-- unfolding are deferᵉ-gated, so each re-entry costs a schedule hop —
-- no synchronous loop
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
  in ((init src ∷ []) at id from src) ∷ [] , sched₄ ,
     register src (thru-outer mergeᵒ nid ↠ κ)
              (installNode nid (merge-st 0 false) st)

-- delivery at a share boundary re-enters chain evaluation: foldPath
-- and dispatchShare are mutually recursive.  TERMINATING because the
-- recursion is bounded by the share telescope — a chain registered on
-- share i sinks only into the root or a strictly later share — but
-- that invariant lives in the registry, invisible to Agda; same
-- proof-phase debt as subscribeE
{-# TERMINATING #-}
dispatchShare : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Id → Tick → (i : Fin n)
              → List (Val Γ (lookup Γ i)) → Bool
              → Sched Γ → EvalSt e
              → Stream Γ t × Sched Γ × EvalSt e

-- one chain, ONE emit — plus, past a share boundary, the fan-out
-- emits it causes.  Fold the value list sinkward through the frames,
-- accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
foldPath : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Id → Tick → Source → Path Γ u t
         → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
         → Sched Γ → EvalSt e
         → Stream Γ t × Sched Γ × EvalSt e
foldPath id now envSrc root vals evs fin sched st =
  ((evs ++ map value vals ++ (if fin then complete ∷ [] else []))
    at id from envSrc) ∷ [] , sched , st
foldPath id now envSrc (share-sink i) vals evs fin sched st =
  -- the chain's own (valueless) emit first, then the fan-out: the
  -- share delivers vals to every chain registered on it, still
  -- inside this instant — the diamond case, batched by construction
  let (fanout , sched₁ , st₁) = dispatchShare id now i vals fin sched st
  in ((evs at id from envSrc) ∷ fanout) , sched₁ , st₁
foldPath id now envSrc (f ↠ path′) vals evs fin sched st =
  let (vals′ , evs′ , fin′ , sched₁ , st₁) =
        stepFrame id now f path′ vals fin sched st
  in foldPath id now envSrc path′ vals′ (evs ++ evs′) fin′ sched₁ st₁

-- deliver to the chains of share i, one emit per registration from
-- source toℕ i (the share's owed count), in subscription order.  A
-- completing def (fin) latches the share BEFORE the fan-out — as a
-- Subject closes before delivering its completion — so a subscriber
-- joining mid-dispatch already sees the one-shot close/complete and
-- never registers only to be dropped silently; then every snapshot
-- registration closes and the sweep collects whatever the share kept
-- alive
dispatchShare {Γ = Γ} {t = t} {e = e} id now i vals fin sched st =
  finish fin (go (admit (EvalSt.registry st)) sched (latch fin st))
  where
  latch : Bool → EvalSt e → EvalSt e
  latch false st₀ = st₀
  latch true  st₀ =
    record st₀ { completedSources = toℕ i ∷ EvalSt.completedSources st₀ }

  admit : List (Source × Chain Γ t) → List (Path Γ (lookup Γ i) t)
  admit [] = []
  admit ((s , (u , p)) ∷ r) with sameSource (toℕ i) s | u ≟ᵗ lookup Γ i
  ... | false | _        = admit r
  ... | true  | no  _    = admit r
  ... | true  | yes refl = p ∷ admit r

  go : List (Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e
     → Stream Γ t × Sched Γ × EvalSt e
  go []       sched₀ st₀ = [] , sched₀ , st₀
  go (p ∷ ps) sched₀ st₀ =
    let (emits , sched₁ , st₁) =
          foldPath id now (toℕ i) p vals
                   (if fin then close (toℕ i) ∷ [] else []) fin sched₀ st₀
        (rest , sched₂ , st₂) = go ps sched₁ st₁
    in emits ++ rest , sched₂ , st₂

  finish : Bool → Stream Γ t × Sched Γ × EvalSt e → Stream Γ t × Sched Γ × EvalSt e
  finish false out = out
  finish true  (emits , sched′ , st′) =
    let kept = dropSource (toℕ i) (EvalSt.registry st′)
    in emits ,
       record sched′ { live = sweepLive kept (Sched.live sched′) } ,
       record st′ { registry = kept }

-- seed one arrival into one chain: the value, plus fin and this
-- registration's close when the source is spent (isLast)
chainStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Id → (a : Arrival Γ) → Path Γ (arrTy a) t → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e
chainStep id a path sched st =
  foldPath id (arrTick a) (arrSource a) path (arrVal a ∷ [])
           (if Arrival.isLast a then close (arrSource a) ∷ [] else [])
           (Arrival.isLast a) sched st

-- one arrival, count(source) emits: every live registration chain of
-- the arrival's source forwards EXACTLY ONE emit (possibly valueless),
-- in subscription order — any further emits a chain contributes are
-- share fan-outs, themselves one per registration of their share
cascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Arrival Γ → Id → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e
cascade {Γ = Γ} {t = t} {e = e} a id sched st =
  finish (go (chainsOf a st) sched (latch st))
  where
  -- a spent source (final scripted value) is latched completed BEFORE
  -- its last delivery fans out — as a Subject closes before delivering
  -- its completion — so a subscriber joining mid-cascade already sees
  -- the one-shot close/complete and never registers only to be
  -- dropped silently at finish.  Colds and deferᵉ hops get latched
  -- too, harmlessly: their sources are per-subscription, never
  -- re-subscribed
  latch : EvalSt e → EvalSt e
  latch st₀ =
    if Arrival.isLast a
    then record st₀ { completedSources = arrSource a ∷ EvalSt.completedSources st₀ }
    else st₀

  go : List (Path Γ (arrTy a) t) → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e
  go []           sched₀ st₀ = [] , sched₀ , st₀
  go (c ∷ chains) sched₀ st₀ =
    let (emits , sched₁ , st₁) = chainStep id a c sched₀ st₀
        (rest  , sched₂ , st₂) = go chains sched₁ st₁
    in emits ++ rest , sched₂ , st₂

  -- the spent source's registrations drop at the end (each snapshot
  -- chain already carried its own close) and the sweep collects its
  -- live entry
  finish : Stream Γ t × Sched Γ × EvalSt e → Stream Γ t × Sched Γ × EvalSt e
  finish (emits , sched′ , st′) with Arrival.isLast a
  ... | false = emits , sched′ , st′
  ... | true  =
        let kept = dropSource (arrSource a) (EvalSt.registry st′)
        in emits ,
           record sched′ { live = sweepLive kept (Sched.live sched′) } ,
           record st′ { registry = kept }

-- fuel = ARRIVALS PROCESSED; each arrival's cascade runs to
-- quiescence (never truncated mid-batch).  The root subscription's
-- burst is free: fuel 0 still yields it.
evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → Stream Γ t
evaluate {Γ = Γ} {t = t} fuel e ins =
  let (burst , sched₀ , st₀) =
        subscribeE e root (freshId 0 0) 0 (sched-init e ins) (st-init e)
  in burst ++ loop fuel sched₀ st₀
  where
  loop : Fuel → Sched Γ → EvalSt e → Stream Γ t
  loop zero    _     _  = []                    -- out of fuel: truncate (only here)
  loop (suc k) sched st with sched-next sched
  ... | inj₁ _            = []                  -- schedule empty: program done
  ... | inj₂ (a , sched′) =
    let (out , sched″ , st′) =
          cascade a (freshId (arrTick a) (arrOrd a)) sched′ st
    in out ++ loop k sched″ st′
