module Rx.Evaluator where

open import Data.Bool    using (Bool; true; false; if_then_else_; not; _∨_; _∧_; T)
open import Data.Fin     using (Fin; toℕ)
open import Data.Maybe   using (Maybe; just; nothing; is-nothing)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _<ᵇ_; _≡ᵇ_; _≤ᵇ_)
open import Data.List    using (List; []; _∷_; _++_; map; concat; tabulate; any; null; sum)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Tick; Fuel; Ordinal; Id; Source;
                           Gas; g0; gs; gasTower; gasPad; towerℕ;
                           Timed; after_,_; ObservableInput; hot; cold;
                           InstEvent; init; value; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; dried;
                           EmitKind; subscribe; delivery; plumbing;
                           InstEmit; _at_from_as_)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; _≟ᵗ_; Ctx; Val; Closed; Fn; isData;
                           applyFn; evalTm; unfoldμ; sizeᵉ; sizeᵛ;
                           input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                           mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                           μᵉ; varᵉ; deferᵉ)
-- for `entryCeil`: the caps recurrence's BASE width, which `budgetAt`
-- must know because it must dominate the recurrence
open import Rx.Frame-Width using (entryCeil)


------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

-- THE SLOT TELESCOPE lives in Rx.Slots and is re-exported here: the
-- width measures need it too, and `budgetAt` below reads THEIR entry
-- ceiling, so the telescope has to sit under both.  Defs must reference
-- only strictly earlier slots (a const telescope) — checked by the
-- generator/decoder, not by these types; a forward reference is
-- rejected there.
open import Rx.Slots public

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

-- sync fuel: the totality budget for one cascade's synchronous work.
-- The subscription machine decrements it at exactly its three
-- non-structural edges — a μ unfold, a share connect, an inner-value
-- subscription — and every other recursion is structural, so
-- termination is a lexicographic (fuel, expression) descent, no
-- pragma.  A dry run does NOT truncate silently: it emits a close
-- with reason `dried` — a CloseReason no machine rule ever emits —
-- so hasDry recognizes it EXACTLY, QuickCheck's WF check flags it at
-- runtime (the close's source is never inited, which the strict
-- protocol rejects on sight), and evaluate-well-formed itself demands
-- budget sufficiency (the old pragma's termination debt, reified as a
-- provable statement).  The marker is the REASON, not the source:
-- Source is an unbounded ℕ and mints are breadth-many (fuel is only
-- depth-consumed), so a burst can legally mint past any numeric
-- sentinel — a sentinel-source check would misfire on a wet run.
-- drySource survives only as the envelope's cosmetic source id.  The
-- seeded budget (syncBudget below) is exponential in program size and
-- instant index — astronomically above the sync work any canonical
-- program performs; proving that is Formal-Verification work
drySource : Source
drySource = 18446744073709551615

dryBurst : ∀ {A : Set} → Id → List (InstEmit A)
dryBurst id =
  ((close drySource dried ∷ []) at id from drySource as subscribe) ∷ []

-- did the run go dry anywhere?  Verify-Well-Formed's step lemmas are
-- conditioned on `hasDry … ≡ false`, and the budget-sufficient
-- postulate asserts it for the seeded budget — the totality debt as a
-- provable statement
dryEvent : ∀ {A : Set} → InstEvent A → Bool
dryEvent (close _ dried) = true
dryEvent _               = false

hasDry : ∀ {A : Set} → List (InstEmit A) → Bool
hasDry []         = false
hasDry (em ∷ ems) = any dryEvent (InstEmit.events em) ∨ hasDry ems

-- a TOWER of 2s, height (size+1)·(id+1) — no 2^(polynomial) budget is
-- sufficient.  Why: a scanᵉ with an obs-typed accumulator whose
-- template embeds the accumulator twice (acc ↦ mergeAll(of[acc,acc]))
-- converts value COUNT into subscription DEPTH one-for-one (after k
-- folded values the acc nests k deep, and fuel is depth-consumed —
-- siblings share it), while SUBSCRIBING that acc emits its 2^k leaves
-- as values — count exponentiates at each chained scan.  Measured
-- exactly (2026-07-19): thresholds 2,3,5,9 = 2^d+1 for one scan over
-- 2^d values; counts 2,6,30,510 = 2^(2^d+1)−2; the next scan's
-- threshold tracks that count.  So fuel demand towers in the number
-- of chained scans (≤ size per instant, and scan state compounds one
-- story per instant across cascades) while syntax stays linear —
-- e.g. two scans over 2^7 values: size 80, demand ~2^129.  μ adds no
-- stories across instants (unfoldμ substitutes the ORIGINAL closed
-- μ).  Height linear in size and instant dominates with slack.
-- Gas, not ℕ: see Rx.Prim — a tower can never materialize strictly.
-- The gasPad literal head (the old quadratic budget) is a pure fast
-- path: every physically runnable consumption stays inside it, so the
-- tower tail is never forced — evaluation cost is exactly the old
-- ℕ budget's, while the tail carries the theorem's sufficiency.
-- Height (7+size)·(id+2), THREE-plus stories above the store bound
-- (Verify-Budget-Sufficient's sizeBudgetAt, height (4+size)·(id+1)):
-- the wet contract's demand anchors at the instant's LANDING budget
-- (mid-walk stores legitimately outgrow the entry cap, so the
-- fixed-per-instant demand base is the next instant's store bound,
-- height (4+size)·(id+2)) and is polynomial in that bound with a
-- syntax-sized exponent (rank of the shell multiset); a tower
-- absorbs any polynomial fudge within two stories — the rest is
-- margin.  The extra stories are free: the tower tail is lazy and
-- never forced on a feasible run.
--
-- AND THE HEIGHT IS NO LONGER LINEAR IN THE INSTANT.  It was, while the
-- caps recurrence's per-instant fold count was `D̂ · cSize`: four tower
-- stories an instant, height (7+sz)(id+2), and `capsAt-tower` bracketed
-- the whole recurrence by that closed form.  Charge-Probe and
-- Instant-Height then priced the frame receipt the induction actually
-- builds — `suc (length vals · suc (sizeᵗ fn))` per frame, a PAYLOAD
-- WIDTH — and the count that fits every measured row reads cWid.  It is
-- now the WALK'S OWN LANDING LEVEL rather than a product of it:
--
--     sizeCount c = lvls (cSize c) (cWid c) 0 (cDel c)
--
-- i.e. the level one instant's deliveries climb to, each delivery
-- charged at the level the one before it LEFT.  The product it replaces
-- (`cDel c · cSize c · suc (suc cWid · suc cSize)`, a whole cascade
-- charged at its ENTRY level) is DOMINATED by it — `lvls-lin` at J = 0,
-- Level-Walk-Probe's `count-gate` — so nothing the old count covered is
-- lost, and the iterated form is what `cascadeGo-level` actually proves,
-- which is what makes the per-instant charge a theorem.
--
-- A count reading cWid iterates the tower FUNCTION once per instant
-- (Width-Count-Probe), so no towerℕ-of-linear-height bracket exists and
-- no closed form does either.  What replaces it is the same move the
-- caps themselves made: a RECURRENCE.  `capsHt sz id` is the tower
-- height of `capsAt e sl id`, one `blowH` per instant, and `blowH` is
-- exactly what one frameBlowup's inequalities demand plus visible
-- margin — so domination is by construction rather than by arithmetic.
--
-- THE PER-INSTANT COST, at a pooled level M (every Caps field ≤ M):
--
--   THE COUNT     sizeCount ≤ poolCount M           (by monotonicity —
--                 poolCount IS sizeCount with every field pooled, so
--                 this costs no arithmetic at all)
--   THE SIZE      a factor (3T) per fold, sizeCount folds
--                                                  TWO stories
--   THE REGISTRY  linear in the count               ONE more
--   THE WIDTH     TWO stories PER FOLD (foldStep squares into the
--                 next-but-one level), sizeCount folds
--                                                  → m + 2 · sizeCount
--
-- and the width term dominates everything else by an exponential, which
-- is why the height is now tower-VALUED rather than linear.  It costs
-- nothing: Gas is lazy, `capsHt` is never normalised, and the gasPad
-- literal head in front of it is the same fast path it always was

------------------------------------------------------------------
-- THE DELIVERY BUDGET, AND WHY IT IS A RECURSION AND NOT A FORMULA.
--
-- One cascade's deliveries are a TREE: `cascadeGo` walks the chains
-- (at most cReg of them), a delivery's `foldPath` bottoms out at one
-- `share-sink`, and `dispatchShare` fans out over `shareAdmit`'s
-- SNAPSHOT of the registry, one dispatch gas cheaper.  So the depth is
-- capped by the dispatch gas and the branching by the registry AS OF
-- THAT DISPATCH — and the registry GROWS mid-cascade, by at most `Q`
-- mints per delivery (a mint is a subscribe, hence a charged step, so Q
-- is the per-delivery charge).
--
-- EVERY CLOSED FORM FAILS, AND NOT BY A CONSTANT.  Each closed attempt
-- bounded the registry through the deliveries and the deliveries
-- through the registry:
--
--     R ≤ cReg + Q · D          D ≤ (1 + R) ^ (1 + n)
--
-- i.e. `D ≤ (1 + cReg + Q · D) ^ (1 + n)`, which has NO solution — the
-- right-hand side outgrows the left at every D, so the pair of facts
-- bounds nothing whatever the constants.  A bigger closed form does not
-- help; the fix is to stop asking for one.
--
-- `dCapᶜ` IS THE SEQUENTIAL READING OF THE SAME TWO FACTS.  The walk
-- happens one chain at a time, and what a later chain sees is what the
-- deliveries ALREADY MADE left behind — which is exactly the ordering
-- fact the mint loop obeys (a minted registration is reachable only by
-- dispatches that come AFTER it, Mint-Loop-Shapes' reading of R_end).
-- Written that way the recursion is on the dispatch gas outside and the
-- walk position inside, and it is well-founded precisely where the
-- closed form was circular.
--
-- AND WHAT IT THREADS IS THE CAPS LEVEL, NOT A REGISTRY.  The first
-- version threaded `R + Q · suc d` with `Q` a per-delivery mint budget
-- read once at the cascade's ENTRY caps, and charging anything
-- per-frame at the entry caps is machine-refuted
-- (agda/probe/Entry-Caps-Refuted.agda: one `map-f` frame's output
-- breaches the very cap it was charged at, because `applyFn` grows a
-- value).  The honest per-frame face REPORTS its growth as an index j′
-- and lands at `frameStep (j + j′) c`, so the walk carries that index:
--
--   · a FRAME costs `fCharge S W J`, the receipt `scanFrame-caps` pays
--     (`suc (length vals * suc (sizeᵗ fn))`) read at the level the frame
--     RUNS at — its factors are the burst ledger's width conjunct and
--     the size cap, both at `frameStep J c`;
--   · a DELIVERY is a chain of frames, each at the level the one before
--     it LEFT, so `dLvl` ITERATES that receipt over the chain (capped at
--     `suc (sizeAt S J)`, pathSz?'s own length conjunct) instead of
--     multiplying by it — a product would repeat the refuted error one
--     level down;
--   · and the REGISTRY needs no accounting at all: `capsOK?`'s fifth
--     conjunct is `length registry ≤ cReg (frameStep J c)`, so the walk
--     a dispatch fans out over is `regAt S R J` long.
--
-- It is POINTWISE ABOVE the registry walk it replaces
-- (agda/probe/Level-Walk-Probe.agda, `old-cDel≤new-cDel`), so every
-- measured delivery row the old bound cleared this one clears too.
--
-- IT IS ACKERMANN-FLAVOURED IN THE GAS, and that costs nothing here:
-- `blowH` READS it, so the per-instant story increment stays true by
-- construction rather than by arithmetic.  The price of a lazy Gas
-- tower's height being large is nothing at all
-- ONE FOLD's worst case on a width — AND WHY IT READS THE SIZE.
--
-- The earlier `2 ^ suc w` was gated against deepScan's PAYLOAD count and
-- is refuted against the quantity capsOK? actually bounds: one fold
-- takes deepScan's stored width 1 ↦ 6 where it allowed 4
-- (State-Blowup-Probe).  The reason is structural — `innWᵉ (scanᵉ f z e)`
-- puts the source's width in an EXPONENT whose base is read off the step
-- function's syntax — so the per-fold multiplier is a property of `f`,
-- and cSize is the only thing in Caps that bounds a step function.
--
-- Note this is a strict GENERALISATION: at S = 2 it is exactly the old
-- step, so Frame-Work-Probe's 2 / 6 / 126 gates still read as before
foldStep : ℕ → ℕ → ℕ
foldStep S w = S ^ suc w

iterFold : ℕ → ℕ → ℕ → ℕ
iterFold S zero    w = w
iterFold S (suc k) w = iterFold S k (foldStep S w)

-- ONE FOLD's worst case on a SIZE, straight off size-subΘᵉ: a fold
-- substitutes the accumulator into the step function, and
-- size-subΘᵉ bounds that by `sizeᵉ f * suc (2 * V)` with V the env cap.
-- Both `sizeᵉ f` and V are ≤ cSize, hence S in both positions
sizeStep : ℕ → ℕ → ℕ
sizeStep S s = S * suc (2 * s)

iterSize : ℕ → ℕ → ℕ → ℕ
iterSize S zero    s = s
iterSize S (suc k) s = iterSize S k (sizeStep S s)


------------------------------------------------------------------
-- THE LEVEL READING, AND THE WALK THAT CARRIES IT.
--
-- `dCap` above threads a REGISTRY and charges each delivery a fixed `Q`
-- read once at the cascade's ENTRY caps.  That charging is REFUTED
-- (agda/probe/Entry-Caps-Refuted.agda: one `map-f` frame's output
-- breaches the entry cap it was charged at, because `applyFn` grows a
-- value), and the honest per-frame face — the PROVEN `stepFrame-caps`
-- — reports a growth index j′ and lands its post-state at
-- `frameStep (j + j′) c`.  So the walk carries the LEVEL instead:
--
--   · a FRAME costs `fCharge`, the receipt `scanFrame-caps` pays
--     (`suc (length vals * suc (sizeᵗ fn))`) read at the level the frame
--     RUNS at — its two factors are the burst ledger's width conjunct
--     `suc (widAt S W J)` and the size cap `sizeAt S J`;
--   · a DELIVERY is a CHAIN of frames, each running at the level the one
--     before it left, so its cost is `iterL` — an ITERATION, not a
--     product.  (A product would charge a delivery's later frames at the
--     level it entered at, which is the same error one level down that
--     the refuted entry axioms made one level up.)  The chain is capped
--     at `suc (sizeAt S J)` by pathSz?'s own length conjunct, read at
--     the delivery's entry level;
--   · and the REGISTRY a later dispatch fans out over needs no separate
--     mint accounting at all: it is `capsOK?`'s own fifth conjunct read
--     at the current level, `regAt S R J = R * suc (J * S)`.
--
-- The recursion is the same lexicographic (dispatch gas, walk position)
-- descent `dCap` runs on — only the threaded quantity changed — and it
-- is POINTWISE ABOVE `dCap` at the same entry caps
-- (`old-cDel≤new-cDel`, agda/probe/Level-Walk-Probe.agda), so every
-- measured D row the old bound cleared this one clears too, with no
-- re-measurement
------------------------------------------------------------------

sizeAt : ℕ → ℕ → ℕ
sizeAt S J = iterSize S J S

widAt : ℕ → ℕ → ℕ → ℕ
widAt S W J = iterFold S J W

regAt : ℕ → ℕ → ℕ → ℕ
regAt S R J = R * suc (J * S)

fCharge : ℕ → ℕ → ℕ → ℕ
fCharge S W J = suc (suc (widAt S W J) * suc (sizeAt S J))

fLvl : ℕ → ℕ → ℕ → ℕ
fLvl S W J = J + fCharge S W J

iterL : ℕ → ℕ → ℕ → ℕ → ℕ
iterL S W zero    J = J
iterL S W (suc k) J = iterL S W k (fLvl S W J)

dLvl : ℕ → ℕ → ℕ → ℕ
dLvl S W J = iterL S W (suc (sizeAt S J)) J

lvls : ℕ → ℕ → ℕ → ℕ → ℕ
lvls S W J zero    = J
lvls S W J (suc d) = dLvl S W (lvls S W J d)

dCapᶜ  : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ       -- S W R gas level
dWalkᶜ : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ   -- S W R gas level position

dCapᶜ S W R zero    J = 0
dCapᶜ S W R (suc g) J = dWalkᶜ S W R g J (regAt S R J)

dWalkᶜ S W R g J zero    = 0
dWalkᶜ S W R g J (suc i) =
  let d = dWalkᶜ S W R g J i
  in d + suc (dCapᶜ S W R g (lvls S W J (suc d)))


-- THE POOLED COUNT: `sizeCount` with every Caps field replaced by one
-- bound M.  `blowH` reads it, which is what makes "one instant costs
-- this much height" a monotonicity fact instead of a tower estimate.
--
-- AND IT PATTERN-MATCHES ON ITS ARGUMENT ON PURPOSE.  `blowH` applies
-- it to `towerℕ m`, which is STUCK for a variable m — so with a
-- match in front the whole count stays one opaque symbol, and
-- `capsHgo`'s nested `blowH (blowH m)` stays the size the old closed
-- increment was.  Written without the match the body inlines on every
-- whnf and mentions its argument SIX times, which squares per instant:
-- .Wet's caps-fuel-root, which normalises `blowH (blowH (capsBase …))`,
-- ran past an hour on it and finished in minutes with the match in.
-- The level form keeps that property for the same reason it keeps it
-- at `sizeCount`: `lvls` matches on its DELIVERY COUNT, which is a
-- `dCapᶜ` stuck at a variable, so the whole body is stuck at whnf
poolBody : ℕ → ℕ
poolBody M = lvls M M 0 (dCapᶜ M M M (suc M) 0)

poolCount : ℕ → ℕ
poolCount zero    = 0
poolCount (suc M) = poolBody (suc M)

-- ABSTRACT, and it is a PERFORMANCE contract rather than an abstraction
-- one.  `capsHgo` nests this per instant, so `blowH (blowH m)` is what
-- .Wet's caps-fuel-root normalises — and with the body visible the
-- delivery count is inlined twice, squared, and that module ran past an
-- hour without finishing (measured twice).  Opaque, the height is one
-- symbol everywhere except where the recurrence's own arithmetic needs
-- it, and `blowH-body` hands that back on demand
abstract
  blowH : ℕ → ℕ
  blowH m = 6 + m + 2 * poolCount (towerℕ m)

  blowH-body : ∀ (m : ℕ) → blowH m ≡ 6 + m + 2 * poolCount (towerℕ m)
  blowH-body m = refl

capsHgo : ℕ → Id → ℕ
capsHgo m zero    = blowH m
capsHgo m (suc id) = blowH (capsHgo m id)

syncBudget : ℕ → ℕ → Id → Gas
syncBudget sz m id =
  gasPad (2 ^ (sz * suc id * suc id)) (gasTower (3 + capsHgo m (suc id)))

-- THE BASE LEVEL of the caps recurrence: everything `capsAt`'s base
-- carries, under one `towerℕ` by `k≤towerℕ` and nothing else.  cSize's
-- base is `2 + sz` and cReg's is `suc sz`; cWid's is the ENTRY CEILING,
-- and the ceiling is read HERE rather than bounded by some function of
-- sz because the five static width measures TOWER in the syntax and no
-- closed bracket on them exists that is worth proving.  Reading it costs
-- nothing: the height is never normalised
capsBase : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → ℕ
capsBase {n = n} e sl = 3 + (sizeᵉ e + slotsSize sl) + suc (entryCeil n sl e)

budgetAt : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Id → Gas
budgetAt e sl id = syncBudget (sizeᵉ e + slotsSize sl) (capsBase e sl) id

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
           → Gas → Closed Γ u → Path Γ u t → Id → Tick
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
-- current instant, split its burst.  A fuel decrement edge: the inner
-- is a runtime VALUE, structurally unrelated to the caller
subscribeInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
               → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
               → Val Γ (obs u) → Sched Γ → EvalSt e
               → NodeId × List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
subscribeInner g0 op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
  in inst , [] , close drySource dried ∷ [] , false
     , record sched { nextNode = suc inst } , st
subscribeInner (gs fuel) op allNid κ id now o sched st =
  let inst = Sched.nextNode sched
      (burst , sched′ , st′) =
        subscribeE fuel o (from-inner op allNid inst ↠ κ) id now
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
scanVals fn acc []       = [] , acc
scanVals fn acc (v ∷ vs) =
  let acc′          = applyFn fn (acc , v)
      (outs , last) = scanVals fn acc′ vs
  in acc′ ∷ outs , last

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
mergeBump : ∀ {n} {Γ : Ctx n} → NodeId → Bool
          → List (NodeId × NodeState Γ) → List (NodeId × NodeState Γ)
mergeBump nid done ns with lookupNode nid ns
... | just (merge-st k od) = setNode nid (merge-st (if done then k else suc k) od) ns
... | _                    = ns

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
            → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
            → Val Γ (obs u) → Sched Γ → EvalSt e
            → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e
thruConsume fuel mergeᵒ nid κ id now o sched₀ st₀ =
  let (_ , vs , bs , done , sched₁ , st₁) =
        subscribeInner fuel mergeᵒ nid κ id now o sched₀ st₀
  in vs , bs , sched₁ , record st₁ { nodes = mergeBump nid done (EvalSt.nodes st₁) }
thruConsume {u = u} fuel concatᵒ nid κ id now o sched₀ st₀
  with lookupNode nid (EvalSt.nodes st₀)
... | just (concat-st {w} q true od) with w ≟ᵗ u
...   | yes refl =
        [] , [] , sched₀ ,
        record st₀ { nodes = setNode nid (concat-st (q ++ o ∷ []) true od) (EvalSt.nodes st₀) }
...   | no _ = [] , [] , sched₀ , st₀
thruConsume {u = u} fuel concatᵒ nid κ id now o sched₀ st₀
    | just (concat-st q false od) =
  let (_ , vs , bs , done , sched₁ , st₁) =
        subscribeInner fuel concatᵒ nid κ id now o sched₀ st₀
  in vs , bs , sched₁ ,
     record st₁ { nodes = setNode nid (concat-st {t = u} [] (not done) od) (EvalSt.nodes st₁) }
thruConsume fuel concatᵒ nid κ id now o sched₀ st₀ | _ = [] , [] , sched₀ , st₀
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
         → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
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
thruWrap mergeᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (merge-st k _) =
      vs , bs , (k ≡ᵇ 0) , sched′ ,
      record st′ { nodes = setNode nid (merge-st k true) (EvalSt.nodes st′) }
... | _ = vs , bs , true , sched′ , st′
thruWrap concatᵒ nid true (vs , bs , sched′ , st′)
  with lookupNode nid (EvalSt.nodes st′)
... | just (concat-st q act _) =
      vs , bs , not act ∧ null q , sched′ ,
      record st′ { nodes = setNode nid (concat-st q act true) (EvalSt.nodes st′) }
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
-- budget proof can reason about its reduction.  concatAll's drain
-- walks the queue, subscribing each parked inner until one stays open
concatDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            → Gas → NodeId → Path Γ s t → Id → Tick
            → List (Closed Γ s) → Sched Γ → EvalSt e
            → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool
              × List (Closed Γ s) × Sched Γ × EvalSt e
concatDrain fuel allNid κ id now []      sched₀ st₀ = [] , [] , false , [] , sched₀ , st₀
concatDrain fuel allNid κ id now (o ∷ q) sched₀ st₀ =
  let (_ , vs , bs , done , sched₁ , st₁) =
        subscribeInner fuel concatᵒ allNid κ id now o sched₀ st₀
  in if done
     then (let (vs′ , bs′ , act , q′ , sched₂ , st₂) =
                 concatDrain fuel allNid κ id now q sched₁ st₁
           in vs ++ vs′ , bs ++ bs′ , act , q′ , sched₂ , st₂)
     else (vs , bs , true , q , sched₁ , st₁)

innerFinish : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
            → Gas → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
            → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ)
            → List (Val Γ s) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
innerFinish fuel mergeᵒ allNid inst κ id now vals sched st (just (merge-st k od)) =
  vals , [] , od ∧ (pred k ≡ᵇ 0) , sched ,
  record st { nodes = setNode allNid (merge-st (pred k) od) (EvalSt.nodes st) }
innerFinish {s = s} fuel concatᵒ allNid inst κ id now vals sched st
            (just (concat-st {w} q act od)) with w ≟ᵗ s
... | yes refl =
      let (vs , bs , act′ , q′ , sched′ , st′) =
            concatDrain fuel allNid κ id now q sched st
      in vals ++ vs , bs , od ∧ not act′ ∧ null q′ , sched′ ,
         record st′ { nodes = setNode allNid (concat-st q′ act′ od) (EvalSt.nodes st′) }
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
           → Gas → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
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
          → Gas → Id → Tick → Frame Γ s u → Path Γ u t
          → List (Val Γ s) → Bool → Sched Γ → EvalSt e
          → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e

stepFrame fuel id now (map-f fn) κ vals fin sched st =
  map (applyFn fn) vals , [] , fin , sched , st

stepFrame {Γ = Γ} {t = t} {e = e} {s = s} {u = u} fuel id now (scan-f fn nid) κ vals fin sched st
  = dispatch (lookupNode nid (EvalSt.nodes st))
  where
  dispatch : Maybe (NodeState Γ)
           → List (Val Γ u) × List (InstEvent (Val Γ t)) × Bool × Sched Γ × EvalSt e
  dispatch (just (scan-st {w} acc)) with w ≟ᵗ u
  ... | yes refl =
        let (outs , acc′) = scanVals fn acc vals
        in outs , [] , fin , sched ,
           record st { nodes = setNode nid (scan-st acc′) (EvalSt.nodes st) }
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
          → Gas → Id → Tick → Frame Γ s u → Path Γ u t
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
             → Gas → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ u t
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
-- proof can name it (as with takeVals / thruConsume / concatDrain)
sharedConnect : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Gas → (i : Fin n) → Closed Γ (lookup Γ i)
              → Path Γ (lookup Γ i) t → Id → Tick
              → Sched Γ → EvalSt e
              → Stream Γ (lookup Γ i) × Sched Γ × EvalSt e
sharedConnect g0 i d κ id now sched st = dryBurst id , sched , st
sharedConnect (gs fuel′) i d κ id now sched st =
  let st₁ = register (toℕ i) κ
              (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st })
      (burst , sched₁ , st₂) = subscribeE fuel′ d (share-sink i) id now sched st₁
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
                    → Gas → (i : Fin n) → Closed Γ (lookup Γ i)
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

subscribeE fuel (mergeAllᵉ b) κ id now sched st =
  subscribeAll fuel mergeᵒ (merge-st 0 false) b κ id now sched st
subscribeE {u = u} fuel (concatAllᵉ b) κ id now sched st =
  subscribeAll fuel concatᵒ (concat-st {t = u} [] false false) b κ id now sched st
subscribeE fuel (switchAllᵉ b) κ id now sched st =
  subscribeAll fuel switchᵒ (switch-st nothing false) b κ id now sched st
subscribeE fuel (exhaustAllᵉ b) κ id now sched st =
  subscribeAll fuel exhaustᵒ (exhaust-st false false) b κ id now sched st

-- one unfold per subscription; the recursive occurrences inside the
-- unfolding are deferᵉ-gated, so each re-entry costs a schedule hop —
-- no synchronous loop.  A fuel decrement edge: the unfolding is
-- larger than the μ, not a subterm
subscribeE g0         (μᵉ body) κ id now sched st = dryBurst id , sched , st
subscribeE (gs fuel)  (μᵉ body) κ id now sched st =
  subscribeE fuel (unfoldμ body) κ id now sched st

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
     register src (thru-outer mergeᵒ nid ↠ κ)
              (installNode nid (merge-st 0 false) st)

-- delivery at a share boundary re-enters chain evaluation: foldPath
-- and dispatchShare are mutually recursive.  The recursion is bounded
-- by the share telescope — a chain registered on share i sinks only
-- into the root or a strictly later share — so dispatch depth never
-- exceeds n.  `gas` makes that bound structural: every dispatch
-- consumes one unit and chainStep seeds n, so the zero clamp is
-- unreachable on real registries (the telescope invariant, Inv-phase
-- work) and termination needs no pragma
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

dispatchShare : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
              → Gas      -- sync fuel, handed to stepFrame's re-entries
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
        → Gas → ℕ → Id → Tick → (i : Fin n)
        → List (Val Γ (lookup Γ i)) → Bool
        → List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e

-- one chain, ONE emit — plus, past a share boundary, the fan-out
-- emits it causes.  Fold the value list sinkward through the frames,
-- accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
foldPath : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Gas → ℕ → Id → Tick → Source → Path Γ u t
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
  foldPath (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
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
        subscribeE (budgetAt e ins 0) e root 0 0 (sched-init e ins) (st-init e)
  in burst ++ drain fuel 1 sched₀ st₀
