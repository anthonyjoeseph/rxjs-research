-- THE PLAIN EVALUATOR: AN `Exp` TREE RUN AS ORDINARY rxjs, WHOSE
-- RESULT IS VALUES.  The machine in `Rx.Evaluator` mints an envelope
-- for every emission because one tree there does two jobs; this one
-- does the plain job only, so nothing here knows what an instant, a
-- source token or a registration is, and its result type is the one a
-- plain pipeline has.  Its mirror is `typescript/src/plain-eval.ts`,
-- operator for operator.
--
-- AND IT CASCADES DEPTH-FIRST, WHICH IS THE WHOLE CONTENT OF THE
-- DEMOTION RATHER THAN A DETAIL OF IT.  The other machine collects a
-- synchronous source WHOLE and then pushes it, so a subscriber that
-- attaches part-way through a source's run sees nothing of the rest of
-- it; rxjs pushes each item all the way down before taking the next,
-- so it sees the remainder.  The witness is one program — a shared
-- slot over a two-item source, flattened by a map whose payload is
-- that same slot — where rxjs yields the second item and the burst
-- machine yields none.  So the work here is a STACK rather than a
-- list: a value's own cascade runs before its successor is taken, and
-- whatever that cascade subscribes runs inside it.
--
-- THE ONE DIVERGENCE FROM THE MIRROR IS A STEP BUDGET, AND IT IS
-- FORCED.  TypeScript leans on the host's own call stack to finish a
-- synchronous cascade; Agda has to see the recursion stop.  Every
-- recursive occurrence in the tree sits behind a `deferᵉ`, so a
-- cascade IS finite — but finite for a reason the termination checker
-- cannot read off the work stack, whose entries grow and shrink.  So
-- the cascade takes a budget, derived from the run's fuel, and the
-- budget is a totality device rather than a semantic one.
module Rx.Depth where

open import Data.Bool    using (Bool; true; false; _∧_; _∨_; if_then_else_)
open import Data.Fin     using (Fin; toℕ)
open import Data.Fin.Properties using () renaming (_≟_ to _≟ᶠ_)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Maybe   using (Maybe; nothing; just)
open import Data.Nat     using (ℕ; zero; suc; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_; _≤ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.Vec     using (lookup; allFin; toList)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim  using (Tick; Fuel; Timed; after_,_; hot; cold)
open import Rx.Exp   using (Ty; Ctx; Val; Env; []ᵉ; _∷ᵉ_; Closed; Tm; FnClo; applyClo; evalWith; unfoldμ; _≟ᵗ_; uniqᵗ;
  obs; _×ᵗ_; input; ofᵉ; emptyᵉ; takeᵉ; batchSyncᵉ; mapᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ)
open import Rx.Slots using (Slots; Slot; scripted; shared)

------------------------------------------------------------------
-- The dynamic topology
------------------------------------------------------------------

-- a node instance, numbered in subscription order.  Only the operators
-- that CARRY something between values own one; `map` owns none, which
-- is what makes it the one former with no cell.
Nodeᵈ : Set
Nodeᵈ = ℕ

data AllOpᵈ : Set where
  mergeᵒ switchᵒ exhaustᵒ : AllOpᵈ

-- one operator an emission passes through, rootward.  `deferᵉ`
-- contributes none (it relays its body) and share is not an operator
-- at all — a shared slot fans out by having several sinks, one per
-- subscriber, which is what a Subject IS.
data Frameᵈ {n} (Γ : Ctx n) : Ty → Ty → Set where
  map-f      : ∀ {s u} → FnClo Γ s u → Frameᵈ Γ s u
  scan-f     : ∀ {s u} → FnClo Γ (u ×ᵗ s) u → Nodeᵈ → Frameᵈ Γ s u
  take-f     : ∀ {s} → Nodeᵈ → Frameᵈ Γ s s
  from-inner : ∀ {s} → AllOpᵈ → (allNode innerInstance : Nodeᵈ) → Frameᵈ Γ s s
  thru-outer : ∀ {u} → AllOpᵈ → Nodeᵈ → Frameᵈ Γ (obs u) u

-- WHERE A VALUE GOES, AS A STACK RATHER THAN AS A CALLBACK.  rxjs's
-- sink is a closure holding the rest of the pipeline, which Agda
-- cannot store: a multicast cell's subscriber list would then be a
-- negative occurrence in the state it is stored in.  Defunctionalised,
-- the same object is a first-order spine, and the stateful frames name
-- their cells rather than closing over them.  The spine ends at the
-- root or at a MULTICAST SLOT, which is the one place a single value
-- reaches several sinks.
data Pathᵈ {n} (Γ : Ctx n) : Ty → Ty → Set where
  rootᵈ  : ∀ {t} → Pathᵈ Γ t t
  multiᵈ : ∀ {t} (i : Fin n) → Pathᵈ Γ (lookup Γ i) t
  _↠ᵈ_   : ∀ {s u t} → Frameᵈ Γ s u → Pathᵈ Γ u t → Pathᵈ Γ s t

infixr 5 _↠ᵈ_

------------------------------------------------------------------
-- What a node carries
------------------------------------------------------------------

-- The element types are EXISTENTIAL, so every read pays a `_≟ᵗ_` —
-- the same price the other machine's store pays, and for the same
-- reason: one store holds cells of every type a program mentions.
data Cellᵈ {n} (Γ : Ctx n) : Set where
  scan-c    : ∀ {u} → Val Γ u → Cellᵈ Γ
  take-c    : (remaining : ℕ) → Cellᵈ Γ
  merge-c   : ∀ {u} → (limit : Maybe ℕ) (active : ℕ)
            → (queued : List (Val Γ (obs u))) (outerDone : Bool) → Cellᵈ Γ
  switch-c  : (currentInner : Maybe Nodeᵈ) (outerDone : Bool) → Cellᵈ Γ
  exhaust-c : (innerActive outerDone : Bool) → Cellᵈ Γ

Storeᵈ : ∀ {n} → Ctx n → Set
Storeᵈ Γ = List (Nodeᵈ × Cellᵈ Γ)

lookupCellᵈ : ∀ {n} {Γ : Ctx n} → Nodeᵈ → Storeᵈ Γ → Maybe (Cellᵈ Γ)
lookupCellᵈ k []              = nothing
lookupCellᵈ k ((j , c) ∷ cs) = if j ≡ᵇ k then just c else lookupCellᵈ k cs

setCellᵈ : ∀ {n} {Γ : Ctx n} → Nodeᵈ → Cellᵈ Γ → Storeᵈ Γ → Storeᵈ Γ
setCellᵈ k c []               = (k , c) ∷ []
setCellᵈ k c ((j , c′) ∷ cs) =
  if j ≡ᵇ k then (k , c) ∷ cs else (j , c′) ∷ setCellᵈ k c cs

-- READING A CELL IS A TYPE MATCH AND THEN A PROJECTION, SPLIT OUT SO
-- THE MACHINE'S OWN CLAUSES STAY ONE `with` DEEP.  A failed match
-- cannot happen — a frame and its cell are installed together — and
-- returning `nothing` rather than asserting it is what keeps the
-- machine total without a store invariant.
readScanᵈ : ∀ {n} {Γ : Ctx n} (u : Ty) → Maybe (Cellᵈ Γ) → Maybe (Val Γ u)
readScanᵈ u (just (scan-c {u = w} a)) with w ≟ᵗ u
... | yes refl = just a
... | no  _    = nothing
readScanᵈ u _ = nothing

readTakeᵈ : ∀ {n} {Γ : Ctx n} → Maybe (Cellᵈ Γ) → Maybe ℕ
readTakeᵈ (just (take-c r)) = just r
readTakeᵈ _                 = nothing

readMergeᵈ : ∀ {n} {Γ : Ctx n} (u : Ty) → Maybe (Cellᵈ Γ)
           → Maybe (Maybe ℕ × ℕ × List (Val Γ (obs u)) × Bool)
readMergeᵈ u (just (merge-c {u = w} l a q d)) with w ≟ᵗ u
... | yes refl = just (l , a , q , d)
... | no  _    = nothing
readMergeᵈ u _ = nothing

readSwitchᵈ : ∀ {n} {Γ : Ctx n} → Maybe (Cellᵈ Γ) → Maybe (Maybe Nodeᵈ × Bool)
readSwitchᵈ (just (switch-c c d)) = just (c , d)
readSwitchᵈ _                     = nothing

readExhaustᵈ : ∀ {n} {Γ : Ctx n} → Maybe (Cellᵈ Γ) → Maybe (Bool × Bool)
readExhaustᵈ (just (exhaust-c b d)) = just (b , d)
readExhaustᵈ _                      = nothing

------------------------------------------------------------------
-- The work stack, which is what makes the cascade depth-first
------------------------------------------------------------------

data Workᵈ {n} (Γ : Ctx n) (t : Ty) : Set where
  deliver : ∀ {s} → List (Val Γ s) → (thenDone : Bool) → Pathᵈ Γ s t → Workᵈ Γ t
            -- push these values into the sink ONE AT A TIME, each
            -- one's cascade finishing before the next is taken, and
            -- complete the sink afterwards when the flag says so
  connect : ∀ {s} → Val Γ (obs s) → Pathᵈ Γ s t → Workᵈ Γ t
            -- subscribe this observable value with this sink
  finish  : ∀ {s} → Pathᵈ Γ s t → Workᵈ Γ t
            -- a completion travelling rootward

-- WHAT A CUT HAS TO REMOVE IS PENDING WORK, NOT LIVE STRUCTURE.  A
-- cancelled branch in rxjs is silent, and silence is all any consumer
-- of this machine can observe — so a delivery ARRIVING through a dead
-- node is dropped by its own operator (a spent `take`, a switched-away
-- inner) and nothing has to be torn down for that.  What cannot be
-- dropped on arrival is a pending ARRIVAL, because the run's fuel
-- counts arrivals: leaving a dead source's schedule in the queue
-- spends fuel the mirror spends on a live one, and the two runs then
-- differ in their outputs rather than merely in their bookkeeping.
frameNodesᵈ : ∀ {n} {Γ : Ctx n} {s u} → Frameᵈ Γ s u → List Nodeᵈ
frameNodesᵈ (map-f _)          = []
frameNodesᵈ (scan-f _ k)       = k ∷ []
frameNodesᵈ (take-f k)         = k ∷ []
frameNodesᵈ (from-inner _ k j) = k ∷ j ∷ []
frameNodesᵈ (thru-outer _ k)   = k ∷ []

anyIsᵈ : Nodeᵈ → List Nodeᵈ → Bool
anyIsᵈ k []       = false
anyIsᵈ k (j ∷ js) = if j ≡ᵇ k then true else anyIsᵈ k js

pathThroughᵈ : ∀ {n} {Γ : Ctx n} {s t} → Nodeᵈ → Pathᵈ Γ s t → Bool
pathThroughᵈ k rootᵈ      = false
pathThroughᵈ k (multiᵈ _) = false
pathThroughᵈ k (f ↠ᵈ p)   = anyIsᵈ k (frameNodesᵈ f) ∨ pathThroughᵈ k p

workThroughᵈ : ∀ {n} {Γ : Ctx n} {t} → Nodeᵈ → Workᵈ Γ t → Bool
workThroughᵈ k (deliver _ _ p) = pathThroughᵈ k p
workThroughᵈ k (connect _ p)   = pathThroughᵈ k p
workThroughᵈ k (finish p)      = pathThroughᵈ k p

------------------------------------------------------------------
-- Scripted arrivals and share cells
------------------------------------------------------------------

-- A SCHEDULED UNIT OF WORK, WHICH IS THIS MACHINE'S WHOLE NOTION OF
-- TIME.  The ordinal breaks ties within a tick, and it is not
-- decoration: two sources firing at the same tick fire in registration
-- order.  What is scheduled is a work item and not a value, because
-- `deferᵉ` schedules a SUBSCRIPTION — the one-tick hop that breaks
-- `μᵉ`'s unfolding regress — and it arrives by the same queue.
record Arrivalᵈ {n} (Γ : Ctx n) (t : Ty) : Set where
  constructor arrival
  field
    tick    : Tick
    ordinal : ℕ
    item    : Workᵈ Γ t

-- A MULTICAST SLOT'S CELL, WHICH IS ONE THING FOR TWO SLOT SHAPES.  A
-- hot script and a shared def are both subscriber-independent, so both
-- keep a sink list and neither re-runs, and the only difference is
-- what feeds the cell — a schedule for one, an expression for the
-- other.  A cold script has no cell at all, for the same reason.
--
-- IDENTITY IS THE INDEX, exactly as the slot telescope states it: the
-- de Bruijn binding and not the expression.  The two latches are the
-- all-resets-false `share`'s own — connected once ever, completed once
-- ever — and they are why a late subscriber to a finished cell gets a
-- completion and no values.
record Multiᵈ {n} (Γ : Ctx n) (t : Ty) : Set where
  constructor multiCell
  field
    slot      : Fin n
    connected : Bool
    completed : Bool
    sinks     : List (Pathᵈ Γ (lookup Γ slot) t)

multiSinksᵈ : ∀ {n} {Γ : Ctx n} {t} (i : Fin n)
            → List (Multiᵈ Γ t) → List (Pathᵈ Γ (lookup Γ i) t)
multiSinksᵈ i []                          = []
multiSinksᵈ i (multiCell j _ _ ss ∷ cs) with i ≟ᶠ j
... | yes refl = ss
... | no  _    = multiSinksᵈ i cs

multiFlagsᵈ : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) → List (Multiᵈ Γ t) → Bool × Bool
multiFlagsᵈ i []                         = false , false
multiFlagsᵈ i (multiCell j c d _ ∷ cs) with i ≟ᶠ j
... | yes refl = c , d
... | no  _    = multiFlagsᵈ i cs

addSinkᵈ : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) → Pathᵈ Γ (lookup Γ i) t
         → List (Multiᵈ Γ t) → List (Multiᵈ Γ t)
addSinkᵈ i p []                           = []
addSinkᵈ i p (multiCell j c d ss ∷ cs) with i ≟ᶠ j
... | yes refl = multiCell j c d (ss ++ p ∷ []) ∷ cs
... | no  _    = multiCell j c d ss ∷ addSinkᵈ i p cs

setFlagsᵈ : ∀ {n} {Γ : Ctx n} {t} (i : Fin n) → Bool → Bool
          → List (Multiᵈ Γ t) → List (Multiᵈ Γ t)
setFlagsᵈ i c d []                              = []
setFlagsᵈ i c d (multiCell j c′ d′ ss ∷ cs) with i ≟ᶠ j
... | yes refl = multiCell j c d ss ∷ cs
... | no  _    = multiCell j c′ d′ ss ∷ setFlagsᵈ i c d cs

------------------------------------------------------------------
-- The machine state
------------------------------------------------------------------

record Stᵈ {n} (Γ : Ctx n) (t : Ty) : Set where
  field
    now      : Tick
    nodes    : Storeᵈ Γ
    nextNode : Nodeᵈ
    nextOrd  : ℕ                       -- ordinal counter for dynamic sources
    nextTok  : ℕ                       -- `mintᵉ`'s fresh tokens
    arrivals : List (Arrivalᵈ Γ t)
    multis   : List (Multiᵈ Γ t)
    work     : List (Workᵈ Γ t)        -- the stack: head is next
    out      : List (Val Γ t)          -- the root's emissions, in order

pushWorkᵈ : ∀ {n} {Γ : Ctx n} {t} → Workᵈ Γ t → Stᵈ Γ t → Stᵈ Γ t
pushWorkᵈ w st = record st { work = w ∷ Stᵈ.work st }

-- pushed in reverse so the FIRST sink is taken first
pushAllᵈ : ∀ {n} {Γ : Ctx n} {t} → List (Workᵈ Γ t) → Stᵈ Γ t → Stᵈ Γ t
pushAllᵈ []       st = st
pushAllᵈ (w ∷ ws) st = pushWorkᵈ w (pushAllᵈ ws st)

cutᵈ : ∀ {n} {Γ : Ctx n} {t} → Nodeᵈ → Stᵈ Γ t → Stᵈ Γ t
cutᵈ k st = record st { arrivals = keepA (Stᵈ.arrivals st)
                       ; work     = keepW (Stᵈ.work st) }
  where
    keepA : List (Arrivalᵈ _ _) → List (Arrivalᵈ _ _)
    keepA []       = []
    keepA (a ∷ as) =
      if workThroughᵈ k (Arrivalᵈ.item a) then keepA as else a ∷ keepA as
    keepW : List (Workᵈ _ _) → List (Workᵈ _ _)
    keepW []       = []
    keepW (w ∷ ws) = if workThroughᵈ k w then keepW ws else w ∷ keepW ws

------------------------------------------------------------------
-- The leaves
------------------------------------------------------------------

scheduleᵈ : ∀ {n} {Γ : Ctx n} {t s} → ℕ → Tick → List (Timed (Val Γ s))
          → Pathᵈ Γ s t → List (Arrivalᵈ Γ t)
scheduleᵈ ord anchor []                      p = []
scheduleᵈ ord anchor ((after w , v) ∷ [])    p =
  arrival (anchor + suc w) ord (deliver (v ∷ []) true p) ∷ []
scheduleᵈ ord anchor ((after w , v) ∷ x ∷ r) p =
  let tk = anchor + suc w
  in arrival tk ord (deliver (v ∷ []) false p) ∷ scheduleᵈ ord tk (x ∷ r) p

evalTmsᵈ : ∀ {n} {Γ : Ctx n} {Θ s} → List (Tm Γ [] [] Θ s) → Env Γ Θ → List (Val Γ s)
evalTmsᵈ []       ρ = []
evalTmsᵈ (x ∷ xs) ρ = evalWith x ρ ∷ evalTmsᵈ xs ρ

nullᵈ : ∀ {A : Set} → List A → Bool
nullᵈ []      = true
nullᵈ (_ ∷ _) = false

mutual

  -- SUBSCRIBING IS ONE FORMER PER STEP, NEVER A DESCENT.  Every arm
  -- either finishes the sink, hands values to it, or pushes ONE
  -- `connect` for the sub-expression with the new frame on the sink —
  -- so the budget bounds the whole cascade uniformly.
  subscribeᵈ : ∀ {n} {Γ : Ctx n} {t s} → Slots Γ
             → Val Γ (obs s) → Pathᵈ Γ s t → Stᵈ Γ t → Stᵈ Γ t

  subscribeᵈ {Γ = Γ} {t = t} ins (_ , input i , ρ) p st = slotᵈ (ins i)
    where
      slotᵈ : Slot Γ (toℕ i) (lookup Γ i) → Stᵈ Γ t
      slotᵈ (scripted (hot _)) =
        let (_ , done) = multiFlagsᵈ i (Stᵈ.multis st)
        in if done then pushWorkᵈ (finish p) st
           else record st { multis = addSinkᵈ i p (Stᵈ.multis st) }
      slotᵈ (scripted (cold sync async)) =
        let o = Stᵈ.nextOrd st
        in pushWorkᵈ (deliver sync (nullᵈ async) p)
             (record st { nextOrd  = suc o
                        ; arrivals = Stᵈ.arrivals st
                                     ++ scheduleᵈ o (Stᵈ.now st) async p })
      slotᵈ (shared d) =
        let (conn , done) = multiFlagsᵈ i (Stᵈ.multis st)
            st₁ = record st { multis = addSinkᵈ i p (Stᵈ.multis st) }
        in if done then pushWorkᵈ (finish p) st
           else if conn then st₁
           else pushWorkᵈ (connect (_ , d , []ᵉ) (multiᵈ i))
                  (record st₁ { multis = setFlagsᵈ i true false (Stᵈ.multis st₁) })

  subscribeᵈ ins (_ , ofᵉ ts , ρ)  p st = pushWorkᵈ (deliver (evalTmsᵈ ts ρ) true p) st
  subscribeᵈ ins (_ , emptyᵉ , ρ)  p st = pushWorkᵈ (finish p) st

  subscribeᵈ ins (_ , takeᵉ c e , ρ) p st with evalWith c ρ
  ... | zero  = pushWorkᵈ (finish p) st
  ... | suc m = let k = Stᵈ.nextNode st
                in pushWorkᵈ (connect (_ , e , ρ) (take-f k ↠ᵈ p))
                     (record st { nodes    = setCellᵈ k (take-c (suc m)) (Stᵈ.nodes st)
                                ; nextNode = suc k })

  subscribeᵈ ins (_ , mapᵉ f e , ρ) p st =
    pushWorkᵈ (connect (_ , e , ρ) (map-f (_ , f , ρ) ↠ᵈ p)) st

  subscribeᵈ ins (_ , scanᵉ f z e , ρ) p st =
    let k = Stᵈ.nextNode st
    in pushWorkᵈ (connect (_ , e , ρ) (scan-f (_ , f , ρ) k ↠ᵈ p))
         (record st { nodes    = setCellᵈ k (scan-c (evalWith z ρ)) (Stᵈ.nodes st)
                    ; nextNode = suc k })

  subscribeᵈ {s = s} ins (_ , mergeAllᵉ l e , ρ) p st =
    let k = Stᵈ.nextNode st
    in pushWorkᵈ (connect (_ , e , ρ) (thru-outer mergeᵒ k ↠ᵈ p))
         (record st { nodes    = setCellᵈ k (merge-c {u = s} l 0 [] false) (Stᵈ.nodes st)
                    ; nextNode = suc k })

  subscribeᵈ ins (_ , switchAllᵉ e , ρ) p st =
    let k = Stᵈ.nextNode st
    in pushWorkᵈ (connect (_ , e , ρ) (thru-outer switchᵒ k ↠ᵈ p))
         (record st { nodes    = setCellᵈ k (switch-c nothing false) (Stᵈ.nodes st)
                    ; nextNode = suc k })

  subscribeᵈ ins (_ , exhaustAllᵉ e , ρ) p st =
    let k = Stᵈ.nextNode st
    in pushWorkᵈ (connect (_ , e , ρ) (thru-outer exhaustᵒ k ↠ᵈ p))
         (record st { nodes    = setCellᵈ k (exhaust-c false false) (Stᵈ.nodes st)
                    ; nextNode = suc k })

  subscribeᵈ ins (_ , μᵉ e , ρ) p st = pushWorkᵈ (connect (_ , unfoldμ e , ρ) p) st
  subscribeᵈ ins (_ , varᵉ () , ρ) p st

  subscribeᵈ ins (_ , deferᵉ e , ρ) p st =
    let o = Stᵈ.nextOrd st
    in record st { nextOrd  = suc o
                 ; arrivals = Stᵈ.arrivals st
                              ++ arrival (suc (Stᵈ.now st)) o (connect (_ , e , ρ) p) ∷ [] }

  subscribeᵈ ins (_ , mintᵉ e , ρ) p st =
    let x = Stᵈ.nextTok st
    in pushWorkᵈ (connect (uniqᵗ ∷ _ , e , x ∷ᵉ ρ) p) (record st { nextTok = suc x })

  -- THIS ARM IS UNWRITTEN, AND IT FINISHES EMPTY RATHER THAN SAYING SO,
  -- WHICH IS WHAT MAKES IT COSTLY.  The operator has a plain-rxjs mirror
  -- and both TypeScript legs now carry it -- the sync bit is `merge`'s
  -- own subscribe ordering, never a subscription either leg owns -- so
  -- what is missing here is a CELL, not a capability.  This carrier
  -- delivers a burst one value per event, so the grouping needs an
  -- accumulator held across the subscribe frame and flipped shut when
  -- it drains, which is exactly the shape the reference operator has and
  -- exactly what no cell kind here can hold today.
  -- DEAD ROUTE: finish empty and let the pairing's `gen`/`agen` columns
  --   carry it as a hole.  A node that emits nothing is not a hole, it
  --   is a DISAGREEMENT, and the oracle reports it as one the moment the
  --   generator draws a `batchSync` -- every such case comes back with
  --   the plain leg's values against an empty Agda run.
  subscribeᵈ ins (_ , batchSyncᵉ _ , ρ) p st = pushWorkᵈ (finish p) st

  pushValueᵈ : ∀ {n} {Γ : Ctx n} {t s} → Val Γ s → Pathᵈ Γ s t → Stᵈ Γ t → Stᵈ Γ t
  pushValueᵈ v rootᵈ      st = record st { out = Stᵈ.out st ++ v ∷ [] }
  pushValueᵈ v (multiᵈ i) st =
    pushAllᵈ (map (deliver (v ∷ []) false) (multiSinksᵈ i (Stᵈ.multis st))) st
  pushValueᵈ v (map-f f ↠ᵈ p) st = pushValueᵈ (applyClo f v) p st

  pushValueᵈ v (scan-f {u = u} f k ↠ᵈ p) st
    with readScanᵈ u (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing = st
  ... | just a  = let a′ = applyClo f (a , v)
                  in pushValueᵈ a′ p
                       (record st { nodes = setCellᵈ k (scan-c a′) (Stᵈ.nodes st) })

  -- rxjs's `take` emits and only THEN completes, and the completion
  -- travels downstream while the cut goes upstream — which is why the
  -- two are separate moves rather than one.
  pushValueᵈ v (take-f k ↠ᵈ p) st with readTakeᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing      = st
  ... | just zero    = st
  ... | just (suc r) =
          let st₁ = pushValueᵈ v p
                      (record st { nodes = setCellᵈ k (take-c r) (Stᵈ.nodes st) })
          in if r ≡ᵇ 0 then finishPathᵈ p (cutᵈ k st₁) else st₁

  pushValueᵈ v (from-inner mergeᵒ   _ _ ↠ᵈ p) st = pushValueᵈ v p st
  pushValueᵈ v (from-inner exhaustᵒ _ _ ↠ᵈ p) st = pushValueᵈ v p st
  pushValueᵈ v (from-inner switchᵒ k j ↠ᵈ p) st
    with readSwitchᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (just c , _) = if c ≡ᵇ j then pushValueᵈ v p st else st
  ... | _                 = st

  pushValueᵈ v (thru-outer op k ↠ᵈ p) st = subscribeInnerᵈ op k v p st

  finishPathᵈ : ∀ {n} {Γ : Ctx n} {t s} → Pathᵈ Γ s t → Stᵈ Γ t → Stᵈ Γ t
  finishPathᵈ rootᵈ      st = st
  finishPathᵈ (multiᵈ i) st =
    pushAllᵈ (map finish (multiSinksᵈ i (Stᵈ.multis st)))
             (record st { multis = setFlagsᵈ i true true (Stᵈ.multis st) })
  finishPathᵈ (map-f _    ↠ᵈ p) st = finishPathᵈ p st
  finishPathᵈ (scan-f _ _ ↠ᵈ p) st = finishPathᵈ p st
  finishPathᵈ (take-f _   ↠ᵈ p) st = finishPathᵈ p st

  finishPathᵈ (from-inner mergeᵒ k j ↠ᵈ p) st = innerDoneMergeᵈ k j p st

  finishPathᵈ (from-inner switchᵒ k j ↠ᵈ p) st
    with readSwitchᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (just c , d) =
          if c ≡ᵇ j
          then (let st₁ = record st { nodes = setCellᵈ k (switch-c nothing d)
                                                (Stᵈ.nodes st) }
                in if d then finishPathᵈ p st₁ else st₁)
          else st
  ... | _ = st

  finishPathᵈ (from-inner exhaustᵒ k _ ↠ᵈ p) st
    with readExhaustᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (_ , d) =
          let st₁ = record st { nodes = setCellᵈ k (exhaust-c false d) (Stᵈ.nodes st) }
          in if d then finishPathᵈ p st₁ else st₁
  ... | nothing = st

  finishPathᵈ (thru-outer {u = u} mergeᵒ k ↠ᵈ p) st
    with readMergeᵈ u (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (l , a , q , _) =
          let st₁ = record st { nodes = setCellᵈ k (merge-c {u = u} l a q true) (Stᵈ.nodes st) }
          in if a ≡ᵇ 0 then finishPathᵈ p st₁ else st₁
  ... | nothing = st

  finishPathᵈ (thru-outer switchᵒ k ↠ᵈ p) st
    with readSwitchᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (nothing , _) =
          finishPathᵈ p (record st { nodes = setCellᵈ k (switch-c nothing true)
                                               (Stᵈ.nodes st) })
  ... | just (just c , _) =
          record st { nodes = setCellᵈ k (switch-c (just c) true) (Stᵈ.nodes st) }
  ... | nothing = st

  finishPathᵈ (thru-outer exhaustᵒ k ↠ᵈ p) st
    with readExhaustᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | just (b , _) =
          let st₁ = record st { nodes = setCellᵈ k (exhaust-c b true) (Stᵈ.nodes st) }
          in if b then st₁ else finishPathᵈ p st₁
  ... | nothing = st

  innerDoneMergeᵈ : ∀ {n} {Γ : Ctx n} {t s} → Nodeᵈ → Nodeᵈ
                  → Pathᵈ Γ s t → Stᵈ Γ t → Stᵈ Γ t
  innerDoneMergeᵈ {s = s} k j p st
    with readMergeᵈ s (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing = st
  ... | just (l , a , [] , d) =
          let st₁ = record st { nodes = setCellᵈ k (merge-c {u = s} l (a ∸ 1) [] d)
                                          (Stᵈ.nodes st) }
          in if d ∧ (a ≤ᵇ 1) then finishPathᵈ p st₁ else st₁
  ... | just (l , a , q ∷ qs , d) =
          let i = Stᵈ.nextNode st
          in pushWorkᵈ (connect q (from-inner mergeᵒ k i ↠ᵈ p))
               (record st { nodes    = setCellᵈ k (merge-c {u = s} l a qs d) (Stᵈ.nodes st)
                           ; nextNode = suc i })

  subscribeInnerᵈ : ∀ {n} {Γ : Ctx n} {t u} → AllOpᵈ → Nodeᵈ
                  → Val Γ (obs u) → Pathᵈ Γ u t → Stᵈ Γ t → Stᵈ Γ t
  subscribeInnerᵈ {u = u} mergeᵒ k v p st
    with readMergeᵈ u (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing = st
  ... | just (just l , a , q , d) =
          if l ≤ᵇ a
          then record st { nodes = setCellᵈ k (merge-c (just l) a (q ++ v ∷ []) d)
                                     (Stᵈ.nodes st) }
          else (let i = Stᵈ.nextNode st
                in pushWorkᵈ (connect v (from-inner mergeᵒ k i ↠ᵈ p))
                     (record st { nodes    = setCellᵈ k (merge-c (just l) (suc a) q d)
                                               (Stᵈ.nodes st)
                                ; nextNode = suc i }))
  ... | just (nothing , a , q , d) =
          let i = Stᵈ.nextNode st
          in pushWorkᵈ (connect v (from-inner mergeᵒ k i ↠ᵈ p))
               (record st { nodes    = setCellᵈ k (merge-c nothing (suc a) q d)
                                         (Stᵈ.nodes st)
                           ; nextNode = suc i })

  subscribeInnerᵈ switchᵒ k v p st
    with readSwitchᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing = st
  ... | just (c , d) =
          let st₀ = cutCurrentᵈ c st
              i   = Stᵈ.nextNode st₀
          in pushWorkᵈ (connect v (from-inner switchᵒ k i ↠ᵈ p))
               (record st₀ { nodes    = setCellᵈ k (switch-c (just i) d) (Stᵈ.nodes st₀)
                            ; nextNode = suc i })

  subscribeInnerᵈ exhaustᵒ k v p st
    with readExhaustᵈ (lookupCellᵈ k (Stᵈ.nodes st))
  ... | nothing = st
  ... | just (true  , _) = st
  ... | just (false , d) =
          let i = Stᵈ.nextNode st
          in pushWorkᵈ (connect v (from-inner exhaustᵒ k i ↠ᵈ p))
               (record st { nodes    = setCellᵈ k (exhaust-c true d) (Stᵈ.nodes st)
                           ; nextNode = suc i })

  cutCurrentᵈ : ∀ {n} {Γ : Ctx n} {t} → Maybe Nodeᵈ → Stᵈ Γ t → Stᵈ Γ t
  cutCurrentᵈ nothing  st = st
  cutCurrentᵈ (just c) st = cutᵈ c st

  stepᵈ : ∀ {n} {Γ : Ctx n} {t} → Slots Γ → Workᵈ Γ t → Stᵈ Γ t → Stᵈ Γ t
  stepᵈ ins (deliver [] false p)      st = st
  stepᵈ ins (deliver [] true  p)      st = finishPathᵈ p st
  stepᵈ ins (deliver (v ∷ vs) done p) st =
    pushValueᵈ v p (record st { work = deliver vs done p ∷ Stᵈ.work st })
  stepᵈ ins (connect o p) st = subscribeᵈ ins o p st
  stepᵈ ins (finish p)    st = finishPathᵈ p st

------------------------------------------------------------------
-- The top line
------------------------------------------------------------------

pickᵈ : ∀ {n} {Γ : Ctx n} {t}
      → List (Arrivalᵈ Γ t) → Maybe (Arrivalᵈ Γ t × List (Arrivalᵈ Γ t))
pickᵈ []       = nothing
pickᵈ (a ∷ as) with pickᵈ as
... | nothing         = just (a , [])
... | just (b , rest) =
        let earlier = (Arrivalᵈ.tick a <ᵇ Arrivalᵈ.tick b)
                    ∨ ((Arrivalᵈ.tick a ≡ᵇ Arrivalᵈ.tick b)
                       ∧ (Arrivalᵈ.ordinal a <ᵇ Arrivalᵈ.ordinal b))
        in if earlier then just (a , b ∷ rest) else just (b , a ∷ rest)

nextArrivalᵈ : ∀ {n} {Γ : Ctx n} {t} → Stᵈ Γ t → Maybe (Stᵈ Γ t)
nextArrivalᵈ st with pickᵈ (Stᵈ.arrivals st)
... | nothing         = nothing
... | just (a , rest) =
        just (record st { now      = Arrivalᵈ.tick a
                        ; arrivals = rest
                        ; work     = Arrivalᵈ.item a ∷ Stᵈ.work st })

runWorkᵈ : ∀ {n} {Γ : Ctx n} {t} → ℕ → Slots Γ → Stᵈ Γ t → Stᵈ Γ t
runWorkᵈ zero    ins st = st
runWorkᵈ (suc b) ins st with Stᵈ.work st
... | []     = st
... | w ∷ ws = runWorkᵈ b ins (stepᵈ ins w (record st { work = ws }))

initᵈ : ∀ {n} {Γ : Ctx n} {t} → Slots Γ → Stᵈ Γ t
initᵈ {n} {Γ} {t} ins = go (toList (allFin n)) empty
  where
    empty : Stᵈ Γ t
    empty = record { now = 0 ; nodes = [] ; nextNode = 0 ; nextOrd = n
                   ; nextTok = suc n ; arrivals = [] ; multis = []
                   ; work = [] ; out = [] }
    go : List (Fin n) → Stᵈ Γ t → Stᵈ Γ t
    go []       st = st
    go (i ∷ is) st = go is (slotᵈ (ins i))
      where
        slotᵈ : Slot Γ (toℕ i) (lookup Γ i) → Stᵈ Γ t
        slotᵈ (scripted (hot async)) =
          record st { multis   = multiCell i true false [] ∷ Stᵈ.multis st
                    ; arrivals = Stᵈ.arrivals st
                                 ++ scheduleᵈ (toℕ i) 0 async (multiᵈ i) }
        slotᵈ (scripted (cold _ _)) = st
        slotᵈ (shared _) = record st { multis = multiCell i false false [] ∷ Stᵈ.multis st }

-- THE CASCADE'S BUDGET, DERIVED FROM THE FUEL RATHER THAN NAMED.  The
-- run's fuel counts ARRIVALS, which is what the TypeScript counts; the
-- budget counts stack entries, and nothing in the mirror corresponds
-- to it.  Deriving it keeps a single knob on the harness side.

-- AND IT IS A WEAKER TOTALITY DEVICE THAN THE ONE THE OTHER EVALUATOR
-- HAS, WHICH IS A FINDING ABOUT THE SPLIT RATHER THAN ABOUT THIS
-- NUMBER.  `runWorkᵈ` recurses structurally on this count, so the
-- cascade loop is total for free and a cascade that outruns the count
-- is TRUNCATED, silently and with no marker in the output.  The
-- envelope-carrying evaluator pays for the same totality with a
-- Girard-Tait reducibility candidate instead, which is a PROOF that
-- every cascade finishes and admits no truncation at all.
--
-- BUT NO THEOREM STANDS ON THIS ONE, WHICH IS WHERE THE SEVERITY
-- ACTUALLY LANDS.  Every module that proves anything reaches the
-- evaluator through `evaluate↓`, which is the candidate-backed one;
-- this machine's sole consumer is the CLI.  So the truncation is
-- exposed to the DIFFERENTIAL ORACLE rather than to the proof — a run
-- the count cuts short still reports agreement with TypeScript, which
-- is the one place a silent cut buys a false green.

-- AND THE CANDIDATE CANNOT BE POINTED AT THIS MACHINE, WHICH IS A
-- FACT ABOUT KIND AND NOT ABOUT VOCABULARY.  Reducibility is an
-- argument that a RELATION is inhabited, and this evaluator declares
-- none: it is a function whose termination argument IS the count, so
-- there is nothing here for the candidate to be about.  Giving it one
-- means a relational domain of its own before any of the candidate
-- transfers, which is why this is not the mechanical port it reads as.

-- AND THE REVERSE DIRECTION IS REFUSED FOR A REASON THAT IS NOT ABOUT
-- TOTALITY AT ALL.  This machine is a SECOND top line rather than a
-- retype of the other because the two disagree with real rxjs
-- differently — a burst collected whole against a depth-first push —
-- on a witness of one program.  That is recorded where the cutover it
-- blocks is defined, in `evaluate↓`'s own header.
budgetᵈ : Fuel → ℕ
budgetᵈ f = 512 * suc f

drainᵈ : ∀ {n} {Γ : Ctx n} {t} → Slots Γ → Fuel → Stᵈ Γ t → Stᵈ Γ t
drainᵈ ins zero    st = st
drainᵈ ins (suc f) st with nextArrivalᵈ st
... | nothing  = st
... | just st′ = drainᵈ ins f (runWorkᵈ (budgetᵈ f) ins st′)

-- THE TOP LINE.  Subscribing already runs the root's synchronous
-- burst, so the fuel pays for arrivals only — which is the mirror's
-- own loop, `for spent < fuel: deliverNextArrival()`.
evaluateᵈ : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Slots Γ → List (Val Γ t)
evaluateᵈ fuel e ins =
  Stᵈ.out (drainᵈ ins fuel
            (runWorkᵈ (budgetᵈ fuel) ins
              (pushWorkᵈ (connect (_ , e , []ᵉ) rootᵈ) (initᵈ ins))))
