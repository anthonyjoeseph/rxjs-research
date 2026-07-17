module Rx.Evaluator where

open import Data.Bool    using (Bool; if_then_else_)
open import Data.Nat     using (zero; suc)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit    using (⊤)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Rx.Prim using (Tick; Fuel; Ordinal; Id; freshId; Source;
                           InstEvent; value; InstEmit; _at_from_; ObservableInput)
open import Rx.Exp  using (Ty; obs; _×ᵗ_; Ctx; Val; Closed; Fn)


------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

Inputs : ∀ {n} → Ctx n → Set
Inputs Γ = ∀ i → ObservableInput (Val Γ (lookup Γ i))

Stream : ∀ {n} → Ctx n → Ty → Set          -- flat, canonical emission order
Stream Γ t = List (InstEmit (Val Γ t))

Grouped : ∀ {n} → Ctx n → Ty → Set         -- batchSimultaneous's output
Grouped Γ t = List (InstEmit (List (Val Γ t)))
  -- one emit per instant, still a protocol citizen (re-batchable)

------------------------------------------------------------------
-- The evaluator and its global scheduler
------------------------------------------------------------------

postulate
  Sched   : ∀ {n} → Ctx n → Set
    -- live sources: pending arrivals keyed (tick, ordinal); hots
    -- registered at anchor 0, colds anchored at subscription tick,
    -- deferᵉ bodies at tick+1; ordinals minted in subscription order
  Arrival : ∀ {n} → Ctx n → Set

  sched-init : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Inputs Γ → Sched Γ
  sched-next : ∀ {n} {Γ : Ctx n} → Sched Γ
             → ⊤ ⊎ (Arrival Γ × Sched Γ)     -- min by (tick, ordinal), or empty
  arrTick    : ∀ {n} {Γ : Ctx n} → Arrival Γ → Tick
  arrOrd     : ∀ {n} {Γ : Ctx n} → Arrival Γ → Ordinal

  -- richer subscribe: called by evaluator clauses (switchAll on a new
  -- inner, merge on outer next, μ/defer unfolding, …).  Returns the
  -- sync burst — processed NOW, inside cascade `Id` (id-inheritance) —
  -- plus the schedule extended with the source's async future.
  arrSource : ∀ {n} {Γ : Ctx n} → Arrival Γ → Source
  arrVal    : ∀ {n} {Γ : Ctx n} → Arrival Γ → (s : Ty) → Val Γ s
    -- the payload, read at the chain's source element type.  Totality
    -- is a fiction: it is exact only because the registry invariant
    -- pairs a source only with chains rooted at its element type —
    -- the eventual EvalSt well-formedness predicate carries this

  sameSource : Source → Source → Bool
  NodeId     : Set                                        -- a node instance in the dynamic topology
  NodeSt     : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set   -- its operator states (scan accs, take counters, *All actives/queues)

------------------------------------------------------------------
-- Registration chains: the dynamic topology, rootward
------------------------------------------------------------------

data AllOp : Set where
  merge concat switch exhaust : AllOp

-- one operator the emission passes through, rootward.  shareᵉ and
-- deferᵉ contribute NO frame: share is counting-transparent (its
-- fan-out is registry multiplicity, one chain per subscriber) and
-- defer merely relays its body
data Frame {n} (Γ : Ctx n) : Ty → Ty → Set where
  map-f      : ∀ {s u} → Fn Γ [] [] [] s u → Frame Γ s u
  scan-f     : ∀ {s u} → Fn Γ [] [] [] (u ×ᵗ s) u → NodeId → Frame Γ s u
  take-f     : ∀ {s} → NodeId → Frame Γ s s
  from-inner : ∀ {s} → AllOp → NodeId → Frame Γ s s        -- exiting a subscribed inner
  thru-outer : ∀ {u} → AllOp → NodeId → Frame Γ (obs u) u  -- the value IS an inner obs: consumed, subscribed, burst grafted

data Path {n} (Γ : Ctx n) : Ty → Ty → Set where   -- source element type → root type
  root : ∀ {t} → Path Γ t t
  _↠_  : ∀ {s u t} → Frame Γ s u → Path Γ u t → Path Γ s t

Chain : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set
Chain {Γ = Γ} {t = t} e = Σ Ty (λ s → Path Γ s t)

record EvalSt {n} {Γ : Ctx n} {t} (e : Closed Γ t) : Set where
  field registry : List (Source × Chain e)   -- live registration chains, subscription order
        nodes    : NodeSt e

postulate
  -- richer subscribe: called by evaluator clauses (switchAll on a new
  -- inner, merge on outer next, μ/defer unfolding, …).  Returns the
  -- sync burst — processed NOW, inside cascade `Id` (id-inheritance) —
  -- plus the schedule extended with the source's async future, plus
  -- the state extended with the new registrations
  subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → Closed Γ u → Id → Tick
             → Sched Γ → EvalSt e
             → Stream Γ u × Sched Γ × EvalSt e

  st-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → EvalSt e

  -- the per-frame meat: map-f/scan-f/take-f do value work (take-f may
  -- CUT — emit close events, drop registrations, forward no values);
  -- thru-outer consumes each inner obs, subscribes it via subscribeE,
  -- and grafts its sync burst into the forwarded values; async futures
  -- are registered on the Sched.  Termination inside a frame is
  -- structural (finite bursts, μ behind deferᵉ), so no gas appears
  stepFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
            → Id → Frame Γ s u → List (Val Γ s) → Sched Γ → EvalSt e
            → List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e

-- the arrival's source's live chains, in subscription order
chainsOf : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
         → Arrival Γ → EvalSt e → List (Chain e)
chainsOf {e = e} a st = go (EvalSt.registry st)
  where
  go : List (Source × Chain e) → List (Chain e)
  go []             = []
  go ((s , c) ∷ r) = if sameSource (arrSource a) s then c ∷ go r else go r

-- one chain, ONE emit: fold the arrival's value rootward through the
-- frames, accumulating protocol events; a cut mid-path leaves the fold
-- running on an empty value list, so the emit is emptied, never
-- swallowed.  The envelope is assembled here and nowhere else
chainStep : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Id → Arrival Γ → Chain e → Sched Γ → EvalSt e
          → InstEmit (Val Γ t) × Sched Γ × EvalSt e
chainStep {Γ = Γ} {t = t} {e = e} id a (s , path) sched st =
  go path (arrVal a s ∷ []) [] sched st
  where
  go : ∀ {u} → Path Γ u t → List (Val Γ u) → List (InstEvent (Val Γ t))
     → Sched Γ → EvalSt e → InstEmit (Val Γ t) × Sched Γ × EvalSt e
  go root         vals evs sched st =
    ((evs ++ map value vals) at id from arrSource a) , sched , st
  go (f ↠ path′) vals evs sched st =
    let (vals′ , evs′ , sched′ , st′) = stepFrame id f vals sched st
    in go path′ vals′ (evs ++ evs′) sched′ st′

-- one arrival, count(source) emits: every live registration chain of
-- the arrival's source forwards EXACTLY ONE emit (possibly valueless),
-- in subscription order — the truthfulness invariant, made structural:
-- chainStep's result type is a single InstEmit, so cascade cannot
-- swallow or duplicate a chain's contribution
cascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
        → Arrival Γ → Id → Sched Γ → EvalSt e
        → Stream Γ t × Sched Γ × EvalSt e
cascade {Γ = Γ} {t = t} {e = e} a id sched st = go (chainsOf a st) sched st
  where
  go : List (Chain e) → Sched Γ → EvalSt e → Stream Γ t × Sched Γ × EvalSt e
  go []           sched st = [] , sched , st
  go (c ∷ chains) sched st =
    let (emit  , sched₁ , st₁) = chainStep id a c sched st
        (emits , sched₂ , st₂) = go chains sched₁ st₁
    in emit ∷ emits , sched₂ , st₂

-- fuel = ARRIVALS PROCESSED; each arrival's cascade runs to
-- quiescence (never truncated mid-batch).  The root subscription's
-- burst is free: fuel 0 still yields it.
evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Inputs Γ → Stream Γ t
evaluate {Γ = Γ} {t = t} fuel e ins =
  let (burst , sched₀ , st₀) =
        subscribeE e (freshId 0 0) 0 (sched-init e ins) (st-init e)
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