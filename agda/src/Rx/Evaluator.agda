module Rx.Evaluator where

open import Data.Nat     using (zero; suc)
open import Data.List    using (List; []; _++_)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_)
open import Data.Unit    using (⊤)
open import Data.Sum     using (_⊎_; inj₁; inj₂)

open import Rx.Prim using (Tick; Fuel; Ordinal; Id; freshId; InstEmit; ObservableInput)
open import Rx.Exp  using (Ty; Ctx; Val; Closed)


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
  EvalSt     : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set   -- all node states
  subscribeE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → Closed Γ u → Id → Tick
             → Sched Γ → EvalSt e
             → Stream Γ u × Sched Γ × EvalSt e

  st-init : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → EvalSt e

  -- the meat: routes the arrival's value to its live source's node,
  -- runs the operator logic to quiescence inside cascade Id
  -- (re-subscribing via subscribeE for μ-unfolding, deferᵉ bodies,
  -- *All inners); termination is structural (rootward propagation,
  -- finite bursts, μ behind deferᵉ), so no gas appears here
  cascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Arrival Γ → Id → Sched Γ → EvalSt e
          → Stream Γ t × Sched Γ × EvalSt e

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