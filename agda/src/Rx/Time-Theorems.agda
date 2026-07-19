module Rx.Time-Theorems where

open import Data.List    using (List)
open import Data.Product using (_×_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Fuel; InstEmit)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Evaluator using (Sched; Arrival; EvalSt; Slots; Stream; evaluate)


------------------------------------------------------------------
-- Isolation (locked-in-time, unaware-of-each-other), against the
-- single evaluator's node-indexed state
------------------------------------------------------------------

postulate
  Node    : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Set
  NodeSt  : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Node e → Set
  Inbox   : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) → Node e → Set

  inboxOf : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
          → EvalSt e → Arrival Γ → (v : Node e) → Inbox e v
  stAt    : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
          → EvalSt e → (v : Node e) → NodeSt e v
  cascade : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t)
          → EvalSt e → Sched Γ → Arrival Γ
          → EvalSt e × Sched Γ × Stream Γ t     -- one arrival, to quiescence
  δ       : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (v : Node e)
          → Inbox e v → NodeSt e v → NodeSt e v

  locality :        -- each node's next state factors through its own inbox+state
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (σ : EvalSt e) (s : Sched Γ)
      (a : Arrival Γ) (v : Node e) →
    stAt e (proj₁ (cascade e σ s a)) v ≡ δ e v (inboxOf e σ a v) (stAt e σ v)

  non-interference :  -- other nodes reach v only via delivered emissions
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (σ₁ σ₂ : EvalSt e) (s : Sched Γ)
      (a : Arrival Γ) (v : Node e) →
    stAt e σ₁ v ≡ stAt e σ₂ v → inboxOf e σ₁ a v ≡ inboxOf e σ₂ a v →
    stAt e (proj₁ (cascade e σ₁ s a)) v ≡ stAt e (proj₁ (cascade e σ₂ s a)) v




------------------------------------------------------------------
-- Timing invariance: ticks are logical order, not wall-clock.
-- Any re-timing preserving the arbitration order (tick, ordinal)
-- of all arrivals — including collisions — is invisible.
------------------------------------------------------------------

postulate
  Retiming : Set                              -- monotone Tick → Tick, order- and
  retime   : ∀ {n} {Γ : Ctx n}                -- coincidence-preserving on arrivals;
           → Retiming → Slots Γ → Slots Γ    -- acts on scripted slots, fixes shared defs

  timing-invariance :
    ∀ {n} {Γ : Ctx n} {t} (ρ : Retiming) (fuel : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) →
    evaluate fuel e (retime ρ ins) ≡ evaluate fuel e ins
    -- ≡, not ≈: ids mint from ARRIVAL POSITION (the drain counter),
    -- so an arbitration-order-preserving retiming preserves the ids
    -- themselves — the recommendation this comment used to make is
    -- now the implementation


------------------------------------------------------------------
-- Trace equivalence up to id renaming (the harness's relation)
------------------------------------------------------------------

postulate
  _≈ˢ_ : ∀ {A} → List (InstEmit A) → List (InstEmit A) → Set
  _≈ᵍ_ : ∀ {A} → List (InstEmit (List A)) → List (InstEmit (List A)) → Set