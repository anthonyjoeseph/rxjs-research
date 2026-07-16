module Rx where

open import Data.Nat     using (ℕ)

------------------------------------------------------------------
-- Time, ids, emissions
------------------------------------------------------------------

Tick Fuel Ordinal : Set
Tick = ℕ ; Fuel = ℕ ; Ordinal = ℕ

postulate
  Id      : Set
  freshId : Tick → Ordinal → Id     -- deterministic minting from arrival identity

record InstEmit (A : Set) : Set where
  constructor _at_
  field val : A
        iid : Id

------------------------------------------------------------------
-- Timed inputs (delta-encoded; real gap = suc wait, so per-source
-- strict monotonicity holds by construction; ticks are logical
-- order, not wall-clock — see timing-invariance)
------------------------------------------------------------------

record Timed (A : Set) : Set where
  constructor after_,_
  field wait : ℕ            -- gap = suc wait
        val  : A

data ObservableInput (A : Set) : Set where
  hot  : (async : List (Timed A))                 → ObservableInput A   -- anchor 0
  cold : (sync : List A) (async : List (Timed A)) → ObservableInput A   -- anchor = subscription tick


------------------------------------------------------------------
-- Types (sums included, for Either/error and sentinel patterns)
------------------------------------------------------------------

data Ty : Set where
  unitᵗ boolᵗ natᵗ : Ty
  _×ᵗ_ _+ᵗ_ : Ty → Ty → Ty
  obs : Ty → Ty

Ctx : ℕ → Set
Ctx n = Vec Ty n

postulate
  PrimOp : Ty → Ty → Set    -- TODO: concrete datatype before the JSON bridge


------------------------------------------------------------------
-- Syntax.  Contexts: Γ inputs, Δᵍ guarded μ-vars, Δ usable μ-vars,
-- Θ value vars.  μᵉ binds into Δᵍ; deferᵉ is the sole gate moving
-- Δᵍ into scope — synchronous self-reference is a type error.
------------------------------------------------------------------

mutual

  data Exp {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    input      : (i : Fin n) → Exp Γ Δᵍ Δ Θ (lookup Γ i)
    ofᵉ        : ∀ {t} → List (Tm Γ Δᵍ Δ Θ t) → Exp Γ Δᵍ Δ Θ t
    emptyᵉ     : ∀ {t} → Exp Γ Δᵍ Δ Θ t
    mapᵉ       : ∀ {s t} → Fn Γ Δᵍ Δ Θ s t → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
    takeᵉ      : ∀ {t} → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ t
                 -- count is a term: evaluated once, at subscription time
    scanᵉ      : ∀ {s t} → Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t → Tm Γ Δᵍ Δ Θ t
               → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
    shareᵉ     : ∀ {t} → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ t
    mergeAllᵉ concatAllᵉ switchAllᵉ exhaustAllᵉ :
                 ∀ {t} → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
    μᵉ         : ∀ {t} → Exp Γ (t ∷ Δᵍ) Δ Θ t → Exp Γ Δᵍ Δ Θ t
    varᵉ       : ∀ {t} → t ∈ Δ → Exp Γ Δᵍ Δ Θ t
    deferᵉ     : ∀ {t} → Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t
                 -- subscribe at tick k ⇒ body subscribed at k+1, fresh ids

  data Tm {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    varᵗ  : ∀ {t} → t ∈ Θ → Tm Γ Δᵍ Δ Θ t
    unit̂  : Tm Γ Δᵍ Δ Θ unitᵗ
    bool̂  : Bool → Tm Γ Δᵍ Δ Θ boolᵗ
    nat̂   : ℕ → Tm Γ Δᵍ Δ Θ natᵗ
    pairᵗ : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s ×ᵗ t)
    fstᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ s
    sndᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ t
    inlᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    inrᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    caseᵗ : ∀ {s t u} → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
          → Tm Γ Δᵍ Δ (s ∷ Θ) u → Tm Γ Δᵍ Δ (t ∷ Θ) u → Tm Γ Δᵍ Δ Θ u
    ifᵗ   : ∀ {t} → Tm Γ Δᵍ Δ Θ boolᵗ → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ t
          → Tm Γ Δᵍ Δ Θ t
    primᵗ : ∀ {s t} → PrimOp s t → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t
    strmᵗ : ∀ {t} → Exp Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (obs t)

  Fn : ∀ {n} → Ctx n → List Ty → List Ty → List Ty → Ty → Ty → Set
  Fn Γ Δᵍ Δ Θ s t = Tm Γ Δᵍ Δ (s ∷ Θ) t

  Val : ∀ {n} → Ctx n → Ty → Set
  Val Γ unitᵗ    = ⊤
  Val Γ boolᵗ    = Bool
  Val Γ natᵗ     = ℕ
  Val Γ (s ×ᵗ t) = Val Γ s × Val Γ t
  Val Γ (s +ᵗ t) = Val Γ s ⊎ Val Γ t
  Val Γ (obs t)  = Exp Γ [] [] [] t     -- runtime observables are closed exprs

Closed : ∀ {n} → Ctx n → Ty → Set
Closed Γ t = Exp Γ [] [] [] t

postulate   -- substitution plumbing (finite structural recursions; define later)
  evalTm  : ∀ {n} {Γ : Ctx n} {t} → Tm Γ [] [] [] t → Val Γ t
  applyFn : ∀ {n} {Γ : Ctx n} {s t} → Fn Γ [] [] [] s t → Val Γ s → Val Γ t
  unfoldμ : ∀ {n} {Γ : Ctx n} {t} → Exp Γ (t ∷ []) [] [] t → Closed Γ t
  wkᵍ     : ∀ {n} {Γ : Ctx n} {g Δᵍ Δ Θ t}
          → Exp Γ Δᵍ Δ Θ t → Exp Γ (g ∷ Δᵍ) Δ Θ t     -- context weakening

------------------------------------------------------------------
-- Inputs, canonical stream, traces
------------------------------------------------------------------

Inputs : ∀ {n} → Ctx n → Set
Inputs Γ = ∀ i → ObservableInput (Val Γ (lookup Γ i))

Stream : ∀ {n} → Ctx n → Ty → Set          -- flat, canonical emission order
Stream Γ t = List (InstEmit (Val Γ t))

Grouped : ∀ {n} → Ctx n → Ty → Set         -- batchSimultaneous's output
Grouped Γ t = List (List (InstEmit (Val Γ t)))

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

  -- fuel = ARRIVALS PROCESSED; each arrival's cascade runs to
  -- quiescence (never truncated mid-batch); cascade termination is
  -- structural (rootward propagation, finite bursts, μ behind deferᵉ),
  -- so no gas appears in the semantics
  evaluate : ∀ {n} {Γ : Ctx n} {t} → Fuel → Closed Γ t → Inputs Γ → Stream Γ t


------------------------------------------------------------------
-- Evaluator-level theorems (tested against TS, proven where cheap)
------------------------------------------------------------------

postulate
  -- fuel is arrivals: processing more arrivals only extends the stream
  fuel-coherent :
    ∀ {n} {Γ : Ctx n} {t} (f₁ f₂ : Fuel) → f₁ ≤ f₂ →
    (e : Closed Γ t) (ins : Inputs Γ) →
    Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)

  -- causality: agreeing input prefixes (arrivals before tick k) give
  -- agreeing output prefixes
  truncateIn : ∀ {A} → Tick → ObservableInput A → ObservableInput A
  emittedBefore : ∀ {n} {Γ : Ctx n} {t} → Tick → Stream Γ t → Stream Γ t

  causality :
    ∀ {n} {Γ : Ctx n} {t} (k : Tick) (fuel : Fuel)
      (e : Closed Γ t) (ins₁ ins₂ : Inputs Γ) →
    (∀ i → truncateIn k (ins₁ i) ≡ truncateIn k (ins₂ i)) →
    emittedBefore k (evaluate fuel e ins₁)
      ≡ emittedBefore k (evaluate fuel e ins₂)

  -- μ laws
  μ-unfold :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Inputs Γ) →
    evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins

  μ-guarded :   -- k arrivals force ≤ k unfoldings (syntactic, via deferᵉ gate)
    ∀ {n} {Γ : Ctx n} {t} (k : Fuel)
      (e : Exp Γ (t ∷ []) [] [] t) (ins : Inputs Γ) →
    evaluate k (μᵉ e) ins ≡ evaluate k (unfoldμ e) ins

  -- deferᵉ's temporal law (≈ because the body's ids are re-minted)
  defer-shift :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Inputs Γ) →
    ⊤   -- state as: stream of (deferᵉ e) ≈ stream of e with ticks +1


------------------------------------------------------------------
-- Id discipline: the bridge premise.  formal-verification says the
-- partition matches the ids; THIS says the ids mean provenance.
------------------------------------------------------------------

postulate
  _⊆ᵢ_ : List Id → List Id → Set

  -- every id in the output stream is the id of some arrival's cascade;
  -- sync-spawned inners inherit, never mint
  id-inheritance :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Inputs Γ) →
    ⊤   -- state as: ids(evaluate fuel e ins) ⊆ᵢ freshId-image of arrivals

  -- distinct arrivals never share an id (freshId injective on (tick,ordinal))
  id-fresh : ∀ (t₁ t₂ : Tick) (o₁ o₂ : Ordinal) →
             freshId t₁ o₁ ≡ freshId t₂ o₂ → (t₁ ≡ t₂) × (o₁ ≡ o₂)



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
  retime   : ∀ {n} {Γ : Ctx n}                -- coincidence-preserving on arrivals
           → Retiming → Inputs Γ → Inputs Γ

  timing-invariance :
    ∀ {n} {Γ : Ctx n} {t} (ρ : Retiming) (fuel : Fuel)
      (e : Closed Γ t) (ins : Inputs Γ) →
    evaluate fuel e (retime ρ ins) ≡ evaluate fuel e ins
    -- ≡, not ≈: ids come from (tick, ordinal); if freshId uses the raw
    -- tick, weaken to ≈ or mint from arrival ORDINAL POSITION instead —
    -- recommend the latter, then ≡ stands



------------------------------------------------------------------
-- Trace equivalence up to id renaming (the harness's relation)
------------------------------------------------------------------

postulate
  _≈ˢ_ : ∀ {A} → List (InstEmit A) → List (InstEmit A) → Set
  _≈ᵍ_ : ∀ {A} → List (List (InstEmit A)) → List (List (InstEmit A)) → Set