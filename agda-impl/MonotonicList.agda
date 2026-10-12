{-# OPTIONS --guardedness #-}

-- THE DENOTATIONAL SEMANTICS.  An observable means a timeline: frames at
-- strictly increasing times, each frame a synchronous burst.  Everything
-- is coinductive — a timeline can have infinitely many frames, and a
-- single burst can be infinite (`ones`) or spin silently forever (a
-- deferred loop that emits nothing), so divergence is a VALUE here, not
-- an absence of one.
module MonotonicList where

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Lift; lower; 0ℓ) renaming (suc to lsuc)

open import AbstractObservable using (Obs; Later; FlatOp;
  cold; of; map; scan; takeWhile; merge; flatMap; share; shared; defer)

Time : Set
Time = ℕ

mutual
  -- A timeline from some point on.
  data ML (A : Set) : Set where
    done  : ML A                      -- completed
    quiet : ML A                      -- silent forever, never completes
    at    : Time → Burst A → ML A     -- the next frame

  -- One synchronous burst.
  data Burst (A : Set) : Set where
    emit  : A → Burst∞ A → Burst A
    stall : Burst∞ A → Burst A        -- a synchronous step emitting nothing
    close : ML∞ A → Burst A           -- the burst is over; the rest of the timeline

  record Burst∞ (A : Set) : Set where
    coinductive
    field force : Burst A

  record ML∞ (A : Set) : Set where
    coinductive
    field force : ML A

postulate
  -- Frame times strictly increase, and the first frame of a cold is at
  -- offset 0 when it bursts on subscribe.  Stated, not yet enforced by
  -- the type.
  Monotone : ∀ {A} → ML A → Set

data MonotonicList (A : Set) : Set where
  hot  : ML A → MonotonicList A       -- times are absolute
  cold : ML A → MonotonicList A       -- times are relative to subscribe

postulate
  -- What a subscriber arriving at time t sees: a cold shifted to t, a
  -- hot with everything before t dropped.
  observe : ∀ {A} → MonotonicList A → Time → ML A

-- The pure runtime's cold leaf IS a relative timeline, so a cold's
-- denotation is its own description.  Lifted only because the leaf slot
-- is `Set₁` (the IO leaf carries an existential `Internal`).
Timeline : Set → Set₁
Timeline A = Lift (lsuc 0ℓ) (ML A)

------------------------------------------------------------------------
-- The operators, as functions on timelines

postulate
  ofᴰ        : ∀ {A} → List A → MonotonicList A
  mapᴰ       : ∀ {A B} → (A → B) → MonotonicList A → MonotonicList B
  scanᴰ      : ∀ {A B} → (B → A → B) → B → MonotonicList A → MonotonicList B
  takeWhileᴰ : ∀ {A} → (A → Bool) → MonotonicList A → MonotonicList A
  mergeᴰ     : ∀ {A} → MonotonicList A → MonotonicList A → MonotonicList A
  -- Each inner's timeline is observed at the time of the outer emission
  -- that created it.
  flatMapᴰ   : ∀ {A B} → FlatOp → (A → MonotonicList B) → MonotonicList A → MonotonicList B
  -- No information yet: a subscribe burst that never closes.  The
  -- bottom of the approximation order, and also the honest meaning of a
  -- silent synchronous loop — the two coincide, as in any domain.
  ⊥ᴰ         : ∀ {A} → MonotonicList A

  -- SHARE IS THE OPEN QUESTION.  What a consumer of a ref-counted share
  -- sees depends on when the FIRST consumer connected and whether the
  -- count has since dropped to zero — facts about the other consumers,
  -- which a denotation computed one subterm at a time cannot see.  So
  -- the environment holds an abstract `Shared`, not a timeline, until
  -- this is designed.
  Shared     : Set → Set
  shareᴰ     : ∀ {A} → MonotonicList A → Shared A
  readShared : ∀ {A} → Shared A → MonotonicList A

DenEnv : List Set → Set₁
DenEnv = All Shared

------------------------------------------------------------------------
-- The denotation

-- APPROXIMANT n: the meaning with every path of more than n nested
-- `defer`s cut off at ⊥ᴰ.  The index is not gas — nothing runs out, and
-- no program's meaning depends on it — it is the approximation order
-- of domain theory, made explicit because the operators are opaque
-- functions here: a guarded `deferᴰ (♯ ⟦ l ⟧)` would be refused for the
-- same reason `subscribe` cannot recurse through `defer` — a total
-- operator may strip the guard.  (Sized types would hide the index in
-- the operators' types; Agda 2.8 refuses them under --safe --guardedness.)
--
-- Lexicographic on (n , tree): `defer` drops n, everything else is
-- structural.  The wiring, clause for clause the shape of `subscribe`.
⟦_⟧[_] : ∀ {Γ A} → Obs Timeline Γ A → ℕ → DenEnv Γ → MonotonicList A
⟦ o ⟧[ n ] = approx n o
  where
    approx : ∀ {Γ A} → ℕ → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
    approx n       (cold c)         ρ = cold (lower c)
    approx n       (of xs)          ρ = ofᴰ xs
    approx n       (map f s)        ρ = mapᴰ f (approx n s ρ)
    approx n       (scan f z s)     ρ = scanᴰ f z (approx n s ρ)
    approx n       (takeWhile p s)  ρ = takeWhileᴰ p (approx n s ρ)
    approx n       (merge s t)      ρ = mergeᴰ (approx n s ρ) (approx n t ρ)
    approx n       (flatMap op f s) ρ = flatMapᴰ op (λ a → approx n (f a) ρ) (approx n s ρ)
    approx n       (share s b)      ρ = approx n b (shareᴰ (approx n s ρ) ∷ ρ)
    approx n       (shared i)       ρ = readShared (lookup ρ i)
    approx zero    (defer l)        ρ = ⊥ᴰ
    approx (suc n) (defer l)        ρ = approx n (Later.force l) ρ

-- Information order on timelines: the left is the right with some
-- suffixes replaced by a burst that never closes, and finitely many
-- `stall`s inserted or dropped.
postulate
  _⊑_ : ∀ {A} → ML A → ML A → Set

  -- The least upper bound of a chain of approximants.
  lub : ∀ {A} → (ℕ → MonotonicList A) → MonotonicList A

-- THE meaning of a program.
⟦_⟧ : ∀ {Γ A} → Obs Timeline Γ A → DenEnv Γ → MonotonicList A
⟦ o ⟧ ρ = lub λ n → ⟦ o ⟧[ n ] ρ
