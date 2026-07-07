-- The SPEC's batchSimultaneous: the referee.
--
-- It receives the ENTIRE Emissions record — past and future — and may
-- "cheat" freely: read timestamps, look ahead, sort. Its job is to
-- define the right answer, not to be computable by a subscriber.
--
-- Shape: a timed denotation ⟦_⟧ maps every Exp to a MonotonicList Val
-- (its complete timed emission history), by structural recursion whose
-- per-primitive combinators are the named postulates below. batchSpec
-- then groups equal times. Discharging a postulate here = transcribing
-- the corresponding v1 combinator (agda/v1/src/Burst.agda) into the
-- MonotonicList discipline.
module Spec.Batch-Simultaneous where

open import Prelude
open import Shared-Types
open import Spec.MonotonicList

------------------------------------------------------------------------
-- timed observables, and cold inner streams as functions of their
-- subscription time (the device that makes burst batching compositional)

TObs : Set
TObs = MonotonicList Val

Inner : Set
Inner = Time → TObs

TObsS : Set
TObsS = MonotonicList Inner

-- a share environment assigns every slot its connection instant and its
-- connected emission history
Slot : Set
Slot = Time × TObs

Env : Set
Env = ℕ → Slot

extendEnv : Slot → Env → Env
extendEnv s ρ zero    = s
extendEnv s ρ (suc i) = ρ i

ρ₀ : Env
ρ₀ _ = (t₀ , emptyM)

------------------------------------------------------------------------
-- the per-primitive combinators: every remaining piece of spec work,
-- as a typed hole (v1 counterparts named alongside)

postulate
  -- hot histories: subscribing at t sees the strict suffix after t
  -- (v1: filterAfter)
  filterAfterT : Time → TObs → TObs
  -- the complete timed history of source subject i: its sync flush at
  -- t₀, its k-th async firing at tick k+1 (v1: envOf / slotEmits)
  srcT         : {n : ℕ} → Fin n → Emissions n → TObs
  -- (v1: ofB — every value at the subscription instant)
  ofT          : List Val → Time → TObs
  -- (v1: mapT — times preserved, values mapped)
  mapT         : (Val → Val) → TObs → TObs
  -- (v1: scanT — times preserved, values folded)
  scanT        : (Val → Val → Val) → Val → TObs → TObs
  -- (v1: takeB/takeCloseB — first k emissions, close at the k-th)
  takeT        : ℕ → Time → TObs → TObs
  -- a ref of a connected slot (v1: refView — the connecting ref replays
  -- from connection, later refs see the strict suffix)
  refT         : Bool → Slot → Time → TObs
  -- the four joins over a timed stream of inner templates
  -- (v1: mergeAllT / concatAllT / switchAllT / exhaustAllT)
  mergeAllT    : TObsS → Time → TObs
  concatAllT   : TObsS → Time → TObs
  switchAllT   : TObsS → Time → TObs
  exhaustAllT  : TObsS → Time → TObs
  -- stream-of-streams introduction (v1: ⟦_⟧S cases)
  ofST         : List Inner → Time → TObsS
  mapST        : (Val → Inner) → TObs → TObsS

------------------------------------------------------------------------
-- the denotation: real structural recursion, holes only in the
-- combinators above. ⟦ e ⟧ em ρ t = the timed history observed by
-- subscribing e at time t, under share environment ρ, in the world em.

⟦_⟧ : {n : ℕ} → Exp n → Emissions n → Env → Time → TObs
⟦_⟧S : {n : ℕ} → ExpS n → Emissions n → Env → Time → TObsS
-- list denotation spelled out structurally (a `map` lambda would hide
-- the descent from the termination checker)
⟦_⟧L : {n : ℕ} → List (Exp n) → Emissions n → Env → List Inner

⟦ srcE i        ⟧ em ρ t = filterAfterT t (srcT i em)
⟦ emptyE        ⟧ em ρ t = emptyM
⟦ ofE vs        ⟧ em ρ t = ofT vs t
⟦ shareE f i    ⟧ em ρ t = refT f (ρ i) t
⟦ letShareE s b ⟧ em ρ t = ⟦ b ⟧ em (extendEnv (t , ⟦ s ⟧ em ρ t) ρ) t
⟦ mapE f e      ⟧ em ρ t = mapT f (⟦ e ⟧ em ρ t)
⟦ takeE k e     ⟧ em ρ t = takeT k t (⟦ e ⟧ em ρ t)
⟦ scanE f z e   ⟧ em ρ t = scanT f z (⟦ e ⟧ em ρ t)
⟦ mergeAllE ss  ⟧ em ρ t = mergeAllT (⟦ ss ⟧S em ρ t) t
⟦ concatAllE ss ⟧ em ρ t = concatAllT (⟦ ss ⟧S em ρ t) t
⟦ switchAllE ss ⟧ em ρ t = switchAllT (⟦ ss ⟧S em ρ t) t
⟦ exhaustAllE ss ⟧ em ρ t = exhaustAllT (⟦ ss ⟧S em ρ t) t

⟦ ofS es   ⟧S em ρ t = ofST (⟦ es ⟧L em ρ) t
⟦ mapS f e ⟧S em ρ t = mapST (λ v u → ⟦ f v ⟧ em ρ u) (⟦ e ⟧ em ρ t)

⟦ []     ⟧L em ρ = []
⟦ e ∷ es ⟧L em ρ = (λ u → ⟦ e ⟧ em ρ u) ∷ ⟦ es ⟧L em ρ

------------------------------------------------------------------------
-- batching: group equal adjacent times. Stated over the raw list so the
-- verification theorem can rewrite through it; MonotonicList is what
-- makes "adjacent" the same as "equal anywhere".

postulate
  batchSpecL : List (Time × Val) → List (List Val)

batchSpec : TObs → Subscription (List Val)
batchSpec o = batchSpecL (list o)

------------------------------------------------------------------------
-- THE SPEC. Whole-input, clairvoyant, one line.

spec-batchSimultaneous : {n : ℕ} → Emissions n → Exp n → Subscription (List Val)
spec-batchSimultaneous em e = batchSpec (⟦ e ⟧ em ρ₀ t₀)
