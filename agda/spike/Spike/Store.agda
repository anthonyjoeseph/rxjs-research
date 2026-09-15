------------------------------------------------------------------
-- THE STORE TELESCOPE: WHAT THE HOP COSTS, AND WHERE ALLOCATION MAY
-- HAPPEN.
--
-- An observable value is a HANDLE and the store is stratified by
-- construction — entry `i` is an expression over handles strictly
-- below `i`.  So "a body mentions only earlier handles" is the
-- store's TYPE, not an invariant to preserve, and `alloc` is total
-- with no side condition.  That is the cheap half and it holds.
--
-- THE EXPENSIVE HALF, AND IT IS A REFUTATION.  The hop descends on
-- the store index: subscribing to `h` runs `σ h`, which lives at
-- `toℕ h < n`.  That argument survives exactly as long as a run does
-- NOT allocate.  Let the run return a WIDENED store — which a fold
-- refolding an observable accumulator forces, since re-templating
-- mints an entry — and the burst's handles land above the caller's
-- budget.  Manufacturing the accessibility afresh at the widened
-- index is REFUSED by the termination checker, and so is the walk
-- that feeds a run's own output back to the hop.  A store does not
-- buy a descent; it RELOCATES the one a depth reading could not pay.
--
-- SO THE FINDING IS A SEPARATION, NOT A MEASURE.  Allocation is
-- confined to the fold DRIVER, which never subscribes; subscription
-- descends and never allocates.  Two recursions that do not
-- interleave, each accepted on its own, rather than one that cannot
-- be ordered.  `drive` and `runA` below are that split, and the
-- design obligation it puts on the evaluator is exactly this: a
-- subscription may not allocate.
--
-- AND THE DRIVER RECURSES ON THE DELIVERY COUNT.  Weakening REBUILDS
-- a list, so a driver written over the burst is refused for its
-- recursive argument — the de Bruijn tax arriving at the termination
-- checker rather than at a signature.  The count is what survives it.
------------------------------------------------------------------
module Spike.Store where


open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_; s≤s; z≤n)
open import Data.Nat.Properties using (<⇒≤; ≤-refl; ≤-trans; n≤1+n; ≤∧≢⇒<; ≤-pred)
open import Data.Fin using (Fin; toℕ; inject≤; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-inject≤; toℕ-fromℕ<)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Relation.Nullary using (yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

data Val (n : ℕ) : Set where
  natᵛ : ℕ → Val n
  hndᵛ : Fin n → Val n

data Exp (n : ℕ) : Set where
  ofᵉ       : List (Val n) → Exp n
  mergeAllᵉ : Exp n → Exp n

Store : ℕ → Set
Store n = (i : Fin n) → Exp (toℕ i)

wkV : ∀ {m n} → m ≤ n → Val m → Val n
wkV le (natᵛ x) = natᵛ x
wkV le (hndᵛ h) = hndᵛ (inject≤ h le)

wkL : ∀ {m n} → m ≤ n → List (Val m) → List (Val n)
wkL le []       = []
wkL le (v ∷ vs) = wkV le v ∷ wkL le vs

σ↓ : ∀ {n} → Store n → (h : Fin n) → Store (toℕ h)
σ↓ {n} σ h i =
  subst Exp (toℕ-inject≤ i (<⇒≤ (toℕ<n h))) (σ (inject≤ i (<⇒≤ (toℕ<n h))))

alloc : ∀ {n} → Store n → Exp n → Store (suc n)
alloc {n} σ b i with n ≟ toℕ i
... | yes p  = subst Exp p b
... | no  ¬p =
  let lt : toℕ i < n
      lt = ≤∧≢⇒< (≤-pred (toℕ<n i)) (λ q → ¬p (sym q))
  in subst Exp (toℕ-fromℕ< lt) (σ (fromℕ< lt))

------------------------------------------------------------------
-- SUBSCRIPTION — ALLOCATION-FREE, so the store it reads is the store
-- it returns to.  The hop spends `toℕ h < n`, which the telescope
-- supplies, and nothing else is needed: no domain predicate, and no
-- constructor quantifying over this function's own output.
------------------------------------------------------------------

runA : ∀ {n} → Acc _<_ n → Store n → Exp n → List (Val n)
hopA : ∀ {n} → Acc _<_ n → Store n → List (Val n) → List (Val n)

runA a σ (ofᵉ vs)      = vs
runA a σ (mergeAllᵉ e) = hopA a σ (runA a σ e)

hopA a σ []                    = []
hopA a σ (natᵛ x ∷ vs)         = hopA a σ vs
hopA (acc rec) σ (hndᵛ h ∷ vs) =
  wkL (<⇒≤ (toℕ<n h)) (runA (rec (toℕ<n h)) (σ↓ σ h) (σ h)) ++ hopA (acc rec) σ vs

run : ∀ {n} → Store n → Exp n → List (Val n)
run {n} = runA (<-wellFounded n)

------------------------------------------------------------------
-- THE DRIVER — the ONLY allocating recursion, and it is structural on
-- the burst.  Each delivery mints the next accumulator cell, whose
-- body is written against the store as it stood, so the new cell
-- references only earlier ones.  The refold's climb is the array
-- INDEX, and the index is a number the machine owns.
------------------------------------------------------------------

Drv : Set
Drv = Σ ℕ Store

-- AND THE DRIVER MUST RECURSE ON THE DELIVERY COUNT, NOT ON THE
-- BURST.  Weakening REBUILDS a list, so `wkL … vs` is not structurally
-- `vs` and a driver written over the burst is refused — the de Bruijn
-- tax arriving at the termination checker rather than at a signature.
-- The count is what survives it, and the count is exactly the carrier
-- the fold's per-delivery reservation was missing
drive : ∀ {n} → (k : ℕ) → Store n → Drv
drive {n} zero    σ = n , σ
drive     (suc k) σ = drive k (alloc σ (ofᵉ []))

-- the composition: the driver allocates and never subscribes, the
-- subscription descends and never allocates.  Each is accepted on its
-- own recursion, which is the whole content of the separation
foldThenRun : ∀ {n} → (k : ℕ) → Store n → Σ ℕ (λ m → List (Val m))
foldThenRun k σ with drive k σ
... | m , σ′ = m , run σ′ (ofᵉ [])
