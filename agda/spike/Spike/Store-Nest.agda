------------------------------------------------------------------
-- KILL ATTEMPT: DOES THE ACCUMULATOR ARRAY RECOVER C ON A
-- SUBSCRIPTION THAT ALLOCATES?  IT DOES NOT.
--
-- `Spike.Store` kills C alone by exhibiting the asymmetry: a
-- subscription that allocates puts the burst's handles ABOVE the
-- caller's budget, so allocation order is not a descent.  What
-- survives there is a SEPARATION -- allocation in the driver, descent
-- in the subscription -- and one line of rxjs breaks it, because a
-- stored body may hold a fold of its own.
--
-- The candidate tested here: two telescopes, not one.  The STORE is
-- program text, fixed for the whole run; the ARRAY is accumulators,
-- grown during it.  The store index would then be a strictly higher
-- lex component than the array index, and allocating into the array
-- could not disturb the descent the hop spends.
--
-- THE CANDIDATE FAILS, AND IT FAILS TWICE.
--
-- FIRST, THE TELESCOPES ARE NOT INDEPENDENT.  An array cell holds an
-- accumulated VALUE, and under C a value that is an observable is a
-- handle -- so a cell mentions the store, and `Arr` is indexed by the
-- store width.  A hop that descends the store therefore has to bring
-- the array down with it, and no such truncation exists: a cell
-- naming a handle has no image at a width where that handle is not a
-- handle.  `truncation-loses` below is that refutation, and it is
-- exactly the accumulator `scan` over a stream of streams builds.
--
-- SECOND, AND FATALLY, THE KILL SIMPLY RELOCATES.  Held at a fixed
-- store with only the array growing, the run was rejected on two
-- calls and only two:
--
--     run (mergeAllᵉ e) → hop (<-wellFounded (wid (run a α e))) …
--     hop (accᵛ j ∷ vs) → wid (run (rec (toℕ<n j)) (α↓ α j) (α j))
--
-- Both are the caller's budget being re-manufactured because the
-- array widened under it -- which is `Spike.Store`'s asymmetry
-- verbatim, one component down.  The rejection is not a `with`
-- artifact: the result was a record read through projections, so
-- nothing was abstracted.  Note the first call: it does not even need
-- a subscribable cell.  `mergeAll` over a source that scans widens the
-- array before the hop begins, so the budget is spent before any
-- accumulator is read.
--
-- WHAT IS LEFT IS WHAT WAS ALREADY THERE.  `descends` below is green,
-- and it is `Spike.Store`'s separation with `Arr` written where
-- `Store` stood -- deliberately, because that is the finding: as a
-- carrier of subscribable text the array IS a store, and moving the
-- allocation from one to the other moves the kill with it.  The
-- accumulator array buys nothing for the allocating case.  Whatever
-- recovers C has to make allocation-during-subscription descend, and
-- a second telescope is not that.
------------------------------------------------------------------
module Spike.Store-Nest where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; _≟_)
open import Data.Nat.Properties using (<⇒≤; ≤∧≢⇒<; ≤-pred)
open import Data.Fin using (Fin; toℕ; inject≤; fromℕ<)
open import Data.Fin.Properties using (toℕ<n; toℕ-inject≤; toℕ-fromℕ<)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

------------------------------------------------------------------
-- (1) THE TELESCOPES ARE NOT INDEPENDENT
------------------------------------------------------------------

data HVal (n k : ℕ) : Set where
  natᴴ : ℕ → HVal n k
  hndᴴ : Fin n → HVal n k     -- a stored observable: program text
  accᴴ : Fin k → HVal n k     -- an accumulator: an array cell

data HExp (n k : ℕ) : Set where
  ofᴴ : List (HVal n k) → HExp n k

HArr : ℕ → ℕ → Set
HArr n k = (j : Fin k) → HExp n (toℕ j)

-- what a cell hands the hop when it is subscribed to
emitsL : ∀ {n k} → List (HVal n k) → List ℕ
emitsL []            = []
emitsL (natᴴ _ ∷ vs) = emitsL vs
emitsL (accᴴ _ ∷ vs) = emitsL vs
emitsL (hndᴴ h ∷ vs) = toℕ h ∷ emitsL vs

emits : ∀ {n k} → HExp n k → List ℕ
emits (ofᴴ vs) = emitsL vs

-- one cell at store width 1 holding handle 0: the accumulator a
-- `scan` over a stream of streams carries
α₁ : HArr 1 1
α₁ _ = ofᴴ (hndᴴ Data.Fin.zero ∷ [])

α₁-emits : emits (α₁ Data.Fin.zero) ≡ 0 ∷ []
α₁-emits = refl

-- at store width 0, no cell emits anything, whatever it holds
nothing-at-zero : ∀ {k} (e : HExp 0 k) → emits e ≡ []
nothing-at-zero (ofᴴ [])            = refl
nothing-at-zero (ofᴴ (natᴴ _ ∷ vs)) = nothing-at-zero (ofᴴ vs)
nothing-at-zero (ofᴴ (accᴴ _ ∷ vs)) = nothing-at-zero (ofᴴ vs)
nothing-at-zero (ofᴴ (hndᴴ () ∷ vs))

-- SO no store-truncation of the array preserves what its cells emit
truncation-loses :
  (T : HArr 1 1 → HArr 0 1) →
  ¬ (∀ (α : HArr 1 1) (j : Fin 1) → emits (T α j) ≡ emits (α j))
truncation-loses T pres =
  absurd (trans (sym (nothing-at-zero (T α₁ Data.Fin.zero)))
                (trans (pres α₁ Data.Fin.zero) α₁-emits))
  where absurd : [] ≡ 0 ∷ [] → ⊥
        absurd ()

------------------------------------------------------------------
-- (2) WHAT SURVIVES: THE SEPARATION, RESTATED OVER THE ARRAY.
-- The store is dropped -- fixed, it is inert -- so this is the array
-- alone, and it is `Spike.Store` with one name changed
------------------------------------------------------------------

data Val (k : ℕ) : Set where
  natᵛ : ℕ → Val k
  accᵛ : Fin k → Val k

data Exp (k : ℕ) : Set where
  ofᵉ       : List (Val k) → Exp k
  mergeAllᵉ : Exp k → Exp k

Arr : ℕ → Set
Arr k = (j : Fin k) → Exp (toℕ j)

wkV : ∀ {k k′} → k ≤ k′ → Val k → Val k′
wkV le (natᵛ x) = natᵛ x
wkV le (accᵛ j) = accᵛ (inject≤ j le)

wkL : ∀ {k k′} → k ≤ k′ → List (Val k) → List (Val k′)
wkL le []       = []
wkL le (v ∷ vs) = wkV le v ∷ wkL le vs

α↓ : ∀ {k} → Arr k → (j : Fin k) → Arr (toℕ j)
α↓ {k} α j i =
  subst Exp (toℕ-inject≤ i (<⇒≤ (toℕ<n j))) (α (inject≤ i (<⇒≤ (toℕ<n j))))

allocA : ∀ {k} → Arr k → Exp k → Arr (suc k)
allocA {k} α b j with k ≟ toℕ j
... | yes p  = subst Exp p b
... | no  ¬p = subst Exp (toℕ-fromℕ< lt) (α (fromℕ< lt))
  where lt : toℕ j < k
        lt = ≤∧≢⇒< (≤-pred (toℕ<n j)) (λ q → ¬p (sym q))

-- THE SUBSCRIPTION: width fixed, no allocation anywhere in it
run : ∀ {k} → Acc _<_ k → Arr k → Exp k → List (Val k)
hop : ∀ {k} → Acc _<_ k → Arr k → List (Val k) → List (Val k)

run a α (ofᵉ vs)      = vs
run a α (mergeAllᵉ e) = hop a α (run a α e)

hop a α []                    = []
hop a α (natᵛ x ∷ vs)         = natᵛ x ∷ hop a α vs
hop (acc rec) α (accᵛ j ∷ vs) =
  wkL (<⇒≤ (toℕ<n j)) (run (rec (toℕ<n j)) (α↓ α j) (α j)) ++ hop (acc rec) α vs

descends : ∀ {k} → Arr k → Exp k → List (Val k)
descends {k} = run (<-wellFounded k)

-- THE DRIVER: allocates, never subscribes.  Structural on the
-- delivery count, as `Spike.Store` found it must be
drive : ∀ {k} → ℕ → Arr k → Σ ℕ Arr
drive {k} zero    α = k , α
drive {k} (suc d) α = drive {suc k} d (allocA α (ofᵉ []))
