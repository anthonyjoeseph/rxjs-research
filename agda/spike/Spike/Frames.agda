------------------------------------------------------------------
-- THIRD SUBDIVISION: A VALUE AS (STATIC HANDLE, FRAME STACK).
--
-- `Spike.Store` and `Spike.Store-Nest` both die the same way: growth
-- during subscription moves an INDEX, so the caller's budget is
-- exceeded.  A frame stack is not an index -- it is inductive data
-- carried inside the value, so growth is a bigger term and recursion
-- on it is structural.  Nothing is allocated and no width exists to
-- exceed.  That is the whole of the candidate, and it is why it
-- looked different from the first two.
--
-- IT IS NOT DIFFERENT.  The subscription below is rejected, and the
-- reported calls are `apply κ (source h)` and the `sub` under
-- `concatMap`: an emitted value carries a stack the subscriber knows
-- nothing about.
--
-- AND THE MAP FRAME IS NOT THE CULPRIT, WHICH IS THE INFORMATIVE
-- HALF.  `Spike.Strata` refutes the type reading by exhibiting
-- `mapᵉ`'s unrelated source and target, so a stack of `mapF` and
-- `mrgF` failing reads at first as that refutation arriving again.
-- It is not: the same pair restricted to `mrgF` ALONE -- where the
-- stack is obs-layered and the type reading descends by construction
-- -- is rejected on the same calls.
--
-- WHAT IS LEFT IS THE ONE REPAIR, AND IT IS THE FIRST TWO AGAIN.  To
-- recover the descent the subscriber must know a BOUND on the stacks
-- its source may emit, so `Val` acquires a depth index and `sub`
-- descends on it.  That index is `depᵗ` -- a rank on values, which is
-- the single thing C exists to abolish -- and the accumulator of
-- `scanᵉ` at observable type grows its stack by one frame per
-- delivery, so no static bound exists to index it by.
--
-- THREE CARRIERS, ONE FAILURE: store index, array index, stack depth.
-- A quantity that grows during subscription ascends exactly where the
-- hop needs it to descend, and moving the growth to a new carrier
-- moves the failure with it.
------------------------------------------------------------------
module Spike.Frames where

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Product using (Σ)

data Ty : Set where
  natᵗ : Ty
  obs  : Ty → Ty

-- an operator applied to a stream of s, yielding a stream of t
data Frame : Ty → Ty → Set where
  mapF : ∀ {s t} → Frame s t        -- an opaque static map: s and t unrelated
  mrgF : ∀ {t} → Frame (obs t) t    -- mergeAll: the ONLY frame that hops

data Stack : Ty → Ty → Set where
  idS : ∀ {t} → Stack t t
  _▸_ : ∀ {r s t} → Stack r s → Frame s t → Stack r t

module _ (n : ℕ) (src : Fin n → Ty) where

  -- a runtime observable is a STATIC source plus a stack.  Nothing
  -- here is allocated: `h` indexes program text, fixed for the run
  Val : Ty → Set
  Val natᵗ    = ℕ
  Val (obs t) = Σ (Fin n) (λ h → Stack (src h) t)

  postulate
    source  : (h : Fin n) → List (Val (src h))
    reframe : ∀ {s t} → Val s → Val t

  -- the subscription these support is REFUTED; it is stated in this
  -- module's header rather than here, because it does not typecheck
