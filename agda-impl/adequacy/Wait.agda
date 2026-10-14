{-# OPTIONS --guardedness --large-indices #-}

-- ONE STEP OF THE SIMULATION: the machine's next step against the
-- meaning's, matched events and paired silent steps guarded, a side's
-- lone silent step inductive, so each side passes finitely many alone.
-- `Rel` is where the corecursion re-enters.
module adequacy.Wait where

open import denotation.MonotonicList using (tick)
open import denotation.Unfold using (Node; outˢ; skipˢ; endˢ; hushˢ) renaming (step to stepᵁ; Step to Stepᵁ)
open import operation.Machine using (module Machine)

module Waiting (R : Set) where
  open Machine R using (Mach; Step; silent; value; complete; drained; step)

  module _ {ℓ} (Rel : Mach → Node R → Set ℓ) where
    data Wait : Step → Stepᵁ R → Set ℓ where
      both  : ∀ {m c p} → Rel m c → Wait (silent m) (skipˢ p c)
      outs  : ∀ {m c p a} → Rel m c → Wait (value (tick p) p a m) (outˢ p a c)
      ends  : ∀ {p} → Wait (complete p) (endˢ p)
      idles : Wait drained hushˢ
      left  : ∀ {m s} → Wait (step m) s → Wait (silent m) s
      right : ∀ {t c p} → Wait t (stepᵁ c) → Wait t (skipˢ p c)
