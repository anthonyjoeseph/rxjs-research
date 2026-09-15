-- WITHIN ONE SYNCHRONOUS BURST: the accumulator CHAIN carries the
-- descent where the count cannot -- FOR A PURE STEP, AND NOT FOR A
-- SUBSCRIBING ONE.
--
-- `Spike.Nodes` orders across instants and owes `c < c` inside one.
-- The chain `of(1,2,3) |> scan((acc,x) => acc |> map(+x))` builds is
-- real -- the third accumulator is the second wrapped once more -- and
-- the question was whether it is a SUBTERM or re-enters through an
-- opaque boundary, which is what killed `Spike.Frames`.
--
-- IT IS A SUBTERM, AND THE SPLIT IS EXACTLY THE STEP FUNCTION.  The
-- constructor turns the module green with `accᴹ` untouched.  So a fold
-- whose step MAPS the accumulator descends structurally on the chain,
-- and a fold whose step SUBSCRIBES to it does not -- the map step
-- consumes its predecessor, the mergeMap step subscribes to what its
-- predecessor emitted, and only the first is a subterm.
--
-- The two are indistinguishable from outside: both rxjs programs emit
-- 1, 3, 6 on the same source, and differ only in whether the step is
-- `map(v => v + x)` or `mergeMap(v => of(v + x))`.
module Spike.Burst where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Nat.Properties using (<⇒≤; ≤-trans)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

module _ (n : ℕ) where

  data Val : ℕ → Set where
    natᵛ : ∀ {c} → ℕ → Val c
    -- built at a STRICTLY EARLIER instant: `Spike.Nodes`' case
    obsᵛ : ∀ {c} → Fin n → (d : ℕ) → d < c → Val c
    -- built EARLIER IN THIS BURST: node h applied to the previous
    -- accumulator, which is a SUBTERM
    accᴹ : ∀ {c} → Fin n → Val c → Val c    -- a map step: no hop
    -- (a `accᴴ` mergeMap step stood here; it is what the header reports)

  postulate
    srcOf : (h : Fin n) → (d : ℕ) → List (Val d)
    mapOf : ∀ {c} → Fin n → Val c → Val c

  wkV : ∀ {c c′} → c ≤ c′ → Val c → Val c′
  wkL : ∀ {c c′} → c ≤ c′ → List (Val c) → List (Val c′)
  wkV le (natᵛ x)       = natᵛ x
  wkV le (obsᵛ h d lt)  = obsᵛ h d (≤-trans lt le)
  wkV le (accᴹ h v)     = accᴹ h (wkV le v)
  wkL le []             = []
  wkL le (v ∷ vs)       = wkV le v ∷ wkL le vs

  subV : ∀ {c} → Acc _<_ c → Val c → List (Val c)
  hopL : ∀ {c} → Acc _<_ c → List (Val c) → List (Val c)

  subV a         (natᵛ x)      = natᵛ x ∷ []
  subV (acc rec) (obsᵛ h d lt) = wkL (<⇒≤ lt) (hopL (rec lt) (srcOf h d))
  subV a         (accᴹ h v)    = map (mapOf h) (subV a v)

  hopL a []       = []
  hopL a (v ∷ vs) = subV a v ++ hopL a vs
