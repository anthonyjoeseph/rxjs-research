module Rx.Prim where

open import Data.Nat     using (ℕ)
open import Data.List    using (List)

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