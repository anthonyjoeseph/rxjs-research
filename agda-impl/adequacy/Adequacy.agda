{-# OPTIONS --guardedness #-}

-- THE LINK.  The pure runtime and the denotation agree: the limit of the
-- machine's prefixes is the meaning, observed at the root, with positions
-- forgotten down to ticks.  The meaning is `denotation.Denote`'s fold; the
-- simulation is run against `denotation.Unfold`'s stepper, a proof device,
-- and `unfolded` carries its reading to the fold's.
--
-- Both halves are read off one simulation between the machine's trace
-- and the events the root is shown (`Simulation`).  BELOW: every prefix's
-- record, positions and all, is placed against those events
-- (`operation.Placed`), so shows nothing they do not.  ABOVE: whatever
-- the meaning shows lies within some prefix, which shows the same.
module adequacy.Adequacy where

open import Data.List using ([])
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; Σ; proj₁; proj₂)

open import operation.Placed using (Up; ahead; framed; shows; placed-⊑)
open import operation.Machine using (module Machine)
open import operation.PureObservable using (PureObs)
open import adequacy.Simulation using (module Sim)
open import denotation.MonotonicList using (ML; observe; root; ticks)
open import denotation.Order using (_⊑_; _≃_; Shows; limit; limit-ub; limit-least; shows-≼; shows-cmp; cmp-long)
open import denotation.Denote using (⟦_⟧)
open import Data.List.Relation.Unary.All using ([])
open import denotation.Unfold using ([]) renaming (⟦_⟧ to ⟦_⟧ᵘ)

-- The pure run: the limit of the machine's prefixes.
run : ∀ {A} → PureObs [] A → ML A
run {A} o = limit λ n → Machine.prefix A n o

-- The stepper's meaning, as the run reports one.
meaning : ∀ {A} → PureObs [] A → ML A
meaning o = ticks (observe (⟦ o ⟧ᵘ []) root)

module Link (R : Set) where
  open Machine R using (prefix; reading; trace; begin; Read)
  open Sim R using (sim; placed; got)
  open Read

  postulate
    -- The meaning's ticks never fall.
    --
    -- RECOVERY: `git show a2e0bb8b` restores `<ᵖ-trans`, `<ᵖ-irrefl` and
    --   `<ᵖ-ix` in `denotation.MonotonicList`: positions strictly ordered,
    --   and an earlier one at no later a tick.
    ticks-up : (o : PureObs [] R) → Up 0 (observe (⟦ o ⟧ᵘ []) root)

  -- THE UPPER HALF: whatever the meaning shows, some prefix shows.  It
  -- shows as many items, and they are the meaning's.
  reaches : (o : PureObs [] R) → ∀ {is} → Shows (meaning o) is → Σ ℕ λ n → Shows (prefix n o) is
  reaches o s with got 0 (ahead s) (sim o)
  ... | n , long = n , shows-≼ (cmp-long (shows-cmp s (shows (ticks-up o) (placed n 0 (sim o)))) long) (framed (log r) (ending r))
    where r = reading n 0 (trace (begin o))

  -- Each prefix is below the meaning.
  complete : (o : PureObs [] R) (n : ℕ) → prefix n o ⊑ meaning o
  complete o n = placed-⊑ (ticks-up o) (placed n 0 (sim o))

postulate
  -- The stepper and the fold show the same: each value at its tick, in
  -- order, then completion or silence.  The stepper mirrors every
  -- operator's `MonotonicList` clause but `connect`'s, which feeds its
  -- joiners from one run where `connectᴰ` hands each the whole hot run.
  unfolded : ∀ {A} (o : PureObs [] A) → meaning o ≃ ticks (observe (⟦ o ⟧ []) root)

adequacy : ∀ {A} (o : PureObs [] A) → run o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacy {A} o = (λ s → proj₁ (unfolded o) (limit-least (prefix-chain o) (complete o) s))
               , λ s → limit-ub (prefix-chain o) (proj₁ (reaches o (proj₂ (unfolded o) s))) (proj₂ (reaches o (proj₂ (unfolded o) s)))
  where open Link A
        open Sim A using (prefix-chain)
