{-# OPTIONS --guardedness #-}

-- THE LINK, ON THE STATE-TREE ENGINE.  The pure semantics the harness
-- runs (`operation.StateTree.Pure`) agrees with the denotation: the limit
-- of its prefixes, each read to as many ticks as steps, is the meaning
-- observed at the root, with positions forgotten down to ticks.
--
-- It stands on `adequacy.Adequacy`, proven of the heap machine, and on
-- the two engines showing the same run.  That bridge is the gap: the
-- state tree mirrors each kernel node for node, so the two runs are one
-- run read through two configurations.
module adequacy.StateTree where

open import Data.List using ([])
open import Data.Product using (_,_)

open import adequacy.Adequacy using (run; adequacy)
open import operation.PureObservable using (PureObs)
open import operation.StateTree.Pure using () renaming (run to prefixˢ)
open import denotation.MonotonicList.Events using (ML; root)
open import denotation.MonotonicList using (observe; ticks)
open import denotation.Order using (_≃_; limit)
open import denotation.Denote using (⟦_⟧)

-- The pure semantics' run: the limit of its prefixes, the n-th read for n
-- steps up to tick n.
runˢ : ∀ {A} → PureObs [] A → ML A
runˢ o = limit λ n → prefixˢ n n o

postulate
  -- The state tree's run shows what the heap machine's does.
  --
  -- RECOVERY: `git show 4b041908` restores, under `agda-impl/spike/`, a
  --   prototype of this machine with the research for proving the link
  --   over it directly: every path it follows lands (`StateTree3Valid`),
  --   its shown positions only move forward (`StateTree3Order`), the
  --   ghost computed from a quiet configuration (`StateTree3Ghost`),
  --   nothing the ghost holds before what was shown (`StateTree3Least`),
  --   and scan and takeWhile keeping what their sources hold
  --   (`StateTree3Kept`).
  engines : ∀ {A} (o : PureObs [] A) → runˢ o ≃ run o

adequacyˢ : ∀ {A} (o : PureObs [] A) → runˢ o ≃ ticks (observe (⟦ o ⟧ []) root)
adequacyˢ o with engines o | adequacy o
... | l₁ , r₁ | l₂ , r₂ = (λ s → l₂ (l₁ s)) , (λ s → r₁ (r₂ s))
