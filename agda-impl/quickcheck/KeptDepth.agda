{-# OPTIONS --guardedness #-}

-- THE KEPT DEPTH, TESTED: every silent step of the engine drops the first
-- skip of what its configuration means (`adequacy.Engine.Meaning.M`), or
-- means the same, event for event, skips and positions included
-- (`adequacy.Content.silent-exact`).  Also the longest run of silent steps
-- meaning the same, which is what `adequacy.Ghost.work` has to bound.
module quickcheck.KeptDepth where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import denotation.MonotonicList.Events using (Events; Events∞; skip)
open import operation.PureObservable using (module Driver; module Machine)
open import adequacy.Engine.Meaning using (M)
open import quickcheck.Code using (toObs; timeline)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Stepping using (exactᵇ)

open Driver ℕ using (Step; step; silent; value; complete; drained)
open Machine using (Conf; load)

private
  -- A run's verdict, carrying its longest run of steps meaning the same.
  data Verdict : Set where
    yes no : ℕ → Verdict

  depth : ℕ
  depth = 60

  -- A silent step from `m` to `m′`: 2 dropped the first skip, 1 meant the
  -- same, 0 neither.
  kind : Conf ℕ → Conf ℕ → ℕ
  kind m m′ = if exactᵇ depth (M m) (M m′) then 1 else dropped (M m)
    where dropped : Events ℕ → ℕ
          dropped (skip p r) = if exactᵇ depth (Events∞.force r) (M m′) then 2 else 0
          dropped _          = 0

  -- Whether every silent step keeps its meaning so, and the longest run
  -- meaning the same.
  mutual
    walk : ℕ → ℕ → ℕ → Conf ℕ → Verdict
    walk zero    run best m = yes (best ⊔ run)
    walk (suc n) run best m = next n run best m (step m)

    next : ℕ → ℕ → ℕ → Conf ℕ → Step → Verdict
    next n run best m (silent t m′)     = after n run best m′ (kind m m′)
    next n run best m (value t p a m′)  = walk n 0 (best ⊔ run) m′
    next n run best m (complete p)      = yes (best ⊔ run)
    next n run best m drained           = yes (best ⊔ run)

    after : ℕ → ℕ → ℕ → Conf ℕ → ℕ → Verdict
    after n run best m′ zero          = no (best ⊔ run)
    after n run best m′ (suc zero)    = walk n (suc run) best m′
    after n run best m′ (suc (suc _)) = walk n 0 (best ⊔ run) m′

-- One seed's verdict.
keptLine : ℕ → String
keptLine s with walk 400 0 0 (load (toObs timeline 3 (program s) []ᴬ []ᴬ []ᴬ))
... | yes l = "kept-depth: ok   seed " ++ showℕ s ++ " longest " ++ showℕ l
... | no l  = "kept-depth: FAIL seed " ++ showℕ s ++ " longest " ++ showℕ l

-- The verdicts on seeds from f.
keptLines : ℕ → ℕ → List String
keptLines f c = mapL (λ s → keptLine (f + s)) (upTo c)
