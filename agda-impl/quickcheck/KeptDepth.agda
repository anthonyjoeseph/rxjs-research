{-# OPTIONS --guardedness #-}

-- THE KEPT DEPTH, TESTED: every silent step of the engine drops leading
-- skips of what its configuration means (`adequacy.Engine.Meaning.M`), or
-- means the same, event for event, skips and positions included
-- (`adequacy.Content.silent-exact`).  Also the longest run of silent steps
-- meaning the same, which is what `adequacy.Ghost.work` has to bound.
module quickcheck.KeptDepth where

open import Data.Bool using (Bool; false; _∨_; if_then_else_)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.String using (String; _++_)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush)
open import operation.PureObservable using (module Driver; module Machine)
open import adequacy.Engine.Meaning using (M)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Stepping using (exactᵇ)
open import quickcheck.Spin using (showP)

open Driver ℕ using (Step; step; silent; value; complete; drained)
open Machine using (Conf; load; spot; subscribing; absorbed; rising)

private
  -- A run's verdict, carrying its longest run of steps meaning the same.
  data Verdict : Set where
    yes : ℕ → Verdict
    no  : ℕ → String → Verdict

  -- The first `k` events of a run, printed.
  showE : ℕ → Events ℕ → String
  showE zero    _           = "…"
  showE (suc k) (out p a r) = "o(" ++ showP p ++ "," ++ showℕ a ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (skip p r)  = "k(" ++ showP p ++ ") " ++ showE k (Events∞.force r)
  showE (suc k) (end p)     = "e(" ++ showP p ++ ")"
  showE (suc k) hush        = "h"

  showMode : Conf ℕ → String
  showMode m with Conf.mode m
  ... | subscribing = "subscribing"
  ... | absorbed    = "absorbed"
  ... | rising _    = "rising"

  showSpot : List ℕ → String
  showSpot []      = ""
  showSpot (i ∷ π) = showℕ i ++ "." ++ showSpot π

  -- What a silent step neither dropping nor keeping its meaning did.
  why : Conf ℕ → Conf ℕ → String
  why m m′ = "\n  from " ++ showMode m ++ " at " ++ showSpot (spot m) ++ " to " ++ showMode m′ ++ " at " ++ showSpot (spot m′)
             ++ "\n  before " ++ showE 10 (M m) ++ "\n  after  " ++ showE 10 (M m′)

  depth : ℕ
  depth = 60

  -- Whether `e′` is `e` past one or more of its first `k` leading skips.
  dropped : ℕ → Events ℕ → Events ℕ → Bool
  dropped zero    e          e′ = false
  dropped (suc k) (skip p r) e′ = exactᵇ depth (Events∞.force r) e′ ∨ dropped k (Events∞.force r) e′
  dropped (suc k) _          e′ = false

  -- A silent step from `m` to `m′`: 2 dropped leading skips, 1 meant the
  -- same, 0 neither.
  kind : Conf ℕ → Conf ℕ → ℕ
  kind m m′ = if exactᵇ depth (M m) (M m′) then 1 else (if dropped 64 (M m) (M m′) then 2 else 0)

  -- Whether every silent step keeps its meaning so, and the longest run
  -- meaning the same.
  mutual
    walk : ℕ → ℕ → ℕ → Conf ℕ → Verdict
    walk zero    run best m = yes (best ⊔ run)
    walk (suc n) run best m = next n run best m (step m)

    next : ℕ → ℕ → ℕ → Conf ℕ → Step → Verdict
    next n run best m (silent t m′)     = after n run best m m′ (kind m m′)
    next n run best m (value t p a m′)  = walk n 0 (best ⊔ run) m′
    next n run best m (complete p)      = yes (best ⊔ run)
    next n run best m drained           = yes (best ⊔ run)

    after : ℕ → ℕ → ℕ → Conf ℕ → Conf ℕ → ℕ → Verdict
    after n run best m m′ zero          = no (best ⊔ run) (why m m′)
    after n run best m m′ (suc zero)    = walk n (suc run) best m′
    after n run best m m′ (suc (suc _)) = walk n 0 (best ⊔ run) m′

-- One seed's verdict.
keptLine : ℕ → String
keptLine s with walk 400 0 0 (load (toObs timeline 3 (program s) []ᴬ []ᴬ []ᴬ))
... | yes l = "kept-depth: ok   seed " ++ showℕ s ++ " longest " ++ showℕ l
... | no l w = "kept-depth: FAIL seed " ++ showℕ s ++ " longest " ++ showℕ l ++ "\n  program " ++ showCode natᵗ (program s) ++ w

-- The verdicts on seeds from f.
keptLines : ℕ → ℕ → List String
keptLines f c = mapL (λ s → keptLine (f + s)) (upTo c)
