-- THE WALK SWEEP: QuickCheck's draw, each case's impl run walked by
-- `CLI.Walk-Check`, the tallies summed by tag.  stdin is
-- "SEED RUNS DEPTH [FUEL]" and then the draw restriction, exactly as
-- QuickCheck reads it, so a `QC_DRAW` aims both.  A case whose draw missed
-- its reach is skipped and counted.
module CLI.Walk where

open import Data.Bool    using (true; false; if_then_else_)
open import Data.List    using (List; []; _∷_)
open import Data.Nat     using (ℕ; zero; suc; _+_; _≡ᵇ_)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.String  using (String; _++_)
open import Agda.Builtin.IO using (IO)
open import CLI.IO       using (_>>=_; getContents; putStr; Unit)
open import CLI.Unit-Test.Prelude using (mkSlots₂)
open import CLI.QuickCheck using (Draw; drawCase; drawOf; randList; toCodes; parseNat; numAt; firstLine; restLines; FUEL)
open import CLI.Walk-Check using (Tally; tags; tagName; walkSides)

-- two tallies of one tag, summed; the first failure kept
addT : Tally → Tally → Tally
addT (k , n , f , w) (k′ , n′ , f′ , w′) = k + k′ , n + n′ , f + f′ , (if f ≡ᵇ 0 then w′ else w)

zeroT : List (ℕ × Tally)
zeroT = go tags
  where
  go : List ℕ → List (ℕ × Tally)
  go []       = []
  go (g ∷ gs) = (g , 0 , 0 , 0 , "") ∷ go gs

addAll : List (ℕ × Tally) → List (ℕ × Tally) → List (ℕ × Tally)
addAll ((g , t) ∷ ts) ((_ , t′) ∷ ts′) = (g , addT t t′) ∷ addAll ts ts′
addAll ts             _                = ts

-- every case drawn, walked, summed; and how many missed their reach
sweep : ℕ → ℕ → ℕ → Draw → List ℕ → List (ℕ × Tally) × ℕ
sweep f zero    d W rs = zeroT , 0
sweep f (suc k) d W rs with drawCase d W rs
... | (true  , _ , e , d₀ , d₁) , rs′ with sweep f k d W rs′
...   | acc , u = addAll (walkSides f e (mkSlots₂ d₀ d₁)) acc , u
sweep f (suc k) d W rs | (false , _ , _) , rs′ with sweep f k d W rs′
...   | acc , u = acc , suc u

report : List (ℕ × Tally) → String
report []                            = ""
report ((g , k , n , fl , w) ∷ ts) =
  tagName g ++ " checked " ++ show k ++ " counted " ++ show n ++ " failed " ++ show fl ++ "\n"
  ++ (if fl ≡ᵇ 0 then "" else "  first failure: " ++ w ++ "\n")
  ++ report ts

run : List ℕ → Draw → IO Unit
run cs W with sweep (if numAt 3 0 cs ≡ᵇ 0 then FUEL else numAt 3 0 cs) (numAt 1 50 cs) (numAt 2 4 cs) W
                    (randList (parseNat cs) 2000000)
... | ts , u = putStr (report ts ++ "unreached " ++ show u ++ "\n")

main : IO Unit
main = getContents >>= λ s → go (drawOf (restLines (toCodes s))) (firstLine (toCodes s))
  where
  go : Draw ⊎ String → List ℕ → IO Unit
  go (inj₁ W) cs = run cs W
  go (inj₂ e) cs = putStr ("restriction: " ++ e ++ "\n")
