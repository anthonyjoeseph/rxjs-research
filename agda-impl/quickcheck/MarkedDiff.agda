{-# OPTIONS --guardedness #-}

-- SPIKE: the pointer-free engine against today's, decided by the
-- typechecker: every position each run places, every value at its tick,
-- and how the run ends, on the bug cache's rows and generated programs.
module quickcheck.MarkedDiff where

open import Data.Bool using (Bool; true; false; _∧_; not)
open import Data.List using (List; []; _∷_; filterᵇ; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.Nat using (ℕ; _+_; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.MonotonicList.Events using (Pos; _<ᵖ_; Time)
open import operation.PureObservable using (module Pure; module Driver)
import port.operation.PureObservable as M
open import quickcheck.Code using (Prog; toObs; timeline)
open import quickcheck.Ty using (natᵗ)
open import quickcheck.Bug-Cache using (cases)
open import quickcheck.Adversary using () renaming (cases to adversary)
open import quickcheck.Quickcheck using (program)

open Pure ℕ using (End; finished; dry; cutOff)

Run : Set
Run = List Pos × List (Time × ℕ) × End

horizon budget : ℕ
horizon = 60
budget  = 30000

old new : ℕ → Prog natᵗ → Run
old b p = Driver.marks r , Driver.log r , Driver.ending r
  where r = Driver.reading ℕ horizon b 0 (Driver.trace ℕ (Driver.begin ℕ (toObs timeline 3 p []ᴬ []ᴬ []ᴬ)))
new b p = M.Driver.Read.marks r , M.Driver.Read.log r , M.Driver.Read.endedAs r
  where r = M.Driver.reading ℕ horizon b 0 (M.Machine.load (toObs timeline 3 p []ᴬ []ᴬ []ᴬ))

private
  samePos : Pos → Pos → Bool
  samePos p q = not (p <ᵖ q) ∧ not (q <ᵖ p)

  sameL : ∀ {A : Set} → (A → A → Bool) → List A → List A → Bool
  sameL f []       []       = true
  sameL f (x ∷ xs) (y ∷ ys) = f x y ∧ sameL f xs ys
  sameL f _        _        = false

  sameV : Time × ℕ → Time × ℕ → Bool
  sameV (t , a) (u , b) = (t ≡ᵇ u) ∧ (a ≡ᵇ b)

  sameE : End → End → Bool
  sameE finished   finished   = true
  sameE dry        dry        = true
  sameE (cutOff t) (cutOff u) = t ≡ᵇ u
  sameE _          _          = false

sameAt : ℕ → Prog natᵗ → Bool
sameAt b p with old b p | new b p
... | (ps , vs , e) | (qs , ws , f) = sameL samePos ps qs ∧ sameL sameV vs ws ∧ sameE e f

same : Prog natᵗ → Bool
same = sameAt budget

rows : List (String × Prog natᵗ) → List String
rows []            = []
rows ((n , p) ∷ r) = if′ (same p)
  where if′ : Bool → List String
        if′ true  = rows r
        if′ false = n ∷ rows r

seeds : ℕ → ℕ → List ℕ
seeds f c = filterᵇ (λ s → not (same (program s))) (mapL (f +_) (upTo c))

rows-agree : rows cases ≡ []
rows-agree = refl

adversary-agree : rows adversary ≡ []
adversary-agree = refl

seeds-agree0 : seeds 0 40 ≡ []
seeds-agree0 = refl

seeds-agree1 : seeds 40 40 ≡ []
seeds-agree1 = refl

seeds-agree2 : seeds 80 40 ≡ []
seeds-agree2 = refl

seeds-agree3 : seeds 120 40 ≡ []
seeds-agree3 = refl

seeds-agree4 : seeds 160 40 ≡ []
seeds-agree4 = refl

seeds-agree5 : seeds 200 40 ≡ []
seeds-agree5 = refl

seeds-agree6 : seeds 240 40 ≡ []
seeds-agree6 = refl

seeds-agree7 : seeds 280 40 ≡ []
seeds-agree7 = refl

seeds-agree8 : seeds 320 40 ≡ []
seeds-agree8 = refl

seeds-agree9 : seeds 360 40 ≡ []
seeds-agree9 = refl
