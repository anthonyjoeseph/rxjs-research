module Pool-Lower-Probe where

open import Data.Nat
  using (ℕ; zero; suc; _+_; _*_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; n≤1+n;
         m≤m+n; m≤n+m;
         +-identityʳ; +-suc;
         +-mono-≤; +-monoʳ-≤;
         *-monoʳ-≤; *-identityʳ)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)

open import Rx.Prim using (towerℕ)
open import Rx.Evaluator
  using (sizeAt; widAt; fCharge; fLvl; fLvlD; iterL; dLvl; lvls;
         dCapᶜ; dWalkᶜ; regAt; poolBody; poolCount; blowH; blowH-body)

open import Verify-Budget-Sufficient.Caps
  using (fLvl≤fLvlD; iterL-infl; poolBody≤poolCount; k≤towerℕ)

-- (1) suc J ≤ fLvlD S W d J
sucJ≤fLvlD : ∀ (S W d J : ℕ) → suc J ≤ fLvlD S W d J
sucJ≤fLvlD S W d J =
  ≤-trans
    (≤-trans (s≤s (m≤m+n J (suc (widAt S W J) * suc (sizeAt S J))))
             (≤-reflexive (sym (+-suc J (suc (widAt S W J) * suc (sizeAt S J))))))
    (fLvl≤fLvlD S W d J)

-- (2) suc J ≤ dLvl S W d J
sucJ≤dLvl : ∀ (S W d J : ℕ) → suc J ≤ dLvl S W d J
sucJ≤dLvl S W d J =
  ≤-trans (sucJ≤fLvlD S W d J)
          (iterL-infl S W d (sizeAt S J) (fLvlD S W d J))

-- (3) J + n ≤ lvls S W d J n
J+n≤lvls : ∀ (S W d J n : ℕ) → J + n ≤ lvls S W d J n
J+n≤lvls S W d J zero    = ≤-reflexive (+-identityʳ J)
J+n≤lvls S W d J (suc n) =
  ≤-trans (≤-reflexive (+-suc J n))
  (≤-trans (s≤s (J+n≤lvls S W d J n))
           (sucJ≤dLvl S W d (lvls S W d J n)))

-- (4) i ≤ dWalkᶜ S W R d g J i
i≤dWalkᶜ : ∀ (S W R d g J i : ℕ) → i ≤ dWalkᶜ S W R d g J i
i≤dWalkᶜ S W R d g J zero    = z≤n
i≤dWalkᶜ S W R d g J (suc i) =
  let w = dWalkᶜ S W R d g J i
      D = dCapᶜ S W R d g (lvls S W d J (suc w))
  in ≤-trans (s≤s (i≤dWalkᶜ S W R d g J i))
     (≤-trans (s≤s (m≤m+n w D))
              (≤-reflexive (sym (+-suc w D))))

-- (5) M ≤ dCapᶜ M M M d (suc M) 0
M≤dCapᶜ : ∀ (M d : ℕ) → M ≤ dCapᶜ M M M d (suc M) 0
M≤dCapᶜ M d =
  ≤-trans (≤-reflexive (sym (*-identityʳ M)))
          (i≤dWalkᶜ M M M d M 0 (regAt M M 0))

-- helper: 1 ≤ towerℕ m for all m
1≤towerℕ : ∀ m → 1 ≤ towerℕ m
1≤towerℕ zero    = ≤-refl
1≤towerℕ (suc m) = ≤-trans (s≤s z≤n) (k≤towerℕ (suc m))

-- DELIVERABLE 1
capsBase-le-pool : ∀ (m : ℕ) → 2 ≤ m → m ≤ poolCount (towerℕ m) m
capsBase-le-pool m _ =
  ≤-trans (k≤towerℕ m)
  (≤-trans (M≤dCapᶜ (towerℕ m) m)
  (≤-trans (J+n≤lvls (towerℕ m) (towerℕ m) m 0
                     (dCapᶜ (towerℕ m) (towerℕ m) (towerℕ m) m (suc (towerℕ m)) 0))
           (poolBody≤poolCount (towerℕ m) m (1≤towerℕ m))))

-- DELIVERABLE 2
three-size-le-blowH : ∀ (X E : ℕ) → 2 ≤ (3 + X + suc E) →
  (2 + X) + (2 + X) + (2 + X) ≤ blowH (3 + X + suc E)
three-size-le-blowH X E 2≤m =
  ≤-trans lhs-le-3m
  (≤-trans 3m-le-blowH-body
           (≤-reflexive (sym (blowH-body (3 + X + suc E)))))
  where
  m = 3 + X + suc E
  P = poolCount (towerℕ m) m
  h2Xm : 2 + X ≤ m
  h2Xm = ≤-trans (n≤1+n (2 + X)) (m≤m+n (3 + X) (suc E))
  hP : m ≤ P
  hP = capsBase-le-pool m 2≤m
  lhs-le-3m : (2 + X) + (2 + X) + (2 + X) ≤ m + m + m
  lhs-le-3m = +-mono-≤ (+-mono-≤ h2Xm h2Xm) h2Xm
  eq3m : 6 + (m + m + m) ≡ 6 + m + 2 * m
  eq3m = solve 1 (λ M → con 6 :+ (M :+ M :+ M) := con 6 :+ M :+ con 2 :* M) refl m
  3m-le-blowH-body : m + m + m ≤ 6 + m + 2 * P
  3m-le-blowH-body =
    ≤-trans (m≤n+m (m + m + m) 6)
    (≤-trans (≤-reflexive eq3m)
             (+-monoʳ-≤ (6 + m) (*-monoʳ-≤ 2 hP)))
