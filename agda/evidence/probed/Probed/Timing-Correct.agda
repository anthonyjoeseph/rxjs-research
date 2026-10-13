-- THE TIMED PROGRAM'S PACKETS AT THREE FIRST-ORDER PROGRAMS, AT FUEL 3:
-- the packets the plain run of the translation carries are one fixed
-- injective naming of its arrivals, pinned by `refl`.  The subscription's
-- packet is empty and the k-th drain step's is `1 ∷ 0 ∷ k - 1`, for a
-- program reading slot zero's script.
--
-- LOAD-BEARING: every row stamps an END item beside a value, so a
-- completion in its own packet fails; `two-arrivals` puts two arrivals
-- in two packets, so one shared packet fails, and `of-two` puts two
-- values and the END in the subscription's, so a split packet fails.
-- TARGET: packets-name-arrivals @2088b5
module Probed.Timing-Correct where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (∷-injectiveʳ; ∷-injectiveˡ)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Timed.Timing-Correct using (packets-name-arrivals)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

-- each arrival's packet, as the census read them
pname : ℕ → List ℕ
pname zero    = []
pname (suc k) = 1 ∷ 0 ∷ k ∷ []

pname-inj : ∀ {a b} → pname a ≡ pname b → a ≡ b
pname-inj {zero}  {zero}  _ = refl
pname-inj {suc a} {suc b} e = cong suc (∷-injectiveˡ (∷-injectiveʳ (∷-injectiveʳ e)))
pname-inj {zero}  {suc _} ()
pname-inj {suc _} {zero}  ()

_ : Confirms (packets-name-arrivals (κᵖ take-one) 3 (Point.prog take-one) (insᵖ take-one))
_ = pname , pname-inj , refl

_ : Confirms (packets-name-arrivals (κᵖ two-arrivals) 3 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = pname , pname-inj , refl

_ : Confirms (packets-name-arrivals (κᵖ of-two) 3 (Point.prog of-two) (insᵖ of-two))
_ = pname , pname-inj , refl
