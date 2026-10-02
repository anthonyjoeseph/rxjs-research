-- TIMING-CORRECT AT THREE FIRST-ORDER PROGRAMS, `AllPairs` DECIDED.
-- LOAD-BEARING where two items are stamped: `two-arrivals` (two instants,
-- so a shared stamp fails) and `of-two` (one instant, so a split stamp or
-- a split packet fails).  `take-one` stamps one item and is DEGENERATE:
-- `AllPairs` of a singleton holds of any relation.
-- TARGET: timing-correct @46974c
module Probed.Timing-Correct where

open import Data.Unit using (tt)
open import Data.Nat using (_≟_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; uncurry)
open import Data.List.Properties using (≡-dec)
open import Data.List.Relation.Unary.AllPairs using (allPairs?)
open import Function using (mk⇔; Equivalence)
open import Relation.Nullary.Decidable using (Dec; toWitness; map′; _×-dec_; _→-dec_)

open import Rx.Prim using (Id)
open import Rx.Exp using (Ctx; Val; natᵗ)
open import SExp.Syntax using (plainᵗ)
open import Timed.Translation using (packetOf; itemᵗ)
open import Timed.Timing-Correct using (timing-correct; Coherent)
open import CLI.Unit-Test.Prelude using (Γ₂ᵗ)
open import Probed.Apparatus using (Confirms; Point; κᵖ; insᵖ; take-one; two-arrivals; of-two)

-- `Coherent`, decided: both directions of the `⇔`, each an implication
-- between two decided equalities
coherent? : ∀ {m} {Γ′ : Ctx m} (p q : Id × Val Γ′ (plainᵗ (itemᵗ natᵗ)))
          → Dec (Coherent {Γ′ = Γ′} natᵗ p q)
coherent? {Γ′ = Γ′} p q =
  map′ (uncurry mk⇔) (λ e → Equivalence.to e , Equivalence.from e)
       ((ids →-dec pkts) ×-dec (pkts →-dec ids))
  where
    ids  = proj₁ p ≟ proj₁ q
    pkts = ≡-dec _≟_ (packetOf {Γ = Γ′} natᵗ (proj₂ p)) (packetOf {Γ = Γ′} natᵗ (proj₂ q))

_ : Confirms (timing-correct (κᵖ take-one) 30 (Point.prog take-one) (insᵖ take-one))
_ = toWitness {a? = allPairs? {R = Coherent {Γ′ = Γ₂ᵗ (κᵖ take-one)} natᵗ}
                         (coherent? {Γ′ = Γ₂ᵗ (κᵖ take-one)}) _} tt

_ : Confirms (timing-correct (κᵖ two-arrivals) 30 (Point.prog two-arrivals) (insᵖ two-arrivals))
_ = toWitness {a? = allPairs? {R = Coherent {Γ′ = Γ₂ᵗ (κᵖ two-arrivals)} natᵗ}
                         (coherent? {Γ′ = Γ₂ᵗ (κᵖ two-arrivals)}) _} tt

_ : Confirms (timing-correct (κᵖ of-two) 30 (Point.prog of-two) (insᵖ of-two))
_ = toWitness {a? = allPairs? {R = Coherent {Γ′ = Γ₂ᵗ (κᵖ of-two)} natᵗ}
                         (coherent? {Γ′ = Γ₂ᵗ (κᵖ of-two)}) _} tt
