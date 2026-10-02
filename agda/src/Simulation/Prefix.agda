------------------------------------------------------------------
-- A RUN AT ONE MORE UNIT OF FUEL EXTENDS THE RUN BEFORE IT.  The root
-- subscribe does not read the fuel, and the drain spends one unit per
-- arrival from the front, so the run at `suc k` is the run at `k`
-- followed by whatever the next arrival sends.
------------------------------------------------------------------
module Simulation.Prefix where

open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Relation.Binary.Prefix.Heterogeneous using (Prefix; []; _∷_)
open import Data.Nat     using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Fuel)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Slots     using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; sched-next)
open import Rx.Evaluator.Builder using (drain!; drainOn; evaluate↓; subscribe!; cascade!; pop-rule)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; Rule)

-- a common head keeps a prefix
prefix-++ : ∀ {A : Set} (xs : List A) {ys zs : List A}
          → Prefix _≡_ ys zs → Prefix _≡_ (xs ++ ys) (xs ++ zs)
prefix-++ []       p = p
prefix-++ (x ∷ xs) p = refl ∷ prefix-++ xs p

mutual
  drain-prefix : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (k : Fuel) (sched : Sched Γ) (st : EvalSt e)
                 (ru : Rule sched st)
               → Prefix _≡_ (Σ⁰.fst⁰ (drain! k sched st ru)) (Σ⁰.fst⁰ (drain! (suc k) sched st ru))
  drain-prefix zero    sched st ru = []
  drain-prefix (suc k) sched st ru = on-prefix k sched st ru (sched-next sched) refl

  on-prefix : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (k : Fuel) (sched : Sched Γ) (st : EvalSt e)
              (ru : Rule sched st) (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) (eqn : sched-next sched ≡ x)
            → Prefix _≡_ (Σ⁰.fst⁰ (drainOn k sched st ru x eqn)) (Σ⁰.fst⁰ (drainOn (suc k) sched st ru x eqn))
  on-prefix k sched st ru (inj₁ _)            eqn = []
  on-prefix k sched st ru (inj₂ (a , sched′)) eqn =
    prefix-++ (proj₁ (Σ⁰.fst⁰ (cascade! a sched′ st (pop-rule eqn ru)))) (drain-prefix k _ _ _)

run-prefix : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
           → Prefix _≡_ (evaluate↓ fuel e ins) (evaluate↓ (suc fuel) e ins)
run-prefix fuel e ins = prefix-++ (proj₁ (Σ⁰.fst⁰ (subscribe! e ins))) (drain-prefix fuel _ _ _)
