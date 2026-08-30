------------------------------------------------------------------
-- THE CLOSURE ENVIRONMENT, built in stages on the slot index.
--
-- `Rx.Clos-Size` states the measure against an ARBITRARY environment
-- because the honest one cannot be written by structural recursion on
-- a term: a definition may itself mention slots.  Stratification is
-- what makes it definable at all, and the staging here is the same
-- one `Rx.Slot-Hop` performs for the hop environment -- correct below
-- k, neutral at and above it, each slot read off its own stage.
--
-- THE FIXPOINT is the fact the arr-keyed walk's slot arm consumes: at
-- a shared slot the staged number is one MORE than the definition's
-- closure size, so the arm has a whole step of the key to spend on the
-- descent it hands off to.  That step is exactly what the additive
-- grant lacked when it was refuted.
-- TWIN: `Rx.Slot-Hop.slotHop-fix`, assembled the same way from the
--   same two halves.
------------------------------------------------------------------
module Rx.Slot-Clos where

open import Data.Bool using (T; true; false; if_then_else_)
open import Data.Fin  using (Fin; toℕ)
open import Data.Nat  using (ℕ; zero; suc; _≤_; s≤s; z≤n; _≡ᵇ_; _<ᵇ_)
open import Data.Nat.Properties
  using (≡ᵇ⇒≡; ≡⇒≡ᵇ; <ᵇ⇒<; <⇒<ᵇ; ≤∧≢⇒<; ≤-pred)
open import Data.Unit using (tt)
open import Data.List using (tabulate)
open import Data.Nat.ListAction using (sum)
open import Data.Vec  using (lookup)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; sym; trans; subst)

open import Rx.Exp   using (Ctx; Closed; inputsBelowᵉ)
open import Rx.Prim  using (hot; cold)
open import Rx.Slots using (Slot; Slots; scripted; shared; inputSize)
open import Rx.Clos-Size using (closSizeᵉ)
open import Rx.Clos-Eta-Cong using (clos-σ-congᵉ)


-- ONE SLOT'S CONTRIBUTION, given an environment for the inputs its
-- definition may read.  A shared slot is descended into, so it costs
-- its definition's closure; a scripted one is not, and costs its
-- SCRIPT -- the same reading the budget face's slot measure takes.
--
-- AND THE SCRIPT ARM IS THE LOAD-BEARING ONE.  A step applied once per
-- delivered value doubles the depth per value, so an arrival whose
-- source is a cold script races a key built from syntax alone: the
-- script is not an expression, so nothing in the arrival moves when it
-- grows.  Charging the script is what puts a term in the delivered
-- length on the key side, and it only ENLARGES the key, so it cannot
-- cost any fit that already held.
-- REFUTED: `Refuted.Scan-Arr-Nest`
slotClosD : ∀ {n} {Γ : Ctx n} {k t} (σ : Fin n → ℕ) → Slot Γ k t → ℕ
slotClosD σ (scripted i) = inputSize i
slotClosD σ (shared d)   = suc (closSizeᵉ σ d)

-- the stage-k environment: the true closure sizes below k, the bare
-- reference at and above it
σAt : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ) → Fin n → ℕ
σAt sl zero    i = 1
σAt sl (suc k) i =
  if toℕ i ≡ᵇ k then slotClosD (σAt sl k) (sl i)
                else σAt sl k i

-- THE ENVIRONMENT: each slot read off its own stage
slotClos : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) → Fin n → ℕ
slotClos sl i = slotClosD (σAt sl (toℕ i)) (sl i)

-- THE STAGE IS ALREADY RIGHT WHERE IT CLAIMS TO BE
σAt-agrees : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (k : ℕ)
  (j : Fin n) → T (toℕ j <ᵇ k) →
  σAt sl k j ≡ slotClos sl j
σAt-agrees sl zero    j ()
σAt-agrees sl (suc k) j lt with toℕ j ≡ᵇ k in eqb
... | true  =
  cong (λ m → slotClosD (σAt sl m) (sl j))
       (sym (≡ᵇ⇒≡ (toℕ j) k (subst T (sym eqb) tt)))
... | false =
  σAt-agrees sl k j
    (<⇒<ᵇ (≤∧≢⇒< (≤-pred (<ᵇ⇒< (toℕ j) (suc k) lt))
                 (λ e → subst T eqb (≡⇒≡ᵇ (toℕ j) k e))))

-- THE FIXPOINT the walk's slot arm spends: at a shared slot the
-- staged number IS one plus the definition's closure size under the
-- full environment, which is the factor the arm has to have.
slotClos-fix : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n)
  {d : Closed Γ (lookup Γ i)} {ok : T (inputsBelowᵉ (toℕ i) d)} →
  sl i ≡ shared d {ok = ok} →
  slotClos sl i ≡ suc (closSizeᵉ (slotClos sl) d)
slotClos-fix sl i {d} {ok} eq =
  trans (cong (slotClosD (σAt sl (toℕ i))) eq)
        (cong suc (clos-σ-congᵉ (toℕ i) (σAt-agrees sl (toℕ i)) d ok))

-- THE WHOLE TELESCOPE'S STAGED READING, summed the way the flat slot
-- measure is summed.  This is the number a base cap has to carry, and
-- nothing already in one does: every flat measure of the slots is
-- linear in the slot count while the staged reading is not, so the
-- deficit cannot be bought by any fixed number of frame levels.
-- REFUTED: `Refuted.Nest-Clos-Stratified`
slotsClos : ∀ {n} {Γ : Ctx n} → Slots Γ → ℕ
slotsClos sl = sum (tabulate λ i → slotClos sl i)

-- EVERY SLOT COSTS AT LEAST THE SYMBOL IT IS WRITTEN AS, which is what
-- the domination lemma asks of an environment before it will admit it.
slotClos-pos : ∀ {n} {Γ : Ctx n} (sl : Slots Γ) (i : Fin n) →
  1 ≤ slotClos sl i
slotClos-pos sl i with sl i
... | scripted (hot _)    = s≤s z≤n
... | scripted (cold _ _) = s≤s z≤n
... | shared d            = s≤s z≤n
