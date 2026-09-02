-- THE BUG CACHE'S SHARED VOCABULARY, split out so that a cached case is a
-- MODULE rather than a row.  Every entry pins a whole `evaluate` run by
-- `refl`, which costs minutes at the two cases already here; appended into
-- one file they are re-checked together on every gate run and the cost grows
-- without bound.  One module per case is what makes an unchanged case free:
-- Agda's interface cache is per module, so only the case just appended is
-- ever checked again.  The two shapes a case can take both live here, so a
-- case module never has to import the ledger that claims it.
module Implementation.Unit-Test.Prelude where

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Exp using (Ctx; Closed; natᵗ)
open import Rx.Evaluator using (evaluate)
open import Rx.Slots using (Slots)
open import Rx.Protocol using (wellFormed?)
open import Implementation using (impl-batchSimultaneous)
open import Spec using (spec-batchSimultaneous)

-- the QuickCheck's fixed context: two nat-typed slots
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- impl and spec, fed the SAME evaluate output, must batch it identically
Agree : ℕ → Closed Γ₂ natᵗ → Slots Γ₂ → Set
Agree fuel e ins =
  impl-batchSimultaneous (evaluate fuel e ins)
    ≡ spec-batchSimultaneous (evaluate fuel e ins)

-- the evaluator's raw output must satisfy the protocol automaton
-- (evaluate-well-formed, cached case by case)
WellFormedOutput : ℕ → Closed Γ₂ natᵗ → Slots Γ₂ → Set
WellFormedOutput fuel e ins = wellFormed? (evaluate fuel e ins) ≡ true
