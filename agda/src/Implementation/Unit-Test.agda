-- Type-level unit tests: a performance cache of discovered counterexamples.
-- Each entry is `_ : Agree FUEL prog slots` checked by `refl` at compile
-- time — it pins the exact batching the impl must produce for a specific
-- generated program (spec-derived). A regression fails the typechecker
-- instantly instead of surfacing only in a random QuickCheck seed.
--
-- APPEND-ONLY, via scripts/gen-unit-tests.sh: a new QuickCheck failure is
-- appended below; a fixed bug just becomes a passing guard that stays.
-- Invariant: this module fully typechecks ⟺ no known counterexample
-- remains — green here is the impl≡spec finish line for the cached cases.
-- Delete this module once Formal-Verification is discharged.
module Implementation.Unit-Test where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Timed; after_,_; ObservableInput; hot; cold; InstEmit)
open import Rx.Exp using (Ctx; Closed; natᵗ; obs; _×ᵗ_;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; concatAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ;
                          add; sub; mul; eqᵖ; ltᵖ; notᵖ)
open import Rx.Evaluator using (evaluate; Slot; scripted; shared; Slots)
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

------------------------------------------------------------------------
-- cached counterexamples (appended by scripts/gen-unit-tests.sh)
-- (none yet — QuickCheck finds no impl≢spec disagreement)
