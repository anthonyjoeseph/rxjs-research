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

open import Data.Bool using (true)
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (after_,_; hot; cold)
open import Rx.Exp using (Ctx; Closed; natᵗ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; flattenᵉ; switchAllᵉ;
  exhaustAllᵉ; nat̂; primᵗ; pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add; mul)
open import Rx.Evaluator using (evaluate)
open import Rx.Slots using (scripted; Slots)
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

------------------------------------------------------------------------
-- cached counterexamples (appended by scripts/gen-unit-tests.sh)
-- (none yet — QuickCheck finds no impl≢spec disagreement)

-- seed 315
_ : WellFormedOutput 30
          {- WF -} (flattenᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (takeᵉ (nat̂ 2) (mapᵉ (varᵗ (here refl)) (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 1) ∷ (nat̂ 3) ∷ []))) ∷ [])))))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 3))) emptyᵉ)) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (input zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (exhaustAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 6) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (ofᵉ ((nat̂ 4) ∷ (nat̂ 8) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 9) (input zero))) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 4))) (input (suc zero)))) ∷ [])))) ∷ (strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 8) ∷ []))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (mapᵉ (varᵗ (here refl)) emptyᵉ)))) ∷ [])))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (flattenᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (flattenᵉ nothing (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ (strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 1))) (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero)))) ∷ (strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) (takeᵉ (nat̂ 3) (flattenᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ emptyᵉ) ∷ [])))))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (flattenᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (flattenᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 7))) (flattenᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 9) ∷ []))) ∷ []))))) ∷ (strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) (input zero))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 6) (ofᵉ ((nat̂ 9) ∷ (nat̂ 1) ∷ [])))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 1) (mapᵉ (varᵗ (here refl)) emptyᵉ))) ∷ []))))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (hot ((after 2 , 0) ∷ [])) ; (suc zero) → scripted (cold (1 ∷ 2 ∷ 3 ∷ []) ((after 1 , 2) ∷ (after 2 , 6) ∷ (after 1 , 3) ∷ [])) ; (suc (suc ())) })
_ = refl

-- seed 378
_ : WellFormedOutput 30
          {- WF -} (flattenᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 0) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (takeᵉ (nat̂ 1) (exhaustAllᵉ (ofᵉ ((strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 6) ∷ []))) ∷ [])))) ∷ [])))))) ∷ (strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ (flattenᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 7) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) emptyᵉ)) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 5))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (input (suc zero)))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (flattenᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 0) ∷ []))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 8))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ)) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 3))) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (flattenᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 2) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ []))))) ∷ (strmᵗ (flattenᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (flattenᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 5) ∷ []))) ∷ [])))) ∷ []))))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 2) (ofᵉ ((nat̂ 9) ∷ (nat̂ 0) ∷ [])))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 8) ∷ []))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 2) ∷ []))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (cold (6 ∷ 7 ∷ 8 ∷ []) ((after 2 , 6) ∷ (after 2 , 4) ∷ (after 0 , 9) ∷ [])) ; (suc zero) → scripted (hot ((after 1 , 8) ∷ [])) ; (suc (suc ())) })
_ = refl
