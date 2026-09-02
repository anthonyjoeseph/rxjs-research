-- One cached counterexample, seed 315.  Appended by
-- `scripts/gen-unit-tests.sh`; the pin is what makes it a guard.
module Implementation.Unit-Test.Case-315 where

open import Data.List using ([]; _∷_)
open import Data.Fin using (zero; suc)
open import Data.Maybe using (nothing; just)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (after_,_; hot; cold)
open import Rx.Exp using (input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; nat̂; primᵗ;
  pairᵗ; fstᵗ; sndᵗ; strmᵗ; varᵗ; add; mul)
open import Rx.Slots using (scripted)

open import Implementation.Unit-Test.Prelude using (WellFormedOutput)

wf-315 : WellFormedOutput 30
          {- WF -} (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (takeᵉ (nat̂ 2) (mapᵉ (varᵗ (here refl)) (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 1) ∷ (nat̂ 3) ∷ []))) ∷ [])))))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 3))) emptyᵉ)) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (input zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (exhaustAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 6) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (ofᵉ ((nat̂ 4) ∷ (nat̂ 8) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 6) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 5) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 9) (input zero))) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 4))) (input (suc zero)))) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 8) ∷ []))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (mapᵉ (varᵗ (here refl)) emptyᵉ)))) ∷ [])))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ (strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 1))) (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero)))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (input zero)) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ emptyᵉ) ∷ [])))))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 8) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 8) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (mapᵉ (varᵗ (here refl)) (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 7))) (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 5) ∷ (nat̂ 9) ∷ []))) ∷ []))))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) (input zero))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 6) (ofᵉ ((nat̂ 9) ∷ (nat̂ 1) ∷ [])))) ∷ (strmᵗ (input (suc zero))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 1) (mapᵉ (varᵗ (here refl)) emptyᵉ))) ∷ []))))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (hot ((after 2 , 0) ∷ [])) ; (suc zero) → scripted (cold (1 ∷ 2 ∷ 3 ∷ []) ((after 1 , 2) ∷ (after 2 , 6) ∷ (after 1 , 3) ∷ [])) ; (suc (suc ())) })
wf-315 = refl
