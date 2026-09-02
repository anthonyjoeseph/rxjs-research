-- One cached counterexample, seed 378.  Appended by
-- `scripts/gen-unit-tests.sh`; the pin is what makes it a guard.
module Implementation.Unit-Test.Case-378 where

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

wf-378 : WellFormedOutput 30
          {- WF -} (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 0) ∷ (nat̂ 4) ∷ []))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (takeᵉ (nat̂ 2) (takeᵉ (nat̂ 1) (exhaustAllᵉ (ofᵉ ((strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ (input zero)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 6) ∷ []))) ∷ [])))) ∷ [])))))) ∷ (strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 7) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 6))) emptyᵉ)) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 5))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (input (suc zero)))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (input (suc zero))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 3) ∷ []))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ [])))) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 7) (mergeAllᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 4) ∷ []))) ∷ []))))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 4) ∷ (nat̂ 0) ∷ []))) ∷ (strmᵗ (switchAllᵉ (ofᵉ ((strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (primᵗ mul (pairᵗ (varᵗ (here refl)) (nat̂ 0))) (input zero))) ∷ (strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 8))) emptyᵉ)) ∷ [])))) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ)) ∷ [])))) ∷ [])))) ∷ [])))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (exhaustAllᵉ (ofᵉ ((strmᵗ (mapᵉ (primᵗ add (pairᵗ (varᵗ (here refl)) (nat̂ 3))) (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 3) emptyᵉ))) ∷ (strmᵗ (takeᵉ (nat̂ 3) (mergeAllᵉ nothing (ofᵉ ((strmᵗ (ofᵉ ((nat̂ 7) ∷ (nat̂ 2) ∷ []))) ∷ (strmᵗ (input (suc zero))) ∷ (strmᵗ (input (suc zero))) ∷ []))))) ∷ []))))) ∷ (strmᵗ (mergeAllᵉ (just 1) (ofᵉ ((strmᵗ (mapᵉ (varᵗ (here refl)) (mergeAllᵉ nothing (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ emptyᵉ) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ emptyᵉ) ∷ (strmᵗ (input zero)) ∷ (strmᵗ (ofᵉ ((nat̂ 9) ∷ (nat̂ 5) ∷ []))) ∷ [])))) ∷ []))))) ∷ (strmᵗ (exhaustAllᵉ (ofᵉ ((strmᵗ (scanᵉ (primᵗ add (pairᵗ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl))))) (nat̂ 2) (ofᵉ ((nat̂ 9) ∷ (nat̂ 0) ∷ [])))) ∷ (strmᵗ emptyᵉ) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 3) ∷ (nat̂ 8) ∷ []))) ∷ [])))) ∷ (strmᵗ (ofᵉ ((nat̂ 2) ∷ (nat̂ 2) ∷ []))) ∷ [])))) ∷ [])))
          (λ { zero → scripted (cold (6 ∷ 7 ∷ 8 ∷ []) ((after 2 , 6) ∷ (after 2 , 4) ∷ (after 0 , 9) ∷ [])) ; (suc zero) → scripted (hot ((after 1 , 8) ∷ [])) ; (suc (suc ())) })
wf-378 = refl
