-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Live
-- cascadeGo-live-nest … cascadeGo-nest-live
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Live where

open import Data.Bool    using (true; false)
open import Data.Nat     using (ℕ; _+_; _*_; _⊔_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (*-identityˡ; *-monoˡ-≤; ≤-trans; ≤-reflexive; m≤m+n; m≤n+m; *-identityʳ; *-mono-≤; *-monoʳ-≤;
  ⊔-lub; m≤m⊔n; m≤n⊔m)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; foldr)
open import Data.Bool.ListAction using (any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong)

open import Rx.Prim      using (Id; _at_from_as_; after_,_)
open import Rx.Exp       using (Ctx; Closed; sizeᵛ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestF; pathNestF; 1≤pathNestF; 1≤chainsNestF; storeNestMax; nestCapAt; nestOK?;
  nestFacAt; 1≤nestFacAt; nest-inflate; nestIncAt; size≤nestIncAt; slotsNestSum; liveNest)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; cascadeGo; Path; arrTy; chainStep)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (chainStep-nest-live; chainStep-slots)

cascadeGo-live-nest : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  foldr (λ l acc → liveNest l ⊔ acc) 0
        (Sched.live (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched₀)
      ⊔ slotsNestSum (Sched.slots sched₀)
      ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
cascadeGo-live-nest a id [] sched₀ st₀ = ≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)
cascadeGo-live-nest a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true =
  ≤-trans (cascadeGo-live-nest a id chains sched₀ st₀)
          (⊔-lub (m≤m⊔n _ _) (≤-trans tailBump (m≤n⊔m _ _)))
  where
  V = sizeᵛ (arrTy a) (arrVal a)

  tailBump : chainsNestF chains * V ≤ pathNestF c * chainsNestF chains * V
  tailBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityˡ (chainsNestF chains))))
                         (*-monoˡ-≤ (chainsNestF chains) (1≤pathNestF c)))
... | false =
  ≤-trans (cascadeGo-live-nest a id chains sched₁ st₁)
          (⊔-lub (⊔-lub liveArm slotsArm)
                 (≤-trans tailBump (m≤n⊔m _ _)))
  where
  st₀′ = record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }
  step = chainStep id a c sched₀ st₀′
  sched₁ = proj₁ (proj₂ step)
  st₁    = proj₂ (proj₂ step)

  slotsEq : Sched.slots sched₁ ≡ Sched.slots sched₀
  slotsEq = chainStep-slots id a c sched₀ st₀′

  V = sizeᵛ (arrTy a) (arrVal a)

  -- one chain's factor sits under the whole selection's, the rest of
  -- the list contributing a factor of at least one
  headBump : pathNestF c * V ≤ pathNestF c * chainsNestF chains * V
  headBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityʳ (pathNestF c))))
                         (*-monoʳ-≤ (pathNestF c) (1≤chainsNestF chains)))

  tailBump : chainsNestF chains * V ≤ pathNestF c * chainsNestF chains * V
  tailBump =
    *-monoˡ-≤ V (≤-trans (≤-reflexive (sym (*-identityˡ (chainsNestF chains))))
                         (*-monoˡ-≤ (chainsNestF chains) (1≤pathNestF c)))

  liveArm = ≤-trans (chainStep-nest-live id a c sched₀ st₀′)
                    (⊔-lub (m≤m⊔n _ _) (≤-trans headBump (m≤n⊔m _ _)))

  slotsArm =
    ≤-trans (≤-reflexive (cong slotsNestSum slotsEq))
            (≤-trans (m≤n⊔m (foldr (λ l acc → liveNest l ⊔ acc) 0
                                   (Sched.live sched₀))
                            (slotsNestSum (Sched.slots sched₀)))
                     (m≤m⊔n _ _))

-- AND THE CALLER'S FORM IS THE SAME FACT READ AGAINST THE WHOLE `⊔`,
-- since the two terms the induction threads are both summands of it.
cascadeGo-nest-live-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
       ≤ storeNestMax sched st
         ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
cascadeGo-nest-live-flat a nextId chains sched st =
  ≤-trans (cascadeGo-live-nest a nextId chains sched st)
          (⊔-lub (⊔-lub (into (m≤n⊔m (slotsNestSum (Sched.slots sched)) _))
                        (into (m≤m⊔n (slotsNestSum (Sched.slots sched)) _)))
                 (m≤n⊔m _ _))
  where
  into : ∀ {m} →
    m ≤ slotsNestSum (Sched.slots sched)
        ⊔ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched) →
    m ≤ storeNestMax sched st
        ⊔ chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
  into h = ≤-trans h (≤-trans (≤-trans (m≤m⊔n _ _) (m≤m⊔n _ _)) (m≤m⊔n _ _))

cascadeGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  chainsNestF chains ≤ nestFacAt e sl id →
  let r = cascadeGo a nextId chains sched st
  in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
       ≤ nestFacAt e sl id * (storeNestMax sched st + nestIncAt e sl id)
cascadeGo-nest-live {e = e} sl id a nextId chains sched st _ _ _ _ hsz hcf =
  ≤-trans (cascadeGo-nest-live-flat a nextId chains sched st)
          (⊔-lub storeArm chainArm)
  where
  RHS : ℕ
  RHS = storeNestMax sched st + nestIncAt e sl id

  storeArm : storeNestMax sched st ≤ nestFacAt e sl id * RHS
  storeArm = ≤-trans (m≤m+n (storeNestMax sched st) (nestIncAt e sl id))
                     (nest-inflate (nestFacAt e sl id) RHS (1≤nestFacAt e sl id))

  -- the arrival's own size is what the live fold gains, and the
  -- selection's factor is what it gains it once per chain for
  chainArm : chainsNestF chains * sizeᵛ (arrTy a) (arrVal a)
               ≤ nestFacAt e sl id * RHS
  chainArm =
    *-mono-≤ hcf
             (≤-trans hsz (≤-trans (size≤nestIncAt e sl id)
                                   (m≤n+m (nestIncAt e sl id)
                                          (storeNestMax sched st))))

-- THE BURST BOUND AT THE INDICES A CHAIN STEP FIXES, so that the fold
-- below and the caps face above name the same hypothesis.
