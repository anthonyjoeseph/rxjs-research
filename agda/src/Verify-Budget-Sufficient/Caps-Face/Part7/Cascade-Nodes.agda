-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes
-- cascadeGo-nodes-chains, chains-count-width
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes where

open import Data.Bool    using (true; false)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; *-identityˡ; ^-distribˡ-+-*; ^-monoˡ-≤; *-monoˡ-≤; ≤-trans; ≤-reflexive; m≤m+n;
  m≤n+m; n≤1+n; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; ⊔-lub; m≤m⊔n; m≤n⊔m; +-mono-≤;
  *-comm)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length; foldr)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin     using (Fin)
import Data.Fin as Fin
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_; map to mapᴬ)
open import Data.List.Relation.Unary.All.Properties
  using (concat⁺; tabulate⁺)
  renaming (++⁺ to all-++; ++⁻ˡ to all-++ˡ; ++⁻ʳ to all-++ʳ)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; trans; subst; cong)

open import Rx.Prim      using (Id; _at_from_as_; after_,_)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestFac-monoS; 1≤nestFac; nestU; nestU-mono)
open import Verify-Budget-Sufficient.Nest-Walk using
  (fac-hoist; one-pow; FaceOK)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (deliverLen; deliverNestD; deliverNestF; 1≤deliverNestF; chainsDelLen; chainsDelNestD;
  chainsDelNestF)
open import Verify-Budget-Sufficient.Fan-Caps using
  (delSq; delSq-monoᶜ)
open import Verify-Budget-Sufficient.Nest-Store using
  (nest-telescope; nest-scale; pow-distrib-*; realWidAt; realWidAt-def; nestUnit; nodeNest)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; chainsOf; cascadeGo; Path; arrTy; chainStep)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (1≤pow≤; Caps; capsAt; _⊑ᶜ_; frameStep; frameStep-reg-mono; iterSize-mono-count; sizeCount)
open import Verify-Budget-Sufficient.Measures using
  (∧-true)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; pathSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (chainStep-slots; chainsOf-length)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainStep-nodes; chainsBurstOK; chainsCapsOK)

cascadeGo-nodes-chains : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize cp → cp ⊑ᶜ ac →
  chainsBurstOK W a nextId chains sched st →
  chainsCapsOK cp ac sl d Lv a nextId chains sched st →
  depthCascade a nextId chains sched st ≤ d →
  all (λ rc → pathSz? (Caps.cSize ac) (proj₂ rc)) chains ≡ true →
  Lv ≤ sizeCount cp d ⊔ Caps.cSize cp →
  ⦃ _ : FaceOK cp sl ⦄ →
  let r = cascadeGo a nextId chains sched st in
  Σ ℕ λ j →
  let cp′ = frameStep j cp in
  (j ≤ sizeCount cp d ⊔ Caps.cSize cp)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize cp′) W ^ chainsDelLen n ac chains
      * (chainsDelNestF n ac chains ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + length chains
                * (W * (nestDᵛ (arrTy a) (arrVal a) + chainsDelNestD n ac chains
                        + suc (chainsDelLen n ac chains) * nestU (delSq n cp′) (nestUnit e sl))))))
cascadeGo-nodes-chains cp ac d W sl Lv a nextId [] sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv =
  0 , z≤n ,
  ≤-trans (≤-trans (m≤m+n _ 0) (one-pow W _)) (≤-reflexive (sym (*-identityˡ _)))
cascadeGo-nodes-chains {n = n} {e = e} cp ac d W sl Lv a nextId ((rid , c) ∷ chains) sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv
  with any (_≡ᵇ rid) (EvalSt.cancelled st) | hb | hc
... | true | hb′ | hc′ =
  proj₁ TL ,
  proj₁ (proj₂ TL) ,
  ≤-trans (proj₂ (proj₂ TL))
    (≤-trans (*-monoʳ-≤ (R ^ K)
      (≤-trans (*-monoʳ-≤ (G ^ W) (+-monoʳ-≤ M grow))
               (≤-trans (nest-scale (deliverNestF n ac c ^ W) (G ^ W)
                           (M + suc (length chains) * (W * (V + C′ + U)))
                           (1≤pow≤ (deliverNestF n ac c) W (1≤deliverNestF n ac c)))
                        (≤-reflexive
                          (cong (_* (M + suc (length chains) * (W * (V + C′ + U))))
                                (sym (pow-distrib-* W (deliverNestF n ac c) G)))))))
    (≤-trans (nest-scale (R ^ deliverLen n ac c) (R ^ K) Xc (1≤pow≤ R (deliverLen n ac c) 1≤R))
             (≤-reflexive (cong (_* Xc) (sym (^-distribˡ-+-* R (deliverLen n ac c) K))))))
  where
  TL = cascadeGo-nodes-chains cp ac d W sl Lv a nextId chains sched st hsl 1≤W 1≤S hac hb′ hc′
         (lub3-l (depthCascade a nextId chains sched st)
                 (depthChain nextId a c sched
                    (record st { delivered = rid ∷ EvalSt.delivered st }))
                 (depthCascade a nextId chains
                    (proj₁ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))
                    (proj₂ (proj₂ (chainStep nextId a c sched
                       (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
         (proj₂ (∧-true _ _ hpz)) hlv
  cp′ = frameStep (proj₁ TL) cp
  R  = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K  = chainsDelLen n ac chains
  M  = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V  = nestDᵛ (arrTy a) (arrVal a)
  C  = chainsDelNestD n ac chains
  C′ = deliverNestD n ac c ⊔ C
  Uz = nestU (delSq n cp′) (nestUnit e sl)
  U  = suc (deliverLen n ac c + K) * Uz
  Uₜ = suc K * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n ac c)))
  G  = chainsDelNestF n ac chains
  Xc = (deliverNestF n ac c * G) ^ W * (M + suc (length chains) * (W * (V + C′ + U)))
  grow : length chains * (W * (V + C + Uₜ)) ≤ suc (length chains) * (W * (V + C′ + U))
  grow = *-mono-≤ (n≤1+n (length chains))
                  (*-monoʳ-≤ W
                    (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n ac c) C)) Uₜ≤U))
... | false | hb′ | hc′ =
  jt ,
  ⊔-lub (proj₁ (proj₂ TAILr)) (proj₁ (proj₂ HEADr)) ,
  ≤-trans TAILw
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (*-monoʳ-≤ (G ^ W)
                        (+-monoˡ-≤ (length chains * (W * (V + C + Uₜ)))
                                   HEADw)))
          (≤-trans (*-monoʳ-≤ (R ^ K)
                      (fac-hoist (R ^ deliverLen n ac c) (G ^ W) A Z (1≤pow≤ R (deliverLen n ac c) 1≤R)))
          (≤-trans (≤-reflexive (sym (*-assoc (R ^ K) (R ^ deliverLen n ac c) Y)))
          (≤-trans (≤-reflexive
                      (cong (_* Y) (trans (*-comm (R ^ K) (R ^ deliverLen n ac c))
                                          (sym (^-distribˡ-+-* R (deliverLen n ac c) K)))))
                   (*-monoʳ-≤ (R ^ (deliverLen n ac c + K))
          (≤-trans (nest-telescope (deliverNestF n ac c ^ W) (G ^ W) M
                                   (W * (V + deliverNestD n ac c + Uc))
                                   (length chains * (W * (V + C + Uₜ)))
                                   (1≤pow≤ (deliverNestF n ac c) W (1≤deliverNestF n ac c)))
                   (≤-trans (≤-reflexive
                               (cong (_* (M + (W * (V + deliverNestD n ac c + Uc)
                                               + length chains * (W * (V + C + Uₜ)))))
                                     (sym (pow-distrib-* W (deliverNestF n ac c) G))))
                     (*-monoʳ-≤ ((deliverNestF n ac c * G) ^ W)
                       (+-monoʳ-≤ M
                         (+-mono-≤ (*-monoʳ-≤ W
                                     (+-mono-≤ (+-monoʳ-≤ V (m≤m⊔n (deliverNestD n ac c) C)) Uc≤U))
                                   (*-monoʳ-≤ (length chains)
                                     (*-monoʳ-≤ W
                                       (+-mono-≤ (+-monoʳ-≤ V (m≤n⊔m (deliverNestD n ac c) C))
                                                 Uₜ≤U)))))))))))))
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  r₁  = chainStep nextId a c sched st′
  sd₁ = proj₁ (proj₂ r₁)
  st₁ = proj₂ (proj₂ r₁)

  -- THE CASCADE'S LEVEL IS THE JOIN OF THIS CHAIN'S AND THE REST'S,
  -- which is the path fold's rule one layer out: a chain walks its own
  -- descent and reports what that descent cost, and the fold cannot ask
  -- one chain to have paid for another's substitutions.
  HEADr = chainStep-nodes cp ac d W sl Lv nextId a c sched st′ hsl
            1≤W 1≤S hac (proj₁ hb′) (proj₁ hc′)
            (lub3-m (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₁ (∧-true _ _ hpz)) hlv
  TAILr = cascadeGo-nodes-chains cp ac d W sl (Lv + proj₁ (proj₂ hc′)) a nextId chains sd₁ st₁
            (trans (chainStep-slots nextId a c sched st′) hsl) 1≤W 1≤S hac
            (proj₂ hb′) (proj₂ (proj₂ (proj₂ hc′)))
            (lub3-r (depthCascade a nextId chains sched st)
                    (depthChain nextId a c sched st′)
                    (depthCascade a nextId chains sd₁ st₁) hdp)
            (proj₂ (∧-true _ _ hpz)) (proj₁ (proj₂ (proj₂ hc′)))
  jt  = proj₁ TAILr ⊔ proj₁ HEADr
  cp′ = frameStep jt cp

  sizeₕ : Caps.cSize (frameStep (proj₁ HEADr) cp) ≤ Caps.cSize cp′
  sizeₕ = iterSize-mono-count (Caps.cSize cp) (Caps.cSize cp) 1≤S
            (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  regₕ : Caps.cReg (frameStep (proj₁ HEADr) cp) ≤ Caps.cReg cp′
  regₕ = frameStep-reg-mono cp (m≤n⊔m (proj₁ TAILr) (proj₁ HEADr))

  sizeₜ : Caps.cSize (frameStep (proj₁ TAILr) cp) ≤ Caps.cSize cp′
  sizeₜ = iterSize-mono-count (Caps.cSize cp) (Caps.cSize cp) 1≤S
            (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  regₜ : Caps.cReg (frameStep (proj₁ TAILr) cp) ≤ Caps.cReg cp′
  regₜ = frameStep-reg-mono cp (m≤m⊔n (proj₁ TAILr) (proj₁ HEADr))

  M   = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
  V   = nestDᵛ (arrTy a) (arrVal a)
  C   = chainsDelNestD n ac chains
  Uz  = nestU (delSq n cp′) (nestUnit e sl)
  G   = chainsDelNestF n ac chains
  R   = nestFac (Caps.cSize cp′) W
  1≤R : 1 ≤ R
  1≤R = 1≤nestFac (Caps.cSize cp′) W
  K   = chainsDelLen n ac chains

  HEADw = ≤-trans (proj₂ (proj₂ HEADr))
            (*-mono-≤ (^-monoˡ-≤ (deliverLen n ac c) (nestFac-monoS sizeₕ W))
              (*-monoʳ-≤ (deliverNestF n ac c ^ W)
                (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st′))
                  (*-monoʳ-≤ W
                    (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n ac c)
                      (*-monoʳ-≤ (suc (deliverLen n ac c))
                        (nestU-mono (delSq n (frameStep (proj₁ HEADr) cp))
                                    (delSq n cp′) (nestUnit e sl)
                          (delSq-monoᶜ n (frameStep (proj₁ HEADr) cp) cp′
                                       sizeₕ regₕ))))))))

  TAILw = ≤-trans (proj₂ (proj₂ TAILr))
            (*-mono-≤ (^-monoˡ-≤ K (nestFac-monoS sizeₜ W))
              (*-monoʳ-≤ (G ^ W)
                (+-monoʳ-≤ (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st₁))
                  (*-monoʳ-≤ (length chains)
                    (*-monoʳ-≤ W
                      (+-monoʳ-≤ (nestDᵛ (arrTy a) (arrVal a) + C)
                        (*-monoʳ-≤ (suc K)
                          (nestU-mono (delSq n (frameStep (proj₁ TAILr) cp))
                                      (delSq n cp′) (nestUnit e sl)
                            (delSq-monoᶜ n (frameStep (proj₁ TAILr) cp) cp′
                                         sizeₜ regₜ)))))))))
  U   = suc (deliverLen n ac c + K) * Uz
  Uₜ  = suc K * Uz
  Uc  = suc (deliverLen n ac c) * Uz
  Uₜ≤U : Uₜ ≤ U
  Uₜ≤U = *-monoˡ-≤ Uz (s≤s (m≤n+m K (deliverLen n ac c)))
  Uc≤U : Uc ≤ U
  Uc≤U = *-monoˡ-≤ Uz (s≤s (m≤m+n (deliverLen n ac c) K))
  A   = deliverNestF n ac c ^ W * (M + W * (V + deliverNestD n ac c + Uc))
  Z   = length chains * (W * (V + C + Uₜ))
  Y   = G ^ W * (A + Z)

-- AND THE SELECTION IS WITHIN THE REAL WIDTH, WHICH IS NOW A TWO-LINE
-- READING RATHER THAN A FACE OF ITS OWN.  A cascade's chain list is a
-- filter of the registry, and the width IS the registry cap, so the
-- fact the row above needs is `capsOK?`'s own fifth conjunct composed
-- with the filter's length bound -- both already proven.
--
-- WHAT THAT REPLACED IS THE POINT.  The width used to be a quantity
-- this development invented, `capsBase` at the entry squaring itself
-- each instant, and bridging it to anything a walk spends took two
-- leaves that were ranked FALSITY and could not be instantiated.
-- Choosing the width to BE the thing that is bounded is what makes the
-- bridge disappear instead of being ground.
chains-count-width : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (capsAt e sl id) sched st ≡ true →
  length (chainsOf a st) ≤ realWidAt e sl id
chains-count-width {e = e} sl id a sched st hcaps =
  subst (length (chainsOf a st) ≤_) (sym (realWidAt-def e sl id))
        (≤-trans (chainsOf-length a st)
                 (capsOK?-count (capsAt e sl id) sched st hcaps))

-- THE NODE-STATE COMPONENT, WHICH IS WHERE THE WIDTH IS ACTUALLY SPENT.
-- A `scan` node stores its accumulator and a bounded `mergeAll` node
-- stores its parked queue, so the nodes map is the only part of the
-- store a delivery can DEEPEN rather than merely re-point.  Measured
-- across every family the harness drives, the slot store, the pending
-- sources and the registry read the same before the walk and after,
-- and every unit of the growth is here -- which is what makes the
-- other three arms of the parent's `⊔` cheap and this one primitive.
