-- Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK
-- chainBurstOK … chainsCapsOK
module Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK where

open import Data.Bool    using (true; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; +-assoc; ⊔-mono-≤;
  ⊔-identityʳ; m⊔n≤m+n; *-distribˡ-+)
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
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤)
open import Relation.Binary.PropositionalEquality
  using (_≡_; sym; cong)

open import Rx.Prim      using (Id; _at_from_as_; after_,_; close; exhausted)
open import Rx.Exp       using (Ctx; Closed)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nodesMax; burstsOK; capsWalkOK; FaceOK)
open import Verify-Budget-Sufficient.Nest-Walk.Share-Fold using
  (foldPath-nodes)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthChain)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (deliverLen; deliverNestD; deliverNestF)
open import Verify-Budget-Sufficient.Fan-Caps using
  (delSq)
open import Verify-Budget-Sufficient.Nest-Store using
  (nest-inflate; nestUnit; nodeNest)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; arrSource; Path; arrTy; chainStep; budgetAt; arrTick)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Caps using
  (Caps; _⊑ᶜ_; frameStep; sizeCount)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (pathSz?)

chainBurstOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (W : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainBurstOK {n = n} {e = e} W id a path sched st =
  burstsOK W (budgetAt e (Sched.slots sched) id) n id (arrTick a) path
           (arrVal a ∷ []) (Arrival.isLast a) sched st

-- AND THE SAME PACKAGING FOR THE CAPS THE `*All` FRAMES SPEND, so a
-- consumer states one hypothesis per walk rather than one per frame.
chainCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) → Set
chainCapsOK {n = n} {e = e} c ac sl d Lv id a path sched st =
  capsWalkOK c ac sl d Lv (budgetAt e (Sched.slots sched) id) n id (arrTick a) path
             (arrVal a ∷ []) (Arrival.isLast a) sched st

-- THE STORE'S ONE ACCUMULATING CORNER, AND WHAT PAYS FOR IT IS THE
-- SELECTION.  Within the node arm the store deepens at two sites, not
-- five: `switch` and `exhaust` cannot move it whatever they store, and
-- a bounded `mergeAll`'s queue cannot either -- the measure over it is
-- a MAX, parking adds the single observable that arrived, and the
-- drain returns a SUFFIX of the queue it was handed.  What is left is
-- a `scan`'s accumulator, which the fold over an instant's values
-- genuinely deepens, and the inners a drain SUBSCRIBES, which install
-- their own nodes.
--
-- SO THE QUANTITY TO CHARGE IS THE CHAIN THE WALK IS WALKING, and the
-- whole of the claim is ONE CHAIN'S STEP.  Both storing sites sit under
-- a single `chainStep`, and the fold visits each chain once, so the
-- walk-level statement is a plain induction over the list -- the skip
-- arm weakens by a chain, the step arm spends this leaf and
-- re-associates -- and everything a single chain does to the store,
-- however many inners it subscribes, is invisible to a MAX that moves
-- once.
--
-- AND THE CHARGE IS THE PATH'S OWN, NOT THE PROGRAM'S.  A `scan` frame
-- carries its accumulator function, and the node the step installs is
-- that function applied to what arrived -- so the two quantities a step
-- can deepen by are the PAYLOAD's nesting and the wraps the frames
-- below it add, which is exactly what `pathNestD` counts.  Charging a
-- syntactic ceiling on `e` instead reads as tighter and is not even
-- true: the path is a free argument, so it is under no obligation to be
-- one of `e`'s.  Tying the two together is the CONSUMER's business,
-- where the chain list comes from the registry and the payload from a
-- slot, and it is a different fact from this one.
--
-- DEAD ROUTE: charging per MINTED INSTANCE, the same statement with the
--   schedule's own node counter in place of the length.  The count is
--   quadratic in the chain axis -- 20, 33, 48, 65 as `progF`'s width
--   climbs -- while every width in this development is linear in it, so
--   the charge is crossed by construction rather than by a constant:
--   at eighteen copies the path width and the entry ceiling are both
--   past, at twenty-two `capsBase` is too, 713 against 690.  The
--   counting is what fails and not the currency, the parent's own
--   conclusion holding at the crossing shape.  Do not re-derive a
--   tighter width for a mint count.
-- DEAD ROUTE: the two max-shaped charges, `store ⊔ nestSyn` and
--   `store + nestSyn`, which drop the count entirely on the reading
--   that a MAX cannot move more than one level per instant.  Both are
--   false at the same shape, the nodes map reading 26 against a store
--   of 3 and a `nestSyn` of 6.  A walk deepens once per CHAIN, so the
--   count that survives is a count of chains and there is no
--   count-free form of this row.
-- REFUTED: `Refuted.Chain-Step-Nodes` kills the `nestSyn` form of this
--   very statement, eleven against nine, and the gap is unbounded in
--   the fold depth of a frame the program never mentions.
chainStep-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c ac : Caps) (d : ℕ) (W : ℕ) (sl : Slots Γ) (Lv : ℕ) (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl → 1 ≤ W → 1 ≤ Caps.cSize c → c ⊑ᶜ ac →
  chainBurstOK W id a path sched st →
  chainCapsOK c ac sl d Lv id a path sched st →
  depthChain id a path sched st ≤ d →
  pathSz? (Caps.cSize ac) path ≡ true →
  Lv ≤ sizeCount c d ⊔ Caps.cSize c →
  ⦃ _ : FaceOK c sl ⦄ →
  let r = chainStep id a path sched st in
  Σ ℕ λ j →
  let c′ = frameStep j c in
  (j ≤ sizeCount c d ⊔ Caps.cSize c)
  × (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes (proj₂ (proj₂ r)))
    ≤ nestFac (Caps.cSize c′) W ^ deliverLen n ac path
      * (deliverNestF n ac path ^ W
         * (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
            + W * (nestDᵛ (arrTy a) (arrVal a) + deliverNestD n ac path
                   + suc (deliverLen n ac path) * nestU (delSq n c′) (nestUnit e sl)))))
chainStep-nodes {n = n} {e = e} c ac d W sl Lv id a path sched st hsl 1≤W 1≤S hac hb hc hdp hpz hlv =
  proj₁ FP ,
  proj₁ (proj₂ FP) ,
  ≤-trans (proj₂ (proj₂ FP))
    (*-monoʳ-≤ (nestFac (Caps.cSize c′) W ^ deliverLen n ac path)
    (*-monoʳ-≤ (deliverNestF n ac path ^ W)
      (≤-trans (+-monoˡ-≤ (W * (deliverNestD n ac path + U))
                          (≤-trans (⊔-mono-≤ (≤-refl {nodesMax st})
                                             (≤-reflexive (⊔-identityʳ V)))
                                   (m⊔n≤m+n (nodesMax st) V)))
      (≤-trans (≤-reflexive (+-assoc (nodesMax st) V (W * (deliverNestD n ac path + U))))
               (+-monoʳ-≤ (nodesMax st) spread)))))
  where
  FP = foldPath-nodes c ac d W sl Lv (budgetAt e (Sched.slots sched) id) n id
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st hsl 1≤W 1≤S hac hb hc hdp
         hpz hlv
  c′ = frameStep (proj₁ FP) c
  V = nestDᵛ (arrTy a) (arrVal a)
  U = suc (deliverLen n ac path) * nestU (delSq n c′) (nestUnit e sl)

  spread : V + W * (deliverNestD n ac path + U) ≤ W * (V + deliverNestD n ac path + U)
  spread =
    ≤-trans (+-monoˡ-≤ (W * (deliverNestD n ac path + U)) (nest-inflate W V 1≤W))
      (≤-trans (≤-reflexive (sym (*-distribˡ-+ W V (deliverNestD n ac path + U))))
               (≤-reflexive (cong (W *_) (sym (+-assoc V (deliverNestD n ac path) U)))))

-- AND OVER A CASCADE'S CHAIN LIST, mirroring `cascadeGo`: a cancelled
-- registration walks nothing and owes nothing, and a delivered one owes
-- its own walk and then the rest of the fold at the state it left.
chainsBurstOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (W : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsBurstOK W a nextId []               sched st = ⊤
chainsBurstOK W a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsBurstOK W a nextId chains sched st
  else (chainBurstOK W nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × chainsBurstOK W a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- AND THE CAPS THE SAME FOLD SPENDS, arm for arm with the burst
-- hypothesis above: a cancelled registration walks nothing, so it owes
-- nothing here either.
chainsCapsOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (cp ac : Caps) (sl : Slots Γ) (d Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) → Set
chainsCapsOK cp ac sl d Lv a nextId []               sched st = ⊤
chainsCapsOK cp ac sl d Lv a nextId ((rid , c) ∷ chains) sched st =
  if any (_≡ᵇ rid) (EvalSt.cancelled st)
  then chainsCapsOK cp ac sl d Lv a nextId chains sched st
  else (chainCapsOK cp ac sl d Lv nextId a c sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
        × Σ ℕ λ L′ →
          (Lv + L′ ≤ sizeCount cp d ⊔ Caps.cSize cp)
        × chainsCapsOK cp ac sl d (Lv + L′) a nextId chains
            (proj₁ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st }))))
            (proj₂ (proj₂ (chainStep nextId a c sched
                             (record st { delivered = rid ∷ EvalSt.delivered st })))))
