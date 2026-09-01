-- Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
-- arr-chain-caps … arr-chains-caps
module Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps where

open import Data.Bool    using (true; false; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _∸_; _⊔_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (m+[n∸m]≡n; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n; m≤n+m; n≤1+n; *-identityʳ; +-monoʳ-≤; m≤m⊔n;
  +-suc)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length)
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
open import Data.Unit    using (tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim      using (Id; _at_from_as_; after_,_; close; exhausted)
open import Rx.Exp       using (Ctx; Closed; sizeᵉ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Verify-Budget-Sufficient.Nest-Ceiling using
  (Reached; Ent; Pos; ent-step; base; walk)
open import Verify-Budget-Sufficient.Subscribe-Face using (subscribeInner-caps; innerFinish-caps)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade; depthChain; lub3-l; lub3-m; lub3-r)
open import Verify-Budget-Sufficient.Nest-Store using
  (storeNestMax; realWidAt-def; nestUnit; sightCeil)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; cascadeLatch; arrSource; chainsOf; cascadeGo; Path;
  arrTy; regAt; dCapᶜ; lvls; iterL; chainStep; budgetAt; arrTick)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk using
  (module Walk)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN; delivN-cons; delivN-split; chainStep-deliv; cascadeGo-deliv; ⊑ᵈ-trans)
open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; Caps; capsAt; capsAt-base-size; capsH; cDel; _⊑ᶜ_; dCapᶜ-mono;
  frameStep; frameStep-0; frameStep-mono-j; iterL-mono; lvls-add; lvls-mono; sizeCount;
  sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; all-impl)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsAt-round-size; capsOK?; n≤capsAt-size; pathSz?; pathSz?-widen; valCaps?; nestClosOK?ᵛ;
  nestClosOK?ᵛ-widen)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-regs; pathSz?-len; slotsCaps?-capsAt; valsCaps?; valsCaps?-lvl)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (valCaps?-widen)
open import Decide using (∧-intro)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeGo-deliveries; cascadeLatch-caps; chainStep-slots; chainsOf-length; walkH)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Chain-Caps-OK using
  (chainCapsOK; chainsCapsOK)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (chains-count-width)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Ring-Vocabulary using
  (floor-parts)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Walk-Sink using
  (chain-walk-caps)

arr-chain-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  all (nestClosOK?ᵛ (frameStep Lv (capsAt e sl id)) sl (arrTy a)) (arrVal a ∷ []) ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  (Σ ℕ λ g → Σ ℕ λ P →
     (4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g)
     × (lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv 1
          ≤ P)
     × Reached (capsAt e sl id) (capsH e sl id) P g) →
  chainCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv nextId a path sched st
arr-chain-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hvc hcl hpz hdp
  (g , P , hfl , hlvP , hR) =
  chain-walk-caps sl id Lv (budgetAt e (Sched.slots sched) nextId) n nextId
    (arrTick a) (arrSource a) path (arrVal a ∷ [])
    (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
    (Arrival.isLast a) sched st
    (sleq , cok , hvc , hcl , hpz , hdp , (g , P , hfl , ENTRY , hR))
  where
  c   = capsAt e sl id
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  ENTRY : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv ≤ P
  ENTRY = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
            hlvP


-- ONE CHAIN'S STEP IS THE PATH FOLD, so the level it lands at is the
-- fold's own theorem and not a leaf.  `chainStep` IS `foldPath` at the
-- minted gas, the walk skeleton is instantiated at exactly the caps
-- hypotheses here, and its receipt reports the three things the
-- statement asks for: the level, that the walk only climbed to it, and
-- the state fact there.  The increment is the difference, which is why
-- the conclusion is stated at `Lv + L'` and proven at the absolute
-- level the walk names.
--
-- TWIN: `stepFrame-caps` -- one frame of this same fold, with the same
--   discipline: invariant at the stepped cap, own increment reported.
chainStep-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valCaps? (frameStep Lv (capsAt e sl id)) sl (arrTy a) (arrVal a) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Σ ℕ λ L′ →
    (Lv + L′ ≤ lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id)
                 Lv (suc (delivN st (proj₂ (proj₂ (chainStep nextId a path sched st))))))
    × (capsOK? (frameStep (Lv + L′) (capsAt e sl id))
         (proj₁ (proj₂ (chainStep nextId a path sched st)))
         (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
chainStep-caps {n = n} {e = e} sl id Lv a nextId path sched st sleq cok hpz hvc hdp =
  W.Res.lvl FP ∸ Lv
  , subst (_≤ CEIL) (sym EQ) (≤-trans (W.Res.hi FP) STEP)
  , subst (λ x → capsOK? (frameStep x c)
                   (proj₁ (proj₂ (chainStep nextId a path sched st)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st))) ≡ true)
          (sym EQ) (proj₂ (proj₁ (W.Res.good FP)))
  where
  c = capsAt e sl id
  d = capsH e sl id
  2≤S : 2 ≤ Caps.cSize c
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH (λ {n′} {Γ′} {t′} {e′} {u′} →
                            subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
                         (λ {n′} {Γ′} {t′} {e′} {s′} →
                            innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
                         c d sl 2≤S (1≤capsAt-reg e sl id)
                         (slotsCaps?-capsAt e sl id) slSz)
  FP = W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
         (arrTick a) (arrSource a) path (arrVal a ∷ [])
         (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
         (Arrival.isLast a) sched st
         ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st cok)
         hpz (∧-intro (∧-intro hvc refl) refl)
         (W.eb-seed Lv (arrSource a) (Arrival.isLast a)) tt tt hdp
  EQ : Lv + (W.Res.lvl FP ∸ Lv) ≡ W.Res.lvl FP
  EQ = m+[n∸m]≡n (W.Res.lo FP)
  D = delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
  CEIL = lvls (Caps.cSize c) (Caps.cWid c) d Lv (suc D)
  -- one chain is at most `suc (sizeAt S Lv)` frames, so its whole level
  -- climb is peeled off the front of the walk's own ladder as ONE
  -- delivery's charge — which is what makes the ceiling base-relative
  -- and so composable along the cascade
  chain≤ : iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv
             ≤ lvls (Caps.cSize c) (Caps.cWid c) d Lv 1
  chain≤ = iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
             (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz) (n≤1+n _))
  STEP : lvls (Caps.cSize c) (Caps.cWid c) d
           (iterL (Caps.cSize c) (Caps.cWid c) d (pathLen path) Lv) D ≤ CEIL
  STEP = ≤-trans (lvls-mono D D 2≤S ≤-refl ≤-refl chain≤ ≤-refl)
                 (≤-reflexive (sym (lvls-add (Caps.cSize c) (Caps.cWid c) d Lv 1 D)))

-- ONE CHAIN'S DELIVERIES AGAINST THE BUDGET READ AT ITS OWN POSITION,
-- which is the recursive shape of the whole claim rather than a step
-- of it: the cascade's total is what `cascadeGo-deliveries` bounds at
-- entry, and this is the same statement one round down, at the level
-- the round's ledger has climbed to instead of at the entry level.
-- The gas is the term's own operator budget, and it is what stops the
-- statement being vacuous -- at gas zero the cap is zero and no chain
-- delivering anything can fit.
chain-deliv-cap : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) (Lv J g i : ℕ) →
  Sched.slots sched ≡ sl →
  n ≤ g →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  pathSz? (Caps.cSize (frameStep Lv (capsAt e sl id))) path ≡ true →
  valsCaps? (frameStep Lv (capsAt e sl id)) sl (arrVal a ∷ []) ≡ true →
  depthChain nextId a path sched st ≤ capsH e sl id →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  delivN st (proj₂ (proj₂ (chainStep nextId a path sched st)))
    ≤ dCapᶜ (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id))
            (Caps.cReg (capsAt e sl id)) (capsH e sl id) g
            (Pos (capsAt e sl id) (capsH e sl id) J g i)
chain-deliv-cap {n = n} {e = e} sl id a nextId path sched st Lv J g i
  sleq n≤g cok hpz hvc hdp hLv =
  ≤-trans (W.Res.cnt (W.foldPath-go Lv (budgetAt e (Sched.slots sched) nextId) n nextId
                        (arrTick a) (arrSource a) path (arrVal a ∷ [])
                        (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                        (Arrival.isLast a) sched st
                        ((sleq , cok) , capsOK?-regs (frameStep Lv c) sched st cok)
                        hpz hvc refl tt tt hdp))
          (dCapᶜ-mono {S} {S} {Wd} {Wd} {R} {R} {_} {_} {d} n g
             2≤S ≤-refl ≤-refl ≤-refl n≤g CLIMB)
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  Wd  = Caps.cWid c
  R   = Caps.cReg c
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  module W = Walk {e = e} S Wd R d 2≤S
    (walkH (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
           (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
           c d sl 2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id)
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)))
  -- the chain's frames climb at most one restart, which is what
  -- `pathSz?` bounds, and one restart from the round's ledger IS the
  -- position -- so the level the fold reads the budget at dominates
  -- the level the chain's own walk reads it at
  CLIMB : iterL S Wd d (pathLen path) Lv ≤ Pos c d J g i
  CLIMB = ≤-trans (iterL-mono (pathLen path) _ 2≤S ≤-refl ≤-refl ≤-refl
                     (≤-trans (pathSz?-len (Caps.cSize (frameStep Lv c)) path hpz)
                              (n≤1+n _)))
                  (lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl)


-- `R` for the tail, related by `lvls-add`.
arr-chains-caps-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (Lv : ℕ) (a : Arrival Γ) (nextId : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  lvls (Caps.cSize (capsAt e sl id)) (Caps.cWid (capsAt e sl id)) (capsH e sl id) Lv
       (delivN st (proj₂ (proj₂ (cascadeGo a nextId chains sched st))))
    ≤ sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id) →
  capsOK? (frameStep Lv (capsAt e sl id)) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId chains sched st ≤ capsH e sl id →
  (J g i : ℕ) →
  4 + (sizeᵉ e + slotsSize sl) + n + n ≤ g →
  Reached (capsAt e sl id) (capsH e sl id) J (suc g) →
  i + length chains
    ≤ regAt (Caps.cSize (capsAt e sl id)) (Caps.cReg (capsAt e sl id)) J →
  Lv ≤ Ent (capsAt e sl id) (capsH e sl id) J g i →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) Lv a nextId chains sched st
arr-chains-caps-go sl id Lv a nextId [] sched st sleq hlv cok hpz hvc hcl hdp
  J g i hfl hR hlen hLv = tt
arr-chains-caps-go {n = n} {e = e} sl id Lv a nextId ((rid , path) ∷ chains) sched st sleq hlv cok hpz hvc hcl hdp
  J g i hfl hR hlen hLv
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = arr-chains-caps-go sl id Lv a nextId chains sched st sleq hlv cok
                (proj₂ (∧-true _ _ hpz)) hvc hcl
                (lub3-l (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched
                           (record st { delivered = rid ∷ EvalSt.delivered st }))
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))
                           (proj₂ (proj₂ (chainStep nextId a path sched
                              (record st { delivered = rid ∷ EvalSt.delivered st }))))) hdp)
                J g i hfl hR
                (≤-trans (+-monoʳ-≤ i (n≤1+n (length chains))) hlen) hLv
... | false =
      arr-chain-caps sl id Lv a nextId path sched st′ sleq cok
        HVC HCL
        (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
        (lub3-m (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        (g , Pos c d J g i , hfl , CH≤ , walk J g i HI hR)
    , proj₁ ST
    , FLAT
    , arr-chains-caps-go sl id (Lv + proj₁ ST) a nextId chains
        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
        (proj₂ (proj₂ (chainStep nextId a path sched st′)))
        (trans (chainStep-slots nextId a path sched st′) sleq)
        REC (proj₂ (proj₂ ST))
        (proj₂ (∧-true _ _ hpz)) hvc hcl
        (lub3-r (depthCascade a nextId chains sched st)
                (depthChain nextId a path sched st′)
                (depthCascade a nextId chains
                   (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                   (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        J g (suc i) hfl hR
        (subst (_≤ regAt S (Caps.cReg c) J) (+-suc i (length chains)) hlen)
        (≤-trans (proj₁ (proj₂ ST)) STEP)
  where st′ = record st { delivered = rid ∷ EvalSt.delivered st }
        c   = capsAt e sl id
        S   = Caps.cSize c
        W   = Caps.cWid c
        d   = capsH e sl id
        TOP = sizeCount c d ⊔ S
        2≤S = 2≤capsAt-size e sl id
        st₁ = proj₂ (proj₂ (chainStep nextId a path sched st′))
        D   = delivN st′ st₁
        R   = delivN st₁ (proj₂ (proj₂ (cascadeGo a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
        step⊑ = frameStep-mono-j c 2≤S (z≤n {Lv})
        c⊑ : c ⊑ᶜ frameStep Lv c
        c⊑ = subst (_⊑ᶜ frameStep Lv c) (frameStep-0 c) step⊑
        HVC0 : valsCaps? c sl (arrVal a ∷ []) ≡ true
        HVC0 = ∧-intro (∧-intro hvc refl) refl
        HVC : valsCaps? (frameStep Lv c) sl (arrVal a ∷ []) ≡ true
        HVC = valsCaps?-lvl c (frameStep Lv c) sl (arrVal a ∷ []) c⊑ HVC0
        HCL : all (nestClosOK?ᵛ (frameStep Lv c) sl (arrTy a)) (arrVal a ∷ []) ≡ true
        HCL = all-impl _ _
                (λ v h → nestClosOK?ᵛ-widen sl _ v c⊑ h)
                (arrVal a ∷ []) (∧-intro hcl refl)
        ST  = chainStep-caps sl id Lv a nextId path sched st′ sleq cok
                (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                (valCaps?-widen sl (arrTy a) (arrVal a) c⊑ hvc)
                (lub3-m (depthCascade a nextId chains sched st)
                        (depthChain nextId a path sched st′)
                        (depthCascade a nextId chains
                           (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                           (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
        -- THE CASCADE'S OWN LEDGER LINE, at the state this arm has
        -- already reduced to: an uncancelled registration costs one
        -- delivery, plus this chain's fold, plus the tail's.  It is
        -- written here rather than taken from the ledger stratum
        -- because the `with` has replaced the cascade by its reduct,
        -- and a lemma stated over the unreduced application no longer
        -- applies to what this arm holds.
        CS  = chainStep-deliv nextId a path sched st′
        GO  = cascadeGo-deliv a nextId chains
                (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁
        SPLIT : delivN st (proj₂ (proj₂ (cascadeGo a nextId chains
                  (proj₁ (proj₂ (chainStep nextId a path sched st′))) st₁)))
                  ≡ suc (D + R)
        SPLIT = trans (delivN-cons rid st _ (⊑ᵈ-trans CS GO))
                      (cong suc (delivN-split CS GO))
        hlvC : lvls S W d Lv (suc (D + R)) ≤ TOP
        hlvC = subst (λ x → lvls S W d Lv x ≤ TOP) SPLIT hlv
        -- this chain's own charge, which is what both the leaf below
        -- and the Σ above are bounded by
        FLATC : lvls S W d Lv (suc D) ≤ TOP
        FLATC = ≤-trans (lvls-mono (suc D) (suc (D + R)) 2≤S ≤-refl ≤-refl ≤-refl
                           (s≤s (m≤m+n D R)))
                        hlvC
        FLAT = ≤-trans (proj₁ (proj₂ ST)) FLATC
        -- this chain sits at the round's `i`-th position, and one
        -- restart from there is what its own frames may climb
        HI : suc i ≤ regAt S (Caps.cReg c) J
        HI = ≤-trans (subst (suc i ≤_) (sym (+-suc i (length chains)))
                            (s≤s (m≤m+n i (length chains))))
                     hlen
        CH≤ : lvls S W d Lv 1 ≤ Pos c d J g i
        CH≤ = lvls-mono 1 1 2≤S ≤-refl ≤-refl hLv ≤-refl
        hgn = proj₁ (proj₂ (floor-parts (4 + (sizeᵉ e + slotsSize sl)) n n g hfl))
        -- and the fold's own climb lands on the NEXT position exactly
        -- when this chain's deliveries fit the budget read at this one
        STEP : lvls S W d Lv (suc D) ≤ Ent c d J g (suc i)
        STEP = ≤-trans (lvls-mono (suc D) (suc D) 2≤S ≤-refl ≤-refl hLv ≤-refl)
                       (ent-step c d J g i D 2≤S
                          (chain-deliv-cap sl id a nextId path sched st′ Lv J g i
                             sleq hgn cok
                             (pathSz?-widen path (proj₁ c⊑) (proj₁ (∧-true _ _ hpz)))
                             HVC
                             (lub3-m (depthCascade a nextId chains sched st)
                                     (depthChain nextId a path sched st′)
                                     (depthCascade a nextId chains
                                        (proj₁ (proj₂ (chainStep nextId a path sched st′)))
                                        (proj₂ (proj₂ (chainStep nextId a path sched st′)))) hdp)
                             hLv))
        REC  = ≤-trans (lvls-mono R R 2≤S ≤-refl ≤-refl (proj₁ (proj₂ ST)) ≤-refl)
                 (≤-trans (≤-reflexive (sym (lvls-add S W d Lv (suc D) R))) hlvC)

arr-chains-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc))
      (chainsOf a st) ≡ true →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  nestClosOK?ᵛ (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st) ≤ capsH e sl id →
  chainsCapsOK (capsAt e sl id) (capsAt e sl (suc id)) sl (capsH e sl id) 0 a nextId (chainsOf a st) sched
    (cascadeLatch a st)
arr-chains-caps {e = e} sl id a nextId sched st sleq cok hpz hvc hcl hdp =
  arr-chains-caps-go sl id 0 a nextId (chainsOf a st) sched (cascadeLatch a st)
    sleq ENTRY
    (subst (λ x → capsOK? x sched (cascadeLatch a st) ≡ true)
           (sym (frameStep-0 (capsAt e sl id))) LATCH)
    hpz hvc hcl hdp
    0 (Caps.cSize (capsAt e sl id)) 0
    (capsAt-round-size e sl id) base REGLEN ≤-refl
  where
  c   = capsAt e sl id
  LATCH = cascadeLatch-caps (capsAt e sl id) a sched st cok
  d   = capsH e sl id
  2≤S = 2≤capsAt-size e sl id
  slSz : slotsSize sl ≤ Caps.cSize c
  slSz = ≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e)) (capsAt-base-size e sl id)
  -- the round has as many positions as the registry has entries, and
  -- the cascade walks a sublist of it
  REGLEN : 0 + length (chainsOf a st) ≤ regAt (Caps.cSize c) (Caps.cReg c) 0
  REGLEN = ≤-trans (≤-trans (chainsOf-length a st)
                            (capsOK?-count c sched st cok))
                   (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))
  -- the cascade's own delivery total, which is what the fold's
  -- invariant is stated over
  DEL = cascadeGo-deliveries
          (λ {n′} {Γ′} {t′} {e′} {u′} → subscribeInner-caps {n′} {Γ′} {t′} {e′} {u′})
          (λ {n′} {Γ′} {t′} {e′} {s′} → innerFinish-caps {n′} {Γ′} {t′} {e′} {s′})
          c d a nextId (chainsOf a st) sl sched (cascadeLatch a st)
          2≤S (1≤capsAt-reg e sl id) (slotsCaps?-capsAt e sl id) sleq
          (cascadeLatch-caps c a sched st cok) hvc hpz (n≤capsAt-size e sl id)
          (subst (length (chainsOf a st) ≤_) (realWidAt-def e sl id)
                 (chains-count-width sl id a sched st cok))
          slSz hdp
  ENTRY = ≤-trans (lvls-mono (delivN (cascadeLatch a st)
                                (proj₂ (proj₂ (cascadeGo a nextId (chainsOf a st) sched
                                                 (cascadeLatch a st)))))
                             (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl DEL)
                  (≤-trans (≤-reflexive (sym (sizeCount-body c d)))
                           (m≤m⊔n (sizeCount c d) (Caps.cSize c)))

-- ONE ROUND'S DESCENT AGAINST WHAT THE ROUND CAN SEE.  A cascade
-- descends by crossing `thru-outer` frames and by draining a bounded
-- mergeAll, and both crossings are paid for out of structure that is
-- already present when the round starts: the payload it carries, the
-- store it walks, and the program's own wrap unit.  `sightCeil` is
-- that sum scaled by the program's size.
--
-- WHY THE SCALING IS THE WHOLE CONTENT.  Edge by edge a descent
-- TRADES: what a frame takes off the subject it puts on the path, so
-- the bare sum is an equality along the subscribe walk.  The drain is
-- the one level with no edge to come out of -- it runs under a
-- `from-inner`, which the path measure charges nothing for -- and a
-- program whose folds nest spends one per layer.  So the gap grows
-- with a program parameter the sum does not see.
--
-- AND THE SEEN PARAMETER IS A SIZE, WHICH IS WHY THE SUMMANDS COULD
-- NOT BE MADE BIGGER.  All three of them are NESTING depths, so none
-- moves with how many values an instant carries: at two programs
-- differing only in the delivered count, every quantity this statement
-- reads is identical while the descent moves by a third.  The size is
-- the only sighted thing that separates them, and it enters as a
-- FACTOR because as a summand it is outrun -- one per delivered value
-- against the descent's eight.
--
-- AND THE STORE SLOT IS THE CAP, NOT THE READING, WHICH IS WHAT MAKES
-- THE ROUND INDUCIBLE.  A round states its ceiling once and spends it
-- at every chain, and the chains after the first run on states their
-- predecessors moved -- so the slot has to hold across the walk.  The
-- reading does not: a chain subscribes what its delivery reaches and
-- installs the nodes for it, and both the live fold and the node fold
-- are places the measure reads.  The CAP does, and it costs the
-- consumer nothing, because the arithmetic below already collapses all
-- three of the ceiling's summands to that same cap.
--
-- REFUTED: `Refuted.Chain-Step-Store` is why the reading could not be
--   carried -- nine before one chain and sixteen after, at the instant
--   the round's own rows are read at, with two further families in the
--   same corpus growing at the same instant.  What died is the plan to
--   thread the entry store across the chains; the growth has to be
--   priced, and pricing it against the cap is what the leaves below do.
-- DEAD ROUTE: descending into `depthE` and spending `depthE-sighted`
--   cannot close this.  That ceiling carries the FOLD's grant in its
--   subject place -- a tower over the payload -- where this one
--   carries the arrival's own nesting, and two upper bounds stated in
--   different currencies do not compose.  The delivery side needs its
--   own value-nesting walk, which is what the leaf below states.
-- REFUTED: `Refuted.Cascade-Deliv-Depth` is the delivery-side witness
--   the ceiling is calibrated against -- a limit-one mergeAll over
--   three inners, read at the second cascade, whose descent climbs six
--   per fold layer against the bare sum's four.
-- PROBED: `Probed.Depth-Sighted` reads this side at the second cascade
--   along both axes -- fold depths two and eight, delivered counts two,
--   six and twenty -- and at the width family that drains nothing.
--   Those rows are what killed the two cheaper shapes: a bare factor of
--   two fails forty-nine against forty-four, and a size SUMMAND fails
--   one hundred and ninety-three against one hundred and fourteen at
--   the far end of the count axis.  A THIRD cascade is reached too, on
--   one family at fold depths two and eight, and the ceiling holds
--   there with room -- fifteen against three hundred and forty-eight,
--   fifty-seven against one thousand five hundred and ninety.  Not
--   covered: the premises, which do not compute; any instant past the
--   third; and the count axis at the third, which is one family only.
--   The DOUBLING family is covered and is the one axis that turns out
--   not to be one: a step naming its accumulator in both additive
--   slots an inner `scanᵉ` offers -- the family that kills the entry
--   fold's width-free grant -- leaves the descent at TWO across the
--   second instant, the third, and twice the script length, while the
--   ceiling moves eighty-four to ninety-eight.  What that family grows
--   is a SUM over an instant's emitted values and a descent is a JOIN
--   over them, so it cannot reach this side.
--   Every row reads the whole ROUND rather than one chain, and the
--   round's descent is the JOIN over its chains, so a green row is a
--   green row for each chain it contains.  Every row is taken at the
--   entry store itself, which is the statement's own store slot
--   instantiated at the tightest value its hypothesis admits.
postulate
  chain-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (a : Arrival Γ) (nextId : Id) (S : ℕ)
    (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    storeNestMax sched st ≤ S →
    depthChain nextId a path sched st
      ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)

-- AND THE BOUND SURVIVES A CHAIN, which is the other half of the same
-- design: the round states its ceiling once and spends it at every
-- later chain, so what a chain may do to the store is exactly what the
-- bound has to absorb.
--
-- AND IT IS NOT A COROLLARY OF THE GROWTH BOUND THIS TREE ALREADY HAS,
-- WHICH IS THE WHOLE OF WHY IT IS A LEAF.  The walk's own store bound
-- lands at the SUCCESSOR cap -- a factor times the cap plus an
-- increment, which is by definition the next instant's -- and the tick
-- statement above it spends exactly that to close an instant.  So the
-- discipline says a round STARTS under its own cap and ENDS under the
-- next one, and says nothing about the states between.  What this leaf
-- claims is that the growth an instant actually performs stays under
-- the instant's own cap, which is the design's intent and is not
-- anywhere derived.  Neither side of it can be instantiated: the cap
-- sits on the caps recurrence, which does not terminate even natively.
-- AND THE STORE IS FOUR PLACES UNDER ONE `⊔`, SO THIS SPLITS FOUR WAYS
-- RATHER THAN INDUCTING ONCE, which is the same split the round's
-- growth statement takes and for the same reason: the four arms are
-- nowhere near equally hard.  The slot arm needs no leaf at all -- a
-- chain threads the vocabulary untouched, so its sum is the one the
-- entry cap already covers -- and the three that survive are each a
-- statement about one thing a delivery writes.
-- THE THREE ARMS PRICE THE GROWTH AGAINST THE PROGRAM AND NOT AGAINST
-- THE STORE THEY START FROM, and that shape is forced rather than
-- chosen.  A growth priced against the entry store COMPOUNDS: each
-- chain's bound is the previous chain's, so no ceiling stated once
-- survives a walk of unknown length.  Charging the increment instead
-- makes preservation a condition on the BOUND -- it holds as soon as
-- the bound already covers one instant's increment -- which is a
-- condition the round discharges once, at its entry, rather than a
-- condition the walk has to re-establish per chain.
--
-- AND THE CHARGE IS THE SAME ONE THE FIRST SUBSCRIPTION PAYS.  The
-- floor rows for a program's own subscribe frame are stated at exactly
-- this quantity, so the three arms are that statement moved from the
-- opening frame to an arbitrary chain, and the two are refutable
-- together at any program where a chain outgrows a first subscription.
--
-- THE UNCONDITIONAL GROWTH BOUND BESIDE THEM CANNOT SUPPLY IT, AND
-- THAT IS WORTH KNOWING BEFORE ANYONE TRIES.  Two of that bound's
-- three disjuncts are places the store measure reads, so the entry
-- bound covers them outright; the third is the chain's own PATH factor
-- times the arrival's size, and the path factor is a PRODUCT over the
-- path's frames while the increment is linear in the caps at the
-- instant.  The product outruns it, and no premise the round can
-- supply changes that -- a legal path of length the size cap already
-- carries a factor exponential in that cap.

-- AND THE CHARGE MAY NOT BE DEPTH-DENOMINATED, WHICH IS WHY IT IS THE
-- INCREMENT AND NOT SOMETHING SMALLER.  The cheap repair replaces the
-- path PRODUCT by the path's additive depth, which holds at every
-- family the corpus reaches -- exactly, four against four, at the
-- transforming frame.  It fails one step further along that same
-- family: both nesting-depth measures read ZERO into a `deferᵉ` body,
-- so a `map-f` whose function is a deferred constant hands the frame a
-- value as deep as the constant while the charge does not move at all.
-- Whatever pays for these arms has to see inside a deferred body, and
-- only a SIZE measure does -- which the size cap carries and no
-- depth-built quantity does.
--
-- AND THE SIZE CAP IS THE LARGEST CHARGE THE FUEL CAN AFFORD, WHICH IS
-- WHY IT IS THAT AND NOT THE INSTANT'S INCREMENT.  A bound covering
-- one chain's growth is not the cap, so the round's ceiling reads the
-- cap PLUS the charge and each half is priced by its own copy of the
-- exponential -- and the fuel carries exactly two.  The size cap fits
-- under one with room, being a quadratic under a double exponential of
-- itself.  Everything about this is index-aligned by construction: the
-- exponential room this face runs on prices no summand at the cap
-- after the one being bounded, so a charge naming the next instant is
-- unaffordable however true it is, and reading the ceiling at the
-- SUCCESSOR cap instead is dead for the same reason.
--
-- AND THE PATH PREMISE IS NOT A CONVENIENCE.  A charge naming the
-- program alone cannot hold against a path built by hand: the path is
-- universally quantified, a frame carries its own function, and a
-- frame whose function wraps twenty times installs a node twenty deep
-- against a program that never mentions it.  So the unconditional form
-- is FALSE and the conditioned one replaces it rather than weakening
-- it.  The premise costs the consumer nothing -- the walk's own caller
-- derives it from the caps invariant it already holds, one
-- application, so it is a fact the round has rather than a fact the
-- round must acquire.
--

-- AND THIS ONE CARRIES THE CHAIN'S OWN DEPTH, which the two arms above
-- do not.  A registration this chain mints sits at the frames of the
-- subscribed value over the REMAINING path, so its depth is the
-- arrival's nesting plus the path's -- and neither of the other
-- premises reaches that quantity: the size premise is about the
-- payload's syntax and `pathSz?` bounds each frame's SIZE and the
-- path's LENGTH, which together allow a nesting quadratic in the cap.
-- The premise is the tree's own cascade-level reading taken one chain
-- at a time, so it is derived where the arm is spent rather than
-- assumed: the selection comes from the registry, and the registry's
-- join is already under the unit there.
--
-- THE BODY IS THE WALK, and the charge it spends is the unit under the
-- path's own FACTOR.  Substitution is multiplicative in this currency,
-- so a walk that survives a map frame carries the factor the frames can
-- still apply -- and the size premise is what bounds it without reading
-- the run: each frame's size is under the cap and the path's length is
-- too, so the factor is two to the cap SQUARED and no more.
-- THE PATH'S OWN DEPTH ONLY GROWS ROOTWARD, which is what lets a
-- premise taken at the chain's entry be spent at every frame the walk
-- reaches: four clauses add a term's depth or nothing, and the outer
-- frame adds one.
