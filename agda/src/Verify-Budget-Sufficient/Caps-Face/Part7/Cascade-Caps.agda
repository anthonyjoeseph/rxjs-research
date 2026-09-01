-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps
-- walkH … cascadeGo-slots
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps where

open import Data.Bool    using (true; false; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _⊔_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≤1+n; *-identityʳ)
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
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted)
open import Rx.Exp       using (obs; _≟ᵗ_; Ctx; Closed; Val; sizeᵛ)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade)
open import Verify-Budget-Sufficient.Nest-Store using
  (pathNestF; slotsNestSum; liveNest)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; Chain; lookupNode; NodeId; AllOp; cascadeLatch;
  cascadeFinish; arrSource; chainsOf; chainsGo; cascadeGo; Path; arrTy; stepFrame;
  subscribeInner; innerFinish; sameSource; regAt; fLvlD; lvls; sLvlD; chainStep; budgetAt;
  arrTick)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk using
  (module Walk; Walk-Hyps)
open import Verify-Budget-Sufficient.Deliveries using
  (delivN)
open import Verify-Budget-Sufficient.Caps using
  (Caps; cDel; cDel-body; dWalkᶜ-mono; frameStep; frameStep-0; frameStep-mono-j; lvls-mono;
  sizeCount; sizeCount-body)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFin; depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; eventCaps?; pathSz?; pathSz?-widen; regsSz?; slotsCaps?; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-regs; dropSweep-caps; frameBud;
  pathSz?-len; pathSz?-tail; shareLatch-caps; valsCaps?; valsCaps?-lvl; walkOK; walkOK-finish)
open import Decide using (∧-intro)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Frame-Face using
  (stepFrame-face)

-- `.Delivery-Walk` MAPS THE DELIVERY CLIQUE ONTO THE LEVEL WALK --
-- foldPath ↦ dCapᶜ, dispatchShare ↦ dCapᶜ, shareGo ↦ dWalkᶜ, cascadeGo
-- ↦ dWalkᶜ -- RELATIVE to one frame's face at the level it RUNS at,
-- which it takes as a record of hypotheses rather than postulating.
-- `walkH` is that record instantiated at the caps face below, and
-- `cascadeGo-deliveries` is the theorem it buys.  `delivN`, from
-- `.Deliveries`, is the currency the cascade conjuncts are stated in.
walkH :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    frameBud c j ≤ bud →
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Caps) (d : ℕ) (sl : Slots Γ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  Walk-Hyps e (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
walkH siC ifc c d sl 2≤S 1≤R slC slSz = record
  { OK        = walkOK c sl
  ; Pb        = λ J p → pathSz? (Caps.cSize (frameStep J c)) p
  ; Vb        = λ J vs → valsCaps? (frameStep J c) sl vs
  -- TRIVIAL BURST INSTANTIATION: Eb and Bb are always true, so every
  -- closure fact is refl and Res.burst is never projected by callers.
  -- GAS-BLIND: the caps axis carries no fuel content, so GOK is ⊤;
  -- CEILING-BLIND for the same reason, so CL is ⊤
  ; GOK       = λ _ _ → ⊤
  ; g-mint    = λ _ _ _ _ _ → tt
  ; CL        = λ _ _ → ⊤
  ; cl-anti   = λ _ _ _ → tt
  ; Eb        = λ _ _ → true
  ; Bb        = λ _ _ → true
  ; e-nil     = λ _ → refl
  ; e-close   = λ _ _ → refl
  ; e-app     = λ _ _ _ _ _ → refl
  ; e-widen   = λ _ _ _ → refl
  ; b-nil     = λ _ → refl
  ; b-app     = λ _ _ _ _ _ → refl
  ; b-widen   = λ _ _ _ → refl
  ; b-deliv   = λ _ _ _ _ _ _ _ _ → refl
  ; b-handoff = λ _ _ _ _ _ _ → refl
  ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p h
  ; p-tail    = λ J f p h → pathSz?-tail (Caps.cSize (frameStep J c)) f p h
  ; p-widen   = λ le p h → pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le)) h
  ; v-widen   = λ le vs h → valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le) h
  ; ok-reg    = λ J sched st ok → capsOK?-count (frameStep J c) sched st (proj₂ ok)
  ; ok-cons   = λ J rid sched st ok →
                  proj₁ ok , capsOK?-delivered (frameStep J c) rid sched st (proj₂ ok)
  ; ok-latch  = λ J i fin sched st ok →
                  proj₁ ok , shareLatch-caps (frameStep J c) i fin sched st (proj₂ ok)
  ; ok-finish = λ J i fin out ok → walkOK-finish c sl J i fin out ok
  ; sf-step   = λ J sf id now f path′ vals fin sched st ok hP hV hL _ _ hD →
                  let r  = stepFrame sf id now f path′ vals fin sched st
                      FC = stepFrame-face siC ifc c d J sl sf id now f path′ vals fin sched st
                             2≤S 1≤R (proj₁ ok) slC (proj₂ ok) hP hV slSz hD in
                  proj₁ FC
                  , proj₁ (proj₂ FC)
                  , ( trans (KeepsC.slotsEq
                               (stepFrame-keeps sf id now f path′ vals fin sched st))
                            (proj₁ ok)
                    , proj₁ (proj₂ (proj₂ FC)) )
                  , proj₁ (proj₂ (proj₂ (proj₂ FC)))
                  , capsOK?-regs (frameStep (J + proj₁ FC) c)
                      (proj₁ (proj₂ (proj₂ (proj₂ r))))
                      (proj₂ (proj₂ (proj₂ (proj₂ r))))
                      (proj₁ (proj₂ (proj₂ FC)))
                  , refl
  }

-- and the bound itself: the walk at level 0, then three widenings — the
-- dispatch gas to cDel's index (n ≤ cSize), the walk length to the
-- registry cap (length chains ≤ cReg), and dCapᶜ's own unfolding, which
-- is what `cDel` abbreviates
cascadeGo-deliveries :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    frameBud c j ≤ bud →
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  -- the walk's two new obligations, sourced one level up at `caps-tick`
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
    ≤ cDel c d
cascadeGo-deliveries siC ifc {n = n} {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD =
  ≤-trans (W.Res.cnt (W.cascadeGo-go 0 a id chains sched st
             ((slEq , invʲ) , capsOK?-regs c sched st inv)
             pS (∧-intro (∧-intro vC refl) refl) tt hD))
    (≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                (regAt (Caps.cSize c) (Caps.cReg c) 0)
                2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
             (≤-reflexive (sym (cDel-body c d))))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH siC ifc c d sl 2≤S 1≤R slC slSz)

------------------------------------------------------------------
-- THE CHARGE, IN THE CURRENCY THE WALK ACTUALLY PROVES — and the
-- currency the caps recurrence now SPENDS, so the charge is a theorem.
--
-- `Res.hi` says the level a cascade lands at is at most `lvls S W 0 D`,
-- which ITERATES `dLvl` once per delivery, and `dLvl` in turn iterates
-- `fLvl` once per frame.  The product this replaces
-- (`D * cSize * suc (suc cWid * suc cSize)`, whose right-hand factor is
-- `fCharge S W 0`, ONE FRAME'S RECEIPT READ AT LEVEL 0) charges every
-- delivery's frames at the level the CASCADE entered at; the iteration
-- charges each at the level the one before it LEFT.  That is the same
-- distinction entry-charging was refuted on one stratum down
-- (machine-refuted: a frame's own output breaches
-- the cap it was charged at), which is why the walk was rebuilt around
-- levels in the first place — and why the count the recurrence spends
-- was rebuilt around them too.
--
-- NOTHING IS LOST BY THE MOVE.  The product is DOMINATED by the
-- iteration — a linearity step at J = 0 gives `D * chargeAt S W 0` under
-- `lvls S W 0 D`, and `chargeAt S W 0` IS `cSize * fCharge S W 0`
-- (measured by a probe module since DELETED) — so every Instant-Height row the
-- product cleared this clears, with the same margin or more, and no
-- measurement is re-run.  `sizeCount` (.Caps) is now this level, its
-- pooled twin `poolBody` (Rx.Evaluator) the same level with every field
-- pooled, and `blowup-tower`'s count axis is `lvls-mono` where it was a
-- product of monotonicities
------------------------------------------------------------------

cascadeGo-level :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    frameBud c j ≤ bud →
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j →
     (j ≤ lvls (Caps.cSize c) (Caps.cWid c) d 0
             (delivN st (proj₂ (proj₂ r))))
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-level siC ifc {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD =
  W.Res.lvl GO , W.Res.hi GO , proj₂ (proj₁ (W.Res.good GO))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH siC ifc c d sl 2≤S 1≤R slC slSz)
  GO = W.cascadeGo-go 0 a id chains sched st
         ((slEq , invʲ) , capsOK?-regs c sched st inv)
         pS (∧-intro (∧-intro vC refl) refl) tt hD

-- and the assembly declared above: the landing level with the delivery
-- count widened to its own recursion, which is `sizeCount` by definition
-- THE ASSEMBLY, ground: the level the walk lands at, with the delivery
-- count widened to its own recursion.  Both pieces are theorems, so
-- this one is (the body is at the end of the next section, where
-- cascadeGo-level is)
cascadeGo-caps :
  (∀ {n′} {Γ′ : Ctx n′} {t′} {e′ : Closed Γ′ t′} {u′}
    (c′ : Caps) (dep bud j′ : ℕ) (g′ : Gas) (op′ : AllOp) (allNid′ : NodeId)
    (κ′ : Path Γ′ u′ t′) (id′ : Id) (now′ : Tick) (o′ : Val Γ′ (obs u′))
    (sl′ : Slots Γ′) (sched′ : Sched Γ′) (st′ : EvalSt e′) →
    2 ≤ Caps.cSize c′ →
    1 ≤ Caps.cReg c′ →
    Sched.slots sched′ ≡ sl′ →
    slotsCaps? (Caps.cSize c′) (Caps.cWid c′) sl′ ≡ true →
    slotsSize sl′ ≤ Caps.cSize c′ →
    capsOK? (frameStep j′ c′) sched′ st′ ≡ true →
    valCaps? (frameStep j′ c′) sl′ (obs u′) o′ ≡ true →
    pathSz? (Caps.cSize (frameStep j′ c′)) κ′ ≡ true →
    suc (pathLen κ′) ≤ Caps.cSize (frameStep j′ c′) →
    nest o′ sl′ (EvalSt.connectedShares st′) ≤ bud →
    depthInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′ ≤ dep →
    let r′ = subscribeInner g′ op′ allNid′ κ′ id′ now′ o′ sched′ st′
    in Σ ℕ λ j₂ →
       (capsOK? (frameStep (j′ + j₂) c′)
                (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r′)))))
                (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r′))))) ≡ true)
       × (valsCaps? (frameStep (j′ + j₂) c′) sl′ (proj₁ (proj₂ r′)) ≡ true)
       × (all (eventCaps? (frameStep (j′ + j₂) c′) sl′)
              (proj₁ (proj₂ (proj₂ r′))) ≡ true)
       × (suc (j′ + j₂) ≤ sLvlD (Caps.cSize c′) (Caps.cWid c′) dep (suc bud) (suc j′))
   ) →
  -- ifc  (innerFinish-caps, .Subscribe-Face)
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (dep bud j : ℕ) (g : Gas) (op : AllOp) (allNid inst : NodeId)
    (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
    (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
    2 ≤ Caps.cSize c →
    1 ≤ Caps.cReg c →
    Sched.slots sched ≡ sl →
    slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
    slotsSize sl ≤ Caps.cSize c →
    capsOK? (frameStep j c) sched st ≡ true →
    pathSz? (Caps.cSize (frameStep j c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep j c) →
    valsCaps? (frameStep j c) sl vals ≡ true →
    frameBud c j ≤ bud →
    depthFin g op allNid inst κ id now vals sched st
      (lookupNode allNid (EvalSt.nodes st)) ≤ dep →
    let r = innerFinish g op allNid inst κ id now vals sched st
              (lookupNode allNid (EvalSt.nodes st))
    in Σ ℕ λ j′ →
       (capsOK? (frameStep (j + j′) c)
                (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
                  ≡ true)
       × (valsCaps? (frameStep (j + j′) c) sl (proj₁ r) ≡ true)
       × (all (eventCaps? (frameStep (j + j′) c) sl)
              (proj₁ (proj₂ r)) ≡ true)
       × (suc (j + j′) ≤ fLvlD (Caps.cSize c) (Caps.cWid c) dep j)) →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (d : ℕ) (a : Arrival Γ) (id : Id)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  Sched.slots sched ≡ sl →
  capsOK? c sched st ≡ true →
  valCaps? c sl (arrTy a) (arrVal a) ≡ true →
  all (λ rc → pathSz? (Caps.cSize c) (proj₂ rc)) chains ≡ true →
  n ≤ Caps.cSize c →
  length chains ≤ Caps.cReg c →
  slotsSize sl ≤ Caps.cSize c →
  depthCascade a id chains sched st ≤ d →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j → (j ≤ sizeCount c d)
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-caps siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD =
  proj₁ LV
    , ≤-trans (≤-trans (proj₁ (proj₂ LV))
                       (lvls-mono D (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl
                          (cascadeGo-deliveries siC ifc c d a id chains sl sched st
                             2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD)))
              (≤-reflexive (sym (sizeCount-body c d)))
    , proj₂ (proj₂ LV)
  where
  D  = delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
  LV = cascadeGo-level siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD

------------------------------------------------------------------
-- THE CASCADE BOOKENDS AND THE CHAIN SNAPSHOT, ground.  Nothing here
-- is a caps argument: latching resets per-cascade scratch capsOK? does
-- not read, finishing is the same drop-and-sweep the share's finish is,
-- and the snapshot is a filter of the registry.
------------------------------------------------------------------

-- the latch resets delivered/cancelled/regWatermark/dying and may add
-- to completedSources — none of the five conjuncts sees any of them
cascadeLatch-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  capsOK? c sched (cascadeLatch a st) ≡ true
cascadeLatch-caps c a sched st h with Arrival.isLast a
... | true  = h
... | false = h

cascadeFinish-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? c sched st ≡ true →
  let r = cascadeFinish a sched st
  in capsOK? c (proj₁ r) (proj₂ r) ≡ true
cascadeFinish-caps c a sched st h with Arrival.isLast a
... | false = h
... | true  = dropSweep-caps c (arrSource a) sched st h

-- the snapshot is chainsGo's filter: source matches and the chain's
-- element type is the arrival's.  Same shape as shareAdmit's
chainsGo-caps : ∀ {n} {Γ : Ctx n} {t} (B : ℕ) (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  regsSz? B rs ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsGo a rs) ≡ true
chainsGo-caps B a [] h = refl
chainsGo-caps B a ((rid , s , (u , p)) ∷ r) h
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | no  _    = chainsGo-caps B a r (proj₂ (∧-true _ _ h))
... | true  | yes refl = ∧-intro (proj₁ (∧-true _ _ h))
                                 (chainsGo-caps B a r (proj₂ (∧-true _ _ h)))

chainsOf-caps : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
  regsSz? B (EvalSt.registry st) ≡ true →
  all (λ rc → pathSz? B (proj₂ rc)) (chainsOf a st) ≡ true
chainsOf-caps B a st = chainsGo-caps B a (EvalSt.registry st)

chainsGo-length : ∀ {n} {Γ : Ctx n} {t} (a : Arrival Γ)
  (rs : List (RegId × Source × Chain Γ t)) →
  length (chainsGo a rs) ≤ length rs
chainsGo-length a [] = z≤n
chainsGo-length a ((rid , s , (u , p)) ∷ r)
  with sameSource (arrSource a) s | u ≟ᵗ arrTy a
... | false | _        = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | no  _    = ≤-trans (chainsGo-length a r) (n≤1+n _)
... | true  | yes refl = s≤s (chainsGo-length a r)

chainsOf-length : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  length (chainsOf a st) ≤ length (EvalSt.registry st)
chainsOf-length a st = chainsGo-length a (EvalSt.registry st)

-- THE SLOT STORE SURVIVES A CHAIN STEP, one call into `foldPath` and so
-- one composition of `foldPath-slots`.
chainStep-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (chainStep id a path sched st))) ≡ Sched.slots sched
chainStep-slots {n = n} {e = e} id a path sched st =
  foldPath-slots (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a) path (arrVal a ∷ [])
                 (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
                 (Arrival.isLast a) sched st


-- AND SURVIVES THE WHOLE CHAIN FOLD, by the obvious induction over the
-- list: the cancelled arm changes nothing and the live arm composes the
-- step above with the tail.  It is one of the four components the
-- store's nesting is a `⊔` of, and the only one that needs no width at
-- all -- the slot store is threaded through the fold untouched, so its
-- nesting is not merely bounded but EQUAL.
cascadeGo-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (chains : List (RegId × Path Γ (arrTy a) t))
  (sched₀ : Sched Γ) (st₀ : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (cascadeGo a id chains sched₀ st₀))) ≡ Sched.slots sched₀
cascadeGo-slots a id [] sched₀ st₀ = refl
cascadeGo-slots a id ((rid , c) ∷ chains) sched₀ st₀
  with any (_≡ᵇ rid) (EvalSt.cancelled st₀)
... | true = cascadeGo-slots a id chains sched₀ st₀
... | false =
      let (emits , sched₁ , st₁) =
            chainStep id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ })
      in trans (cascadeGo-slots a id chains sched₁ st₁)
               (chainStep-slots id a c sched₀ (record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }))


-- AND NO CONSTANT MULTIPLE OF THE SYNTACTIC CEILING CAN WORK, BECAUSE
-- THE DESCENT IS A PRODUCT AND EVERY NARROW TERM IS A SUM.  That is
-- the difference between a width factor that is merely safe and one
-- that is structural.  The two refutations below kill one narrow
-- reading each, and either could be read as an off-by-a-constant that
-- a larger constant would fix.  It is not one.  `Harness.Main`'s
-- SERIES X decomposes the crossing instant and drives its two axes
-- INDEPENDENTLY (measured-not-rechecked, so it discharges nothing):
-- over a grid of fold depth `w` against source length `k` the descent
-- is `w * (k + 4) + 1` throughout, so the slope down the source axis
-- IS the fold depth.  `nestSyn`, `chainsNestD` and `storeNestMax` each
-- move with `w` alone and with `k` not at all, so no multiple of them
-- tracks a term in `w * k` however large it is taken.  `realWidAt` is
-- the one term in this vocabulary that moves with BOTH axes, which is
-- what makes `realWidAt * nestSyn` a product rather than a generous
-- constant, and why the width form clears every row the narrow ones
-- cross on.

-- AND THE CHAIN COUNT AND THE REGISTRY ARE FLAT ACROSS THAT WHOLE
-- GRID, both reading ONE at every cell, which is what says where the
-- growth is NOT.  It is not a longer selection for the cascade to fold
-- over, and it is not registrations accumulating as the fold threads
-- its state -- the two readings the shape of the recursion invites,
-- since both folds in this family carry their tail at the state the
-- head left.  What is left is the bounded limit's drain, which is
-- where all three refutations in this face already pointed.  The
-- positive mechanism is not read off this grid and is not claimed
-- here.

-- THE PENDING-SOURCE COMPONENT, which is where this statement is
-- FALSE.  A live source carries the values an emit has queued but not
-- yet dispatched, so a walk can leave one holding a value nested deeper
-- than anything the store held before.  It does, and the constructor
-- that does it is `deferᵉ`: its subscribe clause mints a live source of
-- its own with `elemTy = obs u` and the deferred BODY as the pending
-- payload, so `liveNest` reads the body's full depth.
--
-- AND THE ARGUMENT THAT SAID OTHERWISE WAS STRUCTURAL, WHICH IS WHY IT
-- HELD FOR SO LONG.  A live minted at a SCRIPTED slot takes its element
-- type from that slot, and `Slot`'s scripted constructor carries an
-- `isData` side condition that is false at every observable type -- so
-- no slot-minted live can carry an observable, and every family the
-- harness drives reads this component as zero.  All of that is true.
-- It is not exhaustive: the slot is one of TWO mint sites, and the
-- other one never meets `isData`.
--
-- THE OBVIOUS REPAIR IS ALSO DEAD, and it is dead for a reason worth
-- carrying rather than rediscovering.  Charging the ARRIVAL's payload
-- cannot cover the new live, because the payload IS the `deferᵉ` term
-- and `nestDᵉ` is zero there by design -- a deferred body is not
-- entered synchronously, so the synchronous measure declines to look
-- inside it.  The measure's zero and the store's content therefore
-- disagree at exactly one constructor, and every quantity built over
-- `nestDᵉ` -- the unit, the syntactic ceiling -- inherits the blindness.
-- What a repair must find is a term that sees a deferred body, and
-- `sizeᵛ` is one: the sighted measure descends where the synchronous
-- one stops, so the charge is the arrival's SIZE rather than its
-- depth, taken once per chain the selection carries.  That currency
-- costs nothing above, because the caps already bound an arrival's
-- size -- it is `valCaps?`'s first conjunct, which the tick holds
-- already -- so the premise the restatement needs is discharged where
-- the cascade is entered and never reaches a caller.
--
-- AND THE FOLD ABOVE IT IS THREADED IN THE LIVE COMPONENT'S OWN
-- CURRENCY, not in the store's, because the store is the one thing the
-- induction cannot carry: a walk GROWS the node table, so an inductive
-- step landing at `storeNestMax` of the state it produced could never
-- be brought back to the state it started from.  What does thread is
-- the pair the live component can actually reach -- the lives already
-- there, and the slots, which `cascadeGo-slots` proves the fold leaves
-- untouched.  The statement the caller wants follows because both are
-- summands of the same `⊔`.
--
-- THE SHAPE THAT COULD WORK IS THE μ STEP'S, NOT THE FRAME'S.  A μ
-- already jumps the level by a quadratic without paying an operator per
-- level, because its measure is RE-MINTED at the stepped level's size
-- cap rather than decremented.  A frame's sibling of that step is what
-- this leaf is waiting on, and it leaves the drain's conjunct
-- arithmetic — which is what kept the ceiling out of the types.
--
-- REFUTED: `Refuted.Chain-Step-Live-Nest`, three against one at a body
--   three layers deep and five against one at five, so the gap is
--   unbounded in the body's depth and no constant repairs it.
-- PROBED: `Probed.Chain-Step-Live-Nest` re-runs that same adversarial
--   family against THIS conclusion rather than a numeral standing in
--   for it.  Covered: the deferred-body rows the old form died on --
--   grown 3 against a charge of 16, grown 5 against 24 -- so the two
--   sides now move together where they used to diverge, and each is
--   pinned separately so a repair moving either fails naming a number.
--   Also covered, and it is the reason the file is not two rows: the
--   right side carries NO store term, so a step minting a live out of
--   a PARKED value would exceed it with the arrival left shallow.  The
--   attack is armed -- a limited merge whose first inner is a `deferᵉ`
--   leaves the second genuinely pending, and the node reads depth 2
--   and 4 -- and the grown fold stays at zero, so the drain does not
--   run inside a step and the missing store term is not owed here.
--   And the tight direction on the path: `frameNestF` is one at every
--   frame but `map-f`/`scan-f`, so two merge frames give the step a
--   second mint site while leaving the charge exactly where the
--   one-frame rows left it -- grown 3 against 19, grown 5 against 27.
--   And a `map-f`, the only frame that both exceeds a factor of one
--   and hands the step a value the ARRIVAL never carried: a constant
--   deferred body two and four deep, against a shallow arrival, mints
--   at the body's depth and the factor pays for it.  The constant must
--   be DEFERRED or the row cannot fail -- a plain deep observable
--   finishes inside the step and the grown fold stays at zero.
--   NOT covered: a share sink, whose mint site no row here reaches.
postulate
  chainStep-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e) →
    let r = chainStep id a path sched st
    in foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ r)))
         ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
           ⊔ slotsNestSum (Sched.slots sched)
           ⊔ pathNestF path * sizeᵛ (arrTy a) (arrVal a)
