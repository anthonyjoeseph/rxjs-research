-- Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps
-- walkH … cascadeGo-slots
module Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps where

open import Data.Bool    using (true; false; _∧_; if_then_else_)
open import Data.Nat     using (ℕ; suc; _+_; _≤_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ≤-reflexive; n≤1+n; *-identityʳ)
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
open import Relation.Nullary using (yes; no)
open import Data.Vec     using (Vec; lookup) renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; subst)

open import Rx.Prim      using (Tick; Id; Source; _at_from_as_; Gas; after_,_; close; exhausted)
open import Rx.Exp       using (obs; _≟ᵗ_; Ctx; Closed; Val)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; Chain; lookupNode; NodeId; AllOp; cascadeLatch;
  cascadeFinish; arrSource; chainsOf; chainsGo; cascadeGo; Path; arrTy; stepFrame;
  subscribeInner; innerFinish; sameSource; regAt; fLvlD; lvls; sLvlD; chainStep; budgetAt;
  arrTick; shareAdmit; _↠_)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Delivery-Walk using
  (module Walk; Walk-Hyps; chP?; chP?-const; regP?)
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
  (capsOK?; eventCaps?; pathSz?; pathSz?-widen; regsSz?; slotsCaps?; valCaps?;
   pathFloor; pathStrat?; frameStrat?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (foldPath-slots; capsOK?-count; capsOK?-delivered; capsOK?-regs; dropSweep-caps; frameBud;
  pathSz?-len; pathSz?-tail; shareLatch-caps; valsCaps?; valsCaps?-lvl; walkOK; walkOK-finish;
  registry-entStrat; valsStrat?)
open import Verify-Budget-Sufficient.Psi-Split using
  (chP?-∧; regP?-∧; regStrat?-paths)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves using
  (shareAdmit-strat; stepFrame-valsStrat)
open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ)
open import Verify-Budget-Sufficient.Caps-Face.Part6 using
  (SiCType; IfcType)
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
  SiCType →
  IfcType →
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (c : Caps) (d : ℕ) (sl : Slots Γ) →
  2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  Walk-Hyps e (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d
walkH siC ifc c d sl 2≤S 1≤R slC slSz = record
  { OK        = walkOK c sl
  -- BOTH LEDGERS CARRY THE ENTRY READING BESIDE THE CAPS ONE, and the
  -- two halves are independent: a size bound does not move when the
  -- level does, and a stratification reading does not mention the level
  -- at all.  The payload half is the one that had to stop being
  -- PATH-BLIND — a value's floor is the floor of where it is GOING, so
  -- the fan is the step where the reading moves and the widenings are
  -- the steps where it cannot
  ; Pb        = λ J p → pathSz? (Caps.cSize (frameStep J c)) p ∧ pathStrat? p
  ; Vb        = λ p J vs → valsCaps? (frameStep J c) sl vs
                             ∧ valsStrat? (pathFloor p) vs
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
  ; p-len     = λ J p h → pathSz?-len (Caps.cSize (frameStep J c)) p (∧-trueˡ h)
  -- the cons of a path splits BOTH readings by the same ∧, and the
  -- strat half sheds the frame's own conjunct on the way
  ; p-tail    = λ J f p h →
                  ∧-intro (pathSz?-tail (Caps.cSize (frameStep J c)) f p (∧-trueˡ h))
                          (proj₂ (∧-true (frameStrat? (pathFloor p) f) (pathStrat? p)
                                    (proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (f ↠ p))
                                                   (pathStrat? (f ↠ p)) h))))
  ; p-widen   = λ le p h →
                  ∧-intro (pathSz?-widen p (proj₁ (frameStep-mono-j c 2≤S le)) (∧-trueˡ h))
                          (∧-trueʳ h)
  ; v-widen   = λ le _ vs h →
                  ∧-intro (valsCaps?-lvl _ _ sl vs (frameStep-mono-j c 2≤S le) (∧-trueˡ h))
                          (∧-trueʳ h)
  -- THE FAN IS WHERE THE READING MOVES: the caps half is constant in
  -- the chain, the strat half is not — every chain the share admits
  -- sinks at or above `i`, which is what the registry's own reading
  -- says and what `shareAdmit-strat` turns into the pointwise ledger
  ; v-fan     = λ J i vs sched st ok h →
                  chP?-∧ (λ _ → valsCaps? (frameStep J c) sl vs)
                         (λ κ → valsStrat? (pathFloor κ) vs)
                         (shareAdmit i (EvalSt.registry st))
                    (chP?-const (valsCaps? (frameStep J c) sl vs)
                       (shareAdmit i (EvalSt.registry st)) (∧-trueˡ h))
                    (proj₂ (shareAdmit-strat i vs st
                              (registry-entStrat (frameStep J c) sched st (proj₂ ok))
                              (∧-trueʳ h)))
  ; ok-reg    = λ J sched st ok → capsOK?-count (frameStep J c) sched st (proj₂ ok)
  ; ok-cons   = λ J rid sched st ok →
                  proj₁ ok , capsOK?-delivered (frameStep J c) rid sched st (proj₂ ok)
  ; ok-latch  = λ J i fin sched st ok →
                  proj₁ ok , shareLatch-caps (frameStep J c) i fin sched st (proj₂ ok)
  ; ok-finish = λ J i fin out ok → walkOK-finish c sl J i fin out ok
  -- THE FRAME, AND THE ONE PLACE THE PAYLOAD READING IS RE-ESTABLISHED
  -- RATHER THAN TRANSPORTED.  `stepFrame` rewrites the payload, so its
  -- floor is earned back from the frame's own conjunct of the path
  -- reading — which is the half `p-tail` throws away, spent here instead
  ; sf-step   = λ J sf id now f path′ vals fin sched st ok hP hV hL _ _ hD →
                  let r  = stepFrame sf id now f path′ vals fin sched st
                      hS = proj₂ (∧-true (pathSz? (Caps.cSize (frameStep J c)) (f ↠ path′))
                                         (pathStrat? (f ↠ path′)) hP)
                      hF = proj₁ (∧-true (frameStrat? (pathFloor path′) f)
                                         (pathStrat? path′) hS)
                      FC = stepFrame-face siC ifc c d J sl sf id now f path′ vals fin sched st
                             2≤S 1≤R (proj₁ ok) slC (proj₂ ok)
                             (∧-trueˡ hP) (∧-trueˡ hV) slSz hD
                             hS (∧-trueʳ hV) in
                  proj₁ FC
                  , proj₁ (proj₂ FC)
                  , ( trans (KeepsC.slotsEq
                               (stepFrame-keeps sf id now f path′ vals fin sched st))
                            (proj₁ ok)
                    , proj₁ (proj₂ (proj₂ FC)) )
                  , ∧-intro (proj₁ (proj₂ (proj₂ (proj₂ FC))))
                      (stepFrame-valsStrat sf id now f path′ vals fin sched st
                         hF (∧-trueʳ hV))
                  , regP?-∧ (pathSz? (Caps.cSize (frameStep (J + proj₁ FC) c)))
                      (λ {u} p → pathStrat? p)
                      (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                      (capsOK?-regs (frameStep (J + proj₁ FC) c)
                        (proj₁ (proj₂ (proj₂ (proj₂ r))))
                        (proj₂ (proj₂ (proj₂ (proj₂ r))))
                        (proj₁ (proj₂ (proj₂ FC))))
                      (regStrat?-paths
                        (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r)))))
                        (registry-entStrat (frameStep (J + proj₁ FC) c)
                           (proj₁ (proj₂ (proj₂ (proj₂ r))))
                           (proj₂ (proj₂ (proj₂ (proj₂ r))))
                           (proj₁ (proj₂ (proj₂ FC)))))
                  , refl
  }

-- and the bound itself: the walk at level 0, then three widenings — the
-- dispatch gas to cDel's index (n ≤ cSize), the walk length to the
-- registry cap (length chains ≤ cReg), and dCapᶜ's own unfolding, which
-- is what `cDel` abbreviates
cascadeGo-deliveries :
  SiCType →
  IfcType →
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
  -- THE ENTRY READING, PER CHAIN.  The walk's ledgers now carry a
  -- stratification half beside the size one, so the cascade's own
  -- entry point owes both: every chain the arrival is dispatched
  -- along is stratified, and the payload sits below that chain's
  -- floor.  The payload half is path-INDEXED, which is what lets the
  -- reading move at the fan and nowhere else
  chP? (λ {u} p → pathStrat? p) chains ≡ true →
  chP? (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains ≡ true →
  delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
    ≤ cDel c d
cascadeGo-deliveries siC ifc {n = n} {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD hpS hvS =
  ≤-trans (W.Res.cnt (W.cascadeGo-go 0 a id chains sched st
             ((slEq , invʲ) , regʲ)
             pS∧ vS∧ tt hD))
    (≤-trans (dWalkᶜ-mono n (Caps.cSize c) (length chains)
                (regAt (Caps.cSize c) (Caps.cReg c) 0)
                2≤S ≤-refl ≤-refl ≤-refl n≤S ≤-refl
                (≤-trans lenB (≤-reflexive (sym (*-identityʳ (Caps.cReg c))))))
             (≤-reflexive (sym (cDel-body c d))))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  regʲ = regP?-∧ (λ {u} p → pathSz? (Caps.cSize c) p)
                 (λ {u} p → pathStrat? p) (EvalSt.registry st)
           (capsOK?-regs c sched st inv)
           (regStrat?-paths (EvalSt.registry st)
              (registry-entStrat c sched st inv))
  pS∧ = chP?-∧ (λ {u} p → pathSz? (Caps.cSize c) p)
               (λ {u} p → pathStrat? p) chains pS hpS
  vS∧ = chP?-∧ (λ {u} _ → valsCaps? (frameStep 0 c) sl (arrVal a ∷ []))
               (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains
          (chP?-const (valsCaps? (frameStep 0 c) sl (arrVal a ∷ [])) chains
             (∧-intro (∧-intro vC refl) refl)) hvS
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
  SiCType →
  IfcType →
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
  -- THE ENTRY READING, PER CHAIN.  The walk's ledgers now carry a
  -- stratification half beside the size one, so the cascade's own
  -- entry point owes both: every chain the arrival is dispatched
  -- along is stratified, and the payload sits below that chain's
  -- floor.  The payload half is path-INDEXED, which is what lets the
  -- reading move at the fan and nowhere else
  chP? (λ {u} p → pathStrat? p) chains ≡ true →
  chP? (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j →
     (j ≤ lvls (Caps.cSize c) (Caps.cWid c) d 0
             (delivN st (proj₂ (proj₂ r))))
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-level siC ifc {e = e} c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD hpS hvS =
  W.Res.lvl GO , W.Res.hi GO , proj₂ (proj₁ (W.Res.good GO))
  where
  invʲ : capsOK? (frameStep 0 c) sched st ≡ true
  invʲ = subst (λ x → capsOK? x sched st ≡ true) (sym (frameStep-0 c)) inv
  regʲ = regP?-∧ (λ {u} p → pathSz? (Caps.cSize c) p)
                 (λ {u} p → pathStrat? p) (EvalSt.registry st)
           (capsOK?-regs c sched st inv)
           (regStrat?-paths (EvalSt.registry st)
              (registry-entStrat c sched st inv))
  pS∧ = chP?-∧ (λ {u} p → pathSz? (Caps.cSize c) p)
               (λ {u} p → pathStrat? p) chains pS hpS
  vS∧ = chP?-∧ (λ {u} _ → valsCaps? (frameStep 0 c) sl (arrVal a ∷ []))
               (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains
          (chP?-const (valsCaps? (frameStep 0 c) sl (arrVal a ∷ [])) chains
             (∧-intro (∧-intro vC refl) refl)) hvS
  module W = Walk {e = e} (Caps.cSize c) (Caps.cWid c) (Caps.cReg c) d 2≤S
                  (walkH siC ifc c d sl 2≤S 1≤R slC slSz)
  GO = W.cascadeGo-go 0 a id chains sched st
         ((slEq , invʲ) , regʲ)
         pS∧ vS∧ tt hD

-- and the assembly declared above: the landing level with the delivery
-- count widened to its own recursion, which is `sizeCount` by definition
-- THE ASSEMBLY, ground: the level the walk lands at, with the delivery
-- count widened to its own recursion.  Both pieces are theorems, so
-- this one is (the body is at the end of the next section, where
-- cascadeGo-level is)
cascadeGo-caps :
  SiCType →
  IfcType →
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
  -- THE ENTRY READING, PER CHAIN.  The walk's ledgers now carry a
  -- stratification half beside the size one, so the cascade's own
  -- entry point owes both: every chain the arrival is dispatched
  -- along is stratified, and the payload sits below that chain's
  -- floor.  The payload half is path-INDEXED, which is what lets the
  -- reading move at the fan and nowhere else
  chP? (λ {u} p → pathStrat? p) chains ≡ true →
  chP? (λ {u} p → valsStrat? (pathFloor p) (arrVal a ∷ [])) chains ≡ true →
  let r = cascadeGo a id chains sched st
  in Σ ℕ λ j → (j ≤ sizeCount c d)
     × (capsOK? (frameStep j c) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true)
cascadeGo-caps siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD hpS hvS =
  proj₁ LV
    , ≤-trans (≤-trans (proj₁ (proj₂ LV))
                       (lvls-mono D (cDel c d) 2≤S ≤-refl ≤-refl ≤-refl
                          (cascadeGo-deliveries siC ifc c d a id chains sl sched st
                             2≤S 1≤R slC slEq inv vC pS n≤S lenB slSz hD hpS hvS)))
              (≤-reflexive (sym (sizeCount-body c d)))
    , proj₂ (proj₂ LV)
  where
  D  = delivN st (proj₂ (proj₂ (cascadeGo a id chains sched st)))
  LV = cascadeGo-level siC ifc c d a id chains sl sched st 2≤S 1≤R slC slEq inv vC pS slSz hD hpS hvS

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
