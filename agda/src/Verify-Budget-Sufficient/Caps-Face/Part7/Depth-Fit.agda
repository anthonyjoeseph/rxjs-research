-- Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit
-- pathNestD-step … caps-tick
module Verify-Budget-Sufficient.Caps-Face.Part7.Depth-Fit where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Nat     using (ℕ; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (*-assoc; ≤ᵇ⇒≤; ≤⇒≤ᵇ; ^-monoʳ-≤; *-monoˡ-≤; *-cancelˡ-≤; ≤-trans; ≤-refl; ≤-reflexive; m≤m+n;
  m≤n+m; n≤1+n; *-identityʳ; *-mono-≤; *-monoʳ-≤; +-monoʳ-≤; +-monoˡ-≤; ⊔-lub; m≤m⊔n; m≤n⊔m;
  +-mono-≤; *-distribˡ-+; +-suc)
open import Data.Nat.Solver     using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.List    using (List; []; _∷_; length; foldr)
open import Data.Bool.ListAction using (all)
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

open import Rx.Prim      using (Tick; Id; _at_from_as_; Gas; after_,_)
open import Rx.Exp       using (obs; Ctx; Closed; Val; sizeᵉ; sizeᵛ)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; valsFit-of-max)
open import Verify-Budget-Sufficient.Nest-Walk using
  (nestDᵛˢ)
open import Verify-Budget-Sufficient.Caps-Depth using
  (depthCascade)
open import Verify-Budget-Sufficient.Deliver-Measure using
  (chainsLenSum)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦF-cap)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using
  (foldPath-nest-regs; PathΦHyp; DispatchΦHyp; FrameΦHyp; valsΦ?; valsSz?;
   stepFrame-nest-Φ; stepFrame-regsSz; stepFrame-sz; Φ-to-bound)
open import Verify-Budget-Sufficient.Regs-Fold-Len using (foldPath-regsSz)
open import Verify-Budget-Sufficient.Nodes-Nest-Walk using (foldPath-nest-nodes)
open import Verify-Budget-Sufficient.Live-Nest-Walk using
  (foldPath-nest-live; PathLiveHyp; walk-LiveHyp-go)
open import Verify-Budget-Sufficient.Nest-Store using
  (chainsNestD; pathNestD; storeNestMax; nestCapAt; nestOK?; realWidAt-def; nestUnit;
  slotsNestSum; liveNest; nodeNest; regsNestMax; sightCeil; slotWrapSum; nestCapAt-0;
  nestCap-mono₀; nestOK?-latch; nestOK?-store; storeNestMax-lub; storeNest-slots≤;
  storeNest-live≤; storeNest-nodes≤; storeNest-regs≤)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; arrVal; RegId; lookupNode; NodeId; _↠_; Frame; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; cascadeLatch; chainsOf; cascadeGo; Path; arrTy; stepFrame;
  subscribeInner; innerFinish; cascade; share-sink; root; fLvlD; sLvlD; chainStep; budgetAt;
  arrTick; iterSize)
open import Rx.Slots using (Slots; slotsSize)

open import Verify-Budget-Sufficient.Caps using
  (1≤capsAt-reg; 2≤capsAt-size; 8≤capsAt-size; B2-cReg≤cSize; Caps; capsAt; capsAt-base-size;
  capsH; frameStep; iterSize-infl; frameStep-mono-j)
open import Verify-Budget-Sufficient.Measures using
  (pathLen; ∧-true; 2X≡X+X)
open import Verify-Budget-Sufficient.Keeps-Ring using
  (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Caps-Nest using
  (nest)
open import Verify-Budget-Sufficient.Caps-Depth
  using (depthInner; depthFin; depthCascade)

open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (capsOK?; capsOK?-mono; eventCaps?; frameSz?; n≤capsAt-size; pathSz?; pathSz?-widen; regsSz?;
  slotsCaps?; valCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using
  (capsOK?-count; capsOK?-regs; frameBud; slotsCaps?-capsAt; valsCaps?)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using
  (valCaps?-size)
open import Decide using (T-to; T⇒≡true; ∧-intro; ∧-trueʳ)
open import Verify-Budget-Sufficient.Caps-Face.Nest-Arith using
  (nestWalkAt; nestWalkAt-def; unit+size≤nestWalkAt; nestCap-inc-sight≤capsH;
   nestUnit≤size; iterSize≤walkFac; walkFac≤nestWalkAt)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Caps using
  (cascadeFinish-caps; cascadeGo-caps; cascadeLatch-caps; chainStep-slots; chainsOf-caps; chainsOf-length)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nodes using
  (chains-count-width)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Cascade-Nest using
  (arr-chains-nest-syn)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Ledger using
  (chainsGo-sz; chainsLenSum-bound)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps using
  (chain-depth-sighted)

pathNestD-step : ∀ {n} {Γ : Ctx n} {s u t} (f : Frame Γ s u) (p : Path Γ u t) →
  pathNestD p ≤ pathNestD (f ↠ p)
pathNestD-step (map-f fn)         p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (scan-f fn _)      p = m≤n+m (pathNestD p) (nestDᵗ fn)
pathNestD-step (take-f _)         p = ≤-refl
pathNestD-step (from-inner _ _ _) p = ≤-refl
pathNestD-step (thru-outer _ _)   p = n≤1+n (pathNestD p)

-- THE GRANT AT ONE OUTER FRAME, which was the whole of what the walk
-- still owed: the four other frame kinds owe nothing, so a path with
-- no `thru-outer` in it needs none of this.  What is owed is a SIGHTED
-- grant covering the values that reach this frame -- a ceiling on each
-- one's depth plus the store's per-slot wrap, which the delivery
-- face's fit demands and the potential does not carry.
--
-- THE GRANT IS NAMED, NOT SEARCHED FOR: the path's remaining depth,
-- plus the maximum depth in flight, plus the wrap the whole context
-- can charge.  The first two come off the premises directly and the
-- input guard is free once the context is read whole, so the only
-- content is that the charge affords it -- and it does, in three
-- pieces that each land on one summand.  The maximum in flight is
-- paid by the outer frame's OWN factor, which is two to the cap and
-- so at least two; the path's depth is under the unit twice over,
-- since the unit is under the cap; and the wrap is charged at the cap
-- while the grant spends it at the context's width, which is smaller.
-- The doubling in the charge is what lets the first piece sit beside
-- the other two rather than competing with them.
walk-thru-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (op : AllOp) (nid : NodeId)
  (p : Path Γ u t) (vals : List (Val Γ (obs u))) (sched : Sched Γ) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (thru-outer op nid ↠ p) ≡ true →
  pathNestD (thru-outer op nid ↠ p) ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
         (thru-outer op nid ↠ p) vals ≡ true →
  FrameΦHyp (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
            (thru-outer op nid) p vals sched
walk-thru-fit {n = n} {e = e} sl id op nid p vals sched hsl hpz hnd hΦ =
  n , G
  , subst (λ z → ValsFit n z G p vals) (sym hsl)
      (valsFit-of-max sl p vals M ≤-refl)
  , *-cancelˡ-≤ 2
      (≤-trans (≤-reflexive spread)
        (≤-trans (+-mono-≤ hA2 hBC2)
                 (≤-reflexive (sym (2X≡X+X (nestWalkAt e sl id))))))
  where
  S    = Caps.cSize (capsAt e sl id)
  Q    = pathΦF S p
  D    = pathNestD p
  M    = nestDᵛˢ vals
  W    = slotWrapSum sl
  X    = nestUnit e sl + S + S * W
  G    = D + M + n * W
  hpp  : pathSz? S p ≡ true
  hpp  = ∧-trueʳ hpz
  2≤S  = 2≤capsAt-size e sl id
  1≤S  = ≤-trans (s≤s z≤n) 2≤S
  Q≤   : Q ≤ 2 ^ (S * S)
  Q≤   = pathΦF-cap S p hpp
  D≤   : D ≤ nestUnit e sl
  D≤   = ≤-trans (n≤1+n D) hnd
  n≤S  : n ≤ S
  n≤S  = n≤capsAt-size e sl id
  2≤2^S : 2 ≤ 2 ^ S
  2≤2^S = ≤-trans (≤-reflexive (sym (*-identityʳ 2))) (^-monoʳ-≤ 2 1≤S)
  -- the values in flight, paid by the outer frame's own factor
  hA   : 2 ^ S * (Q * M) ≤ nestWalkAt e sl id
  hA   = ≤-trans (≤-reflexive (sym (*-assoc (2 ^ S) Q M)))
                 (Φ-to-bound S (nestWalkAt e sl id) (thru-outer op nid ↠ p)
                             vals hΦ)
  hA2  : 2 * (Q * M) ≤ nestWalkAt e sl id
  hA2  = ≤-trans (*-monoˡ-≤ (Q * M) 2≤2^S) hA
  halfShape : ∀ q d → 2 * (q * d) ≡ q * (2 * d)
  halfShape q d = solve 2 (λ q′ d′ → con 2 :* (q′ :* d′) := q′ :* (con 2 :* d′))
                        refl q d
  -- the path's own depth, and the wrap, against the charge's own half
  hBC  : 2 * (Q * D) + Q * (n * W) ≤ 2 ^ (S * S) * X
  hBC  =
    ≤-trans (+-mono-≤
              (≤-trans (≤-reflexive (halfShape Q D))
                       (*-mono-≤ Q≤ (≤-trans (*-monoʳ-≤ 2 D≤)
                                       (≤-trans (≤-reflexive (2X≡X+X (nestUnit e sl)))
                                                (+-monoʳ-≤ (nestUnit e sl)
                                                  (nestUnit≤size e sl id))))))
              (*-mono-≤ Q≤ (*-monoˡ-≤ W n≤S)))
            (≤-reflexive (sym (*-distribˡ-+ (2 ^ (S * S))
                                (nestUnit e sl + S) (S * W))))
  hBC2 : 2 * (2 * (Q * D) + Q * (n * W)) ≤ nestWalkAt e sl id
  hBC2 = subst (2 * (2 * (Q * D) + Q * (n * W)) ≤_)
               (sym (nestWalkAt-def e sl id))
               (≤-trans (*-monoʳ-≤ 2 hBC)
               (≤-trans (≤-reflexive (sym (*-assoc 2 (2 ^ (S * S)) X)))
                        (*-monoˡ-≤ X (^-monoʳ-≤ 2
                          (s≤s (m≤n+m (S * S) (S * (S * S))))))))
  spread : 2 * (Q * (G + D))
             ≡ 2 * (Q * M) + 2 * (2 * (Q * D) + Q * (n * W))
  spread =
    solve 4 (λ q d m w →
               con 2 :* (q :* (d :+ m :+ w :+ d))
                 := con 2 :* (q :* m)
                    :+ con 2 :* (con 2 :* (q :* d) :+ q :* w))
          refl Q D M (n * W)

-- AND THE FRAME'S SIDE-CONDITION IS A CASE SPLIT AND NOTHING ELSE,
-- which is the point of separating it from the walk below: the four
-- silent kinds are units, so the walk's recursion never mentions them.
frameΦ-fit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sl : Slots Γ) (id : ℕ) (f : Frame Γ s u) (p : Path Γ u t)
  (vals : List (Val Γ s)) (sched : Sched Γ) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) (f ↠ p) ≡ true →
  pathNestD (f ↠ p) ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) (f ↠ p) vals ≡ true →
  FrameΦHyp (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
            f p vals sched
frameΦ-fit sl id (map-f _)          p vals sched _ _ _ _ = tt
frameΦ-fit sl id (scan-f _ _)       p vals sched _ _ _ _ = tt
frameΦ-fit sl id (take-f _)         p vals sched _ _ _ _ = tt
frameΦ-fit sl id (from-inner _ _ _) p vals sched _ _ _ _ = tt
frameΦ-fit sl id (thru-outer op nid) p vals sched hsl hpz hnd hΦ =
  walk-thru-fit sl id op nid p vals sched hsl hpz hnd hΦ

-- THE WALK ITSELF, and it is the fold's own recursion with the grant
-- hung off each frame.  Nothing here is arithmetic: the potential is
-- stepped by the frame law, the size receipt and the depth premise are
-- read off the path's head, and the slot equality survives a frame
-- because a frame never rewrites the schedule's slots.
-- THE REGISTRY-SIDE GRANT FOR THE POTENTIAL, and it is the same gap the
-- live arm's is: a sink hands the values to chains whose paths are in
-- the registry, and the potential is a statement about a PATH, so the
-- one the walk carries says nothing about theirs.
--
-- AND THE POTENTIAL IS NOT A SHELTER FROM THAT CROSSING -- IT MEETS IT
-- SOONER.  A sink is a LEAF of the factor recursion, so the receipt
-- handed in here has a factor of one and says only that the values are
-- shallow; the chain fanned into carries its own factor, and every
-- outer frame on it costs the cap's own exponential.  So the fanned-into
-- length enters the charge MULTIPLIED by the cap, where the live arm's
-- size ledger enters it added -- and the level reading the registry is
-- priced at is the same inflated one either way.  The affordable
-- reading is therefore a cap SQUARED here against a cap cubed there --
-- one level lower on the same axis, and the same crossing rather than a
-- second question.  Whatever repairs the live arm's ledger repairs this.
--
-- REFUTED: Refuted.Sink-Level-Range -- the crossing is stated there over
--   an abstract cap and an abstract entry level, so it binds this arm as
--   written and not merely the arm it was taken against.
postulate
  walk-share-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (j : ℕ)
    (i : Fin n) (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    Sched.slots sched ≡ sl →
    regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
              (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
    nestUnit e sl ≤ nestUnit e sl →
    valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
      (share-sink {t = t} i) vals ≡ true →
    DispatchΦHyp sf gas nid now (Caps.cSize (capsAt e sl id))
      (nestWalkAt e sl id) i vals fin sched st

walk-ΦHyp-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id : ℕ) (sf : Gas) (gas : ℕ) (nid : Id) (now : Tick) (j : ℕ)
  (path : Path Γ u t) (vals : List (Val Γ u)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  valsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) vals ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) path vals ≡ true →
  PathΦHyp sf gas nid now (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    path vals fin sched st
walk-ΦHyp-go sl id sf gas nid now j root vals fin sched st _ _ _ _ _ _ = tt
walk-ΦHyp-go sl id sf gas nid now j (share-sink i) vals fin sched st hsl _ _ hreg hnd hΦ =
  walk-share-ΦHyp sl id sf gas nid now j i vals fin sched st hsl hreg ≤-refl hΦ
walk-ΦHyp-go {e = e} sl id sf gas nid now j (f ↠ p) vals fin sched st hsl hpz hsz hreg hnd hΦ =
    hF
  , walk-ΦHyp-go sl id sf gas nid now (suc j) p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
      (trans (KeepsC.slotsEq (stepFrame-keeps sf nid now f p vals fin sched st)) hsl)
      hpz′
      (stepFrame-sz sf nid now f p vals fin sched st B j hfz hsz)
      (stepFrame-regsSz sf nid now f p vals fin sched st B j hsz
        (pathSz?-widen (f ↠ p) (iterSize-infl B 1≤B j B) hpz) hreg)
      (≤-trans (pathNestD-step f p) hnd)
      (stepFrame-nest-Φ sf nid now f p vals fin sched st
        (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) hΦ hF)
  where
  step = stepFrame sf nid now f p vals fin sched st
  hF = frameΦ-fit sl id f p vals sched hsl hpz hnd hΦ
  B  = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  hfz : frameSz? B f ≡ true
  hfz = proj₁ (∧-true (frameSz? B f)
                ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)
  hpz′ : pathSz? B p ≡ true
  hpz′ = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                 (proj₂ (∧-true (frameSz? B f)
                          ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)))

-- THE ARRIVAL'S OWN POTENTIAL, which is the entry reading BOTH the
-- walk's side-condition and the fold's own premise are spent at: one
-- value on the path, so the depth premise the arm was stated with is
-- the whole of it once the path's factor is applied.
entryΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (path : Path Γ (arrTy a) t) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  valsΦ? (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id) path
         (arrVal a ∷ []) ≡ true
entryΦ {e = e} sl id a path hp hΦ = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ Φfit)) refl
  where
  Sz = Caps.cSize (capsAt e sl id)
  Φfit : pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathNestD path)
           ≤ nestWalkAt e sl id
  Φfit = subst (pathΦF Sz path * (nestDᵛ (arrTy a) (arrVal a) + pathNestD path) ≤_)
               (sym (nestWalkAt-def e sl id))
               (*-mono-≤ (≤-trans (pathΦF-cap Sz path hp)
                                  (^-monoʳ-≤ 2
                                    (≤-trans (n≤1+n (Sz * Sz))
                                             (s≤s (m≤n+m (Sz * Sz)
                                                     (Sz * (Sz * Sz)))))))
                         (≤-trans (≤-trans hΦ (m≤m+n (nestUnit e sl) Sz))
                                  (m≤m+n (nestUnit e sl + Sz)
                                         (Sz * slotWrapSum sl))))

-- AND THE CHAIN ENTERS THE WALK WITH IT, the path's remaining depth
-- being under the same unit the arrival's is read against.
chain-walk-ΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (gas : ℕ) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  PathΦHyp (budgetAt e (Sched.slots sched) nextId) gas nextId (arrTick a)
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-ΦHyp {e = e} sl id a nextId gas j path sched st hsl hsz hp hreg hΦ =
  walk-ΦHyp-go sl id _ gas nextId (arrTick a) j path (arrVal a ∷ [])
    (Arrival.isLast a) sched st hsl hp
    (∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans hsz (iterSize-infl B 1≤B j B)))) refl) hreg
    (≤-trans (m≤n+m (pathNestD path) (nestDᵛ (arrTy a) (arrVal a))) hΦ)
    (entryΦ sl id a path hp hΦ)
  where
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)

chainStep-nest-regsC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  regsNestMax (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ regsNestMax (EvalSt.registry st)
      ⊔ (nestWalkAt e sl id)
chainStep-nest-regsC {e = e} sl id a nextId j path sched st hsl hsz hp hreg hΦ =
  foldPath-nest-regs _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)

-- THE NODES ARM IS THE SAME WALK AT THE OTHER PLACE A FRAME STORES,
-- and it is the same three inputs: the entry potential, the walk's
-- per-frame side-condition, and the fold.  What it adds to the
-- registry arm's conclusion is the registry's own join, because a
-- chain that reaches a share fans into paths this one does not walk
-- and stores at their nodes -- the term the path-denominated reading
-- was refuted for missing.  The consumer pays nothing for it: the
-- round already holds the registry under the same ceiling.
--
-- AND IT TAKES THE DEPTH PREMISE THE REGISTRY ARM TAKES.  That is not
-- a convenience of the one call site -- without it the walk has no
-- entry potential, so there is no induction to run at all, and the
-- monolithic form it replaces was asserting the whole walk rather
-- than owing this.
chainStep-nest-nodesC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
        (EvalSt.nodes (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestWalkAt e sl id)
chainStep-nest-nodesC {e = e} sl id a nextId j path sched st hsl hsz hp hreg hΦ =
  foldPath-nest-nodes _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)

-- THE SIZE-SIDE SIDE CONDITION, DISCHARGED.  The walk reads the bound
-- at the level it has reached and each frame moves the level by one,
-- so what the caller owes is the entry reading -- which is the size
-- premise it already carries -- and affordability at every level the
-- path can reach.
--
-- AND AFFORDABILITY IS THE CALLER'S, BECAUSE THE LEVEL A CHAIN ENTERS
-- AT IS THE CALLER'S.  `iterSize≤walkFac` discharges it outright for a
-- chain entered at level zero, which is why this used to carry no such
-- premise; a cascade enters its k-th chain at whatever the first k-1
-- left, so the range that has to be afforded is a property of the
-- SELECTION and cannot be recovered from anything in hand here.
chain-walk-LiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (gas : ℕ) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  j + pathLen path ≤ Lv →
  PathLiveHyp (budgetAt e (Sched.slots sched) nextId) gas nextId (arrTick a)
    (nestWalkAt e sl id) path (arrVal a ∷ []) (Arrival.isLast a) sched st
chain-walk-LiveHyp {e = e} sl id a nextId gas Lv j path sched st hsl afford hsz hp hreg hj =
  walk-LiveHyp-go _ gas nextId (arrTick a) S (nestWalkAt e sl id) Lv j path
    (arrVal a ∷ []) (Arrival.isLast a) sched st afford 1≤S entrySz hp hreg hj
  where
  S = Caps.cSize (capsAt e sl id)
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  entrySz : valsSz? (iterSize S j S) (arrVal a ∷ []) ≡ true
  entrySz = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans hsz (iterSize-infl S 1≤S j S)))) refl

-- THE LIVE ARM, the third and last of the chain's arms to become the
-- walk rather than an assertion about it.  Two extra terms over the
-- registry arm's conclusion: the slots, because a scripted slot's
-- subscribe mints out of script data, and the registry's join, because
-- a share fans into chains that mint out of their own.  The round
-- holds all three under the same ceiling, so the consumer pays for
-- neither.
chainStep-nest-liveC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path ≤ Lv →
  foldr (λ l acc → liveNest l ⊔ acc) 0
        (Sched.live (proj₁ (proj₂ (chainStep nextId a path sched st))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched)
        ⊔ regsNestMax (EvalSt.registry st)
        ⊔ (nestWalkAt e sl id)
chainStep-nest-liveC {e = e} sl id a nextId Lv j path sched st hsl afford hsz hp hreg hΦ hj =
  foldPath-nest-live _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st
    (Caps.cSize (capsAt e sl id)) (nestWalkAt e sl id)
    (entryΦ sl id a path hp hΦ)
    (chain-walk-ΦHyp sl id a nextId _ j path sched st hsl hsz hp hreg hΦ)
    (chain-walk-LiveHyp sl id a nextId _ Lv j path sched st hsl afford hsz hp hreg hj)

-- AND THE UNIT IS UNDER EVERY CAP, being the cap at instant zero and
-- the recurrence nondecreasing after it.
unit≤cap : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  nestUnit e sl ≤ nestCapAt e sl id
unit≤cap e sl id =
  ≤-trans (≤-reflexive (sym (nestCapAt-0 e sl))) (nestCap-mono₀ e sl id)

-- AND THAT IS WHAT A WALK CAN CARRY.  A bound the chains preserve has
-- to be one the growth cannot climb past however many chains run, and
-- a growth priced against the ENTRY store is not one -- it compounds.
-- These three price it against the program instead, so the walk's
-- bound survives a chain exactly when it already covers one instant's
-- increment, which is a condition on the bound and not on the walk.
-- REFUTED: Refuted.Chain-Step-Nodes
-- REFUTED: Refuted.Chain-Step-Live-Additive
-- DEAD ROUTE: spending the unconditional live-growth bound and
--   discharging its three disjuncts against the entry cap.  Two go;
--   the third is the path factor above, and it is not repairable by a
--   premise, only by a tighter growth statement.
-- DEAD ROUTE: restating the whole walk one instant up, so the arms
--   preserve the successor cap and the round's ceiling is read there.
--   The entry lifts and the arms carry over, but the consumer does
--   not: its fuel is the exponential at THIS instant, which the caps
--   recurrence pins to this instant's cap.
-- DEAD ROUTE: charging the arms the instant's INCREMENT, which is what
--   they carried while they mirrored the entry burst.  The increment's
--   own exponent reads the delivery at the NEXT instant, and the size
--   there is already a blowup story above the fuel available here, so
--   no reading of it fits under this instant's exponential.
chainStep-store≤ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  pathSz? (Caps.cSize (capsAt e sl id)) path ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  nestDᵛ (arrTy a) (arrVal a) + pathNestD path ≤ nestUnit e sl →
  j + pathLen path ≤ Lv →
  nestWalkAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  storeNestMax (proj₁ (proj₂ (chainStep nextId a path sched st)))
               (proj₂ (proj₂ (chainStep nextId a path sched st))) ≤ S
chainStep-store≤ {e = e} sl id a nextId S Lv j path sched st hsl afford hsz hp hreg hΦ hj hinc hS =
  storeNestMax-lub sd′ st′ S SL
    (≤-trans (chainStep-nest-liveC  sl id a nextId Lv j path sched st hsl afford hsz hp hreg hΦ hj)
             (⊔-lub (⊔-lub (⊔-lub (≤-trans (storeNest-live≤  sched st) hS)
                                  (≤-trans (storeNest-slots≤ sched st) hS))
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-nodesC sl id a nextId j path sched st hsl hsz hp hreg hΦ)
             (⊔-lub (⊔-lub (≤-trans (storeNest-nodes≤ sched st) hS)
                           (≤-trans (storeNest-regs≤ sched st) hS))
                    hinc))
    (≤-trans (chainStep-nest-regsC  sl id a nextId j path sched st hsl hsz hp hreg hΦ)
             (⊔-lub (≤-trans (storeNest-regs≤  sched st) hS) hinc))
  where
  sd′ = proj₁ (proj₂ (chainStep nextId a path sched st))
  st′ = proj₂ (proj₂ (chainStep nextId a path sched st))
  flat = unit+size≤nestWalkAt e sl id
  SL : slotsNestSum (Sched.slots sd′) ≤ S
  SL = ≤-trans (≤-reflexive (cong slotsNestSum
                              (chainStep-slots nextId a path sched st)))
               (≤-trans (storeNest-slots≤ sched st) hS)

-- THE ROUND IS A WALK OVER ITS CHAINS, and the three-callee clause is
-- the one `depthCascade` reports: the tail at the incoming state, the
-- live chain at the delivered-marked one, and the tail again at the
-- state that chain left.
-- ONE CHAIN'S DEPTH OUT OF THE SELECTION'S JOIN.  The cascade-level
-- reading is a ⊔-fold over the whole selection, and the walk spends it
-- one chain at a time, so the fold has to be taken apart before the
-- first `chainStep` sees it.
chainsNest-all : ∀ {n} {Γ : Ctx n} {s t} (D U : ℕ)
  (cs : List (RegId × Path Γ s t)) →
  D + chainsNestD cs ≤ U →
  all (λ rc → D + pathNestD (proj₂ rc) ≤ᵇ U) cs ≡ true
chainsNest-all D U []       h = refl
chainsNest-all D U (c ∷ cs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (≤-trans (+-monoʳ-≤ D
                       (m≤m⊔n (pathNestD (proj₂ c)) (chainsNestD cs))) h)))
          (chainsNest-all D U cs
            (≤-trans (+-monoʳ-≤ D (m≤n⊔m (pathNestD (proj₂ c))
                                          (chainsNestD cs))) h))

-- THE REGISTRY ACROSS A WHOLE CHAIN, AT ONE LEVEL PER CHAIN, AND THE
-- DOOR IS THE FOLD.  `chainStep` is one call to `foldPath` -- the
-- arrival's value as the only value in flight, its tick and source as
-- the fold's, and its lastness as the fold's fin -- so the whole of
-- what a chain does to the registry is what that call does, and the
-- level it costs is the fold's one step.
--
-- SO WHAT IS OWED HERE IS ONE TRANSPORT AND NOTHING ELSE.  The path
-- passes STRAIGHT THROUGH at the program's cap, because the fold's
-- two caps are the same two this face already keeps apart -- the
-- program's own and the level reached -- so nothing has to claim a
-- chain grew with the level it is walked at.  What remains is the
-- arrival, read here as a size and by the fold as a list, which
-- becomes the one-element values premise at the level's reading and
-- is free at `j = 0`, where the iterate is the cap itself.
--
-- SO THE LEVEL ACCUMULATES DOWN THE SELECTION RATHER THAN COLLAPSING
-- AT THIS DOOR.  The consumer spends this once per chain, feeding each
-- output registry in as the next chain's premise, and what must bound
-- the run is `nestWalkAt` -- the way `iterSize≤walkFac` already makes a
-- bounded run of levels affordable against the walk factor, which is
-- why the store side now carries a `j + pathLen` premise beside it.
chainStep-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (S j : ℕ) (a : Arrival Γ) (nextId : Id)
  (path : Path Γ (arrTy a) t) (sched : Sched Γ) (st : EvalSt e) →
  1 ≤ S →
  sizeᵛ (arrTy a) (arrVal a) ≤ S →
  pathSz? S path ≡ true →
  regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
  regsSz? (iterSize S (suc j) S)
    (EvalSt.registry (proj₂ (proj₂ (chainStep nextId a path sched st))))
    ≡ true
chainStep-regsSz S j a nextId path sched st 1≤S hsz hp hreg =
  foldPath-regsSz _ _ _ _ _ path (arrVal a ∷ []) _ _ sched st S j 1≤S
    entrySz hp hreg
  where
  entrySz : valsSz? (iterSize S j S) (arrVal a ∷ []) ≡ true
  entrySz = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
              (≤-trans hsz (iterSize-infl S 1≤S j S)))) refl

-- AND THE SELECTION'S LEVEL BUDGET IS ONE NUMBER, PEELED THREE WAYS
-- PER CHAIN.  The head chain walks at the level reached so far, so it
-- owes its own frames; the tail is re-entered twice, once at that same
-- level and once one above it, and both times with one fewer chain in
-- hand.  `chainsLenSum + length` is what makes those three fit under
-- one premise: the sum pays the frames and the count pays the levels.
--
-- AND THE BUDGET IS NOT THE SIZE CAP, WHICH IS THE WHOLE FINDING HERE.
-- A cap admits chains of a cap's length and a selection as wide as the
-- registry, so its own `chainsLenSum` already outruns it -- there is no
-- arrangement of the arithmetic under which a cascade's levels fit
-- under the number one chain's frames fit under.  So the budget rides
-- as a parameter with the affordability that pays for it, and the
-- caller carries a ledger it can actually meet.
cascade-depth-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id) (S : ℕ) (Lv j : ℕ)
  (chains : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  iterSize (Caps.cSize (capsAt e sl id)) Lv (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  all (λ rc → pathSz? (Caps.cSize (capsAt e sl id)) (proj₂ rc)) chains ≡ true →
  all (λ rc → nestDᵛ (arrTy a) (arrVal a) + pathNestD (proj₂ rc)
                ≤ᵇ nestUnit e sl) chains ≡ true →
  regsSz? (iterSize (Caps.cSize (capsAt e sl id)) j
            (Caps.cSize (capsAt e sl id))) (EvalSt.registry st) ≡ true →
  j + chainsLenSum chains + length chains ≤ Lv →
  nestWalkAt e sl id ≤ S →
  storeNestMax sched st ≤ S →
  depthCascade a nextId chains sched st
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
cascade-depth-go sl id a nextId S Lv j [] sched st hsl afford hsz hps hΦs hreg hbud hinc hS = z≤n
cascade-depth-go {e = e} sl id a nextId S Lv j ((rid , c) ∷ cs) sched st
  hsl afford hsz hps hΦs hreg hbud hinc hS =
  ⊔-lub (cascade-depth-go sl id a nextId S Lv j cs sched st
           hsl afford hsz hpr hΦr hreg hbud-tail hinc hS)
        (⊔-lub (chain-depth-sighted sl a nextId S c sched st₀ hsl hS)
               (cascade-depth-go sl id a nextId S Lv (suc j) cs
                  (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
                  (trans (chainStep-slots nextId a c sched st₀) hsl)
                  afford hsz hpr hΦr
                  (chainStep-regsSz B j a nextId c sched st₀ 1≤B hsz hpc hreg)
                  hbud-next
                  hinc
                  (chainStep-store≤ sl id a nextId S Lv j c sched st₀ hsl afford hsz hpc hreg
                     (≤ᵇ⇒≤ (nestDᵛ (arrTy a) (arrVal a) + pathNestD c)
                           (nestUnit e sl) (T-to hΦc))
                     hbud-head hinc hS)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  r   = chainStep nextId a c sched st₀
  B   = Caps.cSize (capsAt e sl id)
  1≤B : 1 ≤ B
  1≤B = ≤-trans (s≤s z≤n) (8≤capsAt-size e sl id)
  hpc = proj₁ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hpr = proj₂ (∧-true (pathSz? (Caps.cSize (capsAt e sl id)) c) _ hps)
  hΦc = proj₁ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hΦr = proj₂ (∧-true (nestDᵛ (arrTy a) (arrVal a) + pathNestD c
                         ≤ᵇ nestUnit e sl) _ hΦs)
  hbud-head : j + pathLen c ≤ Lv
  hbud-head =
    ≤-trans (≤-trans (+-monoʳ-≤ j (m≤m+n (pathLen c) (chainsLenSum cs)))
                     (m≤m+n (j + (pathLen c + chainsLenSum cs)) (suc (length cs))))
            hbud
  hbud-tail : j + chainsLenSum cs + length cs ≤ Lv
  hbud-tail =
    ≤-trans (+-mono-≤ (+-monoʳ-≤ j (m≤n+m (chainsLenSum cs) (pathLen c)))
                      (n≤1+n (length cs)))
            hbud
  hbud-next : suc j + chainsLenSum cs + length cs ≤ Lv
  hbud-next =
    ≤-trans (s≤s (+-monoˡ-≤ (length cs)
                    (+-monoʳ-≤ j (m≤n+m (chainsLenSum cs) (pathLen c)))))
            (≤-trans (≤-reflexive
                       (sym (+-suc (j + (pathLen c + chainsLenSum cs)) (length cs))))
                     hbud)

-- the cascade's opening ledger write is not a registry write, on
-- either branch of the spent-source test
latch-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (B : ℕ) (a : Arrival Γ) (st : EvalSt e) →
  regsSz? B (EvalSt.registry st) ≡ true →
  regsSz? B (EvalSt.registry (cascadeLatch a st)) ≡ true
latch-regsSz B a st h with Arrival.isLast a
... | true  = h
... | false = h

-- EVERY LEVEL A WHOLE CASCADE REACHES IS AFFORDABLE, and this is the
-- one place the level ledger has to meet the walk's ceiling.  The
-- selection enters its k-th chain at the level the first k-1 left and
-- climbs one per frame inside it, so the levels it reaches run to the
-- chains' total length plus their count -- and that ledger is what
-- `cascade-depth-go` carries, precisely so this obligation can be
-- stated once for the whole selection rather than re-derived per chain.
--
-- AND THE INVARIANT IS PART OF THE STATEMENT, not a convenience the
-- caller happens to offer.  Without it the two sides are not
-- comparable quantities at all: the charge reads the program, the slot
-- vocabulary and the instant and never the state, while the ledger
-- reads the state and nothing else -- so a registry longer than the
-- charge satisfies every hypothesis and lands a level above the
-- conclusion.  With it the registry is a width and each chain is legal
-- at a cap's length, so the ledger is a cap SQUARED plus a cap, which
-- is the range the walk's charge is now read at a cap CUBED to cover.
--
-- REFUTED: Refuted.Cascade-Afford-Wide
-- TWIN: `arr-chains-len-sum`
-- DEAD ROUTE: keying the cascade's budget to the size cap, so that a
--   one-chain affordability discharges it unchanged.  The cap admits
--   chains of a cap's length and the registry admits a selection as
--   wide as itself, so the selection's own `chainsLenSum` already
--   outruns the cap -- the premise is unsatisfiable at the caller
--   rather than merely hard to prove there.
cascade-afford : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  capsOK? (capsAt e sl id) sched st ≡ true →
  iterSize (Caps.cSize (capsAt e sl id))
    (chainsLenSum (chainsOf a st) + length (chainsOf a st))
    (Caps.cSize (capsAt e sl id))
    ≤ nestWalkAt e sl id
cascade-afford {e = e} sl id a sched st hok =
  ≤-trans (iterSize≤walkFac S _ S (8≤capsAt-size e sl id) ledger ≤-refl)
          (walkFac≤nestWalkAt e sl id)
  where
  S = Caps.cSize (capsAt e sl id)
  wid : length (chainsOf a st) ≤ S
  wid = ≤-trans (chains-count-width sl id a sched st hok)
                (≤-trans (≤-reflexive (realWidAt-def e sl id))
                         (B2-cReg≤cSize e sl id))
  ledger : chainsLenSum (chainsOf a st) + length (chainsOf a st) ≤ S * S + S
  ledger =
    +-mono-≤ (≤-trans (chainsLenSum-bound S (chainsOf a st)
                         (chainsGo-sz S a (EvalSt.registry st)
                           (capsOK?-regs (capsAt e sl id) sched st hok)))
                      (*-monoˡ-≤ S wid))
             wid

cascade-depth-sighted : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a))
                (nestCapAt e sl id + (nestWalkAt e sl id))
                (nestUnit e sl)
cascade-depth-sighted {e = e} sl id a nextId sched st hsl hok hn hsz =
  cascade-depth-go sl id a nextId (nestCapAt e sl id + (nestWalkAt e sl id))
    (chainsLenSum (chainsOf a st) + length (chainsOf a st)) 0
    (chainsOf a st) sched (cascadeLatch a st) hsl
    (cascade-afford sl id a sched st hok) hsz
    (chainsOf-caps (Caps.cSize (capsAt e sl id)) a st
      (capsOK?-regs (capsAt e sl id) sched st hok))
    (chainsNest-all (nestDᵛ (arrTy a) (arrVal a)) (nestUnit e sl) (chainsOf a st)
      (arr-chains-nest-syn sl id a sched st hsl hok hn))
    (latch-regsSz (Caps.cSize (capsAt e sl id)) a st
      (capsOK?-regs (capsAt e sl id) sched st hok))
    ≤-refl
    (m≤n+m (nestWalkAt e sl id)
           (nestCapAt e sl id))
    (≤-trans (nestOK?-store e sl id sched (cascadeLatch a st)
               (trans (nestOK?-latch e sl id a sched st) hn))
             (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))

-- AND ALL THREE OF THE CEILING'S SUMMANDS ARE THE SAME CAP.  The
-- arrival's nesting is held under it by the caller's premise, the
-- store's by the nesting invariant, and the wrap unit IS the cap at
-- instant zero -- so the sighted sum is three readings of one number
-- and the ceiling collapses to a multiple of it.  That collapse is the
-- whole of what the run-side hypotheses buy.
sight-collapse : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ suc (sizeᵉ e) * suc (3 * B)
sight-collapse {e = e} sl a B S hS hval hu =
  *-monoʳ-≤ (suc (sizeᵉ e)) (s≤s sum≤3B)
  where
  eq : B + B + B ≡ 3 * B
  eq = solve 1 (λ b → b :+ b :+ b := con 3 :* b) refl B
  sum≤3B : nestDᵛ (arrTy a) (arrVal a) + S + nestUnit e sl ≤ 3 * B
  sum≤3B =
    ≤-trans (+-mono-≤ (+-mono-≤ hval hS) hu) (≤-reflexive eq)


-- AND THE FUEL HAS THAT ROOM, so the comparison the depth face owes
-- the height is assembled rather than asserted.  The caps recurrence
-- steps by a blowup the fuel itself drives and `blowH` is what the
-- fuel climbs by, so the size at an instant and the fuel at that
-- instant are one quantity read once each -- with two exponentials
-- between them, bought by the single spare registration the tower
-- bracket leaves in the pooled walk.
sighted-nest≤capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (B S : ℕ) →
  S ≤ B →
  nestDᵛ (arrTy a) (arrVal a) ≤ B →
  nestUnit e sl ≤ B →
  suc (sizeᵉ e) * suc (3 * B) ≤ capsH e sl id →
  sightCeil (sizeᵉ e) (nestDᵛ (arrTy a) (arrVal a)) S (nestUnit e sl)
    ≤ capsH e sl id
sighted-nest≤capsH {e = e} sl id a B S hS hval hu room =
  ≤-trans (sight-collapse {e = e} sl a B S hS hval hu) room

-- THE ROUND'S DEPTH FITS THE INSTANT'S FUEL, assembled rather than
-- asserted: the descent goes under what the round can see, and what
-- the round can see goes under the fuel.  The split is the point -- the
-- first half is a statement about the evaluator at concrete programs
-- and the second is arithmetic about two currencies, and only the
-- second is where the height comparison lives.
--
-- THE SIZE PREMISE IS CARRIED AND NOT SPENT.  It is the caller's, and
-- it belongs to the statement rather than to this route: a descent
-- bounded through the payload's NESTING says nothing about the
-- payload's size, and the consumers that hand this premise in are
-- pricing the same arrival on the size axis in the same breath.
cascade-depth-capsH : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  sizeᵛ (arrTy a) (arrVal a) ≤ Caps.cSize (capsAt e sl id) →
  depthCascade a nextId (chainsOf a st) sched (cascadeLatch a st)
    ≤ capsH e sl id
cascade-depth-capsH {e = e} sl id a nextId sched st hsl hcaps hnest hval hsz =
  ≤-trans (cascade-depth-sighted sl id a nextId sched st hsl hcaps hnest hsz)
          (sighted-nest≤capsH sl id a B B ≤-refl
             (≤-trans hval (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))
             (≤-trans (unit≤cap e sl id)
               (m≤m+n (nestCapAt e sl id) (nestWalkAt e sl id)))
             (nestCap-inc-sight≤capsH e sl id))
  where
  B = nestCapAt e sl id + (nestWalkAt e sl id)

caps-tick :
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
  (sl : Slots Γ) (id : ℕ) (a : Arrival Γ) (nextId : Id)
  (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots sched ≡ sl →
  capsOK? (capsAt e sl id) sched st ≡ true →
  nestOK? e sl id sched st ≡ true →
  nestDᵛ (arrTy a) (arrVal a) ≤ nestCapAt e sl id →
  valCaps? (capsAt e sl id) sl (arrTy a) (arrVal a) ≡ true →
  let r = cascade a nextId sched st
  in capsOK? (capsAt e sl (suc id)) (proj₁ (proj₂ r)) (proj₂ (proj₂ r)) ≡ true
caps-tick siC ifc {e = e} sl id a nextId sched st slEq pre nok bnd val =
  cascadeFinish-caps (capsAt e sl (suc id)) a (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
    (capsOK?-mono (frameStep j c) (capsAt e sl (suc id))
                  (proj₁ (proj₂ GOr)) (proj₂ (proj₂ GOr))
                  (frameStep-mono-j c (2≤capsAt-size e sl id) jFits)
                  (proj₂ (proj₂ GO)))
  where
  c    = capsAt e sl id
  st₀  = cascadeLatch a st
  GO   = cascadeGo-caps siC ifc c (capsH e sl id) a nextId (chainsOf a st) sl sched st₀
           (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id)
           (slotsCaps?-capsAt e sl id) slEq
           (cascadeLatch-caps c a sched st pre) val
           (chainsOf-caps (Caps.cSize c) a st (capsOK?-regs c sched st pre))
           (n≤capsAt-size e sl id)
           (≤-trans (chainsOf-length a st) (capsOK?-count c sched st pre))
           -- H1 is FREE here: capsAt's base formula already contains the
           -- slot store as a summand
           (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e))
                    (capsAt-base-size e sl id))
           (cascade-depth-capsH sl id a nextId sched st slEq pre nok bnd
             (≤ᵇ⇒≤ (sizeᵛ (arrTy a) (arrVal a)) (Caps.cSize c)
                   (T-to (valCaps?-size c sl (arrTy a) (arrVal a) val))))
  GOr   = cascadeGo a nextId (chainsOf a st) sched st₀
  j     = proj₁ GO
  jFits = proj₁ (proj₂ GO)

-- REFUTED: `caps-frame-boundary-absurd`
--   (sizeStep C C ≤ C is impossible for 1 ≤ C) and `reach-via-size-absurd`
--   (2 ^ C ≤ C is impossible) now live in `refuted/Refuted/Caps-Face.agda`,
--   checked by `make refuted`.  Do not re-attempt either bound here.


-- (`reach-resets`, the reset cluster this section's prose names, is
-- declared ABOVE the face postulate block — `thruOuter-face` consumes
-- it and is itself consumed before this point in the file.)

------------------------------------------------------------------
-- HOP DESCENT, the *All clause's missing edge — AND THE OPEN HOLE.

