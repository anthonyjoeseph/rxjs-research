-- THE LIVE LIST'S DEPTH ALONG ONE CHAIN, walked frame by frame -- the
-- third and last of the chain's arms to stop being one postulate, and
-- the only one whose per-frame leaf cannot be paid out of the
-- potential alone.
--
-- WHY THE POTENTIAL IS NOT ENOUGH HERE, and it is a property of the
-- currency rather than of the walk.  The nesting-DEPTH measures read
-- ZERO into a deferred body -- that truncation is what makes the fixed
-- point safe -- so an outer frame handed a deferred observable sees a
-- potential of zero and mints a live whose pending payload is the body
-- itself, at whatever depth the body has.  A charge built from the
-- depth measures is blind to exactly that step, which is what killed
-- the additive reading of this arm.  What is not blind to it is SIZE,
-- and depth is under size everywhere; so the outer frame's side
-- condition here is a size bound on the values reaching it, and the
-- four other frame kinds owe nothing.
--
-- AND THE CONCLUSION CARRIES TWO TERMS THE WALKED PATH DOES NOT SAY.
-- A scripted cold slot's subscribe mints a live out of SCRIPT data, so
-- the slots are in it; and a share sink fans into registry chains that
-- mint their own, so the registry's join is in it for the same reason
-- the nodes arm carries it.  Both reproduce across a frame at no cost:
-- a frame never rewrites the slots, and the registry's own frame leaf
-- is already proven to step.
--
-- REFUTED: Refuted.Chain-Step-Live-Additive
module Verify-Budget-Sufficient.Live-Nest-Walk where

open import Data.Bool using (Bool; true)
open import Data.Bool.ListAction using (all)
open import Data.Fin using (Fin)
open import Data.List using (List; _++_; foldr)
open import Data.Nat using (ℕ; _⊔_; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent)
open import Rx.Exp using (Ctx; Closed; Val; sizeᵛ)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_;
         map-f; scan-f; take-f; from-inner; thru-outer;
         foldPath; stepFrame; dispatchShare)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; regsNestMax)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsΦ?; PathΦHyp; stepFrame-nest-Φ; stepFrame-nest-regs)

-- WHAT AN OUTER FRAME OWES BEYOND THE POTENTIAL, stated at the one
-- kind that can subscribe.  A size bound rather than a depth one,
-- because the mint reaches through the gate the depth measures stop
-- at; and stated per frame rather than per statement so that four
-- arms discharge it with a unit and the fold stays uniform.
FrameLiveHyp : ∀ {n} {Γ : Ctx n} {s u t} (U : ℕ) (f : Frame Γ s u)
  (path : Path Γ u t) (vals : List (Val Γ s)) → Set
FrameLiveHyp U (map-f _)          path vals = ⊤
FrameLiveHyp U (scan-f _ _)       path vals = ⊤
FrameLiveHyp U (take-f _)         path vals = ⊤
FrameLiveHyp U (from-inner _ _ _) path vals = ⊤
FrameLiveHyp {s = s} U (thru-outer _ _) path vals =
  all (λ v → sizeᵛ s v ≤ᵇ U) vals ≡ true

-- the same shape `PathΦHyp` has, and threaded by the same fold: the
-- values a frame sees are the ones the frames above it produced, so a
-- side condition on them has to step alongside the walk rather than
-- being stated once at the chain's head.
PathLiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (U : ℕ) (path : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
PathLiveHyp sf id now U root           vals fin sched st = ⊤
PathLiveHyp sf id now U (share-sink _) vals fin sched st = ⊤
PathLiveHyp sf id now U (f ↠ p) vals fin sched st =
  FrameLiveHyp U f p vals
  × PathLiveHyp sf id now U p
      (proj₁ (stepFrame sf id now f p vals fin sched st))
      (proj₁ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st))))
      (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))

postulate
  -- ONE FRAME'S MINTS.  Four kinds mint nothing at all; the outer
  -- frame subscribes, and what a subscribe puts on the live list is
  -- either a script's resolved tail -- charged to the slots -- or a
  -- deferred body, whose depth is under its size and so under the
  -- bound the side condition supplies.
  --
  -- PROBED: `Probed.Chain-Step-Live-Deferred` reaches this leaf by
  --   RUNNING a whole chain over it, at the one program shape that can
  --   move the fold: a `mapᵉ` over the async input handing the outer
  --   *All a deferred nest per arrival, so the chain the evaluator
  --   presents subscribes it and the live it mints carries the body.
  --   Covered: the fold rising 0 to 1 and 0 to 3 as the nest deepens,
  --   against a syntactic charge of eighteen and twenty-six that the
  --   tree proves the size cap dominates -- so both sides move and the
  --   ordering is load-bearing on the depth axis.  Not covered: one
  --   frame in isolation, since the rows read the composite; and a
  --   fold already nonzero at entry, where the growth would compound
  --   rather than start from zero.
  stepFrame-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (f ↠ path) vals ≡ true →
    FrameLiveHyp U f path vals →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched) ⊔ U

  -- THE SHARE BOUNDARY.  The chains the sink fans into are a selection
  -- from the registry and mint their own lives out of their own
  -- values, so the registry's join is what covers the fan-out here --
  -- the same term, and the same reason, as the nodes arm.
  dispatchShare-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ _)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (share-sink {t = t} i) vals ≡ true →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U

-- THE WALK.  Four facts per frame and no more: the live leaf for what
-- this frame minted, the slots' invariance for the term the script
-- mints are charged to, the registry's frame leaf for the term the
-- share fan-out is charged to, and the potential's own step law.
foldPath-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (path : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
  valsΦ? B U path vals ≡ true →
  PathΦHyp sf id now B U path vals fin sched st →
  PathLiveHyp sf id now U path vals fin sched st →
  foldr (λ l acc → liveNest l ⊔ acc) 0
    (Sched.live (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched)
        ⊔ regsNestMax (EvalSt.registry st) ⊔ U
foldPath-nest-live sf gas id now envSrc root vals evs fin sched st B U hΦ _ _ =
  ≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                          (slotsNestSum (Sched.slots sched)))
                   (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
          (m≤m⊔n _ U)
foldPath-nest-live sf gas id now envSrc (share-sink i) vals evs fin sched st B U hΦ _ _ =
  dispatchShare-nest-live sf gas id now i vals fin sched st B U hΦ
foldPath-nest-live sf gas id now envSrc (f ↠ p) vals evs fin sched st B U hΦ (hF , hR) (hL , hLR) =
  ≤-trans (foldPath-nest-live sf gas id now envSrc p
             (proj₁ step) (evs ++ proj₁ (proj₂ step))
             (proj₁ (proj₂ (proj₂ step)))
             (proj₁ (proj₂ (proj₂ (proj₂ step))))
             (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U
             (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR hLR)
          (⊔-lub (⊔-lub (⊔-lub liveStep slotStep) regStep) (m≤n⊔m (L ⊔ S ⊔ R) U))
  where
  step = stepFrame sf id now f p vals fin sched st
  L = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
  S = slotsNestSum (Sched.slots sched)
  R = regsNestMax (EvalSt.registry st)
  intoL : L ≤ L ⊔ S ⊔ R ⊔ U
  intoL = ≤-trans (≤-trans (m≤m⊔n L S) (m≤m⊔n (L ⊔ S) R)) (m≤m⊔n (L ⊔ S ⊔ R) U)
  intoS : S ≤ L ⊔ S ⊔ R ⊔ U
  intoS = ≤-trans (≤-trans (m≤n⊔m L S) (m≤m⊔n (L ⊔ S) R)) (m≤m⊔n (L ⊔ S ⊔ R) U)
  intoR : R ≤ L ⊔ S ⊔ R ⊔ U
  intoR = ≤-trans (m≤n⊔m (L ⊔ S) R) (m≤m⊔n (L ⊔ S ⊔ R) U)
  intoU : U ≤ L ⊔ S ⊔ R ⊔ U
  intoU = m≤n⊔m (L ⊔ S ⊔ R) U
  liveStep : foldr (λ l acc → liveNest l ⊔ acc) 0
               (Sched.live (proj₁ (proj₂ (proj₂ (proj₂ step)))))
               ≤ L ⊔ S ⊔ R ⊔ U
  liveStep =
    ≤-trans (stepFrame-nest-live sf id now f p vals fin sched st B U hΦ hL)
            (⊔-lub (⊔-lub intoL intoS) intoU)
  slotStep : slotsNestSum (Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ step)))))
               ≤ L ⊔ S ⊔ R ⊔ U
  slotStep =
    subst (_≤ L ⊔ S ⊔ R ⊔ U)
          (cong slotsNestSum
            (sym (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))))
          intoS
  regStep : regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ step)))))
              ≤ L ⊔ S ⊔ R ⊔ U
  regStep =
    ≤-trans (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ)
            (⊔-lub intoR intoU)
