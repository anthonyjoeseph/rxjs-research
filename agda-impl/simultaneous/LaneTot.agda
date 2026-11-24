{-# OPTIONS --guardedness #-}

-- A ROW THE SCAN'S SOURCE READS FINDS A ROUTE THE SCAN COUNTS: a value or
-- completion of any branch, and a live over, unless exempt.  The outer
-- and the closer are settled in `simultaneous.HeldSrc`; a lane's rows are
-- read here, over the lanes' own counts (`simultaneous.HeldLaneRoutes`).
module simultaneous.LaneTot where

import Data.List as L
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_; find)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ; ∈-∃++)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum as Sum
open import Data.Bool using (Bool; T; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (¬_; Dec; yes; no)

open import Tree using (Obs; FlatOp; connected)
open import denotation.Position using (Pos; Path; root; _≟ᵖ_; ix; sub; _⊕_; inside; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; enter; hot; _≼_; _≺_)
open import denotation.Read using (Run) renaming (_∷_ to _∷ᴿ_)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; ok-step; ⊑-≼; InvAt; _⊑_; inside-⊑; ⊑-snoc; ⊕-assoc; ⊕-injˡ)
open import denotation.Laws.Modulus using (≺-absurd; ≺-≼-≺; ≺-irrefl; ≺-trans; ≺-ext; ≺→≼)
open import simultaneous.Horizon using (past-sub)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (lone; module Elaborate; Flat; laneB; outerB; closeB)
open import simultaneous.InstEmit using (instEmit; mark; value; begin; over; stop; outerOpen; outerClose; laneStart; laneDone; burstEnd;
  outerDone; subscribed; completed; valuesOf)
open import simultaneous.Relations using (Met)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.Routed using (Held; Early; Placed; Ex; Sync; Carried; cnt; c-value; c-stop; c-done; c-over; nameOf; nm; Valued; opos)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import simultaneous.HeldTake using (ex-ext)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.Counts using (Counts; pre; idle-row)
open import simultaneous.Project using (run-prefix)
open import simultaneous.RealView using (lane-at)
open import simultaneous.LaneLocal using (Fit; Fine; inv-ev)
open import simultaneous.LaneEpoch using (module Lanes)
open import simultaneous.LaneFloor using (module Floor)
open import simultaneous.FlatLanes using (Tg; BProj; module BProj; keep; drop; tagged; brTag)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldComb using (ev; init; past; from-++)
open import simultaneous.FlatSim using (tot)
open import simultaneous.HeldSrc using (module CombSrc; Opens; o-value; o-done)
open import simultaneous.HeldLanes using (module CombLanes; bproj-mem)
open import simultaneous.HeldLaneRoutes using (module LaneRoutes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (AIE; IE; each; laneˢ; count; opening)

module LaneTot (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (fr : Fresh eh p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
               (tp : Placed (Fresh eh) (FlatHots.σ₁ m ρ op f s env p))
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                         (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open Lanes {B} op Own (LaneMark laneStart) DoneMark act LaneEmit using (oc-total; oc[]; oc-in; oc-out)

  -- Whether a row lies in a subscription's burst.
  sync? : ∀ c y → Dec (T (inside c y) × rootOf y ≡ rootOf c)
  sync? c y with inside c y | rootOf y ≟ᵖ rootOf c
  ... | true  | yes e = yes (tt , e)
  ... | true  | no ne = no λ (_ , e) → ne e
  ... | false | _     = no λ (t , _) → t

  -- A positive count, from its not being none.
  pos-tot : ∀ {n} → (n ≡ 0 → ⊥) → Σ ℕ λ k → n ≡ suc k
  pos-tot {zero} nz = ⊥-elim (nz refl)
  pos-tot {suc k}  _  = k , refl

  -- No routes at all, none through the lanes.
  lanes-of : ∀ {S} → tot S ≡ 0 → Flat.lanes S ≡ 0
  lanes-of {S} z = ℕP.n≤0⇒n≡0 (subst (Flat.lanes S ≤_) z
    (ℕP.≤-trans (ℕP.m≤n+m (Flat.lanes S) (Flat.outer S)) (ℕP.≤-trans (ℕP.m≤m+n _ (Flat.held S)) (ℕP.m≤m+n _ (Flat.parked S)))))

  -- A ROW OF THE LANES THE SOURCE MEETS IS SOME LANE'S EMIT.
  row-emit : ∀ rx₁ {q v rx₂} → Met M (rx₁ ++ (q , out (Ln v)) ∷ rx₂) → Σ Pos λ Q → LaneEmit Q (q , out (Ln v)) v
  row-emit rx₁ mt with lane-run mt
  ... | rs , pr , run , _ with bproj-mem pr (∈-++⁺ʳ rx₁ (here refl))
  ...   | y , refl , j with σ₃-lane (proj₁ (run-row∈ run j))
  ...     | Q , a , xo , _ , l , _ = Q , a , y , xo , refl , l

  -- A lane's value or completion lies before its step's over.
  lane-early : ∀ rx₁ {q x rx₂} → Met M (rx₁ ++ (q , out (Ln x)) ∷ rx₂) → Opens x → Early q
  lane-early rx₁ mt o with m-rows (proj₁ (run-row∈ mt (∈-++⁺ʳ rx₁ (here refl)))) tt
  ... | lane {w = w} y = early-inst [ sub w ] (fine-early o (Fit.fine lane-fit y))
    where
      fine-early : ∀ {x y′} → Opens x → Fine x y′ → Early y′
      fine-early o-value e = e
      fine-early o-done  e = e

  -- NO OVER OF A ROW'S INSTANT COMES BEFORE IT, if it lies before the over.
  over-early : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Early q
             → ∀ {k b n} → (k , out (Tg b (instEmit (mark over) n))) ∈ rx₁ → instantOf k ≡ instantOf q → ⊥
  over-early rx₁ {q} mt eq {k} i ik =
    let (v , ok′) = late (proj₁ (run-row∈ (run-prefix rx₁ mt) i))
        rq = cong (_∙ []) ik
        (qo , _) = eq (subst Valued rq v)
    in ≺-absurd {k} {q} (met-before rx₁ mt i) (≺-≼-≺ {q} {opos (rootOf q)} {k} qo (subst (λ r → opos r ≼ k) rq (⊑-≼ ok′)))

  -- The overs met before a row, of its instant, leave `Ov`.
  OvBefore : List Row → Pos → Set → Set
  OvBefore rx₁ q Ov = ∀ {k b n} → (k , out (Tg b (instEmit (mark over) n))) ∈ rx₁ → instantOf k ≡ instantOf q → Ov

  -- And the scan is live past them.
  Live? : List Row → Set → Set
  Live? rx₁ Ov = Flat.spent (St rx₁) ≡ false ⊎ Ov → Flat.spent (St rx₁) ≡ false

  postulate
    -- IN A QUEUED LANE'S SUBSCRIBE BURST, a route an ended lane handed on
    -- (`held`) holds it.  Route: a queued lane subscribes at an earlier
    -- lane's end; follow the chain of such ends down to one outside its
    -- own lane's burst (a lane subscribed at its value never ends in its
    -- burst while a later value is queued), whose count is positive and
    -- whose `laneDone` hands it to `held`; every row between lies under
    -- that end, a row of a lane of the chain, none of which cuts `held`.
    lane-queued : ∀ rx₁ {y v rx₂} (Ov : Set) → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
                → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → ¬ sub-at xo l ≡ Q ⊕ [ ix 1 ] → Sync (sub-at xo l) y
                → Carried (out v) → OvBefore rx₁ (y ⊕ [ sub LS.J ]) Ov → Live? rx₁ Ov → ¬ Ex cs′ (y ⊕ [ sub LS.J ])
                → Σ ℕ λ k → tot (St rx₁) ≡ suc k

  -- A projection keeps nothing of another branch's last row.
  bproj-init : ∀ {b} {h : IE A → IE B} {J} rx {q e rs} → BProj b h J (rx ++ (q , e) ∷ []) rs → brTag b e ≡ nothing → BProj b h J rx rs
  bproj-init {b = b} [] (keep BProj.[]) nl = ⊥-elim (tagged b nl)
  bproj-init []       (drop _ BProj.[]) _  = BProj.[]
  bproj-init (_ ∷ rx) (keep pr)          nl = keep (bproj-init rx pr nl)
  bproj-init (_ ∷ rx) (drop t pr)        nl = drop t (bproj-init rx pr nl)

  -- A branch's row met is a row of its projection, and back.
  bproj-in : ∀ {b} {h : IE A → IE B} {J rx rs k v} → BProj b h J rx rs → (k , out (Tg b v)) ∈ rx
           → Σ Pos λ y → Σ (IE A) λ x → k ≡ y ⊕ [ sub J ] × v ≡ h x × (y , out x) ∈ rs
  bproj-in (keep pr) (here refl) = _ , _ , refl , refl , here refl
  bproj-in (keep pr) (there i) = let (y , x , e₁ , e₂ , j) = bproj-in pr i in y , x , e₁ , e₂ , there j
  bproj-in {b = b} (drop nl pr) (here refl) = ⊥-elim (tagged b nl)
  bproj-in (drop nl pr) (there i) = bproj-in pr i

  bproj-out : ∀ {b} {h : IE A → IE B} {J rx rs y e} → BProj b h J rx rs → (y , e) ∈ rs
            → Σ (IE A) λ x → e ≡ out x × (y ⊕ [ sub J ] , out (Tg b (h x))) ∈ rx
  bproj-out (keep pr) (here refl) = _ , refl , here refl
  bproj-out (keep pr) (there j) = let (x , e , i) = bproj-out pr j in x , e , there i
  bproj-out (drop _ pr) j = let (x , e , i) = bproj-out pr j in x , e , there i

  -- The real flatMap's outer holds each outer row once.
  ro-inj : ∀ r r′ → ro-at r ≡ ro-at r′ → r ≡ r′
  ro-inj r r′ e = ⊕-injˡ r r′ (⊕-injˡ (r ⊕ [ sub q₀ ]) (r′ ⊕ [ sub q₀ ]) (⊕-injˡ ((r ⊕ [ sub q₀ ]) ⊕ [ ix 1 ]) ((r′ ⊕ [ sub q₀ ]) ⊕ [ ix 1 ])
                    (trans (rw r) (trans e (sym (rw r′))))))
    where
      q₀ : Pos
      q₀ = p₀₀ ⊕ [ ix 1 ]

      rw : ∀ x → ((x ⊕ [ sub q₀ ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] ≡ ro-at x
      rw x = trans (⊕-assoc (x ⊕ [ sub q₀ ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc x [ sub q₀ ] (ix 1 ∷ ix 0 ∷ []))

  -- IN THE BURST OF A LANE SUBSCRIBED AT ITS OUTER VALUE, the outer's
  -- route of that value holds it: the outer meets nothing past the value
  -- before the burst does, and the closer's `outerDone` lies past
  -- everything under the value (`simultaneous.CloseDone`).
  lane-room : ∀ rx₁ {y v rx₂} (Ov : Set) → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
            → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → sub-at xo l ≡ Q ⊕ [ ix 1 ] → Sync (sub-at xo l) y
            → OvBefore rx₁ (y ⊕ [ sub LS.J ]) Ov → Live? rx₁ Ov → ¬ Ex cs′ (y ⊕ [ sub LS.J ])
            → Σ ℕ λ k → tot (St rx₁) ≡ suc k
  lane-room rx₁ {y} {v} {rx₂} Ov mt {a = a} xo l sq sy ovf res nx with ro-row xo
  ... | r , n , σr , refl = pos-tot λ z₀ → met-open rx₁ mt σr rJ λ oa →
          let (_ , t) = outer-hold rx₁ Ov mt ovf res nod (cv oa) in 0≢suc (trans (sym z₀) t)
    where
      q₀ : Pos
      q₀ = p₀₀ ⊕ [ ix 1 ]

      Y : Pos
      Y = y ⊕ [ sub LS.J ]

      0≢suc : ∀ {k} → 0 ≡ suc k → ⊥
      0≢suc ()

      ws : Path
      ws = proj₁ (inside-⊑ (sub-at xo l) y (proj₁ sy))

      zs′ : Path
      zs′ = ix 1 ∷ ix 0 ∷ ix 1 ∷ ws L.++ [ sub LS.J ]

      Y₁ : Y ≡ ro-at r ⊕ (ix 1 ∷ ws L.++ [ sub LS.J ])
      Y₁ = trans (cong (_⊕ [ sub LS.J ]) (trans (proj₂ (inside-⊑ (sub-at xo l) y (proj₁ sy))) (cong (_⊕ ws) sq)))
             (trans (⊕-assoc ((ro-at r) ⊕ [ ix 1 ]) ws [ sub LS.J ]) (⊕-assoc (ro-at r) [ ix 1 ] (ws L.++ [ sub LS.J ])))

      Yr : Y ≡ r ⊕ (sub q₀ ∷ zs′)
      Yr = trans Y₁ (⊕-assoc r (sub q₀ ∷ ix 1 ∷ ix 0 ∷ []) (ix 1 ∷ ws L.++ [ sub LS.J ]))

      rY : r ⊑ Y
      rY = sub q₀ ∷ zs′ , Yr

      rJ : (r ⊕ [ sub OS.J ]) ≺ Y
      rJ = ≺-trans {r ⊕ [ sub OS.J ]} {ro-at r} {Y} (J≺ro r) (subst (ro-at r ≺_) (sym Y₁) (≺-ext (ro-at r) (ws L.++ [ sub LS.J ])))

      nod : ∀ {k n} → M k (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → k ≺ Y → instantOf k ≡ instantOf Y → ⊥
      nod mk kY _ with close-sent mk
      ... | c′ , w′ , σk , refl =
        ≺-absurd {c′ ⊕ [ sub w′ ]} {Y} kY (subst (_≺ (c′ ⊕ [ sub w′ ])) (sym Yr) (CD.below-done σr (proj₁ σk) q₀ zs′ w′))

      -- Past the value, the outer meets nothing before the burst.
      none-past : ∀ rs₁ {x′} rs₂ → BProj outerB (opening {A} {B}) OS.J rx₁ (rs₁ ++ (r , out x′) ∷ rs₂)
                → Met σ₁ (rs₁ ++ (r , out x′) ∷ rs₂) → rs₂ ≡ []
      none-past rs₁ []             _  _  = refl
      none-past rs₁ ((k , e) ∷ rs₃) pr rσ = ⊥-elim (≺-absurd {k ⊕ [ sub OS.J ]} {Y} kY Yk)
        where
          rk : r ≺ k
          rk with run-tail rs₁ rσ
          ... | _ ∷ᴿ rn = run-after rn (here refl)

          σk : σ₁ k e
          σk = proj₁ (run-row∈ rσ (∈-++⁺ʳ rs₁ (there (here refl))))

          kY : (k ⊕ [ sub OS.J ]) ≺ Y
          kY = met-before rx₁ mt (proj₂ (proj₂ (bproj-out pr (∈-++⁺ʳ rs₁ (there (here refl))))))

          nk : r ⊑ (k ⊕ [ sub OS.J ]) → ⊥
          nk rk′ with ⊑-snoc k rk′
          ... | inj₁ r⊑k = ≺-irrefl {r} (subst (r ≺_) (OuterRow.σ₁-lead σr σk r⊑k) rk)
          ... | inj₂ eq  = ≺-absurd {r} {k} rk (subst (k ≺_) (sym eq) (≺-ext k []))

          Yk : Y ≺ (k ⊕ [ sub OS.J ])
          Yk = past-sub {r} {Y} {k ⊕ [ sub OS.J ]} rY (≺→≼ {r} {k ⊕ [ sub OS.J ]} (≺-trans {r} {k} {k ⊕ [ sub OS.J ]} rk (≺-ext k []))) nk

      cv : Any (OpenMark (ro-at r)) rx₁
         → ∀ {rs′} → BProj outerB (opening {A} {B}) OS.J (rx₁ ++ (Y , out (Ln v)) ∷ []) rs′ → Met σ₁ rs′
         → Σ _ λ rs → BProj outerB (opening {A} {B}) OS.J rx₁ rs × Σ ℕ λ k → cnt rs ≡ (nameOf Y , suc k)
      cv oa pr′ rσ with find oa
      ... | _ , xi , (_ , r′ , _ , _ , eq , refl) with ro-inj r r′ eq
      ...   | refl with bproj-in (bproj-init rx₁ pr′ refl) xi
      ...     | y′ , x′ , e₁ , _ , j with ⊕-injˡ r y′ e₁
      ...       | refl with ∈-∃++ j
      ...         | rs₁ , rs₂ , refl with none-past rs₁ rs₂ (bproj-init rx₁ pr′ refl) rσ
      ...           | refl with InvAt.func I₁ (proj₁ (proj₁ (run-row∈ rσ (∈-++⁺ʳ rs₁ (here refl))))) (proj₁ σr)
      ...             | refl =
        let (k , cov) = Held.covered H₁ (σ₁-run rσ) rs₁ [] refl c-value (λ e → nx (subst (Ex cs′) (sym Yr) (ex-below (sub q₀ ∷ zs′) e)))
        in _ , bproj-init rx₁ pr′ refl , k
         , trans (from-++ r₀ rs₁ ((r , out (instEmit (value a) n)) ∷ [])) (trans cov (cong (_, suc k) (cong nm (sym (trans (cong rootOf Yr) (rootOf-ext r (sub q₀ ∷ zs′)))))))

  -- IN A LANE'S OWN SUBSCRIBE BURST, a route of the outer value that
  -- started the lane holds it, or, for a lane rxjs queued, a route an
  -- ended lane handed on (`held`).
  lane-burst : ∀ rx₁ {y v rx₂} (Ov : Set) → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
             → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → Sync (sub-at xo l) y → Carried (out v)
             → OvBefore rx₁ (y ⊕ [ sub LS.J ]) Ov → Live? rx₁ Ov → ¬ Ex cs′ (y ⊕ [ sub LS.J ])
             → Σ ℕ λ k → tot (St rx₁) ≡ suc k
  lane-burst rx₁ Ov mt {Q} xo l sy car ovf res nx with sub-at xo l ≟ᵖ (Q ⊕ [ ix 1 ])
  ... | yes sq = lane-room rx₁ Ov mt xo l sq sy ovf res nx
  ... | no nq  = lane-queued rx₁ Ov mt xo l nq sy car ovf res nx

  -- A LANE'S STOP ENDS A ROUTE IT COUNTS: the lane's count is its
  -- program's, whose stops end a route it holds.
  lane-exact : ∀ {q a} → RO q (out a) → ∀ {rs} → Met (RV.Lane op q a) rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
             → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
  lane-exact xo mt r₁ r₂ refl = Counts.stp (lane-counts-own xo (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))) r₁ (pre r₁ r₂ mt)

  -- PAST ITS BURST, A VALUE A LANE CARRIES FINDS A ROUTE OF ITS INSTANT
  -- the lane counts, unless exempt: its program's rows do.
  lane-covered : ∀ {q a} (xo : RO q (out a)) → ∀ {rs} → Met (RV.Lane op q a) rs → ∀ r₁ {y v} r₂ → rs ≡ r₁ ++ (y , out v) ∷ r₂
               → (l : RV.Lane op q a y (out v)) → Carried (out v) → ¬ Sync (sub-at xo l) y → ¬ Ex cs y → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  lane-covered xo mt r₁ r₂ refl l c ns nx = Counts.cov (lane-counts-own xo l) r₁ (pre r₁ r₂ mt) c [ ns , nx ]′

  -- A LANE COUNTS NOTHING BEFORE ITS `laneStart`: a begin of it would
  -- follow a `laneStart` of it, and it starts once.
  start-own : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q n c} → LaneEmit q x (instEmit (mark laneStart) n) → OC q xs c
            → proj₂ c ≡ 0
  start-own xs {rest = rest} mt {q} (a , y , xo , refl , l) oc = aux oc (λ i lu → no-begin i lu)
    where
      no-begin : ∀ {u n′} → u ∈ xs → LaneEmit q u (instEmit (mark begin) n′) → ⊥
      no-begin {u} i lu with ∈-∃++ i
      ... | a₁ , b₁ , refl with find (started a₁ (subst (Met M) (++-assoc a₁ (u ∷ b₁) _) mt) lu tt (λ ()) (λ ()))
      ...   | _ , i₀ , (a′ , y₀ , n₀ , xo₀ , refl , l₀) with ro-func xo xo₀
      ...     | refl = ≺-irrefl {y ⊕ [ sub LS.J ]}
                  (subst (_≺ y ⊕ [ sub LS.J ]) (cong (_⊕ [ sub LS.J ]) (start-once xo l₀ l)) (met-before (a₁ ++ u ∷ b₁) mt (∈-++⁺ˡ i₀)))

      step : ∀ {c} v → proj₂ c ≡ 0 → (∀ {n′} → v ≡ instEmit (mark begin) n′ → ⊥) → proj₂ (count {B} c v) ≡ 0
      step (instEmit (mark begin) _) _ nb = ⊥-elim (nb refl)
      step (instEmit (mark stop) _)  z _  = cong (ℕ._∸ 1) z
      step (instEmit (mark over) _)  _ _  = refl
      step (instEmit (value _) _)    z _  = z
      step (instEmit (mark outerOpen) _)    z _ = z
      step (instEmit (mark outerClose) _)   z _ = z
      step (instEmit (mark laneStart) _)    z _ = z
      step (instEmit (mark (laneDone _)) _) z _ = z
      step (instEmit (mark burstEnd) _)     z _ = z
      step (instEmit (mark outerDone) _)    z _ = z
      step (instEmit (mark subscribed) _)   z _ = z
      step (instEmit (mark completed) _)    z _ = z

      aux : ∀ {pre c} → OC q pre c → (∀ {u n′} → u ∈ pre → LaneEmit q u (instEmit (mark begin) n′) → ⊥) → proj₂ c ≡ 0
      aux oc[] _ = refl
      aux (oc-out oc _) nb = aux oc (λ i → nb (∈-++⁺ˡ i))
      aux (oc-in {p₀} {_} {x₀} {v} oc l′) nb =
        step v (aux oc (λ i → nb (∈-++⁺ˡ i))) (λ e → nb (∈-++⁺ʳ p₀ (here refl)) (subst (LaneEmit q x₀) e l′))

  -- PAST ITS BURST A LANE COUNTS A ROUTE OF ITS ROW'S INSTANT.
  lane-own : ∀ rx₁ {y v rx₂} → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
           → ∀ {Q a} (xo : RO Q (out a)) (l : RV.Lane op Q a y (out v)) → ¬ Sync (sub-at xo l) y → Carried (out v)
           → ¬ Ex cs′ (y ⊕ [ sub LS.J ]) → ∀ {c} → OC Q rx₁ c → Σ ℕ λ k → c ≡ (nameOf y , suc k)
  lane-own rx₁ {y} {v} mt {Q} {a} xo l ns car nx oc =
    let (k , e) = lane-covered xo (own-snoc rx₁ mt xo oc (a , y , xo , refl , l)) (lane-rows oc) [] refl l car ns
                    (λ ex → nx (there (there (there (there (there (ex-ext [ sub LS.J ] ex)))))))
    in k , trans (sym (cnt-lane oc)) e

  -- A LANE'S STOP ENDS A ROUTE OF ITS OWN INSTANT THE LANE COUNTS.
  stop-own : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q n c} → LaneEmit q x (instEmit (mark stop) n) → OC q xs c
           → proj₁ c ≡ nameOf (proj₁ x) × ¬ proj₂ c ≡ 0
  stop-own xs mt {q} {n} le@(a , y , xo , refl , l) oc =
    trans (sym (cong proj₁ c≡)) (trans name (cong nm (rootOf-ext y [ sub LS.J ]))) ,
    λ z → 0≢suc (trans (sym z) (trans (sym (cong proj₂ c≡)) (proj₂ (lane-exact xo rn (lane-rows oc) [] refl))))
    where
      rn : Met (RV.Lane op q a) (lane-rows oc ++ [ (y , out (instEmit (mark stop) n)) ])
      rn = own-snoc xs mt xo oc le

      c≡ = cnt-lane oc

      0≢suc : ∀ {k} → 0 ≡ suc k → ⊥
      0≢suc ()

      name : proj₁ (cnt (lane-rows oc)) ≡ nameOf y
      name with idle-row (lane-idle-own xo) (lane-rows oc) rn
      ... | inj₂ e = e
      ... | inj₁ z = ⊥-elim (0≢suc (trans (sym z) (proj₂ (lane-exact xo rn (lane-rows oc) [] refl))))

  done-live : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q kd n} → LaneEmit q x (instEmit (mark (laneDone kd)) n) → AC.Live [] xs q
  done-live xs mt le = live-of xs mt le (done-started xs mt le)

  -- THE LANES COUNTER KEEPS WHAT EACH LIVE LANE HOLDS OF ITS INSTANT
  -- (`simultaneous.LaneFloor`), read at the instant of the row met next.
  lanes-floor : ∀ rx₁ {z e rx₂} (Ov : Set) → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {Q c} → AC.Live [] rx₁ Q → OC Q rx₁ c
              → proj₁ c ≡ nameOf z → ¬ proj₂ c ≡ 0 → OvBefore rx₁ z Ov → Live? rx₁ Ov → ¬ Flat.lanes (St rx₁) ≡ 0
  lanes-floor rx₁ {z} Ov mt lv oc nm′ nz ovf res = F.floor lv oc nm′ nz hov
    where
      open Inst rx₁ mt using (In; row∈; begin-name; name-begin; in-after; in-root; in-name)

      sm = split-met rx₁ mt

      module F = Floor.Run′ {B} op Own (LaneMark laneStart) DoneMark act LaneEmit rx₁ (nameOf z) (λ x → In (proj₁ x))
        (λ {c} → end-free rx₁ mt {c})
        (λ xs k v ys eq κ → κ (lane-emit rx₁ mt (in-r₁ rx₁ xs _ ys eq)))
        (λ { (_ , y , _ , eq , _) → y ⊕ [ sub LS.J ] , eq })
        (λ {q} {q′} {x} {v} {v′} → emit-one {q} {q′} {x} {v} {v′})
        (λ { (a , y , n , xo , eq , l) → n , a , y , xo , eq , l })
        (λ { {kd = kd} {n = n} (a , y , xo , eq , l) → kd , a , y , n , xo , eq , l })
        (λ xs k b kd n ys eq → done-laneB (row∈ (in-r₁ rx₁ xs _ ys eq)))
        (λ xs x ys eq le → lane-live xs (sm xs x ys eq) le tt (λ ()) (λ ()))
        (λ xs x ys eq le → done-live xs (sm xs x ys eq) le)
        (λ xs x ys eq → done-told rx₁ mt xs x ys eq)
        (λ xs x ys eq → start-own xs (sm xs x ys eq))
        (λ xs x ys eq ik le o → let (cn , nz′) = stop-own xs (sm xs x ys eq) le o in trans cn (in-name ik) , nz′)
        (λ xs x ys eq ik le o → Sum.map₂ (λ cn → trans cn (in-name ik)) (next-idle xs (sm xs x ys eq) le o))
        (λ xs k b n ys eq → begin-name (in-r₁ rx₁ xs _ ys eq))
        (λ xs k b ys eq → name-begin (in-r₁ rx₁ xs _ ys eq))
        (λ xs x ys eq a → fwd xs x ys eq (find a))
        (λ r i → in-root r i)

      fwd : ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys → (Σ Row λ u → u ∈ xs × In (proj₁ u)) → In (proj₁ x)
      fwd xs x ys eq (u , ua , iu) = in-after xs ys eq ua iu

      hov : Any F.OverIn rx₁ → Flat.spent (St rx₁) ≡ false
      hov a with find a
      ... | _ , ua , iu , k , b , n , refl = res (inj₂ (ovf ua iu))

  -- A LANE IS LIVE AT EACH OF ITS CARRIED ROWS: started, not done, not
  -- cut.
  lane-alive : ∀ rx₁ {y v rx₂} → Met M (rx₁ ++ (y ⊕ [ sub LS.J ] , out (Ln v)) ∷ rx₂)
             → ∀ {Q a} → RO Q (out a) → RV.Lane op Q a y (out v) → Carried (out v) → AC.Live [] rx₁ Q
  lane-alive rx₁ mt xo l c-value = lane-live rx₁ mt (_ , _ , xo , refl , l) tt (λ ()) (λ ())
  lane-alive rx₁ mt xo l c-stop  = lane-live rx₁ mt (_ , _ , xo , refl , l) tt (λ ()) (λ ())
  lane-alive rx₁ mt xo l c-over  = lane-live rx₁ mt (_ , _ , xo , refl , l) tt (λ ()) (λ ())
  lane-alive rx₁ mt xo l c-done  = lane-live rx₁ mt (_ , _ , xo , refl , l) tt (λ ()) (λ ())

  -- A ROW OF A LANE'S FINDS A ROUTE: in the lane's burst, or past it the
  -- lane's own, which the lanes counter holds.
  lane-carried : ∀ rx₁ {q x rx₂} (Ov : Set) → Met M (rx₁ ++ (q , out (Ln x)) ∷ rx₂) → Carried (out x)
               → OvBefore rx₁ q Ov → Live? rx₁ Ov → ¬ Ex cs′ q → Σ ℕ λ k → tot (St rx₁) ≡ suc k
  lane-carried rx₁ {q} {x} Ov mt car ovf res nx with row-emit rx₁ mt
  ... | Q , a , y , xo , refl , l with sync? (sub-at xo l) y
  ...   | yes sy = lane-burst rx₁ Ov mt xo l sy car ovf res nx
  ...   | no ns  = pos-tot λ z → oc-total Q rx₁ λ (c , oc) →
            let (k , c≡) = lane-own rx₁ mt xo l ns car nx oc
            in lanes-floor rx₁ Ov mt (lane-alive rx₁ mt xo l car) oc
                 (trans (cong proj₁ c≡) (cong nm (rootOf-ext y [ sub LS.J ]))) (λ e → 0≢suc (trans (sym e) (cong proj₂ c≡)))
                 ovf res (lanes-of z)
    where
      0≢suc : ∀ {k} → 0 ≡ suc k → ⊥
      0≢suc ()

  -- A LANE'S VALUE OR COMPLETION: no over of its instant comes first.
  lane-tot : ∀ rx₁ {q x rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (laneB , x)))) ∷ rx₂) → Opens x → ¬ Ex cs′ q
           → Σ ℕ λ k → tot (proj₁ (past op init rx₁)) ≡ suc k
  lane-tot rx₁ mt o = lane-carried rx₁ ⊥ mt (opens-carried o) (λ i ik → over-early rx₁ mt (lane-early rx₁ mt o) i ik) [ (λ f → f) , ⊥-elim ]′
    where
      opens-carried : ∀ {x} → Opens x → Carried (out x)
      opens-carried o-value = c-value
      opens-carried o-done  = c-done

  -- A LANE'S LIVE OVER.
  lane-over : ∀ rx₁ {q n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (laneB , instEmit (mark over) n)))) ∷ rx₂)
            → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
            → Σ ℕ λ k → tot (proj₁ (past op init rx₁)) ≡ suc k
  lane-over rx₁ mt sp = lane-carried rx₁ ⊤ mt c-over (λ _ _ → tt) (λ _ → sp)

  value-tot : ∀ rx₁ {q b x rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , x)))) ∷ rx₂) → Opens x → ¬ Ex cs′ q
            → Σ ℕ λ k → tot (proj₁ (past op init rx₁)) ≡ suc k
  value-tot rx₁ {b = laneB}  = lane-tot rx₁
  value-tot rx₁ {b = outerB} = outer-tot rx₁
  value-tot rx₁ {b = closeB} = close-tot rx₁

  over-tot : ∀ rx₁ {q b n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ rx₂)
           → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
           → Σ ℕ λ k → tot (proj₁ (past op init rx₁)) ≡ suc k
  over-tot rx₁ {b = laneB}  = lane-over rx₁
  over-tot rx₁ {b = outerB} = outer-over rx₁
  over-tot rx₁ {b = closeB} mt = ⊥-elim (close-over rx₁ mt)
