{-# OPTIONS --guardedness #-}

-- THE SCAN'S LANE COUNTER, AGAINST THE LANES THEMSELVES.  Each lane counts
-- its own routes and tells them in its `laneDone`, which the scan takes off
-- its counter; a cut empties it, a new instant or
-- an over restarts it.  So the counter is at most what the lanes started,
-- never done nor cut, hold of its instant (`lanes-live`): where it is not
-- empty, some such lane holds a route of it.  A live lane holding a route
-- waits on its own next row, so the lanes are idle where it is
-- (`live-idle`), and a live lane still shows a row before the lanes' end
-- (`live-row`).
module simultaneous.HeldLaneRoutes where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Properties using (++-assoc; map-++; foldl-++; ∷-injective)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻; ∈-map⁺)
open import Data.List.Relation.Unary.Any using (Any; here; there; any?) renaming (map to any-map)
open import Data.List.Relation.Unary.Any.Properties using (++⁻; ++⁺ˡ)
open import Data.Unit using (tt)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; suc; _≤_)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; cong₂; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; connected; takeWhile; flatMap; of)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; end; skip; pin; Few; _≼_; _≺_; enter; hot; EmissionSet; Den; Ended; module Joining)
open import Data.Empty using (⊥; ⊥-elim)
open import denotation.Laws.Worlds using (InvAt; ⊕-injˡ; ⊕-identityʳ; full; ⊕-assoc)
open import denotation.Laws.Modulus using (entered-few; ≺-trans; ≺-ext; ≺-≼-≺; ≼-≺-≺; ≺→≼; ≼-or-≻; ≺-irrefl; ≼-refl; ≼-trans; ≼-split; ≺-absurd)
open import denotation.Laws.Truth.Connect.Cuts using (step≼; next≺)
open import denotation.Laws.Fold using (latest)
open import denotation.EmissionSet using (Reach; Dep; module Switch)
open import denotation.Laws.Count using (em; reach-down; child)
open import simultaneous.RealView using (module View; real-to; join-in; cutat-up; lane-at; lane-at₂; lane-fwd; lane-one; join-shows; kill-cut)
open import adequacy.LaneEnd using (join-end; done-over)
open import adequacy.Settle using (done-use)
open import simultaneous.LaneSite using (FoldOf; f-none; f-step; fold-map; Sited; lane-site)
open import simultaneous.HeldLanes using (lane-past; bproj-mem; bproj-memʰ; open-cut; open-routing)
open import simultaneous.Layers using (run-tail; run-after; run-++; cursor-snoc; pinby-vis) renaming (run-row to run-row∈)
open import simultaneous.HeldLim using (run-below)
import simultaneous.LaneStart as LaneStart
open import simultaneous.ColdIdle using (aft-or-in)
open import simultaneous.CombSent using (src-op; closing-mark)
open import simultaneous.InstEmit using (instEmit; mark; value; laneDone; laneStart; begin; burstEnd; outerOpen; valuesOf)
open import simultaneous.Project using (run-prefix)
open import denotation.EmissionSet using (Ev; Superseded; Seen; Work)
open import Data.Maybe using (just)
open import simultaneous.ScanCount using (rowKind; markAct; row-cut; markQue; row-open; past-queue; que-cut)
open import simultaneous.LaneCount using (kCut; kStart; module Count)
open import denotation.Read using (Visible; After; cursor; Run) renaming (_∷_ to _∷ᴿ_; [] to []ᴿ)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful)
open import simultaneous.SObs using (lone; module Elaborate; Flat; laneB; outerB; closeB; lanePart; burstPart)
open import Data.Bool using (Bool; T; not; true; false)
open import Data.Unit using (⊤)
open import denotation.Position using (last)
open import denotation.EmissionSet using (module Op; module TakeWhile)
open import denotation.Laws.Worlds using (world-after; ok-step)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.LaneLayers using (done-of)
open import simultaneous.LaneInnerEnd using (inner-ends)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.Shut using (r₀)
open import simultaneous.Relations using (Met; outs; outs-++; values)
open import simultaneous.LaneEpoch using (module Lanes)
open import simultaneous.Routed using (Held; Early; Placed; nameOf; cnt)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh; shows-ev)
open import denotation.Laws.Shows using (few-reach; ∈-stable)
open import simultaneous.HeldComb using (ev; init; past)
open import simultaneous.FlatLanes using (BProj; Tg; brTag; end-last; tagged; bproj-end) renaming (keep to bkeep; drop to bdrop)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldSrc using (module CombSrc; named-at)
open import simultaneous.HeldLanes using (module CombLanes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; marked; Out; Input; react; laneˢ; each; shareˢ; counted; framed; undone)

-- A JOINER'S END: its outer has ended there, and every lane run, past its
-- value and never cut.
join-done : ∀ {A B} op (f : A → Den B) (o : EmissionSet A) {y} → View.Join f o op y end
          → Ended o y × (∀ {q a} → o q (out a) → View.Runs f o op q → q ≺ y → ¬ View.CutAt f o op q y → Ended (View.Lane f o op q a) y)
join-done op f o {y} r =
  let jd = join-end op f o r
  in done-over op jd , λ x ru qy nc → done-use op jd x ru qy λ {q′} kl →
       [ (λ le → le) , (λ lt → ⊥-elim (nc (kill-cut op f o kl lt))) ]′ (≼-or-≻ y q′)

-- A SWITCH'S END HAS A LAST VALUE PAST ANY BEFORE IT: the end's reach
-- lists every joiner row before it, each value's silent row among them, so
-- the latest of those values is there, and no later value supersedes it.
switch-last : ∀ {A B} (f : A → Den B) (o : EmissionSet A) {y} → Reach (Switch.JoinT f o) y end
            → ∀ {q a} → o q (out a) → q ≺ y
            → ¬ ¬ Σ Pos λ q* → Σ A λ a* → o q* (out a*) × q ≼ q* × ¬ Superseded o q* y
switch-last {A} f o {y} (ks , h) {q} {a} xo qy κ = latest V (y ⊕ [ ix 0 ]) (ks ++ [ y ]) λ
  { (inj₁ none) → none (listed xo qy) (q , refl , a , xo , ≼-refl {q}) (next≺ {q} {y} qy)
  ; (inj₂ (_ , (q* , refl , a* , xo* , qq*) , _ , mx)) →
      κ (q* , a* , xo* , qq* , λ (q′ , a′ , xo′ , q*q′ , q′y) →
        mx (listed xo′ q′y) (q′ , refl , a′ , xo′ , ≼-trans {q} {q*} {q′} qq* (≺→≼ {q*} {q′} q*q′)) (next≺ {q′} {y} q′y)
           (next≺ {q*} {q′} q*q′)) }
  where
    V : Pos → Set
    V z = Σ Pos λ k → z ≡ k ⊕ [ ix 0 ] × Σ A λ b → o k (out b) × q ≼ k

    listed : ∀ {k b} → o k (out b) → k ≺ y → (k ⊕ [ ix 0 ]) ∈ ks ++ [ y ]
    listed {k} x ky = [ (λ lt → ∈-++⁺ˡ (h (Joining.val x) lt tt)) , (λ eq → ∈-++⁺ʳ ks (here eq)) ]′ (≼-split {k ⊕ [ ix 0 ]} {y} (step≼ {k} {y} ky))

-- Only a switch cuts.
cut-switch : ∀ {A B} op (f : A → Den B) (o : EmissionSet A) {q k} → View.CutAt f o op q k → op ≡ switchᶠ
cut-switch switchᶠ f o _ = refl
cut-switch (mergeᶠ _) f o ()
cut-switch exhaustᶠ f o ()

-- A row a projection kept is the scan's row of it.
bproj-in : ∀ {X : Set} {b J rx rs y} {x : IE X} → BProj b (λ v → v) J rx rs → (y , out x) ∈ rs → (y ⊕ [ sub J ] , out (Tg b x)) ∈ rx
bproj-in (bkeep pr)   (here refl) = here refl
bproj-in (bkeep pr)   (there i)   = there (bproj-in pr i)
bproj-in (bdrop _ pr) i           = there (bproj-in pr i)

tg-inj : ∀ {X : Set} {b} {x x′ : IE X} → _≡_ {A = Ev (Maybe (Input X))} (out (Tg b x)) (out (Tg b x′)) → x ≡ x′
tg-inj refl = refl

-- A projection is a function of the run it reads.
bproj-one : ∀ {X : Set} {b J rx rx′ rs rs′} → BProj {X} b (λ v → v) J rx rs → BProj b (λ v → v) J rx′ rs′ → rx ≡ rx′ → rs ≡ rs′
bproj-one {rx = []} {rx′ = _ ∷ _} _ _ ()
bproj-one {rx = _ ∷ _} {rx′ = []} _ _ ()
bproj-one {rx = []} {rx′ = []} {rs = []} {rs′ = []} _ _ _ = refl
bproj-one {rx = []} {rx′ = []} {rs = _ ∷ _} () _ _
bproj-one {rx = []} {rx′ = []} {rs′ = _ ∷ _} _ () _
bproj-one (bkeep {y} p) (bkeep {y′} p′) eq =
  let (hd , tl) = ∷-injective eq
  in cong₂ _∷_ (cong₂ _,_ (⊕-injˡ y y′ (cong proj₁ hd)) (cong out (tg-inj (cong proj₂ hd)))) (bproj-one p p′ tl)
bproj-one {b = b} (bkeep p) (bdrop t p′) eq = ⊥-elim (tagged b (trans (cong (λ r → brTag b (proj₂ r)) (proj₁ (∷-injective eq))) t))
bproj-one {b = b} (bdrop t p) (bkeep p′) eq = ⊥-elim (tagged b (trans (cong (λ r → brTag b (proj₂ r)) (sym (proj₁ (∷-injective eq)))) t))
bproj-one (bdrop _ p) (bdrop _ p′) eq = bproj-one p p′ (proj₂ (∷-injective eq))

-- A TAKE'S END LIES PAST ITS FAILING VALUE, or is its source's own, unfailed.
take-end : ∀ {X : Set} {H : Pos → Set} (keep : X → Bool) (d : Den X) (s : Pos) (iv : InvAt H s (enter d s)) {c}
         → enter (Op.takeWhile true keep d) s c end
         → (Σ Pos λ w → Σ X λ a → c ≡ w ⊕ [ last ] × enter (Op.takeWhile true keep d) s (w ⊕ [ ix 0 ]) (out a) × T (not (keep a)))
           ⊎ (enter d s c end × ¬ TakeWhile.Failed true keep (enter d s) c)
take-end keep d s iv (TakeWhile.stop x nk nf , _) = inj₁ (_ , _ , refl , TakeBack.up true keep d s iv (TakeWhile.fail x nk nf _) , nk)
take-end keep d s iv (TakeWhile.tend x nf , _)    = inj₂ (x , nf)

lane-end : ∀ m {Γ X} (keep : X → Bool) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ s → Ok (Hots ρ) s → ∀ {c}
         → enter (ev m (takeWhile true keep o) ρ) s c end
         → (Σ Pos λ w → Σ X λ a → c ≡ w ⊕ [ last ] × enter (ev m (takeWhile true keep o) ρ) s (w ⊕ [ ix 0 ]) (out a) × T (not (keep a)))
           ⊎ (enter (ev m o ρ) s c end × ¬ TakeWhile.Failed true keep (enter (ev m o ρ) s) c)
lane-end nothing  keep o ρ g s ok = take-end keep (ev nothing o ρ) s (inv-ev nothing o ρ g s ok)
lane-end (just n) keep o ρ g s ok = take-end keep (ev (just n) o ρ) s (inv-ev (just n) o ρ g s ok)

-- A TAKE'S ROWS ALL LIE BY ITS FAILING VALUE: none passes after it, and
-- it fails once.
take-before : ∀ {X : Set} (keep : X → Bool) (d : Den X) (s : Pos) → ∀ {k a k′ a′}
            → enter (Op.takeWhile true keep d) s k (out a) → T (not (keep a))
            → enter (Op.takeWhile true keep d) s k′ (out a′) → k′ ≼ k
take-before keep d s (TakeWhile.pass _ kp _ , _) nk _ = ⊥-elim (both kp nk)
  where
    both : ∀ {b} → T b → T (not b) → ⊥
    both {true}  _ ()
    both {false} () _
take-before keep d s (TakeWhile.fail {q = f} x _ nf _ , _) nk (TakeWhile.pass {q = q′} x′ _ nf′ , _) with ≼-or-≻ q′ f
... | inj₁ q′f = ≺→≼ {q′} {f ⊕ [ ix 0 ]} (≼-≺-≺ {q′} {f} {f ⊕ [ ix 0 ]} q′f (≺-ext f []))
... | inj₂ fq′ = ⊥-elim (nf′ (f , _ , x , nk , fq′))
take-before keep d s (TakeWhile.fail {q = f} x _ nf _ , _) nk (TakeWhile.fail {q = f′} x′ nk′ nf′ _ , _) with ≼-or-≻ f′ f
... | inj₂ ff′ = ⊥-elim (nf′ (f , _ , x , nk , ff′))
... | inj₁ f′f with ≼-split {f′} {f} f′f
...   | inj₁ lt   = ⊥-elim (nf (f′ , _ , x′ , nk′ , lt))
...   | inj₂ refl = ≼-refl {f ⊕ [ ix 0 ]}

lane-before : ∀ m {Γ X} (keep : X → Bool) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) (s : Pos) → ∀ {k a k′ a′}
            → enter (ev m (takeWhile true keep o) ρ) s k (out a) → T (not (keep a))
            → enter (ev m (takeWhile true keep o) ρ) s k′ (out a′) → k′ ≼ k
lane-before nothing  keep o ρ s = take-before keep (ev nothing o ρ) s
lane-before (just n) keep o ρ s = take-before keep (ev (just n) o ρ) s

module LaneRoutes (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
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

  St : List Row → Flat Pos
  St r = proj₁ (past op init r)

  -- A row of lane `q`'s, as the scan's source meets it, with its emit.
  LaneEmit : Pos → Row → IE B → Set
  LaneEmit q x v = Σ A λ a → Σ Pos λ y → RO q (out a) × x ≡ (y ⊕ [ sub LS.J ] , out (Ln v)) × RV.Lane op q a y (out v)

  -- LANE `q`'S OWN COUNT along rows the source met, read forward.
  open Lanes {B} op Own (LaneMark laneStart) DoneMark act LaneEmit using (OC; oc[]; oc-in; oc-out; module Run)

  -- A lane's inner, ahead of its take.
  inner : A → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner a = flatMap (mergeᶠ nothing) (λ k → shareˢ (g a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  -- LANE `q`'S ROWS A PREFIX MET, as the lane shows them, in order.
  lane-rows : ∀ {q xs c} → OC q xs c → List (Pos × Ev (IE B))
  lane-rows oc[] = []
  lane-rows (oc-in {v = v} oc (_ , y , _)) = lane-rows oc ++ [ (y , out v) ]
  lane-rows (oc-out oc _) = lane-rows oc

  -- They hold no end,
  lane-rows-end : ∀ {q xs c} (oc : OC q xs c) {k} → (k , end) ∈ lane-rows oc → ⊥
  lane-rows-end oc[] ()
  lane-rows-end (oc-in oc _) i with ∈-++⁻ (lane-rows oc) i
  ... | inj₁ i′ = lane-rows-end oc i′
  ... | inj₂ (here ())
  lane-rows-end (oc-out oc _) i = lane-rows-end oc i

  -- and the lane's count is theirs.
  cnt-lane : ∀ {q xs c} (oc : OC q xs c) → cnt (lane-rows oc) ≡ c
  cnt-lane oc[] = refl
  cnt-lane (oc-in {v = v} oc (_ , y , _)) =
    trans (cong (L.foldl count r₀) (trans (cong (L.map proj₂) (outs-++ (lane-rows oc) [ (y , out v) ])) (map-++ proj₂ (outs (lane-rows oc)) [ (y , v) ])))
          (trans (foldl-++ count r₀ (values (lane-rows oc)) [ v ]) (cong (λ r → count r v) (cnt-lane oc)))
  cnt-lane (oc-out oc _) = cnt-lane oc

  -- The run holds no end short of its last row.
  end-free : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {c} → (c , end) ∈ rx₁ → ⊥
  end-free rx₁ {z} {e} {rx₂} mt i with ∈-∃++ i
  ... | a₁ , b₁ , refl = nonempty b₁ (end-last I-M a₁ (subst (Met M) (++-assoc a₁ _ ((z , e) ∷ rx₂)) mt))
    where
      nonempty : ∀ b₂ → b₂ ++ (z , e) ∷ rx₂ ≡ [] → ⊥
      nonempty []      ()
      nonempty (_ ∷ _) ()

  -- EVERY LANE ROW THE SCAN MEETS IS SOME LANE'S EMIT.
  lane-emit : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {k v} → (k , out (Tg laneB v)) ∈ rx₁
            → Σ Pos λ q → LaneEmit q (k , out (Tg laneB v)) v
  lane-emit rx₁ mt i with lane-run mt
  ... | rs , pr , run , _ with bproj-mem pr (∈-++⁺ˡ i)
  ...   | y , refl , j with σ₃-lane (proj₁ (run-row∈ run j))
  ...     | q , a , xo , _ , l , _ = q , a , y , xo , refl , l

  -- AN EMIT IS ONE LANE'S.
  emit-one : ∀ {q q′ x v v′} → LaneEmit q x v → LaneEmit q′ x v′ → q ≡ q′
  emit-one (_ , y , xo , refl , l) (_ , y′ , xo′ , e , l′) with ⊕-injˡ y y′ (cong proj₁ e)
  ... | refl = lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo xo′ l l′

  -- NOTHING OF A LANE FOLLOWS ITS `laneDone`: its take fails there, and
  -- no row of one subscription lies under another.
  done-last : ∀ {q a yd y kd n v} → RO q (out a) → RV.Lane op q a yd (out (instEmit (mark (laneDone kd)) n)) → RV.Lane op q a y (out v)
            → (yd ⊕ [ sub LS.J ]) ≺ (y ⊕ [ sub LS.J ]) → ⊥
  done-last {q} {a} {yd} {y} xo ld l lt with lane-at₂ op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo ld l
  ... | s , oks , rd , ry with ≼-split {y} {yd} (lane-before m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) s rd tt ry)
  ...   | inj₂ refl = ≺-irrefl {y ⊕ [ sub LS.J ]} lt
  ...   | inj₁ y≺yd with child {y} {yd} (sub LS.J) y≺yd
  ...     | inj₂ lt′ = ≺-irrefl {y ⊕ [ sub LS.J ]}
                (≺-trans {y ⊕ [ sub LS.J ]} {yd} {y ⊕ [ sub LS.J ]} lt′ (≺-trans {yd} {yd ⊕ [ sub LS.J ]} {y ⊕ [ sub LS.J ]} (≺-ext yd {sub LS.J} []) lt))
  ...     | inj₁ ([] , e) = ≺-irrefl {y} (subst (y ≺_) (trans e (⊕-identityʳ y)) y≺yd)
  ...     | inj₁ (_ ∷ _ , refl) = InvAt.flat (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) ry rd

  -- NOTHING OF A LANE IS MET PAST ITS `laneDone`.
  done-final : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v → AC.DoneIn [] xs q → ⊥
  done-final xs mt (a , y , xo , refl , l) dn with find dn
  ... | _ , i , (_ , a′ , yd , n , xo′ , refl , ld) with ro-func xo xo′
  ...   | refl = done-last xo ld l (met-before xs mt i)

  -- AN `outerOpen` THE SCAN MEETS IS AN OUTER VALUE'S, at the source's
  -- reading of the outer's row.
  open-row : ∀ {rx} → Met M rx → ∀ {k b n} → (k , out (just (inj₁ (b , instEmit (mark outerOpen) n)))) ∈ rx
           → Σ Pos λ c → Σ A λ a → Σ _ λ n′ → σ₁ c (out (instEmit (value a) n′)) × k ≡ c ⊕ [ sub OS.J ] × b ≡ outerB × n ≡ n′
  open-row mt {b = laneB} i with lane-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , σc , _ = ⊥-elim (σ₃-open σc)
  open-row mt {b = closeB} i with close-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , cx , _ = ⊥-elim (closing-mark (close-marks cx) (λ ()) (λ ()))
  open-row {rx} mt {b = outerB} i with OS.run′ (subst (λ d → Run (enter d P) nothing rx) (src-op tk env′ m) mt)
  ... | rs , pr , run , _ with bproj-memʰ pr i
  ...   | c′ , instEmit (value a) n′ , refl , j , refl = c′ , a , n′ , proj₁ (run-row∈ run j) , refl , refl , refl
  ...   | c′ , instEmit (mark _) _ , refl , j , refl = ⊥-elim (open-routing (Held.routing H₁ (proj₁ (proj₁ (run-row∈ run j)))))

  module QL = Count _≟ᵖ_ (rowKind markQue op) (λ q → Σ A λ a → RO q (out a)) OpenMark (LaneMark laneStart) que

  -- WITH A BOUNDED MERGE'S QUEUE UP, A VALUE THE SCAN MET OPENED HAS NOT
  -- STARTED: the queue counts the opens met less the starts.
  queue-live : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ¬ que r₁ ≡ 0
             → ¬ ¬ Σ Pos λ q → Σ A λ a → RO q (out a) × Any (OpenMark q) r₁ × ¬ Any (LaneMark laneStart q) r₁
  queue-live bd r₁ mt nz κ =
    QL.alive r₁ (λ xs y ys eq → past-queue op init xs y (no-end r₁ mt xs eq)) refl
      (λ { (_ , _ , _ , _ , refl , _) → refl }) (λ _ x _ _ kc → que-cut op x kc) st-new (λ _ _ _ _ → start-one)
      (λ xs x ys eq kx κ′ → start-live r₁ mt xs x ys eq kx λ (q , lm , (a , xo , _) , rest) → κ′ (q , lm , (a , xo) , rest))
      nz λ (q , (a , xo) , oi , nd) → κ (q , a , xo , oi , nd)
    where
      st-new : ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markQue op x ≡ kStart
             → ¬ ¬ Σ Pos λ q → (Σ A λ a → RO q (out a)) × OpenMark q x × ¬ Any (OpenMark q) xs
      st-new xs x ys eq kx κ′ with row-open op bd x kx
      ... | k′ , b , n , refl with open-row (run-prefix r₁ mt) (in-r₁ r₁ xs _ ys eq)
      ...   | c , a , n′ , σc , refl , refl , refl = κ′ (ro-at c , (a , ro-of σc) , (a , c , n′ , σc , refl , refl) , unmet)
        where
          ro-inj : ∀ c c′ → ro-at c ≡ ro-at c′ → c ≡ c′
          ro-inj c c′ e = ⊕-injˡ c c′ (⊕-injˡ (c ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) (c′ ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) (⊕-injˡ ((c ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) ⊕ [ ix 1 ]) ((c′ ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) ⊕ [ ix 1 ]) (trans (sym (asc c)) (trans e (asc c′)))))
            where
              asc : ∀ x → ro-at x ≡ ((x ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]
              asc x = sym (trans (⊕-assoc (x ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc x [ sub (p₀₀ ⊕ [ ix 1 ]) ] (ix 1 ∷ ix 0 ∷ [])))
          unmet : ¬ Any (OpenMark (ro-at c)) xs
          unmet oi with find oi
          ... | _ , i , (_ , c′ , _ , _ , e , refl) with ro-inj c c′ e
          ...   | refl = ≺-irrefl {c ⊕ [ sub OS.J ]} (met-before xs (split-met r₁ mt xs _ ys eq) i)

  -- A CUT THE SWITCH'S SCAN MEETS IS AN OUTER VALUE'S `outerOpen`, at the
  -- source's reading of the outer's row.
  cut-row : ∀ {rx} → Met M rx → ∀ {x} → x ∈ rx → rowKind markAct switchᶠ x ≡ kCut
          → Σ Pos λ c → Σ A λ a → Σ _ λ n → σ₁ c (out (instEmit (value a) n)) × proj₁ x ≡ c ⊕ [ sub OS.J ] × Σ _ λ v → M (c ⊕ [ sub OS.J ]) (out v)
  cut-row mt {k , out (just (inj₁ (b , instEmit (mark mk) n)))} i kc with open-cut mk kc
  ... | refl with open-row mt i
  ...   | c , a , _ , σc , refl , refl , refl = c , a , _ , σc , refl , _ , proj₁ (run-row∈ mt i)
  cut-row mt {_ , out (just (inj₁ (_ , instEmit (value _) _)))} i ()
  cut-row mt {_ , out (just (inj₂ _))} i ()
  cut-row mt {_ , out nothing} i ()
  cut-row mt {_ , end} i ()
  cut-row mt {_ , skip} i ()
  cut-row mt {_ , pin _} i ()

  -- A SWITCH'S ARRIVAL THE SCAN MEETS PAST A LANE'S START IS A LATER
  -- VALUE'S, before every lane row the scan meets next.
  switch-cut : op ≡ switchᶠ → ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q} → AC.CutIn [] r₁ q
             → Σ Pos λ q′ → Σ A λ a′ → RO q′ (out a′) × q ≺ q′ × (∀ {y b} → σ₃ y (out b) → z ≡ y ⊕ [ sub LS.J ] → q′ ≺ y)
  switch-cut op≡ r₁ {z} {e} {r₂} mt {q} (xs , ys , r≡ , si , cb) with find si | find cb
  ... | x₀ , i₀ , (a , y₀ , n , xo , refl , l) | xc , ic , kc with ∈-∃++ ic
  ...   | ys₁ , ys₂ , refl with cut-row (run-prefix r₁ mt) (subst (xc ∈_) (sym r≡) (∈-++⁺ʳ xs (∈-++⁺ʳ ys₁ (here refl))))
                               (subst (λ o′ → rowKind markAct o′ xc ≡ kCut) op≡ kc)
  ...     | c , a′ , n′ , σc , pc , v , mc = ro-at c , a′ , ro-of σc , q≺ , later
    where
      W : List Row
      W = (z , e) ∷ r₂

      eqL : r₁ ++ W ≡ (xs ++ ys₁) ++ xc ∷ (ys₂ ++ W)
      eqL = trans (cong (_++ W) r≡) (trans (++-assoc xs (ys₁ ++ xc ∷ ys₂) W)
              (trans (cong (xs ++_) (++-assoc ys₁ (xc ∷ ys₂) W)) (sym (++-assoc xs ys₁ (xc ∷ (ys₂ ++ W))))))

      x₀≺xc : (y₀ ⊕ [ sub LS.J ]) ≺ (c ⊕ [ sub OS.J ])
      x₀≺xc = subst ((y₀ ⊕ [ sub LS.J ]) ≺_) pc (met-before (xs ++ ys₁) {proj₁ xc} {proj₂ xc} {ys₂ ++ W} (subst (Met M) eqL mt) (∈-++⁺ˡ i₀))

      xc≺z : (c ⊕ [ sub OS.J ]) ≺ z
      xc≺z = subst (_≺ z) pc (met-before r₁ mt (subst (xc ∈_) (sym r≡) (∈-++⁺ʳ xs (∈-++⁺ʳ ys₁ (here refl)))))

      q≺y₀ : q ≺ y₀
      q≺y₀ = ≺-trans {q} {q ⊕ [ ix 1 ]} {y₀} (≺-ext q []) (proj₂ (subst (λ o′ → RV.Lane o′ q a y₀ (out (instEmit (mark laneStart) n))) op≡ l))

      q≺ : q ≺ ro-at c
      q≺ with ≼-or-≻ (ro-at c) q
      ... | inj₂ lt = lt
      ... | inj₁ le = ⊥-elim (≺-absurd {y₀ ⊕ [ sub LS.J ]} {c ⊕ [ sub OS.J ]} x₀≺xc
                        (≺-trans {c ⊕ [ sub OS.J ]} {ro-at c} {y₀ ⊕ [ sub LS.J ]} (J≺ro c)
                          (≼-≺-≺ {ro-at c} {q} {y₀ ⊕ [ sub LS.J ]} le (≺-trans {q} {y₀} {y₀ ⊕ [ sub LS.J ]} q≺y₀ (≺-ext y₀ [])))))

      later : ∀ {y b} → σ₃ y (out b) → z ≡ y ⊕ [ sub LS.J ] → ro-at c ≺ y
      later {y} σy refl with ≼-or-≻ y (ro-at c)
      ... | inj₂ lt = lt
      ... | inj₁ le with ≼-or-≻ (c ⊕ [ sub OS.J ]) y
      ...   | inj₁ xy = ⊥-elim (lane-in-outer op≡ σc σy xy le)
      ...   | inj₂ yx = ⊥-elim (≺-irrefl {c ⊕ [ sub OS.J ]} (≺-≼-≺ {c ⊕ [ sub OS.J ]} {y ⊕ [ sub LS.J ]} {c ⊕ [ sub OS.J ]} xc≺z
                          (lane-under σy (subst (λ d → enter d P (c ⊕ [ sub OS.J ]) (out v)) (src-op tk env′ m) mc) yx)))

  -- A lane's row before a row of the lanes, never cut by it, is the lanes'.
  -- (The later row is no timer: a timer's reach counts only rows before its root.)
  σ₃-before : ∀ {q a k b y e} → RO q (out a) → RV.Runs op q → RV.Lane op q a k (out b) → ¬ RV.CutAt op q y → k ≺ y → σ₃ y e
            → (∀ {r} → e ≡ pin r → ⊥) → σ₃ k (out b)
  σ₃-before {q} {a} {k} {b} {y} {e} xo rn l nc ky σy np =
    R-from (join-in op fL RO xo rn l (λ c → nc (cutat-up op fL RO {q} {k} {y} ky c)) tt
           , reach-down {q = y} {w = k} {e = e} {e₁ = out b}
               (proj₂ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σy))) ky (dep e np))
    , λ {c} ce → ≺→≼ {k} {c} (≺-≼-≺ {k} {y} {c} ky (proj₂ σy ce))
    where
      dep : ∀ e′ → (∀ {r} → e′ ≡ pin r → ⊥) → Dep y e′ k (out b)
      dep (pin r) np′ = ⊥-elim (np′ refl)
      dep (out _) _ = tt
      dep end _ = tt
      dep skip _ = tt

  -- No end, nor value, is a timer.
  end-pin : ∀ {r} → end {IE B} ≡ pin r → ⊥
  end-pin ()

  out-pin : ∀ {v : IE B} {r} → out v ≡ pin r → ⊥
  out-pin ()

  -- Two rows of one lane, in order, keep it under the lanes' tag: the
  -- earlier is not above the later, one subscription's rows lying flat.
  lane-J : ∀ {q a y₀ y e₀ e} → RO q (out a) → RV.Lane op q a y₀ e₀ → RV.Lane op q a y e → y₀ ≺ y
         → (y₀ ⊕ [ sub LS.J ]) ≺ (y ⊕ [ sub LS.J ])
  lane-J {q} {a} {y₀} {y} xo l₀ l y₀y with lane-at₂ op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l₀ l
  ... | s , oks , r₀ , r with child {y₀} {y} (sub LS.J) y₀y
  ...   | inj₂ lt = ≺-trans {y₀ ⊕ [ sub LS.J ]} {y} {y ⊕ [ sub LS.J ]} lt (≺-ext y {sub LS.J} [])
  ...   | inj₁ ([] , e) = ⊥-elim (≺-irrefl {y₀} (subst (y₀ ≺_) (trans e (⊕-identityʳ y₀)) y₀y))
  ...   | inj₁ (_ ∷ _ , refl) = ⊥-elim (InvAt.flat (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) r₀ r)

  -- Two rows of one lane keep their order under the lanes' tag.
  J-reflect : ∀ {q a y₁ y₂ e₁ e₂} → RO q (out a) → RV.Lane op q a y₁ e₁ → RV.Lane op q a y₂ e₂
            → (y₁ ⊕ [ sub LS.J ]) ≺ (y₂ ⊕ [ sub LS.J ]) → y₁ ≺ y₂
  J-reflect {y₁ = y₁} {y₂} xo l₁ l₂ lt with ≼-or-≻ y₂ y₁
  ... | inj₂ y₁y₂ = y₁y₂
  ... | inj₁ le with ≼-split {y₂} {y₁} le
  ...   | inj₂ refl = ⊥-elim (≺-irrefl {y₁ ⊕ [ sub LS.J ]} lt)
  ...   | inj₁ y₂y₁ = ⊥-elim (≺-absurd {y₁ ⊕ [ sub LS.J ]} {y₂ ⊕ [ sub LS.J ]} lt (lane-J xo l₂ l₁ y₂y₁))

  -- A row of the met run before a row it met there is met before it.
  in-prefix : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {u} → u ∈ xs ++ x ∷ rest → proj₁ u ≺ proj₁ x → u ∈ xs
  in-prefix xs {x} mt {u} i ux with ∈-++⁻ xs i
  ... | inj₁ i′ = i′
  ... | inj₂ (here refl) = ⊥-elim (≺-irrefl {proj₁ x} ux)
  ... | inj₂ (there i′) with run-tail xs mt
  ...   | _ ∷ᴿ rn = ⊥-elim (≺-absurd {proj₁ u} {proj₁ x} ux (run-after rn i′))

  opaque
    -- A LANE'S ROW BEFORE A ROW OF IT THE LANES' RUN HOLDS IS IN THAT RUN.
    catch-run : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {q a y v k b} → RO q (out a)
              → RV.Lane op q a y (out v) → (y , out v) ∈ rs → RV.Lane op q a k (out b) → k ≺ y
              → (k ⊕ [ sub LS.J ] , out (Ln b)) ∈ rx
    catch-run {rx} {rs} pr run {q} {a} {y} {v} {k} {b} xo l j lk ky =
      let σy = proj₁ (run-row∈ run j)
          (q″ , a″ , xo″ , rn , l″ , nc) = σ₃-lane σy
      in go (emit-one (a , y , xo , refl , l) (a″ , y , xo″ , refl , l″)) rn nc xo″
      where
        go : ∀ {q″ a″} → q ≡ q″ → RV.Runs op q″ → ¬ RV.CutAt op q″ y → RO q″ (out a″) → (k ⊕ [ sub LS.J ] , out (Ln b)) ∈ rx
        go refl rn nc _ = [ (λ af → ⊥-elim (≺-absurd {k} {y} ky (run-below run af j)))
                          , (λ (e″ , i₀) → bproj-in pr (subst (λ e₀ → (k , e₀) ∈ rs) (InvAt.func I₃ (proj₁ (proj₁ (run-row∈ run i₀))) (proj₁ σk)) i₀)) ]′
                          (aft-or-in run σk tt j)
          where
            σk : σ₃ k (out b)
            σk = σ₃-before xo rn lk nc ky (proj₁ (run-row∈ run j)) out-pin

    -- A LANE'S ROW BEFORE A ROW OF IT THE RUN MET IS MET BEFORE THAT ROW:
    -- the lanes show it, never cut between, and their run met it first.
    catch : ∀ xs {x rest} → Met M (xs ++ x ∷ rest)
          → ∀ {q a y v k b} → RO q (out a) → x ≡ (y ⊕ [ sub LS.J ] , out (Ln v)) → RV.Lane op q a y (out v)
          → RV.Lane op q a k (out b) → k ≺ y → (k ⊕ [ sub LS.J ] , out (Ln b)) ∈ xs
    catch xs mt {q} {a} {y} {v} {k} {b} xo x≡ l lk ky =
      let (rs , pr , run , _) = lane-run mt
          (y′ , e′ , j) = bproj-mem pr (∈-++⁺ʳ xs (here (sym x≡)))
      in in-prefix xs mt
           (catch-run pr run xo l (subst (λ w → (w , out v) ∈ rs) (sym (⊕-injˡ y y′ e′)) j) lk ky)
           (subst (λ x₀ → (k ⊕ [ sub LS.J ]) ≺ proj₁ x₀) (sym x≡) (lane-J xo lk l ky))

  private
    lat = lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
            (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
            (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)
    lfwd = lane-fwd op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
             (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
             (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)

  -- A LANE SEES ITS OWN VALUES: few of its rows before, its end after,
  -- all of them its value's rows at one subscription.
  lane-seen : ∀ {q a y v} → RO q (out a) → RV.Lane op q a y (out v) → Seen (RV.Lane op q a) y (out v)
  lane-seen {q} {a} {y} {v} xo l =
    (l , λ {c} lc cy → pinby-vis {e = out v} tt (InvAt.quiet Is (lfwd xo l lc) ry cy)) , proj₁ fw , λ lk lt → proj₂ fw (lfwd xo l lk) lt
    where
      La = lat xo l
      ry = proj₁ (proj₂ (proj₂ La))
      Is = inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (proj₁ La) (proj₁ (proj₂ La))
      fw = entered-few (fL a) (proj₁ La) (λ {k} {e′} → full {IE B} {y} {out v} tt {k} {e′}) ry

  -- A lane's emit a prefix met is among the rows it shows,
  in-rows : ∀ {q r c} (oc : OC q r c) {k v} → (k ⊕ [ sub LS.J ] , out (Ln v)) ∈ r → LaneEmit q (k ⊕ [ sub LS.J ] , out (Ln v)) v
          → Σ (Ev (IE B)) λ e → (k , e) ∈ lane-rows oc
  in-rows oc[] () _
  in-rows (oc-in {r} {x = x} {v = v′} oc (a′ , y , xo′ , x≡ , l′)) {k} i le with ∈-++⁻ r i
  ... | inj₁ i′ = let (e , j) = in-rows oc i′ le in e , ∈-++⁺ˡ j
  ... | inj₂ (here eq) = out v′ , subst (λ w → (w , out v′) ∈ lane-rows oc ++ [ (y , out v′) ]) (sym (⊕-injˡ k y (cong proj₁ (trans eq x≡))))
                           (∈-++⁺ʳ (lane-rows oc) (here refl))
  in-rows {q} (oc-out {r} oc nl) {k} {v} i le with ∈-++⁻ r i
  ... | inj₁ i′ = in-rows oc i′ le
  ... | inj₂ (here eq) = ⊥-elim (nl (subst (λ x → LaneEmit q x v) eq le))

  -- and the last of those is a row of the lane the prefix met.
  rows-last : ∀ {q r c} (oc : OC q r c) → cursor nothing (lane-rows oc) ≡ nothing
            ⊎ Σ Pos λ y₀ → cursor nothing (lane-rows oc) ≡ just y₀ × Σ (IE B) λ v₀ → (y₀ ⊕ [ sub LS.J ] , out (Ln v₀)) ∈ r
              × Σ A λ a₀ → RO q (out a₀) × RV.Lane op q a₀ y₀ (out v₀)
  rows-last oc[] = inj₁ refl
  rows-last (oc-in {r} {v = v} oc (a′ , y , xo′ , x≡ , l′)) =
    inj₂ (y , cursor-snoc nothing (lane-rows oc) , v , ∈-++⁺ʳ r (here (sym x≡)) , a′ , xo′ , l′)
  rows-last (oc-out oc _) with rows-last oc
  ... | inj₁ eq = inj₁ eq
  ... | inj₂ (y₀ , eq , v₀ , i , rest) = inj₂ (y₀ , eq , v₀ , ∈-++⁺ˡ i , rest)

  -- A LANE'S ROWS A PREFIX MET ARE A RUN OF THE LANE: each its lane's first
  -- past the last, since the source meets an earlier lane row first, and
  -- so, with the row met next, if it is the lane's.
  own-snoc : ∀ r {x rx₂} → Met M (r ++ x ∷ rx₂) → ∀ {q a c v} → RO q (out a) → (oc : OC q r c) → (le : LaneEmit q x v)
           → Met (RV.Lane op q a) (lane-rows (oc-in oc le))
  own-run : ∀ r {z e rx₂} → Met M (r ++ (z , e) ∷ rx₂) → ∀ {q a c} → RO q (out a) → (oc : OC q r c) → Met (RV.Lane op q a) (lane-rows oc)
  own-run _ mt xo oc[] = []ᴿ
  own-run _ {z} {e} {rx₂} mt xo (oc-in {r} {x = x} oc le) = own-snoc r (subst (Met M) (++-assoc r [ x ] ((z , e) ∷ rx₂)) mt) xo oc le
  own-run _ {z} {e} {rx₂} mt xo (oc-out {r} {x = x} oc _) = own-run r (subst (Met M) (++-assoc r [ x ] ((z , e) ∷ rx₂)) mt) xo oc

  own-snoc r {x} {rx₂} mt {q} {a} {v = v} xo oc (a′ , y , xo′ , x≡ , l′) =
    run-++ rec ((lane-seen xo l , tt , aft (rows-last oc) , least) ∷ᴿ []ᴿ)
    where
      rec : Met (RV.Lane op q a) (lane-rows oc)
      rec = own-run r mt xo oc

      l : RV.Lane op q a y (out v)
      l = subst (λ b → RV.Lane op q b y (out v)) (sym (ro-func xo xo′)) l′

      aft : _ → After (cursor nothing (lane-rows oc)) y
      aft (inj₁ eq) = subst (λ c → After c y) (sym eq) tt
      aft (inj₂ (y₀ , eq , v₀ , i₀ , a₀ , xo₀ , l₀)) =
        subst (λ c → After c y) (sym eq)
          (J-reflect xo (subst (λ b → RV.Lane op q b y₀ (out v₀)) (sym (ro-func xo xo₀)) l₀) l
            (subst ((y₀ ⊕ [ sub LS.J ]) ≺_) (cong proj₁ x≡) (met-before r mt i₀)))

      least : ∀ {k e′} → RV.Lane op q a k e′ → Visible e′ → After (cursor nothing (lane-rows oc)) k → y ≼ k
      least {e′ = end}   lk _ _ ky = proj₂ (proj₁ (lane-seen xo l)) lk ky
      least {k} {out b}  lk _ ak ky =
        let (_ , j) = in-rows oc (catch r mt xo x≡ l lk ky) (a , k , xo , refl , lk)
        in ≺-irrefl {k} (run-below rec ak j)
      least {e′ = skip}  _ () _
      least {e′ = pin _} _ () _

  -- A LANE'S UNDONE EMIT, NO PIECE'S MARK, IS MET PAST ITS `laneStart`:
  -- the lane shows the mark before it, never cut between, so the lanes
  -- show it too, and their run, having met the later row, met it first.
  started-by : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v
             → (∀ {a s y} → enter (fL a) s y (out v) → Σ Pos λ y₀ → enter (fL a) s y₀ (out (marked laneStart)) × s ≺ y₀ × y₀ ≺ y)
             → AC.StartIn [] xs q
  started-by xs mt {q} (a , y , xo , refl , l) st with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
  ... | s , oks , r , _ , back with st r
  ...   | y₀ , r₀ , sy₀ , y₀y = any-map (λ { refl → a , y₀ , _ , xo , refl , back r₀ sy₀ }) (catch xs mt xo refl l (back r₀ sy₀) y₀y)

  started : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v
          → T (undone v) → (v ≡ marked laneStart → ⊥) → (v ≡ marked burstEnd → ⊥) → AC.StartIn [] xs q
  started xs mt le u nl nb = started-by xs mt le (λ {a} {s} r → LaneStart.plain-starts _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s r u nl nb)

  -- A LANE'S `laneDone` IS MET PAST ITS `laneStart` too.
  done-started : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q kd n} → LaneEmit q x (instEmit (mark (laneDone kd)) n)
               → AC.StartIn [] xs q
  done-started xs mt le = started-by xs mt le (λ {a} {s} r → LaneStart.lane-starts _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s r)

  -- A LANE'S EMIT THE RUN MET IS A ROW OF THE LANES, of a lane running
  -- and never cut by it.
  emit-σ : ∀ {rx} → Met M rx → ∀ {x q v} → x ∈ rx → LaneEmit q x v
         → Σ Pos λ y → proj₁ x ≡ y ⊕ [ sub LS.J ] × σ₃ y (out v) × RV.Runs op q × ¬ RV.CutAt op q y
  emit-σ mt {q = q} {v} i (a , y , xo , refl , l) =
    let (rs , pr , run , _) = lane-run mt
        (y′ , e′ , j) = bproj-mem pr i
        σy = proj₁ (run-row∈ run (subst (λ w → (w , out v) ∈ rs) (sym (⊕-injˡ y y′ e′)) j))
        (q″ , a″ , xo″ , rn , l″ , nc) = σ₃-lane σy
    in go (emit-one (a , y , xo , refl , l) (a″ , y , xo″ , refl , l″)) σy rn nc
    where
      go : ∀ {q″} → q ≡ q″ → σ₃ y (out v) → RV.Runs op q″ → ¬ RV.CutAt op q″ y
         → Σ Pos λ y₀ → y ⊕ [ sub LS.J ] ≡ y₀ ⊕ [ sub LS.J ] × σ₃ y₀ (out v) × RV.Runs op q × ¬ RV.CutAt op q y₀
      go refl σy rn nc = y , refl , σy , rn , nc

  -- NOTHING OF A LANE IS MET PAST A CUT OF IT: the later value's
  -- `outerOpen` the scan met supersedes the lane before its row.
  cut-final : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v → AC.CutIn [] xs q → ⊥
  cut-final xs mt {q} le ci@(_ , _ , _ , _ , cb) =
    let (xc , _ , kc) = find cb
        op≡ = row-cut op xc kc
        (q′ , a′ , xo′ , qq′ , later) = switch-cut op≡ xs mt ci
        (y , px , σy , rn , nc) = emit-σ mt (∈-++⁺ʳ xs (here refl)) le
    in nc (subst (λ o₀ → RV.CutAt o₀ q y) (sym op≡) (q′ , a′ , xo′ , qq′ , later σy px))

  -- A LANE EMITS ONLY WHILE LIVE: its undone row, no piece's mark,
  -- follows its `laneStart`, and neither its `laneDone` nor a cut of it.
  live-of : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v → AC.StartIn [] xs q → AC.Live [] xs q
  live-of xs mt {q} le@(a , y , xo , refl , l) si = own , si , done-final xs mt le , cut-final xs mt le
    where
      own : Own q
      own = let (_ , _ , _ , rn , _) = emit-σ mt (∈-++⁺ʳ xs (here refl)) le in a , xo , rn

  lane-live : ∀ xs {x rest} → Met M (xs ++ x ∷ rest) → ∀ {q v} → LaneEmit q x v
            → T (undone v) → (v ≡ marked laneStart → ⊥) → (v ≡ marked burstEnd → ⊥) → AC.Live [] xs q
  lane-live xs mt le u nl nb = live-of xs mt le (started xs mt le u nl nb)

  emit-live : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
            → ∀ {q n} → LaneEmit q x (instEmit (mark begin) n) → AC.Live [] xs q
  emit-live rx₁ mt xs x ys eq le = lane-live xs (split-met rx₁ mt xs x ys eq) le tt (λ ()) (λ ())

  -- Rows of a met run keep their order.
  met-order : ∀ (xs : List Row) {u ys zs} → Met M (xs ++ u ∷ ys ++ zs) → ∀ {v} → v ∈ ys → proj₁ u ≺ proj₁ v
  met-order xs {u} {ys} {zs} mt {v} j with ∈-∃++ j
  ... | ys₁ , ys₂ , refl =
    met-before (xs ++ u ∷ ys₁) {proj₁ v} {proj₂ v} {ys₂ ++ zs}
      (subst (Met M) (trans (cong (λ t → xs ++ u ∷ t) (++-assoc ys₁ (v ∷ ys₂) zs)) (sym (++-assoc xs (u ∷ ys₁) (v ∷ ys₂ ++ zs)))) mt)
      (∈-++⁺ʳ xs (here refl))

  -- THE LANE'S COUNT BEFORE `x`: its rows' emits there, folded in order.
  FoldAt : Pos → A → Pos → Routes → Set
  FoldAt q a = FoldOf (λ y v → RV.Lane op q a y (out v))

  -- A LANE'S `laneDone` TELLS WHAT THE LANE COUNTED over its rows before
  -- it: the lane's own site, read back through the subscription its rows
  -- share.
  done-site : ∀ {q a yd kd n} → RO q (out a) → RV.Lane op q a yd (out (instEmit (mark (laneDone kd)) n))
            → Σ Routes λ r → kd ≡ proj₂ r × FoldAt q a yd r
  done-site {q} {a} {yd} xo ld = Sited.r Sᵈ , Sited.told Sᵈ , fold-map upᵈ dnᵈ (Sited.fold Sᵈ)
    where
      Lᵈ = lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
            (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
            (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo ld

      sᵈ : Pos
      sᵈ = proj₁ Lᵈ

      Iᵈ : InvAt _ sᵈ (enter (fL a) sᵈ)
      Iᵈ = inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ sᵈ (proj₁ (proj₂ Lᵈ))

      Sᵈ : Sited (enter (fL a) sᵈ) yd _
      Sᵈ = lane-site _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ m sᵈ (proj₁ (proj₂ Lᵈ)) (proj₁ (proj₂ (proj₂ Lᵈ)))

      upᵈ : ∀ {y e} → enter (fL a) sᵈ y e → RV.Lane op q a y e
      upᵈ x = proj₂ (proj₂ (proj₂ (proj₂ Lᵈ))) x (world-after (InvAt.world Iᵈ x) (InvAt.real Iᵈ x))

      dnᵈ : ∀ {y e} → RV.Lane op q a y e → enter (fL a) sᵈ y e
      dnᵈ l = lane-fwd op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
               (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
               (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo ld l

  -- One lane's rows at one place show one emit.
  lane-func : ∀ {q a y e e′} → RO q (out a) → RV.Lane op q a y e → RV.Lane op q a y e′ → e ≡ e′
  lane-func {q} {a} xo l l′ =
    let (s , oks , r , r′) = lane-at₂ op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
                               (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
                               (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l l′
    in InvAt.func (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) r r′

  -- A row met before a run's last is placed before it.
  before-last : ∀ p₀ {x₀ rest u} → Met M ((p₀ ++ [ x₀ ]) ++ rest) → u ∈ p₀ → proj₁ u ≺ proj₁ x₀
  before-last p₀ {x₀} {rest} {u} mt i with ∈-∃++ i
  ... | p₁ , p₂ , refl = met-order p₁ {u} {p₂ ++ [ x₀ ]} {rest} (subst (Met M) eq mt) (∈-++⁺ʳ p₂ (here refl))
    where
      eq : ((p₁ ++ u ∷ p₂) ++ [ x₀ ]) ++ rest ≡ p₁ ++ u ∷ (p₂ ++ [ x₀ ]) ++ rest
      eq = trans (++-assoc (p₁ ++ u ∷ p₂) [ x₀ ] rest)
             (trans (++-assoc p₁ (u ∷ p₂) (x₀ ∷ rest)) (cong (λ t → p₁ ++ u ∷ t) (sym (++-assoc p₂ [ x₀ ] rest))))

  -- A row of a run's prefix plus one is in the prefix, or the one.
  in-snoc : ∀ (p₀ : List Row) {x₀ u : Row} → u ∈ p₀ ++ [ x₀ ] → u ∈ p₀ ⊎ u ≡ x₀
  in-snoc p₀ i with ∈-++⁻ p₀ i
  ... | inj₁ i′ = inj₁ i′
  ... | inj₂ (here e) = inj₂ e

  not-in-[] : ∀ {u : Row} → u ∈ [] → ⊥
  not-in-[] ()

  out-inj : ∀ {v v′ : IE B} → out v ≡ out v′ → v ≡ v′
  out-inj refl = refl

  -- THE RUN'S COUNT OF A LANE IS ITS FOLD: over a met prefix holding
  -- exactly the lane's rows before `w`, in the run's order, which is
  -- theirs.
  fold-oc : ∀ {q a w r} → RO q (out a) → FoldAt q a w r → ∀ pre rest → Met M (pre ++ rest)
          → (∀ {y v} → RV.Lane op q a y (out v) → y ≺ w → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ pre)
          → (∀ {u v} → u ∈ pre → LaneEmit q u v → Σ Pos λ y → proj₁ u ≡ y ⊕ [ sub LS.J ] × y ≺ w)
          → ∀ {c} → OC q pre c → c ≡ r
  fold-oc xo (f-none _) .[] rest mt h₁ h₂ oc[] = refl
  fold-oc xo (f-step _ l yx _) .[] rest mt h₁ h₂ oc[] = ⊥-elim (not-in-[] (h₁ l yx))
  fold-oc {q} {a} xo fd .(p₀ ++ [ x₀ ]) rest mt h₁ h₂ (oc-out {p₀} {c} {x₀} oc nl) =
    fold-oc xo fd p₀ (x₀ ∷ rest) (subst (Met M) (++-assoc p₀ [ x₀ ] rest) mt) h₁′ (λ i le → h₂ (∈-++⁺ˡ i) le) oc
    where
      h₁′ : ∀ {y v} → RV.Lane op q a y (out v) → y ≺ _ → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ p₀
      h₁′ {y} {v} l yx = [ (λ i → i) , (λ e → ⊥-elim (nl (a , y , xo , sym e , l))) ]′ (in-snoc p₀ (h₁ l yx))
  fold-oc {q} {a} {w} xo fd .(p₀ ++ [ x₀ ]) rest mt h₁ h₂ (oc-in {p₀} {c} {x₀} {v₀} oc (a₀ , y₀ , xo₀ , refl , l₀)) =
    step (ro-func xo xo₀) fd
    where
      mt′ : Met M (p₀ ++ (y₀ ⊕ [ sub LS.J ] , out (Ln v₀)) ∷ rest)
      mt′ = subst (Met M) (++-assoc p₀ [ _ ] rest) mt

      step : a ≡ a₀ → ∀ {r} → FoldAt q a w r → count c v₀ ≡ r
      step refl fd₀ = with-last fd₀
        where
          y₀w : y₀ ≺ w
          y₀w = let (y , e , yw) = h₂ (∈-++⁺ʳ p₀ (here refl)) (a₀ , y₀ , xo₀ , refl , l₀)
                in subst (_≺ w) (sym (⊕-injˡ y₀ y e)) yw

          -- A lane row of the prefix lies before the last.
          early : ∀ {y v} → RV.Lane op q a y (out v) → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ p₀ → y ≺ y₀
          early l i = J-reflect xo l l₀ (before-last p₀ mt i)

          -- A lane row before `w` past the last is none.
          none-past : ∀ {y v} → RV.Lane op q a y (out v) → y₀ ≺ y → y ≺ w → ⊥
          none-past {y} l y₀y yw = [ (λ i → ≺-absurd {y} {y₀} (early l i) y₀y)
                                   , (λ e → ≺-irrefl {y₀} (subst (y₀ ≺_) (⊕-injˡ y y₀ (cong proj₁ e)) y₀y)) ]′ (in-snoc p₀ (h₁ l yw))

          same : ∀ {y} → y ≡ y₀ ⊎ (y ≺ y₀ ⊎ y₀ ≺ y) → ∀ {v} → RV.Lane op q a y (out v)
               → (∀ {y′ v′} → RV.Lane op q a y′ (out v′) → y ≺ y′ → y′ ≺ w → ⊥) → y ≺ w → y ≡ y₀
          same (inj₁ e) _ _ _ = e
          same (inj₂ (inj₁ yy₀)) _ lst _ = ⊥-elim (lst l₀ yy₀ y₀w)
          same (inj₂ (inj₂ y₀y)) l _ yw = ⊥-elim (none-past l y₀y yw)

          trich : ∀ y → y ≡ y₀ ⊎ (y ≺ y₀ ⊎ y₀ ≺ y)
          trich y = [ (λ le → [ (λ lt → inj₂ (inj₂ lt)) , (λ e → inj₁ (sym e)) ]′ (≼-split {y₀} {y} le)) , (λ lt → inj₂ (inj₁ lt)) ]′ (≼-or-≻ y₀ y)

          h₁′ : ∀ {y v} → RV.Lane op q a y (out v) → y ≺ y₀ → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ p₀
          h₁′ {y} l yy₀ = [ (λ i → i) , (λ e → ⊥-elim (≺-irrefl {y₀} (subst (_≺ y₀) (⊕-injˡ y y₀ (cong proj₁ e)) yy₀))) ]′
                            (in-snoc p₀ (h₁ l (≺-trans {y} {y₀} {w} yy₀ y₀w)))

          h₂′ : ∀ {u v} → u ∈ p₀ → LaneEmit q u v → Σ Pos λ y → proj₁ u ≡ y ⊕ [ sub LS.J ] × y ≺ y₀
          h₂′ i (a′ , y , xo′ , refl , l′) = y , refl , early (subst (λ a″ → RV.Lane op q a″ y (out _)) (sym (ro-func xo xo′)) l′) i

          from : ∀ {y v r′} → y ≡ y₀ → FoldAt q a y r′ → RV.Lane op q a y (out v) → count c v₀ ≡ count r′ v
          from refl fd′ l = cong₂ count (fold-oc xo fd′ p₀ _ mt′ h₁′ h₂′ oc) (out-inj (lane-func xo l₀ l))

          with-last : ∀ {r} → FoldAt q a w r → count c v₀ ≡ r
          with-last (f-none nl) = ⊥-elim (nl l₀ y₀w)
          with-last (f-step {y = y} fd′ l yw lst) = from (same (trich y) l lst yw) fd′ l

  -- A LANE'S `laneDone` TELLS ITS COUNT AS THE RUN MET IT: the run met
  -- every row of the lane before the `laneDone` first, and none after.
  done-told : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
            → ∀ {q kd n c} → LaneEmit q x (instEmit (mark (laneDone kd)) n) → OC q xs c → proj₂ c ≡ kd
  done-told rx₁ {z} {e} {rx₂} mt xs x ys eq {q} {kd} {n} {c} (a , yd , xo , refl , ld) oc =
    let (r , told , fd) = done-site xo ld
    in trans (cong proj₂ (fold-oc xo fd xs (x ∷ ys ++ (z , e) ∷ rx₂) mt′ h₁ h₂ oc)) (sym told)
    where
      mt′ : Met M (xs ++ x ∷ ys ++ (z , e) ∷ rx₂)
      mt′ = subst (Met M) (trans (cong (_++ (z , e) ∷ rx₂) eq) (++-assoc xs (x ∷ ys) ((z , e) ∷ rx₂))) mt

      h₁ : ∀ {y v} → RV.Lane op q a y (out v) → y ≺ yd → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ xs
      h₁ l yy = catch xs (split-met rx₁ mt xs _ ys eq) xo refl ld l yy

      h₂ : ∀ {u v} → u ∈ xs → LaneEmit q u v → Σ Pos λ y → proj₁ u ≡ y ⊕ [ sub LS.J ] × y ≺ yd
      h₂ i (a′ , y , xo′ , refl , l′) =
        y , refl , J-reflect xo (subst (λ a″ → RV.Lane op q a″ y (out _)) (sym (ro-func xo xo′)) l′) ld (met-before xs (split-met rx₁ mt xs _ ys eq) i)

  -- THE COUNTER IS AT MOST WHAT THE LIVE LANES HOLD OF ITS INSTANT: where
  -- it is not empty, a lane started, never done nor cut, holds a route of
  -- the scan's instant.
  lanes-live : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ¬ Flat.lanes (St rx₁) ≡ 0
             → ¬ ¬ Σ Pos λ q → AC.Live [] rx₁ q × Σ Routes λ c → OC q rx₁ c × proj₁ c ≡ Flat.at (St rx₁) × Σ ℕ λ k → proj₂ c ≡ suc k
  lanes-live rx₁ mt =
    Run.lanes-held rx₁ (λ {c} → end-free rx₁ mt {c})
      (λ xs x ys eq {k} {v} x≡ κ → κ (emit-at (subst (_∈ rx₁) x≡ (in-r₁ rx₁ xs x ys eq)) x≡))
      (λ { {q} {x} {v} (_ , y , _ , eq , _) → y ⊕ [ sub LS.J ] , eq })
      (λ {q} {q′} {x} {v} {v′} → emit-one {q} {q′} {x} {v} {v′})
      (λ { {q} {x} (kd , a , y , n , xo , eq , l) → kd , n , a , y , xo , eq , l })
      (emit-live rx₁ mt) (λ xs x ys eq {q} {kd} {n} {c} l oc → ℕP.≤-reflexive (done-told rx₁ mt xs x ys eq {q} {kd} {n} {c} l oc))
    where
      emit-at : ∀ {x k v} → (k , out (Tg laneB v)) ∈ rx₁ → x ≡ (k , out (Tg laneB v)) → Σ Pos λ q → LaneEmit q x v
      emit-at {v = v} i x≡ = let (q , le) = lane-emit rx₁ mt i in q , subst (λ x′ → LaneEmit q x′ v) (sym x≡) le

  -- A LANE'S INNER NEVER ENDS BEFORE ITS `laneDone`.
  inner-done : ∀ a {s c} → enter (ev m (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀)) s c end
             → ¬ TakeWhile.Failed true undone (enter (ev m (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀)) s) c → ⊥
  inner-done a {s} re nf = inner-ends _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s re nf

  opaque
    -- A LANE'S END FOLLOWS ITS `laneDone`: the take stops just past it.
    lane-end-done : ∀ {q a c} → RO q (out a) → RV.Lane op q a c end
                  → Σ Pos λ y → Σ _ λ kd → Σ _ λ n → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n)) × y ≺ c
    lane-end-done {q} {a} {c} xo l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
        (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
        (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
    ... | s , oks , r , _ , back with lane-end m undone (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r
    ...   | inj₂ (re , nf) = ⊥-elim (inner-done a re nf)
    ...   | inj₁ (w , a′ , refl , rf , nk) with done-of a′ nk
    ...     | kd , n , refl = w ⊕ [ ix 0 ] , kd , n
                       , back rf (world-after (InvAt.world (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) rf)
                                              (InvAt.real (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) rf))
                       , ix<last w

  opaque
    -- The lanes' rows, as the joiner shows them.
    σ-join : ∀ {y e} → σ₃ y e → RV.Join op y e
    σ-join σy = proj₁ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σy))

    -- A SWITCH'S LANES END PAST A LAST VALUE: past any value before the
    -- lanes' end lies one no later value cuts by it.
    last-before : op ≡ switchᶠ → ∀ {y} → σ₃ y end → ∀ {q a} → RO q (out a) → q ≺ y
                → ¬ ¬ Σ Pos λ q* → Σ A λ a* → RO q* (out a*) × q ≼ q* × ¬ RV.CutAt op q* y
    last-before op≡ {y} ry xo qy κ =
      switch-last fL RO (subst (λ o₀ → Reach (RV.Join o₀) y end) op≡
                           (proj₂ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ ry))))
        xo qy λ (q* , a* , xo* , qq* , nc) → κ (q* , a* , xo* , qq* , subst (λ o₀ → ¬ RV.CutAt o₀ q* y) (sym op≡) nc)

  -- A LANE ROW THE SCAN NEVER MET LIES PAST THE LANES' RUN.
  after-of : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {k b} → σ₃ k (out b)
           → ((k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∈ rx → ⊥) → After (cursor nothing rs) k
  after-of {rs = []}    pr run σk nm = tt
  after-of {rs = _ ∷ _} pr run σk nm with aft-or-in run σk tt (here refl)
  ... | inj₁ a = a
  ... | inj₂ (e′ , i) with InvAt.func I₃ (proj₁ σk) (proj₁ (proj₁ (run-row∈ run i)))
  ...   | refl = ⊥-elim (nm (bproj-in pr i))

  -- A LATER VALUE'S `outerOpen` THE RUN MET CUTS A LANE STARTED IN IT:
  -- the mark lies past the lane's start, which no later value had cut.
  opened-cut : op ≡ switchᶠ → ∀ rx₁ {W} → Met M (rx₁ ++ W) → ∀ {q} → AC.StartIn [] rx₁ q
             → ∀ {q′ a′} → RO q′ (out a′) → q ≺ q′ → Any (OpenMark q′) rx₁ → AC.CutIn [] rx₁ q
  opened-cut op≡ rx₁ {W} mt {q} si {q′} {a′} xo′ qq′ oa =
    let (x₀ , i₀ , mk₀) = find si
        (o , io , (_ , r″ , n″ , σr″ , q″≡ , o≡)) = find oa
        (xs₁ , xs₂ , eqx) = ∈-∃++ io
    in go x₀ i₀ mk₀ r″ σr″ q″≡ xs₁ xs₂ (subst (λ o₀ → rx₁ ≡ xs₁ ++ o₀ ∷ xs₂) o≡ eqx)
    where
      lane≢outer : ∀ {u : Ev (IE B)} {v} → just u ≡ v → v ≡ nothing → ⊥
      lane≢outer refl ()

      go : ∀ x₀ → x₀ ∈ rx₁ → LaneMark laneStart q x₀ → ∀ r″ {a″ n″} → σ₁ r″ (out (instEmit (value a″) n″)) → q′ ≡ ro-at r″ → ∀ xs₁ xs₂
         → rx₁ ≡ xs₁ ++ (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″)))) ∷ xs₂ → AC.CutIn [] rx₁ q
      go x₀ i₀ (a , y₀ , n₀ , xo , refl , l) r″ {n″ = n″} σr″ q″≡ xs₁ xs₂ E = xs₁ , (o′ ∷ xs₂) , E , start , here kc
        where
          o′ = (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″))))

          kc : rowKind markAct op o′ ≡ kCut
          kc = subst (λ o₀ → markAct o₀ outerOpen ≡ kCut) (sym op≡) refl

          mt′ : Met M (xs₁ ++ o′ ∷ xs₂ ++ W)
          mt′ = subst (Met M) (trans (cong (_++ W) E) (++-assoc xs₁ (o′ ∷ xs₂) W)) mt

          -- The lane's start, a row of the lanes,
          σs : σ₃ y₀ (out (instEmit (mark laneStart) n₀))
          σs = let (y′ , e′ , _ , σs′) = lane-mark (run-prefix rx₁ mt) i₀ (inj₁ refl)
               in subst (λ w → σ₃ w (out (instEmit (mark laneStart) n₀))) (sym (⊕-injˡ y₀ y′ e′)) σs′

          -- which no later value had cut.
          y₀≼ : y₀ ≼ ro-at r″
          y₀≼ lt =
            let (q₀ , a₀ , xo₀ , _ , l₀ , nc₀) = σ₃-lane σs
            in nc₀ (subst (λ w → RV.CutAt op w y₀) (sym (start-one (a₀ , y₀ , n₀ , xo₀ , refl , l₀) (a , y₀ , n₀ , xo , refl , l)))
                     (subst (λ o₀ → RV.CutAt o₀ q y₀) (sym op≡) (q′ , a′ , xo′ , qq′ , subst (_≺ y₀) (sym q″≡) lt)))

          mc : M (r″ ⊕ [ sub OS.J ]) (out (just (inj₁ (outerB , instEmit (mark outerOpen) n″))))
          mc = proj₁ (run-row∈ mt (∈-++⁺ˡ (subst (o′ ∈_) (sym E) (∈-++⁺ʳ xs₁ (here refl)))))

          -- So the mark lies past the lane's start.
          opened : (r″ ⊕ [ sub OS.J ]) ≺ (y₀ ⊕ [ sub LS.J ]) → ⊥
          opened lt = [ (λ xy → lane-in-outer op≡ σr″ σs xy y₀≼)
                      , (λ yx → ≺-irrefl {r″ ⊕ [ sub OS.J ]} (≺-≼-≺ {r″ ⊕ [ sub OS.J ]} {y₀ ⊕ [ sub LS.J ]} {r″ ⊕ [ sub OS.J ]} lt
                            (lane-under σs (subst (λ d → enter d P (r″ ⊕ [ sub OS.J ]) (out _)) (src-op tk env′ m) mc) yx))) ]′
                      (≼-or-≻ (r″ ⊕ [ sub OS.J ]) y₀)

          start : AC.StartIn [] xs₁ q
          start = [ any-map (λ { refl → a , y₀ , n₀ , xo , refl , l })
                  , (λ { (here eq′) → ⊥-elim (lane≢outer (cong (λ r → brTag {B} laneB (proj₂ r)) eq′) refl)
                       ; (there j) → ⊥-elim (opened (met-order xs₁ mt′ j)) }) ]′
                  (++⁻ xs₁ (subst (_ ∈_) E i₀))

  cut-at : op ≡ switchᶠ → ∀ xs ys {z e rx₂ q q′ a′ k b} → Met M ((xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys) ++ (z , e) ∷ rx₂)
         → ∀ {x₀} → x₀ ∈ xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys → LaneMark laneStart q x₀
         → RO q′ (out a′) → q ≺ q′ → RV.Lane op q′ a′ k (out b)
         → ∀ {r′ n′} → σ₁ r′ (out (instEmit (value a′) n′)) → q′ ≡ ro-at r′
         → ¬ ¬ AC.CutIn [] (xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys) q
  cut-at op≡ xs ys {z} {e} {rx₂} {q} {q′} {a′} {k} {b} mt {x₀} i₀ mk xo′ qq′ l′ {r′} σr′ q′≡ nc =
    met-open xs (split-met (xs ++ row ∷ ys) mt xs _ ys refl) σr′ jz
      λ oa → nc (opened-cut op≡ (xs ++ row ∷ ys) mt (any-map (λ eq → subst (LaneMark laneStart q) eq mk) i₀) xo′ qq′
                   (++⁺ˡ (subst (λ q₀ → Any (OpenMark q₀) xs) (sym q′≡) oa)))
    where
      row = (k ⊕ [ sub LS.J ] , out (Tg laneB b))

      jz : (r′ ⊕ [ sub OS.J ]) ≺ (k ⊕ [ sub LS.J ])
      jz = ≺-trans {r′ ⊕ [ sub OS.J ]} {ro-at r′} {k ⊕ [ sub LS.J ]} (J≺ro r′)
             (≺-trans {ro-at r′} {k} {k ⊕ [ sub LS.J ]} (subst (_≺ k) q′≡ (lane-past op fL RO l′)) (≺-ext k []))

  -- A LATER VALUE'S LANE ROW THE SCAN MET PAST A LANE'S START CUTS IT IN
  -- THE SCAN: the later value's `outerOpen` lies before its lane's rows,
  -- and past the first lane's start, which no later value had cut.
  cut-met : op ≡ switchᶠ → ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {q} → AC.StartIn [] rx₁ q
          → ∀ {q′ a′ k b} → RO q′ (out a′) → q ≺ q′ → RV.Lane op q′ a′ k (out b)
          → (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∈ rx₁ → ¬ ¬ AC.CutIn [] rx₁ q
  cut-met op≡ rx₁ {z} {e} {rx₂} mt {q} si {q′} {a′} {k} {b} xo′ qq′ l′ i κ =
    let (x₀ , i₀ , mk₀) = find si
        (xs , ys , eq) = ∈-∃++ i
        (r′ , _ , σr′ , q′≡) = ro-row xo′
    in cut-at op≡ xs ys (subst (λ r → Met M (r ++ (z , e) ∷ rx₂)) eq mt) (subst (x₀ ∈_) eq i₀) mk₀ xo′ qq′ l′ σr′ q′≡
         (λ c → κ (subst (λ r → AC.CutIn [] r q) (sym eq) c))

  -- An uncut running lane shows its `laneDone` before the lanes' end.
  done-before : ∀ {q a y} → RO q (out a) → RV.Runs op q → ¬ RV.CutAt op q y → σ₃ y end
              → Σ Pos λ yd → Σ ℕ λ kd → Σ Pos λ n → RV.Lane op q a yd (out (instEmit (mark (laneDone kd)) n)) × yd ≺ y
  done-before {q} {a} {y} xo rn nc ry = from-end (join-done op fL RO (σ-join ry))
    where
      from-end : Ended RO y × (∀ {q a} → RO q (out a) → RV.Runs op q → q ≺ y → ¬ RV.CutAt op q y → Ended (RV.Lane op q a) y)
               → Σ Pos λ yd → Σ ℕ λ kd → Σ Pos λ n → RV.Lane op q a yd (out (instEmit (mark (laneDone kd)) n)) × yd ≺ y
      from-end ((co , oe , co≼y) , lanes) =
        let (c* , lc* , c*≼y) = lanes xo rn (≺-≼-≺ {q} {co} {y} (ro-before xo oe) co≼y) nc
            (yd , kd , n , ld , ydc) = lane-end-done xo lc*
        in yd , kd , n , ld , ≺-≼-≺ {yd} {c*} {y} ydc c*≼y

  -- A live lane's own value, or the last value cutting it before `y`,
  -- runs uncut at `y`.
  live-pick : ∀ {q a y} → RO q (out a) → RV.Runs op q → σ₃ y end
            → ¬ ¬ Σ Pos λ q* → Σ A λ a* → RO q* (out a*) × RV.Runs op q* × ¬ RV.CutAt op q* y × (q* ≡ q ⊎ (op ≡ switchᶠ × q ≺ q*))
  live-pick {q} {a} {y} xo rn ry = em {P = RV.CutAt op q y} cut uncut
    where
      uncut : ¬ RV.CutAt op q y → ¬ ¬ Σ Pos λ q* → Σ A λ a* → RO q* (out a*) × RV.Runs op q* × ¬ RV.CutAt op q* y × (q* ≡ q ⊎ (op ≡ switchᶠ × q ≺ q*))
      uncut nct κ′ = κ′ (q , a , xo , rn , nct , inj₁ refl)
      cut : RV.CutAt op q y → ¬ ¬ Σ Pos λ q* → Σ A λ a* → RO q* (out a*) × RV.Runs op q* × ¬ RV.CutAt op q* y × (q* ≡ q ⊎ (op ≡ switchᶠ × q ≺ q*))
      cut ct = let op≡ = cut-switch op fL RO ct
                   (q′ , a′ , xo′ , qq′ , q′y) = subst (λ o₀ → RV.CutAt o₀ q y → Superseded RO q y) (sym op≡) (λ c → c) ct
               in λ κ′ → last-before op≡ ry xo′ q′y λ (q* , a* , xo* , q′≼ , nc*) →
                    κ′ (q* , a* , xo* , subst (λ o₀ → RV.Runs o₀ q*) (sym op≡) tt , nc* , inj₂ (op≡ , ≺-≼-≺ {q} {q′} {q*} qq′ q′≼))

  -- A lane's `laneDone` row, met, is its done.
  done-in : ∀ {rx q q* a* yd kd n} → q* ≡ q → RO q* (out a*) → RV.Lane op q* a* yd (out (instEmit (mark (laneDone kd)) n))
          → (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark (laneDone kd)) n))) ∈ rx → AC.DoneIn [] rx q
  done-in {rx} {q} {q*} {a*} {yd} {kd} {n} refl xo ld i = any-map done-row i
    where
      done-row : ∀ {x} → (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark (laneDone kd)) n))) ≡ x → DoneMark q x
      done-row e = kd , a* , yd , n , xo , sym e , ld

  -- The lanes' run a prefix met.
  met-shown : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → Met σ₃ rs
  met-shown rx₁ mt pr = let (rs′ , pr′ , run′ , _) = lane-run (run-prefix rx₁ mt) in subst (Met σ₃) (bproj-one pr′ pr refl) run′

  end-σ : ∀ {c} → R c end → σ₃ c end
  end-σ rc = rc , λ {c′} rc′ lt → pinby-vis {e = end {IE B}} tt (InvAt.quiet I₃ rc′ rc lt)

  -- The lanes' end lies past their run.
  end-after : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {c} → σ₃ c end → After (cursor nothing rs) c
  end-after {rs = []}    pr run σc = tt
  end-after {rs = _ ∷ _} pr run σc with aft-or-in run σc tt (here refl)
  ... | inj₁ a = a
  ... | inj₂ (e′ , i) with InvAt.func I₃ (proj₁ σc) (proj₁ (proj₁ (run-row∈ run i)))
  ...   | refl = ⊥-elim (bproj-end pr i)

  -- BEFORE A WAIT PAST THE LANES' CURSOR AND BEFORE THEIR NEXT, THE REAL
  -- FLATMAP'S ROWS ARE THE LANES': an end before one would be a lanes'
  -- row past the cursor before the wait.
  wait-proper : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {w}
              → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → ∀ {k e} → R k e → k ≺ w → σ₃ k e
  wait-proper pr run {w} lw {k} rk kw = rk , λ {c} rc ck → lw (end-σ rc) tt (end-after pr run (end-σ rc)) (≺-trans {c} {k} {w} ck kw)

  -- A JOINER ROW BEFORE SUCH A WAIT, where the lanes' rows before it are
  -- few, is the lanes': so are the real flatMap's, so the joiner, which
  -- shows its hangs, has few before it.
  wait-shown : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {w} → Few σ₃ w
             → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
             → ∀ {k e} → RV.Join op k e → k ≺ w → ¬ ¬ σ₃ k e
  wait-shown pr run {w} (ks , h) lw {k} jk kw κ =
    join-shows op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)
      (shows-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))
      (λ a s′ oks → shows-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s′ oks)
      (ks , λ x f lt → h (wait-proper pr run lw (R-from (x , few-reach f)) lt) lt) λ fJ →
        κ (wait-proper pr run lw (R-from (jk , proj₁ fJ , λ {k′} x lt _ → proj₂ fJ x (≺-trans {k′} {k} {w} lt kw))) kw)

  -- AN UNCUT LANE ROW THE SOURCE NEVER MET LIES NO EARLIER THAN SUCH A
  -- WAIT: it is the lanes', past their cursor.
  uncut-past : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {w} → Few σ₃ w
             → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
             → ∀ {q a k b} → RO q (out a) → RV.Runs op q → RV.Lane op q a k (out b) → ¬ RV.CutAt op q k
             → ((k ⊕ [ sub LS.J ] , out (Ln b)) ∈ rx → ⊥) → w ≼ k
  uncut-past pr run fw lw xo rn l nc nm kw =
    wait-shown pr run fw lw (join-in op fL RO xo rn l nc tt) kw λ σk → lw σk tt (after-of pr run σk nm) kw

  -- A LIVE LANE'S ROW CUT THERE LIES PAST THE SOURCE'S NEXT ROW: the
  -- cutter's `outerOpen` lies before it, and, before the next row, would
  -- have been met, cutting the lane in the scan.
  cut-past : ∀ rx₁ {z v rx₂} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → ∀ {q a} → RO q (out a)
           → AC.Live [] rx₁ q → ∀ {w} → w ≼ z → ∀ {k e′} → RV.Lane op q a k e′ → RV.CutAt op q k → w ≼ k
  cut-past rx₁ {z} mt {q} xo (_ , si , _ , nci) {w} wz {k} l ct kw =
    go (subst (λ o₀ → RV.CutAt o₀ q k → Superseded RO q k) (sym op≡) (λ c → c) ct)
    where
      op≡ = cut-switch op fL RO ct

      go : Superseded RO q k → ⊥
      go (q′ , a′ , xo′ , qq′ , q′k) =
        let (r′ , _ , σr′ , q′≡) = ro-row xo′
            Jk = ≺-trans {r′ ⊕ [ sub OS.J ]} {ro-at r′} {k} (J≺ro r′) (subst (_≺ k) q′≡ q′k)
        in [ (λ zJ → wz (≼-≺-≺ {z} {r′ ⊕ [ sub OS.J ]} {w} zJ (≺-trans {r′ ⊕ [ sub OS.J ]} {k} {w} Jk kw)))
           , (λ Jz → met-open rx₁ mt σr′ Jz λ oa → nci (opened-cut op≡ rx₁ mt si xo′ qq′ (subst (λ q₀ → Any (OpenMark q₀) rx₁) (sym q′≡) oa))) ]′
           (≼-or-≻ z (r′ ⊕ [ sub OS.J ]))

  -- A LIVE LANE'S ROW THE SOURCE NEVER MET LIES NO EARLIER THAN SUCH A WAIT,
  unmet-past : ∀ rx₁ {z v rx₂ rs} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q a} → RO q (out a)
             → AC.Live [] rx₁ q → ∀ {w} → w ≼ z → Few σ₃ w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
             → ∀ {k b} → RV.Lane op q a k (out b) → ((k ⊕ [ sub LS.J ] , out (Ln b)) ∈ rx₁ → ⊥) → w ≼ k
  unmet-past rx₁ mt pr {q} xo lv@((_ , _ , rn) , _) {w} wz fw lw {k} l nm kw =
    em {P = RV.CutAt op q k} {G = ⊥}
      (λ ct _ → cut-past rx₁ mt xo lv wz l ct kw)
      (λ nc _ → uncut-past pr (met-shown rx₁ mt pr) fw lw xo rn l nc nm kw)
      (λ ())

  -- and so does its end: its `laneDone` lies before it, which, met, would
  -- have done it.
  end-past : ∀ rx₁ {z v rx₂ rs} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q a} → RO q (out a)
           → AC.Live [] rx₁ q → ∀ {w} → w ≼ z → Few σ₃ w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
           → ∀ {k} → RV.Lane op q a k end → w ≼ k
  end-past rx₁ mt pr xo lv@(_ , _ , nd , _) {w} wz fw lw {k} l kw =
    let (yd , kd , n , ld , ydk) = lane-end-done xo l
    in unmet-past rx₁ mt pr xo lv wz fw lw ld (λ i → nd (done-in refl xo ld i)) (≺-trans {yd} {k} {w} ydk kw)

  -- A LIVE LANE'S ROWS BEFORE SUCH A WAIT ARE FEW: its visible ones the
  -- source met, and its quiet ones the lanes'.
  lane-few : ∀ rx₁ {z v rx₂ rs} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q a} → RO q (out a)
           → AC.Live [] rx₁ q → ∀ {w} → w ≼ z → Few σ₃ w
           → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y) → Few (RV.Lane op q a) w
  lane-few rx₁ {rs = rs} mt pr {q} {a} xo lv@((_ , _ , rn) , _) {w} wz fw lw = L.map proj₁ rs ++ proj₁ fw , pick
    where
      quiet : ∀ {k e′} → RV.Lane op q a k e′ → Work e′ → k ≺ w → k ∈ proj₁ fw
      quiet {k} l wk kw = ∈-stable λ ¬i → em {P = RV.CutAt op q k} {G = ⊥}
        (λ ct _ → cut-past rx₁ mt xo lv wz l ct kw)
        (λ nc _ → wait-shown pr (met-shown rx₁ mt pr) fw lw (join-in op fL RO xo rn l nc wk) kw λ σk → ¬i (proj₂ fw σk kw))
        (λ ())

      pick : ∀ {k e′} → RV.Lane op q a k e′ → k ≺ w → k ∈ L.map proj₁ rs ++ proj₁ fw
      pick {e′ = skip}  l kw = ∈-++⁺ʳ (L.map proj₁ rs) (quiet l tt kw)
      pick {e′ = pin _} l kw = ∈-++⁺ʳ (L.map proj₁ rs) (quiet l tt kw)
      pick {k} {end} l kw = ⊥-elim (end-past rx₁ mt pr xo lv wz fw lw l kw)
      pick {k} {out b} l kw with any? (k ≟ᵖ_) (L.map proj₁ rs)
      ... | yes i = ∈-++⁺ˡ i
      ... | no ni = ⊥-elim (unmet-past rx₁ mt pr xo lv wz fw lw l
                      (λ i → let (y′ , e′ , j) = bproj-mem pr i in ni (subst (_∈ L.map proj₁ rs) (sym (⊕-injˡ k y′ e′)) (∈-map⁺ proj₁ j))) kw)

  -- A WAIT PAST THE LANES' CURSOR AND BEFORE THEIR NEXT ROW IS PAST A
  -- LIVE LANE'S CURSOR AND BEFORE ITS NEXT: the lane's last row the source
  -- met is the lanes'; a later row of it the source met is among its own,
  -- one it never met lies no earlier than a lanes' row past their cursor,
  -- and its end follows its `laneDone`, which, met, would have done it.
  lane-least : ∀ rx₁ {z v rx₂ rs} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q a c} → RO q (out a)
             → AC.Live [] rx₁ q → (oc : OC q rx₁ c)
             → ∀ {w} → w ≼ z → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
             → After (cursor nothing (lane-rows oc)) w × (∀ {y e} → RV.Lane op q a y e → Visible e → After (cursor nothing (lane-rows oc)) y → w ≼ y)
  lane-least rx₁ {z} {v} {rx₂} {rs} mt pr {q} {a} xo lv oc {w} wz fw af lw = first (rows-last oc) , second
    where
      shown : Met σ₃ rs
      shown = met-shown rx₁ mt pr

      first : _ → After (cursor nothing (lane-rows oc)) w
      first (inj₁ eq) = subst (λ c → After c w) (sym eq) tt
      first (inj₂ (y₀ , eq , v₀ , i , _)) =
        let (y′ , e′ , j) = bproj-mem pr i
        in subst (λ c → After c w) (sym eq) (subst (_≺ w) (sym (⊕-injˡ y₀ y′ e′)) (run-below shown af j))

      second : ∀ {y e} → RV.Lane op q a y e → Visible e → After (cursor nothing (lane-rows oc)) y → w ≼ y
      second {y} {end} l _ _ = end-past rx₁ mt pr xo lv wz fw lw l
      second {y} {out b} l _ ay =
        unmet-past rx₁ mt pr xo lv wz fw lw l (λ i → let (_ , j) = in-rows oc i (a , y , xo , refl , l) in ≺-irrefl {y} (run-below (own-run rx₁ mt xo oc) ay j))
      second {e = skip}  _ () _
      second {e = pin _} _ () _

  -- A LIVE LANE IS IDLE WHERE THE LANES ARE: holding a route, it is of the
  -- instant of any position before every lane row still to come.
  live-idle : ∀ rx₁ {z v rx₂ rs} → Met M (rx₁ ++ (z , out v) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q c} → AC.Live [] rx₁ q → OC q rx₁ c
            → ∀ {w} → w ≼ z → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
            → proj₂ c ≡ 0 ⊎ proj₁ c ≡ nameOf w
  live-idle rx₁ mt pr lv@((a , xo , _) , _) oc {w} wz fw af lw =
    let (af′ , lw′) = lane-least rx₁ mt pr xo lv oc wz fw af lw
    in subst (λ r → proj₂ r ≡ 0 ⊎ proj₁ r ≡ nameOf w) (cnt-lane oc)
         (lane-idle-own xo (own-run rx₁ mt xo oc) (lane-rows-end oc) (lane-few rx₁ mt pr xo lv wz fw lw) af′ lw′)


  -- The uncut value standing for a live lane shows its `laneDone`, a row
  -- the scan never met.
  live-shows : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → Met σ₃ rs
             → ∀ {q} → AC.StartIn [] rx₁ q → ¬ AC.DoneIn [] rx₁ q → ¬ AC.CutIn [] rx₁ q
             → ∀ {y q* a*} → σ₃ y end → RO q* (out a*) → RV.Runs op q* → ¬ RV.CutAt op q* y → (q* ≡ q ⊎ (op ≡ switchᶠ × q ≺ q*))
             → Σ Pos λ k → Σ (IE B) λ x → σ₃ k (out x) × After (cursor nothing rs) k × k ≺ y
  live-shows rx₁ {z} {e} {rx₂} {rs} mt pr run {q} si nd nc {y} {q*} {a*} ry xo* rn* nc* rel = shown (done-before xo* rn* nc* ry)
    where
      shown : Σ Pos (λ yd → Σ ℕ λ kd → Σ Pos λ n → RV.Lane op q* a* yd (out (instEmit (mark (laneDone kd)) n)) × yd ≺ y)
            → Σ Pos λ k → Σ (IE B) λ x → σ₃ k (out x) × After (cursor nothing rs) k × k ≺ y
      shown (yd , kd , n , ld , yd≺y) = yd , instEmit (mark (laneDone kd)) n , σd , after-of pr run σd unmet , yd≺y
        where
          σd : σ₃ yd (out (instEmit (mark (laneDone kd)) n))
          σd = σ₃-before xo* rn* ld nc* yd≺y ry end-pin
          unmet : (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark (laneDone kd)) n))) ∈ rx₁ → ⊥
          unmet i = [ (λ eq → nd (done-in eq xo* ld i))
                    , (λ (op≡ , qq*) → cut-met op≡ rx₁ mt si xo* qq* ld i nc) ]′ rel

  -- A LIVE LANE STILL SHOWS A ROW BEFORE THE LANES' END: its `laneDone`,
  -- or, where a later value cuts it, the last value's.
  live-row : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → Met σ₃ rs → ∀ {q} → AC.Live [] rx₁ q
           → ∀ {y} → σ₃ y end → ¬ ¬ Σ Pos λ k → Σ (IE B) λ x → σ₃ k (out x) × After (cursor nothing rs) k × k ≺ y
  live-row rx₁ mt pr run {q} ((a , xo , rn) , si , nd , nc) {y} ry κ = live-pick xo rn ry λ (q* , a* , xo* , rn* , nc* , rel) →
    κ (live-shows rx₁ mt pr run si nd nc ry xo* rn* nc* rel)

  -- THE LANES END WITH THE SCAN HOLDING NONE OF THEIR ROUTES: where the
  -- lanes' next row past what the source met is their end, no lane is live.
  --
  -- REFUTED: cf901010 lane-end-shut over the lanes' own count, by a lane whose inner completes asynchronously: its completion's begin is carried, never stopped
  lane-end-shut : ∀ rx₁ {q a rx₂ rs y} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → Met σ₃ rs → σ₃ y end
                → (∀ {k x} → σ₃ k (out x) → After (cursor nothing rs) k → y ≼ k) → Flat.lanes (St rx₁) ≡ 0
  lane-end-shut rx₁ mt pr run ry all = decidable-stable (Flat.lanes (St rx₁) ℕ.≟ 0) λ nz →
    lanes-live rx₁ mt nz λ (_ , lv , _) → live-row rx₁ mt pr run lv ry λ (_ , _ , rk , ak , ky) → all rk ak ky

  -- WHILE THE SCAN STILL COUNTS A LANE ROUTE, THE LANES' NEXT ROW IS OF
  -- THE SCAN'S INSTANT: a live lane holds a route of it, and is idle there.
  --
  -- REFUTED: 1e9665c7 lane-idle as the lanes' own `Idle`, by a merge whose first lane completes asynchronously while a second is pending: the completion's begin is carried, so the lanes' count keeps its instant as the second lane begins another
  lane-idle : ∀ rx₁ {q a rx₂ rs} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ¬ Flat.lanes (St rx₁) ≡ 0
            → ∀ {w} → w ≼ q → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
            → Flat.at (St rx₁) ≡ nameOf w
  lane-idle rx₁ mt pr nz {w} wz fw af lw = decidable-stable (Flat.at (St rx₁) ≟ᵖ nameOf w) λ ng →
    lanes-live rx₁ mt nz λ (_ , lv , c , oc , c-at , k , ck) →
      [ (λ z → ℕP.0≢1+n (trans (sym z) ck)) , (λ nm → ng (trans (sym c-at) nm)) ]′ (live-idle rx₁ mt pr lv oc wz fw af lw)

  lanes-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
                → Flat.lanes (St rx₁) ≡ 0 ⊎ Flat.at (St rx₁) ≡ nameOf q
  lanes-current rx₁ mt with lane-next rx₁ mt
  ... | rs , pr , run , w , wq , fw , af , outl , endl with Flat.lanes (St rx₁) ℕ.≟ 0
  ...   | yes z = inj₁ z
  ...   | no nz = inj₂ (trans (lane-idle rx₁ mt pr nz (next-≼ wq) fw af
                         (LN.idle-least {cursor nothing rs} {w} (λ ry ay all → nz (lane-end-shut rx₁ mt pr run ry all)) outl endl))
                         (named-at LS.J wq))
    where
      next-≼ : ∀ {w q} → w ≡ q ⊎ q ≡ w ⊕ [ sub LS.J ] → w ≼ q
      next-≼ {w} (inj₁ refl) = ≼-refl {w}
      next-≼ {w} (inj₂ refl) = ≺→≼ {w} {w ⊕ [ sub LS.J ]} (≺-ext w [])
