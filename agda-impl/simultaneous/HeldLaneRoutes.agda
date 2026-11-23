{-# OPTIONS --guardedness #-}

-- THE SCAN'S LANE COUNTER, AGAINST THE LANES THEMSELVES.  Each lane counts
-- its own routes and tells them as carries just before its `laneDone`,
-- which the scan takes off its counter; a cut empties it, a new instant or
-- an over restarts it.  So the counter is at most what the lanes started,
-- never done nor cut, hold of its instant (`lanes-live`): where it is not
-- empty, some such lane holds a route of it.  A live lane holding a route
-- waits on its own next row, so the lanes are idle where it is
-- (`live-idle`), and a live lane still shows a row before the lanes' end
-- (`live-row`).
module simultaneous.HeldLaneRoutes where

open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Properties using (++-assoc; ++-identityʳ; ∷ʳ-injective)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Unit using (tt)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
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
open import denotation.Laws.Worlds using (InvAt; ⊕-injˡ; ⊕-identityʳ)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-≼-≺; ≼-≺-≺; ≺→≼; ≼-or-≻; ≺-irrefl; ≼-refl; ≼-trans; ≼-split; ≺-absurd)
open import denotation.Laws.Truth.Connect.Cuts using (step≼; next≺)
open import denotation.Laws.Fold using (latest)
open import denotation.EmissionSet using (Reach; Dep; module Switch)
open import denotation.Laws.Count using (em; reach-down; child)
open import simultaneous.RealView using (module View; real-to; join-in; cutat-up; lane-at; lane-at₂; lane-one)
open import simultaneous.HeldLanes using (lane-past; bproj-mem; bproj-memʰ; open-cut; open-routing)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.HeldLim using (run-below)
import simultaneous.LaneStart as LaneStart
open import simultaneous.ColdIdle using (aft-or-in)
open import simultaneous.CombSent using (src-op; closing-mark)
open import simultaneous.InstEmit using (instEmit; mark; value; laneDone; laneStart; begin; carry; outerOpen; valuesOf)
open import simultaneous.Project using (run-prefix)
open import denotation.EmissionSet using (Ev; Superseded)
open import Data.Maybe using (just)
open import simultaneous.ScanCount using (rowKind; markAct; row-cut)
open import simultaneous.LaneCount using (kCut)
open import denotation.Read using (Visible; After; cursor; Run) renaming (_∷_ to _∷ᴿ_)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful)
open import simultaneous.SObs using (lone; module Elaborate; Flat; laneB; outerB; closeB; lanePart; burstPart)
open import Data.Bool using (Bool; T; not; true; false)
open import Data.Unit using (⊤)
open import denotation.Position using (last)
open import denotation.EmissionSet using (module Op; module TakeWhile)
open import denotation.Laws.Worlds using (world-after; ok-step)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.LaneLayers using (done-of; Under; under-⊕)
open import denotation.Events using (<ᵖ-between)
open import simultaneous.Layers using (from≺)
open import denotation.Laws.Cut using (ix-asc)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import simultaneous.LaneInnerEnd using (inner-ends)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.Shut using (r₀)
open import simultaneous.Relations using (Met)
open import simultaneous.LaneEpoch using (module Lanes)
open import simultaneous.Routed using (Held; Early; Placed; nameOf)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldComb using (ev; init; past)
open import simultaneous.FlatLanes using (BProj; Tg; brTag; end-last) renaming (keep to bkeep; drop to bdrop)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldSrc using (module CombSrc; named-at)
open import simultaneous.HeldLanes using (module CombLanes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; marked; Out; Input; react; laneˢ; each; shareˢ; counted; framed; undone)

-- A JOINER'S END: its outer has ended there, and every lane run, past its
-- value and never cut.
join-done : ∀ {A B} op (f : A → Den B) (o : EmissionSet A) {y} → View.Join f o op y end
          → Ended o y × (∀ {q a} → o q (out a) → View.Runs f o op q → q ≺ y → ¬ View.CutAt f o op q y → Ended (View.Lane f o op q a) y)
join-done (mergeᶠ nothing)  f o (Joining.oend _ d)         = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done (mergeᶠ nothing)  f o (Joining.lend _ _ _ _ _ d) = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done (mergeᶠ nothing)  f o (Joining.rend () _ _)
join-done (mergeᶠ (just n)) f o (Joining.oend _ d)         = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done (mergeᶠ (just n)) f o (Joining.lend _ _ _ _ _ d) = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done (mergeᶠ (just n)) f o (Joining.rend () _ _)
join-done switchᶠ           f o (Joining.oend _ d)         = proj₁ d , λ x r qy nc → proj₂ d x r qy nc
join-done switchᶠ           f o (Joining.lend _ _ _ _ _ d) = proj₁ d , λ x r qy nc → proj₂ d x r qy nc
join-done switchᶠ           f o (Joining.rend () _ _)
join-done exhaustᶠ          f o (Joining.oend _ d)         = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done exhaustᶠ          f o (Joining.lend _ _ _ _ _ d) = proj₁ d , λ x r qy _ → proj₂ d x r qy (λ ())
join-done exhaustᶠ          f o (Joining.rend () _ _)

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

-- The scan's state past two runs, the first unended, is past the second
-- from where the first left it.
past-++ : ∀ {B} op (o : Out B) xs ys → (∀ {c} → (c , end) ∈ xs → ⊥) → past op o (xs ++ ys) ≡ past op (past op o xs) ys
past-++ op o []                 ys _  = refl
past-++ op o ((_ , out x) ∷ xs) ys ne = past-++ op (react op o x) xs ys (λ i → ne (there i))
past-++ op o ((_ , end) ∷ xs)   ys ne = ⊥-elim (ne (here refl))
past-++ op o ((_ , skip) ∷ xs)  ys ne = past-++ op o xs ys (λ i → ne (there i))
past-++ op o ((_ , pin _) ∷ xs) ys ne = past-++ op o xs ys (λ i → ne (there i))

-- Lane carries, row after row.
data Carries {B : Set} : List (Pos × Ev (Maybe (Input B))) → Set where
  c[] : Carries []
  c∷  : ∀ {k n cs} → Carries cs → Carries ((k , out (Tg laneB (instEmit (mark carry) n))) ∷ cs)

-- EACH CARRY RAISES THE SCAN'S ACCUMULATOR BY ONE.
acc-carries : ∀ {B} op (o : Out B) {cs} → Carries cs → L.length cs + Flat.acc (proj₁ o) ≡ Flat.acc (proj₁ (past op o cs))
acc-carries op o c[] = refl
acc-carries op o (c∷ {cs = cs} cc) = trans (sym (ℕP.+-suc (L.length cs) (Flat.acc (proj₁ o)))) (acc-carries op _ cc)

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
  open Lanes {B} op Own (LaneMark laneStart) (LaneMark laneDone) act LaneEmit using (OC; oc[]; oc-in; oc-out; module Run)

  -- A lane's inner, ahead of its take.
  inner : A → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner a = flatMap (mergeᶠ nothing) (λ k → shareˢ (g a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  postulate
    -- A LIVE LANE IS IDLE WHERE THE LANES ARE: holding a route, it is of the
    -- instant of any position before every lane row still to come.
    live-idle : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q c} → AC.Live [] rx₁ q → OC q rx₁ c
              → ∀ {w} → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → proj₂ c ≡ 0 ⊎ proj₁ c ≡ nameOf w


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
  done-last : ∀ {q a yd y n v} → RO q (out a) → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) → RV.Lane op q a y (out v)
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
  done-final : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
             → ∀ {q v} → LaneEmit q x v → AC.DoneIn [] xs q → ⊥
  done-final rx₁ mt xs x ys eq (a , y , xo , refl , l) dn with find dn
  ... | _ , i , (a′ , yd , n , xo′ , refl , ld) with ro-func xo xo′
  ...   | refl = done-last xo ld l (met-before xs (split-met rx₁ mt xs _ ys eq) i)

  -- A CUT THE SWITCH'S SCAN MEETS IS AN OUTER VALUE'S `outerOpen`, at the
  -- source's reading of the outer's row.
  cut-row : ∀ {rx} → Met M rx → ∀ {x} → x ∈ rx → rowKind markAct switchᶠ x ≡ kCut
          → Σ Pos λ c → Σ A λ a → Σ _ λ n → σ₁ c (out (instEmit (value a) n)) × proj₁ x ≡ c ⊕ [ sub OS.J ] × Σ _ λ v → M (c ⊕ [ sub OS.J ]) (out v)
  cut-row mt {k , out (just (inj₁ (b , instEmit (mark mk) n)))} i kc with open-cut mk kc
  cut-row mt {k , out (just (inj₁ (laneB , _)))} i kc | refl with lane-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , σc , _ = ⊥-elim (σ₃-open σc)
  cut-row mt {k , out (just (inj₁ (closeB , _)))} i kc | refl with close-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , cx , _ = ⊥-elim (closing-mark (close-marks cx) (λ ()) (λ ()))
  cut-row {rx} mt {k , out (just (inj₁ (outerB , _)))} i kc | refl with OS.run′ (subst (λ d → Run (enter d P) nothing rx) (src-op tk env′ m) mt)
  ... | rs , pr , run , _ with bproj-memʰ pr i
  ...   | c′ , instEmit (value a) n′ , refl , j , refl = c′ , a , n′ , proj₁ (run-row∈ run j) , refl , _ , proj₁ (run-row∈ mt i)
  ...   | c′ , instEmit (mark _) _ , refl , j , refl = ⊥-elim (open-routing (Held.routing H₁ (proj₁ (proj₁ (run-row∈ run j)))))
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
    R-from (join-in op fL RO xo rn l (λ c → nc (cutat-up op fL RO {q} {k} {y} ky c))
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
  in-prefix : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
            → ∀ {u} → u ∈ rx₁ ++ (z , e) ∷ rx₂ → proj₁ u ≺ proj₁ x → u ∈ xs
  in-prefix rx₁ {z} {e} {rx₂} mt xs x ys refl {u} i ux with ∈-++⁻ xs (subst (u ∈_) (++-assoc xs (x ∷ ys) ((z , e) ∷ rx₂)) i)
  ... | inj₁ i′ = i′
  ... | inj₂ (here refl) = ⊥-elim (≺-irrefl {proj₁ x} ux)
  ... | inj₂ (there i′) with run-tail xs (subst (Met M) (++-assoc xs (x ∷ ys) ((z , e) ∷ rx₂)) mt)
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
    catch : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
          → ∀ {q a y v k b} → RO q (out a) → x ≡ (y ⊕ [ sub LS.J ] , out (Ln v)) → RV.Lane op q a y (out v)
          → RV.Lane op q a k (out b) → k ≺ y → (k ⊕ [ sub LS.J ] , out (Ln b)) ∈ xs
    catch rx₁ mt xs x ys eq {q} {a} {y} {v} {k} {b} xo x≡ l lk ky =
      let (rs , pr , run , _) = lane-run mt
          (y′ , e′ , j) = bproj-mem pr (∈-++⁺ˡ (subst ((y ⊕ [ sub LS.J ] , out (Ln v)) ∈_) (sym eq) (∈-++⁺ʳ xs (here (sym x≡)))))
      in in-prefix rx₁ mt xs _ ys eq
           (catch-run pr run xo l (subst (λ w → (w , out v) ∈ rs) (sym (⊕-injˡ y y′ e′)) j) lk ky)
           (subst (λ x₀ → (k ⊕ [ sub LS.J ]) ≺ proj₁ x₀) (sym x≡) (lane-J xo lk l ky))

  -- A LANE'S `begin` IS MET PAST ITS `laneStart`: the lane shows the mark
  -- before the `begin`, never cut between, so the lanes show it too, and
  -- their run, having met the later row, met it first.
  begin-started : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
                → ∀ {q n} → LaneEmit q x (instEmit (mark begin) n) → AC.StartIn [] xs q
  begin-started rx₁ mt xs x ys eq {q} (a , y , xo , refl , l) with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
  ... | s , oks , r , _ , back with LaneStart.begin-starts _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s r
  ...   | y₀ , r₀ , sy₀ , y₀y = any-map (λ { refl → a , y₀ , _ , xo , refl , back r₀ sy₀ }) (catch rx₁ mt xs _ ys eq xo refl l (back r₀ sy₀) y₀y)

  -- A LANE'S EMIT THE RUN MET IS A ROW OF THE LANES, of a lane running
  -- and never cut by it.
  emit-σ : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {x q v} → x ∈ rx₁ → LaneEmit q x v
         → Σ Pos λ y → proj₁ x ≡ y ⊕ [ sub LS.J ] × σ₃ y (out v) × RV.Runs op q × ¬ RV.CutAt op q y
  emit-σ rx₁ mt {q = q} {v} i (a , y , xo , refl , l) =
    let (rs , pr , run , _) = lane-run mt
        (y′ , e′ , j) = bproj-mem pr (∈-++⁺ˡ i)
        σy = proj₁ (run-row∈ run (subst (λ w → (w , out v) ∈ rs) (sym (⊕-injˡ y y′ e′)) j))
        (q″ , a″ , xo″ , rn , l″ , nc) = σ₃-lane σy
    in go (emit-one (a , y , xo , refl , l) (a″ , y , xo″ , refl , l″)) σy rn nc
    where
      go : ∀ {q″} → q ≡ q″ → σ₃ y (out v) → RV.Runs op q″ → ¬ RV.CutAt op q″ y
         → Σ Pos λ y₀ → y ⊕ [ sub LS.J ] ≡ y₀ ⊕ [ sub LS.J ] × σ₃ y₀ (out v) × RV.Runs op q × ¬ RV.CutAt op q y₀
      go refl σy rn nc = y , refl , σy , rn , nc

  -- NOTHING OF A LANE IS MET PAST A CUT OF IT: the later value's
  -- `outerOpen` the scan met supersedes the lane before its row.
  cut-final : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
            → ∀ {q v} → LaneEmit q x v → AC.CutIn [] xs q → ⊥
  cut-final rx₁ mt xs x ys eq {q} le ci@(_ , _ , _ , _ , cb) =
    let (xc , _ , kc) = find cb
        op≡ = row-cut op xc kc
        (q′ , a′ , xo′ , qq′ , later) = switch-cut op≡ xs (split-met rx₁ mt xs _ ys eq) ci
        (y , px , σy , rn , nc) = emit-σ rx₁ mt (subst (x ∈_) (sym eq) (∈-++⁺ʳ xs (here refl))) le
    in nc (subst (λ o₀ → RV.CutAt o₀ q y) (sym op≡) (q′ , a′ , xo′ , qq′ , later σy px))

  -- A LANE BEGINS ONLY WHILE LIVE: its `begin` row follows its
  -- `laneStart`, and neither its `laneDone` nor a cut of it.
  emit-live : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
            → ∀ {q n} → LaneEmit q x (instEmit (mark begin) n) → AC.Live [] xs q
  emit-live rx₁ mt xs x ys eq {q} le@(a , y , xo , refl , l) =
    own , begin-started rx₁ mt xs x ys eq le , done-final rx₁ mt xs x ys eq le , cut-final rx₁ mt xs x ys eq le
    where
      own : Own q
      own = let (_ , _ , _ , rn , _) = emit-σ rx₁ mt (subst (_ ∈_) (sym eq) (∈-++⁺ʳ xs (here refl))) le in a , xo , rn

  -- Rows of a met run keep their order.
  met-order : ∀ (xs : List Row) {u ys zs} → Met M (xs ++ u ∷ ys ++ zs) → ∀ {v} → v ∈ ys → proj₁ u ≺ proj₁ v
  met-order xs {u} {ys} {zs} mt {v} j with ∈-∃++ j
  ... | ys₁ , ys₂ , refl =
    met-before (xs ++ u ∷ ys₁) {proj₁ v} {proj₂ v} {ys₂ ++ zs}
      (subst (Met M) (trans (cong (λ t → xs ++ u ∷ t) (++-assoc ys₁ (v ∷ ys₂) zs)) (sym (++-assoc xs (u ∷ ys₁) (v ∷ ys₂ ++ zs)))) mt)
      (∈-++⁺ʳ xs (here refl))

  -- WHERE A LANE'S `laneDone` SITS: under a position `w`, its carries at
  -- `base`'s children before it, and no other row of the lane between.
  record DoneAt (q : Pos) (a : A) (yd w base : Pos) (k : ℕ) : Set where
    field
      w-yd    : Under w yd
      w-base  : Under w base
      carries : ∀ {i} → i ℕ.< k → RV.Lane op q a (base ⊕ [ ix i ]) (out (marked carry)) × (base ⊕ [ ix i ]) ≺ yd
      only    : ∀ {y v} → RV.Lane op q a y (out v) → Under w y → y ≺ yd → Σ ℕ λ i → i ℕ.< k × y ≡ base ⊕ [ ix i ]

  -- THE LANE'S COUNT BEFORE `x`: its rows' emits there, folded in order.
  data FoldAt (q : Pos) (a : A) : Pos → Routes → Set where
    f-none : ∀ {x} → (∀ {y v} → RV.Lane op q a y (out v) → y ≺ x → ⊥) → FoldAt q a x r₀
    f-step : ∀ {x y v r} → FoldAt q a y r → RV.Lane op q a y (out v) → y ≺ x
           → (∀ {y′ v′} → RV.Lane op q a y′ (out v′) → y ≺ y′ → y′ ≺ x → ⊥) → FoldAt q a x (count r v)

  postulate
    -- A LANE'S `laneDone` SITS PAST ITS CARRIES, as many as the lane
    -- counted over its rows before them: its step's split, under the scan's
    -- row, shows the carries, then the `laneDone`, and the scan's state
    -- there is the fold of the frame's values before that row, each the
    -- emit of a lane row before the split.
    done-site : ∀ {q a yd n} → RO q (out a) → RV.Lane op q a yd (out (instEmit (mark laneDone) n))
              → Σ Pos λ w → Σ Pos λ base → Σ Routes λ r → DoneAt q a yd w base (proj₂ r) × FoldAt q a w r

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

  done-at : ∀ {q a yd n} → RO q (out a) → RV.Lane op q a yd (out (instEmit (mark laneDone) n))
          → Σ Pos λ w → Σ Pos λ base → Σ ℕ λ k → DoneAt q a yd w base k
            × (∀ pre rest → Met M (pre ++ rest)
               → (∀ {y v} → RV.Lane op q a y (out v) → y ≺ w → (y ⊕ [ sub LS.J ] , out (Ln v)) ∈ pre)
               → (∀ {u v} → u ∈ pre → LaneEmit q u v → Σ Pos λ y → proj₁ u ≡ y ⊕ [ sub LS.J ] × y ≺ w)
               → ∀ {c} → OC q pre c → proj₂ c ≡ k)
  done-at xo ld =
    let (w , base , r , D , fd) = done-site xo ld
    in w , base , proj₂ r , D , λ pre rest mt h₁ h₂ oc → cong proj₂ (fold-oc xo fd pre rest mt h₁ h₂ oc)

  postulate
    -- A ROW THE RUN MET UNDER A LANE'S `laneDone`'S PLACE, BEFORE IT, IS THE
    -- LANE'S: no other lane's subscription, nor a hot's row, lies there.
    own-under : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {q a yd n w base k} → RO q (out a)
              → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) → DoneAt q a yd w base k
              → ∀ {u} → u ∈ rx₁ → Under w (proj₁ u) → proj₁ u ≺ (yd ⊕ [ sub LS.J ])
              → Σ Pos λ y → Σ (IE B) λ v → u ≡ (y ⊕ [ sub LS.J ] , out (Ln v)) × RV.Lane op q a y (out v)

  -- A position past `w`, before one under it, is under it.
  between-under : ∀ {w u y} → Under w y → w ≺ u → u ≺ y → Under w u
  between-under {w} {u} (ys , refl) wu uy = <ᵖ-between w u ys (from≺ w u wu) (from≺ u (w ⊕ ys) uy)

  under-≼ : ∀ {w y} → Under w y → w ≼ y
  under-≼ {w} ([] , refl) = subst (w ≼_) (sym (⊕-identityʳ w)) (≼-refl {w})
  under-≼ {w} (l ∷ ls , refl) = ≺→≼ {w} {w ⊕ (l ∷ ls)} (≺-ext w ls)

  ix-mono : ∀ p {i j} → (p ⊕ [ ix i ]) ≺ (p ⊕ [ ix j ]) → i ℕ.< j
  ix-mono p {i} {j} lt with ℕP.<-cmp i j
  ... | tri< i<j _ _ = i<j
  ... | tri≈ _ refl _ = ⊥-elim (≺-irrefl {p ⊕ [ ix i ]} lt)
  ... | tri> _ _ j<i = ⊥-elim (≺-absurd {p ⊕ [ ix i ]} {p ⊕ [ ix j ]} lt (ix-asc p j<i))

  -- THE RUN MEETS A LANE'S CARRIES, ROW AFTER ROW, JUST BEFORE ITS `laneDone`.
  module Tail (rx₁ : List Row) {z : Pos} {e : Ev (Maybe (Input B))} {rx₂ : List Row} (mt : Met M (rx₁ ++ (z , e) ∷ rx₂)) (xs ys : List Row)
              {q : Pos} {a : A} {yd w base : Pos} {k : ℕ} {vd : IE B} (xo : RO q (out a))
              (ld : RV.Lane op q a yd (out vd)) (D : DoneAt q a yd w base k)
              (own : ∀ {u} → u ∈ rx₁ → Under w (proj₁ u) → proj₁ u ≺ (yd ⊕ [ sub LS.J ])
                   → Σ Pos λ y → Σ (IE B) λ v → u ≡ (y ⊕ [ sub LS.J ] , out (Ln v)) × RV.Lane op q a y (out v))
              (eq : rx₁ ≡ xs ++ (yd ⊕ [ sub LS.J ] , out (Ln vd)) ∷ ys) where
    open DoneAt D

    J : Pos → Pos
    J y = y ⊕ [ sub LS.J ]

    W : List Row
    W = (z , e) ∷ rx₂

    xd : Row
    xd = (J yd , out (Ln vd))

    cpos : ℕ → Pos
    cpos i = base ⊕ [ ix i ]

    crow : ℕ → Row
    crow i = (J (cpos i) , out (Ln (marked carry)))

    imgs : ℕ → ℕ → List Row
    imgs i zero    = []
    imgs i (suc d) = crow i ∷ imgs (suc i) d

    imgs-carries : ∀ i d → Carries (imgs i d)
    imgs-carries i zero    = c[]
    imgs-carries i (suc d) = c∷ (imgs-carries (suc i) d)

    imgs-length : ∀ i d → L.length (imgs i d) ≡ d
    imgs-length i zero    = refl
    imgs-length i (suc d) = cong suc (imgs-length (suc i) d)

    in-imgs : ∀ i d {r} → r ∈ imgs i d → Σ ℕ λ j → r ≡ crow j
    in-imgs i (suc d) (here refl) = i , refl
    in-imgs i (suc d) (there h)   = in-imgs (suc i) d h

    -- The first row past the carries from `i`, `d` of them.
    nxt-row : ℕ → ℕ → Row
    nxt-row i zero    = xd
    nxt-row i (suc d) = crow i

    nxt-in : ∀ i d → nxt-row i d ∈ imgs i d ++ xd ∷ ys
    nxt-in i zero    = here refl
    nxt-in i (suc d) = here refl

    i<k : ∀ i d → i ℕ.+ suc d ≡ k → i ℕ.< k
    i<k i d sum = subst (suc i ≤_) sum (subst (suc i ≤_) (sym (ℕP.+-suc i d)) (ℕ.s≤s (ℕP.m≤m+n i d)))

    w≺c : ∀ i → w ≺ cpos i
    w≺c i = ≼-≺-≺ {w} {base} {cpos i} (under-≼ w-base) (≺-ext base [])

    asc-≼ : ∀ {i j} → i ≤ j → cpos i ≼ cpos j
    asc-≼ {i} {j} i≤j with ℕP.m≤n⇒m<n∨m≡n i≤j
    ... | inj₁ i<j  = ≺→≼ {cpos i} {cpos j} (ix-asc base i<j)
    ... | inj₂ refl = ≼-refl {cpos i}

    under-of : ∀ {y} → w ≼ y → y ≺ yd → Under w y
    under-of {y} le y≺yd with ≼-split {w} {y} le
    ... | inj₁ wy   = between-under w-yd wy y≺yd
    ... | inj₂ refl = [] , sym (⊕-identityʳ w)

    -- Rows of the met run keep their order.
    ord : ∀ P₁ {r} P₂ → rx₁ ≡ P₁ ++ r ∷ P₂ → ∀ {s} → s ∈ P₂ → proj₁ r ≺ proj₁ s
    ord P₁ {r} P₂ e′ h = met-order P₁ {r} {P₂} {W} (subst (Met M) (trans (cong (_++ W) e′) (++-assoc P₁ (r ∷ P₂) W)) mt) h

    -- A carry lies before every later carry's.
    not-in : ∀ {i} j d → i ℕ.< j → crow i ∈ imgs j d → ⊥
    not-in j zero    i<j ()
    not-in {i} j (suc d) i<j (here e′) = ≺-irrefl {cpos j} (subst (_≺ cpos j) (⊕-injˡ (cpos i) (cpos j) (cong proj₁ e′)) (ix-asc base i<j))
    not-in j (suc d) i<j (there h) = not-in (suc j) d (ℕP.<-trans i<j (ℕP.n<1+n j)) h

    -- A lane row before the first row past the carries from `i` lies before
    -- the `laneDone`, and before each of those carries.
    before-nxt : ∀ i d → i ℕ.+ d ≡ k → ∀ {y e′} → RV.Lane op q a y e′ → J y ≺ proj₁ (nxt-row i d)
               → y ≺ yd × (∀ {j} → i ≤ j → j ℕ.< k → y ≺ cpos j)
    before-nxt i zero sum l lt =
      J-reflect xo l ld lt , λ {j} i≤j j<k → ⊥-elim (ℕP.<⇒≱ j<k (subst (_≤ j) (trans (sym (ℕP.+-identityʳ i)) sum) i≤j))
    before-nxt i (suc d) sum {y} l lt =
      ≺-trans {y} {cpos i} {yd} y≺c (proj₂ cr) , λ {j} i≤j _ → ≺-≼-≺ {y} {cpos i} {cpos j} y≺c (asc-≼ i≤j)
      where
        cr = carries (i<k i d sum)
        y≺c : y ≺ cpos i
        y≺c = J-reflect xo l (proj₁ cr) lt

    -- No lane row lies between carry `i` and the next row past it.
    gap : ∀ i d → i ℕ.+ suc d ≡ k → ∀ {y v} → RV.Lane op q a y (out v) → cpos i ≺ y → J y ≺ proj₁ (nxt-row (suc i) d) → ⊥
    gap i d sum {y} l ciy ynx with before-nxt (suc i) d (trans (sym (ℕP.+-suc i d)) sum) l ynx
    ... | y≺yd , below with only l (between-under w-yd (≺-trans {w} {cpos i} {y} (w≺c i) ciy) y≺yd) y≺yd
    ...   | j , j<k , refl = ≺-irrefl {cpos j} (below (ix-mono base ciy) j<k)

    -- A row the run met past carry `i`, before the next row past it, is none.
    cross : ∀ i d → i ℕ.+ suc d ≡ k → ∀ {u} → u ∈ rx₁ → J (cpos i) ≺ proj₁ u → proj₁ u ≺ proj₁ (nxt-row (suc i) d)
          → proj₁ u ≺ J yd → ⊥
    cross i d sum {u} ui cu unx ux
      with own ui (between-under (under-⊕ w-yd (sub LS.J))
                     (≺-trans {w} {cpos i} {proj₁ u} (w≺c i) (≺-trans {cpos i} {J (cpos i)} {proj₁ u} (≺-ext (cpos i) []) cu)) ux) ux
    ... | y , v , refl , l = gap i d sum l (J-reflect xo (proj₁ (carries (i<k i d sum))) l cu) unx

    -- PEEL ONE CARRY: before the carries from `i + 1`, the run met carry `i`.
    peel : ∀ i d → i ℕ.+ suc d ≡ k → ∀ pre → xs ≡ pre ++ imgs (suc i) d → Σ (List Row) λ pre′ → pre ≡ pre′ ++ [ crow i ]
    peel i d sum pre xs≡ with ∈-++⁻ pre (subst (crow i ∈_) xs≡ (catch rx₁ mt xs xd ys eq xo refl ld (proj₁ (carries (i<k i d sum))) (proj₂ (carries (i<k i d sum)))))
    ... | inj₂ h = ⊥-elim (not-in (suc i) d (ℕP.n<1+n i) h)
    ... | inj₁ h with ∈-∃++ h
    ...   | A₀ , [] , refl = A₀ , refl
    ...   | A₀ , u ∷ B₀ , refl = ⊥-elim (cross i d sum u-in (ord A₀ (u ∷ Rt) rx≡ (here refl)) (ord (A₀ ++ [ crow i ]) Rt rx≡₂ (∈-++⁺ʳ B₀ (nxt-in (suc i) d)))
                                       (ord (A₀ ++ [ crow i ]) Rt rx≡₂ (∈-++⁺ʳ B₀ (∈-++⁺ʳ (imgs (suc i) d) (here refl)))))
      where
        Rt : List Row
        Rt = B₀ ++ (imgs (suc i) d ++ xd ∷ ys)

        rx≡ : rx₁ ≡ A₀ ++ crow i ∷ u ∷ Rt
        rx≡ = trans eq (trans (cong (_++ xd ∷ ys) xs≡)
                (trans (++-assoc (A₀ ++ crow i ∷ u ∷ B₀) (imgs (suc i) d) (xd ∷ ys)) (++-assoc A₀ (crow i ∷ u ∷ B₀) (imgs (suc i) d ++ xd ∷ ys))))

        rx≡₂ : rx₁ ≡ (A₀ ++ [ crow i ]) ++ u ∷ Rt
        rx≡₂ = trans rx≡ (sym (++-assoc A₀ [ crow i ] (u ∷ Rt)))

        u-in : u ∈ rx₁
        u-in = subst (u ∈_) (sym rx≡) (∈-++⁺ʳ A₀ (there (here refl)))

    -- THE RUN MET THE CARRIES FROM `i`, `d` OF THEM, JUST BEFORE THE `laneDone`.
    tail : ∀ d i → i ℕ.+ d ≡ k → Σ (List Row) λ pre → xs ≡ pre ++ imgs i d
    tail zero    i _   = xs , sym (++-identityʳ xs)
    tail (suc d) i sum with tail d (suc i) (trans (sym (ℕP.+-suc i d)) sum)
    ... | pre , xs≡ with peel i d sum pre xs≡
    ...   | pre′ , refl = pre′ , trans xs≡ (++-assoc pre′ [ crow i ] (imgs (suc i) d))

    pre : List Row
    pre = proj₁ (tail k 0 refl)

    xs≡ : xs ≡ pre ++ imgs 0 k
    xs≡ = proj₂ (tail k 0 refl)

    rxp : rx₁ ≡ pre ++ (imgs 0 k ++ xd ∷ ys)
    rxp = trans eq (trans (cong (_++ xd ∷ ys) xs≡) (++-assoc pre (imgs 0 k) (xd ∷ ys)))

    met-pre : Met M (pre ++ (imgs 0 k ++ xd ∷ ys) ++ W)
    met-pre = subst (Met M) (trans (cong (_++ W) rxp) (++-assoc pre (imgs 0 k ++ xd ∷ ys) W)) mt

    -- Every lane row before `w` the run met before the carries.
    below : ∀ {y v} → RV.Lane op q a y (out v) → y ≺ w → (J y , out (Ln v)) ∈ pre
    below {y} {v} l yw with ∈-++⁻ pre (subst ((J y , out (Ln v)) ∈_) xs≡ (catch rx₁ mt xs xd ys eq xo refl ld l (≺-≼-≺ {y} {w} {yd} yw (under-≼ w-yd))))
    ... | inj₁ h = h
    ... | inj₂ h with in-imgs 0 k h
    ...   | j , e′ = ⊥-elim (≺-absurd {y} {w} yw (subst (w ≺_) (sym (⊕-injˡ y (cpos j) (cong proj₁ e′))) (w≺c j)))

    -- Every lane row the run met before the carries lies before `w`.
    above : ∀ {u v} → u ∈ pre → LaneEmit q u v → Σ Pos λ y → proj₁ u ≡ J y × y ≺ w
    above {u} ui (a′ , y , xo′ , refl , l′) with ro-func xo xo′
    ... | refl with ∈-∃++ ui
    ...   | P₁ , P₂ , pe with before-nxt 0 k refl l′
                               (ord P₁ (P₂ ++ (imgs 0 k ++ xd ∷ ys)) (trans rxp (trans (cong (_++ (imgs 0 k ++ xd ∷ ys)) pe) (++-assoc P₁ (u ∷ P₂) (imgs 0 k ++ xd ∷ ys))))
                                    (∈-++⁺ʳ P₂ (nxt-in 0 k)))
    ...     | y≺yd , bl = y , refl , y≺w
      where
        y≺w : y ≺ w
        y≺w with ≼-or-≻ w y
        ... | inj₂ lt = lt
        ... | inj₁ le with only l′ (under-of le y≺yd) y≺yd
        ...   | j , j<k , y≡ = ⊥-elim (≺-irrefl {cpos j} (subst (_≺ cpos j) y≡ (bl ℕ.z≤n j<k)))

  -- A LANE'S `laneDone` IS MET JUST PAST ITS CARRIES: the rows the run
  -- met before it end in exactly as many carries as the lane counted
  -- over the rows before them.
  carries-tail : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
               → ∀ {q n} → LaneEmit q x (instEmit (mark laneDone) n)
               → Σ (List Row) λ pre → Σ (List Row) λ cs → xs ≡ pre ++ cs × Carries cs × (∀ {c} → OC q pre c → proj₂ c ≡ L.length cs)
  carries-tail rx₁ {z} {e} {rx₂} mt xs x ys eq {q} {n} (a , yd , xo , refl , ld) with done-at xo ld
  ... | w , base , k , D , cnt =
    Tl.pre , Tl.imgs 0 k , Tl.xs≡ , Tl.imgs-carries 0 k
    , λ oc → trans (cnt Tl.pre ((Tl.imgs 0 k ++ Tl.xd ∷ ys) ++ Tl.W) Tl.met-pre Tl.below Tl.above oc) (sym (Tl.imgs-length 0 k))
    where module Tl = Tail rx₁ mt xs ys xo ld D (own-under rx₁ mt xo ld D) eq

  -- A count read past a row is the count before it, moved by the row's
  -- emit if the row is the lane's.
  oc-unsnoc : ∀ {q zs c} → OC q zs c → ∀ r x → zs ≡ r ++ [ x ]
            → (Σ Routes λ c′ → Σ (IE B) λ v → OC q r c′ × LaneEmit q x v × c ≡ count c′ v) ⊎ OC q r c
  oc-unsnoc oc[] [] x ()
  oc-unsnoc oc[] (_ ∷ _) x ()
  oc-unsnoc (oc-in {r = r′} {c = c′} {v = v} o l) r x eq with ∷ʳ-injective r′ r eq
  ... | refl , refl = inj₁ (c′ , v , o , l , refl)
  oc-unsnoc (oc-out {r = r′} o _) r x eq with ∷ʳ-injective r′ r eq
  ... | refl , refl = inj₂ o

  -- CARRIES LEAVE A LANE'S COUNT AS IT WAS.
  oc-carries : ∀ {q} pre cs → Carries cs → ∀ {c} → OC q (pre ++ cs) c → OC q pre c
  oc-carries pre [] c[] {c} o = subst (λ z → OC _ z c) (++-identityʳ pre) o
  oc-carries {q} pre ((k , _) ∷ cs) (c∷ {n = n} cc) {c} o
    with oc-unsnoc (oc-carries (pre ++ [ (k , _) ]) cs cc (subst (λ z → OC q z c) (sym (++-assoc pre [ _ ] cs)) o)) pre _ refl
  ... | inj₂ o′ = o′
  ... | inj₁ (c′ , v , o′ , (_ , _ , _ , refl , _) , refl) = o′

  -- A LANE'S `laneDone` IS MET JUST PAST ITS CARRIES: the rows the run
  -- met before it end in at least as many carries as the lane counts.
  carries-before : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
                 → ∀ {q n c} → LaneEmit q x (instEmit (mark laneDone) n) → OC q xs c
                 → Σ (List Row) λ pre → Σ (List Row) λ cs → xs ≡ pre ++ cs × Carries cs × proj₂ c ≤ L.length cs
  carries-before rx₁ mt xs x ys eq le oc with carries-tail rx₁ mt xs x ys eq le
  ... | pre , cs , refl , cc , cnt = pre , cs , refl , cc , ℕP.≤-reflexive (cnt (oc-carries pre cs cc oc))

  -- A LANE'S `laneDone` FOLLOWS THE CARRIES OF ALL IT COUNTED: the scan
  -- has accumulated at least the lane's own count.
  done-carried : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ xs x ys → rx₁ ≡ xs ++ x ∷ ys
               → ∀ {q n c} → LaneEmit q x (instEmit (mark laneDone) n) → OC q xs c → proj₂ c ≤ Flat.acc (St xs)
  done-carried rx₁ mt xs x ys eq {c = c} le oc with carries-before rx₁ mt xs x ys eq le oc
  ... | pre , cs , refl , cc , lc =
    ℕP.≤-trans lc (ℕP.≤-trans (ℕP.m≤m+n (L.length cs) (Flat.acc (St pre)))
      (ℕP.≤-reflexive (trans (acc-carries op (past op init pre) cc) (cong (λ o → Flat.acc (proj₁ o)) (sym (past-++ op init pre cs nopre))))))
    where
      nopre : ∀ {k} → (k , end) ∈ pre → ⊥
      nopre i = end-free rx₁ mt (subst (_ ∈_) (sym eq) (∈-++⁺ˡ (∈-++⁺ˡ i)))

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
      (λ { {q} {x} (a , y , n , xo , eq , l) → n , a , y , xo , eq , l })
      (emit-live rx₁ mt) (done-carried rx₁ mt)
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
                  → Σ Pos λ y → Σ _ λ n → RV.Lane op q a y (out (instEmit (mark laneDone) n)) × y ≺ c
    lane-end-done {q} {a} {c} xo l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
        (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
        (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
    ... | s , oks , r , _ , back with lane-end m undone (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r
    ...   | inj₂ (re , nf) = ⊥-elim (inner-done a re nf)
    ...   | inj₁ (w , a′ , refl , rf , nk) with done-of a′ nk
    ...     | n , refl = w ⊕ [ ix 0 ] , n
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

  cut-at : op ≡ switchᶠ → ∀ xs ys {z e rx₂ q q′ a′ k b} → Met M ((xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys) ++ (z , e) ∷ rx₂)
         → ∀ {x₀} → x₀ ∈ xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys → LaneMark laneStart q x₀
         → RO q′ (out a′) → q ≺ q′ → RV.Lane op q′ a′ k (out b)
         → ∀ {r′ n′} → σ₁ r′ (out (instEmit (value a′) n′)) → q′ ≡ ro-at r′
         → ¬ ¬ AC.CutIn [] (xs ++ (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∷ ys) q
  cut-at op≡ xs ys {z} {e} {rx₂} {q} {q′} {a′} {k} {b} mt {x₀} i₀ (a , y₀ , n₀ , xo , refl , l) xo′ qq′ l′ {r′} σr′ q′≡ nc =
    met-open xs (split-met (xs ++ row ∷ ys) mt xs _ ys refl) σr′ jz
      λ oa → let (o , io , (_ , r″ , n″ , σr″ , q″≡ , o≡)) = find oa
                 (xs₁ , xs₂ , eqx) = ∈-∃++ io
             in cut r″ σr″ q″≡ xs₁ xs₂ (subst (λ o₀ → xs ≡ xs₁ ++ o₀ ∷ xs₂) o≡ eqx) (subst (_∈ xs) o≡ io)
    where
      row = (k ⊕ [ sub LS.J ] , out (Tg laneB b))
      W = (z , e) ∷ rx₂

      jz : (r′ ⊕ [ sub OS.J ]) ≺ (k ⊕ [ sub LS.J ])
      jz = ≺-trans {r′ ⊕ [ sub OS.J ]} {ro-at r′} {k ⊕ [ sub LS.J ]} (J≺ro r′)
             (≺-trans {ro-at r′} {k} {k ⊕ [ sub LS.J ]} (subst (_≺ k) q′≡ (lane-past op fL RO l′)) (≺-ext k []))

      -- The first lane's start, a row of the lanes.
      σs : σ₃ y₀ (out (instEmit (mark laneStart) n₀))
      σs = let (y′ , e′ , _ , σs′) = lane-mark (run-prefix (xs ++ row ∷ ys) mt) i₀ (inj₁ refl)
           in subst (λ w → σ₃ w (out (instEmit (mark laneStart) n₀))) (sym (⊕-injˡ y₀ y′ e′)) σs′

      lane≢outer : ∀ {u : Ev (IE B)} {v} → just u ≡ v → v ≡ nothing → ⊥
      lane≢outer refl ()

      cut : ∀ r″ {a″ n″} → σ₁ r″ (out (instEmit (value a″) n″)) → ro-at r′ ≡ ro-at r″ → ∀ xs₁ xs₂
          → xs ≡ xs₁ ++ (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″)))) ∷ xs₂
          → (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″)))) ∈ xs → ⊥
      cut r″ {n″ = n″} σr″ q″≡ xs₁ xs₂ eqx io = nc (xs₁ , (o′ ∷ xs₂ ++ row ∷ ys) , E , start , here kc)
        where
          o′ = (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″))))

          E : xs ++ row ∷ ys ≡ xs₁ ++ (o′ ∷ xs₂ ++ row ∷ ys)
          E = trans (cong (_++ row ∷ ys) eqx) (++-assoc xs₁ (o′ ∷ xs₂) (row ∷ ys))

          kc : rowKind markAct op o′ ≡ kCut
          kc = subst (λ o₀ → markAct o₀ outerOpen ≡ kCut) (sym op≡) refl

          mt′ : Met M (xs₁ ++ o′ ∷ (xs₂ ++ row ∷ ys) ++ W)
          mt′ = subst (Met M) (trans (cong (_++ W) E) (++-assoc xs₁ (o′ ∷ xs₂ ++ row ∷ ys) W)) mt

          -- No later value had cut the first lane at its start.
          y₀≼ : y₀ ≼ ro-at r″
          y₀≼ lt =
            let (q₀ , a₀ , xo₀ , _ , l₀ , nc₀) = σ₃-lane σs
            in nc₀ (subst (λ w → RV.CutAt op w y₀) (sym (start-one (a₀ , y₀ , n₀ , xo₀ , refl , l₀) (a , y₀ , n₀ , xo , refl , l)))
                     (subst (λ o₀ → RV.CutAt o₀ q y₀) (sym op≡) (q′ , a′ , xo′ , qq′ , subst (_≺ y₀) (sym (trans q′≡ q″≡)) lt)))

          mc : M (r″ ⊕ [ sub OS.J ]) (out (just (inj₁ (outerB , instEmit (mark outerOpen) n″))))
          mc = proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ˡ io)))

          -- So the later value's `outerOpen` lies past the first lane's start.
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
              → Σ Pos λ yd → Σ Pos λ n → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) × yd ≺ y
  done-before {q} {a} {y} xo rn nc ry = from-end (join-done op fL RO (σ-join ry))
    where
      from-lane : ∀ {c} → Σ Pos (λ n → Σ Pos λ yd → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) × yd ≺ c) → c ≼ y
                → Σ Pos λ yd → Σ Pos λ n → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) × yd ≺ y
      from-lane {c} (n , yd , ld , ydc) cy = yd , n , ld , ≺-≼-≺ {yd} {c} {y} ydc cy
      from-end : Ended RO y × (∀ {q a} → RO q (out a) → RV.Runs op q → q ≺ y → ¬ RV.CutAt op q y → Ended (RV.Lane op q a) y)
               → Σ Pos λ yd → Σ Pos λ n → RV.Lane op q a yd (out (instEmit (mark laneDone) n)) × yd ≺ y
      from-end ((co , oe , co≼y) , lanes) =
        let (c* , lc* , c*≼y) = lanes xo rn (≺-≼-≺ {q} {co} {y} (ro-before xo oe) co≼y) nc
            (yd , n , ld , ydc) = lane-end-done xo lc*
        in from-lane {c*} (n , yd , ld , ydc) c*≼y

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
  done-in : ∀ {rx q q* a* yd n} → q* ≡ q → RO q* (out a*) → RV.Lane op q* a* yd (out (instEmit (mark laneDone) n))
          → (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark laneDone) n))) ∈ rx → AC.DoneIn [] rx q
  done-in {rx} {q} {q*} {a*} {yd} {n} refl xo ld i = any-map done-row i
    where
      done-row : ∀ {x} → (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark laneDone) n))) ≡ x → LaneMark laneDone q x
      done-row e = a* , yd , n , xo , sym e , ld

  -- The uncut value standing for a live lane shows its `laneDone`, a row
  -- the scan never met.
  live-shows : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → Met σ₃ rs
             → ∀ {q} → AC.StartIn [] rx₁ q → ¬ AC.DoneIn [] rx₁ q → ¬ AC.CutIn [] rx₁ q
             → ∀ {y q* a*} → σ₃ y end → RO q* (out a*) → RV.Runs op q* → ¬ RV.CutAt op q* y → (q* ≡ q ⊎ (op ≡ switchᶠ × q ≺ q*))
             → Σ Pos λ k → Σ (IE B) λ x → σ₃ k (out x) × After (cursor nothing rs) k × k ≺ y
  live-shows rx₁ {z} {e} {rx₂} {rs} mt pr run {q} si nd nc {y} {q*} {a*} ry xo* rn* nc* rel = shown (done-before xo* rn* nc* ry)
    where
      shown : Σ Pos (λ yd → Σ Pos λ n → RV.Lane op q* a* yd (out (instEmit (mark laneDone) n)) × yd ≺ y)
            → Σ Pos λ k → Σ (IE B) λ x → σ₃ k (out x) × After (cursor nothing rs) k × k ≺ y
      shown (yd , n , ld , yd≺y) = yd , instEmit (mark laneDone) n , σd , after-of pr run σd unmet , yd≺y
        where
          σd : σ₃ yd (out (instEmit (mark laneDone) n))
          σd = σ₃-before xo* rn* ld nc* yd≺y ry end-pin
          unmet : (yd ⊕ [ sub LS.J ] , out (Tg laneB (instEmit (mark laneDone) n))) ∈ rx₁ → ⊥
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
            → ∀ {w} → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
            → Flat.at (St rx₁) ≡ nameOf w
  lane-idle rx₁ mt pr nz {w} fw af lw = decidable-stable (Flat.at (St rx₁) ≟ᵖ nameOf w) λ ng →
    lanes-live rx₁ mt nz λ (_ , lv , c , oc , c-at , k , ck) →
      [ (λ z → ℕP.0≢1+n (trans (sym z) ck)) , (λ nm → ng (trans (sym c-at) nm)) ]′ (live-idle rx₁ mt pr lv oc fw af lw)

  lanes-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂)
                → Flat.lanes (St rx₁) ≡ 0 ⊎ Flat.at (St rx₁) ≡ nameOf q
  lanes-current rx₁ mt with lane-next rx₁ mt
  ... | rs , pr , run , w , wq , fw , af , outl , endl with Flat.lanes (St rx₁) ℕ.≟ 0
  ...   | yes z = inj₁ z
  ...   | no nz = inj₂ (trans (lane-idle rx₁ mt pr nz fw af
                         (LN.idle-least {cursor nothing rs} {w} (λ ry ay all → nz (lane-end-shut rx₁ mt pr run ry all)) outl endl))
                         (named-at LS.J wq))
