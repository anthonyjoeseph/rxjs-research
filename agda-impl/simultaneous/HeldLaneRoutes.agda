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
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.List.Relation.Unary.Any.Properties using (++⁻)
open import Data.Unit using (tt)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; nothing)
open import Data.Nat using (ℕ; suc)
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (decidable-stable)

open import Tree using (Obs; FlatOp; mergeᶠ; switchᶠ; exhaustᶠ; connected; takeWhile; flatMap; of)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (DenEnv; out; end; Few; _≼_; _≺_; enter; hot; EmissionSet; Den; Ended; module Joining)
open import Data.Empty using (⊥; ⊥-elim)
open import denotation.Laws.Worlds using (InvAt; ⊕-injˡ)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-≼-≺; ≺→≼; ≼-or-≻; ≺-irrefl)
open import denotation.Laws.Count using (em; reach-down)
open import simultaneous.RealView using (module View; real-to; join-in; cutat-up; lane-at)
open import simultaneous.HeldLanes using (lane-past)
open import simultaneous.Layers using () renaming (run-row to run-row∈)
open import simultaneous.ColdIdle using (aft-or-in)
open import simultaneous.CombSent using (src-op)
open import simultaneous.InstEmit using (instEmit; mark; value; laneDone; laneStart; outerOpen; valuesOf)
open import simultaneous.Project using (run-prefix)
open import denotation.EmissionSet using (Ev; Superseded)
open import Data.Maybe using (just)
open import simultaneous.ScanCount using (rowKind; markAct)
open import simultaneous.LaneCount using (kCut)
open import denotation.Read using (Visible; After; cursor)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful)
open import simultaneous.SObs using (lone; module Elaborate; Flat; laneB; outerB; lanePart; burstPart)
open import Data.Bool using (Bool; T; not; true)
open import Data.Unit using (⊤)
open import denotation.Position using (last)
open import denotation.EmissionSet using (module Op; module TakeWhile)
open import denotation.Laws.Worlds using (world-after; ok-step)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.LaneStart using (done-of)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Held; Early; Placed; nameOf)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.HeldComb using (ev; init; past)
open import simultaneous.FlatLanes using (BProj; Tg; brTag) renaming (keep to bkeep; drop to bdrop)
open import simultaneous.LaneSplit using (Ln)
open import simultaneous.HeldSrc using (module CombSrc; named-at)
open import simultaneous.HeldLanes using (module CombLanes)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; laneˢ; each; shareˢ; counted; framed; undone)

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
  data OC (q : Pos) : List Row → Routes → Set where
    oc[]   : OC q [] r₀
    oc-in  : ∀ {r c x v} → OC q r c → LaneEmit q x v → OC q (r ++ [ x ]) (count c v)
    oc-out : ∀ {r c x} → OC q r c → (∀ {v} → LaneEmit q x v → ⊥) → OC q (r ++ [ x ]) c

  -- A lane's inner, ahead of its take.
  inner : A → Obs Timeline (IE B ∷ IE A ∷ ⊤ ∷ Δ) (IE B)
  inner a = flatMap (mergeᶠ nothing) (λ k → shareˢ (g a k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))

  postulate
    -- THE COUNTER IS AT MOST WHAT THE LIVE LANES HOLD OF ITS INSTANT: where
    -- it is not empty, a lane started, never done nor cut, holds a route of
    -- the scan's instant.
    lanes-live : ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ¬ Flat.lanes (St rx₁) ≡ 0
               → ¬ ¬ Σ Pos λ q → AC.Live [] rx₁ q × Σ Routes λ c → OC q rx₁ c × proj₁ c ≡ Flat.at (St rx₁) × Σ ℕ λ k → proj₂ c ≡ suc k

    -- A LIVE LANE IS IDLE WHERE THE LANES ARE: holding a route, it is of the
    -- instant of any position before every lane row still to come.
    live-idle : ∀ rx₁ {z e rx₂ rs} → Met M (rx₁ ++ (z , e) ∷ rx₂) → BProj laneB (λ x → x) LS.J rx₁ rs → ∀ {q c} → AC.Live [] rx₁ q → OC q rx₁ c
              → ∀ {w} → Few σ₃ w → After (cursor nothing rs) w → (∀ {y e} → σ₃ y e → Visible e → After (cursor nothing rs) y → w ≼ y)
              → proj₂ c ≡ 0 ⊎ proj₁ c ≡ nameOf w

    -- A LANE'S INNER NEVER ENDS BEFORE ITS `laneDone`: its counted frame
    -- sends it as the lane's source completes, and the inner ends only
    -- once both parts have.
    inner-done : ∀ a {s c} → Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) s → enter (ev m (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀)) s c end
               → ¬ TakeWhile.Failed true undone (enter (ev m (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀)) s) c → ⊥

    -- A SWITCH'S LANES END PAST A LAST VALUE: past any value before the
    -- lanes' end lies one no later value cuts by it.  Owed: the end's
    -- reach lists every joiner row before it, each value's silent row
    -- among them, so a greatest value is there.
    last-before : op ≡ switchᶠ → ∀ {y} → σ₃ y end → ∀ {q a} → RO q (out a) → q ≺ y
                → ¬ ¬ Σ Pos λ q* → Σ A λ a* → RO q* (out a*) × q ≼ q* × ¬ RV.CutAt op q* y

  -- A LANE'S END FOLLOWS ITS `laneDone`: the take stops just past it.
  lane-end-done : ∀ {q a c} → RO q (out a) → RV.Lane op q a c end
                → Σ Pos λ y → Σ _ λ n → RV.Lane op q a y (out (instEmit (mark laneDone) n)) × y ≺ c
  lane-end-done {q} {a} {c} xo l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
  ... | s , oks , r , _ , back with lane-end m undone (inner a) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r
  ...   | inj₂ (re , nf) = ⊥-elim (inner-done a oks re nf)
  ...   | inj₁ (w , a′ , refl , rf , nk) with done-of a′ nk
  ...     | n , refl = w ⊕ [ ix 0 ] , n
                     , back rf (world-after (InvAt.world (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) rf)
                                            (InvAt.real (inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks) rf))
                     , ix<last w

  -- The lanes' rows, as the joiner shows them.
  σ-join : ∀ {y e} → σ₃ y e → RV.Join op y e
  σ-join σy = proj₁ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σy))

  -- A lane's row before a row of the lanes, never cut by it, is the lanes'.
  σ₃-before : ∀ {q a k b y} → RO q (out a) → RV.Runs op q → RV.Lane op q a k (out b) → ¬ RV.CutAt op q y → k ≺ y → σ₃ y end → σ₃ k (out b)
  σ₃-before {q} {a} {k} {b} {y} xo rn l nc ky σy =
    R-from (join-in op fL RO xo rn l (λ c → nc (cutat-up op fL RO {q} {k} {y} ky c))
           , reach-down {q = y} {w = k} {e = end} {e₁ = out b}
               (proj₂ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σy))) ky tt)
    , λ {c} ce → ≺→≼ {k} {c} (≺-≼-≺ {k} {y} {c} ky (proj₂ σy ce))

  -- A LANE ROW THE SCAN NEVER MET LIES PAST THE LANES' RUN.
  after-of : ∀ {rx rs} → BProj laneB (λ x → x) LS.J rx rs → Met σ₃ rs → ∀ {k b} → σ₃ k (out b)
           → ((k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∈ rx → ⊥) → After (cursor nothing rs) k
  after-of {rs = []}    pr run σk nm = tt
  after-of {rs = _ ∷ _} pr run σk nm with aft-or-in run σk tt (here refl)
  ... | inj₁ a = a
  ... | inj₂ (e′ , i) with InvAt.func I₃ (proj₁ σk) (proj₁ (proj₁ (run-row∈ run i)))
  ...   | refl = ⊥-elim (nm (bproj-in pr i))

  -- Rows of a met run keep their order.
  met-order : ∀ (xs : List Row) {u ys zs} → Met M (xs ++ u ∷ ys ++ zs) → ∀ {v} → v ∈ ys → proj₁ u ≺ proj₁ v
  met-order xs {u} {ys} {zs} mt {v} j with ∈-∃++ j
  ... | ys₁ , ys₂ , refl =
    met-before (xs ++ u ∷ ys₁) {proj₁ v} {proj₂ v} {ys₂ ++ zs}
      (subst (Met M) (trans (cong (λ t → xs ++ u ∷ t) (++-assoc ys₁ (v ∷ ys₂) zs)) (sym (++-assoc xs (u ∷ ys₁) (v ∷ ys₂ ++ zs)))) mt)
      (∈-++⁺ʳ xs (here refl))

  -- A LATER VALUE'S LANE ROW THE SCAN MET PAST A LANE'S START CUTS IT IN
  -- THE SCAN: the later value's `outerOpen` lies before its lane's rows,
  -- and past the first lane's start, which no later value had cut.
  cut-met : op ≡ switchᶠ → ∀ rx₁ {z e rx₂} → Met M (rx₁ ++ (z , e) ∷ rx₂) → ∀ {q} → AC.StartIn [] rx₁ q
          → ∀ {q′ a′ k b} → RO q′ (out a′) → q ≺ q′ → RV.Lane op q′ a′ k (out b)
          → (k ⊕ [ sub LS.J ] , out (Tg laneB b)) ∈ rx₁ → ¬ ¬ AC.CutIn [] rx₁ q
  cut-met op≡ rx₁ {z} {e} {rx₂} mt {q} si {q′} {a′} {k} {b} xo′ qq′ l′ i κ with find si | ∈-∃++ i
  ... | x₀ , i₀ , (a , y₀ , n₀ , xo , refl , l) | xs , ys , refl with ro-row xo′
  ...   | r′ , _ , σr′ , refl =
    met-open xs (split-met (xs ++ _ ∷ ys) mt xs _ ys refl) σr′
      (≺-trans {r′ ⊕ [ sub OS.J ]} {ro-at r′} {k ⊕ [ sub LS.J ]} (J≺ro r′)
        (≺-trans {ro-at r′} {k} {k ⊕ [ sub LS.J ]} (lane-past op fL RO l′) (≺-ext k [])))
      λ oa → let (o , io , (a″ , r″ , n″ , σr″ , q′≡ , o≡)) = find oa in cut o io r″ σr″ q′≡ o≡
    where
      row = (k ⊕ [ sub LS.J ] , out (Tg laneB b))
      W = (z , e) ∷ rx₂

      -- The first lane's start, a row of the lanes.
      σs : σ₃ y₀ (out (instEmit (mark laneStart) n₀))
      σs with lane-mark (run-prefix (xs ++ row ∷ ys) mt) i₀ (inj₁ refl)
      ... | y′ , e′ , _ , σs′ = subst (λ w → σ₃ w (out (instEmit (mark laneStart) n₀))) (sym (⊕-injˡ y₀ y′ e′)) σs′

      lane≢outer : ∀ {u : Maybe (Ev (IE B))} {v} → just u ≡ v → v ≡ nothing → ⊥
      lane≢outer refl ()

      cut : ∀ o → o ∈ xs → ∀ r″ {a″ n″} → σ₁ r″ (out (instEmit (value a″) n″)) → ro-at r′ ≡ ro-at r″
          → o ≡ (r″ ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n″)))) → ⊥
      cut o io r″ {n″ = n″} σr″ q′≡ refl with ∈-∃++ io
      ... | xs₁ , xs₂ , eqx = κ (xs₁ , (o′ ∷ xs₂ ++ row ∷ ys) , E , start , here kc)
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
          y₀≼ lt with σ₃-lane σs
          ... | q₀ , a₀ , xo₀ , _ , l₀ , nc₀ =
            nc₀ (subst (λ w → RV.CutAt op w y₀) (sym (start-one (a₀ , y₀ , n₀ , xo₀ , refl , l₀) (a , y₀ , n₀ , xo , refl , l)))
                  (subst (λ o₀ → RV.CutAt o₀ q y₀) (sym op≡) (ro-at r′ , a′ , xo′ , qq′ , subst (_≺ y₀) (sym q′≡) lt)))

          mc : M (r″ ⊕ [ sub OS.J ]) (out (just (inj₁ (outerB , instEmit (mark outerOpen) n″))))
          mc = proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ˡ io)))

          -- So the later value's `outerOpen` lies past the first lane's start.
          opened : (r″ ⊕ [ sub OS.J ]) ≺ (y₀ ⊕ [ sub LS.J ]) → ⊥
          opened lt with ≼-or-≻ (r″ ⊕ [ sub OS.J ]) y₀
          ... | inj₁ xy = lane-in-outer op≡ σr″ σs xy y₀≼
          ... | inj₂ yx = ≺-irrefl {r″ ⊕ [ sub OS.J ]} (≺-≼-≺ {r″ ⊕ [ sub OS.J ]} {y₀ ⊕ [ sub LS.J ]} {r″ ⊕ [ sub OS.J ]} lt
                            (lane-under σs (subst (λ d → enter d P (r″ ⊕ [ sub OS.J ]) (out _)) (src-op tk env′ m) mc) yx))

          start : AC.StartIn [] xs₁ q
          start with ++⁻ xs₁ (subst (_ ∈_) E i₀)
          ... | inj₁ j = any-map (λ { refl → a , y₀ , n₀ , xo , refl , l }) j
          ... | inj₂ (here eq) = ⊥-elim (lane≢outer (cong (λ r → brTag {B} laneB (proj₂ r)) eq) refl)
          ... | inj₂ (there j) = ⊥-elim (opened (met-order xs₁ mt′ j))

