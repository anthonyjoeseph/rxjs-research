{-# OPTIONS --guardedness #-}

-- THE SCAN'S SOURCE AGAINST THE REAL FLATMAP: its counters at the
-- closer's `outerDone` against the lanes rxjs runs, and the combined
-- source's laws (`comb`).
module simultaneous.HeldReal where


open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc; ∷-injectiveˡ; ∷-injectiveʳ; length-++)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst; subst₂)

open import Tree using (Obs; FlatOp; of; map; flatMap; mergeᶠ; switchᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; sub; _⊕_; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; DenEnv; module Op; out; end; Few; _≼_; skip; pin; _≺_)
open import simultaneous.SObs using (lone; module Elaborate; Flat; outerB; laneB; closeB; isZero)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Held; Early; nameOf; nm; cnt; Ex)
open import Data.Product.Properties using (×-≡,≡→≡)
open import simultaneous.HeldIn using (Upto)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; Shows; ok-step; _⊑_; InvAt; ⊕-injˡ; ok-in; ⊑-cmp; ⊑-refl; ⊑-inside; ⊕-assoc) renaming (W to Wld)
open import simultaneous.LaneLocal using (inv-ev; Fit)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (Any; here; there) renaming (map to any-map)
open import simultaneous.InstEmit using (begin; instEmit; value; mark; over; outerDone; laneStart; laneDone; burstEnd; Mark)
open import Data.Product using (_×_; _,_; proj₁; Σ; proj₂)
open import Data.Unit using (tt)
open import simultaneous.FlatPark using (past-park)
open import simultaneous.ScanLive using (live-last; holds-at)
open import simultaneous.LiveRuns using (pre-noend)
open import simultaneous.FlatHeld using (LD; Thru; thru-head; held-onset; onset-why; queue-free; bounded?; finished-from; thru-split; past-dead; start-dead;
  burst-clears; find-ld; past-app)
open import simultaneous.TakeCut using (inst-⊕)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.ShowsOps using (module Take)
open import denotation.Laws.Shows using (k-shows; sk-trunc)
open import denotation.Laws.Modulus using (≼-or-≻; ≺-irrefl; ≼-split; ≺→≼; ≺-≼-≺; ≺-ext; ≺-trans; ≺-absurd; ≼-refl; entered-few)
open import simultaneous.HeldBase using (shows-ev; EnvHeld; module FlatHots; IH; Fresh)
open import simultaneous.Routed using (Placed)
open import simultaneous.FlatLanes using (end-last; past-within; co; bproj-end; Within; within; brTag; BProj; Tg; tagged) renaming (keep to bkeep; drop to bdrop)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; undone; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; Out; cut; left)
open import simultaneous.HeldComb using (ev; CombIn; RunHeld; outRows; init; from; past; lay; Local; Locals; locals-runs; local-end;
  run-row; walk; inv-past; step-local)
open import simultaneous.FlatSim using (NoCB; tot)
open import simultaneous.HeldComb using (exact-past; inv-at; RunHeld; ev; run-row)
open import Relation.Nullary.Decidable using (decidable-stable)
open import Relation.Nullary using (¬_)
import Relation.Nullary as Nl
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import simultaneous.Layers using (run-tail; run-after; run-has) renaming (run-row to run-row∈)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺; irrⁱ; triⁱ; transⁱ)
open import denotation.Read using (Visible; After; cursor; Run; loud) renaming (_∷_ to _∷ᴿ_)
open import denotation.Laws.BoundedInv using (end-uniq)
open import Data.Bool using (true; false; _∧_)
open import simultaneous.Project using (run-prefix)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import simultaneous.OuterSplit using (count-open)
open import simultaneous.ScanPast using (run-catch; past-split; left-cut; both-zero; all-drop)
open import simultaneous.RealView using (real-ends; lane-one; nth-out)
open import simultaneous.LaneLayers using (under-ext)
open import simultaneous.HeldBurst using (under-inst; inst-le)
open import simultaneous.InstEmit using (valuesOf)

open import Tree using (Obs; FlatOp; of; map; flatMap; connected)


open import simultaneous.LaneCount using (kDone)
open import simultaneous.ScanCount using (rowKind; markAct; past-active; past-queue; row-cut; row-done)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import simultaneous.HeldSrc using (module CombSrc; between-inst; open-mark; open-value; named-at; next-≼; o-value; o-done; Opens)
open import simultaneous.TrackHeld using (module CombTrack)

open import simultaneous.HeldLanes using (module CombLanes; bproj-back; bproj-mem)
open import simultaneous.HeldLaneRoutes using (module LaneRoutes)
open import simultaneous.LaneTot using (module LaneTot)
open import simultaneous.HeldBurst using (module CombBurst)
open import adequacy.QueuedAt using (few-nth; module QueuedAt)
open import denotation.EmissionSet using (module Bounded; module Values)

module CombReal (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
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
  open CombLanes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃
  open CombTrack m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (track-held)
  open LaneRoutes m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (switch-cut; queue-live)
  open LaneTot m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (value-tot; over-tot)
  open CombBurst m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ using (burst-next; Q; okQ; Id; If; module Start; module Run; lane-σ₃; no-end-before; sent-few)

  -- NO `laneDone` OF A LANE PRECEDES ITS OWN IN THE SCAN.
  done-once : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → DoneMark q x → ¬ AC.DoneIn [] xs q
  done-once r₁ mt xs x ys eq (_ , a , y , n , xo , refl , l) di with find di
  ... | _ , i , (_ , a′ , y′ , n′ , xo′ , refl , l′) with ro-func xo xo′
  ...   | refl with done-one xo l l′
  ...     | refl = ≺-irrefl {y ⊕ [ sub LS.J ]} (met-before xs (split-met r₁ mt xs _ ys eq) i)

  private
    start-before : ∀ {y y₀ kd n n₀} → σ₃ y₀ (out (instEmit (mark laneStart) n₀)) → σ₃ y (out (instEmit (mark (laneDone kd)) n)) → y₀ ≼ y → y₀ ≺ y
    start-before {y} {y₀} σs σd le with ≼-split {y₀} {y} le
    ... | inj₁ lt = lt
    ... | inj₂ refl with InvAt.func I₃ (proj₁ σs) (proj₁ σd)
    ...   | ()

    -- A lane row before one the scan meets is met before it.
    pick : ∀ {y y₀ kd n n₀} → σ₃ y₀ (out (instEmit (mark laneStart) n₀)) → y₀ ≺ y → ∀ ws → Met M ws
         → (y ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark (laneDone kd)) n)))) ∈ ws
         → (y₀ ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark laneStart) n₀)))) ∈ ws
    pick {y} {y₀} {kd} σs lt ws mw i =
      let (_ , pr , run , _) = lane-run mw
          (yd , ed , j) = bproj-mem pr i
      in bproj-back pr (run-has (λ x x′ → InvAt.func I₃ (proj₁ x) (proj₁ x′)) run σs tt tt (subst (y₀ ≼_) (⊕-injˡ y yd ed) (≺→≼ {y₀} {y} lt)) j)

    st-dn : ∀ {k k′ kd n n′} → _≡_ {A = Row} (k , out (just (inj₁ (laneB , instEmit (mark laneStart) n)))) (k′ , out (just (inj₁ (laneB , instEmit (mark (laneDone kd)) n′)))) → ⊥
    st-dn e with cong proj₂ e
    ... | ()

  -- EACH `laneDone` THE SCAN MEETS FOLLOWS ITS LANE'S START THERE.
  done-started : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → DoneMark q x → AC.StartIn [] xs q
  done-started r₁ {z} {e} {r₂} mt xs x ys eq {q} (kd , a , y , n , xo , refl , l) =
    let (y′ , e′ , _ , σd) = lane-mark (run-prefix r₁ mt) (in-r₁ r₁ xs x ys eq) (inj₂ (kd , refl))
    in begun (subst (λ w → σ₃ w (out (instEmit (mark (laneDone kd)) n))) (sym (⊕-injˡ y y′ e′)) σd)
    where
      begun : σ₃ y (out (instEmit (mark (laneDone kd)) n)) → AC.StartIn [] xs q
      begun σd = fin (lane-begins xo l σd)
        where
          mw : Met M (xs ++ [ x ])
          mw = run-prefix (xs ++ [ x ]) (subst (Met M) (sym (++-assoc xs [ x ] (ys ++ (z , e) ∷ r₂))) (split-met r₁ mt xs x ys eq))
          sel : ∀ y₀ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀))
              → (y₀ ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark laneStart) n₀)))) ∈ xs ++ [ x ] → AC.StartIn [] xs q
          sel y₀ n₀ l₀ i = [ (λ i → any-map (λ { refl → a , y₀ , n₀ , xo , refl , l₀ }) i)
                           , (λ { (here e″) → ⊥-elim (st-dn e″) ; (there ()) }) ]′ (∈-++⁻ xs i)
          fin : (Σ Pos λ y₀ → Σ _ λ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) × σ₃ y₀ (out (instEmit (mark laneStart) n₀)) × y₀ ≼ y)
              → AC.StartIn [] xs q
          fin (y₀ , n₀ , l₀ , σs , le) = sel y₀ n₀ l₀ (pick σs (start-before σs σd le) (xs ++ [ x ]) mw (∈-++⁺ʳ xs (here refl)))

  -- A `laneDone` THE SCAN MEETS IS A RUN LANE'S.
  done-mark : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markAct op x ≡ kDone
            → Σ Pos λ q → DoneMark q x × Own q
  done-mark r₁ mt xs x ys eq kx with row-done op x kx
  ... | k , b , n , c , refl with lane-mark (run-prefix r₁ mt) {k = k} {b = b} {mk = laneDone c} {n = n} (in-r₁ r₁ xs _ ys eq) (inj₂ (c , refl))
  ...   | y , refl , refl , σd with σ₃-lane σd
  ...     | q , a , xo , rn , l , _ = q , (c , a , y , n , xo , refl , l) , (a , xo , rn)

  -- A cut the scan meets is the switch's.
  ci-op : ∀ {xs q} → AC.CutIn [] xs q → op ≡ switchᶠ
  ci-op (_ , _ , _ , _ , cb) = let (xc , _ , kc) = find cb in row-cut op xc kc

  -- NO SCAN CUT FALLS BETWEEN A LANE'S START AND ITS `laneDone`.
  done-uncut : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → DoneMark q x → ¬ AC.CutIn [] xs q
  done-uncut r₁ mt xs x ys eq {q} (kd , a , y , n , xo , refl , l) ci
    with switch-cut (ci-op ci) xs (split-met r₁ mt xs _ ys eq) ci | lane-mark (run-prefix r₁ mt) (in-r₁ r₁ xs _ ys eq) (inj₂ (kd , refl))
  ... | q′ , a′ , xo′ , qq′ , later | y′ , e′ , _ , σd with ⊕-injˡ y y′ e′ | σ₃-lane σd
  ...   | refl | q₀ , a₀ , xo₀ , _ , l₀ , nc₀ =
    subst (λ o′ → ¬ RV.CutAt o′ q y) (ci-op ci)
      (subst (λ q″ → ¬ RV.CutAt op q″ y)
        (lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
           (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
           (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo₀ xo l₀ l)
        nc₀)
      (q′ , a′ , xo′ , qq′ , later σd refl)

  -- EACH `laneDone` THE SCAN MEETS ENDS A LANE IT MET START, AND NEVER MET
  -- END OR CUT.
  done-live : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markAct op x ≡ kDone
            → ¬ ¬ Σ Pos λ q → DoneMark q x × AC.Live [] xs q
  done-live r₁ mt xs x ys eq kx κ with done-mark r₁ mt xs x ys eq kx
  ... | q , dm , own = κ (q , dm , own , done-started r₁ mt xs x ys eq dm , done-once r₁ mt xs x ys eq dm , done-uncut r₁ mt xs x ys eq dm)

  -- NO LANE NEVER CUT MEETS A CUT IN THE SCAN.
  cut-never : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q a} → RO q (out a) → ¬ RV.Cut op q → ¬ AC.CutIn [] r₁ q
  cut-never r₁ mt {q} xo nc ci =
    let (q′ , a′ , xo′ , qq′ , _) = switch-cut (ci-op ci) r₁ mt ci
    in subst (λ o′ → ¬ RV.Cut o′ q) (ci-op ci) nc (q′ , a′ , xo′ , qq′)

  private
    -- What `I` precedes, an instant no later than it precedes.
    ins-lt : ∀ {I a b} → ¬ (I ≺ⁱ a) → I ≺ⁱ b → a ≺ⁱ b
    ins-lt {I} {a} {b} na ib with triⁱ a I
    ... | inj₁ aI        = transⁱ aI ib
    ... | inj₂ (inj₁ eq) = subst (_≺ⁱ b) (sym eq) ib
    ... | inj₂ (inj₂ Ia) = ⊥-elim (na Ia)

    -- No later than an instant no later than `I`, no later than `I`.
    ins-le : ∀ {I a b} → ¬ (I ≺ⁱ a) → ¬ (a ≺ⁱ b) → ¬ (I ≺ⁱ b)
    ins-le {I} {a} {b} na nb Ib with triⁱ a b
    ... | inj₁ ab        = nb ab
    ... | inj₂ (inj₁ eq) = na (subst (I ≺ⁱ_) (sym eq) Ib)
    ... | inj₂ (inj₂ ba) = na (transⁱ Ib ba)

    next-row : ∀ {X : Set} (r₂ : List X) {x rx₂} → Σ X λ y → Σ (List X) λ r → r₂ ++ x ∷ rx₂ ≡ y ∷ r
    next-row []      {x} {rx₂} = x , rx₂ , refl
    next-row (y ∷ r) {x} {rx₂} = y , r ++ x ∷ rx₂ , refl

  -- EACH ROW MET BEFORE `z` LIES NO LATER THAN ITS INSTANT.
  before-z : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {k e′} → (k , e′) ∈ r₁ → ¬ (instantOf z ≺ⁱ instantOf k)
  before-z r₁ {z} mt {k} i h = ≺-absurd {k} {z} (met-before r₁ mt i) (instant-≺ z k h)

  -- AN `outerDone` THE SCAN MEETS IS THE CLOSER'S: the outer's routing
  -- marks and the lanes' rows carry none.
  done-close : ∀ {rx} → Met M rx → ∀ {k b n} → (k , out (just (inj₁ (b , instEmit (mark outerDone) n)))) ∈ rx
             → M k (out (just (inj₁ (closeB , instEmit (mark outerDone) n))))
  done-close mt {b = closeB} i = proj₁ (run-row∈ mt i)
  done-close mt {b = laneB} i =
    let (rs , pr , run , _) = lane-run mt
        (y , _ , j) = bproj-mem pr i
    in ⊥-elim (Fit.fine lane-fit (proj₁ (run-row∈ run j)))
  done-close mt {b = outerB} i with outer-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , x , ox , o≡ , _ with open-mark o≡ (λ ())
  ...   | refl with () ← Held.routing H₁ (proj₁ ox)

  -- WITH NO LANE RUNNING OR QUEUED BY OR PAST THE CLOSER'S `outerDone`,
  -- EVERY LANE THE REAL FLATMAP RUNS AND NEVER CUTS HAS ENDED BY AN
  -- INSTANT NO ROW MET PASSES, where it has few rows before a later one:
  -- the lane started before the mark, and the scan's count of lanes
  -- started and not ended is empty there.
  --
  -- REFUTED: 9e244736 `lanes-by` unrestricted, by a switch whose cut lane loops: the scan meets the next value's lane start the real flatMap never reaches, and drops the cut lane from its count
  lanes-by : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
           → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
           → ∀ {I} → (∀ {k e′} → (k , e′) ∈ r₁ → ¬ (I ≺ⁱ instantOf k)) → ¬ (I ≺ⁱ instantOf z₀)
           → ∀ {v} → Few R v → I ≺ⁱ instantOf v
           → RV.LanesBy op I
  lanes-by r₁ mt mz₀ le ow a0 q0 {I} rI Iz Fv Iv {q} {a} x rn nc ¬g =
    lane-started r₁ mt mz₀ le ow q0 Fv (ins-lt Iz Iv) x rn nc λ si →
      AC.drained r₁ (λ xs y ys eq → past-active op init xs y (no-end r₁ mt xs eq))
        (λ { (_ , _ , _ , _ , refl , _) → refl }) (λ { (_ , _ , _ , _ , _ , refl , _) → refl })
        (λ _ _ _ _ _ _ → start-one) (done-live r₁ mt) a0 (a , x , rn) si (cut-never r₁ mt x nc) done-by
    where
      done-by : AC.DoneIn r₁ r₁ q → ⊥
      done-by di with find di
      ... | _ , i , (_ , a′ , y , n′ , x′ , refl , l) with ro-func x x′ | done-ends x′ l
      ...   | refl | c , lc , ic , _ = ¬g (c , lc , λ Ic → rI i (subst (I ≺ⁱ_) (trans ic (sym (inst-⊕ y [ sub LS.J ]))) Ic))

  -- The real flatMap's outer has ended by the closer's `outerDone`.
  outer-by : ∀ {z n} → M z (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → RV.OuterBy (instantOf z)
  outer-by mz with close-sent mz
  ... | _ , w′ , σd , refl with CD.done-under (proj₁ σd)
  ...   | y₁ , e₁ , (ws , refl) with ro-end e₁
  ...     | c′ , rc , ic = c′ , rc , λ h → irrⁱ (subst (instantOf ((y₁ ⊕ ws) ⊕ [ sub w′ ]) ≺ⁱ_) (trans ic i₁) h)
    where
      i₁ : instantOf y₁ ≡ instantOf ((y₁ ⊕ ws) ⊕ [ sub w′ ])
      i₁ = trans (sym (inst-⊕ y₁ ws)) (sym (inst-⊕ (y₁ ⊕ ws) [ sub w′ ]))

  -- WITH NO LANE RUNNING OR QUEUED BY OR PAST THE CLOSER'S `outerDone`,
  -- THE LANES HAVE ENDED BY AN INSTANT NO ROW MET PASSES: its outer has,
  -- and every lane run and never cut.  Asked only where the real flatMap
  -- has few rows before a later instant's row.
  --
  -- REFUTED: 9e244736 `lanes-ended` unrestricted, by a switch whose cut lane loops: the lane never ends, the switch's count drops it at the cut, and the scan meets the closer's `outerDone` with no lane running or queued
  lanes-ended : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
              → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
              → ∀ {I} → (∀ {k e′} → (k , e′) ∈ r₁ → ¬ (I ≺ⁱ instantOf k)) → ¬ (I ≺ⁱ instantOf z₀)
              → ∀ {q} → Few R q → I ≺ⁱ instantOf q
              → ¬ ¬ Σ Pos λ y → σ₃ y end × ¬ (I ≺ⁱ instantOf y)
  lanes-ended r₁ mt {z₀} mz₀ le ow a0 q0 {I} rI Iz Fq Iq ¬g =
    real-ends op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)
      (shows-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))
      (λ a s′ oks → shows-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s′ oks)
      ro-before (proj₁ Fq , λ x lt → proj₂ Fq (R-from x) lt) Iq
      (outer-at (outer-by mz₀)) (lanes-by r₁ mt mz₀ le ow a0 q0 rI Iz Fq Iq)
      λ (y , ry , iy) → ¬g (y , (R-from ry , λ {c′} rc → subst (y ≼_) (end-uniq I₃ (R-from ry) rc) (≼-refl {y})) , iy)
    where
      outer-at : RV.OuterBy (instantOf z₀) → RV.OuterBy I
      outer-at (c , oc , nc) = c , oc , ins-le Iz nc

  -- NO VISIBLE ROW OF THE SOURCE LIES IN AN INSTANT PAST ONE OF ITS
  -- ROWS AND EVERY BRANCH'S END: its own branches' merge ends at the last
  -- of their ends as its readers see them, and the item telling it, at
  -- once, fails the take (`simultaneous.OwnEnds`).
  src-ends : ∀ {y₁ y₂ y₃ z e q a} → σ₁ y₁ end → σ₂ y₂ end → σ₃ y₃ end → M z e → M q (out a) → instantOf z ≺ⁱ instantOf q
           → ¬ (instantOf z ≺ⁱ instantOf y₁) → ¬ (instantOf z ≺ⁱ instantOf y₂) → ¬ (instantOf z ≺ⁱ instantOf y₃) → ⊥
  src-ends {y₁} {y₂} {y₃} {z} {e} {q} {a} r₁ r₂ r₃ _ mq zq n₁ n₂ n₃ =
    OS.dend sh-σ₁ SO.f1 r₁ (Yq {y₁} OS.J n₁) λ t₁ →
    CS.dend sh-σ₂ SC.f1 r₂ (Yq {y₂} CS.J n₂) λ t₂ →
    LS.dend sh-σ₃ SL.f1 r₃ (Yq {y₃} LS.J n₃) λ t₃ →
    fin (OE.merge-end (OS.Rows.m4-lane OS.dpast t₁ , pst (λ zs → outer-past zs r₁) OS.J)
                      (LS.Rows.m4-lane LS.dpast t₃ , pst (λ zs → lanes-past zs r₃) LS.J)
                      (CS.Rows.m4-lane CS.dpast t₂ , pst (λ zs → closer-past zs r₂) CS.J))
    where
      shM4 : Shows OE.M4.JoinT
      shM4 = k-shows λ n → FM4.sk-merge n
      shB3 : Shows OE.B3.JoinT
      shB3 = k-shows λ n → FB3.Bnd.sk-bounded n 1
      shM2 : Shows OE.M2.JoinT
      shM2 = k-shows λ n → FM2.sk-merge n
      shTW : Shows OE.TW.TakeT
      shTW = k-shows λ n → Take.sk-takeT false going (Op.flatMap (mergeᶠ nothing) (λ b → ev m (fed tk b) env′) (Op.of (true ∷ false ∷ []))) P I-fed (sk-trunc (FM2.sk-merge n))

      module SL = LS.Rows.Shown LS.dpast shM4 shB3 shM2 shTW (λ r → proj₂ (InvAt.pinned I-fed r)) (mq′ mq) (LS.dshow sh-σ₃)
      module SO = OS.Rows.Shown OS.dpast shM4 shB3 shM2 shTW (λ r → proj₂ (InvAt.pinned I-fed r)) (mq′ mq) (OS.dshow sh-σ₁)
      module SC = CS.Rows.Shown CS.dpast shM4 shB3 shM2 shTW (λ r → proj₂ (InvAt.pinned I-fed r)) (mq′ mq) (CS.dshow sh-σ₂)

      I-own : InvAt (Hots env′) s₃ OE.Own′
      I-own = subst (λ d → InvAt (Hots env′) s₃ (enter d s₃)) (cat-op tk env′ m) (inv-ev m (Cat-of tk env′ true) env′ g₃ s₃ (FB3.val-ok 0 LS.o₂))

      module FL′ = OE.Fails shM4 shB3 shM2 (end-uniq I-own) SL.f2 SL.f3 SL.f4 SL.nfq

      iq : ∀ {y} → ¬ (instantOf z ≺ⁱ instantOf y) → instantOf y ≺ⁱ instantOf q
      iq {y} n with triⁱ (instantOf y) (instantOf z)
      ... | inj₁ yz        = transⁱ yz zq
      ... | inj₂ (inj₁ eq) = subst (_≺ⁱ instantOf q) (sym eq) zq
      ... | inj₂ (inj₂ zy) = ⊥-elim (n zy)

      iJ : ∀ {y} J → ¬ (instantOf z ≺ⁱ instantOf y) → instantOf (y ⊕ [ sub J ]) ≺ⁱ instantOf q
      iJ {y} J n = subst (_≺ⁱ instantOf q) (sym (inst-⊕ y [ sub J ])) (iq {y} n)

      Yq : ∀ {y} J → ¬ (instantOf z ≺ⁱ instantOf y) → (y ⊕ [ sub J ]) ≼ q
      Yq {y} J n = ≺→≼ {y ⊕ [ sub J ]} {q} (instant-≺ (y ⊕ [ sub J ]) q (iJ {y} J n))

      pst : ∀ {y} → (∀ zs → (P ⊕ zs) ≺ y) → ∀ J → OE.Past (y ⊕ [ sub J ])
      pst {y} yp J zs = ≺-trans {P ⊕ zs} {y} {y ⊕ [ sub J ]} (yp zs) (≺-ext y [])

      fin : (Σ Pos λ c′ → OE.M4.JoinT c′ end × (c′ ≡ y₁ ⊕ [ sub OS.J ] ⊎ c′ ≡ y₃ ⊕ [ sub LS.J ] ⊎ c′ ≡ y₂ ⊕ [ sub CS.J ])) → ⊥
      fin (_ , x , inj₁ refl)        = FL′.own-fails x (pst (λ zs → outer-past zs r₁) OS.J) (iJ {y₁} OS.J n₁)
      fin (_ , x , inj₂ (inj₁ refl)) = FL′.own-fails x (pst (λ zs → lanes-past zs r₃) LS.J) (iJ {y₃} LS.J n₃)
      fin (_ , x , inj₂ (inj₂ refl)) = FL′.own-fails x (pst (λ zs → closer-past zs r₂) CS.J) (iJ {y₂} CS.J n₂)

  -- THE CLOSER ENDS IN ITS `outerDone`'s INSTANT: the mark is its last
  -- part's only item (`CloseDone.FirstEnd.closer-end`).
  closer-ends : ∀ {k n} → σ₂ k (out (instEmit (mark outerDone) n)) → Σ Pos λ y → σ₂ y end × instantOf y ≡ instantOf k
  closer-ends σd with CD.done-under (proj₁ σd)
  ... | y , ry , (ws , refl) with CD.FirstEnd.closer-end ry (few-σ₁ ry) (InvAt.flat I-D₀)
  ...   | c′ , rc , ic = c′ , (rc , λ rc′ → subst (c′ ≼_) (end-uniq I₂ rc rc′) (≼-refl {c′})) , trans ic (sym (inst-⊕ y ws))

  -- WITH NO LANE RUNNING OR QUEUED BY OR PAST THE CLOSER'S `outerDone`,
  -- NO VISIBLE ROW OF THE SOURCE PAST A ROW `w` NO ROW MET PASSES LIES IN
  -- A LATER INSTANT: the outer has ended under the mark, the closer ends
  -- in its instant, and the lanes by `w`'s.
  idle-ends : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
            → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
            → ∀ {w ew} → M w ew → (∀ {k e′} → (k , e′) ∈ r₁ → ¬ (instantOf w ≺ⁱ instantOf k)) → ¬ (instantOf w ≺ⁱ instantOf z₀)
            → ∀ {q a} → M q (out a) → Few R q → w ≺ q → instantOf w ≡ instantOf q
  idle-ends r₁ mt mz₀ le ow a0 q0 {w} mw rI Iz {q} mq Fq wq with close-sent mz₀
  ... | y₂′ , w′ , σd , refl with CD.done-under (proj₁ σd) | closer-ends σd
  ...   | y₁ , e₁ , (ws , refl) | y₂ , e₂ , i₂ =
    decidable-stable (instantOf w ≟ⁱ instantOf q) λ ne →
      lanes-ended r₁ mt mz₀ le ow a0 q0 rI Iz Fq (lt ne) λ (y₃ , e₃ , i₃) →
        src-ends e₁ e₂ e₃ mw mq (lt ne)
          (ins-le Iz (λ h → irrⁱ (subst (instantOf Z ≺ⁱ_) i₁ h))) (ins-le Iz (λ h → irrⁱ (subst (instantOf Z ≺ⁱ_) i₂′ h))) i₃
    where
      Z : Pos
      Z = (y₁ ⊕ ws) ⊕ [ sub w′ ]

      iz : instantOf Z ≡ instantOf (y₁ ⊕ ws)
      iz = inst-⊕ (y₁ ⊕ ws) [ sub w′ ]

      i₁ : instantOf y₁ ≡ instantOf Z
      i₁ = trans (sym (inst-⊕ y₁ ws)) (sym iz)

      i₂′ : instantOf y₂ ≡ instantOf Z
      i₂′ = trans i₂ (sym iz)

      lt : ¬ instantOf w ≡ instantOf q → instantOf w ≺ⁱ instantOf q
      lt = ≺-instant w q wq

  -- PAST THE CLOSER'S `outerDone`, A COUNTED OUTER ROUTE KEEPS THE SOURCE
  -- IN ITS INSTANT: the scan keeps the outer's routes there only with no
  -- lane running or queued, and no outer row follows to count another.
  done-met : ∀ rx₁ {q a rx₂ z n} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → M z (out (just (inj₁ (closeB , instEmit (mark outerDone) n))))
           → Few R q → z ≺ q → ¬ Flat.outer (proj₁ (past op init rx₁)) ≡ 0 → instantOf z ≡ instantOf q
  done-met rx₁ {q} {a} {rx₂} {z} {n} mt mz Fq zq nz with run-catch rx₁ mt mz tt tt zq
  ... | r₁ , r₂ , e″ , refl with InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ʳ r₁ (here refl))))) mz
  ...   | refl = go (isZero (Flat.active s₀) ∧ isZero (Flat.queue s₀)) refl
    where
      xz : Maybe (Input B)
      xz = just (inj₁ (closeB , instEmit (mark outerDone) n))
      s₀ = proj₁ (past op init r₁)
      rest = (q , out a) ∷ rx₂

      mt′ : Met M (r₁ ++ (z , out xz) ∷ (r₂ ++ rest))
      mt′ = subst (Met M) (++-assoc r₁ ((z , out xz) ∷ r₂) rest) mt

      mx : Met M (r₁ ++ (z , out xz) ∷ r₂)
      mx = run-prefix (r₁ ++ (z , out xz) ∷ r₂) mt

      zk : ∀ {k e} → (k , e) ∈ r₂ → z ≺ k
      zk i with run-tail r₁ mt′
      ... | _ ∷ᴿ rn = run-after rn (∈-++⁺ˡ i)

      rk : ∀ {k e} → (k , e) ∈ r₂ → M k e
      rk i = proj₁ (run-row∈ mt′ (∈-++⁺ʳ r₁ (there (∈-++⁺ˡ i))))

      -- No outer row follows the mark.
      nt : ∀ {k e} → (k , e) ∈ r₂ → brTag {B} outerB e ≡ nothing
      nt {k} {out (just (inj₁ (outerB , v)))} i = ⊥-elim (≺-absurd {z} {k} (zk i) (outer-before-done (rk i) mz))
      nt {k} {out (just (inj₁ (laneB , v)))}  i = refl
      nt {k} {out (just (inj₁ (closeB , v)))} i = refl
      nt {k} {out (just (inj₂ _))}            i = refl
      nt {k} {out nothing}                    i = refl
      nt {k} {end}                            i = refl
      nt {k} {skip}                           i = refl
      nt {k} {pin _}                          i = refl

      tl₂ : ∀ a₁ {c} a₂ → r₂ ≡ a₁ ++ (c , end) ∷ a₂ → a₂ ≡ []
      tl₂ a₁ {c} a₂ eq = end-last I-M (r₁ ++ (z , out xz) ∷ a₁)
        (subst (Met M) (trans (cong (λ w → r₁ ++ (z , out xz) ∷ w) eq) (sym (++-assoc r₁ ((z , out xz) ∷ a₁) ((c , end) ∷ a₂)))) mx)

      split≡ : past op init (r₁ ++ (z , out xz) ∷ r₂) ≡ past op (react op (past op init r₁) xz) r₂
      split≡ = past-split op init r₁ (λ a₁ a₂ eq → end-last I-M a₁ (subst (Met M) eq mx))

      go : ∀ b → (isZero (Flat.active s₀) ∧ isZero (Flat.queue s₀)) ≡ b → instantOf z ≡ instantOf q
      go true h with both-zero (Flat.active s₀) (Flat.queue s₀) h
      ... | a0 , q0 = idle-ends r₁ mt′ mz (≼-refl {z}) (z , _ , mz , ≼-refl {z}) a0 q0 mz (before-z r₁ mt′) irrⁱ (proj₁ (run-row∈ mt (∈-++⁺ʳ (r₁ ++ (z , out xz) ∷ r₂) (here refl)))) Fq zq
      go false h = ⊥-elim (nz (trans (cong (λ o → Flat.outer (proj₁ o)) split≡) (ℕP.n≤0⇒n≡0 (Within.le Wo))))
        where
          oz : Flat.outer (proj₁ (react op (past op init r₁) xz)) ≡ 0
          oz = left-cut n (record s₀ { finished = true }) h
          Wo : Within outerB (proj₁ (past op (react op (past op init r₁) xz) r₂)) (root , 0)
          Wo = past-within {A} {B} co (opening {A} {B}) count-open OS.J op (react op (past op init r₁) xz) (root , 0) r₂ [] tl₂
                (all-drop r₂ nt) (within (λ _ → oz) (subst (ℕ._≤ 0) (sym oz) ℕ.z≤n) (inj₁ oz))

  -- WHILE THE SCAN STILL COUNTS AN OUTER ROUTE, AN OUTER END BEFORE THE
  -- SOURCE'S NEXT ROW IS OF THAT ROW'S INSTANT: the source meets that row
  -- no later than the closer's `outerDone`, or past it.
  outer-end-at : ∀ rx₁ {q a rx₂ y} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q → σ₁ y end → y ≺ q → ¬ Flat.outer (proj₁ (past op init rx₁)) ≡ 0
               → nameOf y ≡ nameOf q
  outer-end-at rx₁ {q} {a} {rx₂} {y} mt Fq ry yq nz = decidable-stable (nameOf y ≟ᵖ nameOf q) λ ne →
    close-done ry (proj₁ (run-row∈ mt (∈-++⁺ʳ rx₁ (here refl)))) yq λ where
      (z , zy , inj₁ qz)            → ne (cong (λ i → nm (i ∙ [])) (between-inst {y} {q} {z} yq qz zy))
      (z , zy , inj₂ (n , mz , zq)) → ne (cong (λ i → nm (i ∙ [])) (trans (sym zy) (done-met rx₁ mt mz Fq zq nz)))

  -- THE SCAN'S OUTER COUNTER IS OF THE SOURCE'S NEXT ROW'S INSTANT, OR
  -- NONE: it is of the instant the outer last began, which the outer,
  -- idle, keeps up to its next row, or up to its end.
  outer-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q
                → Flat.outer (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  outer-current rx₁ {q} mt Fq with outer-next rx₁ mt
  ... | rs , pr , mr , w , wq , fw , af , outl , _ with outer-count (run-prefix rx₁ mt) pr
  ...   | inj₁ z = inj₁ z
  ...   | inj₂ (at≡ , k , ck) with Flat.outer (proj₁ (past op init rx₁)) ℕ.≟ 0
  ...     | Nl.yes z = inj₁ z
  ...     | Nl.no nz = inj₂ (trans at≡ (decidable-stable (proj₁ (cnt rs) ≟ᵖ nameOf q) λ ¬g → ¬g (idle-w λ e → ¬g (idle-y e))))
    where
      Cr : Maybe Pos
      Cr = cursor nothing rs

      at-idle : ∀ {v} → Few σ₁ v → After Cr v → (∀ {y e} → σ₁ y e → Visible e → After Cr y → v ≼ y) → proj₁ (cnt rs) ≡ nameOf v
      at-idle fv av lv = [ (λ z → ⊥-elim (ℕP.0≢1+n (trans (sym z) ck))) , (λ n → n) ]′ (outer-idle mr (λ i → bproj-end pr i) fv av lv)

      -- No outer end before `w`: the outer is idle at `w`.
      idle-w : (Σ Pos (λ y → σ₁ y end × After Cr y × y ≺ w) → ⊥) → proj₁ (cnt rs) ≡ nameOf q
      idle-w ne = trans (at-idle fw af lw) (named-at OS.J wq)
        where
          lw : ∀ {y e} → σ₁ y e → Visible e → After Cr y → w ≼ y
          lw {e = out _} ry _ ay    = outl ry ay
          lw {e = end}   ry _ ay yw = ne (_ , ry , ay , yw)
          lw {e = skip}  _  () _
          lw {e = pin _} _  () _

      -- An outer end before it: the outer is idle at that end.
      idle-y : Σ Pos (λ y → σ₁ y end × After Cr y × y ≺ w) → proj₁ (cnt rs) ≡ nameOf q
      idle-y (y , ry , ay , yw) =
        trans (at-idle (proj₁ fw , λ {k} rk ky → proj₂ fw rk (≺-trans {k} {y} {w} ky yw)) ay ly)
              (outer-end-at rx₁ {y = y} mt Fq ry (≺-≼-≺ {y} {w} {q} yw (next-≼ OS.J wq)) nz)
        where
          ly : ∀ {y′ e} → σ₁ y′ e → Visible e → After Cr y′ → y ≼ y′
          ly {y′} {out _} ry′ _ ay′ = ≺→≼ {y} {y′} (≺-≼-≺ {y} {w} {y′} yw (outl ry′ ay′))
          ly {e = end}    ry′ _ _   = Lawful.proper L₁ ry′ ry
          ly {e = skip}   _   () _
          ly {e = pin _}  _   () _

  -- A lane's mark, as the scan's source shows it.
  LnMk : Mark → Pos → Maybe (Input B)
  LnMk mk n = just (inj₁ (laneB , instEmit (mark mk) n))

  -- A CONNECT IN SCOPE KEEPS NO ROUTE PAST ITS INSTANT, read at the
  -- scan's rows: what the scan holds is a connect's last report.
  live-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
               → anyHolds (Flat.at (proj₁ (past op init rx₁))) (Flat.live (proj₁ (past op init rx₁))) ≡ true
               → Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  live-current rx₁ {q} {e} {rx₂} mt v h with live-last op rx₁ (pre-noend rx₁ (run-prefix (rx₁ ++ [ (q , e) ]) (subst (Met M) (sym (++-assoc rx₁ [ (q , e) ] rx₂)) mt))) h
  ... | i , r , hr , li with holds-at hr
  ...   | at≡ , nz = [ (λ z → ⊥-elim (nz z)) , (λ eq → trans (sym at≡) eq) ]′ (track-held rx₁ mt v li)

  -- A BOUNDED MERGE'S LANES COUNTED AT A LANE'S END, by adequacy's census
  -- at the cursor before it: every slot taken and a value waiting, the
  -- queue's head starts one step below the end.
  module Queue (k : ℕ) where
    open Bounded k fL RO using (Sub; Lane)
    open Values RO using (Nth)
    module QA = QueuedAt okQ k fL If (Id Q okQ)

    -- A `laneDone` the scan reads at `x`: its lane, and the lane's end
    -- in its instant.
    record Done (x : Pos) : Set where
      field
        {ce yd q₀} : Pos
        {a₀}       : A
        {b₀}       : IE B
        at-x   : x ≡ yd ⊕ [ sub LS.J ]
        seen   : σ₃ yd (out b₀)
        before : yd ≺ ce
        same   : instantOf ce ≡ instantOf x
        val    : RO q₀ (out a₀)
        row    : Lane q₀ a₀ yd (out b₀)
        ends   : Lane q₀ a₀ ce end

    -- A LANE BEGUN BEFORE A LANE'S END SHOWS ITS START BEFORE IT: the
    -- start lies under the subscription's first child.
    started-by : ∀ {x} (D : Done x) {i q a s} → Sub i q s a → s ≺ Done.ce D
               → Σ Pos λ y → Σ Pos λ n → Lane q a y (out (instEmit (mark laneStart) n)) × y ≺ Done.ce D
    started-by D {i} {q} {a} {s} sb sc =
      let (y , n , r , u) = start-under {a} s
          (j₀ , s₀ , sb₀ , af₀) = Done.ends D
      in y , n , (i , s , sb , r , under-ext s u)
       , QA.row-before sb r (ix 0 ∷ proj₁ u , trans (proj₂ u) (⊕-assoc s [ ix 0 ] (proj₁ u))) sb₀ af₀ sc

    -- A VALUE WHOSE `outerOpen` THE SCAN READS BEFORE A LANE'S ROW LIES
    -- BEFORE THAT ROW.
    opened-before : ∀ {q x q′ a′ y e} → OpenMark q x → Lane q′ a′ y e → proj₁ x ≺ (y ⊕ [ sub LS.J ]) → q ≺ y
    opened-before (_ , _ , _ , σr , refl , refl) l lt = UnderPast.read-past k σr l lt

    -- A `laneDone` READ IS A LANE'S, ENDING IN ITS INSTANT.
    done-at : op ≡ mergeᶠ (just k) → ∀ r₁ {x xl r₂} → Met M (r₁ ++ (x , out xl) ∷ r₂) → LD xl → Done x
    done-at refl r₁ mt (_ , kd , _ , refl) with lane-mark mt (∈-++⁺ʳ r₁ (here refl)) (inj₂ (kd , refl))
    ... | y , refl , refl , σd with σ₃-lane σd
    ...   | q₀ , a₀ , xo , _ , l , _ with done-ends xo l
    ...     | c , lc , ic , yc = record { at-x = refl ; seen = σd ; before = yc ; same = trans ic (sym (inst-⊕ y [ sub LS.J ])) ; val = xo ; row = l ; ends = lc }

    -- A LANE SUBSCRIBED ONE STEP BELOW A LANE'S END SHOWS ITS START IN
    -- THE END'S INSTANT, past the ended lane's `laneDone`: the scan's
    -- source shows the start before the next instant's value.
    start-shown : op ≡ mergeᶠ (just k) → ∀ {x} → (D : Done x)
                → ∀ {i q a} → Sub i q (Done.ce D ⊕ [ ix 1 ]) a
                → ∀ {q′ a′} → M q′ (out a′) → instantOf (Done.ce D) ≺ⁱ instantOf q′
                → ¬ ¬ Σ Pos λ y → Σ Pos λ n → M y (out (LnMk laneStart n)) × x ≺ y × instantOf y ≡ instantOf (Done.ce D)
    start-shown refl {x} D {i} {q} {a} sb {q′} mq cq =
      let (c , n , r , u) = start-under {a} (Done.ce D ⊕ [ ix 1 ]) in go c n r (under-ext (Done.ce D ⊕ [ ix 1 ]) u) (under-inst u)
      where
        open Done D
        xo : RO q (out a)
        xo = nth-out (proj₁ sb)
        rn : RV.Runs (mergeᶠ (just k)) q
        rn = i , a , proj₁ sb
        go : ∀ c n → enter (fL a) (ce ⊕ [ ix 1 ]) c (out (instEmit (mark laneStart) n)) → (ce ⊕ [ ix 1 ]) ≺ c
           → instantOf c ≡ instantOf ((ce ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
           → ¬ ¬ Σ Pos λ y → Σ Pos λ n → M y (out (LnMk laneStart n)) × x ≺ y × instantOf y ≡ instantOf ce
        go c n r sc u-c no =
          lane-σ₃ xo rn l tt (λ ()) (≼-refl {c}) noend (sent-few mq cq′) λ σc →
          Start.Shown.shown-M xo rn l mq cq′ σc refl refl λ mc →
          no (c ⊕ [ sub LS.J ] , n , mc , subst (_≺ (c ⊕ [ sub LS.J ])) (sym at-x) (LS.mono seen σc ycd) , trans (inst-⊕ c [ sub LS.J ]) ic)
          where
            l : RV.Lane (mergeᶠ (just k)) q a c (out (instEmit (mark laneStart) n))
            l = i , _ , sb , r , sc
            ic : instantOf c ≡ instantOf ce
            ic = trans u-c (trans (inst-⊕ (ce ⊕ [ ix 1 ]) [ ix 0 ]) (inst-⊕ ce [ ix 1 ]))
            cq′ : instantOf c ≺ⁱ instantOf q′
            cq′ = subst (_≺ⁱ instantOf q′) (sym ic) cq
            ycd : yd ≺ c
            ycd = ≺-trans {yd} {ce} {c} before (≺-trans {ce} {ce ⊕ [ ix 1 ]} {c} (≺-ext ce []) sc)
            noend : ∀ {d} → R d end → d ≺ c → ⊥
            noend = no-end-before xo rn (λ ()) λ {yd′} ld′ y′c →
              let (y₀ , _ , r₀ , s₀ , lt₀) = lane-starts (Run.fwd xo rn l ld′)
              in ≺-irrefl {c} (≺-trans {c} {yd′} {c} (subst (_≺ yd′) (sym (start-once xo l (Run.back xo rn l r₀ s₀))) lt₀) y′c)

  -- A BOUNDED MERGE'S LANE END WITH A LANE QUEUED STARTS ONE IN ITS
  -- INSTANT: rxjs subscribes the queued lane inside the end, where the
  -- schedule starts it (`Bounded.queued`, at the end's `ix 1`).
  queued-next : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ r₁ {x xl r₂} → Met M (r₁ ++ (x , out xl) ∷ r₂) → LD xl
              → ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0 → ∀ {q a} → M q (out a) → instantOf x ≺ⁱ instantOf q
              → ¬ ¬ Σ Pos λ y → Σ Pos λ n → M y (out (LnMk laneStart n)) × x ≺ y × instantOf y ≡ instantOf x
  queued-next {k} refl r₁ {x} {xl} mt ld nz {q′} mq xq no =
    queue-live refl r₁ mt nz λ (qv , av , xo , oi , ns) →
      let (rw , i , om) = find oi
          qce = ≺-trans {qv} {yd} {ce} (opened-before om row (subst (proj₁ rw ≺_) at-x (met-before r₁ mt i))) before
      in few-nth RO (entered-few (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ]) {qv} {out av} (λ {_} {_} → tt) xo) xo λ (iv , nv) →
         QA.queued-at ends nv qce λ
           { (inj₁ e) → let (_ , sb , sc) = QA.early-at e nv
                            (y , n , l , yce) = started-by D sb sc
                        in between xo ns l yce
           ; (inj₂ (_ , _ , _ , sb)) → start-shown refl D sb mq cq λ (y , n , my , lt , iy) → no (y , n , my , lt , trans iy same) }
    where
      open Queue k
      D : Done x
      D = done-at refl r₁ mt ld
      open Done D

      cq : instantOf ce ≺ⁱ instantOf q′
      cq = subst (_≺ⁱ instantOf q′) (sym same) xq

      -- A begun lane the scan has not seen start starts in the end's
      -- instant, past the `laneDone`.
      between : ∀ {qv av y n} → RO qv (out av) → ¬ Any (LaneMark laneStart qv) r₁
              → RV.Lane (mergeᶠ (just k)) qv av y (out (instEmit (mark laneStart) n)) → y ≺ ce
              → ⊥
      between {qv} {av} {y} {n} xo ns l@(il , _ , sbl , _) yce =
        lane-σ₃ xo rn l tt (λ ()) (≼-refl {y}) noend (sent-few mq yq) λ σy →
        Start.Shown.shown-M xo rn l mq yq σy refl refl λ my →
        [ (λ xy → [ (λ lt → no (y ⊕ [ sub LS.J ] , n , my , lt , squeeze lt))
                  , (λ e → ld-start (subst (λ z → M z (out (LnMk laneStart n))) (sym e) my)) ]′ (≼-split {x} {y ⊕ [ sub LS.J ]} xy))
        , (λ jx → ns (start-caught r₁ mt xo l jx my)) ]′ (≼-or-≻ x (y ⊕ [ sub LS.J ]))
        where
          rn : RV.Runs (mergeᶠ (just k)) qv
          rn = il , av , proj₁ sbl
          yq : instantOf y ≺ⁱ instantOf q′
          yq = inst-le {y} {ce} {q′} yce cq
          noend : ∀ {d} → R d end → d ≺ y → ⊥
          noend = no-end-before xo rn (λ ()) λ {yd′} ld′ y′y →
            let (y₀ , _ , r₀ , s₀ , lt₀) = lane-starts (Run.fwd xo rn l ld′)
            in ≺-irrefl {y} (≺-trans {y} {yd′} {y} (subst (_≺ yd′) (sym (start-once xo l (Run.back xo rn l r₀ s₀))) lt₀) y′y)
          ld-start : M x (out (LnMk laneStart n)) → ⊥
          ld-start mx = no-st ld (InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl)))) mx)
            where
              no-st : ∀ {v} → LD v → out v ≡ out (LnMk laneStart n) → ⊥
              no-st (_ , _ , _ , refl) ()
          squeeze : x ≺ (y ⊕ [ sub LS.J ]) → instantOf (y ⊕ [ sub LS.J ]) ≡ instantOf x
          squeeze lt with triⁱ (instantOf (y ⊕ [ sub LS.J ])) (instantOf x)
          ... | inj₁ wx        = ⊥-elim (≺-irrefl {x} (≺-trans {x} {y ⊕ [ sub LS.J ]} {x} lt (instant-≺ (y ⊕ [ sub LS.J ]) x wx)))
          ... | inj₂ (inj₁ e)  = e
          ... | inj₂ (inj₂ xw) = ⊥-elim (≺-irrefl {y} (≺-trans {y} {ce} {y} yce
                  (instant-≺ ce y (subst₂ _≺ⁱ_ (sym same) (inst-⊕ y [ sub LS.J ]) xw))))

  -- THE LAST LANE'S END KEEPS THE SOURCE IN ITS INSTANT while the scan
  -- holds its routes: the scan finished at the closer's `outerDone`
  -- (`finished-from`), and past the end no lane runs or waits.
  held-final : ∀ r₁ {d xd} r₂ {q a rx₂} → Met M ((r₁ ++ (d , out xd) ∷ r₂) ++ (q , out a) ∷ rx₂) → Few R q → LD xd
             → Flat.queue (proj₁ (past op init r₁)) ≡ 0 → Flat.finished (proj₁ (past op init r₁)) ≡ true
             → Flat.active (proj₁ (past op init r₁)) ℕ.∸ 1 ≡ 0 → instantOf d ≡ instantOf q
  held-final r₁ {d} r₂ {q} {a} {rx₂} mt Fq (b , kd , nd , refl) q0 fi a0 with finished-from op r₁ fi | next-row r₂ {(q , out a)} {rx₂}
  ... | a₁ , k , _ , a₂ , r₁≡ , (bk , nk , refl) | (z , e′) , r₂′ , nx =
    idle-ends rp mtp mz₀ (≺→≼ {k} {z} (met-before rp mtp (∈-++⁺ˡ k-in))) (q , a , mq , zq) a0′ q0′ md rI (before-z r₁ mt₁ k-in) mq Fq dq
    where
      xd′ : Maybe (Input B)
      xd′ = just (inj₁ (b , instEmit (mark (laneDone kd)) nd))

      rp : List Row
      rp = r₁ ++ [ (d , out xd′) ]

      mt₁ : Met M (r₁ ++ (d , out xd′) ∷ (r₂ ++ (q , out a) ∷ rx₂))
      mt₁ = subst (Met M) (++-assoc r₁ ((d , out xd′) ∷ r₂) ((q , out a) ∷ rx₂)) mt

      mtp : Met M (rp ++ (z , e′) ∷ r₂′)
      mtp = subst (Met M) (trans (cong (λ w → r₁ ++ (d , out xd′) ∷ w) nx) (sym (++-assoc r₁ [ (d , out xd′) ] ((z , e′) ∷ r₂′)))) mt₁

      k-in : (k , out (just (inj₁ (bk , instEmit (mark outerDone) nk)))) ∈ r₁
      k-in = subst ((k , out (just (inj₁ (bk , instEmit (mark outerDone) nk)))) ∈_) (sym r₁≡) (∈-++⁺ʳ a₁ (here refl))

      mz₀ : M k (out (just (inj₁ (closeB , instEmit (mark outerDone) nk))))
      mz₀ = done-close mt₁ (∈-++⁺ˡ k-in)

      ne₁ : ∀ {c} → (c , end) ∈ r₁ → ⊥
      ne₁ = no-end rp mtp r₁ refl

      a0′ : Flat.active (proj₁ (past op init rp)) ≡ 0
      a0′ = trans (past-active op init r₁ (d , out xd′) ne₁) a0

      q0′ : Flat.queue (proj₁ (past op init rp)) ≡ 0
      q0′ = trans (past-queue op init r₁ (d , out xd′) ne₁) q0

      md : M d (out xd′)
      md = proj₁ (run-row∈ mt₁ (∈-++⁺ʳ r₁ (here refl)))

      mq : M q (out a)
      mq = proj₁ (run-row∈ mt (∈-++⁺ʳ (r₁ ++ (d , out xd′) ∷ r₂) (here refl)))

      dq : d ≺ q
      dq = met-before (r₁ ++ (d , out xd′) ∷ r₂) mt (∈-++⁺ʳ r₁ (here refl))

      zq : z ≼ q
      zq with subst (λ L → (q , out a) ∈ L) nx (∈-++⁺ʳ r₂ (here refl))
      ... | here eq = subst (λ x → x ≼ q) (cong proj₁ eq) (≼-refl {q})
      ... | there j with run-tail rp mtp
      ...   | _ ∷ᴿ rn = ≺→≼ {z} {q} (run-after rn j)

      rI : ∀ {k′ e″} → (k′ , e″) ∈ rp → ¬ (instantOf d ≺ⁱ instantOf k′)
      rI i with ∈-++⁻ r₁ i
      ... | inj₁ j           = before-z r₁ mt₁ j
      ... | inj₂ (here refl) = irrⁱ
      ... | inj₂ (there ())

  private
    -- A lane's start or end.
    Kind : Maybe (Input B) → Set
    Kind x = (Σ Pos λ n → x ≡ LnMk laneStart n) ⊎ LD x

    -- Before a row of an instant before `I`, of an instant before `I`.
    inst-pre : ∀ {k k′ I} → k ≺ k′ → instantOf k′ ≺ⁱ I → instantOf k ≺ⁱ I
    inst-pre {k} {k′} kk h with triⁱ (instantOf k) (instantOf k′)
    ... | inj₁ lt        = transⁱ lt h
    ... | inj₂ (inj₁ eq) = subst (_≺ⁱ _) (sym eq) h
    ... | inj₂ (inj₂ gt) = ⊥-elim (≺-absurd {k} {k′} kk (instant-≺ k′ k gt))

    -- A row met past `x`, past every row before it.
    cut-in : ∀ pre {x : Row} {rest r₁ y r₂} → pre ++ x ∷ rest ≡ r₁ ++ y ∷ r₂ → ¬ y ∈ (pre ++ [ x ])
           → Σ (List Row) λ ra → rest ≡ ra ++ y ∷ r₂
    cut-in []        {r₁ = []}     eq ny = ⊥-elim (ny (here (sym (∷-injectiveˡ eq))))
    cut-in []        {r₁ = _ ∷ r₁} eq ny = r₁ , ∷-injectiveʳ eq
    cut-in (_ ∷ pre) {r₁ = []}     eq ny = ⊥-elim (ny (here (sym (∷-injectiveˡ eq))))
    cut-in (_ ∷ pre) {r₁ = _ ∷ r₁} eq ny = cut-in pre (∷-injectiveʳ eq) (λ i → ny (there i))

    -- A visible row between `x` and `q` is met between them.
    locate : ∀ pre {x xx} rest {q a rx₂ y v} → Met M ((pre ++ (x , out xx) ∷ rest) ++ (q , out a) ∷ rx₂) → M y (out v) → x ≺ y → y ≺ q
           → Σ (List Row) λ ra → Σ (List Row) λ rb → rest ≡ ra ++ (y , out v) ∷ rb
    locate pre {x} {xx} rest {q} {a} {rx₂} {y} {v} mt my xy yq with run-catch (pre ++ (x , out xx) ∷ rest) mt my tt tt yq
    ... | r₁ , r₂ , e″ , eq with InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ˡ (subst ((y , e″) ∈_) (sym eq) (∈-++⁺ʳ r₁ (here refl)))))) my
    ...   | refl = proj₁ (cut-in pre eq ny) , r₂ , proj₂ (cut-in pre eq ny)
      where
        mt′ : Met M (pre ++ (x , out xx) ∷ (rest ++ (q , out a) ∷ rx₂))
        mt′ = subst (Met M) (++-assoc pre ((x , out xx) ∷ rest) ((q , out a) ∷ rx₂)) mt

        ny : ¬ (y , out v) ∈ (pre ++ [ (x , out xx) ])
        ny i with ∈-++⁻ pre i
        ... | inj₁ j           = ≺-absurd {y} {x} (met-before pre mt′ j) xy
        ... | inj₂ (here e)    = ≺-irrefl {x} (subst (x ≺_) (cong proj₁ e) xy)
        ... | inj₂ (there ())

    regroup : ∀ (pre : List Row) x ra b rb (tl : List Row) → (pre ++ x ∷ (ra ++ b ∷ rb)) ++ tl ≡ (pre ++ x ∷ ra) ++ b ∷ (rb ++ tl)
    regroup pre x ra b rb tl =
      trans (++-assoc pre (x ∷ (ra ++ b ∷ rb)) tl) (trans (cong (λ w → pre ++ x ∷ w) (++-assoc ra (b ∷ rb) tl)) (sym (++-assoc pre (x ∷ ra) (b ∷ (rb ++ tl)))))

  -- THE HANDED ROUTES END IN THE LANE END'S INSTANT: from a lane's start
  -- or end, held through to a row of a later instant, another start or
  -- end of its instant follows before it, or a burst's end with none dead,
  -- which stops what is held, or it is the last lane's end (`held-final`).
  -- Each step moves to a later row of the run, so the run bounds them.
  mutual
    queued-loop : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ fuel pre {x xx} rest {q a rx₂} → ℕ.suc (L.length rest) ℕ.≤ fuel
                → Met M ((pre ++ (x , out xx) ∷ rest) ++ (q , out a) ∷ rx₂) → Few R q → Kind xx
                → instantOf x ≺ⁱ instantOf q → Thru op (react op (past op init pre) xx) rest → ⊥
    queued-loop bd ℕ.zero pre rest () mt Fq kx xq th
    queued-loop bd (ℕ.suc fuel) pre {x} {xx} rest {q} {a} {rx₂} (ℕ.s≤s lt) mt Fq (inj₂ ld) xq th =
      [ (λ qn → queued-next bd pre mt₁ ld qn mq xq λ (y , n , my , xy , iy) →
                  go-to bd fuel pre rest lt mt Fq th my (inj₁ (n , refl)) xy (subst (_≺ⁱ instantOf q) (sym iy) xq))
      , (λ (q0 , fi , a0) → irrⁱ (subst (instantOf x ≺ⁱ_) (sym (held-final pre rest mt Fq ld q0 fi a0)) xq))
      ]′ (onset-why op (past op init pre) ld (thru-head op rest th))
      where
        mt₁ : Met M (pre ++ (x , out xx) ∷ (rest ++ (q , out a) ∷ rx₂))
        mt₁ = subst (Met M) (++-assoc pre ((x , out xx) ∷ rest) ((q , out a) ∷ rx₂)) mt

        mq : M q (out a)
        mq = proj₁ (run-row∈ mt (∈-++⁺ʳ (pre ++ (x , out xx) ∷ rest) (here refl)))
    queued-loop bd (ℕ.suc fuel) pre {x} rest {q} {a} (ℕ.s≤s lt) mt Fq (inj₁ (n , refl)) xq th =
      burst-next mx mq xq λ (b , n′ , kb , xb , ib) → burst-step bd fuel pre rest lt mt Fq th kb xb (subst (_≺ⁱ instantOf q) (sym ib) xq)
      where
        mx : M x (out (LnMk laneStart n))
        mx = proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ʳ pre (here refl))))

        mq : M q (out a)
        mq = proj₁ (run-row∈ mt (∈-++⁺ʳ (pre ++ (x , out (LnMk laneStart n)) ∷ rest) (here refl)))

    -- A burst's end past a lane's start: a lane's end before it is the next
    -- step; with none, nothing dead, so the burst's end stops what is held.
    burst-step : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ fuel pre {x n} rest {q a rx₂} → L.length rest ℕ.≤ fuel
               → Met M ((pre ++ (x , out (LnMk laneStart n)) ∷ rest) ++ (q , out a) ∷ rx₂) → Few R q
               → Thru op (react op (past op init pre) (LnMk laneStart n)) rest
               → ∀ {b n′} → (M b (out (LnMk burstEnd n′)) ⊎ Σ ℕ λ kd → M b (out (LnMk (laneDone kd) n′))) → x ≺ b → instantOf b ≺ⁱ instantOf q → ⊥
    burst-step bd fuel pre rest le mt Fq th (inj₂ (kd , mb)) xb bq = go-to bd fuel pre rest le mt Fq th mb (inj₂ (laneB , kd , _ , refl)) xb bq
    burst-step bd fuel pre {x} {n} rest {q} {a} {rx₂} le mt Fq th {b} {n′} (inj₁ mb) xb bq with locate pre rest mt mb xb (instant-≺ b q bq)
    ... | ra , rb , refl with find-ld ra
    ...   | inj₁ (r₁ , z , xz , r₂ , refl , ldz) =
            go-at bd fuel pre _ le mt Fq th r₁ (r₂ ++ (b , out (LnMk burstEnd n′)) ∷ rb) (++-assoc r₁ ((z , out xz) ∷ r₂) ((b , out (LnMk burstEnd n′)) ∷ rb)) (inj₂ ldz)
              (inst-pre {z} {b} (met-before (pre ++ (x , out (LnMk laneStart n)) ∷ (r₁ ++ (z , out xz) ∷ r₂)) mtb (∈-++⁺ʳ pre (there (∈-++⁺ʳ r₁ (here refl))))) bq)
      where
        mtb : Met M ((pre ++ (x , out (LnMk laneStart n)) ∷ (r₁ ++ (z , out xz) ∷ r₂)) ++ (b , out (LnMk burstEnd n′)) ∷ (rb ++ (q , out a) ∷ rx₂))
        mtb = subst (Met M) (regroup pre (x , out (LnMk laneStart n)) (r₁ ++ (z , out xz) ∷ r₂) (b , out (LnMk burstEnd n′)) rb ((q , out a) ∷ rx₂)) mt
    ...   | inj₂ none = thru-head op rb (proj₂ sp) (burst-clears op (past op o₀ ra) laneB n′ (proj₁ sp) (past-dead op o₀ ra ne none (start-dead op (past op init pre) laneB n)))
      where
        o₀ = react op (past op init pre) (LnMk laneStart n)

        ne : ∀ {c} → (c , end) ∈ ra → ⊥
        ne i = no-end _ mt (pre ++ (x , out (LnMk laneStart n)) ∷ ra) (sym (++-assoc pre ((x , out (LnMk laneStart n)) ∷ ra) ((b , out (LnMk burstEnd n′)) ∷ rb))) (∈-++⁺ʳ pre (there i))

        sp = thru-split op o₀ ra ne th

    -- A start or end shown between `x` and `q`: the next step.
    go-to : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ fuel pre {x xx} rest {q a rx₂} → L.length rest ℕ.≤ fuel
          → Met M ((pre ++ (x , out xx) ∷ rest) ++ (q , out a) ∷ rx₂) → Few R q → Thru op (react op (past op init pre) xx) rest
          → ∀ {y v} → M y (out v) → Kind v → x ≺ y → instantOf y ≺ⁱ instantOf q → ⊥
    go-to bd fuel pre rest {q} le mt Fq th {y} my kv xy yq with locate pre rest mt my xy (instant-≺ y q yq)
    ... | ra , rb , eq = go-at bd fuel pre rest le mt Fq th ra rb eq kv yq

    -- A start or end met past `x`: the run past it is shorter.
    go-at : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ fuel pre {x xx} rest {q a rx₂} → L.length rest ℕ.≤ fuel
          → Met M ((pre ++ (x , out xx) ∷ rest) ++ (q , out a) ∷ rx₂) → Few R q → Thru op (react op (past op init pre) xx) rest
          → ∀ ra {z xz} rb → rest ≡ ra ++ (z , out xz) ∷ rb → Kind xz → instantOf z ≺ⁱ instantOf q → ⊥
    go-at bd fuel pre {x} {xx} rest {q} {a} {rx₂} le mt Fq th ra {z} {xz} rb refl kz zq =
      queued-loop bd fuel (pre ++ (x , out xx) ∷ ra) rb lt′ mt′ Fq kz zq th′
      where
        lt′ : ℕ.suc (L.length rb) ℕ.≤ fuel
        lt′ = ℕP.≤-trans (ℕP.m≤n+m (ℕ.suc (L.length rb)) (L.length ra)) (subst (ℕ._≤ fuel) (length-++ ra) le)

        mt′ : Met M (((pre ++ (x , out xx) ∷ ra) ++ (z , out xz) ∷ rb) ++ (q , out a) ∷ rx₂)
        mt′ = subst (λ r → Met M (r ++ (q , out a) ∷ rx₂)) (sym (++-assoc pre ((x , out xx) ∷ ra) ((z , out xz) ∷ rb))) mt

        ne-pre : ∀ {c} → (c , end) ∈ pre → ⊥
        ne-pre i = no-end _ mt pre refl i

        ne : ∀ {c} → (c , end) ∈ ra → ⊥
        ne i = no-end _ mt (pre ++ (x , out xx) ∷ ra) (sym (++-assoc pre ((x , out xx) ∷ ra) ((z , out xz) ∷ rb))) (∈-++⁺ʳ pre (there i))

        th′ : Thru op (react op (past op init (pre ++ (x , out xx) ∷ ra)) xz) rb
        th′ = subst (λ o → Thru op (react op o xz) rb) (sym (past-app op init pre ne-pre))
                (proj₂ (thru-split op (react op (past op init pre) xx) ra ne th))

  -- A BOUNDED MERGE'S LANE END HANDING ITS ROUTES TO A QUEUED LANE KEEPS
  -- THE SOURCE IN ITS INSTANT while the scan holds them: a row of a later
  -- instant is ruled out step by step from the end (`queued-loop`).
  held-queued : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ r₁ {d xd} r₂ {q a rx₂} → Met M ((r₁ ++ (d , out xd) ∷ r₂) ++ (q , out a) ∷ rx₂) → Few R q → LD xd
              → Thru op (react op (past op init r₁) xd) r₂ → instantOf d ≡ instantOf q
  held-queued bd r₁ {d} r₂ {q} mt Fq ld th with triⁱ (instantOf d) (instantOf q)
  ... | inj₂ (inj₁ eq) = eq
  ... | inj₂ (inj₂ qd) = ⊥-elim (≺-absurd {d} {q} (met-before (r₁ ++ (d , out _) ∷ r₂) mt (∈-++⁺ʳ r₁ (here refl))) (instant-≺ q d qd))
  ... | inj₁ dq        = ⊥-elim (queued-loop bd (ℕ.suc (L.length r₂)) r₁ r₂ ℕP.≤-refl mt Fq (inj₂ ld) dq th)

  -- A LANE'S END HANDING ITS ROUTES TO A QUEUED LANE: only a bounded merge
  -- queues (`queue-free`).
  held-handoff : ∀ r₁ {d xd} r₂ {q a rx₂} → Met M ((r₁ ++ (d , out xd) ∷ r₂) ++ (q , out a) ∷ rx₂) → Few R q → LD xd
               → ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0
               → Thru op (react op (past op init r₁) xd) r₂ → instantOf d ≡ instantOf q
  held-handoff r₁ r₂ mt Fq ld qn th with bounded? op
  ... | inj₁ (_ , eq) = held-queued eq r₁ r₂ mt Fq ld th
  ... | inj₂ nb       = ⊥-elim (qn (queue-free op nb r₁))

  -- THE ROUTES THE SCAN HOLDS ARE OF THE SOURCE'S NEXT ROW'S INSTANT, OR
  -- NONE: held since a lane's end, in its instant (`held-onset`), which a
  -- live lane's count put the scan in.
  held-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q
               → Flat.held (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  held-current rx₁ {q} {a} {rx₂} mt Fq with Flat.held (proj₁ (past op init rx₁)) ℕ.≟ 0
  ... | Nl.yes z = inj₁ z
  ... | Nl.no nz with held-onset op rx₁ nz
  ...   | r₁ , d , xd , r₂ , refl , ld , _ , ln , at≡ , th = inj₂ (trans at≡ (trans at-d (cong (λ i → nm (i ∙ [])) inst)))
    where
      mt′ : Met M (r₁ ++ (d , out xd) ∷ (r₂ ++ (q , out a) ∷ rx₂))
      mt′ = subst (Met M) (++-assoc r₁ ((d , out xd) ∷ r₂) ((q , out a) ∷ rx₂)) mt

      at-d : Flat.at (proj₁ (past op init r₁)) ≡ nameOf d
      at-d = [ (λ z → ⊥-elim (ln z)) , (λ a → a) ]′
        (LaneRoutes.lanes-current m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ r₁ mt′)

      why : ¬ Flat.queue (proj₁ (past op init r₁)) ≡ 0
          ⊎ (Flat.queue (proj₁ (past op init r₁)) ≡ 0 × Flat.finished (proj₁ (past op init r₁)) ≡ true × Flat.active (proj₁ (past op init r₁)) ℕ.∸ 1 ≡ 0)
          → instantOf d ≡ instantOf q
      why (inj₁ qn)              = held-handoff r₁ r₂ mt Fq ld qn th
      why (inj₂ (q0 , fi , a0)) = held-final r₁ r₂ mt Fq ld q0 fi a0

      inst : instantOf d ≡ instantOf q
      inst = why (onset-why op (past op init r₁) ld (thru-head op r₂ th))

  parked-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → Flat.parked (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  parked-current rx₁ mt v with past-park op init rx₁ (inj₁ refl)
  ... | inj₁ z = inj₁ z
  ... | inj₂ h = inj₂ (live-current rx₁ mt v h)

  -- No closer's row begins a route.
  no-cb : ∀ {q n} → MRow q (out (just (inj₁ (closeB , instEmit (mark begin) n)))) → ⊥
  no-cb (close y) = closing-mark (close-marks y) (λ ()) (λ ())

  nocb : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → ∀ r₁ {q′ x} r₂ → rx₁ ≡ r₁ ++ (q′ , out x) ∷ r₂ → NoCB x
  nocb rx₁ {q} {e} {rx₂} mt r₁ {q′} r₂ refl refl =
    no-cb (m-rows (proj₁ (run-row r₁ (subst (Met M) (++-assoc r₁ ((q′ , _) ∷ r₂) ((q , e) ∷ rx₂)) mt))) tt)

  -- What the scan sends at a value, a live over and the end is its
  -- counters, which the branches keep open there.
  value-open : ∀ rx₁ {q b x rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , x)))) ∷ rx₂) → Opens x → ¬ Ex cs′ q
             → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
  value-open rx₁ mt o ne = let (k , e) = value-tot rx₁ mt o ne in k , trans (exact-past op rx₁ (nocb rx₁ mt)) e

  over-open : ∀ rx₁ {q b n rx₂} → Met M (rx₁ ++ (q , out (just (inj₁ (b , instEmit (mark over) n)))) ∷ rx₂)
            → Flat.spent (proj₁ (past op init rx₁)) ≡ false → ¬ Ex cs′ q
            → Σ ℕ λ k → proj₂ (from r₀ (outRows op init rx₁)) ≡ suc k
  over-open rx₁ mt sp ne = let (k , e) = over-tot rx₁ mt sp ne in k , trans (exact-past op rx₁ (nocb rx₁ mt)) e

  end-open : ∀ rx₁ {q rx₂} → Met M (rx₁ ++ (q , end) ∷ rx₂) → ¬ Ex cs′ q
           → Σ ℕ λ k → from r₀ (outRows op init rx₁) ≡ (nameOf q , suc k)
  end-open rx₁ mt ne =
    let (a≡ , k , e) = end-tot rx₁ mt ne
    in k , ×-≡,≡→≡ (trans (inv-at (inv-past op rx₁)) a≡ , trans (exact-past op rx₁ (nocb rx₁ mt)) e)

  -- Four counters each of the instant or none: their sum is.
  sum-current : ∀ {X : Set} (a b c d : ℕ) → (a ≡ 0 ⊎ X) → (b ≡ 0 ⊎ X) → (c ≡ 0 ⊎ X) → (d ≡ 0 ⊎ X) → a + b + c + d ≡ 0 ⊎ X
  sum-current .0 .0 .0 .0 (inj₁ refl) (inj₁ refl) (inj₁ refl) (inj₁ refl) = inj₁ refl
  sum-current _ _ _ _ (inj₂ x) _ _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₂ x) _ _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₂ x) _ = inj₂ x
  sum-current _ _ _ _ (inj₁ _) (inj₁ _) (inj₁ _) (inj₂ x) = inj₂ x

  flat-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q
               → tot (proj₁ (past op init rx₁)) ≡ 0 ⊎ Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q
  flat-current rx₁ mt Fq = sum-current (Flat.outer st) (Flat.lanes st) (Flat.held st) (Flat.parked st)
    (outer-current rx₁ mt Fq) (LaneRoutes.lanes-current m ρ op f s env cs gd eh hf p ok fr ep H₁ tp L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃ rx₁ mt) (held-current rx₁ mt Fq) (parked-current rx₁ mt tt)
    where st = proj₁ (past op init rx₁)

  start-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q
                → proj₂ (from r₀ (outRows op init rx₁)) ≡ 0 ⊎ proj₁ (from r₀ (outRows op init rx₁)) ≡ nameOf q
  start-current rx₁ mt Fq with flat-current rx₁ mt Fq
  ... | inj₁ z = inj₁ (trans (exact-past op rx₁ (nocb rx₁ mt)) z)
  ... | inj₂ a = inj₂ (trans (inv-at (inv-past op rx₁)) a)

  early : ∀ {q b a n} → M q (out (just (inj₁ (b , instEmit (value a) n)))) → Early q
  early x with m-rows x tt
  ... | outer y eq = ⊥-elim (open-value eq)
  ... | lane {w = w} y = early-inst [ sub w ] (lane-early y)
  ... | close y = ⊥-elim (closing-value (close-marks y))

  ends : ∀ {q} → M q end → Early q
  ends x with m-rows x tt
  ... | under {zs} = early-inst zs ep₃
  ... | done {zs = zs} b = early-inst zs (bend b)
    where
      bend : ∀ {c} → BEnd c → Early c
      bend (b-outer {w = w} y) = early-inst [ sub w ] (Held.ends H₁ (proj₁ y))
      bend (b-lane {w = w} y)  = early-inst [ sub w ] (lane-ends y)
      bend (b-close {w = w} y) = early-inst [ sub w ] (close-ends y)

  comb-runs : ∀ {rx} → Met M rx → Upto (Few R) rx → RunHeld cs′ (outRows op init rx)
  comb-runs {rx} mt up = locals-runs (walk op cs′ init r₀ rx step fin) (comb-shut mt)
    where
      step : ∀ rx₁ {q x} rx₂ → rx ≡ rx₁ ++ (q , out x) ∷ rx₂
           → Locals cs′ (from r₀ (outRows op init rx₁)) (lay q 0 (proj₂ (react op (past op init rx₁) x)))
      step rx₁ {q} {x} rx₂ refl =
        step-local op cs′ (past op init rx₁) (from r₀ (outRows op init rx₁)) q x (inv-past op rx₁) (start-current rx₁ mt (up (∈-++⁺ʳ rx₁ (here refl))))
          (λ { refl → named (proj₁ (run-row rx₁ mt)) })
          (λ { refl ne → value-open rx₁ mt o-value ne })
          (λ { refl sp ne → over-open rx₁ mt sp ne })
          (λ { refl ne → value-open rx₁ mt o-done ne })
          (λ j → rootOf-ext q (ix 1 ∷ ix j ∷ []))

      fin : ∀ rx₁ {q} rx₂ → rx ≡ rx₁ ++ (q , end) ∷ rx₂ → Local cs′ (from r₀ (outRows op init rx₁)) q end
      fin rx₁ rx₂ refl = local-end (end-open rx₁ mt)

  comb : CombIn (Few R) op M cs′
  comb = record { named = named ; early = early ; ends = ends ; late = late ; done = mdone ; runs = comb-runs }
