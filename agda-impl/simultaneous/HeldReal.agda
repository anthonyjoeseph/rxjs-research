{-# OPTIONS --guardedness #-}

-- THE SCAN'S SOURCE AGAINST THE REAL FLATMAP: its counters at the
-- closer's `outerDone` against the lanes rxjs runs, and the combined
-- source's laws (`comb`).
module simultaneous.HeldReal where


open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; FlatOp; of; map; flatMap; mergeᶠ)
open import denotation.Position using (Pos; root; _≟ᵖ_; _≟ⁱ_; ix; sub; last; _⊕_; _∙_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; DenEnv; module Op; Ev; out; end; Few; _≼_; EmissionSet; skip; pin; _≺_)
open import simultaneous.SObs using (lone; module Elaborate; Flat; outerB; laneB; closeB; isZero)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Routing; Held; Early; nameOf; nm; Valued; opos; cnt)
open import simultaneous.HeldIn using (Upto)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; Shows; ok-step; _⊑_; InvAt; ⊕-injˡ)
open import simultaneous.LaneLocal using (inv-ev; late-ext; Fit)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import simultaneous.HeldConnect using (early-inst; rootOf-ext)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import simultaneous.InstEmit using (begin; completed; instEmit; value; mark; over; outerDone; Mark; laneStart; laneDone)
open import Data.Product using (_×_; _,_; proj₁; Σ; proj₂)
open import Data.Unit using (tt)
open import simultaneous.FlatPark using (past-park)
open import simultaneous.TakeCut using (inst-⊕)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.ShowsOps using (module Take)
open import denotation.Laws.Shows using (k-shows; sk-trunc)
open import denotation.Laws.Modulus using (T-not; ≺-irrefl; ≼-split; ≺→≼; ≺-≼-≺; ≺-ext; ≺-trans; ≺-absurd; ≼-refl)
open import simultaneous.HeldBase using (shows-ev; EnvHeld; module FlatHots; IH)
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
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.Readings using (rootOf; instantOf)
open import simultaneous.Instants using (_≺ⁱ_; ≺-instant; instant-≺; irrⁱ; triⁱ; transⁱ)
open import denotation.Read using (Visible; After; cursor; Run; loud) renaming (_∷_ to _∷ᴿ_)
open import denotation.Laws.BoundedInv using (end-uniq)
open import Data.Bool using (Bool; T; not; true; false; _∧_)
open import simultaneous.Project using (run-prefix)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import simultaneous.OuterSplit using (count-open)
open import simultaneous.ScanPast using (run-catch; past-split; left-cut; both-zero; all-drop)
open import simultaneous.RealView using (module View; real-from; real-to; real-ends; lane-at; lane-at₂; lane-one; join-out)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.TakeKit using (ix<last)
open import denotation.EmissionSet using (Den; Truncate)
open import simultaneous.InstEmit using (valuesOf)

open import Tree using (Obs; FlatOp; of; map; flatMap; connected; takeWhile; switchᶠ)


open import simultaneous.LaneCount using (module Count; kDone)
open import simultaneous.ScanCount using (rowKind; markAct; past-active; row-cut; row-done)
open import Data.List.Membership.Propositional using (find)
open import Data.List.Membership.Propositional.Properties using (∈-∃++; ∈-++⁻)
open import simultaneous.HeldSrc using (module CombSrc; between-inst; open-mark; open-value; named-at; next-≼; o-value; o-done)

-- A LANE'S TAKE ENDS BESIDE ITS FAILING VALUE: the take's `ix 0` row of a
-- failing value at `w` has the take's end at `w`'s `last`.
module _ {X : Set} {H : Pos → Set} (keep : X → Bool) (d : Den X) (s : Pos) (iv : InvAt H s (enter d s)) where
  private module TB = TakeBack true keep d s iv

  take-fail : ∀ {k a} → enter (Op.takeWhile true keep d) s k (out a) → T (not (keep a))
            → Σ Pos λ w → k ≡ w ⊕ [ ix 0 ] × enter (Op.takeWhile true keep d) s (w ⊕ [ last ]) end
  take-fail (TB.pass _ kp _ , _)     nk = ⊥-elim (T-not kp nk)
  take-fail (TB.fail x nk′ nf _ , _) _  = _ , refl , TB.up (TB.stop x nk′ nf)

  -- and fails once.
  take-once : ∀ {k k′ a a′} → enter (Op.takeWhile true keep d) s k (out a) → T (not (keep a))
            → enter (Op.takeWhile true keep d) s k′ (out a′) → T (not (keep a′)) → k ≡ k′
  take-once (TB.pass _ kp _ , _)     nk _                        _   = ⊥-elim (T-not kp nk)
  take-once (TB.fail _ _ _ _ , _)    _  (TB.pass _ kp _ , _)     nk′ = ⊥-elim (T-not kp nk′)
  take-once (TB.fail x nk nF _ , _)  _  (TB.fail x′ nk′ nF′ _ , _) _ = cong (_⊕ [ ix 0 ]) (TB.first-uniq x nk nF x′ nk′ nF′)

lane-take : ∀ m {Γ X} (keep : X → Bool) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ s → Ok (Hots ρ) s
          → ∀ {k a} → enter (ev m (takeWhile true keep o) ρ) s k (out a) → T (not (keep a))
          → Σ Pos λ w → k ≡ w ⊕ [ ix 0 ] × enter (ev m (takeWhile true keep o) ρ) s (w ⊕ [ last ]) end
lane-take nothing  keep o ρ g s ok = take-fail keep (ev nothing o ρ) s (inv-ev nothing o ρ g s ok)
lane-take (just n) keep o ρ g s ok = take-fail keep (ev (just n) o ρ) s (inv-ev (just n) o ρ g s ok)

lane-once : ∀ m {Γ X} (keep : X → Bool) (o : Obs Timeline Γ X) (ρ : DenEnv Γ) → GoodEnv ρ → ∀ s → Ok (Hots ρ) s
          → ∀ {k k′ a a′} → enter (ev m (takeWhile true keep o) ρ) s k (out a) → T (not (keep a))
          → enter (ev m (takeWhile true keep o) ρ) s k′ (out a′) → T (not (keep a′)) → k ≡ k′
lane-once nothing  keep o ρ g s ok = take-once keep (ev nothing o ρ) s (inv-ev nothing o ρ g s ok)
lane-once (just n) keep o ρ g s ok = take-once keep (ev (just n) o ρ) s (inv-ev (just n) o ρ g s ok)

-- No lane mark is read above a flatMap.
lane-routing : ∀ {mk} → mk ≡ laneStart ⊎ mk ≡ laneDone → Routing mk → ⊥
lane-routing (inj₁ refl) ()
lane-routing (inj₂ refl) ()

-- A BRANCH'S ROW A PROJECTION MEETS IS KEPT, one `sub J` below its own,
bproj-mem : ∀ {B b J} {rx : List (Pos × Ev (Maybe (Input B)))} {rs k x}
          → BProj b (λ x → x) J rx rs → (k , out (Tg b x)) ∈ rx → Σ Pos λ y → k ≡ y ⊕ [ sub J ] × (y , out x) ∈ rs
bproj-mem (bkeep pr)      (here refl) = _ , refl , here refl
bproj-mem (bkeep pr)      (there i)   = let (y , e , j) = bproj-mem pr i in y , e , there j
bproj-mem {b = b} (bdrop nb pr) (here refl) = ⊥-elim (tagged b nb)
bproj-mem (bdrop nb pr)   (there i)   = bproj-mem pr i

-- and each of the branch's rows it keeps is met.
bproj-back : ∀ {B b J} {rx : List (Pos × Ev (Maybe (Input B)))} {rs y x}
           → BProj b (λ x → x) J rx rs → (y , out x) ∈ rs → (y ⊕ [ sub J ] , out (Tg b x)) ∈ rx
bproj-back (bkeep pr)    (here refl) = here refl
bproj-back (bkeep pr)    (there i)   = there (bproj-back pr i)
bproj-back (bdrop _ pr)  i           = there (bproj-back pr i)

module CombReal (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
               (s : Obs Timeline Γ A) (env : DenEnv Δ) (cs : List Pos) (gd : GoodEnv env) (eh : EnvHeld ρ env cs)
               (hf : ∀ a {Δ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ′) → IH m ρ′ (f a))
               (p : Pos) (ok : Ok (Hots env) p) (ep : Early p)
               (H₁ : Held (enter (ev m (FlatHots.trig m ρ op f s env p) (FlatHots.env₀ m ρ op f s env p)) (FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]))
                          ((FlatHots.c m ρ op f s env p ⊕ [ ix 1 ]) ∷ p ∷ cs))
               (L₁ : Lawful (FlatHots.σ₁ m ρ op f s env p)) (L₂ : Lawful (FlatHots.σ₂ m ρ op f s env p))
               (L₃ : Lawful (FlatHots.σ₃ m ρ op f s env p))
               (ok₁ : Ok (Hots (hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p)) (FlatHots.p₀ m ρ op f s env p))
               (ok₂ : Ok (Hots (hot (FlatHots.σ₂ m ρ op f s env p) ∷ hot (FlatHots.σ₁ m ρ op f s env p) ∷ FlatHots.env₀ m ρ op f s env p))
                         (FlatHots.p₀₀ m ρ op f s env p))
               (ok₃ : Ok (Hots (FlatHots.env′ m ρ op f s env p)) (FlatHots.P m ρ op f s env p))
               (ep₃ : Early (FlatHots.P m ρ op f s env p)) where
  open FlatHots m ρ op f s env p
  open CombSrc m ρ op f s env cs gd eh hf p ok ep H₁ L₁ L₂ L₃ ok₁ ok₂ ok₃ ep₃

  -- THE REAL FLATMAP, READ THROUGH ITS POLICY: its outer is the hot
  -- outer's values, each lane a value's elaborated lane.
  fL : A → Den (IE B)
  fL a = ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀)

  RO : EmissionSet A
  RO = enter (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ])

  module RV = View fL RO

  R-from : ∀ {k e} → Truncate (RV.Join op) k e → R k e
  R-from = real-from m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ])

  postulate
    -- THE REAL FLATMAP'S OUTER ENDS AFTER ITS VALUES, IN THE HOT OUTER'S
    -- END'S INSTANT: the hot outer's values each end their own lane at once.
    ro-before : ∀ {q a c} → RO q (out a) → RO c end → q ≺ c
    ro-end    : ∀ {y} → σ₁ y end → Σ Pos λ c → RO c end × instantOf c ≡ instantOf y

  -- THE ROWS OF THE SCAN'S SOURCE, AS THE LANE COUNT READS THEM: a value
  -- `q` of the real flatMap's outer owns its lane's marks, each read one
  -- `sub` below where the lanes show it.
  Row : Set
  Row = Pos × Ev (Maybe (Input B))

  Own : Pos → Set
  Own q = Σ A λ a → RO q (out a) × RV.Runs op q

  LaneMark : Mark → Pos → Row → Set
  LaneMark mk q x = Σ A λ a → Σ Pos λ y → Σ Pos λ n → RO q (out a)
    × x ≡ (y ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark mk) n)))) × RV.Lane op q a y (out (instEmit (mark mk) n))

  act : List Row → ℕ
  act r = Flat.active (proj₁ (past op init r))

  module AC = Count _≟ᵖ_ (rowKind markAct op) Own (LaneMark laneStart) (LaneMark laneDone) act

  postulate
    -- A LANE BEGINS WITH ITS `laneStart`, a row of the real flatMap at or
    -- before each of the lane's rows there.
    lane-begins : ∀ {q a y b} → RO q (out a) → RV.Lane op q a y (out b) → σ₃ y (out b)
                → Σ Pos λ y₀ → Σ _ λ n → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n)) × σ₃ y₀ (out (instEmit (mark laneStart) n)) × y₀ ≼ y

    -- A SWITCH'S ARRIVAL THE SCAN MEETS PAST A LANE'S START IS A LATER
    -- VALUE'S, before every lane row the scan meets next.
    switch-cut : op ≡ switchᶠ → ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q} → AC.CutIn [] r₁ q
               → Σ Pos λ q′ → Σ A λ a′ → RO q′ (out a′) × q ≺ q′ × (∀ {y e′} → σ₃ y e′ → z ≡ y ⊕ [ sub LS.J ] → q′ ≺ y)

    -- A LANE RUN AND NEVER CUT HAS STARTED BY THE CLOSER'S `outerDone`, with
    -- no lane queued there.
    --
    -- RECOVERY: git show ea69c2b2:agda-impl/simultaneous/ScanCount.agda restores `past-queue`, the bounded merge's queue counter row by row
    lane-started : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
                 → Flat.queue (proj₁ (past op init r₁)) ≡ 0 → ∀ {v} → Few R v → instantOf z ≺ⁱ instantOf v
                 → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ RV.Cut op q → ¬ ¬ AC.StartIn [] r₁ q



  -- EACH `laneStart` IS ONE LANE'S: no two values' lanes start at one row.
  start-one : ∀ {x q q′} → LaneMark laneStart q x → LaneMark laneStart q′ x → q ≡ q′
  start-one (_ , y , _ , xo , refl , l) (_ , y′ , _ , xo′ , e , l′) with ⊕-injˡ y y′ (cong proj₁ e)
  ... | refl = lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo xo′ l l′

  -- A LANE ENDS IN ITS `laneDone`'s INSTANT.
  done-ends : ∀ {q a y n} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark laneDone) n))
            → Σ Pos λ c → RV.Lane op q a c end × instantOf c ≡ instantOf y
  done-ends x l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) x l
  ... | s , oks , r , sk , back with lane-take m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r tt
  ...   | w , refl , e = w ⊕ [ last ] , back e (≺-trans {s} {w ⊕ [ ix 0 ]} {w ⊕ [ last ]} sk (ix<last w)) , trans (inst-⊕ w [ last ]) (sym (inst-⊕ w [ ix 0 ]))

  private
    I-RO : InvAt (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ]) RO
    I-RO = inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)

    ro-func : ∀ {q a a′} → RO q (out a) → RO q (out a′) → a ≡ a′
    ro-func x x′ with InvAt.func I-RO x x′
    ... | refl = refl

    -- The run holds no end before its last row.
    no-end : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs {x ys} → r₁ ≡ xs ++ x ∷ ys → ∀ {c} → (c , end) ∈ xs → ⊥
    no-end r₁ {z} {e} {r₂} mt xs {x} {ys} refl i with ∈-∃++ i
    ... | a₁ , b₁ , refl = nonempty b₁ (end-last I-M a₁ (subst (Met M) (shape a₁ b₁) mt))
      where
        shape : ∀ a₁ b₁ → ((a₁ ++ (_ , end) ∷ b₁) ++ x ∷ ys) ++ (z , e) ∷ r₂ ≡ a₁ ++ (_ , end) ∷ ((b₁ ++ x ∷ ys) ++ (z , e) ∷ r₂)
        shape a₁ b₁ = trans (cong (_++ (z , e) ∷ r₂) (++-assoc a₁ _ (x ∷ ys))) (++-assoc a₁ _ _)
        nonempty : ∀ b₁ {w} → (b₁ ++ x ∷ ys) ++ w ≡ [] → ⊥
        nonempty []      ()
        nonempty (_ ∷ _) ()

    -- A row the run met lies before its last.
    met-before : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {k e′} → (k , e′) ∈ r₁ → k ≺ z
    met-before r₁ {z} {e} {r₂} mt i with ∈-∃++ i
    ... | a₁ , b₁ , refl with run-tail a₁ (subst (Met M) (++-assoc a₁ _ ((z , e) ∷ r₂)) mt)
    ...   | _ ∷ᴿ rn = run-after rn (∈-++⁺ʳ b₁ (here refl))

  -- A ROW OF THE REAL FLATMAP'S VALUES IS A LANE'S, run and not cut there.
  σ₃-lane : ∀ {y b} → σ₃ y (out b) → Σ Pos λ q → Σ A λ a → RO q (out a) × RV.Runs op q × RV.Lane op q a y (out b) × ¬ RV.CutAt op q y
  σ₃-lane (r , _) = join-out op fL RO (proj₁ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) r))

  -- A LANE MARK THE SCAN MEETS IS A LANE'S ROW, one `sub J` below it.
  lane-mark : ∀ {rx} → Met M rx → ∀ {k b mk n} → (k , out (just (inj₁ (b , instEmit (mark mk) n)))) ∈ rx → mk ≡ laneStart ⊎ mk ≡ laneDone
            → Σ Pos λ y → k ≡ y ⊕ [ sub LS.J ] × b ≡ laneB × σ₃ y (out (instEmit (mark mk) n))
  lane-mark mt {b = laneB} i _ with lane-run mt
  ... | rs , pr , run , _ with bproj-mem pr i
  ...   | y , refl , j = y , refl , refl , proj₁ (run-row∈ run j)
  lane-mark mt {b = outerB} i mk with outer-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , x , ox , o≡ , _ with open-mark o≡ (λ { refl → [ (λ ()) , (λ ()) ]′ mk })
  ...   | refl = ⊥-elim (lane-routing mk (Held.routing H₁ (proj₁ ox)))
  lane-mark mt {b = closeB} i mk with close-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , cx , _ = ⊥-elim (closing-mark (close-marks cx) (λ { refl → [ (λ ()) , (λ ()) ]′ mk }) (λ { refl → [ (λ ()) , (λ ()) ]′ mk }))

  -- A LANE'S `laneDone`s ARE ONE ROW.
  done-one : ∀ {q a y y′ n n′} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark laneDone) n)) → RV.Lane op q a y′ (out (instEmit (mark laneDone) n′)) → y ≡ y′
  done-one x l l′ with lane-at₂ op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) x l l′
  ... | s , oks , r , r′ = lane-once m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r tt r′ tt

  private
    split-met : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → Met M (xs ++ x ∷ (ys ++ (z , e) ∷ r₂))
    split-met r₁ {z} {e} {r₂} mt xs x ys refl = subst (Met M) (++-assoc xs (x ∷ ys) ((z , e) ∷ r₂)) mt

    in-r₁ : ∀ (r₁ : List Row) xs x ys → r₁ ≡ xs ++ x ∷ ys → x ∈ r₁
    in-r₁ r₁ xs x ys refl = ∈-++⁺ʳ xs (here refl)

  -- NO `laneDone` OF A LANE PRECEDES ITS OWN IN THE SCAN.
  done-once : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → LaneMark laneDone q x → ¬ AC.DoneIn [] xs q
  done-once r₁ mt xs x ys eq (a , y , n , xo , refl , l) di with find di
  ... | _ , i , (a′ , y′ , n′ , xo′ , refl , l′) with ro-func xo xo′
  ...   | refl with done-one xo l l′
  ...     | refl = ≺-irrefl {y ⊕ [ sub LS.J ]} (met-before xs (split-met r₁ mt xs _ ys eq) i)

  private
    start-before : ∀ {y y₀ n n₀} → σ₃ y₀ (out (instEmit (mark laneStart) n₀)) → σ₃ y (out (instEmit (mark laneDone) n)) → y₀ ≼ y → y₀ ≺ y
    start-before {y} {y₀} σs σd le with ≼-split {y₀} {y} le
    ... | inj₁ lt = lt
    ... | inj₂ refl with InvAt.func I₃ (proj₁ σs) (proj₁ σd)
    ...   | ()

    -- A lane row before one the scan meets is met before it.
    pick : ∀ {y y₀ n n₀} → σ₃ y₀ (out (instEmit (mark laneStart) n₀)) → y₀ ≺ y → ∀ ws → Met M ws
         → (y ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark laneDone) n)))) ∈ ws
         → (y₀ ⊕ [ sub LS.J ] , out (just (inj₁ (laneB , instEmit (mark laneStart) n₀)))) ∈ ws
    pick {y} σs lt ws mw i with lane-run mw
    ... | rs , pr , run , _ with bproj-mem pr i
    ...   | yd , ed , j with ⊕-injˡ y yd ed
    ...     | refl with ∈-∃++ j
    ...       | r , r′ , refl with run-catch r run σs tt tt lt
    ...         | r₁′ , r₂′ , e″ , refl with InvAt.func I₃ (proj₁ (proj₁ (run-row∈ run (∈-++⁺ˡ (∈-++⁺ʳ r₁′ (here refl)))))) (proj₁ σs)
    ...           | refl = bproj-back pr (∈-++⁺ˡ (∈-++⁺ʳ r₁′ (here refl)))

    st-dn : ∀ {k k′ n n′} → _≡_ {A = Row} (k , out (just (inj₁ (laneB , instEmit (mark laneStart) n)))) (k′ , out (just (inj₁ (laneB , instEmit (mark laneDone) n′)))) → ⊥
    st-dn e with cong proj₂ e
    ... | ()

  -- EACH `laneDone` THE SCAN MEETS FOLLOWS ITS LANE'S START THERE.
  done-started : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → LaneMark laneDone q x → AC.StartIn [] xs q
  done-started r₁ mt xs x ys eq {q} (a , y , n , xo , refl , l) with lane-mark (run-prefix r₁ mt) (in-r₁ r₁ xs _ ys eq) (inj₂ refl)
  ... | y′ , e′ , _ , σd with ⊕-injˡ y y′ e′
  ...   | refl with lane-begins xo l σd
  ...     | y₀ , n₀ , l₀ , σs , le with ∈-++⁻ xs (pick σs (start-before σs σd le) (xs ++ [ _ ])
              (run-prefix (xs ++ [ _ ]) (subst (Met M) (sym (++-assoc xs [ _ ] (ys ++ _))) (split-met r₁ mt xs _ ys eq))) (∈-++⁺ʳ xs (here refl)))
  ...       | inj₁ i = any-map (λ { refl → a , y₀ , n₀ , xo , refl , l₀ }) i
  ...       | inj₂ (here e″) = ⊥-elim (st-dn e″)

  -- A `laneDone` THE SCAN MEETS IS A RUN LANE'S.
  done-mark : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markAct op x ≡ kDone
            → Σ Pos λ q → LaneMark laneDone q x × Own q
  done-mark r₁ mt xs x ys eq kx with row-done op x kx
  ... | k , b , n , refl with lane-mark (run-prefix r₁ mt) {k = k} {b = b} {mk = laneDone} {n = n} (in-r₁ r₁ xs _ ys eq) (inj₂ refl)
  ...   | y , refl , refl , σd with σ₃-lane σd
  ...     | q , a , xo , rn , l , _ = q , (a , y , n , xo , refl , l) , (a , xo , rn)

  -- NO SCAN CUT FALLS BETWEEN A LANE'S START AND ITS `laneDone`.
  done-uncut : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → LaneMark laneDone q x → ¬ AC.CutIn [] xs q
  done-uncut r₁ mt xs x ys eq {q} (a , y , n , xo , refl , l) ci with ci
  ... | _ , _ , _ , _ , cb with find cb
  ...   | xc , _ , kc with row-cut op xc kc
  ...     | op≡ with switch-cut op≡ xs (split-met r₁ mt xs _ ys eq) ci
  ...       | q′ , a′ , xo′ , qq′ , later with lane-mark (run-prefix r₁ mt) (in-r₁ r₁ xs _ ys eq) (inj₂ refl)
  ...         | y′ , e′ , _ , σd with ⊕-injˡ y y′ e′
  ...           | refl with σ₃-lane σd
  ...             | q₀ , a₀ , xo₀ , _ , l₀ , nc₀ with lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
                      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
                      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo₀ xo l₀ l
  ...               | refl = subst (λ o′ → ¬ RV.CutAt o′ q y) op≡ nc₀ (q′ , a′ , xo′ , qq′ , later σd refl)

  -- EACH `laneDone` THE SCAN MEETS ENDS A LANE IT MET START, AND NEVER MET
  -- END OR CUT.
  done-live : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markAct op x ≡ kDone
            → ¬ ¬ Σ Pos λ q → LaneMark laneDone q x × AC.Live [] xs q
  done-live r₁ mt xs x ys eq kx κ with done-mark r₁ mt xs x ys eq kx
  ... | q , dm , own = κ (q , dm , own , done-started r₁ mt xs x ys eq dm , done-once r₁ mt xs x ys eq dm , done-uncut r₁ mt xs x ys eq dm)

  -- NO LANE NEVER CUT MEETS A CUT IN THE SCAN.
  cut-never : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q a} → RO q (out a) → ¬ RV.Cut op q → ¬ AC.CutIn [] r₁ q
  cut-never r₁ mt {q} xo nc ci with ci
  ... | _ , _ , _ , _ , cb with find cb
  ...   | xc , _ , kc with row-cut op xc kc
  ...     | op≡ with switch-cut op≡ r₁ mt ci
  ...       | q′ , a′ , xo′ , qq′ , _ = subst (λ o′ → ¬ RV.Cut o′ q) op≡ nc (q′ , a′ , xo′ , qq′)

  -- WITH NO LANE RUNNING OR QUEUED AT THE CLOSER'S `outerDone`, EVERY LANE
  -- THE REAL FLATMAP RUNS AND NEVER CUTS HAS ENDED BY ITS INSTANT, where it
  -- has few rows before a later one: the lane started before the mark,
  -- and the scan's count of lanes started and not ended is empty there.
  --
  -- REFUTED: 9e244736 `lanes-by` unrestricted, by a switch whose cut lane loops: the scan meets the next value's lane start the real flatMap never reaches, and drops the cut lane from its count
  lanes-by : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
           → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
           → ∀ {v} → Few R v → instantOf z ≺ⁱ instantOf v
           → RV.LanesBy op (instantOf z)
  lanes-by r₁ {z} {n} {r₂} mt a0 q0 Fv zv {q} {a} x rn nc ¬g =
    lane-started r₁ mt q0 Fv zv x rn nc λ si →
      AC.drained r₁ (λ xs y ys eq → past-active op init xs y (no-end r₁ mt xs eq))
        (λ { (_ , _ , _ , _ , refl , _) → refl }) (λ { (_ , _ , _ , _ , refl , _) → refl })
        (λ _ _ _ _ _ _ → start-one) (done-live r₁ mt) a0 (a , x , rn) si (cut-never r₁ mt x nc) done-by
    where
      done-by : AC.DoneIn r₁ r₁ q → ⊥
      done-by di with find di
      ... | _ , i , (a′ , y , n′ , x′ , refl , l) with ro-func x x′ | done-ends x′ l
      ...   | refl | c , lc , ic = ¬g (c , lc , λ zc → ≺-absurd {y ⊕ [ sub LS.J ]} {z} (met-before r₁ mt i)
              (instant-≺ z (y ⊕ [ sub LS.J ]) (subst (instantOf z ≺ⁱ_) (trans ic (sym (inst-⊕ y [ sub LS.J ]))) zc)))

  -- The real flatMap's outer has ended by the closer's `outerDone`.
  outer-by : ∀ {z n} → M z (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → RV.OuterBy (instantOf z)
  outer-by mz with close-sent mz
  ... | _ , w′ , σd , refl with CD.done-under (proj₁ σd)
  ...   | y₁ , e₁ , (ws , refl) with ro-end e₁
  ...     | c′ , rc , ic = c′ , rc , λ h → irrⁱ (subst (instantOf ((y₁ ⊕ ws) ⊕ [ sub w′ ]) ≺ⁱ_) (trans ic i₁) h)
    where
      i₁ : instantOf y₁ ≡ instantOf ((y₁ ⊕ ws) ⊕ [ sub w′ ])
      i₁ = trans (sym (inst-⊕ y₁ ws)) (sym (inst-⊕ (y₁ ⊕ ws) [ sub w′ ]))

  -- WITH NO LANE RUNNING OR QUEUED AT THE CLOSER'S `outerDone`, THE
  -- LANES HAVE ENDED BY ITS INSTANT: its outer has, and every lane run and
  -- never cut.  Asked only where the real flatMap has few rows before a
  -- later instant's row.
  --
  -- REFUTED: 9e244736 `lanes-ended` unrestricted, by a switch whose cut lane loops: the lane never ends, the switch's count drops it at the cut, and the scan meets the closer's `outerDone` with no lane running or queued
  lanes-ended : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
              → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
              → ∀ {q} → Few R q → instantOf z ≺ⁱ instantOf q
              → ¬ ¬ Σ Pos λ y → σ₃ y end × ¬ (instantOf z ≺ⁱ instantOf y)
  lanes-ended r₁ mt a0 q0 Fq zq ¬g =
    real-ends op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)
      (shows-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))
      (λ a s′ oks → shows-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s′ oks)
      ro-before (proj₁ Fq , λ x lt → proj₂ Fq (R-from x) lt) zq
      (outer-by (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))) (lanes-by r₁ mt a0 q0 Fq zq)
      λ (y , ry , iy) → ¬g (y , (R-from ry , λ {c′} rc → subst (y ≼_) (end-uniq I₃ (R-from ry) rc) (≼-refl {y})) , iy)


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

  -- WITH NO LANE RUNNING OR QUEUED AT THE CLOSER'S `outerDone`, NO
  -- VISIBLE ROW OF THE SOURCE PAST IT LIES IN A LATER INSTANT: the outer
  -- has ended under the mark, the closer ends in its instant, and the
  -- lanes by it.
  idle-ends : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
            → Flat.active (proj₁ (past op init r₁)) ≡ 0 → Flat.queue (proj₁ (past op init r₁)) ≡ 0
            → ∀ {q a} → M q (out a) → Few R q → z ≺ q → instantOf z ≡ instantOf q
  idle-ends r₁ {z} mt a0 q0 {q} mq Fq zq with close-sent (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))
  ... | y₂′ , w′ , σd , refl with CD.done-under (proj₁ σd) | closer-ends σd
  ...   | y₁ , e₁ , (ws , refl) | y₂ , e₂ , i₂ =
    decidable-stable (instantOf Z ≟ⁱ instantOf q) λ ne →
      lanes-ended r₁ mt a0 q0 Fq (lt ne) λ (y₃ , e₃ , i₃) →
        src-ends e₁ e₂ e₃ (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl)))) mq (lt ne)
          (λ h → irrⁱ (subst (instantOf Z ≺ⁱ_) i₁ h)) (λ h → irrⁱ (subst (instantOf Z ≺ⁱ_) i₂′ h)) i₃
    where
      Z : Pos
      Z = (y₁ ⊕ ws) ⊕ [ sub w′ ]

      iz : instantOf Z ≡ instantOf (y₁ ⊕ ws)
      iz = inst-⊕ (y₁ ⊕ ws) [ sub w′ ]

      i₁ : instantOf y₁ ≡ instantOf Z
      i₁ = trans (sym (inst-⊕ y₁ ws)) (sym iz)

      i₂′ : instantOf y₂ ≡ instantOf Z
      i₂′ = trans i₂ (sym iz)

      lt : ¬ instantOf Z ≡ instantOf q → instantOf Z ≺ⁱ instantOf q
      lt = ≺-instant Z q zq

  -- EVERY OUTER ROW THE SOURCE MEETS LIES BEFORE THE CLOSER'S `outerDone`.
  outer-before-done : ∀ {k v z n} → M k (out (just (inj₁ (outerB , v)))) → M z (out (just (inj₁ (closeB , instEmit (mark outerDone) n))))
                    → k ≺ z
  outer-before-done mk mz with outer-sent mk | close-sent mz
  ... | y₁ , w , _ , σy , _ , refl | y₂ , w′ , σy′ , refl = CD.before-done σy (proj₁ σy′) w w′

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
      ... | a0 , q0 = idle-ends r₁ mt′ a0 q0 (proj₁ (run-row∈ mt (∈-++⁺ʳ (r₁ ++ (z , out xz) ∷ r₂) (here refl)))) Fq zq
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

  postulate
    -- A CONNECT IN SCOPE KEEPS NO ROUTE PAST ITS INSTANT, read at the
    -- scan's rows.  Owed: the run split onto that connect's tracker, and
    -- the binder's own `idle` (`Bound.held`) read through `annotate`.
    live-current : ∀ rx₁ {q e rx₂} → Met M (rx₁ ++ (q , e) ∷ rx₂) → Visible e
                 → anyHolds (Flat.at (proj₁ (past op init rx₁))) (Flat.live (proj₁ (past op init rx₁))) ≡ true
                 → Flat.at (proj₁ (past op init rx₁)) ≡ nameOf q

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
    (outer-current rx₁ mt Fq) (lanes-current rx₁ mt) (held-current rx₁ mt tt) (parked-current rx₁ mt tt)
    where st = proj₁ (past op init rx₁)

  start-current : ∀ rx₁ {q a rx₂} → Met M (rx₁ ++ (q , out a) ∷ rx₂) → Few R q
                → proj₂ (from r₀ (outRows op init rx₁)) ≡ 0 ⊎ proj₁ (from r₀ (outRows op init rx₁)) ≡ nameOf q
  start-current rx₁ mt Fq with flat-current rx₁ mt Fq
  ... | inj₁ z = inj₁ (trans (exact-past op rx₁ (nocb rx₁ mt)) z)
  ... | inj₂ a = inj₂ (trans (inv-at (inv-past op rx₁)) a)

  named : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark begin) n)))) → n ≡ nameOf q
  named x with m-rows x tt
  ... | outer {q = c} {w = w} y eq with refl ← open-mark eq (λ ()) =
    trans (Held.named H₁ (proj₁ y)) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | lane {q = c} {w = w} y  = trans (lane-named y) (cong nm (sym (rootOf-ext c [ sub w ])))
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

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

  late : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark over) n)))) → Valued (rootOf q) × opos (rootOf q) ⊑ q
  late x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = late-ext [ sub w ] (Held.late H₁ (proj₁ y))
  ... | lane {w = w} y = late-ext [ sub w ] (lane-late y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

  mdone : ∀ {q b n} → M q (out (just (inj₁ (b , instEmit (mark completed) n)))) → Early q
  mdone x with m-rows x tt
  ... | outer {w = w} y eq with refl ← open-mark eq (λ ()) = early-inst [ sub w ] (Held.done H₁ (proj₁ y))
  ... | lane {w = w} y = early-inst [ sub w ] (Fit.fine lane-fit y)
  ... | close y = ⊥-elim (closing-mark (close-marks y) (λ ()) (λ ()))

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
