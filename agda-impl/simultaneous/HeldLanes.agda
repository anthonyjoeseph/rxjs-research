{-# OPTIONS --guardedness #-}

-- THE REAL FLATMAP'S LANES AGAINST THE SCAN'S SOURCE: the lane a row of
-- the real flatMap's values runs in, and where a lane lies against the
-- outer rows that open it.
module simultaneous.HeldLanes where


open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Properties using (++-assoc)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup; _∷_) renaming ([] to []ᵉ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; FlatOp; map)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; DenEnv; module Op; Ev; out; end; Few; _≼_; EmissionSet; _≺_)
open import simultaneous.SObs using (lone; module Elaborate; Flat; outerB; laneB; closeB)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Routing; Held; Early; Idle)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; Shows; PinBy; ok-step; _⊑_; InvAt; ⊕-injˡ; ok-in; ⊑-cmp; ⊑-refl; ⊑-inside; ⊕-assoc) renaming (W to Wld)
open import denotation.Laws.HotBelow using (under-hot)
open import simultaneous.EachRow using (each-row; each-at; each-end; each-before)
open import denotation.EmissionSet using (LaneOf)
open import simultaneous.LaneLocal using (inv-ev; Fit)
open import simultaneous.CombSent using (src-op; own-op; cat-op; tag-op; no-track; no-close; tag-branch; Cat-of; Tag; sent-branch; Closing; closing-mark; closing-value; closer-marks; closer-good; src-where; Where) renaming (under to w-under; past to w-past)
open import denotation.EmissionSet using (map-end) renaming (ended to r-ended; late to r-late; shown to r-shown)
open import denotation.Laws.Connect using () renaming (lawful to src-lawful; ok₀ to body-ok)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import simultaneous.InstEmit using (begin; completed; instEmit; value; mark; over; outerDone; Mark; laneStart; laneDone; stop; outerOpen; outerClose; burstEnd; subscribed)
open import Data.Product using (_×_; _,_; proj₁; Σ; proj₂)
open import Data.Unit using (tt)
open import simultaneous.TakeCut using (inst-⊕)
import denotation.Laws.ShowsJoin as SJ
open import denotation.Laws.Count using (reach-down)
import simultaneous.LaneLayers as LaneLayers
import simultaneous.LaneStart as LaneStart
open import denotation.Laws.Modulus using (entered-few; T-not; ≺-irrefl; ≼-split; ≺→≼; ≺-≼-≺; ≺-ext; ≺-trans; ≼-≺-≺; ≼-or-≻; ≺-absurd)
open import denotation.Events using (<ᵖ-part; <ᵖ-between)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence; _|>′_)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; shows-ev; Fresh)
open import simultaneous.Routed using (Placed)
open import simultaneous.FlatLanes using (end-last; past-within; co; bproj-end; Within; within; brTag; BProj; Tg; tagged) renaming (keep to bkeep; drop to bdrop)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ʳ; ∈-++⁺ˡ)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; elab; srcLane; laneSrc; annotate; marked; trackers; closer; combined; laneˢ; undone; each; coldˢ;
  Input; react; going; fed; opening; anyHolds; branch; restamp; wrapped; Out; cut; left)
open import simultaneous.HeldComb using (ev; init; from; past)
open import simultaneous.HeldComb using (ev)
open import Relation.Nullary using (¬_)
import Relation.Nullary as Nl
open import Data.Sum using (_⊎_; [_,_]′; inj₁; inj₂)
open import simultaneous.Layers using (run-tail; run-after) renaming (run-row to run-row∈)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Instants using (_≺ⁱ_; triⁱ; transⁱ; instant-≺)
open import denotation.Read using (Visible; After; cursor; Run; loud) renaming (_∷_ to _∷ᴿ_)
open import Data.Bool using (Bool; T; not; true)
import denotation.Read as Run
import Data.Nat as ℕ
import Data.Nat.Properties as ℕP
import denotation.EmissionSet as ES
open import simultaneous.RealView using (module View; real-from; real-to; lane-at; lane-at₂; lane-one; join-out; join-in; cutat-up; join-shows)
open import simultaneous.HeldTake using (module TakeBack)
open import simultaneous.TakeKit using (ix<last)
open import denotation.EmissionSet using (Den; Truncate)
open import simultaneous.InstEmit using (valuesOf)

open import Tree using (Obs; FlatOp; map; connected; takeWhile; switchᶠ)


open import simultaneous.LaneCount using (module Count; kCut)
open import simultaneous.ScanCount using (rowKind; markAct)
open import Data.List.Membership.Propositional.Properties using (∈-∃++)
open import simultaneous.HeldSrc using (module CombSrc; open-mark)
open import simultaneous.LaneCount using (kStart; kDone)
open import simultaneous.ScanCount using (markQue; past-queue; row-start; que-cut)
open import simultaneous.CombSent using (starts-after)
open import simultaneous.Project using (run-prefix)
open import simultaneous.ScanPast using (run-catch)
open import Data.List.Relation.Unary.Any using (Any)
open import Data.List.Relation.Unary.Any.Properties using () renaming (++⁺ʳ to any-++ʳ)
open import Data.List.Membership.Propositional using (find)
open import Tree using (mergeᶠ; exhaustᶠ)
open import simultaneous.LaneOnce using (module LaneOnce)
open import simultaneous.LaneIdle using (module LaneIdle)
open import denotation.Laws using (good-cons)
open import simultaneous.HeldConnect using (early-inst)

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
lane-routing : ∀ {mk} → mk ≡ laneStart ⊎ Σ ℕ (λ kd → mk ≡ laneDone kd) → Routing mk → ⊥
lane-routing (inj₁ refl) ()
lane-routing (inj₂ (_ , refl)) ()

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

-- A BRANCH'S ROW A PROJECTION MEETS, read through its map, is a row it
-- keeps one `sub J` below.
bproj-memʰ : ∀ {A′ B′ b} {h : IE A′ → IE B′} {J} {rx : List (Pos × Ev (Maybe (Input B′)))} {rs : List (Pos × Ev (IE A′))} {k y}
           → BProj b h J rx rs → (k , out (Tg b y)) ∈ rx → Σ Pos λ c → Σ (IE A′) λ x → k ≡ c ⊕ [ sub J ] × (c , out x) ∈ rs × h x ≡ y
bproj-memʰ (bkeep pr)              (here refl) = _ , _ , refl , here refl , refl
bproj-memʰ (bkeep pr)              (there i)   = let (c , x , e , j , hx) = bproj-memʰ pr i in c , x , e , there j , hx
bproj-memʰ {b = b} (bdrop nb pr)   (here refl) = ⊥-elim (tagged b nb)
bproj-memʰ (bdrop nb pr)           (there i)   = bproj-memʰ pr i

-- A switch cuts at an `outerOpen` alone.
open-cut : ∀ mk → markAct switchᶠ mk ≡ kCut → mk ≡ outerOpen
open-cut outerOpen  _  = refl
open-cut begin      ()
open-cut over       ()
open-cut stop       ()
open-cut outerClose ()
open-cut laneStart  ()
open-cut (laneDone _) ()
open-cut burstEnd   ()
open-cut outerDone  ()
open-cut subscribed ()
open-cut completed  ()

-- No `outerOpen` is read above a flatMap.
open-routing : Routing outerOpen → ⊥
open-routing ()

-- A LANE'S ROWS LIE PAST ITS VALUE.
lane-past : ∀ {X Y : Set} op (f : X → Den Y) (o : EmissionSet X) {q a y e} → View.Lane f o op q a y e → q ≺ y
lane-past (mergeᶠ nothing)  f o {q} {y = y} (_ , sy)                  = ≺-trans {q} {q ⊕ [ ix 1 ]} {y} (≺-ext q []) sy
lane-past (mergeᶠ (just n)) f o {q} {y = y} (_ , s′ , (_ , st) , _ , sy) = ≺-trans {q} {s′} {y} (starts-after st) sy
lane-past switchᶠ           f o {q} {y = y} (_ , sy)                  = ≺-trans {q} {q ⊕ [ ix 1 ]} {y} (≺-ext q []) sy
lane-past exhaustᶠ          f o {q} {y = y} (_ , sy)                  = ≺-trans {q} {q ⊕ [ ix 1 ]} {y} (≺-ext q []) sy

-- Whether a flatMap is a bounded merge.
bounded? : ∀ o → (Σ ℕ λ k → o ≡ mergeᶠ (just k)) ⊎ (∀ k → o ≡ mergeᶠ (just k) → ⊥)
bounded? (mergeᶠ (just k)) = inj₁ (k , refl)
bounded? (mergeᶠ nothing)  = inj₂ λ _ ()
bounded? switchᶠ           = inj₂ λ _ ()
bounded? exhaustᶠ          = inj₂ λ _ ()

-- A LANE NEVER CUT IS CUT AT NO ROW.
never-cut : ∀ {A B} op (f : A → Den B) (o : EmissionSet A) {q k} → ¬ View.Cut f o op q → ¬ View.CutAt f o op q k
never-cut switchᶠ    f o nc (q′ , a′ , x , lt , _) = nc (q′ , a′ , x , lt)
never-cut (mergeᶠ _) f o nc ()
never-cut exhaustᶠ   f o nc ()

lane-of : ∀ {A B} (f : A → Den B) (o : EmissionSet A) op → (∀ k → op ≡ mergeᶠ (just k) → ⊥) → ∀ {q a y e} → LaneOf f q a y e → View.Lane f o op q a y e
lane-of f o (mergeᶠ nothing)  nb l = l
lane-of f o (mergeᶠ (just k)) nb l = ⊥-elim (nb k refl)
lane-of f o switchᶠ           nb l = l
lane-of f o exhaustᶠ          nb l = l

module CombLanes (m : Maybe ℕ) {Γ Δ A B} (ρ : ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ) (op : FlatOp) (f : A → Obs Timeline Γ B)
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

  -- THE REAL FLATMAP, READ THROUGH ITS POLICY: its outer is the hot
  -- outer's values, each lane a value's elaborated lane.
  fL : A → Den (IE B)
  fL a = ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀)

  RO : EmissionSet A
  RO = enter (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) (p₀₀ ⊕ [ ix 1 ])

  module RV = View fL RO

  R-from : ∀ {k e} → Truncate (RV.Join op) k e → R k e
  R-from = real-from m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ])

  private
    q₀≺σ₁ : ∀ {o₁ e} → σ₁ o₁ e → (p₀₀ ⊕ [ ix 1 ]) ≺ o₁
    q₀≺σ₁ {o₁} σo = ≺-trans {p₀₀ ⊕ [ ix 1 ]} {p₀ ⊕ [ ix 1 ]} {o₁} q₀≺s₂ (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {o₁} s₂≺c₁ (σ₁-after σo))

    few-out : ∀ {o₁ x} → σ₁ o₁ (out x) → Few σ₁ o₁
    few-out {o₁} {x} σo = let (ks , h) = entered-few (ev m trig env₀) (c ⊕ [ ix 1 ]) {o₁} {out x} (λ {_} {_} → tt) (proj₁ σo) in ks , λ r lt → h (proj₁ r) lt

    few-end : ∀ {o₁} → σ₁ o₁ end → Few σ₁ o₁
    few-end {o₁} σo = let (ks , h) = entered-few (ev m trig env₀) (c ⊕ [ ix 1 ]) {o₁} {end} (λ {_} {_} → tt) (proj₁ σo) in ks , λ r lt → h (proj₁ r) lt

    val-end : ∀ {r x k} → σ₁ r (out x) → σ₁ k end → r ≺ k
    val-end {r} {x} {k} σr σk = [ (λ lt → lt) , (λ eq → ⊥-elim (out≢end (InvAt.func I₁ (proj₁ σr) (subst (λ z → enter (ev m trig env₀) (c ⊕ [ ix 1 ]) z end) (sym eq) (proj₁ σk))))) ]′
                                  (≼-split {r} {k} (proj₂ σr (proj₁ σk)))
      where
        out≢end : out x ≡ end → ⊥
        out≢end ()

  -- THE REAL FLATMAP'S OUTER ENDS AFTER ITS VALUES,
  ro-before : ∀ {q a c} → RO q (out a) → RO c end → q ≺ c
  ro-before = each-before m σ₂ σ₁ env₀ L₁ val-end (p₀₀ ⊕ [ ix 1 ])

  -- IN THE HOT OUTER'S END'S INSTANT.
  ro-end : ∀ {y} → σ₁ y end → Σ Pos λ c → RO c end × instantOf c ≡ instantOf y
  ro-end {y} σy = y ⊕ [ sub (p₀₀ ⊕ [ ix 1 ]) ] , each-end m σ₂ σ₁ env₀ L₁ (p₀₀ ⊕ [ ix 1 ]) σy (q₀≺σ₁ σy) (few-end σy) , inst-⊕ y _

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

  -- A lane's `laneDone`, telling whatever it counted.
  DoneMark : Pos → Row → Set
  DoneMark q x = Σ ℕ λ kd → LaneMark (laneDone kd) q x

  module AC = Count _≟ᵖ_ (rowKind markAct op) Own (LaneMark laneStart) DoneMark act

  -- A LANE'S `laneDone` FOLLOWS ITS OWN `laneStart`, both past its
  -- subscription.
  lane-starts : ∀ {a s y kd n} → enter (fL a) s y (out (instEmit (mark (laneDone kd)) n))
              → Σ Pos λ y₀ → Σ _ λ n₀ → enter (fL a) s y₀ (out (instEmit (mark laneStart) n₀)) × s ≺ y₀ × y₀ ≺ y
  lane-starts {a} {s} r =
    let (y₀ , r₀ , lt₀ , lt) = LaneStart.lane-starts _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s r in y₀ , _ , r₀ , lt₀ , lt

  -- EACH `laneStart` IS ONE LANE'S: no two values' lanes start at one row.
  start-one : ∀ {x q q′} → LaneMark laneStart q x → LaneMark laneStart q′ x → q ≡ q′
  start-one (_ , y , _ , xo , refl , l) (_ , y′ , _ , xo′ , e , l′) with ⊕-injˡ y y′ (cong proj₁ e)
  ... | refl = lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo xo′ l l′

  -- A LANE ENDS IN ITS `laneDone`'s INSTANT.
  done-ends : ∀ {q a y kd n} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n))
            → Σ Pos λ c → RV.Lane op q a c end × instantOf c ≡ instantOf y
  done-ends x l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) x l
  ... | s , oks , r , sk , back with lane-take m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r tt
  ...   | w , refl , e = w ⊕ [ last ] , back e (≺-trans {s} {w ⊕ [ ix 0 ]} {w ⊕ [ last ]} sk (ix<last w)) , trans (inst-⊕ w [ last ]) (sym (inst-⊕ w [ ix 0 ]))

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

  -- A LANE'S `laneDone` IN THE REAL FLATMAP FOLLOWS ITS `laneStart` THERE.
  lane-begins : ∀ {q a y kd n} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n)) → σ₃ y (out (instEmit (mark (laneDone kd)) n))
              → Σ Pos λ y₀ → Σ _ λ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) × σ₃ y₀ (out (instEmit (mark laneStart) n₀)) × y₀ ≼ y
  lane-begins {q} {a} {y} {kd} {n} xo l σd =
    let (_ , _ , r , _ , back) = lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
            (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
            (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l
        (y₀ , n₀ , r₀ , sy₀ , lt) = lane-starts r
        (_ , _ , xo′ , rn , l′ , nc) = σ₃-lane σd
    in begin-at (back r₀ sy₀) lt rn nc (lane-one op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
            (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
            (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo xo′ l l′)
    where
      begin-at : ∀ {y₀ n₀ q′} → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) → y₀ ≺ y → RV.Runs op q′ → ¬ RV.CutAt op q′ y → q ≡ q′
               → Σ Pos λ y₀ → Σ _ λ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) × σ₃ y₀ (out (instEmit (mark laneStart) n₀)) × y₀ ≼ y
      begin-at {y₀} {n₀} L₀ lt rn nc refl = y₀ , n₀ , L₀
                     , (R-from (join-in op fL RO xo rn L₀ (λ c → nc (cutat-up op fL RO {q} {y₀} {y} lt c))
                                , reach-down {q = y} {w = y₀} {e = out (instEmit (mark (laneDone kd)) n)} {e₁ = out (instEmit (mark laneStart) n₀)} (proj₂ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σd))) lt tt)
                       , λ {c} ce → ≺→≼ {y₀} {c} (≺-≼-≺ {y₀} {y} {c} lt (proj₂ σd ce)))
                     , ≺→≼ {y₀} {y} lt

  -- A LANE MARK THE SCAN MEETS IS A LANE'S ROW, one `sub J` below it.
  lane-mark : ∀ {rx} → Met M rx → ∀ {k b mk n} → (k , out (just (inj₁ (b , instEmit (mark mk) n)))) ∈ rx → mk ≡ laneStart ⊎ Σ ℕ (λ kd → mk ≡ laneDone kd)
            → Σ Pos λ y → k ≡ y ⊕ [ sub LS.J ] × b ≡ laneB × σ₃ y (out (instEmit (mark mk) n))
  lane-mark mt {b = laneB} i _ with lane-run mt
  ... | rs , pr , run , _ with bproj-mem pr i
  ...   | y , refl , j = y , refl , refl , proj₁ (run-row∈ run j)
  lane-mark mt {b = outerB} i mk with outer-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , x , ox , o≡ , _ with open-mark o≡ (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk })
  ...   | refl = ⊥-elim (lane-routing mk (Held.routing H₁ (proj₁ ox)))
  lane-mark mt {b = closeB} i mk with close-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , cx , _ = ⊥-elim (closing-mark (close-marks cx) (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk }) (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk }))

  -- A LANE'S `laneDone`s ARE ONE ROW.
  done-one : ∀ {q a y y′ kd kd′ n n′} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark (laneDone kd)) n)) → RV.Lane op q a y′ (out (instEmit (mark (laneDone kd′)) n′)) → y ≡ y′
  done-one x l l′ with lane-at₂ op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) x l l′
  ... | s , oks , r , r′ = lane-once m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r tt r′ tt

  -- WHERE THE REAL FLATMAP'S OUTER HOLDS THE OUTER'S ROW `c`: a value step
  -- below its hot's reading of it.
  ro-at : Pos → Pos
  ro-at c = c ⊕ (sub (p₀₀ ⊕ [ ix 1 ]) ∷ ix 1 ∷ ix 0 ∷ [])

  -- A VALUE OF THE REAL FLATMAP'S OUTER IS AN OUTER VALUE'S, at `ro-at`.
  ro-row : ∀ {q a} → RO q (out a) → Σ Pos λ r → Σ _ λ n → σ₁ r (out (instEmit (value a) n)) × q ≡ ro-at r
  ro-row = each-row m σ₂ σ₁ env₀ (p₀₀ ⊕ [ ix 1 ])

  private
    Qo : Pos
    Qo = (p₀₀ ⊕ [ ix 1 ]) ⊕ [ last ]

    Qo≺s₂ : Qo ≺ (p₀ ⊕ [ ix 1 ])
    Qo≺s₂ = subst (_≺ (p₀ ⊕ [ ix 1 ])) (sym (trans (⊕-assoc p₀₀ [ ix 1 ] [ last ]) (⊕-assoc p₀ [ ix 0 ] (ix 1 ∷ last ∷ []))))
              (Equivalence.from T-≡ (<ᵖ-part p₀ {ix 0} {ix 1} (ix 1 ∷ last ∷ []) [] refl))

  -- NO LANE ROW OF A VALUE LIES BETWEEN THE SOURCE'S READING OF AN OUTER ROW
  -- AND THE REAL FLATMAP'S VALUE OF IT: the lane reaches inside another
  -- value's outer row only by joining it past its own subscription, so past
  -- that value, and its own value's row lies before its subscription.
  lane-in : ∀ {o₁ x r n a y b} → σ₁ o₁ (out x) → σ₁ r (out (instEmit (value a) n)) → RO (ro-at r) (out a)
          → LaneOf fL (ro-at r) a y (out b) → (o₁ ⊕ [ sub OS.J ]) ≼ y → y ≼ ro-at o₁ → ⊥
  lane-in {o₁} {x} {r} {n} {a} {y} {b} r₁ σr xo (ly , sy) jy yr =
    ≺-irrefl {y} (≼-≺-≺ {y} {ro-at o₁} {y} yr (beyond (under-hot {H = Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)} {s = S} {q = Qo} {y = o₁} QS
      (OuterRow.hots-under r₁ Qo (≺→≼ {Qo} {p₀ ⊕ [ ix 1 ]} Qo≺s₂)) dj sS (InvAt.world IS ly) (InvAt.real IS ly) o₁y)))
    where
      q₀ S : Pos
      q₀ = p₀₀ ⊕ [ ix 1 ]
      S  = ro-at r ⊕ [ ix 1 ]

      okS : Ok (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S
      okS = ok-step (ro-at r) (ok-in (ok-step p₀₀ ok₂) (InvAt.world I-RO xo) (InvAt.real I-RO xo))

      IS : InvAt (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S (enter (fL a) S)
      IS = inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ S okS

      r≺S : r ≺ S
      r≺S = ≺-trans {r} {ro-at r} {S} (≺-ext r (ix 1 ∷ ix 0 ∷ [])) (≺-ext (ro-at r) [])

      QS : Qo ≼ S
      QS = ≺→≼ {Qo} {S} (≺-trans {Qo} {p₀ ⊕ [ ix 1 ]} {S} Qo≺s₂ (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {S} s₂≺c₁
             (≺-trans {c ⊕ [ ix 1 ]} {r} {S} (σ₁-after σr) r≺S)))

      dj : ∀ {w} → Wld (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) S w → w ≡ o₁ → ⊥
      dj ww refl = proj₂ okS (inj₂ (inj₁ (_ , r₁))) ww (⊑-inside (⊑-refl o₁))

      own : r ≡ o₁ → ⊥
      own eq = ≺-irrefl {y} (≼-≺-≺ {y} {ro-at o₁} {y} yr (subst (λ z → ro-at z ≺ y) eq (≺-trans {ro-at r} {S} {y} (≺-ext (ro-at r) []) sy)))

      same : o₁ ⊑ r ⊎ r ⊑ o₁ → r ≡ o₁
      same (inj₁ or) = OuterRow.σ₁-lead r₁ σr or
      same (inj₂ ro) = sym (OuterRow.σ₁-lead σr r₁ ro)

      sS : o₁ ⊑ S → ⊥
      sS os = own (same (⊑-cmp o₁ r os ((sub q₀ ∷ ix 1 ∷ ix 0 ∷ []) L.++ [ ix 1 ] , ⊕-assoc r (sub q₀ ∷ ix 1 ∷ ix 0 ∷ []) [ ix 1 ])))

      o₁≺y : o₁ ≺ y
      o₁≺y = ≺-≼-≺ {o₁} {o₁ ⊕ [ sub OS.J ]} {y} (≺-ext o₁ []) jy

      o₁y : o₁ ⊑ y
      o₁y = [ (λ lt → <ᵖ-between o₁ y (sub q₀ ∷ ix 1 ∷ ix 0 ∷ []) (Equivalence.to T-≡ o₁≺y) (Equivalence.to T-≡ lt)) , (λ eq → _ , eq) ]′
              (≼-split {y} {ro-at o₁} yr)

      beyond : OuterRow.Below r₁ Qo y → ro-at o₁ ≺ y
      beyond (e′ , zs , eq , qe) = subst (ro-at o₁ ≺_) (sym eq)
        (Equivalence.from T-≡ (<ᵖ-part o₁ {sub q₀} {sub e′} (ix 1 ∷ ix 0 ∷ []) zs (Equivalence.to T-≡ (≺-≼-≺ {q₀} {Qo} {e′} (≺-ext q₀ []) qe))))

  lane-in-outer : op ≡ switchᶠ → ∀ {o₁ x y b} → σ₁ o₁ (out x) → σ₃ y (out b) → (o₁ ⊕ [ sub OS.J ]) ≼ y → y ≼ ro-at o₁ → ⊥
  lane-in-outer op≡ {y = y} {b} r₁ σy jy yr with σ₃-lane σy
  ... | q , a , xo , _ , l , _ with ro-row xo
  ...   | r , n , σr , refl = lane-in r₁ σr xo (subst (λ o′ → RV.Lane o′ (ro-at r) a y (out b)) op≡ l) jy yr

  -- NO LANE OF THE REAL FLATMAP SHOWS AN `outerOpen`.
  σ₃-open : ∀ {y n} → σ₃ y (out (instEmit (mark outerOpen) n)) → ⊥
  σ₃-open = Fit.fine lane-fit

  -- THE REAL FLATMAP'S OUTER HOLDS EACH OF THE OUTER'S VALUES, at `ro-at`.
  ro-of : ∀ {o₁ a n} → σ₁ o₁ (out (instEmit (value a) n)) → RO (ro-at o₁) (out a)
  ro-of {o₁} {a} σo = subst (λ z → RO z (out a)) (trans (⊕-assoc (o₁ ⊕ [ sub q₀ ]) [ ix 1 ] [ ix 0 ]) (⊕-assoc o₁ [ sub q₀ ] (ix 1 ∷ ix 0 ∷ [])))
                        (each-at m σ₂ σ₁ env₀ L₁ q₀ σo (q₀≺σ₁ σo) (few-out σo) refl)
    where
      q₀ : Pos
      q₀ = p₀₀ ⊕ [ ix 1 ]

  -- The source reads the outer before the real flatMap does.
  J≺q₀ : OS.J ≺ (p₀₀ ⊕ [ ix 1 ])
  J≺q₀ = subst (_≺ (p₀₀ ⊕ [ ix 1 ])) (sym (proj₂ OS.J-under)) (P≺q₀ (proj₁ OS.J-under))

  J≺ro : ∀ c → (c ⊕ [ sub OS.J ]) ≺ ro-at c
  J≺ro c = Equivalence.from T-≡ (<ᵖ-part c {sub OS.J} {sub (p₀₀ ⊕ [ ix 1 ])} [] (ix 1 ∷ ix 0 ∷ []) (Equivalence.to T-≡ J≺q₀))

  split-met : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → Met M (xs ++ x ∷ (ys ++ (z , e) ∷ r₂))
  split-met r₁ {z} {e} {r₂} mt xs x ys refl = subst (Met M) (++-assoc xs (x ∷ ys) ((z , e) ∷ r₂)) mt

  in-r₁ : ∀ (r₁ : List Row) xs x ys → r₁ ≡ xs ++ x ∷ ys → x ∈ r₁
  in-r₁ r₁ xs x ys refl = ∈-++⁺ʳ xs (here refl)

  -- THE ROWS THAT QUEUE A LANE: an outer value's `outerOpen`, where the
  -- source shows the outer's row, owned by the real flatMap's value of it.
  OpenMark : Pos → Row → Set
  OpenMark q x = Σ A λ a → Σ Pos λ r → Σ Pos λ n → σ₁ r (out (instEmit (value a) n)) × q ≡ ro-at r
    × x ≡ (r ⊕ [ sub OS.J ] , out (just (inj₁ (outerB , instEmit (mark outerOpen) n))))

  que : List Row → ℕ
  que r = Flat.queue (proj₁ (past op init r))

  module QC = Count _≟ᵖ_ (rowKind markQue op) Own OpenMark (LaneMark laneStart) que

  private
    shown-at : ∀ {z′ e″ k e} → M z′ e″ → z′ ≡ k × e″ ≡ e → M k e
    shown-at mo (refl , refl) = mo

    open-caught : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {r a n} → σ₁ r (out (instEmit (value a) n)) → (r ⊕ [ sub OS.J ]) ≺ z
                → M (r ⊕ [ sub OS.J ]) (out (OS.g (instEmit (value a) n))) → Any (OpenMark (ro-at r)) r₁
    open-caught r₁ mt {r} {a} {n} σr jz mo with run-catch r₁ mt mo tt tt jz
    ... | a₁ , b₁ , e₁ , refl with InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ʳ a₁ (here refl))))) mo
    ...   | refl = any-++ʳ a₁ (here (a , r , n , σr , refl , refl))

  -- AN OUTER VALUE BEFORE A ROW THE SCAN MEETS HAS ITS `outerOpen` MET
  -- BEFORE IT.
  met-open : ∀ r₁ {z v r₂} → Met M (r₁ ++ (z , out v) ∷ r₂) → ∀ {r a n} → σ₁ r (out (instEmit (value a) n))
           → (r ⊕ [ sub OS.J ]) ≺ z → ¬ ¬ Any (OpenMark (ro-at r)) r₁
  met-open r₁ {z} mt {r} σr jz κ =
    outer-shown σr (mq′ (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))) (≺→≼ {r ⊕ [ sub OS.J ]} {z} jz)
      λ (_ , _ , mo , _ , _ , pn) → κ (open-caught r₁ mt σr jz (shown-at (toM mo) (pn refl)))

  -- EACH VALUE OF THE REAL FLATMAP'S OUTER HAS ITS `outerOpen` MET BEFORE
  -- THE CLOSER'S `outerDone`.
  open-met : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
           → ∀ {q a} → RO q (out a) → ¬ ¬ Any (OpenMark q) r₁
  open-met r₁ mt xo with ro-row xo
  ... | r , _ , σr , refl with close-sent (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))
  ...   | _ , w′ , σk , refl = met-open r₁ mt σr (CD.before-done σr (proj₁ σk) OS.J w′)

  -- EACH `outerOpen` QUEUES ONE LANE.
  open-one : ∀ {x q q′} → OpenMark q x → OpenMark q′ x → q ≡ q′
  open-one (_ , r , _ , _ , refl , refl) (_ , r′ , _ , _ , refl , e) with ⊕-injˡ r r′ (cong proj₁ e)
  ... | refl = refl

  private
    module LO = LaneOnce m {Fr = Fresh eh} op f (λ i → there (there (there (there (ρ i))))) σ₂ σ₁ env₀ g₂ L₁
                  (λ r → Held.early H₁ (proj₁ r)) (λ r → Held.ends H₁ (proj₁ r)) tp ad₂ cs
                  (λ a {t} L → IH.holds (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs (good-cons L g₂) (eh₄ {t}))
                  (λ a {t} L → IH.placed (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs (good-cons L g₂) (eh₄ {t}))

    module LI = LaneIdle m {Fr = Fresh eh} op f (λ i → there (there (there (there (ρ i))))) σ₂ σ₁ env₀ g₂ L₁
                  (λ r → Held.early H₁ (proj₁ r)) (λ r → Held.ends H₁ (proj₁ r)) tp ad₂ cs
                  (λ a {t} L → IH.holds (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs (good-cons L g₂) (eh₄ {t}))
                  (λ a {t} L → IH.placed (hf a (λ i → there (there (there (there (ρ i)))))) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) cs (good-cons L g₂) (eh₄ {t}))

  -- A LANE IS IDLE ON ITS OWN.
  lane-idle-own : ∀ {q a} → RO q (out a) → Idle (RV.Lane op q a)
  lane-idle-own = LI.lane-idle op (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

  -- A LANE STARTS ONCE.
  start-once : ∀ {q a y y′ n n′} → RO q (out a) → RV.Lane op q a y (out (instEmit (mark laneStart) n))
             → RV.Lane op q a y′ (out (instEmit (mark laneStart) n′)) → y ≡ y′
  start-once = LO.start-once (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

  -- NO `laneStart` OF A LANE PRECEDES ITS OWN IN THE SCAN.
  start-first : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → ∀ {q} → LaneMark laneStart q x → ¬ QC.DoneIn [] xs q
  start-first r₁ mt xs x ys eq (a , y , n , xo , refl , l) di with find di
  ... | _ , i , (a′ , y′ , n′ , xo′ , refl , l′) with ro-func xo xo′
  ...   | refl with start-once xo l l′
  ...     | refl = ≺-irrefl {y ⊕ [ sub LS.J ]} (met-before xs (split-met r₁ mt xs _ ys eq) i)

  -- EACH `laneStart` THE SCAN MEETS STARTS A LANE IT MET QUEUED, NEVER MET
  -- START, AND NEVER EMPTIED.
  start-live : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ xs x ys → r₁ ≡ xs ++ x ∷ ys → rowKind markQue op x ≡ kDone
             → ¬ ¬ Σ Pos λ q → LaneMark laneStart q x × QC.Live [] xs q
  start-live r₁ mt xs x ys eq kx κ with row-start op x kx
  ... | k , b , n , refl with lane-mark (run-prefix r₁ mt) {k = k} {b = b} {mk = laneStart} {n = n} (in-r₁ r₁ xs _ ys eq) (inj₁ refl)
  ...   | y , refl , refl , σs with σ₃-lane σs
  ...     | q , a , xo , rn , l , _ with ro-row xo
  ...       | r , _ , σr , refl =
    met-open xs (split-met r₁ mt xs _ ys eq) σr
      (≺-trans {r ⊕ [ sub OS.J ]} {ro-at r} {y ⊕ [ sub LS.J ]} (J≺ro r) (≺-trans {ro-at r} {y} {y ⊕ [ sub LS.J ]} (lane-past op fL RO l) (≺-ext y [])))
      λ oi → κ (ro-at r , (a , y , n , xo , refl , l) , (a , xo , rn) , oi , start-first r₁ mt xs _ ys eq (a , y , n , xo , refl , l)
                , λ (_ , _ , _ , _ , cb) → let (xc , _ , kc) = find cb in que-cut op xc kc)

  -- WITH NO LANE QUEUED AT THE CLOSER'S `outerDone`, EACH LANE OF A
  -- BOUNDED MERGE HAS STARTED: its value's `outerOpen` was met before the
  -- mark, and the queue rises at each and falls at each lane's start.
  queued-started : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
                 → que r₁ ≡ 0 → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ ¬ AC.StartIn [] r₁ q
  queued-started bd r₁ mt q0 xo rn κ =
    open-met r₁ mt xo λ oi →
      QC.drained r₁ (λ xs y ys eq → past-queue op init xs y (no-end r₁ mt xs eq))
        (λ { (_ , _ , _ , _ , _ , refl) → subst (λ o → markQue o outerOpen ≡ kStart) (sym bd) refl })
        (λ { (_ , _ , _ , _ , refl , _) → refl })
        (λ _ _ _ _ _ _ → open-one) (start-live r₁ mt) q0 (_ , xo , rn) oi
        (λ (_ , _ , _ , _ , cb) → let (xc , _ , kc) = find cb in que-cut op xc kc) κ

  -- AN IMMEDIATE LANE SHOWS ITS `laneStart`, under its value.
  lane-shows-start : (∀ k → op ≡ mergeᶠ (just k) → ⊥) → ∀ {q a} → Σ Pos λ y₀ → Σ _ λ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) × q ⊑ y₀
  lane-shows-start nb {q} {a} =
    let (r , u) = LaneStart.lane-start-row _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m (q ⊕ [ ix 1 ])
    in _ , _ , lane-of fL RO op nb (r , LaneLayers.under-ext (q ⊕ [ ix 1 ]) u)
     , LaneLayers.under-trans (LaneLayers.under-⊕ (LaneLayers.under-⊕ (LaneLayers.under-refl q) (ix 1)) (ix 0)) u

  private
    few-reach : ∀ {X : Set} {t : EmissionSet X} {k e} → Few t k → ES.Reach t k e
    few-reach f = proj₁ f , λ x lt _ → proj₂ f x lt

    -- A `laneStart` the source shows before a row the scan meets is met.
    start-caught : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q a y₀ n₀} → RO q (out a)
                 → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) → (y₀ ⊕ [ sub LS.J ]) ≺ z
                 → M (y₀ ⊕ [ sub LS.J ]) (out (just (inj₁ (laneB , instEmit (mark laneStart) n₀)))) → AC.StartIn [] r₁ q
    start-caught r₁ mt xo l jz mo with run-catch r₁ mt mo tt tt jz
    ... | a₁ , b₁ , e₁ , refl with InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ʳ a₁ (here refl))))) mo
    ...   | refl = any-++ʳ a₁ (here (_ , _ , _ , xo , refl , l))

    shown-at′ : ∀ {z′ e″ k e} → LS.M′ z′ e″ → z′ ≡ k × e″ ≡ e → M k e
    shown-at′ mo (refl , refl) = toM mo

    -- A row before one the scan meets lies before a later instant.
    before-inst : ∀ {k z v} → k ≺ z → instantOf z ≺ⁱ instantOf v → k ≺ v
    before-inst {k} {z} {v} kz zv with triⁱ (instantOf k) (instantOf z)
    ... | inj₁ lt        = instant-≺ k v (transⁱ lt zv)
    ... | inj₂ (inj₁ eq) = instant-≺ k v (subst (_≺ⁱ instantOf v) (sym eq) zv)
    ... | inj₂ (inj₂ gt) = ⊥-elim (≺-absurd {k} {z} kz (instant-≺ z k gt))

  -- AN IMMEDIATE LANE RUN AND NEVER CUT HAS STARTED BY THE CLOSER'S
  -- `outerDone`: its `laneStart` lies under its value, so before the mark,
  -- and the real flatMap, with few rows before a later instant, shows it.
  start-met : (∀ k → op ≡ mergeᶠ (just k) → ⊥) → ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
            → ∀ {v} → Few R v → instantOf z ≺ⁱ instantOf v
            → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ RV.Cut op q → ¬ ¬ AC.StartIn [] r₁ q
  start-met nb r₁ mt {v} Fv zv {q} {a} xo rn nc with ro-row xo
  ... | r , _ , σr , refl with close-sent (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))
  ...   | c , w′ , σk , refl = λ κ → lane-shows-start nb {q} {a} |>′ λ (y₀ , n₀ , l , ys , qy) →
    join-shows op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂)
      (shows-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂))
      (λ a s′ oks → shows-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s′ oks)
      (proj₁ Fv , λ x f lt → proj₂ Fv (R-from (x , few-reach f)) lt) λ fJ →
    let q₀ = p₀₀ ⊕ [ ix 1 ]
        x₀ = y₀ ⊕ [ sub LS.J ]
        x₀-eq : x₀ ≡ r ⊕ (sub q₀ ∷ ix 1 ∷ ix 0 ∷ ys ++ [ sub LS.J ])
        x₀-eq = trans (cong (_⊕ [ sub LS.J ]) (trans qy (⊕-assoc r (sub q₀ ∷ ix 1 ∷ ix 0 ∷ []) ys)))
                      (⊕-assoc r (sub q₀ ∷ ix 1 ∷ ix 0 ∷ ys) [ sub LS.J ])
        x₀≺z : x₀ ≺ (c ⊕ [ sub w′ ])
        x₀≺z = subst (_≺ (c ⊕ [ sub w′ ])) (sym x₀-eq) (CD.below-done σr (proj₁ σk) q₀ (ix 1 ∷ ix 0 ∷ ys ++ [ sub LS.J ]) w′)
        y₀≺v : y₀ ≺ v
        y₀≺v = before-inst {y₀} {c ⊕ [ sub w′ ]} {v} (≺-trans {y₀} {x₀} {c ⊕ [ sub w′ ]} (≺-ext y₀ []) x₀≺z) zv
        rR : R y₀ (out (instEmit (mark laneStart) n₀))
        rR = R-from (join-in op fL RO xo rn l (never-cut op fL RO nc) , proj₁ fJ , λ {k} x lt _ → proj₂ fJ x (≺-trans {k} {y₀} {v} lt y₀≺v))
        σs : σ₃ y₀ (out (instEmit (mark laneStart) n₀))
        σs = rR , λ {c′} rc → [ (λ le → le) , (λ lt → ⊥-elim (pin-not (InvAt.quiet I₃ rc rR lt))) ]′ (≼-or-≻ y₀ c′)
    in lane-shown σs (mq′ (proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))))) (≺→≼ {x₀} {c ⊕ [ sub w′ ]} x₀≺z)
         λ (z′ , e″ , m′ , _ , _ , pr) → κ (start-caught r₁ mt xo l x₀≺z (shown-at′ m′ (pr refl)))
    where
      pin-not : ∀ {c′ b} → PinBy c′ (out b) → ⊥
      pin-not (_ , () , _)

  -- A LANE RUN AND NEVER CUT HAS STARTED BY THE CLOSER'S `outerDone`, with
  -- no lane queued there.
  lane-started : ∀ r₁ {z n r₂} → Met M (r₁ ++ (z , out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) ∷ r₂)
               → Flat.queue (proj₁ (past op init r₁)) ≡ 0 → ∀ {v} → Few R v → instantOf z ≺ⁱ instantOf v
               → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ RV.Cut op q → ¬ ¬ AC.StartIn [] r₁ q
  lane-started r₁ mt q0 Fv zv xo rn nc with bounded? op
  ... | inj₁ (_ , bd) = queued-started bd r₁ mt q0 xo rn
  ... | inj₂ nb       = start-met nb r₁ mt Fv zv xo rn nc
