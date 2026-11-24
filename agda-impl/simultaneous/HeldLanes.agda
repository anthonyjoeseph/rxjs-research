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
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)

open import Tree using (Obs; FlatOp; map)
open import denotation.Position using (Pos; root; _≟ᵖ_; ix; sub; last; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (hot; enter; DenEnv; module Op; Ev; out; end; Few; _≼_; EmissionSet; _≺_)
open import simultaneous.SObs using (lone; module Elaborate; Flat; outerB; laneB; closeB)
open import simultaneous.Relations using (Met)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Routing; Held; Early; Idle; Sync; Ex; cnt; nameOf)
open import simultaneous.Counts using (Counts)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; Shows; PinBy; ok-step; _⊑_; InvAt; ⊕-injˡ; ok-in; ⊑-cmp; ⊑-refl; ⊑-inside; ⊕-assoc; ⊑-snoc) renaming (W to Wld)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import simultaneous.RealView using (nth-out)
open import simultaneous.CombSent using (starts-after)
open import denotation.Laws.Count using (⊑?; child)
open import Relation.Nullary using (yes; no)
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
open import denotation.Laws.Modulus using (entered-few; T-not; ≺-irrefl; ≼-split; ≺→≼; ≺-≼-≺; ≺-ext; ≺-trans; ≼-≺-≺; ≼-or-≻; ≺-absurd; ≼-refl)
open import denotation.Events using (<ᵖ-part; <ᵖ-between)
open import Data.Bool.Properties using (T-≡)
open import Function using (Equivalence; _|>′_)
open import simultaneous.HeldBase using (EnvHeld; module FlatHots; IH; shows-ev; Fresh; ev-undone; eh-u)
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
open import adequacy.Bound using (lane-st)
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
lane-past op f o {q} {y = y} l = let (s , _ , qs , sy) = lane-st op f o l in ≺-trans {q} {s} {y} qs sy

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
            → Σ Pos λ c → RV.Lane op q a c end × instantOf c ≡ instantOf y × y ≺ c
  done-ends x l with lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
      (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
      (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) x l
  ... | s , oks , r , sk , back with lane-take m undone _ (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂ s oks r tt
  ...   | w , refl , e = w ⊕ [ last ] , back e (≺-trans {s} {w ⊕ [ ix 0 ]} {w ⊕ [ last ]} sk (ix<last w)) , trans (inst-⊕ w [ last ]) (sym (inst-⊕ w [ ix 0 ])) , ix<last w

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
                     , (R-from (join-in op fL RO xo rn L₀ (λ c → nc (cutat-up op fL RO {q} {y₀} {y} lt c)) tt
                                , reach-down {q = y} {w = y₀} {e = out (instEmit (mark (laneDone kd)) n)} {e₁ = out (instEmit (mark laneStart) n₀)} (proj₂ (real-to m op (λ a → laneˢ (g a)) (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) (p₀₀ ⊕ [ ix 1 ]) (proj₁ σd))) lt tt)
                       , λ {c} ce → ≺→≼ {y₀} {c} (≺-≼-≺ {y₀} {y} {c} lt (proj₂ σd ce)))
                     , ≺→≼ {y₀} {y} lt

  -- A MARK THE SCAN MEETS, NO ROUTE AND NO BRACKET, IS A LANE'S ROW, one
  -- `sub J` below it.
  lane-row : ∀ {rx} → Met M rx → ∀ {k b mk n} → (k , out (just (inj₁ (b , instEmit (mark mk) n)))) ∈ rx
           → (Routing mk → ⊥) → (mk ≡ outerOpen → ⊥) → (mk ≡ outerClose → ⊥) → (mk ≡ outerDone → ⊥)
           → Σ Pos λ y → k ≡ y ⊕ [ sub LS.J ] × b ≡ laneB × σ₃ y (out (instEmit (mark mk) n))
  lane-row mt {b = laneB} i _ _ _ _ with lane-run mt
  ... | rs , pr , run , _ with bproj-mem pr i
  ...   | y , refl , j = y , refl , refl , proj₁ (run-row∈ run j)
  lane-row mt {b = outerB} i nr nop _ _ with outer-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , x , ox , o≡ , _ with open-mark o≡ nop
  ...   | refl = ⊥-elim (nr (Held.routing H₁ (proj₁ ox)))
  lane-row mt {b = closeB} i _ _ nc nd with close-sent (proj₁ (run-row∈ mt i))
  ... | _ , _ , cx , _ = ⊥-elim (closing-mark (close-marks cx) nc nd)

  -- A LANE MARK THE SCAN MEETS IS A LANE'S ROW.
  lane-mark : ∀ {rx} → Met M rx → ∀ {k b mk n} → (k , out (just (inj₁ (b , instEmit (mark mk) n)))) ∈ rx → mk ≡ laneStart ⊎ Σ ℕ (λ kd → mk ≡ laneDone kd)
            → Σ Pos λ y → k ≡ y ⊕ [ sub LS.J ] × b ≡ laneB × σ₃ y (out (instEmit (mark mk) n))
  lane-mark mt i mk = lane-row mt i (lane-routing mk) (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk })
    (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk }) (λ { refl → [ (λ ()) , (λ { (_ , ()) }) ]′ mk })

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

  private
    -- What lies under an outer row's `sub` past `Qo` lies past its value.
    below-past : ∀ {o₁ e y} (r₁ : σ₁ o₁ e) → OuterRow.Below r₁ Qo y → ro-at o₁ ≺ y
    below-past {o₁} r₁ (e′ , zs , eq , qe) = subst (ro-at o₁ ≺_) (sym eq)
      (Equivalence.from T-≡ (<ᵖ-part o₁ {sub (p₀₀ ⊕ [ ix 1 ])} {sub e′} (ix 1 ∷ ix 0 ∷ []) zs
        (Equivalence.to T-≡ (≺-≼-≺ {p₀₀ ⊕ [ ix 1 ]} {Qo} {e′} (≺-ext (p₀₀ ⊕ [ ix 1 ]) []) qe))))

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
      beyond = below-past r₁

  lane-in-outer : op ≡ switchᶠ → ∀ {o₁ x y b} → σ₁ o₁ (out x) → σ₃ y (out b) → (o₁ ⊕ [ sub OS.J ]) ≼ y → y ≼ ro-at o₁ → ⊥
  lane-in-outer op≡ {y = y} {b} r₁ σy jy yr with σ₃-lane σy
  ... | q , a , xo , _ , l , _ with ro-row xo
  ...   | r , n , σr , refl = lane-in r₁ σr xo (subst (λ o′ → RV.Lane o′ (ro-at r) a y (out b)) op≡ l) jy yr

  -- A BOUNDED LANE'S ROW UNDER AN OUTER ROW LIES PAST THAT ROW'S VALUE: a
  -- lane reaches under an outer row only by joining it past its own
  -- subscription, so past `Qo`; or by subscribing under that row itself,
  -- which only its own value's lane does, or under an earlier lane's end
  -- that already lies past the value.
  module UnderPast (n : ℕ) {o₁ x} (r₁ : σ₁ o₁ (out x)) where
    private
      module Bd = ES.Bounded n fL RO
      module BI = BoundedI (ok-step p₀₀ ok₂) n fL (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) I-RO
      open ES.Values RO using (Nth)

      own-row : ∀ {r e} → σ₁ r e → o₁ ⊑ (ro-at r ⊕ [ ix 1 ]) → r ≡ o₁
      own-row {r} σr os with ⊑-cmp o₁ r os ((sub (p₀₀ ⊕ [ ix 1 ]) ∷ ix 1 ∷ ix 0 ∷ []) L.++ [ ix 1 ] , ⊕-assoc r (sub (p₀₀ ⊕ [ ix 1 ]) ∷ ix 1 ∷ ix 0 ∷ []) [ ix 1 ])
      ... | inj₁ or = OuterRow.σ₁-lead r₁ σr or
      ... | inj₂ ro = sym (OuterRow.σ₁-lead σr r₁ ro)

      val-past : ∀ {q a} → RO q (out a) → o₁ ⊑ (q ⊕ [ ix 1 ]) → ro-at o₁ ≺ (q ⊕ [ ix 1 ])
      val-past xo os with ro-row xo
      ... | r , _ , σr , refl with own-row σr os
      ...   | refl = ≺-ext (ro-at r) []

      Qo-past : ∀ {q a s} → RO q (out a) → q ≺ s → Qo ≼ s
      Qo-past {s = s} xo qs with ro-row xo
      ... | r , _ , σr , refl = ≺→≼ {Qo} {s} (≺-trans {Qo} {p₀ ⊕ [ ix 1 ]} {s} Qo≺s₂ (≺-trans {p₀ ⊕ [ ix 1 ]} {c ⊕ [ ix 1 ]} {s} s₂≺c₁
        (≺-trans {c ⊕ [ ix 1 ]} {r} {s} (σ₁-after σr) (≺-trans {r} {ro-at r} {s} (≺-ext r (ix 1 ∷ ix 0 ∷ [])) qs))))

    mutual
      under-past : ∀ i {q a s y e} → Nth i q a → Bd.Starts i q (Bd.Sched i) s → ES.After (fL a) s y e → o₁ ⊑ y → ro-at o₁ ≺ y
      under-past i {q} {a} {s} {y} nt st (yr , sy) oy with ⊑? o₁ s
      ... | yes os = ≺-trans {ro-at o₁} {s} {y} (start-past i nt st os) sy
      ... | no ¬os = below-past r₁ (under-hot {H = Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)} {s = s} {q = Qo} {y = o₁}
                      (Qo-past (nth-out nt) (starts-after st)) (OuterRow.hots-under r₁ Qo (≺→≼ {Qo} {p₀ ⊕ [ ix 1 ]} Qo≺s₂))
                      dj ¬os (InvAt.world (BI.LI (nt , st)) yr) (InvAt.real (BI.LI (nt , st)) yr) oy)
        where
          dj : ∀ {w} → Wld (Hots (hot σ₂ ∷ hot σ₁ ∷ env₀)) s w → w ≡ o₁ → ⊥
          dj ww refl = proj₂ (BI.okS (nt , st)) (inj₂ (inj₁ (_ , r₁))) ww (⊑-inside (⊑-refl o₁))

      start-past : ∀ i {q a s} → Nth i q a → Bd.Starts i q (Bd.Sched i) s → o₁ ⊑ s → ro-at o₁ ≺ s
      start-past i nt (Bd.room _)              os = val-past (nth-out nt) os
      start-past i nt (Bd.freed _ _)           os = val-past (nth-out nt) os
      start-past i nt (Bd.queued _ _ kc _ _) os = sched-past i kc os

      sched-past : ∀ i {c} → Bd.Kth (_≡ c) (Bd.Sched i) 0 → o₁ ⊑ (c ⊕ [ ix 1 ]) → ro-at o₁ ≺ (c ⊕ [ ix 1 ])
      sched-past zero ()
      sched-past (suc i) {c} (inj₁ (_ , (_ , _ , _ , nt , st , (cx , sc)) , refl)) os with ⊑-snoc c os
      ... | inj₁ oc = ≺-trans {ro-at o₁} {c} {c ⊕ [ ix 1 ]} (under-past i nt st (cx , sc) oc) (≺-ext c [])
      ... | inj₂ eq = ⊥-elim (proj₂ (BI.okS (nt , st)) (inj₂ (inj₁ (_ , r₁))) (InvAt.world (BI.LI (nt , st)) cx) (⊑-inside ([ ix 1 ] , eq)))
      sched-past (suc i) (inj₂ kc) os = sched-past i kc os

    -- No lane row leads the outer row.
    lane-lead : ∀ {q a y e} → Bd.Lane q a y e → y ⊑ o₁ → ⊥
    lane-lead (_ , _ , sb , yr , _) yo = proj₂ (BI.okS sb) (inj₂ (inj₁ (_ , r₁))) (InvAt.world (BI.LI sb) yr) (⊑-inside yo)

    -- A LANE ROW A READER OF IT PLACES PAST A READER OF THE OUTER ROW LIES
    -- PAST THE ROW'S VALUE: under the row, by `under-past`; beside it, the
    -- readers keep the order of what they read.
    read-past : ∀ {q a y e l₁ l₂} → Bd.Lane q a y e → (o₁ ⊕ [ l₁ ]) ≺ (y ⊕ [ l₂ ]) → ro-at o₁ ≺ y
    read-past {y = y} {l₁ = l₁} {l₂} l@(i , s , (nt , st) , aft) lt with ⊑? o₁ y
    ... | yes oy = under-past i nt st aft oy
    ... | no ¬oy with ≼-or-≻ (ro-at o₁) y
    ...   | inj₁ le = [ (λ lt′ → lt′) , (λ eq → ⊥-elim (¬oy (_ , sym eq))) ]′ (≼-split {ro-at o₁} {y} le)
    ...   | inj₂ yr with child l₂ yr
    ...     | inj₁ yo = ⊥-elim ([ (λ y⊑o → lane-lead l y⊑o) , (λ o⊑y → ¬oy o⊑y) ]′ (⊑-cmp y o₁ yo (_ , refl)))
    ...     | inj₂ ly with <ᵖ-between o₁ (y ⊕ [ l₂ ]) (sub (p₀₀ ⊕ [ ix 1 ]) ∷ ix 1 ∷ ix 0 ∷ [])
                             (Equivalence.to T-≡ (≺-trans {o₁} {o₁ ⊕ [ l₁ ]} {y ⊕ [ l₂ ]} (≺-ext o₁ []) lt)) (Equivalence.to T-≡ ly)
    ...       | zs , eq with ⊑-snoc y (zs , eq)
    ...         | inj₁ oy = ⊥-elim (¬oy oy)
    ...         | inj₂ eq′ = ⊥-elim (lane-lead l ([ l₂ ] , eq′))

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

  -- A VALUE THE SOURCE MEETS AT OR PAST `z`.
  OutPast : Pos → Set
  OutPast z = Σ Pos λ w → Σ (Maybe (Input B)) λ v → M w (out v) × z ≼ w

  -- AN OUTER VALUE BEFORE A ROW THE SCAN MEETS, WITH A VALUE MET AT OR
  -- PAST IT, HAS ITS `outerOpen` MET BEFORE IT.
  met-open-at : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → OutPast z → ∀ {r a n} → σ₁ r (out (instEmit (value a) n))
              → (r ⊕ [ sub OS.J ]) ≺ z → ¬ ¬ Any (OpenMark (ro-at r)) r₁
  met-open-at r₁ {z} mt (w , _ , mw , zw) {r} σr jz κ =
    outer-shown σr (mq′ mw) (≺→≼ {r ⊕ [ sub OS.J ]} {w} (≺-≼-≺ {r ⊕ [ sub OS.J ]} {z} {w} jz zw))
      λ (_ , _ , mo , _ , _ , pn) → κ (open-caught r₁ mt σr jz (shown-at (toM mo) (pn refl)))

  -- AN OUTER VALUE BEFORE A ROW THE SCAN MEETS HAS ITS `outerOpen` MET
  -- BEFORE IT.
  met-open : ∀ r₁ {z v r₂} → Met M (r₁ ++ (z , out v) ∷ r₂) → ∀ {r a n} → σ₁ r (out (instEmit (value a) n))
           → (r ⊕ [ sub OS.J ]) ≺ z → ¬ ¬ Any (OpenMark (ro-at r)) r₁
  met-open r₁ {z} mt = met-open-at r₁ mt (z , _ , proj₁ (run-row∈ mt (∈-++⁺ʳ r₁ (here refl))) , ≼-refl {z})

  -- EACH VALUE OF THE REAL FLATMAP'S OUTER HAS ITS `outerOpen` MET BY THE
  -- CLOSER'S `outerDone`.
  open-met : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
           → ∀ {q a} → RO q (out a) → ¬ ¬ Any (OpenMark q) r₁
  open-met r₁ {z} mt mz₀ le ow xo with ro-row xo
  ... | r , _ , σr , refl with close-sent mz₀
  ...   | c , w′ , σk , refl = met-open-at r₁ mt ow σr (≺-≼-≺ {r ⊕ [ sub OS.J ]} {c ⊕ [ sub w′ ]} {z} (CD.before-done σr (proj₁ σk) OS.J w′) le)

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
                  (λ a {t} → ev-undone m (λ i → there (there (there (there (ρ i))))) (f a) (hot t ∷ hot σ₂ ∷ hot σ₁ ∷ env₀) (eh-u (eh₄ {t})))

  -- A LANE IS IDLE ON ITS OWN.
  lane-idle-own : ∀ {q a} → RO q (out a) → Idle (RV.Lane op q a)
  lane-idle-own = LI.lane-idle op (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

  -- A lane's subscription, read off one of its rows.
  sub-at : ∀ {Q a y e} → RO Q (out a) → RV.Lane op Q a y e → Pos
  sub-at xo l = proj₁ (lane-at op (ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀)) fL
    (inv-ev m (each valuesOf (connected (there (here refl)))) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂) (λ a → inv-ev m (laneˢ (g a)) (hot σ₂ ∷ hot σ₁ ∷ env₀) g₂)
    (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) xo l)

  -- A LANE'S SUBSCRIPTION IS ADMISSIBLE.
  lane-fresh-own : ∀ {q a k e} (xo : RO q (out a)) (l : RV.Lane op q a k e) → Fresh eh (sub-at xo l)
  lane-fresh-own = LI.lane-fresh op (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

  -- A LANE'S `laneDone` HOLDS A ROUTE, outside its burst and every exemption.
  lane-done-own : ∀ {q a k e} (xo : RO q (out a)) (l : RV.Lane op q a k e) → ∀ r₁ {y kd n}
                → Met (RV.Lane op q a) (r₁ ++ [ (y , out (instEmit (mark (laneDone kd)) n)) ]) → ¬ Sync (sub-at xo l) y → ¬ Ex cs y
                → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
  lane-done-own = LI.lane-done op (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

  -- A LANE COUNTS WHAT ITS PROGRAM COUNTS, exempt for its own burst.
  lane-counts-own : ∀ {q a k e} (xo : RO q (out a)) (l : RV.Lane op q a k e) → Counts (RV.Lane op q a) (λ y → Sync (sub-at xo l) y ⊎ Ex cs y)
  lane-counts-own = LI.lane-counts op (p₀₀ ⊕ [ ix 1 ]) (ok-step p₀₀ ok₂) fr₁ (early-inst [ ix 1 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] (early-inst [ ix 0 ] ep))))

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

  -- WITH NO LANE QUEUED BY OR PAST THE CLOSER'S `outerDone`, EACH LANE
  -- OF A BOUNDED MERGE HAS STARTED: its value's `outerOpen` was met before
  -- the mark, and the queue rises at each and falls at each lane's start.
  queued-started : ∀ {k} → op ≡ mergeᶠ (just k) → ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
                 → que r₁ ≡ 0 → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ ¬ AC.StartIn [] r₁ q
  queued-started bd r₁ mt mz₀ le ow q0 xo rn κ =
    open-met r₁ mt mz₀ le ow xo λ oi →
      QC.drained r₁ (λ xs y ys eq → past-queue op init xs y (no-end r₁ mt xs eq))
        (λ { (_ , _ , _ , _ , _ , refl) → subst (λ o → markQue o outerOpen ≡ kStart) (sym bd) refl })
        (λ { (_ , _ , _ , _ , refl , _) → refl })
        (λ _ _ _ _ _ _ → open-one) (start-live r₁ mt) q0 (_ , xo , rn) oi
        (λ (_ , _ , _ , _ , cb) → let (xc , _ , kc) = find cb in que-cut op xc kc) κ

  -- A LANE SUBSCRIBED AT `s` SHOWS ITS `laneStart` under `s`'s first step.
  start-under : ∀ {a} s → Σ Pos λ y₀ → Σ _ λ n₀ → enter (fL a) s y₀ (out (instEmit (mark laneStart) n₀)) × LaneLayers.Under (s ⊕ [ ix 0 ]) y₀
  start-under {a} s = let (r , u) = LaneStart.lane-start-row _ (f a) (hot σ₂ ∷ hot σ₁ ∷ env₀) m s in _ , _ , r , u

  -- AN IMMEDIATE LANE SHOWS ITS `laneStart`, under its value.
  lane-shows-start : (∀ k → op ≡ mergeᶠ (just k) → ⊥) → ∀ {q a} → Σ Pos λ y₀ → Σ _ λ n₀ → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) × q ⊑ y₀
  lane-shows-start nb {q} {a} =
    let (_ , _ , r , u) = start-under {a} (q ⊕ [ ix 1 ])
    in _ , _ , lane-of fL RO op nb (r , LaneLayers.under-ext (q ⊕ [ ix 1 ]) u)
     , LaneLayers.under-trans (LaneLayers.under-⊕ (LaneLayers.under-⊕ (LaneLayers.under-refl q) (ix 1)) (ix 0)) u

  -- A `laneStart` the source shows before a row the scan meets is met.
  start-caught : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {q a y₀ n₀} → RO q (out a)
               → RV.Lane op q a y₀ (out (instEmit (mark laneStart) n₀)) → (y₀ ⊕ [ sub LS.J ]) ≺ z
               → M (y₀ ⊕ [ sub LS.J ]) (out (just (inj₁ (laneB , instEmit (mark laneStart) n₀)))) → AC.StartIn [] r₁ q
  start-caught r₁ mt xo l jz mo with run-catch r₁ mt mo tt tt jz
  ... | a₁ , b₁ , e₁ , refl with InvAt.func I-M (proj₁ (run-row∈ mt (∈-++⁺ˡ (∈-++⁺ʳ a₁ (here refl))))) mo
  ...   | refl = any-++ʳ a₁ (here (_ , _ , _ , xo , refl , l))

  private
    few-reach : ∀ {X : Set} {t : EmissionSet X} {k e} → Few t k → ES.Reach t k e
    few-reach f = proj₁ f , λ x lt _ → proj₂ f x lt

    shown-at′ : ∀ {z′ e″ k e} → LS.M′ z′ e″ → z′ ≡ k × e″ ≡ e → M k e
    shown-at′ mo (refl , refl) = toM mo

    -- A row before one the scan meets lies before a later instant.
    before-inst : ∀ {k z v} → k ≺ z → instantOf z ≺ⁱ instantOf v → k ≺ v
    before-inst {k} {z} {v} kz zv with triⁱ (instantOf k) (instantOf z)
    ... | inj₁ lt        = instant-≺ k v (transⁱ lt zv)
    ... | inj₂ (inj₁ eq) = instant-≺ k v (subst (_≺ⁱ instantOf v) (sym eq) zv)
    ... | inj₂ (inj₂ gt) = ⊥-elim (≺-absurd {k} {z} kz (instant-≺ z k gt))

  -- AN IMMEDIATE LANE RUN AND NEVER CUT HAS STARTED BY OR PAST THE
  -- CLOSER'S `outerDone`: its `laneStart` lies under its value, so before the mark,
  -- and the real flatMap, with few rows before a later instant, shows it.
  start-met : (∀ k → op ≡ mergeᶠ (just k) → ⊥) → ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
            → ∀ {v} → Few R v → instantOf z₀ ≺ⁱ instantOf v
            → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ RV.Cut op q → ¬ ¬ AC.StartIn [] r₁ q
  start-met nb r₁ {z} mt mz₀ le (w , _ , mw , zw) {v} Fv zv {q} {a} xo rn nc with ro-row xo
  ... | r , _ , σr , refl with close-sent mz₀
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
        rR = R-from (join-in op fL RO xo rn l (never-cut op fL RO nc) tt , proj₁ fJ , λ {k} x lt _ → proj₂ fJ x (≺-trans {k} {y₀} {v} lt y₀≺v))
        σs : σ₃ y₀ (out (instEmit (mark laneStart) n₀))
        σs = rR , λ {c′} rc → [ (λ le → le) , (λ lt → ⊥-elim (pin-not (InvAt.quiet I₃ rc rR lt))) ]′ (≼-or-≻ y₀ c′)
        x₀≺z′ : x₀ ≺ z
        x₀≺z′ = ≺-≼-≺ {x₀} {c ⊕ [ sub w′ ]} {z} x₀≺z le
    in lane-shown σs (mq′ mw) (≺→≼ {x₀} {w} (≺-≼-≺ {x₀} {z} {w} x₀≺z′ zw))
         λ (z′ , e″ , m′ , _ , _ , pr) → κ (start-caught r₁ mt xo l x₀≺z′ (shown-at′ m′ (pr refl)))
    where
      pin-not : ∀ {c′ b} → PinBy c′ (out b) → ⊥
      pin-not (_ , () , _)

  -- A LANE RUN AND NEVER CUT HAS STARTED BY OR PAST THE CLOSER'S
  -- `outerDone`, with no lane queued there.
  lane-started : ∀ r₁ {z e r₂} → Met M (r₁ ++ (z , e) ∷ r₂) → ∀ {z₀ n} → M z₀ (out (just (inj₁ (closeB , instEmit (mark outerDone) n)))) → z₀ ≼ z → OutPast z
               → Flat.queue (proj₁ (past op init r₁)) ≡ 0 → ∀ {v} → Few R v → instantOf z₀ ≺ⁱ instantOf v
               → ∀ {q a} → RO q (out a) → RV.Runs op q → ¬ RV.Cut op q → ¬ ¬ AC.StartIn [] r₁ q
  lane-started r₁ mt mz₀ le ow q0 Fv zv xo rn nc with bounded? op
  ... | inj₁ (_ , bd) = queued-started bd r₁ mt mz₀ le ow q0 xo rn
  ... | inj₂ nb       = start-met nb r₁ mt mz₀ le ow Fv zv xo rn nc
