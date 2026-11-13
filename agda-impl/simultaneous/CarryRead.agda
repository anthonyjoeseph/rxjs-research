{-# OPTIONS --guardedness #-}

-- THE READER'S SENDING: the fold of `joinStep` over its reading, each
-- fold's emits sent on a lane under the row folded in.  A fold's emits
-- are the emit it folds in, past the routes a reader joining late sends
-- first, so the sending carries what the reading carries: a plain row's
-- carrier is its reading row's own joined row (`simultaneous.ReadRows`'
-- `Pt`), and everything the reading's carry lists, few or live, the
-- joined rows hung under it do too.
--
-- The reading is a hot rejoined over a run with no pins, so the carry's
-- pins hold vacuously.
--
-- DEAD ROUTE: over any reading, not only a hot rejoined.  A joined pin
--   row waits on every joined row before its connect, so it is a row
--   only with those listed; the reading's carry lists rows only up to a
--   carrier (`Listed`), never up to a connect, so nothing builds the
--   joined pin a plain pin's carrier must be.
module simultaneous.CarryRead where

open import Data.Bool using (true)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (any?)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; ix; _⊕_; _≟ᵖ_; root)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Den; hot; enter; Few; InE; _≺_; _≼_; module Op)
  renaming (shown to rj-shown)
open import denotation.Laws.Modulus using (≺→≼; ≺-≼-≺; ≼-split; entered-reach)
open import denotation.Laws.Worlds using (InvAt; _⊑_; ⊑-trans; ⊑-≼)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.Attribution using (Live; Shown; Match; Every; One; Reads)
open import simultaneous.Listing using (Listed)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Folds using (few-¬¬listed)
open import simultaneous.CarryBase using (From; PMap; CarryAt; Whole; whole-listed; sub-listed; instant-⊕; IntoAt; Near; ahead-over)
open import simultaneous.Carry using (annValues)
open import simultaneous.ReadRows using (module Rows; step-just; step-none; of-shown; of-marks; up; up-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; joinStep)

-- The elaborated reader's run over a handle: the fold of `joinStep`,
-- each fold's emits sent.
Reading : ∀ {X} → Den (AIE X) → Den (IE X)
Reading d = Op.flatMap (mergeᶠ nothing) (λ x → Op.of (proj₂ x)) (Op.scan joinStep (true , []) d)

private
  oe : ∀ {B : Set} {x : B} → out x ≡ end → ⊥
  oe ()

  module Post {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {T : EmissionSet (AIE X)} {s s′ : Pos}
    (Iu : InvAt H s′ (enter (hot T) s′)) (c : CarryAt annValues M HP HE LP t (enter (hot T) s′) s s′) where

    u : EmissionSet (AIE X)
    u = enter (hot T) s′

    pinU : ∀ {y r} → u y (pin r) → ⊥
    pinU (rj-shown _ () _ , _)

    func : ∀ {y e e′} → u y e → u y e′ → e ≡ e′
    func = InvAt.func Iu

    quietU : ∀ {c y e} → u c end → u y e → c ≺ y → ⊥
    quietU xc xy cy with InvAt.quiet Iu xc xy cy
    ... | _ , refl , _ = pinU xy

    open Rows {X} {u} func (InvAt.flat Iu) pinU (λ {q} {e} → entered-reach (hot T) s′ {q} {e}) quietU
    open CarryAt c

    instH : ∀ {l k} → Hang l k → instantOf k ≡ instantOf l
    instH {l} h = let (σ , eq) = hang-⊑ h in trans (cong instantOf eq) (instant-⊕ l σ)

    MatchV : Ev X → Ev (IE X) → Set
    MatchV = Match Every (One valuesOf) (Reads valuesOf)

    Img′ : Pos → Pos → Set
    Img′ k l′ = Σ Pos λ l → Img k l × Pt l l′

    PB′ : Pos → Pos → Set
    PB′ k l′ = Σ Pos λ l → PB k l × Pt l l′ × Σ _ (u l)

    pb-few′ : ∀ {l′ e} → R l′ e → Σ (List Pos) λ ks → ∀ {k} → PB′ k l′ → k ∈ ks
    pb-few′ y = proj₁ (pb-few (vrow v)) , λ { (l , pb , p , (_ , x)) → proj₂ (pb-few (vrow v)) (subst (PB _) (hang-uniq x (vrow v) (pt-hang p) (vhang v)) pb) }
      where v = view (proj₁ y)

    img′ : ∀ {k e} → t k e → Unpinned e → Live t k → Listed t k → LP k
         → (Σ Pos λ l′ → Img′ k l′ × Σ (Ev (IE X)) λ e″ → R l′ e″ × Listed R l′ × MatchV e e″)
           ⊎ (e ≡ skip × IntoAt Img′ R PB′ HP s k)
    img′ {k} x un lv Lt lp with img x un lv Lt lp
    ... | inj₁ (l , i , e₀ , y , Lu , m) =
      let (l′ , p , e″ , r , Lr , tr) = post y Lu in inj₁ (l′ , (l , i , p) , e″ , r , Lr , tr m)
    ... | inj₂ (eq , ((l , (e₁ , y) , Lu , pb) , rest)) =
      let (l′ , p , e″ , r , Lr , _) = post y Lu in inj₂ (eq , ((l′ , (e″ , r) , Lr , (l , pb , p , (e₁ , y))) , rest′ rest))
      where
        rest′ : instantOf k ≡ instantOf s
                ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → Img k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ _ (u l₀) × Listed u l₀)
                ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
              → instantOf k ≡ instantOf s
                ⊎ (Σ Pos λ k₀ → Σ Pos λ l₀ → Img′ k₀ l₀ × k₀ ≺ k × instantOf k₀ ≡ instantOf k × Σ _ (R l₀) × Listed R l₀)
                ⊎ Σ Pos (λ h → HP h × instantOf h ≡ instantOf k)
        rest′ (inj₁ ie) = inj₁ ie
        rest′ (inj₂ (inj₁ (k₀ , l₀ , i₀ , kk , ie , (_ , y₀) , L₀))) =
          let (l₀′ , p₀ , e₃ , r₀ , Lr₀ , _) = post y₀ L₀ in inj₂ (inj₁ (k₀ , l₀′ , (l₀ , i₀ , p₀) , kk , ie , (e₃ , r₀) , Lr₀))
        rest′ (inj₂ (inj₂ h)) = inj₂ (inj₂ h)

    img¬¬′ : ∀ {k e} → t k e → Unpinned e → Live t k → Few t k
           → ¬ ¬ ((Σ Pos λ l′ → Img′ k l′ × Σ (Ev (IE X)) λ e″ → R l′ e″ × MatchV e e″) ⊎ e ≡ skip)
    img¬¬′ x un lv fw n = img¬¬ x un lv fw λ
      { (inj₁ (l , i , e₀ , y , m)) → few-¬¬listed (fewU y) λ Lu →
          let (l′ , p , e″ , r , _ , tr) = post y Lu in n (inj₁ (l′ , (l , i , p) , e″ , r , tr m))
      ; (inj₂ eq) → n (inj₂ eq) }

    shown-lane : ∀ {q st l′ v} → S.Acc q st → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 (proj₂ st)) l′ (out v) → Shown (One valuesOf) (out v)
               → Live R l′ → Few R l′ → Σ Pos λ k → Img′ k l′ × Σ (Ev X) λ e₀ → t k e₀ × MatchV e₀ (out v)
    shown-lane {q} ac r sh lv fw with acc-step ac
    ... | b , (rt , nothing) , y , refl = ⊥-elim (of-marks (q ⊕ [ ix 1 ]) 0 _ (step-none b rt) r sh)
    ... | b , (rt , just w) , y , refl with step-just b rt w
    ...   | ms , mk , eq with of-shown (q ⊕ [ ix 1 ]) 0 ms w mk (subst (λ z → InE (ofᴱ (q ⊕ [ ix 1 ]) 0 z) _ _) eq r) sh
    ...     | l′eq , refl =
      let (k , i , e₀ , tk , m) = shown y sh (liveU y (lane-hang r) lv) (fewU′ y (lane-hang r) fw)
      in k , (q , i , inj₂ ((rt , just w) , y , _ , ac , ms , eq , l′eq)) , e₀ , tk , tr-just m

    shown′ : ∀ {l′ e″} → J.JoinT l′ e″ → Shown (One valuesOf) e″ → Live R l′ → Few R l′
           → Σ Pos λ k → Img′ k l′ × Σ (Ev X) λ e₀ → t k e₀ × MatchV e₀ e″
    shown′ (J.val _) () _ _
    shown′ (J.step _) () _ _
    shown′ (J.opass _ _) () _ _
    shown′ (J.lpass _ _ _ _ _ _) () _ _
    shown′ (J.opin _) () _ _
    shown′ (J.oend (S.send x , _) _) _ lv fw =
      let (k , i , e₀ , tk , m) = shown x tt (liveU x h-at lv) (fewU′ x h-at fw)
      in k , (_ , i , inj₁ (refl , λ y → oe (func y x))) , e₀ , tk , tr-end m
    shown′ (J.lend (S.sval ac , _) _ ((r , _) , _) _ _ d) _ _ _ = ⊥-elim (not-done (acc-u ac) (lane-hang r) d)
    shown′ (J.lane {e = out _} (S.sval ac , _) _ ((r , _) , _) _ _) sh lv fw = shown-lane ac r sh lv fw
    shown′ (J.lane {e = end} _ _ _ _ ()) _ _ _
    shown′ (J.lane {e = skip} _ _ _ _ _) () _ _
    shown′ (J.lane {e = pin _} _ _ _ _ _) () _ _
    shown′ (J.hand _ _ _ _ ()) _ _ _
    shown′ (J.left _ _ _ _ _) () _ _
    shown′ (J.run () _) _ _ _
    shown′ (J.rend () _ _) _ _ _
    shown′ (J.rpass () _ _) _ _ _
    shown′ (J.rhand () _) _ _ _

    img-fun′ : ∀ {k l₁ l₂} → Img′ k l₁ → Img′ k l₂ → l₁ ≡ l₂
    img-fun′ (_ , i₁ , p₁) (_ , i₂ , p₂) with img-fun i₁ i₂
    ... | refl = pt-fun p₁ p₂

    place′ : ∀ {m e} → R m e → Live R m → Listed R m
           → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l′ → Img′ k l′ × instantOf l′ ≡ instantOf m × Near R m l′)
             ⊎ Σ Pos λ h → HE h × instantOf h ≡ instantOf m
    place′ {m} y lv Lm = go (place x (liveU x h lv) Lu)
      where
        v = view (proj₁ y)
        l = vpos v
        x = vrow v
        h = vhang v
        Lu = listedU x h Lm

        viaPost : ∀ {k l₀ e₁} → Img k l₀ → instantOf l₀ ≡ instantOf l → u l₀ e₁ → Listed u l₀
                → Σ Pos λ l′ → Img′ k l′ × instantOf l′ ≡ instantOf m × Near R m l′
        viaPost {l₀ = l₀} i ie y₀ L₀ =
          let (l₀′ , p₀ , e″ , r₀ , Lr₀ , _) = post y₀ L₀
          in l₀′ , (l₀ , i , p₀) , trans (instH (pt-hang p₀)) (trans ie (sym (instH h))) , inj₂ ((e″ , r₀) , Lr₀)

        near : ∀ {k l₀} → Img k l₀ → instantOf l₀ ≡ instantOf l → Near u l l₀
             → Σ Pos λ l′ → Img′ k l′ × instantOf l′ ≡ instantOf m × Near R m l′
        near i ie (inj₂ ((_ , y₀) , L₀)) = viaPost i ie y₀ L₀
        near {l₀ = l₀} i ie (inj₁ l₀l) with ≼-split {l₀} {l} l₀l
        ... | inj₂ refl = viaPost i ie x Lu
        ... | inj₁ lt with any? (l₀ ≟ᵖ_) (proj₁ Lu)
        ...   | yes mm = viaPost i ie (proj₂ (proj₂ (proj₂ (proj₂ Lu) mm))) (sub-listed Lu lt)
        ...   | no nm  = l₀ , (l₀ , i , inj₁ (refl , λ y₀ → nm (proj₁ (proj₂ Lu) y₀ lt))) , trans ie (sym (instH h))
                       , inj₁ (≺→≼ {l₀} {m} (≺-≼-≺ {l₀} {l} {m} lt (⊑-≼ (hang-⊑ h))))

        go : instantOf l ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l₀ → Img k l₀ × instantOf l₀ ≡ instantOf l × Near u l l₀)
             ⊎ Σ Pos (λ h′ → HE h′ × instantOf h′ ≡ instantOf l)
           → instantOf m ≡ instantOf s′ ⊎ (Σ Pos λ k → Σ Pos λ l′ → Img′ k l′ × instantOf l′ ≡ instantOf m × Near R m l′)
             ⊎ Σ Pos λ h′ → HE h′ × instantOf h′ ≡ instantOf m
        go (inj₁ ie)                        = inj₁ (trans (instH h) ie)
        go (inj₂ (inj₁ (k , l₀ , i , ie , nr))) = inj₂ (inj₁ (k , near i ie nr))
        go (inj₂ (inj₂ (h′ , he , ie)))     = inj₂ (inj₂ (h′ , he , trans ie (sym (instH h))))

    live′ : ∀ {k l′} → Img′ k l′ → Live t k → Live R l′
    live′ (l , i , p) lt {c} rc = go p (live i lt (end-src rc))
      where
        go : ∀ {l′} → Pt l l′ → l ≼ c → l′ ≼ c
        go (inj₁ (refl , _)) lc = lc
        go {l′} (inj₂ (a , y , po)) lc with ≼-split {l} {c} lc
        ... | inj₁ lc′ = ≺→≼ {l′} {c} (hang-lt y (end-src rc) lc′ (pt-hang (inj₂ (a , y , po))) h-at)
        ... | inj₂ refl = ⊥-elim (oe (func y (end-src rc)))

    whole′ : Whole t → (∀ {c} → t c end → ⊥) → (∀ {q} → LP q) → Whole R
    whole′ wt ne lp with whole wt ne lp
    ... | ks , G , B = rowsOf ks g , (λ y → let v = view (proj₁ y) in rowsOf-in ks g (G (vrow v)) (vin v (g (G (vrow v)))))
                     , λ m → let (z , zm , km) = rowsOf-out ks g m in r-at (proj₂ (B zm)) WL km
      where
        WL : ∀ {v} → Listed u v
        WL = whole-listed (ks , G , B)

        g : ∀ {x} → x ∈ ks → Cell x
        g m = cell (proj₂ (B m)) WL

    bk′ : Pos → List Pos
    bk′ l′ = bk l′ ++ bk (up l′) ++ bk (up (up l′))

    in-bk′ : ∀ {k l′} → Img′ k l′ → k ∈ bk′ l′
    in-bk′ {k} (l , i , p) = at (pt-hang p)
      where
        at : ∀ {l′} → Hang l l′ → k ∈ bk′ l′
        at h-at       = ∈-++⁺ˡ (in-bk i)
        at h-val      = ∈-++⁺ʳ (bk _) (∈-++⁺ˡ (subst (λ z → k ∈ bk z) (sym (up-⊕ l (ix 0))) (in-bk i)))
        at (h-lane b) = ∈-++⁺ʳ (bk _) (∈-++⁺ʳ (bk _)
          (subst (λ z → k ∈ bk z) (sym (trans (cong up (up-⊕ (l ⊕ [ ix 1 ]) b)) (up-⊕ l (ix 1)))) (in-bk i)))

    -- The sending listed before a point its carriers follow.
    postulate
      read-cover : ∀ {v w} → Listed t v → LP v → Live t v → From Img′ PB′ t R v w → Listed R w

    carry : (∀ {k r} → t k (pin r) → ⊥) → CarryAt valuesOf M HP HE LP t R s s′
    carry nopin = record
      { Img     = Img′
      ; ext     = λ { (l , i , p) → let (y , my , yl) = ext i in y , my , ⊑-trans yl (hang-⊑ (pt-hang p)) }
      ; PB      = PB′
      ; pb-few  = pb-few′
      ; pb-img  = λ { (_ , pb , _) (_ , i , _) → pb-img pb i }
      ; pb-past = λ { (_ , pb , p , (_ , x)) tk lv _ m xk nxk → ahead-over (pb-past pb tk lv x m xk nxk) (hang-⊑ (pt-hang p)) }
      ; img     = img′
      ; img¬¬   = img¬¬′
      ; shown   = λ y sh lv fw → shown′ (proj₁ y) sh lv fw
      ; img-row = λ { (_ , i , _) → img-row i }
      ; img-fun = img-fun′
      ; place   = place′
      ; live    = live′
      ; few     = λ { (_ , i , _) → few i }
      ; whole   = whole′
      ; cover   = read-cover
      ; bk      = bk′
      ; in-bk   = in-bk′
      ; pinned  = λ kp _ _ _ → ⊥-elim (nopin kp)
      }

    -- A row read carried into its instant: on, or under, the annotated carrier.
    pb-up : ∀ {k l′} → PB′ k l′ → Σ Pos λ l → PB k l × l ⊑ l′
    pb-up (l , pb , p , _) = l , pb , hang-⊑ (pt-hang p)

read-post : ∀ {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {T : EmissionSet (AIE X)} {s s′}
          → InvAt H s′ (enter (hot T) s′) → CarryAt annValues M HP HE LP t (enter (hot T) s′) s s′
          → (∀ {k r} → t k (pin r) → ⊥) → CarryAt valuesOf M HP HE LP t (enter (Reading (hot T)) s′) s s′
read-post Iu c nopin = Post.carry Iu c nopin

read-post-pb : ∀ {X : Set} {M : PMap} {HP HE LP H : Pos → Set} {t : EmissionSet X} {T : EmissionSet (AIE X)} {s s′}
             → (Iu : InvAt H s′ (enter (hot T) s′)) (c : CarryAt annValues M HP HE LP t (enter (hot T) s′) s s′) (nopin : ∀ {k r} → t k (pin r) → ⊥)
             → ∀ {k l′} → CarryAt.PB (read-post Iu c nopin) k l′ → Σ Pos λ l → CarryAt.PB c k l × l ⊑ l′
read-post-pb Iu c _ = Post.pb-up Iu c
