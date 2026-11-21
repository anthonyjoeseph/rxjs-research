{-# OPTIONS --guardedness #-}

-- THE LANES' ROWS THE SCAN'S SOURCE MEETS ARE A RUN OF THE LANES.  The
-- source reads the lanes through one reader, five operators deep, at a
-- subscription fixed by its own `of`s: so a lane row it shows carries,
-- level by level, as few rows before it as it has, and any earlier lane
-- row past that reader is shown too, at its own place below.  A lane row
-- the lanes would show before the one the source meets is then one the
-- source would have met first.
module simultaneous.LaneSplit where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
import denotation.Read as Run
import simultaneous.Project as Proj
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; Path; ix; sub; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-down)
open import denotation.EmissionSet using (Ev; out; skip; pin; end; EmissionSet; Den; hot; enter; Reach; Rejoin; shown;
  Truncate; Seen; _≺_; _≼_; at-out; on-out; map-out; module Op; module TakeWhile; module Merge; module Bounded)
open import denotation.Read using (Run; Least; After; Visible; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≼-split; reach-few)
open import denotation.Laws.Worlds using (Lawful; ⊕-assoc)
open import denotation.Laws.Rejoined using (lower; row-few)
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB; laneB; closeB)
open import simultaneous.Project using (Proj; keep; drop)
open import simultaneous.FlatLanes using (laneTag)
open import simultaneous.DenRows using (module Cat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Input; going)

-- A lane's row, as the source tags it.
Ln : ∀ {B} → IE B → Maybe (Input B)
Ln x = just (inj₁ (laneB , x))

-- Where the source's reader of the lanes subscribes, under its own `of`s.
module Spots (P : Pos) where
  q₁ S₂ q₂ s₃ q₃ J : Pos
  q₁ = P ⊕ [ ix 1 ]
  S₂ = q₁ ⊕ [ ix 1 ]
  q₂ = S₂ ⊕ [ ix 0 ]
  s₃ = q₂ ⊕ [ ix 1 ]
  q₃ = s₃ ⊕ [ ix 1 ]
  J  = q₃ ⊕ [ ix 1 ]

  private
    ext : ∀ {x} → Σ Path (λ zs → x ≡ P ⊕ zs) → ∀ l → Σ Path (λ zs → x ⊕ [ l ] ≡ P ⊕ zs)
    ext (zs , refl) l = zs ++ [ l ] , ⊕-assoc P zs [ l ]

  J-under : Σ Path λ zs → J ≡ P ⊕ zs
  J-under = ext (ext (ext (ext (ext ([ ix 1 ] , refl) (ix 1)) (ix 0)) (ix 1)) (ix 1)) (ix 1)

  s₃≺J : s₃ ≺ J
  s₃≺J = ≺-trans {s₃} {q₃} {J} (≺-ext s₃ []) (≺-ext q₃ [])

  S₂≺J : S₂ ≺ J
  S₂≺J = ≺-trans {S₂} {q₂} {J} (≺-ext S₂ []) (≺-trans {q₂} {s₃} {J} (≺-ext q₂ []) s₃≺J)

-- The source as operators: the trackers, then the flatMap's own branches
-- concatenated before a closing `nothing`.
SrcOf : ∀ {B} → (Bool → Den (Maybe (Input B))) → Pos → EmissionSet (Maybe (Input B))
SrcOf F P = enter (Op.takeWhile false going (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ [])))) P

module LaneSplit {B : Set} (σ : EmissionSet (IE B)) (Lσ : Lawful σ) (P : Pos)
                 (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B)))
                 (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
                 (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of (outerB ∷ laneB ∷ closeB ∷ [])))
                 (eqG : G laneB ≡ Op.map (λ e → just (inj₁ (laneB , e))) (hot σ))
                 (noF : ∀ {s k x} → enter (F true) s k (out (Ln x)) → ⊥)
                 (noC : ∀ {s k x} → enter (C false) s k (out (Ln x)) → ⊥)
                 (noG : ∀ {b s k x} → enter (G b) s k (out (Ln x)) → b ≡ laneB)
                 (funcM : ∀ {y e e′} → SrcOf F P y e → SrcOf F P y e′ → e ≡ e′)
                 (past : ∀ zs {k e} → σ k e → (P ⊕ zs) ≺ k) where
  open Spots P

  M′ : EmissionSet (Maybe (Input B))
  M′ = SrcOf F P

  pastJ : ∀ {k e} → σ k e → J ≺ k
  pastJ {k} r = subst (_≺ k) (sym (proj₂ J-under)) (past (proj₁ J-under) r)

  under-J : ∀ {k} → J ≺ k → J ≺ (k ⊕ [ sub J ])
  under-J {k} jk = ≺-trans {J} {k} {k ⊕ [ sub J ]} jk (≺-ext k [])

  -- Two lanes' rows one label down keep their order.
  mono : ∀ {k e y e′} → σ k e → σ y e′ → k ≺ y → (k ⊕ [ sub J ]) ≺ (y ⊕ [ sub J ])
  mono {k} {e} {y} {e′} rk ry ky =
    Equivalence.from T-≡ (<ᵖ-down k y (sub J) (sub J) (Equivalence.to T-≡ ky) (λ l ls eq → Lawful.flat Lσ rk (subst (λ z → σ z e′) eq ry)))

  -- Below a row it reaches few rows before, a level has as few.
  tr↓ : ∀ {V} {t : EmissionSet V} Y a {K e} → Reach t Y (out a) → t K e → K ≺ Y → Truncate t K e
  tr↓ Y a {K} (ks , h) r KY = r , ks , λ {k} x lt _ → h x (≺-trans {k} {K} {Y} lt KY) tt

  -- A LANE ROW A LEVEL SHOWS: the lanes' row it shows, as few rows before
  -- it, and every earlier lane row past the reader shown too.
  Split : ∀ {V} → EmissionSet V → (IE B → V) → Pos → IE B → Set
  Split U g Y x = Σ Pos λ y → Y ≡ y ⊕ [ sub J ] × σ y (out x) × J ≺ y × Reach (Rejoin J σ) Y (out x)
                × (∀ {k x′} → σ k (out x′) → J ≺ k → (k ⊕ [ sub J ]) ≺ Y → U (k ⊕ [ sub J ]) (out (g x′)))

  s-tr : ∀ {V} {d d′ : Den V} {s g Y x} → d ≡ d′ → Split (enter d s) g Y x → Split (enter d′ s) g Y x
  s-tr refl sp = sp

  s-hot : ∀ {Y x} → enter (hot σ) J Y (out x) → Split (enter (hot σ) J) (λ x → x) Y x
  s-hot {x = x} (shown {q = y} r _ jy , rch) = y , refl , r , jy , rch , λ r′ jk KY → tr↓ (y ⊕ [ sub J ]) x rch (shown r′ tt jk) KY

  s-map : ∀ {Y x} → enter (Op.map Ln (hot σ)) J Y (out (Ln x)) → Split (enter (Op.map Ln (hot σ)) J) Ln Y x
  s-map {Y} {x} (map-out r , rch) with s-hot r
  ... | y , eq , ry , jy , rr , dn = y , eq , ry , jy , rr , λ r′ jk KY → tr↓ Y (Ln x) rch (map-out (dn r′ jk KY)) KY

  s-tag : ∀ {Y x} → enter (G laneB) J Y (out (Ln x)) → Split (enter (G laneB) J) Ln Y x
  s-tag {Y} {x} r = s-tr (sym eqG) (s-map (subst (λ d → enter d J Y (out (Ln x))) eqG r))

  -- The flatMap's own branches: the lanes' is the second.
  private module M4 = Merge G (enter (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) s₃)

  Own′ : EmissionSet (Maybe (Input B))
  Own′ = enter (Op.flatMap (mergeᶠ nothing) G (Op.of (outerB ∷ laneB ∷ closeB ∷ []))) s₃

  own-lane : ∀ b {q Y x} → b ≡ laneB → enter (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) s₃ q (out b)
           → enter (G b) (q ⊕ [ ix 1 ]) Y (out (Ln x)) → Reach M4.JoinT Y (out (Ln x)) → Split Own′ Ln Y x
  own-lane .laneB {Y = Y} {x} refl o@(on-out at-out , _) r rch with s-tag r
  ... | y , eq , ry , jy , rr , dn =
    y , eq , ry , jy , rr , λ r′ jk KY → tr↓ Y (Ln x) rch (M4.lane o tt (dn r′ jk KY , under-J jk) (λ ()) tt) KY
  own-lane .laneB refl (on-out (on-out (on-out ())) , _) _ _

  s-own : ∀ {Y x} → Own′ Y (out (Ln x)) → Split Own′ Ln Y x
  s-own (M4.lane {a = b} o _ (r , _) _ _ , rch) = own-lane b (noG r) o r rch
  s-own (M4.run () _ , _)

  -- The concat: the branches first.
  private module B3 = Bounded 1 C (enter (Op.of (true ∷ false ∷ [])) S₂)

  Cat′ : EmissionSet (Maybe (Input B))
  Cat′ = enter (Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ []))) S₂

  cat-first : ∀ {q i s Y x} → enter (Op.of (true ∷ false ∷ [])) S₂ q (out true) → B3.Indexed q → B3.Sub i q s true
            → enter (C true) s Y (out (Ln x)) → Reach B3.JoinT Y (out (Ln x)) → Split Cat′ Ln Y x
  cat-first {Y = Y} {x} o ixd sb r rch with Cat.first-sub C S₂ o sb
  ... | refl with s-tr (sym eqC) (s-own (subst (λ d → enter d s₃ Y (out (Ln x))) eqC r))
  ...   | y , eq , ry , jy , rr , dn =
    y , eq , ry , jy , rr , λ {k} r′ jk KY →
      tr↓ Y (Ln x) rch (B3.lane o ixd (_ , s₃ , sb , dn r′ jk KY , ≺-trans {s₃} {J} {k ⊕ [ sub J ]} s₃≺J (under-J jk)) (λ ()) tt) KY

  s-cat : ∀ {Y x} → Cat′ Y (out (Ln x)) → Split Cat′ Ln Y x
  s-cat (B3.lane {a = true} o ixd (_ , _ , sb , r , _) _ _ , rch) = cat-first o ixd sb r rch
  s-cat (B3.lane {a = false} _ _ (_ , _ , _ , r , _) _ _ , _)  = ⊥-elim (noC r)
  s-cat (B3.run () _ , _)

  -- The trackers and the flatMap's own: the second.
  private module M2 = Merge F (enter (Op.of (true ∷ false ∷ [])) P)

  Fed′ : EmissionSet (Maybe (Input B))
  Fed′ = enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P

  fed-own : ∀ {Y x} → enter (F false) S₂ Y (out (Ln x)) → Split (enter (F false) S₂) Ln Y x
  fed-own {Y} {x} r = s-tr (sym eqF) (s-cat (subst (λ d → enter d S₂ Y (out (Ln x))) eqF r))

  s-fed : ∀ {Y x} → Fed′ Y (out (Ln x)) → Split Fed′ Ln Y x
  s-fed (M2.lane {a = true} _ _ (r , _) _ _ , _) = ⊥-elim (noF r)
  s-fed {Y} {x} (M2.lane {a = false} o@(on-out at-out , _) _ (r , _) _ _ , rch) with fed-own r
  ... | y , eq , ry , jy , rr , dn =
    y , eq , ry , jy , rr , λ {k} r′ jk KY →
      tr↓ Y (Ln x) rch (M2.lane o tt (dn r′ jk KY , ≺-trans {S₂} {J} {k ⊕ [ sub J ]} S₂≺J (under-J jk)) (λ ()) tt) KY
  s-fed (M2.lane {a = false} (on-out (on-out ()) , _) _ _ _ _ , _)
  s-fed (M2.run () _ , _)

  private module TW = TakeWhile false going (enter (Op.flatMap (mergeᶠ nothing) F (Op.of (true ∷ false ∷ []))) P)

  split : ∀ {Y x} → M′ Y (out (Ln x)) → Split M′ Ln Y x
  split {Y} {x} (TW.pass r _ nf , rch) with s-fed r
  ... | y , eq , ry , jy , rr , dn =
    y , eq , ry , jy , rr , λ {k} r′ jk KY →
      tr↓ Y (Ln x) rch (TW.pass (dn r′ jk KY) tt (λ { (q , a , rq , na , qK) → nf (q , a , rq , na , ≺-trans {q} {k ⊕ [ sub J ]} qK KY) })) KY
  split (TW.fail _ _ _ () , _)

  ------------------------------------------------------------------------
  -- The run

  data LView : Ev (Maybe (Input B)) → Set where
    isLane  : ∀ x → LView (out (Ln x))
    notLane : ∀ {e} → laneTag e ≡ nothing → LView e

  lview : ∀ e → LView e
  lview (out (just (inj₁ (laneB , x))))  = isLane x
  lview (out (just (inj₁ (outerB , _)))) = notLane refl
  lview (out (just (inj₁ (closeB , _)))) = notLane refl
  lview (out (just (inj₂ _)))            = notLane refl
  lview (out nothing)                    = notLane refl
  lview skip                             = notLane refl
  lview (pin _)                          = notLane refl
  lview end                              = notLane refl

  lane-tagged : ∀ {x} → laneTag (out (Ln {B} x)) ≡ nothing → ⊥
  lane-tagged ()

  -- WHAT THE TWO READERS HAVE MET: every lane row past the lanes' cursor
  -- that the source shows lies past the source's cursor, and the source's
  -- cursor lies past the last lane row met.
  record Inv (cM cσ : Maybe Pos) : Set where
    field
      i1 : ∀ {k x} → σ k (out x) → After cσ k → M′ (k ⊕ [ sub J ]) (out (Ln x)) → After cM (k ⊕ [ sub J ])
      i2 : ∀ {y} → cσ ≡ just y → Σ (Ev (IE B)) (σ y) × (∀ {Z} → After cM Z → (y ⊕ [ sub J ]) ≺ Z)

  -- The lane row met next lies past the last one met.
  after-last : ∀ {cM y e} cσ → Inv cM cσ → σ y e → After cM (y ⊕ [ sub J ]) → After cσ y
  after-last nothing  _  _  _  = tt
  after-last (just y′) iv ry am with Inv.i2 iv refl
  ... | (_ , ry′) , f = lower Lσ ry ry′ (f am)

  -- Past a lane row met, both cursors there.
  iv-lane : ∀ {y e} → σ y e → Inv (just (y ⊕ [ sub J ])) (just y)
  Inv.i1 (iv-lane ry) rk yk _ = mono ry rk yk
  Inv.i2 (iv-lane ry) refl    = (_ , ry) , λ z → z

  -- Past another row met, only the source's cursor moves: no lane row it
  -- shows lies there, since one event lies at a row.
  iv-other : ∀ {cM cσ q e} → Inv cM cσ → M′ q e → Least M′ cM q → laneTag e ≡ nothing → Inv (just q) cσ
  Inv.i1 (iv-other {q = q} {e} iv mq lst nl) {k} {x} rk ak mK
    with ≼-split {q} {k ⊕ [ sub J ]} (proj₂ lst mK tt (Inv.i1 iv rk ak mK))
  ... | inj₁ lt = lt
  ... | inj₂ eq = ⊥-elim (lane-tagged (subst (λ z → laneTag z ≡ nothing) (funcM (subst (λ z → M′ z e) eq mq) mK) nl))
  Inv.i2 (iv-other {q = q} iv mq lst nl) {y} eq with Inv.i2 iv eq
  ... | r , f = r , λ {Z} qZ → ≺-trans {y ⊕ [ sub J ]} {q} {Z} (f (proj₁ lst)) qZ

  -- THE LANES' NEXT ROW, where the source's next row is a lane's: the
  -- lanes' row it shows, reached, and the first past the lanes' cursor.
  next-lane : ∀ {cM cσ q x} → Inv cM cσ → M′ q (out (Ln x)) → Least M′ cM q
            → Σ Pos λ y → q ≡ y ⊕ [ sub J ] × σ y (out x) × Seen σ y (out x) × Least σ cσ y
  next-lane {cσ = cσ} {x = x} iv mq lst with split mq
  ... | y , refl , ry , jy , rr , dn = y , refl , ry , seen , after-last cσ iv ry (proj₁ lst) , least
    where
      seen : Seen σ y (out x)
      seen = (ry , λ c → Lawful.proper Lσ c ry) , row-few Lσ pastJ ry (reach-few {q = y ⊕ [ sub J ]} {e = out x} (λ {k} {e′} → tt) rr)

      least : ∀ {k e′} → σ k e′ → Visible e′ → After cσ k → y ≼ k
      least {k} {out x′} rk _ ak ky = proj₂ lst mK tt (Inv.i1 iv rk ak mK) KY
        where
          KY = mono rk ry ky
          mK = dn rk (pastJ rk) KY
      least {e′ = end}   rk _ _ = Lawful.proper Lσ rk ry
      least {e′ = skip}  _ ()
      least {e′ = pin _} _ ()

  Lanes : Maybe Pos → Maybe Pos → List (Pos × Ev (Maybe (Input B))) → Set
  Lanes cM cσ rx = Σ _ λ rs → Proj laneTag rx rs × Run σ cσ rs × Inv (cursor cM rx) (cursor cσ rs)

  mutual
    go : ∀ {cM rx} cσ → Run M′ cM rx → Inv cM cσ → Lanes cM cσ rx
    go cσ Run.[] iv = [] , Proj.[] , Run.[] , iv
    go cσ (Run._∷_ {e = e} row rest) iv = step cσ (lview e) row rest iv

    step : ∀ {cM q e rx} cσ → LView e → Seen M′ q e × Visible e × Least M′ cM q → Run M′ (just q) rx → Inv cM cσ
         → Lanes cM cσ ((q , e) ∷ rx)
    step cσ (isLane x)   (sn , _ , lst) rest iv = lane-step cσ (proj₁ (proj₁ sn)) lst rest iv
    step cσ (notLane nl) (sn , _ , lst) rest iv with go cσ rest (iv-other iv (proj₁ (proj₁ sn)) lst nl)
    ... | rs , pr , run , iv′ = rs , drop nl pr , run , iv′

    lane-step : ∀ {cM q x rx} cσ → M′ q (out (Ln x)) → Least M′ cM q → Run M′ (just q) rx → Inv cM cσ
              → Lanes cM cσ ((q , out (Ln x)) ∷ rx)
    lane-step {x = x} cσ mq lst rest iv with next-lane iv mq lst
    ... | y , refl , ry , seen , least with go (just y) rest (iv-lane ry)
    ...   | rs , pr , run , iv′ = (y , out x) ∷ rs , keep refl refl pr , (seen , tt , least) Run.∷ run , iv′

  -- THE LANES' ROWS A RUN OF THE SOURCE MEETS ARE A RUN OF THE LANES.
  lane-run′ : ∀ {rx} → Run M′ nothing rx → Lanes nothing nothing rx
  lane-run′ r = go nothing r (record { i1 = λ _ _ _ → tt ; i2 = λ () })
