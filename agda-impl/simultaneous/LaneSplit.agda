{-# OPTIONS --guardedness #-}

-- THE LANES' ROWS THE SCAN'S SOURCE MEETS ARE A RUN OF THE LANES.  The
-- source reads the lanes through one reader, five operators deep, at a
-- subscription fixed by its own `of`s: so a lane row it shows carries,
-- level by level, as few rows before it as it has, and any earlier lane
-- row past that reader is shown too, at its own place below.  A lane row
-- the lanes would show before the one the source meets is then one the
-- source would have met first.
module simultaneous.LaneSplit where

open import Data.Bool using (Bool; true; false; T; not)
open import Data.Nat using (suc; s≤s; z≤n)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Effect.Monad using (RawMonad)
open import Level using () renaming (zero to lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-Monad)
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
open import denotation.Position using (Pos; Path; ix; sub; root; _≟ᵖ_; _⊕_; inside)
open import denotation.Events using (Timeline; fresh; <ᵖ-down)
open import denotation.EmissionSet using (Ev; out; skip; pin; end; EmissionSet; Den; hot; enter; Reach; Rejoin; shown; heard; ended; late;
  Truncate; Seen; Few; LaneOf; _≺_; _≼_; at-out; on-out; MapT; map-out; map-skip; map-pin; map-end; module Op; module TakeWhile; module Merge;
  module Bounded; module Values)
open import denotation.Read using (Run; Least; After; Visible; cursor)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≼-split; reach-few; ≺→≼; ≼-≺-≺; ≺-≼-≺; ≼-refl)
open import denotation.Laws.Worlds using (Lawful; ⊕-assoc; Shows; inside-⊑; ⊑-≼; hot-shows)
open import denotation.Laws.Worlds.Leaves using (of-in; of-rows; of-reach)
open import denotation.Laws.Shows using (Step; k-shows; shows-k)
open import denotation.Laws.ShowsOps using (sk-mapT)
open import denotation.Laws.Lift using (few-lift; few-below; step-≼)
open import denotation.Laws.Count using (em)
import denotation.Laws.Join as LJ
open import denotation.Laws.Rejoined using (lower; row-few; row-reach)
open import denotation.Up using (up; up-⊕)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
import Data.List as L
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

  ------------------------------------------------------------------------
  -- Shown

  -- An of's rows lie past its subscription.
  of-past : ∀ {X : Set} s (xs : List X) {k e} → enter (Op.of xs) s k e → s ≺ k
  of-past {X} s xs (r , _) = rows 0 xs (of-in s 0 xs r)
    where
      rows : ∀ i (ys : List X) {k} → k ∈ of-rows s i ys → s ≺ k
      rows i []       (here refl) = ≺-ext s []
      rows i (_ ∷ _)  (here refl) = ≺-ext s []
      rows i (_ ∷ ys) (there m)   = rows (suc i) ys m

  -- The flatMap's own branches' rows lie past their outer's subscription.
  own-past : ∀ {k e} → Own′ k e → s₃ ≺ k
  own-past (M4.val {q} o , _)                    = ≺-trans {s₃} {q} {q ⊕ [ ix 0 ]} (of-past s₃ _ o) (≺-ext q [])
  own-past (M4.step o , _)                       = of-past s₃ _ o
  own-past (M4.opin o , _)                       = of-past s₃ _ o
  own-past (M4.oend o _ , _)                     = of-past s₃ _ o
  own-past (M4.opass o _ , _)                    = of-past s₃ _ o
  own-past (M4.lane {q} {k = k} o _ (_ , lt) _ _ , _) = ≺-trans {s₃} {q} {k} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt)
  own-past (M4.lend {q} {c = c} o _ (_ , lt) _ _ _ , _) = ≺-trans {s₃} {q} {c} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {c} (≺-ext q []) lt)
  own-past (M4.lpass {q} {c = c} o _ (_ , lt) _ _ _ , _) = ≺-trans {s₃} {q} {c} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {c} (≺-ext q []) lt)
  own-past (M4.hand {q} {c = c} o _ (_ , lt) _ () , _)
  own-past (M4.left {q} {k = k} o _ (_ , lt) _ _ , _) = ≺-trans {s₃} {q} {k} (of-past s₃ _ o) (≺-trans {q} {q ⊕ [ ix 1 ]} {k} (≺-ext q []) lt)
  own-past (M4.run () _ , _)
  own-past (M4.rend () _ _ , _)
  own-past (M4.rpass () _ _ , _)
  own-past (M4.rhand () _ , _)

  -- The concat's rows lie past its outer's subscription.
  cat-past : ∀ {k e} → Cat′ k e → S₂ ≺ k
  cat-past (B3.val {q} o , _)  = ≺-trans {S₂} {q} {q ⊕ [ ix 0 ]} (of-past S₂ _ o) (≺-ext q [])
  cat-past (B3.step o , _)     = of-past S₂ _ o
  cat-past (B3.opin o , _)     = of-past S₂ _ o
  cat-past (B3.oend o _ , _)   = of-past S₂ _ o
  cat-past (B3.opass o _ , _)  = of-past S₂ _ o
  cat-past (B3.lane {q} {k = k} o _ (_ , s , (_ , st) , (_ , sk)) _ _ , _) =
    ≺-trans {S₂} {q} {k} (of-past S₂ _ o) (≺-trans {q} {s} {k} (LJ.Join.BoundedJ.starts-past P 1 st) sk)
  cat-past (B3.lend {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ _ , _) =
    ≺-trans {S₂} {q} {c} (of-past S₂ _ o) (≺-trans {q} {s} {c} (LJ.Join.BoundedJ.starts-past P 1 st) sc)
  cat-past (B3.lpass {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ _ , _) =
    ≺-trans {S₂} {q} {c} (of-past S₂ _ o) (≺-trans {q} {s} {c} (LJ.Join.BoundedJ.starts-past P 1 st) sc)
  cat-past (B3.hand {q} {c = c} o _ (_ , s , (_ , st) , (_ , sc)) _ _ , _) =
    ≺-trans {S₂} {q} {c ⊕ [ ix 0 ]} (of-past S₂ _ o) (≺-trans {q} {s} {c ⊕ [ ix 0 ]} (LJ.Join.BoundedJ.starts-past P 1 st) (≺-trans {s} {c} {c ⊕ [ ix 0 ]} sc (≺-ext c [])))
  cat-past (B3.left {q} {k = k} o _ (_ , s , (_ , st) , (_ , sk)) _ _ , _) =
    ≺-trans {S₂} {q} {k} (of-past S₂ _ o) (≺-trans {q} {s} {k} (LJ.Join.BoundedJ.starts-past P 1 st) sk)
  cat-past (B3.run () _ , _)
  cat-past (B3.rend () _ _ , _)
  cat-past (B3.rpass () _ _ , _)
  cat-past (B3.rhand () _ , _)

  -- A joiner's row for a lane's: the same, or its end hushed.
  data Same {X : Set} : Ev X → Ev X → Set where
    same : ∀ {e} → Same e e
    hush : Same end skip

  same-out : ∀ {X} {e e′ : Ev X} {v} → Same e e′ → e ≡ out v → e′ ≡ out v
  same-out same eq = eq
  same-out hush ()

  -- The concat's, or its end handed to the next lane one step down.
  data Moved {X : Set} (k : Pos) (e : Ev X) : Pos → Ev X → Set where
    kept   : ∀ {e′} → Same e e′ → Moved k e k e′
    handed : e ≡ end → Moved k e (k ⊕ [ ix 0 ]) skip

  moved-step : ∀ {X k z} {e e′ : Ev X} → Moved k e z e′ → Step k z
  moved-step (kept _)   = inj₁ refl
  moved-step (handed _) = inj₂ refl

  -- The shapes a lane's row takes past the lanes' reader.
  data K : Ev (Maybe (Input B)) → Set where
    kout  : ∀ x → K (out (Ln x))
    kskip : K skip
    kend  : K end

  same-K : ∀ {e e′} → Same e e′ → K e → K e′
  same-K same k = k
  same-K hush _ = kskip

  T0 : EmissionSet (IE B)
  T0 = enter (hot σ) J

  T1 : EmissionSet (Maybe (Input B))
  T1 = enter (Op.map Ln (hot σ)) J

  rj-past : ∀ {k e} → Rejoin J σ k e → J ≺ k
  rj-past (shown _ _ jq) = under-J jq
  rj-past (heard _ jq)   = under-J jq
  rj-past (ended _ jc)   = under-J jc
  rj-past (late _ _)     = ≺-ext J []

  t1-past : ∀ {k e} → T1 k e → J ≺ k
  t1-past (map-out (r , _) , _)  = rj-past r
  t1-past (map-skip (r , _) , _) = rj-past r
  t1-past (map-pin (r , _) , _)  = rj-past r
  t1-past (map-end (r , _) , _)  = rj-past r

  -- A lanes' row at the lanes' reader, lifted one level.
  rj : ∀ {y e} → σ y e → Σ (Ev (IE B)) λ e₀ → Rejoin J σ (y ⊕ [ sub J ]) e₀ × Σ _ λ e₁ → (∀ {Z} → T0 Z e₀ → MapT Ln T0 Z e₁)
     × K e₁ × (∀ {x} → e ≡ out x → e₁ ≡ out (Ln x))
  rj {e = out x} r = out x , shown r tt (pastJ r) , _ , map-out , kout x , λ { refl → refl }
  rj {e = skip}  r = skip , shown r tt (pastJ r) , _ , map-skip , kskip , λ ()
  rj {e = pin _} r = skip , heard r (pastJ r) , _ , map-skip , kskip , λ ()
  rj {e = end}   r = end , ended r (pastJ r) , _ , map-end , kend , λ ()

  o₃ : enter (Op.of (outerB ∷ laneB ∷ closeB ∷ [])) s₃ q₃ (out laneB)
  o₃ = on-out at-out , of-reach s₃ 0 (outerB ∷ laneB ∷ closeB ∷ []) {q₃} {out laneB}

  o₂ : enter (Op.of (true ∷ false ∷ [])) S₂ q₂ (out true)
  o₂ = at-out , of-reach S₂ 0 (true ∷ false ∷ []) {q₂} {out true}

  o₁ : enter (Op.of (true ∷ false ∷ [])) P q₁ (out false)
  o₁ = on-out at-out , of-reach P 0 (true ∷ false ∷ []) {q₁} {out false}

  ixd : B3.Indexed q₂
  ixd = 0 , true , Values.first o₂ (λ {k} {b} x → Cat.min0 C S₂ {k} {b} x)

  sb₀ : B3.Sub 0 q₂ s₃ true
  sb₀ = proj₂ (proj₂ ixd) , B3.room (s≤s z≤n)

  m4-lane : ∀ {k e} → T1 k e → LaneOf G q₃ laneB k e
  m4-lane {k} {e} t = subst (λ d → enter d J k e) (sym eqG) t , t1-past t

  b3-lane : ∀ {k e} → Own′ k e → B3.Lane q₂ true k e
  b3-lane {k} {e} r = 0 , s₃ , sb₀ , subst (λ d → enter d s₃ k e) (sym eqC) r , own-past r

  m2-lane : ∀ {k e} → Cat′ k e → LaneOf F q₁ false k e
  m2-lane {k} {e} r = subst (λ d → enter d S₂ k e) (sym eqF) r , cat-past r

  m4-row : ∀ {k e} → T1 k e → ¬ ¬ Σ _ λ e′ → M4.JoinT k e′ × Same e e′
  m4-row {e = out _} t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
  m4-row {e = skip}  t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
  m4-row {e = pin _} t ¬j = ¬j (_ , M4.lane o₃ tt (m4-lane t) (λ ()) tt , same)
  m4-row {k} {end}   t    =
    em {P = M4.Done k} (λ d ¬j → ¬j (_ , M4.lend o₃ tt (m4-lane t) (λ ()) (λ ()) d , same))
                       (λ nd ¬j → ¬j (_ , M4.lpass o₃ tt (m4-lane t) (λ ()) (λ ()) nd , hush))

  b3-row : ∀ {k e} → Own′ k e → ¬ ¬ Σ Pos λ z → Σ _ λ e′ → B3.JoinT z e′ × Moved k e z e′
  b3-row {e = out _} r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
  b3-row {e = skip}  r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
  b3-row {e = pin _} r ¬j = ¬j (_ , _ , B3.lane o₂ ixd (b3-lane r) (λ ()) tt , kept same)
  b3-row {k} {end}   r    =
    em {P = B3.Queued k} (λ h ¬j → ¬j (_ , _ , B3.hand o₂ ixd (b3-lane r) (λ ()) h , handed refl)) λ nh →
    em {P = B3.Done k} (λ d ¬j → ¬j (_ , _ , B3.lend o₂ ixd (b3-lane r) (λ ()) nh d , kept same))
                       (λ nd ¬j → ¬j (_ , _ , B3.lpass o₂ ixd (b3-lane r) (λ ()) nh nd , kept hush))

  m2-row : ∀ {k e} → Cat′ k e → ¬ ¬ Σ _ λ e′ → M2.JoinT k e′ × Same e e′
  m2-row {e = out _} r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
  m2-row {e = skip}  r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
  m2-row {e = pin _} r ¬j = ¬j (_ , M2.lane o₁ tt (m2-lane r) (λ ()) tt , same)
  m2-row {k} {end}   r    =
    em {P = M2.Done k} (λ d ¬j → ¬j (_ , M2.lend o₁ tt (m2-lane r) (λ ()) (λ ()) d , same))
                       (λ nd ¬j → ¬j (_ , M2.lpass o₁ tt (m2-lane r) (λ ()) (λ ()) nd , hush))

  -- THE LANES' ROWS BEFORE A SOURCE VALUE ARE SHOWN.  Each level the
  -- source's reader passes through shows its hangs, and the source has
  -- few rows before its value: so each level has few there, top down, and
  -- a lanes' row lifts bottom up, the concat handing a lane's end on one
  -- step down.  A hand-off that would pass the value is the value itself.
  module Shown (shσ : Shows σ) (shM4 : Shows M4.JoinT) (shB3 : Shows B3.JoinT) (shM2 : Shows M2.JoinT)
               (shTW : Shows TW.TakeT) (pinF : ∀ {k r} → Fed′ k (pin r) → T (inside r k)) {q a} (mq : M′ q (out a)) where
    open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)

    shU1 : Shows (MapT Ln T0)
    shU1 = k-shows λ n → sk-mapT Ln (shows-k {n = n} (hot-shows σ J))

    nfq : ¬ TW.Failed q
    nfq = nf-of mq
      where
        nf-of : ∀ {q a} → M′ q (out a) → ¬ TW.Failed q
        nf-of (TW.pass _ _ nf , _)   = nf
        nf-of (TW.fail _ _ _ () , _)

    nf-mono : ∀ {r k} → r ≼ k → ¬ TW.Failed k → ¬ TW.Failed r
    nf-mono {r} {k} rk nk (w , b , x , nb , wr) = nk (w , b , x , nb , ≺-≼-≺ {w} {r} {k} wr rk)

    f5 : Few M′ q
    f5 = proj₁ (proj₂ mq) , λ x lt → proj₂ (proj₂ mq) (proj₁ x) lt tt

    st5 : ∀ {k e} → Fed′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (TW.TakeT z) × Step k z
    st5 {k} {out b} r kq with going b in g
    ... | true  = pure (k , (_ , TW.pass r (Equivalence.from T-≡ g) (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
    ... | false = ⊥-elim (nfq (k , b , r , subst (λ x → T (not x)) (sym g) tt , kq))
    st5 {k} {skip}  r kq = pure (k , (_ , TW.step r (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
    st5 {k} {end}   r kq = pure (k , (_ , TW.tend r (nf-mono (≺→≼ {k} {q} kq) nfq)) , inj₁ refl)
    st5 {k} {pin s} r kq =
      pure (k , (_ , TW.left r (nf-mono {s} {q} (≺→≼ {s} {q} (≼-≺-≺ {s} {k} {q} (⊑-≼ {s} {k} (inside-⊑ s k (pinF r))) kq)) nfq) (pinF r)) , inj₁ refl)

    f4 : Few Fed′ q
    f4 = few-below shTW f5 st5

    st4 : ∀ {k e} → Cat′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (M2.JoinT z) × Step k z
    st4 {k} r _ = m2-row r >>= λ (e′ , u , _) → pure (k , (e′ , u) , inj₁ refl)

    f3 : Few Cat′ q
    f3 = few-below shM2 f4 st4

    st3 : ∀ {k e} → Own′ k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (B3.JoinT z) × Step k z
    st3 r _ = b3-row r >>= λ (z , e′ , u , mv) → pure (z , (e′ , u) , moved-step mv)

    f2 : Few Own′ q
    f2 = few-below shB3 f3 st3

    st2 : ∀ {k e} → T1 k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (M4.JoinT z) × Step k z
    st2 {k} t _ = m4-row t >>= λ (e′ , u , _) → pure (k , (e′ , u) , inj₁ refl)

    f1 : Few T1 q
    f1 = few-below shM4 f2 st2

    st1 : ∀ {k e} → T0 k e → k ≺ q → ¬ ¬ Σ Pos λ z → Σ _ (MapT Ln T0 z) × Step k z
    st1 {k} {out _} t _ = pure (k , (_ , map-out t) , inj₁ refl)
    st1 {k} {skip}  t _ = pure (k , (_ , map-skip t) , inj₁ refl)
    st1 {k} {pin _} t _ = pure (k , (_ , map-pin t) , inj₁ refl)
    st1 {k} {end}   t _ = pure (k , (_ , map-end t) , inj₁ refl)

    f0 : Few T0 q
    f0 = few-below shU1 f1 st1

    tw-lift : ∀ {z e} → K e → Fed′ z e → z ≼ q → TW.TakeT z e
    tw-lift (kout x) r zq = TW.pass r tt (nf-mono zq nfq)
    tw-lift kskip    r zq = TW.step r (nf-mono zq nfq)
    tw-lift kend     r zq = TW.tend r (nf-mono zq nfq)

    -- Past the concat: the source's row there.
    past-cat : ∀ {z e} → K e → Cat′ z e → z ≼ q → ¬ ¬ Σ _ λ e′ → M′ z e′ × Same e e′
    past-cat k t3 zq =
      m2-row t3 >>= λ (e′ , u4 , s) →
      few-lift shM2 f4 u4 zq >>= λ t4 →
      few-lift shTW f5 (tw-lift (same-K s k) t4 zq) zq >>= λ t5 →
      pure (e′ , t5 , s)

    Lifted : Pos → Ev (Maybe (Input B)) → Set
    Lifted Y e = Σ Pos λ z → Σ _ λ e″ → M′ z e″ × Step Y z × z ≼ q × (∀ {v} → e ≡ out v → z ≡ Y × e″ ≡ out v)

    handed-on : ∀ {Y e z e′} → K e → Moved Y e z e′ → B3.JoinT z e′ → Y ≼ q → ¬ ¬ Lifted Y e
    handed-on k (kept s) u3 Yq =
      few-lift shB3 f3 u3 Yq >>= λ t3 →
      past-cat (same-K s k) t3 Yq >>= λ (e″ , t5 , s′) →
      pure (_ , e″ , t5 , inj₁ refl , Yq , λ {_} eq → refl , same-out s′ (same-out s eq))
    handed-on {Y} k (handed refl) u3 Yq with ≼-split {Y} {q} Yq
    ... | inj₁ lt =
      few-lift shB3 f3 u3 zq >>= λ t3 →
      past-cat kskip t3 zq >>= λ (e″ , t5 , _) →
      pure (_ , e″ , t5 , inj₂ refl , zq , λ {_} ())
      where
        zq : (Y ⊕ [ ix 0 ]) ≼ q
        zq = step-≼ {Y} {Y ⊕ [ ix 0 ]} {q} (inj₂ refl) lt
    ... | inj₂ eq = pure (q , out a , mq , inj₁ (sym eq) , ≼-refl {q} , λ {_} ())

    lifted : ∀ {Y e} → K e → T1 Y e → Y ≼ q → ¬ ¬ Lifted Y e
    lifted k t1 Yq =
      m4-row t1 >>= λ (e₂ , u2 , s) →
      few-lift shM4 f2 u2 Yq >>= λ t2 →
      b3-row t2 >>= λ (z , e₃ , u3 , mv) →
      handed-on (same-K s k) mv u3 Yq >>= λ (z′ , e″ , t5 , st , zq , pr) →
      pure (z′ , e″ , t5 , st , zq , λ {_} eq → pr (same-out s eq))

    -- The lanes' row, as their reader shows it: the lanes' rows before it
    -- are few, each shown at or before it.
    t0-of : ∀ {y e e₀} → σ y e → Rejoin J σ (y ⊕ [ sub J ]) e₀ → (y ⊕ [ sub J ]) ≼ q → ¬ ¬ T0 (y ⊕ [ sub J ]) e₀
    t0-of {y} ry r0 Yq = shσ {v = y} (L.map up (proj₁ f0) , pick) >>= λ fy → pure (r0 , row-reach Lσ ry fy (pastJ ry))
      where
        pick : ∀ {k e} → σ k e → Few σ k → k ≺ y → k ∈ L.map up (proj₁ f0)
        pick {k} rk fk ky with rj rk
        ... | _ , rk′ , _ = subst (_∈ L.map up (proj₁ f0)) (up-⊕ k (sub J))
          (∈-map⁺ up (proj₂ f0 (rk′ , row-reach Lσ rk fk (pastJ rk)) (≺-≼-≺ {k ⊕ [ sub J ]} {y ⊕ [ sub J ]} {q} (mono rk ry ky) Yq)))

    -- A LANES' ROW AT OR BEFORE THE SOURCE'S VALUE, as the source shows it.
    shown′ : ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
           → ¬ ¬ Σ Pos λ z → Σ _ λ e″ → M′ z e″ × Step (y ⊕ [ sub J ]) z × z ≼ q × (∀ {x} → e ≡ out x → z ≡ y ⊕ [ sub J ] × e″ ≡ out (Ln x))
    shown′ ry Yq with rj ry
    ... | _ , r0 , _ , mp , k1 , o1 =
      t0-of ry r0 Yq >>= λ t0 →
      few-lift shU1 f1 (mp t0) Yq >>= λ t1 →
      lifted k1 t1 Yq >>= λ (z , e″ , t5 , st , zq , pr) →
      pure (z , e″ , t5 , st , zq , λ {_} eq → pr (o1 eq))
