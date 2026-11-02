{-# OPTIONS --guardedness #-}

-- A NODE ENTERED, ITS PARTS PLACED.  A subscription at `q` keeps the
-- invariant there, so its rows lie in its world and none lies in the
-- world of another's child (`under`): a region holding the world, but for
-- what its rows subscribe below them, holds every visible row.
--
-- A joiner's rows are its outer's, or lie in the world of an outer row's
-- child, so what excludes the outer's children excludes the joiner's.  A
-- lane starts in such a child's world, so the outer's region, the world
-- less every lane's, still holds the outer.
--
-- A connect's body and source subscribe at sibling children.  A body row's
-- child's world lies in the body's world, which leads no source position;
-- a source row's first child's world leads a body position only through a
-- joined source row, which would lie under that child.  So each part's
-- region excludes the other's rows.
module adequacy.Enter where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (_∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect)
open import denotation.Events using (Pos; Label; Timeline; ix; root)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; _≼_; Den; hot; ⟦_⟧; Proper; LaneOf; Ended; module Joining;
  module Bounded; module Switch; module Exhaust; module Connecting)
open import denotation.Laws.Modulus using (≼-or-≻; ≼-≺-≺; ≺-irrefl)
open import denotation.Laws.Worlds using (W; W⁼; step; here; inW; Plain; plain-ix; Real; Ok; Lawful; InvAt; InvD; Hots; _⊑_;
  ⊑-refl; ⊑-≼; ⊑-inside; nest⁼; nest-in; narrow⁼; widen⁼; world-after; real-init; nonempty⁼; ok-step)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws.JoinInv using (module Join)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Nth using (module Nths)
import denotation.Laws.Connect as LC
open import operation.PureObservable using (module Machine)
open Machine using (Scope; binds; CS; cs)
open import adequacy.Rows using (full; pendRows)
open import adequacy.Cursor using (Rgn; Sound; Excl; Within; Parts; JRo; LaneRg; Start; polF; Adm)
open import adequacy.Bound using (good-full)

------------------------------------------------------------------------
-- Excluded worlds

-- No world position leads its subscription.
w-unled : ∀ {H p w} → Real p → W H p w → w ⊑ p → ⊥
w-unled {w = w} rp ww (zs , refl) with real-init w zs rp
... | inj₁ refl = nonempty⁼ (λ { refl → rp }) (inW ww)
... | inj₂ rw   = ≺-irrefl {w} (≼-≺-≺ {w} {w ++ zs} {w} (⊑-≼ {w} {w ++ zs} (zs , refl)) (world-after ww rw))

-- A subscription lies outside what its rows subscribe below them.
excl-root : ∀ {A H p} {E : EmissionSet A} → InvAt H p E → Real p → Excl H E p
excl-root I rp x pl v le = w-unled rp (nest-in (step (inW (InvAt.world I x)) pl) v) le

-- In the world of a row's plain child.
Kid : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
Kid {A} H E y = Σ Pos λ r → Σ (Ev A) λ e → Σ Label λ l → E r e × Plain l × W⁼ H (r ++ [ l ]) y

kid-in : ∀ {A H} {E : EmissionSet A} {s y} → Kid H E s → W H s y → Kid H E y
kid-in (r , e , l , x , pl , w) wy = r , e , l , x , pl , nest⁼ w (inW wy)

kid-lead : ∀ {A H} {E : EmissionSet A} {s y} → Kid H E s → W⁼ H s y → Excl H E y → ⊥
kid-lead (r , e , l , x , pl , w) ws ex = ex x pl (nest⁼ w ws) (⊑-refl _)

-- A row of `E`, or in the world of one's plain child.
Anchor : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
Anchor {A} H E y = Σ (Ev A) (E y) ⊎ Kid H E y

-- What excludes `E`'s children excludes those of rows anchored in `E`.
excl-anchor : ∀ {A A′ H y} {E : EmissionSet A} {E′ : EmissionSet A′} → (∀ {k e} → E′ k e → Anchor H E k) → Excl H E y → Excl H E′ y
excl-anchor an ex x pl v le with an x
... | inj₁ (_ , x₀)                    = ex x₀ pl v le
... | inj₂ (r , e , l₀ , x₀ , pl₀ , w₀) = ex x₀ pl₀ (inW (nest-in (step w₀ pl) v)) le

------------------------------------------------------------------------
-- A region holding the world, but for what its rows subscribe below
-- them, holds every visible row.

within-sound : ∀ {Γ A} {sc : Scope Γ} {Rg : Rgn} {q} {E : EmissionSet A} → InvAt (Hots (full sc)) q E → Within Rg sc q E → Sound Rg E
within-sound {E = E} I (_ , wi) = record
  { fn   = λ x x′ _ _ → InvAt.func I x x′
  ; ends = ends
  ; past = InvAt.quiet I
  ; rg   = λ x _ → wi (InvAt.world I x) (λ x′ pl w le → InvAt.under I x′ x pl w le)
  }
  where
    ends : ∀ {c y e} → E c end → E y e → Visible e → y ≼ c
    ends {c} {y} xc xy v with ≼-or-≻ y c
    ... | inj₁ le = le
    ... | inj₂ lt with InvAt.quiet I xc xy lt
    ...   | _ , refl , _ = ⊥-elim v

------------------------------------------------------------------------
-- A joiner entered

-- A joiner's rows, anchored in its outer's, given each lane's.
module JoinAnchor {A B : Set} {H : Pos → Set} {O : EmissionSet A} (L : Pos → A → EmissionSet B) (Over Runs : Pos → Set)
                  (Cut : Pos → Pos → Set) (Hand : Pos → Set) (lk : ∀ {q a k e} → O q (out a) → L q a k e → Kid H O k) where
  open Joining L O (λ _ _ → ⊥) Over Runs Cut Hand using (JoinT; val; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)
    renaming (step to o-step)

  j-anchor : ∀ {k e} → JoinT k e → Anchor H O k
  j-anchor (val {q} {a} x)        = inj₂ (q , out a , ix 0 , x , plain-ix , here)
  j-anchor (o-step x)             = inj₁ (_ , x)
  j-anchor (opin x)               = inj₁ (_ , x)
  j-anchor (oend x _)             = inj₁ (_ , x)
  j-anchor (opass x _)            = inj₁ (_ , x)
  j-anchor (lane x _ l _ _)       = inj₂ (lk x l)
  j-anchor (lend x _ l _ _ _)     = inj₂ (lk x l)
  j-anchor (lpass x _ l _ _ _)    = inj₂ (lk x l)
  j-anchor (hand x _ l _ _) with lk x l
  ... | r , e , l′ , xr , pl , w  = inj₂ (r , e , l′ , xr , pl , inW (step w plain-ix))
  j-anchor (left x _ l _ _)       = inj₂ (lk x l)
  j-anchor (run () _)
  j-anchor (rend () _ _)
  j-anchor (rpass () _ _)
  j-anchor (rhand () _)

-- A joiner of `f` over `s`, entered at `q`.
module FlatAt {Γ A B} (sc : Scope Γ) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) (q : Pos)
              (ok : Ok (Hots (full sc)) q) (ad : Adm sc) where
  H : Pos → Set
  H = Hots (full sc)

  f′ : A → Den B
  f′ a = ⟦ f a ⟧ (full sc)

  fi : ∀ a → InvD H (f′ a)
  fi a = inv-⟦⟧ (f a) (full sc) (good-full sc ad)

  O : EmissionSet A
  O = pendRows (full sc) s q

  Io : InvAt H q O
  Io = inv-⟦⟧ s (full sc) (good-full sc ad) q ok

  -- A lane at a value's second child.
  plain-lk : ∀ {q′ a k e} → O q′ (out a) → LaneOf f′ q′ a k e → Kid H O k
  plain-lk {q′} {a} x l = q′ , out a , ix 1 , x , plain-ix , inW (Join.lw ok f′ fi Io x l)

  -- A bounded lane in the world of an earlier value's second child.
  module Bd (m : ℕ) where
    open BoundedI ok m f′ fi Io using (Seat; seat′; seat*; row-w)
    open Nths O using (nth-val)

    seat-kid : ∀ {i s′} → Seat i s′ → Kid H O s′
    seat-kid (seat′ {r = r} {b} _ _ _ nr rw) = r , out b , ix 1 , nth-val nr , plain-ix , rw

    lk : ∀ {q′ a k e} → O q′ (out a) → Bounded.Lane m f′ O q′ a k e → Kid H O k
    lk _ (_ , _ , sb , ac) = kid-in (seat-kid (seat* sb)) (row-w sb ac)

    start : ∀ {q′ a s′} → Σ ℕ (λ i → Bounded.Sub m f′ O i q′ s′ a) → Kid H O s′
    start (_ , sb) = seat-kid (seat* sb)

  anchor : ∀ op {k e} → pendRows (full sc) (flatMap op f s) q k e → Anchor H O k
  anchor (mergeᶠ nothing)  x = JoinAnchor.j-anchor (LaneOf f′) (Ended O) (λ _ → ⊤) (λ _ _ → ⊥) (λ _ → ⊥) plain-lk (proj₁ x)
  anchor (mergeᶠ (just m)) x =
    JoinAnchor.j-anchor (Bounded.Lane m f′ O) (Ended O) (Bounded.Indexed m f′ O) (λ _ _ → ⊥) (Bounded.Queued m f′ O) (Bd.lk m) (proj₁ x)
  anchor switchᶠ           x = JoinAnchor.j-anchor (LaneOf f′) (Ended O) (λ _ → ⊤) (Switch.Cut f′ O) (λ _ → ⊥) plain-lk (proj₁ x)
  anchor exhaustᶠ          x = JoinAnchor.j-anchor (LaneOf f′) (Ended O) (Exhaust.Run f′ O) (λ _ _ → ⊥) (λ _ → ⊥) plain-lk (proj₁ x)

  -- A lane starts in the world of a value's child.
  start-kid : ∀ op {q′ a s′} → O q′ (out a) → Start (polF op f′ O) q′ a s′ → Kid H O s′
  start-kid (mergeᶠ nothing)  {q′} {a} x refl = q′ , out a , ix 1 , x , plain-ix , here
  start-kid (mergeᶠ (just m))          _ st   = Bd.start m st
  start-kid switchᶠ           {q′} {a} x refl = q′ , out a , ix 1 , x , plain-ix , here
  start-kid exhaustᶠ          {q′} {a} x refl = q′ , out a , ix 1 , x , plain-ix , here

  -- No lane's region holds what excludes the outer's children.
  no-lane : ∀ op {q′ y} → LaneRg H (polF op f′ O) O q′ y → Excl H O y → ⊥
  no-lane op (_ , _ , _ , x , st , ws , _) ex = kid-lead (start-kid op x st) ws ex

-- A JOINER'S OUTER, ENTERED, lies in the joiner's region less its lanes'.
flat-within : ∀ {Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
            → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q (pendRows (full sc) (flatMap op f s) q)
            → Within (JRo sc Rg op f (pendRows (full sc) s q)) sc q (pendRows (full sc) s q)
flat-within {sc = sc} {op = op} {f} {s} {q} ok ad (rq , wi) =
  (rq , λ lr → no-lane op lr (excl-root Io (proj₁ ok))) , λ wy ex → wi wy (excl-anchor {E′ = pendRows (full sc) (flatMap op f s) q} (anchor op) ex) , λ lr → no-lane op lr ex
  where open FlatAt sc f s q ok ad

flat-sound : ∀ {Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
           → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q (pendRows (full sc) (flatMap op f s) q)
           → Sound (JRo sc Rg op f (pendRows (full sc) s q)) (pendRows (full sc) s q)
flat-sound {sc = sc} {op = op} {f} {s} {q} ok ad wi = within-sound {sc = sc} (FlatAt.Io sc f s q ok ad) (flat-within {sc = sc} {op = op} {f = f} {s = s} {q = q} ok ad wi)

------------------------------------------------------------------------
-- A connect entered

-- A connect as entered at `q`: its source live, not yet subscribed.
conn₀ : ∀ {Γ X} → Obs Timeline Γ X → Pos → Scope Γ → CS Γ X
conn₀ s q sc = cs false true false (just q) nothing nothing q root s sc

module ConnAt {Γ X B} (sc : Scope Γ) (s : Obs Timeline Γ X) (b : Obs Timeline (X ∷ Γ) B) (q : Pos)
              (ok : Ok (Hots (full sc)) q) (ad : Adm sc) where
  H : Pos → Set
  H = Hots (full sc)

  Fb : Den X → Den B
  Fb h = ⟦ b ⟧ (h ∷ full sc)

  Is : InvD H (⟦ s ⟧ (full sc))
  Is = inv-⟦⟧ s (full sc) (good-full sc ad)

  IF : ∀ {t} → Lawful t → InvD (Hots (hot t ∷ full sc)) (Fb (hot t))
  IF {t} L = inv-⟦⟧ b (hot t ∷ full sc) (good-cons L (good-full sc ad))

  σ : EmissionSet X
  σ = pendRows (full sc) s (q ++ [ ix 1 ])

  β : EmissionSet B
  β = pendRows (full (binds s q sc)) b (q ++ [ ix 0 ])

  H₀ : Pos → Set
  H₀ = Hots (full (binds s q sc))

  ok₀ : Ok H₀ (q ++ [ ix 0 ])
  ok₀ = LC.ok₀ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  Iβ : InvAt H₀ (q ++ [ ix 0 ]) β
  Iβ = LC.Iβ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  Iσ : InvAt H (q ++ [ ix 1 ]) σ
  Iσ = LC.Iσ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  σw : ∀ {h e} → Proper σ h e → W H q h
  σw = LC.σ-wp {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  bl : ∀ {w x} → W⁼ H₀ (q ++ [ ix 0 ]) w → W⁼ H (q ++ [ ix 1 ]) x → w ⊑ x → ⊥
  bl = LC.body-leads {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  -- The connect's rows.
  E : EmissionSet B
  E = pendRows (full sc) (connect s b) q

  Rb Rs : Rgn
  Rb y = W⁼ H₀ (q ++ [ ix 0 ]) y × Excl H₀ β y
  Rs y = W⁼ H (q ++ [ ix 1 ]) y × Excl H σ y

  open Connecting using (body; burst; echo; kept)

  -- A source row's first child's world leads no body position.
  src-kid : ∀ {k e l v y} → σ k e → Plain l → W⁼ H ((k ++ [ ix 0 ]) ++ [ l ]) v → v ⊑ y → W⁼ H₀ (q ++ [ ix 0 ]) y → ⊥
  src-kid x pl v le wy
    with LC.source-leads {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok
           (inW (nest-in (step (inW (step (inW (InvAt.world Iσ x)) plain-ix)) pl) v)) wy le
  ... | _ , _ , (_ , σh) , vh , _ = InvAt.under Iσ x (proj₁ σh) plain-ix (nest⁼ (inW (step here pl)) v) vh

  -- Inside the body's region, outside the connect's rows' children.
  b-excl : ∀ {y} → Rb y → Excl H E y
  b-excl (_ , ex) (body x , _)          pl v le = ex x pl (widen⁼ (Proper σ) v) le
  b-excl (w , _)  (burst x _ , _)       pl v le = src-kid x pl v le w
  b-excl (w , _)  (echo x _ _ _ , _)    pl v le = src-kid x pl v le w
  b-excl (w , _)  (kept x _ _ _ , _)    pl v le = src-kid x pl v le w

  -- Inside the source's region, outside the connect's rows' children.
  s-excl : ∀ {y} → Rs y → Excl H E y
  s-excl (w , _)  (body x , _)          pl v le =
    bl (inW (nest-in (step (inW (InvAt.world Iβ x)) pl) (widen⁼ (Proper σ) v))) w le
  s-excl (_ , ex) (burst x _ , _)       pl v le = ex x plain-ix (nest⁼ (inW (step here pl)) v) le
  s-excl (_ , ex) (echo x _ _ _ , _)    pl v le = ex x plain-ix (nest⁼ (inW (step here pl)) v) le
  s-excl (_ , ex) (kept x _ _ _ , _)    pl v le = ex x plain-ix (nest⁼ (inW (step here pl)) v) le

  wb : Within Rb (binds s q sc) (q ++ [ ix 0 ]) β
  wb = (here , excl-root Iβ (proj₁ ok₀)) , λ w ex → inW w , ex

  ws : Within Rs sc (q ++ [ ix 1 ]) σ
  ws = (here , excl-root Iσ (proj₁ (ok-step q ok))) , λ w ex → inW w , ex

-- A CONNECT ENTERED: its body and source in regions apart and clear of
-- the scope's hots, each within its own.
conn-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {s : Obs Timeline Γ X} {b : Obs Timeline (X ∷ Γ) B} {q}
           → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q (pendRows (full sc) (connect s b) q)
           → Σ (Parts sc Rg (conn₀ s q sc) (pendRows (full (binds s q sc)) b (q ++ [ ix 0 ]))) λ pt
             → Within (Parts.Rb pt) (binds s q sc) (q ++ [ ix 0 ]) (pendRows (full (binds s q sc)) b (q ++ [ ix 0 ]))
             × Within (Parts.Rs pt) sc (q ++ [ ix 1 ]) (pendRows (full sc) s (q ++ [ ix 1 ]))
conn-parts {sc = sc} {s = s} {b} {q} ok ad (_ , wi) = pt , wb , ws
  where
    open ConnAt sc s b q ok ad
    pt = record
      { Rb      = Rb
      ; Rs      = Rs
      ; b⊆      = λ rb → wi (narrow⁼ σw (proj₁ rb)) (b-excl rb)
      ; s⊆      = λ rs → wi (nest-in (step here plain-ix) (proj₁ rs)) (s-excl rs)
      ; apart   = λ {y} rb rs → bl (proj₁ rb) (proj₁ rs) (⊑-refl y)
      ; clear-b = λ {y} h rb → proj₂ ok h (narrow⁼ σw (proj₁ rb)) (⊑-inside (⊑-refl y))
      ; clear-s = λ {y} h rs → proj₂ ok h (nest-in (step here plain-ix) (proj₁ rs)) (⊑-inside (⊑-refl y))
      ; sb      = within-sound {sc = binds s q sc} Iβ wb
      ; ss      = within-sound {sc = sc} Iσ ws
      }

-- A connect's body subscribed admissibly.
conn-ok : ∀ {Γ X} {sc : Scope Γ} {s : Obs Timeline Γ X} {q}
        → Ok (Hots (full sc)) q → Adm sc → Ok (Hots (full (binds s q sc))) (q ++ [ ix 0 ])
conn-ok {sc = sc} {s} {q} ok ad =
  LC.ok₀ {s = ⟦ s ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ s (full sc) (good-full sc ad)) (λ L → lawful-hot L) q ok
