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
open import Data.List using ([]; _∷_; [_])
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.AllPairs using ([])
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Nat.Properties using (<-cmp)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; flatMap; connect)
open import denotation.Position using (Pos; Label; ix; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.Read using (Visible)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; _≼_; _≺_; enter; Den; hot; ⟦_⟧; Proper; LaneOf; Ended; After; Truncate;
  module Joining; module Bounded; module Switch; module Exhaust; module Connecting)
open import denotation.Laws.Modulus using (≼-or-≻; ≼-≺-≺; ≺-irrefl; ≺→≼; ≺-ext)
open import denotation.Laws.Worlds using (W; W⁼; step; timer; join; here; inW; ⊑-trans; Plain; plain-ix; Real; Ok; Lawful; InvAt; InvD; Hots; _⊑_; ⊑-refl; ⊑-≼; ⊑-snoc⁺; PinBy; ⊑-inside; nest⁼; nest-in; narrow⁼; widen⁼; world-after; real-init; ok-step; real-snoc; anc-lead; anc-trans; world-anc; world-anc⁼; ⊕-injˡ; ⊕-injʳ; step≢root)
open import denotation.Laws using (inv-⟦⟧; good-cons)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws.JoinInv using (module Join; ix01)
open import denotation.Laws.Worlds.Leaves using (out-inj)
open import denotation.Laws.BoundedInv using (module BoundedI)
open import denotation.Laws.Nth using (module Nths)
import denotation.Laws.Connect as LC
open import operation.PureObservable using (module Machine)
open Machine using (Scope; binds; CS; cs)
open import adequacy.Rows using (full; pendRows)
open import adequacy.Cursor using (slots-0; Rgn; Sound; Excl; Within; Parts; JRo; JRl; LaneRg; Start; polF; Adm; Owes; Joined; joined; JInv;
  none; LanesIn; Ends; Lane; JoinF; Ze; e₀; e+)
open import adequacy.Bound using (good-full; owes-≼)

------------------------------------------------------------------------
-- Excluded worlds

-- No world position leads its subscription.
w-unled : ∀ {H p w} → Real p → W H p w → w ⊑ p → ⊥
w-unled {w = w} rp ww (zs , refl) =
  ≺-irrefl {w} (≼-≺-≺ {w} {w ⊕ zs} {w} (⊑-≼ {w} {w ⊕ zs} (zs , refl)) (world-after ww (real-init w zs rp)))

-- A subscription lies outside what its rows subscribe below them.
excl-root : ∀ {A H p} {E : EmissionSet A} → InvAt H p E → Real p → Excl H E p
excl-root I rp x pl v le = w-unled rp (nest-in (step (inW (InvAt.world I x)) pl) v) le

-- In the world of a row's plain child.
Kid : ∀ {A} → (Pos → Set) → EmissionSet A → Pos → Set
Kid {A} H E y = Σ Pos λ r → Σ (Ev A) λ e → Σ Label λ l → E r e × Plain l × W⁼ H (r ⊕ [ l ]) y

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
  no-lane op (_ , _ , x , st , ws , _) ex = kid-lead (start-kid op x st) ws ex

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

-- A JOINER'S LANES, FROM ITS OUTER'S ENTRY.  A joiner row's child's world
-- leads a position of a lane's world only if the row is the lane's own:
-- an outer row's, a value's first child's and another lane's children's
-- worlds are apart from the lane's, and of two bounded lanes the later
-- lies under its own root or under an end of the earlier.  So a position
-- of a lane's world clear of its own rows' children is clear of every
-- joiner row's.
module Lanes {Γ A B} (sc : Scope Γ) (f : A → Obs Timeline Γ B) {O : EmissionSet A} (ji : JInv sc f O) where
  H : Pos → Set
  H = Hots (full sc)

  f′ : A → Den B
  f′ a = ⟦ f a ⟧ (full sc)

  at : Pos
  at = JInv.at ji

  Io : InvAt H at O
  Io = JInv.io ji

  module J = Join (JInv.ok ji) f′ (JInv.fi ji) Io

  vis-pin : ∀ {c} {e : Ev B} → PinBy c e → Visible e → ⊥
  vis-pin (_ , refl , _) ()

  -- Every row of the outer lies past the joiner's subscription.
  owed : ∀ {C} → Owes C at → ∀ {q′ e} → O q′ e → Owes C q′
  owed {C} ow {q′} x = owes-≼ C ow (≺→≼ {at} {q′} (world-after (InvAt.world Io x) (InvAt.real Io x)))

  -- An outer row's child's world leads no position of a value's second
  -- child's but through that child.
  kid-lane⁼ : ∀ {x e l w q′ e″ y} → O x e → Plain l → W⁼ H (x ⊕ [ l ]) w → O q′ e″ → W⁼ H (q′ ⊕ [ ix 1 ]) y
            → (x ⊕ [ l ] ≡ q′ ⊕ [ ix 1 ] → ⊥) → w ⊑ y → ⊥
  kid-lane⁼ ox pl v oq here     ne le = J.kid-root ox pl v oq plain-ix ne le
  kid-lane⁼ ox pl v oq (inW yw) ne le = J.kid-lane ox pl v oq yw ne le

  -- A lane at a value's second child.
  module Un (Runs : Pos → Set) (Cut : Pos → Pos → Set) where
    open J.View (λ _ → ⊥) (λ _ _ _ → ⊤) using (V; v-o; v-val; v-lane; o-skip; o-pin; o-pass; o-nout; l-work; l-pass)
    open Joining (LaneOf f′) O (λ _ _ → ⊥) (Ended O) Runs Cut (λ _ → ⊥)
      using (JoinT; val; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand) renaming (step to o-step)

    -- Each row, shown whatever ends it.
    vw : ∀ {y e} → JoinT y e → Σ (Ev B) (V y)
    vw (val x)             = _ , v-val x refl
    vw (o-step x)          = _ , v-o x o-skip
    vw (opin x)            = _ , v-o x o-pin
    vw (oend x _)          = _ , v-o x (o-pass (λ ()))
    vw (opass x _)         = _ , v-o x (o-pass (λ ()))
    vw (lane x _ l _ w)    = _ , v-lane x l (l-work tt w)
    vw (lend x _ l _ _ _)  = _ , v-lane x l (l-pass tt (λ ()))
    vw (lpass x _ l _ _ _) = _ , v-lane x l (l-pass tt (λ ()))
    vw (hand _ _ _ _ ())
    vw (left x _ l _ _)    = _ , v-lane x l (l-work tt tt)
    vw (run () _)
    vw (rend () _ _)
    vw (rpass () _ _)
    vw (rhand () _)

    excl : ∀ {q′ a y} → O q′ (out a) → W⁼ H (q′ ⊕ [ ix 1 ]) y → Excl H (LaneOf f′ q′ a) y → Excl H (Truncate JoinT) y
    excl {q′} {a} {y} xq yw ex jr = go (proj₂ (vw (proj₁ jr)))
      where
        go : ∀ {x e l w} → V x e → Plain l → W⁼ H (x ⊕ [ l ]) w → w ⊑ y → ⊥
        go {x} (v-o ox ev) pl v le =
          kid-lane⁼ ox pl v xq yw (λ eq → o-nout ev ox (subst (λ z → O z (out a)) (sym (⊕-injˡ x q′ eq)) xq)) le
        go (v-val {q″} xr refl) pl v le =
          kid-lane⁼ xr plain-ix (nest⁼ (inW (step here pl)) v) xq yw (λ eq → ix01 (⊕-injʳ q″ q′ eq)) le
        go (v-lane {q″} xr l″ _) pl v le with q″ ≟ᵖ q′
        ... | yes refl with out-inj (InvAt.func Io xr xq)
        ...   | refl = ex l″ pl v le
        go (v-lane {q″} xr l″ _) pl v le | no ne =
          kid-lane⁼ xr plain-ix (nest⁼ (inW (step (inW (J.lw xr l″)) pl)) v) xq yw (λ eq → ne (⊕-injˡ q″ q′ eq)) le

  un-ends : ∀ {q′ a c k e} → O q′ (out a) → LaneOf f′ q′ a c end → LaneOf f′ q′ a k e → Visible e → k ≼ c
  un-ends {c = c} {k} x lc lk v with ≼-or-≻ k c
  ... | inj₁ le = le
  ... | inj₂ lt = ⊥-elim (vis-pin (InvAt.quiet (J.LI x) (proj₁ lc) (proj₁ lk) lt) v)

  -- A bounded lane, wherever its schedule subscribes it.
  module Bo (m : ℕ) where
    open BoundedI (JInv.ok ji) m f′ (JInv.fi ji) Io
      using (V; v-o; v-val; v-l; vw; lr; Lr; lr-row; lr-hand; Rel; apart; queued-in; rel; child-in; nest-under; row-not-c; lane-end;
             module LK; LI; sub-fun; row-w; s-w; seat*; seat′) renaming (sub-same to same)
    open J.View (Bounded.Done m f′ O) (λ _ _ _ → ⊤) using (o-nout)
    open Nths O using (nth-inj; nth-val)

    Sub : ℕ → Pos → Pos → A → Set
    Sub = Bounded.Sub m f′ O


    -- Under a lane's queued end's second child, against the lane.
    nu⁼ : ∀ {j qj sj aj c x l w y} → Sub j qj sj aj → After (f′ aj) sj c end → Bounded.Queued m f′ O c → Lr aj sj x → Plain l
        → W⁼ H (x ⊕ [ l ]) w → W⁼ H (c ⊕ [ ix 1 ]) y → w ⊑ y → ⊥
    nu⁼ sb ac Q lx pl v (inW yw) le = nest-under sb ac Q lx pl v yw le
    nu⁼ {c = c} {x} sb ac Q (lr-row x′ nq) pl v here le =
      LK.kid-root sb (proj₁ x′) pl v (proj₁ ac) plain-ix
        (λ eq → row-not-c sb ac Q x′ nq (subst (_⊑ (c ⊕ [ ix 1 ])) (sym (⊕-injˡ x c eq)) (⊑-snoc⁺ c))) le
    nu⁼ {c = c} sb ac Q (lr-hand x _ refl) pl v here le with lane-end sb ac x
    ... | refl = LK.kid-root sb (proj₁ ac) plain-ix (nest⁼ (inW (step here pl)) v) (proj₁ ac) plain-ix (λ eq → ix01 (⊕-injʳ c c eq)) le

    excl : ∀ {i q′ s a y} → Sub i q′ s a → W⁼ H s y → Excl H (Bounded.Lane m f′ O q′ a) y → Excl H (Truncate (Bounded.JoinT m f′ O)) y
    excl {i} {q′} {s} {a} {y} sb yw ex jr with seat* sb
    ... | seat′ {r = r} _ _ _ nr rw = go (vw (proj₁ jr))
      where
        ry : W⁼ H (r ⊕ [ ix 1 ]) y
        ry = nest⁼ rw yw

        go : ∀ {x e l w} → V x e → Plain l → W⁼ H (x ⊕ [ l ]) w → w ⊑ y → ⊥
        go {x} (v-o ox ev) pl v le =
          kid-lane⁼ ox pl v (nth-val nr) ry (λ eq → o-nout ev ox (subst (λ z → O z (out _)) (sym (⊕-injˡ x r eq)) (nth-val nr))) le
        go (v-val {q″} xr refl) pl v le =
          kid-lane⁼ xr plain-ix (nest⁼ (inW (step here pl)) v) (nth-val nr) ry (λ eq → ix01 (⊕-injʳ q″ r eq)) le
        go (v-l {i = j} sb′ lv) pl v le with <-cmp j i
        ... | tri≈ _ refl _ with sub-fun sb′ sb
        ...   | refl , refl , refl with lr sb lv
        ...     | lr-row x′ _      = ex (i , s , sb , x′) pl v le
        ...     | lr-hand ac _ refl = ex (i , s , sb , ac) plain-ix (nest⁼ (inW (step here pl)) v) le
        go (v-l {i = j} sb′ lv) pl v le | tri< lt _ _ with rel lt sb′ sb
        ... | apart xr₁ xr₂ ne rw₁ rw₂ =
          kid-lane⁼ xr₁ plain-ix (child-in rw₁ sb′ (lr sb′ lv) pl v) xr₂ (nest⁼ rw₂ yw) (λ eq → ne (⊕-injˡ _ _ eq)) le
        ... | queued-in ac Q v₁ = nu⁼ sb′ ac Q (lr sb′ lv) pl v (nest⁼ v₁ yw) le
        go (v-l {i = j} sb′ lv) pl v le | tri> _ _ gt with rel gt sb sb′
        ... | apart xr₁ xr₂ ne rw₁ rw₂ =
          kid-lane⁼ xr₂ plain-ix (child-in rw₂ sb′ (lr sb′ lv) pl v) xr₁ (nest⁼ rw₁ yw) (λ eq → ne (sym (⊕-injˡ _ _ eq))) le
        ... | queued-in ac Q v₁ = ex (i , s , sb , ac) plain-ix (child-in v₁ sb′ (lr sb′ lv) pl v) le

    row : ∀ {q′ a k e} → Bounded.Lane m f′ O q′ a k e
        → Σ Pos λ s′ → Σ ℕ (λ i → Sub i q′ s′ a) × W⁼ H s′ k × Excl H (Bounded.Lane m f′ O q′ a) k
    row (i , _ , sb , ac) = _ , (i , sb) , inW (row-w sb ac) , own
      where
        own : Excl H (Bounded.Lane m f′ O _ _) _
        own (_ , _ , sb′ , ar) pl v le with same sb sb′
        ... | refl = InvAt.under (LI sb) (proj₁ ar) (proj₁ ac) pl v le

    ends : ∀ {q′ a c k e} → O q′ (out a) → Bounded.Lane m f′ O q′ a c end → Bounded.Lane m f′ O q′ a k e → Visible e → k ≼ c
    ends {c = c} {k} _ (_ , _ , sb , lc) (_ , _ , sb′ , lk) v with same sb sb′
    ... | refl with ≼-or-≻ k c
    ...   | inj₁ le = le
    ...   | inj₂ lt = ⊥-elim (vis-pin (InvAt.quiet (LI sb) (proj₁ lc) (proj₁ lk) lt) v)

  -- Every lane's world, but for what its rows subscribe below them, in
  -- the joiner's region and the lane's.
  lanes-in : ∀ op {Rg} → (∀ {y} → W H at y → Excl H (Truncate (JoinF op f′ O)) y → Rg y) → LanesIn H (JRl sc Rg op f O) (polF op f′ O) O
  lanes-in (mergeᶠ nothing)  wi x refl yw ex = wi (nest-in (J.sw x) yw) (Un.excl (λ _ → ⊤) (λ _ _ → ⊥) x yw ex) , _ , _ , x , refl , yw , ex
  lanes-in (mergeᶠ (just m)) wi x (i , sb) yw ex =
    wi (nest-in (BoundedI.s-w (JInv.ok ji) m f′ (JInv.fi ji) Io sb) yw) (Bo.excl m sb yw ex) , _ , _ , x , (i , sb) , yw , ex
  lanes-in switchᶠ           wi x refl yw ex = wi (nest-in (J.sw x) yw) (Un.excl (λ _ → ⊤) (Switch.Cut f′ O) x yw ex) , _ , _ , x , refl , yw , ex
  lanes-in exhaustᶠ          wi x refl yw ex = wi (nest-in (J.sw x) yw) (Un.excl (Exhaust.Run f′ O) (λ _ _ → ⊥) x yw ex) , _ , _ , x , refl , yw , ex

  -- A lane's row: in its world, clear of its own rows' children.
  lane-row : ∀ op {q′ a k e} → O q′ (out a) → Lane (polF op f′ O) q′ a k e
           → Σ Pos λ s′ → Start (polF op f′ O) q′ a s′ × W⁼ H s′ k × Excl H (Lane (polF op f′ O) q′ a) k
  lane-row (mergeᶠ nothing)  x l = _ , refl , inW (J.lw x l) , λ l′ pl v le → InvAt.under (J.LI x) (proj₁ l′) (proj₁ l) pl v le
  lane-row (mergeᶠ (just m)) _ l = Bo.row m l
  lane-row switchᶠ           x l = _ , refl , inW (J.lw x l) , λ l′ pl v le → InvAt.under (J.LI x) (proj₁ l′) (proj₁ l) pl v le
  lane-row exhaustᶠ          x l = _ , refl , inW (J.lw x l) , λ l′ pl v le → InvAt.under (J.LI x) (proj₁ l′) (proj₁ l) pl v le

  lane-rows : ∀ op {Rl} → LanesIn H Rl (polF op f′ O) O → ∀ {q′ a k e} → O q′ (out a) → Lane (polF op f′ O) q′ a k e → Rl q′ k
  lane-rows op li x l with lane-row op x l
  ... | _ , st , w , ex = li x st w ex

  -- A lane's rows lie past its start.
  past : ∀ op {q′ a s′ r e} → Start (polF op f′ O) q′ a s′ → Lane (polF op f′ O) q′ a r e → enter (f′ a) s′ r e × s′ ≺ r
  past (mergeᶠ nothing)  refl l = l
  past (mergeᶠ (just m)) (_ , sb) (_ , _ , sb′ , ac) with BoundedI.sub-same (JInv.ok ji) m f′ (JInv.fi ji) Io sb sb′
  ... | refl = ac
  past switchᶠ           refl l = l
  past exhaustᶠ          refl l = l

  real-start : ∀ op {q′ a s′} → O q′ (out a) → Start (polF op f′ O) q′ a s′ → Real s′
  real-start (mergeᶠ nothing)  {q′} x refl = real-snoc q′ plain-ix (InvAt.real Io x)
  real-start (mergeᶠ (just m)) _ (_ , sb) with BoundedI.seat* (JInv.ok ji) m f′ (JInv.fi ji) Io sb
  ... | BoundedI.seat′ _ rs _ _ _ = rs
  real-start switchᶠ           {q′} x refl = real-snoc q′ plain-ix (InvAt.real Io x)
  real-start exhaustᶠ          {q′} x refl = real-snoc q′ plain-ix (InvAt.real Io x)

  -- A LANE SUBSCRIBED, WITHIN ITS REGION: no child of a lane's row leads
  -- back to its start, so the start lies in the region, and so does every
  -- position of its world clear of the lane's rows' children.
  lane-within : ∀ op {Rl} → LanesIn H Rl (polF op f′ O) O → ∀ {q′ a s′} → O q′ (out a) → Start (polF op f′ O) q′ a s′
              → Within (Rl q′) sc s′ (enter (f′ a) s′)
  lane-within op li x st = li x st here back , λ w ex → li x st (inW w) (λ l → ex (proj₁ (past op st l)))
    where
      back : Excl H (Lane (polF op f′ O) _ _) _
      back l pl v le = anc-lead (anc-trans (world-anc {H = H} (step here pl)) (world-anc⁼ v)) le (real-start op x st) (proj₂ (past op st l))

  ends : ∀ op → Ends (polF op f′ O) O
  ends (mergeᶠ nothing)  = un-ends
  ends (mergeᶠ (just m)) = Bo.ends m
  ends switchᶠ           = un-ends
  ends exhaustᶠ          = un-ends

-- A JOINER ENTERED: its outer's entry where it subscribed, every lane's
-- program admissible.
flat-jinv : ∀ {Γ A B} {sc : Scope Γ} {f : A → Obs Timeline Γ B} {s q}
          → Ok (Hots (full sc)) q → Adm sc → JInv sc f (pendRows (full sc) s q)
flat-jinv {sc = sc} {f} {s} {q} ok ad = record { at = q ; ok = ok ; io = Io ; fi = fi ; adm = ad }
  where open FlatAt sc f s q ok ad

-- Nothing begun or queued, every lane's world in its region.
flat-joined : ∀ {C Γ A B} {sc : Scope Γ} {Rg} {op} {f : A → Obs Timeline Γ B} {s q}
            → Owes C q → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q (pendRows (full sc) (flatMap op f s) q)
            → Joined sc (JRl sc Rg op f (pendRows (full sc) s q)) C (polF op (λ a → ⟦ f a ⟧ (full sc)) (pendRows (full sc) s q))
                     (pendRows (full sc) s q) false 0 [] []
flat-joined {C} {sc = sc} {op = op} {f} {s} {q} ow ok ad wi =
  joined {vs = []} {ws = []} none (refl , [] , (λ ()) , (λ _ → refl) , tt) (λ x no _ → ⊥-elim (no (owed {C} ow x))) ((λ ()) , λ x no → no (owed {C} ow x))
         (λ ()) [] (ends op) (lanes-in op (λ w ex → proj₂ wi w (as op ex))) (slots-0 op _ _ (owed {C} ow))
  where
    open Lanes sc f (flat-jinv {sc = sc} {f = f} {s = s} {q = q} ok ad)

    as : ∀ op′ {y} → Excl H (Truncate (JoinF op′ f′ (pendRows (full sc) s q))) y → Excl H (pendRows (full sc) (flatMap op′ f s) q) y
    as (mergeᶠ nothing)  ex = ex
    as (mergeᶠ (just m)) ex = ex
    as switchᶠ           ex = ex
    as exhaustᶠ          ex = ex

------------------------------------------------------------------------
-- A connect entered

-- A connect as entered at `q`: its source live, not yet subscribed.
conn₀ : ∀ {Γ X} → Obs Timeline Γ X → Pos → Scope Γ → CS Γ X
conn₀ s q sc = cs false true false (just q) nothing nothing q root s sc

-- A world's point one first child down, short of the world's start: its
-- parent is in the world too.
w-down : ∀ {H s z x} → W⁼ H s z → z ≡ x ⊕ [ ix 0 ] → (s ≡ x ⊕ [ ix 0 ] → ⊥) → W⁼ H s x
w-down here eq ne = ⊥-elim (ne eq)
w-down {H} {s} {x = x} (inW (step {x′} w _)) eq _ = subst (W⁼ H s) (⊕-injˡ x′ x eq) w
w-down {x = x} (inW (timer t _ _)) eq _ = ⊥-elim (step≢root x _ (sym eq))
w-down {x = x} (inW (join {h} _ _ _)) eq _ with ⊕-injʳ h x eq
... | ()

-- A chain's head leads its foot.
ze-⊑ : ∀ {q w} → Ze q w → q ⊑ w
ze-⊑ {q} e₀    = ⊑-refl q
ze-⊑ (e+ {w} e) = ⊑-trans (ze-⊑ e) (⊑-snoc⁺ w)

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
  σ = pendRows (full sc) s (q ⊕ [ ix 1 ])

  β : EmissionSet B
  β = pendRows (full (binds s q sc)) b (q ⊕ [ ix 0 ])

  H₀ : Pos → Set
  H₀ = Hots (full (binds s q sc))

  ok₀ : Ok H₀ (q ⊕ [ ix 0 ])
  ok₀ = LC.ok₀ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  Iβ : InvAt H₀ (q ⊕ [ ix 0 ]) β
  Iβ = LC.Iβ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  Iσ : InvAt H (q ⊕ [ ix 1 ]) σ
  Iσ = LC.Iσ {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  σw : ∀ {h e} → Proper σ h e → W H q h
  σw = LC.σ-wp {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  bl : ∀ {w x} → W⁼ H₀ (q ⊕ [ ix 0 ]) w → W⁼ H (q ⊕ [ ix 1 ]) x → w ⊑ x → ⊥
  bl = LC.body-leads {s = ⟦ s ⟧ (full sc)} {F = Fb} Is IF q ok

  -- The connect's rows.
  E : EmissionSet B
  E = pendRows (full sc) (connect s b) q

  Rb Rs : Rgn
  Rb y = W⁼ H₀ (q ⊕ [ ix 0 ]) y × Excl H₀ β y
  Rs y = W⁼ H (q ⊕ [ ix 1 ]) y × Excl H σ y

  open Connecting using (body; burst; echo; kept)

  -- A source row's first child's world leads no body position.
  src-kid : ∀ {k e l v y} → σ k e → Plain l → W⁼ H ((k ⊕ [ ix 0 ]) ⊕ [ l ]) v → v ⊑ y → W⁼ H₀ (q ⊕ [ ix 0 ]) y → ⊥
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

  wb : Within Rb (binds s q sc) (q ⊕ [ ix 0 ]) β
  wb = (here , excl-root Iβ (proj₁ ok₀)) , λ w ex → inW w , ex

  ws : Within Rs sc (q ⊕ [ ix 1 ]) σ
  ws = (here , excl-root Iσ (proj₁ (ok-step q ok))) , λ w ex → inW w , ex

-- A CONNECT ENTERED: its body and source in regions apart and clear of
-- the scope's hots, each within its own.
conn-parts : ∀ {Γ X B} {sc : Scope Γ} {Rg} {s : Obs Timeline Γ X} {b : Obs Timeline (X ∷ Γ) B} {q}
           → Ok (Hots (full sc)) q → Adm sc → Within Rg sc q (pendRows (full sc) (connect s b) q)
           → Σ (Parts sc Rg (conn₀ s q sc) (pendRows (full (binds s q sc)) b (q ⊕ [ ix 0 ]))) λ pt
             → Within (Parts.Rb pt) (binds s q sc) (q ⊕ [ ix 0 ]) (pendRows (full (binds s q sc)) b (q ⊕ [ ix 0 ]))
             × Within (Parts.Rs pt) sc (q ⊕ [ ix 1 ]) (pendRows (full sc) s (q ⊕ [ ix 1 ]))
conn-parts {sc = sc} {s = s} {b} {q} ok ad (_ , wi) = pt , wb , ws
  where
    open ConnAt sc s b q ok ad
    -- a point of the body's world past the source's subscription has its
    -- chain's head in that world too: the chain never reaches `q`
    up : ∀ {x w} → (q ⊕ [ ix 1 ]) ≼ x → Ze x w → W⁼ H₀ (q ⊕ [ ix 0 ]) w → W⁼ H₀ (q ⊕ [ ix 0 ]) x
    up px e₀ h = h
    up {x} px (e+ {w} e) h = up px e (w-down h refl ne)
      where ne : q ⊕ [ ix 0 ] ≡ w ⊕ [ ix 0 ] → ⊥
            ne eq with ⊕-injˡ q w eq
            ... | refl = px (≼-≺-≺ {x} {q} {q ⊕ [ ix 1 ]} (⊑-≼ (ze-⊑ e)) (≺-ext q []))
    pt = record
      { Rb      = Rb
      ; Rs      = Rs
      ; b⊆      = λ rb → wi (narrow⁼ σw (proj₁ rb)) (b-excl rb)
      ; s⊆      = λ rs → wi (nest-in (step here plain-ix) (proj₁ rs)) (s-excl rs)
      ; apart   = λ {y} rb rs → bl (proj₁ rb) (proj₁ rs) (⊑-refl y)
      ; b-lead  = λ rb rs le → bl (proj₁ rb) (proj₁ rs) le
      ; b-chain = λ {x} px rs e rb → bl (up px e (proj₁ rb)) (proj₁ rs) (⊑-refl x)
      ; clear-b = λ {y} h rb → proj₂ ok h (narrow⁼ σw (proj₁ rb)) (⊑-inside (⊑-refl y))
      ; clear-s = λ {y} h rs → proj₂ ok h (nest-in (step here plain-ix) (proj₁ rs)) (⊑-inside (⊑-refl y))
      ; sb      = within-sound {sc = binds s q sc} Iβ wb
      ; ss      = within-sound {sc = sc} Iσ ws
      ; cr      = proj₁ ok
      ; Hβ      = H₀
      ; iβ      = Iβ
      ; iσ      = Iσ
      ; wapart  = bl
      }

-- A connect's body subscribed admissibly.
conn-ok : ∀ {Γ X} {sc : Scope Γ} {s : Obs Timeline Γ X} {q}
        → Ok (Hots (full sc)) q → Adm sc → Ok (Hots (full (binds s q sc))) (q ⊕ [ ix 0 ])
conn-ok {sc = sc} {s} {q} ok ad =
  LC.ok₀ {s = ⟦ s ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ s (full sc) (good-full sc ad)) (λ L → lawful-hot L) q ok
