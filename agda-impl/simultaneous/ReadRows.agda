{-# OPTIONS --guardedness #-}

-- THE ELABORATED READER'S ROWS: a lawful annotated hot `G`, joined at
-- `p′` (`R`), folded by `joinStep` (`O`), each fold's list merged (`U`).
-- Every row of each lies under one row of `G` joined, or is the late end;
-- where the rows of `G` up to a downward-closed bound are listed with
-- their rows, so are the reader's, and each is constructed with its
-- reach.
module simultaneous.ReadRows where

open import Data.Bool using (Bool; true; T)
open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; length; filter)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-map⁻; ∈-filter⁺; ∈-filter⁻; ∈-++⁺ˡ; ∈-++⁺ʳ; ∈-++⁻)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; _<ᵖ_; sub; ix; last)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Bare; Unpinned; EmissionSet; Den; Few; Reach; Truncate;
  Rejoin; shown; heard; ended; late; InE; LaneOf; _≺_; _≼_; module Scan; module Merge; module Op)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-≺-≺; ≺-≼-≺; ≼-antisym; ≼-split; ≺-ext; ≼-or-≻)
open import denotation.Laws.Worlds using (Lawful; _⊑_; ⊕-injˡ; ⊕-injʳ; ⊑-≼; ⊕-assoc; ⊕-identityʳ; ⊑-cmp; ⊑-snoc; ⊑-refl; ⊑-trans)
open import denotation.Laws.Worlds.Leaves using (module AccF; of-idx; of-row; of-rows; of-in; of-reach; of-end-row; ine-pin)
open import adequacy.SubOne using (scan-reach)
open import simultaneous.SimPos using (apart)
open import simultaneous.ReadLane using (Marks; step-just; step-nothing; of-marks; of-last⁻; of-last; of-skip)
open import adequacy.SubJoin using (Bind; lower; row-reach; rejoin-reach)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.ReadFold using (foldᵈ)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; joinStep)

module Rows {X : Set} (G : EmissionSet (AIE X)) (p′ : Pos) (lawG : Lawful G)
            (fewG : ∀ {q e} → G q e → Unpinned e → Few G q) where

  z₀ : Bool × List (IE X)
  z₀ = true , []

  R : EmissionSet (AIE X)
  R = Truncate (Rejoin p′ G)

  O : EmissionSet (Bool × List (IE X))
  O = Truncate (Scan.ScanT joinStep z₀ R)

  F : Bool × List (IE X) → Den (IE X)
  F s = Op.of (proj₂ s)

  J : EmissionSet (IE X)
  J = Merge.JoinT F O

  U : EmissionSet (IE X)
  U = Truncate J

  module JM = Merge F O

  BG : Bind G
  BG = record { law = lawG ; few = fewG }

  -- A hot row joined.
  at : Pos → Pos
  at l = l ⊕ [ sub p′ ]

  ----------------------------------------------------------------------
  -- The joined rows

  -- How a hot row's event is joined.
  data Lifted : Ev (AIE X) → Ev (AIE X) → Set where
    l-out  : ∀ {x} → Lifted (out x) (out x)
    l-skip : Lifted skip skip
    l-pin  : ∀ {r} → Lifted (pin r) skip
    l-end  : Lifted end end

  -- A joined row: a hot row joined, or the late end.
  data RV (k : Pos) (e : Ev (AIE X)) : Set where
    rv-row  : ∀ {l e₀} → G l e₀ → p′ ≺ l → k ≡ at l → Lifted e₀ e → RV k e
    rv-late : ∀ {c} → G c end → c ≼ p′ → k ≡ p′ ⊕ [ last ] → e ≡ end → RV k e

  rv : ∀ {k e} → Rejoin p′ G k e → RV k e
  rv (shown {e = out _} x _ pl) = rv-row x pl refl l-out
  rv (shown {e = skip} x _ pl)  = rv-row x pl refl l-skip
  rv (heard x pl)               = rv-row x pl refl l-pin
  rv (ended x pl)               = rv-row x pl refl l-end
  rv (late x cp)                = rv-late x cp refl refl

  lifted-func : ∀ {e₀ e e′} → Lifted e₀ e → Lifted e₀ e′ → e ≡ e′
  lifted-func l-out  l-out  = refl
  lifted-func l-skip l-skip = refl
  lifted-func l-pin  l-pin  = refl
  lifted-func l-end  l-end  = refl

  -- Nothing joined lies past the hot's end at the subscription.
  late-none : ∀ {c l e₀} → G c end → c ≼ p′ → G l e₀ → p′ ≺ l → ⊥
  late-none {c} {l} gc cp gl pl = ≼-trans {l} {c} {p′} (Lawful.proper lawG gc gl) cp pl

  rj-func : ∀ {k e e′} → Rejoin p′ G k e → Rejoin p′ G k e′ → e ≡ e′
  rj-func x x′ with rv x | rv x′
  ... | rv-row {l} g _ refl f | rv-row {l′} g′ _ eq f′ with ⊕-injˡ l l′ eq
  ...   | refl with Lawful.func lawG g g′
  ...     | refl = lifted-func f f′
  rj-func x x′ | rv-row {l} _ _ refl _ | rv-late _ _ eq _ with ⊕-injʳ l p′ eq
  ... | ()
  rj-func x x′ | rv-late _ _ refl _ | rv-row {l} _ _ eq _ with ⊕-injʳ p′ l eq
  ... | ()
  rj-func x x′ | rv-late _ _ _ refl | rv-late _ _ _ refl = refl

  r-func : ∀ {k e e′} → R k e → R k e′ → e ≡ e′
  r-func x x′ = rj-func (proj₁ x) (proj₁ x′)

  r-reach : ∀ {y e} → R y e → Reach R y e
  r-reach (_ , ks , h) = ks , λ z lt d → h (proj₁ z) lt d

  -- Two hot rows joined, in order: in order.
  at-lower : ∀ {l l′ e e′} → G l e → G l′ e′ → at l′ ≺ at l → l′ ≺ l
  at-lower g g′ lt = lower lawG g g′ lt

  -- A HOT ROW JOINED, with the rows before it.
  r-row : ∀ {l e₀} → G l e₀ → p′ ≺ l → Few G l → Σ (Ev (AIE X)) (R (at l))
  r-row {e₀ = out x} g pl f = _ , shown g tt pl , row-reach BG g f pl {out x}
  r-row {e₀ = skip}  g pl f = _ , shown g tt pl , row-reach BG g f pl {skip}
  r-row {e₀ = pin _} g pl f = _ , heard g pl , row-reach BG g f pl {skip}
  r-row {e₀ = end}   g pl f = _ , ended g pl , row-reach BG g f pl {end}

  r-out : ∀ {l x} → G l (out x) → p′ ≺ l → R (at l) (out x)
  r-out {x = x} g pl = shown g tt pl , row-reach BG g (fewG g tt) pl {out x}

  r-end : ∀ {l} → G l end → p′ ≺ l → R (at l) end
  r-end g pl = ended g pl , row-reach BG g (fewG g tt) pl {end}

  ----------------------------------------------------------------------
  -- Joined rows apart

  flat-apart : ∀ {l l′ e e′} → G l e → G l′ e′ → l ≺ l′ → ¬ (l ⊑ l′)
  flat-apart {l} g g′ lt ([] , refl)    = ≺-irrefl {l} (subst (l ≺_) (⊕-identityʳ l) lt)
  flat-apart     g g′ lt (_ ∷ _ , refl) = Lawful.flat lawG g g′

  -- Joined rows of rows in order lie in order, everything below them too.
  at-apart : ∀ {l l′ e e′} → G l e → G l′ e′ → l ≺ l′ → ∀ σ σ′ → (at l ⊕ σ) ≺ (at l′ ⊕ σ′)
  at-apart {l} {l′} g g′ lt σ σ′ =
    subst₂ _≺_ (sym (⊕-assoc l [ sub p′ ] σ)) (sym (⊕-assoc l′ [ sub p′ ] σ′)) (apart lt (flat-apart g g′ lt) (sub p′ ∷ σ) (sub p′ ∷ σ′))

  -- No hot row lies under another's join.
  under-at : ∀ {l l′ e e′} → G l e → G l′ e′ → at l ⊑ l′ → ⊥
  under-at {l} {e′ = e′} g g′ (zs , refl) = Lawful.flat lawG g (subst (λ z → G z e′) (⊕-assoc l [ sub p′ ] zs) g′)

  -- One join leads a position.
  at-unique : ∀ {l l′ e e′ m} → G l e → G l′ e′ → at l ⊑ m → at l′ ⊑ m → l ≡ l′
  at-unique {l} {l′} g g′ a a′ with ⊑-cmp (at l) (at l′) a a′
  ... | inj₁ h = one g g′ h
    where
      one : ∀ {l l′ e e′} → G l e → G l′ e′ → at l ⊑ at l′ → l ≡ l′
      one {l} {l′} g g′ h with ⊑-snoc l′ h
      ... | inj₁ u  = ⊥-elim (under-at g g′ u)
      ... | inj₂ eq = ⊕-injˡ l l′ eq
  ... | inj₂ h = sym (one g′ g h)
    where
      one : ∀ {l l′ e e′} → G l e → G l′ e′ → at l ⊑ at l′ → l ≡ l′
      one {l} {l′} g g′ h with ⊑-snoc l′ h
      ... | inj₁ u  = ⊥-elim (under-at g g′ u)
      ... | inj₂ eq = ⊕-injˡ l l′ eq

  -- No join leads the late end.
  at-late : ∀ {l} → p′ ≺ l → at l ⊑ (p′ ⊕ [ last ]) → ⊥
  at-late {l} pl h with ⊑-snoc p′ h
  ... | inj₁ u  = ≺-absurd {p′} {l} pl (≺-≼-≺ {l} {at l} {p′} (≺-ext l []) (⊑-≼ u))
  ... | inj₂ eq with ⊕-injʳ l p′ eq
  ...   | ()

  -- A row before the end: strictly.
  before-end : ∀ {l c x} → G l (out x) → G c end → l ≺ c
  before-end {l} {c} g gc with ≼-split {l} {c} (Lawful.proper lawG gc g)
  ... | inj₁ lt   = lt
  ... | inj₂ refl with Lawful.func lawG g gc
  ...   | ()

  ----------------------------------------------------------------------
  -- Where the reader's rows lie

  open AccF joinStep z₀ {R} r-func using (acc-func)

  -- A fold: a step from some fold, at a joined value.
  acc-step : ∀ {q s} → Scan.Acc joinStep z₀ R q s → Σ (Bool × List (IE X)) λ β → Σ (AIE X) λ x → R q (out x) × s ≡ joinStep β x
  acc-step (Scan.acc₀ x _)         = _ , _ , x , refl
  acc-step (Scan.acc {b = b} _ x _ _) = b , _ , x , refl

  -- What a fold row is: a joined value folded, a joined skip or pin, a
  -- joined end, or the late end.
  data OV (q : Pos) : Ev (Bool × List (IE X)) → Set where
    ov-val  : ∀ {l x s} β → G l (out x) → p′ ≺ l → q ≡ at l → Scan.Acc joinStep z₀ R q s → s ≡ joinStep β x → OV q (out s)
    ov-skip : ∀ {l e₀} → G l e₀ → p′ ≺ l → q ≡ at l → (∀ {x} → e₀ ≡ out x → ⊥) → OV q skip
    ov-end  : ∀ {l} → G l end → p′ ≺ l → q ≡ at l → OV q end
    ov-late : ∀ {c} → G c end → c ≼ p′ → q ≡ p′ ⊕ [ last ] → OV q end

  ov : ∀ {q e} → O q e → OV q e
  ov (Scan.sval a , _) with acc-step a
  ... | β , x , r , eq with rv (proj₁ r)
  ...   | rv-row g pl refl l-out = ov-val β g pl refl a eq
  ov (Scan.sstep r , _) with rv (proj₁ r)
  ... | rv-row g pl refl l-skip = ov-skip g pl refl λ ()
  ... | rv-row g pl refl l-pin  = ov-skip g pl refl λ ()
  ov (Scan.spin r , _) with rv (proj₁ r)
  ... | rv-row _ _ _ ()
  ... | rv-late _ _ _ ()
  ov (Scan.send r , _) with rv (proj₁ r)
  ... | rv-row g pl refl l-end = ov-end g pl refl
  ... | rv-late g cp refl _    = ov-late g cp refl

  -- An `of`'s rows lie past its subscription.
  of-after : ∀ {w} {xs : List (IE X)} {k e} → InE (ofᴱ w 0 xs) k e → w ⊑ k × w ≺ k
  of-after {w} {xs} r with of-idx w 0 xs r
  ... | inj₁ (j , _ , refl) = ([ ix j ] , refl) , ≺-ext w []
  ... | inj₂ refl           = ([ last ] , refl) , ≺-ext w []

  -- Where a reader's row lies: under a joined hot row, or the late end.
  data Origin (m : Pos) : Set where
    or-row  : ∀ {l e₀} → G l e₀ → p′ ≺ l → at l ⊑ m → Origin m
    or-late : ∀ {c} → G c end → c ≼ p′ → m ≡ p′ ⊕ [ last ] → Origin m

  lane-at : ∀ {q s k e} → LaneOf F q s k e → (q ⊕ [ ix 1 ]) ⊑ k
  lane-at ln = proj₁ (of-after (proj₁ (proj₁ ln)))

  origin : ∀ {m e} → J m e → Origin m
  origin (Merge.val x) with ov x
  ... | ov-val _ g pl refl _ _ = or-row g pl ([ ix 0 ] , refl)
  origin (Merge.step x) with ov x
  ... | ov-skip g pl refl _ = or-row g pl (⊑-refl _)
  origin (Merge.opin x) with ov x
  ... | ()
  origin (Merge.oend x _) with ov x
  ... | ov-end g pl refl    = or-row g pl (⊑-refl _)
  ... | ov-late g cp refl   = or-late g cp refl
  origin (Merge.opass x _) with ov x
  ... | ov-end g pl refl    = or-row g pl (⊑-refl _)
  ... | ov-late g cp refl   = or-late g cp refl
  origin (Merge.lane {q} {a} x _ ln _ _) with ov x
  ... | ov-val _ g pl refl _ _ = or-row g pl (⊑-trans ([ ix 1 ] , refl) (lane-at {q} {a} ln))
  origin (Merge.lend {q} {a} x _ ln _ _ _) with ov x
  ... | ov-val _ g pl refl _ _ = or-row g pl (⊑-trans ([ ix 1 ] , refl) (lane-at {q} {a} ln))
  origin (Merge.lpass {q} {a} x _ ln _ _ _) with ov x
  ... | ov-val _ g pl refl _ _ = or-row g pl (⊑-trans ([ ix 1 ] , refl) (lane-at {q} {a} ln))
  origin (Merge.hand _ _ _ _ ())
  origin (Merge.left _ _ ln _ _) = ⊥-elim (ine-pin (proj₁ (proj₁ ln)))
  origin (Merge.run () _)
  origin (Merge.rend () _ _)
  origin (Merge.rpass () _ _)
  origin (Merge.rhand () _)

  -- Rows in order lie under joins in order.
  origin-order : ∀ {m m′ l l′ e₀ e₀′} → G l e₀ → G l′ e₀′ → at l ⊑ m → at l′ ⊑ m′ → m′ ≺ m → l′ ≼ l
  origin-order {l = l} {l′} g g′ (σ , refl) (σ′ , refl) lt ll′ = ≺-absurd {at l ⊕ σ} {at l′ ⊕ σ′} (at-apart g g′ ll′ σ σ′) lt

  ----------------------------------------------------------------------
  -- The rows a joined hot row yields

  o-val : ∀ {l x s} → G l (out x) → p′ ≺ l → Scan.Acc joinStep z₀ R (at l) s → O (at l) (out s)
  o-val g pl a = Scan.sval a , scan-reach r-reach (Scan.sval a)

  o-end : ∀ {l} → G l end → p′ ≺ l → O (at l) end
  o-end g pl = Scan.send (r-end g pl) , scan-reach r-reach (Scan.send (r-end g pl))

  o-late : ∀ {c} → G c end → c ≼ p′ → O (p′ ⊕ [ last ]) end
  o-late g cp = Scan.send r , scan-reach r-reach (Scan.send r)
    where r = late g cp , rejoin-reach BG (late g cp) tt

  o-skip : ∀ {l e₀} → G l e₀ → p′ ≺ l → Few G l → (∀ {x} → e₀ ≡ out x → ⊥) → (e₀ ≡ end → ⊥) → O (at l) skip
  o-skip {e₀ = out _} _ _ _ nx _  = ⊥-elim (nx refl)
  o-skip {e₀ = end}   _ _ _ _  ne = ⊥-elim (ne refl)
  o-skip {e₀ = skip}  g pl f _ _  = Scan.sstep r , scan-reach r-reach (Scan.sstep r)
    where r = shown g tt pl , row-reach BG g f pl {skip}
  o-skip {e₀ = pin _} g pl f _ _  = Scan.sstep r , scan-reach r-reach (Scan.sstep r)
    where r = heard g pl , row-reach BG g f pl {skip}

  -- A lane's end.
  lane-end : ∀ q s → LaneOf F q s (q ⊕ [ ix 1 ] ⊕ [ last ]) end
  lane-end q s = (of-end-row (q ⊕ [ ix 1 ]) 0 (proj₂ s) , of-reach (q ⊕ [ ix 1 ]) 0 (proj₂ s) {_} {end}) , ≺-ext (q ⊕ [ ix 1 ]) []

  -- No lane ends the whole: the outer ends past it.
  not-done : ∀ {l x} → G l (out x) → p′ ≺ l → ∀ σ → ¬ Merge.Done F O (at l ⊕ [ ix 1 ] ⊕ σ)
  not-done {l} g pl σ ((c₀ , oc , c≼) , _) with ov oc
  ... | ov-end {le} ge _ refl =
    c≼ (subst₂ _≺_ (sym (⊕-assoc (at l) [ ix 1 ] σ)) (⊕-identityʳ (at le)) (at-apart g ge (before-end g ge) (ix 1 ∷ σ) []))
  ... | ov-late gc cp refl = late-none gc cp g pl

  -- An outer end ends the whole: every lane before it has.
  done-at : ∀ {l} → G l end → p′ ≺ l → Merge.Done F O (at l)
  done-at {l} g pl = (at l , o-end g pl , ≼-refl {at l}) , λ x _ ql _ → lane-ended x ql
    where
      lane-ended : ∀ {q s} → O q (out s) → q ≺ at l → Σ Pos λ c₀ → LaneOf F q s c₀ end × c₀ ≼ at l
      lane-ended {s = s} x ql with ov x
      ... | ov-val {l′} _ g′ _ refl _ _ = at l′ ⊕ [ ix 1 ] ⊕ [ last ] , lane-end (at l′) s ,
        ≺→≼ {at l′ ⊕ [ ix 1 ] ⊕ [ last ]} {at l}
          (subst₂ _≺_ (sym (⊕-assoc (at l′) [ ix 1 ] [ last ])) (⊕-identityʳ (at l)) (at-apart g′ g (at-lower g g′ ql) (ix 1 ∷ last ∷ []) []))

  done-late : ∀ {c} → G c end → c ≼ p′ → Merge.Done F O (p′ ⊕ [ last ])
  done-late g cp = (p′ ⊕ [ last ] , o-late g cp , ≼-refl {p′ ⊕ [ last ]}) , λ x _ _ _ → none x
    where
      none : ∀ {q s} → O q (out s) → Σ Pos λ c₀ → LaneOf F q s c₀ end × c₀ ≼ (p′ ⊕ [ last ])
      none x with ov x
      ... | ov-val _ g′ pl′ refl _ _ = ⊥-elim (late-none g cp g′ pl′)

  ----------------------------------------------------------------------
  -- THE ROWS LISTED: where the rows of `G` in a decided, downward-closed
  -- `UG` are listed with their rows, the reader's rows over them are
  -- listed too, each with its row and its reach.

  module Listed (UG : Pos → Set) (ug? : ∀ l → Dec (UG l)) (down : ∀ {l l′} → l′ ≺ l → UG l → UG l′)
                (ls : List Pos) (cov : ∀ {l e} → G l e → UG l → l ∈ ls) (back : ∀ {l} → l ∈ ls → Σ (Ev (AIE X)) (G l)) where

    down≼ : ∀ {l l′} → l′ ≼ l → UG l → UG l′
    down≼ {l} {l′} h u with ≼-split {l′} {l} h
    ... | inj₁ lt   = down lt u
    ... | inj₂ refl = u

    few-ug : ∀ {l} → UG l → Few G l
    few-ug u = ls , λ g lt → cov g (down lt u)

    Live : Pos → Set
    Live l = UG l × p′ ≺ l

    live? : ∀ l → Dec (Live l)
    live? l = ug? l ×-dec T? (p′ <ᵖ l)

    -- The joined rows a fold reads.
    ksR : List Pos
    ksR = L.map at (filter live? ls)

    rowsR : ∀ {k} → k ∈ ksR → Σ (Ev (AIE X)) (R k)
    rowsR i with ∈-map⁻ at i
    ... | l , il , refl with ∈-filter⁻ live? {xs = ls} il
    ...   | ils , (u , pl) = r-row (proj₂ (back ils)) pl (few-ug u)

    covR : ∀ {l e₀} → G l e₀ → Live l → ∀ {k e} → R k e → k ≺ at l → k ∈ ksR
    covR g (u , pl) y lt with rv (proj₁ y)
    ... | rv-row g′ pl′ refl _ = let u′ = down (at-lower g g′ lt) u in ∈-map⁺ at (∈-filter⁺ live? (cov g′ u′) (u′ , pl′))
    ... | rv-late gc cp refl _ = ⊥-elim (late-none gc cp g pl)

    -- A joined value's fold, constructed.
    acc : ∀ {l x} → G l (out x) → Live l → Σ (Bool × List (IE X)) (Scan.Acc joinStep z₀ R (at l))
    acc g lv = foldᵈ joinStep z₀ R r-func ksR rowsR (covR g lv) (r-out g (proj₂ lv))

    -- The reader's rows over one listed row.
    gen : ∀ l → Σ (Ev (AIE X)) (G l) → Live l → List Pos
    gen l (out x , g) lv = (at l ⊕ [ ix 0 ]) ∷ of-rows (at l ⊕ [ ix 1 ]) 0 (proj₂ (proj₁ (acc g lv)))
    gen l (skip , _)  _  = [ at l ]
    gen l (pin _ , _) _  = [ at l ]
    gen l (end , _)   _  = [ at l ]

    Back : List Pos → Set
    Back ks = ∀ {l} → l ∈ ks → Σ (Ev (AIE X)) (G l)

    genAll : (ks : List Pos) → Back ks → List Pos
    genAll []       b = []
    genAll (l ∷ ks) b with live? l
    ... | yes lv = gen l (b (here refl)) lv ++ genAll ks (λ i → b (there i))
    ... | no _   = genAll ks (λ i → b (there i))

    -- The late end, where a listed end lies at or before the subscription.
    late? : ∀ l → Σ (Ev (AIE X)) (G l) → List Pos
    late? l (out _ , _) = []
    late? l (skip , _)  = []
    late? l (pin _ , _) = []
    late? l (end , _) with ug? l | T? (p′ <ᵖ l)
    ... | yes _ | no _  = [ p′ ⊕ [ last ] ]
    ... | yes _ | yes _ = []
    ... | no _  | _     = []

    lateAll : (ks : List Pos) → Back ks → List Pos
    lateAll []       b = []
    lateAll (l ∷ ks) b = late? l (b (here refl)) ++ lateAll ks (λ i → b (there i))

    ksU : List Pos
    ksU = genAll ls back ++ lateAll ls back

    ----------------------------------------------------------------------
    -- Listed

    genAll-in : ∀ ks (b : Back ks) {l m} → l ∈ ks → Live l → (∀ r lv → m ∈ gen l r lv) → m ∈ genAll ks b
    genAll-in (k ∷ ks) b (here refl) lv h with live? k
    ... | yes lv′ = ∈-++⁺ˡ (h (b (here refl)) lv′)
    ... | no nl   = ⊥-elim (nl lv)
    genAll-in (k ∷ ks) b (there i) lv h with live? k
    ... | yes lv′ = ∈-++⁺ʳ (gen k (b (here refl)) lv′) (genAll-in ks (λ j → b (there j)) i lv h)
    ... | no _    = genAll-in ks (λ j → b (there j)) i lv h

    late-np : ∀ {c} → c ≼ p′ → ¬ (p′ ≺ c)
    late-np {c} cp h = ≺-irrefl {c} (≼-≺-≺ {c} {p′} {c} cp h)

    late-has : ∀ {c} (r : Σ (Ev (AIE X)) (G c)) → G c end → UG c → ¬ (p′ ≺ c) → (p′ ⊕ [ last ]) ∈ late? c r
    late-has {c} (e , g′) g u np with Lawful.func lawG g g′
    ... | refl with ug? c | T? (p′ <ᵖ c)
    ...   | yes _ | no _  = here refl
    ...   | yes _ | yes h = ⊥-elim (np h)
    ...   | no nu | _     = ⊥-elim (nu u)

    lateAll-in : ∀ ks (b : Back ks) {c} → c ∈ ks → G c end → UG c → ¬ (p′ ≺ c) → (p′ ⊕ [ last ]) ∈ lateAll ks b
    lateAll-in (k ∷ ks) b (here refl) g u np = ∈-++⁺ˡ (late-has (b (here refl)) g u np)
    lateAll-in (k ∷ ks) b (there i)   g u np = ∈-++⁺ʳ (late? k (b (here refl))) (lateAll-in ks (λ j → b (there j)) i g u np)

    -- Where a reader's row lies, within the bound.
    data Good (m : Pos) : Set where
      g-row  : ∀ {l e₀} → G l e₀ → p′ ≺ l → at l ⊑ m → UG l → Good m
      g-late : ∀ {c} → G c end → c ≼ p′ → m ≡ p′ ⊕ [ last ] → UG c → Good m

    good-before : ∀ {m y e} → J y e → y ≺ m → Good m → Good y
    good-before y lt (g-row g pl a u) with origin y
    ... | or-row g′ pl′ a′  = g-row g′ pl′ a′ (down≼ (origin-order g g′ a a′ lt) u)
    ... | or-late gc cp _   = ⊥-elim (late-none gc cp g pl)
    good-before y lt (g-late gc′ cp′ _ u) with origin y
    ... | or-row g′ pl′ _   = ⊥-elim (late-none gc′ cp′ g′ pl′)
    ... | or-late gc cp eq  = g-late gc cp eq (down≼ (Lawful.proper lawG gc′ gc) u)

    ug-row : ∀ {l e₀ m} → G l e₀ → p′ ≺ l → at l ⊑ m → Good m → UG l
    ug-row g pl a (g-row g′ _ a′ u) with at-unique g g′ a a′
    ... | refl = u
    ug-row g pl a (g-late _ _ refl _) = ⊥-elim (at-late pl a)

    in-gen : ∀ {l e₀ m} → G l e₀ → Live l → (∀ r lv → m ∈ gen l r lv) → m ∈ ksU
    in-gen g lv h = ∈-++⁺ˡ (genAll-in ls back (cov g (proj₁ lv)) lv h)

    val-in : ∀ {l x} → G l (out x) → ∀ r lv → (at l ⊕ [ ix 0 ]) ∈ gen l r lv
    val-in g (e , g′) lv with Lawful.func lawG g g′
    ... | refl = here refl

    lane-in : ∀ {l x s k} → G l (out x) → Scan.Acc joinStep z₀ R (at l) s → k ∈ of-rows (at l ⊕ [ ix 1 ]) 0 (proj₂ s)
            → ∀ r lv → k ∈ gen l r lv
    lane-in {l} {k = k} g a i (e , g′) lv with Lawful.func lawG g g′
    ... | refl = there (subst (λ s′ → k ∈ of-rows (at l ⊕ [ ix 1 ]) 0 (proj₂ s′)) (acc-func refl a (proj₂ (acc g′ lv))) i)

    at-in : ∀ {l e₀} → G l e₀ → (∀ {x} → e₀ ≡ out x → ⊥) → ∀ r lv → at l ∈ gen l r lv
    at-in g nx (out x , g′) lv = ⊥-elim (nx (Lawful.func lawG g g′))
    at-in g nx (skip , _)   lv = here refl
    at-in g nx (pin _ , _)  lv = here refl
    at-in g nx (end , _)    lv = here refl

    late-cov : ∀ {c} → G c end → c ≼ p′ → Good (p′ ⊕ [ last ]) → (p′ ⊕ [ last ]) ∈ ksU
    late-cov gc cp (g-row g pl a _)   = ⊥-elim (at-late pl a)
    late-cov gc cp (g-late gc′ _ _ u) =
      let u′ = down≼ (Lawful.proper lawG gc′ gc) u in ∈-++⁺ʳ (genAll ls back) (lateAll-in ls back (cov gc u′) gc u′ (late-np cp))

    end-cov : ∀ {m} → O m end → Good m → m ∈ ksU
    end-cov x gd with ov x
    ... | ov-end g pl refl   = in-gen g (ug-row g pl (⊑-refl _) gd , pl) (at-in g (λ ()))
    ... | ov-late gc cp refl = late-cov gc cp gd

    lane-cov : ∀ {q s k e} → O q (out s) → LaneOf F q s k e → Good k → k ∈ ksU
    lane-cov {s = s} x ln gd with ov x
    ... | ov-val {l} _ g pl refl a _ =
      in-gen g (ug-row g pl (⊑-trans ([ ix 1 ] , refl) (lane-at {at l} {s} ln)) gd , pl)
        (lane-in g a (of-in (at l ⊕ [ ix 1 ]) 0 (proj₂ s) (proj₁ (proj₁ ln))))

    -- EVERY READER ROW WITHIN THE BOUND IS LISTED.
    covJ : ∀ {m e} → J m e → Good m → m ∈ ksU
    covJ (Merge.val x) gd with ov x
    ... | ov-val _ g pl refl _ _ = in-gen g (ug-row g pl ([ ix 0 ] , refl) gd , pl) (val-in g)
    covJ (Merge.step x) gd with ov x
    ... | ov-skip g pl refl nx = in-gen g (ug-row g pl (⊑-refl _) gd , pl) (at-in g nx)
    covJ (Merge.opin x) gd with ov x
    ... | ()
    covJ (Merge.oend x _)  gd = end-cov x gd
    covJ (Merge.opass x _) gd = end-cov x gd
    covJ (Merge.lane x _ ln _ _)    gd = lane-cov x ln gd
    covJ (Merge.lend x _ ln _ _ _)  gd = lane-cov x ln gd
    covJ (Merge.lpass x _ ln _ _ _) gd = lane-cov x ln gd
    covJ (Merge.hand _ _ _ _ ())    gd
    covJ (Merge.left _ _ ln _ _)    gd = ⊥-elim (ine-pin (proj₁ (proj₁ ln)))
    covJ (Merge.run () _)    gd
    covJ (Merge.rend () _ _)  gd
    covJ (Merge.rpass () _ _) gd
    covJ (Merge.rhand () _)   gd

    reachJ : ∀ {m e} → J m e → Good m → Reach J m e
    reachJ _ gd = ksU , λ y lt _ → covJ y (good-before y lt gd)

    ----------------------------------------------------------------------
    -- Each listed, with its row

    gen-back : ∀ l (r : Σ (Ev (AIE X)) (G l)) lv {m} → m ∈ gen l r lv → Good m × Σ (Ev (IE X)) (J m)
    gen-back l (out x , g) (u , pl) (here refl) =
      g-row g pl ([ ix 0 ] , refl) u , skip , JM.val (o-val g pl (proj₂ (acc g (u , pl))))
    gen-back l (out x , g) (u , pl) {m} (there i) = lane-back (of-row (at l ⊕ [ ix 1 ]) 0 (proj₂ s) i)
      where
        s = proj₁ (acc g (u , pl))
        ov′ = o-val g pl (proj₂ (acc g (u , pl)))
        lane-back : Σ (Ev (IE X)) (InE (ofᴱ (at l ⊕ [ ix 1 ]) 0 (proj₂ s)) m) → Good m × Σ (Ev (IE X)) (J m)
        lane-back (out v , r) = g-row g pl (⊑-trans ([ ix 1 ] , refl) (proj₁ (of-after r))) u , out v ,
          JM.lane ov′ tt ((r , of-reach (at l ⊕ [ ix 1 ]) 0 (proj₂ s) {m} {out v}) , proj₂ (of-after r)) (λ ()) tt
        lane-back (end , r) = g-row g pl (⊑-trans ([ ix 1 ] , refl) (proj₁ (of-after r))) u , skip ,
          JM.lpass ov′ tt ((r , of-reach (at l ⊕ [ ix 1 ]) 0 (proj₂ s) {m} {end}) , proj₂ (of-after r)) (λ ()) (λ ())
            (λ d → not-done g pl (proj₁ (proj₁ (of-after r))) (subst (Merge.Done F O) (proj₂ (proj₁ (of-after r))) d))
        lane-back (skip , r)  = ⊥-elim (of-skip (at l ⊕ [ ix 1 ]) 0 (proj₂ s) r)
        lane-back (pin _ , r) = ⊥-elim (ine-pin r)
    gen-back l (skip , g)  (u , pl) (here refl) =
      g-row g pl (⊑-refl _) u , skip , JM.step (o-skip g pl (few-ug u) (λ ()) (λ ()))
    gen-back l (pin _ , g) (u , pl) (here refl) =
      g-row g pl (⊑-refl _) u , skip , JM.step (o-skip g pl (few-ug u) (λ ()) (λ ()))
    gen-back l (end , g)   (u , pl) (here refl) =
      g-row g pl (⊑-refl _) u , end , JM.oend (o-end g pl) (done-at g pl)

    genAll-back : ∀ ks (b : Back ks) {m} → m ∈ genAll ks b → Good m × Σ (Ev (IE X)) (J m)
    genAll-back (k ∷ ks) b i with live? k
    ... | yes lv = [ gen-back k (b (here refl)) lv , genAll-back ks (λ j → b (there j)) ]′ (∈-++⁻ (gen k (b (here refl)) lv) i)
    ... | no _   = genAll-back ks (λ j → b (there j)) i

    late-back : ∀ l (r : Σ (Ev (AIE X)) (G l)) {m} → m ∈ late? l r → Good m × Σ (Ev (IE X)) (J m)
    late-back l (end , g) i with ug? l | T? (p′ <ᵖ l)
    late-back l (end , g) (here refl) | yes u | no np = g-late g cp refl u , end , JM.oend (o-late g cp) (done-late g cp)
      where cp = [ (λ h → h) , (λ h → ⊥-elim (np h)) ]′ (≼-or-≻ l p′)
    late-back l (end , g) () | yes _ | yes _
    late-back l (end , g) () | no _  | _

    lateAll-back : ∀ ks (b : Back ks) {m} → m ∈ lateAll ks b → Good m × Σ (Ev (IE X)) (J m)
    lateAll-back (k ∷ ks) b i =
      [ late-back k (b (here refl)) , lateAll-back ks (λ j → b (there j)) ]′ (∈-++⁻ (late? k (b (here refl))) i)

    backJ : ∀ {m} → m ∈ ksU → Good m × Σ (Ev (IE X)) (J m)
    backJ i = [ genAll-back ls back , lateAll-back ls back ]′ (∈-++⁻ (genAll ls back) i)

    -- EVERY LISTED POSITION HOLDS A READER ROW.
    backU : ∀ {m} → m ∈ ksU → Σ (Ev (IE X)) (U m)
    backU i with backJ i
    ... | gd , e , x = e , x , reachJ x gd
