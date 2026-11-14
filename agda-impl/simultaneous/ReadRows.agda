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
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (_×-dec_)

open import denotation.Position using (Pos; root; _≟ᵖ_; _⊕_; _<ᵖ_; sub; ix; last)
open import denotation.Events using (Timeline; fresh; ofᴱ)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Bare; Unpinned; EmissionSet; Den; Few; Reach; Truncate;
  Rejoin; shown; heard; ended; late; InE; LaneOf; _≺_; _≼_; module Scan; module Merge; module Op)
open import denotation.Laws.Modulus using (≺-irrefl; ≺-absurd; ≺-trans; ≺→≼; ≼-refl; ≼-trans; ≼-≺-≺; ≺-≼-≺; ≼-antisym; ≼-split; ≺-ext)
open import denotation.Laws.Worlds using (Lawful; _⊑_; ⊕-injˡ; ⊕-injʳ; ⊑-≼; ⊕-assoc; ⊕-identityʳ; ⊑-cmp; ⊑-snoc; ⊑-refl; ⊑-trans)
open import denotation.Laws.Worlds.Leaves using (module AccF; of-idx; of-row; of-in; of-reach; of-end-row; ine-pin)
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
