{-# OPTIONS --guardedness #-}

-- WHERE A LANE'S `laneDone` SITS (`lane-site`).  The lane fails its take at
-- the lane part's split of a frame value `v₂` whose scan step reads the
-- `laneDone`: the split shows the carries under its true lane, then the
-- `laneDone` under its false one.  Below `v₂`'s split, nothing else of the
-- lane lies before the `laneDone`: another frame value's split lies wholly
-- before or after it, the frame's rows lying flat, and the burst part's one
-- row lies in another subscription's world.  The scan's state there is the
-- fold of the frame's values before `v₂`, each shown by its own split's
-- false lane: the lane's rows before the split are those values' rows,
-- with the burst part's `burstEnd`, which counts nothing.
module simultaneous.LaneSite where

open import Data.Bool using (Bool; true; false; T; not; if_then_else_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; replicate)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_; s≤s; z≤n)
open import Data.Nat.Properties using (+-identityʳ; +-suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ; <ᵖ-apart)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; InE; at-out; at-end; on-out; _≺_; _≼_;
  Few; LaneOf; module Op; module Joining; module Bounded; module Merge; module Scan; module TakeWhile; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd; ≼-or-≻; ≼-split)
open import denotation.Laws.Worlds using (notT; Hots; GoodEnv; Ok; Lawful; InvAt; InvD; W⁼; inW; w-up; plain-ix; ok-in; ok-step; ⊕-injˡ; ⊕-injʳ; ⊕-identityʳ; ⊑-≼)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-rows; of-in; empty-inv; of-inv)
open import denotation.Laws.Count using (reach-down)
open import denotation.Laws.Connect using (module Apart)
open import denotation.Laws.JoinInv using (module Kids)
open import denotation.Laws using (good-cons)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (merge-out; bounded-out; hot-out)
open import simultaneous.LaneEndSched using (ls-one; of-one)
open import simultaneous.Layers using (to≺; from≺)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone; value; begin; over; stop; outerOpen; outerClose; carry; burstEnd; outerDone; subscribed; completed)
open import simultaneous.LaneLayers using (Under; acc-row; bd-lane-past; conn-few; few-row; few-tr; join-few; join-past; of-after; scan-few;
  under-ext; under-last; under-refl; under-trans; under-≺; under-⊕)
import simultaneous.LaneStart as LaneStart
open LaneStart using (z₀; module Core)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; count; laneˢ; laneSrc; laneStep; undone; marked; piece; shareˢ; counted; framed)

------------------------------------------------------------------------
-- A count folded over rows, in order

-- THE COUNT BEFORE `x`: the emits of `t`'s rows before it, folded in
-- order, each step the row just before the next.
data FoldOf {B : Set} (t : Pos → IE B → Set) : Pos → Routes → Set where
  f-none : ∀ {x} → (∀ {y v} → t y v → y ≺ x → ⊥) → FoldOf t x r₀
  f-step : ∀ {x y v r} → FoldOf t y r → t y v → y ≺ x
         → (∀ {y′ v′} → t y′ v′ → y ≺ y′ → y′ ≺ x → ⊥) → FoldOf t x (count r v)

fold-map : ∀ {B} {t t′ : Pos → IE B → Set} → (∀ {y v} → t y v → t′ y v) → (∀ {y v} → t′ y v → t y v)
         → ∀ {x r} → FoldOf t x r → FoldOf t′ x r
fold-map to from (f-none no)         = f-none λ r lt → no (from r) lt
fold-map to from (f-step F r lt btw) = f-step (fold-map to from F) (to r) lt λ r′ a b → btw (from r′) a b

-- A fold reaches past a gap holding no row.
fold-ext : ∀ {B} {t : Pos → IE B → Set} {x x′ r} → FoldOf t x r → x ≼ x′ → (∀ {y v} → t y v → x ≼ y → y ≺ x′ → ⊥) → FoldOf t x′ r
fold-ext {x = x} (f-none no) xx′ gap = f-none λ {y} r lt → [ (λ xy → gap r xy lt) , (λ yx → no r yx) ]′ (≼-or-≻ x y)
fold-ext {x = x} {x′} (f-step {y = y} F r lt btw) xx′ gap =
  f-step F r (≺-≼-≺ {y} {x} {x′} lt xx′) λ {y′} r′ a b → [ (λ xy′ → gap r′ xy′ b) , (λ y′x → btw r′ a y′x) ]′ (≼-or-≻ x y′)

-- A ROW THAT COUNTS NOTHING JOINS A FOLD where it falls.
insert : ∀ {B} {t : Pos → IE B → Set} (yb : Pos) (nb : IE B) → (∀ r → count r nb ≡ r)
       → ∀ {x r} → FoldOf (λ y v → t y v × (y ≡ yb → ⊥)) x r → (yb ≺ x → t yb nb) → FoldOf t x r
insert {t = t} yb nb neu {x} (f-none no) has with ≼-or-≻ x yb
... | inj₁ xyb = f-none λ {y} r lt → no (r , λ eq → xyb (subst (_≺ x) eq lt)) lt
... | inj₂ ybx = subst (FoldOf t x) (neu r₀)
      (f-step (f-none λ {y} r lt → no (r , λ eq → ≺-irrefl {yb} (subst (_≺ yb) eq lt)) (≺-trans {y} {yb} {x} lt ybx)) (has ybx) ybx
              λ r′ a b → no (r′ , λ eq → ≺-irrefl {yb} (subst (yb ≺_) eq a)) b)
insert {t = t} yb nb neu {x} (f-step {y = y} {v} {r} F (row , _) lt btw) has with ≼-or-≻ x yb
... | inj₁ xyb = f-step IH row lt λ r′ a b → btw (r′ , λ eq → xyb (subst (_≺ x) eq b)) a b
  where IH = insert yb nb neu F λ ybY → has (≺-trans {yb} {y} {x} ybY lt)
... | inj₂ ybx with ≼-or-≻ yb y
...   | inj₁ yby = f-step IH row lt λ r′ a b → btw (r′ , λ eq → yby (subst (y ≺_) eq a)) a b
  where IH = insert yb nb neu F λ ybY → has (≺-trans {yb} {y} {x} ybY lt)
...   | inj₂ yyb = subst (FoldOf t x) (neu (count r v))
          (f-step (f-step IH row yyb λ {y′} r′ a b → btw (r′ , λ eq → ≺-irrefl {yb} (subst (_≺ yb) eq b)) a (≺-trans {y′} {yb} {x} b ybx))
                  (has ybx) ybx λ {y′} r′ a b → btw (r′ , λ eq → ≺-irrefl {yb} (subst (yb ≺_) eq a)) (≺-trans {y} {yb} {y′} yyb a) b)
  where IH = insert yb nb neu F λ ybY → has (≺-trans {yb} {y} {x} ybY lt)

------------------------------------------------------------------------
-- The scan's split, row by row

rep-at : ∀ {X : Set} p (c : X) k j {i} → i < k → InE (ofᴱ p j (replicate k c)) (p ⊕ [ ix (j + i) ]) (out c)
rep-at p c (suc k) j {zero}  _        = subst (λ n → InE (ofᴱ p j (replicate (suc k) c)) (p ⊕ [ ix n ]) (out c)) (sym (+-identityʳ j)) at-out
rep-at p c (suc k) j {suc i} (s≤s lt) =
  on-out (subst (λ n → InE (ofᴱ p (suc j) (replicate k c)) (p ⊕ [ ix n ]) (out c)) (sym (+-suc j i)) (rep-at p c k (suc j) lt))

rep-view : ∀ {X : Set} p (c : X) k j {y v} → InE (ofᴱ p j (replicate k c)) y (out v) → Σ ℕ λ i → i < k × y ≡ p ⊕ [ ix (j + i) ] × v ≡ c
rep-view p c zero    j ()
rep-view p c (suc k) j at-out     = 0 , s≤s z≤n , cong (λ n → p ⊕ [ ix n ]) (sym (+-identityʳ j)) , refl
rep-view p c (suc k) j (on-out r) with rep-view p c k (suc j) r
... | i , lt , refl , refl = suc i , s≤s lt , cong (λ n → p ⊕ [ ix n ]) (sym (+-suc j i)) , refl

-- A scan step ends the lane, or counts its value and shows it alone.
ls-view : ∀ {X} (st : Routes × (List (IE X) × List (IE X))) a
        → (Σ Pos λ n → a ≡ instEmit (mark laneDone) n) ⊎ (T (undone a) × laneStep st a ≡ (count (proj₁ st) a , ([] , a ∷ [])))
ls-view st (instEmit (value _) _)      = inj₂ (tt , refl)
ls-view st (instEmit (mark begin) _)      = inj₂ (tt , refl)
ls-view st (instEmit (mark over) _)       = inj₂ (tt , refl)
ls-view st (instEmit (mark stop) _)       = inj₂ (tt , refl)
ls-view st (instEmit (mark outerOpen) _)  = inj₂ (tt , refl)
ls-view st (instEmit (mark outerClose) _) = inj₂ (tt , refl)
ls-view st (instEmit (mark laneStart) _)  = inj₂ (tt , refl)
ls-view st (instEmit (mark carry) _)      = inj₂ (tt , refl)
ls-view st (instEmit (mark laneDone) n)   = inj₁ (n , refl)
ls-view st (instEmit (mark burstEnd) _)   = inj₂ (tt , refl)
ls-view st (instEmit (mark outerDone) _)  = inj₂ (tt , refl)
ls-view st (instEmit (mark subscribed) _) = inj₂ (tt , refl)
ls-view st (instEmit (mark completed) _)  = inj₂ (tt , refl)

cnt : ∀ {X} (st : Routes × (List (IE X) × List (IE X))) a → T (undone a) → proj₁ (laneStep st a) ≡ count (proj₁ st) a
cnt st a u with ls-view st a
... | inj₁ (n , refl) = ⊥-elim u
... | inj₂ (_ , eq)   = cong proj₁ eq

-- WHAT A SPLIT SHOWS: the step's value under its false lane, or a carry
-- under its true one, the step's read then a `laneDone`.
split-row : ∀ {X} (st : Routes × (List (IE X) × List (IE X))) a {U w c y e} → InE (ofᴱ U 0 (true ∷ false ∷ [])) w (out c)
          → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ (laneStep st a)) else proj₂ (proj₂ (laneStep st a)))) y (out e)
          → (y ≡ ((U ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ] × e ≡ a)
            ⊎ (Σ ℕ λ i → Σ Pos λ n → y ≡ ((U ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix i ] × i < proj₂ (proj₁ st) × e ≡ marked carry × a ≡ instEmit (mark laneDone) n)
split-row st a (on-out at-out) l with of-one _ a (subst (λ xs → InE (ofᴱ _ 0 xs) _ (out _)) (ls-one st a) l)
... | refl , refl = inj₁ (refl , refl)
split-row st a at-out l with ls-view st a
... | inj₁ (n , refl) = let (i , lt , ey , ee) = rep-view _ (marked carry) (proj₂ (proj₁ st)) 0 l in inj₂ (i , n , ey , lt , ee , refl)
... | inj₂ (_ , eq)   = ⊥-elim (nil (subst (λ z → InE (ofᴱ _ 0 (proj₁ (proj₂ z))) _ (out _)) eq l))
  where
    nil : ∀ {X : Set} {p y} {e : X} → InE (ofᴱ p 0 []) y (out e) → ⊥
    nil ()
split-row st a (on-out (on-out ())) _

-- A split has few rows.
inner-few : ∀ {X} (y : Routes × (List (IE X) × List (IE X))) U v
          → Few (Merge.JoinT (λ c → Op.of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (enter (Op.of (true ∷ false ∷ [])) U)) v
inner-few y U v = join-few (few-tr (ofF U (true ∷ false ∷ []))) (kt ++ kf , hl) ([] , λ ())
  where
    ofF : ∀ {Z : Set} p (xs : List Z) → Few (InE (ofᴱ p 0 xs)) v
    ofF p xs = of-rows p 0 xs , λ x _ → of-in p 0 xs x

    kt kf : List Pos
    kt = of-rows ((U ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) 0 (proj₁ (proj₂ y))
    kf = of-rows ((U ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) 0 (proj₂ (proj₂ y))

    hl : ∀ {q c k e} → enter (Op.of (true ∷ false ∷ [])) U q (out c)
       → LaneOf (λ c → Op.of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) q c k e → k ≺ v → k ∈ kt ++ kf
    hl (at-out , _)             (l , _) _ = ∈-++⁺ˡ (of-in _ 0 _ (proj₁ l))
    hl (on-out at-out , _)      (l , _) _ = ∈-++⁺ʳ kt (of-in _ 0 _ (proj₁ l))
    hl (on-out (on-out ()) , _) _ _

under-≼ : ∀ {x y} → Under x y → x ≼ y
under-≼ u = ⊑-≼ u

undone-false : ∀ {X} (a : IE X) → T (undone a) → T (not (undone a)) → ⊥
undone-false a u nu = notT (undone a) nu u

------------------------------------------------------------------------
-- The site, over the lane's layers

-- What a lane's `laneDone` at `yd` sits past, read in one emission set.
record Sited {B : Set} (t : EmissionSet (IE B)) (yd : Pos) : Set where
  field
    w base  : Pos
    r       : Routes
    w-yd    : Under w yd
    w-base  : Under w base
    carries : ∀ {i} → i < proj₂ r → t (base ⊕ [ ix i ]) (out (marked carry)) × (base ⊕ [ ix i ]) ≺ yd
    only    : ∀ {y v} → t y (out v) → Under w y → y ≺ yd → Σ ℕ λ i → i < proj₂ r × y ≡ base ⊕ [ ix i ]
    fold    : FoldOf (λ y v → t y (out v)) w r

module Site {B : Set} (SH : Part → Den ⊤ → Den (IE B)) (PC : Part → ℕ → Den ⊤ → Den (IE B) → Den (IE B))
  (pc0    : ∀ h h′ s → enter (PC lanePart 0 h h′) s (s ⊕ [ ix 0 ]) (out (marked laneStart)))
  (pc0-at : ∀ k h h′ s {y a} → enter (PC k 0 h h′) s y (out a) → y ≡ s ⊕ [ ix 0 ] × T (undone a))
  (pc1    : ∀ k h h′ s {y a} → enter (PC k 1 h h′) s y (out a) → enter h′ s y (out a))
  (pc2    : ∀ h h′ s {y a} → enter (PC burstPart 2 h h′) s y (out a) → ⊥)
  (sh-b   : ∀ h p {y a} → enter (SH burstPart h) p y (out a) → ⊥)
  (pc0-b  : ∀ h h′ s {y n} → enter (PC burstPart 0 h h′) s y (out (instEmit (mark laneStart) n)) → ⊥)
  (pc2-l  : ∀ h h′ s {y n} → enter (PC lanePart 2 h h′) s y (out (instEmit (mark laneStart) n)) → ⊥)
  (pc0-rows : ∀ k h h′ s {y e} → enter (PC k 0 h h′) s y e → y ≡ s ⊕ [ ix 0 ] ⊎ y ≡ s ⊕ [ last ])
  (pc0-ls   : ∀ h h′ s {y a} → enter (PC lanePart 0 h h′) s y (out a) → a ≡ marked laneStart)
  (pc0-be   : ∀ h h′ s {y a} → enter (PC burstPart 0 h h′) s y (out a) → a ≡ marked burstEnd)
  (sh-past  : ∀ k h p {y e} → enter (SH k h) p y e → p ≺ y)
  -- The burst part's first piece shows its mark at its first child.
  (pc0b     : ∀ h h′ s → enter (PC burstPart 0 h h′) s (s ⊕ [ ix 0 ]) (out (marked burstEnd))) where
  open Core SH PC pc0 pc0-at pc1 pc2 sh-b pc0-b pc2-l pc0-rows pc0-ls pc0-be sh-past public

  St : Set
  St = Routes × (List (IE B) × List (IE B))

  ----------------------------------------------------------------------
  -- The burst part's one row

  module FrB (P : Pos) where
    h₁ : Den ⊤
    h₁ = H₁ P

    h₂ : Den (IE B)
    h₂ = H₂ P burstPart

    open Frame burstPart h₁ h₂ (Bp P) using (O; f; ob₀; nth₀; S₀; sb₀; V₀; u-V₀; nth-zero; starts-0; fr-min; fr-few) public

    FrEb : EmissionSet (IE B)
    FrEb = enter (Fr burstPart h₁ h₂) (Bp P)

    ScEb : EmissionSet St
    ScEb = enter (Sc burstPart h₁ h₂) (Bp P)

    -- The burst part's frame shows its first piece's mark, and nothing else.
    fb-row : ∀ {y a} → FrEb y (out a) → y ≡ V₀ × a ≡ marked burstEnd
    fb-row r with bounded-out 1 f (Op.of (0 ∷ 1 ∷ 2 ∷ [])) (Bp P) r
    ... | _ , _ , _ , _ , oq , sb , (l , _) = go oq sb l
      where
        go : ∀ {q j i s y a} → O q (out j) → Bounded.Sub 1 f O i q s j → enter (f j) s y (out a) → y ≡ V₀ × a ≡ marked burstEnd
        go (at-out , _) (nth , st) l with nth-zero nth
        ... | refl with starts-0 st
        ...   | refl = proj₁ (pc0-at burstPart h₁ h₂ S₀ l) , pc0-be h₁ h₂ S₀ l
        go {s = s} (on-out at-out , _) _ l = ⊥-elim (sh-b h₁ _ (proj₁ (proj₁ (proj₂ (hot-out (pc1 burstPart h₁ h₂ s l))))))
        go {s = s} (on-out (on-out at-out) , _) _ l = ⊥-elim (pc2 h₁ h₂ s l)
        go (on-out (on-out (on-out ())) , _) _ _

    acc-b : ∀ {v b} → Scan.Acc laneStep z₀ FrEb v b → v ≡ V₀ × b ≡ laneStep z₀ (marked burstEnd)
    acc-b (Scan.acc₀ x _) with fb-row x
    ... | refl , refl = refl , refl
    acc-b (Scan.acc a x lt _) with fb-row (proj₂ (acc-row a)) | fb-row x
    ... | refl , _ | refl , _ = ⊥-elim (≺-irrefl {V₀} lt)

    yst : St
    yst = laneStep z₀ (marked burstEnd)

    W₀ Ib : Pos
    W₀ = V₀ ⊕ [ ix 1 ]
    Ib = ((W₀ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    u-V₀I : Under V₀ Ib
    u-V₀I = under-⊕ (under-⊕ (under-⊕ (under-⊕ (under-refl V₀) (ix 1)) (ix 1)) (ix 1)) (ix 0)

    u-Bp : Under (Bp P) Ib
    u-Bp = under-trans (under-⊕ (under-refl (Bp P)) (ix 0)) (under-trans u-V₀ u-V₀I)

    u-P : Under (P ⊕ [ ix 0 ]) Ib
    u-P = under-trans (under-⊕ (under-refl (P ⊕ [ ix 0 ])) (ix 0)) u-Bp

    sc-few : ∀ {v} → Under V₀ v → Few (Scan.ScanT laneStep z₀ FrEb) v
    sc-few uv = scan-few laneStep z₀ FrEb (few-tr (fr-few uv))

    ct-few : Few (Merge.JoinT Inner ScEb) Ib
    ct-few = join-few (few-tr (sc-few u-V₀I)) (proj₁ (inner-few yst W₀ Ib) , hl) ([] , λ ())
      where
        hl : ∀ {q y k e} → ScEb q (out y) → LaneOf Inner q y k e → k ≺ Ib → k ∈ proj₁ (inner-few yst W₀ Ib)
        hl (Scan.sval a , _) (l , _) lt with acc-b a
        ... | refl , refl = proj₂ (inner-few yst W₀ Ib) (proj₁ l) lt

    in-few : Few (Connecting.ConnT (P ⊕ [ ix 0 ]) (enter (SH burstPart h₁) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) (enter (Ct burstPart h₁ h₂) (Bp P))) Ib
    in-few = conn-few (P ⊕ [ ix 0 ]) (enter (SH burstPart h₁) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])) (enter (Ct burstPart h₁ h₂) (Bp P))
               (λ {y} x → ≺-trans {Ib} {(P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]} {y} (under-≺ (P ⊕ [ ix 0 ]) (s≤s z≤n) u-Bp) (sh-past burstPart h₁ ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) x))
               (few-tr ct-few)

    sv-few : Few (Connecting.ConnT P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (SH burstPart h₁) (λ h′ → Ct burstPart h₁ h′)) (P ⊕ [ ix 0 ]))) Ib
    sv-few = conn-few P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (SH burstPart h₁) (λ h′ → Ct burstPart h₁ h′)) (P ⊕ [ ix 0 ])) past (few-tr in-few)
      where
        past : ∀ {y e} → enter Op.empty (P ⊕ [ ix 1 ]) y e → Ib ≺ y
        past (at-end , _) = ≺-trans {Ib} {P ⊕ [ ix 1 ]} {(P ⊕ [ ix 1 ]) ⊕ [ last ]} (under-≺ P (s≤s z≤n) u-P) (≺-ext (P ⊕ [ ix 1 ]) [])

    fr-row : FrEb V₀ (out (marked burstEnd))
    fr-row = few-row (Joining.lane ob₀ (0 , 0 , nth₀) (0 , S₀ , sb₀ , (pc0b h₁ h₂ S₀ , ≺-ext S₀ [])) (λ ()) tt) (fr-few (under-refl V₀))

    sc-row : ScEb V₀ (out yst)
    sc-row = few-row (Scan.sval (Scan.acc₀ fr-row fr-min)) (sc-few (under-refl V₀))

    in-row : enter (Inner yst) W₀ Ib (out (marked burstEnd))
    in-row = few-row (Joining.lane (on-out at-out , of-reach W₀ 0 (true ∷ false ∷ []) {W₀ ⊕ [ ix 1 ]} {out false}) tt
                       ((at-out , of-reach ((W₀ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) 0 (marked burstEnd ∷ []) {Ib} {out (marked burstEnd)}) , ≺-ext ((W₀ ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) [])
                       (λ ()) tt)
                     (inner-few yst W₀ Ib)

    ct-row : enter (Ct burstPart h₁ h₂) (Bp P) Ib (out (marked burstEnd))
    ct-row = few-row (Joining.lane sc-row tt (in-row , under-ext W₀ (under-⊕ (under-⊕ (under-refl (W₀ ⊕ [ ix 1 ])) (ix 1)) (ix 0))) (λ ()) tt) ct-few

    -- THE BURST PART'S `burstEnd`, a row of its connect.
    sv-row : enter (Sv burstPart) P Ib (out (marked burstEnd))
    sv-row = few-row (Connecting.body (few-row (Connecting.body ct-row) in-few)) sv-few

    P≺Ib : P ≺ Ib
    P≺Ib = under-ext P u-P

  ----------------------------------------------------------------------
  -- The lane at `s`

  module At (s : Pos) where
    K Kb P Pb FB : Pos
    K  = s ⊕ [ ix 0 ]
    Kb = s ⊕ [ ix 1 ]
    P  = K ⊕ [ ix 1 ]
    Pb = Kb ⊕ [ ix 1 ]
    FB = Bp P

    h₁ : Den ⊤
    h₁ = H₁ P

    h₂ : Den (IE B)
    h₂ = H₂ P lanePart

    FrE : EmissionSet (IE B)
    FrE = enter (Fr lanePart h₁ h₂) FB

    ScE : EmissionSet St
    ScE = enter (Sc lanePart h₁ h₂) FB

    SvE SbE MME LDE : EmissionSet (IE B)
    SvE = enter (Sv lanePart) P
    SbE = enter (Sv burstPart) Pb
    MME = enter MM s
    LDE = enter LaneD s

    OS : EmissionSet Part
    OS = enter (Op.of (lanePart ∷ burstPart ∷ [])) s

    okK : OS K (out lanePart)
    okK = at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {K} {out lanePart}

    okKb : OS Kb (out burstPart)
    okKb = on-out at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {Kb} {out burstPart}

    open FrB Pb using (Ib; sv-row; P≺Ib)

    Ac : Pos → St → Set
    Ac = Scan.Acc laneStep z₀ FrE

    pre : ∀ {v b} → Ac v b → St
    pre (Scan.acc₀ _ _)            = z₀
    pre (Scan.acc {b = b} _ _ _ _) = b

    val : ∀ {v b} → Ac v b → IE B
    val (Scan.acc₀ {a = a} _ _)       = a
    val (Scan.acc {a′ = a} _ _ _ _)   = a

    val-row : ∀ {v b} (ac : Ac v b) → FrE v (out (val ac))
    val-row (Scan.acc₀ x _)    = x
    val-row (Scan.acc _ x _ _) = x

    b-eq : ∀ {v b} (ac : Ac v b) → b ≡ laneStep (pre ac) (val ac)
    b-eq (Scan.acc₀ _ _)    = refl
    b-eq (Scan.acc _ _ _ _) = refl

    U Bs I : Pos → Pos
    U v  = v ⊕ [ ix 1 ]
    Bs v = (U v ⊕ [ ix 0 ]) ⊕ [ ix 1 ]
    I v  = ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]

    u-vU : ∀ v → Under v (U v)
    u-vU v = under-⊕ (under-refl v) (ix 1)

    u-UI : ∀ v → Under (U v) (I v)
    u-UI v = under-⊕ (under-⊕ (under-⊕ (under-refl (U v)) (ix 1)) (ix 1)) (ix 0)

    u-UB : ∀ v i → Under (U v) (Bs v ⊕ [ ix i ])
    u-UB v i = under-⊕ (under-⊕ (under-⊕ (under-refl (U v)) (ix 0)) (ix 1)) (ix i)

    U≺I : ∀ v → U v ≺ I v
    U≺I v = under-ext (U v) (under-⊕ (under-⊕ (under-refl (U v ⊕ [ ix 1 ])) (ix 1)) (ix 0))

    U≺B : ∀ v i → U v ≺ (Bs v ⊕ [ ix i ])
    U≺B v i = under-ext (U v) (under-⊕ (under-⊕ (under-refl (U v ⊕ [ ix 0 ])) (ix 1)) (ix i))

    B≺I : ∀ v i → (Bs v ⊕ [ ix i ]) ≺ I v
    B≺I v i = ≺-trans {Bs v ⊕ [ ix i ]} {U v ⊕ [ ix 1 ]} {I v}
                (under-≺ (U v) {0} {1} (s≤s z≤n) (under-⊕ (under-⊕ (under-refl (U v ⊕ [ ix 0 ])) (ix 1)) (ix i)))
                (under-ext (U v ⊕ [ ix 1 ]) (under-⊕ (under-refl ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ])) (ix 0)))

    -- The frame's rows lie past the lane part's connect.
    P≺U : ∀ {v e} → FrE v e → P ≺ U v
    P≺U {v} x = ≺-trans {P} {FB} {U v} (≺-trans {P} {P ⊕ [ ix 0 ]} {FB} (≺-ext P []) (≺-ext (P ⊕ [ ix 0 ]) []))
                  (≺-trans {FB} {v} {U v} (join-past {p = FB} (of-after FB (0 ∷ 1 ∷ 2 ∷ [])) (λ _ → bd-lane-past) (λ ()) (proj₁ x)) (≺-ext v []))

    -- A step's value, at its split's false lane.
    inner-row : ∀ {v b} (ac : Ac v b) → enter (Inner b) (U v) (I v) (out (val ac))
    inner-row {v} {b} ac =
      few-row (Joining.lane (on-out at-out , of-reach (U v) 0 (true ∷ false ∷ []) {U v ⊕ [ ix 1 ]} {out false}) tt
                 (lrow , ≺-ext ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) []) (λ ()) tt)
              (inner-few b (U v) (I v))
      where
        fl : proj₂ (proj₂ b) ≡ val ac ∷ []
        fl = trans (cong (λ z → proj₂ (proj₂ z)) (b-eq ac)) (ls-one (pre ac) (val ac))

        lrow : enter (Op.of (proj₂ (proj₂ b))) ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (I v) (out (val ac))
        lrow = subst (λ xs → enter (Op.of xs) ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) (I v) (out (val ac))) (sym fl)
                 (at-out , of-reach ((U v ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) 0 (val ac ∷ []) {I v} {out (val ac)})

    -- A `laneDone` step's carries, at its split's true lane.
    carry-row : ∀ {v b} (ac : Ac v b) {n} → val ac ≡ instEmit (mark laneDone) n → ∀ {i} → i < proj₂ (proj₁ (pre ac))
              → enter (Inner b) (U v) (Bs v ⊕ [ ix i ]) (out (marked carry))
    carry-row {v} {b} ac {n} vd {i} lt =
      few-row (Joining.lane (at-out , of-reach (U v) 0 (true ∷ false ∷ []) {U v ⊕ [ ix 0 ]} {out true}) tt
                 (lrow , ≺-ext (Bs v) []) (λ ()) tt)
              (inner-few b (U v) (Bs v ⊕ [ ix i ]))
      where
        fc : proj₁ (proj₂ b) ≡ replicate (proj₂ (proj₁ (pre ac))) (marked carry)
        fc = trans (cong (λ z → proj₁ (proj₂ z)) (b-eq ac)) (cong (λ a → proj₁ (proj₂ (laneStep (pre ac) a))) vd)

        lrow : enter (Op.of (proj₁ (proj₂ b))) (Bs v) (Bs v ⊕ [ ix i ]) (out (marked carry))
        lrow = subst (λ xs → enter (Op.of xs) (Bs v) (Bs v ⊕ [ ix i ]) (out (marked carry))) (sym fc)
                 (rep-at (Bs v) (marked carry) (proj₂ (proj₁ (pre ac))) 0 lt , of-reach (Bs v) 0 _ {Bs v ⊕ [ ix i ]} {out (marked carry)})

    -- WHAT THE LANE PART'S CONNECT SHOWS: a frame value's step, under its
    -- split's false lane, or a carry under its true one.
    View : Pos → IE B → Set
    View y e = Σ Pos λ v → Σ St λ b → Σ (Ac v b) λ ac → ScE v (out b)
             × ((y ≡ I v × e ≡ val ac)
                ⊎ (Σ ℕ λ i → Σ Pos λ n → y ≡ Bs v ⊕ [ ix i ] × i < proj₂ (proj₁ (pre ac)) × e ≡ marked carry × val ac ≡ instEmit (mark laneDone) n))

    -- A split's row, read without normalising the layers above it.
    Spl : Pos → St → Pos → IE B → Set
    Spl u b y e = Σ Pos λ w → Σ Bool λ c → enter (Op.of (true ∷ false ∷ [])) u w (out c)
                × enter (Op.of (if c then proj₁ (proj₂ b) else proj₂ (proj₂ b))) (w ⊕ [ ix 1 ]) y (out e) × (w ⊕ [ ix 1 ]) ≺ y

    spl : ∀ b u {y e} → enter (Inner b) u y (out e) → Spl u b y e
    spl b u r = merge-out (λ c → Op.of (if c then proj₁ (proj₂ b) else proj₂ (proj₂ b))) (Op.of (true ∷ false ∷ [])) u r

    img-sp : ∀ {v b y e} (ac : Ac v b) → ScE v (out b) → Spl (U v) b y e → View y e
    img-sp {v} {b} {y} {e} ac scr (w , c , ow , ll , _) = v , b , ac , scr ,
      split-row (pre ac) (val ac) (proj₁ ow)
        (subst (λ z → InE (ofᴱ (w ⊕ [ ix 1 ]) 0 (if c then proj₁ (proj₂ z) else proj₂ (proj₂ z))) y (out e)) (b-eq ac) (proj₁ ll))

    img-sc : ∀ {y e} → Σ Pos (λ v → Σ St λ b → ScE v (out b) × enter (Inner b) (U v) y (out e) × U v ≺ y) → View y e
    img-sc (v , b , scr@(Scan.sval ac , _) , inr , _) = img-sp ac scr (spl b (U v) inr)

    img : ∀ {y e} → SvE y (out e) → View y e
    img r = img-sc (merge-out Inner (Sc lanePart h₁ h₂) FB (sv-out lanePart P r))

    -- The burst part's connect shows its `burstEnd`, alone.
    bo-sp : ∀ {y a} → Spl (U (FrB.V₀ Pb)) (laneStep z₀ (marked burstEnd)) y a → y ≡ Ib × a ≡ marked burstEnd
    bo-sp (w , c , ow , ll , _) with split-row z₀ (marked burstEnd) (proj₁ ow) (proj₁ ll)
    ... | inj₁ (refl , refl) = refl , refl
    ... | inj₂ (_ , _ , _ , _ , _ , ())

    bo-ac : ∀ {v b y a} → Scan.Acc laneStep z₀ (FrB.FrEb Pb) v b → enter (Inner b) (U v) y (out a) → y ≡ Ib × a ≡ marked burstEnd
    bo-ac {v} {b} ac inr with FrB.acc-b Pb ac
    ... | refl , refl = bo-sp (spl b (U v) inr)

    bo-sc : ∀ {y a} → Σ Pos (λ v → Σ St λ b → FrB.ScEb Pb v (out b) × enter (Inner b) (U v) y (out a) × U v ≺ y) → y ≡ Ib × a ≡ marked burstEnd
    bo-sc (v , b , (Scan.sval ac , _) , inr , _) = bo-ac ac inr

    burst-only : ∀ {y a} → SbE y (out a) → y ≡ Ib × a ≡ marked burstEnd
    burst-only r = bo-sc (merge-out Inner (Sc burstPart (H₁ Pb) (H₂ Pb burstPart)) (Bp Pb) (sv-out burstPart Pb r))

    -- The lanes' merge shows a part's connect.
    mm-at : ∀ {y e} → Σ Pos (λ q → Σ Part λ k → OS q (out k) × enter (Sv k) (q ⊕ [ ix 1 ]) y (out e) × (q ⊕ [ ix 1 ]) ≺ y)
          → (SvE y (out e) × P ≺ y) ⊎ (SbE y (out e) × Pb ≺ y)
    mm-at (_ , _ , (at-out , _) , svr , lt)          = inj₁ (svr , lt)
    mm-at (_ , _ , (on-out at-out , _) , svr , lt)   = inj₂ (svr , lt)
    mm-at (_ , _ , (on-out (on-out ()) , _) , _ , _)

    mm-anat : ∀ {y e} → MME y (out e) → (SvE y (out e) × P ≺ y) ⊎ (SbE y (out e) × Pb ≺ y)
    mm-anat r = mm-at (merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r)

    -- The frame's rows lie flat, one value at each, and the burst part's
    -- rows lie apart from the lane part's.
    module Hyp (ff : ∀ {y e l ys e′} → FrE y e → FrE (y ⊕ (l ∷ ys)) e′ → ⊥)
               (fu : ∀ {y e e′} → FrE y e → FrE y e′ → e ≡ e′)
               (ap : ∀ {u a y′ a′} → SvE (((u ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out a) → SbE y′ (out a′) → P ≺ u → Under u y′ → ⊥) where

      -- Below an earlier frame value lies before a later one.
      beyond : ∀ {v v′ e e′} → FrE v e → FrE v′ e′ → v ≺ v′ → ∀ zs → (v ⊕ zs) ≺ v′
      beyond {v} {v′} {e′ = e′} x x′ lt zs = to≺ (v ⊕ zs) v′ (<ᵖ-apart v v′ zs (from≺ v v′ lt) ne)
        where
          ne : ∀ ys → v′ ≡ v ⊕ ys → ⊥
          ne []       eq = ≺-irrefl {v} (subst (v ≺_) (trans eq (⊕-identityʳ v)) lt)
          ne (l ∷ ys) eq = ff x (subst (λ z → FrE z e′) eq x′)

      far : ∀ {v v′ e e′ y y′} → FrE v e → FrE v′ e′ → v ≺ v′ → Under v y → Under v′ y′ → y ≺ y′
      far {v} {v′} {y′ = y′} x x′ lt (zs , refl) uy′ = ≺-≼-≺ {v ⊕ zs} {v′} {y′} (beyond x x′ lt zs) (under-≼ uy′)

      out-inj : ∀ {a a′ : IE B} → out a ≡ out a′ → a ≡ a′
      out-inj refl = refl

      -- One fold at each frame value.
      pre-val : ∀ {v b b′} (ac : Ac v b) (ac′ : Ac v b′) → pre ac ≡ pre ac′ × val ac ≡ val ac′
      pre-val (Scan.acc₀ x _)    (Scan.acc₀ x′ _)     = refl , out-inj (fu x x′)
      pre-val (Scan.acc₀ _ mn)   (Scan.acc a _ lt _)  = ⊥-elim (mn (proj₂ (acc-row a)) lt)
      pre-val (Scan.acc a _ lt _) (Scan.acc₀ _ mn)    = ⊥-elim (mn (proj₂ (acc-row a)) lt)
      pre-val {v} (Scan.acc {q = q₀} a x lt nx) (Scan.acc {q = q₁} a′ x′ lt′ nx′) with same
        where
          same : q₀ ≡ q₁
          same with ≼-or-≻ q₀ q₁
          ... | inj₂ q₁q₀ = ⊥-elim (nx′ (proj₂ (acc-row a)) q₁q₀ lt)
          ... | inj₁ q₀q₁ with ≼-split {q₀} {q₁} q₀q₁
          ...   | inj₁ lt₀ = ⊥-elim (nx (proj₂ (acc-row a′)) lt₀ lt′)
          ...   | inj₂ eq  = eq
      ... | refl = let (pe , ve) = pre-val a a′ in trans (b-eq a) (trans (cong₂ laneStep pe ve) (sym (b-eq a′))) , out-inj (fu x x′)

      -- THE SPLIT OF `v₂`'S `laneDone`, and the layers above it.
      module Chain {v₂ b₂} (ac₂ : Ac v₂ b₂) {n} (vd : val ac₂ ≡ instEmit (mark laneDone) n) (scr : ScE v₂ (out b₂))
                   (svq : SvE (I v₂) (out (instEmit (mark laneDone) n))) (mmq : MME (I v₂) (out (instEmit (mark laneDone) n)))
                   (ldq : LDE (I v₂ ⊕ [ ix 0 ]) (out (instEmit (mark laneDone) n)))
                   (nF : ¬ TakeWhile.Failed true undone MME (I v₂)) where
        q₂ yd : Pos
        q₂ = I v₂
        yd = q₂ ⊕ [ ix 0 ]

        q≺yd : q₂ ≺ yd
        q≺yd = ≺-ext q₂ []

        u-yd : Under v₂ yd
        u-yd = under-⊕ (under-trans (u-vU v₂) (u-UI v₂)) (ix 0)

        ctq : enter (Ct lanePart h₁ h₂) FB q₂ (out (instEmit (mark laneDone) n))
        ctq = sv-out lanePart P svq

        -- Each layer shows, before the split, what the layer below does.
        ct-up : ∀ {v b y e} → ScE v (out b) → enter (Inner b) (U v) y (out e) → U v ≺ y → y ≺ q₂ → enter (Ct lanePart h₁ h₂) FB y (out e)
        ct-up {y = y} {e} sc inr uy yq = Joining.lane sc tt (inr , uy) (λ ()) tt , reach-down {q = q₂} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ ctq) yq tt

        sv-up : ∀ {y e} → enter (Ct lanePart h₁ h₂) FB y (out e) → y ≺ q₂ → SvE y (out e)
        sv-up {y} {e} ct yq = Connecting.body (Connecting.body ct , reach-down {q = q₂} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ (mid-out lanePart P svq)) yq tt)
                    , reach-down {q = q₂} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ svq) yq tt

        mm-up : ∀ {y e} → SvE y (out e) → P ≺ y → y ≺ q₂ → MME y (out e)
        mm-up {y} {e} sv Py yq = Joining.lane okK tt (sv , Py) (λ ()) tt , reach-down {q = q₂} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ mmq) yq tt

        mb-up : ∀ {y e} → SbE y (out e) → Pb ≺ y → y ≺ q₂ → MME y (out e)
        mb-up {y} {e} sb Py yq = Joining.lane okKb tt (sb , Py) (λ ()) tt , reach-down {q = q₂} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ mmq) yq tt

        ld-up : ∀ {y e} → MME y (out e) → T (undone e) → y ≺ q₂ → LDE y (out e)
        ld-up {y} {e} mm kp yq = TakeWhile.pass mm kp (λ (q′ , a′ , x′ , nk′ , lt′) → nF (q′ , a′ , x′ , nk′ , ≺-trans {q′} {y} {q₂} lt′ yq))
                           , reach-down {q = yd} {w = y} {e = out (instEmit (mark laneDone) n)} {e₁ = out e} (proj₂ ldq) (≺-trans {y} {q₂} {yd} yq q≺yd) tt

        sc-at : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → ScE v (out b)
        sc-at {v} {b} ac lt = Scan.sval ac , reach-down {q = v₂} {w = v} {e = out b₂} {e₁ = out b} (proj₂ scr) lt tt

        Iq : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → I v ≺ q₂
        Iq {v} ac lt = far (val-row ac) (val-row ac₂) lt (under-trans (u-vU v) (u-UI v)) (under-trans (u-vU v₂) (u-UI v₂))

        val-sv : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → SvE (I v) (out (val ac))
        val-sv {v} ac lt = sv-up (ct-up (sc-at ac lt) (inner-row ac) (U≺I v) (Iq ac lt)) (Iq ac lt)

        -- Nothing ends the lane before `v₂`.
        ub : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → Σ ℕ (λ n′ → val ac ≡ instEmit (mark laneDone) n′) → ⊥
        ub {v} ac lt (n′ , eq) = nF (I v , val ac , mm-up (val-sv ac lt) (≺-trans {P} {U v} {I v} (P≺U (val-row ac)) (U≺I v)) (Iq ac lt)
                                          , subst (λ a → T (not (undone a))) (sym eq) tt , Iq ac lt)

        undone-before : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → T (undone (val ac))
        undone-before ac lt = [ (λ d → ⊥-elim (ub ac lt d)) , proj₁ ]′ (ls-view (pre ac) (val ac))

        -- The lane's failing row is its `laneDone`'s.
        ld-anat : ∀ {y e} → LDE y (out e) → y ≡ yd ⊎ (MME y (out e) × T (undone e))
        ld-anat (TakeWhile.pass x kp _ , _) = inj₂ (x , kp)
        ld-anat (TakeWhile.fail {q = q′} x nk nF′ _ , _) = inj₁ (cong (_⊕ [ ix 0 ]) same)
          where
            same : q′ ≡ q₂
            same with ≼-or-≻ q′ q₂
            ... | inj₂ q₂q′ = ⊥-elim (nF′ (q₂ , _ , mmq , tt , q₂q′))
            ... | inj₁ q′q₂ with ≼-split {q′} {q₂} q′q₂
            ...   | inj₁ lt = ⊥-elim (nF (q′ , _ , x , nk , lt))
            ...   | inj₂ eq = eq

        -- WHAT A ROW OF THE LANE IS: its `laneDone`, the burst part's
        -- `burstEnd`, or a frame value's split.
        data Kind (y : Pos) (e : IE B) : Set where
          k-done  : y ≡ yd → Kind y e
          k-burst : y ≡ Ib → SbE y (out e) → Kind y e
          k-val   : ∀ {v b} (ac : Ac v b) → y ≡ I v → e ≡ val ac → T (undone e) → Kind y e
          k-carry : ∀ {v b} (ac : Ac v b) i {n′} → y ≡ Bs v ⊕ [ ix i ] → i < proj₂ (proj₁ (pre ac)) → val ac ≡ instEmit (mark laneDone) n′ → Kind y e

        kind : ∀ {y e} → LDE y (out e) → Kind y e
        kind r with ld-anat r
        ... | inj₁ eq = k-done eq
        ... | inj₂ (mm , kp) with mm-anat mm
        ...   | inj₂ (sb , _) = k-burst (proj₁ (burst-only sb)) sb
        ...   | inj₁ (sv , _) with img sv
        ...     | _ , _ , ac , _ , inj₁ (ey , ee)                    = k-val ac ey ee kp
        ...     | _ , _ , ac , _ , inj₂ (i , _ , ey , lt , _ , vd′) = k-carry ac i ey lt vd′

        -- A split's rows lie under its value's.
        Anch : Pos → Set
        Anch y = Σ Pos λ v → Σ St λ b → Σ (Ac v b) λ ac → Under (U v) y × (y ≡ I v ⊎ T (not (undone (val ac))))

        anch : ∀ {y e} → Kind y e → (y ≡ yd ⊎ y ≡ Ib) ⊎ Anch y
        anch (k-done eq)               = inj₁ (inj₁ eq)
        anch (k-burst eq _)            = inj₁ (inj₂ eq)
        anch (k-val {v} ac refl _ _)   = inj₂ (v , _ , ac , u-UI v , inj₁ refl)
        anch (k-carry {v} ac i refl _ vd′) = inj₂ (v , _ , ac , u-UB v i , inj₂ (subst (λ a → T (not (undone a))) (sym vd′) tt))

        -- An anchored row lies past every earlier value's split and before
        -- every later one's.
        u-v : ∀ {v y} → Under (U v) y → Under v y
        u-v {v} uy = under-trans (u-vU v) uy

        ----------------------------------------------------------------
        -- The carries

        carries : ∀ {i} → i < proj₂ (proj₁ (pre ac₂)) → LDE (Bs v₂ ⊕ [ ix i ]) (out (marked carry)) × (Bs v₂ ⊕ [ ix i ]) ≺ yd
        carries {i} lt =
          ld-up (mm-up (sv-up (ct-up scr (carry-row ac₂ vd lt) (U≺B v₂ i) (B≺I v₂ i)) (B≺I v₂ i))
                       (≺-trans {P} {U v₂} {Bs v₂ ⊕ [ ix i ]} (P≺U (val-row ac₂)) (U≺B v₂ i)) (B≺I v₂ i)) tt (B≺I v₂ i)
          , ≺-trans {Bs v₂ ⊕ [ ix i ]} {q₂} {yd} (B≺I v₂ i) q≺yd

        ----------------------------------------------------------------
        -- Nothing else under the split before the `laneDone`

        only : ∀ {y e} → LDE y (out e) → Under (U v₂) y → y ≺ yd → Σ ℕ λ i → i < proj₂ (proj₁ (pre ac₂)) × y ≡ Bs v₂ ⊕ [ ix i ]
        only r uy lt = go (kind r)
          where
            go : ∀ {y e} → Kind y e → Under (U v₂) y → y ≺ yd → Σ ℕ λ i → i < proj₂ (proj₁ (pre ac₂)) × y ≡ Bs v₂ ⊕ [ ix i ]
            go (k-done refl) _ lt′ = ⊥-elim (≺-irrefl {yd} lt′)
            go (k-burst refl sb) uy′ _ = ⊥-elim (ap svq sb (P≺U (val-row ac₂)) uy′)
            go {y} (k-val {v} ac refl ee kp) uy′ lt′ with ≼-or-≻ v₂ v
            ... | inj₂ vv₂ = ⊥-elim (under-≼ uy′ (far (val-row ac) (val-row ac₂) vv₂ (u-v (u-UI v)) (u-vU v₂)))
            ... | inj₁ v₂v with ≼-split {v₂} {v} v₂v
            ...   | inj₁ lt₂ = ⊥-elim (≺-absurd {y} {yd} lt′ (far (val-row ac₂) (val-row ac) lt₂ u-yd (u-v (u-UI v))))
            ...   | inj₂ refl = ⊥-elim (subst (λ a → T (undone a)) (trans ee (trans (proj₂ (pre-val ac ac₂)) vd)) kp)
            go {y} (k-carry {v} ac i refl lt₀ _) uy′ lt′ with ≼-or-≻ v₂ v
            ... | inj₂ vv₂ = ⊥-elim (under-≼ uy′ (far (val-row ac) (val-row ac₂) vv₂ (u-v (u-UB v i)) (u-vU v₂)))
            ... | inj₁ v₂v with ≼-split {v₂} {v} v₂v
            ...   | inj₁ lt₂ = ⊥-elim (≺-absurd {y} {yd} lt′ (far (val-row ac₂) (val-row ac) lt₂ u-yd (u-v (u-UB v i))))
            ...   | inj₂ refl = i , subst (λ st → i < proj₂ (proj₁ st)) (proj₁ (pre-val ac ac₂)) lt₀ , refl

        ----------------------------------------------------------------
        -- The fold

        T₀ : Pos → IE B → Set
        T₀ y e = LDE y (out e) × (y ≡ Ib → ⊥)

        U≺yd : ∀ {v b} (ac : Ac v b) → v ≼ v₂ → U v ≺ yd
        U≺yd {v} ac h with ≼-split {v} {v₂} h
        ... | inj₁ lt = far (val-row ac) (val-row ac₂) lt (u-vU v) u-yd
        ... | inj₂ refl = ≺-trans {U v} {q₂} {yd} (U≺I v) q≺yd

        -- An anchored row of the lane against a value's split.
        before-U : ∀ {v b y} (ac : Ac v b) → Anch y → (∀ {v′ b′} (ac′ : Ac v′ b′) → v′ ≺ v → ⊥) → y ≺ U v → ⊥
        before-U {v} {y = y} ac (v′ , _ , ac′ , uy , _) mn lt with ≼-or-≻ v v′
        ... | inj₂ v′v = mn ac′ v′v
        ... | inj₁ vv′ with ≼-split {v} {v′} vv′
        ...   | inj₁ lt′ = ≺-absurd {y} {U v} lt (far (val-row ac) (val-row ac′) lt′ (u-vU v) (u-v uy))
        ...   | inj₂ refl = under-≼ uy lt

        claim : ∀ {v b} (ac : Ac v b) → v ≼ v₂ → FoldOf T₀ (U v) (proj₁ (pre ac))
        claim {v} ac₀@(Scan.acc₀ x mn) h = f-none λ {y} (r , nb) lt → gap (anch (kind r)) nb lt
          where
            gap : ∀ {y} → (y ≡ yd ⊎ y ≡ Ib) ⊎ Anch y → (y ≡ Ib → ⊥) → y ≺ U v → ⊥
            gap (inj₁ (inj₁ refl)) _ lt = ≺-absurd {yd} {U v} lt (U≺yd ac₀ h)
            gap (inj₁ (inj₂ eq)) nb _   = nb eq
            gap (inj₂ an) _ lt          = before-U ac₀ an (λ ac′ lt′ → mn (val-row ac′) lt′) lt
        claim {v} (Scan.acc {q = v₀} a x lt nx) h =
          subst (FoldOf T₀ (U v)) (sym (trans (cong proj₁ (b-eq a)) (cnt (pre a) (val a) (undone-before a v₀v₂))))
            (f-step (fold-ext (claim a (≺→≼ {v₀} {v₂} v₀v₂)) (≺→≼ {U v₀} {I v₀} (U≺I v₀)) gap₁)
                    (ld-up (mm-up (val-sv a v₀v₂) (≺-trans {P} {U v₀} {I v₀} (P≺U (val-row a)) (U≺I v₀)) (Iq a v₀v₂)) (undone-before a v₀v₂) (Iq a v₀v₂)
                    , λ eq → ap (val-sv a v₀v₂) sv-row (P≺U (val-row a)) (subst (Under (U v₀)) eq (u-UI v₀)))
                    (far (val-row a) x lt (u-v (u-UI v₀)) (u-vU v)) btw)
          where
            v₀v₂ : v₀ ≺ v₂
            v₀v₂ = ≺-≼-≺ {v₀} {v} {v₂} lt h

            -- Nothing of the lane between `v₀`'s value and its split.
            gap₁ : ∀ {y e} → T₀ y e → U v₀ ≼ y → y ≺ I v₀ → ⊥
            gap₁ {y} (r , nb) uy yI = go (anch (kind r))
              where
                go : (y ≡ yd ⊎ y ≡ Ib) ⊎ Anch y → ⊥
                go (inj₁ (inj₁ eq)) = ≺-absurd {yd} {I v₀} (subst (_≺ I v₀) eq yI) (≺-trans {I v₀} {q₂} {yd} (Iq a v₀v₂) q≺yd)
                go (inj₁ (inj₂ eq))   = nb eq
                go (inj₂ (v′ , _ , ac′ , uy′ , k)) with ≼-or-≻ v₀ v′
                ... | inj₂ v′v₀ = uy (far (val-row ac′) (val-row a) v′v₀ (u-v uy′) (u-vU v₀))
                ... | inj₁ v₀v′ with ≼-split {v₀} {v′} v₀v′
                ...   | inj₁ lt′ = ≺-absurd {y} {I v₀} yI (far (val-row a) (val-row ac′) lt′ (u-v (u-UI v₀)) (u-v uy′))
                ...   | inj₂ refl with k
                ...     | inj₁ eq = ≺-irrefl {I v₀} (subst (_≺ I v₀) eq yI)
                ...     | inj₂ nu = undone-false (val ac′) (undone-before ac′ v₀v₂) nu

            -- Nothing of the lane between `v₀`'s split and `v`'s value.
            btw : ∀ {y′ e′} → T₀ y′ e′ → I v₀ ≺ y′ → y′ ≺ U v → ⊥
            btw {y′} (r , nb) Iy yU = go (anch (kind r))
              where
                go : (y′ ≡ yd ⊎ y′ ≡ Ib) ⊎ Anch y′ → ⊥
                go (inj₁ (inj₁ eq)) = ≺-absurd {yd} {U v} (subst (_≺ U v) eq yU) (U≺yd (Scan.acc a x lt nx) h)
                go (inj₁ (inj₂ eq))   = nb eq
                go (inj₂ (v′ , _ , ac′ , uy′ , k)) with ≼-or-≻ v₀ v′
                ... | inj₂ v′v₀ = ≺-absurd {I v₀} {y′} Iy (far (val-row ac′) (val-row a) v′v₀ (u-v uy′) (u-v (u-UI v₀)))
                ... | inj₁ v₀v′ with ≼-split {v₀} {v′} v₀v′
                ...   | inj₁ lt′ with ≼-or-≻ v v′
                ...     | inj₂ v′v = nx (val-row ac′) lt′ v′v
                ...     | inj₁ vv′ with ≼-split {v} {v′} vv′
                ...       | inj₁ lt″ = ≺-absurd {y′} {U v} yU (far x (val-row ac′) lt″ (u-vU v) (u-v uy′))
                ...       | inj₂ refl = under-≼ uy′ yU
                go (inj₂ (v′ , _ , ac′ , uy′ , k)) | inj₁ v₀v′ | inj₂ refl with k
                ... | inj₁ eq = ≺-irrefl {I v₀} (subst (I v₀ ≺_) eq Iy)
                ... | inj₂ nu = undone-false (val ac′) (undone-before ac′ v₀v₂) nu

        has : Ib ≺ U v₂ → LDE Ib (out (marked burstEnd))
        has lt = ld-up (mb-up sv-row P≺Ib Ibq) tt Ibq
          where
            Ibq : Ib ≺ q₂
            Ibq = ≺-trans {Ib} {U v₂} {q₂} lt (U≺I v₂)

        fold : FoldOf (λ y e → LDE y (out e)) (U v₂) (proj₁ (pre ac₂))
        fold = insert Ib (marked burstEnd) (λ _ → refl) (claim ac₂ (≼-refl {v₂})) has

        sited : Sited LDE yd
        sited = record
          { w = U v₂ ; base = Bs v₂ ; r = proj₁ (pre ac₂)
          ; w-yd = under-⊕ (u-UI v₂) (ix 0)
          ; w-base = under-⊕ (under-⊕ (under-refl (U v₂)) (ix 0)) (ix 1)
          ; carries = carries
          ; only = only
          ; fold = fold
          }

      -- A LANE'S `laneDone` SITS AT ITS SPLIT.
      site : ∀ {yd n} → LDE yd (out (instEmit (mark laneDone) n)) → Sited LDE yd
      site (TakeWhile.pass _ () _ , _)
      site ldq@(TakeWhile.fail mmq nk nF tt , _) with mm-anat mmq
      ... | inj₂ (sb , _) with proj₂ (burst-only sb)
      ...   | ()
      site ldq@(TakeWhile.fail mmq nk nF tt , _) | inj₁ (svq , _) with img svq
      ...   | v₂ , b₂ , ac₂ , scr , inj₁ (refl , vd) = Chain.sited ac₂ (sym vd) scr svq mmq ldq nF
      ...   | _ , _ , _ , _ , inj₂ (_ , _ , _ , _ , () , _)

------------------------------------------------------------------------
-- The lane, as the elaboration builds it

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) (g : GoodEnv ρ) where
  open LaneStart using (Sh; pc0; pc0-at; pc1; pc2; sh-b; pc0-b; pc2-l; pc0-rows; pc0-ls; pc0-be; sh-past; lane-eq)

  pc0b : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s → enter (ev m (piece {B = B} burstPart 0) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out (marked burstEnd))
  pc0b nothing  h h′ s = at-out , of-reach s 0 (marked burstEnd ∷ []) {s ⊕ [ ix 0 ]} {out (marked burstEnd)}
  pc0b (just _) h h′ s = at-out , of-reach s 0 (marked burstEnd ∷ []) {s ⊕ [ ix 0 ]} {out (marked burstEnd)}

  module S (m : Maybe ℕ) = Site (λ k (h : Den ⊤) → ev m (Sh ρ′ o ρ k) (h ∷ ρ)) (λ k j (h : Den ⊤) (h′ : Den (IE B)) → ev m (piece k j) (h′ ∷ h ∷ ρ))
    (pc0 ρ′ o ρ m) (pc0-at ρ′ o ρ m) (pc1 ρ′ o ρ m) (pc2 ρ′ o ρ m) (sh-b ρ′ o ρ m) (pc0-b ρ′ o ρ m) (pc2-l ρ′ o ρ m) (pc0-rows ρ′ o ρ m)
    (pc0-ls ρ′ o ρ m) (pc0-be ρ′ o ρ m) (sh-past ρ′ o ρ m) (pc0b m)

  -- Each part's connect, and the lane part's frame, as the elaboration
  -- builds them.
  inv-sv : ∀ m k → InvD (Hots ρ) (S.Sv m k)
  inv-sv nothing  k = inv-ev nothing  (shareˢ (laneSrc ρ′ o k) (counted (framed k))) ρ g
  inv-sv (just n) k = inv-ev (just n) (shareˢ (laneSrc ρ′ o k) (counted (framed k))) ρ g

  inv-fr : ∀ m {h h′} → GoodEnv (h′ ∷ h ∷ ρ) → InvD (Hots (h′ ∷ h ∷ ρ)) (S.Fr m lanePart h h′)
  inv-fr nothing  g′ = inv-ev nothing  (framed lanePart) (_ ∷ _ ∷ ρ) g′
  inv-fr (just n) g′ = inv-ev (just n) (framed lanePart) (_ ∷ _ ∷ ρ) g′

  module Inv (m : Maybe ℕ) (s : Pos) (oks : Ok (Hots ρ) s) where
    open S m
    open At s using (K; Kb; P; Pb; FB; okK; okKb; OS; FrE; SvE; SbE)

    IOS : InvAt (Hots ρ) s OS
    IOS = of-inv (lanePart ∷ burstPart ∷ []) s oks

    okP okPb : Ok (Hots ρ) _
    okP  = ok-step K  (ok-in oks (InvAt.world IOS okK)  (InvAt.real IOS okK))
    okPb = ok-step Kb (ok-in oks (InvAt.world IOS okKb) (InvAt.real IOS okKb))

    ISv : InvAt (Hots ρ) P SvE
    ISv = inv-sv m lanePart P okP

    ISb : InvAt (Hots ρ) Pb SbE
    ISb = inv-sv m burstPart Pb okPb

    -- The connects' sources, lawful, and their bodies' worlds.
    law : ∀ {A H p} {σ : EmissionSet A} → InvAt H p σ → Lawful (Proper σ)
    law I = record
      { real   = λ x → InvAt.real I (proj₁ x)
      ; func   = λ x x′ → InvAt.func I (proj₁ x) (proj₁ x′)
      ; flat   = λ x x′ → InvAt.flat I (proj₁ x) (proj₁ x′)
      ; proper = λ c y → proj₂ y (proj₁ c)
      }

    I₁ : InvAt (Hots ρ) (P ⊕ [ ix 1 ]) (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ]))
    I₁ = empty-inv (P ⊕ [ ix 1 ]) (ok-step P okP)

    t₁ : EmissionSet ⊤
    t₁ = Proper (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ]))

    ok₁ : Ok (Hots (hot t₁ ∷ ρ)) (P ⊕ [ ix 0 ])
    ok₁ = Apart.ok₀ t₁ P okP (λ x → InvAt.world I₁ (proj₁ x))

    g₁ : GoodEnv (hot t₁ ∷ ρ)
    g₁ = good-cons (law I₁) g

    I₂ : InvAt (Hots (hot t₁ ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) (enter (ev m (Sh ρ′ o ρ lanePart) (hot t₁ ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))
    I₂ = inv-ev m (Sh ρ′ o ρ lanePart) (hot t₁ ∷ ρ) g₁ ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) (ok-step (P ⊕ [ ix 0 ]) ok₁)

    t₂ : EmissionSet (IE B)
    t₂ = Proper (enter (ev m (Sh ρ′ o ρ lanePart) (hot t₁ ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))

    ok₂ : Ok (Hots (hot t₂ ∷ hot t₁ ∷ ρ)) FB
    ok₂ = Apart.ok₀ t₂ (P ⊕ [ ix 0 ]) ok₁ (λ x → InvAt.world I₂ (proj₁ x))

    IFr : InvAt (Hots (hot t₂ ∷ hot t₁ ∷ ρ)) FB FrE
    IFr = inv-fr m (good-cons (law I₂) g₁) FB ok₂

    -- Below a step of the lane part lies no row of the burst part: the two
    -- connects sit at different values' children.
    up1 : ∀ {x i} → P ≺ x → W⁼ (Hots ρ) P (x ⊕ [ ix i ]) → W⁼ (Hots ρ) P x
    up1 {x} lt w with w-up plain-ix w
    ... | inj₁ eq = ⊥-elim (≺-absurd {P} {x} lt (subst (x ≺_) (sym eq) (≺-ext x [])))
    ... | inj₂ w′ = w′

    ap : ∀ {u a y′ a′} → SvE (((u ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ]) (out a) → SbE y′ (out a′) → P ≺ u → Under u y′ → ⊥
    ap {u} svr sbr Pu uy′ =
      Kids.kid-lane oks IOS okK plain-ix (up1 Pu (up1 Pu₁ (up1 Pu₂ (inW (InvAt.world ISv svr))))) okKb (InvAt.world ISb sbr) ne uy′
      where
        Pu₁ : P ≺ (u ⊕ [ ix 1 ])
        Pu₁ = ≺-trans {P} {u} {u ⊕ [ ix 1 ]} Pu (≺-ext u [])

        Pu₂ : P ≺ ((u ⊕ [ ix 1 ]) ⊕ [ ix 1 ])
        Pu₂ = ≺-trans {P} {u ⊕ [ ix 1 ]} {(u ⊕ [ ix 1 ]) ⊕ [ ix 1 ]} Pu₁ (≺-ext (u ⊕ [ ix 1 ]) [])

        ix01 : ix 0 ≡ ix 1 → ⊥
        ix01 ()

        ne : K ⊕ [ ix 1 ] ≡ Kb ⊕ [ ix 1 ] → ⊥
        ne eq = ix01 (⊕-injʳ s s (⊕-injˡ K Kb eq))

  -- WHERE A LANE'S `laneDone` SITS, in the lane as elaborated.
  lane-site : ∀ m s → Ok (Hots ρ) s → ∀ {yd n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s yd (out (instEmit (mark laneDone) n))
            → Sited (enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s) yd
  lane-site m s oks {yd} {n} r =
    subst (λ d → Sited (enter d s) yd) (sym (lane-eq ρ′ o ρ m))
      (S.At.Hyp.site m s (InvAt.flat (Inv.IFr m s oks)) (InvAt.func (Inv.IFr m s oks)) (Inv.ap m s oks)
        (subst (λ d → enter d s yd (out (instEmit (mark laneDone) n))) (lane-eq ρ′ o ρ m) r))
