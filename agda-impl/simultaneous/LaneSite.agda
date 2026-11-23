{-# OPTIONS --guardedness #-}

-- WHERE A LANE'S `laneDone` SITS (`lane-site`).  The lane fails its take
-- just past the frame value `v₂` whose scan step reads the `laneDone`, and
-- the map shows that step told the scan's routes.  Below `v₂` nothing else
-- of the lane lies before the `laneDone`: another frame value lies wholly
-- before or after it, the frame's rows lying flat, and the burst part's
-- one row lies in another subscription's world.  The scan's routes there
-- are the fold of the frame's values before `v₂`, each shown at its own
-- place: the lane's rows before the `laneDone` are those values' rows,
-- with the burst part's `burstEnd`, which counts nothing.
module simultaneous.LaneSite where

open import Data.Bool using (true; false; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs)
open import denotation.Position using (Pos; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-apart; <ᵖ-between)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; Proper; at-out; at-end; on-out; _≺_; _≼_; Few;
  MapT; map-out; module Op; module Joining; module Bounded; module Scan; module TakeWhile;
  module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-≺-≺; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd; ≼-or-≻; ≼-split)
open import denotation.Laws.Worlds using (Hots; GoodEnv; Ok; Lawful; InvAt; InvD; inW; plain-ix; ok-in; ok-step; ⊕-injˡ; ⊕-injʳ;
  ⊕-identityʳ; ⊑-≼)
open import denotation.Laws.Worlds.Leaves using (of-reach; empty-inv; of-inv)
open import denotation.Laws.Count using (reach-down)
open import denotation.Laws.Connect using (module Apart)
open import denotation.Laws.JoinInv using (module Kids)
open import denotation.Laws using (good-cons)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (merge-out; bounded-out; hot-out; map-out′)
open import simultaneous.ElabUndone using (tell-back; tell-done)
open import simultaneous.Layers using (to≺; from≺)
open import simultaneous.LaneLocal using (inv-ev)
open import simultaneous.Shut using (r₀)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; laneDone; burstEnd)
open import simultaneous.LaneLayers using (Under; acc-row; bd-lane-past; conn-few; few-row; few-tr; join-past; map-few; of-after;
  scan-few; under-ext; under-refl; under-trans; under-≺; under-⊕)
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
-- Small facts

under-≼ : ∀ {x y} → Under x y → x ≼ y
under-≼ u = ⊑-≼ u

-- Two positions, by their order: an eliminator, so no `with` abstracts a
-- large context.
tri : ∀ {C : Set} {v w : Pos} → (w ≺ v → C) → (v ≺ w → C) → (v ≡ w → C) → C
tri {v = v} {w} a b c = [ (λ vw → [ b , c ]′ (≼-split {v} {w} vw)) , a ]′ (≼-or-≻ v w)

-- A position past `w`, before one under it, is under it.
between-under : ∀ {w u y} → Under w y → w ≺ u → u ≺ y → Under w u
between-under {w} {u} (ys , refl) wu uy = <ᵖ-between w u ys (from≺ w u wu) (from≺ u (w ⊕ ys) uy)

-- A step counts what it shows, when that ends no lane.
step-count : ∀ {X} (st : Routes × IE X) e → T (undone (proj₂ (laneStep st e)))
           → count (proj₁ st) (proj₂ (laneStep st e)) ≡ proj₁ (laneStep st e)
step-count st e u = cong (count (proj₁ st)) (sym (tell-back (proj₁ st) e refl u))

dec-undone : ∀ b → (T (not b) → ⊥) → T b
dec-undone true  _ = tt
dec-undone false k = ⊥-elim (k tt)

------------------------------------------------------------------------
-- The site, over the lane's layers

-- What a lane's `laneDone` at `yd`, telling `k`, sits past, read in one
-- emission set: the fold of the lane's rows before it, whose count it
-- tells.
record Sited {B : Set} (t : EmissionSet (IE B)) (yd : Pos) (k : ℕ) : Set where
  field
    r    : Routes
    told : k ≡ proj₂ r
    fold : FoldOf (λ y v → t y (out v)) yd r

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
  St = Routes × IE B

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

    Ib : Pos
    Ib = V₀

    u-Bp : Under (Bp P) Ib
    u-Bp = under-trans (under-⊕ (under-refl (Bp P)) (ix 0)) u-V₀

    u-P : Under (P ⊕ [ ix 0 ]) Ib
    u-P = under-trans (under-⊕ (under-refl (P ⊕ [ ix 0 ])) (ix 0)) u-Bp

    sc-few : ∀ {v} → Under V₀ v → Few (Scan.ScanT laneStep z₀ FrEb) v
    sc-few uv = scan-few laneStep z₀ FrEb (few-tr (fr-few uv))

    ct-few : Few (MapT proj₂ ScEb) Ib
    ct-few = map-few proj₂ ScEb (few-tr (sc-few (under-refl V₀)))

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

    sc-row : ScEb V₀ (out (laneStep z₀ (marked burstEnd)))
    sc-row = few-row (Scan.sval (Scan.acc₀ fr-row fr-min)) (sc-few (under-refl V₀))

    ct-row : enter (Ct burstPart h₁ h₂) (Bp P) Ib (out (marked burstEnd))
    ct-row = few-row (map-out sc-row) ct-few

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

    -- The frame's rows lie past the lane part's connect.
    P≺v : ∀ {v e} → FrE v e → P ≺ v
    P≺v {v} x = ≺-trans {P} {FB} {v} (≺-trans {P} {P ⊕ [ ix 0 ]} {FB} (≺-ext P []) (≺-ext (P ⊕ [ ix 0 ]) []))
                  (join-past {p = FB} (of-after FB (0 ∷ 1 ∷ 2 ∷ [])) (λ _ → bd-lane-past) (λ ()) (proj₁ x))

    -- WHAT THE LANE PART'S CONNECT SHOWS: a frame value's step, told, at
    -- the value.
    View : Pos → IE B → Set
    View y e = Σ St λ b → Σ (Ac y b) λ ac → ScE y (out b) × e ≡ proj₂ b

    img-sc : ∀ {y e} → Σ St (λ b → ScE y (out b) × e ≡ proj₂ b) → View y e
    img-sc (b , scr@(Scan.sval ac , _) , eq) = b , ac , scr , eq

    img : ∀ {y e} → SvE y (out e) → View y e
    img r = img-sc (map-out′ proj₂ (Sc lanePart h₁ h₂) FB (sv-out lanePart P r))

    -- The burst part's connect shows its `burstEnd`, alone.
    bo-sc : ∀ {y a} → Σ St (λ b → FrB.ScEb Pb y (out b) × a ≡ proj₂ b) → y ≡ Ib × a ≡ marked burstEnd
    bo-sc (b , (Scan.sval ac , _) , refl) with FrB.acc-b Pb ac
    ... | refl , refl = refl , refl

    burst-only : ∀ {y a} → SbE y (out a) → y ≡ Ib × a ≡ marked burstEnd
    burst-only r = bo-sc (map-out′ proj₂ (Sc burstPart (H₁ Pb) (H₂ Pb burstPart)) (Bp Pb) (sv-out burstPart Pb r))

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
               (ap : ∀ {u a y′ a′} → SvE u (out a) → SbE y′ (out a′) → Under u y′ → ⊥) where

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

      -- THE `laneDone` AT `v₂`'S STEP, and the layers above it.
      module Chain {v₂ b₂} (ac₂ : Ac v₂ b₂) {kd n} (ed : proj₂ b₂ ≡ instEmit (mark (laneDone kd)) n) (scr : ScE v₂ (out b₂))
                   (svq : SvE v₂ (out (instEmit (mark (laneDone kd)) n))) (mmq : MME v₂ (out (instEmit (mark (laneDone kd)) n)))
                   (ldq : LDE (v₂ ⊕ [ ix 0 ]) (out (instEmit (mark (laneDone kd)) n)))
                   (nF : ¬ TakeWhile.Failed true undone MME v₂) where
        LD : IE B
        LD = instEmit (mark (laneDone kd)) n

        yd : Pos
        yd = v₂ ⊕ [ ix 0 ]

        v≺yd : v₂ ≺ yd
        v≺yd = ≺-ext v₂ []

        u-yd : Under v₂ yd
        u-yd = under-⊕ (under-refl v₂) (ix 0)

        ctq : enter (Ct lanePart h₁ h₂) FB v₂ (out LD)
        ctq = sv-out lanePart P svq

        -- Each layer shows, before `v₂`, what the layer below does.
        ct-up : ∀ {v b} → ScE v (out b) → v ≺ v₂ → enter (Ct lanePart h₁ h₂) FB v (out (proj₂ b))
        ct-up {v} {b} sc lt = map-out sc , reach-down {q = v₂} {w = v} {e = out LD} {e₁ = out (proj₂ b)} (proj₂ ctq) lt tt

        sv-up : ∀ {y e} → enter (Ct lanePart h₁ h₂) FB y (out e) → y ≺ v₂ → SvE y (out e)
        sv-up {y} {e} ct yq = Connecting.body (Connecting.body ct , reach-down {q = v₂} {w = y} {e = out LD} {e₁ = out e} (proj₂ (mid-out lanePart P svq)) yq tt)
                    , reach-down {q = v₂} {w = y} {e = out LD} {e₁ = out e} (proj₂ svq) yq tt

        mm-up : ∀ {y e} → SvE y (out e) → P ≺ y → y ≺ v₂ → MME y (out e)
        mm-up {y} {e} sv Py yq = Joining.lane okK tt (sv , Py) (λ ()) tt , reach-down {q = v₂} {w = y} {e = out LD} {e₁ = out e} (proj₂ mmq) yq tt

        mb-up : ∀ {y e} → SbE y (out e) → Pb ≺ y → y ≺ v₂ → MME y (out e)
        mb-up {y} {e} sb Py yq = Joining.lane okKb tt (sb , Py) (λ ()) tt , reach-down {q = v₂} {w = y} {e = out LD} {e₁ = out e} (proj₂ mmq) yq tt

        ld-up : ∀ {y e} → MME y (out e) → T (undone e) → y ≺ v₂ → LDE y (out e)
        ld-up {y} {e} mm kp yq = TakeWhile.pass mm kp (λ (q′ , a′ , x′ , nk′ , lt′) → nF (q′ , a′ , x′ , nk′ , ≺-trans {q′} {y} {v₂} lt′ yq))
                           , reach-down {q = yd} {w = y} {e = out LD} {e₁ = out e} (proj₂ ldq) (≺-trans {y} {v₂} {yd} yq v≺yd) tt

        sc-at : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → ScE v (out b)
        sc-at {v} {b} ac lt = Scan.sval ac , reach-down {q = v₂} {w = v} {e = out b₂} {e₁ = out b} (proj₂ scr) lt tt

        val-sv : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → SvE v (out (proj₂ b))
        val-sv ac lt = sv-up (ct-up (sc-at ac lt) lt) lt

        mm-val : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → MME v (out (proj₂ b))
        mm-val ac lt = mm-up (val-sv ac lt) (P≺v (val-row ac)) lt

        -- Nothing ends the lane before `v₂`.
        undone-before : ∀ {v b} (ac : Ac v b) → v ≺ v₂ → T (undone (proj₂ b))
        undone-before {v} {b} ac lt = dec-undone (undone (proj₂ b)) λ nu → nF (v , proj₂ b , mm-val ac lt , nu , lt)

        -- The lane's failing row is its `laneDone`'s.
        ld-anat : ∀ {y e} → LDE y (out e) → y ≡ yd ⊎ (MME y (out e) × T (undone e))
        ld-anat (TakeWhile.pass x kp _ , _) = inj₂ (x , kp)
        ld-anat (TakeWhile.fail {q = q′} x nk nF′ _ , _) = inj₁ (cong (_⊕ [ ix 0 ]) same)
          where
            same : q′ ≡ v₂
            same = tri {v = q′} {v₂} (λ v₂q′ → ⊥-elim (nF′ (v₂ , _ , mmq , tt , v₂q′))) (λ lt → ⊥-elim (nF (q′ , _ , x , nk , lt))) (λ eq → eq)

        -- WHAT A ROW OF THE LANE IS: its `laneDone`, the burst part's
        -- `burstEnd`, or a frame value's step.
        data Kind (y : Pos) (e : IE B) : Set where
          k-done  : y ≡ yd → Kind y e
          k-burst : y ≡ Ib → Kind y e
          k-val   : ∀ {b} (ac : Ac y b) → e ≡ proj₂ b → T (undone e) → Kind y e

        kind-sv : ∀ {y e} → View y e → T (undone e) → Kind y e
        kind-sv (_ , ac , _ , ee) kp = k-val ac ee kp

        kind-mm : ∀ {y e} → MME y (out e) → T (undone e) → Kind y e
        kind-mm mm kp = [ (λ x → kind-sv (img (proj₁ x)) kp) , (λ x → k-burst (proj₁ (burst-only (proj₁ x)))) ]′ (mm-anat mm)

        kind : ∀ {y e} → LDE y (out e) → Kind y e
        kind r = [ k-done , (λ x → kind-mm (proj₁ x) (proj₂ x)) ]′ (ld-anat r)

        -- The lane shows nothing at `v₂` that does not end it.
        not-at : ∀ {b e} (ac : Ac v₂ b) → e ≡ proj₂ b → T (undone e) → ⊥
        not-at {b} ac refl kp = subst (λ a → T (undone a)) (trans (cong proj₂ same) ed) kp
          where
            same : b ≡ b₂
            same = let (pe , ve) = pre-val ac ac₂ in trans (b-eq ac) (trans (cong₂ laneStep pe ve) (sym (b-eq ac₂)))

        ----------------------------------------------------------------
        -- The fold

        T₀ : Pos → IE B → Set
        T₀ y e = LDE y (out e) × (y ≡ Ib → ⊥)

        v≺yd′ : ∀ {v} → v ≼ v₂ → v ≺ yd
        v≺yd′ {v} h = ≼-≺-≺ {v} {v₂} {yd} h v≺yd

        claim : ∀ {v b} (ac : Ac v b) → v ≼ v₂ → FoldOf T₀ v (proj₁ (pre ac))
        claim {v} (Scan.acc₀ x mn) h = f-none λ (r , nb) lt → gap (kind r) nb lt
          where
            gap : ∀ {y e} → Kind y e → (y ≡ Ib → ⊥) → y ≺ v → ⊥
            gap (k-done refl) _ lt   = ≺-absurd {yd} {v} lt (v≺yd′ h)
            gap (k-burst eq) nb _    = nb eq
            gap (k-val ac′ _ _) _ lt = mn (val-row ac′) lt
        claim {v} (Scan.acc {q = v₀} {b = bₐ} a x lt nx) h =
          subst (FoldOf T₀ v) ce (f-step (claim a (≺→≼ {v₀} {v₂} v₀v₂)) row lt btw)
          where
            v₀v₂ : v₀ ≺ v₂
            v₀v₂ = ≺-≼-≺ {v₀} {v} {v₂} lt h

            u : T (undone (proj₂ bₐ))
            u = undone-before a v₀v₂

            ce : count (proj₁ (pre a)) (proj₂ bₐ) ≡ proj₁ bₐ
            ce = subst (λ z → T (undone (proj₂ z)) → count (proj₁ (pre a)) (proj₂ z) ≡ proj₁ z) (sym (b-eq a)) (step-count (pre a) (val a)) u

            row : T₀ v₀ (proj₂ bₐ)
            row = ld-up (mm-val a v₀v₂) u v₀v₂ , λ eq → ap (val-sv a v₀v₂) sv-row (subst (Under v₀) eq (under-refl v₀))

            -- Nothing of the lane between `v₀` and `v`.
            btw : ∀ {y′ e′} → T₀ y′ e′ → v₀ ≺ y′ → y′ ≺ v → ⊥
            btw (r , nb) = go (kind r) nb
              where
                go : ∀ {y e} → Kind y e → (y ≡ Ib → ⊥) → v₀ ≺ y → y ≺ v → ⊥
                go (k-done refl) _ _ yv     = ≺-absurd {yd} {v} yv (v≺yd′ h)
                go (k-burst eq) nb _ _      = nb eq
                go (k-val ac′ _ _) _ v₀y yv = nx (val-row ac′) v₀y yv

        has : Ib ≺ v₂ → LDE Ib (out (marked burstEnd))
        has lt = ld-up (mb-up sv-row P≺Ib lt) tt lt

        fold₀ : FoldOf (λ y e → LDE y (out e)) v₂ (proj₁ (pre ac₂))
        fold₀ = insert {t = λ y e → LDE y (out e)} Ib (marked burstEnd) (λ _ → refl) (claim ac₂ (≼-refl {v₂})) has

        -- Nothing of the lane from `v₂` to its `laneDone`.
        gap : ∀ {y e} → LDE y (out e) → v₂ ≼ y → y ≺ yd → ⊥
        gap r h = go (kind r) (≼-split {v₂} {_} h)
          where
            ub : ∀ {y} → v₂ ≺ y ⊎ v₂ ≡ y → y ≺ yd → Under v₂ y
            ub (inj₁ v₂y) lt = between-under u-yd v₂y lt
            ub (inj₂ refl) _ = under-refl v₂

            go : ∀ {y e} → Kind y e → v₂ ≺ y ⊎ v₂ ≡ y → y ≺ yd → ⊥
            go (k-done refl) _ lt               = ≺-irrefl {yd} lt
            go (k-burst eq) s lt                = ap svq sv-row (subst (Under v₂) eq (ub s lt))
            go (k-val ac′ ee kp) (inj₂ refl) _  = not-at ac′ ee kp
            go {y} (k-val ac′ _ _) (inj₁ v₂y) lt = ≺-absurd {y} {yd} lt (far (val-row ac₂) (val-row ac′) v₂y u-yd (under-refl y))

        sited : Sited LDE yd kd
        sited = record
          { r    = proj₁ (pre ac₂)
          ; told = tell-done (proj₁ (pre ac₂)) (val ac₂) (trans (sym (cong proj₂ (b-eq ac₂))) ed)
          ; fold = fold-ext fold₀ (≺→≼ {v₂} {yd} v≺yd) gap
          }

      ld≢be : ∀ {kd n} → _≡_ {A = IE B} (instEmit (mark (laneDone kd)) n) (marked burstEnd) → ⊥
      ld≢be ()

      site-v : ∀ {q kd n} → View q (instEmit (mark (laneDone kd)) n) → SvE q (out (instEmit (mark (laneDone kd)) n))
             → MME q (out (instEmit (mark (laneDone kd)) n)) → LDE (q ⊕ [ ix 0 ]) (out (instEmit (mark (laneDone kd)) n))
             → ¬ TakeWhile.Failed true undone MME q → Sited LDE (q ⊕ [ ix 0 ]) kd
      site-v (b₂ , ac₂ , scr , ee) svq mmq ldq nF = Chain.sited ac₂ (sym ee) scr svq mmq ldq nF

      -- A LANE'S `laneDone` SITS JUST PAST ITS FRAME VALUE.
      site : ∀ {yd kd n} → LDE yd (out (instEmit (mark (laneDone kd)) n)) → Sited LDE yd kd
      site (TakeWhile.pass _ () _ , _)
      site ldq@(TakeWhile.fail mmq nk nF tt , _) =
        [ (λ x → site-v (img (proj₁ x)) (proj₁ x) mmq ldq nF) , (λ x → ⊥-elim (ld≢be (proj₂ (burst-only (proj₁ x))))) ]′ (mm-anat mmq)

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
    ap : ∀ {u a y′ a′} → SvE u (out a) → SbE y′ (out a′) → Under u y′ → ⊥
    ap {u} svr sbr uy′ =
      Kids.kid-lane oks IOS okK plain-ix (inW (InvAt.world ISv svr)) okKb (InvAt.world ISb sbr) ne uy′
      where
        ix01 : ix 0 ≡ ix 1 → ⊥
        ix01 ()

        ne : K ⊕ [ ix 1 ] ≡ Kb ⊕ [ ix 1 ] → ⊥
        ne eq = ix01 (⊕-injʳ s s (⊕-injˡ K Kb eq))

  -- WHERE A LANE'S `laneDone` SITS, in the lane as elaborated.
  lane-site : ∀ m s → Ok (Hots ρ) s → ∀ {yd kd n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s yd (out (instEmit (mark (laneDone kd)) n))
            → Sited (enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s) yd kd
  lane-site m s oks {yd} {kd} {n} r =
    subst (λ d → Sited (enter d s) yd kd) (sym (lane-eq ρ′ o ρ m))
      (S.At.Hyp.site m s (InvAt.flat (Inv.IFr m s oks)) (InvAt.func (Inv.IFr m s oks)) (Inv.ap m s oks)
        (subst (λ d → enter d s yd (out (instEmit (mark (laneDone kd)) n))) (lane-eq ρ′ o ρ m) r))
