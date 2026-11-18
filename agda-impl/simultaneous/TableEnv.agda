{-# OPTIONS --guardedness #-}

-- THE ENVIRONMENT A SUBTERM'S RECORD IS STATED IN.  A subterm's plain
-- and elaborated tables are read in environments of hots, each hot
-- carrying its map onto the elaborated hot (`Maps`) and its readers'
-- record (`HotR`).  The record holds wherever the two subscriptions cut
-- every hot in scope alike (`Aligned`) and lie in alike instants
-- (`Linked`).
--
-- STREAMS SUBSCRIBED AT DIFFERENT TIMES AGREE ON ORDER ONLY THROUGH
-- THEIR MAPS.  A flatMap's lane is subscribed past its creator, a row of
-- the source, so it cuts each hot in scope where that row falls among
-- the hot's rows.  So the record carries, past the correspondence itself
-- (`Rest`): every row is linked to its image, every row cuts every hot in
-- scope alike with its image, the rows cut the stream's own rows alike
-- just under each, and every pair cutting the subscription alike from
-- before it cuts the stream's rows alike.
--
-- An alike cut is checked up an instant's creators too (`Cut`): two
-- steps of one tick are ordered by their timers' creators, so a row of a
-- later instant is ordered against a hot's row by where the creators lie.
module simultaneous.TableEnv where

open import Data.Bool using (T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool.Properties using (T-≡)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connected; of)
open import denotation.Position using (Pos; Label; _∙_; root; _≟ᵖ_; _⊕_; frame; cascade; inside; ix; sub; last)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Unpinned; _≺_; _≼_; pin; out; DenEnv; enter; Proper; module Op; at-out; at-end; on-out)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (AgreeTo; AgreeTo-sym; ag-down; ≺-trans; ≺-ext; ≺-absurd; ≼-≺-≺; ≺→≼; ≼-trans; ≼-refl)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc; ⊕-identityʳ; ⊑-refl; ⊑-trans; ⊑-snoc⁺; Ok; InvAt; GoodEnv; Hots; Lawful; _∪ʰ_; ok-step;
  W; W⁼; step; timer; join; here; inW; Real; real-snoc; real-sub; plain-ix; shrink; ok-in)
open import denotation.Laws.Worlds.Leaves using (empty-inv)
open import denotation.Laws.Count using (child)
open import denotation.Laws.Cut using (capprox; inv-capprox; inv-sub)
open import denotation.Laws using (good-cons)
import denotation.Laws.Connect as Cn
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; rejoin)
open import quickcheck.Tabled.Exact using (EnvRel; _∷_; truncate-exact; rejoin-exact; proper-exact)
import quickcheck.Tabled.Exact as Ex
open import quickcheck.Tabled.Exact.Base using (Exactly; sound)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.ElabUndone using (EnvU; AUndone; ann-u; elab-undone)
open import simultaneous.DenRows using (hot-out)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; UncutEnv)
open import simultaneous.ListTR using (tr-at)
open import simultaneous.ListPin using (listC-pin)
open import simultaneous.ListAfter using (listC-past; listC-pinpast)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.Instants using (_≺ⁱ_; triⁱ; instant-≺)
open import simultaneous.TableCorr using (Rel; Same; Scope; Rows; TR; Got)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; annotate)

------------------------------------------------------------------------
-- The subterm's two families of tables

-- The elaboration's scope for a plain scope.
Ren : List Set → List Set → Set₁
Ren Γ Δ = ∀ {X} → X ∈ L.map AIE Γ → X ∈ Δ

-- One more binder in the elaboration's scope.
wk : ∀ {Γ Δ X} → Ren Γ Δ → Ren Γ (X ∷ Δ)
wk ρι j = there (ρι j)

Tab : ∀ {Γ A} → ℕ → Obs Timeline Γ A → (ℕ → All Tb.Listed Γ) → Pos → ℕ → Maybe (Tb.Listed A)
Tab n o ρ p N = listC (3 + N) n o (ρ N) p

Tab* : ∀ {Γ Δ A} → ℕ → Ren Γ Δ → Obs Timeline Γ A → (ℕ → All Tb.Listed Δ) → Pos → ℕ → Maybe (Tb.Listed (IE A))
Tab* n ρι o ρ* p N = listC (3 + N) n (elab ρι o) (ρ* N) p

-- A table listed under an uncut environment is there.
got-ok : ∀ {Γ X} N n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} → UncutEnv ρL → ∀ q → Got (listC N n o ρL q)
got-ok N n o u q with listC-ok N n o u q
... | L , eq , _ = L , eq

-- A pin listed in any environment lies inside its connect.
pin-ok : ∀ {Γ X} N n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} q {l r} → TR (listC N n o ρL q) l (pin r) → T (inside r l)
pin-ok N n o q (_ , eq , m) = listC-pin N n o q eq m

-- A row listed in any environment lies past its subscription.
after-ok : ∀ {Γ X} N n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} q {k e} → TR (listC N n o ρL q) k e → q ≼ k
after-ok N n o q (_ , eq , m) = listC-past N n o q eq m

-- A pin listed in any environment names a connect past its subscription.
pin-after-ok : ∀ {Γ X} N n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} q {l r} → TR (listC N n o ρL q) l (pin r) → q ≼ r
pin-after-ok N n o q (_ , eq , m) = listC-pinpast N n o q eq m

private
  dropLast : List Label → List Label
  dropLast []           = []
  dropLast (_ ∷ [])     = []
  dropLast (y ∷ z ∷ zs) = y ∷ dropLast (z ∷ zs)

  dropLast-++ : ∀ ys l → dropLast (ys L.++ [ l ]) ≡ ys
  dropLast-++ []           l = refl
  dropLast-++ (y ∷ [])     l = refl
  dropLast-++ (y ∷ z ∷ zs) l = cong (y ∷_) (dropLast-++ (z ∷ zs) l)

-- One label up.
up : Pos → Pos
up (i ∙ ys) = i ∙ dropLast ys

up-⊕ : ∀ q l → up (q ⊕ [ l ]) ≡ q
up-⊕ (i ∙ ys) l = cong (i ∙_) (dropLast-++ ys l)

-- A path walked one label at a time, as the listing walks it.
infixl 5 _⊕ˡ_
_⊕ˡ_ : Pos → List Label → Pos
q ⊕ˡ []       = q
q ⊕ˡ (l ∷ ls) = (q ⊕ [ l ]) ⊕ˡ ls

------------------------------------------------------------------------
-- Alike instants, alike cuts

-- Two positions in alike instants: both the frame, or steps of one tick
-- and label whose creators, each before its step and in another instant,
-- are alike.
data Linked : Pos → Pos → Set where
  framed   : ∀ {y y*} → instantOf y ≡ frame → instantOf y* ≡ frame → Linked y y*
  cascaded : ∀ {y y* t c c* l} → instantOf y ≡ cascade t c l → instantOf y* ≡ cascade t c* l
           → c ≺ y → c* ≺ y* → ¬ (instantOf c ≡ instantOf y) → ¬ (instantOf c* ≡ instantOf y*)
           → Linked c c* → Linked y y*

-- A position seen from one subscription as its image is from the other:
-- past the one exactly when past the other, in its instant exactly when
-- the image is in the other's, and under neither.
Lvl : Pos → Pos → Pos → Pos → Set
Lvl q q* y y* = (q ≺ y ⇔ q* ≺ y*) × (instantOf y ≡ instantOf q ⇔ instantOf y* ≡ instantOf q*) × ¬ (q ⊑ y) × ¬ (q* ⊑ y*)

-- And so every creator up its instants, each step of one tick and label.
data Cut (q q* : Pos) : Pos → Pos → Set where
  at-frame : ∀ {y y*} → Lvl q q* y y* → instantOf y ≡ frame → instantOf y* ≡ frame → Cut q q* y y*
  at-step  : ∀ {y y* t c c* l} → Lvl q q* y y* → instantOf y ≡ cascade t c l → instantOf y* ≡ cascade t c* l
           → Cut q q* c c* → Cut q q* y y*

-- A run's map onto its elaborated run: each row's image, each row's late
-- placements, and its late rows.
record HotMap : Set₁ where
  constructor hotMap
  field
    ψ    : Pos → Pos
    π    : Pos → Pos → Set
    late : Pos → Set
open HotMap public

-- A table's rows cut alike, along a map: each row not late with its
-- image, each row with its late placements.
record Alike {X : Set} (h : HotMap) (t : EmissionSet X) (q q* : Pos) : Set where
  constructor alike
  field
    cut     : ∀ {k e} → t k e → Unpinned e → ¬ late h k → Cut q q* k (ψ h k)
    cut-put : ∀ {k e l} → t k e → π h k l → Cut q q* k l
open Alike public

------------------------------------------------------------------------
-- Going down a label

private
  -- Past `v` and not under it: past what lies under it.
  down : ∀ v l {y} → v ≺ y → ¬ (v ⊑ y) → (v ⊕ [ l ]) ≺ y
  down v l lt nv with child l lt
  ... | inj₁ u   = ⊥-elim (nv u)
  ... | inj₂ lt′ = lt′

  up⊑ : ∀ v l {y} → (v ⊕ [ l ]) ⊑ y → v ⊑ y
  up⊑ v l (zs , refl) = l ∷ zs , ⊕-assoc v [ l ] zs

lvl-l : ∀ {q q* y y*} → Lvl q q* y y* → ∀ l → Lvl (q ⊕ [ l ]) q* y y*
lvl-l {q} {q*} {y} {y*} (lt , ie , nq , nq*) l =
  mk⇔ (λ h → Equivalence.to lt (≺-trans {q} {q ⊕ [ l ]} {y} (≺-ext q []) h))
      (λ h → down q l (Equivalence.from lt h) nq)
  , subst₂ (λ a b → instantOf y ≡ a ⇔ instantOf y* ≡ b) (sym (inst-⊕ q [ l ])) refl ie
  , (λ u → nq (up⊑ q l u)) , nq*

lvl-r : ∀ {q q* y y*} → Lvl q q* y y* → ∀ l* → Lvl q (q* ⊕ [ l* ]) y y*
lvl-r {q} {q*} {y} {y*} (lt , ie , nq , nq*) l* =
  mk⇔ (λ h → down q* l* (Equivalence.to lt h) nq*)
      (λ h → Equivalence.from lt (≺-trans {q*} {q* ⊕ [ l* ]} {y*} (≺-ext q* []) h))
  , subst₂ (λ a b → instantOf y ≡ a ⇔ instantOf y* ≡ b) refl (sym (inst-⊕ q* [ l* ])) ie
  , nq , (λ u → nq* (up⊑ q* l* u))

cut-l : ∀ {q q* y y*} → Cut q q* y y* → ∀ l → Cut (q ⊕ [ l ]) q* y y*
cut-l (at-frame v a b)   l = at-frame (lvl-l v l) a b
cut-l (at-step v a b c)  l = at-step (lvl-l v l) a b (cut-l c l)

cut-r : ∀ {q q* y y*} → Cut q q* y y* → ∀ l* → Cut q (q* ⊕ [ l* ]) y y*
cut-r (at-frame v a b)   l* = at-frame (lvl-r v l*) a b
cut-r (at-step v a b c)  l* = at-step (lvl-r v l*) a b (cut-r c l*)

alike-l : ∀ {X : Set} {h : HotMap} {t : EmissionSet X} {q q*} → Alike h t q q* → ∀ l → Alike h t (q ⊕ [ l ]) q*
alike-l a l = alike (λ x un nl → cut-l (cut a x un nl) l) (λ x pl → cut-l (cut-put a x pl) l)

alike-r : ∀ {X : Set} {h : HotMap} {t : EmissionSet X} {q q*} → Alike h t q q* → ∀ l* → Alike h t q (q* ⊕ [ l* ])
alike-r a l* = alike (λ x un nl → cut-r (cut a x un nl) l*) (λ x pl → cut-r (cut-put a x pl) l*)

alike-r* : ∀ {X : Set} {h : HotMap} {t : EmissionSet X} {q q*} → Alike h t q q* → ∀ ys → Alike h t q (q* ⊕ˡ ys)
alike-r* a []       = a
alike-r* a (l ∷ ls) = alike-r* (alike-r a l) ls

------------------------------------------------------------------------
-- Going past, under a position no image is under

⊑-⊕ˡ : ∀ q ls → q ⊑ (q ⊕ˡ ls)
⊑-⊕ˡ q []       = ⊑-refl q
⊑-⊕ˡ q (l ∷ ls) = ⊑-trans (⊑-snoc⁺ q) (⊑-⊕ˡ (q ⊕ [ l ]) ls)

-- Past `v` and not under it: past all that lies under it.
under-past : ∀ {v z y} → v ⊑ z → v ≺ y → ¬ (v ⊑ y) → z ≺ y
under-past {v} {y = y} (zs , refl) = go v zs
  where
    go : ∀ w ws → w ≺ y → ¬ (w ⊑ y) → (w ⊕ ws) ≺ y
    go w []       lt nw = subst (_≺ y) (sym (⊕-identityʳ w)) lt
    go w (l ∷ ws) lt nw = subst (_≺ y) (⊕-assoc w [ l ] ws) (go (w ⊕ [ l ]) ws (down w l lt nw) (λ u → nw (up⊑ w l u)))

lvl-past : ∀ {q q* y y* L z} → L ≼ q* → q* ≺ z → L ⊑ z → instantOf q* ≡ instantOf z → ¬ (L ⊑ y*)
         → Lvl q q* y y* → Lvl q z y y*
lvl-past {q} {q*} {y} {y*} {L} {z} Lq qz Lz iz nL (lt , ie , nq , _) =
  mk⇔ (λ h → under-past Lz (≼-≺-≺ {L} {q*} {y*} Lq (Equivalence.to lt h)) nL)
      (λ h → Equivalence.from lt (≺-trans {q*} {z} {y*} qz h))
  , subst (λ a → instantOf y ≡ instantOf q ⇔ instantOf y* ≡ a) iz ie
  , nq , (λ u → nL (⊑-trans Lz u))

private
  lead : ∀ {s L y y*} → Cut s L y y* → ¬ (L ⊑ y*)
  lead (at-frame (_ , _ , _ , n) _ _)  = n
  lead (at-step (_ , _ , _ , n) _ _ _) = n

  creator : ∀ {s L y y* t c c* l} → instantOf y ≡ cascade t c l → instantOf y* ≡ cascade t c* l → Cut s L y y* → Cut s L c c*
  creator a _ (at-frame _ a′ _) with trans (sym a) a′
  ... | ()
  creator a b (at-step _ a′ b′ C) with trans (sym a) a′ | trans (sym b) b′
  ... | refl | refl = C

cut-past : ∀ {q q* s L z y y*} → L ≼ q* → q* ≺ z → L ⊑ z → instantOf q* ≡ instantOf z
         → Cut q q* y y* → Cut s L y y* → Cut q z y y*
cut-past Lq qz Lz iz (at-frame v a b)  C′ = at-frame (lvl-past Lq qz Lz iz (lead C′) v) a b
cut-past Lq qz Lz iz (at-step v a b C) C′ = at-step (lvl-past Lq qz Lz iz (lead C′) v) a b (cut-past Lq qz Lz iz C (creator a b C′))

linked-l : ∀ {y y*} → Linked y y* → ∀ l → Linked (y ⊕ [ l ]) y*
linked-l {y} (framed a b)             l = framed (trans (inst-⊕ y [ l ]) a) b
linked-l {y} (cascaded {c = c} a b lt lt* d d* L)  l =
  cascaded (trans (inst-⊕ y [ l ]) a) b (≺-trans {c} {y} {y ⊕ [ l ]} lt (≺-ext y {l} [])) lt*
           (λ e → d (trans e (inst-⊕ y [ l ]))) d* L

linked-r : ∀ {y y*} → Linked y y* → ∀ l* → Linked y (y* ⊕ [ l* ])
linked-r {y* = y*} (framed a b)             l* = framed a (trans (inst-⊕ y* [ l* ]) b)
linked-r {y* = y*} (cascaded {c* = c*} a b lt lt* d d* L)  l* =
  cascaded a (trans (inst-⊕ y* [ l* ]) b) lt (≺-trans {c*} {y*} {y* ⊕ [ l* ]} lt* (≺-ext y* {l*} []))
           d (λ e → d* (trans e (inst-⊕ y* [ l* ]))) L

linked-r* : ∀ {y y*} → Linked y y* → ∀ ys → Linked y (y* ⊕ˡ ys)
linked-r* L []       = L
linked-r* L (l ∷ ls) = linked-r* (linked-r L l) ls

-- Later in the second's instant, still alike.
linked-later : ∀ {y y* z} → Linked y y* → instantOf y* ≡ instantOf z → y* ≺ z → Linked y z
linked-later (framed a b) e _ = framed a (trans (sym e) b)
linked-later {y* = y*} {z} (cascaded {c* = c*} a b l l* d d* L) e lt =
  cascaded a (trans (sym e) b) l (≺-trans {c*} {y*} {z} l* lt) d (λ q → d* (trans q (sym e))) L

inst-⊕ˡ : ∀ q ls → instantOf (q ⊕ˡ ls) ≡ instantOf q
inst-⊕ˡ q []       = refl
inst-⊕ˡ q (l ∷ ls) = trans (inst-⊕ˡ (q ⊕ [ l ]) ls) (inst-⊕ q [ l ])

-- Between two positions of one instant, a third is in it too.
squeeze : ∀ {a b c} → a ≼ b → b ≺ c → instantOf a ≡ instantOf c → instantOf b ≡ instantOf c
squeeze {a} {b} {c} ab bc e with triⁱ (instantOf b) (instantOf c)
... | inj₁ lt        = ⊥-elim (ab (instant-≺ b a (subst (instantOf b ≺ⁱ_) (sym e) lt)))
... | inj₂ (inj₁ eq) = eq
... | inj₂ (inj₂ gt) = ⊥-elim (≺-absurd {b} {c} bc (instant-≺ c b gt))

------------------------------------------------------------------------
-- The emission sets the tables list

-- Each cut's hots listed exactly off a lawful environment, so a table's
-- func and flat are its denotation's, read at an admissible subscription.
--
-- DEAD ROUTE: func and flat over an arbitrary aligned environment.  A hot
--   row the alignment exempts may sit in the subscription's world, and the
--   table then lists rows the invariant does not cover.
--
-- Each hot's connect subscribes its body first (`lo`): a reader of the
-- hot is one of the body's, subscribed at or past it.
record DenOf {Γ} (ρ : ℕ → All Tb.Listed Γ) : Set₁ where
  constructor denOf
  field
    den    : ℕ → DenEnv Γ
    den-ex : ∀ N → EnvRel (ρ N) (den N)
    den-ok : ∀ N → GoodEnv (den N)
    lo     : List Pos
open DenOf public

-- More hot rows, the world no smaller.
mutual
  w-mono : ∀ {H H′ : Pos → Set} {p w} → (∀ {h} → H h → H′ h) → W H p w → W H′ p w
  w-mono f (step w l)           = step (w-mono⁼ f w) l
  w-mono f (timer i w lt pl)    = timer i (w-mono⁼ f w) lt pl
  w-mono f (join (inj₁ h) w eh) = join (inj₁ (f h)) (w-mono⁼ f w) eh
  w-mono f (join (inj₂ v) w eh) = join (inj₂ (w-mono f v)) (w-mono⁼ f w) eh

  w-mono⁼ : ∀ {H H′ : Pos → Set} {p w} → (∀ {h} → H h → H′ h) → W⁼ H p w → W⁼ H′ p w
  w-mono⁼ f here    = here
  w-mono⁼ f (inW w) = inW (w-mono f w)

-- Fewer hot rows, still admissible.
ok-mono : ∀ {H H′ : Pos → Set} {p} → (∀ {h} → H h → H′ h) → Ok H′ p → Ok H p
ok-mono f (r , dj) = r , λ hh w i → dj (f hh) (w-mono f w) i

-- Every cut's hot rows.
HotsAll : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → Set
HotsAll D h = Σ ℕ λ N → Hots (den D N) h

-- No hots: nothing listed, nothing to keep.
none : DenOf {[]} (λ _ → All.[])
none = denOf (λ _ → All.[]) (λ _ → Ex.[]) (λ _ ()) []

-- At or past each of them.
Past : List Pos → Pos → Set
Past fs p = All (_≼ p) fs

past-up : ∀ {fs} p p′ → Past fs p → p ≼ p′ → Past fs p′
past-up p p′ fp pp′ = All.map (λ {f} fp₁ → ≼-trans {f} {p} {p′} fp₁ pp′) fp

past-⊕ : ∀ {fs} p l ls → Past fs p → Past fs (p ⊕ (l ∷ ls))
past-⊕ p l ls fp = past-up p (p ⊕ (l ∷ ls)) fp (≺→≼ {p} {p ⊕ (l ∷ ls)} (≺-ext p {l} ls))

-- ADMISSIBLE: reachable, and no cut's hot row in its world.  Every cut's
-- at once, because a lane subscribed under a row of one cut is read at
-- every cut, where that row's world may join other cuts' rows.  And in
-- each hot's scope: at or past its connect's body.
Admits : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → Set
Admits D p = Ok (HotsAll D) p × Past (lo D) p

admits-at : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → Admits D p → ∀ N → Ok (Hots (den D N)) p
admits-at D a N = ok-mono (λ hh → N , hh) (proj₁ a)

admits-step : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → Admits D p → Admits D (p ⊕ [ ix 1 ])
admits-step D {p} (o , fp) = ok-step p o , past-⊕ p (ix 1) [] fp

admits-ix : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} i → Admits D p → Admits D (p ⊕ [ ix i ])
admits-ix D {p} i ((r , dj) , fp) = (real-snoc p plain-ix r , λ hh w ins → dj hh (shrink w) ins) , past-⊕ p (ix i) [] fp

-- A table listed at an admissible subscription keeps the invariant.
tab-inv : ∀ {Γ X} N n (o : Obs Timeline Γ X) {ρL : All Tb.Listed Γ} {ρD : DenEnv Γ} → EnvRel ρL ρD → GoodEnv ρD → UncutEnv ρL
        → ∀ q → Ok (Hots ρD) q → InvAt (Hots ρD) q (TR (listC N n o ρL q))
tab-inv N n o ex g u q ok with listC-ok N n o u q
... | L , eq , uL = inv-sub (λ x → sound (listC-exact N n o ex q eq uL) (tr-at eq x)) (inv-capprox N n o _ g q ok)

tab-at : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} → (∀ N → UncutEnv (ρ N)) → (D : DenOf ρ)
       → ∀ {q} → Admits D q → ∀ N → InvAt (Hots (den D N)) q (TR (Tab n o ρ q N))
tab-at n o u D {q} a N = tab-inv (3 + N) n o (den-ex D N) (den-ok D N) (u N) q (admits-at D a N)

-- One event at a position, none under another.
tab-func : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} → (∀ N → UncutEnv (ρ N)) → (D : DenOf ρ)
         → ∀ {q} → Admits D q → ∀ {N y e e′} → TR (Tab n o ρ q N) y e → TR (Tab n o ρ q N) y e′ → e ≡ e′
tab-func n o u D a {N} = InvAt.func (tab-at n o u D a N)

tab-flat : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} → (∀ N → UncutEnv (ρ N)) → (D : DenOf ρ)
         → ∀ {q} → Admits D q → ∀ {N y e l ys e′} → TR (Tab n o ρ q N) y e → TR (Tab n o ρ q N) (y ⊕ (l ∷ ys)) e′ → ⊥
tab-flat n o u D a {N} = InvAt.flat (tab-at n o u D a N)

-- A row of a table listed admissibly: admissible past its plain child.
admits-row : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ)
           → ∀ {q} → Admits D q → ∀ {N k e} → TR (Tab n o ρ q N) k e → Admits D (k ⊕ [ ix 1 ])
admits-row n o u D {q} a {N} {k} x =
  ok-step k (ok-in (proj₁ a) (w-mono (λ hh → N , hh) (InvAt.world I x)) (InvAt.real I x)) ,
  past-⊕ k (ix 1) [] (past-up q k (proj₂ a) (after-ok (3 + N) n o q x))
  where I = tab-at n o u D a N

-- A hot listed exactly off a lawful emission set.
record HotD {X : Set} (t : ℕ → Tb.Listed X) : Set₁ where
  constructor hotD
  field
    hev  : ℕ → EmissionSet X
    hex  : ∀ N p → Exactly (rejoin p (t N)) (enter (ES.hot (hev N)) p)
    hlaw : ∀ N → Lawful (hev N)
    hlo  : Pos
open HotD public

den-cons : ∀ {Γ X} {t : ℕ → Tb.Listed X} {ρ : ℕ → All Tb.Listed Γ} → HotD t → DenOf ρ → DenOf (λ N → t N ∷ ρ N)
den-cons h D = denOf (λ N → ES.hot (hev h N) ∷ den D N) (λ N → hex h N ∷ den-ex D N) (λ N → good-cons (hlaw h N) (den-ok D N)) (hlo h ∷ lo D)

-- One hot more, a world no smaller.
admits-wk : ∀ {Γ X} {t : ℕ → Tb.Listed X} {ρ : ℕ → All Tb.Listed Γ} (h : HotD t) (D : DenOf ρ) {p} → Admits (den-cons h D) p → Admits D p
admits-wk h D (o , _ ∷ fp) = ok-mono (λ { (N , hh) → N , inj₂ hh }) o , fp

-- A CONNECT'S HOT: its source listed under the connect's second label.
listHot : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c → Admits D c
        → HotD (λ N → hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))
listHot {X = X} n o u D c a = hotD hv hx hl (c ⊕ [ ix 0 ])
  where
    hv : ℕ → EmissionSet _
    hv N = Proper (enter (capprox (3 + N) n o (den D N)) (c ⊕ [ ix 1 ]))

    hx : ∀ N p → Exactly (rejoin p (hotOf (proj₁ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ]))))) (enter (ES.hot (hv N)) p)
    hx N p = truncate-exact (rejoin-exact (proper-exact (listC-exact (3 + N) n o (den-ex D N) (c ⊕ [ ix 1 ]) (proj₁ (proj₂ (listC-ok (3 + N) n o (u N) (c ⊕ [ ix 1 ])))))) p)

    hl : ∀ N → Lawful (hv N)
    hl N = Cn.lawful {s = capprox (3 + N) n o (den D N)} {F = λ _ → Op.empty {X}} (inv-capprox (3 + N) n o (den D N) (den-ok D N)) (λ _ → empty-inv) c (admits-at D a N)

-- A connect's body is past every connect it lies in.
past-body : ∀ {fs} c → Past fs c → Past ((c ⊕ [ ix 0 ]) ∷ fs) (c ⊕ [ ix 0 ])
past-body c fp = ≼-refl {c ⊕ [ ix 0 ]} ∷ past-⊕ c (ix 0) [] fp

-- Its body admissible where the connect is.
admits-body : ∀ {Γ X} n (o : Obs Timeline Γ X) {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
            → Admits (den-cons (listHot n o u D c a) D) (c ⊕ [ ix 0 ])
admits-body {X = X} n o u D c a = ok-mono into (Cn.Apart.ok₀ σ∞ c (proj₁ a) σw) , past-body c (proj₂ a)
  where
    hD = listHot n o u D c a

    -- The source's rows at every cut, each in the source's world.
    σ∞ : EmissionSet X
    σ∞ h e = Σ ℕ λ N → hev hD N h e

    σw : ∀ {h e} → σ∞ h e → W (HotsAll D) (c ⊕ [ ix 1 ]) h
    σw (N , x) = w-mono (λ hh → N , hh)
      (InvAt.world (inv-capprox (3 + N) n o (den D N) (den-ok D N) (c ⊕ [ ix 1 ]) (ok-step c (admits-at D a N))) (proj₁ x))

    into : ∀ {h} → HotsAll (den-cons hD D) h → (HotsAll D ∪ʰ σ∞) h
    into (N , inj₁ (e , x)) = inj₁ (e , N , x)
    into (N , inj₂ hh)      = inj₂ (N , hh)

-- A ONE-VALUE TRIGGER'S LANE: a connect at `c` whose source is `of
-- [tt]`, its value read by a flatMap subscribed one label under the
-- body.  The lane under the value is admissible.
admits-trig : ∀ {Γ} n {ρ : ℕ → All Tb.Listed Γ} (u : ∀ N → UncutEnv (ρ N)) (D : DenOf ρ) c (a : Admits D c)
            → Admits (den-cons (listHot n (of (tt ∷ [])) u D c a) D) (c ⊕ [ ix 1 ] ⊕ [ ix 0 ] ⊕ [ sub (c ⊕ [ ix 0 ] ⊕ [ ix 1 ]) ] ⊕ [ ix 1 ])
admits-trig n u D c a =
  ok-step (h ⊕ [ sub r ]) (ok-in (proj₁ ar) (join (inj₁ hh) here lt) (real-sub h rh (proj₁ (proj₁ ar)) (≺-trans {r} {h} {h ⊕ [ sub r ]} lt (≺-ext h [])))) ,
  past-⊕ (h ⊕ [ sub r ]) (ix 1) [] (past-⊕ h (sub r) [] (past-up r h (proj₂ ar) (≺→≼ {r} {h} lt)))
  where
    hD = listHot n (of (tt ∷ [])) u D c a
    r h : Pos
    r = c ⊕ [ ix 0 ] ⊕ [ ix 1 ]
    h = c ⊕ [ ix 1 ] ⊕ [ ix 0 ]

    ar : Admits (den-cons hD D) r
    ar = admits-step (den-cons hD D) (admits-body n (of (tt ∷ [])) u D c a)

    rh : Real h
    rh = real-snoc (c ⊕ [ ix 1 ]) plain-ix (real-snoc c plain-ix (proj₁ (proj₁ a)))

    lt : r ≺ h
    lt = subst₂ _≺_ (sym (⊕-assoc c [ ix 0 ] [ ix 1 ])) (sym (⊕-assoc c [ ix 1 ] [ ix 0 ]))
           (Equivalence.from T-≡ (<ᵖ-part c (ix 1 ∷ []) (ix 0 ∷ []) refl))

    s₁ : Pos
    s₁ = c ⊕ [ ix 1 ]

    -- The trigger's one value, before its end.
    row : hev hD 0 h (out tt)
    row = (at-out , (h ∷ (s₁ ⊕ [ last ]) ∷ []) , λ { at-out _ _ → here refl ; (on-out at-end) _ _ → there (here refl) })
        , λ { (on-out at-end , _) → ≺→≼ {h} {s₁ ⊕ [ last ]} (Equivalence.from T-≡ (<ᵖ-part s₁ [] [] refl)) }

    hh : HotsAll (den-cons hD D) h
    hh = 0 , inj₁ (out tt , row)

------------------------------------------------------------------------
-- The hots in scope

-- Each hot's map onto its elaborated hot, one per cut.
Maps : List Set → Set₁
Maps Γ = ∀ {X} → X ∈ Γ → ℕ → HotMap

-- Two subscriptions cutting every hot in scope alike.
Aligned : ∀ {Γ} → Maps Γ → (ℕ → All Tb.Listed Γ) → Pos → Pos → Set₁
Aligned {Γ} Ψ ρ q q* = ∀ {X} (i : X ∈ Γ) N → Alike (Ψ i N) (Rows (lookup (ρ N) i)) q q*

aligned-r* : ∀ {Γ} {Ψ : Maps Γ} {ρ q q*} → Aligned Ψ ρ q q* → ∀ ys → Aligned Ψ ρ q (q* ⊕ˡ ys)
aligned-r* al ys i N = alike-r* (al i N) ys

aligned-⊕ : ∀ {Γ} {Ψ : Maps Γ} {ρ q q*} → Aligned Ψ ρ q q* → ∀ l l* → Aligned Ψ ρ (q ⊕ [ l ]) (q* ⊕ [ l* ])
aligned-⊕ al l l* i N = alike-r (alike-l (al i N) l) l*

-- Past an image, in its instant and under a position some pair aligns:
-- aligned there too.
aligned-past : ∀ {Γ} {Ψ : Maps Γ} {ρ q q* s L z} → Aligned Ψ ρ s L → L ≼ q* → q* ≺ z → L ⊑ z
             → instantOf q* ≡ instantOf z → Aligned Ψ ρ q q* → Aligned Ψ ρ q z
aligned-past aL Lq qz Lz iz al i N =
  alike (λ x un nl → cut-past Lq qz Lz iz (cut (al i N) x un nl) (cut (aL i N) x un nl))
        (λ x pl → cut-past Lq qz Lz iz (cut-put (al i N) x pl) (cut-put (aL i N) x pl))

------------------------------------------------------------------------
-- The scope's agreement

-- A fact at every index of a scope, as one small proposition.
AllIx : (Γ : List Set) → (∀ {X} → X ∈ Γ → Set) → Set
AllIx []      P = ⊤
AllIx (X ∷ Γ) P = P (here refl) × AllIx Γ (λ i → P (there i))

ix-at : ∀ {Γ} {P : ∀ {X} → X ∈ Γ → Set} → AllIx Γ P → ∀ {X} (i : X ∈ Γ) → P i
ix-at (p , _)  (here refl) = p
ix-at (_ , ps) (there i)   = ix-at ps i

ix-map : ∀ {Γ} {P Q : ∀ {X} → X ∈ Γ → Set} → (∀ {X} {i : X ∈ Γ} → P i → Q i) → AllIx Γ P → AllIx Γ Q
ix-map {[]}    f _        = tt
ix-map {X ∷ Γ} f (p , ps) = f p , ix-map f ps

-- Two cuts' hots in scope agreeing up to a position, plain and
-- elaborated.
Gs : ∀ {Γ} → (ℕ → All Tb.Listed Γ) → ℕ → ℕ → Pos → Set
Gs {Γ} ρ N N′ y = AllIx Γ λ i → AgreeTo y (Rows (lookup (ρ N) i)) (Rows (lookup (ρ N′) i))

Gs* : ∀ {Γ Δ} → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → ℕ → ℕ → Pos → Set
Gs* {Γ} ρι ρ* N N′ y = AllIx Γ λ i → AgreeTo y (Rows (lookup (ρ* N) (ρι (∈-map⁺ AIE i)))) (Rows (lookup (ρ* N′) (ρι (∈-map⁺ AIE i))))

scopeOf : ∀ {Γ Δ} → (ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → Scope
scopeOf ρ ρι ρ* = record
  { G = Gs ρ ; G* = Gs* ρι ρ*
  ; g-down = λ yy → ix-map (ag-down yy) ; g-sym = ix-map AgreeTo-sym
  ; g*-down = λ yy → ix-map (ag-down yy) ; g*-sym = ix-map AgreeTo-sym }

------------------------------------------------------------------------
-- The record and what it carries past the correspondence

-- A record's map at a cut, as a hot's.
relMap : ∀ {A} {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {p p* S} → Rel P Q p p* S → ℕ → HotMap
relMap {Q = Q} R N = hotMap (Rel.φ R N) (λ k l → Rel.Put R N k l × Σ _ λ e′ → TR (Q N) l e′) (Rel.Late R N)

-- Every row not late linked to its image and cutting every hot in scope
-- alike with it; and every pair before the subscription, cutting it
-- alike, cuts the stream's rows alike.
record Rest {Γ A} (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {p p* S}
            (R : Rel P Q p p* S) : Set₁ where
  field
    linked : ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Rel.Late R N k → Linked k (Rel.φ R N k)
    cuts   : ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Rel.Late R N k → Aligned Ψ ρ k (Rel.φ R N k)
    seen   : ∀ {q q*} → Aligned Ψ ρ q q* → Cut q q* p p* → q ≺ p → ∀ N → Alike (relMap R N) (TR (P N)) q q*

record Out {Γ Δ A} (n : ℕ) (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ)
           (Ψ : Maps Γ) (p p* : Pos) : Set₁ where
  constructor _⊢_
  field
    rel  : Rel (Tab n o ρ p) (Tab* n ρι o ρ* p*) p p* (scopeOf ρ ρι ρ*)
    rest : Rest Ψ ρ rel

-- A hot in scope: its two readers' record wherever they are subscribed
-- alike.
HotR : ∀ {Γ Δ X} → X ∈ Γ → (ρ : ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ρ* : ℕ → All Tb.Listed Δ) → Maps Γ → DenOf ρ → DenOf ρ* → Set₁
HotR i ρ ρι ρ* Ψ D D* = ∀ n p p* → Admits D p → Admits D* p* → Aligned Ψ ρ p p* → Linked p p* → Out n (connected i) ρ ρι ρ* Ψ p p*

record EnvR {Γ Δ} (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) : Set₁ where
  constructor envR
  field
    maps : Maps Γ
    lw   : DenOf ρ
    lw*  : DenOf ρ*
    hot  : ∀ {X} (i : X ∈ Γ) → HotR i ρ ρι ρ* maps lw lw*
    -- A hot's map is its readers' subscriptions', never their admissions'.
    hot-coh : ∀ {X} (i : X ∈ Γ) n p p* (a a′ : Admits lw p) (a* a*′ : Admits lw* p*) (al al′ : Aligned maps ρ p p*) (lk lk′ : Linked p p*) N y
            → Same (Out.rel (hot i n p p* a a* al lk)) (Out.rel (hot i n p p* a′ a*′ al′ lk′)) N y
    -- No elaborated hot a program reads ends a lane.
    unended : ∀ N → EnvU ρι (den lw* N)
open EnvR public

-- Wherever the two are subscribed alike, each admissibly.
Holds : ∀ {Γ Δ A} → ℕ → Obs Timeline Γ A → (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → EnvR ρ ρι ρ* → Set₁
Holds n o ρ ρι ρ* env = ∀ p p* → Admits (lw env) p → Admits (lw* env) p* → Aligned (maps env) ρ p p* → Linked p p* → Out n o ρ ρι ρ* (maps env) p p*

-- In every environment of uncut tables whose hots are related.
Full : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Set₁
Full {Γ} n o = ∀ (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N))
             → ∀ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → (∀ N → UncutEnv (ρ* N)) → (env : EnvR ρ ρι ρ*) → Holds n o ρ ρι ρ* env

-- Two environments whose hots map alike, however their readers are
-- admitted.
EnvEq : ∀ {Γ Δ} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} → EnvR ρ ρι ρ* → EnvR ρ ρι ρ* → Set₁
EnvEq {Γ} {ρ = ρ} E E′ = ∀ {X} (i : X ∈ Γ) n p p* (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*)
                 (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) N y
               → Same (Out.rel (hot E i n p p* a a* al lk)) (Out.rel (hot E′ i n p p* a′ a*′ al′ lk′)) N y

-- THE MAP IS THE SUBSCRIPTIONS': a record's map and its late rows are
-- had from its subscriptions and its environment's maps, never from how
-- either is admitted.  A flatMap's lane is related at each cut from that cut's
-- row, so two cuts' records of one lane are two records, which only
-- this relates.
Coh : ∀ {Γ A} n (o : Obs Timeline Γ A) → Full n o → Set₁
Coh {Γ} n o F = ∀ (ρ : ℕ → All Tb.Listed Γ) uρ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) uρ* (E E′ : EnvR ρ ρι ρ*) → EnvEq E E′
              → ∀ p p* (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*)
                  (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) N y
              → Same (Out.rel (F ρ uρ ρι ρ* uρ* E p p* a a* al lk)) (Out.rel (F ρ uρ ρι ρ* uρ* E′ p p* a′ a*′ al′ lk′)) N y

-- An elaborated binder no plain subterm reads changes no reader.
env-wk : ∀ {Γ Δ X} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} {t : ℕ → Tb.Listed X}
       → HotD t → EnvR ρ ρι ρ* → EnvR ρ (wk ρι) (λ N → t N ∷ ρ* N)
env-wk h env = envR (maps env) (lw env) (den-cons h (lw* env)) (λ i n p p* a a* al lk →
  let O = hot env i n p p* a (admits-wk h (lw* env) a*) al lk in Out.rel O ⊢ Out.rest O)
  (λ i n p p* a a′ a* a*′ al al′ lk lk′ → hot-coh env i n p p* a a′ (admits-wk h (lw* env) a*) (admits-wk h (lw* env) a*′) al al′ lk lk′)
  (λ N i → unended env N i)

-- Two environments whose hots map alike, weakened by two records of one
-- hot: their hots map alike.
env-wk-eq : ∀ {Γ Δ X} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} {t : ℕ → Tb.Listed X}
          → (h h′ : HotD t) {E E′ : EnvR ρ ρι ρ*} → EnvEq E E′ → EnvEq (env-wk h E) (env-wk h′ E′)
env-wk-eq h h′ {E} {E′} ee i n p p* a a′ a* a*′ al al′ lk lk′ =
  ee i n p p* a a′ (admits-wk h (lw* E) a*) (admits-wk h′ (lw* E′) a*′) al al′ lk lk′

-- An elaborated connect's hot ends no lane, wherever its scope's hots end none.
listHot-u : ∀ {Γ Δ X} n {ρι : Ren Γ Δ} (s : Obs Timeline Γ X) {ρ* : ℕ → All Tb.Listed Δ} (u : ∀ N → UncutEnv (ρ* N)) (D : DenOf ρ*) c a
          → (∀ N → EnvU ρι (den D N)) → ∀ N → AUndone (ES.hot (hev (listHot n (annotate (elab ρι s)) u D c a) N))
listHot-u n {ρι} s u D c a eu N p r with hot-out r
... | _ , (x , _) , _ = ann-u (3 + N) n (elab ρι s) (den D N) (elab-undone (3 + N) n ρι s (den D N) (eu N)) (c ⊕ [ ix 1 ]) x
