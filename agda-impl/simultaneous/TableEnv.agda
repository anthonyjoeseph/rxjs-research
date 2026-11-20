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
-- (`Rest`): every row is linked to its image, every shown row cuts every
-- hot in scope and the stream's own rows of every cut alike with its
-- image, and every pair cutting the subscription alike from before it
-- cuts the stream's rows alike.
--
-- An alike cut is checked up an instant's creators too (`Cut`): two
-- steps of one tick are ordered by their timers' creators, so a row of a
-- later instant is ordered against a hot's row by where the creators lie.
module simultaneous.TableEnv where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Bool.Properties using (T-≡)
open import Function using (_⇔_; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connected)
open import denotation.Position using (Pos; Label; _∙_; root; _≟ᵖ_; _⊕_; frame; cascade; inside; ix)
open import denotation.Events using (Timeline; fresh; <ᵖ-split)
open import denotation.EmissionSet using (EmissionSet; Ev; Unpinned; _≺_; _≼_; pin; out; DenEnv; enter)
import denotation.EmissionSet as ES
open import denotation.Laws.Modulus using (≺-trans; ≺-ext; ≺-absurd; ≼-or-≻; ≼-false)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc; ⊑-refl; ⊑-trans; ⊑-snoc⁺; ⊑-snoc; Ok; InvAt; GoodEnv; Hots; Lawful; ok-step; W;
  W⁼; step; timer; join; here; inW; real-snoc; plain-ix; shrink; ok-in; _∪ʰ_)
open import denotation.Laws.Count using (child)
open import denotation.Laws.Cut using (inv-capprox; inv-sub)
open import denotation.Laws using (good-cons)
import denotation.Laws.Connect as Cn
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rejoin)
open import quickcheck.Tabled.Exact using (EnvRel; _∷_)
import quickcheck.Tabled.Exact as Ex
open import quickcheck.Tabled.Exact.Base using (Exactly; sound)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.ElabUndone using (EnvU)
open import simultaneous.Listing using (listC; listC-ok; listC-exact; UncutEnv)
open import simultaneous.ListTR using (tr-at)
open import simultaneous.ListPin using (listC-pin)
open import simultaneous.ListAfter using (listC-past; listC-pinpast)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.TableCorr using (Rel; Same)
open import simultaneous.TableKit using (Rows; TR; Got)
open import simultaneous.Horizon using (Tag; module Cuts)
open import simultaneous.HorizonCorr using (module Inter; Btw; PB; Own; OwnPut)
open import simultaneous.HorizonTree using (BdEnv; _∷ᵇ_; bd)

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

-- An event a reader shows: a value or an end.
shownᵇ : ∀ {X : Set} → ES.Ev X → Bool
shownᵇ (out _) = true
shownᵇ ES.end  = true
shownᵇ _       = false

-- A position seen from one subscription as its image is from the other:
-- the image past the other when the position is past the one, and,
-- where the position is shown (`b`), back; in its instant exactly when
-- the image is in the other's; and under neither.
--
-- An unshown position need not come back.  A cut that truncates a lane
-- shows a flatMap's outer end as a skip where a longer cut shows its
-- end, and a reader images the two apart: the end at the annotation's
-- end, under `ix 1`, the skip under its own `sub`.  So a row of one cut
-- whose image lies between the two is past the skip's image though not
-- past its position.  What such a skip's image is past, the reader's
-- elaborated table shows only as an unshown row.
Lvl : Bool → Pos → Pos → Pos → Pos → Set
Lvl b q q* y y* = (q ≺ y → q* ≺ y*) × (T b → q* ≺ y* → q ≺ y) × (instantOf y ≡ instantOf q ⇔ instantOf y* ≡ instantOf q*)
                × ¬ (q ⊑ y) × ¬ (q* ⊑ y*)

-- And so every creator up its instants, each step of one tick and label.
data Cut (b : Bool) (q q* : Pos) : Pos → Pos → Set where
  at-frame : ∀ {y y*} → Lvl b q q* y y* → instantOf y ≡ frame → instantOf y* ≡ frame → Cut b q q* y y*
  at-step  : ∀ {y y* t c c* l} → Lvl b q q* y y* → instantOf y ≡ cascade t c l → instantOf y* ≡ cascade t c* l
           → Cut true q q* c c* → Cut b q q* y y*

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
    cut     : ∀ {k e} → t k e → Unpinned e → ¬ late h k → Cut (shownᵇ e) q q* k (ψ h k)
    cut-put : ∀ {k e l} → t k e → π h k l → Cut false q q* k l
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

lvl-l : ∀ {b q q* y y*} → Lvl b q q* y y* → ∀ l → Lvl b (q ⊕ [ l ]) q* y y*
lvl-l {b} {q} {q*} {y} {y*} (to , fr , ie , nq , nq*) l =
  (λ h → to (≺-trans {q} {q ⊕ [ l ]} {y} (≺-ext q []) h))
  , (λ t h → down q l (fr t h) nq)
  , subst₂ (λ a b → instantOf y ≡ a ⇔ instantOf y* ≡ b) (sym (inst-⊕ q [ l ])) refl ie
  , (λ u → nq (up⊑ q l u)) , nq*

lvl-r : ∀ {b q q* y y*} → Lvl b q q* y y* → ∀ l* → Lvl b q (q* ⊕ [ l* ]) y y*
lvl-r {b} {q} {q*} {y} {y*} (to , fr , ie , nq , nq*) l* =
  (λ h → down q* l* (to h) nq*)
  , (λ t h → fr t (≺-trans {q*} {q* ⊕ [ l* ]} {y*} (≺-ext q* []) h))
  , subst₂ (λ a b → instantOf y ≡ a ⇔ instantOf y* ≡ b) refl (sym (inst-⊕ q* [ l* ])) ie
  , nq , (λ u → nq* (up⊑ q* l* u))

cut-l : ∀ {b q q* y y*} → Cut b q q* y y* → ∀ l → Cut b (q ⊕ [ l ]) q* y y*
cut-l (at-frame v a b)   l = at-frame (lvl-l v l) a b
cut-l (at-step v a b c)  l = at-step (lvl-l v l) a b (cut-l c l)

cut-r : ∀ {b q q* y y*} → Cut b q q* y y* → ∀ l* → Cut b q (q* ⊕ [ l* ]) y y*
cut-r (at-frame v a b)   l* = at-frame (lvl-r v l*) a b
cut-r (at-step v a b c)  l* = at-step (lvl-r v l*) a b (cut-r c l*)

-- A ROW NOT OVER THE CUT STAYS CUT ALIKE ONE LABEL DOWN: nothing strictly
-- between a position and its child lies outside the position.
lvl-sub : ∀ {b q q* y y*} → Lvl b q q* y y* → ¬ (y* ⊑ q*) → ∀ l → Lvl b q q* y (y* ⊕ [ l ])
lvl-sub {b} {q} {q*} {y} {y*} (to , fr , ie , nq , nq*) ny l =
  (λ h → ≺-trans {q*} {y*} {y* ⊕ [ l ]} (to h) (≺-ext y* []))
  , (λ t h → fr t (back h))
  , subst (λ a → instantOf y ≡ instantOf q ⇔ a ≡ instantOf q*) (sym (inst-⊕ y* [ l ])) ie
  , nq , nsub
  where
    nsub : ¬ (q* ⊑ (y* ⊕ [ l ]))
    nsub u with ⊑-snoc y* u
    ... | inj₁ v  = nq* v
    ... | inj₂ eq = ny (subst (y* ⊑_) (sym eq) (⊑-snoc⁺ y*))

    back : q* ≺ (y* ⊕ [ l ]) → q* ≺ y*
    back h with ≼-or-≻ q* y*
    ... | inj₂ yq with child l yq
    ...   | inj₁ u  = ⊥-elim (ny u)
    ...   | inj₂ lt = ⊥-elim (≺-absurd {q*} {y* ⊕ [ l ]} h lt)
    back h | inj₁ qy with <ᵖ-split q* y* (≼-false {q*} {y*} qy)
    ... | inj₁ lt   = Equivalence.from T-≡ lt
    ... | inj₂ refl = ⊥-elim (nq* (⊑-refl q*))

cut-sub : ∀ {b q q* y y*} → Cut b q q* y y* → ¬ (y* ⊑ q*) → ∀ l → Cut b q q* y (y* ⊕ [ l ])
cut-sub {y* = y*} (at-frame v a b)  n l = at-frame (lvl-sub v n l) a (trans (inst-⊕ y* [ l ]) b)
cut-sub {y* = y*} (at-step v a b c) n l = at-step (lvl-sub v n l) a (trans (inst-⊕ y* [ l ]) b) c

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

------------------------------------------------------------------------
-- The emission sets the tables list

-- Each cut's hots listed exactly off a lawful environment, so a table's
-- func and flat are its denotation's, read at an admissible subscription.
--
-- Each hot's connect subscribes its body at `dlo` over hot rows `dH`:
-- the scope's, and the hot's own.  The scope's later hots' rows lie in
-- that world (`dnest`), and no position of it leads the hot's
-- boundaries (`dlead`).
--
-- DEAD ROUTE: func and flat over an arbitrary aligned environment.  A hot
--   row the alignment exempts may sit in the subscription's world, and the
--   table then lists rows the invariant does not cover.
record DenOf {Γ} (ρ : ℕ → All Tb.Listed Γ) : Set₁ where
  constructor denOf
  field
    den    : ℕ → DenEnv Γ
    den-ex : ∀ N → EnvRel (ρ N) (den N)
    den-ok : ∀ N → GoodEnv (den N)
    dlo    : ∀ {X : Set} → X ∈ Γ → Pos
    dH     : ∀ {X : Set} → X ∈ Γ → Pos → Set
    dbd      : BdEnv Γ
    dbounded : ∀ {X : Set} (i : X ∈ Γ) → Cuts.Bounded (λ N → Rows (lookup (ρ N) i)) (dbd i)
    dnest    : ∀ {X : Set} (i : X ∈ Γ) {h} → (Σ ℕ λ N → Hots (den N) h) → dH i h ⊎ W (dH i) (dlo i) h
    dlead    : ∀ {X : Set} (i : X ∈ Γ) {N b g w} → dbd i N b g → W⁼ (dH i) (dlo i) w → ¬ w ⊑ b
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

-- A world reached from one whose hot rows lie in another's lies in it.
mutual
  transfer : ∀ {H H′ : Pos → Set} {f x w} → (∀ {h} → H h → H′ h ⊎ W H′ f h) → W⁼ H′ f x → W H x w → W H′ f w
  transfer t fx (step w l)           = step (transfer⁼ t fx w) l
  transfer t fx (timer i w lt pl)    = timer i (transfer⁼ t fx w) lt pl
  transfer t fx (join (inj₁ h) w eh) = join (t h) (transfer⁼ t fx w) eh
  transfer t fx (join (inj₂ v) w eh) = join (inj₂ (transfer t fx v)) (transfer⁼ t fx w) eh

  transfer⁼ : ∀ {H H′ : Pos → Set} {f x w} → (∀ {h} → H h → H′ h ⊎ W H′ f h) → W⁼ H′ f x → W⁼ H x w → W⁼ H′ f w
  transfer⁼ t fx here    = fx
  transfer⁼ t fx (inW w) = inW (transfer t fx w)

-- Fewer hot rows, still admissible.
ok-mono : ∀ {H H′ : Pos → Set} {p} → (∀ {h} → H h → H′ h) → Ok H′ p → Ok H p
ok-mono f (r , dj) = r , λ hh w i → dj (f hh) (w-mono f w) i

-- Every cut's hot rows.
HotsAll : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → Set
HotsAll D h = Σ ℕ λ N → Hots (den D N) h

-- No hots: nothing listed, nothing to keep.
none : DenOf {[]} (λ _ → All.[])
none = denOf (λ _ → All.[]) (λ _ → Ex.[]) (λ _ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ())

-- One fact per scope entry, by recursion: a product indexed over `Set`
-- would not be small.
Each : ∀ {Γ : List Set} → (∀ {X : Set} → X ∈ Γ → Set) → Set
Each {[]}    P = ⊤
Each {_ ∷ Γ} P = P (here refl) × Each {Γ} (λ i → P (there i))

each-at : ∀ {Γ : List Set} {P : ∀ {X : Set} → X ∈ Γ → Set} → Each P → ∀ {X : Set} (i : X ∈ Γ) → P i
each-at {_ ∷ Γ} (x , _)  (here refl) = x
each-at {_ ∷ Γ} (_ , xs) (there i)   = each-at xs i

each : ∀ {Γ : List Set} {P : ∀ {X : Set} → X ∈ Γ → Set} → (∀ {X : Set} (i : X ∈ Γ) → P i) → Each P
each {[]}    f = tt
each {_ ∷ Γ} f = f (here refl) , each (λ i → f (there i))

-- In the world of each hot's body.
Inside : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → Set
Inside D p = Each (λ i → W⁼ (dH D i) (dlo D i) p)

-- Its family named, for a scope whose `Each` has already unfolded.
inside-at : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → (∀ {X : Set} (i : X ∈ Γ) → W⁼ (dH D i) (dlo D i) p) → Inside D p
inside-at D f = each f

-- ADMISSIBLE: reachable, and no cut's hot row in its world.  Every cut's
-- at once, because a lane subscribed under a row of one cut is read at
-- every cut, where that row's world may join other cuts' rows.  And in
-- each hot's scope: in its connect's body's world.
Admits : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} → DenOf ρ → Pos → Set
Admits D p = Ok (HotsAll D) p × Inside D p

-- A hot's boundary is led by no position of a world reached from its
-- body's, nor of an admissible reader's.
scope-lead : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {X : Set} (i : X ∈ Γ) {N b g} → dbd D i N b g
           → ∀ {H : Pos → Set} {x w} → (∀ {h} → H h → dH D i h ⊎ W (dH D i) (dlo D i) h) → W⁼ (dH D i) (dlo D i) x → W⁼ H x w → ¬ w ⊑ b
scope-lead D i bd t fx v = dlead D i bd (transfer⁼ t fx v)

reader-lead : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → Admits D p → ∀ {X : Set} (i : X ∈ Γ) {N b g} → dbd D i N b g
            → ∀ {M w} → W⁼ (Hots (den D M)) p w → ¬ w ⊑ b
reader-lead D a i bd {M} v = scope-lead D i bd (λ hh → dnest D i (M , hh)) (each-at (proj₂ a) i) v

admits-at : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → Admits D p → ∀ N → Ok (Hots (den D N)) p
admits-at D a N = ok-mono (λ hh → N , hh) (proj₁ a)

admits-step : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} → Admits D p → Admits D (p ⊕ [ ix 1 ])
admits-step D {p} (o , fp) = ok-step p o , each (λ i → inW (step (each-at fp i) plain-ix))

admits-ix : ∀ {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {p} i → Admits D p → Admits D (p ⊕ [ ix i ])
admits-ix D {p} i ((r , dj) , fp) = (real-snoc p plain-ix r , λ hh w ins → dj hh (shrink w) ins) , each (λ j → inW (step (each-at fp j) plain-ix))

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
  each (λ i → inW (step (inW (transfer (λ hh → dnest D i (N , hh)) (each-at (proj₂ a) i) (InvAt.world I x))) plain-ix))
  where I = tab-at n o u D a N

-- A hot of the scope `D`, listed exactly off a lawful emission set: its
-- source subscribed at `hat ⊕ [ ix 1 ]`, its rows in that world, its
-- boundaries led by no position of its body's world.
record HotD {Γ} {ρ : ℕ → All Tb.Listed Γ} (D : DenOf ρ) {X : Set} (t : ℕ → Tb.Listed X) : Set₁ where
  constructor hotD
  field
    hev  : ℕ → EmissionSet X
    hex  : ∀ N p → Exactly (rejoin p (t N)) (enter (ES.hot (hev N)) p)
    hlaw : ∀ N → Lawful (hev N)
    hat  : Pos
    hadm : Admits D hat
    hin  : ∀ N {h e} → hev N h e → W (HotsAll D) (hat ⊕ [ ix 1 ]) h
    hbd      : ℕ → Pos → Tag → Set
    hbounded : Cuts.Bounded (λ N → Rows (t N)) hbd
    hlead    : ∀ {N b g w} → hbd N b g → W⁼ (HotsAll D ∪ʰ (λ h e → Σ ℕ λ N → hev N h e)) (hat ⊕ [ ix 0 ]) w → ¬ w ⊑ b
open HotD public

den-cons : ∀ {Γ X} {t : ℕ → Tb.Listed X} {ρ : ℕ → All Tb.Listed Γ} {D : DenOf ρ} → HotD D t → DenOf (λ N → t N ∷ ρ N)
den-cons {Γ} {X} {t = t} {ρ = ρ} {D} h =
  denOf (λ N → ES.hot (hev h N) ∷ den D N) (λ N → hex h N ∷ den-ex D N) (λ N → good-cons (hlaw h N) (den-ok D N))
    lo′ H′ (hbd h ∷ᵇ dbd D) db dn dl
  where
    σ∞ : EmissionSet X
    σ∞ k e = Σ ℕ λ N → hev h N k e

    lo′ : ∀ {Y : Set} → Y ∈ X ∷ Γ → Pos
    lo′ (here refl) = hat h ⊕ [ ix 0 ]
    lo′ (there i)   = dlo D i

    H′ : ∀ {Y : Set} → Y ∈ X ∷ Γ → Pos → Set
    H′ (here refl) = HotsAll D ∪ʰ σ∞
    H′ (there i)   = dH D i

    db : ∀ {Y : Set} (i : Y ∈ _ ∷ _) → Cuts.Bounded (λ N → Rows (lookup (t N ∷ ρ N) i)) ((hbd h ∷ᵇ dbd D) i)
    db (here refl) = hbounded h
    db (there i)   = dbounded D i

    dn : ∀ {Y : Set} (i : Y ∈ X ∷ Γ) {k} → (Σ ℕ λ N → Hots (ES.hot (hev h N) ∷ den D N) k) → H′ i k ⊎ W (H′ i) (lo′ i) k
    dn (here refl) (N , inj₁ (e , x)) = inj₁ (inj₁ (e , N , x))
    dn (here refl) (N , inj₂ hh)      = inj₁ (inj₂ (N , hh))
    dn (there i)   (N , inj₁ (e , x)) = inj₂ (transfer (dnest D i) (inW (step (each-at (proj₂ (hadm h)) i) plain-ix)) (hin h N x))
    dn (there i)   (N , inj₂ hh)      = dnest D i (N , hh)

    dl : ∀ {Y : Set} (i : Y ∈ X ∷ Γ) {N b g w} → (hbd h ∷ᵇ dbd D) i N b g → W⁼ (H′ i) (lo′ i) w → ¬ w ⊑ b
    dl (here refl) = hlead h
    dl (there i)   = dlead D i

-- One hot more, a world no smaller.
admits-wk : ∀ {Γ X} {t : ℕ → Tb.Listed X} {ρ : ℕ → All Tb.Listed Γ} {D : DenOf ρ} (h : HotD D t) {p} → Admits (den-cons h) p → Admits D p
admits-wk h (o , fp) = ok-mono (λ { (N , hh) → N , inj₂ hh }) o , proj₂ fp

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

------------------------------------------------------------------------
-- The record and what it carries past the correspondence

-- A record's map at a cut, as a hot's.
relMap : ∀ {A} {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {p p*} → Rel P Q p p* → ℕ → HotMap
relMap {Q = Q} R N = hotMap (Rel.φ R N) (λ k l → Rel.Put R N k l × Σ _ λ e′ → TR (Q N) l e′) (Rel.Late R N)

-- A table's rows but those under a position.
Off : ∀ {X : Set} → Pos → EmissionSet X → EmissionSet X
Off k t y e = t y e × ¬ (k ⊑ y)

-- Every hot in scope cut alike by a pair: its rows before the one exactly
-- when their images are before the other, its placements before.
EnvCut : ∀ {Γ} → Maps Γ → (ℕ → All Tb.Listed Γ) → ℕ → Pos → Pos → Set
EnvCut {[]}    Ψ ρ N z z* = ⊤
EnvCut {_ ∷ Γ} Ψ ρ N z z* =
  (Btw (Own (Rows (All.head (ρ N))) (late (Ψ (here refl) N))) (ψ (Ψ (here refl) N)) z z*
   × PB (OwnPut (Rows (All.head (ρ N))) (π (Ψ (here refl) N))) z z*)
  × EnvCut {Γ} (λ i → Ψ (there i)) (λ N′ → All.tail (ρ N′)) N z z*

-- Every row not late linked to its image; every shown row cutting every
-- hot in scope alike with it, and the stream's own rows of every cut
-- but those under it, which no cut has; a shown row's image one in every
-- cut showing it; and every pair before the subscription, cutting it
-- alike, cuts the stream's rows alike.  The stream's boundaries have
-- partners whose pairs cut every hot in scope alike too (`bcorr-env`):
-- a connect's body reads its source as a hot, and its boundaries must
-- cut the source's rows as they cut its own.
--
-- The stream's own rows are what a reader of it reads once a connect
-- shares it, so a reader's shown row cuts that hot alike by the source's
-- `self`, carried one label down.
record Rest {Γ A} (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {p p*}
            (R : Rel P Q p p*) : Set₁ where
  field
    linked    : ∀ N {k e} → TR (P N) k e → Unpinned e → ¬ Rel.Late R N k → Linked k (Rel.φ R N k)
    cuts      : ∀ N {k e} → TR (P N) k e → T (shownᵇ e) → Aligned Ψ ρ k (Rel.φ R N k)
    self      : ∀ N {k e} → TR (P N) k e → T (shownᵇ e) → ∀ N′ → Alike (relMap R N′) (Off k (TR (P N′))) k (Rel.φ R N k)
    self-at   : ∀ {N N′ k e e′} → TR (P N) k e → T (shownᵇ e) → TR (P N′) k e′ → T (shownᵇ e′) → Rel.φ R N k ≡ Rel.φ R N′ k
    self-flat : ∀ {N N′ k e l ys e′} → TR (P N) k e → T (shownᵇ e) → TR (P N′) (k ⊕ (l ∷ ys)) e′ → ⊥
    seen      : ∀ {q q*} → Aligned Ψ ρ q q* → Cut true q q* p p* → q ≺ p → ∀ N → Alike (relMap R N) (TR (P N)) q q*
    bcorr-env : ∀ N → Inter.BCorrX (Own (TR (P N)) (Rel.Late R N)) (Rel.φ R N) (OwnPut (TR (P N)) (Rel.Put R N)) (Rel.Bd R N) (Rel.Bd* R N)
                                   (EnvCut Ψ ρ N)

-- Two families holding the same boundaries.
record SameBd (Bd Bd′ : ℕ → Pos → Tag → Set) : Set where
  constructor sameBd
  field
    to   : ∀ {N b g} → Bd N b g → Bd′ N b g
    from : ∀ {N b g} → Bd′ N b g → Bd N b g
open SameBd public

same-bd : ∀ {Bd : ℕ → Pos → Tag → Set} → SameBd Bd Bd
same-bd = sameBd (λ x → x) (λ x → x)

-- A SUBTERM'S RECORD, its boundaries its tree's on both sides (`bd-pin`,
-- `bd-pin*`): a join's pair is its parts' pairs at the tree's boundaries.
record Out {Γ Δ A} (n : ℕ) (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (ρι : Ren Γ Δ)
           (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N)) (Ψ : Maps Γ) (D : DenOf ρ) (D* : DenOf ρ*) (p p* : Pos) : Set₁ where
  constructor out
  field
    rel  : Rel (Tab n o ρ p) (Tab* n ρι o ρ* p*) p p*
    rest : Rest Ψ ρ rel
    bd-pin  : SameBd (Rel.Bd rel) (bd n o ρ uρ (dbd D) p)
    bd-pin* : SameBd (Rel.Bd* rel) (bd n (elab ρι o) ρ* uρ* (dbd D*) p*)

-- A hot in scope: its two readers' record wherever they are subscribed
-- alike.
HotR : ∀ {Γ Δ X} → X ∈ Γ → (ρ : ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ρ* : ℕ → All Tb.Listed Δ) → Maps Γ → DenOf ρ → DenOf ρ* → Set₁
HotR i ρ ρι ρ* Ψ D D* = ∀ uρ uρ* n p p* → Admits D p → Admits D* p* → Aligned Ψ ρ p p* → Linked p p* → Out n (connected i) ρ uρ ρι ρ* uρ* Ψ D D* p p*

record EnvR {Γ Δ} (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) : Set₁ where
  constructor envR
  field
    maps : Maps Γ
    lw   : DenOf ρ
    lw*  : DenOf ρ*
    hot  : ∀ {X} (i : X ∈ Γ) → HotR i ρ ρι ρ* maps lw lw*
    -- A hot's map is its readers' subscriptions', never their admissions'.
    hot-coh : ∀ {X} (i : X ∈ Γ) uρ uρ* n p p* (a a′ : Admits lw p) (a* a*′ : Admits lw* p*) (al al′ : Aligned maps ρ p p*) (lk lk′ : Linked p p*) N y
            → Same (Out.rel (hot i uρ uρ* n p p* a a* al lk)) (Out.rel (hot i uρ uρ* n p p* a′ a*′ al′ lk′)) N y
    -- No elaborated hot a program reads ends a lane.
    unended : ∀ N → EnvU ρι (den lw* N)
open EnvR public

-- Wherever the two are subscribed alike, each admissibly.
Holds : ∀ {Γ Δ A} → ℕ → Obs Timeline Γ A → (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N)) → (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ)
      → (∀ N → UncutEnv (ρ* N)) → EnvR ρ ρι ρ* → Set₁
Holds n o ρ uρ ρι ρ* uρ* env = ∀ p p* → Admits (lw env) p → Admits (lw* env) p* → Aligned (maps env) ρ p p* → Linked p p*
                             → Out n o ρ uρ ρι ρ* uρ* (maps env) (lw env) (lw* env) p p*

-- In every environment of uncut tables whose hots are related.
Full : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Set₁
Full {Γ} n o = ∀ (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N))
             → ∀ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) (uρ* : ∀ N → UncutEnv (ρ* N)) → (env : EnvR ρ ρι ρ*) → Holds n o ρ uρ ρι ρ* uρ* env

-- Two environments whose hots map alike, however their readers are
-- admitted.
EnvEq : ∀ {Γ Δ} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} → EnvR ρ ρι ρ* → EnvR ρ ρι ρ* → Set₁
EnvEq {Γ} {ρ = ρ} E E′ = ∀ {X} (i : X ∈ Γ) uρ uρ* n p p* (a : Admits (lw E) p) (a′ : Admits (lw E′) p) (a* : Admits (lw* E) p*) (a*′ : Admits (lw* E′) p*)
                 (al : Aligned (maps E) ρ p p*) (al′ : Aligned (maps E′) ρ p p*) (lk lk′ : Linked p p*) N y
               → Same (Out.rel (hot E i uρ uρ* n p p* a a* al lk)) (Out.rel (hot E′ i uρ uρ* n p p* a′ a*′ al′ lk′)) N y

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
       → (env : EnvR ρ ρι ρ*) → HotD (lw* env) t → EnvR ρ (wk ρι) (λ N → t N ∷ ρ* N)
env-wk env h = envR (maps env) (lw env) (den-cons h) (λ i uρ uρ* n p p* a a* al lk →
  let O = hot env i uρ (λ N → proj₂ (uρ* N)) n p p* a (admits-wk h a*) al lk in out (Out.rel O) (Out.rest O) (Out.bd-pin O) (Out.bd-pin* O))
  (λ i uρ uρ* n p p* a a′ a* a*′ al al′ lk lk′ →
     hot-coh env i uρ (λ N → proj₂ (uρ* N)) n p p* a a′ (admits-wk h a*) (admits-wk h a*′) al al′ lk lk′)
  (λ N i → unended env N i)

-- Two environments whose hots map alike, weakened by two records of one
-- hot: their hots map alike.
env-wk-eq : ∀ {Γ Δ X} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} {t : ℕ → Tb.Listed X}
          → {E E′ : EnvR ρ ρι ρ*} (h : HotD (lw* E) t) (h′ : HotD (lw* E′) t) → EnvEq E E′ → EnvEq (env-wk E h) (env-wk E′ h′)
env-wk-eq {E = E} {E′} h h′ ee i uρ uρ* n p p* a a′ a* a*′ al al′ lk lk′ =
  ee i uρ (λ N → proj₂ (uρ* N)) n p p* a a′ (admits-wk h a*) (admits-wk h′ a*′) al al′ lk lk′
