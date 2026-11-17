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

open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; _∷_; lookup)
open import Data.List.Relation.Unary.Any using (there)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Function using (_⇔_; mk⇔; Equivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst₂)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; connected)
open import denotation.Position using (Pos; Label; _∙_; root; _≟ᵖ_; _⊕_; frame; cascade)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Unpinned; _≺_)
open import denotation.Laws.Modulus using (≺-trans; ≺-ext)
open import denotation.Laws.Worlds using (_⊑_; ⊕-assoc)
open import denotation.Laws.Count using (child)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.Readings using (instantOf)
open import simultaneous.TakeCut using (inst-⊕)
open import simultaneous.TableCorr using (Rel; Rows; TR)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab)

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

-- A table's rows cut alike, along a map.
record Alike {X : Set} (ψ : Pos → Pos) (t : EmissionSet X) (q q* : Pos) : Set where
  constructor alike
  field cut : ∀ {k e} → t k e → Unpinned e → Cut q q* k (ψ k)
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

alike-l : ∀ {X : Set} {ψ : Pos → Pos} {t : EmissionSet X} {q q*} → Alike ψ t q q* → ∀ l → Alike ψ t (q ⊕ [ l ]) q*
alike-l a l = alike λ x un → cut-l (cut a x un) l

alike-r : ∀ {X : Set} {ψ : Pos → Pos} {t : EmissionSet X} {q q*} → Alike ψ t q q* → ∀ l* → Alike ψ t q (q* ⊕ [ l* ])
alike-r a l* = alike λ x un → cut-r (cut a x un) l*

alike-r* : ∀ {X : Set} {ψ : Pos → Pos} {t : EmissionSet X} {q q*} → Alike ψ t q q* → ∀ ys → Alike ψ t q (q* ⊕ˡ ys)
alike-r* a []       = a
alike-r* a (l ∷ ls) = alike-r* (alike-r a l) ls

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
-- The hots in scope

-- Each hot's map onto its elaborated hot, one per cut.
Maps : List Set → Set₁
Maps Γ = ∀ {X} → X ∈ Γ → ℕ → Pos → Pos

-- Two subscriptions cutting every hot in scope alike.
Aligned : ∀ {Γ} → Maps Γ → (ℕ → All Tb.Listed Γ) → Pos → Pos → Set₁
Aligned {Γ} Ψ ρ q q* = ∀ {X} (i : X ∈ Γ) N → Alike (Ψ i N) (Rows (lookup (ρ N) i)) q q*

aligned-r* : ∀ {Γ} {Ψ : Maps Γ} {ρ q q*} → Aligned Ψ ρ q q* → ∀ ys → Aligned Ψ ρ q (q* ⊕ˡ ys)
aligned-r* al ys i N = alike-r* (al i N) ys

aligned-⊕ : ∀ {Γ} {Ψ : Maps Γ} {ρ q q*} → Aligned Ψ ρ q q* → ∀ l l* → Aligned Ψ ρ (q ⊕ [ l ]) (q* ⊕ [ l* ])
aligned-⊕ al l l* i N = alike-r (alike-l (al i N) l) l*

------------------------------------------------------------------------
-- The record and what it carries past the correspondence

-- Every row linked to its image; cutting every hot in scope alike with
-- it; the stream's own rows cut alike just under each row and its image;
-- and every pair before the subscription, cutting it alike, cuts the
-- stream's rows alike.
record Rest {Γ A} (Ψ : Maps Γ) (ρ : ℕ → All Tb.Listed Γ) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))} {p p*}
            (R : Rel P Q p p*) : Set₁ where
  field
    linked : ∀ N {k e} → TR (P N) k e → Unpinned e → Linked k (Rel.φ R N k)
    cuts   : ∀ N {k e} → TR (P N) k e → Unpinned e → Aligned Ψ ρ k (Rel.φ R N k)
    self   : ∀ N {k e} → TR (P N) k e → Unpinned e → ∀ l l* N′ → Alike (Rel.φ R N′) (TR (P N′)) (k ⊕ [ l ]) (Rel.φ R N k ⊕ [ l* ])
    seen   : ∀ {q q*} → Aligned Ψ ρ q q* → Cut q q* p p* → q ≺ p → ∀ N → Alike (Rel.φ R N) (TR (P N)) q q*

record Out {Γ Δ A} (n : ℕ) (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ)
           (Ψ : Maps Γ) (p p* : Pos) : Set₁ where
  constructor _⊢_
  field
    rel  : Rel (Tab n o ρ p) (Tab* n ρι o ρ* p*) p p*
    rest : Rest Ψ ρ rel

-- A hot in scope: its two readers' record wherever they are subscribed
-- alike.
HotR : ∀ {Γ Δ X} → X ∈ Γ → (ℕ → All Tb.Listed Γ) → Ren Γ Δ → (ℕ → All Tb.Listed Δ) → Maps Γ → Set₁
HotR i ρ ρι ρ* Ψ = ∀ n p p* → Aligned Ψ ρ p p* → Linked p p* → Out n (connected i) ρ ρι ρ* Ψ p p*

record EnvR {Γ Δ} (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) : Set₁ where
  constructor envR
  field
    maps : Maps Γ
    hot  : ∀ {X} (i : X ∈ Γ) → HotR i ρ ρι ρ* maps
open EnvR public

-- Wherever the two are subscribed alike.
Holds : ∀ {Γ Δ A} → ℕ → Obs Timeline Γ A → (ρ : ℕ → All Tb.Listed Γ) (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → EnvR ρ ρι ρ* → Set₁
Holds n o ρ ρι ρ* env = ∀ p p* → Aligned (maps env) ρ p p* → Linked p p* → Out n o ρ ρι ρ* (maps env) p p*

-- In every environment of uncut tables whose hots are related.
Full : ∀ {Γ A} → ℕ → Obs Timeline Γ A → Set₁
Full {Γ} n o = ∀ (ρ : ℕ → All Tb.Listed Γ) → (∀ N → UncutEnv (ρ N))
             → ∀ {Δ} (ρι : Ren Γ Δ) (ρ* : ℕ → All Tb.Listed Δ) → (∀ N → UncutEnv (ρ* N)) → (env : EnvR ρ ρι ρ*) → Holds n o ρ ρι ρ* env

-- An elaborated binder no plain subterm reads changes no reader.
env-wk : ∀ {Γ Δ X} {ρ : ℕ → All Tb.Listed Γ} {ρι : Ren Γ Δ} {ρ* : ℕ → All Tb.Listed Δ} (t : ℕ → Tb.Listed X)
       → EnvR ρ ρι ρ* → EnvR ρ (wk ρι) (λ N → t N ∷ ρ* N)
env-wk t env = envR (maps env) λ i n p p* al lk → let O = hot env i n p p* al lk in Out.rel O ⊢ Out.rest O
