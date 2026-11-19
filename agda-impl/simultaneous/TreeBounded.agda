{-# OPTIONS --guardedness #-}

-- EVERY PROGRAM'S CUTS ARE BOUNDED BY ITS TREE'S BOUNDARIES
-- (`tree-bounded`): a row before every boundary of a cut is a row of
-- every deeper cut, so of the meaning, and nothing decides where the
-- program hangs.  One induction over the tree, in any lawful scope whose
-- hots hang at their own boundaries (`Hung`), at any admissible
-- subscription; it reads no elaboration, so it bounds a plain program
-- and its elaboration alike.
--
-- Each case is its former's: a leaf never moves, a spin has its next
-- tick (`SpinB`), a map keeps its child's rows in place, a take is
-- `TakeB`'s, a connect `ConnB`'s over its source and its body in the
-- scope the source's hot extends, a reader `RejoinB`'s over its hot.
--
-- A source's boundaries past its subscription (`src-after`, `src-held`)
-- are owed of every tree, a hot's reader among them, whose boundaries
-- are its hot's and may precede it.
module simultaneous.TreeBounded where

open import Data.Bool using (Bool)
open import Data.List using (List; _∷_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; FlatOp; Later; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Position using (Pos; ix; last; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; pin; Rejoin; _≺_; _≼_; module Connecting)
open import denotation.Laws.Modulus using (⟨_⟩; upto)
open import denotation.Laws.Worlds using (_⊑_)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf; rejoin; bind; scanRows)
open import quickcheck.Tabled.Exact using (rejoin-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; sound; complete)
open import simultaneous.Listing using (listC; listC-ok; UncutEnv; Uncut)
open import simultaneous.TableKit using (Rows; TR; ev)
open import simultaneous.TableCorr using (keys; in-keys)
open import simultaneous.TableMap using (map-bounded)
open import simultaneous.TableScan using (scan-bounded)
open import simultaneous.TableTake using (tr-take→; tr-take←; failed?)
open import simultaneous.TableEnv using (Hung; hot-bounded; hot-apart; DenOf; Admits; admits-step; admits-body; admits-wk; listHot; den-cons; tab-func; tab-flat; pin-ok)
open import simultaneous.Horizon using (Tag; held; module Cuts; module SpinB; module TakeB; module ConnB; module RejoinB; const-bounded; bounded-≃)
open import simultaneous.HorizonTree using (Cut; srcL; bodyρ; bodyU; BdEnv; _∷ᵇ_; bd; cold-bd)

------------------------------------------------------------------------
-- A reader's table is its hot's, rejoined

private
  rj : ∀ {X : Set} (L : Tb.Listed X) p → Σ (Tb.Listed X) (λ x → just (rejoin p L) ≡ just x × Uncut x) → Exact (rejoin p L) (Rejoin p (Rows L))
  rj L p (_ , refl , u) = rejoin-exact {l = L} {t = Rows L} (λ _ → record { sound = λ m → m ; complete = λ m → m }) p u

------------------------------------------------------------------------
-- The leaves owed

postulate
  -- A COLD'S CUTS: the listing stops short of the timeline only at its
  -- boundaries.
  cold-bounded : ∀ {Γ A} n (c : Timeline A) (ρ : ℕ → All Tb.Listed Γ) p → Cuts.Bounded (Cut n (cold c) ρ p) (cold-bd c p)

  -- A HOT'S ROWS are its source's proper rows, cut where the source is.
  hot-rows-bounded : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {Bd : ℕ → Pos → Tag → Set}
                   → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd → Cuts.Bounded (λ N → Rows (hotOf (srcL n s uρ p N))) Bd

  -- A CONNECT'S TABLE is the connect of its parts'.
  conn-tr→ : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
           → Cut n (connect s b) ρ p N y e → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e
  conn-tr← : ∀ {Γ A B} n (s : Obs Timeline Γ A) (b : Obs Timeline (A ∷ Γ) B) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {N y e}
           → Connecting.ConnT p (Cut n s ρ (p ⊕ [ ix 1 ]) N) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]) N) y e → Cut n (connect s b) ρ p N y e

module _ {Γ} (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (β : BdEnv Γ) (D : DenOf ρ) (H : Hung ρ D β) where
  postulate
    -- A SOURCE'S BOUNDARIES lie past its subscription, and so do the
    -- connects its held ones wait on.
    src-after : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → ∀ {N b g} → bd n s ρ uρ β (p ⊕ [ ix 1 ]) N b g → (p ⊕ [ ix 1 ]) ≺ b
    src-held  : ∀ {A} n (s : Obs Timeline Γ A) p → Admits D p → ∀ {N b q} → bd n s ρ uρ β (p ⊕ [ ix 1 ]) N b (held q) → (p ⊕ [ ix 1 ]) ≼ q

    -- A SOURCE'S BOUNDARIES lie apart from the late end of any reader of
    -- its hot.
    src-apart : ∀ {A} n (s : Obs Timeline Γ A) p (a : Admits D p) {q} → Admits (den-cons (listHot n s uρ D p a) D) q
              → ∀ {N b g} → bd n s ρ uρ β (p ⊕ [ ix 1 ]) N b g → ¬ b ⊑ (q ⊕ [ last ]) × ¬ (q ⊕ [ last ]) ⊑ b

    -- A JOIN'S CUTS: its outer's boundaries, and each running lane's
    -- before the lane's cut.
    join-bounded : ∀ {A B} n (op : FlatOp) (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p → Admits D p
                 → Cuts.Bounded (Cut n (flatMap op f s) ρ p) (bd n (flatMap op f s) ρ uρ β p)

    -- A DEFER'S CUTS: its marker under its first label, apart from every
    -- boundary of its body, subscribed one label down.
    later-bounded : ∀ {A} n (l : Later Timeline Γ A) p → Admits D p
                  → Cuts.Bounded (Cut (suc n) (defer l) ρ p) (bd (suc n) (defer l) ρ uρ β p)

------------------------------------------------------------------------
-- Every tree

-- The scope a connect's body reads hangs: the source's hot at the
-- source's boundaries, the rest as before.
hung-body : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) (β : BdEnv Γ) (D : DenOf ρ) (H : Hung ρ D β)
          → ∀ p (a : Admits D p) → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) (bd n s ρ uρ β (p ⊕ [ ix 1 ]))
          → Hung (bodyρ n s uρ p) (den-cons (listHot n s uρ D p a) D) (bd n s ρ uρ β (p ⊕ [ ix 1 ]) ∷ᵇ β)
hung-body n s {ρ} uρ β D H p a Bσ = record { hot-bounded = hb ; hot-apart = ha }
  where
    D′ = den-cons (listHot n s uρ D p a) D
    β′ = bd n s ρ uρ β (p ⊕ [ ix 1 ]) ∷ᵇ β

    hb : ∀ {X : Set} (i : X ∈ _ ∷ _) → Cuts.Bounded (λ N → Rows (lookup (bodyρ n s uρ p N) i)) (β′ i)
    hb (here refl) = hot-rows-bounded n s uρ p Bσ
    hb (there i)   = hot-bounded H i

    ha : ∀ {X : Set} (i : X ∈ _ ∷ _) {q} → Admits D′ q → ∀ {N b g} → β′ i N b g → ¬ b ⊑ (q ⊕ [ last ]) × ¬ (q ⊕ [ last ]) ⊑ b
    ha (here refl) aq {N} {b} {g} = src-apart ρ uρ β D H n s p a aq {N} {b} {g}
    ha (there i)   aq {N} {b} {g} = hot-apart H i (admits-wk (listHot n s uρ D p a) D aq) {N} {b} {g}

-- EVERY TREE'S CUTS ARE BOUNDED BY ITS BOUNDARIES.
tree-bounded : ∀ {Γ A} n (o : Obs Timeline Γ A) (ρ : ℕ → All Tb.Listed Γ) (uρ : ∀ N → UncutEnv (ρ N)) (β : BdEnv Γ) (D : DenOf ρ) → Hung ρ D β
             → ∀ p → Admits D p → Cuts.Bounded (Cut n o ρ p) (bd n o ρ uρ β p)
tree-bounded n       (cold c)          ρ uρ β D H p a = cold-bounded n c ρ p
tree-bounded n       empty             ρ uρ β D H p a = const-bounded _
tree-bounded n       (of xs)           ρ uρ β D H p a = const-bounded _
tree-bounded n       (map f s)         ρ uρ β D H p a = map-bounded f (λ N → listC (3 + N) n s (ρ N) p) (tree-bounded n s ρ uρ β D H p a)
tree-bounded n       (scan f z s)      ρ uρ β D H p a = scan-bounded f z (λ N → listC (3 + N) n s (ρ N) p) (tree-bounded n s ρ uρ β D H p a)
tree-bounded n       (takeWhile i q s) ρ uρ β D H p a =
  bounded-≃ (λ {N} → tr-take← i q (listC (3 + N) n s (ρ N) p)) (λ {N} → tr-take→ i q (listC (3 + N) n s (ρ N) p))
    (TakeB.bounded′ i q (Cut n s ρ p) (bd n s ρ uρ β p)
      (λ N → record { func = tab-func n s uρ D a {N} ; flat = tab-flat n s uρ D a {N} ; pin-in = pin-ok (3 + N) n s p })
      (λ N → failed? i q (listC (3 + N) n s (ρ N) p))
      (λ N w → keys (listC (3 + N) n s (ρ N) p) , λ x _ → in-keys x)
      (tree-bounded n s ρ uρ β D H p a))
tree-bounded n       (flatMap op f s)  ρ uρ β D H p a = join-bounded ρ uρ β D H n op f s p a
tree-bounded n       (connect s b)     ρ uρ β D H p a =
  bounded-≃ (λ {N} {y} {e} → conn-tr← n s b uρ p {N} {y} {e}) (λ {N} {y} {e} → conn-tr→ n s b uρ p {N} {y} {e})
    (ConnB.bounded p (Cut n s ρ (p ⊕ [ ix 1 ])) (Cut n b (bodyρ n s uρ p) (p ⊕ [ ix 0 ]))
      (bd n s ρ uρ β (p ⊕ [ ix 1 ]))
      (bd n b (bodyρ n s uρ p) (bodyU n s uρ p) (bd n s ρ uρ β (p ⊕ [ ix 1 ]) ∷ᵇ β) (p ⊕ [ ix 0 ]))
      Bσ
      (tree-bounded n b (bodyρ n s uρ p) (bodyU n s uρ p) (bd n s ρ uρ β (p ⊕ [ ix 1 ]) ∷ᵇ β)
        (den-cons (listHot n s uρ D p a) D) (hung-body n s uρ β D H p a Bσ) (p ⊕ [ ix 0 ]) (admits-body n s uρ D p a))
      (λ {N} {b′} {g} → src-after ρ uρ β D H n s p a {N} {b′} {g})
      (λ {N} {b′} {q} → src-held ρ uρ β D H n s p a {N} {b′} {q}))
  where
    Bσ = tree-bounded n s ρ uρ β D H (p ⊕ [ ix 1 ]) (admits-step D a)
tree-bounded n       (connected i)     ρ uρ β D H p a =
  bounded-≃ (λ {N} {y} {e} x → rejoin p (lookup (ρ N) i) , refl , complete (ex N) x)
            (λ {N} {y} {e} → λ { (_ , refl , m) → sound (ex N) m })
    (RejoinB.bounded-j p (λ N → Rows (lookup (ρ N) i)) (β i) (hot-bounded H i) (λ {N} {b} {g} → hot-apart H i a {N} {b} {g}))
  where
    ex : ∀ N → Exact (rejoin p (lookup (ρ N) i)) (Rejoin p (Rows (lookup (ρ N) i)))
    ex N = rj (lookup (ρ N) i) p (listC-ok (3 + N) n (connected i) (uρ N) p)
tree-bounded zero    (defer l)         ρ uρ β D H p a = SpinB.bounded p
tree-bounded (suc n) (defer l)         ρ uρ β D H p a = later-bounded ρ uρ β D H n l p a
