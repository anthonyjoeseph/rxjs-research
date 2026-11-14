{-# OPTIONS --guardedness #-}

-- A FOLD FROM A LISTING: where the rows before a value are listed, each
-- with its row, which of them holds a value is decided by the row, so the
-- latest value among them is found and the fold constructed.
module simultaneous.ReadFold where

open import Data.Bool.Properties using (T?)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import denotation.Position using (Pos; _<ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; _≺_; module Scan)
open import denotation.Laws.Modulus using (≼-refl; ≼-or-≻; ≼-trans; ≺→≼; ≺-trans; few-ind)
open import denotation.Laws.Fold using (Latest)

-- The latest position before `w` among `ks` where a decided `P` holds.
latestᵈ : ∀ (P : Pos → Set) w ks → (∀ {k} → k ∈ ks → Dec (P k)) → Latest P w ks
latestᵈ P w []       d = inj₁ λ ()
latestᵈ P w (k ∷ ks) d = add (latestᵈ P w ks (λ m → d (there m))) (dk (d (here refl)) (T? (k <ᵖ w)))
  where
    dk : Dec (P k) → Dec (k ≺ w) → Dec (P k × k ≺ w)
    dk (yes a) (yes b) = yes (a , b)
    dk (no ¬a) _       = no λ (a , _) → ¬a a
    dk _       (no ¬b) = no λ (_ , b) → ¬b b

    add : Latest P w ks → Dec (P k × k ≺ w) → Latest P w (k ∷ ks)
    add (inj₁ none) (no ¬h) = inj₁ λ { {_} (here refl) vk kw → ¬h (vk , kw) ; {_} (there m) → none m }
    add (inj₂ (v , vv , vw , mx)) (no ¬h) =
      inj₂ (v , vv , vw , λ { {_} (here refl) vk kw → ⊥-elim (¬h (vk , kw)) ; {_} (there m) → mx m })
    add (inj₁ none) (yes (vk , kw)) =
      inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {_} (there m) vk′ k′w → ⊥-elim (none m vk′ k′w) })
    add (inj₂ (v , vv , vw , mx)) (yes (vk , kw)) with ≼-or-≻ v k
    ... | inj₁ vk≼ = inj₂ (k , vk , kw , λ { {_} (here refl) _ _ → ≼-refl {k} ; {k′} (there m) vk′ k′w → ≼-trans {k′} {v} {k} (mx m vk′ k′w) vk≼ })
    ... | inj₂ kv  = inj₂ (v , vv , vw , λ { {_} (here refl) _ _ → ≺→≼ {k} {v} kv ; {_} (there m) → mx m })

module _ {A B : Set} (f : B → A → B) (z : B) (t : EmissionSet A) (fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
  open Scan f z t using (Acc; acc₀; acc)

  Val : Pos → Set
  Val k = Σ A λ a → t k (out a)

  -- A row decides whether its position holds a value.
  val? : ∀ {k} → Σ (Ev A) (t k) → Dec (Val k)
  val? (out a , x) = yes (a , x)
  val? (skip , x)  = no λ (_ , y) → skip≢ (fu x y)
    where skip≢ : ∀ {a} → skip ≡ out a → ⊥
          skip≢ ()
  val? (end , x)   = no λ (_ , y) → end≢ (fu x y)
    where end≢ : ∀ {a} → end ≡ out a → ⊥
          end≢ ()
  val? (pin r , x) = no λ (_ , y) → pin≢ (fu x y)
    where pin≢ : ∀ {a} → pin r ≡ out a → ⊥
          pin≢ ()

  -- THE FOLD, from rows listed before the value.
  module _ (ks : List Pos) (rows : ∀ {k} → k ∈ ks → Σ (Ev A) (t k)) where

    Folds : Pos → Set
    Folds w = (∀ {k e} → t k e → k ≺ w → k ∈ ks) → ∀ {a} → t w (out a) → Σ B (Acc w)

    foldᵈ : ∀ {w} → (∀ {k e} → t k e → k ≺ w → k ∈ ks) → ∀ {a} → t w (out a) → Σ B (Acc w)
    foldᵈ {w} cov = few-ind {t = t} Folds step (ks , cov) cov
      where
        step : ∀ {w} → _ → (∀ {v e} → t v e → v ≺ w → Folds v) → Folds w
        step {w} _ ih cov {a} x with latestᵈ Val w ks (λ m → val? (rows m))
        ... | inj₁ none = f z a , acc₀ x λ y kw → none (cov y kw) (_ , y) kw
        ... | inj₂ (v , (_ , xv) , vw , mx) with ih xv vw (λ {k} y kv → cov y (≺-trans {k} {v} {w} kv vw)) xv
        ...   | b , av = f b a , acc av x vw λ y vk kw → mx (cov y kw) (_ , y) kw vk
