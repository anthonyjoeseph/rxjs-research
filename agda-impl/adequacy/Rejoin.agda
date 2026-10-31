{-# OPTIONS --guardedness #-}
-- A JOINER'S INBOX STAYS ASCENDING: a feed appends rows in its source's
-- order, and a lawful hot's rows, none below another, keep that order
-- once each is rejoined under one `sub j`.  An admissible scope makes
-- every handle such a hot.
module adequacy.Rejoin where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (lookup)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import denotation.Events using (Pos; ix; sub)
open import denotation.EmissionSet using (EmissionSet; _≺_; hot; Proper; Den; ⟦_⟧)
open import denotation.Laws.Modulus using (≺-trans; ≺-irrefl; ≺-ext)
open import denotation.Laws.Worlds using (Lawful; GoodEnv)
open import denotation.Laws.Count using (child)
open import denotation.Laws.HotInv using (lawful-hot)
open import denotation.Laws using (inv-⟦⟧; good-cons)
import denotation.Laws.Connect as LC
open import operation.PureObservable using (module Machine)
open Machine using (Scope; unbound; binds)
open import adequacy.Rows using (full)
open import adequacy.Cursor using (Adm)

-- Rows of a lawful hot, rejoined at one joiner, keep their order.
rejoin-mono : ∀ {A} {t : EmissionSet A} → Lawful t → ∀ {y y′ e e′} j → t y e → t y′ e′ → y ≺ y′
            → (y ++ [ sub j ]) ≺ (y′ ++ [ sub j ])
rejoin-mono {t = t} L {y} {y′} j x x′ lt with child (sub j) lt
... | inj₂ lt′ = ≺-trans {y ++ [ sub j ]} {y′} {y′ ++ [ sub j ]} lt′ (≺-ext y′ [])
... | inj₁ ([] , eq) = ⊥-elim (≺-irrefl {y} (subst (λ z → y ≺ z) (trans eq (++-identityʳ y)) lt))
... | inj₁ (l ∷ ys , eq) = ⊥-elim (Lawful.flat L x (subst (λ z → t z _) eq x′))

good-full : ∀ {Γ} (sc : Scope Γ) → Adm sc → GoodEnv (full sc)
good-full unbound        _        ()
good-full (binds o p sc) (ok , a) = good-cons (LC.lawful {s = ⟦ o ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ o (full sc) g) (λ L → lawful-hot L) p ok) g
  where g = good-full sc a

-- Each handle of an admissible scope is a lawful hot.
lawful-at : ∀ {Γ A} (sc : Scope Γ) → Adm sc → (x : A ∈ Γ) → Σ (EmissionSet A) λ t → lookup (full sc) x ≡ hot t × Lawful t
lawful-at (binds o p sc) (ok , a) (here refl) = _ , refl , LC.lawful {s = ⟦ o ⟧ (full sc)} {F = λ h → h} (inv-⟦⟧ o (full sc) (good-full sc a)) (λ L → lawful-hot L) p ok
lawful-at (binds o p sc) (ok , a) (there x)   = lawful-at sc a x
