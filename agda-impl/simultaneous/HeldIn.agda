{-# OPTIONS --guardedness #-}

-- HELD AS FAR AS A READER GETS: `Held`, its runs and positions taken
-- only where `D` holds.  A connect shows its body only where its source
-- has few rows before, so its body need hold no further: past a lane of
-- the source that loops, the body reads on in rows the connect never
-- reaches.
module simultaneous.HeldIn where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _++_; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Data.List.Properties using (∷-injective)
open import Relation.Nullary using (¬_)
open import Data.Empty using (⊥)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; Few; _≼_)
open import denotation.Read using (Visible; After; cursor)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; completed)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (rootOf)
open import simultaneous.Relations using (Met; values)
open import simultaneous.Shut using (r₀)
open import simultaneous.Routed using (Held; Carried; cnt; Ex; nameOf; Routing; Early; Valued; opos)
open import denotation.Laws.Worlds using (_⊑_)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; count)
import Data.List as L

-- Two ways to cut one list.
++-split : ∀ {B : Set} (xs ys r₁ r₂ : List B) → xs ++ ys ≡ r₁ ++ r₂
         → (Σ (List B) λ m → r₁ ≡ xs ++ m × ys ≡ m ++ r₂) ⊎ (Σ (List B) λ m → xs ≡ r₁ ++ m × r₂ ≡ m ++ ys)
++-split []       ys r₁       r₂ eq = inj₁ (r₁ , refl , eq)
++-split (x ∷ xs) ys []       r₂ eq = inj₂ (x ∷ xs , refl , sym eq)
++-split (x ∷ xs) ys (z ∷ r₁) r₂ eq with ∷-injective eq
... | refl , eq′ with ++-split xs ys r₁ r₂ eq′
...   | inj₁ (m , e₁ , e₂) = inj₁ (m , cong (x ∷_) e₁ , e₂)
...   | inj₂ (m , e₁ , e₂) = inj₂ (m , cong (x ∷_) e₁ , e₂)

-- Every row of a run lies where `D` holds.
Upto : ∀ {X : Set} → (Pos → Set) → List (Pos × Ev X) → Set
Upto D rs = ∀ {k e} → (k , e) ∈ rs → D k

-- `Idle`, at a wait where `D` holds, after a run where it does.
IdleIn : ∀ {A} → (Pos → Set) → EmissionSet (IE A) → Set
IdleIn D t = ∀ {rs} → Met t rs → Upto D rs → (∀ {c} → (c , end) ∈ rs → ⊥) → ∀ {w} → D w → Few t w → After (cursor nothing rs) w
           → (∀ {y e} → t y e → Visible e → After (cursor nothing rs) y → w ≼ y)
           → proj₂ (cnt rs) ≡ 0 ⊎ proj₁ (cnt rs) ≡ nameOf w

-- `Rest`, past a run where `D` holds.
RestIn : ∀ {A} → (Pos → Set) → EmissionSet (IE A) → Set
RestIn D t = ∀ {rs} → Met t rs → Upto D rs → proj₂ (cnt rs) ≡ 0 → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (cnt rs)))) ∈ rs
           → Σ (List Pos) λ ks → ∀ {y e} → t y e → After (cursor nothing rs) y → rootOf y ≡ rootOf q → y ∈ ks

record HeldIn {A : Set} (D : Pos → Set) (t : EmissionSet (IE A)) (cs : List Pos) : Set where
  field
    named   : ∀ {y n} → t y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    covered : ∀ {rs} → Met t rs → Upto D rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex cs y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    exact   : ∀ {rs} → Met t rs → Upto D rs → ∀ r₁ {y n} r₂ → rs ≡ r₁ ++ (y , out (instEmit (mark stop) n)) ∷ r₂
            → Σ ℕ λ k → proj₂ (cnt r₁) ≡ suc k
    routing : ∀ {y m n} → t y (out (instEmit (mark m) n)) → Routing m
    shut    : ∀ {rs} → Met t rs → Upto D rs → ∀ r₁ r₂ → rs ≡ r₁ ++ r₂ → proj₂ (L.foldl count r₀ (values r₁)) ≡ 0
            → ∀ {q} → (q , out (instEmit (mark begin) (proj₁ (L.foldl count r₀ (values r₁))))) ∈ r₁
            → ∀ {y a j} → (y , out (instEmit (value a) j)) ∈ r₂ → rootOf y ≡ rootOf q → ⊥
    early   : ∀ {y a n} → t y (out (instEmit (value a) n)) → Early y
    ends    : ∀ {y} → t y end → Early y
    done    : ∀ {y n} → t y (out (instEmit (mark completed) n)) → Early y
    late    : ∀ {y n} → t y (out (instEmit (mark over) n)) → Valued (rootOf y) × opos (rootOf y) ⊑ y
    idle    : IdleIn D t
    rest    : RestIn D t

-- What holds everywhere holds where `D` does.
held-in : ∀ {A} {D : Pos → Set} {t : EmissionSet (IE A)} {cs} → Held t cs → HeldIn D t cs
held-in H = record
  { named   = Held.named H
  ; covered = λ m _ → Held.covered H m
  ; exact   = λ m _ → Held.exact H m
  ; routing = Held.routing H
  ; shut    = λ m _ → Held.shut H m
  ; early   = Held.early H
  ; ends    = Held.ends H
  ; done    = Held.done H
  ; late    = Held.late H
  ; idle    = λ m _ ne _ → Held.idle H m ne
  ; rest    = λ m _ → Held.rest H m }
