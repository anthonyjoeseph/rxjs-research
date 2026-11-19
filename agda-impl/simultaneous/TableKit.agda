{-# OPTIONS --guardedness #-}

-- A CUT PROGRAM'S TABLE READ AS RUNS (`TR`), and what two runs share:
-- shape (`Sh`), truncation before they differ (`Cons`), agreement by
-- induction on rows (`ag-ind`), the match of a plain event with its image
-- (`M`).
module simultaneous.TableKit where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; EmissionSet; Few; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; few-ind; ≼-refl; ≺→≼; ≺-≼-≺; ≼-≺-≺; ≼-split)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (rows; bind)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Attribution using (Every; One; Reads; Match; Shown)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

-- An event's value mapped, its constructor kept.
ev : ∀ {A B : Set} → (A → B) → Ev A → Ev B
ev f (out a) = out (f a)
ev f skip    = skip
ev f end     = end
ev f (pin r) = pin r

-- A run's shape: where its rows lie, and of what constructor.
Sh : ∀ {X : Set} → EmissionSet X → EmissionSet ⊤
Sh {X} a y e = Σ (Ev X) λ e₀ → a y e₀ × e ≡ ev (λ _ → tt) e₀

-- Agreement between runs carries to runs holding the same rows.
ag-≃ : ∀ {X : Set} {a a′ b b′ : EmissionSet X} {q}
     → (∀ {k e} → a k e → a′ k e) → (∀ {k e} → a′ k e → a k e) → (∀ {k e} → b k e → b′ k e) → (∀ {k e} → b′ k e → b k e)
     → AgreeTo q a b → AgreeTo q a′ b′
ag-≃ f f′ g g′ ⟨ a ⟩ = ⟨ (λ {y} {e} yq → (λ x → g (proj₁ (a {y} {e} yq) (f′ x))) , (λ x → f (proj₂ (a {y} {e} yq) (g′ x)))) ⟩

-- Two runs are truncated before they differ: agreeing below a value of
-- the first where the scope agrees (`G`), the second holding a row at or
-- past it, the second holds it.
Cons : ∀ {X : Set} → (Pos → Set) → EmissionSet X → EmissionSet X → Set
Cons {X} G a b = ∀ {y y′ e′} {v : X} → G y → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b) → a y (out v) → b y′ e′ → y ≼ y′ → b y (out v)

-- AGREEMENT BY INDUCTION ON ROWS: two runs with few rows below each
-- position agree up to `k` once they agree at each position up to it
-- that everything before agrees below.
ag-ind : ∀ {X : Set} {a b : EmissionSet X} {k} → (∀ q → Few (λ y e → a y e ⊎ b y e) q)
       → (∀ {y} → y ≼ k → (∀ {y₀} → y₀ ≺ y → AgreeTo y₀ a b) → ∀ {e} → (a y e → b y e) × (b y e → a y e))
       → AgreeTo k a b
ag-ind {X} {a} {b} {k} fin step = few-ind {t = λ y e → a y e ⊎ b y e} P go (fin k) (≼-refl {k})
  where
    P : Pos → Set
    P w = w ≼ k → AgreeTo w a b

    go : ∀ {w} → Few (λ y e → a y e ⊎ b y e) w → (∀ {v e} → a v e ⊎ b v e → v ≺ w → P v) → P w
    go {w} _ ih wk = ⟨ at ⟩
      where
        before : ∀ {y e} → y ≺ w → (a y e → b y e) × (b y e → a y e)
        before {y} lt = (λ x → proj₁ (upto (ih (inj₁ x) lt yk) (≼-refl {y})) x) , (λ x → proj₂ (upto (ih (inj₂ x) lt yk) (≼-refl {y})) x)
          where yk = ≺→≼ {y} {k} (≺-≼-≺ {y} {w} {k} lt wk)

        below : ∀ {y₀} → y₀ ≺ w → AgreeTo y₀ a b
        below {y₀} lt = ⟨ (λ {y} yy₀ → before (≼-≺-≺ {y} {y₀} {w} yy₀ lt)) ⟩

        at : ∀ {y e} → y ≼ w → (a y e → b y e) × (b y e → a y e)
        at {y} yw with ≼-split {y} {w} yw
        ... | inj₁ lt   = before lt
        ... | inj₂ refl = step wk below

-- Rows of a cut program's table.
Rows : ∀ {X : Set} → Tb.Listed X → Pos → Ev X → Set
Rows L k e = (k , e) ∈ rows L

-- A table there is.
Got : ∀ {X : Set} → Maybe (Tb.Listed X) → Set
Got {X} m = Σ (Tb.Listed X) λ L → m ≡ just L

-- A table read on is one.
got-bind : ∀ {X Y : Set} {m : Maybe (Tb.Listed X)} (g : Tb.Listed X → Tb.Listed Y) → Got m → Got (bind m λ l → just (g l))
got-bind g (L , refl) = g L , refl

-- Rows of a table, if there is one.
TR : ∀ {X : Set} → Maybe (Tb.Listed X) → EmissionSet X
TR {X} m k e = Σ (Tb.Listed X) λ L → m ≡ just L × Rows L k e

M : ∀ {A : Set} → Ev A → Ev (IE A) → Set
M = Match Every (One valuesOf) (Reads valuesOf)

-- A matched end is an end.
ends : ∀ {A : Set} {e : Ev A} → Unpinned e → M e end → e ≡ end
ends {e = out a} _ (c , _) with c tt
... | _ , () , _
ends {e = skip} _ (_ , d) = ⊥-elim (d (λ ()) tt)
ends {e = end} _ _ = refl

-- A shown elaborated value is matched by the value it reads.
m-back : ∀ {A : Set} {e : Ev A} {x : IE A} → Unpinned e → M e (out x) → Shown (One valuesOf) (out x)
       → Σ A λ a → e ≡ out a × valuesOf x ≡ a ∷ []
m-back {e = out a} _ (c , _) _ with c tt
... | _ , refl , rd = a , refl , rd
m-back {e = skip} _ (_ , d) sh = ⊥-elim (d (λ ()) sh)
m-back {e = end} _ (c , _) _ with c tt
... | ()

m-val : ∀ {A : Set} {a : A} {x : IE A} → valuesOf x ≡ a ∷ [] → M (out a) (out x)
m-val rd = (λ _ → _ , refl , rd) , (λ n → ⊥-elim (n tt))

m-ee : ∀ {A : Set} → M {A} end end
m-ee = (λ _ → refl) , (λ n → ⊥-elim (n tt))

m-ss : ∀ {A : Set} → M {A} skip skip
m-ss = (λ ()) , (λ _ ())

