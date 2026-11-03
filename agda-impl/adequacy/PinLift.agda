{-# OPTIONS --guardedness #-}

-- A PIN CARRIED UP: a pin under its connect, waiting on finitely many
-- rows, shows one frame up at or under its row, still waiting on
-- finitely many.  Each former places the rows it reads at or under rows
-- it shows, so what a pin waits on above is the image of what it waits
-- on below, but for the rows before its connect, which a cursor past the
-- connect has behind it.
module adequacy.PinLift where

open import Data.Bool using (T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-map⁺)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import denotation.Events using (Pos; ix; last; inside)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; pin; _≺_; _≼_; Dep; Reach; Few; MapT; map-out; map-skip; map-pin; map-end;
  module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺→≼)
open import adequacy.Cursor using (Cur; Owes; Behind; _≈_; cov; voc)
open import adequacy.Bound using (owes-≼)

------------------------------------------------------------------------
-- What a pin waits on, split: every row before its connect, and its own
-- pins before it.

-- The pins of `r` before `y`, few.
PinFew : ∀ {A} → EmissionSet A → Pos → Pos → Set
PinFew E r y = Σ (List Pos) λ ks → ∀ {k} → E k (pin r) → k ≺ y → k ∈ ks

reach-few : ∀ {A} {E : EmissionSet A} {y r} → T (inside r y) → Few E r → PinFew E r y → Reach E y (pin r)
reach-few i (ks , f) (ls , g) = ks ++ ls , λ x ky d → [ (λ kr → ∈-++⁺ˡ (f x kr)) , (λ { refl → ∈-++⁺ʳ ks (g x ky) }) ]′ (d i)

-- A pin's wait, read without its connect: its own pins before it.
few-pin : ∀ {A} {E : EmissionSet A} {y r} → T (inside r y) → Reach E y (pin r) → PinFew E r y
few-pin i (ks , f) = ks , λ x ky → f x ky (λ _ → inj₂ refl)

-- Passed at `C`, a connect: every row before it.
before-few : ∀ {A} {C} {E : EmissionSet A} {r} → Behind C E → ¬ Owes C r → Few E r
before-few {C = C} {r = r} (ks , f) nr = ks , λ {k} x kr → f x (λ o → nr (owes-≼ C o (≺→≼ {k} {r} kr)))

------------------------------------------------------------------------
-- Images

-- Every row of `E′` at a row of `E` at its position, its pins kept.
reach-img : ∀ {A B} {E : EmissionSet A} {E′ : EmissionSet B} {y r}
          → (∀ {k e′} → E′ k e′ → Σ (Ev A) λ e → E k e × (e′ ≡ pin r → e ≡ pin r))
          → Reach E y (pin r) → Reach E′ y (pin r)
reach-img im (ks , f) = ks , λ x ky d → let (_ , x′ , pp) = im x in f x′ ky λ i → [ inj₁ , (λ eq → inj₂ (pp eq)) ]′ (d i)

reach-≈ : ∀ {A} {E E′ : EmissionSet A} {y e} → E ≈ E′ → Reach E y e → Reach E′ y e
reach-≈ m (ks , f) with cov m
... | ls , g = ls ++ ks , λ x ky d → [ (λ x′ → ∈-++⁺ʳ ls (f x′ ky d)) , ∈-++⁺ˡ ]′ (g x)

reach-map : ∀ {A B} {f : A → B} {E : EmissionSet A} {y r} → Reach E y (pin r) → Reach (MapT f E) y (pin r)
reach-map = reach-img λ where
  (map-out x)  → _ , x , λ ()
  (map-skip x) → _ , x , λ ()
  (map-pin x)  → _ , x , λ { refl → refl }
  (map-end x)  → _ , x , λ ()

acc-row : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} {q b} → Scan.Acc f z E q b → Σ A λ a → E q (out a)
acc-row (Scan.acc₀ x _)    = _ , x
acc-row (Scan.acc _ x _ _) = _ , x

reach-scan : ∀ {A B} {f : B → A → B} {z} {E : EmissionSet A} {y r} → Reach E y (pin r) → Reach (Scan.ScanT f z E) y (pin r)
reach-scan = reach-img λ where
  (Scan.sval a)  → let (_ , x) = acc-row a in _ , x , λ ()
  (Scan.sstep x) → _ , x , λ ()
  (Scan.spin x)  → _ , x , λ { refl → refl }
  (Scan.send x)  → _ , x , λ ()
