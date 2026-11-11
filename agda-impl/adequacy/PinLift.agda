{-# OPTIONS --guardedness #-}

-- A PIN CARRIED UP: a pin under its connect, waiting on finitely many
-- rows, shows one frame up at or under its row, still waiting on
-- finitely many.  Each former places the rows it reads at or under rows
-- it shows, so what a pin waits on above is the image of what it waits
-- on below, but for the rows before its connect, which a cursor past the
-- connect has behind it.
module adequacy.PinLift where

open import Data.Bool using (T)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; [_]; _++_; concatMap)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ; ∈-concatMap⁺)
open import Data.List.Relation.Unary.Any using (here; there) renaming (map to any-map)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; ix; last; inside; _⊕_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; pin; _≺_; _≼_; Reach; Few; MapT; map-out; map-skip; map-pin; map-end;
  module Scan; module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺→≼; ≼-refl; ≼-≺-≺)
open import adequacy.Cursor using (_≈_; cov)

------------------------------------------------------------------------
-- What a pin waits on, split: every row before its connect, and its own
-- pins before it.

-- The pins of `r` before `y`, few.
PinFew : ∀ {A} → EmissionSet A → Pos → Pos → Set
PinFew E r y = Σ (List Pos) λ ks → ∀ {k} → E k (pin r) → k ≺ y → k ∈ ks

reach-few : ∀ {A} {E : EmissionSet A} {y r} → T (inside r y) → Few E r → PinFew E r y → Reach E y (pin r)
reach-few i (ks , f) (ls , g) = ks ++ ls , λ x ky d → [ (λ kr → ∈-++⁺ˡ (f x kr)) , (λ { refl → ∈-++⁺ʳ ks (g x ky) }) ]′ (d i)

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

-- Every row of `E′` at or under a row of `E`, among its `g`-images, its
-- pins kept in place.
reach-mv : ∀ {A B} {E : EmissionSet A} {E′ : EmissionSet B} {y r} (g : Pos → List Pos)
         → (∀ {k′ e′} → E′ k′ e′ → Σ Pos λ k → Σ (Ev A) λ e → E k e × k ≼ k′ × k′ ∈ g k × (e′ ≡ pin r → e ≡ pin r))
         → Reach E y (pin r) → Reach E′ y (pin r)
reach-mv {y = y} {r = r} g im (ks , f) = concatMap g ks , λ {k′} x ky d → let (k , _ , x′ , le , m , pp) = im x in
  ∈-concatMap⁺ g (any-map (λ { refl → m }) (f x′ (≼-≺-≺ {k} {k′} {y} le ky) (λ i → [ (λ lt → inj₁ (≼-≺-≺ {k} {k′} {r} le lt)) , (λ eq → inj₂ (pp eq)) ]′ (d i))))

-- A take's rows: at its source's, or one under it.
tk : Pos → List Pos
tk k = k ∷ (k ⊕ [ ix 0 ]) ∷ (k ⊕ [ last ]) ∷ []

reach-take : ∀ {A} {incl} {keep : A → Bool} {E : EmissionSet A} {y r} → Reach E y (pin r) → Reach (TakeWhile.TakeT incl keep E) y (pin r)
reach-take = reach-mv tk λ where
  (TakeWhile.pass {q} x _ _)   → q , _ , x , ≼-refl {q} , here refl , λ ()
  (TakeWhile.fail {q} x _ _ _) → q , _ , x , ≺→≼ {q} {q ⊕ [ ix 0 ]} (≺-ext q []) , there (here refl) , λ ()
  (TakeWhile.stop {q} x _ _)   → q , _ , x , ≺→≼ {q} {q ⊕ [ last ]} (≺-ext q []) , there (there (here refl)) , λ ()
  (TakeWhile.step {q} x _)     → q , _ , x , ≼-refl {q} , here refl , λ ()
  (TakeWhile.tend {q} x _)     → q , _ , x , ≼-refl {q} , here refl , λ ()
  (TakeWhile.left {q} x _ _)   → q , _ , x , ≼-refl {q} , here refl , λ { refl → refl }
