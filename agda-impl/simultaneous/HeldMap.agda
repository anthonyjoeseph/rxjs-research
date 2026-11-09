{-# OPTIONS --guardedness #-}

-- A MAP IS ITS SOURCE, ROW FOR ROW, at any subscription: each row met of
-- it is its source's row, the event mapped.  So a map of marks that
-- leaves every mark in place holds what its source holds: the count reads
-- only marks, and a value stays a value.
module simultaneous.HeldMap where

open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; module Op; map-out; map-end; map-skip;
  map-pin)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Modulus using (entered-reach)
open import adequacy.SubOne using (map-reach)
open import simultaneous.InstEmit using (instEmit; value; mark)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (HeldD)
open import simultaneous.Relabel using (Same; same-mark; same-value; Rows≈; []; _∷_; ev-out; ev-end; held-same)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; Routes; count; mapIE)

------------------------------------------------------------------------
-- Rows

mapEv : ∀ {A B : Set} → (A → B) → Ev A → Ev B
mapEv g (out a) = out (g a)
mapEv g skip    = skip
mapEv g (pin r) = pin r
mapEv g end     = end

mapRow : ∀ {A B : Set} → (A → B) → Pos × Ev A → Pos × Ev B
mapRow g (q , e) = q , mapEv g e

mapRows : ∀ {A B : Set} → (A → B) → List (Pos × Ev A) → List (Pos × Ev B)
mapRows g = L.map (mapRow g)

visible-back : ∀ {A B : Set} {g : A → B} e → Visible (mapEv g e) → Visible e
visible-back (out _) v = tt
visible-back end     v = tt

visible-map : ∀ {A B : Set} {g : A → B} e → Visible e → Visible (mapEv g e)
visible-map (out _) v = tt
visible-map end     v = tt

------------------------------------------------------------------------
-- Runs

module MapRun {A B : Set} (g : A → B) (d : Den A) (p : Pos) where

  S : EmissionSet A
  S = enter d p

  M : EmissionSet B
  M = enter (Op.map g d) p

  lift : ∀ {y e} → S y e → M y (mapEv g e)
  lift {e = out _} x = map-out x , map-reach (entered-reach d p) (map-out x)
  lift {e = skip}  x = map-skip x , map-reach (entered-reach d p) (map-skip x)
  lift {e = pin _} x = map-pin x , map-reach (entered-reach d p) (map-pin x)
  lift {e = end}   x = map-end x , map-reach (entered-reach d p) (map-end x)

  unmap : ∀ {y e′} → M y e′ → Σ (Ev A) λ e → S y e × e′ ≡ mapEv g e
  unmap (map-out x , _)  = _ , x , refl
  unmap (map-skip x , _) = _ , x , refl
  unmap (map-pin x , _)  = _ , x , refl
  unmap (map-end x , _)  = _ , x , refl

  back : ∀ {c rx} → Run M c rx → Σ _ λ sc → Run S c sc × rx ≡ mapRows g sc
  back [] = [] , [] , refl
  back {c} ((((x , pr) , ks , few) , vi , aft , lst) ∷ run) with unmap x | back run
  ... | e , y , refl | sc , run′ , refl =
    _ ∷ sc , (((y , λ z → pr (lift z)) , ks , λ z k≺ → few (lift z) k≺) , visible-back e vi , aft
             , λ z v a → lst (lift z) (visible-map _ v) a) ∷ run′ , refl

------------------------------------------------------------------------
-- Held through a map

same-mapIE : ∀ {A B : Set} {f : A → B} (x : IE A) → Same (mapIE f x) x
same-mapIE (instEmit (value _) _) = same-value
same-mapIE (instEmit (mark _) _)  = same-mark

-- The rows met of a map of marks relabel its source's.
rows-mapIE : ∀ {A B : Set} {f : A → B} {t : EmissionSet (IE A)} {c sc} → Run t c sc → Rows≈ (mapRows (mapIE f) sc) sc
rows-mapIE []                                     = []
rows-mapIE (_∷_ {e = out x} (_ , _ , _) run)      = ev-out (same-mapIE x) ∷ rows-mapIE run
rows-mapIE (_∷_ {e = end}   (_ , _ , _) run)      = ev-end ∷ rows-mapIE run
rows-mapIE (_∷_ {e = skip}  (_ , () , _) _)
rows-mapIE (_∷_ {e = pin _} (_ , () , _) _)

held-map-den : ∀ {A B : Set} (f : A → B) (d : Den (IE A)) {W} cs → HeldD W d cs → HeldD W (Op.map (mapIE f) d) cs
held-map-den f d cs h p ok nt ep = held-same row end-row back′ (λ _ {k} {e} x _ no → no (_ , lift x , visible-map {g = mapIE f} e)) (h p ok nt ep)
  where
    open MapRun (mapIE f) d p

    row : ∀ {y x′} → M y (out x′) → Σ _ λ x → S y (out x) × Same x′ x
    row m with unmap m
    ... | out x , y , refl = x , y , same-mapIE x

    end-row : ∀ {y} → M y end → S y end
    end-row m with unmap m
    ... | end , y , refl = y

    back′ : ∀ {rs′} → Met M rs′ → Σ _ λ rs → Met S rs × Rows≈ rs′ rs
    back′ m with back m
    ... | sc , run , refl = sc , run , rows-mapIE run
