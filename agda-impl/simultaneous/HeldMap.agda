{-# OPTIONS --guardedness #-}

-- A MAP IS ITS SOURCE, ROW FOR ROW, at any subscription: each row met of
-- it is its source's row, the event mapped.  So a map of marks that
-- leaves every mark in place holds what its source holds: the count reads
-- only marks, and a value stays a value.
module simultaneous.HeldMap where

open import Data.List using (List; []; _∷_)
import Data.List as L
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos; root; _≟ᵖ_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (_≼_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; module Op; map-out; map-end; map-skip;
  map-pin)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Modulus using (entered-reach)
open import adequacy.SubOne using (map-reach)
open import simultaneous.InstEmit using (instEmit; value; mark)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Relations using (Met)
open import simultaneous.Routed using (HeldD)
open import simultaneous.Relabel using (Same; same-mark; same-value; Rows≈; []; _∷_; ev-out; ev-end; held-same; rest-same)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Routes; count; mapIE)

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

  -- A run met of the source, mapped, is met of the map.
  fwd : ∀ {c sc} → Run S c sc → Run M c (mapRows g sc)
  fwd [] = []
  fwd {c} (_∷_ {q = q} {e = e} (((x , pr) , ks , few) , vi , aft , lst) run) =
    (((lift x , end-of) , ks , λ z k≺ → few (proj₁ (proj₂ (unmap z))) k≺) , visible-map e vi , aft
      , λ z v a → lst (proj₁ (proj₂ (unmap z))) (vis-of z v) a) ∷ fwd run
    where
      end-of : ∀ {c′} → M c′ end → q ≼ c′
      end-of z with unmap z
      ... | end , y , refl = pr y
      ... | out _ , _ , ()
      ... | skip , _ , ()
      ... | pin _ , _ , ()
      vis-of : ∀ {k e′} (z : M k e′) → Visible e′ → Visible (proj₁ (unmap z))
      vis-of z v with unmap z
      ... | e₁ , _ , refl = visible-back e₁ v

------------------------------------------------------------------------
-- Held through a map

same-mapIE : ∀ {A B : Set} {f : A → B} (x : IE A) → Same (mapIE f x) x
same-mapIE (instEmit (value _) _) = same-value
same-mapIE (instEmit (mark _) _)  = same-mark (λ _ → refl)

-- The rows met of a map of marks relabel its source's.
rows-mapIE : ∀ {A B : Set} {f : A → B} {t : EmissionSet (IE A)} {c sc} → Run t c sc → Rows≈ (mapRows (mapIE f) sc) sc
rows-mapIE []                                     = []
rows-mapIE (_∷_ {e = out x} (_ , _ , _) run)      = ev-out (same-mapIE x) ∷ rows-mapIE run
rows-mapIE (_∷_ {e = end}   (_ , _ , _) run)      = ev-end ∷ rows-mapIE run
rows-mapIE (_∷_ {e = skip}  (_ , () , _) _)
rows-mapIE (_∷_ {e = pin _} (_ , () , _) _)

-- A run of a relabelled stream is its source's, row for row.
map-back : ∀ {A B : Set} (f : A → B) (d : Den (IE A)) p → ∀ {rs′} → Met (MapRun.M (mapIE f) d p) rs′
         → Σ _ λ rs → Met (MapRun.S (mapIE f) d p) rs × Rows≈ rs′ rs
map-back f d p m with MapRun.back (mapIE f) d p m
... | sc , run , refl = sc , run , rows-mapIE run

held-map-den : ∀ {A B : Set} (f : A → B) (d : Den (IE A)) {W F} cs → HeldD W F d cs → HeldD W F (Op.map (mapIE f) d) cs
held-map-den f d cs h p ok fr ep =
  held-same row end-row (map-back f d p) (λ _ {k} {e} x _ no → no (_ , lift x , visible-map {g = mapIE f} e))
    (rest-same (λ m → proj₁ (unmap m) , proj₁ (proj₂ (unmap m))) (map-back f d p)) (h p ok fr ep)
  where
    open MapRun (mapIE f) d p

    row : ∀ {y x′} → M y (out x′) → Σ _ λ x → S y (out x) × Same x′ x
    row m with unmap m
    ... | out x , y , refl = x , y , same-mapIE x

    end-row : ∀ {y} → M y end → S y end
    end-row m with unmap m
    ... | end , y , refl = y

