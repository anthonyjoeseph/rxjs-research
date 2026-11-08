{-# OPTIONS --guardedness #-}

-- A MAP IS ITS SOURCE, ROW FOR ROW, at any subscription: each row met of
-- it is its source's row, the event mapped.  So a map of marks that
-- leaves every mark in place holds what its source holds: the count reads
-- only marks, and a value stays a value.
module simultaneous.HeldMap where

open import Data.List using (List; []; _∷_; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-map⁻)
open import Data.List.Properties using (map-∘; ∷-injective)
open import Data.Bool using (true; false)
open import Data.Nat using (ℕ; suc)
open import Relation.Nullary using (¬_)
open import Relation.Nullary using (does)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)

open import denotation.Events using (Pos; Timeline; root; fresh; _≟ᵖ_)
open import denotation.EmissionSet using (EmissionSet; Ev; out; end; skip; pin; Den; enter; module Op; map-out; map-end; map-skip;
  map-pin)
open import denotation.Read using (Run; []; _∷_; Visible)
open import denotation.Laws.Modulus using (entered-reach)
open import adequacy.SubOne using (map-reach)
open import simultaneous.InstEmit using (instEmit; value; mark; begin; stop; over; outerOpen; outerClose; laneStart; carry; laneDone; burstEnd; outerDone; subscribed; completed)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Relations using (Met; values; outs)
open import simultaneous.Shut using (Shut; r₀)
open import simultaneous.Routed using (Held; HeldD; Carried; c-value; c-stop; c-over; c-end; cnt; Ex; nameOf)

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

-- A value met of a map is a value of its source's, mapped.
row-back : ∀ {X Y : Set} {g : X → Y} (rs : List (Pos × Ev X)) {q b} → (q , out b) ∈ mapRows g rs
         → Σ X λ a → (q , out a) ∈ rs × g a ≡ b
row-back {g = g} rs m with ∈-map⁻ (mapRow g) m
... | (_ , out a) , m′ , refl = a , m′ , refl
... | (_ , skip)  , _  , ()
... | (_ , pin _) , _  , ()
... | (_ , end)   , _  , ()

visible-back : ∀ {A B : Set} {g : A → B} e → Visible (mapEv g e) → Visible e
visible-back (out _) v = tt
visible-back end     v = tt

visible-map : ∀ {A B : Set} {g : A → B} e → Visible e → Visible (mapEv g e)
visible-map (out _) v = tt
visible-map end     v = tt

-- A map's rows split where its source's do.
map-split : ∀ {X Y : Set} (f : X → Y) xs (ys zs : List Y) → L.map f xs ≡ ys ++ zs
          → Σ (List X) λ xs₁ → Σ (List X) λ xs₂ → xs ≡ xs₁ ++ xs₂ × ys ≡ L.map f xs₁ × zs ≡ L.map f xs₂
map-split f xs       []       zs e    = [] , xs , refl , refl , sym e
map-split f (x ∷ xs) (y ∷ ys) zs e with ∷-injective e
... | e₁ , e₂ with e₁ | map-split f xs ys zs e₂
...   | refl | xs₁ , xs₂ , refl , refl , refl = x ∷ xs₁ , xs₂ , refl , refl , refl

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
-- Counts

count-mapIE : ∀ {A B : Set} (f : A → B) r (x : IE A) → count r (mapIE f x) ≡ count r x
count-mapIE f r (instEmit (value _) _) = refl
count-mapIE f (m , k) (instEmit (mark begin) n) with does (n ≟ᵖ m)
... | true  = refl
... | false = refl
count-mapIE f r (instEmit (mark over) _) = refl
count-mapIE f r (instEmit (mark stop) _) = refl
count-mapIE f r (instEmit (mark outerOpen) _) = refl
count-mapIE f r (instEmit (mark outerClose) _) = refl
count-mapIE f r (instEmit (mark laneStart) _) = refl
count-mapIE f r (instEmit (mark carry) _) = refl
count-mapIE f r (instEmit (mark laneDone) _) = refl
count-mapIE f r (instEmit (mark burstEnd) _) = refl
count-mapIE f r (instEmit (mark outerDone) _) = refl
count-mapIE f r (instEmit (mark subscribed) _) = refl
count-mapIE f r (instEmit (mark completed) _) = refl

fold-mapIE : ∀ {A B : Set} (f : A → B) r (xs : List (IE A)) → L.foldl count r (L.map (mapIE f) xs) ≡ L.foldl count r xs
fold-mapIE f r []       = refl
fold-mapIE f r (x ∷ xs) rewrite count-mapIE f r x = fold-mapIE f (count r x) xs

second : ∀ {A B : Set} → (A → B) → Pos × A → Pos × B
second f (q , a) = q , f a

outs-map : ∀ {A B : Set} (f : A → B) (rs : List (Pos × Ev A)) → outs (mapRows f rs) ≡ L.map (second f) (outs rs)
outs-map f []                 = refl
outs-map f ((q , out a) ∷ rs) = cong ((q , f a) ∷_) (outs-map f rs)
outs-map f ((q , skip) ∷ rs)  = outs-map f rs
outs-map f ((q , pin _) ∷ rs) = outs-map f rs
outs-map f ((q , end) ∷ rs)   = outs-map f rs

values-map : ∀ {A B : Set} (f : A → B) (rs : List (Pos × Ev A)) → values (mapRows f rs) ≡ L.map f (values rs)
values-map f rs = trans (cong (L.map proj₂) (outs-map f rs)) (trans (sym (map-∘ (outs rs))) (map-∘ (outs rs)))

cnt-map : ∀ {A B : Set} (f : A → B) (rs : List (Pos × Ev (IE A))) → cnt (mapRows (mapIE f) rs) ≡ cnt rs
cnt-map f rs = trans (cong (L.foldl count r₀) (values-map (mapIE f) rs)) (fold-mapIE f r₀ (values rs))

------------------------------------------------------------------------
-- Marks stay put

carried-back : ∀ {A B : Set} {f : A → B} (e : Ev (IE A)) → Carried (mapEv (mapIE f) e) → Carried e
carried-back (out (instEmit (value _) _))     c-value = c-value
carried-back (out (instEmit (mark stop) _))   c-stop  = c-stop
carried-back (out (instEmit (mark over) _))   c-over  = c-over
carried-back end                              c-end   = c-end

begin-back : ∀ {A B : Set} {f : A → B} (x : IE A) {n} → mapIE f x ≡ instEmit (mark begin) n → x ≡ instEmit (mark begin) n
begin-back (instEmit (mark _) _) refl = refl

value-back : ∀ {A B : Set} {f : A → B} (x : IE A) {b j} → mapIE f x ≡ instEmit (value b) j → Σ A λ a → x ≡ instEmit (value a) j
value-back (instEmit (value a) _) refl = a , refl

------------------------------------------------------------------------
-- Held through a map

held-map-den : ∀ {A B : Set} (f : A → B) (d : Den (IE A)) cs → HeldD d cs → HeldD (Op.map (mapIE f) d) cs
held-map-den f d cs h p = record
  { named   = named
  ; covered = covered
  ; shut    = shut
  }
  where
    open MapRun (mapIE f) d p
    H = h p

    named : ∀ {y n} → M y (out (instEmit (mark begin) n)) → n ≡ nameOf y
    named x with unmap x
    ... | out (instEmit (mark _) _)  , y , refl = Held.named H y
    ... | out (instEmit (value _) _) , _ , ()
    ... | skip  , _ , ()
    ... | pin _ , _ , ()
    ... | end   , _ , ()

    covered : ∀ {rs} → Met M rs → ∀ r₁ {y e} r₂ → rs ≡ r₁ ++ (y , e) ∷ r₂ → Carried e → ¬ Ex (p ∷ cs) y
            → Σ ℕ λ k → cnt r₁ ≡ (nameOf y , suc k)
    covered m r₁ r₂ e c nx with back m
    ... | sc , run , refl with map-split _ sc r₁ (_ ∷ r₂) e
    ...   | s₁ , [] , refl , refl , ()
    ...   | s₁ , (y , e₀) ∷ s₂ , refl , refl , eq with proj₁ (∷-injective eq)
    ...     | refl = subst (λ r → Σ _ λ k → r ≡ _) (sym (cnt-map f s₁))
                       (Held.covered H run s₁ s₂ refl (carried-back e₀ c) nx)

    shut : Shut M
    shut m r₁ r₂ e z bq vy iq with back m
    ... | sc , run , refl with map-split _ sc r₁ r₂ e
    ...   | s₁ , s₂ , refl , refl , refl with row-back s₁ bq | row-back s₂ vy
    ...     | b , bq′ , eb | v , vy′ , ev with begin-back b eb | value-back v ev
    ...       | refl | a′ , refl =
      Held.shut H run s₁ s₂ refl (subst (λ r → proj₂ r ≡ 0) (cnt-map f s₁) z)
        (subst (λ n → (_ , out (instEmit (mark begin) n)) ∈ s₁) (cong proj₁ (cnt-map f s₁)) bq′) vy′ iq
