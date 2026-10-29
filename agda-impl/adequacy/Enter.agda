{-# OPTIONS --guardedness #-}

-- WHAT A SUBSCRIPTION ENTERS, IN THE FRAGMENT: finitely many rows, so the
-- truncation `enter` takes keeps every one, and a merge entered is the
-- merge part way through with nothing begun.
module adequacy.Enter where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; [_]; _++_; concatMap) renaming (map to mapL)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)

open import Tree using (Obs; mergeᶠ; switchᶠ; exhaustᶠ; cold; empty; of; map; scan; takeWhile; flatMap; connect; connected; defer)
open import denotation.Events using (Pos; Timeline; ix; last; ofᴱ)
open import denotation.EmissionSet using (EmissionSet; Ev; out; skip; end; InE; at-out; at-end; on-out; Truncate; Few; enter; ⟦_⟧;
  MapT; map-out; map-skip; map-end; module Joining)
open import denotation.Laws.Modulus using (few-via; entered-few)
open import adequacy.Rows using (Frag; ∅; pendRows; _≃_; _⇄_; module Flat)
open import adequacy.Up using (≃-trans)

open _≃_

-- Every row among a list.
Finite : ∀ {A} → EmissionSet A → Set
Finite {A} t = Σ (List (Pos × Ev A)) λ rs → ∀ {k e} → t k e → (k , e) ∈ rs

few : ∀ {A} {t : EmissionSet A} → Finite t → ∀ q → Few t q
few (rs , h) q = mapL proj₁ rs , λ x _ → ∈-map⁺ proj₁ (h x)

-- Nothing truncated.
kept : ∀ {A} {t : EmissionSet A} → Finite t → Truncate t ≃ t
kept fin = proj₁ ⇄ λ {q} x → x , few fin q

trunc-fin : ∀ {A} {t : EmissionSet A} → Finite t → Finite (Truncate t)
trunc-fin (rs , h) = rs , λ x → h (proj₁ x)

of-fin : ∀ {A} p i (xs : List A) → Finite (InE (ofᴱ p i xs))
of-fin p i []       = [ (p ++ [ last ] , end) ] , λ { at-end → here refl }
of-fin p i (x ∷ xs) = (p ++ [ ix i ] , out x) ∷ proj₁ rest , λ { at-out → here refl ; (on-out y) → there (proj₂ rest y) }
  where rest = of-fin p (suc i) xs

evMap : ∀ {A B} → (A → B) → Pos × Ev A → Pos × Ev B
evMap f (k , out a) = k , out (f a)
evMap f (k , skip)  = k , skip
evMap f (k , end)   = k , end

map-fin : ∀ {A B} (f : A → B) {t : EmissionSet A} → Finite t → Finite (MapT f t)
map-fin f (rs , h) = mapL (evMap f) rs , λ { (map-out x) → ∈-map⁺ (evMap f) (h x) ; (map-skip x) → ∈-map⁺ (evMap f) (h x) ; (map-end x) → ∈-map⁺ (evMap f) (h x) }

in-cm : ∀ {X Y : Set} {g : X → List Y} {x y xs} → x ∈ xs → y ∈ g x → y ∈ concatMap g xs
in-cm (here refl) h = ∈-++⁺ˡ h
in-cm {g = g} (there {x = z} m) h = ∈-++⁺ʳ (g z) (in-cm m h)

-- A joiner over finitely many outer rows, lanes and begun rows.
module _ {A B : Set} (L : A → Pos → EmissionSet B) (lf : ∀ a k → Finite (L a k)) where

  -- A row as itself, and as a skip.
  both : Pos × Ev B → List (Pos × Ev B)
  both (k , e) = (k , e) ∷ (k , skip) ∷ []

  laneRows : Pos × Ev A → List (Pos × Ev B)
  laneRows (q , out a) = concatMap both (proj₁ (lf a (q ++ [ ix 1 ])))
  laneRows (q , skip)  = []
  laneRows (q , end)   = []

  part : Pos × Ev A → List (Pos × Ev B)
  part (q , e) = (q ++ [ ix 0 ] , skip) ∷ (q , skip) ∷ (q , end) ∷ laneRows (q , e)

  join-fin : ∀ {O Bg Over Runs Cut} → Finite O → Finite Bg → Finite (Joining.JoinT L O Bg Over Runs Cut)
  join-fin {O} {Bg} {Over} {Runs} {Cut} (os , ho) (bs , hb) = concatMap part os ++ concatMap both bs , row
    where
      open Joining L O Bg Over Runs Cut
      outer : ∀ {r k e} → r ∈ os → (k , e) ∈ part r → (k , e) ∈ (concatMap part os ++ concatMap both bs)
      outer m h = ∈-++⁺ˡ (in-cm m h)
      lanes : ∀ {q a k e} → (q , out a) ∈ os → (k , e) ∈ concatMap both (proj₁ (lf a (q ++ [ ix 1 ]))) → (k , e) ∈ (concatMap part os ++ concatMap both bs)
      lanes m h = outer m (there (there (there h)))
      begun : ∀ {r k e} → r ∈ bs → (k , e) ∈ both r → (k , e) ∈ (concatMap part os ++ concatMap both bs)
      begun m h = ∈-++⁺ʳ (concatMap part os) (in-cm m h)
      row : ∀ {k e} → JoinT k e → (k , e) ∈ (concatMap part os ++ concatMap both bs)
      row (val x)                     = outer (ho x) (here refl)
      row (step x)                    = outer (ho x) (there (here refl))
      row (oend x _)                  = outer (ho x) (there (there (here refl)))
      row (opass x _)                 = outer (ho x) (there (here refl))
      row (lane {a = a} x _ (y , _) _ _)  = lanes (ho x) (in-cm (proj₂ (lf a _) y) (here refl))
      row (lend {a = a} x _ (y , _) _ _)  = lanes (ho x) (in-cm (proj₂ (lf a _) y) (here refl))
      row (lpass {a = a} x _ (y , _) _ _) = lanes (ho x) (in-cm (proj₂ (lf a _) y) (there (here refl)))
      row (left {a = a} x _ (y , _) _ _)  = lanes (ho x) (in-cm (proj₂ (lf a _) y) (there (here refl)))
      row (run x _)                   = begun (hb x) (here refl)
      row (rend x _)                  = begun (hb x) (here refl)
      row (rpass x _)                 = begun (hb x) (there (here refl))

-- A fragment program, entered anywhere: finitely many rows.
frag-fin : ∀ {A} (o : Obs Timeline [] A) → Frag o → ∀ p → Finite (enter (⟦ o ⟧ []ᴬ) p)
frag-fin empty                          _        p = trunc-fin (of-fin p 0 [])
frag-fin (of xs)                        _        p = trunc-fin (of-fin p 0 xs)
frag-fin (map f s)                      fs       p = trunc-fin (map-fin f (frag-fin s fs p))
frag-fin (flatMap (mergeᶠ nothing) f s) (ff , fs) p =
  trunc-fin (join-fin (λ a → enter (⟦ f a ⟧ []ᴬ)) (λ a → frag-fin (f a) (ff a)) (frag-fin s fs p) ([] , λ ()))
frag-fin (cold _)                       () _
frag-fin (scan _ _ _)                   () _
frag-fin (takeWhile _ _ _)              () _
frag-fin (flatMap (mergeᶠ (just _)) _ _) () _
frag-fin (flatMap switchᶠ _ _)          () _
frag-fin (flatMap exhaustᶠ _ _)         () _
frag-fin (connect _ _)                  () _
frag-fin (connected ())                 _  _
frag-fin (defer _)                      () _

-- Two joiners on one outer and one lane reading, with the same begun
-- rows and over at the same places: the same rows.
module _ {A B : Set} {L : A → Pos → EmissionSet B} {O : EmissionSet A} {Bg Bg′ : EmissionSet B} {Over Over′ : Pos → Set}
         {Runs : Pos → Set} {Cut : Pos → Pos → Set}
         (bg : Bg ≃ Bg′) (ov : ∀ {c} → Over c → Over′ c) (vo : ∀ {c} → Over′ c → Over c) where
  private
    module X = Joining L O Bg Over Runs Cut
    module Y = Joining L O Bg′ Over′ Runs Cut

    xy : ∀ {c} → X.Done c → Y.Done c
    xy (o , h) = ov o , h

    yx : ∀ {c} → Y.Done c → X.Done c
    yx (o , h) = vo o , h

  joining-≃ : X.JoinT ≃ Y.JoinT
  joining-≃ = fwd ⇄ bwd
    where
      fwd : ∀ {k e} → X.JoinT k e → Y.JoinT k e
      fwd (X.val x)             = Y.val x
      fwd (X.step x)            = Y.step x
      fwd (X.oend x d)          = Y.oend x (xy d)
      fwd (X.opass x nd)        = Y.opass x λ d → nd (yx d)
      fwd (X.lane x r l nc w)   = Y.lane x r l nc w
      fwd (X.lend x r l nc d)   = Y.lend x r l nc (xy d)
      fwd (X.lpass x r l nc nd) = Y.lpass x r l nc λ d → nd (yx d)
      fwd (X.left x r l c i)    = Y.left x r l c i
      fwd (X.run x w)           = Y.run (to bg x) w
      fwd (X.rend x d)          = Y.rend (to bg x) (xy d)
      fwd (X.rpass x nd)        = Y.rpass (to bg x) λ d → nd (yx d)
      bwd : ∀ {k e} → Y.JoinT k e → X.JoinT k e
      bwd (Y.val x)             = X.val x
      bwd (Y.step x)            = X.step x
      bwd (Y.oend x d)          = X.oend x (yx d)
      bwd (Y.opass x nd)        = X.opass x λ d → nd (xy d)
      bwd (Y.lane x r l nc w)   = X.lane x r l nc w
      bwd (Y.lend x r l nc d)   = X.lend x r l nc (yx d)
      bwd (Y.lpass x r l nc nd) = X.lpass x r l nc λ d → nd (xy d)
      bwd (Y.left x r l c i)    = X.left x r l c i
      bwd (Y.run x w)           = X.run (from bg x) w
      bwd (Y.rend x d)          = X.rend (from bg x) (yx d)
      bwd (Y.rpass x nd)        = X.rpass (from bg x) λ d → nd (xy d)

-- A merge with no outer rows and no lane begun: no rows.
flat-∅ : ∀ {A B} (L : A → Pos → EmissionSet B) d → Flat.JoinT L ∅ d [] ≃ ∅
flat-∅ L d = to′ ⇄ λ ()
  where
    to′ : ∀ {k e} → Flat.JoinT L ∅ d [] k e → ⊥
    to′ (Flat.val ())
    to′ (Flat.step ())
    to′ (Flat.oend () _)
    to′ (Flat.opass () _)
    to′ (Flat.lane () _ _ _ _)
    to′ (Flat.lend () _ _ _ _)
    to′ (Flat.lpass () _ _ _ _)
    to′ (Flat.left () _ _ _ _)
    to′ (Flat.run () _)
    to′ (Flat.rend () _)
    to′ (Flat.rpass () _)

-- A MAP ENTERED: its source entered, mapped.
enter-map : ∀ {Γ A B} (f : A → B) (s : Obs Timeline Γ A) p → pendRows (map f s) p ≃ MapT f (pendRows s p)
enter-map {[]}    f s p = proj₁ ⇄ λ x → x , few′ x
  where
    inner : ∀ {k e} → MapT f (enter (⟦ s ⟧ []ᴬ) p) k e → Σ (Ev _) (enter (⟦ s ⟧ []ᴬ) p k)
    inner (map-out y)  = _ , y
    inner (map-skip y) = _ , y
    inner (map-end y)  = _ , y
    few′ : ∀ {q e} → MapT f (enter (⟦ s ⟧ []ᴬ) p) q e → Few (MapT f (enter (⟦ s ⟧ []ᴬ) p)) q
    few′ x = few-via inner (entered-few (⟦ s ⟧ []ᴬ) p (proj₂ (inner x)))
enter-map {_ ∷ _} f s p = (λ ()) ⇄ λ { (map-out ()) ; (map-skip ()) ; (map-end ()) }

-- A MERGE ENTERED: the merge part way through, at its outer entered, not
-- done, nothing begun.
enter-merge : ∀ {Γ A B} (f : A → Obs Timeline Γ B) (s : Obs Timeline Γ A) p → Frag (flatMap (mergeᶠ nothing) f s)
            → pendRows (flatMap (mergeᶠ nothing) f s) p ≃ Flat.JoinT (λ a → pendRows (f a)) (pendRows s p) false []
enter-merge {[]}    f s p fr =
  ≃-trans (kept (join-fin (λ a → enter (⟦ f a ⟧ []ᴬ)) (λ a → frag-fin (f a) (proj₁ fr a)) (frag-fin s (proj₂ fr) p) ([] , λ ())))
          (joining-≃ ((λ ()) ⇄ λ ()) (λ e → inj₂ e , tt) λ { (inj₁ () , _) ; (inj₂ e , _) → e })
enter-merge {_ ∷ _} f s p _ = (λ ()) ⇄ λ x → to (flat-∅ (λ a → pendRows (f a)) false) x
