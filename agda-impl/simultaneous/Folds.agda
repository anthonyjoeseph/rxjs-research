{-# OPTIONS --guardedness #-}

-- FOLDS AND REACHES OVER A RELABELLING.  What a row waits on, a row it
-- came from waits on; few rows before a row are classically listed; and
-- a fold at a value is built from its listing, which names every row
-- before it with its event, so the latest value before it is decided.
module simultaneous.Folds where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable.Core using (¬¬-excluded-middle)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import denotation.Position using (Pos)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Reach; Dep; Few; _≺_; _≼_; module Scan)
open import denotation.Laws.Modulus using (≺→≼; ≼-refl; ≼-trans; ≼-or-≻; reach-via; few-ind)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (Kin; k-out; k-skip; k-pin; k-end; sub-listed)

-- What a row of `b` waits on, a row of `a` it came from waits on.
dep : ∀ {X Y : Set} {q k} {e₀ e : Ev X} {e₀′ e′ : Ev Y} → Kin e₀ e₀′ → Kin e e′ → Dep q e₀′ k e′ → Dep q e₀ k e
dep k-out  _ _ = tt
dep k-skip _ _ = tt
dep k-end  _ _ = tt
dep k-pin  kn d i with d i
... | inj₁ kr = inj₁ kr
... | inj₂ refl with kn
...   | k-pin = inj₂ refl

-- Each row of `b` from a row of `a` of its kind: what a row of `b`
-- waits on is as few as what its row of `a` does.
reach-kin : ∀ {X Y : Set} {a : EmissionSet X} {b : EmissionSet Y} → (∀ {k e′} → b k e′ → Σ (Ev X) λ e → a k e × Kin e e′)
          → ∀ {q e e′} → Kin e e′ → Reach a q e → Reach b q e′
reach-kin dn kq = reach-via (λ y _ d → let (e , x , kn) = dn y in e , x , dep kq kn d)

-- Few rows before a row, classically listed.
few-¬¬listed : ∀ {X : Set} {a : EmissionSet X} {q} → Few a q → ¬ ¬ Listed a q
few-¬¬listed {X} {a} {q} (ks , F) n = go ks λ ls G B → n (ls , (λ y kq → G (F y kq) kq (_ , y)) , B)
  where
    go : ∀ ks → (∀ ls → (∀ {k} → k ∈ ks → k ≺ q → Σ (Ev X) (a k) → k ∈ ls) → (∀ {k} → k ∈ ls → k ≺ q × Σ (Ev X) (a k)) → ⊥) → ⊥
    go []       κ = κ [] (λ ()) (λ ())
    go (k ∷ ks) κ = go ks λ ls G B → ¬¬-excluded-middle {A = k ≺ q × Σ (Ev X) (a k)} λ
      { (yes h) → κ (k ∷ ls) (λ { (here refl) _ _ → here refl ; (there m) kq r → there (G m kq r) }) (λ { (here refl) → h ; (there m) → B m })
      ; (no ¬h) → κ ls (λ { (here refl) kq r → ⊥-elim (¬h (kq , r)) ; (there m) → G m }) B }

-- THE FOLD FROM A LISTING: from the latest value before the row, or from
-- none.
module ListedFold {A B : Set} (f : B → A → B) (z : B) {t : EmissionSet A} (fu : ∀ {y e e′} → t y e → t y e′ → e ≡ e′) where
  open Scan f z t using (Acc; acc₀; acc)

  private
    -- The latest value among rows listed before `w`, decided: each comes
    -- with its event, which is the only one there.
    Latest : Pos → List Pos → Set
    Latest w ks = (∀ {k y} → k ∈ ks → t k (out y) → ⊥)
                ⊎ Σ Pos λ v → Σ A (λ y → t v (out y)) × v ≺ w × (∀ {k y} → k ∈ ks → t k (out y) → k ≼ v)

    keep : ∀ {w k ks} → Latest w ks → (∀ {y} → t k (out y) → ⊥) → Latest w (k ∷ ks)
    keep (inj₁ none) nk = inj₁ λ { (here refl) ty → nk ty ; (there m) → none m }
    keep (inj₂ (v , vy , vw , mx)) nk = inj₂ (v , vy , vw , λ { (here refl) ty → ⊥-elim (nk ty) ; (there m) → mx m })

    skip≢ : ∀ {y : A} → skip ≡ out y → ⊥
    skip≢ ()

    end≢ : ∀ {y : A} → end ≡ out y → ⊥
    end≢ ()

    pin≢ : ∀ {r} {y : A} → pin r ≡ out y → ⊥
    pin≢ ()

    latest : ∀ {w} ks → (∀ {k} → k ∈ ks → k ≺ w × Σ (Ev A) (t k)) → Latest w ks
    latest []       Bk = inj₁ λ ()
    latest (k ∷ ks) Bk with latest ks (λ m → Bk (there m)) | Bk (here refl)
    ... | inj₁ none | kw , out y , tk =
      inj₂ (k , (y , tk) , kw , λ { (here refl) _ → ≼-refl {k} ; (there m) ty → ⊥-elim (none m ty) })
    ... | inj₂ (v , vy , vw , mx) | kw , out y , tk with ≼-or-≻ v k
    ...   | inj₁ vk = inj₂ (k , (y , tk) , kw , λ { (here refl) _ → ≼-refl {k} ; {k′} (there m) ty → ≼-trans {k′} {v} {k} (mx m ty) vk })
    ...   | inj₂ kv = inj₂ (v , vy , vw , λ { (here refl) _ → ≺→≼ {k} {v} kv ; (there m) → mx m })
    latest (k ∷ ks) Bk | L | kw , skip  , tk = keep L λ ty → skip≢ (fu tk ty)
    latest (k ∷ ks) Bk | L | kw , end   , tk = keep L λ ty → end≢ (fu tk ty)
    latest (k ∷ ks) Bk | L | kw , pin _ , tk = keep L λ ty → pin≢ (fu tk ty)

  fold-listed : ∀ {w} → Listed t w → ∀ {x} → t w (out x) → Σ B (Acc w)
  fold-listed L = few-ind {t = t} (λ w → Listed t w → ∀ {x} → t w (out x) → Σ B (Acc w)) step (proj₁ L , proj₁ (proj₂ L)) L
    where
      step : ∀ {w} → Few t w → (∀ {v e} → t v e → v ≺ w → Listed t v → ∀ {x} → t v (out x) → Σ B (Acc v))
           → Listed t w → ∀ {x} → t w (out x) → Σ B (Acc w)
      step {w} _ ih (ks , F , Bk) {x} tx with latest ks Bk
      ... | inj₁ none = _ , acc₀ tx (λ ty kw → none (F ty kw) ty)
      ... | inj₂ (v , (y , tv) , vw , mx) with ih tv vw (sub-listed (ks , F , Bk) vw) tv
      ...   | st , av = _ , acc av tx vw (λ ty vk kw → mx (F ty kw) ty vk)
