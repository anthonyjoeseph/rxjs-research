{-# OPTIONS --guardedness #-}

-- A HOT'S ROWS SETTLE WHERE ITS SOURCE'S ARE (`hot-rows-settle`).  A hot
-- lists its source's proper rows (`quickcheck.Tabled.hotOf`), and cutting
-- a bounded source at its end keeps its gaps, its held boundaries and its
-- settling (`ProperCuts`): an end past the settled prefix lies past every
-- row of it.
--
-- Not its pins: a connect's body hangs in its burst, free, and ends one
-- cut deeper, before the source's burst pins it (a cold emitting without
-- end under a `takeWhile`).  Every boundary lies past the connect and
-- none is held, yet the deeper hot drops the pins the end now precedes.
-- A reader shows a hot's pin as a skip (`Rejoin`), so asks nothing of
-- them (`Cuts.Settles`).
module simultaneous.HotRows where

open import Data.List using ([_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)

open import Tree using (Obs)
open import denotation.Position using (Pos; ix; _⊕_)
open import denotation.Events using (Timeline)
open import denotation.EmissionSet using (EmissionSet; end; Proper; _≼_)
open import denotation.Laws.Modulus using (⟨_⟩; upto; ≺→≼; ≼-≺-≺; ≼-or-≻)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (hotOf)
open import quickcheck.Tabled.Exact using (proper-exact)
open import quickcheck.Tabled.Exact.Base using (Exact; sound; complete)
open import simultaneous.Listing using (listC-ok; UncutEnv)
open import simultaneous.TableKit using (Rows; ag-≃)
open import simultaneous.ListTR using (self-exact)
open import simultaneous.Horizon using (Tag; module Cuts)
open import simultaneous.HorizonTree using (Cut; srcL)

------------------------------------------------------------------------
-- Cuts cut at their ends

module ProperCuts {A : Set} (c : ℕ → EmissionSet A) (Bd : ℕ → Pos → Tag → Set) (B : Cuts.Bounded c Bd) where

  open Cuts c Bd
  module B = Bounded B
  module P = Cuts (λ N → Proper (c N)) Bd

  -- An end in the other cut lies past `k`, or is one here.
  move : ∀ {k} {t t′ : EmissionSet A} → (∀ {z e′} → z ≼ k → t z e′ → t′ z e′) → (∀ {z e′} → z ≼ k → t′ z e′ → t z e′)
       → ∀ {y e} → y ≼ k → Proper t y e → Proper t′ y e
  move {k} {t} {t′} to from {y} {e} yk (x , pe) = to {y} {e} yk x , λ {c₀} x′ → help c₀ x′
    where
      help : ∀ c₀ → t′ c₀ end → y ≼ c₀
      help c₀ x′ with ≼-or-≻ c₀ k
      ... | inj₁ ck = pe (from {c₀} {end} ck x′)
      ... | inj₂ kc = ≺→≼ {y} {c₀} (≼-≺-≺ {y} {k} {c₀} yk kc)

  fwd : ∀ {N k} → Clear N k → P.Settled N k
  fwd {N} {k} cl {N′} le = ⟨ (λ {y} {e} yk → move {k} {c N} {c N′} (λ {z} {e′} zk → proj₁ (upto ag {z} {e′} zk)) (λ {z} {e′} zk → proj₂ (upto ag {z} {e′} zk)) {y} {e} yk
                                         , move {k} {c N′} {c N} (λ {z} {e′} zk → proj₂ (upto ag {z} {e′} zk)) (λ {z} {e′} zk → proj₁ (upto ag {z} {e′} zk)) {y} {e} yk) ⟩
    where
      ag = B.fwd {N} {k} cl le

  proper-settles : P.Settles
  proper-settles = record { gap = λ bd x → B.gap bd (proj₁ x) ; held-in = B.held-in ; held-under = B.held-under ; fwd = λ {N} {k} → fwd {N} {k} }

------------------------------------------------------------------------
-- A hot

-- A HOT'S ROWS are its source's proper rows, settled where the source is.
hot-rows-settle : ∀ {Γ A} n (s : Obs Timeline Γ A) {ρ : ℕ → All Tb.Listed Γ} (uρ : ∀ N → UncutEnv (ρ N)) p {Bd : ℕ → Pos → Tag → Set}
                → Cuts.Bounded (Cut n s ρ (p ⊕ [ ix 1 ])) Bd → Cuts.Settles (λ N → Rows (hotOf (srcL n s uρ p N))) Bd
hot-rows-settle n s {ρ} uρ p {Bd} B = record
  { gap = λ bd x → S.gap bd (sound (ex _) x) ; held-in = S.held-in ; held-under = S.held-under
  ; fwd = λ {N} {k} cl {N′} le → ag-≃ (complete (ex N)) (sound (ex N)) (complete (ex N′)) (sound (ex N′)) (S.fwd {N} {k} cl le) }
  where
    ex : ∀ N → Exact (hotOf (srcL n s uρ p N)) (Proper (Cut n s ρ (p ⊕ [ ix 1 ]) N))
    ex N = proper-exact (self-exact (proj₁ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ])))))
                        (proj₂ (proj₂ (listC-ok (3 + N) n s (uρ N) (p ⊕ [ ix 1 ]))))

    module S = Cuts.Settles (ProperCuts.proper-settles (Cut n s ρ (p ⊕ [ ix 1 ])) Bd B)
