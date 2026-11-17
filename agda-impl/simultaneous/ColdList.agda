{-# OPTIONS --guardedness #-}

-- THE ELABORATED COLD'S LISTING IS ITS WRITTEN-OUT ROWS (`cold-rows`).
-- The elaborated cold is the merge of the scan's rows (`scan-rows`) and
-- each tag's render (`rend-rows`), so its rows are `CRow`'s.  They are
-- read at depth `3 + N`, where a render's mint is listed whole.
--
-- The joiner's two side conditions come from one fact about the order
-- (`srow-lane-end`): every tag's render ends before the scan does.  So
-- the scan's end has every part ended, and a render's end never does.
module simultaneous.ColdList where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; [_])
open import Data.List.Relation.Unary.All using (All)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Function using (_⇔_; mk⇔; Equivalence)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; From; fixed; fresh)
open import denotation.EmissionSet using (out; end; _≺_; module Merge)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Listing using (listC; UncutEnv)
open import simultaneous.TableCorr using (TR)
open import simultaneous.ColdRows using (module At)
open import simultaneous.ColdOrder using (module Ord)
open import simultaneous.ColdScan using (module Phase)
open import simultaneous.ColdRend using (module Rnd)
open import simultaneous.ListTR using (merge-tr)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; coldˢ; render)

------------------------------------------------------------------------
-- The elaborated cold

module Cold {A : Set} (N n : ℕ) {Δ : List Set} (ρ : All Tb.Listed Δ) (uρ : UncutEnv ρ) (m : From A 0) (P : Pos) where
  open At {A} P using (C₀; c₀; SRow; Rend; CRow; r-end; c-skp; c-end; c-val; c-lane; c-lend)

  open Rnd {A} N n ρ uρ P using (K; fR; rend-rows)
  open Ord {A} P K m using (J)
  open Phase K n ρ uρ m P using (scanned; scan-rows)

  open Merge fR (TR (listC K n scanned ρ P)) using (JoinT; Done; val; step; opin; oend; opass; lane; lend; lpass; hand; left; run; rend; rpass; rhand)

  postulate
    -- THE COLD'S ROWS.
    srow-lane-end : ∀ {q x c} → SRow J q (out x) → SRow J c end → (q ⊕ [ ix 1 ] ⊕ [ last ]) ≺ c

  private
    to-s : ∀ {k e} → TR (listC K n scanned ρ P) k e → SRow J k e
    to-s = Equivalence.to scan-rows

    fr-s : ∀ {k e} → SRow J k e → TR (listC K n scanned ρ P) k e
    fr-s = Equivalence.from scan-rows

    -- At the scan's end every part has ended.
    done : ∀ {c} → SRow J c end → Done c
    done {c} s = (c , fr-s s , ≼-refl {c})
               , λ {q} {a} x _ _ _ → q ⊕ [ ix 1 ] ⊕ [ last ] , Equivalence.from (rend-rows q a) r-end
                                   , ≺→≼ {q ⊕ [ ix 1 ] ⊕ [ last ]} {c} (srow-lane-end (to-s x) s)

    -- At a render's end the scan has not.
    undone : ∀ {q x} → SRow J q (out x) → Done (q ⊕ [ ix 1 ] ⊕ [ last ]) → ⊥
    undone {q} s ((c₁ , t , le) , _) = le (srow-lane-end {q} {c = c₁} s (to-s t))

  top-to : ∀ {k e} → JoinT k e → CRow J k e
  top-to (val x)             = c-val (to-s x)
  top-to (step x)            = c-skp (to-s x)
  top-to (opin x)            with to-s x
  ... | ()
  top-to (oend x _)          = c-end (to-s x)
  top-to (opass x nD)        = ⊥-elim (nD (done (to-s x)))
  top-to (lane {q} {a} x _ l _ w) = c-lane (to-s x) (Equivalence.to (rend-rows q a) l) w
  top-to (lend {q} {a} x _ l _ _ D) with Equivalence.to (rend-rows q a) l
  ... | r-end = ⊥-elim (undone (to-s x) D)
  top-to (lpass {q} {a} x _ l _ _ _) with Equivalence.to (rend-rows q a) l
  ... | r-end = c-lend (to-s x)
  top-to (hand _ _ _ _ ())
  top-to (left {q} {a} x _ l _ _) with Equivalence.to (rend-rows q a) l
  ... | ()
  top-to (run () _)
  top-to (rend () _ _)
  top-to (rpass () _ _)
  top-to (rhand () _)

  top-from : ∀ {k e} → CRow J k e → JoinT k e
  top-from (c-skp s)    = step (fr-s s)
  top-from (c-end s)    = oend (fr-s s) (done s)
  top-from (c-val s)    = val (fr-s s)
  top-from (c-lane {q} {x} s r w) = lane (fr-s s) tt (Equivalence.from (rend-rows q x) r) (λ ()) w
  top-from (c-lend {q} {x} s) = lpass (fr-s s) tt (Equivalence.from (rend-rows q x) r-end) (λ ()) (λ ()) (undone s)

  cold-rows : ∀ {k e} → TR (listC K n (coldˢ (fixed m)) ρ P) k e ⇔ CRow J k e
  cold-rows = mk⇔ (λ x → top-to (Equivalence.to (merge-tr K n render scanned uρ P) x))
                  (λ x → Equivalence.from (merge-tr K n render scanned uρ P) (top-from x))
