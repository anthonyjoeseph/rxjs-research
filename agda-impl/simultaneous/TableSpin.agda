{-# OPTIONS --guardedness #-}

-- A SPIN'S RECORD (`spin-tab`): a `defer` cut at depth zero lists its
-- first rows, skips at the subscription's ticks, alike on both sides.
-- Each plain tick is imaged on the elaborated tick of its index; nothing
-- is put late.  A deeper cut lists more ticks, so two cuts agree up to
-- any tick the shallower lists.
module simultaneous.TableSpin where

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (Σ; _×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Function using (mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; skip; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (≺→≼; ≺-ext)
open import denotation.Laws.Cut using (ix-asc; ix-back)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (_⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.Listing using (spinRows)
open import simultaneous.TableCorr using (Corr; Rel)
open import simultaneous.TableKit using (TR; M; m-ss)
open import simultaneous.TakeCut using (inst-⊕)

open import simultaneous.Horizon using (module SpinB; module Cuts)
open import simultaneous.HorizonCorr using (module SpinPair; module Sub)
open import simultaneous.SpinKit using (S; sp→; sp←; lastL; lastL-⊕; spin-flat)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- A spin's table

------------------------------------------------------------------------
-- The record

module SpinTab {A : Set} (p p* : Pos) where

  P : ℕ → Maybe (Tb.Listed A)
  P N = S (3 + N) p

  Q : ℕ → Maybe (Tb.Listed (IE A))
  Q N = S (3 + N) p*

  φ′ : ℕ → Pos → Pos
  φ′ _ k = p* ⊕ [ lastL k ]

  φ-ix : ∀ {N} i → φ′ N (p ⊕ [ ix i ]) ≡ p* ⊕ [ ix i ]
  φ-ix i = cong (λ l → p* ⊕ [ l ]) (lastL-⊕ p (ix i))

  Put′ : ℕ → Pos → Pos → Set
  Put′ _ _ _ = ⊥

  -- Every tick in the subscription's instant.
  same : ∀ {X : Set} {N q k} {e : Ev X} → TR (S N q) k e → instantOf k ≡ instantOf q
  same {q = q} x with sp→ x
  ... | i , _ , refl , _ = inst-⊕ q [ ix i ]

  corr′ : ∀ N → Corr p p* (φ′ N) (Put′ N) (λ _ → ⊥) (TR (P N)) (TR (Q N))
  corr′ N = record
    { row→ = row→′
    ; late-put = λ ()
    ; pin→ = pin→′
    ; put-before = λ _ ()
    ; pin-before = λ _ ()
    ; shown← = shown←′
    ; place = λ y _ → inj₁ (same y)
    ; mono = λ x x′ un un′ _ _ → mono′ x x′ un un′
    ; inst = λ {k} {k′} x x′ _ _ _ _ →
        mk⇔ (λ _ → trans (same x) (sym (same x′)))
            (λ _ → trans (inst-⊕ p* [ lastL k ]) (sym (inst-⊕ p* [ lastL k′ ])))
    ; home = λ {k} x _ _ → mk⇔ (λ _ → same x) (λ _ → inst-⊕ p* [ lastL k ]) }
    where
      row→′ : ∀ {k e} → TR (P N) k e → Unpinned e
            → ((Σ (Ev (IE A)) λ e′ → TR (Q N) (φ′ N k) e′ × M e e′) × ¬ ⊥) ⊎ (e ≡ skip × Corr.PutAt (corr′ N) k)
      row→′ x _ with sp→ x
      ... | i , lt , refl , refl = inj₁ ((skip , subst (λ z → TR (Q N) z skip) (sym (φ-ix {N} i)) (sp← lt) , m-ss {A}) , (λ ()))

      pin→′ : ∀ {k r} → TR (P N) k (pin r) → Live (TR (P N)) k → Corr.PinAt (corr′ N) k r
      pin→′ x _ with sp→ x
      ... | _ , _ , _ , ()

      shown←′ : ∀ {l e′} → TR (Q N) l e′ → Shown (One valuesOf) e′
              → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ N k × TR (P N) k e × Unpinned e × ¬ ⊥ × M e e′
      shown←′ y sh with sp→ y
      ... | _ , _ , _ , refl = ⊥-elim sh

      mono′ : ∀ {k k′ e e′} → TR (P N) k e → TR (P N) k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ′ N k ≺ φ′ N k′
      mono′ x x′ _ _ lt with sp→ x | sp→ x′
      ... | i , _ , refl , _ | j , _ , refl , _ = subst₂ _≺_ (sym (φ-ix {N} i)) (sym (φ-ix {N} j)) (ix-asc p* (ix-back p lt))

  rel′ : Rel P Q p p*
  rel′ = record
    { φ = φ′ ; Put = Put′ ; Late = λ _ _ → ⊥ ; corr = corr′
    ; bk = λ _ l → [ p ⊕ [ lastL l ] ]
    ; in-bk = λ x un _ → in-bk′ x un
    ; pb-few = λ _ _ → [] , λ ()
    ; Bd = SpinB.Bd {A} p ; Bd* = SpinB.Bd {IE A} p* ; bounded = SpinB.bounded p ; bounded* = SpinB.bounded p*
    ; bcorr = λ N → Sub.restrict inj₁ (λ { (_ , ()) })
        (SpinPair.corr p p* N (φ′ N) (λ _ → ⊥) (λ _ _ → ⊥) rows* (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()) (λ ()))
    ; across = record { back-clear = λ _ x _ _ cl* → back-clear′ x cl* ; put-clear = λ _ _ () ; lead-clear = λ x _ _ _ _ _ _ → at-cut x }
    ; skip-off* = λ _ _ ()
    ; func = λ x x′ → trans (proj₂ (proj₂ (proj₂ (sp→ x)))) (sym (proj₂ (proj₂ (proj₂ (sp→ x′)))))
    ; func* = λ y y′ → trans (proj₂ (proj₂ (proj₂ (sp→ y)))) (sym (proj₂ (proj₂ (proj₂ (sp→ y′)))))
    ; flat = spin-flat
    ; flat* = spin-flat
    ; pin-in = λ x → ⊥-elim (pin-no x)
    ; pin-in* = λ y → ⊥-elim (pin-no y)
    ; got = λ _ → _ , refl
    ; got* = λ _ → _ , refl
    ; after = after′
    ; after* = after′
    ; after-φ = λ {_} {k} _ _ _ → ≺→≼ {p*} {p* ⊕ [ lastL k ]} (≺-ext p* [])
    ; pin-after* = λ y → ⊥-elim (pin-no y) }
    where
      pin-no : ∀ {X : Set} {M q k r} → TR {X} (S M q) k (pin r) → ⊥
      pin-no x with sp→ x
      ... | _ , _ , _ , ()

      -- Every tick a cut lists lies before its hang.
      at-cut : ∀ {N k e} → TR (P N) k e → Cuts.Clear (λ N → TR (P N)) (SpinB.Bd {A} p) N k
      at-cut x (refl , refl) with sp→ x
      ... | _ , lt , refl , _ = ix-asc p lt

      -- A deeper tick whose image lies before a cut's elaborated hang lies
      -- before its plain one: the same index.
      back-clear′ : ∀ {N N′ k e} → TR (P N′) k e → Cuts.Clear (λ N → TR (Q N)) (SpinB.Bd {IE A} p*) N (φ′ N′ k)
                  → Cuts.Clear (λ N → TR (P N)) (SpinB.Bd {A} p) N k
      back-clear′ {N} {N′} x cl* (refl , refl) with sp→ x
      ... | i , _ , refl , _ = ix-asc p (ix-back p* (subst (_≺ (p* ⊕ [ ix (3 + N) ])) (φ-ix {N′} i) (cl* (refl , refl))))

      rows* : ∀ {N k e} → SpinB.c {A} p N k e → Σ (Ev (IE A)) (SpinB.c {IE A} p* N (φ′ N k))
      rows* {N} x with sp→ x
      ... | i , lt , refl , refl = skip , subst (λ z → TR (Q N) z skip) (sym (φ-ix {N} i)) (sp← lt)

      in-bk′ : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ [ p ⊕ [ lastL (φ′ N k) ] ]
      in-bk′ {N} x _ with sp→ x
      ... | i , _ , refl , _ = here (cong (λ l → p ⊕ [ l ]) (sym (trans (lastL-⊕ p* (lastL (p ⊕ [ ix i ]))) (lastL-⊕ p (ix i)))))

      after′ : ∀ {X : Set} {N q k} {e : Ev X} → TR (S (3 + N) q) k e → q ≼ k
      after′ {q = q} x with sp→ x
      ... | i , _ , refl , _ = ≺→≼ {q} {q ⊕ [ ix i ]} (≺-ext q [])

spin-tab : ∀ {A} p p* → Rel {A} (λ N → just (spinRows (3 + N) p ⊣ false)) (λ N → just (spinRows (3 + N) p* ⊣ false)) p p*
spin-tab p p* = SpinTab.rel′ p p*
