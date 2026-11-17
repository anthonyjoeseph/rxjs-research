{-# OPTIONS --guardedness #-}

-- AN `of`'S RECORD (`of-tab`): its table lists each value one step past
-- the subscription, at the step of its index, then the end at the last
-- step; the elaborated `of` lists each value carried, at the same steps.
-- Each row is imaged on the elaborated row of its step; nothing is put
-- late.  No cut lists more of it than another, so every agreement holds.
-- `empty` lists what `of []` does.
module simultaneous.TableOf where

open import Data.Bool using (false)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; length; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; n≤1+n; n≮n)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (tt)
open import Function using (Equivalence; mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; last; _⊕_)
open import denotation.Events using (Timeline; fresh; ofᴱ; <ᵖ-part)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; ≺-irrefl; ≺-absurd; ≺→≼; ≺-ext)
open import denotation.Laws.Cut using (ix-asc; ix-back)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (Row; _⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown)
open import simultaneous.Listing using (walkN)
open import simultaneous.TableCorr using (TR; M; ev; m-val; m-ee; Corr; Rel)
open import simultaneous.TableSpin using (lastL; lastL-⊕; step-inj; step-flat; ix-inj)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- An `of`'s rows

W : ∀ {X : Set} → Pos → ℕ → List X → List (Row X)
W q i xs = walkN (suc (length xs)) (ofᴱ q i xs)

-- A row is a value at a step of its index, or the end at the last step.
shape : ∀ {X : Set} q i (xs : List X) {k e} → (k , e) ∈ W q i xs
      → (Σ ℕ λ j → i ≤ j × k ≡ q ⊕ [ ix j ] × Σ X λ x → e ≡ out x) ⊎ (k ≡ q ⊕ [ last ] × e ≡ end)
shape q i []       (here refl) = inj₂ (refl , refl)
shape q i (x ∷ xs) (here refl) = inj₁ (i , ≤-refl , refl , x , refl)
shape q i (x ∷ xs) (there m) with shape q (suc i) xs m
... | inj₁ (j , le , eq , v , ee) = inj₁ (j , ≤-trans (n≤1+n i) le , eq , v , ee)
... | inj₂ r                     = inj₂ r

-- The labels a leaf's rows lie at.
data Step : Label → Set where
  at-ix   : ∀ j → Step (ix j)
  at-last : Step last

step : ∀ {X : Set} q i (xs : List X) {k e} → (k , e) ∈ W q i xs → Σ Label λ a → Step a × k ≡ q ⊕ [ a ]
step q i xs m with shape q i xs m
... | inj₁ (j , _ , eq , _) = ix j , at-ix j , eq
... | inj₂ (eq , _)         = last , at-last , eq

unp : ∀ {X : Set} q i (xs : List X) {k e} → (k , e) ∈ W q i xs → Unpinned e
unp q i xs m with shape q i xs m
... | inj₁ (_ , _ , _ , _ , refl) = tt
... | inj₂ (_ , refl)             = tt

no-pin : ∀ {X : Set} q i (xs : List X) {k r} → (k , pin r) ∈ W q i xs → ⊥
no-pin q i xs m with shape q i xs m
... | inj₁ (_ , _ , _ , _ , ())
... | inj₂ (_ , ())

-- Steps keep their order whatever they are steps past.
shift : ∀ q q* {a b} → Step a → Step b → (q ⊕ [ a ]) ≺ (q ⊕ [ b ]) → (q* ⊕ [ a ]) ≺ (q* ⊕ [ b ])
shift q q* (at-ix i) (at-ix j) lt = ix-asc q* (ix-back q lt)
shift q q* (at-ix i) at-last   _  = Equivalence.from T-≡ (<ᵖ-part q* [] [] refl)
shift q q* at-last   (at-ix j) lt = ⊥-elim (≺-absurd {q ⊕ [ last ]} {q ⊕ [ ix j ]} lt (Equivalence.from T-≡ (<ᵖ-part q [] [] refl)))
shift q q* at-last   at-last   lt = ⊥-elim (≺-irrefl {q ⊕ [ last ]} lt)

-- One row per step.
clash : ∀ {X : Set} q i (xs : List X) {e} → (q ⊕ [ ix i ] , e) ∈ W q (suc i) xs → ⊥
clash q i xs m with shape q (suc i) xs m
... | inj₁ (j , le , eq , _) = n≮n i (subst (suc i ≤_) (sym (ix-inj (step-inj q eq))) le)
... | inj₂ (eq , _) with step-inj q eq
...   | ()

func-W : ∀ {X : Set} q i (xs : List X) {k e e′} → (k , e) ∈ W q i xs → (k , e′) ∈ W q i xs → e ≡ e′
func-W q i []       (here refl) (here refl) = refl
func-W q i (x ∷ xs) (here refl) (here refl) = refl
func-W q i (x ∷ xs) (here refl) (there m′)  = ⊥-elim (clash q i xs m′)
func-W q i (x ∷ xs) (there m)   (here refl) = ⊥-elim (clash q i xs m)
func-W q i (x ∷ xs) (there m)   (there m′)  = func-W q (suc i) xs m m′

flat-W : ∀ {X : Set} q i (xs : List X) {y e l ys e′} → (y , e) ∈ W q i xs → (y ⊕ (l ∷ ys) , e′) ∈ W q i xs → ⊥
flat-W q i xs m m′ with step q i xs m
... | a , _ , refl with step q i xs m′
...   | b , _ , eq = step-flat q eq

------------------------------------------------------------------------
-- The record

module OfTab {A : Set} (xs : List A) (v : A → IE A) (vals : ∀ x → valuesOf (v x) ≡ x ∷ []) (p p* : Pos) where

  P : ℕ → Maybe (Tb.Listed A)
  P _ = just (W p 0 xs ⊣ false)

  Q : ℕ → Maybe (Tb.Listed (IE A))
  Q _ = just (W p* 0 (map v xs) ⊣ false)

  φ′ : ℕ → Pos → Pos
  φ′ _ k = p* ⊕ [ lastL k ]

  Put′ : ℕ → Pos → Pos → Set
  Put′ _ _ _ = ⊥

  m-v : ∀ (e : Ev A) → M e (ev v e)
  m-v (out a) = m-val (vals a)
  m-v skip    = (λ ()) , (λ _ ())
  m-v end     = m-ee
  m-v (pin r) = (λ ()) , (λ _ ())

  -- Each plain row on the elaborated row of its step.
  fwd : ∀ i ys {k e} → (k , e) ∈ W p i ys → (p* ⊕ [ lastL k ] , ev v e) ∈ W p* i (map v ys)
  fwd i []       (here refl) = here (cong (λ l → p* ⊕ [ l ] , end) (lastL-⊕ p last))
  fwd i (x ∷ ys) (here refl) = here (cong (λ l → p* ⊕ [ l ] , out (v x)) (lastL-⊕ p (ix i)))
  fwd i (x ∷ ys) (there m)   = there (fwd (suc i) ys m)

  bwd : ∀ i ys {l e′} → (l , e′) ∈ W p* i (map v ys)
      → Σ Pos λ k → Σ (Ev A) λ e → (k , e) ∈ W p i ys × l ≡ p* ⊕ [ lastL k ] × e′ ≡ ev v e
  bwd i []       (here refl) = p ⊕ [ last ] , end , here refl , cong (λ l → p* ⊕ [ l ]) (sym (lastL-⊕ p last)) , refl
  bwd i (x ∷ ys) (here refl) = p ⊕ [ ix i ] , out x , here refl , cong (λ l → p* ⊕ [ l ]) (sym (lastL-⊕ p (ix i))) , refl
  bwd i (x ∷ ys) (there m) with bwd (suc i) ys m
  ... | k , e , m′ , eq , ee = k , e , there m′ , eq , ee

  same : ∀ {X : Set} {q i} {ys : List X} {k e} → (k , e) ∈ W q i ys → instantOf k ≡ instantOf q
  same {q = q} {i} {ys} m with step q i ys m
  ... | a , _ , refl = inst-⊕ q [ a ]

  ag-id : ∀ {X : Set} {t : Pos → Ev X → Set} {k} → AgreeTo k t t
  ag-id = ⟨ (λ _ → (λ x → x) , (λ x → x)) ⟩

  corr′ : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P N)) (TR (Q N))
  corr′ N = record
    { row→ = λ { {e = e} (_ , refl , m) _ → inj₁ (ev v e , (_ , refl , fwd 0 xs m) , m-v e) }
    ; pin→ = λ { (_ , refl , m) _ → ⊥-elim (no-pin p 0 xs m) }
    ; put-before = λ _ ()
    ; shown← = shown←′
    ; place = λ { (_ , refl , m) _ → inj₁ (same m) }
    ; mono = mono′
    ; inst = λ { {k} {k′} (_ , refl , m) (_ , refl , m′) _ _ →
        mk⇔ (λ _ → trans (same m) (sym (same m′))) (λ _ → trans (inst-⊕ p* [ lastL k ]) (sym (inst-⊕ p* [ lastL k′ ]))) }
    ; home = λ { {k} (_ , refl , m) _ → mk⇔ (λ _ → same m) (λ _ → inst-⊕ p* [ lastL k ]) } }
    where
      shown←′ : ∀ {l e′} → TR (Q N) l e′ → Shown (One valuesOf) e′
              → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ N k × TR (P N) k e × Unpinned e × M e e′
      shown←′ (_ , refl , m) _ with bwd 0 xs m
      ... | k , e , m′ , eq , refl = k , e , eq , (_ , refl , m′) , unp p 0 xs m′ , m-v e

      mono′ : ∀ {k k′ e e′} → TR (P N) k e → TR (P N) k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ′ N k ≺ φ′ N k′
      mono′ (_ , refl , m) (_ , refl , m′) _ _ lt with step p 0 xs m | step p 0 xs m′
      ... | a , sa , refl | b , sb , refl =
        subst₂ (λ c d → (p* ⊕ [ c ]) ≺ (p* ⊕ [ d ])) (sym (lastL-⊕ p a)) (sym (lastL-⊕ p b)) (shift p p* sa sb lt)

  rel′ : Rel P Q p p*
  rel′ = record
    { φ = φ′ ; Put = Put′ ; corr = corr′
    ; φ-agree = λ _ _ _ → refl
    ; bk = λ l → [ p ⊕ [ lastL l ] ]
    ; in-bk = λ {N} → in-bk′ {N}
    ; pb-few = λ _ → [] , λ ()
    ; elab-causal = λ _ _ _ _ → ag-id
    ; stable← = λ _ _ _ _ _ → ag-id
    ; stable-put = λ _ _ _ ()
    ; stable-lead = λ _ _ _ _ _ _ _ _ → ag-id
    ; elab-all = λ _ _ y → y
    ; func = λ { (_ , refl , m) (_ , refl , m′) → func-W p 0 xs m m′ }
    ; func* = λ { (_ , refl , m) (_ , refl , m′) → func-W p* 0 (map v xs) m m′ }
    ; flat = λ { (_ , refl , m) (_ , refl , m′) → flat-W p 0 xs m m′ }
    ; flat* = λ { (_ , refl , m) (_ , refl , m′) → flat-W p* 0 (map v xs) m m′ }
    ; pin-in = λ { (_ , refl , m) → ⊥-elim (no-pin p 0 xs m) }
    ; pin-in* = λ { (_ , refl , m) → ⊥-elim (no-pin p* 0 (map v xs) m) }
    ; cons = λ _ x _ _ → x
    ; cons* = λ _ y _ _ → y
    ; got = λ _ → _ , refl
    ; got* = λ _ → _ , refl
    ; after = λ { (_ , refl , m) → after-W p 0 xs m }
    ; after* = λ { (_ , refl , m) → after-W p* 0 (map v xs) m }
    ; after-φ = λ {_} {k} _ _ → ≺→≼ {p*} {p* ⊕ [ lastL k ]} (≺-ext p* [])
    ; pin-after* = λ { (_ , refl , m) → ⊥-elim (no-pin p* 0 (map v xs) m) }
    ; pin-stable = λ _ _ _ _ _ _ y → y }
    where
      in-bk′ : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ [ p ⊕ [ lastL (φ′ N k) ] ]
      in-bk′ (_ , refl , m) _ with step p 0 xs m
      ... | a , _ , refl = here (cong (λ l → p ⊕ [ l ]) (sym (trans (lastL-⊕ p* (lastL (p ⊕ [ a ]))) (lastL-⊕ p a))))

      after-W : ∀ {X : Set} q i (ys : List X) {k e} → (k , e) ∈ W q i ys → q ≼ k
      after-W q i ys m with step q i ys m
      ... | a , _ , refl = ≺→≼ {q} {q ⊕ [ a ]} (≺-ext q [])

of-tab : ∀ {A} (xs : List A) (v : A → IE A) → (∀ x → valuesOf (v x) ≡ x ∷ []) → ∀ p p*
       → Rel {A} (λ _ → just (W p 0 xs ⊣ false)) (λ _ → just (W p* 0 (map v xs) ⊣ false)) p p*
of-tab xs v vals p p* = OfTab.rel′ xs v vals p p*
