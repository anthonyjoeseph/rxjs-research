{-# OPTIONS --guardedness #-}

-- A SPIN'S RECORD (`spin-tab`): a `defer` cut at depth zero lists its
-- first rows, skips at the subscription's ticks, alike on both sides.
-- Each plain tick is imaged on the elaborated tick of its index; nothing
-- is put late.  A deeper cut lists more ticks, so two cuts agree up to
-- any tick the shallower lists.
module simultaneous.TableSpin where

open import Data.Bool using (false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-applyUpTo⁺; ∈-applyUpTo⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; _≤_; _<_; _+_)
open import Data.Nat.Properties using (≤-<-trans; <-≤-trans; ≮⇒≥; +-monoʳ-≤)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁)
open import Function using (mk⇔)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)

open import denotation.Position using (Pos; Label; root; _≟ᵖ_; ix; last; _∙_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; pin; Unpinned; _≺_; _≼_)
open import denotation.Laws.Modulus using (AgreeTo; ⟨_⟩; upto; ≼-refl; ≺→≼; ≺-ext)
open import denotation.Laws.Worlds using (⊕-cancelˡ; ⊕-assoc)
open import denotation.Laws.Cut using (ix-asc; ix-back)
import quickcheck.Tabled as Tb
open import quickcheck.Tabled using (_⊣_)
open import simultaneous.InstEmit using (valuesOf)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (One; Shown; Live)
open import simultaneous.Listing using (spinRows)
open import simultaneous.TableCorr using (TR; M; Corr; Rel; m-ss)
open import simultaneous.TakeCut using (inst-⊕)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- A spin's table

S : ∀ {X : Set} → ℕ → Pos → Maybe (Tb.Listed X)
S M q = just (spinRows M q ⊣ false)

sp→ : ∀ {X : Set} {M q k} {e : Ev X} → TR (S M q) k e → Σ ℕ λ i → i < M × k ≡ q ⊕ [ ix i ] × e ≡ skip
sp→ {q = q} (_ , refl , r) with ∈-applyUpTo⁻ (λ i → q ⊕ [ ix i ] , skip) r
... | i , lt , refl = i , lt , refl , refl

sp← : ∀ {X : Set} {M q i} → i < M → TR {X} (S M q) (q ⊕ [ ix i ]) skip
sp← {q = q} lt = _ , refl , ∈-applyUpTo⁺ (λ i → q ⊕ [ ix i ] , skip) lt

-- A position's last label: a leaf's row, one step past its subscription,
-- read back off its position.
lastOf : List Label → Label
lastOf []           = last
lastOf (l ∷ [])     = l
lastOf (_ ∷ l ∷ ls) = lastOf (l ∷ ls)

lastL : Pos → Label
lastL (_ ∙ x) = lastOf x

lastL-⊕ : ∀ q l → lastL (q ⊕ [ l ]) ≡ l
lastL-⊕ (c ∙ x) l = go x
  where
    go : ∀ x → lastOf (x ++ [ l ]) ≡ l
    go []           = refl
    go (_ ∷ [])     = refl
    go (_ ∷ m ∷ xs) = go (m ∷ xs)

-- One step past a subscription, two positions differ by their labels.
step-inj : ∀ q {a b} → q ⊕ [ a ] ≡ q ⊕ [ b ] → a ≡ b
step-inj q {a} {b} eq = trans (sym (lastL-⊕ q a)) (trans (cong lastL eq) (lastL-⊕ q b))

ix-inj : ∀ {i j} → ix i ≡ ix j → i ≡ j
ix-inj refl = refl

-- Nothing lies under a step.
step-flat : ∀ q {a b l ys} → (q ⊕ [ a ]) ⊕ (l ∷ ys) ≡ q ⊕ [ b ] → ⊥
step-flat q {a} {b} {l} {ys} eq with ⊕-cancelˡ q [ b ] (a ∷ l ∷ ys) (trans (sym eq) (⊕-assoc q [ a ] (l ∷ ys)))
... | ()

-- A shallower spin's ticks, a deeper one's.
widen : ∀ {X : Set} {M M′ q y} {e : Ev X} → M ≤ M′ → TR (S M q) y e → TR (S M′ q) y e
widen le x with sp→ x
... | j , lj , refl , refl = sp← (<-≤-trans lj le)

-- A deeper spin's ticks up to one the shallower lists, the shallower's.
shrink : ∀ {X : Set} {M M′ q i y} {e : Ev X} → i < M → y ≼ (q ⊕ [ ix i ]) → TR (S M′ q) y e → TR (S M q) y e
shrink {q = q} lt yk x with sp→ x
... | j , lj , refl , refl = sp← (≤-<-trans (≮⇒≥ (λ ij → yk (ix-asc q ij))) lt)

spin-ag : ∀ {X : Set} {M M′ q i} → M ≤ M′ → i < M → AgreeTo (q ⊕ [ ix i ]) (TR {X} (S M′ q)) (TR (S M q))
spin-ag le lt = ⟨ (λ yk → shrink lt yk , widen le) ⟩

-- No tick lies under another.
spin-flat : ∀ {X : Set} {M q y l ys} {e e′ : Ev X} → TR (S M q) y e → TR (S M q) (y ⊕ (l ∷ ys)) e′ → ⊥
spin-flat {q = q} x x′ with sp→ x
... | i , _ , refl , _ with sp→ x′
...   | j , _ , eq , _ = step-flat q eq

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

  corr′ : ∀ N → Corr p p* (φ′ N) (Put′ N) (TR (P N)) (TR (Q N))
  corr′ N = record
    { row→ = row→′
    ; pin→ = pin→′
    ; put-before = λ _ ()
    ; shown← = shown←′
    ; place = λ y _ → inj₁ (same y)
    ; mono = mono′
    ; inst = λ {k} {k′} x x′ _ _ →
        mk⇔ (λ _ → trans (same x) (sym (same x′)))
            (λ _ → trans (inst-⊕ p* [ lastL k ]) (sym (inst-⊕ p* [ lastL k′ ])))
    ; home = λ {k} x _ → mk⇔ (λ _ → same x) (λ _ → inst-⊕ p* [ lastL k ]) }
    where
      row→′ : ∀ {k e} → TR (P N) k e → Unpinned e
            → (Σ (Ev (IE A)) λ e′ → TR (Q N) (φ′ N k) e′ × M e e′) ⊎ (e ≡ skip × Corr.PutAt (corr′ N) k)
      row→′ x _ with sp→ x
      ... | i , lt , refl , refl = inj₁ (skip , subst (λ z → TR (Q N) z skip) (sym (φ-ix {N} i)) (sp← lt) , m-ss {A})

      pin→′ : ∀ {k r} → TR (P N) k (pin r) → Live (TR (P N)) k → Corr.PinAt (corr′ N) k r
      pin→′ x _ with sp→ x
      ... | _ , _ , _ , ()

      shown←′ : ∀ {l e′} → TR (Q N) l e′ → Shown (One valuesOf) e′
              → Σ Pos λ k → Σ (Ev A) λ e → l ≡ φ′ N k × TR (P N) k e × Unpinned e × M e e′
      shown←′ y sh with sp→ y
      ... | _ , _ , _ , refl = ⊥-elim sh

      mono′ : ∀ {k k′ e e′} → TR (P N) k e → TR (P N) k′ e′ → Unpinned e → Unpinned e′ → k ≺ k′ → φ′ N k ≺ φ′ N k′
      mono′ x x′ _ _ lt with sp→ x | sp→ x′
      ... | i , _ , refl , _ | j , _ , refl , _ = subst₂ _≺_ (sym (φ-ix {N} i)) (sym (φ-ix {N} j)) (ix-asc p* (ix-back p lt))

  rel′ : Rel P Q p p*
  rel′ = record
    { φ = φ′ ; Put = Put′ ; corr = corr′
    ; φ-agree = λ _ _ _ → refl
    ; bk = λ l → [ p ⊕ [ lastL l ] ]
    ; in-bk = in-bk′
    ; pb-few = λ _ → [] , λ ()
    ; elab-causal = λ le x un _ → elab-causal′ le x un
    ; stable← = stable←′
    ; stable-put = λ _ _ _ ()
    ; stable-lead = λ le x un _ _ _ _ _ → elab-causal′ le x un
    ; elab-all = elab-all′
    ; func = λ x x′ → trans (proj₂ (proj₂ (proj₂ (sp→ x)))) (sym (proj₂ (proj₂ (proj₂ (sp→ x′)))))
    ; func* = λ y y′ → trans (proj₂ (proj₂ (proj₂ (sp→ y)))) (sym (proj₂ (proj₂ (proj₂ (sp→ y′)))))
    ; flat = spin-flat
    ; flat* = spin-flat
    ; pin-in = λ x → ⊥-elim (pin-no x)
    ; pin-in* = λ y → ⊥-elim (pin-no y)
    ; cons = λ _ x _ _ → ⊥-elim (out-no x)
    ; cons* = λ _ y _ _ → ⊥-elim (out-no y)
    ; got = λ _ → _ , refl
    ; got* = λ _ → _ , refl
    ; after = after′
    ; after* = after′
    ; after-φ = λ {_} {k} _ _ → ≺→≼ {p*} {p* ⊕ [ lastL k ]} (≺-ext p* []) }
    where
      pin-no : ∀ {X : Set} {M q k r} → TR {X} (S M q) k (pin r) → ⊥
      pin-no x with sp→ x
      ... | _ , _ , _ , ()

      out-no : ∀ {X : Set} {M q k} {v : X} → TR (S M q) k (out v) → ⊥
      out-no x with sp→ x
      ... | _ , _ , _ , ()

      in-bk′ : ∀ {N k e} → TR (P N) k e → Unpinned e → k ∈ [ p ⊕ [ lastL (φ′ N k) ] ]
      in-bk′ {N} x _ with sp→ x
      ... | i , _ , refl , _ = here (cong (λ l → p ⊕ [ l ]) (sym (trans (lastL-⊕ p* (lastL (p ⊕ [ ix i ]))) (lastL-⊕ p (ix i)))))

      elab-causal′ : ∀ {N N′ k e} → N ≤ N′ → TR (P N) k e → Unpinned e → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N))
      elab-causal′ {N} le x _ with sp→ x
      ... | i , lt , refl , _ = subst (λ z → AgreeTo z (TR (Q _)) (TR (Q N))) (sym (φ-ix {N} i)) (spin-ag (+-monoʳ-≤ 3 le) lt)

      stable←′ : ∀ {N N′ k e e′} → N ≤ N′ → TR (P N) k e → Unpinned e → TR (Q N) (φ′ N k) e′
               → AgreeTo (φ′ N k) (TR (Q N′)) (TR (Q N)) → AgreeTo k (TR (P N′)) (TR (P N))
      stable←′ le x _ _ _ with sp→ x
      ... | i , lt , refl , _ = spin-ag (+-monoʳ-≤ 3 le) lt

      elab-all′ : ∀ {N N′} → N ≤ N′ → (∀ q → AgreeTo q (TR (P N′)) (TR (P N))) → ∀ {y e} → TR (Q N′) y e → TR (Q N) y e
      elab-all′ {N} {N′} _ all y with sp→ y
      ... | j , lj , refl , refl with sp→ {M = 3 + N} (proj₁ (upto (all (p ⊕ [ ix j ])) {p ⊕ [ ix j ]} {skip} (≼-refl {p ⊕ [ ix j ]})) (sp← lj))
      ...   | j′ , lj′ , eq , _ = sp← (subst (_< 3 + N) (sym (ix-inj (step-inj p eq))) lj′)

      after′ : ∀ {X : Set} {N q k} {e : Ev X} → TR (S (3 + N) q) k e → q ≼ k
      after′ {q = q} x with sp→ x
      ... | i , _ , refl , _ = ≺→≼ {q} {q ⊕ [ ix i ]} (≺-ext q [])

spin-tab : ∀ {A} p p* → Rel {A} (λ N → just (spinRows (3 + N) p ⊣ false)) (λ N → just (spinRows (3 + N) p* ⊣ false)) p p*
spin-tab p p* = SpinTab.rel′ p p*
