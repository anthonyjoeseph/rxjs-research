{-# OPTIONS --guardedness #-}

-- A SPIN'S TABLE: a `defer` cut at depth zero lists skips at its
-- subscription's ticks (`S`), read back by index (`sp→`); a deeper cut
-- lists more ticks, agreeing up to any tick the shallower lists
-- (`spin-ag`).
module simultaneous.SpinKit where

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
open import Relation.Nullary using (¬_)

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
open import simultaneous.TableKit using (TR)


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

