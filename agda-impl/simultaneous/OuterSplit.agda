{-# OPTIONS --guardedness #-}

-- THE OUTER'S ROWS THE SCAN'S SOURCE MEETS ARE A RUN OF THE OUTER
-- (`simultaneous.BranchSplit`): the outer is read by its hot, its value
-- through `opening`, then tagged.
module simultaneous.OuterSplit where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; [_])
open import Effect.Monad using (RawMonad)
open import Level using () renaming (zero to lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-Monad)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; sub; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; EmissionSet; Den; hot; enter; Few; _≺_; _≼_; module Op)
open import denotation.Laws.Worlds using (Lawful; Shows; hot-shows)
open import simultaneous.SObs using (lone; module Elaborate; Branch; outerB)
open import simultaneous.FlatLanes using (Tg)
open import simultaneous.BranchSplit using (SrcOf; OwnOf; K; kout; kskip; kend; mev; module BranchSplit)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Input; opening)

-- The outer's row, as the source tags it.
Ou : ∀ {B} → IE B → Maybe (Input B)
Ou x = Tg outerB x

module OuterSplit {A B : Set} (σ : EmissionSet (IE A)) (Lσ : Lawful σ) (P : Pos)
                  (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B)))
                  (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
                  (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf))
                  (eqG : G outerB ≡ Op.map Ou (Op.map (opening {A} {B}) (hot σ)))
                  (noF : ∀ {s k x} → enter (F true) s k (out (Ou x)) → ⊥)
                  (noC : ∀ {s k x} → enter (C false) s k (out (Ou x)) → ⊥)
                  (noG : ∀ {b s k x} → enter (G b) s k (out (Ou x)) → b ≡ outerB)
                  (funcM : ∀ {y e e′} → SrcOf F P y e → SrcOf F P y e′ → e ≡ e′)
                  (past : ∀ zs {k e} → σ k e → (P ⊕ zs) ≺ k) where
  open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)
  open BranchSplit σ Lσ P outerB (opening {A} {B}) F C G (Op.map Ou (Op.map (opening {A} {B}) (hot σ))) eqF eqC eqG noF noC noG funcM past public

  open Up (s-map Ou {d = Op.map (opening {A} {B}) (hot σ)} (s-map (opening {A} {B}) {d = hot σ} s-hot)) public

  dpast : ∀ {k e} → T1 k e → J ≺ k
  dpast = map-past Ou {d = Op.map (opening {A} {B}) (hot σ)} (map-past (opening {A} {B}) {d = hot σ} hot-past)

  private
    top : ∀ {e₀} → K0 e₀ → K outerB (mev Ou (mev (opening {A} {B}) e₀))
    top (k0out x) = kout (opening x)
    top k0skip    = kskip
    top k0end     = kend

  -- The outer's row as its reader shows it, opened and tagged.
  dshow : Shows σ → ∀ {q} → Few T1 q → ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
        → ¬ ¬ Σ _ λ e₁ → T1 (y ⊕ [ sub J ]) e₁ × K outerB e₁ × (∀ {x} → e ≡ out x → e₁ ≡ out (g x))
  dshow shσ f1 ry Yq with rj ry
  ... | e₀ , r0 , k0 , o0 with map-lift Ou (Op.map (opening {A} {B}) (hot σ)) (map-shows (opening {A} {B}) (hot σ) (hot-shows σ J)) f1
  ...   | f0′ , lift′ with map-lift (opening {A} {B}) (hot σ) (hot-shows σ J) f0′
  ...     | f0 , lift₀ =
    t0-of shσ f0 ry r0 Yq >>= λ t0 → lift₀ t0 Yq >>= λ t0′ → lift′ t0′ Yq >>= λ t1 →
    pure (mev Ou (mev (opening {A} {B}) e₀) , t1 , top k0 , λ {_} eq → cong (λ z → mev Ou (mev (opening {A} {B}) z)) (o0 eq))
