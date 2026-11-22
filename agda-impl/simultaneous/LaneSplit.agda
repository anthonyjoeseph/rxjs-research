{-# OPTIONS --guardedness #-}

-- THE ROWS OF A HOT BRANCH THE SCAN'S SOURCE MEETS ARE A RUN OF IT
-- (`simultaneous.BranchSplit`): the lanes, and the closer, are each read
-- by their hot, tagged, their values unchanged.
module simultaneous.LaneSplit where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_; [_])
open import Effect.Monad using (RawMonad)
open import Level using () renaming (zero to lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-Monad)
open import Relation.Binary.PropositionalEquality using (_≡_; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; sub; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (out; end; ended; EmissionSet; Den; hot; enter; Few; _≺_; _≼_; module Op)
open import denotation.Laws.Worlds using (Lawful; Shows; hot-shows)
open import simultaneous.SObs using (lone; module Elaborate; Branch; laneB)
open import simultaneous.FlatLanes using (Tg)
import simultaneous.FlatLanes as FL
open import simultaneous.BranchSplit using (SrcOf; OwnOf; K; kout; kskip; kend; mev; module BranchSplit)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Input)

-- A lane's row, as the source tags it.
Ln : ∀ {B} → IE B → Maybe (Input B)
Ln x = Tg laneB x

module HotSplit {B : Set} (b : Branch) (σ : EmissionSet (IE B)) (Lσ : Lawful σ) (P : Pos)
                 (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B)))
                 (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
                 (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf))
                 (eqG : G b ≡ Op.map (Tg b) (hot σ))
                 (noF : ∀ {s k x} → enter (F true) s k (out (Tg b x)) → ⊥)
                 (noC : ∀ {s k x} → enter (C false) s k (out (Tg b x)) → ⊥)
                 (noG : ∀ {b′ s k x} → enter (G b′) s k (out (Tg b x)) → b′ ≡ b)
                 (funcM : ∀ {y e e′} → SrcOf F P y e → SrcOf F P y e′ → e ≡ e′)
                 (past : ∀ zs {k e} → σ k e → (P ⊕ zs) ≺ k) where
  open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)
  open BranchSplit σ Lσ P b (λ x → x) F C G (Op.map (Tg b) (hot σ)) eqF eqC eqG noF noC noG funcM past public

  open Up (s-map (Tg b) {d = hot σ} s-hot) public

  dpast : ∀ {k e} → T1 k e → J ≺ k
  dpast = map-past (Tg b) {d = hot σ} hot-past

  private
    top : ∀ {e₀} → K0 e₀ → K b (mev (Tg b) e₀)
    top (k0out x) = kout x
    top k0skip    = kskip
    top k0end     = kend

  -- A lanes' row as their reader shows it, tagged.
  dshow : Shows σ → ∀ {q} → Few T1 q → ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
        → ¬ ¬ Σ _ λ e₁ → T1 (y ⊕ [ sub J ]) e₁ × K b e₁ × (∀ {x} → e ≡ out x → e₁ ≡ out (g x))
  dshow shσ f1 ry Yq with rj ry
  ... | e₀ , r0 , k0 , o0 with map-lift (Tg b) (hot σ) (hot-shows σ J) f1
  ...   | f0 , lift = t0-of shσ f0 ry r0 Yq >>= λ t0 → lift t0 Yq >>= λ t1 → pure (mev (Tg b) e₀ , t1 , top k0 , λ {_} eq → cong (mev (Tg b)) (o0 eq))

  -- A lanes' end as their reader shows it.
  dend : Shows σ → ∀ {q} → Few T1 q → ∀ {y} → σ y end → (y ⊕ [ sub J ]) ≼ q → ¬ ¬ T1 (y ⊕ [ sub J ]) end
  dend shσ f1 ry Yq with map-lift (Tg b) (hot σ) (hot-shows σ J) f1
  ... | f0 , lift = t0-of shσ f0 ry (ended ry (pastJ ry)) Yq >>= λ t0 → lift t0 Yq
