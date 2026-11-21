{-# OPTIONS --guardedness #-}

-- THE LANES' ROWS THE SCAN'S SOURCE MEETS ARE A RUN OF THE LANES
-- (`simultaneous.BranchSplit`): the lanes are read by their hot, tagged,
-- their values unchanged.
module simultaneous.LaneSplit where

open import Data.Product using (Σ; _×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; [_])
open import Effect.Monad using (RawMonad)
open import Level using () renaming (zero to lzero)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Negation using (¬¬-Monad)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Tree using (mergeᶠ)
open import denotation.Position using (Pos; sub; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; EmissionSet; Den; hot; enter; Few; _≺_; _≼_; module Op)
open import denotation.Laws.Worlds using (Lawful; Shows; hot-shows)
open import simultaneous.SObs using (lone; module Elaborate; Branch; laneB)
open import simultaneous.Project using (Proj)
import simultaneous.Project as Proj
open import simultaneous.FlatLanes using (Tg; laneTag; BProj; keep; drop)
import simultaneous.FlatLanes as FL
open import simultaneous.BranchSplit using (SrcOf; OwnOf; K; kout; kskip; kend; mev; module BranchSplit)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; Input)

-- A lane's row, as the source tags it.
Ln : ∀ {B} → IE B → Maybe (Input B)
Ln x = Tg laneB x

-- A run's lane rows, where the source meets them.
lane-proj : ∀ {B J} {rx : List (Pos × Ev (Maybe (Input B)))} {rs} → BProj laneB (λ x → x) J rx rs → Proj laneTag rx rs
lane-proj FL.[]          = Proj.[]
lane-proj (keep pr)      = Proj.keep refl refl (lane-proj pr)
lane-proj (drop nl pr)   = Proj.drop nl (lane-proj pr)

module LaneSplit {B : Set} (σ : EmissionSet (IE B)) (Lσ : Lawful σ) (P : Pos)
                 (F C : Bool → Den (Maybe (Input B))) (G : Branch → Den (Maybe (Input B)))
                 (eqF : F false ≡ Op.flatMap (mergeᶠ (just 1)) C (Op.of (true ∷ false ∷ [])))
                 (eqC : C true ≡ Op.flatMap (mergeᶠ nothing) G (Op.of OwnOf))
                 (eqG : G laneB ≡ Op.map Ln (hot σ))
                 (noF : ∀ {s k x} → enter (F true) s k (out (Ln x)) → ⊥)
                 (noC : ∀ {s k x} → enter (C false) s k (out (Ln x)) → ⊥)
                 (noG : ∀ {b s k x} → enter (G b) s k (out (Ln x)) → b ≡ laneB)
                 (funcM : ∀ {y e e′} → SrcOf F P y e → SrcOf F P y e′ → e ≡ e′)
                 (past : ∀ zs {k e} → σ k e → (P ⊕ zs) ≺ k) where
  open RawMonad (¬¬-Monad {lzero}) using (_>>=_; pure)
  open BranchSplit σ Lσ P laneB (λ x → x) F C G (Op.map Ln (hot σ)) eqF eqC eqG noF noC noG funcM past public

  open Up (s-map Ln {d = hot σ} s-hot) public

  dpast : ∀ {k e} → T1 k e → J ≺ k
  dpast = map-past Ln {d = hot σ} hot-past

  private
    top : ∀ {e₀} → K0 e₀ → K laneB (mev Ln e₀)
    top (k0out x) = kout x
    top k0skip    = kskip
    top k0end     = kend

  -- A lanes' row as their reader shows it, tagged.
  dshow : Shows σ → ∀ {q} → Few T1 q → ∀ {y e} → σ y e → (y ⊕ [ sub J ]) ≼ q
        → ¬ ¬ Σ _ λ e₁ → T1 (y ⊕ [ sub J ]) e₁ × K laneB e₁ × (∀ {x} → e ≡ out x → e₁ ≡ out (g x))
  dshow shσ f1 ry Yq with rj ry
  ... | e₀ , r0 , k0 , o0 with map-lift Ln (hot σ) (hot-shows σ J) f1
  ...   | f0 , lift = t0-of shσ f0 ry r0 Yq >>= λ t0 → lift t0 Yq >>= λ t1 → pure (mev Ln e₀ , t1 , top k0 , λ {_} eq → cong (mev Ln) (o0 eq))
