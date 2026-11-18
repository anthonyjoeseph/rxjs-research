{-# OPTIONS --guardedness #-}

-- WHERE A CUT STOPS BEING THE RUN, ON BOTH SIDES AT ONCE.  A cut bounds
-- each hang's rows, so past the last row it keeps of one (an EDGE) its
-- table is no longer the run's.  Two tables corresponding at one cut
-- (`Corr`) whose edges correspond (`Edges.hang←`, `Edges.hang→`: every
-- elaborated edge at or past a plain edge's image, every plain edge's
-- image at or past an elaborated edge) are the runs' together: a plain
-- row at or before every plain edge has its image at or before every
-- elaborated one (`Edges.img-clear`), and back (`Edges.back-clear`).
--
-- No subterm is asked whether a hang came before one of its rows.  Its
-- tables are finite at every cut, and only the root's are held against
-- the run, by the edges alone.
--
-- A spin's edges correspond (`spin-edges`): each side's is its last
-- row, and the map takes one to the other.  A `defer` keeps its child's
-- (`DeferEdges`): the guard row is no edge, and a child's row keeps its
-- image.
module simultaneous.HangCut where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([_])
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import denotation.Position using (Pos; root; _≟ᵖ_; ix; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; skip; Unpinned; EmissionSet; _≺_; _≼_)
open import denotation.Laws.Modulus using (≼-refl; ≺→≼; ≼-trans; ≼-split; ≼-or-≻; ≺-≼-≺; ≼-≺-≺; ≺-absurd)
import quickcheck.Tabled as Tb
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.TableCorr using (TR; Corr; Rel; module Rel; Scope)
open import simultaneous.TableSpin using (module SpinTab; sp←)
open import simultaneous.TableDefer using (module DeferTab; tr-g←)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE)

------------------------------------------------------------------------
-- Edges corresponding

module Edges {A : Set} {s s* : Pos} {φ : Pos → Pos} {Put : Pos → Pos → Set} {Late : Pos → Set}
  {L : EmissionSet A} {L* : EmissionSet (IE A)} (C : Corr s s* φ Put Late L L*)
  (Hg Hg* : Pos → Set)
  -- an edge is a row with an image
  (hg-row : ∀ {g} → Hg g → Σ (Ev A) λ e → L g e × Unpinned e × ¬ Late g)
  (hang← : ∀ {g*} → Hg* g* → Σ Pos λ g → Hg g × φ g ≼ g*)
  (hang→ : ∀ {g} → Hg g → Σ Pos λ g* → Hg* g* × g* ≼ φ g)
  where

  -- At or before every edge.
  Clear : Pos → Set
  Clear k = ∀ {g} → Hg g → k ≼ g

  Clear* : Pos → Set
  Clear* l = ∀ {g*} → Hg* g* → l ≼ g*

  -- THE IMAGE OF A ROW BEFORE EVERY HANG IS BEFORE EVERY HANG.
  img-clear : ∀ {k e} → L k e → Unpinned e → ¬ Late k → Clear k → Clear* (φ k)
  img-clear {k} x un nl cl {g*} h* with hang← h*
  ... | g , h , le with hg-row h | ≼-split {k} {g} (cl h)
  ...   | _ | inj₂ refl = le
  ...   | e₀ , x₀ , un₀ , nl₀ | inj₁ lt = ≺→≼ {φ k} {g*} (≺-≼-≺ {φ k} {φ g} {g*} (Corr.mono C x x₀ un un₀ nl nl₀ lt) le)

  -- And a row whose image is, is.
  back-clear : ∀ {k e} → L k e → Unpinned e → ¬ Late k → Clear* (φ k) → Clear k
  back-clear {k} x un nl cl* {g} h lt with hang→ h | hg-row h
  ... | g* , h* , le | e₀ , x₀ , un₀ , nl₀ =
    cl* h* (≼-≺-≺ {g*} {φ g} {φ k} le (Corr.mono C x₀ x un₀ un nl₀ nl lt))

  -- A late placement of a skip strictly before every hang is before
  -- every hang.
  put-clear : ∀ {k l} → L k skip → Put k l → (∀ {g} → Hg g → k ≺ g) → Clear* l
  put-clear {k} {l} x pl cl {g*} h* with hang← h*
  ... | g , h , le with hg-row h
  ...   | e₀ , x₀ , un₀ , nl₀ = ≼-trans {l} {φ g} {g*} (Corr.put-before C x pl x₀ un₀ nl₀ (cl h)) le

------------------------------------------------------------------------
-- A spin's edges

module SpinEdges {A : Set} (p p* : Pos) {S′ : Scope} (N : ℕ) where
  open SpinTab {A} p p* {S′}

  Hg : Pos → Set
  Hg g = g ≡ p ⊕ [ ix (2 + N) ]

  Hg* : Pos → Set
  Hg* g* = g* ≡ p* ⊕ [ ix (2 + N) ]

  hg-row : ∀ {g} → Hg g → Σ (Ev A) λ e → TR (P N) g e × Unpinned e × ¬ ⊥
  hg-row refl = skip , sp← ≤-refl , tt , λ ()

  hang← : ∀ {g*} → Hg* g* → Σ Pos λ g → Hg g × φ′ N g ≼ g*
  hang← refl = p ⊕ [ ix (2 + N) ] , refl , subst (_≼ (p* ⊕ [ ix (2 + N) ])) (sym (φ-ix {N} (2 + N))) (≼-refl {p* ⊕ [ ix (2 + N) ]})

  hang→ : ∀ {g} → Hg g → Σ Pos λ g* → Hg* g* × g* ≼ φ′ N g
  hang→ refl = p* ⊕ [ ix (2 + N) ] , refl , subst ((p* ⊕ [ ix (2 + N) ]) ≼_) (sym (φ-ix {N} (2 + N))) (≼-refl {p* ⊕ [ ix (2 + N) ]})

  spin-edges : ∀ {k e} → TR (P N) k e → Unpinned e → Edges.Clear (corr′ N) Hg Hg* hg-row hang← hang→ k
             → Edges.Clear* (corr′ N) Hg Hg* hg-row hang← hang→ (φ′ N k)
  spin-edges x un = Edges.img-clear (corr′ N) Hg Hg* hg-row hang← hang→ x un (λ ())

------------------------------------------------------------------------
-- A defer keeps its child's edges

module DeferEdges {A : Set} (p p* : Pos) {P : ℕ → Maybe (Tb.Listed A)} {Q : ℕ → Maybe (Tb.Listed (IE A))}
  {S : Scope} (R : Rel P Q (p ⊕ [ ix 1 ]) (p* ⊕ [ ix 1 ]) S) (N : ℕ)
  (Hg Hg* : Pos → Set)
  (hg-row : ∀ {g} → Hg g → Σ (Ev A) λ e → TR (P N) g e × Unpinned e × ¬ Rel.Late R N g)
  (hang← : ∀ {g*} → Hg* g* → Σ Pos λ g → Hg g × Rel.φ R N g ≼ g*)
  (hang→ : ∀ {g} → Hg g → Σ Pos λ g* → Hg* g* × g* ≼ Rel.φ R N g)
  where
  open DeferTab p p* R

  hg-row′ : ∀ {g₀} → Hg g₀ → Σ (Ev A) λ e → TR (P′ N) g₀ e × Unpinned e × ¬ Late′ N g₀
  hg-row′ h with hg-row h
  ... | e , x , un , nl = e , tr-g← g (P N) x , un , λ { (_ , lt) → nl lt }

  hang←′ : ∀ {g₁} → Hg* g₁ → Σ Pos λ g₀ → Hg g₀ × φ′ N g₀ ≼ g₁
  hang←′ {g₁} h* with hang← h*
  ... | g₀ , h , le with hg-row h
  ...   | _ , x , _ , _ = g₀ , h , subst (_≼ g₁) (sym (φ-c {N} {g₀} (ab N x))) le

  hang→′ : ∀ {g₀} → Hg g₀ → Σ Pos λ g₁ → Hg* g₁ × g₁ ≼ φ′ N g₀
  hang→′ {g₀} h with hang→ h | hg-row h
  ... | g₁ , h* , le | _ , x , _ , _ = g₁ , h* , subst (g₁ ≼_) (sym (φ-c {N} {g₀} (ab N x))) le

  defer-edges : ∀ {k e} → TR (P′ N) k e → Unpinned e → ¬ Late′ N k → Edges.Clear (corr′ N) Hg Hg* hg-row′ hang←′ hang→′ k
              → Edges.Clear* (corr′ N) Hg Hg* hg-row′ hang←′ hang→′ (φ′ N k)
  defer-edges = Edges.img-clear (corr′ N) Hg Hg* hg-row′ hang←′ hang→′
