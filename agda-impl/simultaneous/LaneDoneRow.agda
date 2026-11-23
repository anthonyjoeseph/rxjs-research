{-# OPTIONS --guardedness #-}

-- A LANE PART'S SHARE ENDING, THE LANE SHOWS ITS `laneDone` IN THAT
-- INSTANT (`done-row`), the upward mirror of `simultaneous.LaneInnerEnd`.
-- The frame reads the share, so its second piece ends where the share
-- does and its third shows the `laneDone`; the scan folds the frame up to
-- it, the map shows it, and each layer above shows it, its rows before it
-- few.  The share's rows before it are its rows up to its end; the
-- burst part's lane has few rows anywhere.
module simultaneous.LaneDoneRow where

open import Data.Bool using (not; T)
open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; ix; sub; root; instant; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; end; Proper; _≺_; _≼_; Few; module Op)
open import denotation.Laws.Modulus using (≺-trans; ≼-split; ≺-irrefl)
open import denotation.Laws.Worlds using (InvAt; ⊕-identityʳ)
open import denotation.Laws.BoundedInv using (end-uniq)
open import denotation.Laws.Cut using (ix-asc)
open import simultaneous.HeldComb using (ev)
open import simultaneous.EnterFew using (enter-few)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (laneStart; laneDone)
open import simultaneous.LaneLayers using (Under; under-refl; under-⊕; under-≺; few-tr)
open import simultaneous.LaneSite using (between-under)
open import simultaneous.ConcatThree using (module Three)
open import simultaneous.LaneStart using (module C; Sh; sh-past; laneAt)
open import simultaneous.LaneUp using (module Lift)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; laneStep; undone; marked; piece; shareˢ; counted; framed; laneSrc)

-- A lawful set's row before a position under its end is at or before
-- the end: past it, it would lie under the end.
between-flat : ∀ {C H p} {X : EmissionSet C} → InvAt H p X → ∀ {e k w e′} → X e end → X k e′ → Under e w → k ≺ w → k ≼ e
between-flat {X = X} I {e} {k} {w} {e′} se x u lt ek = go (between-under u ek lt)
  where
    go : Under e k → ⊥
    go ([] , eq)     = ≺-irrefl {e} (subst (e ≺_) (trans eq (⊕-identityʳ e)) ek)
    go (_ ∷ _ , eq)  = InvAt.flat I se (subst (λ z → X z e′) eq x)

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where
  open Lift ρ′ o ρ using (p0→; p0←; p1→; p1←)

  ld : IE B
  ld = marked (laneDone 0)

  -- The lane part's third piece, read through the elaboration.
  p2→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y e → enter (Op.of (ld ∷ [])) s y e
  p2→ nothing  h h′ s r = r
  p2→ (just _) h h′ s r = r

  p2← : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (Op.of (ld ∷ [])) s y e → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y e
  p2← nothing  h h′ s r = r
  p2← (just _) h h′ s r = r

  module _ (m : Maybe ℕ) where
    open C ρ′ o ρ m using (MM; Fr; H₁; H₂; Bp)
    open Lift.At ρ′ o ρ m using (ShE; FrE; module Up)

    -- THE FRAME SHOWS ITS `laneDone` IN ITS SHARE'S ENDING INSTANT: its
    -- second piece reads the share and ends one label under its end, and
    -- its third, queued there, shows the `laneDone`.  The frame's rows
    -- before it are few, and the share's rows before it are its rows up to
    -- its end, none lying under it.  Lawful only: a share read over a hot
    -- holding a row under its own end shows one under its end too.
    frame-ld : ∀ P {H p} → InvAt H p (ShE P) → ∀ {e} → ShE P e end
             → Σ Pos λ w → FrE P w (out ld) × Few (FrE P) w × instant w ≡ instant e × (∀ {k e′} → ShE P k e′ → k ≺ w → k ≼ e) × Bp P ≺ w
    frame-ld P I {e} se = Th.w , Th.row , few-tr (Th.few Th.w) , Th.w-inst , (λ x lt → between-flat I se x u-w lt) , Bw
      where
        Q′ : Pos
        Q′ = P ⊕ [ ix 0 ]

        h₁ = H₁ P
        h₂ = H₂ P lanePart

        Qe : (Q′ ⊕ [ ix 1 ]) ≺ e
        Qe = sh-past ρ′ o ρ m lanePart h₁ (Q′ ⊕ [ ix 1 ]) se

        ef = enter-few (ev m (Sh ρ′ o ρ lanePart) (h₁ ∷ ρ)) (Q′ ⊕ [ ix 1 ]) se tt

        Tp : EmissionSet (IE B)
        Tp = Proper (ShE P)

        te : Tp e end
        te = se , λ {c} ce lt → ≺-irrefl {c} (subst (c ≺_) (sym (end-uniq I ce se)) lt)

        tu : ∀ {c} → Tp c end → c ≡ e
        tu (x , _) = end-uniq I x se

        tl : ∀ {y e′} → Tp y e′ → y ≼ e
        tl (_ , mn) = mn se

        tf : Few Tp e
        tf = proj₁ ef , λ x lt → proj₂ ef (proj₁ x) lt

        q₂e : (Bp P ⊕ [ ix 2 ]) ≺ e
        q₂e = ≺-trans {Bp P ⊕ [ ix 2 ]} {Q′ ⊕ [ ix 1 ]} {e} (under-≺ Q′ (s≤s z≤n) (under-⊕ (under-refl (Bp P)) (ix 2))) Qe

        module Th = Three (λ j → ev m (piece {B = B} lanePart j) (h₂ ∷ h₁ ∷ ρ)) (Bp P) (marked laneStart) ld Tp {e}
          (p0→ m h₁ h₂) (p0← m h₁ h₂) (p1→ m h₁ h₂) (p1← m h₁ h₂) (p2→ m h₁ h₂) (p2← m h₁ h₂) te tu tl tf q₂e

        u-w : Under e Th.w
        u-w = under-⊕ (under-⊕ (under-⊕ (under-refl e) (sub Th.s₁)) (ix 1)) (ix 0)

        Bw : Bp P ≺ Th.w
        Bw = ≺-trans {Bp P} {e} {Th.w} (≺-trans {Bp P} {Q′ ⊕ [ ix 1 ]} {e} (ix-asc Q′ (s≤s z≤n)) Qe) Th.e≺w

    -- THE LANE SHOWS ITS `laneDone` IN ITS SHARE'S ENDING INSTANT.
    core-row : ∀ s {H p} → InvAt H p (ShE (laneAt s)) → ∀ {e} → ShE (laneAt s) e end
             → ¬ ¬ Σ Pos λ f′ → Σ (IE B) λ v → enter MM s f′ (out v) × T (not (undone v)) × instant f′ ≡ instant e
    core-row s I {e} se κ = U.val-up frow λ (b , r) → κ (w , _ , r , tt , iw)
      where
        P : Pos
        P = laneAt s

        F = frame-ld P I se
        w = proj₁ F
        frow = proj₁ (proj₂ F)
        ffew = proj₁ (proj₂ (proj₂ F))
        iw = proj₁ (proj₂ (proj₂ (proj₂ F)))
        shb = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ F))))
        Bw = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ F))))

        ef = enter-few (ev m (Sh ρ′ o ρ lanePart) (H₁ P ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) se tt

        shf : Few (ShE P) w
        shf = e ∷ proj₁ ef , pick
          where
            pick : ∀ {k e′} → ShE P k e′ → k ≺ w → k ∈ (e ∷ proj₁ ef)
            pick {k} x lt with ≼-split {k} {e} (shb x lt)
            ... | inj₁ lt′ = there (proj₂ ef x lt′)
            ... | inj₂ eq = here eq

        module U = Up s ffew shf Bw

  -- The lane part's share, as the elaboration builds it, is the core's.
  done-row : ∀ m s {H p} → InvAt H p (enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))
           → ∀ {e} → enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) e end
           → ¬ ¬ Σ Pos λ f′ → Σ (IE B) λ v
               → enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s f′ (out v)
               × T (not (undone v)) × instant f′ ≡ instant e
  done-row nothing  s I se = core-row nothing s I se
  done-row (just n) s I se = core-row (just n) s I se
