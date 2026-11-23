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
open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; ix; sub; last; root; instant; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; end; Proper; at-out; on-out; at-end; _≺_; _≼_; Few;
  MapT; map-out; LaneOf; module Op; module Joining; module Merge; module Scan; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≼-split; ≺-irrefl)
open import denotation.Laws.Worlds using (InvAt; ⊕-identityʳ)
open import denotation.Laws.BoundedInv using (end-uniq)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.HeldComb using (ev)
open import simultaneous.EnterFew using (enter-few)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (laneStart; laneDone)
open import simultaneous.LaneLayers using (Under; under-refl; under-⊕; under-≺; few-row; few-tr; map-few; scan-few; join-few)
open import simultaneous.LaneSite using (between-under)
open import simultaneous.ConcatThree using (module Three)
open import simultaneous.BurstFew using (conn-few-src; burst-few)
open import simultaneous.LaneStart using (module C; Sh; sh-past; laneAt; z₀)

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

  ld : IE B
  ld = marked (laneDone 0)

  -- The lane part's pieces, read through the elaboration.
  p0→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} lanePart 0) (h′ ∷ h ∷ ρ)) s y e → enter (Op.of (marked laneStart ∷ [])) s y e
  p0→ nothing  h h′ s r = r
  p0→ (just _) h h′ s r = r

  p0← : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (Op.of (marked laneStart ∷ [])) s y e → enter (ev m (piece {B = B} lanePart 0) (h′ ∷ h ∷ ρ)) s y e
  p0← nothing  h h′ s r = r
  p0← (just _) h h′ s r = r

  p1→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} lanePart 1) (h′ ∷ h ∷ ρ)) s y e → enter h′ s y e
  p1→ nothing  h h′ s r = r
  p1→ (just _) h h′ s r = r

  p1← : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter h′ s y e → enter (ev m (piece {B = B} lanePart 1) (h′ ∷ h ∷ ρ)) s y e
  p1← nothing  h h′ s r = r
  p1← (just _) h h′ s r = r

  p2→ : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y e → enter (Op.of (ld ∷ [])) s y e
  p2→ nothing  h h′ s r = r
  p2→ (just _) h h′ s r = r

  p2← : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y e} → enter (Op.of (ld ∷ [])) s y e → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y e
  p2← nothing  h h′ s r = r
  p2← (just _) h h′ s r = r

  module _ (m : Maybe ℕ) where
    open C ρ′ o ρ m using (MM; Sv; Ct; Sc; Fr; H₁; H₂; Bp)

    ShE : Pos → EmissionSet (IE B)
    ShE P = enter (ev m (Sh ρ′ o ρ lanePart) (H₁ P ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

    FrE : Pos → EmissionSet (IE B)
    FrE P = enter (Fr lanePart (H₁ P) (H₂ P lanePart)) (Bp P)

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
    core-row s I {e} se κ = fold laneStep z₀ (FrE P) ffew frow λ (b , ac) → κ (w , _ , mm-row b ac , tt , iw)
      where
        P Q′ K : Pos
        P = laneAt s
        Q′ = P ⊕ [ ix 0 ]
        K = s ⊕ [ ix 0 ]

        h₁ = H₁ P
        h₂ = H₂ P lanePart

        F = frame-ld P I se
        w = proj₁ F
        frow = proj₁ (proj₂ F)
        ffew = proj₁ (proj₂ (proj₂ F))
        iw = proj₁ (proj₂ (proj₂ (proj₂ F)))
        shb = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ F))))
        Bw = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ F))))

        P≺w : P ≺ w
        P≺w = ≺-trans {P} {Bp P} {w} (≺-trans {P} {Q′} {Bp P} (≺-ext P []) (≺-ext Q′ [])) Bw

        ScE = enter (Sc lanePart h₁ h₂) (Bp P)

        scf : Few (Scan.ScanT laneStep z₀ (FrE P)) w
        scf = scan-few laneStep z₀ (FrE P) ffew

        ctf : Few (MapT proj₂ ScE) w
        ctf = map-few proj₂ ScE (few-tr scf)

        ef = enter-few (ev m (Sh ρ′ o ρ lanePart) (h₁ ∷ ρ)) (Q′ ⊕ [ ix 1 ]) se tt

        shf : Few (ShE P) w
        shf = e ∷ proj₁ ef , pick
          where
            pick : ∀ {k e′} → ShE P k e′ → k ≺ w → k ∈ (e ∷ proj₁ ef)
            pick {k} x lt with ≼-split {k} {e} (shb x lt)
            ... | inj₁ lt′ = there (proj₂ ef x lt′)
            ... | inj₂ eq = here eq

        inf : Few (Connecting.ConnT Q′ (ShE P) (enter (Ct lanePart h₁ h₂) (Bp P))) w
        inf = conn-few-src Q′ (ShE P) (enter (Ct lanePart h₁ h₂) (Bp P)) shf (few-tr ctf)

        emf : Few (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) w
        emf = [ (P ⊕ [ ix 1 ]) ⊕ [ last ] ] , λ { (at-end , _) _ → here refl }

        svf : Few (Connecting.ConnT P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (ev m (Sh ρ′ o ρ lanePart) (h₁ ∷ ρ)) (λ h′ → Ct lanePart h₁ h′)) Q′)) w
        svf = conn-few-src P (enter (Op.empty {⊤}) (P ⊕ [ ix 1 ])) (enter (Op.connect (ev m (Sh ρ′ o ρ lanePart) (h₁ ∷ ρ)) (λ h′ → Ct lanePart h₁ h′)) Q′) emf (few-tr inf)

        OS : EmissionSet _
        OS = enter (Op.of (lanePart ∷ burstPart ∷ [])) s

        ok : OS K (out lanePart)
        ok = at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {K} {out lanePart}

        osf : Few OS w
        osf = K ∷ (s ⊕ [ ix 1 ]) ∷ (s ⊕ [ last ]) ∷ [] , go
          where
            go : ∀ {k e′} → OS k e′ → k ≺ w → k ∈ (K ∷ (s ⊕ [ ix 1 ]) ∷ (s ⊕ [ last ]) ∷ [])
            go (at-out , _) _                  = here refl
            go (on-out at-out , _) _           = there (here refl)
            go (on-out (on-out at-end) , _) _  = there (there (here refl))

        bf = burst-few ρ′ o ρ m s w

        lf : Σ (List Pos) λ kl → ∀ {q a k e′} → OS q (out a) → LaneOf Sv q a k e′ → k ≺ w → k ∈ kl
        lf = proj₁ svf ++ proj₁ bf , go
          where
            go : ∀ {q a k e′} → OS q (out a) → LaneOf Sv q a k e′ → k ≺ w → k ∈ (proj₁ svf ++ proj₁ bf)
            go (at-out , _) (l , _) lt                  = ∈-++⁺ˡ (proj₂ svf (proj₁ l) lt)
            go (on-out at-out , _) (l , _) lt           = ∈-++⁺ʳ (proj₁ svf) (proj₂ bf l lt)
            go (on-out (on-out ()) , _) _ _

        mmf : Few (Merge.JoinT Sv OS) w
        mmf = join-few osf lf ([] , λ ())

        mm-row : ∀ b → Scan.Acc laneStep z₀ (FrE P) w (laneStep b ld) → enter MM s w (out (proj₂ (laneStep b ld)))
        mm-row b ac = few-row (Joining.lane ok tt (svrow , P≺w) (λ ()) tt) mmf
          where
            scrow : ScE w (out (laneStep b ld))
            scrow = few-row (Scan.sval ac) scf

            ctrow : enter (Ct lanePart h₁ h₂) (Bp P) w (out (proj₂ (laneStep b ld)))
            ctrow = few-row (map-out scrow) ctf

            svrow : enter (Sv lanePart) P w (out (proj₂ (laneStep b ld)))
            svrow = few-row (Connecting.body (few-row (Connecting.body ctrow) inf)) svf

  -- The lane part's share, as the elaboration builds it, is the core's.
  done-row : ∀ m s {H p} → InvAt H p (enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))
           → ∀ {e} → enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) e end
           → ¬ ¬ Σ Pos λ f′ → Σ (IE B) λ v
               → enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s f′ (out v)
               × T (not (undone v)) × instant f′ ≡ instant e
  done-row nothing  s I se = core-row nothing s I se
  done-row (just n) s I se = core-row (just n) s I se
