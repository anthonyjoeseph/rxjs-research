{-# OPTIONS --guardedness #-}

-- A ROW OF THE LANE PART'S FRAME IS THE LANE'S, read up through the
-- frame's scan, its map, both connects and the parts' merge (`Up`): a skip
-- as it is, a value as the scan tells it once it has folded the frame's
-- values before it, which `denotation.Laws.Fold` gives classically.  Each
-- layer has few rows before the row when the frame and the share do.
--
-- A row of the frame's connected piece but its end is the frame's
-- (`frame-mid`), with few frame rows before it, whether or not the share
-- ever ends.
module simultaneous.LaneUp where

open import Data.List using (List; []; _∷_; [_]; _++_)
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; hot; enter; out; skip; end; Proper; Work; at-out; on-out; at-end; _≺_; _≼_; Few;
  MapT; map-out; map-skip; LaneOf; module Op; module Joining; module Merge; module Scan; module Connecting)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans)
open import denotation.Laws.Fold using (fold)
open import denotation.Laws.Worlds.Leaves using (of-reach)
open import simultaneous.HeldComb using (ev)
open import simultaneous.SObs using (lone; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (laneStart)
open import simultaneous.LaneLayers using (few-row; few-tr; map-few; scan-few; join-few)
open import simultaneous.ConcatThree using (module Mid)
open import simultaneous.BurstFew using (conn-few-src; burst-few)
open import simultaneous.LaneStart using (module C; Sh; laneAt; z₀)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; laneStep; marked; piece; shareˢ; counted; framed; laneSrc)

module Lift {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  -- The lane part's first two pieces, read through the elaboration.
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

  module At (m : Maybe ℕ) where
    open C ρ′ o ρ m using (MM; Sv; Ct; Sc; Fr; H₁; H₂; Bp)

    ShE : Pos → EmissionSet (IE B)
    ShE P = enter (ev m (Sh ρ′ o ρ lanePart) (H₁ P ∷ ρ)) ((P ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

    FrE : Pos → EmissionSet (IE B)
    FrE P = enter (Fr lanePart (H₁ P) (H₂ P lanePart)) (Bp P)

    -- The frame's connected piece's subscription.
    zOf : Pos → Pos
    zOf P = (Bp P ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

    -- A ROW OF THE CONNECTED PIECE BUT ITS END IS THE FRAME'S, few frame
    -- rows before it: the share's rows read are proper, so every row of the
    -- read lies at or before its end.
    module FrameMid (P : Pos)
      (rp : ∀ {y e c} → enter (H₂ P lanePart) (zOf P) y e → enter (H₂ P lanePart) (zOf P) c end → y ≼ c)
      (rf : ∀ {y e} → enter (H₂ P lanePart) (zOf P) y e → Few (enter (H₂ P lanePart) (zOf P)) y) where

      h₁ = H₁ P
      h₂ = H₂ P lanePart

      module M = Mid (λ j → ev m (piece {B = B} lanePart j) (h₂ ∷ h₁ ∷ ρ)) (Bp P) (marked laneStart) (Proper (ShE P))
                     (p0→ m h₁ h₂) (p0← m h₁ h₂) (p1→ m h₁ h₂) (p1← m h₁ h₂) rp rf

      frame-mid : ∀ {y e} → enter h₂ (zOf P) y e → zOf P ≺ y → Work e → FrE P y e × Few (FrE P) y
      frame-mid r zy wk = M.row r zy wk , few-tr (M.few r)

    -- A FRAME ROW BEFORE WHICH THE FRAME AND THE SHARE HAVE FEW ROWS IS THE
    -- LANE'S.  The burst part's lane has few rows anywhere.
    module Up (s : Pos) {w : Pos} (ffew : Few (FrE (laneAt s)) w) (shf : Few (ShE (laneAt s)) w) (Bw : Bp (laneAt s) ≺ w) where

      P Q′ K : Pos
      P = laneAt s
      Q′ = P ⊕ [ ix 0 ]
      K = s ⊕ [ ix 0 ]

      h₁ = H₁ P
      h₂ = H₂ P lanePart

      P≺w : P ≺ w
      P≺w = ≺-trans {P} {Bp P} {w} (≺-trans {P} {Q′} {Bp P} (≺-ext P []) (≺-ext Q′ [])) Bw

      ScE = enter (Sc lanePart h₁ h₂) (Bp P)

      scf : Few (Scan.ScanT laneStep z₀ (FrE P)) w
      scf = scan-few laneStep z₀ (FrE P) ffew

      ctf : Few (MapT proj₂ ScE) w
      ctf = map-few proj₂ ScE (few-tr scf)

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

      -- The map's row, up through both connects and the merge.
      ct-up : ∀ {e} → enter (Ct lanePart h₁ h₂) (Bp P) w e → Work e → enter MM s w e
      ct-up r wk = few-row (Joining.lane ok tt (few-row (Connecting.body (few-row (Connecting.body r) inf)) svf , P≺w) (λ ()) wk) mmf

      -- A value, as the scan tells it,
      val-up : ∀ {a} → FrE P w (out a) → ¬ ¬ Σ (Routes × IE B) λ b → enter MM s w (out (proj₂ (laneStep b a)))
      val-up fr κ = fold laneStep z₀ (FrE P) ffew fr λ (b , ac) → κ (b , ct-up (few-row (map-out (few-row (Scan.sval ac) scf)) ctf) tt)

      -- and a skip as it is.
      skip-up : FrE P w skip → enter MM s w skip
      skip-up fr = ct-up (few-row (map-skip (few-row (Scan.sstep fr) scf)) ctf) tt

    -- A ROW OF THE CONNECTED PIECE, BUT ITS END, IS THE LANE'S: a skip as it
    -- is, a value as the scan tells it.
    module Core (s : Pos)
      (rp : ∀ {y e c} → enter (H₂ (laneAt s) lanePart) (zOf (laneAt s)) y e → enter (H₂ (laneAt s) lanePart) (zOf (laneAt s)) c end → y ≼ c)
      (rf : ∀ {y e} → enter (H₂ (laneAt s) lanePart) (zOf (laneAt s)) y e → Few (enter (H₂ (laneAt s) lanePart) (zOf (laneAt s))) y)
      {y e} (r : enter (H₂ (laneAt s) lanePart) (zOf (laneAt s)) y e) (zy : zOf (laneAt s) ≺ y) (wk : Work e)
      (sf : Few (ShE (laneAt s)) y) (bw : Bp (laneAt s) ≺ y) where

      F = FrameMid.frame-mid (laneAt s) rp rf r zy wk

      open Up s (proj₂ F) sf bw public using (val-up; skip-up)

      row : FrE (laneAt s) y e
      row = proj₁ F

  -- THE LANE AS THE ELABORATION BUILDS IT: its share at the lane `s`, the
  -- frame's read of it, and the parts' merge.
  ShL : Maybe ℕ → Pos → EmissionSet (IE B)
  ShL m s = enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ])

  BL zL : Pos → Pos
  BL s = (laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 0 ]
  zL s = (BL s ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

  RdL : Maybe ℕ → Pos → EmissionSet (IE B)
  RdL m s = enter (hot (Proper (ShL m s))) (zL s)

  MML : Maybe ℕ → Pos → EmissionSet (IE B)
  MML m s = enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s

  RP RF : Maybe ℕ → Pos → Set
  RP m s = ∀ {y e c} → RdL m s y e → RdL m s c end → y ≼ c
  RF m s = ∀ {y e} → RdL m s y e → Few (RdL m s) y

  up-skip : ∀ m s → RP m s → RF m s → ∀ {y} → RdL m s y skip → zL s ≺ y → Few (ShL m s) y → BL s ≺ y → MML m s y skip
  up-skip nothing  s rp rf r zy sf bw = At.Core.skip-up nothing s rp rf r zy tt sf bw (At.Core.row nothing s rp rf r zy tt sf bw)
  up-skip (just n) s rp rf r zy sf bw = At.Core.skip-up (just n) s rp rf r zy tt sf bw (At.Core.row (just n) s rp rf r zy tt sf bw)

  up-val : ∀ m s → RP m s → RF m s → ∀ {y v} → RdL m s y (out v) → zL s ≺ y → Few (ShL m s) y → BL s ≺ y
         → ¬ ¬ Σ (Routes × IE B) λ b → MML m s y (out (proj₂ (laneStep b v)))
  up-val nothing  s rp rf r zy sf bw = At.Core.val-up nothing s rp rf r zy tt sf bw (At.Core.row nothing s rp rf r zy tt sf bw)
  up-val (just n) s rp rf r zy sf bw = At.Core.val-up (just n) s rp rf r zy tt sf bw (At.Core.row (just n) s rp rf r zy tt sf bw)
