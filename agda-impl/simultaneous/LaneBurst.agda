{-# OPTIONS --guardedness #-}

-- A LANE'S `burstEnd` CLOSES ITS SUBSCRIBE BURST (`lane-burst`).  The
-- `burstEnd` is the burst part's one row, under the lane's second child:
-- the lane part's frame shows none, its pieces' marks being others and its
-- share holding none.  What the lane shows or ends with in its
-- subscription's instant comes of the lane part's connect, whose world
-- reaches under the subscription only below its first child, holding no
-- hot row there; or it is the `burstEnd` itself.  Every such row lies
-- before the second child, so by the `burstEnd`.
--
-- A skip or a pin is no such row: the burst part's own end, a skip in
-- the merge, lies past the `burstEnd` in the same instant.
module simultaneous.LaneBurst where

open import Data.Bool using (true; T; not)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; empty)
open import denotation.Position using (Pos; ix; sub; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Den; DenEnv; hot; enter; out; end; Proper; at-out; on-out; _≺_; _≼_; module Op; module TakeWhile)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds using (W; W⁼; here; inW; step; timer; join; Real; real-init; world-after; _⊑_; ⊑-snoc; ⊑-snoc⁺;
  ⊑-trans; ⊑-unit; Hots; GoodEnv; Ok; InvAt)
open import denotation.Read using (Visible)
open import simultaneous.HeldComb using (ev)
open import simultaneous.DenRows using (bounded-out; hot-out)
open import simultaneous.LaneEndSched using (of-one)
open import simultaneous.ElabUndone using (tell-back)
open import simultaneous.SObs using (lone; lanePart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; laneStart; burstEnd)
open import simultaneous.LaneLayers using (under-refl; under-trans; under-≺; under-⊕)
open import simultaneous.LaneSite using (module S; module Inv; under-≼)
open import simultaneous.LaneInnerEnd using (inner-ends)
import simultaneous.LaneStart as LaneStart
open LaneStart using (laneAt; Sh)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; laneˢ; laneSrc; undone; marked; piece)

------------------------------------------------------------------------
-- Under a subscription, its first child's world

-- WHAT A WORLD AT `s`'s FIRST CHILD'S SECOND REACHES UNDER `s` LIES UNDER
-- THAT FIRST CHILD, when no hot row lies under `s`: a step, a timer or a
-- join at `s` itself would lie before the world.
module FirstChild {H : Pos → Set} (s : Pos) (cold : ∀ {h} → H h → s ⊑ h → ⊥) where
  K P : Pos
  K = s ⊕ [ ix 0 ]
  P = K ⊕ [ ix 1 ]

  s≺P : s ≺ P
  s≺P = ≺-trans {s} {K} {P} (≺-ext s []) (≺-ext K [])

  not-s : ∀ {y} → W H P y → Real y → s ≡ y → ⊥
  not-s w r refl = ≺-absurd {s} {P} s≺P (world-after w r)

  mutual
    k-in⁼ : ∀ {y} → W⁼ H P y → Real y → s ⊑ y → K ⊑ y
    k-in⁼ here    _ _  = ⊑-snoc⁺ K
    k-in⁼ (inW w) r le = k-in w r le

    k-in : ∀ {y} → W H P y → Real y → s ⊑ y → K ⊑ y
    k-in (step {x} {l} v pl) r le with ⊑-snoc x le
    ... | inj₁ le′ = ⊑-trans (k-in⁼ v (real-init x [ l ] r) le′) (⊑-snoc⁺ x)
    ... | inj₂ eq  = ⊥-elim (not-s (step v pl) r eq)
    k-in (timer t v lt pl) r le = ⊥-elim (not-s (timer t v lt pl) r (⊑-unit _ le))
    k-in (join {h} (inj₁ hh) v eh) r le with ⊑-snoc h le
    ... | inj₁ le′ = ⊥-elim (cold hh le′)
    ... | inj₂ eq  = ⊥-elim (not-s (join (inj₁ hh) v eh) r eq)
    k-in (join {h} {e} (inj₂ u) v eh) r le with ⊑-snoc h le
    ... | inj₁ le′ = ⊑-trans (k-in u (real-init h [ sub e ] r) le′) (⊑-snoc⁺ h)
    ... | inj₂ eq  = ⊥-elim (not-s (join (inj₂ u) v eh) r eq)

------------------------------------------------------------------------
-- The lane, as the elaboration builds it

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) (g : GoodEnv ρ) where

  -- The lane part's third piece shows no `burstEnd`.
  pc2-be : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y n} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y (out (instEmit (mark burstEnd) n)) → ⊥
  pc2-be nothing  h h′ s (r , _) with of-one s _ r
  ... | _ , ()
  pc2-be (just _) h h′ s (r , _) with of-one s _ r
  ... | _ , ()

  -- The lane's inner ends only past a failing value.
  tend-no : ∀ m s {c} → enter (S.MM ρ′ o ρ g m) s c end → ¬ TakeWhile.Failed true undone (enter (S.MM ρ′ o ρ g m) s) c → ⊥
  tend-no nothing  s = inner-ends ρ′ o ρ nothing s
  tend-no (just n) s = inner-ends ρ′ o ρ (just n) s

  module Past (m : Maybe ℕ) (s : Pos) (oks : Ok (Hots ρ) s)
              (hb : ∀ {y n} → enter (ev m (Sh ρ′ o ρ lanePart) (S.H₁ ρ′ o ρ g m (laneAt s) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) y
                      (out (instEmit (mark burstEnd) n)) → ⊥)
              (cold : ∀ {h} → Hots ρ h → s ⊑ h → ⊥) where
    open S ρ′ o ρ g m using (Fr; LaneD; ct-read; module Frame; module FrB)
    open S.At ρ′ o ρ g m s using (K; Kb; P; Pb; FB; h₁; h₂; FrE; SvE; MME; mm-anat; burst-only)
    open FrB Pb using (Ib; u-P)
    open Inv ρ′ o ρ g m s oks using (ISv)
    open FirstChild {Hots ρ} s cold using (k-in; s≺P)

    -- The lane part's frame shows no `burstEnd`: its first piece's mark is
    -- its `laneStart`, its share holds none, its third piece's mark is its
    -- `laneDone`.
    fr-burst : ∀ {y n} → FrE y (out (instEmit (mark burstEnd) n)) → ⊥
    fr-burst {n = n} r with bounded-out 1 (Frame.f lanePart h₁ h₂ FB) (Op.of (0 ∷ 1 ∷ 2 ∷ [])) FB r
    ... | _ , _ , _ , _ , oq , _ , (l , _) = go oq l
      where
        ls≢ : instEmit (mark burstEnd) n ≡ marked laneStart → ⊥
        ls≢ ()

        go : ∀ {q j s′ y} → enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) FB q (out j) → enter (Frame.f lanePart h₁ h₂ FB j) s′ y (out (instEmit (mark burstEnd) n)) → ⊥
        go {s′ = s′} (at-out , _) l = ls≢ (LaneStart.pc0-ls ρ′ o ρ m h₁ h₂ s′ l)
        go {s′ = s′} (on-out at-out , _) l = hb (proj₁ (proj₁ (proj₂ (hot-out (LaneStart.pc1 ρ′ o ρ m lanePart h₁ h₂ s′ l)))))
        go {s′ = s′} (on-out (on-out at-out) , _) l = pc2-be m h₁ h₂ s′ l
        go (on-out (on-out (on-out ())) , _) _

    -- Nor does the lane part's connect, which shows what its frame did.
    sv-burst : ∀ {y n} → SvE y (out (instEmit (mark burstEnd) n)) → ⊥
    sv-burst {y} svr =
      let (st , a₀ , _ , fa , ea) = ct-read lanePart P svr
      in fr-burst (subst (λ a → FrE y (out a)) (tell-back (proj₁ st) a₀ ea tt) fa)

    -- So the lane's `burstEnd` is the burst part's.
    burst-at : ∀ {yb n} → enter LaneD s yb (out (instEmit (mark burstEnd) n)) → yb ≡ Ib
    burst-at (TakeWhile.pass mm _ _ , _) = [ (λ x → ⊥-elim (sv-burst (proj₁ x))) , (λ x → proj₁ (burst-only (proj₁ x))) ]′ (mm-anat mm)
    burst-at (TakeWhile.fail _ () _ _ , _)

    Kb≼Ib : Kb ≼ Ib
    Kb≼Ib = under-≼ (under-trans (under-⊕ (under-refl Kb) (ix 1)) (under-trans (under-⊕ (under-refl Pb) (ix 0)) u-P))

    past-K : ∀ {y} → K ⊑ y → y ≼ Ib
    past-K {y} k = ≺→≼ {y} {Ib} (≺-≼-≺ {y} {Kb} {Ib} (under-≺ s (s≤s z≤n) k) Kb≼Ib)

    sv-K : ∀ {y a} → SvE y (out a) → s ⊑ y → K ⊑ y
    sv-K r = k-in (InvAt.world ISv r) (InvAt.real ISv r)

    up : ∀ {q l} → P ≺ q → s ⊑ (q ⊕ [ l ]) → s ⊑ q
    up {q} {l} Pq le with ⊑-snoc q le
    ... | inj₁ le′ = le′
    ... | inj₂ eq  = ⊥-elim (≺-irrefl {s} (subst (s ≺_) (sym eq) (≺-trans {s} {q} {q ⊕ [ l ]} (≺-trans {s} {P} {q} s≺P Pq) (≺-ext q []))))

    be-undone : ∀ {a : IE B} → T (not (undone a)) → a ≡ marked burstEnd → ⊥
    be-undone nk refl = nk

    -- A failing value is the lane part's.
    fail-K : ∀ {q a l} → MME q (out a) → T (not (undone a)) → s ⊑ (q ⊕ [ l ]) → K ⊑ q
    fail-K mm nk le =
      [ (λ x → sv-K (proj₁ x) (up (proj₂ x) le)) , (λ x → ⊥-elim (be-undone nk (proj₂ (burst-only (proj₁ x))))) ]′ (mm-anat mm)

    row : ∀ {y e} → enter LaneD s y e → Visible e → s ⊑ y → y ≼ Ib
    row (TakeWhile.pass mm _ _ , _) _ le =
      [ (λ x → past-K (sv-K (proj₁ x) le)) , (λ x → subst (_≼ Ib) (sym (proj₁ (burst-only (proj₁ x)))) (≼-refl {Ib})) ]′ (mm-anat mm)
    row (TakeWhile.fail {q} mm nk _ _ , _) _ le = past-K (⊑-trans (fail-K mm nk le) (⊑-snoc⁺ q))
    row (TakeWhile.stop {q} mm nk _ , _) _ le = past-K (⊑-trans (fail-K mm nk le) (⊑-snoc⁺ q))
    row (TakeWhile.tend mm nF , _) _ _ = ⊥-elim (tend-no m s mm nF)
    row (TakeWhile.step _ _ , _) () _
    row (TakeWhile.left _ _ _ , _) () _

    burst-past-at : ∀ {y e yb n} → enter LaneD s y e → Visible e → s ⊑ y → enter LaneD s yb (out (instEmit (mark burstEnd) n)) → y ≼ yb
    burst-past-at {y} r v le rb = subst (y ≼_) (sym (burst-at rb)) (row r v le)

  -- A LANE'S `burstEnd` LIES BY EVERYTHING IT SHOWS OR ENDS WITH UNDER ITS
  -- SUBSCRIPTION, when its lane part's share shows no `burstEnd` and no hot
  -- row lies under the subscription.
  lane-burst : ∀ m s → Ok (Hots ρ) s
             → (∀ {y n} → enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) y
                  (out (instEmit (mark burstEnd) n)) → ⊥)
             → (∀ {h} → Hots ρ h → s ⊑ h → ⊥)
             → ∀ {y e yb n} → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s y e → Visible e → s ⊑ y
             → enter (ev m (laneˢ (laneSrc ρ′ o)) ρ) s yb (out (instEmit (mark burstEnd) n)) → y ≼ yb
  lane-burst nothing  s oks hb cold = Past.burst-past-at nothing  s oks hb cold
  lane-burst (just k) s oks hb cold = Past.burst-past-at (just k) s oks hb cold
