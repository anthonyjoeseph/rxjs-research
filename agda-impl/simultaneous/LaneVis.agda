{-# OPTIONS --guardedness #-}

-- A LANE'S VALUES, AHEAD OF ITS TAKE, ARE ITS LANE PART'S SHARE READ HOT
-- AT ITS FRAME'S SECOND PIECE, OR MARKS ONE STEP PAST A PIECE'S
-- SUBSCRIPTION THAT NO ROUTE CARRIES (`lane-vis`).  The frame's first piece
-- is a one-value `of`, ended below its value before the second arrives,
-- so the second starts at once below the second value; the burst part's
-- share shows nothing; every other piece is a one-value `of` of a mark.
-- The scan tells a lane's routes only into a `laneDone`, which the share
-- never shows: its blocker shows nothing and its program ends no lane.
module simultaneous.LaneVis where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using ([]; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Bool using (T; true; false)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Obs; mergeᶠ; empty; of; flatMap)
open import denotation.Position using (Pos; ix; sub; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (EmissionSet; DenEnv; hot; enter; out; Proper; _≺_; at-out; on-out; shown; heard; ended; late; module Op; module Bounded)
open import denotation.Laws.Modulus using (≺-absurd)
open import simultaneous.HeldComb using (ev)
open import simultaneous.Routed using (Carried)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (instEmit; mark; value; laneDone; begin; over; stop; outerOpen; outerClose; laneStart; burstEnd; outerDone;
  subscribed; completed)
open import simultaneous.DenRows using (merge-out; bounded-out; hot-out; each-one)
open import simultaneous.LaneEndSched using (of-one)
open import simultaneous.ElabUndone using (Undone; tell-back; tell-undone)
open import simultaneous.LaneLayers using (under-refl; under-⊕; under-≺)
open import simultaneous.SpinKit using (lastL; lastL-⊕)
open import simultaneous.ConcatTwo using (starts₀)
open import simultaneous.ConcatThree using (module Of3)
open import simultaneous.LaneStart using (module C; Sh; laneAt; pc0-at; pc0-ls; pc0-be; pc0-rows; pc1; pc2; sh-b)
open import simultaneous.LaneDoneRow using (p2→)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; elab; laneSrc; shareˢ; counted; framed; piece; count; tell; undone)

-- A mark that moves no route.
Silent : ∀ {B} → IE B → Set
Silent v = ∀ r → count r v ≡ r

-- A mark no route carries, moving none.
Quiet : ∀ {B} → IE B → Set
Quiet v = Silent v × (Carried (out v) → ⊥)

-- What a lane tells is as quiet as what it read.
tell-quiet : ∀ {B} r (a : IE B) → Quiet a → Quiet (tell r a)
tell-quiet r (instEmit (mark (laneDone _)) _) _ = (λ _ → refl) , λ ()
tell-quiet r (instEmit (value _) _)        h = h
tell-quiet r (instEmit (mark begin) _)      h = h
tell-quiet r (instEmit (mark over) _)       h = h
tell-quiet r (instEmit (mark stop) _)       h = h
tell-quiet r (instEmit (mark outerOpen) _)  h = h
tell-quiet r (instEmit (mark outerClose) _) h = h
tell-quiet r (instEmit (mark laneStart) _)  h = h
tell-quiet r (instEmit (mark burstEnd) _)   h = h
tell-quiet r (instEmit (mark outerDone) _)  h = h
tell-quiet r (instEmit (mark subscribed) _) h = h
tell-quiet r (instEmit (mark completed) _)  h = h

-- A hot's joined rows lie under the joiner's `sub`, or a `last` past it.
hot-lab : ∀ {A} {t : EmissionSet A} {z q e} → enter (hot t) z q e → lastL q ≡ ix 0 → ⊥
hot-lab {z = z} (shown {q} _ _ _ , _) ly with trans (sym (lastL-⊕ q (sub z))) ly
... | ()
hot-lab {z = z} (heard {q} _ _ , _) ly with trans (sym (lastL-⊕ q (sub z))) ly
... | ()
hot-lab {z = z} (ended {c} _ _ , _) ly with trans (sym (lastL-⊕ c (sub z))) ly
... | ()
hot-lab {z = z} (late _ _ , _) ly with trans (sym (lastL-⊕ z last)) ly
... | ()

-- Where a part's frame, its connect at `P`, subscribes its second piece.
zOf : Pos → Pos
zOf P = (((P ⊕ [ ix 0 ]) ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  -- The lane part's share shows what its program shows.
  sh-u : ∀ m → (∀ {t} → Undone (ev m (elab ρ′ o) (hot t ∷ ρ))) → ∀ {t p y a} → enter (ev m (Sh ρ′ o ρ lanePart) (hot t ∷ ρ)) p y (out a) → T (undone a)
  sh-u m pu {t} {p} r with bounded-out 1 (λ c → ev m (laneSrc ρ′ o lanePart c) (hot t ∷ ρ)) (Op.of (true ∷ false ∷ [])) p (sh-at m r)
    where
      sh-at : ∀ m {y a} → enter (ev m (Sh ρ′ o ρ lanePart) (hot t ∷ ρ)) p y (out a)
            → enter (Op.flatMap (mergeᶠ (just 1)) (λ c → ev m (laneSrc ρ′ o lanePart c) (hot t ∷ ρ)) (Op.of (true ∷ false ∷ []))) p y (out a)
      sh-at nothing  r = r
      sh-at (just _) r = r
  ... | _ , _ , _ , _ , (at-out , _) , _ , (l , _) = ⊥-elim (blk m l)
    where
      blk : ∀ m {s y a} → enter (ev m (laneSrc ρ′ o lanePart true) (hot t ∷ ρ)) s y (out a) → ⊥
      blk nothing  {s} l with each-one (λ _ → []) (hot t) s l
      ... | _ , _ , _ , ()
      blk (just _) {s} l with each-one (λ _ → []) (hot t) s l
      ... | _ , _ , _ , ()
  ... | _ , _ , _ , s , (on-out at-out , _) , _ , (l , _) = pu s l
  ... | _ , _ , _ , _ , (on-out (on-out ()) , _) , _ , _

  module _ (m : Maybe ℕ) (pu : ∀ {t} → Undone (ev m (elab ρ′ o) (hot t ∷ ρ))) where
    open C ρ′ o ρ m using (MM; Sv; Fr; H₁; H₂; Bp; ct-read)

    -- A FRAME'S VALUE: the lane part's second piece's reading of its share,
    -- or a mark one step past its piece's subscription.
    fr-vis : ∀ k P {y a} → enter (Fr k (H₁ P) (H₂ P k)) (Bp P) y (out a)
           → (k ≡ lanePart × enter (H₂ P lanePart) (zOf P) y (out a)) ⊎ (lastL y ≡ ix 0 × Quiet a)
    fr-vis k P r with bounded-out 1 (λ j → ev m (piece {B = B} k j) (H₂ P k ∷ H₁ P ∷ ρ)) (Op.of (0 ∷ 1 ∷ 2 ∷ [])) (Bp P) r
    ... | _ , _ , _ , _ , _ , (nth , st) , (l , _) = go k (O3.nth-c nth) st l
      where
        module O3 = Of3 (Bp P)
        module Bd (k′ : Part) = Bounded 1 (λ j → ev m (piece {B = B} k′ j) (H₂ P k′ ∷ H₁ P ∷ ρ)) O3.O

        step0 : ∀ s {y} → y ≡ s ⊕ [ ix 0 ] → lastL y ≡ ix 0
        step0 s eq = subst (λ w → lastL w ≡ ix 0) (sym eq) (lastL-⊕ s (ix 0))

        -- The first piece ends below the first value, before the second.
        end₀ : ∀ k′ {c} → Bd.Ends k′ 0 [] c → c ≺ O3.q₁
        end₀ k′ (_ , _ , s₀ , n , st₀ , (r₀ , _)) with O3.nth-c n
        ... | O3.n₀ with starts₀ st₀ | pc0-rows ρ′ o ρ m k′ (H₁ P) (H₂ P k′) s₀ r₀
        ...   | refl | inj₁ refl = under-≺ (Bp P) (s≤s z≤n) (under-⊕ (under-⊕ (under-refl O3.q₀) (ix 1)) (ix 0))
        ...   | refl | inj₂ refl = under-≺ (Bp P) (s≤s z≤n) (under-⊕ (under-⊕ (under-refl O3.q₀) (ix 1)) last)

        starts₁ : ∀ k′ {s} → Bd.Starts k′ 1 O3.q₁ (Bd.Sched k′ 1) s → s ≡ zOf P
        starts₁ k′ (Bounded.room (s≤s ()))
        starts₁ k′ (Bounded.freed _ _) = refl
        starts₁ k′ (Bounded.queued {c} _ qc (inj₁ (_ , ec , refl)) _ _) = ⊥-elim (≺-absurd {c} {O3.q₁} (end₀ k′ ec) qc)
        starts₁ k′ (Bounded.queued _ _ (inj₂ ()) _ _)

        go : ∀ k′ {i q j s y a} → O3.NthC i q j → Bd.Starts k′ i q (Bd.Sched k′ i) s → enter (ev m (piece {B = B} k′ j) (H₂ P k′ ∷ H₁ P ∷ ρ)) s y (out a)
           → (k′ ≡ lanePart × enter (H₂ P lanePart) (zOf P) y (out a)) ⊎ (lastL y ≡ ix 0 × Quiet a)
        go lanePart {s = s} O3.n₀ _ l =
          inj₂ (step0 s (proj₁ (pc0-at ρ′ o ρ m lanePart (H₁ P) (H₂ P lanePart) s l)) , subst Quiet (sym (pc0-ls ρ′ o ρ m (H₁ P) (H₂ P lanePart) s l)) ((λ _ → refl) , λ ()))
        go burstPart {s = s} O3.n₀ _ l =
          inj₂ (step0 s (proj₁ (pc0-at ρ′ o ρ m burstPart (H₁ P) (H₂ P burstPart) s l)) , subst Quiet (sym (pc0-be ρ′ o ρ m (H₁ P) (H₂ P burstPart) s l)) ((λ _ → refl) , λ ()))
        go lanePart {s = s} {y} {a} O3.n₁ st l =
          inj₁ (refl , subst (λ w → enter (H₂ P lanePart) w y (out a)) (starts₁ lanePart st) (pc1 ρ′ o ρ m lanePart (H₁ P) (H₂ P lanePart) s l))
        go burstPart {s = s} O3.n₁ _ l =
          ⊥-elim (sh-b ρ′ o ρ m (H₁ P) _ (proj₁ (proj₁ (proj₂ (hot-out (pc1 ρ′ o ρ m burstPart (H₁ P) (H₂ P burstPart) s l))))))
        go lanePart {s = s} O3.n₂ _ l =
          let (ey , ea) = of-one s _ (proj₁ (p2→ ρ′ o ρ m (H₁ P) (H₂ P lanePart) s l))
          in inj₂ (step0 s ey , subst Quiet (sym ea) ((λ _ → refl) , λ ()))
        go burstPart {s = s} O3.n₂ _ l = ⊥-elim (pc2 ρ′ o ρ m (H₁ P) (H₂ P burstPart) s l)

    -- A PART'S VALUE, told by its scan: its frame's, the share's left as
    -- it was read.
    part : ∀ k P {y v} → enter (Sv k) P y (out v) → (k ≡ lanePart × enter (H₂ P lanePart) (zOf P) y (out v)) ⊎ (lastL y ≡ ix 0 × Quiet v)
    part k P {y} {v} svr with ct-read k P svr
    ... | st , a₀ , _ , fa , ea with fr-vis k P fa
    ...   | inj₂ (ly , sa) = inj₂ (ly , subst Quiet ea (tell-quiet (proj₁ st) a₀ sa))
    ...   | inj₁ (ek , h) = inj₁ (ek , subst (λ b → enter (H₂ P lanePart) (zOf P) y (out b)) (tell-back (proj₁ st) a₀ ea ua) h)
      where
        ua : T (undone v)
        ua = subst (λ b → T (undone b)) ea (subst T (sym (tell-undone (proj₁ st) a₀)) (sh-u m pu (proj₁ (proj₁ (proj₂ (hot-out h))))))

    mm-vis : ∀ s {y v} → enter MM s y (out v) → enter (H₂ (laneAt s) lanePart) (zOf (laneAt s)) y (out v) ⊎ (lastL y ≡ ix 0 × Quiet v)
    mm-vis s r with merge-out Sv (Op.of (lanePart ∷ burstPart ∷ [])) s r
    ... | _ , _ , (at-out , _) , svr , _ = [ (λ (_ , h) → inj₁ h) , inj₂ ]′ (part lanePart (laneAt s) svr)
    ... | _ , _ , (on-out at-out , _) , svr , _ = [ (λ { (() , _) }) , inj₂ ]′ (part burstPart _ svr)
    ... | _ , _ , (on-out (on-out ()) , _) , _ , _

  -- THE ELABORATED LANE'S VALUES, AHEAD OF ITS TAKE.
  lane-vis : ∀ m → (∀ {t} → Undone (ev m (elab ρ′ o) (hot t ∷ ρ))) → ∀ s {y v}
           → enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s y (out v)
           → enter (hot (Proper (enter (ev m (Sh ρ′ o ρ lanePart) (hot (Proper (enter (ev m empty ρ) (laneAt s ⊕ [ ix 1 ]))) ∷ ρ)) ((laneAt s ⊕ [ ix 0 ]) ⊕ [ ix 1 ]))))
               (zOf (laneAt s)) y (out v)
             ⊎ (lastL y ≡ ix 0 × Quiet v)
  lane-vis nothing  pu s r = mm-vis nothing pu s r
  lane-vis (just n) pu s r = mm-vis (just n) pu s r
