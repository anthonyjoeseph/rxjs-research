{-# OPTIONS --guardedness #-}

-- A LANE'S INNER ENDS ONLY PAST ITS `laneDone` (`inner-ends`).  The
-- inner's end waits on its lane part's connect; that connect's end is its
-- `counted` map's, which is its scan's, so its frame's; the frame's end
-- waits on its third piece, the `laneDone`.  Read back up, the scan folds
-- the frame's values up to that one, the map shows it told its lane's
-- routes, and every layer shows it before its own end.
module simultaneous.LaneInnerEnd where

open import Data.Bool using (not; T)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; [_])
import Data.List as L
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; s≤s; z≤n)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (Equivalence)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (¬_)

open import Tree using (Obs; mergeᶠ; of; flatMap)
open import denotation.Position using (Pos; ix; last; root; _≟ᵖ_; _⊕_)
open import denotation.Events using (Timeline; fresh; <ᵖ-part)
open import denotation.EmissionSet using (EmissionSet; Den; DenEnv; enter; out; end; at-out; on-out; _≺_; _≼_; Few; Ended; module Op;
  module Values; module Bounded; module Merge; module Scan; module TakeWhile;
  module Connecting; module Joining; map-out; map-end)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Fold using (fold)
open import simultaneous.HeldComb using (ev)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.CombSent using (reach-below)
open import simultaneous.SObs using (lone; Part; lanePart; burstPart; module Elaborate)
open import simultaneous.InstEmit using (laneDone)
open import simultaneous.LaneLayers using (starts-after)
open import simultaneous.LaneStart using (module C; z₀)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (IE; AIE; Routes; laneSrc; laneStep; undone; marked; piece; shareˢ; counted; framed)

------------------------------------------------------------------------
-- A joiner's end holds its every lane's

module _ {X Y : Set} (f : X → Den Y) (o : EmissionSet X) where
  private module Mg = Merge f o

  merge-done : ∀ {c} → Mg.JoinT c end → Mg.Done c
  merge-done (Mg.oend _ d)         = d
  merge-done (Mg.lane _ _ _ _ ())
  merge-done (Mg.lend _ _ _ _ _ d) = d
  merge-done (Mg.run () _)
  merge-done (Mg.rend () _ _)

module _ {X Y : Set} (n : ℕ) (f : X → Den Y) (o : EmissionSet X) where
  private module Bd = Bounded n f o

  bounded-done : ∀ {c} → Bd.JoinT c end → Bd.Done c
  bounded-done (Bd.oend _ d)         = d
  bounded-done (Bd.lane _ _ _ _ ())
  bounded-done (Bd.lend _ _ _ _ _ d) = d
  bounded-done (Bd.run () _)
  bounded-done (Bd.rend () _ _)

------------------------------------------------------------------------
-- A frame's third value

module Third (P : Pos) where
  O : EmissionSet ℕ
  O = enter (Op.of (0 ∷ 1 ∷ 2 ∷ [])) P

  ob₀ : O (P ⊕ [ ix 0 ]) (out 0)
  ob₀ = at-out , of-reach P 0 (0 ∷ 1 ∷ 2 ∷ []) {P ⊕ [ ix 0 ]} {out 0}

  ob₁ : O (P ⊕ [ ix 1 ]) (out 1)
  ob₁ = on-out at-out , of-reach P 0 (0 ∷ 1 ∷ 2 ∷ []) {P ⊕ [ ix 1 ]} {out 1}

  ob₂ : O (P ⊕ [ ix 2 ]) (out 2)
  ob₂ = on-out (on-out at-out) , of-reach P 0 (0 ∷ 1 ∷ 2 ∷ []) {P ⊕ [ ix 2 ]} {out 2}

  lt01 : (P ⊕ [ ix 0 ]) ≺ (P ⊕ [ ix 1 ])
  lt01 = ix-asc P (s≤s z≤n)

  lt12 : (P ⊕ [ ix 1 ]) ≺ (P ⊕ [ ix 2 ])
  lt12 = ix-asc P (s≤s (s≤s z≤n))

  lt02 : (P ⊕ [ ix 0 ]) ≺ (P ⊕ [ ix 2 ])
  lt02 = ix-asc P (s≤s z≤n)

  lo : ∀ {k b} → O k (out b) → (P ⊕ [ ix 0 ]) ≼ k
  lo (at-out , _)                         = ≼-refl {P ⊕ [ ix 0 ]}
  lo (on-out at-out , _)                  = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 1 ]} lt01
  lo (on-out (on-out at-out) , _)         = ≺→≼ {P ⊕ [ ix 0 ]} {P ⊕ [ ix 2 ]} lt02
  lo (on-out (on-out (on-out ())) , _)

  nx₁ : ∀ {k b} → O k (out b) → (P ⊕ [ ix 0 ]) ≺ k → (P ⊕ [ ix 1 ]) ≼ k
  nx₁ (at-out , _) lt                         = ⊥-elim (≺-irrefl {P ⊕ [ ix 0 ]} lt)
  nx₁ (on-out at-out , _) _                   = ≼-refl {P ⊕ [ ix 1 ]}
  nx₁ (on-out (on-out at-out) , _) _          = ≺→≼ {P ⊕ [ ix 1 ]} {P ⊕ [ ix 2 ]} lt12
  nx₁ (on-out (on-out (on-out ())) , _) _

  nx₂ : ∀ {k b} → O k (out b) → (P ⊕ [ ix 1 ]) ≺ k → (P ⊕ [ ix 2 ]) ≼ k
  nx₂ (at-out , _) lt                         = ⊥-elim (≺-absurd {P ⊕ [ ix 1 ]} {P ⊕ [ ix 0 ]} lt lt01)
  nx₂ (on-out at-out , _) lt                  = ⊥-elim (≺-irrefl {P ⊕ [ ix 1 ]} lt)
  nx₂ (on-out (on-out at-out) , _) _          = ≼-refl {P ⊕ [ ix 2 ]}
  nx₂ (on-out (on-out (on-out ())) , _) _

  nth₂ : Values.Nth O 2 (P ⊕ [ ix 2 ]) 2
  nth₂ = Values.next (Values.next (Values.first ob₀ lo) ob₁ lt01 nx₁) ob₂ lt12 nx₂

  -- The third value lies before the list's end.
  third-before : ∀ {c} → Ended O c → (P ⊕ [ ix 2 ]) ≺ c
  third-before {c} (c′ , (e , _) , c′c) with of-end P 0 (0 ∷ 1 ∷ 2 ∷ []) e
  ... | refl = ≺-≼-≺ {P ⊕ [ ix 2 ]} {P ⊕ [ last ]} {c} (Equivalence.from T-≡ (<ᵖ-part P [] [] refl)) c′c

-- A one-value list's value lies before its end, which is past it.
one-done : ∀ {X : Set} p (x : X) {c} → enter (Op.of (x ∷ [])) p c end → (p ⊕ [ ix 0 ]) ≺ c
one-done p x (e , _) with of-end p 0 (x ∷ []) e
... | refl = ix<last p

-- A two-value list's first value lies before its end.
first-before : ∀ {X : Set} {x y : X} p {c} → Ended (enter (Op.of (x ∷ y ∷ [])) p) c → (p ⊕ [ ix 0 ]) ≺ c
first-before {x = x} {y} p {c} (c′ , (e , _) , c′c) with of-end p 0 (x ∷ y ∷ []) e
... | refl = ≺-≼-≺ {p ⊕ [ ix 0 ]} {p ⊕ [ last ]} {c} (ix<last p) c′c

------------------------------------------------------------------------
-- The lane's inner

module _ {Θ B Γ′} (ρ′ : ∀ {X} → X ∈ L.map AIE Γ′ → X ∈ ⊤ ∷ Θ) (o : Obs Timeline Γ′ B) (ρ : DenEnv Θ) where

  ld : IE B
  ld = marked (laneDone 0)

  -- The lane part's third piece shows its `laneDone` before it ends.
  pc2-done : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y end
           → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out ld) × (s ⊕ [ ix 0 ]) ≺ y
  pc2-done nothing  h h′ s e = (at-out , of-reach s 0 (ld ∷ []) {s ⊕ [ ix 0 ]} {out ld}) , one-done s ld e
  pc2-done (just _) h h′ s e = (at-out , of-reach s 0 (ld ∷ []) {s ⊕ [ ix 0 ]} {out ld}) , one-done s ld e

  module _ (m : Maybe ℕ) where
    open C ρ′ o ρ m using (MM; Sv; Ct; Sc; Fr; H₁; H₂; Bp)

    -- THE COUNTED STREAM SHOWS ITS `laneDone` BEFORE IT ENDS: it ends
    -- where its scan does, so its frame has ended, so the frame's third
    -- piece; the scan folds the frame up to that piece's `laneDone`, and
    -- the map shows it, told its lane's routes.
    ct-ld : ∀ P {c₁} → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) c₁ end
          → ¬ ¬ Σ Pos λ R → Σ (IE B) λ a → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) R (out a) × T (not (undone a)) × R ≺ c₁ × Bp P ≺ R
    ct-ld P {c₁} (map-end (Scan.send (fj , rf) , r₂) , rct) = from-lane (proj₂ dfr T₃.ob₂ (2 , 2 , T₃.nth₂) (T₃.third-before (proj₁ dfr)) (λ ()))
      where
        h₁ : Den ⊤
        h₁ = H₁ P

        h₂ : Den (IE B)
        h₂ = H₂ P lanePart

        Q : Pos
        Q = Bp P

        fr : ℕ → Den (IE B)
        fr j = ev m (piece lanePart j) (h₂ ∷ h₁ ∷ ρ)

        module T₃ = Third Q
        module Bd = Bounded 1 fr T₃.O

        FrE : EmissionSet (IE B)
        FrE = enter (Fr lanePart h₁ h₂) Q

        ScE : EmissionSet (Routes × IE B)
        ScE = enter (Sc lanePart h₁ h₂) Q

        dfr : Bd.Done c₁
        dfr = bounded-done 1 fr T₃.O fj

        from-lane : Ended (Bd.Lane (Q ⊕ [ ix 2 ]) 2) c₁ → ¬ ¬ Σ Pos λ R → Σ (IE B) λ a → enter (Ct lanePart h₁ h₂) Q R (out a) × T (not (undone a)) × R ≺ c₁ × Q ≺ R
        from-lane (c₃ , (i , s′ , sb , (pe , _)) , c₃c₁) κ =
          fold laneStep z₀ FrE few-fr frow λ (b , ac) → to-ct b ac
          where
            w : Pos
            w = s′ ⊕ [ ix 0 ]

            pd : enter (fr 2) s′ w (out ld) × w ≺ c₃
            pd = pc2-done m h₁ h₂ s′ pe

            w≺c₁ : w ≺ c₁
            w≺c₁ = ≺-≼-≺ {w} {c₃} {c₁} (proj₂ pd) c₃c₁

            frow : FrE w (out ld)
            frow = Bd.lane T₃.ob₂ (2 , 2 , T₃.nth₂) (i , s′ , sb , proj₁ pd , ≺-ext s′ []) (λ ()) tt , reach-below {a = ld} rf w≺c₁

            few-fr : Few FrE w
            few-fr = proj₁ rf , λ {k} x lt → proj₂ rf (proj₁ x) (≺-trans {k} {w} {c₁} lt w≺c₁) tt

            Q≺w : Q ≺ w
            Q≺w = ≺-trans {Q} {s′} {w} (≺-trans {Q} {Q ⊕ [ ix 2 ]} {s′} (≺-ext Q []) (starts-after (proj₂ sb))) (≺-ext s′ [])

            to-ct : ∀ b → Scan.Acc laneStep z₀ FrE w (laneStep b ld) → ⊥
            to-ct b ac = κ (w , proj₂ y , ctrow , tt , w≺c₁ , Q≺w)
              where
                y : Routes × IE B
                y = laneStep b ld

                scrow : ScE w (out y)
                scrow = Scan.sval ac , reach-below {a = y} r₂ w≺c₁

                ctrow : enter (Ct lanePart h₁ h₂) Q w (out (proj₂ y))
                ctrow = map-out scrow , reach-below {a = proj₂ y} rct w≺c₁

    -- A LANE'S INNER NEVER ENDS BEFORE ITS `laneDone`.
    inner-end : ∀ s {c} → enter MM s c end → ¬ TakeWhile.Failed true undone (enter MM s) c → ⊥
    inner-end s {c} (x , rc) nF = from-sv (proj₂ dm ok tt K≺c (λ ()))
      where
        OS : EmissionSet Part
        OS = enter (Op.of (lanePart ∷ burstPart ∷ [])) s

        K P : Pos
        K = s ⊕ [ ix 0 ]
        P = K ⊕ [ ix 1 ]

        ok : OS K (out lanePart)
        ok = at-out , of-reach s 0 (lanePart ∷ burstPart ∷ []) {K} {out lanePart}

        dm : Merge.Done Sv OS c
        dm = merge-done Sv OS x

        K≺c : K ≺ c
        K≺c = first-before s (proj₁ dm)

        from-sv : Ended (λ k e → enter (Sv lanePart) P k e × P ≺ k) c → ⊥
        from-sv (c₁ , ((Connecting.body (Connecting.body cte , r₁) , r₀) , _) , c₁c) = ct-ld P cte λ (R , a , ctrow , na , R≺c₁ , Q≺R) → lift ctrow na R≺c₁ Q≺R
          where
            lift : ∀ {R a} → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) R (out a) → T (not (undone a)) → R ≺ c₁ → Bp P ≺ R → ⊥
            lift {R} {a} ctrow na R≺c₁ Q≺R = nF (R , a , mmrow , na , R≺c)
              where
                R≺c : R ≺ c
                R≺c = ≺-≼-≺ {R} {c₁} {c} R≺c₁ c₁c

                svrow : enter (Sv lanePart) P R (out a)
                svrow = Connecting.body (Connecting.body ctrow , reach-below {a = a} r₁ R≺c₁) , reach-below {a = a} r₀ R≺c₁

                P≺R : P ≺ R
                P≺R = ≺-trans {P} {Bp P} {R} (≺-trans {P} {P ⊕ [ ix 0 ]} {Bp P} (≺-ext P []) (≺-ext (P ⊕ [ ix 0 ]) [])) Q≺R

                mmrow : enter MM s R (out a)
                mmrow = Joining.lane ok tt (svrow , P≺R) (λ ()) tt , reach-below {a = a} rc R≺c

  -- The lane's inner, as the elaboration builds it, is the core's.
  inner-ends : ∀ m s {c} → enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s c end
             → ¬ TakeWhile.Failed true undone (enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s) c → ⊥
  inner-ends nothing  s e nF = inner-end nothing s e nF
  inner-ends (just n) s e nF = inner-end (just n) s e nF
