{-# OPTIONS --guardedness #-}

-- A LANE'S INNER ENDS ONLY PAST ITS `laneDone` (`inner-ends`).  The
-- inner's end waits on its lane part's connect; that connect's end is its
-- `counted` merge's, which waits on its scan, so on its frame; the frame's
-- end waits on its third piece, the `laneDone`.  Read back up, the scan
-- folds the frame's values up to that one, the split shows the `laneDone`,
-- and every layer shows it before its own end.
module simultaneous.LaneInnerEnd where

open import Data.Bool using (true; false; if_then_else_)
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
  module Connecting; module Joining)
open import denotation.Laws.Modulus using (≺-ext; ≺-trans; ≺-≼-≺; ≼-refl; ≺→≼; ≺-irrefl; ≺-absurd)
open import denotation.Laws.Worlds.Leaves using (of-reach; of-end)
open import denotation.Laws.Cut using (ix-asc)
open import denotation.Laws.Fold using (fold)
open import simultaneous.HeldComb using (ev)
open import simultaneous.TakeKit using (ix<last)
open import simultaneous.CombSent using (reach-below; module Two)
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
  ld = marked laneDone

  -- The lane part's third piece shows its `laneDone` before it ends.
  pc2-done : ∀ m (h : Den ⊤) (h′ : Den (IE B)) s {y} → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s y end
           → enter (ev m (piece {B = B} lanePart 2) (h′ ∷ h ∷ ρ)) s (s ⊕ [ ix 0 ]) (out ld) × (s ⊕ [ ix 0 ]) ≺ y
  pc2-done nothing  h h′ s e = (at-out , of-reach s 0 (ld ∷ []) {s ⊕ [ ix 0 ]} {out ld}) , one-done s ld e
  pc2-done (just _) h h′ s e = (at-out , of-reach s 0 (ld ∷ []) {s ⊕ [ ix 0 ]} {out ld}) , one-done s ld e

  module _ (m : Maybe ℕ) where
    open C ρ′ o ρ m using (MM; Sv; Ct; Sc; Fr; Inner; H₁; H₂; Bp)

    -- Below a frame's start, the split of its `laneDone` lies past the
    -- start, by a fixed path.
    up : ∀ (s′ : Pos) → s′ ≺ (((((s′ ⊕ [ ix 0 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 1 ]) ⊕ [ ix 0 ])
    up s′ = ≺-trans {s′} {w} {R} (≺-ext s′ [])
              (≺-trans {w} {U} {R} (≺-ext w [])
                (≺-trans {U} {U ⊕ [ ix 1 ]} {R} (≺-ext U [])
                  (≺-trans {U ⊕ [ ix 1 ]} {V} {R} (≺-ext (U ⊕ [ ix 1 ]) []) (≺-ext V []))))
      where
        w = s′ ⊕ [ ix 0 ]
        U = w ⊕ [ ix 1 ]
        V = (U ⊕ [ ix 1 ]) ⊕ [ ix 1 ]
        R = V ⊕ [ ix 0 ]

    -- THE COUNTED MERGE SHOWS ITS `laneDone` BEFORE IT ENDS: its scan has
    -- ended, so its frame, so the frame's third piece; the scan folds the
    -- frame up to that piece's `laneDone`, and its split shows it.
    ct-ld : ∀ P {c₁} → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) c₁ end
          → ¬ ¬ Σ Pos λ R → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) R (out ld) × R ≺ c₁ × Bp P ≺ R
    ct-ld P {c₁} (cj , rct) = from-sc (proj₁ dct)
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

        ScE : EmissionSet (Routes × (List (IE B) × List (IE B)))
        ScE = enter (Sc lanePart h₁ h₂) Q

        dct : Merge.Done Inner ScE c₁
        dct = merge-done Inner ScE cj

        from-sc : Ended ScE c₁ → ¬ ¬ Σ Pos λ R → enter (Ct lanePart h₁ h₂) Q R (out ld) × R ≺ c₁ × Q ≺ R
        from-sc (c₂ , (Scan.send (fj , rf) , r₂) , c₂c₁) = from-lane (proj₂ dfr T₃.ob₂ (2 , 2 , T₃.nth₂) (T₃.third-before (proj₁ dfr)) (λ ()))
          where
            dfr : Bd.Done c₂
            dfr = bounded-done 1 fr T₃.O fj

            from-lane : Ended (Bd.Lane (Q ⊕ [ ix 2 ]) 2) c₂ → ¬ ¬ Σ Pos λ R → enter (Ct lanePart h₁ h₂) Q R (out ld) × R ≺ c₁ × Q ≺ R
            from-lane (c₃ , (i , s′ , sb , (pe , _)) , c₃c₂) κ =
              fold laneStep z₀ FrE few-fr frow λ (b , ac) → to-ct b ac
              where
                w U V R : Pos
                w = s′ ⊕ [ ix 0 ]
                U = w ⊕ [ ix 1 ]
                V = (U ⊕ [ ix 1 ]) ⊕ [ ix 1 ]
                R = V ⊕ [ ix 0 ]

                pd : enter (fr 2) s′ w (out ld) × w ≺ c₃
                pd = pc2-done m h₁ h₂ s′ pe

                w≺c₂ : w ≺ c₂
                w≺c₂ = ≺-≼-≺ {w} {c₃} {c₂} (proj₂ pd) c₃c₂

                w≺c₁ : w ≺ c₁
                w≺c₁ = ≺-≼-≺ {w} {c₂} {c₁} w≺c₂ c₂c₁

                frow : FrE w (out ld)
                frow = Bd.lane T₃.ob₂ (2 , 2 , T₃.nth₂) (i , s′ , sb , proj₁ pd , ≺-ext s′ []) (λ ()) tt , reach-below {a = ld} rf w≺c₂

                few-fr : Few FrE w
                few-fr = proj₁ rf , λ {k} x lt → proj₂ rf (proj₁ x) (≺-trans {k} {w} {c₂} lt w≺c₂) tt

                Q≺s′ : Q ≺ s′
                Q≺s′ = ≺-trans {Q} {Q ⊕ [ ix 2 ]} {s′} (≺-ext Q []) (starts-after (proj₂ sb))

                U≺R : U ≺ R
                U≺R = ≺-trans {U} {U ⊕ [ ix 1 ]} {R} (≺-ext U []) (≺-trans {U ⊕ [ ix 1 ]} {V} {R} (≺-ext (U ⊕ [ ix 1 ]) []) (≺-ext V []))

                to-ct : ∀ b → Scan.Acc laneStep z₀ FrE w (laneStep b ld) → ⊥
                to-ct b ac = from-in (proj₂ dct scrow tt w≺c₁ (λ ()))
                  where
                    y : Routes × (List (IE B) × List (IE B))
                    y = laneStep b ld

                    scrow : ScE w (out y)
                    scrow = Scan.sval ac , reach-below {a = y} r₂ w≺c₂

                    from-in : Ended (λ k e → enter (Inner y) U k e × U ≺ k) c₁ → ⊥
                    from-in (c₄ , ((ij , ri) , _) , c₄c₁) = from-of (proj₂ dI (Two.snd-row true false U) tt (Two.snd-before true false U (proj₁ dI)) (λ ()))
                      where
                        dI : Merge.Done (λ c → Op.of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (enter (Op.of (true ∷ false ∷ [])) U) c₄
                        dI = merge-done (λ c → Op.of (if c then proj₁ (proj₂ y) else proj₂ (proj₂ y))) (enter (Op.of (true ∷ false ∷ [])) U) ij

                        from-of : Ended (λ k e → enter (Op.of (ld ∷ [])) V k e × V ≺ k) c₄ → ⊥
                        from-of (c₅ , (le , _) , c₅c₄) = κ (R , ctrow , R≺c₁ , ≺-trans {Q} {s′} {R} Q≺s′ (up s′))
                          where
                            R≺c₄ : R ≺ c₄
                            R≺c₄ = ≺-≼-≺ {R} {c₅} {c₄} (one-done V ld le) c₅c₄

                            R≺c₁ : R ≺ c₁
                            R≺c₁ = ≺-≼-≺ {R} {c₄} {c₁} R≺c₄ c₄c₁

                            irow : enter (Inner y) U R (out ld)
                            irow = Joining.lane (Two.snd-row true false U) tt ((at-out , of-reach V 0 (ld ∷ []) {R} {out ld}) , ≺-ext V []) (λ ()) tt
                                 , reach-below {a = ld} ri R≺c₄

                            ctrow : enter (Ct lanePart h₁ h₂) Q R (out ld)
                            ctrow = Joining.lane scrow tt (irow , U≺R) (λ ()) tt , reach-below {a = ld} rct R≺c₁

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
        from-sv (c₁ , ((Connecting.body (Connecting.body cte , r₁) , r₀) , _) , c₁c) = ct-ld P cte λ (R , ctrow , R≺c₁ , Q≺R) → lift ctrow R≺c₁ Q≺R
          where
            lift : ∀ {R} → enter (Ct lanePart (H₁ P) (H₂ P lanePart)) (Bp P) R (out ld) → R ≺ c₁ → Bp P ≺ R → ⊥
            lift {R} ctrow R≺c₁ Q≺R = nF (R , ld , mmrow , tt , R≺c)
              where
                R≺c : R ≺ c
                R≺c = ≺-≼-≺ {R} {c₁} {c} R≺c₁ c₁c

                svrow : enter (Sv lanePart) P R (out ld)
                svrow = Connecting.body (Connecting.body ctrow , reach-below {a = ld} r₁ R≺c₁) , reach-below {a = ld} r₀ R≺c₁

                P≺R : P ≺ R
                P≺R = ≺-trans {P} {Bp P} {R} (≺-trans {P} {P ⊕ [ ix 0 ]} {Bp P} (≺-ext P []) (≺-ext (P ⊕ [ ix 0 ]) [])) Q≺R

                mmrow : enter MM s R (out ld)
                mmrow = Joining.lane ok tt (svrow , P≺R) (λ ()) tt , reach-below {a = ld} rc R≺c

  -- The lane's inner, as the elaboration builds it, is the core's.
  inner-ends : ∀ m s {c} → enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s c end
             → ¬ TakeWhile.Failed true undone (enter (ev m (flatMap (mergeᶠ nothing) (λ k → shareˢ (laneSrc ρ′ o k) (counted (framed k))) (of (lanePart ∷ burstPart ∷ []))) ρ) s) c → ⊥
  inner-ends nothing  s e nF = inner-end nothing s e nF
  inner-ends (just n) s e nF = inner-end (just n) s e nF
