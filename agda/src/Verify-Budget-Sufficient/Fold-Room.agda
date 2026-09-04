-- Verify-Budget-Sufficient.Fold-Room
-- widAt<fLvlD … reached-len
--
-- THE WIDTH A WALK MEETS IS UNDER THE BURST NUMBER, and it is a shelf
-- of level arithmetic rather than a face.  A walk under `WalkHyps`
-- stands at a level `L` at or below a REACHED level `P`, and a reached
-- level's room is the delivery ladder from it over the deliveries the
-- gas still owes, under the count joined with the size.  One delivery
-- from `L` is under that ladder -- there is at least one delivery
-- while the gas is positive, and a delivery from a lower level is
-- under one from a higher -- and one delivery from `L` begins with a
-- frame charge that carries the width AT `L`, strictly.  So the width
-- at every level the walk stands at is under the count joined with the
-- size, and that top is under the next instant's size by the count
-- being under its own size iterate, which is what `nestBurstAt` names.
-- It sits in its own module because nothing here is in a mutual block
-- with the walk that spends it.
module Verify-Budget-Sufficient.Fold-Room where

open import Data.Nat using (ℕ; suc; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (≤-trans; ≤-reflexive; ≤-refl; m≤n+m; n≤1+n; m≤m*n; ⊔-lub)
open import Relation.Binary.PropositionalEquality using (sym)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (iterFold; dLvl; dCapᶜ; sizeAt; widAt; fLvlD; fCharge)
open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt; capsH; sizeCount; fLvl≤fLvlD; iterL-infl; lvls-mono; dLvl-mono; 1≤dCapᶜ;
   iterSize-infl; 2≤capsAt-size; 1≤capsAt-reg)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (k≤iterSize)
open import Verify-Budget-Sufficient.Nest-Ceiling using (Reached; reached-room)
open import Verify-Budget-Sufficient.Nest-Store using (nestBurstAt; nestBurstAt-def)

-- A FRAME CHARGE CARRIES THE WIDTH AT ITS OWN LEVEL, STRICTLY: the
-- charge is a `suc` of a product whose first factor is one over that
-- width, and the frame level at any depth fuel is over the charge.
widAt<fLvlD : ∀ (S W d J : ℕ) → suc (widAt S W J) ≤ fLvlD S W d J
widAt<fLvlD S W d J =
  ≤-trans (≤-trans (n≤1+n (suc (widAt S W J)))
                   (s≤s (m≤m*n (suc (widAt S W J)) (suc (sizeAt S J)))))
          (≤-trans (m≤n+m (fCharge S W J) J) (fLvl≤fLvlD S W d J))

-- and a DELIVERY from a level begins with that frame, so it is over
-- the width at the level it is entered at
wid<dLvl : ∀ (S W d L : ℕ) → suc (widAt S W L) ≤ dLvl S W d L
wid<dLvl S W d L =
  ≤-trans (widAt<fLvlD S W d L) (iterL-infl S W d (sizeAt S L) (fLvlD S W d L))

-- ONE DELIVERY FROM A LEVEL AT OR BELOW A REACHED ONE IS UNDER THE
-- TOP.  The reached level's room is the ladder from it over the
-- deliveries still owed; the gas is positive so at least one is, and
-- a delivery from lower is under a delivery from higher.
dLvl≤room : ∀ (c : Caps) (d L P g : ℕ) → 2 ≤ Caps.cSize c → 1 ≤ Caps.cReg c →
  Reached c d P (suc g) → L ≤ P →
  dLvl (Caps.cSize c) (Caps.cWid c) d L ≤ sizeCount c d ⊔ Caps.cSize c
dLvl≤room c d L P g 2≤S 1≤R hR L≤P =
  ≤-trans (dLvl-mono {d = d} 2≤S ≤-refl ≤-refl L≤P)
          (≤-trans (lvls-mono {d = d} 1 (dCapᶜ S W R d (suc g) P) 2≤S ≤-refl ≤-refl ≤-refl
                              (1≤dCapᶜ S W R d g P 1≤R))
                   (reached-room c d P (suc g) 2≤S hR))
  where
  S = Caps.cSize c
  W = Caps.cWid c
  R = Caps.cReg c

-- AND THE TOP IS UNDER THE NEXT INSTANT'S SIZE, which is the burst
-- number: that size is the size iterate at the count, over both the
-- count and the size it iterates from.
room≤nestBurstAt : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id : ℕ) →
  sizeCount (capsAt e sl id) (capsH e sl id) ⊔ Caps.cSize (capsAt e sl id)
    ≤ nestBurstAt e sl id
room≤nestBurstAt e sl id =
  ≤-trans (⊔-lub (k≤iterSize S (sizeCount c d) S 1≤S 1≤S)
                 (iterSize-infl S 1≤S (sizeCount c d) S))
          (≤-reflexive (sym (nestBurstAt-def e sl id)))
  where
  c = capsAt e sl id
  d = capsH e sl id
  S = Caps.cSize c
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) (2≤capsAt-size e sl id)

-- THE WIDTH AT ANY LEVEL A WALK STANDS AT, ONE ABOVE, UNDER THE BURST
-- NUMBER -- the length conjunct of the burst walk in one line, since
-- `valsCaps?` prices a handoff by exactly that width.
reached-len : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (sl : Slots Γ) (id L P g : ℕ) →
  Reached (capsAt e sl id) (capsH e sl id) P (suc g) → L ≤ P →
  suc (iterFold (Caps.cSize (capsAt e sl id)) L (Caps.cWid (capsAt e sl id)))
    ≤ nestBurstAt e sl id
reached-len e sl id L P g hR L≤P =
  ≤-trans (wid<dLvl (Caps.cSize c) (Caps.cWid c) (capsH e sl id) L)
          (≤-trans (dLvl≤room c (capsH e sl id) L P g
                      (2≤capsAt-size e sl id) (1≤capsAt-reg e sl id) hR L≤P)
                   (room≤nestBurstAt e sl id))
  where
  c = capsAt e sl id
