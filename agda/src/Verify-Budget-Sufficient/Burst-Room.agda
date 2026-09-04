-- Verify-Budget-Sufficient.Burst-Room
-- bCeil-fold … inner-room
--
-- WHAT A DRAIN'S INNER SUBSCRIPTION COSTS, IN THE CURRENCY THE BURST
-- NUMBER IS STATED IN.  A `thru-outer` frame hands an arriving
-- observable to a fresh subscribe, and the width that descent reads is
-- the BURST ceiling of the arrival joined with the telescope's.  Both
-- halves are widths of SYNTAX, so the width lemma prices each by a
-- width fold at its own size, and a caps reading of the arrival caps
-- that size by the size at the frame's level -- which is where the
-- level shelf takes over.
--
-- THE ONE STEP THAT IS NOT MECHANICAL IS THE SEED.  The telescope
-- supplies its width leaf at ONE OVER the caps width, so every bound
-- here is a fold seeded at `suc W` while the burst number is
-- denominated at `W`.  A seed step is not a count step in general --
-- comparing the two directly is false, and the size iterate is the
-- wrong side to compare on -- but one fold step off the TOP dominates
-- a `suc` at the seed, so the whole reading moves down one seed at the
-- cost of one count.  The walk pays that count from its own path: a
-- frame arm stands one level below the length its reached premise is
-- stated at, so the level is read at `suc L` and the extra count fits
-- because the size at a level is strictly under the size at the next.
module Verify-Budget-Sufficient.Burst-Room where

open import Data.Nat using (ℕ; suc; _+_; _⊔_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (≤-trans; ≤-refl; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤n+m; n≤1+n)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; tabulate)
open import Data.Product using (proj₁)

open import Rx.Exp using
  (Ctx; Exp; Closed; sizeᵉ; sizeᵗ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
   mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slots; slotsSize; scripted; shared)
open import Rx.Burst-Ceil using (bCeilᵉ; bKidsᵉ; slotBCeil; slotsBCeilgo; slotsBCeil)
open import Rx.Evaluator using (iterFold; sizeAt)
open import Verify-Budget-Sufficient.Measures using (slotDef-size)
open import Verify-Budget-Sufficient.Caps using
  (Caps; capsAt; capsH; frameStep; iterFold-mono-count; iterFold-mono-base;
   iterSize-infl; 2≤capsAt-size; capsAt-base-size; sizeAt-strict)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (SlotWid; suc≤foldStep)
open import Verify-Budget-Sufficient.Caps-Face.Part2 using (wid-iterFold; slotsCaps?-slotWid)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (slotsCaps?-capsAt)
open import Verify-Budget-Sufficient.Nest-Ceiling using (Reached)
open import Verify-Budget-Sufficient.Fold-Room using (size-room)
open import Verify-Budget-Sufficient.Nest-Store using (nestBurstAt)

-- THE BURST CEILING IS A WIDTH FOLD AT THE NODE'S OWN SIZE.  It is the
-- joined ceiling's induction run over strictly fewer readings and
-- strictly fewer children, so the join at each node is the width
-- lemma's `outWᵉ` conjunct against one child, and every child's size is
-- under its parent's.
mutual
  bCeil-fold : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
    (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
    bCeilᵉ n sl e ≤ iterFold S (sizeᵉ e) M
  bCeil-fold S M hS hM sl hI e =
    ⊔-lub (proj₁ (wid-iterFold S M hS hM sl hI e))
          (bKids-fold S M hS hM sl hI e)

  bKids-fold : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
    (sl : Slots Γ) → SlotWid sl M → (e : Exp Γ Δᵍ Δ Θ t) →
    bKidsᵉ n sl e ≤ iterFold S (sizeᵉ e) M
  bKids-fold S M hS hM sl hI (input i)         = z≤n
  bKids-fold S M hS hM sl hI (ofᵉ ts)          = z≤n
  bKids-fold S M hS hM sl hI emptyᵉ            = z≤n
  bKids-fold S M hS hM sl hI (varᵉ x)          = z≤n
  bKids-fold S M hS hM sl hI (deferᵉ b)        = z≤n
  bKids-fold S M hS hM sl hI (mapᵉ f b)        =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS
               (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) (n≤1+n (sizeᵗ f + sizeᵉ b))))
  bKids-fold S M hS hM sl hI (takeᵉ c b)       =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS
               (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ c)) (n≤1+n (sizeᵗ c + sizeᵉ b))))
  bKids-fold S M hS hM sl hI (scanᵉ f z b)     =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS
               (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f + sizeᵗ z))
                        (n≤1+n (sizeᵗ f + sizeᵗ z + sizeᵉ b))))
  bKids-fold S M hS hM sl hI (mergeAllᵉ lim b) =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS (n≤1+n (sizeᵉ b)))
  bKids-fold S M hS hM sl hI (switchAllᵉ b)    =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS (n≤1+n (sizeᵉ b)))
  bKids-fold S M hS hM sl hI (exhaustAllᵉ b)   =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS (n≤1+n (sizeᵉ b)))
  bKids-fold S M hS hM sl hI (μᵉ b)            =
    ≤-trans (bCeil-fold S M hS hM sl hI b)
            (iterFold-mono-count S M hS (n≤1+n (sizeᵉ b)))

-- AND THE TELESCOPE'S IS ONE AT ITS OWN SIZE, slot by slot: a scripted
-- slot carries no syntax to descend into, and a shared one's def is
-- under the telescope's size by the very sum that defines it.
slotB-fold : ∀ {n} {Γ : Ctx n} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (i : Fin n) →
  slotBCeil n sl (sl i) ≤ iterFold S (slotsSize sl) M
slotB-fold S M hS hM sl hI i with sl i in eq
... | scripted _ = z≤n
... | shared d   =
  ≤-trans (bCeil-fold S M hS hM sl hI d)
          (iterFold-mono-count S M hS (slotDef-size sl i eq))

slotsBgo-fold : ∀ {n} {Γ : Ctx n} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M → (is : List (Fin n)) →
  slotsBCeilgo n sl is ≤ iterFold S (slotsSize sl) M
slotsBgo-fold S M hS hM sl hI []       = z≤n
slotsBgo-fold S M hS hM sl hI (i ∷ is) =
  ⊔-lub (slotB-fold S M hS hM sl hI i) (slotsBgo-fold S M hS hM sl hI is)

slotsBCeil-fold : ∀ {n} {Γ : Ctx n} (S M : ℕ) → 2 ≤ S → 1 ≤ M →
  (sl : Slots Γ) → SlotWid sl M →
  slotsBCeil n sl ≤ iterFold S (slotsSize sl) M
slotsBCeil-fold {n = n} S M hS hM sl hI =
  slotsBgo-fold S M hS hM sl hI (tabulate {n = n} (λ i → i))

-- THE ASSEMBLY: THE WIDTH A DRAIN'S INNER DESCENT READS IS UNDER THE
-- BURST NUMBER.  The seed the telescope supplies is one over the caps
-- width, and the trade for it is the count step described above -- so
-- the level is read at `suc L`, which is what a frame arm has, and the
-- size the arrival's own caps reading gives at `L` still fits with the
-- step to spare.
inner-room : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (id L P g : ℕ) (o : Closed Γ u) →
  Reached (capsAt e sl id) (capsH e sl id) P (suc g) →
  suc L ≤ P →
  sizeᵉ o ≤ Caps.cSize (frameStep L (capsAt e sl id)) →
  bCeilᵉ n sl o ⊔ slotsBCeil n sl ≤ nestBurstAt e sl id
inner-room {n = n} {e = e} sl id L P g o hR hLP hsz =
  ≤-trans
    (⊔-lub (≤-trans (bCeil-fold S M 2≤S 1≤M sl slW o)
                    (iterFold-mono-count S M 2≤S (m≤m⊔n (sizeᵉ o) (slotsSize sl))))
           (≤-trans (slotsBCeil-fold S M 2≤S 1≤M sl slW)
                    (iterFold-mono-count S M 2≤S (m≤n⊔m (sizeᵉ o) (slotsSize sl)))))
    (≤-trans (iterFold-mono-base k 2≤S ≤-refl (suc≤foldStep S W 2≤S))
             (size-room e sl id (suc L) P g (suc k) hR hLP
                (≤-trans (s≤s k≤sz) (sizeAt-strict S L 1≤S))))
  where
  c   = capsAt e sl id
  S   = Caps.cSize c
  W   = Caps.cWid c
  M   = suc W
  k   = sizeᵉ o ⊔ slotsSize sl
  2≤S : 2 ≤ S
  2≤S = 2≤capsAt-size e sl id
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  1≤M : 1 ≤ M
  1≤M = s≤s z≤n
  slW : SlotWid sl M
  slW = slotsCaps?-slotWid S W sl (slotsCaps?-capsAt e sl id)
  k≤sz : k ≤ sizeAt S L
  k≤sz = ⊔-lub hsz
           (≤-trans (≤-trans (m≤n+m (slotsSize sl) (2 + sizeᵉ e))
                             (capsAt-base-size e sl id))
                    (iterSize-infl S 1≤S L S))
