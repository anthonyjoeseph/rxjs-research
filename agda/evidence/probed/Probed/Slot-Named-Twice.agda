-- ══════════════════════════════════════════════════════════════════
-- THE SLOT NAMED TWICE, WHICH DECIDES WHETHER THE SUMMAND IS SOUND
-- RATHER THAN MERELY GENEROUS.
--
-- TARGET: subscribeE-sz @c1fd3b
--
-- WHAT THE CHAINED TELESCOPE LEFT OPEN.  A chain runs each definition
-- once and its layers compound in series, which is what the sum buys
-- and a max does not.  A DIAMOND asks the other question: an apex
-- naming ONE lower slot twice is reached down two paths, and the sum
-- charges that slot once.  A binding whose definition were resolved at
-- each reference would run twice, and then the charge is short by
-- exactly the thing it declined to count.
--
-- THE ROWS.  Three shared slots -- a singleton, an eight-rung
-- duplication over it, and an apex merging two references to that one
-- rung -- entered at the apex as a bare reference, so the arrival's
-- own layers are zero and the whole charge is the telescope.
--
-- WHAT THEY FIND, AND IT IS STRONGER THAN THE SUMMAND NEEDED.  The
-- reference count reaches neither axis.  Not the SIZE: the one value
-- delivered is the size a single reference delivers, so the binding is
-- what is entered and not the definition.  And not the LENGTH either:
-- the share is connected by the first reference and has already fired
-- when the second registers, so the second receives nothing in this
-- instant.  A slot named twice costs a charge that counts it once
-- exactly nothing.
--
-- WHAT THE ROWS DO NOT BUY.  One diamond, over one shared slot, at one
-- door; nothing about an apex naming two DIFFERENT slots that share a
-- third, which `Probed.Slot-Two-Depths` reads; and nothing about a
-- `scripted` slot named twice, whose
-- definition a subscription does not run at all.
-- ══════════════════════════════════════════════════════════════════
module Probed.Slot-Named-Twice where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; map; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz; suc to fs)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; mergeAllᵉ; input; nat̂; varᵗ; pairᵗ; strmᵗ; sizeᵛ)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Slots using (Slots; shared; slotSize; slotsSize)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; mergeAll-st;
  from-inner; _↠_;
  installNode; st-init; sched-init; iterSize; subscribeInner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeE-sz)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `Pw k` is the balanced product of `2 ^ k`
-- naturals and `dupG` writes its payload into both arms, so a rung's
-- emission is twice what fed it and a re-run definition cannot hide.
----------------------------------------------------------------------
Pw : ℕ → Ty
Pw zero    = natᵗ
Pw (suc k) = Pw k ×ᵗ Pw k

dupG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (Pw k) (Pw (suc k))
dupG = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

----------------------------------------------------------------------
-- THE DIAMOND.  The middle slot is an eight-rung duplication over the
-- singleton below it; the apex merges TWO references to that one slot,
-- which is the whole shape under test.
----------------------------------------------------------------------
Γᴰ : Ctx 3
Γᴰ = Pw 0 ∷ⱽ Pw 8 ∷ⱽ Pw 8 ∷ⱽ []ⱽ

midD : Closed Γᴰ (Pw 8)
midD = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG
         (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (input fz))))))))

apexD : Closed Γᴰ (Pw 8)
apexD = mergeAllᵉ nothing
          (ofᵉ (strmᵗ (input (fs fz)) ∷ strmᵗ (input (fs fz)) ∷ []))

slᴰ : Slots Γᴰ
slᴰ fz           = shared (ofᵉ (nat̂ 0 ∷ []))
slᴰ (fs fz)      = shared midD
slᴰ (fs (fs fz)) = shared apexD

eᴰ : Closed Γᴰ (Pw 8)
eᴰ = emptyᵉ

stᴰ : EvalSt eᴰ
stᴰ = installNode 0 (mergeAll-st {Γ = Γᴰ} {t = Pw 8} nothing 0 [] false)
        (st-init eᴰ)

-- the arrival is a bare reference to the apex, so its own layers are
-- zero and the whole charge is the telescope standing behind it
oᴰ : Val Γᴰ (obs (Pw 8))
oᴰ = input (fs (fs fz))

outᴰ : List (Val Γᴰ (Pw 8))
outᴰ = proj₁ (proj₂ (subscribeInner {e = eᴰ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       oᴰ (sched-init eᴰ slᴰ) stᴰ))

----------------------------------------------------------------------
-- THE CHARGE AND WHAT THE RUN DELIVERS.
----------------------------------------------------------------------

-- LOAD-BEARING: the first entry says the arrival contributes nothing,
-- so the whole charge is the telescope; the middle slot's own size
-- beside the total is what a reading that charged it per reference
-- would have added again.
diamondFigures : List ℕ
diamondFigures = layᵉ oᴰ ∷ slotSize (slᴰ (fs fz)) ∷ slotsSize slᴰ ∷ []

diamondFigures≡ : diamondFigures ≡ 0 ∷ 33 ∷ 43 ∷ []
diamondFigures≡ = refl

-- LOAD-BEARING, and this file's product: one value, of the size a
-- SINGLE reference to that slot delivers.  A definition resolved at
-- each reference would show here as a value twice the size.
diamondDelivered≡ : map (sizeᵛ {Γ = Γᴰ} (Pw 8)) outᴰ ≡ 511 ∷ []
diamondDelivered≡ = refl

-- LOAD-BEARING, and the half the size row cannot say: the reference
-- count does not reach the LIST either.  The share is connected by the
-- first reference and has already fired when the second registers, so
-- the second receives nothing in this instant -- naming a slot twice
-- costs the charge nothing on either axis.
diamondCount≡ : length outᴰ ≡ 1
diamondCount≡ = refl

-- THE CONTROL, and the row above says nothing without it: the same
-- apex over the same eight rungs written INLINE at both arms rather
-- than named, so nothing is shared and both arms run.
midFree : Closed Γᴰ (Pw 8)
midFree = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG
            (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG
              (ofᵉ (nat̂ 0 ∷ [])))))))))

twinInline : Val Γᴰ (obs (Pw 8))
twinInline = mergeAllᵉ nothing
               (ofᵉ (strmᵗ midFree ∷ strmᵗ midFree ∷ []))

outC : List (Val Γᴰ (Pw 8))
outC = proj₁ (proj₂ (subscribeInner {e = eᴰ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       twinInline (sched-init eᴰ slᴰ) stᴰ))

-- LOAD-BEARING: it is what rules out the merge having entered one arm.
-- The same rungs twice, unshared, deliver twice -- so the diamond's
-- single value is the multicast and not a door that stopped at the
-- first observable.
controlDelivered≡ : map (sizeᵛ {Γ = Γᴰ} (Pw 8)) outC ≡ 511 ∷ 511 ∷ []
controlDelivered≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION, at the smallest rungs the statement admits: two is
-- the least ladder and one bounds the arrival's syntax.
----------------------------------------------------------------------

-- LOAD-BEARING: the first row is the reading with no telescope at all,
-- which the whole charge here is, so a conclusion carried by anything
-- other than the summand would report `true` twice.
diamondRows : List Bool
diamondRows = valsSz? {Γ = Γᴰ} {s = Pw 8} (iterSize 2 (layᵉ oᴰ) 1) outᴰ
            ∷ valsSz? {Γ = Γᴰ} {s = Pw 8}
                (iterSize 2 (layᵉ oᴰ + slotsSize slᴰ) 1) outᴰ
            ∷ []

diamondRows≡ : diamondRows ≡ false ∷ true ∷ []
diamondRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it is read at the same rungs the rows are, so a charge
-- a re-entered binding outran would fail it exactly as the
-- telescope-free reading beside it does.
tieDiamond : Confirms
  (subscribeE-sz {e = eᴰ} (gasPad 63 g0) oᴰ (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init eᴰ slᴰ) { nextNode = 1 }) stᴰ 2 1)
tieDiamond = λ _ _ → refl
