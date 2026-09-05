-- ══════════════════════════════════════════════════════════════════
-- THE SHARE REACHED AT TWO DEPTHS, WHICH THE DIAMOND DID NOT ASK.
--
-- TARGET: subscribeInner-sz @e1520e
--
-- WHAT THE DIAMOND LEFT OPEN.  An apex naming ONE slot twice reaches
-- the multicast from a single point of the walk, and the second
-- reference finds it already fired.  A LATTICE is the other shape:
-- two DIFFERENT slots each name a third, and the apex names those
-- two, so the share is reached through each arm's own definition
-- rather than beside the other reference -- and the two arms are
-- subscribed at different depths, which is a fact about the ORDER a
-- telescope is walked rather than about the reference count.
--
-- THE ROWS.  Five shared slots: a singleton, four duplication rungs
-- over it -- the share -- and two arms of four more rungs each, one of
-- them under three identity rungs so the two reach the share three
-- layers apart.  The apex merges bare references to both arms and is
-- entered as a bare reference itself, so the arrival's own layers are
-- nought and the whole charge is the telescope.
--
-- WHAT THEY FIND.  Depth buys the second arm nothing.  The share
-- connects on whichever arm the walk reaches first and has already
-- fired when the other registers, exactly as at one apex -- against a
-- control with the same rungs written INLINE in both arms, which
-- delivers twice.  So a sum charging the share once is not short here
-- either, and the conclusion holds at the smallest rungs the statement
-- admits while the telescope-free reading beside it fails.
--
-- WHAT THE ROWS DO NOT BUY.  Two arms over one share at one apex, all
-- five slots `shared`; nothing about a `scripted` slot in the lattice,
-- whose definition a subscription does not run; and nothing about an
-- arm that reaches the share TWICE itself, where the two shapes are
-- stacked rather than beside each other.
-- ══════════════════════════════════════════════════════════════════
module Probed.Slot-Two-Depths where

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
  installNode; st-init; sched-init; iterSize; subscribeInner)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeInner-sz)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE PROGRAM FAMILY.  `Pw k` is the balanced product of `2 ^ k`
-- naturals; `dupG` writes its payload into both arms, so a re-run
-- definition shows in the delivered size, and `idG` adds a layer
-- without adding a rung, which is what sets the two arms apart.
----------------------------------------------------------------------
Pw : ℕ → Ty
Pw zero    = natᵗ
Pw (suc k) = Pw k ×ᵗ Pw k

dupG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (Pw k) (Pw (suc k))
dupG = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

idG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (Pw k) (Pw k)
idG = varᵗ (here refl)

----------------------------------------------------------------------
-- THE LATTICE.  The share sits above the singleton; each arm names it
-- and adds the same four rungs; one arm carries three identity layers
-- above them, so the two arms meet the share three layers apart.
----------------------------------------------------------------------
Γᶻ : Ctx 5
Γᶻ = Pw 0 ∷ⱽ Pw 4 ∷ⱽ Pw 8 ∷ⱽ Pw 8 ∷ⱽ Pw 8 ∷ⱽ []ⱽ

shareZ : Closed Γᶻ (Pw 4)
shareZ = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (input fz))))

fourZ : Closed Γᶻ (Pw 8)
fourZ = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (input (fs fz)))))

armA : Closed Γᶻ (Pw 8)
armA = fourZ

armB : Closed Γᶻ (Pw 8)
armB = mapᵉ idG (mapᵉ idG (mapᵉ idG fourZ))

apexZ : Closed Γᶻ (Pw 8)
apexZ = mergeAllᵉ nothing
          (ofᵉ (strmᵗ (input (fs (fs fz)))
              ∷ strmᵗ (input (fs (fs (fs fz)))) ∷ []))

slᶻ : Slots Γᶻ
slᶻ fz                     = shared (ofᵉ (nat̂ 0 ∷ []))
slᶻ (fs fz)                = shared shareZ
slᶻ (fs (fs fz))           = shared armA
slᶻ (fs (fs (fs fz)))      = shared armB
slᶻ (fs (fs (fs (fs fz)))) = shared apexZ

eᶻ : Closed Γᶻ (Pw 8)
eᶻ = emptyᵉ

stᶻ : EvalSt eᶻ
stᶻ = installNode 0 (mergeAll-st {Γ = Γᶻ} {t = Pw 8} nothing 0 [] false)
        (st-init eᶻ)

-- the arrival is a bare reference to the apex, so its own layers are
-- nought and the whole charge is the telescope standing behind it
oᶻ : Val Γᶻ (obs (Pw 8))
oᶻ = input (fs (fs (fs (fs fz))))

outᶻ : List (Val Γᶻ (Pw 8))
outᶻ = proj₁ (proj₂ (subscribeInner {e = eᶻ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                       oᶻ (sched-init eᶻ slᶻ) stᶻ))

----------------------------------------------------------------------
-- THE CHARGE AND WHAT THE RUN DELIVERS.
----------------------------------------------------------------------

-- LOAD-BEARING: the first entry says the arrival contributes nothing,
-- so the whole charge is the telescope; the share's own size beside
-- the total is what a reading resolving it per ARM would add again.
latticeFigures : List ℕ
latticeFigures = layᵉ oᶻ ∷ slotSize (slᶻ (fs fz)) ∷ slotsSize slᶻ ∷ []

latticeFigures≡ : latticeFigures ≡ 0 ∷ 17 ∷ 67 ∷ []
latticeFigures≡ = refl

-- LOAD-BEARING, and this file's product: one value, of the size ONE
-- walk of the lattice delivers.  A share resolved at each arm's own
-- depth would show here as a second value.
latticeDelivered≡ : map (sizeᵛ {Γ = Γᶻ} (Pw 8)) outᶻ ≡ 511 ∷ []
latticeDelivered≡ = refl

latticeCount≡ : length outᶻ ≡ 1
latticeCount≡ = refl

-- THE CONTROL, and the row above says nothing without it: the same
-- lattice with the share written INLINE inside both arms rather than
-- named, so nothing is shared and both arms run to the end.
shareFree : Closed Γᶻ (Pw 4)
shareFree = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG
              (ofᵉ (nat̂ 0 ∷ [])))))

fourFree : Closed Γᶻ (Pw 8)
fourFree = mapᵉ dupG (mapᵉ dupG (mapᵉ dupG (mapᵉ dupG shareFree)))

apexFree : Val Γᶻ (obs (Pw 8))
apexFree = mergeAllᵉ nothing
             (ofᵉ (strmᵗ fourFree
                 ∷ strmᵗ (mapᵉ idG (mapᵉ idG (mapᵉ idG fourFree))) ∷ []))

outFree : List (Val Γᶻ (Pw 8))
outFree = proj₁ (proj₂ (subscribeInner {e = eᶻ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0
                          apexFree (sched-init eᶻ slᶻ) stᶻ))

-- LOAD-BEARING: it is what rules out the merge having entered one arm.
-- The same two arms unshared deliver twice, so the lattice's single
-- value is the multicast and not a door that stopped at the first.
latticeControl≡ : map (sizeᵛ {Γ = Γᶻ} (Pw 8)) outFree ≡ 511 ∷ 511 ∷ []
latticeControl≡ = refl

----------------------------------------------------------------------
-- THE CONCLUSION, at the smallest rungs the statement admits: two is
-- the least ladder and one bounds the arrival's syntax.
----------------------------------------------------------------------

-- LOAD-BEARING: the first row is the reading with no telescope at all,
-- which the whole charge here is, so a conclusion carried by anything
-- other than the summand would report `true` twice.
latticeRows : List Bool
latticeRows = valsSz? {Γ = Γᶻ} {s = Pw 8} (iterSize 2 (layᵉ oᶻ) 1) outᶻ
            ∷ valsSz? {Γ = Γᶻ} {s = Pw 8}
                (iterSize 2 (layᵉ oᶻ + slotsSize slᶻ) 1) outᶻ
            ∷ []

latticeRows≡ : latticeRows ≡ false ∷ true ∷ []
latticeRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: it is read at the same rungs the rows are, so a charge
-- a per-arm resolution outran would fail it exactly as the
-- telescope-free reading beside it does.
tieLattice : Confirms
  (subscribeInner-sz {e = eᶻ} (gasPad 64 g0) mergeAllᵒ 0 root 0 0 oᶻ
     (sched-init eᶻ slᶻ) stᶻ 2 1)
tieLattice = λ _ _ → refl
