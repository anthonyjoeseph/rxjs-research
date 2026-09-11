-- ══════════════════════════════════════════════════════════════════
-- AND SPLITTING THE PACKED READING BACK APART IS NOT THE REPAIR:
-- THE FRAME HALF DIES AT THE ENTRY CAP TOO.  Its sibling kills the
-- packed pair on the LENGTH conjunct, by making the inner longer than
-- twice the cap.  That leaves one obvious escape -- keep the frame
-- conjunct at the entry cap, which is the half the leaves' pricing
-- actually spends, and find the length somewhere else.  This closes
-- it.  A subscribing frame pushes one frame per operator of the
-- INNER, and the frame it pushes carries that operator's TRANSFORMER
-- verbatim; what bounds the inner is the receipt in hand, taken at
-- the STEPPED cap.  So a single operator whose transformer is larger
-- than the entry cap and far under the stepped one registers a chain
-- that is short -- well inside twice the cap -- and still fails the
-- per-frame conjunct.  Length and syntax fail independently, and
-- neither is a bound the mint respects.
--
-- WHY THE CAPS-GENERIC FORM IS THE ONE STATED.  `capsAt`'s fields are
-- iterates of a count the tower seals, so no row can compute the live
-- statement's cap and no witness can contradict it directly.  What a
-- proof may read is what survives the seal: the caps package over an
-- arbitrary triple.  Refuting that closes the route however large the
-- sealed numerals turn out.
--
-- WHAT SEPARATES IT FROM ITS SIBLING, AND IT IS ONLY THE INNER.  The
-- state, the node, the chain and the triple are unchanged.  The
-- payload carries ONE operator rather than nine, and its transformer
-- has a syntax size of ten against an entry size of six -- so the
-- registered chain is seven frames where the sibling's is fifteen,
-- and seven is inside the doubled budget the sibling busts.  The two
-- witnesses therefore fail DIFFERENT conjuncts of the same pair.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Fan-Regs-Packed-Frame where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _≤_; s≤s; z≤n)
open import Data.Product using (proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; input; mapᵉ; varᵗ;
  pairᵗ; fstᵗ; nat̂; sizeᵗ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Path; root; _↠_;
  thru-outer; take-f; mergeAllᵒ; mergeAll-st; chainStep;
  sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; slotsCaps?)
open import Verify-Budget-Sufficient.Walk-Factor using (pathFrameSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  It is the mint's
-- own caps-generic form with the packed pair replaced by its FRAME
-- conjunct alone -- the split the sibling's refutation invites.
----------------------------------------------------------------------
FanRegsFrameMintGeneric : Set
FanRegsFrameMintGeneric = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Lv : ℕ) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep (suc Lv) c) sched st ≡ true →
  all (λ en → pathFrameSz? (Caps.cSize c) (proj₂ (proj₂ (proj₂ en))))
      (EvalSt.registry st) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE WITNESS.  The offending registry entry is MINTED by running one
-- `chainStep`; what is assembled by hand is only the node the run
-- subscribes against.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

-- the FAT transformer: three `fstᵗ`/`pairᵗ` wraps over a variable, so
-- its syntax size is ten against an entry cap of six and far under the
-- stepped cap the hypothesis is taken at
fatFn : Fn Γ₁ [] [] [] natᵗ natᵗ
fatFn = fstᵗ (pairᵗ (fstᵗ (pairᵗ (fstᵗ (pairᵗ (varᵗ (here refl)) (nat̂ 0)))
                                 (nat̂ 0)))
                    (nat̂ 0))

fatSz : ℕ
fatSz = sizeᵗ fatFn

fatSz≡ : fatSz ≡ 10
fatSz≡ = refl

-- ONE operator, so the chain the subscribe registers stays short
inner : Val Γ₁ (obs natᵗ)
inner = mapᵉ fatFn (input fzero)

a : Arrival Γ₁
a = record { tick = 0 ; ordinal = 0 ; source = 0
           ; elemTy = obs natᵗ ; payload = inner ; isLast = false }

chain : Path Γ₁ (obs natᵗ) natᵗ
chain = thru-outer mergeAllᵒ 0
      ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ root)))))

st₀ : EvalSt e₁
st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (st-init e₁)

after : EvalSt e₁
after = proj₂ (proj₂ (chainStep 0 a chain (sched-init e₁ sl₁) st₀))

schedAfter : Sched Γ₁
schedAfter = proj₁ (proj₂ (chainStep 0 a chain (sched-init e₁ sl₁) st₀))

-- THE ENTRY TRIPLE, the sibling's unchanged
c₀ : Caps
c₀ = caps 6 4 2

----------------------------------------------------------------------
-- THE FIGURES.  The length is the row that says this witness is NOT
-- the sibling's: seven frames against a doubled budget of twelve, so
-- the conjunct the sibling kills is satisfied here and the one that
-- fails is the syntax.
----------------------------------------------------------------------
regLens : List ℕ
regLens = map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry after)

regLens≡ : regLens ≡ 7 ∷ []
regLens≡ = refl

stepped : List ℕ
stepped = Caps.cSize (frameStep 1 c₀) ∷ Caps.cWid (frameStep 1 c₀)
        ∷ Caps.cReg (frameStep 1 c₀) ∷ []

stepped≡ : stepped ≡ 78 ∷ 7776 ∷ 14 ∷ []
stepped≡ = refl

----------------------------------------------------------------------
-- THE PREMISES, every one of them discharged at the witness.
----------------------------------------------------------------------
prem2≤ : 2 ≤ Caps.cSize c₀
prem2≤ = s≤s (s≤s z≤n)

prem1≤reg : 1 ≤ Caps.cReg c₀
prem1≤reg = s≤s z≤n

premReg≤ : Caps.cReg c₀ ≤ Caps.cSize c₀
premReg≤ = s≤s (s≤s z≤n)

premSlots : Sched.slots schedAfter ≡ sl₁
premSlots = refl

premSlotsCaps : slotsCaps? (Caps.cSize c₀) (Caps.cWid c₀) sl₁ ≡ true
premSlotsCaps = refl

premSlotsSz : slotsSize sl₁ ≤ Caps.cSize c₀
premSlotsSz = s≤s z≤n

-- THE HYPOTHESIS HOLDS AT THE STEPPED CAP, which is what makes the fat
-- transformer legal in the first place
premCaps : capsOK? (frameStep 1 c₀) schedAfter after ≡ true
premCaps = refl

-- AND THE FRAME CONJUNCT FAILS AT THE ENTRY CAP
row : Bool
row = all (λ en → pathFrameSz? (Caps.cSize c₀) (proj₂ (proj₂ (proj₂ en))))
          (EvalSt.registry after)

row≡false : row ≡ false
row≡false = refl

fan-regs-packed-frame-absurd : FanRegsFrameMintGeneric → ⊥
fan-regs-packed-frame-absurd pr =
  f≡t (trans (sym row≡false)
             (pr {e = e₁} c₀ 0 sl₁ schedAfter after
                 prem2≤ prem1≤reg premReg≤ premSlots premSlotsCaps
                 premSlotsSz premCaps))
