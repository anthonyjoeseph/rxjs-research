-- ══════════════════════════════════════════════════════════════════
-- PACKING THE READING BUYS NOTHING AT THE MINT, AND THE LENGTH HALF
-- IS WHERE IT DIES AGAIN.  The flat entry-cap reading was refuted by a
-- registered chain of eight frames against an entry size of six, and
-- the packed reading was adopted because that witness satisfies it --
-- its length side asks only for twice the cap.  The doubling is not a
-- bound the operation respects: a subscribing frame pushes one frame
-- per operator of the INNER, and what bounds the inner is the caps
-- receipt in hand, which is taken at the STEPPED cap.  So the number
-- of frames pushed is bounded by the stepped size and not by the entry
-- one, and twice the entry cap is cleared by making the inner longer.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHY THE CAPS-GENERIC FORM IS THE ONE STATED.  The live statement
-- reads its cap off `capsAt`, whose fields are iterates of a count the
-- tower seals, so no row can compute either side and no witness can
-- contradict it directly.  What a proof may read is what survives the
-- seal: the caps package over an arbitrary triple.  The generic form
-- is therefore the strongest statement any caps-generic route may use,
-- and refuting it closes the route however large the sealed numerals
-- turn out.  Its premises are the ones a real cap carries, so the
-- statement refuted here is the weakest the walk's own doors ask for.
--
-- WHAT SEPARATES IT FROM ITS SIBLING, AND IT IS ONLY THE INNER.  The
-- witness state, the node, the chain and the triple are the sibling's
-- unchanged; the arrival's payload carries nine operators instead of
-- two.  That is the whole of the difference, which is what says the
-- doubling was a figure about one witness rather than about the
-- operation: the gap grows with the inner, and the inner is priced by
-- the receipt in hand.
--
-- WHAT IT COSTS UPSTREAM.  No multiple of the entry cap is a bound
-- here, so the repair is not a larger budget.  The reading has to be
-- taken at a cap the registered chain is actually under -- the level
-- the fan stands at -- or be paid in a currency that is not a cap.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Fan-Regs-Packed-Len where

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
open import Rx.Exp using (Ctx; Closed; Val; natᵗ; obs; input; mapᵉ; varᵗ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; Path; root; _↠_;
  thru-outer; take-f; mergeAllᵒ; mergeAll-st; chainStep;
  sched-init; st-init; installNode)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Caps using (Caps; caps; frameStep)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; slotsCaps?)
open import Verify-Budget-Sufficient.Walk-Factor using (pathSzL?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
FanRegsSzLMintGeneric : Set
FanRegsSzLMintGeneric = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Lv : ℕ) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep (suc Lv) c) sched st ≡ true →
  all (λ en → pathSzL? (Caps.cSize c) (proj₂ (proj₂ (proj₂ en))))
      (EvalSt.registry st) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE WITNESS.  The registry entry that busts twice the cap is MINTED
-- by running one `chainStep`, not written down; what is assembled by
-- hand is only the node the run subscribes against.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

-- the inner the outer frame consumes: NINE operators over a leaf, so
-- subscribing it pushes nine frames before it reaches the leaf that
-- registers -- and its whole syntax is well under the stepped cap the
-- hypothesis is taken at
inner : Val Γ₁ (obs natᵗ)
inner = mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl))
       (mapᵉ (varᵗ (here refl)) (input fzero)))))))))

a : Arrival Γ₁
a = record { tick = 0 ; ordinal = 0 ; source = 0
           ; elemTy = obs natᵗ ; payload = inner ; isLast = false }

-- a chain exactly as long as the entry cap admits
chain : Path Γ₁ (obs natᵗ) natᵗ
chain = thru-outer mergeAllᵒ 0
      ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ (take-f 0 ↠ root)))))

-- the node a `mergeAllᵉ` subscribe installs, with no lane taken
st₀ : EvalSt e₁
st₀ = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 [] false) (st-init e₁)

after : EvalSt e₁
after = proj₂ (proj₂ (chainStep 0 a chain (sched-init e₁ sl₁) st₀))

schedAfter : Sched Γ₁
schedAfter = proj₁ (proj₂ (chainStep 0 a chain (sched-init e₁ sl₁) st₀))

-- THE ENTRY TRIPLE, the sibling's unchanged.  Size six is the cap the
-- walked chain is priced by, so twice it is twelve.
c₀ : Caps
c₀ = caps 6 4 2

----------------------------------------------------------------------
-- THE FIGURES, spelled out so that a repair moving any of them fails
-- loudly and names the number rather than quietly closing the gap.
----------------------------------------------------------------------

-- what the run registers: the head swapped for a `from-inner` and the
-- inner's nine operators pushed on top of a chain already at the cap
regLens : List ℕ
regLens = map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry after)

regLens≡ : regLens ≡ 15 ∷ []
regLens≡ = refl

-- ONE level of the step, and the size cap is already thirteen times
-- the entry's -- so the inner that pushes those frames is legal under
-- the receipt in hand while the chain it builds clears twice the cap
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

-- THE HYPOTHESIS HOLDS AT THE STEPPED CAP -- this is the row the whole
-- refutation turns on, and the one a reader should re-run first
premCaps : capsOK? (frameStep 1 c₀) schedAfter after ≡ true
premCaps = refl

-- AND THE PACKED CONCLUSION FAILS AT THE ENTRY CAP, on its LENGTH half
row : Bool
row = all (λ en → pathSzL? (Caps.cSize c₀) (proj₂ (proj₂ (proj₂ en))))
          (EvalSt.registry after)

row≡false : row ≡ false
row≡false = refl

fan-regs-packed-len-absurd : FanRegsSzLMintGeneric → ⊥
fan-regs-packed-len-absurd pr =
  f≡t (trans (sym row≡false)
             (pr {e = e₁} c₀ 0 sl₁ schedAfter after
                 prem2≤ prem1≤reg premReg≤ premSlots premSlotsCaps
                 premSlotsSz premCaps))
