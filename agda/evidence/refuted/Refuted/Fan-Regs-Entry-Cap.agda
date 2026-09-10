-- ══════════════════════════════════════════════════════════════════
-- THE FAN'S REGISTRY READING CANNOT BE COLLAPSED TO THE ENTRY CAP,
-- AND ONE LEVEL IS ALREADY TOO MANY.  A caps receipt taken at a
-- STEPPED cap says nothing about the registry at the cap the instant
-- was entered on: `regsSz?` is upward-closed, so the receipt in hand
-- prices the registry at the LARGER number and the direction the
-- reading is wanted in is the one widening does not run.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHY THE CAPS-GENERIC FORM IS THE ONE STATED.  The live statement
-- reads both caps off `capsAt`, whose fields are iterates of a count
-- the tower seals -- `cDel` does not return at any program, so no row
-- can compute either side and no witness can contradict it directly.
-- What a PROOF may read is what survives the seal: the caps package
-- over an arbitrary triple.  So the generic form is not a convenience
-- weakening, it is the strongest statement any caps-generic route may
-- use, and refuting it closes the route however large the sealed
-- numerals turn out.
--
-- AND THE PREMISES ARE THE ONES A REAL CAP CARRIES, which is what
-- makes the refutation bite rather than merely typecheck.  The witness
-- triple satisfies every side-condition the walk's own doors take --
-- two under the size, a registration cap under it, the slot telescope
-- priced by the pair and its size under the cap -- so the statement
-- refuted here is the weakest one those doors could ask for.
--
-- WHERE IT BREAKS, AND IT IS THE SIBLING'S BREAK ONE FLOOR UP.
-- `Refuted.Chain-Step-Regs-Cap` shows one chain leaving the entry cap:
-- a subscribing frame does not register the path it walked but swaps
-- its head for a `from-inner` and pushes one frame per operator of the
-- inner, so the registered chain is LONGER than the walked one.  That
-- refutation kills the COLLAPSE at the chain door.  This one kills the
-- reading that would have recovered it afterwards -- the state it runs
-- on is that same reached state, and the level the fan is standing at
-- is exactly what pays for the extra frames.
--
-- WHAT IT COSTS UPSTREAM.  The fan's registry reading splits at the
-- level and discharges free at the instant's top, where the step is
-- the identity.  Above the top there is nothing to recover: the
-- residue is not a lemma waiting to be proven but a false reading, so
-- no premise threaded to the descent pays it, and the consumer must be
-- restated at the level it is standing at or be paid in a currency
-- that is not a cap.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Fan-Regs-Entry-Cap where

open import Data.Bool using (Bool; true; false)
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
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (regsSz?;
  capsOK?; slotsCaps?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.
----------------------------------------------------------------------
FanRegsMintGeneric : Set
FanRegsMintGeneric = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (c : Caps) (Lv : ℕ) (sl : Slots Γ) (sched : Sched Γ) (st : EvalSt e) →
  2 ≤ Caps.cSize c →
  1 ≤ Caps.cReg c →
  Caps.cReg c ≤ Caps.cSize c →
  Sched.slots sched ≡ sl →
  slotsCaps? (Caps.cSize c) (Caps.cWid c) sl ≡ true →
  slotsSize sl ≤ Caps.cSize c →
  capsOK? (frameStep (suc Lv) c) sched st ≡ true →
  regsSz? (Caps.cSize c) (EvalSt.registry st) ≡ true

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE WITNESS.  The registry entry that busts the cap is MINTED by
-- running one `chainStep`, not written down; what is assembled by hand
-- is only the node the run subscribes against, exactly as the sibling
-- refutation assembles it.  The ⊥ does not rest on reachability in any
-- case -- the statement quantifies over every state its premises
-- admit -- but the entry being minted is what says the gap is the
-- operation's and not the state's.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

e₁ : Closed Γ₁ natᵗ
e₁ = input fzero

-- the inner the outer frame consumes: two operators over a leaf, so
-- subscribing it pushes two frames before it reaches the leaf that
-- registers -- and its whole syntax is five nodes, under the cap
inner : Val Γ₁ (obs natᵗ)
inner = mapᵉ (varᵗ (here refl)) (mapᵉ (varᵗ (here refl)) (input fzero))

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

-- THE ENTRY TRIPLE.  Size six is the cap the walked chain is priced
-- by; the registration cap and the frame width are whatever a real
-- entry carries, and the premises below pin that they are legal.
c₀ : Caps
c₀ = caps 6 4 2

----------------------------------------------------------------------
-- THE FIGURES, spelled out so that a repair moving any of them fails
-- loudly and names the number rather than quietly closing the gap.
----------------------------------------------------------------------

-- what the run registers: the head swapped for a `from-inner` and the
-- inner's two operators pushed on top of a chain already at the cap
regLens : List ℕ
regLens = map (λ en → pathLen (proj₂ (proj₂ (proj₂ en)))) (EvalSt.registry after)

regLens≡ : regLens ≡ 8 ∷ []
regLens≡ = refl

-- ONE level of the step, and the size cap is already thirteen times
-- the entry's -- so the receipt in hand admits the registered chain
-- with room to spare while the conclusion's cap does not admit it
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

-- AND THE CONCLUSION FAILS AT THE ENTRY CAP
row : Bool
row = regsSz? (Caps.cSize c₀) (EvalSt.registry after)

row≡false : row ≡ false
row≡false = refl

fan-regs-entry-cap-absurd : FanRegsMintGeneric → ⊥
fan-regs-entry-cap-absurd pr =
  f≡t (trans (sym row≡false)
             (pr {e = e₁} c₀ 0 sl₁ schedAfter after
                 prem2≤ prem1≤reg premReg≤ premSlots premSlotsCaps
                 premSlotsSz premCaps))
