-- ══════════════════════════════════════════════════════════════════
-- A FRAME'S OUTPUT COUNT IS NOT THE COUNT IT WAS HANDED PLUS A CHARGE.
-- It is that count TIMES the arriving width, and two crossing frames
-- already put the product past every additive reading of the cap.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE ROUTE SAID.  The walk's burst ledger asks, at every clause,
-- how MANY values a frame is handed, and nothing in the caps package a
-- chain carries says that -- the value premise prices payloads ONE AT
-- A TIME, on a size axis and a width axis.  So the missing fact is a
-- law about what a STEP OUTPUTS, stated where the step is; and since
-- every other ledger in this region charges a frame ADDITIVELY -- one
-- frame ceiling per frame of the path, summed -- the natural law is
-- additive too: the output count is the input count plus one cap's
-- worth.  That law would carry the ledger's fixed width down the path
-- unchanged, which is exactly what the ledger needs.
--
-- WHY IT CANNOT WORK.  A crossing frame subscribes each observable it
-- is handed and emits that subscription's whole synchronous burst, so
-- one frame's output is the SUM of its inputs' emission widths -- a
-- PRODUCT when the inputs are alike, not a sum.  The program here maps
-- every arrival of a scripted slot to a fresh observable over the same
-- slot, so a single value entering two crossing frames leaves the
-- second as the script's length SQUARED, while the cap's own entry
-- base moves only linearly in that length.
--
-- THE CROSSING IS EXACT, WHICH IS WHAT MAKES THIS A REFUTATION RATHER
-- THAN A SCALE ERROR.  At a script of five the second frame delivers
-- 25 against an additive allowance of 28 and the reading holds; at six
-- it delivers 36 against 31.  Both rows are pinned, so what is
-- exhibited is a crossing and not accumulated slack.
--
-- THE CAP IS GENEROUS, WHICH IS THE DIRECTION THAT COSTS THIS FILE
-- SOMETHING.  It is the entry recurrence's whole BASE -- two, the
-- program's own syntax, the slot telescope and its closure weight --
-- where the value premise would admit the handed value's size alone,
-- and its width and registry fields are given room outright.  A
-- smaller cap only makes the allowance smaller, so the refutation is
-- stated at the largest reading of the additive law that the entry
-- arithmetic offers.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Burst-Additive where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ; ≤ᵇ⇒≤)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Exp; Val; natᵗ; obs; mapᵉ; emptyᵉ; input; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Slot-Clos using (slotsClos)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; _↠_; thru-outer; mergeAllᵒ;
         mergeAll-st; stepFrame; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Refuted.Demand-Programs using (Γ₂)

-- a scripted slot of k arrivals; the second slot is the one both
-- levels of the program read
sync : ℕ → List ℕ
sync zero    = []
sync (suc k) = k ∷ sync k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (sync k) [])

gas : Gas
gas = gasPad 400 g0

e₀ : Closed Γ₂ (obs natᵗ)
e₀ = emptyᵉ

sched : ℕ → Sched Γ₂
sched k = sched-init e₀ (slots k)

-- every arrival becomes a fresh observable over the SAME slot, so a
-- subscription's burst is the script and a burst of bursts is the
-- script squared
innerProg : ∀ {Δᵍ Δ Θ} → Exp Γ₂ Δᵍ Δ Θ (obs natᵗ)
innerProg = mapᵉ (strmᵗ (input (fsuc fzero))) (input (fsuc fzero))

outerProg : Closed Γ₂ (obs (obs natᵗ))
outerProg = mapᵉ (strmᵗ innerProg) (input (fsuc fzero))

vals : List (Val Γ₂ (obs (obs (obs natᵗ))))
vals = outerProg ∷ []

frame₁ : Frame Γ₂ (obs (obs (obs natᵗ))) (obs (obs natᵗ))
frame₁ = thru-outer mergeAllᵒ 0

frame₂ : Frame Γ₂ (obs (obs natᵗ)) (obs natᵗ)
frame₂ = thru-outer mergeAllᵒ 1

path₁ : Path Γ₂ (obs (obs natᵗ)) (obs natᵗ)
path₁ = frame₂ ↠ root

st₀ : EvalSt e₀
st₀ = installNode 1 (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
        (installNode 0 (mergeAll-st {t = obs (obs natᵗ)} nothing 0 [] false)
          (st-init e₀))

step₁ : ℕ → _
step₁ k = stepFrame gas 0 0 frame₁ path₁ vals false (sched k) st₀

-- what the FIRST crossing hands the second, and the state it hands it in
mid : ℕ → List (Val Γ₂ (obs (obs natᵗ)))
mid k = proj₁ (step₁ k)

midSched : ℕ → Sched Γ₂
midSched k = proj₁ (proj₂ (proj₂ (proj₂ (step₁ k))))

midSt : ℕ → EvalSt e₀
midSt k = proj₂ (proj₂ (proj₂ (proj₂ (step₁ k))))

step₂ : ℕ → _
step₂ k = stepFrame gas 0 0 frame₂ root (mid k) false (midSched k) (midSt k)

-- the entry recurrence's own base, which is the cap this file grants
cap : ℕ → Caps
cap k = caps (2 + sizeᵉ outerProg + slotsSize (slots k) + slotsClos (slots k))
             4000 4000

-- the additive reading: what a frame outputs is what it was handed
-- plus one cap's worth
allowance : ℕ → ℕ
allowance k = length (mid k) + Caps.cSize (cap k)

premises : (Sched.slots (midSched 6) ≡ slots 6)
         × (capsOK? (cap 6) (midSched 6) (midSt 6) ≡ true)
         × (all (valCaps? (cap 6) (slots 6) (obs (obs natᵗ))) (mid 6) ≡ true)
         × ((slotsSize (slots 6) + length (mid 6)) ≤ Caps.cSize (cap 6))
premises = refl , refl , refl , ≤ᵇ⇒≤ _ _ tt

handed≡6 : length (mid 6) ≡ 6
handed≡6 = refl

delivered≡36 : length (proj₁ (step₂ 6)) ≡ 36
delivered≡36 = refl

allowed≡31 : allowance 6 ≡ 31
allowed≡31 = refl

-- ONE ARRIVAL SHORTER AND THE ADDITIVE READING HOLDS, so this is a
-- crossing rather than a scale error
delivered₅≡25 : length (proj₁ (step₂ 5)) ≡ 25
delivered₅≡25 = refl

allowed₅≡28 : allowance 5 ≡ 28
allowed₅≡28 = refl

frame-out-additive-absurd :
  length (proj₁ (step₂ 6)) ≤ allowance 6 → ⊥
frame-out-additive-absurd h = ≤⇒≤ᵇ h
