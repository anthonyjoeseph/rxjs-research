-- THE OUTER WRAP'S NEST BOUND, KILLED BY THE BURST ITS OWN SUBSCRIPTION
-- HANDS BACK.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- WHAT DIES.  `stepFrame-nodes-thru` charges a `thru-outer` frame two
-- to a SIZE cap times what it was handed, plus one unit per input
-- value.  A `thru-outer` subscribes each observable it takes, so the
-- values leaving it are a subscription's burst -- and a burst is not
-- one value.  A `scanᵉ` stored behind that subscription is refolded
-- once per value of the burst, so the delivered depth doubles per
-- value while both terms of the charge stand still: the size cap is
-- read off the handed value's syntax, and the unit is counted per
-- INPUT, of which there is one.
--
-- WHY THE BURST IS FREE ON BOTH SIDES, which is the whole mechanism and
-- the same one that killed the descent's own form.  The burst comes
-- from a COLD SCRIPT.  `sizeᵉ` cannot see a slot telescope and
-- `slotNest` reads zero at every scripted slot, so lengthening the
-- script moves neither the exponent nor the base -- while it doubles
-- what the frame delivers.
--
-- THE CROSSING IS EXACT, WHICH IS WHAT MAKES THIS A REFUTATION RATHER
-- THAN A SCALE ERROR.  At thirteen values the frame delivers 8191
-- against a charge of 8192 and the statement holds by one; at fourteen
-- it delivers 16383 against the same 8192.  Both rows are pinned, so
-- the reading is a crossing and not an accumulated slack.
--
-- THE PREMISES ARE PINNED AND THE CAP IS THE SMALLEST ADMISSIBLE.  The
-- size cap is the handed value's own -- `valCaps?` admits no smaller --
-- and a larger one would only make the charge astronomical, which is
-- the way this file would lie.  `W` is one, which is both what
-- `1 ≤ W` and `length vals ≤ W` admit at a single input and the
-- smallest the statement allows.
module Refuted.Thru-Scan-Burst-Nest where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Bool.ListAction using (all)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; _×ᵗ_; scanᵉ; mergeAllᵉ; emptyᵉ; input;
         varᵗ; fstᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; root; thru-outer; mergeAllᵒ; mergeAll-st;
         stepFrame; installNode; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂)

sync : ℕ → List ℕ
sync zero    = []
sync (suc k) = k ∷ sync k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (sync k) [])

deepen : Fn Γ₂ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing
           (scanᵉ (fstᵗ (varᵗ (there (here refl))))
                  (fstᵗ (varᵗ (here refl)))
                  (input (fsuc fzero))))

prog : Closed Γ₂ (obs natᵗ)
prog = scanᵉ deepen (strmᵗ emptyᵉ) (input (fsuc fzero))

gas : Gas
gas = gasPad 400 g0

e₀ : Closed Γ₂ (obs natᵗ)
e₀ = emptyᵉ

vals : List (Val Γ₂ (obs (obs natᵗ)))
vals = prog ∷ []

frame : Frame Γ₂ (obs (obs natᵗ)) (obs natᵗ)
frame = thru-outer mergeAllᵒ 0

st₀ : EvalSt e₀
st₀ = installNode 0 (mergeAll-st {t = obs natᵗ} nothing 0 [] false) (st-init e₀)

sched : ℕ → Sched Γ₂
sched k = sched-init e₀ (slots k)

-- the size cap is the handed value's own, which is the smallest
-- `valCaps?` admits; the width and registry caps are given room, which
-- only makes the premises easier and the refutation stronger
cap : Caps
cap = caps (sizeᵉ prog) 4000 4000

W : ℕ
W = 1

row : ℕ → ℕ × ℕ
row k =
  let r = stepFrame gas 0 0 frame root vals false (sched k) st₀
  in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)
   , 2 ^ Caps.cSize cap * ((nodesMax st₀ ⊔ nestDᵛˢ vals) + W)

premises : (all (valCaps? cap (slots 14) (obs (obs natᵗ))) vals ≡ true)
         × (capsOK? cap (sched 14) st₀ ≡ true)
premises = refl , refl

burst≡14 : length (proj₁ (stepFrame gas 0 0 frame root vals false (sched 14) st₀)) ≡ 14
burst≡14 = refl

delivered≡16383 : proj₁ (row 14) ≡ 16383
delivered≡16383 = refl

charged≡8192 : proj₂ (row 14) ≡ 8192
charged≡8192 = refl

-- ONE VALUE SHORTER AND THE STATEMENT HOLDS BY ONE, so this is a
-- crossing rather than a scale error
delivered₁₃≡8191 : proj₁ (row 13) ≡ 8191
delivered₁₃≡8191 = refl

charged₁₃≡8192 : proj₂ (row 13) ≡ 8192
charged₁₃≡8192 = refl

stepFrame-nodes-thru-burst-absurd : proj₁ (row 14) ≤ proj₂ (row 14) → ⊥
stepFrame-nodes-thru-burst-absurd h = ≤⇒≤ᵇ h
