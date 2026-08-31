-- ══════════════════════════════════════════════════════════════════
-- IS THE DRAIN'S QUEUE LENGTH BOUNDED BY WHAT THE SIZE CAP IS BUILT
-- FROM?  The drain's fold spends one unit of the frame's ceiling per
-- queued entry, so the ceiling's measure names the queue's LENGTH --
-- and no conjunct of the caps record bounds it.  Before a field is
-- added, this reads the length against the two quantities the cap is
-- built out of, at a program whose queue grows while its syntax does
-- not.
--
-- CONFIDENCE RECEIPTS, not theorems: `refl` at concrete programs.  See
-- EVIDENCE.md for the tree's law and how a probe expires.
--
-- THE CAP ITSELF IS NOT READ, and that is deliberate rather than a
-- shortfall.  `capsAt` is a tower over the program and the slots, so
-- instantiating it is symbolic-or-nothing; what a field would have to
-- be stated against is its INPUTS, and those compute.  A length under
-- the slot vocabulary is a length under any cap built above it.
--
-- THE ADVERSARY IS A SCRIPT, because an `ofᵉ` source cannot break
-- this: its entries sit inside the program's own syntax, so a longer
-- queue is a bigger `sizeᵉ` by construction.  A scripted input is the
-- only source whose emission count is free of the program text -- the
-- same defect that refuted the entry fold's exponent, arriving at the
-- queue instead of at the burst.  So the program is fixed and the
-- SCRIPT grows: the queue length is read at three script lengths
-- against a syntax size that does not move.
--
-- WHAT WOULD MAKE IT FAIL.  `lenRow` is LOAD-BEARING at every entry:
-- a length outgrowing the slot vocabulary is a queue the cap cannot
-- bound, and then the field cannot be stated at the size cap at all.
-- `sizes≡` and `vocab≡` pin the two sides so a later reader can see
-- which one moved.
--
-- WHAT THE ROWS SAY.  The queue is one short of the script -- two,
-- five and eleven at scripts of three, six and twelve -- while the
-- program's syntax reads EIGHT throughout, so the length is genuinely
-- free of the program text and a bound naming only `sizeᵉ` is
-- refuted before it is written.  The vocabulary is two above the
-- script, so it dominates with a constant margin of three at every
-- length: the queue can be bounded at the slot vocabulary, and hence
-- at any cap built above it.
--
-- NOT COVERED: a source that parks without a script -- the margin
-- here is a fact about this family and not about queues; a limit
-- other than one; nested merges, where one drain's subscribe parks
-- into another's queue; and the cap itself, which is not read here
-- at all.
-- ══════════════════════════════════════════════════════════════════
module Probed.Drain-Queue-Length where

-- TARGET: walk-frame-drain-inner @46a5c3

open import Data.Bool using (Bool; true)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc; zero; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₂)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gasPad; cold)
open import Rx.Exp
  using (Closed; Fn; natᵗ; obs; ofᵉ; mapᵉ; mergeAllᵉ; input; nat̂; strmᵗ; sizeᵉ; deferᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; EvalSt; NodeState; lookupNode;
         mergeAll-st)
open import Refuted.Demand-Programs using (Γ₂)

script : ℕ → List ℕ
script zero    = []
script (suc k) = k ∷ script k

slots : ℕ → Slots Γ₂
slots k fzero        = scripted (cold [] [])
slots k (fsuc fzero) = scripted (cold (script k) [])

gas : Gas
gas = gasPad 400 g0

-- every scripted value becomes a one-element inner, so the source
-- emits one observable per script entry and the limit parks all but one
mkInner : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
mkInner = strmᵗ (deferᵉ (ofᵉ (nat̂ 0 ∷ [])))

prog : Closed Γ₂ natᵗ
prog = mergeAllᵉ (just 1) (mapᵉ mkInner (input (fsuc fzero)))

stᶠ : ℕ → EvalSt prog
stᶠ k = proj₂ (proj₂ (subscribeE gas prog root 0 0
                       (sched-init prog (slots k)) (st-init prog)))

qAt : Maybe (NodeState Γ₂) → ℕ
qAt (just (mergeAll-st {w} lim act q od)) = length q
qAt _ = 0

-- the queue is read off whichever node the run installed, since a
-- `mapᵉ` between the source and the merge moves the id
qlen : ℕ → ℕ
qlen k = go 0 4
  where
  st = stᶠ k
  go : ℕ → ℕ → ℕ
  go i zero    = 0
  go i (suc f) = qAt (lookupNode i (EvalSt.nodes st)) + go (suc i) f

sizes : ℕ
sizes = sizeᵉ prog + 1000 * qlen 3 + 100000 * qlen 6 + 10000000 * qlen 12

sizes≡ : sizes ≡ 110502008
sizes≡ = refl

vocab : ℕ
vocab = slotsSize (slots 3) + 1000 * slotsSize (slots 6)
      + 1000000 * slotsSize (slots 12)

vocab≡ : vocab ≡ 14008005
vocab≡ = refl

lenRow : List Bool
lenRow = (qlen 3  ≤ᵇ slotsSize (slots 3))
       ∷ (qlen 6  ≤ᵇ slotsSize (slots 6))
       ∷ (qlen 12 ≤ᵇ slotsSize (slots 12)) ∷ []

lenRow≡ : lenRow ≡ true ∷ true ∷ true ∷ []
lenRow≡ = refl
