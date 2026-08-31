-- ══════════════════════════════════════════════════════════════════
-- DOES THE PARENT FRAME'S REMAINING LADDER DOMINATE A QUEUED TERM'S,
-- WITH THE LEVEL CLIMBING ENTRY BY ENTRY?  The one inequality the
-- delivery-side account of a queued term rests on, instantiated at a
-- program that really queues before anything is restated.
--
-- CONFIDENCE RECEIPTS, not theorems: `refl` at concrete programs.  See
-- EVIDENCE.md for the tree's law and how a probe expires.
--
-- THE LADDER ITSELF CANNOT BE INSTANTIATED, so what is read here is
-- its INPUTS.  A comparison of two `opIterD` readings is
-- symbolic-or-nothing -- that family's own header records the dead
-- route, and the blowup is computational rather than definitional, so
-- unsealing buys nothing.  What the ladder is monotone in is proven,
-- and one unit of the operator measure is proven to pay for one level.
-- So what is read here is each queued entry's closure measure against
-- the parent's, and each entry's operator measure PLUS ITS OWN
-- POSITION against the parent's -- both computable, and the position
-- is what a length-one queue cannot show.
--
-- THE POSITION IS CHARGED, NOT MEASURED, AND THAT IS THE BOUNDARY.
-- One level per entry is what the one-child step spends; what the
-- drain actually climbs is the level the subscribe's own caps lemma
-- chooses, bounded in the sweep currency rather than in operator
-- units.  No row here reaches that, so these rows are evidence that
-- the queue does not exhaust the measure -- not that the climb fits.
--
-- THE PROGRAM QUEUES FOR REAL.  A `mergeAll` at limit one over three
-- deferred inners: one is subscribed, the others are parked, so the
-- queue the drain reads has LENGTH TWO.  It is read off the node the
-- run installed rather than written down, so the entries are the ones
-- the evaluator actually parked.
--
-- WHAT THE ROWS SAY.  `qlen≡` is the non-vacuity witness -- two and
-- four, so neither fold below runs over an empty list.  `measures≡`
-- pins the numbers so a later reader can see WHICH side any future
-- failure moved, and `dom≡` and `dom5≡` are the comparisons.  The
-- later entries are the LOAD-BEARING ones: each is charged one
-- position more than the last, so a fold that does not pay for the
-- positions fails at the tail and not at the head.
-- ══════════════════════════════════════════════════════════════════
module Probed.Drain-Queue-Ladder where

-- TARGET: walk-frame-drain-inner @46a5c3

open import Data.Bool using (Bool; true; _∧_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; natᵗ; obs; _≟ᵗ_; ofᵉ; switchAllᵉ; mergeAllᵉ; nat̂; strmᵗ; deferᵉ; sizeᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator
  using (root; sched-init; st-init; subscribeE; EvalSt; NodeState; lookupNode; mergeAll-st)
open import Verify-Budget-Sufficient.Caps-Nest using (nest)
open import Refuted.Demand-Programs using (Γ₂; insT)

sl : Slots Γ₂
sl = insT 0 0 0

gasBig : Gas
gasBig = gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs (gs g0)))))))))))))))))))

inner1 : Val Γ₂ (obs natᵗ)
inner1 = switchAllᵉ (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ []))

inner3 : Val Γ₂ (obs (obs natᵗ))
inner3 = ofᵉ (strmᵗ inner1 ∷ strmᵗ inner1 ∷ strmᵗ inner1 ∷ [])

-- three parked inners, so the drain's queue is two long
parked : Val Γ₂ (obs (obs (obs natᵗ)))
parked = ofᵉ (strmᵗ (deferᵉ inner3) ∷
              strmᵗ (deferᵉ inner3) ∷
              strmᵗ (deferᵉ inner3) ∷ [])

parked5 : Val Γ₂ (obs (obs (obs natᵗ)))
parked5 = ofᵉ (strmᵗ (deferᵉ inner3) ∷
               strmᵗ (deferᵉ inner3) ∷
               strmᵗ (deferᵉ inner3) ∷
               strmᵗ (deferᵉ inner3) ∷
               strmᵗ (deferᵉ inner3) ∷ [])

head : Closed Γ₂ (obs natᵗ)
head = mergeAllᵉ (just 1) parked

head5 : Closed Γ₂ (obs natᵗ)
head5 = mergeAllᵉ (just 1) parked5

run : _
run = subscribeE gasBig head root 0 0 (sched-init head sl) (st-init head)

stᶠ : EvalSt head
stᶠ = proj₂ (proj₂ run)

run5 : _
run5 = subscribeE gasBig head5 root 0 0 (sched-init head5 sl) (st-init head5)

stᶠ5 : EvalSt head5
stᶠ5 = proj₂ (proj₂ run5)

-- the node the run installed, read back rather than written down
qAt : Maybe (NodeState Γ₂) → List (Val Γ₂ (obs (obs natᵗ)))
qAt (just (mergeAll-st {w} lim act q od)) with w ≟ᵗ obs natᵗ
... | yes refl = q
... | no  _    = []
qAt _ = []

q : List (Val Γ₂ (obs (obs natᵗ)))
q = qAt (lookupNode 0 (EvalSt.nodes stᶠ))

q5 : List (Val Γ₂ (obs (obs natᵗ)))
q5 = qAt (lookupNode 0 (EvalSt.nodes stᶠ5))

qlen≡ : length q + 100 * length q5 ≡ 402
qlen≡ = refl

kParent mParent : ℕ
kParent = nest parked sl (EvalSt.connectedShares stᶠ)
mParent = suc (sizeᵉ parked)

-- the two readings, per entry, with the entry's POSITION charged to
-- the operator measure: one level costs one unit of it
kOf : List (Val Γ₂ (obs (obs natᵗ))) → List ℕ
kOf []       = []
kOf (o ∷ os) = nest o sl (EvalSt.connectedShares stᶠ) ∷ kOf os

mOf : ℕ → List (Val Γ₂ (obs (obs natᵗ))) → List ℕ
mOf i []       = []
mOf i (o ∷ os) = i + suc (suc (sizeᵉ o)) ∷ mOf (suc i) os

enc : List ℕ → ℕ → ℕ
enc []       f = 0
enc (x ∷ xs) f = x * f + enc xs (f * 100)

measures : ℕ
measures = kParent + 100 * mParent
         + 10000 * enc (kOf q) 1 + 100000000 * enc (mOf 0 q) 1

measures≡ : measures ≡ 302911118718
measures≡ = refl

dom : List Bool
dom = go 0 q
  where
  go : ℕ → List (Val Γ₂ (obs (obs natᵗ))) → List Bool
  go i []       = []
  go i (o ∷ os) =
    ((nest o sl (EvalSt.connectedShares stᶠ) ≤ᵇ kParent)
      ∧ (i + suc (suc (sizeᵉ o)) ≤ᵇ mParent)) ∷ go (suc i) os

dom≡ : dom ≡ true ∷ true ∷ []
dom≡ = refl

-- AND AT FOUR, where the position charge has climbed three times over
kParent5 mParent5 : ℕ
kParent5 = nest parked5 sl (EvalSt.connectedShares stᶠ5)
mParent5 = suc (sizeᵉ parked5)

dom5 : List Bool
dom5 = go 0 q5
  where
  go : ℕ → List (Val Γ₂ (obs (obs natᵗ))) → List Bool
  go i []       = []
  go i (o ∷ os) =
    ((nest o sl (EvalSt.connectedShares stᶠ5) ≤ᵇ kParent5)
      ∧ (i + suc (suc (sizeᵉ o)) ≤ᵇ mParent5)) ∷ go (suc i) os

dom5≡ : dom5 ≡ true ∷ true ∷ true ∷ true ∷ []
dom5≡ = refl
