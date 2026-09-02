-- ══════════════════════════════════════════════════════════════════
-- THE NODE TABLE GROWS WITH THE BURST TOO, so charging one frame's
-- node writes to the potential's budget alone is FALSE.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  One frame leaves the whole node table
-- under what it found there joined with the potential's budget: the
-- values in flight are charged by `valsΦ?`, and whatever the frame
-- stores is supposed to fit inside that same `U`.
--
-- WHY IT LOOKED RIGHT, AND WHICH ARMS IT IS RIGHT AT.  Four of the
-- five frames either write no node at all or write back something the
-- premise measures, so the join is honest there and the budget really
-- does cover the write.  A scan is the one that stores a value nobody
-- handed it: the cell holds the ACCUMULATOR, and the accumulator is
-- what the fold has been building.
--
-- WHERE IT BREAKS.  `valsΦ?` is `all` over the burst, so it charges
-- `2 ^ sizeᵗ fn` times the step function's own nesting ONCE PER VALUE
-- and takes the maximum -- a constant in the burst length.  The fold
-- THREADS, so a step function that deepens its own accumulator adds a
-- layer per value and the stored depth is LINEAR in that length.  A
-- constant budget therefore buys a fixed number of values rather than
-- a bound, and the values past it are over.
--
-- WHY THIS IS NOT THE SAME FINDING AS THE EMIT'S.
-- `Refuted.Scan-Fold-Burst` and `Refuted.Scan-Phi-Burst` cross on what
-- the frame HANDS ON; both readings can be repaired by a grant over
-- the values in flight, because the emit is a value in flight.  This
-- one crosses on what the frame LEAVES BEHIND, at a statement carrying
-- no grant of any kind -- its sibling on the registry axis was
-- repaired with a `FrameΦHyp` and this one never was -- so the repair
-- the other two point at does not reach it and the gap is in the
-- signature rather than in the arithmetic.
--
-- WHAT DIES AND WHAT DOES NOT.  The dynamics are untouched: the cell
-- really does hold sixty-five layers after sixty-five folds, and one
-- substitution really does cost `2 ^ sizeᵗ fn`, which `applyFn-nest`
-- proves.  What dies is a node-table statement with no term in how
-- many times the frame fires.  The currency the iteration face already
-- pays in is a power in the BURST WIDTH -- `stepFrame-nodes-scan` is
-- proven with `(2 ^ sizeᵗ fn) ^ W` under `length vals ≤ W` -- so the
-- repair the numbers point at is a width premise on this leaf, not a
-- larger `U`.
--
-- WHAT IS REUSED, AND WHY.  The witness is `Refuted.Scan-Fold-Burst`'s
-- verbatim -- same step function, same accumulator, same burst, same
-- state -- and the budget is `Refuted.Scan-Phi-Burst`'s, which is
-- exactly what the frame surrenders.  Sharing them is what makes the
-- three findings comparable: one program, one fold, three quantities,
-- and only the quantity read changes between the files.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Scan-Nodes-Burst where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Nat using (ℕ; _≤_; _⊔_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0)
open import Rx.Evaluator using (scan-f; root; stepFrame)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax)
open import Refuted.Scan-Fold-Burst
  using (deepen; nid; burst; st₀; sched₀)
open import Refuted.Scan-Phi-Burst using (U)

----------------------------------------------------------------------
-- THE TWO READINGS OF THE TABLE, taken either side of the one frame.
-- The `⊔` in the statement is over the whole map, and this map has a
-- single entry, so the fold reads that entry's accumulator and nothing
-- is hidden behind a join with an unrelated cell.
----------------------------------------------------------------------

after : ℕ
after =
  nodesMax
    (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame g0 0 0 (scan-f deepen nid) root burst false sched₀ st₀)))))

-- the accumulator starts as a bare stream of numerals, so the incoming
-- side of the join contributes nothing and the crossing is the fold's
before≡0 : nodesMax st₀ ≡ 0
before≡0 = refl

after≡65 : after ≡ 65
after≡65 = refl

-- THE FIGURES, PINNED, so that a repair moving either side fails here
-- naming the number instead of turning the crossing into an equality
budget≡64 : U ≡ 64
budget≡64 = refl

stepFrame-nest-nodes-burst-absurd : after ≤ nodesMax st₀ ⊔ U → ⊥
-- `65 ≤ᵇ 0 ⊔ 64` reduces to `false`, so `T` of it IS the empty type
stepFrame-nest-nodes-burst-absurd h = ≤⇒≤ᵇ h
