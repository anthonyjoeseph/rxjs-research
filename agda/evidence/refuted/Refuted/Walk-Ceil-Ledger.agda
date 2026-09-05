-- ══════════════════════════════════════════════════════════════════
-- AND THE WHOLE LEDGER DOES NOT BUY WHAT ONE FRAME'S CEILING COULD
-- NOT: the crossing side is the one that breaks, and it breaks at the
-- SECOND rung of the walk.

-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.

-- WHAT THE STATEMENT SAYS.  The size walk asserts, at every frame, that
-- the level it has climbed to plus that frame's count stays under one
-- ABSOLUTE ceiling, and the chain door supplies that ceiling from a
-- LEDGER: a per-frame charge times the path's length, plus a
-- telescope allowance of a cap's worth per slot.  So the question a
-- discharge turns on is not whether one frame fits its own product --
-- `Refuted.Frame-Step-Size-Cross-Count` settles that -- but whether
-- the sum of every frame's allowance covers the one frame that reads
-- what it subscribes.  This row carries that whole sum on the right,
-- with the two ties a real walk supplies: the path's length is under
-- the cap, because the size predicate's own length conjunct says so,
-- and the level in hand is under the ledger, because the ceiling
-- conjunct held at every frame before this one.

-- WHERE IT BREAKS.  The ledger is LINEAR in the frames walked and the
-- level is GEOMETRIC in them, so the two cross almost immediately and
-- never come back.  Two frames of charge take a cap of three to a
-- level of a hundred and twenty-nine while the whole ledger -- three
-- frames' worth plus a slot's -- is seventy-two.  An arriving
-- burst the level admits exactly therefore overruns the sum of
-- every allowance the path has, with a frame to spare.  Raising the
-- cap does not close it and raising the path length does not either:
-- the ledger is a fixed product of the cap with the length and the
-- slot count, while every rung of the size ladder multiplies the level
-- by twice the cap -- so whatever the ledger comes to, a walk a few
-- rungs in has passed it.

-- AND THE ROW SITS WHERE A WALK STANDS, which is the half that makes
-- it a finding rather than an arithmetic curiosity.  Two units of
-- charge is one `map-f` frame the size test admits with room, or two
-- of them; the level is read at exactly the rung such a walk has
-- reached, and each arrival is a chain of map layers whose size the
-- level admits exactly.  One rung lower the row does NOT fire, and
-- that is the point: the crossing is affordable exactly while the
-- walk has not moved.

-- AND WHAT OVERRUNS IT IS THE BURST, not the depth of any one arrival.
-- The count reads an arrival's LAYERS and a chain spends two nodes of
-- size per layer, so the level's bound on SIZE admits sixty-three
-- layers and no more: one such arrival costs sixty-four against a
-- ledger of seventy-two and fits.  Three do not, and three is what the
-- length premise allows.  So the level reaches this arm only
-- logarithmically now, and it is the width that takes it out of the
-- ledger's priceable set.

-- WHAT THIS DOES NOT SHOW.  It does not refute the ceiling SHAPE for
-- the three arms that read the program's own syntax -- their counts
-- are bounded by the cap and a per-frame product pays them at every
-- rung.  Nor does it reach the `from-inner` arm, whose charge is the
-- level itself and which therefore breaks the same way without needing
-- a value at all.  And it says nothing against a ledger that CLIMBS:
-- what is refuted is a product, and a right-hand side iterating the
-- way the left-hand side does is a different statement.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Ceil-Ledger where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Val; Closed; Fn; natᵗ; obs; ofᵉ; mapᵉ;
  nat̂; varᵗ; sizeᵛ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Evaluator using (NodeId; AllOp; mergeAllᵒ; thru-outer; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; frameCh; szCount)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED -- and what stands
-- here is the chain door's ceiling premise SPENT, not the door
-- itself: the walk's own ceiling conjunct at a crossing frame, with
-- the ceiling replaced by the ledger the door hands it.  Every premise
-- such a discharge has is carried, including the two the walk supplies
-- rather than the caller: the path length under the cap, and the level
-- in hand under the ledger it has been spending.
----------------------------------------------------------------------
WalkCeilLedger : Set
WalkCeilLedger = ∀ {n} {Γ : Ctx n} {u} (S L k : ℕ) → 2 ≤ S → L ≤ S →
  k ≤ L * frameCh S S + n * (S * frameCh S S) →
  (sl : Slots Γ) (op : AllOp) (nid : NodeId)
  (vals : List (Val Γ (obs u))) →
  frameSz? S (thru-outer {Γ = Γ} {u = u} op nid) ≡ true →
  length vals ≤ S →
  valsSz? (iterSize S k S) vals ≡ true →
  k + szCount sl (iterSize S k S) (thru-outer {Γ = Γ} {u = u} op nid) vals
    ≤ L * frameCh S S + n * (S * frameCh S S)

----------------------------------------------------------------------
-- ONE SLOT, SCRIPTED AND EMPTY, so the telescope allowance the ledger
-- pays for is genuinely spent by the count and not padded: the whole
-- of `slotsSize` here is one, and the ledger still hands a cap's worth
-- of a frame charge for it.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

----------------------------------------------------------------------
-- THE WITNESS.  A chain of map layers over a singleton source, whose
-- function is the identity, so the arrival's `sizeᵛ` -- `sizeᵉ` of
-- what the `obs` holds -- grows by two per layer while the count the
-- crossing takes grows by one.
----------------------------------------------------------------------
idF : Fn Γ₁ [] [] [] natᵗ natᵗ
idF = varᵗ (here refl)

chainN : ℕ → Closed Γ₁ natᵗ
chainN zero    = ofᵉ (nat̂ 0 ∷ [])
chainN (suc k) = mapᵉ idF (chainN k)

-- THE BURST IS THREE WIDE, which is exactly what the length premise
-- admits at this cap, and it is the axis the row turns on.
vals₁ : List (Val Γ₁ (obs natᵗ))
vals₁ = chainN 63 ∷ chainN 63 ∷ chainN 63 ∷ []

-- THE FOUR FIGURES THE ROW TURNS ON: one arrival's own size, the
-- level two rungs above a cap of three, the telescope the ledger pays
-- for, and the whole ledger at the longest path the cap admits.
figures : List ℕ
figures = sizeᵛ (obs natᵗ) (chainN 63) ∷ iterSize 3 2 3 ∷ slotsSize sl₁
  ∷ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3)) ∷ []

figures≡ : figures ≡ 129 ∷ 129 ∷ 1 ∷ 72 ∷ []
figures≡ = refl

-- LOAD-BEARING: the level premise is genuinely met, so the row is not
-- a claim about a reading no walk could have.  It would fail for an
-- arrival the level does not admit, and one layer deeper it does.
premLvl : valsSz? {Γ = Γ₁} {s = obs natᵗ} (iterSize 3 2 3) vals₁ ≡ true
premLvl = refl

-- LOAD-BEARING: and the count genuinely overruns the whole ledger.
-- Both sides are numerals, so nothing here rests on a normal form.
count≡ : 2 + szCount sl₁ (iterSize 3 2 3)
           (thru-outer {Γ = Γ₁} {u = natᵗ} mergeAllᵒ 0) vals₁ ≡ 192
count≡ = refl

walk-ceil-ledger-absurd : WalkCeilLedger → ⊥
walk-ceil-ledger-absurd pr =
  ≤⇒≤ᵇ (pr {Γ = Γ₁} 3 3 2
           (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s z≤n))
           sl₁ mergeAllᵒ 0 vals₁ refl (s≤s (s≤s (s≤s z≤n))) premLvl)
