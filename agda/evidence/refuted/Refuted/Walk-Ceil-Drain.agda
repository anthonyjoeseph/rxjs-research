-- ══════════════════════════════════════════════════════════════════
-- AND THE DRAIN ARM BREAKS THE SAME LEDGER WITH NO ARRIVAL AT ALL,
-- one rung EARLIER than the arm that reads its arrivals.

-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.

-- WHAT THE STATEMENT SAYS.  The same ceiling premise as the sibling
-- row -- the walk's ceiling conjunct at one frame, with the ceiling
-- replaced by the whole ledger the chain door hands it -- instantiated
-- at the frame that EXITS a subscribed inner rather than at the one
-- that subscribes an arriving observable.  Every premise a discharge
-- has is carried: the frame passes its own size test, the burst is
-- under the width cap, the values are under the level, and the level
-- in hand is under the ledger it has been spending.

-- WHERE IT BREAKS, AND THE VALUE HAS NO PART IN IT.  This arm's charge
-- is the LEVEL, flatly: the parked program is in the store and the
-- count is handed no state to read it out of, so what it prices is the
-- bound every stored node is held under.  The level is geometric in
-- the frames walked and the ledger is linear in them, so the row needs
-- no arrival, no depth and no width -- a single nat, whose whole size
-- is one, is carried only so that no premise of the row is vacuous.

-- AND IT FIRES ONE RUNG BEFORE THE ARRIVAL-READING ARM DOES, which is
-- what makes it a separate finding rather than a second instance.  Two
-- frames of charge take a cap of three to a level of one hundred and
-- twenty-nine against a ledger of seventy-two; one frame reaches
-- twenty-one and fits.  So repairing what the sibling arm reads about
-- its arrivals -- the currency, the burst join, the channel from the
-- level to an arrival's layers -- cannot rescue this premise, because
-- the earliest crossing that overruns it reads nothing about a value.

-- WHAT THIS DOES NOT SHOW.  It does not refute the ceiling SHAPE for
-- the three arms that read the program's own syntax, whose counts are
-- bounded by the cap.  Nor does it say the drain's own cost IS the
-- level: what a `mergeAllᵒ` exit actually spends is the subscription of
-- whatever its node has parked, and that is a reading of the store
-- rather than of the bound the store is held under.  And it says
-- nothing against a ledger that CLIMBS -- what is refuted is a
-- product, and a right-hand side iterating the way the left-hand side
-- does is a different statement.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Ceil-Drain where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; _≤_; _≤ᵇ_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Val; natᵗ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (NodeId; AllOp; mergeAllᵒ; from-inner; iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; frameCh; szCount)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED, and the only thing
-- separating it from its sibling is the frame it stands at.
----------------------------------------------------------------------
WalkCeilDrain : Set
WalkCeilDrain = ∀ {n} {Γ : Ctx n} (S L k : ℕ) → 2 ≤ S → L ≤ S →
  k ≤ L * frameCh S S + n * (S * frameCh S S) →
  (sl : Slots Γ) (op : AllOp) (allNid inst : NodeId)
  (vals : List (Val Γ natᵗ)) →
  frameSz? S (from-inner {Γ = Γ} {s = natᵗ} op allNid inst) ≡ true →
  length vals ≤ S →
  valsSz? {Γ = Γ} {s = natᵗ} (iterSize S k S) vals ≡ true →
  k + szCount sl (iterSize S k S)
        (from-inner {Γ = Γ} {s = natᵗ} op allNid inst) vals
    ≤ L * frameCh S S + n * (S * frameCh S S)

----------------------------------------------------------------------
-- ONE SLOT, SCRIPTED AND EMPTY, so the ledger's telescope allowance is
-- as small as it can be made and the row does not turn on it.
----------------------------------------------------------------------
Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

sl₁ : Slots Γ₁
sl₁ fzero = scripted (hot [])

----------------------------------------------------------------------
-- THE WITNESS: one nat, carried so that the width and level premises
-- are met by something rather than by an empty list.
----------------------------------------------------------------------
vals₁ : List (Val Γ₁ natᵗ)
vals₁ = 0 ∷ []

-- THE THREE FIGURES THE ROW TURNS ON: the level one frame of charge
-- reaches, the level two frames reach, and the whole ledger at the
-- longest path the cap admits.
figures : List ℕ
figures = iterSize 3 1 3 ∷ iterSize 3 2 3
  ∷ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3)) ∷ []

figures≡ : figures ≡ 21 ∷ 129 ∷ 72 ∷ []
figures≡ = refl

-- LOAD-BEARING: the level premise is genuinely met, so the row is not
-- a claim about a reading no walk could have.
premLvl : valsSz? {Γ = Γ₁} {s = natᵗ} (iterSize 3 2 3) vals₁ ≡ true
premLvl = refl

-- LOAD-BEARING: and the count genuinely overruns the whole ledger.
-- Both sides are numerals, so nothing here rests on a normal form.
count≡ : 2 + szCount sl₁ (iterSize 3 2 3)
           (from-inner {Γ = Γ₁} {s = natᵗ} mergeAllᵒ 0 1) vals₁ ≡ 131
count≡ = refl

-- LOAD-BEARING, AND IT IS THE HALF THAT MAKES THE ROW A FINDING: one
-- rung lower the charge FITS, so what is exhibited is a crossing the
-- ledger stops affording rather than a ledger that never afforded one.
belowFits : ((1 + szCount sl₁ (iterSize 3 1 3)
               (from-inner {Γ = Γ₁} {s = natᵗ} mergeAllᵒ 0 1) vals₁)
             ≤ᵇ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3))) ≡ true
belowFits = refl

walk-ceil-drain-absurd : WalkCeilDrain → ⊥
walk-ceil-drain-absurd pr =
  ≤⇒≤ᵇ (pr {Γ = Γ₁} 3 3 2
           (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s z≤n))
           sl₁ mergeAllᵒ 0 1 vals₁ refl (s≤s z≤n) premLvl)
