-- ══════════════════════════════════════════════════════════════════
-- AND THE WHOLE LEDGER DOES NOT BUY WHAT ONE FRAME'S CEILING COULD
-- NOT: the crossing side is the one that breaks, and it breaks at the
-- SECOND rung of the walk.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
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
--
-- WHERE IT BREAKS.  The ledger is LINEAR in the frames walked and the
-- level is GEOMETRIC in them, so the two cross almost immediately and
-- never come back.  Two frames of charge take a cap of three to a
-- level of a hundred and twenty-nine while the whole ledger -- three
-- frames' worth plus a slot's -- is seventy-two.  An arriving
-- observable the level admits exactly therefore overruns the sum of
-- every allowance the path has, with a frame to spare.  Raising the
-- cap does not close it and raising the path length does not either:
-- the ledger is a fixed product of the cap with the length and the
-- slot count, while every rung of the size ladder multiplies the level
-- by twice the cap -- so whatever the ledger comes to, a walk a few
-- rungs in has passed it.
--
-- AND THE ROW SITS WHERE A WALK STANDS, which is the half that makes
-- it a finding rather than an arithmetic curiosity.  Two units of
-- charge is one `map-f` frame the size test admits with room, or two
-- of them; the level is read at exactly the rung such a walk has
-- reached, and the arrival is the one `reify` at a doubling product
-- delivers -- the same reachable value the per-frame row is built on.
-- One rung lower the row does NOT fire, and that is the point: the
-- crossing is affordable exactly while the walk has not moved.
--
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
open import Data.Nat using (ℕ; zero; suc; _≤_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Ty; Val; natᵗ; obs; _×ᵗ_; ofᵉ; reify; sizeᵛ)
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
-- THE WITNESS.  A value that doubles per layer, reified into a
-- one-shot observable -- so the observable's `sizeᵛ` is its own syntax
-- size, `sizeᵛ` at an `obs` being `sizeᵉ` of what it holds.
----------------------------------------------------------------------
Pow : ℕ → Ty
Pow zero    = natᵗ
Pow (suc k) = Pow k ×ᵗ Pow k

pow : (k : ℕ) → Val Γ₁ (Pow k)
pow zero    = 0
pow (suc k) = pow k , pow k

bigObs : Val Γ₁ (obs (Pow 6))
bigObs = ofᵉ (reify {t = Pow 6} (pow 6) ∷ [])

vals₁ : List (Val Γ₁ (obs (Pow 6)))
vals₁ = bigObs ∷ []

-- THE FOUR FIGURES THE ROW TURNS ON: the observable's own size, the
-- level two rungs above a cap of three, the telescope the ledger pays
-- for, and the whole ledger at the longest path the cap admits.
figures : List ℕ
figures = sizeᵛ (obs (Pow 6)) bigObs ∷ iterSize 3 2 3 ∷ slotsSize sl₁
  ∷ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3)) ∷ []

figures≡ : figures ≡ 129 ∷ 129 ∷ 1 ∷ 72 ∷ []
figures≡ = refl

-- LOAD-BEARING: the level premise is genuinely met, so the row is not
-- a claim about a reading no walk could have.  It would fail for a
-- value the level does not admit, and one rung lower it does.
premLvl : valsSz? {Γ = Γ₁} {s = obs (Pow 6)} (iterSize 3 2 3) vals₁ ≡ true
premLvl = refl

-- LOAD-BEARING: and the count genuinely overruns the whole ledger.
-- Both sides are numerals, so nothing here rests on a normal form.
count≡ : 2 + szCount sl₁ (iterSize 3 2 3)
           (thru-outer {Γ = Γ₁} {u = Pow 6} mergeAllᵒ 0) vals₁ ≡ 132
count≡ = refl

walk-ceil-ledger-absurd : WalkCeilLedger → ⊥
walk-ceil-ledger-absurd pr =
  ≤⇒≤ᵇ (pr {Γ = Γ₁} 3 3 2
           (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s z≤n))
           sl₁ mergeAllᵒ 0 vals₁ refl (s≤s z≤n) premLvl)
