-- ══════════════════════════════════════════════════════════════════
-- AND THE DRAIN ARM BREAKS THE SAME LEDGER THROUGH WHAT IS PARKED,
-- once the arm is priced at the parked program rather than at the
-- bound the store is held under.

-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.

-- WHAT THE STATEMENT SAYS.  The same ceiling premise as the sibling
-- row -- the walk's ceiling conjunct at one frame, with the ceiling
-- replaced by the whole ledger the chain door hands it -- instantiated
-- at the frame that EXITS a subscribed inner rather than at the one
-- that subscribes an arriving observable.  Every premise a discharge
-- has is carried, and one more than the walk's frame clause states:
-- the entry store reading, so that what the row parks is a thing a
-- walk arriving from its sink could actually have found in the table.

-- WHERE IT BREAKS, AND IT IS NOW THE LEVEL RATHER THAN THE ARM.  The
-- charge reads the layers of what the exiting node has queued, and
-- nothing bounds that but the store premise, which bounds it by the
-- LEVEL.  A rung admits size geometrically and a layer costs two
-- units of size, so the level reaches the charge at half its own
-- growth -- still far faster than a ledger that is a fixed product.
-- Three frames of charge admit a chain of three hundred and
-- eighty-seven layers where the whole ledger is seventy-two, and a
-- seventy-layer chain already overruns it.

-- AND THE ARM'S HEAD START IS GONE, which is the half worth reading.
-- Priced at the store BOUND this row fired at the second rung with one
-- nat arriving; priced at what is parked it cannot fire there at all,
-- because the deepest chain that rung's store reading admits is
-- sixty-three layers and sixty-six is under the ledger.  So the two
-- crossing arms now break at the same rung and through the same
-- channel, and one statement about where a delivered observable's
-- layers come from is what both are waiting on.

-- WHAT THIS DOES NOT SHOW.  It does not refute the ceiling SHAPE for
-- the three arms that read the program's own syntax, whose counts are
-- bounded by the cap.  It says nothing about a queue of several, whose
-- join is a separate claim.  And it says nothing against a ledger that
-- CLIMBS -- what is refuted is a product, and a right-hand side
-- iterating the way the left-hand side does is a different statement.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Walk-Ceil-Drain where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _≤ᵇ_; _+_; _*_; s≤s; z≤n)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (hot)
open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; ofᵉ; emptyᵉ; mapᵉ;
  nat̂; varᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (EvalSt; NodeId; AllOp; mergeAllᵒ;
  from-inner; mergeAll-st; installNode; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (frameSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; frameCh; szCount)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Two things
-- separate it from its sibling: the frame it stands at, and the store
-- reading, which the frame clause does not state but the walk's own
-- sink does -- carried here so the row cannot be bought by a table no
-- walk could have reached this frame with.
----------------------------------------------------------------------
WalkCeilDrain : Set
WalkCeilDrain = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (S L k : ℕ) →
  2 ≤ S → L ≤ S →
  k ≤ L * frameCh S S + n * (S * frameCh S S) →
  (sl : Slots Γ) (op : AllOp) (allNid inst : NodeId) (st : EvalSt e)
  (vals : List (Val Γ natᵗ)) →
  frameSz? S (from-inner {Γ = Γ} {s = natᵗ} op allNid inst) ≡ true →
  length vals ≤ S →
  valsSz? {Γ = Γ} {s = natᵗ} (iterSize S k S) vals ≡ true →
  all (λ kv → boundedNode (iterSize S k S) (proj₂ kv))
      (EvalSt.nodes st) ≡ true →
  k + szCount sl (EvalSt.nodes st)
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
-- THE PARKED PROGRAM.  A chain of identity map layers, which spends
-- one layer and two units of size per rung -- so the level's reading
-- of SIZE admits half of itself in layers, and that ratio is the whole
-- of what stands between the store premise and the charge.
----------------------------------------------------------------------
idF : Fn Γ₁ [] [] [] natᵗ natᵗ
idF = varᵗ (here refl)

chainN : ℕ → Closed Γ₁ natᵗ
chainN zero    = ofᵉ (nat̂ 0 ∷ [])
chainN (suc k) = mapᵉ idF (chainN k)

e₀ : Closed Γ₁ natᵗ
e₀ = emptyᵉ

parked : ℕ → EvalSt e₀
parked m = installNode 0
  (mergeAll-st {Γ = Γ₁} {t = natᵗ} nothing 1 (chainN m ∷ []) true)
  (st-init e₀)

vals₁ : List (Val Γ₁ natᵗ)
vals₁ = 0 ∷ []

-- THE FIGURES THE ROW TURNS ON: the two levels, the sizes of the two
-- chains they admit, and the whole ledger at the longest path the cap
-- admits.
figures : List ℕ
figures = iterSize 3 2 3 ∷ iterSize 3 3 3
  ∷ sizeᵉ (chainN 63) ∷ sizeᵉ (chainN 70)
  ∷ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3)) ∷ []

figures≡ : figures ≡ 129 ∷ 777 ∷ 129 ∷ 143 ∷ 72 ∷ []
figures≡ = refl

-- LOAD-BEARING: the store premise is genuinely met, so what the row
-- parks is a thing the walk's own sink reading admits at this rung.
premSt : all (λ kv → boundedNode (iterSize 3 3 3) (proj₂ kv))
             (EvalSt.nodes (parked 70)) ≡ true
premSt = refl

premLvl : valsSz? {Γ = Γ₁} {s = natᵗ} (iterSize 3 3 3) vals₁ ≡ true
premLvl = refl

-- LOAD-BEARING: and the count genuinely overruns the whole ledger.
-- Both sides are numerals, so nothing here rests on a normal form.
count≡ : 3 + szCount sl₁ (EvalSt.nodes (parked 70))
           (from-inner {Γ = Γ₁} {s = natᵗ} mergeAllᵒ 0 1) vals₁ ≡ 74
count≡ = refl

-- LOAD-BEARING, AND IT IS WHAT SAYS THE ARM LOST ITS HEAD START: at
-- the rung below, the DEEPEST chain the store reading admits still
-- fits under the ledger, and one layer deeper is a chain that reading
-- rejects.  So the earlier breach the store-bound denomination bought
-- is gone rather than merely moved.
belowFits : ((2 + szCount sl₁ (EvalSt.nodes (parked 63))
               (from-inner {Γ = Γ₁} {s = natᵗ} mergeAllᵒ 0 1) vals₁)
             ≤ᵇ (3 * frameCh 3 3 + 1 * (3 * frameCh 3 3))) ≡ true
belowFits = refl

belowAdmits : all (λ kv → boundedNode (iterSize 3 2 3) (proj₂ kv))
                  (EvalSt.nodes (parked 64)) ≡ false
belowAdmits = refl

walk-ceil-drain-absurd : WalkCeilDrain → ⊥
walk-ceil-drain-absurd pr =
  ≤⇒≤ᵇ (pr {Γ = Γ₁} 3 3 3
           (s≤s (s≤s z≤n)) (s≤s (s≤s (s≤s z≤n))) (s≤s (s≤s (s≤s z≤n)))
           sl₁ mergeAllᵒ 0 1 (parked 70) vals₁ refl (s≤s z≤n) premLvl premSt)
