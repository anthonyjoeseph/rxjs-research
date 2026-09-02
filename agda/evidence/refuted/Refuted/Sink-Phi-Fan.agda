-- ══════════════════════════════════════════════════════════════════
-- THE SINK IS A LEAF OF THE FACTOR RECURSION AND A FAN-OUT OF THE
-- WALK, so the receipt it is handed is one factor short of the one
-- every chain it hands the values to is owed.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  The potential arriving at a sink pays for
-- the chains the registry admits from it.  `pathΦF` charges a sink
-- one and `pathNestD` charges it zero, so what the walk hands in is
-- that the VALUES are shallow; an admitted chain's own obligation is
-- its factor times the same values' depth plus its own, and the fan-out
-- fold demands it at every entry.
--
-- WHERE IT BREAKS, AND IT IS NOT THE BUDGET.  Legality bounds an
-- admitted chain's factor and its depth -- `pathΦF-cap` and
-- `pathNestD-len` deliver both from the size premise the arm already
-- takes -- so nothing here is unbounded.  What is missing is a
-- RELATION: the receipt is read at factor one and spent at a factor
-- the same cap allows to be an exponential of the cap squared, and no
-- reading of the sink's own syntax supplies the difference, because
-- the sink's syntax is a slot index and the chains are the STATE's.
--
-- AND THE OBVIOUS RECHARGE DIES ON THE SAME WITNESS, which is what the
-- second half below is for.  Reading the sink's factor as anything the
-- cap allows -- an exponential, the cap's own tower, a quantity chosen
-- per program -- multiplies a depth the witness takes to ZERO, so the
-- receipt is satisfied at a budget of nothing while the admitted chain
-- still owes its own `pathNestD`.  A multiplicative charge cannot pay
-- an additive debt, so the repair is not a bigger factor at the sink.
--
-- WHAT IS OWED INSTEAD.  The two facts an admitted chain needs are
-- both derivable where the arm stands -- its factor from `pathΦF-cap`
-- and its depth from `pathNestD-len`, each off the registry's own size
-- legality -- so what the sink is short of is a receipt read at those
-- two rather than at one and zero.  That is a restatement of what the
-- WALK hands a sink, in the currency it already carries, and not a
-- ledger, a level or a field: the budget never moves through the
-- fan-out, since `ShareGoΦHyp` and `PathΦHyp` recurse at the very same
-- `U`, so nothing here compounds with the hop count.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Sink-Phi-Fan where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≤_; _*_; _+_)
open import Data.Nat.Properties using (≤-refl; ≤-reflexive; *-zeroʳ)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Fn; natᵗ; obs; ofᵉ; nat̂; strmᵗ)
open import Rx.Nest-Depth using (nestDᵛ)
open import Rx.Evaluator using (Path; root; _↠_; map-f; thru-outer;
  mergeAllᵒ; share-sink)
open import Verify-Budget-Sufficient.Nest-Store using (pathNestD)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything -- and it could not be instantiated in any case, since its
-- cap does not return at any program and its budget is sealed.  So the
-- obligation is stated over the quantities the arm's own premises
-- deliver: an abstract cap and budget, one admitted chain legal at the
-- cap, and the receipt the walk hands the sink.
----------------------------------------------------------------------
SinkΦFits : Set
SinkΦFits = ∀ {n} {Γ : Ctx n} {t} (B U : ℕ) (i : Fin n)
  (v : Val Γ (lookup Γ i)) (p : Path Γ (lookup Γ i) t) →
  8 ≤ B →
  pathSz? B p ≡ true →
  valsΦ? B U (share-sink {t = t} i) (v ∷ []) ≡ true →
  valsΦ? B U p (v ∷ []) ≡ true

----------------------------------------------------------------------
-- THE WITNESS.  A shallow value -- a bare nat, so its depth is zero
-- and the sink's receipt is satisfied at a budget of nothing -- handed
-- to one registered chain that maps to an observable and parks it at a
-- merge.  Both frames are the smallest of their kind, so the chain is
-- legal at every cap the invariant admits and the crossing is not an
-- artifact of a large registration.
----------------------------------------------------------------------

shallow : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
shallow = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

chain : Path Γ₂ natᵗ natᵗ
chain = map-f shallow ↠ (thru-outer mergeAllᵒ 0 ↠ root)

val : Val Γ₂ natᵗ
val = 0

-- THE THREE QUANTITIES, PINNED, so a repair moving any of them fails
-- here naming the number rather than turning the crossing into an
-- equality.  The chain's factor is what the receipt is read at one;
-- its depth is what no factor can pay for.
factor≡ : pathΦF 8 chain ≡ 4096
factor≡ = refl

depth≡ : pathNestD chain ≡ 1
depth≡ = refl

legal : pathSz? 8 chain ≡ true
legal = refl

-- the sink's own receipt, at the smallest budget there is
handed : valsΦ? 8 0 (share-sink {Γ = Γ₂} {t = natᵗ} fzero) (val ∷ []) ≡ true
handed = refl

8≤B : 8 ≤ 8
8≤B = ≤-refl

sink-phi-fan-absurd : SinkΦFits → ⊥
sink-phi-fan-absurd pr with pr {Γ = Γ₂} {t = natᵗ} 8 0 fzero val chain
                              8≤B legal handed
... | ()

----------------------------------------------------------------------
-- AND NO RECHARGE OF THE SINK REPAIRS IT.  The reading above is about
-- the charge the sink CARRIES; this one is about any multiplicative
-- charge at all.  The factor is universally quantified, so it may be
-- an exponential of the cap, the caps recurrence itself, or a quantity
-- chosen per program -- and it is multiplied by a depth the witness
-- takes to zero, so the premise holds at every one of them while the
-- admitted chain's own `pathNestD` is still owed.
--
-- SO WHAT THE SINK IS SHORT OF IS NOT A NUMBER.  A factor pays for
-- what the values carry INTO the fan-out and the chains charge for
-- what their own frames add on top; the second survives a value with
-- nothing in it, and a product with a zero in it cannot.
----------------------------------------------------------------------
SinkΦRecharge : Set
SinkΦRecharge = ∀ {n} {Γ : Ctx n} {t} (B U F : ℕ) (i : Fin n)
  (v : Val Γ (lookup Γ i)) (p : Path Γ (lookup Γ i) t) →
  8 ≤ B →
  pathSz? B p ≡ true →
  F * (nestDᵛ (lookup Γ i) v + 0) ≤ U →
  valsΦ? B U p (v ∷ []) ≡ true

-- the receipt holds at EVERY factor, because the value is shallow, and
-- the refutation is taken at a bound one rather than at a chosen big
-- one: a row that names a number is a fact about that number, while a
-- row discharged under the binder is the statement the header makes.
recharged : ∀ (F : ℕ) → F * (nestDᵛ {Γ = Γ₂} natᵗ val + 0) ≤ 0
recharged F = ≤-reflexive (*-zeroʳ F)

sink-phi-recharge-absurd : SinkΦRecharge → ∀ (F : ℕ) → ⊥
sink-phi-recharge-absurd pr F
  with pr {Γ = Γ₂} {t = natᵗ} 8 0 F fzero val chain 8≤B legal (recharged F)
... | ()
