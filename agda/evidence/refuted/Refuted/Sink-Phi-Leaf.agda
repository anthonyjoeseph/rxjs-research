-- ══════════════════════════════════════════════════════════════════
-- A PRICED SINK LEAF PAYS FOR THE CHAINS THAT END AT A ROOT AND FOR
-- NO OTHERS, so the fan-out closes on one half of a case split and
-- the other half is what is left.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAYS.  The potential arriving at a sink pays for
-- every chain the registry admits from it.  The sink is a leaf of the
-- factor recursion, so what it is charged is a number the pricing
-- picks; what an admitted chain is owed is its own factor times the
-- values' depth plus its own.  Both of the chain's quantities are
-- bounded off the size legality this arm already takes, so the whole
-- question is whether the leaf's price dominates them.
-- ══════════════════════════════════════════════════════════════════

-- AND FOR A ROOT-TERMINATED CHAIN IT DOES.  A path carries exactly
-- one leaf, so a chain ending at `root` spends its whole factor on
-- frames, and legality caps the frame count by the size cap -- which
-- is precisely the exponent the sink is priced at.  Its depth is
-- capped in the same currency by the same premise.  That half needs
-- no new fact and is not what this file is about.

-- WHERE IT BREAKS IS THE OTHER TERMINAL.  A chain ending at a second
-- hand-over carries the leaf's own price MULTIPLIED by its frames',
-- so the leaf would have to dominate itself times a frame product,
-- and no function of the cap does that at an arbitrary chain -- which
-- is the only kind the obligation below is handed, since the path is
-- universally quantified and `pathRoots p ≡ false` is all that is
-- known of it.

-- AND AN ORDINARY PROGRAM PUTS A CHAIN THERE, which is why this is a
-- refutation rather than a caution.  A registration minted while a
-- share's own definition is being subscribed carries that share's
-- sink as its continuation, so one shared observable derived from a
-- second is already the shape.  The witness below is the smallest of
-- them: one map, one merge, and a hand-over where the previous
-- generation of this statement had a root.

-- WHAT THE WITNESS IS NOT IS A REACHABLE REGISTRY ENTRY, and that is
-- worth stating here because the shape it takes -- a chain from source
-- zero terminating at `share-sink` zero -- is precisely the one a run
-- cannot produce.  The slot telescope is stratified, so a chain ending
-- at a slot's sink was minted subscribing an input below that slot and
-- its source is strictly under it; sink hops climb and the hop count
-- is capped by the slot count.  The obligation is nonetheless refuted
-- as stated, because it quantifies over the path: the finding is that
-- the repair is to READ the chain from the registry and carry the
-- stratification, not to find a number that survives an arbitrary one.
module Refuted.Sink-Phi-Leaf where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using ([]; _∷_)
open import Data.Nat using (ℕ; _≤_; _*_; _+_; _^_)
open import Data.Nat.Properties using (≤-refl)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Val; Fn; natᵗ; obs; ofᵉ; nat̂; strmᵗ; sizeᵗ)
open import Rx.Evaluator using (Path; _↠_; map-f; thru-outer;
  mergeAllᵒ; share-sink)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsΦ?)
open import Refuted.Demand-Programs using (Γ₂)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything -- and it could not be instantiated in any case, since its
-- cap does not return at any program and its budget is sealed.  So
-- the obligation is stated over the quantities the arm's own premises
-- deliver: an abstract cap and budget, one admitted chain legal at
-- the cap, and the receipt the walk hands the sink.
----------------------------------------------------------------------
SinkΦFits : Set
SinkΦFits = ∀ {n} {Γ : Ctx n} {t} (B U : ℕ) (i : Fin n)
  (v : Val Γ (lookup Γ i)) (p : Path Γ (lookup Γ i) t) →
  8 ≤ B →
  pathSz? B p ≡ true →
  valsΦ? B U (share-sink {t = t} i) (v ∷ []) ≡ true →
  valsΦ? B U p (v ∷ []) ≡ true

----------------------------------------------------------------------
-- THE WITNESS.  A shallow value handed to one registered chain that
-- maps to an observable, parks it at a merge, and hands it on again.
-- Both frames are the smallest of their kind, so the chain is legal
-- at every cap the invariant admits and the crossing is not an
-- artifact of a large registration.  The budget is the exact number
-- the sink's own receipt is satisfied at, so nothing here turns on a
-- budget chosen small.
----------------------------------------------------------------------

shallow : Fn Γ₂ [] [] [] natᵗ (obs natᵗ)
shallow = strmᵗ (ofᵉ (nat̂ 0 ∷ []))

sink : Path Γ₂ natᵗ natᵗ
sink = share-sink fzero

chain : Path Γ₂ natᵗ natᵗ
chain = map-f shallow ↠ (thru-outer mergeAllᵒ 0 ↠ sink)

val : Val Γ₂ natᵗ
val = 0

-- the budget: what the walk hands a sink under the pricing in force
budget : ℕ
budget = pathΦF 8 sink * pathΦD 8 sink

-- THE ESCALATION, PINNED UNDER THE BINDER so that it is a fact about
-- the pricing and not about the cap this file happens to run at: the
-- chain's factor is the leaf's own multiplied by its frames', which
-- is the shape no leaf price survives.
escalates : ∀ (B : ℕ) →
  pathΦF B chain ≡ 2 ^ sizeᵗ shallow * (2 ^ B * pathΦF B sink)
escalates _ = refl

-- and its depth is the leaf's plus what the merge adds
deepens : ∀ (B : ℕ) → pathΦD B chain ≡ 1 + pathΦD B sink
deepens _ = refl

-- THE TWO QUANTITIES AT THE FLOOR THE TOWER DISCHARGES FROM, pinned,
-- so a repair moving either fails here naming the number rather than
-- turning the crossing into an equality.
leafFac≡ : pathΦF 8 sink ≡ 2 ^ 576
leafFac≡ = refl

leafDep≡ : pathΦD 8 sink ≡ 64
leafDep≡ = refl

legal : pathSz? 8 chain ≡ true
legal = refl

-- the sink's own receipt, at the budget it exactly exhausts
handed : valsΦ? 8 budget sink (val ∷ []) ≡ true
handed = refl

8≤B : 8 ≤ 8
8≤B = ≤-refl

sink-phi-leaf-absurd : SinkΦFits → ⊥
sink-phi-leaf-absurd pr with pr {Γ = Γ₂} {t = natᵗ} 8 budget fzero val chain
                               8≤B legal handed
... | ()
