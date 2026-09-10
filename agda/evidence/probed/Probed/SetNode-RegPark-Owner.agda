-- ══════════════════════════════════════════════════════════════════
-- PROBE FOR setNode-regPark-owner: does regPark? survive a setNode
-- whose new state satisfies parkStrat? at the walk's own floor?
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT THE ROWS COVER.  Two shapes: an empty registry (DEGENERATE,
-- included to pin that side explicitly) and a registry carrying one
-- entry whose path visits the written node at the walk's floor
-- (LOAD-BEARING).  In the load-bearing row the antecedent is
-- non-vacuous -- the mergeAll state at nid has an empty queue, so
-- parkStrat? returns true at the walk's floor -- and the conclusion
-- holds because the new state also has an empty queue.
--
-- WHAT IS NOT COVERED.  The only case that could distinguish this
-- postulate from the stronger regPark?-set (which requires the
-- ownership condition at ALL floors) is a state where the registry
-- holds a path that visits nid at a floor DIFFERENT from pathFloor κ.
-- Whether such a state is reachable by the evaluator is the node-
-- ownership question the postulate header names.  No row here reaches
-- it: the load-bearing row uses a single registry entry whose path
-- visits nid at pathFloor κ exactly, so the hypothesis and the
-- registry check are at the same floor.  A row that separated them
-- would need a registry with two entries visiting the same node at
-- different floors -- a shape requiring two inner subscriptions on one
-- mergeAll at different chain depths, not tested here.
--
-- AND THE ANTECEDENT IS NON-VACUOUS IN THE LOAD-BEARING ROW.  The
-- node at nid is a mergeAll-st with an empty queue; parkStrat? at any
-- floor over an empty queue is all [] = true, so the antecedent
-- actually holds rather than being trivially false.  Changing ns to a
-- mergeAll-st with a queue entry above the walk's floor would make the
-- conclusion false -- that is what would make the row fail.
-- ══════════════════════════════════════════════════════════════════
-- TARGET: setNode-regPark-owner @9a9f03
module Probed.SetNode-RegPark-Owner where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; emptyᵉ)
open import Rx.Evaluator
  using (EvalSt; NodeState; mergeAll-st; take-st; st-init; setNode;
         from-inner; mergeAllᵒ; _↠_; root)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (parkStrat?; pathFloor; regPark?; setNode-regPark-owner)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT AND PROGRAM -- one slot, simplest closed term
----------------------------------------------------------------------

Γ₀ : Ctx 1
Γ₀ = natᵗ ∷ⱽ []ⱽ

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

----------------------------------------------------------------------
-- THE DEGENERATE STATE -- empty registry, empty nodes
-- regPark? [] _ = true by definition; setNode changes nothing
----------------------------------------------------------------------

stDeg : EvalSt e₀
stDeg = st-init e₀

-- DEGENERATE: the registry is empty, so regPark? holds trivially on
-- both sides.  Nothing would make this row fail: an empty registry is
-- never disturbed by any setNode.

tieEmpty : Confirms
  (setNode-regPark-owner {e = e₀} 0 root (take-st 0) stDeg)
tieEmpty _ _ = refl

----------------------------------------------------------------------
-- THE LOAD-BEARING STATE -- one registry entry visiting node 0
--
-- The registry has one entry: rid=0, src=1, element type natᵗ,
-- path = from-inner mergeAllᵒ 0 0 ↠ root.
-- Node 0 holds a mergeAll-st with empty queue.
-- pathFloor root = n = 1 (context size).
-- parkStrat? 1 (just (mergeAll-st nothing 1 [] false))
--   = all (inputsBelowᵉ 1) [] = true  ← antecedent holds
-- parkStrat? 1 (just ns) = all (inputsBelowᵉ 1) [] = true
--   ← consequent holds
-- After setNode 0 ns nodes:
--   regPark? registry new_st
--   = pathPark? (from-inner mergeAllᵒ 0 0 ↠ root) new_st
--   = parkStrat? 1 (lookupNode 0 new_nodes) ∧ true
--   = parkStrat? 1 (just ns) ∧ true = true ∧ true = true
--
-- WHAT WOULD MAKE THIS ROW FAIL.  If ns were a mergeAll-st whose queue
-- contained a closed term e with inputsBelowᵉ 1 e = false (an input
-- at index ≥ 1), then parkStrat? 1 (just ns) = false and the
-- conclusion would be false.  In the 1-element context Γ₀ no such
-- term can be constructed, so this row cannot actually fail here.
-- A 2-element context with a queue entry at input index 1 would make
-- the row genuinely falsifiable.
----------------------------------------------------------------------

stLoad : EvalSt e₀
stLoad = record (st-init e₀)
  { registry = (0 , 1 , natᵗ , from-inner mergeAllᵒ 0 0 ↠ root) ∷ []
  ; nextReg  = 1
  ; nodes    = (0 , mergeAll-st {Γ = Γ₀} {t = obs natᵗ} nothing 1 [] false) ∷ []
  }

nsLoad : NodeState Γ₀
nsLoad = mergeAll-st {Γ = Γ₀} {t = obs natᵗ} nothing 0 [] false

-- sanity checks: the antecedent and conclusion hold by computation
antecedent≡ : parkStrat? (pathFloor {Γ = Γ₀} {t = natᵗ} root)
                (just (mergeAll-st {Γ = Γ₀} {t = obs natᵗ} nothing 1 [] false)) ≡ true
antecedent≡ = refl

regPark-before≡ : regPark? (EvalSt.registry stLoad) stLoad ≡ true
regPark-before≡ = refl

regPark-after≡ : regPark? (EvalSt.registry stLoad)
  (record stLoad { nodes = setNode 0 nsLoad (EvalSt.nodes stLoad) }) ≡ true
regPark-after≡ = refl

-- LOAD-BEARING: registry is non-empty and visits node 0 at floor 1.
-- The implication hypothesis is non-vacuously satisfied (antecedent
-- true from mergeAll with empty queue; consequent true from ns with
-- empty queue).  If ns had a bad queue entry the conclusion would be
-- false, but the hypothesis prevents that via the antecedent→consequent
-- implication.

tieLoad : Confirms
  (setNode-regPark-owner {e = e₀} 0 root nsLoad stLoad)
tieLoad _ _ = refl
