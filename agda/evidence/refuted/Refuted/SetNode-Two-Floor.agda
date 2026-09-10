-- ══════════════════════════════════════════════════════════════════
-- A NODE WRITE PRICED AT ONE CHAIN'S FLOOR DOES NOT KEEP THE REGISTRY
-- PARKED, because the registry may reach the same cell at a DIFFERENT
-- floor.  The statement asks the write to preserve the reading at the
-- floor of the path it is handed, and concludes the whole registry's
-- park ledger survives; a registered chain ending at a shared slot
-- reads that cell at the slot's index instead, and nothing in the
-- hypotheses says the two agree.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- THE TWO FLOORS, AND WHY ONE CELL CAN CARRY BOTH.  A chain's floor is
-- the context width when it ends at the root and the SLOT INDEX when it
-- ends at a share sink, so a two-slot context already offers 2 and 0.
-- The queue reading is `inputsBelowᵉ`, which is a strict `<` against
-- that number: a payload naming the first slot is below 2 and is not
-- below 0.  So one written queue is simultaneously admissible at the
-- root-ended path the write is priced against and inadmissible at the
-- share-ended chain the registry holds.
--
-- THE HYPOTHESIS IS DISCHARGED WITHOUT USING ITS ANTECEDENT, which is
-- what makes the row a statement about the FLOOR rather than about a
-- write that was always going to be illegal.  At the priced floor the
-- new content is admissible outright, so the implication holds by a
-- constant -- the write is exactly as legal as the statement asks it to
-- be, and the registry still breaks.
--
-- THE CELL IS PRESENT BEFORE THE WRITE, deliberately: an absent cell
-- reads as parked at every floor, so a fresh-cell witness would be
-- refuting the ordering lemma's job instead of this one.  Here the
-- overwritten cell is installed with an EMPTY queue, which is parked at
-- both floors, so the whole difference between pre-state and post-state
-- is the content this write puts there.
--
-- WHAT THIS DOES AND DOES NOT DECIDE.  The state is built rather than
-- run, so nothing here says a run REACHES a registry visiting a cell at
-- a floor other than the writer's.  What it does say is that the
-- invariant as it stands would not stop one: the two conjuncts that
-- read a chain at all clear this registry, so no repair is available
-- from tightening either.  That is the point rather than a
-- limitation: the reading quantifies over every state and over every
-- path, so the repair cannot be a cleverer proof of it -- what is
-- missing is the writer's PROVENANCE, that the chain it stands on is
-- the one that installed the cell, and provenance travels with a chain
-- rather than being read off a store.
-- ══════════════════════════════════════════════════════════════════
module Refuted.SetNode-Two-Floor where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Fin using () renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; input)
open import Rx.Evaluator
  using (EvalSt; NodeId; NodeState; Path; root; share-sink; _↠_;
         from-inner; mergeAllᵒ; mergeAll-st; installNode; st-init; setNode)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (parkStrat?; pathFloor; regPark?; regStrat?; regOrd?; regOwn?)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Walk-Burst-Additive using (e₀)

-- the cell every reading below is about
nid : NodeId
nid = 0

-- the registered chain: it exits an inner of the same flatten and ends
-- at the first shared slot, so it reads `nid` at floor zero
regPath : Path Γ₂ natᵗ (obs natᵗ)
regPath = from-inner mergeAllᵒ nid 9 ↠ share-sink fzero

-- the path the write is priced against: root-ended, so floor two
pricedPath : Path Γ₂ (obs natᵗ) (obs natᵗ)
pricedPath = root

floors : pathFloor regPath ≡ 0
floors = refl

pricedFloor : pathFloor pricedPath ≡ 2
pricedFloor = refl

-- empty queue: parked at every floor, so the pre-state is clean
before : NodeState Γ₂
before = mergeAll-st {t = natᵗ} nothing 0 [] false

-- one payload naming the first slot: below two, not below zero
after : NodeState Γ₂
after = mergeAll-st {t = natᵗ} nothing 0 (input fzero ∷ []) false

pricedOK : parkStrat? (pathFloor pricedPath) (just after) ≡ true
pricedOK = refl

sunkBad : parkStrat? (pathFloor regPath) (just after) ≡ false
sunkBad = refl

stᵗ : EvalSt e₀
stᵗ = record (installNode nid before (st-init e₀))
        { registry = (0 , 0 , (natᵗ , regPath)) ∷ [] }

parkedBefore : regPark? (EvalSt.registry stᵗ) stᵗ ≡ true
parkedBefore = refl

parkedAfter :
  regPark? (EvalSt.registry stᵗ)
    (record stᵗ { nodes = setNode nid after (EvalSt.nodes stᵗ) }) ≡ false
parkedAfter = refl

-- AND THE TWO LEDGERS THAT READ A CHAIN AT ALL ADMIT THIS REGISTRY, so
-- the repair cannot be recovered from either.  The stratification
-- ledger clears the entry because its source sits at or below the
-- chain's own floor and every frame of it is free; the ordering ledger
-- clears it at any counter standing above the cells the chain names.
stratOK : regStrat? (EvalSt.registry stᵗ) ≡ true
stratOK = refl

ordOK : regOrd? 10 (EvalSt.registry stᵗ) ≡ true
ordOK = refl

-- THE READING THE WRITE IS WAITING ON, at this registry and this
-- chain: the cell is visited at zero and the writer stands at two.
ownBad : regOwn? nid (pathFloor pricedPath) (EvalSt.registry stᵗ) ≡ false
ownBad = refl

setNode-two-floor-absurd :
  (∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
     (nd : NodeId) (κ : Path Γ u t) (st : EvalSt e) →
     regOwn? nd (pathFloor κ) (EvalSt.registry st) ≡ true) → ⊥
setNode-two-floor-absurd h with h nid pricedPath stᵗ
... | ()
