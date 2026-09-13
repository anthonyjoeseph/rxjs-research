-- THE DRAIN LEAF RE-SEEDS FROM THE ARRIVAL AND THE STORE, AND A CHAIN'S
-- OWN FRAMES MANUFACTURE DEPTH FROM NEITHER.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- The sibling witness one door along left this open deliberately,
-- reading the drain-side hole as needing a REACHED state.  It does not.
-- A registration's chain is a `Path Γ lo s t`, typed by the context and
-- the root type alone — it carries no index tying it to the program
-- being run — so an adversarial registry is WRITTEN, and the arithmetic
-- that kills the leaf is arithmetic about what a written chain can do.
--
-- WHAT THE RE-SEED READS AND WHAT IT MISSES.  One arrival enters at
-- `hopDᵛ` of its own payload joined with the store's own reading, and
-- `foldPath` threads that ONE witness through every frame of the chain
-- without re-seeding at any of them.  So a `map-f` frame is free: it
-- applies a function to the payload, and the function's body is an
-- expression of whatever size the registry's author wrote.  A plain
-- numeral arrives — reading zero, and a store whose only node holds an
-- empty queue adds zero — and the frame hands back a tower.  The
-- `thru-outer` frame behind it then subscribes that tower, and every
-- flattener inside it peels the rank once more.
--
-- SO THE PROGRAM IS IRRELEVANT, WHICH IS THE WHOLE FINDING.  The rank
-- the arrival enters at reads the ROOT term, and the root term here is
-- the empty observable — the smallest reading this language has.
-- Nothing about the run's own program constrains what the chain
-- manufactures, so the gap is not a rate to be closed by entering
-- higher: it is unbounded at every entry, since the tower below can be
-- written one level deeper at no cost to any quantity the entry reads.
-- That is what the fit hypothesis is for, and it is a hypothesis about
-- the REGISTRY rather than about the program precisely because of this.
--
-- AND CONDITIONING ON A COHERENCE RECORD IS NOT THE REPAIR, which is
-- the half worth having: such a record constrains the registry's COUNTS
-- and its element TYPES, and the depth this witness manufactures is a
-- property of a chain's FRAMES.  What is missing is a fact tying a
-- registration's frames to the program being run.
--
-- DEAD ROUTE: demanding the between-cascades coherence record as a
--   hypothesis.  Every field of it was satisfied at the same
--   adversarial state, so the conditioned statement was refuted by the
--   witness below unchanged.
-- RECOVERY: git show 9a72dff:agda/evidence/refuted/Refuted/Drain-Reachable.agda
--   restores the machine form of that second witness, which is gone
--   because `src` no longer states the record it was conditioned on.
module Refuted.Drain-Reachable where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Fuel; Id)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂; ofᵉ;
  emptyᵉ; mergeAllᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; map-f;
  thru-outer; mergeAllᵒ; mergeAll-st; drain; hasDry; sched-init; st-init;
  atDyn)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED, so that this is
-- evidence about the form it was taken against and not about whatever
-- the postulate says today.  A repaired statement makes the witness
-- below fail to typecheck rather than quietly agree with it.
----------------------------------------------------------------------

DrainDryFree : Set
DrainDryFree = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e) →
  hasDry (drain fuel nextId sched st) ≡ false

----------------------------------------------------------------------
-- THE ADVERSARIAL RUN.  An empty context, so there are no slots to
-- count; the empty observable as the root term, so the seed is as small
-- as this language can make it; and one scripted numeral arriving on
-- source zero, so the payload's own nesting is zero.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

e₀ : Closed Γ₀ natᵗ
e₀ = emptyᵉ

-- the frame's own function: a constant map into a four-deep tower of
-- flatteners, each layer of which the `thru-outer` behind it will
-- subscribe.  Nothing the entry reads grows when a layer is added
deep : Fn Γ₀ [] [] [] natᵗ (obs natᵗ)
deep = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ
         (mergeAllᵉ nothing (ofᵉ (strmᵗ
           (mergeAllᵉ nothing (ofᵉ (strmᵗ
             (mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 1 ∷ [])) ∷ [])))
             ∷ [])))
           ∷ [])))
         ∷ [])))

chain₀ : Path Γ₀ 0 natᵗ natᵗ
chain₀ = map-f deep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

sched₀ : Sched Γ₀
sched₀ = record (sched-init e₀ ins₀)
  { live = record { source = 0 ; ordinal = 0 ; elemTy = natᵗ
                  ; pending = (0 , 1) ∷ [] } ∷ [] }

st₀ : EvalSt e₀
st₀ = record (st-init e₀)
  { registry = (0 , atDyn 0 0 , (natᵗ , chain₀)) ∷ []
  ; nextReg  = 1
  ; nodes    = (0 , mergeAll-st {t = natᵗ} nothing 0 [] false) ∷ [] }

----------------------------------------------------------------------
-- THE CROSSING, PINNED BY `refl` RATHER THAN COMPUTED INSIDE THE ⊥, so
-- that the witness fails loudly if either side of the comparison moves.
----------------------------------------------------------------------

dry₀ : hasDry (drain 1 1 sched₀ st₀) ≡ true            -- LOAD-BEARING
dry₀ = refl

drain-dry-free-false : DrainDryFree → ⊥
drain-dry-free-false h with trans (sym (h 1 1 sched₀ st₀)) dry₀
... | ()
