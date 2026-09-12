-- THE DRAIN LEAF RE-SEEDS FROM THE ARRIVAL AND THE STORE, AND A CHAIN'S
-- OWN FRAMES MANUFACTURE DEPTH FROM NEITHER.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.
--
-- The sibling witness one door along left this open deliberately,
-- reading the drain-side hole as needing a REACHED state.  It does not.
-- A registration's chain is a `Path Γ s t`, typed by the context and
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
-- AND THE INVARIANT DOES NOT CLOSE IT EITHER, which is the half worth
-- having: the coherence record carried between cascades constrains the
-- registry's COUNTS and its element TYPES, and says nothing about the
-- frames a chain is built from.  A statement conditioned on it is
-- refuted by the same witness, so conditioning is not the repair; what
-- is missing is a fact tying a registration's frames to the program,
-- and that fact has no home in the record as it stands.
module Refuted.Drain-Reachable where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; z≤n)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Fuel; Id)
open import Rx.Protocol using (ProtocolSt; paidUp)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂; ofᵉ;
  emptyᵉ; mergeAllᵉ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; map-f;
  thru-outer; mergeAllᵒ; mergeAll-st; drain; hasDry; sched-init; st-init)
open import Verify-Well-Formed.Part2 using (Inv)

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

-- THE STORE BOUND the schedule below is built at.  `evaluate` builds
-- its schedule at the fuel it then hands the drain, so a witness is
-- about a RUN only when the two agree.  A larger bound raises what the
-- ROOT term would read, and this witness's crossing is manufactured by
-- the chain rather than read off the program — which is the finding —
-- so the bound is picked generously rather than tightly.
SB : ℕ
SB = 30

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

chain₀ : Path Γ₀ natᵗ natᵗ
chain₀ = map-f deep ↠ (thru-outer mergeAllᵒ 0 ↠ root)

sched₀ : Sched Γ₀
sched₀ = record (sched-init SB e₀ ins₀)
  { live = record { source = 0 ; ordinal = 0 ; elemTy = natᵗ
                  ; pending = (0 , 1) ∷ [] } ∷ [] }

st₀ : EvalSt e₀
st₀ = record (st-init e₀)
  { registry = (0 , 0 , (natᵗ , chain₀)) ∷ []
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

----------------------------------------------------------------------
-- AND CONDITIONING ON THE COHERENCE RECORD DOES NOT REPAIR IT.  The
-- obvious reading of the witness above is that it is a store no run
-- mints, so the repair is to demand the invariant every run carries.
-- The invariant is imported rather than restated, precisely so that a
-- field added to it makes this second witness fail to typecheck — which
-- is the answer this half is here to give, and it is currently no.
--
-- EVERY FIELD IS SATISFIED AT THE SAME STATE.  The registry holds one
-- entry, so the automaton's multiset is one entry and the counts agree;
-- the entry's element type is the live source's, so the type gate
-- admits it; the protocol is at its initial watermark with no open
-- instant; nothing is done, so the share-plumbing obligation is
-- vacuous; the merge node's counter is zero and the chain contributes
-- no inner instance, so the cache agrees; and the context is empty, so
-- there is no hot slot to keep live.
--
-- WHAT THAT LOCATES.  The record constrains the registry's COUNTS and
-- its element TYPES, and the depth the witness manufactures is a
-- property of a chain's FRAMES — of which function a `map-f` carries,
-- a quantity no field mentions.  So the missing fact is not coherence
-- between the store's parts: it is a tie between a registration's
-- frames and the program being run, and adding the record as a
-- hypothesis buys a statement that is false at exactly the same point.
----------------------------------------------------------------------

DrainDryFreeInv : Set
DrainDryFreeInv = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (nextId : Id) (sched : Sched Γ) (st : EvalSt e)
  (S : ProtocolSt) →
  Inv nextId sched st S → paidUp S ≡ true →
  hasDry (drain fuel nextId sched st) ≡ false

S₀ : ProtocolSt
S₀ = record { live = 0 ∷ [] ; horizon = 0 ; current = nothing ; done = false }

inv₀ : Inv 1 sched₀ st₀ S₀
inv₀ = record
  { live-matches = λ s → refl
  ; reg-typed    = refl
  ; horizon-low  = z≤n
  ; current-past = tt
  ; done-plumbed = λ ()
  ; caches       = refl
  ; hot-live     = λ ()
  }

paid₀ : paidUp S₀ ≡ true                               -- LOAD-BEARING
paid₀ = refl

drain-dry-free-inv-false : DrainDryFreeInv → ⊥
drain-dry-free-inv-false h
  with trans (sym (h 1 1 sched₀ st₀ S₀ inv₀ paid₀)) dry₀
... | ()
