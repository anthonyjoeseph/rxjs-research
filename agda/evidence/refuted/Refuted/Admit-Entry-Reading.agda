-- ══════════════════════════════════════════════════════════════════
-- WHAT AN ADMITTED ENTRY READS, IN ITS FREE FORM: four refutations
--
-- REFUTATIONS: machine-checked `… → ⊥`.  Each theorem here says a route
-- CANNOT work, and says it in a form the typechecker rechecks — unlike a
-- prose note, which decays silently.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Admit-Entry-Reading where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_; proj₂)
open import Data.Vec using ([]; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; natᵗ; obs; ofᵉ; emptyᵉ; strmᵗ; nat̂;
                          input)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Path; share-sink; _↠_; take-f; from-inner;
                                mergeAllᵒ; mergeAll-st; Sched; EvalSt; Arrival;
                                sched-init; st-init; shareAdmit; shareLatch;
                                chainsOf; cascadeLatch; arrTy)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathPark?; pathOrd?)

------------------------------------------------------------------
-- WHAT IS BEING REFUTED, AND IT IS THE QUANTIFIER RATHER THAN THE
-- CLAIM.  Four statements read a registry entry the admission filters
-- hand back — two that its chain is ORDERED against the node counter,
-- two that the cells its chain names are PARKED below its floor — and
-- every one of them quantifies the state freely, with no premise about
-- the registry at all.  A registry is an ordinary field of that state,
-- so the free form says every entry ANY state could carry reads well.
--
-- THE SIBLING THAT ALREADY TAKES THE PREMISE IS WHAT MAKES THIS A
-- FINDING AND NOT A CURIOSITY.  `shareAdmit-strat` reads the same
-- entries through the same filter and takes `regStrat?` of the registry
-- as a hypothesis; its two neighbours read the other two properties of
-- the same entries and take nothing.  The refutations below say the
-- omission is not an economy: the missing premise is the whole
-- statement.
--
-- WHAT THEY DO NOT SAY, and the distinction is the reason to write it
-- down rather than patch the statements quietly.  Nothing here claims
-- the evaluator REACHES a registry of this shape — a chain is built
-- outward-in, so a built one is ordered by construction.  The states
-- below are hand-built, which is exactly what a free quantifier
-- licenses, and the repair is therefore a premise recording what
-- `register` makes rather than a weaker conclusion.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE WITNESS PROGRAM.  Two slots: slot nought is the share the
-- entries register on, and slot one is the input a stored cell names
-- when it is meant to name nothing.  Slot nought carries an observable,
-- which is scripted by no data, so it is a `shared` def reading no
-- input at all.
------------------------------------------------------------------

Γᵣ : Ctx 2
Γᵣ = obs natᵗ ∷ natᵗ ∷ []

d₀ : Closed Γᵣ (obs natᵗ)
d₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

slᵣ : Slots Γᵣ
slᵣ fzero        = shared d₀
slᵣ (fsuc fzero) = shared emptyᵉ

progᵣ : Closed Γᵣ natᵗ
progᵣ = ofᵉ (nat̂ 0 ∷ [])

-- the counter starts at nought, which is what the ord rows are read
-- against: `sched-init` mints no node before the root subscribe
schedᵣ : Sched Γᵣ
schedᵣ = sched-init progᵣ slᵣ

aᵣ : Arrival Γᵣ
aᵣ = record { tick = 0 ; ordinal = 0 ; source = 0 ; elemTy = obs natᵗ
            ; payload = input (fsuc fzero) ; isLast = false }

------------------------------------------------------------------
-- (1) THE ORDER HALF.  A chain whose TAIL names a node above the
-- counter: `pathOrd?` charges each frame at the read of the chain below
-- it, so the defect needs two frames — a bare `from-inner` over a sink
-- is charged at the sink's read, which is nought, and passes.
------------------------------------------------------------------

badOrdChain : Path Γᵣ (obs natᵗ) natᵗ
badOrdChain = take-f 0 ↠ (from-inner mergeAllᵒ 7 7 ↠ share-sink fzero)

-- LOAD-BEARING: it would read `true` if `pathRead` stopped at the head
-- frame, or if the head's charge were taken against the counter rather
-- than against the tail's read.
badOrdChain-disordered : pathOrd? 0 badOrdChain ≡ false
badOrdChain-disordered = refl

stOrd : EvalSt progᵣ
stOrd = record (st-init progᵣ)
  { registry = (0 , 0 , obs natᵗ , badOrdChain) ∷ [] }

-- LOAD-BEARING at both filters, and they are separate rows because
-- neither rearranges into the other: it would read `true` if the SLOT
-- filter dropped the entry on its source or its type, and again if the
-- ARRIVAL filter did.
shareAdmit-keeps-ord : all (λ rp → pathOrd? 0 (proj₂ rp))
                           (shareAdmit fzero (EvalSt.registry stOrd)) ≡ false
shareAdmit-keeps-ord = refl

chainsOf-keeps-ord : all (λ rc → pathOrd? 0 (proj₂ rc))
                         (chainsOf aᵣ stOrd) ≡ false
chainsOf-keeps-ord = refl

shareAdmit-ord-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
     all (λ rp → pathOrd? {n} {Γ} {lookup Γ i} {t} (Sched.nextNode sched) (proj₂ rp))
         (shareAdmit i (EvalSt.registry st)) ≡ true) →
  ⊥
shareAdmit-ord-absurd h with h {e = progᵣ} fzero schedᵣ stOrd
... | ()

cascade-admit-ord-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
     all (λ rc → pathOrd? {n} {Γ} {arrTy a} {t} (Sched.nextNode sched) (proj₂ rc))
         (chainsOf a st) ≡ true) →
  ⊥
cascade-admit-ord-absurd h with h {e = progᵣ} aᵣ schedᵣ stOrd
... | ()

------------------------------------------------------------------
-- (2) THE PARK HALF, AND IT IS INDEPENDENT.  It fails at a chain that
-- IS ordered, so this is a second finding rather than the first one
-- restated: one frame suffices, and the defect is in the STORE the
-- frame's node names rather than in the chain.  A node-table miss reads
-- `true`, so the cell has to be present and hold a queue naming an
-- input the sink's floor cannot cover.
------------------------------------------------------------------

badParkChain : Path Γᵣ (obs natᵗ) natᵗ
badParkChain = from-inner mergeAllᵒ 3 3 ↠ share-sink fzero

-- LOAD-BEARING: the row is only a separation while this reads `true`, and
-- the counter is four rather than the nought the order half reads at
-- because this chain NAMES node three -- the smallest counter that admits
-- it.  Reading it at nought would make it fail for the order half's reason
-- and the park finding would be the first one restated.
badParkChain-ordered : pathOrd? 4 badParkChain ≡ true
badParkChain-ordered = refl

stPark : EvalSt progᵣ
stPark = record (st-init progᵣ)
  { registry = (0 , 0 , obs natᵗ , badParkChain) ∷ []
  ; nodes    = (3 , mergeAll-st nothing 0 (input (fsuc fzero) ∷ []) false) ∷ [] }

-- LOAD-BEARING: it would read `true` at a queue naming an input below
-- the sink's index, and at any node id the chain does not name.
badParkChain-unparked : pathPark? badParkChain stPark ≡ false
badParkChain-unparked = refl

-- LOAD-BEARING, and this is what the two park statements actually
-- quantify over: it would read `true` if either latch cleared the node
-- table or dropped the entry on its way to the fan-out.
shareLatch-keeps-park : all (λ rp → pathPark? (proj₂ rp) (shareLatch fzero false stPark))
                            (shareAdmit fzero (EvalSt.registry stPark)) ≡ false
shareLatch-keeps-park = refl

cascadeLatch-keeps-park : all (λ rc → pathPark? (proj₂ rc) (cascadeLatch aᵣ stPark))
                              (chainsOf aᵣ stPark) ≡ false
cascadeLatch-keeps-park = refl

shareAdmit-park-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (i : Fin n) (fin : Bool) (st : EvalSt e) →
     all (λ rp → pathPark? {n} {Γ} {lookup Γ i} {t} (proj₂ rp) (shareLatch i fin st))
         (shareAdmit i (EvalSt.registry st)) ≡ true) →
  ⊥
shareAdmit-park-absurd h with h {e = progᵣ} fzero false stPark
... | ()

cascade-admit-park-absurd :
  (∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
     (a : Arrival Γ) (st : EvalSt e) →
     all (λ rc → pathPark? {n} {Γ} {arrTy a} {t} (proj₂ rc) (cascadeLatch a st))
         (chainsOf a st) ≡ true) →
  ⊥
cascade-admit-park-absurd h with h {e = progᵣ} aᵣ stPark
... | ()
