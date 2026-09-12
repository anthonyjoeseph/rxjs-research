-- THE ACCUMULATOR DEEPENS ONE PER ARRIVAL, AND IT OVERTAKES THE TERM'S
-- OWN READING INSIDE SIX UNITS OF FUEL.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- ONE PROGRAM, SIX FUELS, AND THE ONE AXIS THAT IS NOT SYNTAX.  The
-- source here is a recursion rather than a literal, so how many
-- deliveries happen is set by the DRAIN and not by the term: the
-- program holds still at a hop reading of 3 across every row below,
-- while what the run hands out reads the fuel plus one.  One hop per
-- unit of fuel, against a term reading constant in it.
--
-- SO A RANK READ OFF THE PROGRAM ALONE DOES NOT BOUND THIS, AND THE
-- ROWS NOW EXHIBIT THAT RATHER THAN ARGUING TOWARDS IT.  The
-- accumulator is stored across arrivals and deepened by one flattener
-- at each, the arrivals are paid for out of fuel, and fuel is not a
-- property of the term — so for a fixed program the readings are
-- unbounded while a term-only rank stands still.  THREE units is where
-- that stops being a rate argument: the run's output reads 4 against
-- the term's 3, and at six it reads more than twice it.
--
-- WHICH IS WHY AN ENTRY IS NOT TAKEN OFF THE PROGRAM ALONE.  A cascade
-- re-seeds per arrival, at the value it carries joined with the store's
-- own reading, and the value's reading is exactly what these rows
-- measure — one `mergeAllᵉ` layer per application, which `depthᵉ` counts
-- as one hop.  So the rate they establish is the rate the arrival's own
-- entry already grants, one for one.  These rows are both the reason the
-- re-seed is there and the check that it moves at the rate it must.
--
-- WHERE THE SHELF IS STILL UNPAID.  Nothing above says the OPERATOR
-- shelf is paid for: it is handed an arbitrary triple satisfying the
-- entry invariant rather than one the machine minted, so no re-seed
-- reaches it.  `Refuted.Rank-Entry` holds the rank at that invariant's
-- own floor and reaches the dry close inside one subscribe frame, off
-- the smallest operator that subscribes an inner at all.
--
-- WHAT IS NOT COVERED, AND IT IS WHERE THE DRAIN LEAF IS STILL OPEN.
-- One delivery lands per arrival here, so every hop counted below is
-- paid for by a fresh entry; no row reaches a burst delivering many
-- times inside ONE cascade, which is the growth no entry sees however it
-- is denominated.  One recursion shape and one flattening layer in the
-- step; the fuels are small because each row re-walks the whole drain,
-- so what is established is the RATE.
--
-- TARGET: drain-dry-free @0b82eb
module Probed.Fuel-Growth where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Fuel; InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  ofᵉ; emptyᵉ; scanᵉ; mergeAllᵉ; μᵉ; varᵉ; deferᵉ;
  strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; drain; subscribeE;
  rootWitness; root; sched-init; st-init)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Verify-Rank-Sufficient using (drain-dry-free)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE QUANTITY THE ROWS MOVE: how deep the values a run hands out read,
-- in the currency the rank itself is denominated in.  Two payloads
-- abreast cost what the deeper costs, which is the clause the measure
-- itself uses, so this is the friendliest reading available and the
-- claim being instantiated is an upper bound.
----------------------------------------------------------------------

evHop : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
        List (InstEvent (Closed Γ u)) → ℕ
evHop ψ []             = 0
evHop ψ (value v ∷ es) = depthᵉ ψ v ⊔ evHop ψ es
evHop ψ (_ ∷ es)       = evHop ψ es

carried : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃) →
          Stream Γ (obs u) → ℕ
carried ψ []         = 0
carried ψ (em ∷ ems) = evHop ψ (InstEmit.events em) ⊔ carried ψ ems

entry : ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ) →
  Stream Γ t × Sched Γ × EvalSt e
entry e ins =
  subscribeE (rootWitness e ins) e root 0 0 (sched-init e ins)
    (st-init e)

-- the fuel is a PARAMETER here rather than a module constant, which is
-- the whole instrument: every other quantity a row names is fixed by
-- the program, and this is the one axis left to move
drainAt : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) (ins : Slots Γ) → Stream Γ t
drainAt f e ins = drain f 1 (proj₁ (proj₂ (entry e ins))) (proj₂ (proj₂ (entry e ins)))

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE PROGRAM.  The step hands its accumulator straight back inside one
-- flattening layer, so each application reads one deeper than the last;
-- the source is `repeat`, the smallest recursion that goes on
-- delivering, so how many applications happen is the drain's business
-- and not the term's.  Together they are the one shape where a run's
-- own output outgrows every reading of the program that produced it.
----------------------------------------------------------------------

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

recur : Closed Γ₀ natᵗ
recur = μᵉ (mergeAllᵉ nothing
  (ofᵉ ( strmᵗ (ofᵉ (nat̂ 1 ∷ []))
       ∷ strmᵗ (deferᵉ (varᵉ (here refl)))
       ∷ [])))

fold : Closed Γ₀ (obs natᵗ)
fold = scanᵉ step (strmᵗ emptyᵉ) recur

----------------------------------------------------------------------
-- THE FIXED SIDE.  The term's hop reading, which every row below holds
-- constant — that is what makes the moving one mean something, and it
-- is the SAME quantity the moving rows report.
----------------------------------------------------------------------

ψ₀ : Fin 0 → Rd₃
ψ₀ = slotRd ins₀

_ : depthᵉ ψ₀ fold ≡ 3                               -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE MOVING SIDE.  Six drains of the SAME run, differing in fuel
-- alone.  Each is LOAD-BEARING and each could have failed in either
-- direction: a reading that stalled would say the accumulator is not
-- what deepens, and a reading that jumped would say the rate is not one
-- per arrival.  It is one per arrival, exactly, and the fuel is the
-- number of arrivals.
----------------------------------------------------------------------

_ : carried ψ₀ (drainAt 1 fold ins₀) ≡ 2           -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (drainAt 2 fold ins₀) ≡ 3           -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (drainAt 3 fold ins₀) ≡ 4           -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (drainAt 4 fold ins₀) ≡ 5           -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (drainAt 5 fold ins₀) ≡ 6           -- LOAD-BEARING
_ = refl

_ : carried ψ₀ (drainAt 6 fold ins₀) ≡ 7           -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE LEAF, INSTANTIATED PAST THE CROSSING.  It is green at fuel six,
-- where the run's output reads 7 against the term's 3 — so the row does
-- not merely sit inside the region the leaf quantifies over, it sits in
-- the part of that region a term-only rank has already lost.  What it
-- still cannot reach is a burst: one delivery per arrival is what keeps
-- a row affordable at all.
----------------------------------------------------------------------

drF : Confirms (drain-dry-free 6 1
  (proj₁ (proj₂ (entry fold ins₀))) (proj₂ (proj₂ (entry fold ins₀))) Below)
drF = refl
