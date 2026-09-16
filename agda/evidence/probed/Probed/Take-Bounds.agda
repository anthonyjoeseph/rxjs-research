----------------------------------------------------------------------
-- TAKE AT ZERO, AND WHAT THE DRAIN DOES AFTERWARDS.
--
-- WHAT A ROW HERE DECIDES.  A take at zero emits its completion burst
-- and subscribes NOTHING, so no chain is ever registered against any
-- source -- while the slots go on seeding arrivals regardless, and the
-- drain goes on popping them.  The claim is that those arrivals reach
-- no frame, and it is a claim about REGISTRATION rather than about a
-- budget: the node this program's take would have spent is never
-- minted, so there is no account for the drain to be held to.
--
-- AND THE WHOLE STATEMENT COMPUTES.  `drainRest` is the builder's own
-- output read back and nothing on the path is postulated, so a row that
-- failed would be a refutation rather than an unproven goal.
--
-- AND THE ROWS ARE CHOSEN SO THE DRAIN ACTUALLY RUNS.  A source with
-- nothing pending leaves the drain empty at its first arrival and the
-- equation holds for a reason that has nothing to do with the take, so
-- each row below scripts values the drain must pop and discard.
--
-- NOT REACHED: every flattening program; any type other than `natᵗ`; a
-- COLD source; a take at a term that is not a literal, since the count
-- is read through `evalTm` and no row here makes that step non-trivial.
----------------------------------------------------------------------

-- TARGET: take-zero-drain-silent @f5150c
-- TARGET: root-regs @2e174b
-- TARGET: chains-take-at @e3870b
-- TARGET: cascade-keeps-regs @80d45b
-- TARGET: stepFrame-quiet @de928f
module Probed.Take-Bounds where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Bool using (false)
open import Data.Nat using (s≤s; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Vec using ([]; _∷_)     -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Data.List.Relation.Unary.All as All

open import Rx.Prim using (after_,_; hot)
open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; input; takeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator using (Sched; EvalSt; Arrival; sched-next; take-f;
  root; arrVal)
open import Rx.Evaluator.Builder using (evaluate↓; cascade!; stepFrame!)
open import Readme-Theorems using (oneSlot; emitValues)
open import Verify-Take-Bounds using (take-zero-drain-silent; root-regs;
  take-here; rootRun; RegTakeAt; chains-take-at; cascade-keeps-regs;
  stepFrame-quiet; nodeBudget)

open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- 1.  TWO VALUES ARRIVE AND THE TAKE IS AT ZERO.  LOAD-BEARING on the
-- registration claim: both arrivals are live in the schedule the frame
-- hands on, so the drain pops them both.  A drain that reached a frame
-- would emit them, and the row fails.
----------------------------------------------------------------------

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ []

src₁ : Closed Γ₁ natᵗ
src₁ = input zero

slots₁ : Slots Γ₁
slots₁ = oneSlot (scripted (hot ((after 0 , 5) ∷ (after 0 , 7) ∷ [])))

row-zero-sync : Confirms (take-zero-drain-silent 6 src₁ slots₁)
row-zero-sync = refl

----------------------------------------------------------------------
-- 2.  AND ONE THAT ARRIVES LATE, which is the shape that separates the
-- registration claim from an accident of the subscribe frame.  The
-- first row's arrivals are pending at tick zero and could in principle
-- be absorbed where the frame runs; this one's second value lands at a
-- later tick and can only be popped by the drain.
----------------------------------------------------------------------

slots₂ : Slots Γ₁
slots₂ = oneSlot (scripted (hot ((after 0 , 5) ∷ (after 3 , 7) ∷ [])))

row-zero-late : Confirms (take-zero-drain-silent 6 src₁ slots₂)
row-zero-late = refl

----------------------------------------------------------------------
-- NON-VACUITY, and it is what makes the rows rows at all.  Pinned
-- beside each is what the SAME program emits with the take removed: the
-- drain's silence is a fact about this take and not about a schedule
-- that had nothing in it.  Without these, a source the evaluator never
-- ran at all would satisfy every row above.
----------------------------------------------------------------------

sync-uncut : emitValues (evaluate↓ 6 src₁ slots₁) ≡ 5 ∷ 7 ∷ []
sync-uncut = refl

late-uncut : emitValues (evaluate↓ 6 src₁ slots₂) ≡ 5 ∷ 7 ∷ []
late-uncut = refl

cut-emits-nothing : emitValues (evaluate↓ 6 (takeᵉ (nat̂ 0) src₁) slots₁) ≡ []
cut-emits-nothing = refl

----------------------------------------------------------------------
-- 3.  WHAT THE ROOT SUBSCRIBE LEAVES IN THE REGISTRY.  The account is
-- about chains that pass the take's frame, and the drain reads its
-- chains out of the registry -- so the whole of it rests on the root
-- frame having registered nothing else.  This row COMPUTES that
-- registry at a real program and inhabits the predicate by hand:
-- LOAD-BEARING, since a registration grown from any other path has no
-- `take-here` to close it and the row does not typecheck.
----------------------------------------------------------------------

row-regs : Confirms (root-regs 0 src₁ slots₁)
row-regs = take-here All.∷ All.[]

----------------------------------------------------------------------
-- 4.  AND WHAT THE FIRST ARRIVAL DOES TO THE REGISTRY.  The account is
-- stated over chains that pass the take's frame, and the drain visits a
-- fresh state at every arrival, so the condition has to survive a
-- cascade and has to be readable back off the chain filter.  These rows
-- run the root subscribe, pop what it left scheduled, and check both at
-- a take with budget left over: LOAD-BEARING, since a cascade that
-- registered a chain grown from any other path leaves the row with no
-- `take-here` to close it.
--
-- NEITHER THE ARRIVAL NOR THE RESIDUAL SCHEDULE IS WRITTEN DOWN, THEY
-- ARE FORCED.  `sched-next` computes at a concrete state, so binding it
-- through a `refl` hypothesis makes Agda supply both -- a hand-written
-- arrival would be one the evaluator need never reach.
--
-- NOT REACHED: any flattening program, which is the one shape that can
-- register a chain mid-cascade at all, so these rows say nothing about
-- the arm where the claim could fail.
----------------------------------------------------------------------

sched₀ : Sched Γ₁
sched₀ = proj₁ (proj₂ (rootRun 2 src₁ slots₁))

st₀ : EvalSt (takeᵉ (nat̂ 2) src₁)
st₀ = proj₂ (proj₂ (rootRun 2 src₁ slots₁))

popped : Arrival Γ₁ × Sched Γ₁
popped = go (sched-next sched₀) refl
  where
    go : (x : ⊤ ⊎ (Arrival Γ₁ × Sched Γ₁)) →
         sched-next sched₀ ≡ x → Arrival Γ₁ × Sched Γ₁
    go (inj₁ _) ()
    go (inj₂ p) _ = p

regs₀ : RegTakeAt 0 st₀
regs₀ = take-here All.∷ All.[]

row-chains : Confirms (chains-take-at 0 (proj₁ popped) st₀ regs₀)
row-chains = take-here All.∷ All.[]

row-cascade : Confirms (cascade-keeps-regs {e = takeᵉ (nat̂ 2) src₁} 0 regs₀
  (proj₂ (cascade! (proj₁ popped) 1 (proj₂ popped) st₀)))
row-cascade = take-here All.∷ All.[]

----------------------------------------------------------------------
-- 5.  AND ONE FRAME, WHICH IS THE ARM THE ACCOUNT BOTTOMS OUT IN.
--
-- The claim is that a frame emits no value the take node did not pay
-- for, and this row runs the take's OWN frame at a node holding two: it
-- emits one and the node comes back holding one, so the sum is TIGHT
-- rather than slack.  LOAD-BEARING -- a frame that emitted without
-- charging, or charged without emitting, misses it at this program, and
-- the two figures are pinned below so the tightness is legible.
--
-- NOT REACHED, AND THIS IS THE WHOLE OF THE RESIDUAL RISK: the two
-- FLATTENER arms.  `from-inner` is excluded from this builder by
-- `srcFrame` outright, and `thru-outer` needs a program whose value is
-- itself an observable -- which is where an inner subscribe can mint a
-- node and splice a burst into the instant, and so where the claim
-- would be false if it is.  Neither `map-f` nor `scan-f` is reached
-- either, though both are local and neither can emit what it was not
-- given.
----------------------------------------------------------------------

row-frame : Confirms (stepFrame-quiet {e = takeᵉ (nat̂ 2) src₁}
  {f = take-f 0} {κ = root {lo = 1}} 0 (s≤s z≤n)
  (proj₂ (stepFrame! slots₁ 1 0 (take-f 0) tt (root {lo = 1})
            (arrVal (proj₁ popped) ∷ []) false sched₀ refl st₀)))
row-frame = s≤s z≤n

st₁ : EvalSt (takeᵉ (nat̂ 2) src₁)
st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₁
        (stepFrame! slots₁ 1 0 (take-f 0) tt (root {lo = 1})
           (arrVal (proj₁ popped) ∷ []) false sched₀ refl st₀)))))

-- NON-VACUITY: the node's figure before and after, so the row's sum
-- is visibly tight rather than slack on either side.
frame-spends : nodeBudget 0 st₀ ≡ 2
frame-spends = refl

frame-spent : nodeBudget 0 st₁ ≡ 1
frame-spent = refl
