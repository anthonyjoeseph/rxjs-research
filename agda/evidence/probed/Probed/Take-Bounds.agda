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
-- TARGET: cascade-take-spends @87e3af
module Probed.Take-Bounds where

open import Data.Fin using (zero)
open import Data.List using (_∷_; [])
open import Data.Sum using (inj₁; inj₂)
open import Data.Vec using ([]; _∷_)     -- contexts are Vecs; ∷/[] overload per type
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat using (s≤s; z≤n)
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Data.Unit using (⊤)
open import Data.Sum using (_⊎_)

open import Rx.Prim using (after_,_; hot)
open import Rx.Evaluator using (Arrival; Sched; sched-next)
open import Rx.Evaluator.Builder using (cascade!)
open import Rx.Exp using (Ctx; natᵗ; Closed; nat̂; input; takeᵉ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Readme-Theorems using (oneSlot; emitValues)
open import Verify-Take-Bounds using (take-zero-drain-silent;
  cascade-take-spends; rootRun)

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
-- 3.  ONE ARRIVAL'S CASCADE, AGAINST A TAKE THAT IS ABOUT TO CUT.
-- The tier's monster is about a single arrival rather than the whole
-- drain, so this row runs the root subscribe, pops what the frame left
-- scheduled, and cascades exactly that one arrival.  The take is at ONE
-- against a source with two values, so the node is holding a budget the
-- cascade must actually spend: LOAD-BEARING on the account, since a
-- cascade that delivered without charging, or charged without
-- delivering, misses the sum at this very program.
--
-- THE ARRIVAL IS NOT WRITTEN DOWN, IT IS FORCED.  `sched-next` computes
-- at a concrete schedule, so binding its result through a `refl`
-- hypothesis makes Agda supply the arrival and the residual schedule --
-- a hand-written pair would be a state the evaluator need never reach.
----------------------------------------------------------------------

sched₀ : Sched Γ₁
sched₀ = proj₁ (proj₂ (rootRun 1 src₁ slots₁))

popped : Arrival Γ₁ × Sched Γ₁
popped = go (sched-next sched₀) refl
  where
    go : (x : ⊤ ⊎ (Arrival Γ₁ × Sched Γ₁)) →
         sched-next sched₀ ≡ x → Arrival Γ₁ × Sched Γ₁
    go (inj₁ _) ()
    go (inj₂ p) _ = p

row-cascade : Confirms (cascade-take-spends {e = takeᵉ (nat̂ 1) src₁} 0
  (s≤s z≤n) (proj₂ (cascade! (proj₁ popped) 1 (proj₂ popped)
                             (proj₂ (proj₂ (rootRun 1 src₁ slots₁))))))
row-cascade = s≤s z≤n
