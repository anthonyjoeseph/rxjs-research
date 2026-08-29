-- ══════════════════════════════════════════════════════════════════
-- THE SUBSCRIBE SIDE AT THE LIVE REGISTRY COUNT IS FALSE, so the width
-- factor the caps face consumes cannot be traded for one that computes.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE` notes.
--
-- WHAT THE STATEMENT SAID.  The subscribe descent under its subject, its
-- rootward path, the store it starts from, and the number of LIVE
-- registrations times one syntactic charge.  The attraction is that
-- every term of it reduces: the increment the caps face actually carries
-- is sealed and no row prints a verdict on it, so a bound reading the
-- registry instead would be the same claim in a form a probe can pin.
--
-- WHY IT LOOKED RIGHT.  A proven inequality does sit between the two --
-- a width of the syntactic charge is under the increment whenever that
-- width is under the cap, and the registry length IS under the cap, by
-- the count conjunct of the caps predicate.  So the live-count form is
-- a genuine strengthening, arrived at by a real proof, and it reads as
-- the harmless direction.
--
-- WHERE IT BREAKS.  A cap is a CEILING on the registry and the descent
-- is charged against the ceiling; the live count is a reading of the
-- registry NOW, and at the state a root subscribe is entered from there
-- is nothing registered at all.  The whole width term is then zero and
-- the bound collapses to the store's own base, while the descent is
-- whatever the program's folds spend.  So the strengthening is not a
-- near thing: on the drain family it loses by more than a factor of
-- three.
--
-- THE WITNESS is the one that already refuted the single-charge form --
-- `progU 20 2` at `insT 1 2 0`, read at the root subscribe -- which
-- makes the pair of figures directly comparable.  Eighty-one against
-- twenty-four, where the single charge managed seventy-four.  Dropping
-- the count is a loss of seven; reading the count at the live registry
-- is a loss of fifty-seven, so the live reading is WORSE than the form
-- that carries no width factor at all, at this state.
--
-- WHAT THIS DOES NOT SHOW.  Nothing here touches the increment form the
-- caps face consumes, which the same witness clears.  What died is the
-- plan to split that statement into a computable leaf plus a widening:
-- the widening runs from the leaf UP to the increment, so the leaf is
-- the stronger statement and has to be true on its own, and it is not.
-- A leaf must read the cap, and the cap is what does not compute.
-- ══════════════════════════════════════════════════════════════════
module Refuted.Nest-Depth-Live-Reg where

open import Data.Empty using (⊥)
open import Data.List using (length)
open import Data.Nat using (ℕ; _+_; _*_; _≤_)
open import Data.Nat.Properties using (≤⇒≤ᵇ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; natᵗ)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; sched-init; st-init; root; budgetAt)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Slots using (Slots)

open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; progU; insT)
open import Verify-Budget-Sufficient.Caps-Depth using (depthE)
open import Verify-Budget-Sufficient.Nest-Store
  using (pathNestD; storeNestMax; nestSyn)

-- the crossing point: the mergeAll drain under twenty nested folds
prog : Closed Γ₂ natᵗ
prog = progU 20 2

slots : Slots Γ₂
slots = insT 1 2 0

sd : Sched Γ₂
sd = sched-init prog slots

st : EvalSt prog
st = st-init prog

-- pinned rather than written inline at both uses: `root` leaves its
-- indices to be solved, and the measure's use alone does not fix them
κ : Path Γ₂ natᵗ natᵗ
κ = root

descent : ℕ
descent = depthE (budgetAt prog slots 0) prog κ 0 0 sd st

liveReg : ℕ
liveReg = nestDᵉ prog + pathNestD κ + storeNestMax sd st
          + length (EvalSt.registry st) * nestSyn prog slots

-- THE FIGURES, PINNED.  Spelled out rather than left inline so that any
-- repair moving either measure fails here, naming the number, instead of
-- quietly turning the crossing into an equality.
liveDescent≡81 : descent ≡ 81
liveDescent≡81 = refl

liveReg≡24 : liveReg ≡ 24
liveReg≡24 = refl

nest-live-reg-absurd : descent ≤ liveReg → ⊥
-- `descent ≤ᵇ liveReg` reduces to `false`, so `T` of it IS the empty type
nest-live-reg-absurd h = ≤⇒≤ᵇ h
