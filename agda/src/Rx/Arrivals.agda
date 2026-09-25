-- A RUN CUT WHERE AN RXJS SUBSCRIBER'S BURSTS END: ONE ENTRY FOR THE
-- ROOT SUBSCRIBE, THEN ONE PER ARRIVAL.  The evaluator's own `Burst` is
-- finer than that -- `fold-root` makes one per delivery reaching the
-- root, so an arrival's cascade is several of them, and how many is a
-- property of the program's SHAPE: an operator built from a flattener
-- delivers more often than the program under it, and a per-`Burst`
-- comparison would line up deliveries no subscriber can tell apart.
-- One arrival is what the subscriber cannot see inside of, so that is
-- the unit the top line compares in.
--
-- READ OFF THE DERIVATION RATHER THAN RECOMPUTED.  `evaluate!` builds
-- the relation's witness, and each `drain-step` in it names the stream
-- its own arrival produced; nothing here runs the machine again.
module Rx.Arrivals where

open import Data.List    using (List; []; _∷_; concat)
open import Data.Product using (proj₂)

open import Rx.Prim    using (Fuel)
open import Rx.Exp     using (Ctx; Closed)
open import Rx.Slots   using (Slots)
open import Rx.Evaluator using (Burst)
open import Rx.Evaluator.Domain using (drain⇓; evaluate⇓;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Builder using (evaluate!)

drained : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {fuel sched st s}
        → drain⇓ {e = e} fuel sched st s → List (Burst Γ t)
drained drain-done                    = []
drained (drain-empty _)               = []
drained (drain-step {out = out} _ _ d) = concat out ∷ drained d

arrivalsOf : ∀ {n} {Γ : Ctx n} {t} {fuel} {e : Closed Γ t} {ins s}
           → evaluate⇓ fuel e ins s → List (Burst Γ t)
arrivalsOf (eval-run {out = out} _ d) = concat out ∷ drained d

arrivals↓ : ∀ {n} {Γ : Ctx n} {t} → Fuel → (e : Closed Γ t) → Slots Γ
          → List (Burst Γ t)
arrivals↓ fuel e ins = arrivalsOf (proj₂ (evaluate! fuel e ins))
