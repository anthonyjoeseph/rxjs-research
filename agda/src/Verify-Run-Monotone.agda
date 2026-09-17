-- MORE FUEL ONLY EXTENDS A RUN.  A fact about the machine and nothing
-- else: the statement mentions `evaluate↓` and two fuels, and a
-- concrete program decides it, which makes it the one claim on this
-- side of the repo that is neither about the syntax nor about a domain.
--
-- AND IT IS TWO PROPERTIES IN ONE EQUATION, which is what makes it
-- worth stating rather than assuming.  A remainder EXISTS, so the
-- longer run reaches at least as far; and the shorter run is an honest
-- PREFIX of it, so nothing already emitted is renumbered, re-minted or
-- re-ordered when the fuel goes up.  The second is the one a machine
-- can break: every id in the answer is minted during the run, so a
-- longer run that restarted its counters would still be longer.

module Verify-Run-Monotone where

open import Data.List using (_++_)
open import Data.Nat using (_≤_)
open import Data.Product using (∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (Slots)

postulate
  -- PROBED: `Probed.Run-Monotone` reaches this conclusion at two
  --   programs and three fuel gaps.  One row grows — the remainder is
  --   pinned non-empty, so the EXISTENCE half is decided and not merely
  --   the prefix half — and two saturate, where the remainder is pinned
  --   EMPTY and a renumbered instant, a re-minted provenance or a
  --   re-ordered burst is the only available failure.  One of those two
  --   sits past a delivery, so the drain has stepped in the shorter run
  --   and its resumption ordinal is part of what is decided.  Not
  --   reached: any flattening program, any cold source, a source firing
  --   at more than one tick, and a fuel gap wider than the program's
  --   own horizon.
  run-monotone :
    ∀ {n} {Γ : Ctx n} {t} (fuel₁ fuel₂ : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) → fuel₁ ≤ fuel₂ →
    ∃ λ rest → evaluate↓ fuel₂ e ins ≡ evaluate↓ fuel₁ e ins ++ rest
