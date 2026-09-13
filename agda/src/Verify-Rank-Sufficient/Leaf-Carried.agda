------------------------------------------------------------------
-- WHAT THE WALK'S TWO EVALUATING ARMS OWE THE CARRIED REPORT.
--
-- Both are one fact twice: a term the machine EVALUATES is read by the
-- reading's own term clause before it is evaluated, and what comes out
-- carries no more than what went in.  The machine turns a `Tm` into a
-- `Val` at exactly two places in a subscribe — the literals of a
-- one-shot source and a fold's seed — and at both the value it obtains
-- lands somewhere the report is about: in the burst at the first, in
-- the store at the second.
--
-- WHY THEY ARE LEAVES AND NOT AN ASSEMBLY OVER ONE.  The shared
-- content is a coherence between `evalWith` and `rdᵗ` at the EMPTY
-- environment, and neither arm can be derived from it without the
-- reading's own arithmetic on top: the source arm needs the literal
-- list's join reassociated against `rdᵗˢ`, and the seed arm needs the
-- refold recursion's base case joined out of `foldGo`, which is a fact
-- about the iteration rather than about evaluation.  Stating the shared
-- half alone and passing it into two postulates would be the `-core`
-- shape the wiring law refuses, and stating it as a lemma nothing
-- consumes would leave it unwired.  So each arm states what it needs,
-- and the shared half is what discharging either one will find.
--
-- THE SECOND IS WHERE THE TWO BOUNDS MEET.  A fold's seed is written
-- into the STORE, so its obligation is denominated against the rank
-- rather than against the burst — and it is bounded here by the scan
-- term's own reading, which the entry invariant already puts under the
-- rank.  That is what lets the store half of the report ride a
-- quantity the descent preserves without the arm having to know it.
------------------------------------------------------------------
module Verify-Rank-Sufficient.Leaf-Carried where

open import Data.Fin using (Fin)
open import Data.List using (List; []; map)
open import Data.Nat using (_≤_)

open import Rx.Exp using (Ctx; Tm; Fn; Exp; _×ᵗ_; evalTm; scanᵉ)
open import Rx.Hop-Depth using (Rd₃; depthᵉ; depthᵛ; rdᵗˢ; ε)
open import Verify-Rank-Sufficient.Carried using (valsRd; _⊑_)

postulate
  -- a one-shot source delivers its literals, and the reading prices
  -- them at the join of their term readings
  --
  -- PROBED: `Probed.Carried-Leaf` — two points in a closed context, both
  --   with OBSERVABLE literals, since a data payload reads zero on the
  --   left and a row taken there could not have failed.  One flat list
  --   and one whose first literal nests a flattener, which is where the
  --   reading's own `suc` enters.  BOTH components are decided, and the
  --   count half is tight at each — two against two and three against
  --   three — so a literal list the reading undercharged by one delivery
  --   crosses.  Not covered: a literal mentioning an INPUT, so nothing
  --   here reaches the slot telescope.
  ofᵉ-carried : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd₃)
    (ts : List (Tm Γ [] [] [] u)) →
    valsRd ψ u (map (λ tm → evalTm tm) ts) ⊑ rdᵗˢ ψ ε ts

  -- a fold installs its seed, and the reading's fold clause starts its
  -- accumulator at that seed's own reading
  --
  -- PROBED: `Probed.Carried-Leaf` — two folds over a three-literal
  --   synchronous source, seeded with a live observable and with a
  --   flattened one, which is the deepest thing a seed can be.  Not
  --   covered: a seed whose reading involves an input, and no row runs
  --   the fold, so this says nothing about what the accumulator becomes.
  scan-seed-carried : ∀ {n} {Γ : Ctx n} {s u} (ψ : Fin n → Rd₃)
    (f : Fn Γ [] [] [] (u ×ᵗ s) u) (z : Tm Γ [] [] [] u)
    (b : Exp Γ [] [] [] s) →
    depthᵛ ψ u (evalTm z) ≤ depthᵉ ψ (scanᵉ f z b)
