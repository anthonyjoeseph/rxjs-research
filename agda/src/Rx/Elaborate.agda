module Rx.Elaborate where

open import Data.List using (List)

open import Rx.Exp      using (Ty; Ctx; Exp)
open import Rx.Envelope using (machineEmitᵗ)
open import Rx.SExp     using (SExp; plainᵗ; plainᶜ; plainᵛ)

------------------------------------------------------------------
-- The elaboration: one simul program down into one plain program.
------------------------------------------------------------------

-- THE ONE PLACE THE ENVELOPE IS WRITTEN, WHICH IS WHAT MAKES THE
-- PALETTE ARGUMENT A PROOF RATHER THAN A CONVENTION.  A simul program
-- names no token, so every instant and every source appearing in an
-- elaborated program is put there here; and since the evaluator runs
-- only the plain tree, the elaboration is also the sole route by which
-- a shipped operator's protocol behaviour reaches a run.  Anything an
-- author could do to an envelope, they did by choosing a former.
--
-- IT IS A LEAF TODAY AND THE SIGNATURE IS THE CLAIM.  What the body
-- will be is per-former plumbing over the type translation; what the
-- type already fixes is that a simul program at the author's payload
-- becomes a plain program at the machine envelope over the TRANSLATED
-- payload, in the pointwise-translated contexts — so a nested
-- observable's own emits are envelopes too, which is the property the
-- flatteners' protocol traffic is stated in.

postulate
  toPlain : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ Θ t
          → Exp (plainᵛ Γ) (plainᶜ Δᵍ) (plainᶜ Δ) (plainᶜ Θ) (machineEmitᵗ (plainᵗ t))
