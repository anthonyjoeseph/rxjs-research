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
--
-- AND THE BODY CANNOT BE WRITTEN IN TODAY'S PLAIN TREE, WHICH IS A
-- QUESTION FOR ANTHONY AND NOT A GRIND.  Every envelope this
-- elaboration builds needs two things the object language has no way to
-- say: the token of the cascade the emit belongs to, and a fresh source
-- token for a registration coming alive.  Neither is derivable inside a
-- program.  A `liftᵉ` state advances per emit and so cannot tell two
-- emits of one cascade from two cascades, and `uniq̂` is a literal,
-- which is exactly the forgery the palette layer rules out; both are
-- properties of the RUN, held by the scheduler.  The TypeScript mirror
-- says the same thing outright — its operators read `currentInstant`
-- and `mintSourceId` off the driver, which is its scheduler — so an
-- Agda elaboration that produced them from nothing would be the one
-- divergence the mirroring law forbids.  What the body needs is
-- therefore a plain-tree FORMER for each read, and a new former decides
-- what every theorem above quantifies over, so it is not an agent's to
-- invent.  Until it is ruled on, the demotion this elaboration exists
-- to permit cannot land either: the evaluator can stop RETURNING
-- envelopes only once a program can build one.

postulate
  toPlain : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ Θ t
          → Exp (plainᵛ Γ) (plainᶜ Δᵍ) (plainᶜ Δ) (plainᶜ Θ) (machineEmitᵗ (plainᵗ t))
