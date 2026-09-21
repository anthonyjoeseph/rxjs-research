module Verify-Input-Well-Formed.Input-Well-Formed where

open import Data.Fin     using (Fin)
open import Data.List    using (concat)

open import Rx.Prim     using (Fuel)
open import Rx.Exp      using (Ctx)
open import Rx.SExp     using (inputˢ; plainᵛ)
open import Rx.Slots using (Slots)
open import Rx.Elaborate using (elaborate)
open import Rx.Elaborated using (elab-mint; elab-toPlain)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (protocol-init; runProtocol; Accepted)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)

-- THE SOURCE LEAF, WHICH IS THE INDUCTION'S BASE CASE READ BACK OUT.
-- One elaborated input, at any fuel, against ANY slot table.
--
-- THE TABLE CARRIES NO HYPOTHESIS HERE, and that is `Rx.Slots` having
-- earned it rather than this file assuming it.  A `Slots` used to be
-- open at an observable-typed SHARED slot -- `subs-shared` subscribes a
-- definition straight down the consumer's path, so such a slot handed
-- the flattener a stream the elaboration never built, and Probed.
-- Share-Channel drives the automaton to `nothing` through exactly that
-- gap.  Both slot arms now carry `isData`, so no table is inhabited at
-- the type that gap needed and `Slots (plainᵛ Γ)` may be quantified
-- over bare.  What is left to say is about the ROOT, which is why
-- `run-wellFormed` takes an `Elabᵉ` and this leaf discharges it.
input-wellFormed :
  ∀ {n} {Γ : Ctx n} (fuel : Fuel) (i : Fin n) (ins : Slots (plainᵛ Γ)) →
  Accepted (runProtocol protocol-init
             (decodeStream (concat (evaluate↓ fuel (elaborate (inputˢ i)) ins))))
input-wellFormed fuel i ins =
  run-wellFormed fuel (elaborate (inputˢ i)) ins
                 (elab-mint (elab-toPlain (inputˢ i)))
