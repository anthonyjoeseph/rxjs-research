module Verify-Input-Well-Formed.Input-Well-Formed where

open import Data.Fin     using (Fin)
open import Data.List    using (concat)

open import Rx.Prim     using (Fuel)
open import Rx.Exp      using (Ctx)
open import Rx.SExp     using (inputˢ; plainᵛ)
open import Rx.Slots    using (Slots)
open import Rx.Elaborate using (elaborate)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (protocol-init; runProtocol; Accepted)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)

-- THE SOURCE LEAF, WHICH IS THE INDUCTION'S BASE CASE READ BACK OUT.
-- One elaborated input, at any fuel, against any slot table -- and the
-- table carries bare payloads, so there is no hypothesis on `ins` and
-- nothing a script can forge.
input-wellFormed :
  ∀ {n} {Γ : Ctx n} (fuel : Fuel) (i : Fin n) (ins : Slots (plainᵛ Γ)) →
  Accepted (runProtocol protocol-init
             (decodeStream (concat (evaluate↓ fuel (elaborate (inputˢ i)) ins))))
input-wellFormed fuel i ins =
  run-wellFormed fuel (elaborate (inputˢ i)) ins
