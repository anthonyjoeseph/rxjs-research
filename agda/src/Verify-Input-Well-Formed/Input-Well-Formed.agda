module Verify-Input-Well-Formed.Input-Well-Formed where

open import Data.Fin     using (Fin)
open import Data.List    using (concat)

open import Rx.Prim     using (Fuel)
open import Rx.Exp      using (Ctx)
open import Rx.SExp     using (inputˢ; plainᵛ)
open import Rx.Palette.SExp using (sexpPalette)
open import Rx.Slots sexpPalette using (Slots)
open import Rx.Elaborate using (elaborate)
open import Rx.Authored using (auth-elab; elab-mint; elab-toPlain)
open import Rx.Envelope.Decode using (decodeStream)
open import Rx.Evaluator.Builder sexpPalette using (evaluate↓)
open import Rx.Protocol using (protocol-init; runProtocol; Accepted)
open import Verify-Input-Well-Formed.Run-Well-Formed using (run-wellFormed)

-- THE SOURCE LEAF, WHICH IS THE INDUCTION'S BASE CASE READ BACK OUT.
-- One elaborated input, at any fuel, against any slot table the
-- PALETTE admits.
--
-- THE TABLE USED TO CARRY NO HYPOTHESIS AT ALL, on the reading that it
-- carries bare payloads and so nothing a script can forge.  That is
-- true of a SCRIPTED slot and false of a SHARED one: `subs-shared`
-- subscribes a definition straight down the consumer's path, so an
-- observable-typed slot hands the flattener a stream the elaboration
-- never built.  Probed.Share-Channel drives the automaton to `nothing`
-- through exactly that gap, with the author having written nothing
-- unusual.  `sexpPalette` is the repair and it is a hypothesis on
-- `ins` rather than on the program: a definition must carry its own
-- authorship (Rx.Authored), which bars the forged envelope and, as the
-- same file reads, admits the data-typed, the static observable-typed
-- and the dynamic observable-typed definitions alike.
input-wellFormed :
  ∀ {n} {Γ : Ctx n} (fuel : Fuel) (i : Fin n) (ins : Slots (plainᵛ Γ)) →
  Accepted (runProtocol protocol-init
             (decodeStream (concat (evaluate↓ fuel (elaborate (inputˢ i)) ins))))
input-wellFormed fuel i ins =
  run-wellFormed fuel (elaborate (inputˢ i)) ins
                 (auth-elab (elab-mint (elab-toPlain (inputˢ i))))
