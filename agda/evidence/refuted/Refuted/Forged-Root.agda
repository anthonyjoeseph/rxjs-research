-- A COUNTEREXAMPLE TO `run-wellFormed` AS IT WAS STATED, AND THE
-- REASON IT NOW CARRIES AN ELABORATION PREMISE.
--
-- `Rx.Simul-Slots` closed the forgery channel in the SLOT TABLE, by
-- making a shared definition an `SExp` that reaches the evaluator only
-- through `elaborateSpec`.  That left the ROOT PROGRAM untouched, and no
-- condition on slots could ever have reached it.  `run-wellFormed` quantified over an arbitrary
-- `e : Closed Γ (machineEmitᵗ a)` -- its own header said "every run of
-- every ELABORATED program" while its statement said every run of every
-- PLAIN one -- and the gap is inhabited by the same three lines that
-- inhabit the table's:
--
--   mintᵉ (ofᵉ (instEmitᵛ nilᵗ tok tok deliveryᵛ ∷ []))
--
-- a `delivery` whose source no `init` ever enlisted, standing at the
-- root rather than in a slot.  `settle` seeds owed from `countIn s []`,
-- `payOwed` underflows, and the automaton rejects.  No slot table is
-- involved: the table below is a single ordinary scripted input.
--
-- WHAT IT COST TO FIX: one premise, `Elabᵉ e` -- ONE FORMER DEEP,
-- since the definition side is answered by the telescope and not by a
-- predicate over the whole of `Exp` -- threaded through
-- `subscribe-shaped`, `cascade-shaped`, `drain-shaped` and
-- `run-wellFormed⇓`.  `elaborated-accepted` discharges it at the only
-- call site, since its program is `elaborateSpec κ e` and
-- `elab-mint (elab-toPlain κ e)` is exactly that.
--
-- WHY IT WAS NOT FOUND EARLIER.  The old comment on `run-wellFormed`
-- gave the reason it was wrong as the reason it was right: "quantified
-- over the plain tree rather than over `SExp`, because the two leaves
-- know nothing of the author's syntax."  The leaves do need to know --
-- not the author's syntax, but that there IS one.
module Refuted.Forged-Root where

open import Data.Fin using (zero)
open import Data.List using ([]; _∷_; concat)
open import Data.Maybe using (Maybe; nothing)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; natᵗ; Closed; ofᵉ; mintᵉ; nilᵗ; varᵗ)
open import Rx.SExp using (Kinds; scriptedᵏ; plainᵏ; emitᵗ)
open import Rx.Envelope using (instEmitᵛ)
open import Rx.Elaborate using (deliveryᵛ)
open import Rx.Slots using (Slots; scripted)
open import Rx.Envelope.Decode using (decodeSpec)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Protocol using (ProtocolSt; protocol-init; runProtocol)

Γ₁ : Ctx 1
Γ₁ = natᵗ ∷ⱽ []ⱽ

-- the slot is fed by a SCRIPT, which is the kind that stands at the
-- bare payload -- so nothing the table supplies carries an envelope
κ₁ : Kinds 1
κ₁ = scriptedᵏ ∷ⱽ []ⱽ

-- an ordinary table: one scripted input, nothing shared, nothing forged
ins₁ : Slots (plainᵏ Γ₁ κ₁)
ins₁ zero = scripted (cold (1 ∷ []) ((after 0 , 2) ∷ []))

-- the forgery is the PROGRAM
forged : Closed (plainᵏ Γ₁ κ₁) (emitᵗ natᵗ)
forged = mintᵉ (ofᵉ (instEmitᵛ nilᵗ (varᵗ (here refl)) (varᵗ (here refl))
                                deliveryᵛ ∷ []))

S : Maybe ProtocolSt
S = runProtocol protocol-init
      (decodeSpec {Γ = plainᵏ Γ₁ κ₁} {a = natᵗ}
        (concat (evaluate↓ 60 forged ins₁)))

saw-forged-root : S ≡ nothing
saw-forged-root = refl
