module Rx.Envelope.Decode where

open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)

open import Rx.Prim using (PlainEvent; valueᵖ; completeᵖ;
  InstEmit; _at_from_as_; InstEvent; init; value; close; handoff; complete;
  CloseReason; cut; cutPending; exhausted;
  EmitKind; subscribe; delivery; plumbing)
open import Rx.Exp using (Ctx; Val; uniqᵗ)
open import Rx.Envelope using (closeReasonᵗ; emitKindᵗ; instEventᵗ; instEmitᵗ)

------------------------------------------------------------------
-- READING THE PROTOCOL BACK OFF THE VALUES IT NOW RIDES ON.
------------------------------------------------------------------

-- WHAT THE MACHINE PUSHES IS A VALUE AND WHAT THE SPEC READS IS AN
-- ENVELOPE, and this is the one place the two levels meet.  The
-- evaluator carries a `PlainEvent`, exactly as an rxjs pipeline does:
-- a payload, or the end of the stream.  The protocol vocabulary the
-- spec is written in — instant, source, kind, and the five events —
-- is ELABORATED into that payload, so it arrives as an ordinary tuple
-- of the object language rather than as something the machine minted.
--
-- Decoding is therefore total and structural: `Val` computes on the
-- encoding, so an envelope value IS the nested pair its type says it
-- is, and each arm below is the inverse of the constructor next to it
-- in `Rx.Envelope`.  Nothing is inferred and nothing can fail, which
-- is what makes the spec's statement transportable across the change
-- rather than restated for it.

decodeReason : ∀ {n} {Γ : Ctx n} → Val Γ closeReasonᵗ → CloseReason
decodeReason (inj₁ _)        = cut
decodeReason (inj₂ (inj₁ _)) = cutPending
decodeReason (inj₂ (inj₂ _)) = exhausted

decodeKind : ∀ {n} {Γ : Ctx n} → Val Γ emitKindᵗ → EmitKind
decodeKind (inj₁ _)        = subscribe
decodeKind (inj₂ (inj₁ _)) = delivery
decodeKind (inj₂ (inj₂ _)) = plumbing

decodeEvent : ∀ {n} {Γ : Ctx n} {a}
            → Val Γ (instEventᵗ uniqᵗ a) → InstEvent (Val Γ a)
decodeEvent (inj₁ tok)                      = init tok
decodeEvent (inj₂ (inj₁ v))                 = value v
decodeEvent (inj₂ (inj₂ (inj₁ (tok , r))))  = close tok (decodeReason r)
decodeEvent (inj₂ (inj₂ (inj₂ (inj₁ tok)))) = handoff tok
decodeEvent (inj₂ (inj₂ (inj₂ (inj₂ _))))   = complete

decodeEvents : ∀ {n} {Γ : Ctx n} {a}
             → List (Val Γ (instEventᵗ uniqᵗ a)) → List (InstEvent (Val Γ a))
decodeEvents []       = []
decodeEvents (e ∷ es) = decodeEvent e ∷ decodeEvents es

decodeEmit : ∀ {n} {Γ : Ctx n} {a}
           → Val Γ (instEmitᵗ uniqᵗ a) → InstEmit (Val Γ a)
decodeEmit (evs , inst , src , k) =
  decodeEvents evs at inst from src as decodeKind k

-- AND THE STREAM'S OWN END CARRIES NO ENVELOPE, WHICH IS THE ASYMMETRY
-- WORTH NAMING.  `completeᵖ` says the carrier stops; the protocol's own
-- `complete` is an event INSIDE an envelope and arrives as a payload
-- like any other.  So the end contributes no emit and the decode is a
-- filter rather than a map.
--
-- DROPPING IT LOSES NOTHING, AND THAT IS A FACT ABOUT THE ELABORATION
-- RATHER THAN A CONVENTION ADOPTED HERE.  An elaborated source emits a
-- single envelope holding `init`, its payloads, a `close` at
-- `exhausted` and a `complete` -- so every completion the protocol
-- automaton reads is already inside a value, and the carrier's end is
-- the rxjs-level signal beside it.  Were the two independent, this
-- clause would have to SYNTHESISE an emit and there would be no
-- instant to give it.
decodeStream : ∀ {n} {Γ : Ctx n} {a}
             → List (PlainEvent (Val Γ (instEmitᵗ uniqᵗ a)))
             → List (InstEmit (Val Γ a))
decodeStream []               = []
decodeStream (valueᵖ e ∷ es)  = decodeEmit e ∷ decodeStream es
decodeStream (completeᵖ ∷ es) = decodeStream es
