-- WHAT AN INPUT SLOT'S ENVELOPE CARRIES IS A SEMANTICS QUESTION, NOT A
-- SPELLING, AND THE DECODE IS WHERE IT SURFACES (Anthony).  Reading the
-- protocol back out of the values narrows every consuming face to
-- programs that emit envelopes, and a face that QUANTIFIES over its
-- program crosses on that narrowing alone, since an abstract slot table
-- comes with it.  A face pinning a CONCRETE script does not: under
-- elaboration a slot sits at the envelope type, so a scripted hot slot
-- must deliver an envelope rather than a value, and nothing here builds
-- one.  `ofᵖ` shows a SOURCE emitting a single envelope holding `init`,
-- its payloads, a `close` at `exhausted` and a `complete` -- which is
-- also why dropping the stream's own `completeᵖ` below loses nothing --
-- but a hot slot delivering one value at a tick is a different shape,
-- and which shape the drivers owe is not this module's to decide.
-- State it in one shape and report it; do not invent one.
module Rx.Envelope.Decode where

open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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
decodeEvent {Γ = Γ} (inj₂ (inj₂ (inj₁ (tok , r)))) =
  close tok (decodeReason {Γ = Γ} r)
decodeEvent (inj₂ (inj₂ (inj₂ (inj₁ tok)))) = handoff tok
decodeEvent (inj₂ (inj₂ (inj₂ (inj₂ _))))   = complete

decodeEvents : ∀ {n} {Γ : Ctx n} {a}
             → List (Val Γ (instEventᵗ uniqᵗ a)) → List (InstEvent (Val Γ a))
decodeEvents []       = []
decodeEvents (e ∷ es) = decodeEvent e ∷ decodeEvents es

decodeEmit : ∀ {n} {Γ : Ctx n} {a}
           → Val Γ (instEmitᵗ uniqᵗ a) → InstEmit (Val Γ a)
decodeEmit {Γ = Γ} (evs , inst , src , k) =
  decodeEvents evs at inst from src as decodeKind {Γ = Γ} k

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

-- AND THE DECODE COMMUTES WITH CONCATENATION, WHICH IS WHAT THE
-- ACCEPTANCE FACE SPENDS IT ON.  A run is its subscribe burst followed
-- by its drain, and soundness composes the two segments once their
-- watermarks meet; with the protocol read off the values, that
-- composition happens one level up from where the stream is built, so
-- the two levels have to be shown to agree on `++` before `Sound-++`
-- can be applied at all.
decodeStream-++ : ∀ {n} {Γ : Ctx n} {a}
                  (xs ys : List (PlainEvent (Val Γ (instEmitᵗ uniqᵗ a))))
                → decodeStream (xs ++ ys)
                  ≡ decodeStream xs ++ decodeStream ys
decodeStream-++ []               ys = refl
decodeStream-++ (valueᵖ e ∷ xs)  ys = cong (decodeEmit e ∷_) (decodeStream-++ xs ys)
decodeStream-++ (completeᵖ ∷ xs) ys = decodeStream-++ xs ys
