-- THE IMPL SIDE OF THE TOP LINE, AND EVERYTHING HERE IS FREE.  The
-- theorem runs two pipelines over one author program: the SPEC side
-- (`elaborateSpec`, `embedSlotsSpec`, `decodeSpec`, `Spec.Unwrap`),
-- which is frozen, and this one, which is whatever makes
-- `batchSimultaneousᵖ` agree with it.  The two meet only in raw values,
-- burst by burst, so the envelope this side runs on -- its fields, its
-- ids, its kinds -- is an implementation detail the theorem never sees.
--
-- EACH NAME IS A FORK POINT.  Today every one of them runs the spec
-- side's machinery, because nothing has yet needed to differ; the first
-- change to the impl's envelope lands HERE, as a new body, and the spec
-- side is not touched.  What is NOT free is below this module: `Rx.Exp`,
-- `Rx.SExp` and the evaluator.  A change that needs one of those is a
-- question for Anthony, never a patch.
--
-- THE VALUE TYPE IS PINNED BY THE COMPARISON.  `unwrapImpl` answers in
-- `Val (plainᵏ Γ κ) a`, the type the spec side's values have, because
-- `≡` needs one type; at a data type that is the bare value whatever the
-- context, so only an observable-typed payload feels the pin.
module Implementation.Pipeline where

open import Data.List    using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Data.Sum     using (inj₁; inj₂)

open import Rx.Prim      using (valueᵖ; completeᵖ)
open import Rx.Exp       using (Ctx; Ty; Exp; Val; listᵗ; uniqᵗ)
open import Rx.SExp      using (SExp; Kinds; plainᵏ; emitᵗ)
open import Rx.Slots     using (Slots)
open import Rx.Envelope  using (instEventᵗ; machineEmitᵗ)
open import Rx.Evaluator using (Burst)
open import Rx.Elaborate using (elaborateSpec)
open import Rx.Simul-Slots using (SimulSlots; embedSlotsSpec)

elaborateImpl : ∀ {n} {Γ : Ctx n} (κ : Kinds n) {t : Ty}
              → SExp Γ [] [] [] t → Exp (plainᵏ Γ κ) [] [] [] (emitᵗ t)
elaborateImpl κ e = elaborateSpec κ e

embedSlotsImpl : ∀ {n} {Γ : Ctx n} {κ : Kinds n}
               → SimulSlots Γ κ → Slots (plainᵏ Γ κ)
embedSlotsImpl ins = embedSlotsSpec ins

-- an envelope's value payloads, read off the wire directly: the impl
-- side has no use for the spec's decoded `InstEmit`
payloadsᴵ : ∀ {n} {Γ : Ctx n} {u b : Ty}
          → List (Val Γ (instEventᵗ u b)) → List (Val Γ b)
payloadsᴵ []                  = []
payloadsᴵ (inj₂ (inj₁ v) ∷ xs) = v ∷ payloadsᴵ xs
payloadsᴵ (_ ∷ xs)            = payloadsᴵ xs

-- one burst of the batched run, as a subscriber sees it: one entry per
-- batch, in stream order
unwrapImpl : ∀ {n} {Γ : Ctx n} {a : Ty}
           → Burst Γ (machineEmitᵗ (listᵗ a)) → List (List (Val Γ a))
unwrapImpl []                     = []
unwrapImpl {a = a} (valueᵖ (evs , _) ∷ es) =
  payloadsᴵ {u = uniqᵗ} {b = listᵗ a} evs ++ unwrapImpl es
unwrapImpl (completeᵖ ∷ es)       = unwrapImpl es
