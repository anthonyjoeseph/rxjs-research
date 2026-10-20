-- THE INSTEMIT: what every srxjs observable emits, one per incoming
-- emit, carrying everything that emit caused.  An `SObservable<A>` is
-- an `Observable<InstEmit<A>>`, so an elaborated program is an ordinary
-- `Obs` tree at this element type, and the operators are blind to it.
--
-- THE PROVENANCE IS THE INSTANT: the root cause the emit belongs to,
-- one subscribe frame or one async emission's cascade.  Names are of a
-- type `N` the engine is generic in, so it can compare them and nothing
-- else: the denotation's are positions, the IO runtime's symbols.  The
-- rest is the counting
-- protocol a batcher reads to know when an instant is over: `init` and
-- `close` keep the live registrations of each source, `source` names
-- the arrival's source, `kind` who minted the emit.
module simultaneous.InstEmit where

open import Data.List using (List; []; _∷_)

-- Why a registration ended: an operator cut it after it delivered this
-- instant, cut it before it delivered what it owed, or it ran dry.
data CloseReason : Set where
  cut cutPending exhausted : CloseReason

-- Who minted the emit: a subscription's own burst, an arrival's
-- delivery, or a share's connect burst forwarded up its first subscriber.
data EmitKind : Set where
  subscribe delivery plumbing : EmitKind

-- `init`, `close` and `handoff` name a source.
data InstEvent (N A : Set) : Set where
  init     : N → InstEvent N A
  value    : A → InstEvent N A
  close    : N → CloseReason → InstEvent N A
  handoff  : N → InstEvent N A
  complete : InstEvent N A

record InstEmit (N A : Set) : Set where
  constructor instEmit
  field
    events  : List (InstEvent N A)
    instant : N
    source  : N
    kind    : EmitKind

-- The values among an emit's events, in order.
valuesᴱ : ∀ {N A} → List (InstEvent N A) → List A
valuesᴱ []              = []
valuesᴱ (value a ∷ es)  = a ∷ valuesᴱ es
valuesᴱ (init _ ∷ es)    = valuesᴱ es
valuesᴱ (close _ _ ∷ es) = valuesᴱ es
valuesᴱ (handoff _ ∷ es) = valuesᴱ es
valuesᴱ (complete ∷ es)  = valuesᴱ es

valuesOf : ∀ {N A} → InstEmit N A → List A
valuesOf x = valuesᴱ (InstEmit.events x)
