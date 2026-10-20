-- THE INSTEMIT: what every srxjs observable emits, one per incoming
-- emit, carrying everything that emit caused.  An `SObservable<A>` is
-- an `Observable<InstEmit<A>>`, so an elaborated program is an ordinary
-- `Obs` tree at this element type, and the operators are blind to it.
--
-- THE PROVENANCE IS THE INSTANT: the root cause the emit belongs to,
-- one subscribe frame or one arrival's cascade.  Only its equality is
-- ever read, by the spec and by `coherent`.  The rest is the counting
-- protocol a batcher reads to know when an instant is over: `init` and
-- `close` keep the live registrations of each source, `source` names
-- the arrival's source, `kind` who minted the emit.
module simultaneous.InstEmit where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)

Provenance : Set
Provenance = ℕ

SourceId : Set
SourceId = ℕ

-- Why a registration ended: an operator cut it after it delivered this
-- instant, cut it before it delivered what it owed, or it ran dry.
data CloseReason : Set where
  cut cutPending exhausted : CloseReason

-- Who minted the emit: a subscription's own burst, an arrival's
-- delivery, or a share's connect burst forwarded up its first subscriber.
data EmitKind : Set where
  subscribe delivery plumbing : EmitKind

data InstEvent (A : Set) : Set where
  init     : SourceId → InstEvent A
  value    : A → InstEvent A
  close    : SourceId → CloseReason → InstEvent A
  handoff  : SourceId → InstEvent A
  complete : InstEvent A

record InstEmit (A : Set) : Set where
  constructor instEmit
  field
    events  : List (InstEvent A)
    instant : Provenance
    source  : SourceId
    kind    : EmitKind

-- The values among an emit's events, in order.
valuesᴱ : ∀ {A} → List (InstEvent A) → List A
valuesᴱ []              = []
valuesᴱ (value a ∷ es)  = a ∷ valuesᴱ es
valuesᴱ (init _ ∷ es)    = valuesᴱ es
valuesᴱ (close _ _ ∷ es) = valuesᴱ es
valuesᴱ (handoff _ ∷ es) = valuesᴱ es
valuesᴱ (complete ∷ es)  = valuesᴱ es

valuesOf : ∀ {A} → InstEmit A → List A
valuesOf x = valuesᴱ (InstEmit.events x)
