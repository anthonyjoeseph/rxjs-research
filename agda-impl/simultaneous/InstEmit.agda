-- THE INSTEMIT: what every srxjs observable emits, one per incoming
-- emit.  An `SObservable<A>` is an `Observable<InstEmit<A>>`, so an
-- elaborated program is an ordinary `Obs` tree at this element type, and
-- the operators are blind to it.
--
-- THE PROVENANCE IS THE INSTANT: the root cause the emit belongs to,
-- one subscribe frame or one async step's cascade.  Names are of a type
-- `N` the engine is generic in, so it can compare them and nothing else:
-- the denotation's are positions, the IO runtime's symbols.
--
-- An emit carries a value or a mark.  The marks are how a batcher learns,
-- inside an instant, that the instant is over; `simultaneous.SObs` says
-- who sends each and what it means.
module simultaneous.InstEmit where

open import Data.List using (List; []; _∷_)

data Mark : Set where
  -- read above every flatMap
  begin over stop : Mark
  -- one flatMap's own, consumed by its scan
  outerOpen outerClose laneStart carry laneDone burstEnd outerDone : Mark
  -- the whole run's, sent at the top and read by the batcher
  subscribed completed : Mark

data InstEvent (A : Set) : Set where
  value : A → InstEvent A
  mark  : Mark → InstEvent A

record InstEmit (N A : Set) : Set where
  constructor instEmit
  field
    event   : InstEvent A
    instant : N

-- The values an emit carries, in order.
valuesOf : ∀ {N A} → InstEmit N A → List A
valuesOf (instEmit (value a) _) = a ∷ []
valuesOf (instEmit (mark _) _)  = []
