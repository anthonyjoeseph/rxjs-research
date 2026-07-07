-- An observable is its emission history plus the instant it completes.
-- Closes are what make concat-style sequencing and take definable: a serial
-- join subscribes its next inner at the previous one's close, and take
-- manufactures a close. The operators over Obs live in Burst.agda, as the
-- subscription-time-parameterized denotation of the primitive grammar.
module Obs where

open import Prelude
open import Time
open import TimedObs

record Obs (A : Set) : Set where
  constructor obs
  field
    emits : TimedObs A
    close : Time
open Obs public

-- well-formedness of a root input: emissions are time-ordered and happen
-- before the close
record WF {A : Set} (o : Obs A) : Set where
  constructor wf
  field
    sorted  : Sorted (emits o)
    bounded : BoundedBy (close o) (emits o)
open WF public
