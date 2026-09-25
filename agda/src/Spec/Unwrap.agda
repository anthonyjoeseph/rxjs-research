-- WHAT AN RXJS SUBSCRIBER SEES OF THE SPEC'S BATCHES: THE VALUES, AND
-- NOTHING ELSE.  `spec-batchSimultaneous` answers in envelopes because
-- its input is envelopes, and an envelope's instant, source and kind are
-- the elaboration's bookkeeping rather than anything a subscriber can
-- observe.  Comparing envelopes would let the impl's bookkeeping decide
-- the verdict: an elaborator giving every emit its own instant makes the
-- spec batch nothing, and two envelope shapes could never be compared at
-- all.  So the top line compares what is left once this has run.
--
-- FROZEN WITH THE REST OF THE SPEC SIDE.  It is the right-hand side's
-- last step, so moving it moves what the theorem says.
module Spec.Unwrap where

open import Data.List using (List; []; _∷_; _++_)

open import Rx.Prim using (InstEmit; _at_from_as_)
open import Spec    using (valuesOf)

-- one entry per batch, in stream order
unwrapSpec : ∀ {A : Set} → List (InstEmit (List A)) → List (List A)
unwrapSpec []                         = []
unwrapSpec ((es at _ from _ as _) ∷ xs) = valuesOf es ++ unwrapSpec xs
