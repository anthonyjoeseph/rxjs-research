------------------------------------------------------------------
-- DECIDING TWO EMIT STREAMS EQUAL AS A BOOLEAN, for the two compiled
-- binaries that have to compare batchings without a typechecker
-- underneath them.
--
-- WHY A BOOLEAN AND NOT A DECISION PROCEDURE.  Nothing here is used in
-- a proof: both consumers are `main`s that print a verdict, so what is
-- wanted is a comparison the GHC backend runs, not a witness.  A
-- `Dec (xs ≡ ys)` would oblige every constructor along the way to
-- carry an injectivity argument for a value that is thrown away at the
-- moment it is printed.
--
-- THE VALUE TYPE IS FIXED AT `List ℕ` RATHER THAN GENERALISED, which
-- is the batched side of the pipeline: a batch groups an instant's
-- values, so the unbatched stream this family never sees is the one
-- carrying bare values.  Generalising over the payload would need an
-- equality on it passed in, and there is exactly one payload either
-- caller ever compares.
--
-- IT IS A SEPARATE MODULE BECAUSE IT HAS TWO ROOTS.  The QuickCheck
-- binary and the bug cache's runner are each compiled entry points
-- reachable from neither the other nor Main, so a family living in
-- one of them cannot be spent by the other -- and the duplicate that
-- would otherwise be written is precisely what `make dup-check`
-- exists to refuse.  It sits directly above the protocol's own
-- vocabulary so that the cone either caller pays for is that
-- vocabulary and nothing else.
------------------------------------------------------------------
module Rx.Emit-Eq where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; _≡ᵇ_)

open import Rx.Prim using (InstEvent; init; value; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; EmitKind;
                           subscribe; delivery; plumbing; InstEmit; _at_from_as_)

eqKind : EmitKind → EmitKind → Bool
eqKind subscribe subscribe = true
eqKind delivery  delivery  = true
eqKind plumbing  plumbing  = true
eqKind _         _         = false

eqReason : CloseReason → CloseReason → Bool
eqReason cut        cut        = true
eqReason cutPending cutPending = true
eqReason exhausted  exhausted  = true
eqReason _          _          = false

eqListℕ : List ℕ → List ℕ → Bool
eqListℕ []       []       = true
eqListℕ (x ∷ xs) (y ∷ ys) = (x ≡ᵇ y) ∧ eqListℕ xs ys
eqListℕ _        _        = false

eqEvent : InstEvent (List ℕ) → InstEvent (List ℕ) → Bool
eqEvent (init a)    (init b)    = a ≡ᵇ b
eqEvent (value a)   (value b)   = eqListℕ a b
eqEvent (close a p) (close b q) = (a ≡ᵇ b) ∧ eqReason p q
eqEvent (handoff a) (handoff b) = a ≡ᵇ b
eqEvent complete    complete    = true
eqEvent _           _           = false

eqEvents : List (InstEvent (List ℕ)) → List (InstEvent (List ℕ)) → Bool
eqEvents []       []       = true
eqEvents (x ∷ xs) (y ∷ ys) = eqEvent x y ∧ eqEvents xs ys
eqEvents _        _        = false

eqEmit : InstEmit (List ℕ) → InstEmit (List ℕ) → Bool
eqEmit (es at i from s as k) (es′ at i′ from s′ as k′) =
  eqEvents es es′ ∧ (i ≡ᵇ i′) ∧ (s ≡ᵇ s′) ∧ eqKind k k′

eqBatched : List (InstEmit (List ℕ)) → List (InstEmit (List ℕ)) → Bool
eqBatched []       []       = true
eqBatched (x ∷ xs) (y ∷ ys) = eqEmit x y ∧ eqBatched xs ys
eqBatched _        _        = false
