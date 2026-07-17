module Rx.Protocol where

open import Data.List  using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import Rx.Prim using (InstEmit)

------------------------------------------------------------------
-- The protocol automaton: InstEmit's contract made explicit.
-- batchSimultaneous is total and trusting — the impl reads only
-- init/close counts, the spec reads only instant ids.  WellFormed
-- is the bridge premise that the two vocabularies tell the same
-- story on a stream: what the evaluator promises
-- (evaluate-well-formed) and what the batcher assumes
-- (batch-agreement).  stepProtocol rejects (nothing) any emit
-- breaking a clause:
--   bracketing          — value/close from s only inside an open
--                         init s … close s window; closes match inits
--   fan-out exactness   — within one instant, each live registration
--                         of s forwards EXACTLY ONE emit of s
--                         (possibly valueless) — the clause that
--                         makes owed = live-count recover boundaries
--   instant freshness   — an instant, once left, never recurs
--   complete discipline — complete only where the protocol
--                         materializes it (root, subscribe bursts)
------------------------------------------------------------------

postulate
  ProtocolSt    : Set    -- live registrations per source + the open instant's owed set
  protocol-init : ProtocolSt
  stepProtocol  : ∀ {A} → InstEmit A → ProtocolSt → Maybe ProtocolSt

runProtocol : ∀ {A} → ProtocolSt → List (InstEmit A) → Maybe ProtocolSt
runProtocol s []       = just s
runProtocol s (x ∷ xs) with stepProtocol x s
... | just s′ = runProtocol s′ xs
... | nothing = nothing

data Accepted {A : Set} : Maybe A → Set where
  accepted : ∀ {s} → Accepted (just s)

WellFormed : ∀ {A} → List (InstEmit A) → Set
WellFormed xs = Accepted (runProtocol protocol-init xs)
