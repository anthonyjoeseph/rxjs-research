-- THE ENTRYPOINT. Building this module builds every verification in the
-- development: the main theorem (impl ≡ spec for batchSimultaneous) and
-- the README semantics proofs.
module Formal-Verification.All-Verifications where

open import Formal-Verification.Verify-Batch-Simultaneous.Main-Theorem
open import Formal-Verification.Readme-Semantics
