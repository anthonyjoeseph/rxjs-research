-- The ledger's FFI exemption: a `COMPILE GHC`-bound postulate in `CLI/` has
-- a Haskell body and leaves the ledger; an unbound one beside it stays.
module CLI.Ffi where
open import Thy using (Nat)

postulate ffi-bound : Nat → Nat
{-# COMPILE GHC ffi-bound = id #-}

postulate ffi-unbound : Nat
