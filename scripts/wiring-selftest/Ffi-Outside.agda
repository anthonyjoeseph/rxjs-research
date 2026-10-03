-- A binding outside `CLI/` earns nothing: a proof could cite it.
module Ffi-Outside where
open import Thy using (Nat)

postulate ffi-outside : Nat → Nat
{-# COMPILE GHC ffi-outside = id #-}
