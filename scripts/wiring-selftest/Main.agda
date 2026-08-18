-- The wiring checker's own fixture.  NOT part of the proof: it is checked by
-- `make wiring-selftest`, never by `make agda`, and lives outside agda/src.
module Main where
open import Thy using (top-line)
