{-# OPTIONS --guardedness #-}

-- THE BUG CACHE'S RUNNER: checks `prop` of every row and
-- prints a `FAIL` line per failing row, then a closing `done` line.
-- `make bug-cache`
-- demands the `done` line — so a runner that died part-way is red — and
-- refuses any `FAIL`.
--
-- A binary, not a typecheck: the typechecker would normalise every run
-- on every gate, and the corpus only grows.
module quickcheck.Bug-Cache-Runner where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat.Show using (show)
open import Data.Product using (_×_; _,_)
open import Data.String using (String; _++_)
open import IO.Primitive.Core using (_>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)

open import quickcheck.Ty using (natᵗ)
open import quickcheck.Code using (Prog)
open import quickcheck.Quickcheck using (prop)
open import quickcheck.Bug-Cache using (cases)

-- MATCHED IN A HELPER, NEVER BY A `with` ON THE VERDICT: a `with prop p`
-- makes the TYPECHECKER normalise the run it abstracts, which exhausts
-- the heap before the module finishes checking.
private
  verdict : String → Bool → IO Unit → IO Unit
  verdict l true  rest = rest
  verdict l false rest = putStrLn ("bug-cache: FAIL " ++ l) >>= λ _ → rest

  report : List (String × Prog natᵗ) → IO Unit
  report []             = putStrLn ("bug-cache: done " ++ show (length cases) ++ " rows")
  report ((l , p) ∷ rs) = verdict l (prop p) (report rs)

main : IO Unit
main = report cases
