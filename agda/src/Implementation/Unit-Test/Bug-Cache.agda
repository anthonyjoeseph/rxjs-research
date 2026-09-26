------------------------------------------------------------------
-- THE BUG CACHE'S RUNNER: a compiled entry point that runs ONE row of
-- the corpus, named by the number on stdin, and prints which of its
-- properties failed.  Zero asks for the row count instead.
--
-- WHY THERE IS A BINARY AT ALL.  A row is a set of booleans over a
-- whole `evaluate` run, and Agda's evaluator is the wrong machine to
-- ask: the typechecker normalises the run, pays the termination check
-- on the way and caches nothing usable, while the GHC backend runs the
-- same definitions at a speed that makes the corpus's size stop
-- mattering.  The cache is append-only, so a cost per row that the gate
-- pays forever is the one property it must not have.
--
-- ONE ROW PER PROCESS, BECAUSE A ROW CAN FAIL TO TERMINATE.  The
-- runner is compiled with termination checking off, and a row whose run
-- never ends is a counterexample like any other -- but inside one walk
-- of the whole corpus it would take every later verdict down with it.
-- So `make bug-cache` starts one process per row under a time budget,
-- and a row that outruns it is reported as a failure by name: the name
-- is printed, and flushed, before the run it labels starts.
--
-- THE VERDICT IS PRINTED, NOT RETURNED, because `CLI.IO` has no exit
-- status to return: its whole FFI surface is stdin and stdout.  So the
-- closing `done` line is the contract -- `make bug-cache` demands it of
-- every row, which is what stops a row that ran nothing from reading as
-- green, and then refuses any `FAIL` line.
------------------------------------------------------------------
module Implementation.Unit-Test.Bug-Cache where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
                      renaming (_++_ to _++ᴸ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Show using (show; readMaybe)
open import Data.String using (String; _++_; words)

open import CLI.IO using (putStr; getContents; _>>=_; Unit)
open import Implementation.Unit-Test using (cases)
open import Implementation.Unit-Test.Prelude using (Case; checksOf)

open Case using (name)

-- one row's verdicts, as the report lines it is owed: a row can fail
-- several properties, and saying which is the whole value of the line
--
-- MATCHED IN A HELPER, NEVER BY A `with` ON THE VERDICTS.  A `with
-- agrees c` makes the TYPECHECKER normalise the run it abstracts, and
-- the run is a whole `evaluate↓` over a variable case: measured, it
-- exhausts any heap before the module finishes checking.
verdict : Case → String → Bool → List String
verdict c l true  = []
verdict c l false = (name c ++ " " ++ l) ∷ []

verdicts : Case → List (String × Bool) → List String
verdicts c []             = []
verdicts c ((l , b) ∷ bs) = verdict c l b ++ᴸ verdicts c bs

faults : Case → List String
faults c = verdicts c (checksOf c)

lines : List String → String
lines []       = ""
lines (l ∷ ls) = "bug-cache: FAIL " ++ l ++ "\n" ++ lines ls

-- the k-th row, 1-based
row : ℕ → List Case → Maybe Case
row _             []       = nothing
row (suc zero)    (c ∷ cs) = just c
row (suc (suc k)) (c ∷ cs) = row (suc k) cs
row zero          (c ∷ cs) = nothing

runRow : Maybe Case → IO Unit
runRow nothing  = putStr "bug-cache: no such row\n"
runRow (just c) =
  putStr ("bug-cache: row " ++ name c ++ "\n") >>= λ _ →
  putStr (lines (faults c) ++ "bug-cache: done\n")

answer : Maybe ℕ → IO Unit
answer nothing  = putStr "bug-cache: expected a row number on stdin\n"
answer (just zero) = putStr ("bug-cache: rows " ++ show (length cases) ++ "\n")
answer (just k) = runRow (row k cases)

firstNat : List String → Maybe ℕ
firstNat []      = nothing
firstNat (w ∷ _) = readMaybe 10 w

main : IO Unit
main =
  getContents >>= λ s →
  answer (firstNat (words s))
