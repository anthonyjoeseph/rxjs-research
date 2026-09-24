------------------------------------------------------------------
-- THE BUG CACHE'S RUNNER: a compiled entry point that walks the corpus
-- and prints which rows failed, and on which property.
--
-- WHY THERE IS A BINARY AT ALL.  A row is a pair of booleans over a
-- whole `evaluate` run, and Agda's evaluator is the wrong machine to
-- ask: the typechecker normalises the run, pays the termination check
-- on the way and caches nothing usable, while the GHC backend runs the
-- same definitions at a speed that makes the corpus's size stop
-- mattering.  The cache is append-only, so a cost per row that the gate
-- pays forever is the one property it must not have.
--
-- THE VERDICT IS PRINTED, NOT RETURNED, because `CLI.IO` has no exit
-- status to return: its whole FFI surface is stdin and stdout.  So the
-- summary line is the contract -- `make bug-cache` demands it, which is
-- what stops a binary that ran nothing at all from reading as green,
-- and then refuses any `FAIL` line.
------------------------------------------------------------------
module Implementation.Unit-Test.Bug-Cache where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
                      renaming (_++_ to _++ᴸ_)
open import Data.Nat.Show using (show)
open import Data.String using (String; _++_)

open import CLI.IO using (putStr; Unit)
open import Implementation.Unit-Test using (cases)
open import Implementation.Unit-Test.Prelude using (Case; wellFormed; agrees)

open Case using (name)

-- one row's verdicts, as the report lines it is owed: a row can fail
-- both properties, and saying which is the whole value of the line
--
-- MATCHED IN A HELPER, NEVER BY A `with` ON THE VERDICTS.  A `with
-- agrees c` makes the TYPECHECKER normalise the run it abstracts, and
-- the run is a whole `evaluate↓` over a variable case: measured, it
-- exhausts any heap before the module finishes checking.
verdicts : Case → Bool → Bool → List String
verdicts c true  true  = []
verdicts c true  false = (name c ++ " impl≡spec") ∷ []
verdicts c false true  = (name c ++ " well-formed") ∷ []
verdicts c false false = (name c ++ " well-formed") ∷ (name c ++ " impl≡spec") ∷ []

faults : Case → List String
faults c = verdicts c (wellFormed c) (agrees c)

allFaults : List Case → List String
allFaults []       = []
allFaults (c ∷ cs) = faults c ++ᴸ allFaults cs

lines : List String → String
lines []       = ""
lines (l ∷ ls) = "bug-cache: FAIL " ++ l ++ "\n" ++ lines ls

report : List Case → String
report cs =
  lines bad ++ "bug-cache: ran " ++ show (length cs) ++ " cases, "
    ++ show (length bad) ++ " failures\n"
  where bad = allFaults cs

main : IO Unit
main = putStr (report cases)
