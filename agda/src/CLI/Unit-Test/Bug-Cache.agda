------------------------------------------------------------------
-- THE BUG CACHE'S RUNNER: a compiled entry point that runs ONE row of
-- the corpus, named by the number on stdin, and prints which of its
-- properties failed.  Zero asks for the row count instead, and a
-- second word `sides` asks for the two sides each comparison read, which
-- is what a failing row is diagnosed from.  A second word `plain`,
-- `joined`, `untimed` or `stamps` runs ONE side alone -- the plain run,
-- the elaborated run, the timed program run plain, the timed program
-- elaborated -- which is what a SLOW row is timed from, since a row's
-- budget covers every side at once.
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
module CLI.Unit-Test.Bug-Cache where

open import Agda.Builtin.IO using (IO)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; length)
                      renaming (_++_ to _++ᴸ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat.Show using (show; readMaybe)
open import Data.String using (String; _++_; words)

open import CLI.IO using (putStr; getContents; _>>=_; Unit)
open import CLI.Unit-Test using (cases)
open import CLI.Unit-Test.Prelude using (Case; checksOf; statements; ltrSides; batchableSides; stampsOf; Γ₂ᵉ; faithfulSides)
open import Rx.Prim using (InstEmit; InstEvent; EmitKind; subscribe; delivery; plumbing;
  init; value; close; handoff; complete; CloseReason; cut; cutPending; exhausted;
  PlainEvent; valueᵖ; completeᵖ)
open import SExp.Syntax using (plainᵗ)
open import Rx.Exp using (natᵗ)
open import SExp.Pipeline using (emitsᴵ)
open import SExp.InstEmit.Decode using (decodeEmits)

open Case using (name; fuel; prog; kinds; slots)

-- one row's verdicts, as the report lines it is owed: a row can fail
-- several properties, and saying which is the whole value of the line
--
-- MATCHED IN A HELPER, NEVER BY A `with` ON THE VERDICTS.  A `with
-- holds s c` makes the TYPECHECKER normalise the run it abstracts, and
-- the run is a whole `evaluate↓` over a variable case: measured, it
-- exhausts any heap before the module finishes checking.
verdict : Case → String → Bool → List String
verdict c l true  = []
verdict c l false = (name c ++ " " ++ l) ∷ []

verdicts : Case → List (String × Bool) → List String
verdicts c []             = []
verdicts c ((l , b) ∷ bs) = verdict c l b ++ᴸ verdicts c bs

faults : Case → List String
faults c = verdicts c (checksOf statements c)

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

showNats : List ℕ → String
showNats []       = "[]"
showNats (x ∷ xs) = show x ++ " ∷ " ++ showNats xs

showBatches : List (List ℕ) → String
showBatches []       = "[]"
showBatches (b ∷ bs) = "[" ++ showNats b ++ "] ∷ " ++ showBatches bs

showKind : EmitKind → String
showKind subscribe = "subscribe"
showKind delivery  = "delivery"
showKind plumbing  = "plumbing"

showReason : CloseReason → String
showReason cut        = "cut"
showReason cutPending = "cutPending"
showReason exhausted  = "exhausted"

-- every event, with the source it names: what the batcher counts
showEvents : ∀ {A : Set} → List (InstEvent A) → String
showEvents []                = ""
showEvents (init s ∷ es)     = " init " ++ show s ++ showEvents es
showEvents (value _ ∷ es)    = " value" ++ showEvents es
showEvents (close s r ∷ es)  = " close " ++ show s ++ " " ++ showReason r ++ showEvents es
showEvents (handoff s ∷ es)  = " handoff " ++ show s ++ showEvents es
showEvents (complete ∷ es)   = " complete" ++ showEvents es

showEmits : ∀ {A : Set} → List (InstEmit A) → String
showEmits []       = ""
showEmits (e ∷ es) =
  "  emit at " ++ show (InstEmit.instant e) ++ " from " ++ show (InstEmit.source e) ++ " " ++
  showKind (InstEmit.kind e) ++ ":" ++ showEvents (InstEmit.events e) ++ "\n" ++
  showEmits es

plainEnd : ∀ {A : Set} → List (PlainEvent A) → String
plainEnd []                = "the run does not complete\n"
plainEnd (completeᵖ ∷ _)   = "the run completes\n"
plainEnd (valueᵖ _ ∷ es)   = plainEnd es

-- MATCHED IN HELPERS, NEVER BY A `with`, for the reason `verdict` is:
-- a `with` over a run makes the typechecker normalise it.
ltrLines : List ℕ × List ℕ × List ℕ → String
ltrLines (l , r , l′) = "left-to-right  joined  " ++ showNats l ++ "\n" ++
                        "left-to-right  plain   " ++ showNats r ++ "\n" ++
                        "left-to-right  joined+1 " ++ showNats l′ ++ "\n"

batchLines : List (List ℕ) × List (List ℕ) → String
batchLines (l , r) = "batchable      batched " ++ showBatches l ++ "\n" ++
                     "batchable      grouped " ++ showBatches r ++ "\n"

-- the timed run's values, each with its instant and its packet
showStamps : List (ℕ × List ℕ) → String
showStamps []             = ""
showStamps ((i , p) ∷ ps) =
  "  stamp at " ++ show i ++ " packet " ++ showNats p ++ "\n" ++ showStamps ps

showSides : Maybe Case → IO Unit
showSides nothing  = putStr "bug-cache: no such row\n"
showSides (just c) =
  putStr (ltrLines (ltrSides c) ++ batchLines (batchableSides c) ++ showStamps (stampsOf c) ++
          showEmits (decodeEmits {Γ = Γ₂ᵉ (kinds c)} {a = plainᵗ natᵗ} (emitsᴵ (kinds c) (fuel c) (prog c) (slots c))) ++
          plainEnd (emitsᴵ (kinds c) (fuel c) (prog c) (slots c)))

oneSide : Maybe Case → (Case → String) → IO Unit
oneSide nothing  f = putStr "bug-cache: no such row\n"
oneSide (just c) f = putStr (f c)

sideLine : String → List ℕ → String
sideLine name vs = name ++ " " ++ showNats vs ++ "\n"

answer : Maybe ℕ → List String → IO Unit
answer nothing     _               = putStr "bug-cache: expected a row number on stdin\n"
answer (just zero) _               = putStr ("bug-cache: rows " ++ show (length cases) ++ "\n")
answer (just k)    ("sides" ∷ _)   = showSides (row k cases)
answer (just k)    ("plain" ∷ _)   = oneSide (row k cases) (λ c → sideLine "plain" (proj₁ (proj₂ (ltrSides c))))
answer (just k)    ("joined" ∷ _)  = oneSide (row k cases) (λ c → sideLine "joined" (proj₁ (ltrSides c)))
answer (just k)    ("untimed" ∷ _) = oneSide (row k cases) (λ c → sideLine "untimed" (proj₁ (faithfulSides c)))
answer (just k)    ("stamps" ∷ _)  = oneSide (row k cases) (λ c → showStamps (stampsOf c))
answer (just k)    _               = runRow (row k cases)

firstNat : List String → Maybe ℕ
firstNat []      = nothing
firstNat (w ∷ _) = readMaybe 10 w

rest : List String → List String
rest []       = []
rest (_ ∷ ws) = ws

main : IO Unit
main =
  getContents >>= λ s →
  answer (firstNat (words s)) (rest (words s))
