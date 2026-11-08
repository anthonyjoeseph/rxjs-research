{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, TESTED.  Each generated program is listed three
-- ways, each subscribed at the root: its plain emission set, its
-- elaborated program's, and the batcher's on top.  The three statements
-- of `simultaneous.Statement` are decided over those listings, through
-- the statement's own readings (`joined`, `batchesOut`, `grouped`,
-- `named`), so the check and the claim cannot drift apart.
--
-- A WHOLE RUN, NOT ITS PREFIXES.  Each statement is two directions over
-- prefixes; on a run listed to its end, uncut, both directions say the
-- same as equality of the whole readings, and the run is over, so the
-- last group is kept.  A seed whose listing a budget cut is skipped, and
-- counted as skipped.
--
-- THE SELFTEST: each statement is decided again against a sabotage made
-- to break it alone, built over the same elaboration: the batcher
-- replaced by `empty`, the elaborated emits all restamped to one name,
-- every batch delivered twice.  A sabotage no seed catches is a checker
-- that cannot fire.  A probe for `make spec-check`: no proof reads it.
--
-- THE PINNED PROGRAMS: Anthony's examples, each with the batches it must
-- deliver, written out.  The statements say the batcher agrees with the
-- elaboration's instants; a pin says the instants are the intended ones.
module quickcheck.Spec-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; _++_; [_]; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _≡ᵇ_; _≤ᵇ_; _<ᵇ_; z≤n; s≤s)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import IO.Primitive.Core using (_>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import Relation.Nullary using (does)

open import Tree using (Obs; cold; empty; map; flatMap; of; mergeᶠ; connect; connected; takeWhile)
open import denotation.Events using (Pos; Timeline; fixed; From∞; done; at; emit; close; root; _≟ᵖ_; fresh)
open import denotation.EmissionSet using (Ev; end)
open import simultaneous.Readings using (instantOf; stamped)
open import simultaneous.InstEmit using (instEmit; mark)
import simultaneous.InstEmit as M
open import simultaneous.SObs using (Batching; module Elaborate)
open import simultaneous.Protocol using (nameStep; subStep)
open import simultaneous.Relations using (batchedObs; values; joined; batchesOut; grouped; outs; named)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Tabled using (Listed; rows; short; listT; sort; proper; allᵇ)
open import quickcheck.Trace using (depth)
open import quickcheck.Ty using (natᵗ)

open Elaborate {C = Timeline} _≟ᵖ_ root fresh using (IE; elaborate; Step; bstep; bstart)

------------------------------------------------------------------------
-- Listings

Rows : Set → Set
Rows A = List (Pos × Ev A)

-- A listing in the order a reader meets it, unless a budget cut it.
whole : ∀ {A} → Maybe (Listed A) → Maybe (Rows A)
whole nothing  = nothing
whole (just l) with short l
... | true  = nothing
... | false = just (sort (proper (rows l)))

------------------------------------------------------------------------
-- The three statements, decided over whole runs

private
  eqℕs : List ℕ → List ℕ → Bool
  eqℕs []       []       = true
  eqℕs (a ∷ as) (b ∷ bs) = (a ≡ᵇ b) ∧ eqℕs as bs
  eqℕs _        _        = false

  eqBatches : List (Pos × List ℕ) → List (Pos × List ℕ) → Bool
  eqBatches []              []              = true
  eqBatches ((i , as) ∷ xs) ((j , bs) ∷ ys) = does (i ≟ᵖ j) ∧ eqℕs as bs ∧ eqBatches xs ys
  eqBatches _               _               = false

  iff : Bool → Bool → Bool
  iff a b = (a ∧ b) ∨ (not a ∧ not b)

  -- every pair, the earlier first
  allPairsᵇ : ∀ {X : Set} → (X → X → Bool) → List X → Bool
  allPairsᵇ r []       = true
  allPairsᵇ r (x ∷ xs) = allᵇ (r x) xs ∧ allPairsᵇ r xs

  -- `Statement.SameInstant`
  sameInstant : Pos × Pos → Pos × Pos → Bool
  sameInstant (p , i) (q , j) = iff (does (i ≟ᵖ j)) (does (instantOf p ≟ᵖ instantOf q))

-- `Statement.InstantsAgree`
agreeᵇ : ∀ {A} → Rows (IE A) → Bool
agreeᵇ rs = allPairsᵇ sameInstant (mapL named (outs rs))

-- `Statement.Ends`
endsᵇ : ∀ {A} → Rows A → Bool
endsᵇ []                = false
endsᵇ ((_ , end) ∷ _)   = true
endsᵇ (_ ∷ rs)          = endsᵇ rs

-- `Statement.Joins`, over a whole run
joinsᵇ : Rows (IE (List ℕ)) → Rows ℕ → Bool
joinsᵇ b e = eqℕs (joined b) (values e) ∧ iff (endsᵇ b) (endsᵇ e)

-- `Statement.Batches`, over a whole run: the run is over, so `ov` holds
batchesᵇ : Rows (IE (List ℕ)) → Rows (IE ℕ) → Bool
batchesᵇ b x = eqBatches (batchesOut b) (grouped true x)

------------------------------------------------------------------------
-- The protocol `good-run` walks, decided at every emit

private
  freshᵇ : ∀ {A : Set} → Pos → List (Pos × A) → Bool
  freshᵇ i []            = true
  freshᵇ i ((j , _) ∷ _) = not (does (i ≟ᵖ j))

  nil : ∀ {X : Set} → List X → Bool
  nil [] = true
  nil _  = false

  unless : Bool → String → List String → List String
  unless true  _ r = r
  unless false s r = s ∷ r

  -- The leaves of `simultaneous.Closing` refuted at the emit `w`, the walk
  -- named `a`, past the burst when `s`, in batcher state `st`, before `ys`.
  leafAt : Pos → Bool → Step ℕ → IE ℕ → List (IE ℕ) → List String
  leafAt a s st (instEmit (mark M.begin) n) ys =
    unless s "begin-late" (unless (does (n ≟ᵖ a) ∨ freshᵇ a (stamped ys)) "begin-fresh" [])
  leafAt a s st (instEmit (mark M.subscribed) n) ys =
    unless (not s) "sub-once" (unless (freshᵇ root (stamped ys)) "sub-fresh" [])
  leafAt a s st (instEmit (mark M.over) n) ys =
    unless (not s ∨ freshᵇ a (stamped ys)) "over-fresh" []
  leafAt a s st (instEmit (mark M.stop) n) ys =
    unless (not s ∨ not (Batching.routes (proj₁ st) ≤ᵇ 1) ∨ freshᵇ a (stamped ys)) "stop-fresh" []
  leafAt a s st (instEmit (mark M.completed) n) ys = unless (nil (stamped ys)) "completed-end" []
  leafAt a s st _ ys = []

  -- One pass, the walk's state carried along.
  protocol : Pos → Bool → Step ℕ → List (IE ℕ) → List String
  protocol a s st []       = []
  protocol a s st (w ∷ ys) = leafAt a s st w ys ++ protocol (nameStep a w) (subStep s w) (bstep st w) ys

-- The leaves a seed's elaborated run refutes; nothing when cut.
protocolOf : ℕ → Obs Timeline [] (IE ℕ) → List String
protocolOf n x with whole (listT n x [] root)
... | just rx = protocol root false bstart (values rx)
... | nothing = []

------------------------------------------------------------------------
-- One seed

-- A seed's three programs: plain, elaborated, batched.
record Three : Set₁ where
  constructor three
  field
    plain      : Obs Timeline [] ℕ
    elaborated : Obs Timeline [] (IE ℕ)
    batched    : Obs Timeline [] (IE (List ℕ))

data Verdict : Set where
  skipped : Verdict
  -- left-to-right, coherent, batchable
  checked : Bool → Bool → Bool → Verdict

judge : ℕ → Three → Verdict
judge n (three o x b) with whole (listT n o [] root) | whole (listT n x [] root) | whole (listT n b [] root)
... | just ro | just rx | just rb = checked (joinsᵇ rb ro) (agreeᵇ rx ∧ agreeᵇ rb) (batchesᵇ rb rx)
... | _       | _       | _       = skipped

private
  plainOf : ℕ → Obs Timeline [] ℕ
  plainOf seed = toObs timeline 3 (program seed) [] [] []

  budget : ℕ → ℕ
  budget seed = depth 3 (program seed)

  real : ℕ → Three
  real seed = let o = plainOf seed in three o (elaborate o) (batchedObs o)

  restamp : ∀ {A} → IE A → IE A
  restamp x = record x { instant = root }

  twice : ∀ {A : Set} → A → List A
  twice a = a ∷ a ∷ []

  -- The sabotages, each aimed at one statement.
  emptied unstamped doubled : ℕ → Three
  emptied seed   = let o = plainOf seed in three o (elaborate o) empty
  unstamped seed = let o = plainOf seed in three o (map restamp (elaborate o)) (batchedObs o)
  doubled seed   = let o = plainOf seed in three o (elaborate o) (flatMap (mergeᶠ nothing) (λ e → of (twice e)) (batchedObs o))

  -- The protocol's sabotage: every emit twice, the subscribe mark too.
  protoTwice : ℕ → Obs Timeline [] (IE ℕ)
  protoTwice seed = flatMap (mergeᶠ nothing) (λ e → of (twice e)) (elaborate (plainOf seed))

------------------------------------------------------------------------
-- The pinned programs

private
  over : ∀ {A t} → From∞ A t
  over .From∞.force = done

  -- `timer(1).pipe(mergeMap(() => of(3, 4)))`: one async step, whose
  -- synchronous cascade is one instant
  -- [3, 4]
  timerOf : Obs Timeline [] ℕ
  timerOf = flatMap (mergeᶠ nothing) (λ _ → of (3 ∷ 4 ∷ [])) (cold (fixed (at 1 z≤n (emit 0 (close over)))))

  -- a raw source: next(1), next(2) as it is subscribed, then one timer
  -- callback calling next(3), next(4): every async `next` is an instant
  -- [1, 2] [3] [4]
  raw : Obs Timeline [] ℕ
  raw = cold (fixed (at 0 z≤n (emit 1 (emit 2 (close λ where
    .From∞.force → at 2 (s≤s z≤n) (emit 3 (emit 4 (close over))))))))

  -- `raw.pipe(mergeMap(e => of(e, e + 1, e + 2)))`
  -- [1, 2, 3, 2, 3, 4] [3, 4, 5] [4, 5, 6]
  spread : Obs Timeline [] ℕ
  spread = flatMap (mergeᶠ nothing) (λ e → of (e ∷ e + 1 ∷ e + 2 ∷ [])) raw

  -- `timerOf`, shared, its outer cut while lanes it started read on:
  -- `timer(1).pipe(mergeMap(() => of(1, 2, 3)),
  --    connect(h => h.pipe(takeWhile(v => v < 3), mergeMap(() => h))))`
  -- [2, 3, 3]
  cutShared : Obs Timeline [] ℕ
  cutShared = connect (flatMap (mergeᶠ nothing) (λ _ → of (1 ∷ 2 ∷ 3 ∷ [])) (cold (fixed (at 1 z≤n (emit 0 (close over))))))
    (flatMap (mergeᶠ nothing) (λ _ → connected (here refl)) (takeWhile false (λ v → v <ᵇ 3) (connected (here refl))))

  pins : List (String × Obs Timeline [] ℕ × List (List ℕ))
  pins = ("timer-of" , timerOf , (3 ∷ 4 ∷ []) ∷ [])
       ∷ ("cut-shared" , cutShared , (2 ∷ 3 ∷ 3 ∷ []) ∷ [])
       ∷ ("raw" , raw , (1 ∷ 2 ∷ []) ∷ (3 ∷ []) ∷ (4 ∷ []) ∷ [])
       ∷ ("spread" , spread , (1 ∷ 2 ∷ 3 ∷ 2 ∷ 3 ∷ 4 ∷ []) ∷ (3 ∷ 4 ∷ 5 ∷ []) ∷ (4 ∷ 5 ∷ 6 ∷ []) ∷ [])
       ∷ []

  pinBudget : ℕ
  pinBudget = 10

  eqAll : List (List ℕ) → List (List ℕ) → Bool
  eqAll []       []       = true
  eqAll (a ∷ as) (b ∷ bs) = eqℕs a b ∧ eqAll as bs
  eqAll _        _        = false

  showBatch : List ℕ → String
  showBatch []       = "[]"
  showBatch (a ∷ as) = "[" +++ showℕ a +++ go as
    where
      go : List ℕ → String
      go []       = "]"
      go (b ∷ bs) = ", " +++ showℕ b +++ go bs

  showBatches : List (List ℕ) → String
  showBatches []       = "(none)"
  showBatches (b ∷ []) = showBatch b
  showBatches (b ∷ bs) = showBatch b +++ " " +++ showBatches bs

  pinLine : String × Obs Timeline [] ℕ × List (List ℕ) → String
  pinLine (s , o , want) with whole (listT pinBudget (batchedObs o) [] root)
  ... | nothing = "spec-check: FAIL pinned " +++ s +++ " cut by its budget"
  ... | just rb with mapL proj₂ (batchesOut rb)
  ...   | got with eqAll got want
  ...     | true  = "spec-check: pinned " +++ s +++ " batches " +++ showBatches got
  ...     | false = "spec-check: FAIL pinned " +++ s +++ " batches " +++ showBatches got +++ ", wanted " +++ showBatches want

  pinned : List (String × Obs Timeline [] ℕ × List (List ℕ)) → IO Unit
  pinned []       = putStrLn "spec-check: pinned programs checked"
  pinned (p ∷ ps) = putStrLn (pinLine p) >>= λ _ → pinned ps

------------------------------------------------------------------------
-- The report

record Tally : Set where
  constructor tally
  field
    seen skip l2r coh bat : ℕ

private
  bump : Bool → ℕ → ℕ
  bump true  k = k
  bump false k = suc k

  add : Verdict → Tally → Tally
  add skipped         (tally s k l c b) = tally (suc s) (suc k) l c b
  add (checked x y z) (tally s k l c b) = tally (suc s) k (bump x l) (bump y c) (bump z b)

  fails : Verdict → List String
  fails skipped         = []
  fails (checked x y z) = name x "left-to-right" (name y "coherent" (name z "batchable" []))
    where
      name : Bool → String → List String → List String
      name true  _ r = r
      name false s r = s ∷ r

  words : List String → String
  words []       = ""
  words (s ∷ ss) = " " +++ s +++ words ss

  tallyOf : (ℕ → Three) → List ℕ → Tally
  tallyOf mk []          = tally 0 0 0 0 0
  tallyOf mk (seed ∷ ss) = add (judge (budget seed) (mk seed)) (tallyOf mk ss)

  showTally : Tally → String
  showTally (tally s k l c b) =
    showℕ (s Data.Nat.∸ k) +++ " checked, " +++ showℕ k +++ " skipped; failing: left-to-right "
    +++ showℕ l +++ ", coherent " +++ showℕ c +++ ", batchable " +++ showℕ b

  fires : String → ℕ → String
  fires s 0 = "spec-check: selftest " +++ s +++ " SILENT"
  fires s k = "spec-check: selftest " +++ s +++ " fires on " +++ showℕ k +++ " seeds"

  seeds : List ℕ
  seeds = upTo 300

  protoFails : (ℕ → Obs Timeline [] (IE ℕ)) → List ℕ → ℕ
  protoFails mk []          = 0
  protoFails mk (seed ∷ ss) with protocolOf (budget seed) (mk seed)
  ... | []    = protoFails mk ss
  ... | _ ∷ _ = suc (protoFails mk ss)

  protoReport : List ℕ → IO Unit
  protoReport []          = putStrLn "spec-check: protocol checked"
  protoReport (seed ∷ ss) with protocolOf (budget seed) (elaborate (plainOf seed))
  ... | []     = protoReport ss
  ... | f ∷ fs = putStrLn ("spec-check: FAIL protocol seed " +++ showℕ seed +++ words (f ∷ fs) +++ " " +++ showCode natᵗ (program seed))
                 >>= λ _ → protoReport ss

  report : List ℕ → IO Unit
  report []          = putStrLn ("spec-check: done " +++ showTally (tallyOf real seeds))
  report (seed ∷ ss) with fails (judge (budget seed) (real seed))
  ... | []     = report ss
  ... | f ∷ fs = putStrLn ("spec-check: FAIL seed " +++ showℕ seed +++ words (f ∷ fs) +++ " " +++ showCode natᵗ (program seed))
                 >>= λ _ → report ss

  selftest : IO Unit
  selftest =
    putStrLn (fires "left-to-right" (Tally.l2r (tallyOf emptied seeds))) >>= λ _ →
    putStrLn (fires "coherent" (Tally.coh (tallyOf unstamped seeds))) >>= λ _ →
    putStrLn (fires "batchable" (Tally.bat (tallyOf doubled seeds))) >>= λ _ →
    putStrLn (fires "protocol" (protoFails protoTwice (upTo 60)))

main : IO Unit
main = selftest >>= λ _ → pinned pins >>= λ _ → protoReport seeds >>= λ _ → report seeds
