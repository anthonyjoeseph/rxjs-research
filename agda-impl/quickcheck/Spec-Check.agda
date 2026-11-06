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
module quickcheck.Spec-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _≡ᵇ_)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_)
open import Data.String using (String) renaming (_++_ to _+++_)
open import IO.Primitive.Core using (_>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import Relation.Nullary using (does)

open import Tree using (Obs; empty; map; flatMap; of; mergeᶠ)
open import denotation.Events using (Pos; Timeline; root; _≟ᵖ_)
open import denotation.EmissionSet using (Ev)
open import simultaneous.Readings using (instantOf)
open import simultaneous.SObs using (module Elaborate)
open import simultaneous.Statement using (batchedObs; values; joined; batchesOut; grouped; outs; named)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Tabled using (Listed; rows; short; listT; sort; proper; allᵇ)
open import quickcheck.Trace using (depth)
open import quickcheck.Ty using (natᵗ)

open Elaborate {C = Timeline} _≟ᵖ_ root using (IE; elaborate)

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

-- `Statement.Joins`, over a whole run
joinsᵇ : Rows (IE (List ℕ)) → Rows ℕ → Bool
joinsᵇ b e = eqℕs (joined b) (values e)

-- `Statement.Batches`, over a whole run: the run is over, so `ov` holds
batchesᵇ : Rows (IE (List ℕ)) → Rows (IE ℕ) → Bool
batchesᵇ b x = eqBatches (batchesOut b) (grouped true x)

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
    putStrLn (fires "batchable" (Tally.bat (tallyOf doubled seeds)))

main : IO Unit
main = selftest >>= λ _ → report seeds
