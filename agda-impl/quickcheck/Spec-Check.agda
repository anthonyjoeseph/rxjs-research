{-# OPTIONS --guardedness #-}

-- THE SIMULTANEOUS SPEC, TESTED.  Each generated program is listed three
-- ways, each subscribed at the root: its plain emission set, its
-- elaborated program's, and the batcher's on top.  Decided over those
-- listings: that the batches joined are the plain run's values, that the
-- batcher's grouping by the names the elaboration mints is the spec's
-- grouping of the elaborated run by those names, and that the names
-- agree with the instants pairwise.  Those are the route to `batchable`
-- and `erases` in `simultaneous.Statement`, read here by the
-- elaboration's names rather than the spec's stamps.
--
-- OWED: deciding `Groups` itself.  A stamp is a count of instants over a
-- whole listing, so on an uncut listing it is computable, and the check
-- then compares the batched listing against the plain one directly, the
-- elaborated listing dropping out.
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
-- that cannot fire; it needs only to fire, so it runs over fewer seeds.
-- A probe for `make spec-check`: no proof reads it.
--
-- THE PINNED PROGRAMS: Anthony's examples, each with the batches it must
-- deliver, written out.  The statements say the batcher agrees with the
-- elaboration's instants; a pin says the instants are the intended ones.
module quickcheck.Spec-Check where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using () renaming (⊤ to Unit)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not; if_then_else_)
open import Data.List using (List; []; _∷_; upTo) renaming (map to mapL)
open import Data.List.Relation.Unary.All using ([])
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_; _≡ᵇ_; _<ᵇ_; z≤n; s≤s)
open import Data.Nat.Show using () renaming (show to showℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String) renaming (_++_ to _+++_)
open import IO.Primitive.Core using (_>>=_; return)
open import IO.Primitive.Finite using (putStrLn)
open import IO.Primitive.Handle using (hSetBuffering; stdout; lineBuffering)
open import Relation.Nullary using (does)

open import Tree using (Obs; cold; empty; map; flatMap; of; mergeᶠ; connect; connected; takeWhile; merge)
open import denotation.Events using (Timeline; fixed; From∞; done; at; emit; close; fresh)
open import denotation.Position using (_≟ⁱ_; Pos; root; _≟ᵖ_)
open import denotation.EmissionSet using (Ev; end)
open import simultaneous.Readings using (instantOf; stamped)
open import simultaneous.InstEmit using (InstEmit)
open import simultaneous.SObs using (module Elaborate)
import simultaneous.Spec as Grouping
open Grouping _≟ᵖ_ using (batchSimultaneousᴰ)
open import simultaneous.Relations using (batchedObs; values; joined; outs)
open import quickcheck.Code using (toObs; timeline; showCode)
open import quickcheck.Quickcheck using (program)
open import quickcheck.Tabled using (Listed; rows; short; listT; sort; proper; allᵇ)
open import quickcheck.Trace using (depth)
open import quickcheck.Ty using (natᵗ)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) using (IE; elaborate)

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

  -- the batches met, each with the name it carries
  batchesOut : ∀ {A} → Rows (IE (List A)) → List (Pos × List A)
  batchesOut rs = stamped (values rs)

  -- the spec's grouping of an elaborated run's values by name, the run
  -- over, so the last group is kept
  groupedᴺ : ∀ {A} → Rows (IE A) → List (Pos × List A)
  groupedᴺ rs = batchSimultaneousᴰ (stamped (values rs))

  -- an emit at its position, read as its position and its name
  named : ∀ {A} → Pos × IE A → Pos × Pos
  named (p , x) = p , InstEmit.instant x

  -- names equal exactly when instants are
  sameInstant : Pos × Pos → Pos × Pos → Bool
  sameInstant (p , i) (q , j) = iff (does (i ≟ᵖ j)) (does (instantOf p ≟ⁱ instantOf q))

-- every pair of emits met agrees
agreeᵇ : ∀ {A} → Rows (IE A) → Bool
agreeᵇ rs = allPairsᵇ sameInstant (mapL named (outs rs))

-- `Relations.Ends`
endsᵇ : ∀ {A} → Rows A → Bool
endsᵇ []                = false
endsᵇ ((_ , end) ∷ _)   = true
endsᵇ (_ ∷ rs)          = endsᵇ rs

-- the batches joined are the plain run's values, over a whole run
joinsᵇ : Rows (IE (List ℕ)) → Rows ℕ → Bool
joinsᵇ b e = eqℕs (joined b) (values e) ∧ iff (endsᵇ b) (endsᵇ e)

-- the batches are the grouping by name, over a whole run
batchesᵇ : Rows (IE (List ℕ)) → Rows (IE ℕ) → Bool
batchesᵇ b x = eqBatches (batchesOut b) (groupedᴺ x)

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

  -- A late reader whose first event is its source's end, ending a lane
  -- whose successor's burst the batch must still cover; the timer's
  -- completion is an async call of its own, so its instant too:
  -- `timer(1).pipe(connect(h => merge(h.pipe(map(() => 5)),
  --    h.pipe(mergeMap(() => of(1, 2)), concatMap(v => v === 1 ? h : of(v * 10))))))`
  -- [5] [20]
  endHanded : Obs Timeline [] ℕ
  endHanded = connect (cold (fixed (at 1 z≤n (emit 0 (close over)))))
    (merge (map (λ _ → 5) (connected (here refl)))
      (flatMap (mergeᶠ (just 1)) (λ v → if v ≡ᵇ 1 then connected (here refl) else of (v * 10 ∷ []))
        (flatMap (mergeᶠ nothing) (λ _ → of (1 ∷ 2 ∷ [])) (connected (here refl)))))

  -- Every early reader of `h` cut while a lane reading it late is yet to
  -- meet its next emit:
  -- `timer(1).pipe(mergeMap(() => of(1, 2, 3)), connect(h => merge(
  --    h.pipe(takeWhile(v => v < 2), mergeMap(() => h)), h.pipe(takeWhile(v => v < 2)))))`
  -- [1, 2, 3]
  lazyCut : Obs Timeline [] ℕ
  lazyCut = connect (flatMap (mergeᶠ nothing) (λ _ → of (1 ∷ 2 ∷ 3 ∷ [])) (cold (fixed (at 1 z≤n (emit 0 (close over))))))
    (merge (flatMap (mergeᶠ nothing) (λ _ → connected (here refl)) (takeWhile false (λ v → v <ᵇ 2) (connected (here refl))))
           (takeWhile false (λ v → v <ᵇ 2) (connected (here refl))))

  -- The same, the late reader a queued lane, queued an instant before:
  -- `timer(3).pipe(mergeMap(() => of(1, 2, 3)), connect(h => merge(h.pipe(takeWhile(v => v < 2)),
  --    timer(1).pipe(mergeMap(() => of(0, 1)), concatMap(x => x === 0 ? h.pipe(takeWhile(v => v < 2)) : h)))))`
  -- [1, 1, 3]
  queueCut : Obs Timeline [] ℕ
  queueCut = connect (flatMap (mergeᶠ nothing) (λ _ → of (1 ∷ 2 ∷ 3 ∷ [])) (cold (fixed (at 3 z≤n (emit 0 (close over))))))
    (merge (takeWhile false (λ v → v <ᵇ 2) (connected (here refl)))
      (flatMap (mergeᶠ (just 1)) (λ x → if x ≡ᵇ 0 then takeWhile false (λ v → v <ᵇ 2) (connected (here refl)) else connected (here refl))
        (flatMap (mergeᶠ nothing) (λ _ → of (0 ∷ 1 ∷ [])) (cold (fixed (at 1 z≤n (emit 0 (close over))))))))

  -- A connect's body done before its source, its completion handing the
  -- concat on within the same instant: with `src` sending 0 at 1 and
  -- completing at 3,
  -- `of(0, 1).pipe(concatMap(v => v === 0
  --    ? src.pipe(connect(h => h.pipe(takeWhile(v => v < 0, true), mergeMap(() => of(5)))))
  --    : of(7)))`
  -- [5, 7]
  heldOpen : Obs Timeline [] ℕ
  heldOpen = flatMap (mergeᶠ (just 1)) (λ v → if v ≡ᵇ 0 then body else of (7 ∷ [])) (of (0 ∷ 1 ∷ []))
    where
      body : Obs Timeline [] ℕ
      body = connect (cold (fixed (at 1 z≤n (emit 0 (close λ where .From∞.force → at 3 (s≤s (s≤s z≤n)) (close over))))))
        (flatMap (mergeᶠ nothing) (λ _ → of (5 ∷ [])) (takeWhile true (λ v → v <ᵇ 0) (connected (here refl))))

  pins : List (String × Obs Timeline [] ℕ × List (List ℕ))
  pins = ("timer-of" , timerOf , (3 ∷ 4 ∷ []) ∷ [])
       ∷ ("held-open" , heldOpen , (5 ∷ 7 ∷ []) ∷ [])
       ∷ ("cut-shared" , cutShared , (2 ∷ 3 ∷ 3 ∷ []) ∷ [])
       ∷ ("end-handed" , endHanded , (5 ∷ []) ∷ (20 ∷ []) ∷ [])
       ∷ ("lazy-cut" , lazyCut , (1 ∷ 2 ∷ 3 ∷ []) ∷ [])
       ∷ ("queue-cut" , queueCut , (1 ∷ 1 ∷ 3 ∷ []) ∷ [])
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
  pinned (p ∷ ps) = putStrLn ("spec-check: pinning " +++ proj₁ p) >>= λ _ → putStrLn (pinLine p) >>= λ _ → pinned ps

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

  -- a line as each seed starts, so a run cut short shows how far it got
  -- and the log's timestamps show what each seed cost
  progress : ℕ → IO Unit
  progress seed = putStrLn ("spec-check: seed " +++ showℕ seed +++ " " +++ showCode natᵗ (program seed))

  showTally : Tally → String
  showTally (tally s k l c b) =
    showℕ (s Data.Nat.∸ k) +++ " checked, " +++ showℕ k +++ " skipped; failing: left-to-right "
    +++ showℕ l +++ ", coherent " +++ showℕ c +++ ", batchable " +++ showℕ b

  fires : String → ℕ → String
  fires s 0 = "spec-check: selftest " +++ s +++ " SILENT"
  fires s k = "spec-check: selftest " +++ s +++ " fires on " +++ showℕ k +++ " seeds"

  seeds : List ℕ
  seeds = upTo 300

  -- a sabotage needs only to fire, so fewer seeds serve
  sabotaged : List ℕ
  sabotaged = upTo 100

  -- each seed judged once, its failures printed as met
  report : List ℕ → Tally → IO Unit
  report []          t = putStrLn ("spec-check: done " +++ showTally t)
  report (seed ∷ ss) t with judge (budget seed) (real seed)
  ... | v = progress seed >>= λ _ → failed (fails v) >>= λ _ → report ss (add v t)
    where
      failed : List String → IO Unit
      failed []       = return _
      failed (f ∷ fs) = putStrLn ("spec-check: FAIL seed " +++ showℕ seed +++ words (f ∷ fs) +++ " " +++ showCode natᵗ (program seed))

  selftest : IO Unit
  selftest =
    putStrLn (fires "left-to-right" (Tally.l2r (tallyOf emptied sabotaged))) >>= λ _ →
    putStrLn (fires "coherent" (Tally.coh (tallyOf unstamped sabotaged))) >>= λ _ →
    putStrLn (fires "batchable" (Tally.bat (tallyOf doubled sabotaged)))

main : IO Unit
main = hSetBuffering stdout lineBuffering >>= λ _ → pinned pins >>= λ _ → report seeds (tally 0 0 0 0 0) >>= λ _ → selftest
