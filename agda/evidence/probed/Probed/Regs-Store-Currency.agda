-- WHICH CURRENCY THE REGISTRY COMPONENT IS OWED IN, AND IT IS A CHOICE
-- BETWEEN TWO READINGS RATHER THAN A COVERAGE CLAIM.  The frame's own
-- caps predicate prices a registered path above the row it would have
-- to close, and the reading that suggests itself next -- the syntax the
-- frame registers from -- is refuted.  What is left open is narrow and
-- decidable: is the component owed against the program, or against the
-- STORE the frame is walking?  This file is a FORK and not a receipt
-- because its product is that the two candidates DISAGREE on the
-- verdict, not that either statement held.
--
-- FORK: burst-nest-regs
--
-- THE TWO CANDIDATES.  `synVerdict` reads the registry against the
-- program's own unit -- the currency the row's left summand is already
-- written in.  `storeVerdict` reads it against the NODE TABLE's
-- maximum, which is what the walk face grants at every clause and then
-- spends on the node table alone.  They are two functions of one
-- argument, so the disagreement is a value rather than a paragraph.

-- WHY THE ANSWER IS NOT ALREADY KNOWN FROM THE REFUTATION.  A
-- refutation says the program's syntax is too small; it does not say
-- the store is big enough, and the two grow for different reasons.  A
-- scan whose accumulator is observable-typed carries syntax as a VALUE:
-- the accumulator lives in a NODE, so the node table climbs a layer per
-- fold, while the registered path is minted from the `map-f` the frame
-- builds when that value is delivered.  Whether the mint is under the
-- thing it was built from, or one layer over it, is exactly the
-- question -- and one layer over is what a `map-f` costs, so the losing
-- answer was the likely one.

-- THE ROWS SAY IT IS UNDER, BY EXACTLY ONE, AND THAT IT TRACKS.  Three
-- script lengths, the fold driven once per delivery.  The registry
-- reads one, three and five where the node table reads two, four and
-- six, so the margin neither closes nor widens: the registered path is
-- the accumulator's own depth and the node holds one wrap more.  A row
-- reading a fixed margin at one length would be a coincidence; a margin
-- that holds while both sides climb is the mechanism.  The unit stands
-- at four throughout, which is what makes the length axis LOAD-BEARING
-- rather than a scale: it is the axis the program's syntax cannot see.

-- WHAT THE ROWS DO NOT BUY.  They say nothing about the row's own
-- right-hand side, which no row here runs and which no row can -- the
-- increment is caps-denominated and a cap does not evaluate.  What
-- reaches the row is the SEPARATION, since a component the store
-- dominates is one the walk face's existing grant already bounds, and
-- what would remain is transporting that grant onto a conjunct the
-- face carries for the node table and declines to carry here.  They say
-- nothing about a registration minted from something OTHER than a
-- delivered value -- the walk's own path extensions, which are
-- syntactic and were never in doubt -- and nothing about retirement,
-- where the delivery face reads zero because a cascade retires what it
-- mints.  This family keeps every registration it makes, which is why
-- it is the one that separates.
module Probed.Regs-Store-Currency where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Nat using (ℕ; _⊔_; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed)
open import Rx.Evaluator using (EvalSt)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nodeNest; nestUnit)
open import Probed.Apparatus using (Separates; separates-at)
open import Refuted.Reg-Nest-Reached using (prog; slots; run)

-- the node table's maximum, spelled here rather than imported so this
-- file does not pull the walk module in behind it: same fold, over the
-- same measure, at the same table.
nodesN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
nodesN st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

------------------------------------------------------------------
-- THE FIGURES.  Base one hundred, least significant first: the
-- registry, the node table and the unit at each of three lengths.
------------------------------------------------------------------

pack : List ℕ → ℕ
pack = foldr (λ x acc → x + 100 * acc) 0

figures : ℕ
figures = pack ( regsNestMax (EvalSt.registry (run 1))
               ∷ nodesN (run 1)
               ∷ regsNestMax (EvalSt.registry (run 3))
               ∷ nodesN (run 3)
               ∷ regsNestMax (EvalSt.registry (run 5))
               ∷ nodesN (run 5)
               ∷ nestUnit prog (slots 5)
               ∷ [])

figures≡ : figures ≡ 4060504030201
figures≡ = refl

------------------------------------------------------------------
-- THE TWO CANDIDATES, AND THE POINT THEY COME APART AT
------------------------------------------------------------------

synVerdict : ℕ → Bool
synVerdict k = regsNestMax (EvalSt.registry (run k)) ≤ᵇ nestUnit prog (slots k)

storeVerdict : ℕ → Bool
storeVerdict k = regsNestMax (EvalSt.registry (run k)) ≤ᵇ nodesN (run k)

separates : Separates synVerdict storeVerdict
separates = separates-at 5 (λ ())

-- AND THE STORE CANDIDATE HOLDS WHERE THE OTHER ALREADY DID, so the
-- separation is a strengthening rather than a swap: LOAD-BEARING at
-- five, where the syntactic reading fails; DEGENERATE at one and
-- three, where both hold and the row only shows the store side does
-- not lose what the program side had.
verdicts : List Bool
verdicts = synVerdict 1 ∷ storeVerdict 1
         ∷ synVerdict 3 ∷ storeVerdict 3
         ∷ synVerdict 5 ∷ storeVerdict 5
         ∷ []

verdicts≡ : verdicts ≡ true ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []
verdicts≡ = refl
