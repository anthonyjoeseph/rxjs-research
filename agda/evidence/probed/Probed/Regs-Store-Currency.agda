-- WHICH CURRENCY THE REGISTRY COMPONENT IS OWED IN, AND IT IS A CHOICE
-- AMONG THREE READINGS RATHER THAN A COVERAGE CLAIM.  The frame's own
-- caps predicate prices a registered path above the row it would have
-- to close, so the component has to be read off something else.  Two
-- candidates suggest themselves -- the program the walk descends
-- through, and the STORE the walk is holding -- and the question this
-- file settles is not which of them is right but that NEITHER is, and
-- that the reading which merely takes both is not right either.  It is
-- a FORK and not a receipt because its product is that the candidates
-- DISAGREE, not that any one statement held.
--
-- FORK: burst-regs-split
--
-- THE THREE CANDIDATES.  `synVerdict` reads the registry against the
-- program's own unit.  `storeVerdict` reads it against the NODE
-- TABLE's maximum, which is what the walk face grants at every clause
-- and then spends on the node table alone.  `joinVerdict` takes the
-- larger of the two, which is the shape every grant in that face is
-- already written in.  They are functions of one argument, so each
-- disagreement is a value rather than a paragraph.

-- WHY NEITHER SOURCE ALONE CAN BE THE ANSWER.  A registered chain is
-- built from two kinds of frame and `pathNestD` SUMS along it.  The
-- walk contributes the frames it descends through, which are the
-- program's own syntax.  A delivery contributes the frames minted from
-- the value delivered, and a scan whose accumulator is observable-typed
-- carries syntax as a VALUE -- `natᵗ` cannot BE the accumulator, but
-- `sndᵗ (pairᵗ _ _)` lets it CARRY one and the measure charges the ⊔ of
-- a pair's sides.  So the program stands still while the chain climbs
-- one per fold, which is the first candidate's death; and a map whose
-- function carries a stream registers at positive depth while
-- installing no node at all, which is the second's.

-- AND THE JOIN DIES WHERE THE TWO SOURCES COMPOSE, which is the row
-- worth having, because a join is what every neighbouring grant is
-- shaped like and it survives each candidate's own counterexample.
-- Stacking a carrying map ABOVE a carrying fold makes the chain carry
-- both contributions at once: the registry reads eight where the node
-- table reads six and the unit reads seven, so it passes both maxima
-- while the sum, thirteen, is not close.  A join loses whichever
-- contribution is smaller; the fold does not.

-- WHAT THE ROWS DO NOT BUY.  They say nothing about the margin at the
-- target's own budget -- these runs are at padded gas -- and nothing
-- about retirement, where a cascade retires what it mints and the
-- delivery face reads zero.  This family keeps every registration it
-- makes, which is why it is the one that separates.  Nor do they reach
-- a registration minted from anything but a delivery or the walk's own
-- descent.  The syntactic axis is TWO-SIDED rather than a scale:
-- deepening the map moves the registry and the unit together and the
-- node table not at all, so a row that grew only the bound could not
-- have produced the crossing.
module Probed.Regs-Store-Currency where

open import Data.Bool using (Bool; true; false)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; foldr)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _⊔_; _+_; _*_; _≤ᵇ_)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs;
  mapᵉ; ofᵉ; mergeAllᵉ; input; sndᵗ; pairᵗ; nat̂; strmᵗ)
open import Rx.Evaluator using (subscribeE; root; sched-init; st-init; EvalSt)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nodeNest; nestUnit)
open import Probed.Apparatus using (Separates; separates-at)
open import Refuted.Reg-Nest-Reached using (Γ₂; prog; slots; run; fuel)

-- the node table's maximum, spelled here rather than imported so this
-- file does not pull the walk module in behind it: same fold, over the
-- same measure, at the same table.
nodesN : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} → EvalSt e → ℕ
nodesN st = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)

------------------------------------------------------------------
-- THE COMPOSED PROGRAM.  A map whose function CARRIES a stream, laid
-- over the fold family whose accumulator carries one, so the chain a
-- registration reports takes a contribution from each source.
------------------------------------------------------------------

fn1 : Fn Γ₂ [] [] [] natᵗ natᵗ
fn1 = sndᵗ (pairᵗ (strmᵗ (mergeAllᵉ nothing (ofᵉ {t = obs natᵗ} []))) (nat̂ 0))

fn3 : Fn Γ₂ [] [] [] natᵗ natᵗ
fn3 = sndᵗ (pairᵗ (strmᵗ (mergeAllᵉ nothing (ofᵉ
              (strmᵗ (mergeAllᵉ nothing (ofᵉ
                (strmᵗ (mergeAllᵉ nothing (ofᵉ {t = obs natᵗ} [])) ∷ []))) ∷ [])))) (nat̂ 0))

prog1 : Closed Γ₂ natᵗ
prog1 = mapᵉ fn1 prog

prog3 : Closed Γ₂ natᵗ
prog3 = mapᵉ fn3 prog

-- AND THE MAP ALONE, over an input rather than over the fold family:
-- nothing here installs a node at all, so the node table is empty while
-- the carried stream still puts the registration at positive depth.
progM : Closed Γ₂ natᵗ
progM = mapᵉ fn1 (input fzero)

runM : EvalSt progM
runM = proj₂ (proj₂ (subscribeE fuel progM root 0 0
                       (sched-init progM (slots 5)) (st-init progM)))

run1 : EvalSt prog1
run1 = proj₂ (proj₂ (subscribeE fuel prog1 root 0 0
                       (sched-init prog1 (slots 5)) (st-init prog1)))

run3 : EvalSt prog3
run3 = proj₂ (proj₂ (subscribeE fuel prog3 root 0 0
                       (sched-init prog3 (slots 5)) (st-init prog3)))

------------------------------------------------------------------
-- THE FIGURES.  Base one hundred, least significant first: the
-- registry, the node table and the unit at each of three lengths, then
-- the same three at the map alone and at each composed program.
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

composed : ℕ
composed = pack ( regsNestMax (EvalSt.registry runM)
                ∷ nodesN runM
                ∷ nestUnit progM (slots 5)
                ∷ regsNestMax (EvalSt.registry run1)
                ∷ nodesN run1
                ∷ nestUnit prog1 (slots 5)
                ∷ regsNestMax (EvalSt.registry run3)
                ∷ nodesN run3
                ∷ nestUnit prog3 (slots 5)
                ∷ [])

composed≡ : composed ≡ 70608050606020001
composed≡ = refl

------------------------------------------------------------------
-- THE CANDIDATES, AND THE POINTS THEY COME APART AT
------------------------------------------------------------------

synVerdict : ℕ → Bool
synVerdict k = regsNestMax (EvalSt.registry (run k)) ≤ᵇ nestUnit prog (slots k)

storeVerdict : ℕ → Bool
storeVerdict k = regsNestMax (EvalSt.registry (run k)) ≤ᵇ nodesN (run k)

separates : Separates synVerdict storeVerdict
separates = separates-at 5 (λ ())

-- AND THE STORE CANDIDATE HOLDS WHERE THE OTHER ALREADY DID, so that
-- first separation is a strengthening rather than a swap: LOAD-BEARING
-- at five, where the syntactic reading fails; DEGENERATE at one and
-- three, where both hold and the row only shows the store side does
-- not lose what the program side had.
verdicts : List Bool
verdicts = synVerdict 1 ∷ storeVerdict 1
         ∷ synVerdict 3 ∷ storeVerdict 3
         ∷ synVerdict 5 ∷ storeVerdict 5
         ∷ []

verdicts≡ : verdicts ≡ true ∷ true ∷ true ∷ true ∷ false ∷ true ∷ []
verdicts≡ = refl

-- and the store candidate dies on its own axis, where a carrying map
-- registers over a table that holds nothing: LOAD-BEARING, and it is
-- the axis the first separation holds fixed
mapOnly : Bool
mapOnly = regsNestMax (EvalSt.registry runM) ≤ᵇ nodesN runM

------------------------------------------------------------------
-- THE JOIN, WHICH IS THE READING THAT SURVIVES BOTH COUNTEREXAMPLES,
-- AND THE SUM, WHICH IS THE ONE THE TARGET IS STATED IN
------------------------------------------------------------------

joinAt : ℕ → ℕ → ℕ → Bool
joinAt r nd un = r ≤ᵇ (nd ⊔ un)

sumAt : ℕ → ℕ → ℕ → Bool
sumAt r nd un = r ≤ᵇ (un + nd)

joinVerdict : ℕ → Bool
joinVerdict 1 = joinAt (regsNestMax (EvalSt.registry run1)) (nodesN run1)
                       (nestUnit prog1 (slots 5))
joinVerdict _ = joinAt (regsNestMax (EvalSt.registry run3)) (nodesN run3)
                       (nestUnit prog3 (slots 5))

sumVerdict : ℕ → Bool
sumVerdict 1 = sumAt (regsNestMax (EvalSt.registry run1)) (nodesN run1)
                     (nestUnit prog1 (slots 5))
sumVerdict _ = sumAt (regsNestMax (EvalSt.registry run3)) (nodesN run3)
                     (nestUnit prog3 (slots 5))

-- the second separation, and the one that decides the target's shape:
-- at one contributed layer the join still holds and holds TIGHTLY, at
-- three it fails.  LOAD-BEARING at three; the row at one is what says
-- the crossing is a crossing and not a scale.
separatesJoin : Separates joinVerdict sumVerdict
separatesJoin = separates-at 3 (λ ())

joinVerdicts : List Bool
joinVerdicts = joinVerdict 1 ∷ sumVerdict 1
             ∷ joinVerdict 3 ∷ sumVerdict 3
             ∷ mapOnly
             ∷ []

joinVerdicts≡ : joinVerdicts ≡ true ∷ true ∷ false ∷ true ∷ false ∷ []
joinVerdicts≡ = refl
