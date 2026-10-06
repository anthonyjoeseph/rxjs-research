------------------------------------------------------------------
-- THE BUG CACHE'S SHARED VOCABULARY: what a cached case IS, now that a
-- case is a value rather than a type.
--
-- A CASE IS A PROGRAM, AND EVERY TOP-LINE STATEMENT IS CHECKED OF IT.
-- Compiled, a run is a function call and asking several questions of it
-- is free -- so a row names a program, and every row is held to the four
-- statements `Main` imports, each at its own two sides.
--
-- WHY THE PREDICATES ARE BOOLEANS RATHER THAN EQUATIONS.  Each is the
-- decision of one statement's conclusion on one row, settled by
-- `CLI.Emit-Eq` where it is an agreement -- the family the QuickCheck
-- binary decides with, so a cached case and the seed that found it are
-- answering one question.
--
-- WHAT IS NOT HERE, DELIBERATELY: a predicate for a run that went DRY.
-- No builder constructs the marker, so a dry run is not a disagreement
-- between two implementations of one batching — it is the descent
-- refusing, which the QuickCheck binary reports unpasteably, and it
-- stays out of a corpus whose verdict gates the build.
------------------------------------------------------------------
module CLI.Unit-Test.Prelude where

open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not; _xor_; if_then_else_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.List using (List; []; _∷_; _++_; map; length; zipWith; concat; take; drop; replicate)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _≤ᵇ_; _+_)
open import Data.Fin using (zero; suc)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function.Base using (_|>′_)

open import Rx.Prim using (ObservableInput; hot; cold; Fuel; Id)
open import Rx.Exp using (Ctx; Val; Closed; natᵗ; obs; inputsBelowᵉ; FlatOp; mergeᶠ; ltᵖ; add)
open import Rx.Slots using (Slots)
open import SExp.Syntax using (SExp; plainᵏ; plainᵗ; Kinds; hotᵏ; coldᵏ; sharedᵏ; emptyˢ; emitᵗ;
  flattenˢ; mapˢ; pairˢ; inlˢ; inrˢ; unitˢ; varˢᵗ; scanˢ; takeWhileˢ; primˢ; fstˢ; sndˢ; natˢ)
open import Rx.Evaluator using (Burst; Stream; Sched; EvalSt; Arrival; sched-next)
open import Rx.Mint using (counter; sourceᵏ)
open import Rx.Evaluator.Builder using (drain!; drainOn; cascade!; pop-rule; subscribe!; evaluate↓)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; _,_; Rule)
open import SExp.Plain using (plainExp; plainValues)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ; plainSlots)
open import SExp.InstEmit.Decode using (decodeEmits)
open import CLI.Emit-Eq using (eqListℕ; prefixListℕ; eqBatches)
open import SExp.Pipeline using (emitsᴵ; runᴾ)
open import SExp.Impl-Slots using (elaborateImpl; embedSlotsImpl)
open import Timed.Translation using (packetOf; timedᶜ; itemᵗ; timed; timedSlots)
open import Batchable.Inst-Extract using (instExtract)
open import SExp.Readings using (joinedᴵ; valsᴵ; arrivalsOf)
open import Batchable.Statement using (batchedᴱ; groupedᴱ)
open import Timed.Faithful using (untimedᵀ)
open import CLI.Store-Check using (storeSides)

-- the harness's fixed context: two nat-typed slots the AUTHOR sees, and
-- the one an elaborated program stands in, where each slot holds the
-- InstEmit over the author's type
Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

-- SLOT ZERO IS SCRIPTED AND SLOT ONE IS SHARED.  A script is the only
-- slot that schedules arrivals -- a share runs inside whatever
-- subscribed it -- so without one every run is its subscribe burst
-- alone.  Slot one holds another srxjs program, stands at the INSTEMIT,
-- and may read slot zero.  The kind vector is not a free choice beside
-- the table -- `SimulSlot` is indexed by it, so slot zero's kind is
-- read off its script, and `mkSlots` below is what says so.
κOf : ObservableInput ℕ → Kinds 2
κOf (hot _)    = hotᵏ  ∷ⱽ sharedᵏ ∷ⱽ []ⱽ
κOf (cold _ _) = coldᵏ ∷ⱽ sharedᵏ ∷ⱽ []ⱽ

Γ₂ᵉ : Kinds 2 → Ctx 4
Γ₂ᵉ κ = plainᵏ Γ₂ κ

-- THE TABLE IS BUILT FROM A SCRIPT AND AN AUTHOR-WRITTEN DEFINITION,
-- and that is what a row has to name, because the sweep DRAWS it.  What
-- makes a drawn definition possible at all is that the stratification
-- side condition COMPUTES: a definition is an `SExp` and every elaboration
-- leaf is a real body, so `inputsBelowᵉ` of it reduces to a boolean
-- rather than getting stuck on a postulate.
--
-- IT LIVES HERE RATHER THAN IN THE GENERATOR because a pasted row has
-- to typecheck where the corpus lives, so the name a row prints has to
-- be one the corpus can see.
tOf : (b : Bool) → Maybe (T b)
tOf true  = just tt
tOf false = nothing

-- A DEFINITION THAT BREAKS STRATIFICATION FALLS BACK TO SILENCE rather
-- than being rejected, because this is a total function and the
-- generator has no way to prove its draw stratified.  In practice the
-- fallback is unreached -- `genSlotRef k` draws only from slots below
-- `k` by construction -- but it is what makes the row a program rather
-- than a proof obligation.

slot₁ : ∀ {κ} → SExp Γ₂ [] [] [] natᵗ → SimulSlot Γ₂ κ 1 natᵗ sharedᵏ
slot₁ d with tOf (inputsBelowᵉ 1 (plainExp d))
... | just ok = sharedˢ d {ok = ok}
... | nothing = sharedˢ emptyˢ

-- WRITTEN SLOT BY SLOT rather than with a wildcard: the arm a slot may
-- use is `lookup (κOf d₀) i`, which does not reduce for an abstract `i`
-- or script.  That is the kind indexing doing its job -- a table cannot
-- name an arm without saying which slot it is naming it for.
mkSlots : (d₀ : ObservableInput ℕ) → SExp Γ₂ [] [] [] natᵗ → SimulSlots Γ₂ (κOf d₀)
mkSlots (hot as)     d₁ zero       = hotˢ {ok = tt} as
mkSlots (cold ss as) d₁ zero       = coldˢ {ok = tt} ss as
mkSlots (hot _)      d₁ (suc zero) = slot₁ d₁
mkSlots (cold _ _)   d₁ (suc zero) = slot₁ d₁
mkSlots _            d₁ (suc (suc ()))

-- RXJS'S THREE NAMED FLATTENERS, which the author's tree does not have
-- as formers: `flattenˢ` over a map making every element a lane and none
-- an echo.  `mergeAll` is `flatAllˢ (mergeᶠ nothing)`, `concatAll` is
-- `flatAllˢ (mergeᶠ (just 1))`, `switchAll` and `exhaustAll` are
-- `flatAllˢ switchᶠ` and `flatAllˢ exhaustᶠ`.  It lives HERE because a
-- row is pasted where the corpus lives and the sweep prints the name.
flatAllˢ : ∀ {Δᵍ Δ Θ t} → FlatOp → SExp Γ₂ Δᵍ Δ Θ (obs t) → SExp Γ₂ Δᵍ Δ Θ t
flatAllˢ op e = flattenˢ op (mapˢ (pairˢ (inlˢ unitˢ) (inrˢ (varˢᵗ (here refl)))) e)

-- RXJS'S `take`, which the author's tree does not have as a former: a
-- count scanned beside the value, cut by an inclusive test at the n-th,
-- the value kept by an echo-only flatten.  The count is a LITERAL, so
-- zero is decided here: `take(0)` never subscribes its source, which no
-- program of the tree can do, and the empty program is what it is.
takeˢ : ∀ {Δᵍ Δ Θ t} → ℕ → SExp Γ₂ Δᵍ Δ Θ t → SExp Γ₂ Δᵍ Δ Θ t
takeˢ zero    e = emptyˢ
takeˢ (suc k) e =
  flattenˢ (mergeᶠ nothing) (mapˢ (pairˢ (sndˢ (varˢᵗ (here refl))) (inlˢ unitˢ))
    (takeWhileˢ (primˢ ltᵖ (pairˢ (fstˢ (varˢᵗ (here refl))) (natˢ (suc k))))
      (scanˢ (pairˢ (primˢ add (pairˢ (fstˢ (fstˢ (varˢᵗ (here refl)))) (natˢ 1)))
                    (inrˢ (sndˢ (varˢᵗ (here refl)))))
             (pairˢ (natˢ 0) (inlˢ unitˢ)) e)))

-- one cached counterexample: a label, and the run that produced it
record Case : Set where
  field
    name  : String
    fuel  : ℕ
    prog  : SExp Γ₂ [] [] [] natᵗ
    kinds : Kinds 2
    slots : SimulSlots Γ₂ kinds

open Case using (name; fuel; prog; kinds; slots)

-- the kinds are read off the table's own type, so a row names none
cached : String → ℕ → SExp Γ₂ [] [] [] natᵗ → {κ : Kinds 2} → SimulSlots Γ₂ κ → Case
cached n f e {κ} ins = record { name = n ; fuel = f ; prog = e ; kinds = κ ; slots = ins }

------------------------------------------------------------------
-- THE FOUR STATEMENTS `Main` IMPORTS, AND THE SIMULATION TWO OF THEM
-- ARE ASSEMBLED OVER, EACH DECIDED AT ITS OWN SIDES.
-- A side is the statement module's own definition applied at this row,
-- never a restatement of it, so the check and the claim cannot drift
-- apart: at `Γ₂`, the row's kinds, `natᵗ` and `tt`, what is compared here is what
-- the statement says is equal.
--
-- NO CAP.  A `takeˢ` above the program -- counted in InstEmits or in
-- values -- runs a different program from the one the row names, and a
-- capped run is an instance of no statement.  The fuel is the one budget
-- the statements quantify over, so it is the one a row may set.
------------------------------------------------------------------

data Statement : Set where
  left-to-rightˢ timing-correctˢ batchableˢ timed-faithfulˢ simulationˢ arrival-runsˢ : Statement
  batched-sandwichˢ packets-name-arrivalsˢ same-clockˢ storeˢ : Statement

-- in `Main`'s order, which is the order a report counts them in, then
-- the simulation and the leaf it stands on, then the leaves the two
-- assembled top lines stand on beside it.  `same-clock` and `store` are
-- not among them: each decides an invariant, not a statement, so no row
-- of the bug cache is held to either
statements : List Statement
statements = left-to-rightˢ ∷ timing-correctˢ ∷ batchableˢ ∷ timed-faithfulˢ ∷ simulationˢ ∷ arrival-runsˢ
           ∷ batched-sandwichˢ ∷ packets-name-arrivalsˢ ∷ []

statementName : Statement → String
statementName left-to-rightˢ  = "left-to-right"
statementName timing-correctˢ = "timing-correct"
statementName batchableˢ      = "batchable"
statementName timed-faithfulˢ = "timed-faithful"
statementName simulationˢ     = "simulation"
statementName arrival-runsˢ = "arrival-runs"
statementName batched-sandwichˢ = "batched-sandwich"
statementName packets-name-arrivalsˢ = "packets-name-arrivals"
statementName same-clockˢ = "same-clock"
statementName storeˢ = "store"

-- `left-to-right`: the batches joined back up, the plain run, and the
-- batches joined back up at one more unit of fuel, the joined runs at
-- an impl fuel the statement leaves free.  A unit of fuel is an arrival
-- and an arrival can be silent, so the batcher can need several units
-- past the plain run's fuel before the instant it holds open closes.
-- The witness is SEARCHED upward from the plain run's fuel, stopping at
-- the first that sandwiches it, at the first whose joined run has
-- overtaken the plain one, or `ltrWindow` units past: a green decides
-- the statement and a red is a candidate past that window.
ltrWindow : ℕ
ltrWindow = 8

-- the joined runs at `f` and one past it, `j` and `j′`, each computed
-- once and only if read
ltrFrom : (Fuel → List ℕ) → List ℕ → ℕ → Fuel → List ℕ → List ℕ → List ℕ × List ℕ × List ℕ
ltrFrom J p zero    f j j′ = j , p , j′
ltrFrom J p (suc k) f j j′ =
  if prefixListℕ j p ∧ not (prefixListℕ p j′)
  then ltrFrom J p k (suc f) j′ (J (suc (suc f)))
  else (j , p , j′)

-- the search, against whichever run the joined ones are read against
sandwichFrom : Case → List ℕ → List ℕ × List ℕ × List ℕ
sandwichFrom c p = ltrFrom J p ltrWindow (fuel c) (J (fuel c)) (J (suc (fuel c)))
  where
    J : Fuel → List ℕ
    J f = joinedᴵ tt (kinds c) f (prog c) (slots c)

ltrSides : Case → List ℕ × List ℕ × List ℕ
ltrSides c = sandwichFrom c (runᴾ (fuel c) (prog c) (slots c))

-- `batched-sandwich`: the same search, against the elaborated run's
-- own values at the fuel, the only run the batcher sees
bsSides : Case → List ℕ × List ℕ × List ℕ
bsSides c = sandwichFrom c (valsᴵ tt (kinds c) (fuel c) (prog c) (slots c))

-- `timing-correct`: each value's stamp, beside its packet.  The
-- contexts are passed by hand because `Val` at a concrete type forgets
-- its context, so no argument's type can say which one it was.
Γ₂ᵗ : Kinds 2 → Ctx 4
Γ₂ᵗ κ = plainᵏ (timedᶜ Γ₂ κ) κ

packets : ∀ κ → List (ℕ × Val (Γ₂ᵗ κ) (plainᵗ (itemᵗ natᵗ))) → List (ℕ × List ℕ)
packets κ []             = []
packets κ ((i , v) ∷ ps) = (i , packetOf {Γ = Γ₂ᵗ κ} natᵗ v) ∷ packets κ ps

-- a timed item at `natᵗ`: its packet, and a value or END
Item : Set
Item = List ℕ × (ℕ ⊎ ⊤)

-- AN ARRIVAL'S KEY: its tick and the source it came from.  Both
-- machines run the same scripts, so a tick names the same moment on
-- each and a slot names the same script.  A dynamic source's number is
-- not comparable -- the elaboration's mints draw on the same ledger --
-- so each is renamed by the order of its first arrival, past the slots.
Key : Set
Key = ℕ × ℕ

posOf : ℕ → List ℕ → Maybe ℕ
posOf s []       = nothing
posOf s (x ∷ xs) = if x ≡ᵇ s then just 0 else Data.Maybe.map suc (posOf s xs)

rankFrom : ℕ → List ℕ → List Key → List Key
rankFrom n seen []             = []
rankFrom n seen ((t , s) ∷ ks) with s <ᵇ n | posOf s seen
... | true  | _      = (t , s) ∷ rankFrom n seen ks
... | false | just i = (t , n + i) ∷ rankFrom n seen ks
... | false | nothing = (t , n + length seen) ∷ rankFrom n (seen ++ s ∷ []) ks

-- THE RUN CUT AT ITS ARRIVALS: the subscribe's stream, then one per
-- arrival the drain took, each arrival's key, and whether the queue ran
-- dry before the fuel did.  It is the drain's own builder split where it
-- appends, and the erased half says the pieces concatenate to the run
-- `evaluate↓` returns -- so a slice read off them is the run's, not a
-- second machine's.
mutual
  chunks! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st)
          → Σ⁰ (List (Stream Γ t) × List Key × List ℕ × Bool) λ r → concat (proj₁ r) ≡ Σ⁰.fst⁰ (drain! fuel sched st ru)
  chunks! zero    sched st ru = ([] , [] , [] , false) , refl
  chunks! (suc k) sched st ru = chunksOn k sched st ru (sched-next sched) refl

  chunksOn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (k : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st)
           → (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) ({-@0-}eqn : sched-next sched ≡ x)
           → Σ⁰ (List (Stream Γ t) × List Key × List ℕ × Bool) λ r → concat (proj₁ r) ≡ Σ⁰.fst⁰ (drainOn k sched st ru x eqn)
  chunksOn k sched st ru (inj₁ _)            eqn = ([] , [] , [] , true) , refl
  chunksOn k sched st ru (inj₂ (a , sched′)) eqn =
    then! k ((Arrival.tick a , Arrival.source a) ∷ []) (cascade! a sched′ st (pop-rule eqn ru))

  -- a step's stream, then the drain from where it left the queue
  then! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {D : Stream Γ t × Sched Γ × EvalSt e → Set} (k : Fuel)
          (ks : List Key)
          (r : Σ⁰ (Stream Γ t × Sched Γ × EvalSt e) λ r → D r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
        → Σ⁰ (List (Stream Γ t) × List Key × List ℕ × Bool) λ x →
            concat (proj₁ x) ≡ proj₁ (Σ⁰.fst⁰ r) ++
              Σ⁰.fst⁰ (drain! k (proj₁ (proj₂ (Σ⁰.fst⁰ r))) (proj₂ (proj₂ (Σ⁰.fst⁰ r))) (proj₂ (Σ⁰.snd⁰ r)))
  then! k ks ((out , sched′ , st′) , _ , ru′) =
    chunks! k sched′ st′ ru′ |>′ λ ((cs , ks′ , cl , dry) , eq) →
      (out ∷ cs , ks ++ ks′ , counter (Sched.mint sched′) sourceᵏ ∷ cl , dry) , cong (out ++_) eq

cut : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
    → Σ⁰ (List (Stream Γ t) × List Key × List ℕ × Bool) λ r → concat (proj₁ r) ≡ evaluate↓ fuel e ins
cut fuel e ins = then! fuel [] (subscribe! e ins)

-- EACH ARRIVAL'S SLICE, read off the cut with the reading the statement
-- takes the whole run through.  Every step of each reading is
-- element by element, so it commutes with the cut.  The keys come back
-- with their dynamic sources ranked.
implSlices : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
           → List (List (Id × Val (plainᵏ Γ κ) (plainᵗ t))) × List Key × List ℕ × Bool
implSlices {n} κ fuel e ins =
  readSlices (λ s → instExtract (decodeEmits (concat s))) (Σ⁰.fst⁰ (cut fuel (elaborateImpl κ e) (embedSlotsImpl ins)))
  where
    readSlices : ∀ {A B : Set} → (A → B) → List A × List Key × List ℕ × Bool → List B × List Key × List ℕ × Bool
    readSlices f (cs , ks , cl , dry) = map f cs , rankFrom n [] ks , cl , dry

-- the plain run's, one per arrival through the fuel, an arrival past
-- the queue's end sending nothing, and the keys one arrival further:
-- the next arrival's key is where the last run ends
plainSlices : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
            → List (List (Val Γ t)) × List Key
plainSlices {n} fuel e ins with Σ⁰.fst⁰ (cut (suc fuel) (plainExp e) (plainSlots ins))
... | cs , ks , _ = padTo (suc fuel) (take (suc fuel) (map (λ s → plainValues (concat s)) cs)) , rankFrom n [] ks
  where
    padTo : ∀ {A : Set} → ℕ → List (List A) → List (List A)
    padTo zero    xs       = xs
    padTo (suc m) []       = [] ∷ padTo m []
    padTo (suc m) (x ∷ xs) = x ∷ padTo m xs

-- THE IMPL'S FUEL CAP: twice the plain run's and one past.  A queue that
-- runs dry first makes the cap irrelevant, and that is the usual case.
capOf : ℕ → ℕ
capOf f = suc (f + f)

-- A PROGRAM'S TWO RUNS, CUT: the impl's slices through the cap and
-- whether its queue ran dry first, the plain run's through the fuel, and
-- each run's arrival keys
Arr : Set → Set
Arr A = List (List (ℕ × A)) × Bool × List (List A) × List Key × List Key × List ℕ

arrWith : {A : Set} → List (List (ℕ × A)) × List Key × List ℕ × Bool → List (List A) × List Key → Arr A
arrWith (is , ik , cl , dry) (ps , pk) = is , dry , ps , ik , pk , cl

arrPlain : Case → Arr ℕ
arrPlain c = arrWith (implSlices (kinds c) (capOf (fuel c)) (prog c) (slots c))
                     (plainSlices {κ = kinds c} (fuel c) (prog c) (slots c))

-- THE TIMED TRANSLATION'S, a row's dearest side, read by
-- `timing-correct`, `simulation` and `arrival-runs`: a row computes it
-- once and passes it to each
arrTimed : Case → Arr Item
arrTimed c = arrWith (implSlices (kinds c) (capOf (fuel c)) (timed (kinds c) (prog c)) (timedSlots (slots c)))
                     (plainSlices {κ = kinds c} (fuel c) (timed (kinds c) (prog c)) (timedSlots (slots c)))

-- the impl's stamped run at the plain run's fuel: its first slices
stampedAtFuel : {A : Set} → Arr A → List (ℕ × A)
stampedAtFuel (is , _ , ps , _) = concat (take (length ps) is)

stampsOf : Case → List (ℕ × List ℕ)
stampsOf c = packets (kinds c) (stampedAtFuel (arrTimed c))

-- `batchable`: both sides read one run's emits, so the run is an
-- argument and computed once
batchSides : ∀ κ → Burst (Γ₂ᵉ κ) (emitᵗ natᵗ) → List (List ℕ) × List (List ℕ)
batchSides κ es = batchedᴱ {Γ′ = Γ₂ᵉ κ} natᵗ tt es , groupedᴱ {Γ′ = Γ₂ᵉ κ} natᵗ tt es

batchableSides : Case → List (List ℕ) × List (List ℕ)
batchableSides c = batchSides (kinds c) (emitsᴵ (kinds c) (fuel c) (prog c) (slots c))

-- `timed-faithful`: the timed program's run untimed, and the plain run
faithfulSides : Case → List ℕ × List ℕ
faithfulSides c = untimedᵀ tt (kinds c) (fuel c) (prog c) (slots c) , runᴾ (fuel c) (prog c) (slots c)

-- `packets-name-arrivals`: the timed program's plain run, each value's
-- arrival and its packet
namingSides : Case → List ℕ × List (List ℕ)
namingSides c =
  arrivalsOf {κ = kinds c} (fuel c) (timed (kinds c) (prog c)) (timedSlots (slots c)) ,
  map proj₁ (runᴾ {κ = kinds c} (fuel c) (timed (kinds c) (prog c)) (timedSlots (slots c)))

-- `Coherent`, decided: same stamp exactly when same packet
coherentᵇ : ℕ × List ℕ → ℕ × List ℕ → Bool
coherentᵇ (i , p) (j , q) = not ((i ≡ᵇ j) xor eqListℕ p q)

-- `AllPairs`, decided
coheresWith : ℕ × List ℕ → List (ℕ × List ℕ) → Bool
coheresWith x []       = true
coheresWith x (y ∷ ys) = coherentᵇ x y ∧ coheresWith x ys

allPairsᵇ : List (ℕ × List ℕ) → Bool
allPairsᵇ []       = true
allPairsᵇ (x ∷ xs) = coheresWith x xs ∧ allPairsᵇ xs

-- an injective naming of the arrivals by packets, decided: a packet per
-- arrival read, the same exactly when the arrival is.  A finite
-- injection extends to one on all of ℕ, so this is the `Σ`.
namesᵇ : List ℕ × List (List ℕ) → Bool
namesᵇ (ar , ps) = (length ar ≡ᵇ length ps) ∧ allPairsᵇ (zipWith (λ a q → a , q) ar ps)

-- `Agrees` at data, decided: equal, element by element
eqBy : {A : Set} → (A → A → Bool) → List A → List A → Bool
eqBy eq []       []       = true
eqBy eq (x ∷ xs) (y ∷ ys) = eq x y ∧ eqBy eq xs ys
eqBy eq _        _        = false

eqItem : Item → Item → Bool
eqItem (p , inj₁ a) (q , inj₁ b) = eqListℕ p q ∧ (a ≡ᵇ b)
eqItem (p , inj₂ _) (q , inj₂ _) = eqListℕ p q
eqItem _            _            = false

-- an injective naming of the arrivals, decided: as many stamps as
-- arrivals, equal exactly when the arrivals are.  A finite injection
-- always extends to one on all of ℕ, so this is the `Σ`, not a weakening.
renamesᵇ : List ℕ → List ℕ → Bool
renamesᵇ ss ar = (length ss ≡ᵇ length ar) ∧ allPairsᵇ (zipWith (λ s a → s , a ∷ []) ss ar)

-- each plain value's arrival, read off the slices
arrivalsFrom : {A : Set} → ℕ → List (List A) → List ℕ
arrivalsFrom k []       = []
arrivalsFrom k (p ∷ ps) = replicate (length p) k ++ arrivalsFrom (suc k) ps

-- `simulation`, decided at every impl fuel from the plain run's to the
-- cap: the impl run at a fuel is its slices through that fuel
simAtᵇ : {A : Set} → (A → A → Bool) → List A → List ℕ → List (ℕ × A) → Bool
simAtᵇ eq vs ar st = eqBy eq (map proj₂ st) vs ∧ renamesᵇ (map proj₁ st) ar

searchᵇ : {A : Set} → (A → A → Bool) → List A → List ℕ → List (ℕ × A) → List (List (ℕ × A)) → Bool
searchᵇ eq vs ar st []       = simAtᵇ eq vs ar st
searchᵇ eq vs ar st (s ∷ ss) = simAtᵇ eq vs ar st ∨ searchᵇ eq vs ar (st ++ s) ss

simᵇ : {A : Set} → (A → A → Bool) → Arr A → Bool
simᵇ eq (is , _ , ps , _) = searchᵇ eq (concat ps) (arrivalsFrom 0 ps) (concat (take (length ps) is)) (drop (length ps) is)

simulationᴮ : Arr ℕ × Arr Item → Bool
simulationᴮ (p , t) = simᵇ _≡ᵇ_ p ∧ simᵇ eqItem t

-- `arrival-runs`, decided: the impl run's k-th slice against the plain
-- run's k-th, through the fuel, each slice's values carrying one
-- instant, each later slice holding values a later one.  Out of impl
-- slices, every plain slice past them is empty; the cap is past the
-- fuel, so that is a queue run dry, never the cap.
emptyᵇ : {A : Set} → List A → Bool
emptyᵇ []      = true
emptyᵇ (_ ∷ _) = false

-- a slice's one instant, if it holds a value
instantOf : {A : Set} → List (ℕ × A) → List ℕ
instantOf []          = []
instantOf ((i , _) ∷ _) = i ∷ []

stampedᵇ : {A : Set} → ℕ → List (ℕ × A) → Bool
stampedᵇ i []            = true
stampedᵇ i ((j , _) ∷ r) = (j ≡ᵇ i) ∧ stampedᵇ i r

uniformᵇ : {A : Set} → List (ℕ × A) → Bool
uniformᵇ []            = true
uniformᵇ ((i , _) ∷ r) = stampedᵇ i r

-- each instant past the one before it, which is what a clock minting
-- them one arrival at a time gives
risingᵇ : List ℕ → Bool
risingᵇ []           = true
risingᵇ (m ∷ [])     = true
risingᵇ (m ∷ n ∷ ns) = (m <ᵇ n) ∧ risingᵇ (n ∷ ns)

agreeSlicesᵇ : {A : Set} → (A → A → Bool) → List (List (ℕ × A)) → List (List A) → List ℕ → Bool
agreeSlicesᵇ eq []       ps       ns = emptyᵇ (concat ps) ∧ risingᵇ ns
agreeSlicesᵇ eq (r ∷ rs) []       ns = risingᵇ ns
agreeSlicesᵇ eq (r ∷ rs) (p ∷ ps) ns =
  eqBy eq (map proj₂ r) p ∧ uniformᵇ r ∧ agreeSlicesᵇ eq rs ps (ns ++ instantOf r)

lockstepᵇ : {A : Set} → (A → A → Bool) → Arr A → Bool
lockstepᵇ eq (is , _ , ps , _) = agreeSlicesᵇ eq is ps []

arrivalRunsᴮ : Arr ℕ × Arr Item → Bool
arrivalRunsᴮ (p , t) = lockstepᵇ _≡ᵇ_ p ∧ lockstepᵇ eqItem t

-- THE TWO SCHEDULES TICK TOGETHER: the impl's arrival keys are the
-- plain run's, in order, as far as both were read.  A candidate for the
-- schedule half of the correspondence `arrival-runs` recurses on,
-- decided before anything is stated over it.
eqKey : Key → Key → Bool
eqKey (t , s) (u , r) = (t ≡ᵇ u) ∧ (s ≡ᵇ r)

sameKeysᵇ : List Key → List Key → Bool
sameKeysᵇ []       _        = true
sameKeysᵇ _        []       = true
sameKeysᵇ (k ∷ ks) (q ∷ qs) = eqKey k q ∧ sameKeysᵇ ks qs

-- AND EACH ARRIVAL CARRIES ONE INSTANT, MINTED WHILE CASCADING IT:
-- every value's the first's, between the source counter it entered with
-- and the one it left, the subscribe's from zero.  `OneIn`, decided.
sameIdᵇ : {A : Set} → ℕ → List (ℕ × A) → Bool
sameIdᵇ i []            = true
sameIdᵇ i ((j , _) ∷ r) = (i ≡ᵇ j) ∧ sameIdᵇ i r

oneInᵇ : {A : Set} → ℕ → ℕ → List (ℕ × A) → Bool
oneInᵇ lo hi []            = true
oneInᵇ lo hi ((i , _) ∷ r) = (lo ≤ᵇ i) ∧ (i <ᵇ hi) ∧ sameIdᵇ i r

clockedᵇ : {A : Set} → ℕ → List (List (ℕ × A)) → List ℕ → Bool
clockedᵇ lo (r ∷ rs) (hi ∷ hs) = oneInᵇ lo hi r ∧ clockedᵇ hi rs hs
clockedᵇ lo _        _         = true

sameClockᵇ : {A : Set} → Arr A → Bool
sameClockᵇ (is , _ , _ , ik , pk , cl) = sameKeysᵇ ik pk ∧ clockedᵇ 0 is cl

sameClockᴮ : Arr ℕ × Arr Item → Bool
sameClockᴮ (p , t) = sameClockᵇ p ∧ sameClockᵇ t

-- each takes its sides as ONE argument, so a pair is computed once
agreeᴸ : List ℕ × List ℕ → Bool
agreeᴸ (l , r) = eqListℕ l r

-- the plain run between the two joined ones, each a prefix of the next
sandwichᴸ : List ℕ × List ℕ × List ℕ → Bool
sandwichᴸ (l , p , l′) = prefixListℕ l p ∧ prefixListℕ p l′

agreeᴮ : List (List ℕ) × List (List ℕ) → Bool
agreeᴮ (l , r) = eqBatches l r

holds : Statement → Case → Arr ℕ → Arr Item → Bool
holds left-to-rightˢ  c p t = sandwichᴸ (ltrSides c)
holds timing-correctˢ c p t = allPairsᵇ (packets (kinds c) (stampedAtFuel t))
holds batchableˢ      c p t = agreeᴮ (batchableSides c)
holds timed-faithfulˢ c p t = agreeᴸ (faithfulSides c)
holds simulationˢ     c p t = simulationᴮ (p , t)
holds arrival-runsˢ c p t = arrivalRunsᴮ (p , t)
holds batched-sandwichˢ c p t = sandwichᴸ (bsSides c)
holds packets-name-arrivalsˢ c p t = namesᵇ (namingSides c)
holds same-clockˢ c p t = sameClockᴮ (p , t)
holds storeˢ c p t = proj₁ (storeSides (fuel c) (prog c) (slots c))

checksWith : List Statement → Case → Arr ℕ → Arr Item → List (String × Bool)
checksWith ss c p t = map (λ s → statementName s , holds s c p t) ss

checksOf : List Statement → Case → List (String × Bool)
checksOf ss c = checksWith ss c (arrPlain c) (arrTimed c)
