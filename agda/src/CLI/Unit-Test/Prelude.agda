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
open import Data.List using (List; []; _∷_; _++_; map; length; zipWith; concat; take; drop; replicate)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_; _+_)
open import Data.Fin using (zero; suc)
open import Data.String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Vec using () renaming (_∷_ to _∷ⱽ_; [] to []ⱽ)
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Function.Base using (_|>′_)

open import Rx.Prim using (ObservableInput; hot; cold; Fuel; Id)
open import Rx.Exp using (Ctx; Val; Closed; natᵗ; obs; inputsBelowᵉ; FlatOp)
open import Rx.Slots using (Slots)
open import SExp.Syntax using (SExp; plainᵏ; plainᵗ; Kinds; hotᵏ; coldᵏ; sharedᵏ; emptyˢ; emitᵗ;
  flattenˢ; mapˢ; pairˢ; inlˢ; inrˢ; unitˢ; varˢᵗ)
open import Rx.Evaluator using (Burst; Stream; Sched; EvalSt; Arrival; sched-next)
open import Rx.Evaluator.Builder using (drain!; drainOn; cascade!; pop-rule; subscribe!; evaluate↓)
open import Rx.Evaluator.Reducible.Support using (Σ⁰; _,_; Rule)
open import SExp.Plain using (plainExp; plainValues)
open import SExp.Simul-Slots using (SimulSlots; SimulSlot; hotˢ; coldˢ; sharedˢ; plainSlots)
open import SExp.InstEmit.Decode using (decodeEmits)
open import CLI.Emit-Eq using (eqListℕ; prefixListℕ; eqBatches)
open import SExp.Pipeline using (emitsᴵ; runᴾ; elaborateImpl; embedSlotsImpl)
open import Timed.Translation using (packetOf; timedᶜ; itemᵗ; timed; timedSlots)
open import Batchable.Inst-Extract using (instExtract)
open import Left-To-Right.Statement using (joinedᴵ)
open import Batchable.Statement using (batchedᴱ; groupedᴱ)
open import Timed.Faithful using (untimedᵀ)

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
-- NO CAP.  A `takeᵉ` above the program -- counted in InstEmits or in
-- values -- runs a different program from the one the row names, and a
-- capped run is an instance of no statement.  The fuel is the one budget
-- the statements quantify over, so it is the one a row may set.
------------------------------------------------------------------

data Statement : Set where
  left-to-rightˢ timing-correctˢ batchableˢ timed-faithfulˢ simulationˢ arrival-runsˢ : Statement

-- in `Main`'s order, which is the order a report counts them in, then
-- the simulation and the leaf it stands on
statements : List Statement
statements = left-to-rightˢ ∷ timing-correctˢ ∷ batchableˢ ∷ timed-faithfulˢ ∷ simulationˢ ∷ arrival-runsˢ ∷ []

statementName : Statement → String
statementName left-to-rightˢ  = "left-to-right"
statementName timing-correctˢ = "timing-correct"
statementName batchableˢ      = "batchable"
statementName timed-faithfulˢ = "timed-faithful"
statementName simulationˢ     = "simulation"
statementName arrival-runsˢ = "arrival-runs"

-- `left-to-right`: the batches joined back up, the plain run, and the
-- batches joined back up at one more unit of fuel.  Every side at the
-- case's one fuel: that names the impl's own fuel as the plain run's,
-- which is a witness and not the statement, so a green decides it and a
-- red is a candidate, to be read at a larger impl fuel.
ltrSides : Case → List ℕ × List ℕ × List ℕ
ltrSides c = joinedᴵ tt (kinds c) (fuel c) (prog c) (slots c) , runᴾ (fuel c) (prog c) (slots c) ,
             joinedᴵ tt (kinds c) (1 + fuel c) (prog c) (slots c)

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

-- THE RUN CUT AT ITS ARRIVALS: the subscribe's stream, then one per
-- arrival the drain took, and whether the queue ran dry before the fuel
-- did.  It is the drain's own builder split where it appends, and the
-- erased half says the pieces concatenate to the run `evaluate↓` returns
-- -- so a slice read off them is the run's, not a second machine's.
mutual
  chunks! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            (fuel : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st)
          → Σ⁰ (List (Stream Γ t) × Bool) λ r → concat (proj₁ r) ≡ Σ⁰.fst⁰ (drain! fuel sched st ru)
  chunks! zero    sched st ru = ([] , false) , refl
  chunks! (suc k) sched st ru = chunksOn k sched st ru (sched-next sched) refl

  chunksOn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             (k : Fuel) (sched : Sched Γ) (st : EvalSt e) ({-@0-}ru : Rule sched st)
           → (x : ⊤ ⊎ (Arrival Γ × Sched Γ)) ({-@0-}eqn : sched-next sched ≡ x)
           → Σ⁰ (List (Stream Γ t) × Bool) λ r → concat (proj₁ r) ≡ Σ⁰.fst⁰ (drainOn k sched st ru x eqn)
  chunksOn k sched st ru (inj₁ _)            eqn = ([] , true) , refl
  chunksOn k sched st ru (inj₂ (a , sched′)) eqn = then! k (cascade! a sched′ st (pop-rule eqn ru))

  -- a step's stream, then the drain from where it left the queue
  then! : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {D : Stream Γ t × Sched Γ × EvalSt e → Set} (k : Fuel)
          (r : Σ⁰ (Stream Γ t × Sched Γ × EvalSt e) λ r → D r × Rule (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
        → Σ⁰ (List (Stream Γ t) × Bool) λ x →
            concat (proj₁ x) ≡ proj₁ (Σ⁰.fst⁰ r) ++
              Σ⁰.fst⁰ (drain! k (proj₁ (proj₂ (Σ⁰.fst⁰ r))) (proj₂ (proj₂ (Σ⁰.fst⁰ r))) (proj₂ (Σ⁰.snd⁰ r)))
  then! k ((out , sched′ , st′) , _ , ru′) =
    chunks! k sched′ st′ ru′ |>′ λ ((cs , dry) , eq) → (out ∷ cs , dry) , cong (out ++_) eq

cut : ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ)
    → Σ⁰ (List (Stream Γ t) × Bool) λ r → concat (proj₁ r) ≡ evaluate↓ fuel e ins
cut fuel e ins = then! fuel (subscribe! e ins)

-- EACH ARRIVAL'S SLICE, read off the cut with the reading the statement
-- takes the whole run through.  Every step of each reading is
-- element by element, so it commutes with the cut.
implSlices : ∀ {n} {Γ : Ctx n} {t} (κ : Kinds n) → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
           → List (List (Id × Val (plainᵏ Γ κ) (plainᵗ t))) × Bool
implSlices κ fuel e ins =
  readSlices (λ s → instExtract (decodeEmits (concat s))) (Σ⁰.fst⁰ (cut fuel (elaborateImpl κ e) (embedSlotsImpl ins)))
  where
    readSlices : ∀ {A B : Set} → (A → B) → List A × Bool → List B × Bool
    readSlices f (cs , dry) = map f cs , dry

-- the plain run's, one per arrival through the fuel, an arrival past
-- the queue's end sending nothing
plainSlices : ∀ {n} {Γ : Ctx n} {κ : Kinds n} {t} → Fuel → SExp Γ [] [] [] t → SimulSlots Γ κ
            → List (List (Val Γ t))
plainSlices fuel e ins =
  padTo (suc fuel) (map (λ s → plainValues (concat s)) (proj₁ (Σ⁰.fst⁰ (cut fuel (plainExp e) (plainSlots ins)))))
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
-- whether its queue ran dry first, and the plain run's through the fuel
Arr : Set → Set
Arr A = List (List (ℕ × A)) × Bool × List (List A)

arrWith : {A : Set} → List (List (ℕ × A)) × Bool → List (List A) → Arr A
arrWith (is , dry) ps = is , dry , ps

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
stampedAtFuel (is , _ , ps) = concat (take (length ps) is)

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
simᵇ eq (is , _ , ps) = searchᵇ eq (concat ps) (arrivalsFrom 0 ps) (concat (take (length ps) is)) (drop (length ps) is)

simulationᴮ : Arr ℕ × Arr Item → Bool
simulationᴮ (p , t) = simᵇ _≡ᵇ_ p ∧ simᵇ eqItem t

-- `arrival-runs`, decided: ψ built greedily.  Each plain slice takes
-- impl slices, at least one, until what they hold agrees with it, and
-- refutes once they hold as many values and do not.  Closing at the
-- first agreement loses nothing: what a later close would add is empty,
-- and the next run is free to take it.  Every run's values carry one
-- instant, and no two runs holding values share one.  Out of impl
-- slices with the queue dry, every slice past it is empty; out of them
-- with fuel left, it is undecided at the cap and reads as a failure.
emptyᵇ : {A : Set} → List A → Bool
emptyᵇ []      = true
emptyᵇ (_ ∷ _) = false

-- a run's one instant, if it holds a value
instantOf : {A : Set} → List (ℕ × A) → List ℕ
instantOf []          = []
instantOf ((i , _) ∷ _) = i ∷ []

stampedᵇ : {A : Set} → ℕ → List (ℕ × A) → Bool
stampedᵇ i []            = true
stampedᵇ i ((j , _) ∷ r) = (j ≡ᵇ i) ∧ stampedᵇ i r

uniformᵇ : {A : Set} → List (ℕ × A) → Bool
uniformᵇ []            = true
uniformᵇ ((i , _) ∷ r) = stampedᵇ i r

-- `n` among `ns`
amongᵇ : ℕ → List ℕ → Bool
amongᵇ n []       = false
amongᵇ n (m ∷ ms) = (m ≡ᵇ n) ∨ amongᵇ n ms

distinctᵇ : List ℕ → Bool
distinctᵇ []       = true
distinctᵇ (n ∷ ns) = not (amongᵇ n ns) ∧ distinctᵇ ns

mutual
  runsᵇ : {A : Set} → (A → A → Bool) → List (List (ℕ × A)) → Bool → List (List A) → List ℕ → Bool
  runsᵇ eq is dry []       ns = distinctᵇ ns
  runsᵇ eq is dry (p ∷ ps) ns = runᵇ eq [] is dry p ps ns

  runᵇ : {A : Set} → (A → A → Bool) → List (ℕ × A) → List (List (ℕ × A)) → Bool → List A → List (List A)
       → List ℕ → Bool
  runᵇ eq acc []       dry p ps ns =
    dry ∧ eqBy eq (map proj₂ acc) p ∧ uniformᵇ acc ∧ emptyᵇ (concat ps) ∧ distinctᵇ (ns ++ instantOf acc)
  runᵇ eq acc (i ∷ is) dry p ps ns =
    closeᵇ eq (acc ++ i) is dry p ps ns

  closeᵇ : {A : Set} → (A → A → Bool) → List (ℕ × A) → List (List (ℕ × A)) → Bool → List A → List (List A)
         → List ℕ → Bool
  closeᵇ eq acc is dry p ps ns =
    if eqBy eq (map proj₂ acc) p then uniformᵇ acc ∧ runsᵇ eq is dry ps (ns ++ instantOf acc)
    else ((length acc <ᵇ length p) ∧ runᵇ eq acc is dry p ps ns)

-- one run's half of it, untimed or timed
runsOfᵇ : {A : Set} → (A → A → Bool) → Arr A → Bool
runsOfᵇ eq (is , dry , ps) = runsᵇ eq is dry ps []

arrivalRunsᴮ : Arr ℕ × Arr Item → Bool
arrivalRunsᴮ (p , t) = runsOfᵇ _≡ᵇ_ p ∧ runsOfᵇ eqItem t

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

checksWith : List Statement → Case → Arr ℕ → Arr Item → List (String × Bool)
checksWith ss c p t = map (λ s → statementName s , holds s c p t) ss

checksOf : List Statement → Case → List (String × Bool)
checksOf ss c = checksWith ss c (arrPlain c) (arrTimed c)
