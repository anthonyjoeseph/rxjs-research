-- ══════════════════════════════════════════════════════════════════
-- THE SIZE WALK'S FAN-OUT FOLD READS EVERY ENTRY AT THE LEVEL THE
-- FIRST ONE ENTERED AT, AND THE FIRST ENTRY'S OWN RUN MOVES THE TABLE
-- PAST IT.
--
-- REFUTATIONS: machine-checked `… → ⊥`.  See EVIDENCE.md for why this
-- tree is outside `agda/src` and how it relates to `-- DEAD ROUTE`
-- notes.
--
-- WHAT THE STATEMENT SAID.  A sink hands the arriving values to every
-- admitted chain in turn, and the size walk charges each delivered
-- entry one reading of the node table.  The claim is that a fan's
-- worth of those readings follows from what a consumer can hold about
-- the fan as a whole: the table bounded once at the state the fan is
-- entered at, the values bounded there, and a size receipt per
-- admitted path.
--
-- WHY IT LOOKED RIGHT.  The entry reading genuinely is available --
-- it is the walk's own head projection, and the first entry of any
-- fan is exactly the case a chain door already discharges.  What the
-- shape hides is that the SECOND entry's reading is taken at a state
-- the first entry's whole run produced, and the level it is taken at
-- did not move.
-- ══════════════════════════════════════════════════════════════════

-- WHERE IT BREAKS.  A chain reaching a drain door subscribes what the
-- `*All` node has parked, and the subscribed program installs a node
-- of its own.  Park one duplication chain behind such a door and the
-- accumulator the subscription stores is exponential in a program of
-- size sixty-three, against a rung of eight thousand and one.  So the
-- fan enters with the table under the rung and leaves the first entry
-- with it over -- and the second entry is charged the same rung.
--
-- AND THE CAPS FACE ALREADY PAYS FOR THIS, WHICH IS WHAT MAKES IT A
-- MECHANISM FINDING RATHER THAN A ROW.  The caps walk's own fan-out
-- fold threads a level increment per entry under an absolute ceiling,
-- so its readings are taken where the fold has reached; the size
-- walk's fold is the same recursion with the increment missing.  The
-- two are otherwise clause for clause identical, which is why the
-- gap is invisible from either one alone.

-- WHAT DIES AND WHAT DOES NOT.  What dies is the reconstruction of a
-- fan's readings from a fan-wide hypothesis at one level -- every
-- consumer that spends the size walk across a sink is spending that.
-- What stands is the reading itself: the second row below takes the
-- same table at the level a per-entry advance would have reached and
-- it holds, so the quantity is coverable and it is the fold's
-- bookkeeping that is not.  Neither row says the advance is
-- AFFORDABLE once the ledger has to pay for it.

-- WHAT IS HAND-BUILT.  The parked queue is installed rather than
-- reached by a run, so the state is a claim about the predicate and
-- not about reachability; the fan list is passed directly, since the
-- fold takes it as an argument and never consults the registry.  Both
-- are the shapes the predicate quantifies over.
module Refuted.Fan-Store-Level where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n)
open import Data.Product using (proj₁; proj₂; _×_; _,_)
open import Data.Vec using (lookup) renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Rx.Prim using (Gas; g0; gasPad; Id; Tick; close; exhausted)
open import Rx.Exp using (Ctx; Ty; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; mapᵉ; scanᵉ; nat̂; varᵗ; pairᵗ; sndᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; shared)
open import Rx.Evaluator using (Sched; EvalSt; Path; root; _↠_; RegId;
  from-inner; mergeAllᵒ; mergeAll-st; installNode; foldPath;
  sched-init; st-init; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk using (valsSz?; shareGoSzOK)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT RATHER THAN IMPORTED.  Importing the
-- postulate would prove the tower inconsistent instead of refuting
-- anything.  The predicate it concludes in IS imported, since that is
-- the object under test and a transcription of it would be refuting a
-- copy.  The cap is a free numeral rather than the face's own
-- `capsAt`, which returns at no program: the crossing below is a
-- crossing at whatever size the fan is read at, so the free form is
-- stronger than the tied one rather than weaker.
----------------------------------------------------------------------
ShareGoFixed : Set
ShareGoFixed = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (S W k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sched : Sched Γ) (st : EvalSt e) →
  length vals ≤ W →
  all (λ kv → boundedNode (iterSize S k S) (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? (iterSize S k S) vals ≡ true →
  all (λ rp → pathSz? S (proj₂ rp)) ps ≡ true →
  shareGoSzOK S W k sf gas id now i vals fin ps sched st

f≡t : false ≡ true → ⊥
f≡t ()

----------------------------------------------------------------------
-- THE PROGRAM.  `chain 13` duplicates thirteen times, so its syntax
-- measures fifty-five and it emits at `2 ^ 14 - 1`; `keep` discards
-- the accumulator and stores the arriving value back as a one-shot
-- observable, which is the step that converts an EMISSION into a
-- store reading.  The slot is a shared definition rather than a
-- script because the fan's element type is an observable one, which
-- is what puts a drainable queue at the sink in the first place.
----------------------------------------------------------------------
Pow : ℕ → Ty
Pow zero    = natᵗ
Pow (suc k) = Pow k ×ᵗ Pow k

K : ℕ
K = 13

Γ₂ : Ctx 1
Γ₂ = obs (Pow K) ∷ⱽ []ⱽ

sl₂ : Slots Γ₂
sl₂ fzero = shared emptyᵉ

dup : ∀ {k} → Fn Γ₂ [] [] [] (Pow k) (Pow (suc k))
dup = pairᵗ (varᵗ (here refl)) (varᵗ (here refl))

chain : (k : ℕ) → Closed Γ₂ (Pow k)
chain zero    = ofᵉ (nat̂ 0 ∷ [])
chain (suc k) = mapᵉ dup (chain k)

keep : Fn Γ₂ [] [] [] (obs (Pow K) ×ᵗ Pow K) (obs (Pow K))
keep = strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))

inner : Closed Γ₂ (obs (Pow K))
inner = scanᵉ keep (strmᵗ emptyᵉ) (chain K)

e₂ : Closed Γ₂ (obs (Pow K))
e₂ = emptyᵉ

-- LOAD-BEARING FIGURES: the parked program the entry reading covers,
-- and the rung one level of the ladder buys at that cap.
figures : List ℕ
figures = sizeᵉ inner ∷ iterSize 63 1 63 ∷ []

figures≡ : figures ≡ 63 ∷ 8001 ∷ []
figures≡ = refl

----------------------------------------------------------------------
-- THE FAN.  Two admitted entries at one sink: a drain door and a bare
-- hand-back.  Neither is cancelled, so both are charged, and the
-- second is charged at the state the first one's run leaves.
----------------------------------------------------------------------
st : EvalSt e₂
st = installNode 0 (mergeAll-st {Γ = Γ₂} {t = obs (Pow K)} nothing 1
                     (inner ∷ []) true)
       (st-init e₂)

drain : Path Γ₂ (obs (Pow K)) (obs (Pow K))
drain = from-inner mergeAllᵒ 0 7 ↠ root

fan : List (RegId × Path Γ₂ (obs (Pow K)) (obs (Pow K)))
fan = (0 , drain) ∷ (1 , root) ∷ []

-- the two premises the fan owes, at the fan's own entry state
entry : all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv))
            (EvalSt.nodes st) ≡ true
entry = refl

paths : all (λ rp → pathSz? 63 (proj₂ rp)) fan ≡ true
paths = refl

vals₀ : valsSz? {Γ = Γ₂} {s = obs (Pow K)} (iterSize 63 1 63) [] ≡ true
vals₀ = refl

----------------------------------------------------------------------
-- THE CROSSING.  The second entry's reading is taken at the state the
-- first entry's fold produced, and at the level the fan was entered
-- at, which is the one quantity the fold does not move.
----------------------------------------------------------------------
after : EvalSt e₂
after = proj₂ (proj₂ (foldPath (gasPad 8 g0) 1 0 0 0 drain []
          (close 0 exhausted ∷ []) true (sched-init e₂ sl₂)
          (record st { delivered = 0 ∷ EvalSt.delivered st })))

-- LOAD-BEARING: it is the second entry's own conjunct, at the level
-- the fold hands it, and it fails where the entry row above holds.
tailRow : all (λ kv → boundedNode (iterSize 63 1 63) (proj₂ kv))
              (EvalSt.nodes after) ≡ false
tailRow = refl

-- LOAD-BEARING against the reading being uncoverable: the same table
-- at the level a per-entry advance reaches, where it holds.  A
-- crossing that had outrun every rung would report `false` twice.
advanced : all (λ kv → boundedNode (iterSize 63 63 63) (proj₂ kv))
               (EvalSt.nodes after) ≡ true
advanced = refl

fan-store-level-absurd : ShareGoFixed → ⊥
fan-store-level-absurd pr =
  f≡t (trans (sym tailRow)
             (proj₁ (proj₂ (proj₂
               (pr {e = e₂} 63 63 1 (gasPad 8 g0) 1 0 0 fzero [] true fan
                   (sched-init e₂ sl₂) st z≤n entry vals₀ paths)))))
