-- THE INPUT BOUND ON AN OBSERVABLE THE RUN MANUFACTURES, AT THE FLOORS
-- THE RUN ACTUALLY SUPPLIES.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHY THE STATEMENT IS FALSE AND THE ROWS ARE STILL WORTH TAKING.  Over
-- an arbitrary floor the target is refuted outright, so no row here can
-- be read as evidence for it as written.  What the rows decide is the
-- different question the refutation leaves open and that the whole
-- repair rests on: whether the pairs a RUN produces — a value carried
-- into a flattener together with the floor of the chain it is carried
-- on — satisfy the predicate.  If they do, the demand can be met by
-- letting the registration decide its own floor test, and the bound
-- becomes a theorem about a branch nothing reaches.
--
-- WHERE THE PAIRS COME FROM, AND WHY NONE OF THEM IS WRITTEN DOWN.  A
-- floor strictly inside the context arises in exactly one way: the
-- connect of a shared slot walks that slot's stored definition at the
-- slot's own index.  So each program below flattens inside a share's
-- def, and the value the flattener is handed is read back out of the
-- machine's own node table — a bounded merge keeps its second inner in
-- a queue, so the value that reached the consuming clause is a state
-- the loop wrote rather than a term this file picked.  Each extraction
-- is pinned by `refl` to what the run left there, so a row cannot go
-- green over an empty queue.
--
-- WHAT SEPARATES A READING FROM A VACUITY HERE.  The tight program's
-- inner names the slot directly beneath the share, so the floor the
-- connect supplies is the smallest one that works and the control at
-- one below it computes to `false`; the loose program's inner reaches
-- two slots down and survives that same control.  The pair therefore
-- reads the BOUND rather than the flattener's shape, since a value
-- drifting by a single slot fails one row and not the other.
--
-- AND THE THIRD PROGRAM IS THE ONE THAT COULD HAVE FAILED, because its
-- inner is not a subterm of anything: the flattener's outer is a `map`
-- whose function BUILDS an observable around the arriving number, so
-- the queued value is a substitution instance that exists nowhere in
-- the program text.  That is the manufacture the target's own header
-- says the syntax cannot reach, and it is the only route by which a
-- value could carry an input the def's stored bound never saw.
--
-- NOT COVERED: a value manufactured under a μ-unfold, and a flattener
-- reached through a second share rather than through the root — every
-- row connects one share, one level deep.  Nor is the other direction
-- probed at all, since it cannot be: the scripted slot is the only
-- other way a value enters a run, and its own constructor refuses an
-- observable element type, which is a closure the rows record rather
-- than instantiate.
--
-- TARGET: below-inner @6878ca
module Probed.Inner-Bound where

open import Data.Bool using (T; false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; isData; inputsBelowᵉ;
  input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; mergeAllᵉ; strmᵗ; varᵗ; nat̂; _≟ᵗ_)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator using (EvalSt; NodeId; NodeState; mergeAll-st; root; subscribeE; rootWitness; sched-init; st-init)
open import Rx.Inputs-Below using (below-ctx; below-inner)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT.  Three slots, so the shared one at the top leaves two
-- positions beneath it and the floor its connect supplies can be missed
-- in either direction.
----------------------------------------------------------------------

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

----------------------------------------------------------------------
-- THE DEFINITIONS THE SHARE STORES.  Each is a bounded merge over a
-- pair of inners, so the first is subscribed and the second is left in
-- the node's queue where it can be read back.  The `shared`
-- constructor's own bound is solved by eta, which is the fact that
-- makes each of these representable at all.
----------------------------------------------------------------------

defTight : Closed Γ₃ natᵗ
defTight = mergeAllᵉ (just 1)
  (ofᵉ (strmᵗ (input (suc zero)) ∷ strmᵗ (input (suc zero)) ∷ []))

defLoose : Closed Γ₃ natᵗ
defLoose = mergeAllᵉ (just 1)
  (ofᵉ (strmᵗ (input zero) ∷ strmᵗ (input zero) ∷ []))

-- the inner that is BUILT rather than named: the arriving number
-- becomes a take-count around a slot the def is allowed to reach, so
-- the queued value is a substitution instance
mkObs : Fn Γ₃ [] [] [] natᵗ (obs natᵗ)
mkObs = strmᵗ (takeᵉ (varᵗ (here refl)) (input (suc zero)))

defBuilt : Closed Γ₃ natᵗ
defBuilt = mergeAllᵉ (just 1) (mapᵉ mkObs (input zero))

----------------------------------------------------------------------
-- THE SLOT TELESCOPES.  Slot zero delivers its numbers inside the
-- subscribe frame, which is what lets the built program's map run
-- before the run is read.
----------------------------------------------------------------------

insOf : (d : Closed Γ₃ natᵗ) → T (inputsBelowᵉ 2 d) → Slots Γ₃
insOf d ok zero             = scripted (cold (9 ∷ 8 ∷ []) (after 0 , 7 ∷ []))
insOf d ok (suc zero)       = scripted (cold (5 ∷ []) (after 0 , 4 ∷ []))
insOf d ok (suc (suc zero)) = shared d {ok}

prog : Closed Γ₃ natᵗ
prog = input (suc (suc zero))

----------------------------------------------------------------------
-- THE RUN, AND THE READ-BACK.  `subscribeE` at the context size is the
-- root's own entry; the share connect beneath it is what descends to a
-- floor of two.  Nothing here constructs a state.
----------------------------------------------------------------------

runSt : (d : Closed Γ₃ natᵗ) → T (inputsBelowᵉ 2 d) → EvalSt prog
runSt d ok with subscribeE {lo = 3} (rootWitness prog (insOf d ok)) prog
                 root 0 0
                 (sched-init prog (insOf d ok)) (st-init prog)
... | (_ , _ , st) = st

queuedAll : List (NodeId × NodeState Γ₃) → List (Closed Γ₃ natᵗ)
queuedAll []                                   = []
queuedAll ((_ , mergeAll-st {w} _ _ q _) ∷ r) with w ≟ᵗ natᵗ
... | yes refl = q ++ queuedAll r
... | no  _    = queuedAll r
queuedAll (_ ∷ r)                              = queuedAll r

queued : (d : Closed Γ₃ natᵗ) → T (inputsBelowᵉ 2 d) → List (Closed Γ₃ natᵗ)
queued d ok = queuedAll (EvalSt.nodes (runSt d ok))

first : List (Closed Γ₃ natᵗ) → Closed Γ₃ natᵗ
first (o ∷ _) = o
first []      = emptyᵉ

inner : (d : Closed Γ₃ natᵗ) → T (inputsBelowᵉ 2 d) → Closed Γ₃ natᵗ
inner d ok = first (queued d ok)

----------------------------------------------------------------------
-- WHAT THE RUN LEFT, first, because it is what every row below stands
-- on: a queue that came back empty would send each `Confirms` row to a
-- default the machine never produced.
----------------------------------------------------------------------

tightQueued : queued defTight tt ≡ input (suc zero) ∷ []      -- LOAD-BEARING
tightQueued = refl

looseQueued : queued defLoose tt ≡ input zero ∷ []            -- LOAD-BEARING
looseQueued = refl

builtQueued : queued defBuilt tt ≡ takeᵉ (nat̂ 8) (input (suc zero)) ∷ []  -- LOAD-BEARING
builtQueued = refl

----------------------------------------------------------------------
-- THE CONTROLS.  Each drops the floor by one from what the connect
-- supplies and the predicate computes to `false`, so the empty type is
-- reachable along this conclusion at these very values.  The loose row
-- survives its neighbour's control, which is what makes the pair a
-- reading of the floor rather than of the flattener.
----------------------------------------------------------------------

tightGround : inputsBelowᵉ 1 (inner defTight tt) ≡ false       -- LOAD-BEARING
tightGround = refl

builtGround : inputsBelowᵉ 1 (inner defBuilt tt) ≡ false       -- LOAD-BEARING
builtGround = refl

looseGround : inputsBelowᵉ 0 (inner defLoose tt) ≡ false       -- LOAD-BEARING
looseGround = refl

-- and the loose value at the tight control's floor, which is the half
-- that says the two rows are not measuring the same thing
looseSurvives : Confirms (below-inner {Γ = Γ₃} 1 (inner defLoose tt))
looseSurvives = tt

----------------------------------------------------------------------
-- THE ROWS.  Two is the floor the share connect supplies, and each is
-- the target applied at this probe's own point, so Agda generates the
-- type from the statement as it reads.
----------------------------------------------------------------------

tightRow : Confirms (below-inner {Γ = Γ₃} 2 (inner defTight tt))
tightRow = tt

looseRow : Confirms (below-inner {Γ = Γ₃} 2 (inner defLoose tt))
looseRow = tt

builtRow : Confirms (below-inner {Γ = Γ₃} 2 (inner defBuilt tt))
builtRow = tt

----------------------------------------------------------------------
-- THE CLOSURE, which is a row about what CANNOT be instantiated: the
-- only other way a value enters a run is a scripted slot, and its
-- constructor demands a data element type.  So no script can hand the
-- machine an observable at all, and the manufacture the rows above
-- cover is the whole of the space.
----------------------------------------------------------------------

scriptShut : isData (obs natᵗ) ≡ false                      -- LOAD-BEARING
scriptShut = refl
