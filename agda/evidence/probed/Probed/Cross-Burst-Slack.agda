-- ══════════════════════════════════════════════════════════════════
-- WHETHER A CROSSING'S BURST REALLY OUTRUNS THE RUNGS ITS DOOR WAS
-- CHARGED, WHICH IS AN ARITHMETIC QUESTION AND NOT A STRUCTURAL ONE.
--
-- TARGET: pushBurst-sz-store-outer @2e9e3f
--
-- WHAT IS AT STAKE, AND IT IS THE DENOMINATION RATHER THAN THIS LEAF.
-- The obvious route through the fold spends the delivered bound on the
-- arrival and then climbs again for what re-subscribing it writes, so
-- it asks for the arrival's layers and the telescope a SECOND time --
-- rungs the door's own premise does not carry.  What makes that worth
-- instantiating before restating anything is that the callers cannot
-- pay it either: a crossing arm holds exactly the ceiling its parent
-- was handed, so a leaf asking for more rungs than `suc (layᵉ b)` is
-- unsatisfiable at every site that would use it and the charge the
-- whole descent is denominated in has to move.  A route being short is
-- not a statement being false, and only one of the two costs anything
-- to find out.
--
-- THE ROWS, AND WHY THE ARRIVAL IS BUILT TO PARK.  A door over a
-- reifying scan -- the step discards its accumulator and stores the
-- arriving datum back as an observable -- fed a duplication chain,
-- which is the shape that makes a run's payload exponential in a
-- program's layers while its syntax stays linear in them.  The stored
-- observable is a merging door of its OWN with no room, so
-- re-subscribing it PARKS the payload in a fresh cell: without that
-- the arrival is a one-shot that installs nothing, the fold's table is
-- the subscription's table, and a row could not have failed.  Both
-- tables are then read at the same rungs, since what settles the
-- question is whether the crossing needs a rung the subscription
-- underneath it did not.
--
-- WHAT THEY FIND.  The fold costs no rung of its own: at either chain
-- length the parked cell clears at exactly the rung the subscription's
-- own cell needs, so the two columns never separate.  And the charge
-- outgrows the need.  Four further layers of duplication multiply the
-- payload by sixteen and so cost TWO rungs -- the tables clear at two
-- and at four -- while the door's charge over the same four layers
-- rises by four, from eleven to fifteen.  That is `S * suc (2 * s)`
-- against a doubling: a rung at the tightest `S` the statement admits
-- still quadruples, so the slack widens with the witness rather than
-- being a constant a bigger one would eat.
--
-- WHAT THE ROWS DO NOT BUY, AND ONE OF IT IS A REFUTATION CANDIDATE.
-- A layer of THIS chain doubles what the run carries, which is why the
-- rungs outrun it; an arrival carrying a `μ` is the shape where that
-- fails, since unfolding SQUARES a size and no layer charge grows with
-- it -- and squaring outruns a rung, which multiplies.  So these rows
-- say nothing about that shape and it is where the statement would
-- break if it breaks.  Nor do they reach a source whose emission is
-- manufactured by the TELESCOPE rather than by the program, where the
-- layer count is 0 and the rungs are bought by `slotsSize` alone.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cross-Burst-Slack where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad; hot)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; scanᵉ; mergeAllᵉ; varᵗ; sndᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Layer-Count using (layᵉ)
open import Rx.Evaluator using (EvalSt; Sched; Stream; root; _↠_;
  mergeAllᵒ; switchᵒ; exhaustᵒ; thru-outer;
  mergeAll-st; switch-st; exhaust-st; installNode; st-init; sched-init;
  subscribeE; pushBurst; iterSize)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (pushBurst-sz-store-outer)
open import Refuted.Frame-Step-Size-Slot using (Pw; chnG)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE SOURCE THE DOOR SUBSCRIBES.  `keepB` throws the accumulator away
-- and stores the arriving datum back as an observable, which is the
-- one step that turns an EMISSION into a store reading; the chain
-- under it makes that emission exponential in the layers the scan is
-- charged for, and the roomless merging door inside it is what makes
-- re-subscribing the emission write a cell of its own.
----------------------------------------------------------------------
Γᵇ : Ctx 1
Γᵇ = natᵗ ∷ⱽ []ⱽ

slᵇ : Slots Γᵇ
slᵇ fz = scripted (hot [])

keepB : ∀ {k} → Fn Γᵇ [] [] [] (obs (Pw k) ×ᵗ Pw k) (obs (Pw k))
keepB = strmᵗ (mergeAllᵉ (just 0)
          (ofᵉ (strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ [])) ∷ [])))

srcAt : (k : ℕ) → Closed Γᵇ (obs (Pw k))
srcAt k = scanᵉ keepB (strmᵗ emptyᵉ) (chnG k)

eAt : (k : ℕ) → Closed Γᵇ (Pw k)
eAt k = emptyᵉ

----------------------------------------------------------------------
-- THE DOOR, RUN FOR REAL.  The mint and the initial cell are the
-- caller's work, so the state carries the node already and the
-- schedule has moved past it; the subscription is then the leaf's own
-- `r`, and the fold is entered at exactly the table that subscription
-- left.
----------------------------------------------------------------------
stAt : (k : ℕ) → EvalSt (eAt k)
stAt k = installNode 0 (mergeAll-st {Γ = Γᵇ} {t = Pw k} nothing 0 [] false)
           (st-init (eAt k))

schedAt : (k : ℕ) → Sched Γᵇ
schedAt k = record (sched-init (eAt k) slᵇ) { nextNode = 1 }

subAt : (k : ℕ) → Stream Γᵇ (obs (Pw k)) × Sched Γᵇ × EvalSt (eAt k)
subAt k = subscribeE (gasPad 64 g0) (srcAt k)
            (thru-outer mergeAllᵒ 0 ↠ root) 0 0 (schedAt k) (stAt k)

afterAt : (k : ℕ) → EvalSt (eAt k)
afterAt k = proj₂ (proj₂
  (pushBurst (gasPad 64 g0) 0 0 (thru-outer mergeAllᵒ 0) root
     (proj₁ (subAt k)) (proj₁ (proj₂ (subAt k))) (proj₂ (proj₂ (subAt k)))))

----------------------------------------------------------------------
-- THE FIGURES.
----------------------------------------------------------------------

-- LOAD-BEARING: the layer counts and the sizes are what the rungs
-- below are bought by, and both are LINEAR in the chain length while
-- the value the run carries is not.  A reading that had grown with the
-- run would not report nine and thirteen here.
figures : List ℕ
figures = layᵉ (srcAt 8) ∷ sizeᵉ (srcAt 8)
        ∷ layᵉ (srcAt 12) ∷ sizeᵉ (srcAt 12)
        ∷ slotsSize slᵇ ∷ []

figures≡ : figures ≡ 9 ∷ 47 ∷ 13 ∷ 63 ∷ 1 ∷ []
figures≡ = refl

-- LOAD-BEARING, and this file's premise twice over: the fold has
-- something to push, and pushing it WRITES.  An empty burst would make
-- `pushBurst` the identity and a table it left unchanged would make
-- every row below a reading of the subscription instead of the
-- crossing -- which is what a one-shot arrival does, and why this one
-- parks.
liveness : List ℕ
liveness = length (proj₁ (subAt 8))
         ∷ length (EvalSt.nodes (proj₂ (proj₂ (subAt 8))))
         ∷ length (EvalSt.nodes (afterAt 8)) ∷ []

liveness≡ : liveness ≡ 1 ∷ 2 ∷ 3 ∷ []
liveness≡ = refl

----------------------------------------------------------------------
-- THE RUNGS EACH TABLE NEEDS, read as a CLIMB from the program's own
-- size and read at BOTH tables.  A charge is a rung COUNT, so what
-- settles whether a second block is owed is the count the fold's table
-- needs against the count the subscription's already needed -- not
-- whether some ceiling clears them both.
----------------------------------------------------------------------
premRow : (k j : ℕ) → Bool
premRow k j = all (λ kv → boundedNode (iterSize 2 j (sizeᵉ (srcAt k))) (proj₂ kv))
                  (EvalSt.nodes (proj₂ (proj₂ (subAt k))))

concRow : (k j : ℕ) → Bool
concRow k j = all (λ kv → boundedNode (iterSize 2 j (sizeᵉ (srcAt k))) (proj₂ kv))
                  (EvalSt.nodes (afterAt k))

-- LOAD-BEARING at both ends and at both lengths.  Each length is read
-- at the rung BELOW the one it needs and at that one, so neither table
-- is bought by the program being large enough to cover its own run;
-- and each pair holds together, so the fold's table clears exactly
-- where the subscription's does.  A crossing owing a rung of its own
-- would separate the two columns, and the two lengths are what the
-- charge is measured against: four layers move the need by two.
climbRows : List Bool
climbRows = premRow 8 1 ∷ concRow 8 1
          ∷ premRow 8 2 ∷ concRow 8 2
          ∷ premRow 12 3 ∷ concRow 12 3
          ∷ premRow 12 4 ∷ concRow 12 4 ∷ []

climbRows≡ : climbRows ≡ false ∷ false ∷ true ∷ true
                       ∷ false ∷ false ∷ true ∷ true ∷ []
climbRows≡ = refl

-- LOAD-BEARING: the leaf's own store premise at the ceiling the tie is
-- read at, spelled out so the point cannot be read as one that merely
-- fails to satisfy it.
ceilRows : List Bool
ceilRows = premRow 8 11 ∷ premRow 12 15 ∷ []

ceilRows≡ : ceilRows ≡ true ∷ true ∷ []
ceilRows≡ = refl

----------------------------------------------------------------------
-- THE OTHER TWO SINKS, at the same source and the same rung.  Each is
-- entered at its own idle cell, so the admission rule is the live one:
-- a switch cancels what it holds as the emission lands and an exhaust
-- drops what arrives while busy, and the fold is read down all three.
----------------------------------------------------------------------
stSw : EvalSt (eAt 8)
stSw = installNode 0 (switch-st {Γ = Γᵇ} nothing false) (st-init (eAt 8))

stEx : EvalSt (eAt 8)
stEx = installNode 0 (exhaust-st {Γ = Γᵇ} false false) (st-init (eAt 8))

subSw : Stream Γᵇ (obs (Pw 8)) × Sched Γᵇ × EvalSt (eAt 8)
subSw = subscribeE (gasPad 64 g0) (srcAt 8)
          (thru-outer switchᵒ 0 ↠ root) 0 0 (schedAt 8) stSw

subEx : Stream Γᵇ (obs (Pw 8)) × Sched Γᵇ × EvalSt (eAt 8)
subEx = subscribeE (gasPad 64 g0) (srcAt 8)
          (thru-outer exhaustᵒ 0 ↠ root) 0 0 (schedAt 8) stEx

-- LOAD-BEARING: each door ADMITS this emission and subscribes it
-- itself, so the same rung is reached down three different admission
-- paths rather than only the one that lets everything in.
sinkRows : List Bool
sinkRows =
    all (λ kv → boundedNode (iterSize 2 2 47) (proj₂ kv))
        (EvalSt.nodes (proj₂ (proj₂
          (pushBurst (gasPad 64 g0) 0 0 (thru-outer switchᵒ 0) root
             (proj₁ subSw) (proj₁ (proj₂ subSw)) (proj₂ (proj₂ subSw))))))
  ∷ all (λ kv → boundedNode (iterSize 2 2 47) (proj₂ kv))
        (EvalSt.nodes (proj₂ (proj₂
          (pushBurst (gasPad 64 g0) 0 0 (thru-outer exhaustᵒ 0) root
             (proj₁ subEx) (proj₁ (proj₂ subEx)) (proj₂ (proj₂ subEx))))))
  ∷ []

sinkRows≡ : sinkRows ≡ true ∷ true ∷ []
sinkRows≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so a
-- restatement changes it rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the ceiling the door's own premise carries and
-- at the tightest `S` the statement admits, which is where a rung buys
-- the least it ever buys.  A crossing that outran its charge would
-- fail here exactly as the climb's first rows do.
tieBurstSlack : Confirms
  (pushBurst-sz-store-outer {e = eAt 8} slᵇ (gasPad 64 g0) mergeAllᵒ 0
     (srcAt 8) root 0 0 (schedAt 8) (stAt 8) (subAt 8) 2 47
     (iterSize 2 11 47))
tieBurstSlack = λ _ _ _ _ _ _ → refl
