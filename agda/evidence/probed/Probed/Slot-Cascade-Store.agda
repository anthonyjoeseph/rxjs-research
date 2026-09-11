-- ══════════════════════════════════════════════════════════════════
-- THE TELESCOPE THAT SUBSCRIBING ONE REFERENCE WALKS THROUGH, WHERE
-- THE SUMMAND HAS TO REACH A SLOT NOBODY NAMED.
--
-- TARGET: subscribeSharedSlot-sz-store @048f7d
-- TARGET: pushBurst-sz-store-scan @8db9e9
--
-- WHAT EVERY SLOT ROW SO FAR LEFT OPEN, and both statements left it
-- open in the SAME place.  A telescope is stratified, so slot k's
-- definition may reference a slot below it, and `sharedConnect`
-- subscribes that definition -- which re-enters the very door being
-- priced.  One subscription therefore walks a CHAIN of definitions,
-- and only the first of them is named anywhere in the call.  Every
-- witness at this half has stood at a telescope of ONE, where a slot
-- that cascades and a slot that does not are the same slot, so
-- nothing has yet said whether the summand is owed the definitions
-- the walk arrives at or only the one it starts from.
--
-- THE ROWS, at the smallest family that separates anything.  A
-- reifying scan parked in slot zero, and above it references that
-- carry no syntax of their own: a slot whose whole definition is
-- `input` below it charges ONE, so the subscribed slot's own reading
-- is as near nothing as the telescope permits while the slot the
-- cascade lands on holds the emission.  Read at one hop and at two,
-- and once more through the scan door, where the source resolving a
-- shared slot is the shape that face's rows declined.
--
-- WHAT THEY FIND.  The stated sum holds and every reading short of it
-- fails: the charge over the slot the call NAMES, the charge over the
-- named slot and the one it passes through, and the charge with the
-- telescope dropped.  So the summand is owed the TRANSITIVE reach of
-- the connect and not the reference's own entry, which is a fact
-- about which slots the sum ranges over rather than about its size.
-- All three are taken in SLOT SIZES, which is why they are indifferent
-- to how the term half of the sum is spelled.  The scan face then
-- confirms the stated sum from the other side, at the shape that
-- face's own rows declined: a source that resolves a shared slot
-- rather than a written-out program.
--
-- WHAT THE ROWS DO NOT BUY, and the first half is a boundary rather
-- than a gap.  Whether the summand is really a SUM or really a MAXIMUM
-- cannot be instantiated here at all: the charge is GEOMETRIC in it,
-- so the largest slot alone already clears the table by a margin that
-- a second slot could only be needed to cross -- and crossing it at
-- this corpus's rate of growth asks for a stored value of some half a
-- million units, which is a program of half a million leaves.  The
-- separation these rows do buy is the other one, over which slots are
-- counted rather than how they are combined.  And beyond that: one
-- connect per hop, no queue, no second arm, and a chain whose every
-- upper slot is a bare reference.
-- ══════════════════════════════════════════════════════════════════
module Probed.Slot-Cascade-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad)
open import Rx.Exp using (Ctx; Closed; Fn; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; scanᵉ; input; varᵗ; sndᵗ; strmᵗ; sizeᵉ; evalTm)
open import Rx.Slots using (Slots; shared; slotSize; slotsSize)
open import Rx.Evaluator using (EvalSt; Sched; root; _↠_; scan-st; scan-f;
  installNode; st-init; sched-init; iterSize; subscribeSharedSlot; subscribeE)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (descChg; subscribeSharedSlot-sz-store; pushBurst-sz-store-scan)
open import Refuted.Frame-Step-Size-Slot using (Pw; chnG)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE DEFINITION THE CASCADE LANDS ON.  A duplication chain under a
-- scan whose step throws the accumulator away and re-wraps the
-- arriving value as a one-shot observable, which is the one step that
-- converts an EMISSION into a STORE reading.
----------------------------------------------------------------------
K : ℕ
K = 6

keepG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (obs (Pw k) ×ᵗ Pw k) (obs (Pw k))
keepG = strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))

reifyG : ∀ {n} {Γ : Ctx n} (k : ℕ) → Closed Γ (obs (Pw k))
reifyG k = scanᵉ keepG (strmᵗ emptyᵉ) (chnG k)

----------------------------------------------------------------------
-- WITNESS ONE — ONE HOP.  Slot one's whole definition is the
-- reference below it, so the subscribed slot's own reading is one
-- unit of syntax and the definition that writes is the slot the
-- connect arrives at.
----------------------------------------------------------------------
Γᴬ : Ctx 2
Γᴬ = obs (Pw K) ∷ⱽ obs (Pw K) ∷ⱽ []ⱽ

slᴬ : Slots Γᴬ
slᴬ fz        = shared (reifyG K)
slᴬ (fsuc fz) = shared (input fz)

eᴬ : Closed Γᴬ (obs (Pw K))
eᴬ = input (fsuc fz)

-- LOAD-BEARING: the second entry is what says the cascade happened at
-- all.  A connect that declined to resolve the reference would leave
-- the table empty and every row below would read `true` for a reason
-- that has nothing to do with the summand.
hopFigures : ℕ
hopFigures =
  let r  = subscribeSharedSlot {e = eᴬ} (gasPad 64 g0) (fsuc fz) (input fz)
             root 0 0 (sched-init eᴬ slᴬ) (st-init eᴬ)
      ns = EvalSt.nodes (proj₂ (proj₂ r))
  in slotsSize slᴬ + 1000 * length ns

hopFigures≡ : hopFigures ≡ 1036
hopFigures≡ = refl

-- LOAD-BEARING: the second entry is the charge over the slot the call
-- NAMES and the third is the charge with the telescope dropped.  Both
-- fail, so the row separates a sum ranging over the connect's reach
-- from one ranging over its entry.
hopRows : List Bool
hopRows =
  let r  = subscribeSharedSlot {e = eᴬ} (gasPad 64 g0) (fsuc fz) (input fz)
             root 0 0 (sched-init eᴬ slᴬ) (st-init eᴬ)
      ns = EvalSt.nodes (proj₂ (proj₂ r))
  in all (λ kv → boundedNode (iterSize 2 (slotsSize slᴬ) 1) (proj₂ kv)) ns
   ∷ all (λ kv → boundedNode (iterSize 2 (slotSize (slᴬ (fsuc fz))) 1)
                   (proj₂ kv)) ns
   ∷ all (λ kv → boundedNode 1 (proj₂ kv)) ns
   ∷ []

hopRows≡ : hopRows ≡ true ∷ false ∷ false ∷ []
hopRows≡ = refl

----------------------------------------------------------------------
-- WITNESS TWO — TWO HOPS, which is the axis that turns "the summand
-- reaches the next slot" into "it reaches the connect's transitive
-- closure".  A charge stopping one slot short is still short.
----------------------------------------------------------------------
Γᴮ : Ctx 3
Γᴮ = obs (Pw K) ∷ⱽ obs (Pw K) ∷ⱽ obs (Pw K) ∷ⱽ []ⱽ

slᴮ : Slots Γᴮ
slᴮ fz               = shared (reifyG K)
slᴮ (fsuc fz)        = shared (input fz)
slᴮ (fsuc (fsuc fz)) = shared (input (fsuc fz))

eᴮ : Closed Γᴮ (obs (Pw K))
eᴮ = input (fsuc (fsuc fz))

-- LOAD-BEARING: the second entry counts the named slot AND the one the
-- first connect passes through, and still fails -- so what is short is
-- the reach and not the arithmetic.
farRows : List Bool
farRows =
  let r  = subscribeSharedSlot {e = eᴮ} (gasPad 64 g0) (fsuc (fsuc fz))
             (input (fsuc fz)) root 0 0 (sched-init eᴮ slᴮ) (st-init eᴮ)
      ns = EvalSt.nodes (proj₂ (proj₂ r))
  in all (λ kv → boundedNode (iterSize 2 (slotsSize slᴮ) 1) (proj₂ kv)) ns
   ∷ all (λ kv → boundedNode
                   (iterSize 2 (slotSize (slᴮ (fsuc fz))
                                + slotSize (slᴮ (fsuc (fsuc fz)))) 1)
                   (proj₂ kv)) ns
   ∷ []

farRows≡ : farRows ≡ true ∷ false ∷ []
farRows≡ = refl

----------------------------------------------------------------------
-- WITNESS THREE — THE SCAN DOOR, whose source resolves a shared slot.
-- Same region from the other side: the term's own descent charge is
-- what a bare reference leaves it, and the telescope is the rest.
----------------------------------------------------------------------
Γᶜ : Ctx 1
Γᶜ = Pw K ∷ⱽ []ⱽ

slᶜ : Slots Γᶜ
slᶜ fz = shared (chnG K)

eᶜ : Closed Γᶜ (obs (Pw K))
eᶜ = scanᵉ keepG (strmᵗ emptyᵉ) (input fz)

Bᶜ : ℕ
Bᶜ = sizeᵉ eᶜ

-- LOAD-BEARING: the middle entry is the whole of what reading the
-- PROGRAM TERM buys at this shape.  A descent charge that saw through
-- the reference would report the slot's own syntax here instead.
scanFigures : ℕ
scanFigures = Bᶜ
            + 1000 * descChg (obs (obs (Pw K))) Bᶜ eᶜ
            + 1000000 * slotsSize slᶜ

scanFigures≡ : scanFigures ≡ 27037009
scanFigures≡ = refl

-- LOAD-BEARING: it fails for any level the resolved cascade's stored
-- emission outruns, and the cascade is what puts that emission in the
-- table -- a door that declined to resolve the reference leaves
-- nothing here to bound.
-- DEAD ROUTE: separating the TELESCOPE summand at this door, by
--   reading the same table at the term's charge with the summand
--   dropped.  The charge now carries a delivery block geometric in
--   the size bound, and it clears this table on its own -- so the row
--   holds either way and decides nothing.  Recovering the separation
--   needs a telescope whose climb outruns that block, which at this
--   corpus's rate of growth is a slot of some hundreds of leaves; the
--   separation the cascade witnesses above buy is over WHICH slots are
--   counted, and it is taken in slot sizes rather than through the
--   charge, so it is untouched by this.
scanRows : List Bool
scanRows =
  let r  = subscribeE (gasPad 64 g0) eᶜ root 0 0
             (sched-init eᶜ slᶜ) (st-init eᶜ)
      ns = EvalSt.nodes (proj₂ (proj₂ r))
  in all (λ kv → boundedNode
                   (iterSize 2 (descChg (obs (obs (Pw K))) Bᶜ eᶜ
                                + slotsSize slᶜ) Bᶜ)
                   (proj₂ kv)) ns
   ∷ []

scanRows≡ : scanRows ≡ true ∷ []
scanRows≡ = refl

----------------------------------------------------------------------
-- THE TIES.  The types are generated from the statements as they
-- read, so a restatement changes them rather than leaving the rows
-- above copied out beside a claim.  The premises are left as
-- arguments: each row asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the same point the rows are, so a table the
-- resolved cascade outran would fail it exactly as the charge over the
-- named slot beside it does.
tieHop : Confirms
  (subscribeSharedSlot-sz-store {e = eᴬ} slᴬ (gasPad 64 g0) (fsuc fz)
     (input fz) root 0 0 (sched-init eᴬ slᴬ) (st-init eᴬ) 2 1
     (iterSize 2 (slotsSize slᴬ) 1))
tieHop = λ _ _ _ _ _ → refl

-- LOAD-BEARING: the same statement one hop further along the
-- telescope, which is this witness's axis.
tieFar : Confirms
  (subscribeSharedSlot-sz-store {e = eᴮ} slᴮ (gasPad 64 g0) (fsuc (fsuc fz))
     (input (fsuc fz)) root 0 0 (sched-init eᴮ slᴮ) (st-init eᴮ) 2 1
     (iterSize 2 (slotsSize slᴮ) 1))
tieFar = λ _ _ _ _ _ → refl

-- LOAD-BEARING: the scan face at the shape its own rows declined, a
-- cell whose source is a slot rather than a written-out program.
-- the mint is the caller's now, so the point is taken past it
schedS : Sched Γᶜ
schedS = record (sched-init eᶜ slᶜ) { nextNode = 1 }

stS : EvalSt eᶜ
stS = installNode 0 (scan-st (evalTm (strmᵗ (emptyᵉ {t = Pw K})))) (st-init eᶜ)

tieScan : Confirms
  (pushBurst-sz-store-scan {e = eᶜ} slᶜ (gasPad 64 g0) keepG
     (strmᵗ (emptyᵉ {t = Pw K})) (input fz) 0 root 0 0
     schedS stS
     (subscribeE (gasPad 64 g0) (input fz) (scan-f keepG 0 ↠ root) 0 0
        schedS stS)
     2 Bᶜ
     (iterSize 2 (descChg (obs (obs (Pw K))) Bᶜ eᶜ + slotsSize slᶜ) Bᶜ))
tieScan = λ _ _ _ _ _ _ → refl
