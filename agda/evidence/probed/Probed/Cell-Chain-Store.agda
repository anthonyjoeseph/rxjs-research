-- ══════════════════════════════════════════════════════════════════
-- A TABLE WHOSE CELLS WERE WRITTEN IN SERIES, WHICH IS THE SHAPE THE
-- SINGLE CLIMB HAS NEVER BEEN ASKED ABOUT.
--
-- TARGET: subscribeE-sz-store @f8b804
--
-- WHAT EVERY STORE ROW SO FAR DECLINED.  Each witness at either half
-- subscribes a program that installs ONE node, and the refutation
-- that set this denomination says so in as many words.  So the
-- conclusion has only ever been read where the table it bounds is one
-- cell wide, and a climb that covered a chain by accident would look
-- exactly the same there.  The chain is the shape where a per-cell
-- reading and a per-consumption reading come apart: the level counts
-- the arriving program's layers ONCE, while the cells are written one
-- after another and each holds what the one below it emitted.
--
-- THE ROWS.  A reifying scan, whose emission is fed to a `mergeAll`,
-- whose emission is fed to a SECOND reifying scan -- arriving at a
-- `thru-outer` frame as one value, so subscribing it writes the whole
-- chain into one table in one step.  The frame is read rather than the
-- subscription directly, and at ONE arrival, a door with room and no
-- close the two are the same table: the fold has a single step, the
-- wrap moves nothing, and the bump between them moves a live count the
-- reading does not price.  Against it, a control that is the same scan
-- alone, which writes one cell.  Both tables are read at the SAME two
-- rungs, at the smallest level the statement admits, so what the rows
-- compare is the number of climbs a table needs and not the size of
-- the program that wrote it.
--
-- WHAT THEY FIND.  The chain is really built -- the table the frame
-- leaves is three cells wider than the one it entered, against one
-- for the control -- and it costs the same rungs.  One climb fails on
-- both tables and two clear both, so a cell holding what the cell
-- below it emitted is priced by the emission and not by its position
-- in the chain: the series does not compound.  That is the drained
-- queue's max arriving at the other arm and at cells rather than at
-- entries, and it is why counting the arrival's layers once is not
-- short here.
--
-- WHAT THE ROWS DO NOT BUY.  One chain, of one length, at one door,
-- with a telescope of a single scripted slot -- so nothing about a
-- chain each of whose cells resolves a SLOT, where the summand would
-- be doing the work, and nothing about the inner arm, whose charge
-- reads the parked queue rather than the arrival.  And the rungs are
-- read at the smallest level the statement admits, which is the
-- sharpest reading available and not a tight one: the charge counts
-- twelve rungs where these tables need two.
-- ══════════════════════════════════════════════════════════════════
module Probed.Cell-Chain-Store where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (all)
open import Data.List using (List; []; _∷_; length)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_)
open import Data.Product using (proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Data.Fin using () renaming (zero to fz)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (g0; gasPad; hot)
open import Rx.Exp using (Ctx; Closed; Val; Fn; natᵗ; obs; _×ᵗ_;
  emptyᵉ; ofᵉ; scanᵉ; mergeAllᵉ; varᵗ; sndᵗ; strmᵗ; sizeᵉ)
open import Rx.Slots using (Slots; scripted; slotsSize)
open import Rx.Layer-Count using (layᵛˢ; layᵉ)
open import Rx.Evaluator using (EvalSt; root; mergeAllᵒ; thru-outer;
  from-inner; _↠_;
  mergeAll-st; installNode; st-init; sched-init; iterSize; stepFrame)
open import Verify-Budget-Sufficient.Measures using (boundedNode)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsSz?; subscribeE-sz-store)
open import Refuted.Frame-Step-Size-Slot using (Pw; chnG)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CHAIN.  `keepG` throws the accumulator away and re-wraps the
-- arriving value as a one-shot observable, which is the one step that
-- turns an EMISSION into a STORE reading; a `mergeAll` between two of
-- them is what makes the second scan's cell hold what the first one's
-- run produced rather than what the program spells.
----------------------------------------------------------------------
keepG : ∀ {n} {Γ : Ctx n} {k} → Fn Γ [] [] [] (obs (Pw k) ×ᵗ Pw k) (obs (Pw k))
keepG = strmᵗ (ofᵉ (sndᵗ (varᵗ (here refl)) ∷ []))

Γᶜ : Ctx 1
Γᶜ = natᵗ ∷ⱽ []ⱽ

slᶜ : Slots Γᶜ
slᶜ fz = scripted (hot [])

lowC : Closed Γᶜ (obs (Pw 8))
lowC = scanᵉ keepG (strmᵗ emptyᵉ) (chnG 8)

midC : Closed Γᶜ (Pw 8)
midC = mergeAllᵉ nothing lowC

topC : Closed Γᶜ (obs (Pw 8))
topC = scanᵉ keepG (strmᵗ emptyᵉ) midC

eᶜ : Closed Γᶜ (obs (Pw 8))
eᶜ = emptyᵉ

----------------------------------------------------------------------
-- THE DOOR, AND THE TWO ARRIVALS: the chain, and the control that is
-- its bottom rung alone.
----------------------------------------------------------------------
stᶜ : EvalSt eᶜ
stᶜ = installNode 0
        (mergeAll-st {Γ = Γᶜ} {t = obs (Pw 8)} nothing 0 [] false)
        (st-init eᶜ)

valsChain : List (Val Γᶜ (obs (obs (Pw 8))))
valsChain = topC ∷ []

valsFlat : List (Val Γᶜ (obs (obs (Pw 8))))
valsFlat = lowC ∷ []

postChain : EvalSt eᶜ
postChain = proj₂ (proj₂ (proj₂ (proj₂
              (stepFrame {e = eᶜ} (gasPad 64 g0) 0 0 (thru-outer mergeAllᵒ 0)
                 root valsChain false (sched-init eᶜ slᶜ) stᶜ))))

postFlat : EvalSt eᶜ
postFlat = proj₂ (proj₂ (proj₂ (proj₂
             (stepFrame {e = eᶜ} (gasPad 64 g0) 0 0 (thru-outer mergeAllᵒ 0)
                root valsFlat false (sched-init eᶜ slᶜ) stᶜ))))

----------------------------------------------------------------------
-- THE FIGURES.
----------------------------------------------------------------------

-- LOAD-BEARING: the two arrivals' layer counts stand apart, so a
-- reading that charged the CHAIN what it charges the control would
-- have to say so here; and the telescope is one scripted slot, so
-- what the rungs below are bought by is the arrival.
chainFigures : List ℕ
chainFigures = layᵛˢ {Γ = Γᶜ} (obs (obs (Pw 8))) valsChain
             ∷ layᵛˢ {Γ = Γᶜ} (obs (obs (Pw 8))) valsFlat
             ∷ slotsSize slᶜ
             ∷ sizeᵉ topC
             ∷ sizeᵉ lowC
             ∷ []

chainFigures≡ : chainFigures ≡ 11 ∷ 9 ∷ 1 ∷ 52 ∷ 43 ∷ []
chainFigures≡ = refl

-- LOAD-BEARING, and this file's premise: the chain writes THREE cells
-- where the control writes one, so the rows below are read at a table
-- nothing has stood at.  Equal counts would say the door flattened
-- the chain and the rows decide nothing.
chainNodes≡ : length (EvalSt.nodes stᶜ) ∷ length (EvalSt.nodes postChain)
            ∷ length (EvalSt.nodes postFlat) ∷ [] ≡ 1 ∷ 4 ∷ 2 ∷ []
chainNodes≡ = refl

----------------------------------------------------------------------
-- THE RUNGS THE TWO TABLES NEED, at the smallest level the statement
-- admits.  A charge is a rung COUNT, so the question a chain raises
-- is answered by counting rungs and not by clearing a charge: the
-- statement's own reading stands far above both readings below.
----------------------------------------------------------------------

-- LOAD-BEARING all four ways.  The first and third fail, so neither
-- table is bought by the program being small; the second and fourth
-- hold at the SAME rung, so the chain's three cells cost what the
-- control's one does.  A series that compounded would clear the
-- second later than the fourth.
chainRows : List Bool
chainRows =
    all (λ kv → boundedNode (iterSize 2 1 52) (proj₂ kv))
        (EvalSt.nodes postChain)
  ∷ all (λ kv → boundedNode (iterSize 2 2 52) (proj₂ kv))
        (EvalSt.nodes postChain)
  ∷ all (λ kv → boundedNode (iterSize 2 1 52) (proj₂ kv))
        (EvalSt.nodes postFlat)
  ∷ all (λ kv → boundedNode (iterSize 2 2 52) (proj₂ kv))
        (EvalSt.nodes postFlat)
  ∷ []

chainRows≡ : chainRows ≡ false ∷ true ∷ false ∷ true ∷ []
chainRows≡ = refl

-- LOAD-BEARING: the value premise at the bound the rows are read at,
-- spelled out so the witness cannot be read as one that merely fails
-- to satisfy it.
chainPrem≡ : valsSz? {Γ = Γᶜ} {s = obs (obs (Pw 8))} 52 valsChain ≡ true
chainPrem≡ = refl

----------------------------------------------------------------------
-- THE TIE.  The type is generated from the statement as it reads, so
-- a restatement changes it rather than leaving the rungs above copied
-- out beside a claim.  The premises are left as arguments: the row
-- asserts the conclusion with them unasked.
----------------------------------------------------------------------

-- LOAD-BEARING: read at the level the rows are, so a table the chain
-- outran would fail it exactly as one climb does above.  The point is
-- the one the merging door hands the descent -- the caller's path under
-- a `from-inner` decoration, one gas spent, the minted instance
-- counted -- so the row computes what a crossing at this state
-- computes.
tieCellChain : Confirms
  (subscribeE-sz-store {e = eᶜ} slᶜ (gasPad 63 g0) topC
     (from-inner mergeAllᵒ 0 0 ↠ root) 0 0
     (record (sched-init eᶜ slᶜ) { nextNode = 1 }) stᶜ 2 52
     (iterSize 2 (layᵉ topC + slotsSize slᶜ) 52))
tieCellChain = λ _ _ _ _ _ → refl
