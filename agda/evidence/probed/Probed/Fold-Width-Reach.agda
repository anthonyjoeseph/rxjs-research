-- THE BINARY THE FOLD ARM WAITS ON, AND IT IS A CHOICE BETWEEN TWO
-- WIDTH READINGS RATHER THAN A COVERAGE CLAIM.  `scanΦ-fit` sets a
-- depth fixed before an instant runs against a delivery count that
-- towers in it, and every denomination tried so far moves both numbers
-- together -- which is why this file is a FORK and not a receipt: its
-- product is that two candidate readings of the same width DISAGREE,
-- not that either one held.
--
-- THE TWO CANDIDATES.  `admitted` is the recurrence as it stands: one
-- fold's worst case puts the previous width in an EXPONENT, so the cap
-- at level J is a power TOWER of height J.  `fanout` is the reading the
-- arm's own header proposes instead -- a program fans out per hop by at
-- most its size, so J hops buy J sizes and the cap is LINEAR in the
-- level.  They agree at the entry and part at the first hop, which is
-- what `separates` pins.
--
-- FORK: scanΦ-fit
--
-- AND THE ROWS SAY WHICH SIDE THE SYNTAX SITS ON, which is the
-- whole reason the fork can be DECIDED rather than merely stated.  The
-- family is the one shape that can tower a width at all: a `scanᵉ`
-- whose step names its accumulator twice, wrapped in the `mergeAllᵉ`
-- that turns the doubled accumulator into emissions.  One layer is
-- `foldStep` written in the syntax instead of in the caps, and `k`
-- layers iterate it.
--
-- THE ANSWER THE ROWS GIVE IS `admitted`, AND IT IS NOT A CAP ARTEFACT.
-- `outWⱽ` is the frame face's OWN width reading, defined over syntax
-- and slots with no cap anywhere in it, and a fold takes the source's
-- payload count into an EXPONENT -- on the INNER reading, which the
-- outer one multiplies by only when a FLATTEN consumes it.  So a bare
-- scan is flat here and one LAYER, scan under flatten, takes a width
-- to a power of itself; the syntactic reading then towers in the
-- layer count exactly as the recurrence does.  The linear reading is
-- therefore not a tightening the arm is waiting for -- it is refuted by
-- a measure this tower already computes, at the smallest program that
-- can express a refold.  What that costs the arm is its FIELD repair:
-- a width carried on the invariant record would be denominated in this
-- measure, and there is no field to thread when the measure towers.

-- THE MEASURED SIDE REACHES ONE LAYER, AND IT CROSSES THERE.  A
-- flatten emits nothing in the frame that SUBSCRIBES it, so a layered
-- program delivers its widths only in LATER frames and the entry burst
-- reads a flat zero at every `k ≥ 1`.  `drain` drives those frames off
-- the state the subscribe actually produced, so no hand-built state is
-- priced, and the widest instant at one layer then outruns the linear
-- reading at the program's own size -- the crossing is MEASURED and
-- not merely syntactic.

-- AND WHAT HELD THE FAMILY TO THE ENTRY WAS THE SEED, NOT THE SLOT.
-- The drive does want TWO slots doing different jobs, since a cold
-- script drains and a base sharing its slot with the refolds leaves
-- them reading nothing.  But splitting the slots and driving both in
-- later frames still read zero: every payload the flatten subscribes
-- descends from the `emptyᵉ` seed, and an empty observable emits
-- nothing however long it is driven.  Seeding the driven layer from a
-- real source is what opens it, at sizes the row below pins equal to
-- the syntactic family's -- so the two readings are compared at one
-- program's measurements and not across two.
module Probed.Fold-Width-Reach where

open import Data.List using (List; []; _∷_; _++_; length; foldr)
open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _<ᵇ_)
open import Data.Maybe using (nothing)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Val; natᵗ; scanᵉ; mergeAllᵉ; emptyᵉ; input;
  strmᵗ; sizeᵉ)
open import Rx.Prim using (InstEmit; Timed; after_,_; cold)
open import Rx.Slots using (Slots; scripted)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Evaluator using (subscribeE; drain; splitEvents; Stream; root;
  sched-init; st-init; widAt)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Scan-Burst-Nest using (deepen; slots; sync; gas)
open import Probed.Apparatus using (Separates; separates-at)

----------------------------------------------------------------------
-- THE FAMILY.  One layer is a doubling fold flattened, which is the
-- `foldStep` shape in the syntax rather than in the caps.
----------------------------------------------------------------------

layer : Closed Γ₂ natᵗ → Closed Γ₂ natᵗ
layer e = mergeAllᵉ nothing (scanᵉ deepen (strmᵗ emptyᵉ) e)

tower : ℕ → Closed Γ₂ natᵗ
tower zero    = input (fsuc fzero)
tower (suc k) = layer (tower k)

sizeOf : ℕ → ℕ
sizeOf k = sizeᵉ (tower k)

----------------------------------------------------------------------
-- THE TWO CANDIDATES, at one signature so the disagreement is a value
-- and not a paragraph.  BOTH READINGS ARE TAKEN AT THE SETTING MOST
-- FAVOURABLE TO THE LINEAR ONE, so that its loss below is not an
-- artefact of the dials: `admitted` is read at a size base of two, the
-- smallest the caps face admits and every larger base only widens the
-- gap, while `fanout` is given the program's OWN size at each level
-- rather than a fixed one.
----------------------------------------------------------------------

admitted : ℕ → ℕ
admitted J = widAt 2 1 J

fanout : ℕ → ℕ
fanout J = suc (J * sizeOf J)

-- LOAD-BEARING, and it is this file's product: the two readings part
-- at the FIRST hop, so no instantiation of the arm can be read as
-- evidence for both.  `apart` cannot be written when they agree.
separates : Separates admitted fanout
separates = separates-at 1 (λ ())

----------------------------------------------------------------------
-- WHICH SIDE THE SYNTAX SITS ON.
----------------------------------------------------------------------

-- the frame face's own width reading, at slot fuel the program's size
-- and the same two-value script every row here uses
synW : ℕ → ℕ
synW k = outWⱽ (sizeOf k) [] (slots 2) (tower k)

admittedRow : List ℕ
admittedRow = admitted 0 ∷ admitted 1 ∷ admitted 2 ∷ admitted 3 ∷ []

admittedRow≡ : admittedRow ≡ 1 ∷ 4 ∷ 32 ∷ 8589934592 ∷ []
admittedRow≡ = refl

census : ℕ
census = sizeOf 0 + 100 * sizeOf 1 + 10000 * sizeOf 2

census≡ : census ≡ 251301
census≡ = refl

-- THE THREE WIDTHS, and the shape of the growth is the finding: the
-- step from the second to the third carries a factor `2 ^ 8`, which is
-- the SECOND width in an exponent.  That is `foldStep` -- so the
-- syntactic reading towers in the layer count, with no cap anywhere in
-- its definition.
widths : ℕ
widths = synW 0 + 100 * synW 1

widths≡ : widths ≡ 801
widths≡ = refl

width2≡ : synW 2 ≡ 22528
width2≡ = refl

-- LOAD-BEARING, and the row that decides the fork: at two layers the
-- syntax admits a width the linear reading cannot reach, at the
-- linear reading's own most generous setting.  A family whose width
-- grew per hop by at most its size would put this at `false`.
outruns : (fanout 2 <ᵇ synW 2) ≡ true
outruns = refl

-- AND THE ENTRY IS WHERE THEY AGREE, which is what makes the row above
-- a crossing rather than a scale difference.
agrees : fanout 0 ≡ synW 0
agrees = refl

----------------------------------------------------------------------
-- THE ENTRY ROW, RUN -- the only layer count the subscribe BURST
-- reaches on its own; the later frames are driven further down.
----------------------------------------------------------------------

instW : ∀ {t} → Stream Γ₂ t → List ℕ
instW         []         = []
instW {t = t} (em ∷ ems) =
  length (proj₁ (splitEvents {A = Val Γ₂ t} (InstEmit.events em))) ∷ instW ems

realW : ℕ → ℕ → ℕ
realW n k = foldr _⊔_ 0 (instW
  (proj₁ (subscribeE gas (tower k) root 0 0
            (sched-init (tower k) (slots n)) (st-init (tower k)))))

entry≡ : realW 2 0 ≡ 2
entry≡ = refl

----------------------------------------------------------------------
-- THE LATER FRAMES, RUN.  Two slots doing two jobs, which is what the
-- one-slot family could not do.
----------------------------------------------------------------------

-- THE HARNESS, and both departures from the family above are forced.
-- Slot zero drives the base ASYNCHRONOUSLY, one value per frame, while
-- slot one carries both the synchronous burst each refold reads at its
-- own subscribe and later values for the refolds that re-enter.  And
-- the layer seeds from a real source rather than from `emptyᵉ`, which
-- is what makes the flattened payloads emit at all.
layerD : Closed Γ₂ natᵗ → Closed Γ₂ natᵗ
layerD e = mergeAllᵉ nothing (scanᵉ deepen (strmᵗ (input (fsuc fzero))) e)

towerD : ℕ → Closed Γ₂ natᵗ
towerD zero    = input fzero
towerD (suc k) = layerD (towerD k)

timed : ℕ → List (Timed ℕ)
timed zero    = []
timed (suc k) = (after 0 , k) ∷ timed k

slotsD : ℕ → Slots Γ₂
slotsD k fzero        = scripted (cold [] (timed k))
slotsD k (fsuc fzero) = scripted (cold (sync k) (timed k))

-- the whole run, subscribe burst and every later frame `drain` reaches
runD : ℕ → ℕ → ℕ → Stream Γ₂ natᵗ
runD vals fuel k =
  let r = subscribeE gas (towerD k) root 0 0
            (sched-init (towerD k) (slotsD vals)) (st-init (towerD k))
  in proj₁ r ++ drain fuel 1 (proj₁ (proj₂ r)) (proj₂ (proj₂ r))

wideD : ℕ → ℕ → ℕ → ℕ
wideD vals fuel k = foldr _⊔_ 0 (instW (runD vals fuel k))

countD : ℕ → ℕ → ℕ → ℕ
countD vals fuel k = length (instW (runD vals fuel k))

-- LOAD-BEARING, and it is the sizes that let the run be compared with
-- the syntactic rows above: the driven family measures the same at
-- every layer, so `fanout` is the linear reading AT THIS PROGRAM.
sizesAgree : sizeᵉ (towerD 1) ≡ sizeOf 1
sizesAgree = refl

-- the run, packed: widest instant and instant count at no layer and at
-- one.  The entry width is LOAD-BEARING against the burst-only row
-- above -- four instants rather than one, so the drive really did
-- reach later frames -- and the one-layer width is load-bearing
-- against the zero the burst-only reading gives there.
driven : ℕ
driven = wideD 3 6 0 + 10 * countD 3 6 0
       + 100 * wideD 3 6 1 + 10000 * countD 3 6 1

driven≡ : driven ≡ 72741
driven≡ = refl

-- LOAD-BEARING, and the row the leg was for: a RUN crosses the linear
-- reading at the FIRST hop, where the syntactic row above needed two
-- layers to cross.  A family whose width grew per hop by at most its
-- size would put this at `false`.  NOT COVERED: two layers, which
-- outran the evidence loop's budget outright rather than reporting a
-- number -- so the measured side is bounded at one layer, and that
-- bound is the loop's and not the evaluator's.
crossesRun : (fanout 1 <ᵇ wideD 3 6 1) ≡ true
crossesRun = refl
