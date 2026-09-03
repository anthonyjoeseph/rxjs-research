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
-- and slots with no cap anywhere in it, and its `scanᵉ` clause carries
-- the source's payload count into an EXPONENT.  So one layer takes a
-- width to a power of itself and the syntactic reading towers in the
-- layer count exactly as the recurrence does.  The linear reading is
-- therefore not a tightening the arm is waiting for -- it is refuted by
-- a measure this tower already computes, at the smallest program that
-- can express a refold.  What that costs the arm is its FIELD repair:
-- a width carried on the invariant record would be denominated in this
-- measure, and there is no field to thread when the measure towers.

-- THE MEASURED SIDE IS BOUNDED AT ONE LAYER, and that is a finding
-- about what can be instantiated rather than a gap to be filled later.
-- A flatten emits nothing in the frame that SUBSCRIBES it, so a run of
-- a layered program delivers its widths in later frames; and the family
-- reaches its source through a single scripted slot, which a re-entering
-- inner finds drained.  `subscribeE` therefore reads a flat zero at
-- every `k ≥ 1` under both the subscribe-burst and widest-instant
-- readings, and the entry row is the only live one.  Reaching the later
-- frames wants the `stepFrame` door `Probed.Frame-Drain-Live` uses, at a
-- state built by hand -- which prices a run against a state no run
-- produced, so it is not taken here.
module Probed.Fold-Width-Reach where

open import Data.List using (List; []; _∷_; length; foldr)
open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _<ᵇ_)
open import Data.Maybe using (nothing)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Closed; Val; natᵗ; scanᵉ; mergeAllᵉ; emptyᵉ; input;
  strmᵗ; sizeᵉ)
open import Rx.Prim using (InstEmit)
open import Rx.Frame-Width using (outWⱽ)
open import Rx.Evaluator using (subscribeE; splitEvents; Stream; root; sched-init;
  st-init; widAt)
open import Refuted.Demand-Programs using (Γ₂)
open import Refuted.Scan-Burst-Nest using (deepen; slots; gas)
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
-- THE ENTRY ROW, RUN.  The only layer count `subscribeE` reaches; see
-- the header for why, and for why it is a coverage boundary rather
-- than a hole.
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
