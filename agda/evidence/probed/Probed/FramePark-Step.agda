-- ══════════════════════════════════════════════════════════════════
-- A FRAME'S OWN PARK READING SURVIVES ITS STEP, at the two frame
-- shapes that actually WRITE the cell the reading is about.
--
-- TARGET: framePark-step @112abf
--
-- WHAT THE ROWS INSTANTIATE.  A two-slot context, so `pathFloor` at a
-- root-ended chain is 2 and an `input` reference at index 0 or 1 sits
-- below it.  The chain is `map-f (nat̂ 0) ↠ root` where the frame under
-- test needs an observable payload, and `root` where it does not.
--
-- THE SCAN IS THE SHAPE AT RISK, and the two scan rows separate the
-- two ways its conclusion can be reached.  `stepFrame` at a `scan-f`
-- OVERWRITES the cell with `applyFn` of the frame's own closure, so
-- nothing about the old accumulator's reading survives on its own.
-- The TRANSPORT row runs an identity closure, where the post-state
-- accumulator IS the pre-state one and the conclusion comes from the
-- third premise; the BOUGHT row runs a closure that discards the
-- accumulator entirely and manufactures a reference at index 1, where
-- the third premise says nothing about the answer and the conclusion
-- comes from `frameStrat?` alone.  That is the header's claim that a
-- scan's reading is bought rather than transported, instantiated at
-- both of the cases it distinguishes.
--
-- WHAT MAKES THE BOUGHT ROW LOAD-BEARING.  Drop the floor to 1 and the
-- conclusion goes false — `inputsBelowᵉ 1 (input (fsuc fzero))` is
-- `1 <ᵇ 1 = false` — and the closure premise goes false at exactly the
-- same point, since `frameStrat? 1 (scan-f fn₁ _)` is the same
-- comparison. The premise is the only thing standing between this row
-- and a counterexample.  The transport row is load-bearing on the
-- THIRD premise instead: at floor 0 the pre-state reading is already
-- false and the hypothesis blocks, while the closure premise stays
-- true, an identity closure naming no input.
--
-- THE ENQUEUE ROW IS THE ASSEMBLY'S CONCLUSION at the point
-- `Probed.ThruConsume-CellPark` instantiates its leaf: a capacity-zero
-- mergeAll node, so `hasRoom` fails and the arriving observable is
-- appended to the queue the reading is about.  It is load-bearing on
-- the vals premise, which is what prices the term being appended.
--
-- WHAT IS NOT COVERED.  `from-inner`, whose step is `innerReact` — a
-- gas-driven subscription of the inner, not a transparent write.  The
-- `hasRoom = true` arm of the enqueue row, for the same reason.  A
-- `share-sink` chain, where the floor sits below the context width:
-- every row here is taken at a root-ended chain, so nothing says what
-- happens when the floor is not the full width.  `map-f` and `take-f`
-- are covered only degenerately, `framePark?` being `true` at both.
-- ══════════════════════════════════════════════════════════════════
module Probed.FramePark-Step where

open import Data.Bool using (false)
open import Data.Fin using () renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (just)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (g0; cold)
open import Rx.Exp
  using (Ctx; Closed; Fn; natᵗ; obs; _×ᵗ_; emptyᵉ; input;
         strmᵗ; fstᵗ; varᵗ; nat̂)
open import Rx.Slots using (Slots; scripted)
open import Rx.Evaluator
  using (EvalSt; Path; root; _↠_; map-f; scan-f; thru-outer; mergeAllᵒ; sched-init; st-init;
  installNode; scan-st; mergeAll-st)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
  using (framePark-step)
open import Probed.Apparatus using (Confirms)

----------------------------------------------------------------------
-- THE CONTEXT.  Two slots, so a root-ended chain has floor 2 and both
-- `input fzero` and `input (fsuc fzero)` sit below it.
----------------------------------------------------------------------

Γ₂ : Ctx 2
Γ₂ = natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

e₂ : Closed Γ₂ natᵗ
e₂ = emptyᵉ

sl₂ : Slots Γ₂
sl₂ fzero        = scripted (cold [] [])
sl₂ (fsuc fzero) = scripted (cold [] [])

----------------------------------------------------------------------
-- THE TWO CLOSURES.  `fn₀` keeps the accumulator, `fn₁` replaces it
-- with an observable naming slot 1 and reads the payload not at all.
----------------------------------------------------------------------

fn₀ : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn₀ = fstᵗ (varᵗ (here refl))

fn₁ : Fn Γ₂ [] [] [] ((obs natᵗ) ×ᵗ natᵗ) (obs natᵗ)
fn₁ = strmᵗ (input (fsuc fzero))

-- the chain a scan frame sits on: its output is an observable, and the
-- `map-f` below it is what carries the chain down to a `natᵗ` root
κˢ : Path Γ₂ (obs natᵗ) natᵗ
κˢ = map-f (nat̂ 0) ↠ root

-- the accumulator cell, at nid 5, holding an observable that names
-- slot 0
stˢ : EvalSt e₂
stˢ = installNode 5 (scan-st {t = obs natᵗ} (input fzero)) (st-init e₂)

----------------------------------------------------------------------
-- ROW 1 — TRANSPORT.  `applyFn fn₀ (acc , v)` is `acc`, so the cell is
-- rewritten with the value it already held and the post-state reading
-- is the pre-state one.  LOAD-BEARING on the third premise.
----------------------------------------------------------------------

tieScanTransport : Confirms
  (framePark-step g0 0 0 (scan-f fn₀ 5) κˢ (3 ∷ []) false
     (sched-init e₂ sl₂) stˢ refl refl refl)
tieScanTransport = refl

----------------------------------------------------------------------
-- ROW 2 — BOUGHT.  `applyFn fn₁ (acc , v)` is `input (fsuc fzero)`,
-- which the pre-state cell never held: the post-state reading is
-- `1 <ᵇ 2 = true`, and the only premise that mentions it is the
-- closure's.  LOAD-BEARING on the first premise.
----------------------------------------------------------------------

tieScanBought : Confirms
  (framePark-step g0 0 0 (scan-f fn₁ 5) κˢ (3 ∷ []) false
     (sched-init e₂ sl₂) stˢ refl refl refl)
tieScanBought = refl

----------------------------------------------------------------------
-- ROW 3 — THE ENQUEUE, one level above `thruConsume-cellPark`'s leaf.
-- A capacity-zero mergeAll node at nid 0, so the arriving observable
-- is appended rather than subscribed.  LOAD-BEARING on the vals
-- premise, which prices the appended term.
----------------------------------------------------------------------

stᵗ : EvalSt e₂
stᵗ = installNode 0 (mergeAll-st {t = natᵗ} (just 0) 0 [] false) (st-init e₂)

tieThruEnqueue : Confirms
  (framePark-step g0 0 0 (thru-outer mergeAllᵒ 0) root
     (input fzero ∷ []) false (sched-init e₂ sl₂) stᵗ refl refl refl)
tieThruEnqueue = refl

----------------------------------------------------------------------
-- ROW 4 — DEGENERATE, and labelled so.  A `map-f` names no cell, so
-- `framePark?` is `true` on both sides and the row could not have
-- failed.  It is here to pin that the free shapes really are free.
----------------------------------------------------------------------

tieMapFree : Confirms
  (framePark-step g0 0 0 (map-f (nat̂ 0)) root (input fzero ∷ []) false
     (sched-init e₂ sl₂) stᵗ refl refl refl)
tieMapFree = refl
