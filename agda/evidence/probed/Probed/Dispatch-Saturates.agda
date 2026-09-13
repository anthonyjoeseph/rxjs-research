-- THE DISPATCH COUNTER, INSTANTIATED — the one re-entry bound this
-- development seeded in prose and never once ran.  A share boundary
-- re-enters chain evaluation, so the fan-out descends on a counter the
-- arrival seeds at the context size; the clause that fires when it runs
-- out returns an EMPTY fan-out rather than failing, so no obligation the
-- tower states can see it.  These rows ask the only question that
-- decides the seed: past the context size, does more counter change the
-- answer?

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- THE TELESCOPE IS THREE DEEP AND THE NEST IS TWO, WHICH IS WHAT MAKES
-- THE ROWS ASK ANYTHING.  Slot one is a share over the script, slot two
-- a share over slot one, and the root consumes slot two — so a dispatch
-- at slot one admits the chain slot two's subscription registered, that
-- chain sinks at slot two, and its fold dispatches again.  A counter of
-- one is spent before the inner dispatch runs; the rows stand above and
-- below that point.

-- THE NON-SATURATING PAIR IS THE CONTROL, AND WITHOUT IT THE REST WOULD
-- BE UNFALSIFIABLE.  A program whose dispatch never re-enters saturates
-- at every counter including zero, so the saturating rows alone cannot
-- say the counter is load-bearing at this shape.  The two emit lengths
-- below are read at a counter of one and of two and come back DIFFERENT
-- — so the clamp demonstrably truncates here when the seed is short,
-- which is what makes the saturation rows a statement about the seed
-- rather than about a machine that ignores it.

-- AND BREADTH IS NOT THE RISK, WHICH IS READ OFF THE DISPATCH RATHER
-- THAN MEASURED HERE.  The peel is once per BOUNDARY: the fan-out hands
-- every admitted chain, and its own tail, the counter it was itself
-- entered at.  So a share with many registrations costs what a share
-- with one costs, and the only thing that can outrun the seed is DEPTH —
-- a nest of shares longer than the context.  That is what the seed is a
-- claim about, and it is why the stratification of the telescope is the
-- premise underneath it.

-- NOT COVERED, AND THE UNCOVERED HALF IS THE RISKY ONE.  One arrival,
-- one telescope, one root shape, and a nest TWO boundaries deep against
-- a context of three — so the seed is exercised where it is slack and
-- never where it binds.  The row that would decide it is a program whose
-- nest reaches the context size, which needs a share whose own source is
-- a share at every rung; until one exists these rows say the counter is
-- read and that the seed suffices HERE, and nothing about the bound
-- being right in general.  Nor does anything here reach a cancelled
-- registration or a completing share, both of which take the dispatch
-- down arms these rows never enter.
-- TARGET: dispatch-saturates @51e075
module Probed.Dispatch-Saturates where

open import Data.Bool using (false)
open import Data.Fin using (zero; suc)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (cold; after_,_)
open import Rx.Exp using (Ctx; Closed; Fn; natᵗ; obs; strmᵗ; nat̂;
  ofᵉ; mapᵉ; mergeAllᵉ; input)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Strat-Order using (_≺_)
open import Rx.Evaluator using (Sched; EvalSt; root; rootTri;
  subscribeE; rootWitness; sched-init; st-init; dispatchShare;
  shareAdmit)
open import Rx.Evaluator-Theorems using (dispatch-saturates)

open import Probed.Apparatus using (Below; Confirms)

----------------------------------------------------------------------
-- THE TELESCOPE.  Three slots, two of them shares, each reading the one
-- below it — the shape the seed is stated over, and the shallowest one
-- in which a dispatch can re-enter a dispatch.
----------------------------------------------------------------------

Γ₃ : Ctx 3
Γ₃ = natᵗ ∷ⱽ natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

lit : Fn Γ₃ [] [] [] natᵗ (obs natᵗ)
lit = strmᵗ (ofᵉ (nat̂ 1 ∷ []))

ins : Slots Γ₃
ins zero             = scripted (cold [] (after 0 , 9 ∷ []))
ins (suc zero)       = shared (input zero)
ins (suc (suc zero)) = shared (mergeAllᵉ nothing (mapᵉ lit (input (suc zero))))

-- the root consumes the DEEPEST share, so every slot below it is on the
-- path and the registry carries one chain per boundary
prog : Closed Γ₃ natᵗ
prog = mergeAllᵉ nothing (ofᵉ (strmᵗ (input (suc (suc zero))) ∷ []))

ac₀ : Acc _≺_ (rootTri prog ins)
ac₀ = rootWitness prog ins

sd₀ : Sched Γ₃
sd₀ = proj₁ (proj₂ (subscribeE ac₀ prog root 0 0 (sched-init prog ins)
                     (st-init prog)))

st₀ : EvalSt prog
st₀ = proj₂ (proj₂ (subscribeE ac₀ prog root 0 0 (sched-init prog ins)
                     (st-init prog)))

vals₀ : List ℕ
vals₀ = 7 ∷ []

----------------------------------------------------------------------
-- THE REGISTRY THE DISPATCH MEETS, pinned first.  A row over an empty
-- admitted list is the arm that returns immediately, so it saturates at
-- every counter and would report a tidy green having entered nothing.
----------------------------------------------------------------------

admits₁-is : length (shareAdmit (suc zero) (EvalSt.registry st₀)) ≡ 1
admits₁-is = refl                                       -- LOAD-BEARING

admits₂-is : length (shareAdmit (suc (suc zero)) (EvalSt.registry st₀)) ≡ 1
admits₂-is = refl                                       -- LOAD-BEARING

----------------------------------------------------------------------
-- THE CONTROL.  What the dispatch emits at a counter of one against a
-- counter of two: the first is spent before the inner boundary, so the
-- clamp truncates and the two figures differ.  This is what says the
-- counter is read at all at this program.
----------------------------------------------------------------------

emitsAt : ℕ → ℕ
emitsAt g = length (proj₁ (dispatchShare {e = prog} ac₀ g 0 0 (suc zero)
                            vals₀ false sd₀ st₀))

short-is : emitsAt 1 ≡ 1                                -- LOAD-BEARING
short-is = refl

long-is : emitsAt 2 ≡ 2                                 -- LOAD-BEARING
long-is = refl

-- and where saturation actually begins, which is what says the seed is
-- SLACK here rather than tight: the nest is two boundaries deep and the
-- context is three, so the counter stops being read one below the seed
seed-is : emitsAt 3 ≡ 2                                 -- LOAD-BEARING
seed-is = refl

----------------------------------------------------------------------
-- THE STATEMENT AT ITS OWN POINTS.  The type is generated from
-- `dispatch-saturates` as it now reads; the probe chooses only the
-- counter and the share, and `Below` decides the premise — so a counter
-- under the context size leaves the row unsolvable rather than green.
----------------------------------------------------------------------

-- at the seed itself, and at the SHALLOWER share, where the nest is two
-- dispatches deep
satSeed : Confirms (dispatch-saturates {e = prog} ac₀ 3 Below 0 0
                     (suc zero) vals₀ false sd₀ st₀)
satSeed = refl

-- and one above it, which is what says the seed is not merely the first
-- counter that happens to work
satAbove : Confirms (dispatch-saturates {e = prog} ac₀ 4 Below 0 0
                      (suc zero) vals₀ false sd₀ st₀)
satAbove = refl

-- at the DEEPEST share, whose own dispatch re-enters nothing: the
-- degenerate arm of the same statement, claimed so the pair above is
-- read as covering a nest rather than a boundary
satDeep : Confirms (dispatch-saturates {e = prog} ac₀ 3 Below 0 0
                     (suc (suc zero)) vals₀ false sd₀ st₀)
satDeep = refl
