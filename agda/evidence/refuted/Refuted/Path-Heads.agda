-- THE HEADROOM PIN DOES NOT HOLD EITHER HEAD, IT FAILS WHERE THE WALK
-- STANDS RATHER THAN AT AN EDGE, AND THE REPAIR IT POINTS AT IS NOT
-- AVAILABLE EITHER — SO WHAT IS REFUTED HERE IS THE PAYLOAD CURRENCY
-- AND NOT THE THREE STATEMENTS DENOMINATED IN IT.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make refuted`, claimed by
-- `Refuted.Main`.

-- WHAT THE PIN SAYS.  The chain walk composes its steps out of frame
-- statements, and for the map and the fold it has no frame-local figure
-- to hand them: what either produces is read off a source EXPRESSION,
-- and a chain records the frame rather than what the frame was built
-- from.  So both are pinned at the HEADROOM the tail leaves — the store
-- bound less whatever the rest of the path spends on flatteners — on
-- the reasoning that a frame staying inside the room the path has left
-- is the widest thing a frame-shaped statement can say.

-- AND THE HEADROOM IS NOUGHT ON THE COMMONEST CHAIN THERE IS.  Neither
-- of these frames is charged a flattener, so a chain carrying no
-- flattener at all has a headroom equal to its whole store bound — and
-- a chain whose store bound is nought therefore pins both heads at
-- nought.  That is not a corner: it is what the walk is handed for
-- every registration on a data-typed source, where the payload reads
-- nothing and no earlier frame has written.  The walk's own hypothesis
-- there is `0 + 0 ≤ 0`, which holds, so the two statements below are
-- instantiated at exactly the point that kills them.

-- WHAT THE FRAMES THEN DO, AND IT IS THE SAME DEFECT TWICE.  A map's
-- outputs are its TEMPLATE evaluated at the payload and a fold's are
-- its STEP applied to the accumulator, and either function may IGNORE
-- what it is handed: the two below drop their arguments and return one
-- flattener over a literal.  So each returns a reading of one against a
-- bound of nought, with every hypothesis met — the payload carries no
-- observable and the store is at the floor — and the gap is not a rate
-- but whatever the function writes, which is unbounded while both
-- bounds stay where they are.

-- SO NO FIGURE COMPUTED FROM THE PATH PINS EITHER HEAD, because the
-- path is exactly what says nothing about the template or the step.
-- What a chain step does carry is the frame's own function, and the
-- rows past the two witnesses are about whether that is enough.
module Refuted.Path-Heads where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _*_; _∸_; z≤n; s≤s)
open import Data.Product using (proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Val; Fn; natᵗ; obs; _×ᵗ_;
  strmᵗ; ofᵉ; emptyᵉ; mergeAllᵉ; mapᵉ; scanᵉ; fstᵗ; varᵗ; nat̂)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵉ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Path; NodeId; Sched; EvalSt; root; map-f; scan-f; scan-st; stepFrame; stHop; installNode;
  rootWitness; sched-init; st-init)
open import Verify-Rank-Sufficient.Carried using (valsHop)
open import Verify-Rank-Sufficient.Push-Carried using (FrameCarries)
open import Verify-Rank-Sufficient.Path-Fits using (pathHops)

----------------------------------------------------------------------
-- THE TWO STATEMENTS, RESTATED.  Both the frame predicate and the
-- path's flattener count are IMPORTED rather than spelled out: what is
-- refuted is the two heads' choice of residue, so a repair that moves
-- either must make this file fail to typecheck instead of leaving it
-- quietly green.
----------------------------------------------------------------------

MapHeadCarried : Set
MapHeadCarried = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) →
  FrameCarries {e = e} ac id now (map-f fn) κ ψ Rin (Rst ∸ pathHops κ) Rst

ScanHeadCarried : Set
ScanHeadCarried = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) →
  FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ Rin
    (Rst ∸ pathHops κ) Rst

----------------------------------------------------------------------
-- THE GROUND.  An empty context, so the reading has no slot to blame,
-- and a root term of the type the chain ends at.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ ()

ψ₀ : Fin 0 → Rd₃
ψ₀ = slotRd ins₀

root₀ : Closed Γ₀ (obs natᵗ)
root₀ = ofᵉ (strmᵗ emptyᵉ ∷ [])

ac₀ : Acc _≺_ _
ac₀ = rootWitness root₀ ins₀

sd₀ : Sched Γ₀
sd₀ = sched-init root₀ ins₀

-- one flattening layer over a one-element literal: the least a term of
-- this language can read above nothing, and nothing here is deferred
deep : ∀ {Δᵍ Δ Θ} → Exp Γ₀ Δᵍ Δ Θ natᵗ
deep = mergeAllᵉ nothing (ofᵉ (strmᵗ (ofᵉ (nat̂ 5 ∷ [])) ∷ []))

-- LOAD-BEARING: the chain both heads are refuted on carries no
-- flattener, so its headroom IS its store bound and a store bound of
-- nought leaves neither head any room at all
chain-is : pathHops {Γ = Γ₀} {s = obs natᵗ} root ≡ 0
chain-is = refl

----------------------------------------------------------------------
-- THE MAP HEAD.  A template that drops a numeral and returns the
-- flattener above it, so the input's reading cannot bound an output the
-- input did not contribute to.
----------------------------------------------------------------------

tmpl : Fn Γ₀ [] [] [] natᵗ (obs natᵗ)
tmpl = strmᵗ deep

mapVals : List (Val Γ₀ natᵗ)
mapVals = 0 ∷ []

mapOut : List (Val Γ₀ (obs natᵗ))
mapOut = proj₁ (stepFrame {e = root₀} ac₀ 0 0 (map-f tmpl) root mapVals
                  false sd₀ (st-init root₀))

-- LOAD-BEARING: the payload carries no observable, so the bound the
-- frame is held to is the tightest the predicate admits
map-in-is : valsHop {Γ = Γ₀} ψ₀ natᵗ mapVals ≡ 0
map-in-is = refl

-- LOAD-BEARING: a map writes nothing, so the store enters and leaves at
-- the floor and the crossing is the payload one alone
map-store-is : stHop ψ₀ (st-init root₀) ≡ 0
map-store-is = refl

-- LOAD-BEARING: the template's flattener, read off the value the frame
-- actually produced rather than off the term
map-out-is : valsHop ψ₀ (obs natᵗ) mapOut ≡ 1
map-out-is = refl

map-head-carried-false : MapHeadCarried → ⊥
map-head-carried-false h
  with proj₁ (h {e = root₀} ac₀ 0 0 tmpl root ψ₀ 0 0 mapVals false sd₀
                (st-init root₀) z≤n z≤n)
... | ()

----------------------------------------------------------------------
-- THE FOLD HEAD, where the headroom pin was supposed to survive: a
-- fold's outputs come from the STORE, so reading the residue off the
-- store bound was the repair.  It fails for the same reason and at the
-- same point — the step is what produces the accumulator, and a step
-- that discards its pair is bounded by neither side.  The node is
-- installed exactly as a subscribe frame seeds a fold, so nothing here
-- is a record written by hand.
----------------------------------------------------------------------

-- the seed: reads zero, so the store enters at the floor
seed : Val Γ₀ (obs natᵗ)
seed = emptyᵉ

step : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
step = strmᵗ deep

stˢ : EvalSt root₀
stˢ = installNode 0 (scan-st {t = obs natᵗ} seed) (st-init root₀)

scanVals′ : List (Val Γ₀ natᵗ)
scanVals′ = 3 ∷ []

scanOut : List (Val Γ₀ (obs natᵗ))
scanOut = proj₁ (stepFrame ac₀ 0 0 (scan-f step 0) root scanVals′ false
                   sd₀ stˢ)

-- LOAD-BEARING: the payload enters at the floor, so the statement
-- stands at its strongest
scan-in-is : valsHop {Γ = Γ₀} ψ₀ natᵗ scanVals′ ≡ 0
scan-in-is = refl

-- LOAD-BEARING: and so does the store the accumulator sits in, which is
-- the side the headroom pin reads its residue off
scan-store-is : stHop ψ₀ stˢ ≡ 0
scan-store-is = refl

-- LOAD-BEARING: one delivery, one refold, and the accumulator comes
-- back reading one
scan-out-is : valsHop ψ₀ (obs natᵗ) scanOut ≡ 1
scan-out-is = refl

scan-head-carried-false : ScanHeadCarried → ⊥
scan-head-carried-false h
  with proj₁ (h ac₀ 0 0 step 0 root ψ₀ 0 0 scanVals′ false sd₀ stˢ
                z≤n z≤n)
... | ()

----------------------------------------------------------------------
-- AND THE AXIS ANY REPAIR HAS TO COVER, WHICH IS NOT THE ONE THE TWO
-- WITNESSES ABOVE POINT AT.  Reading the residue off the template at a
-- payload held to the floor answers the dropping function — it charges
-- whatever the function writes on its own — and the rows below say it
-- is still not enough.  A template may FOLD over its argument, and then
-- the depth it hands back is one layer per DELIVERY: the payloads here
-- are observables of plain numbers, so every one of them reads nought
-- and every one is admitted under a bound of nought, while what the
-- frame returns rises a layer per element carried.  The delivery count
-- is a component of the value's reading that the frame predicate's
-- payload currency does not carry at all, so no figure computed from
-- the template and the incoming HOP can bound this frame.

-- SO THE PAYLOAD CURRENCY IS WHAT IS WRONG, AND IT IS WRONG IN EVERY
-- FRAME STATEMENT RATHER THAN IN THESE TWO HEADS.  A value of
-- observable type is read as an event count PAIRED with a hop, and the
-- predicate projects the hop and discards the count — so the three rows
-- below are one bound apart in what the predicate sees and four apart
-- in what the frame produces.  A residue read off the frame's own
-- function repairs the witnesses above and leaves this untouched,
-- because the missing quantity is not the function's: it is the half of
-- the payload's own reading the currency threw away.
----------------------------------------------------------------------

-- deepens the accumulator by one flattening layer per delivery
deepen : ∀ {Δᵍ Δ Θ} → Fn Γ₀ Δᵍ Δ Θ (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

seed₀ : ∀ {Δᵍ Δ Θ} → Tm Γ₀ Δᵍ Δ Θ (obs natᵗ)
seed₀ = strmᵗ emptyᵉ

-- folds over the deliveries of its own argument, which is the shape the
-- floor reading cannot see
folding : Fn Γ₀ [] [] [] (obs natᵗ) (obs natᵗ)
folding = strmᵗ (mergeAllᵉ nothing (scanᵉ deepen seed₀
            (mergeAllᵉ nothing (ofᵉ (varᵗ (here refl) ∷ [])))))

-- three payloads of plain numbers, differing only in how many they carry
val₁ val₃ val₅ : Val Γ₀ (obs natᵗ)
val₁ = ofᵉ (nat̂ 0 ∷ [])
val₃ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])
val₅ = ofᵉ (nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ nat̂ 0 ∷ [])

foldOut₁ foldOut₃ foldOut₅ : List (Val Γ₀ (obs natᵗ))
foldOut₁ = proj₁ (stepFrame {e = root₀} ac₀ 0 0 (map-f folding) root
                    (val₁ ∷ []) false sd₀ (st-init root₀))
foldOut₃ = proj₁ (stepFrame {e = root₀} ac₀ 0 0 (map-f folding) root
                    (val₃ ∷ []) false sd₀ (st-init root₀))
foldOut₅ = proj₁ (stepFrame {e = root₀} ac₀ 0 0 (map-f folding) root
                    (val₅ ∷ []) false sd₀ (st-init root₀))

-- radix 1000, low digit first: what the payloads carrying one, three
-- and five deliveries produced.  LOAD-BEARING as a TRIPLE — one figure
-- is a height and two are a direction, and three are what say the rate
-- is linear in the deliveries rather than a step that saturates
fold-packed : ℕ
fold-packed = valsHop ψ₀ (obs natᵗ) foldOut₁
            + 1000 * valsHop ψ₀ (obs natᵗ) foldOut₃
            + 1000000 * valsHop ψ₀ (obs natᵗ) foldOut₅

fold-packed-is : fold-packed ≡ 7005003
fold-packed-is = refl

-- LOAD-BEARING: all three payloads sit at the floor, so ONE bound of
-- nought admits every one of them and the figures above differ in
-- nothing the frame predicate is able to read
fold-in-packed : ℕ
fold-in-packed = valsHop ψ₀ (obs natᵗ) (val₁ ∷ [])
               + 1000 * valsHop ψ₀ (obs natᵗ) (val₃ ∷ [])
               + 1000000 * valsHop ψ₀ (obs natᵗ) (val₅ ∷ [])

fold-in-packed-is : fold-in-packed ≡ 0
fold-in-packed-is = refl

-- LOAD-BEARING: and the store is at the floor at both ends of all
-- three, so nothing the predicate reads on that side separates them
-- either — a map writes nothing, so the state it is handed is the
-- state it returns
fold-store-is : stHop ψ₀ (st-init root₀) ≡ 0
fold-store-is = refl

----------------------------------------------------------------------
-- AND THE SHELF'S OWN LEAF FALLS TO IT, WHICH IS WHAT MAKES THE
-- CURRENCY THE FINDING RATHER THAN THE PIN.  The leaf reads both its
-- ends off a source EXPRESSION, so its bound does see the count the
-- payload currency drops — but only the SOURCE's, and its hypothesis
-- admits any payload whose HOP fits.  So a source carrying one
-- delivery fixes a bound of two while a payload carrying five, read at
-- nought and admitted, hands back seven.  The leaf is not a weaker
-- statement that happens to survive: it is the same statement with the
-- same blind side, and the blind side is the currency's.
----------------------------------------------------------------------

MapFrameCarried : Set
MapFrameCarried = ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
  (b : Exp Γ [] [] [] s) (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rst : ℕ) →
  FrameCarries {e = e} ac id now (map-f fn) κ ψ
    (depthᵉ ψ b) (depthᵉ ψ (mapᵉ fn b)) Rst

srcᵇ : Exp Γ₀ [] [] [] (obs natᵗ)
srcᵇ = root₀

-- radix 1000, low digit first: the source's own reading, which is what
-- the payload is admitted against, and the map expression's, which is
-- the bound the frame is held to.  LOAD-BEARING as a PAIR: the first
-- being nought is what lets every payload above through, and the second
-- being finite is what the growing outputs overrun
src-packed : ℕ
src-packed = depthᵉ ψ₀ srcᵇ + 1000 * depthᵉ ψ₀ (mapᵉ folding srcᵇ)

src-packed-is : src-packed ≡ 2000
src-packed-is = refl

map-frame-carried-count-false : MapFrameCarried → ⊥
map-frame-carried-count-false h
  with proj₁ (h {e = root₀} ac₀ 0 0 folding srcᵇ root ψ₀ 0
                (val₅ ∷ []) false sd₀ (st-init root₀) z≤n z≤n)
... | s≤s (s≤s ())
