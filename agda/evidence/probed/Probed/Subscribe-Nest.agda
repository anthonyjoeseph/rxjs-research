-- THE SUBSCRIBE DESCENT'S NEST BOUND, AT THE FAMILY THAT KILLED EVERY
-- EARLIER FORM OF IT.
--
-- EVIDENCE, not a claim: `src` cannot import this file (the library
-- layout makes the name unresolvable from there) and nothing in the
-- proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
-- TARGET: subscribeE-nest
-- TARGET: stepFrame-nodes-thru
--
-- WHAT IS BEING TESTED.  `subscribeE-nest` charges a subscription
-- `2 ^ cSize` times what it was handed, and the whole question is where
-- the exponent comes from.  Taking it from the STORE's cap is refuted --
-- `Refuted.Subscribe-Caps-Nest`, sixteen against six -- so the statement
-- now takes it from a `valCaps?` on the observable being subscribed, and
-- these rows are the first instantiation of THAT form.
--
-- HOW THE CAP IS CHOSEN, and it is the opposite of generous.  Each row
-- sets `c` to the value's OWN size and width, which is the smallest cap
-- its `valCaps?` premise admits: `sizeᵛ ≤ᵇ sizeᵛ` is `true` by refl and
-- there is no slack anywhere in the choice.  A larger cap would make
-- every row pass by making the right-hand side astronomical, which is
-- the way this probe would lie.
--
-- WHY THE OTHER PREMISES ARE FREE HERE.  `B` is taken to be `nestDᵉ o`
-- exactly, so the depth premise is `refl`; the store is `st-init`, whose
-- `nodesMax` is zero, so the store premise holds at every cap; and
-- `capsOK?` at an empty node table holds outright, which is pinned
-- rather than assumed.  What is left is the conclusion, and it is the
-- only thing these rows measure.
--
-- EVERY ROW IS LOAD-BEARING, and what would make one fail is a
-- substitution that deepens its payload faster than two to its own
-- size.  The family is exactly the one that refuted the caps-free, the
-- summand-only and the store-capped forms -- a stack of `mapᵉ` frames
-- each naming its payload on both sides of a sum, which doubles the
-- emitted depth per layer.  The margin is pinned per row, so a repair
-- that moves either side is visible as a number and not as a verdict.
--
-- WHAT IS NOT COVERED.  Every row subscribes at `root` from `st-init`,
-- so the queue-facing half -- a descent under a `from-inner` frame with
-- a non-empty node table -- is untouched here, and so is every `c` whose
-- cap exceeds the value's own size.
module Probed.Subscribe-Nest where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; g0; gs)
open import Rx.Exp
  using (Closed; Val; Fn; natᵗ; obs; ofᵉ; mapᵉ; switchAllᵉ; varᵗ; nat̂; strmᵗ; emptyᵉ; sizeᵛ)
open import Rx.Frame-Width using (pWᵛ)
open import Rx.Slots using (Slots)
open import Rx.Nest-Depth using (nestDᵉ)
open import Rx.Evaluator
  using (Path; _↠_; from-inner; Sched; EvalSt; Frame; mergeAll-st; thru-outer; mergeAllᵒ; stepFrame;
         installNode; subscribeE; splitBurst; root; sched-init; st-init)
open import Verify-Budget-Sufficient.Caps using (Caps; caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (capsOK?; valCaps?)
open import Verify-Budget-Sufficient.Nest-Store using (nestUnit)
open import Verify-Budget-Sufficient.Nest-Walk using (nodesMax; nestDᵛˢ)
open import Verify-Budget-Sufficient.Demand-Programs using (Γ₂; insT)

slots : Slots Γ₂
slots = insT 0 0 0

gas : Gas
gas = gs (gs (gs (gs (gs (gs g0)))))

-- a payload k `*All` layers deep
deepV : ℕ → Val Γ₂ (obs natᵗ)
deepV zero    = ofᵉ (nat̂ 0 ∷ [])
deepV (suc k) = switchAllᵉ (ofᵉ (strmᵗ (deepV k) ∷ []))

-- the step function names its payload TWICE, once on each side of the
-- `mapᵉ` sum, which is what doubles the depth a subscription delivers
dup₁ : Fn Γ₂ [] [] [] (obs natᵗ) (obs (obs natᵗ))
dup₁ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

dup₂ : Fn Γ₂ [] [] [] (obs (obs natᵗ)) (obs (obs (obs natᵗ)))
dup₂ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

dup₃ : Fn Γ₂ [] [] [] (obs (obs (obs natᵗ))) (obs (obs (obs (obs natᵗ))))
dup₃ = strmᵗ (mapᵉ (varᵗ (there (here refl))) (ofᵉ (varᵗ (here refl) ∷ [])))

p₁ : Closed Γ₂ (obs (obs natᵗ))
p₁ = mapᵉ dup₁ (ofᵉ (strmᵗ (deepV 2) ∷ []))

p₂ : Closed Γ₂ (obs (obs (obs natᵗ)))
p₂ = mapᵉ dup₂ p₁

p₃ : Closed Γ₂ (obs (obs (obs (obs natᵗ))))
p₃ = mapᵉ dup₃ p₂

-- THE SMALLEST CAP THE PREMISE ADMITS: the value's own size and width.
tight : ∀ {u} → Val Γ₂ u → Caps
tight {u} v = caps (sizeᵛ u v) (pWᵛ 2 slots u v) 0

-- the two sides, at the cap above and at `B = nestDᵉ o` exactly
read : ∀ {t} (e : Closed Γ₂ t) → ℕ × ℕ
read {t} e =
  let c = tight {obs t} e
      r = subscribeE gas e root 0 0 (sched-init e slots) (st-init e)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ t} (proj₁ r)))
   , 2 ^ Caps.cSize (tight {obs t} e) * (nestDᵉ e + nestUnit e slots)

-- the premises, pinned rather than assumed
prem : ∀ {t} (e : Closed Γ₂ t) → Set
prem {t} e =
  (valCaps? (tight {obs t} e) slots (obs t) e ≡ true)
  × (capsOK? (tight {obs t} e) (sched-init e slots) (st-init e) ≡ true)

premises₁ : prem p₁
premises₁ = refl , refl

premises₂ : prem p₂
premises₂ = refl , refl

premises₃ : prem p₃
premises₃ = refl , refl

-- THE CONCLUSION, at each stack height
fits₁ : (proj₁ (read p₁) ≤ᵇ proj₂ (read p₁)) ≡ true
fits₁ = refl

fits₂ : (proj₁ (read p₂) ≤ᵇ proj₂ (read p₂)) ≡ true
fits₂ = refl

fits₃ : (proj₁ (read p₃) ≤ᵇ proj₂ (read p₃)) ≡ true
fits₃ = refl

-- WHAT THE FAMILY ACTUALLY SPENDS, which is the measurement and not the
-- verdict.  A row saying the bound holds at these caps says almost
-- nothing -- `2 ^ 21` against a delivered four -- so each program is
-- also pinned at the SMALLEST exponent that carries it, and at the one
-- below, where it fails.  Those two rows per program are the pair that
-- could have gone either way.
--
-- AND THE RATIO IS THE FINDING.  The exponent the family demands grows
-- by ONE per stacked frame while the size it is read off grows by
-- SEVEN, so the statement's shape -- exponential in the substituted
-- value's size -- is not merely sufficient here, it outruns the doubling
-- with six of its seven per-layer bits to spare.  A linear factor would
-- not: the demand doubles.
tightSize : ∀ {t} (e : Closed Γ₂ t) → ℕ
tightSize {t} e = Caps.cSize (tight {obs t} e)

base : ∀ {t} (e : Closed Γ₂ t) → ℕ
base e = nestDᵉ e + nestUnit e slots

delivered : ∀ {t} (e : Closed Γ₂ t) → ℕ
delivered {t} e =
  let r = subscribeE gas e root 0 0 (sched-init e slots) (st-init e)
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ t} (proj₁ r)))

-- the size the cap is read off, and the base the factor multiplies
sizes : ℕ × ℕ × ℕ
sizes = tightSize p₁ , tightSize p₂ , tightSize p₃

sizes≡ : sizes ≡ (21 , 28 , 35)
sizes≡ = refl

bases : ℕ × ℕ × ℕ
bases = base p₁ , base p₂ , base p₃

bases≡ : bases ≡ (6 , 6 , 6)
bases≡ = refl

emits : ℕ × ℕ × ℕ
emits = delivered p₁ , delivered p₂ , delivered p₃

emits≡ : emits ≡ (4 , 8 , 16)
emits≡ = refl

-- ONE STACKED FRAME, ONE BIT.  Each pair is the crossing: the exponent
-- above carries the program, the one below does not.  `p₁` has no such
-- pair and is marked DEGENERATE for it -- one substitution still fits
-- under the base term, so that row could not have failed and is kept
-- only to place the family's floor.
spend₁ : (delivered p₁ ≤ᵇ 2 ^ 0 * base p₁) ≡ true   -- DEGENERATE
spend₁ = refl

spend₂ : ((delivered p₂ ≤ᵇ 2 ^ 1 * base p₂) ≡ true)
       × ((delivered p₂ ≤ᵇ 2 ^ 0 * base p₂) ≡ false)
spend₂ = refl , refl

spend₃ : ((delivered p₃ ≤ᵇ 2 ^ 2 * base p₃) ≡ true)
       × ((delivered p₃ ≤ᵇ 2 ^ 1 * base p₃) ≡ false)
spend₃ = refl , refl

----------------------------------------------------------------------
-- THE SAME DESCENT AT THE OTHER `*All` FRAME.  A `thru-outer` subscribes
-- each observable it is handed, so `stepFrame-nodes-thru` is this bound
-- arriving through a frame rather than at `root`, and it was repaired by
-- the same premise on the same day -- which is exactly why it must be
-- instantiated separately: the frame's charge carries a per-value unit
-- the descent's does not, and a receipt at `root` says nothing about it.
--
-- The witness is `Refuted.Thru-Subscribe-Nest`'s, which refuted both the
-- per-value and the caps-scaled forms, at the width its own hypotheses
-- pin: `1 ≤ W` and one value in the list.
----------------------------------------------------------------------

oThru : Val Γ₂ (obs (obs (obs natᵗ)))
oThru = mapᵉ dup₁ (ofᵉ (strmᵗ (deepV 40) ∷ []))

valsThru : List (Val Γ₂ (obs (obs (obs natᵗ))))
valsThru = oThru ∷ []

eThru : Closed Γ₂ (obs (obs natᵗ))
eThru = emptyᵉ

schedThru : Sched Γ₂
schedThru = sched-init eThru slots

stThru : EvalSt eThru
stThru = installNode 0 (mergeAll-st {t = obs (obs natᵗ)} nothing 0 [] false)
                     (st-init eThru)

fThru : Frame Γ₂ (obs (obs (obs natᵗ))) (obs (obs natᵗ))
fThru = thru-outer mergeAllᵒ 0

cThru : Caps
cThru = tight {obs (obs (obs natᵗ))} oThru

WThru : ℕ
WThru = 1

-- the premises, pinned rather than assumed: the cap is again the value's
-- own size and width, and the state is one ordinary installed node
premThru : (valCaps? cThru slots (obs (obs (obs natᵗ))) oThru ≡ true)
         × (capsOK? cThru schedThru stThru ≡ true)
premThru = refl , refl

deliveredThru : ℕ
deliveredThru =
  let r = stepFrame gas 0 0 fThru root valsThru false schedThru stThru
  in nodesMax (proj₂ (proj₂ (proj₂ (proj₂ r)))) ⊔ nestDᵛˢ (proj₁ r)

baseThru : ℕ
baseThru = (nodesMax stThru ⊔ nestDᵛˢ valsThru) + WThru

fitsThru : (deliveredThru ≤ᵇ 2 ^ Caps.cSize cThru * baseThru) ≡ true
fitsThru = refl

-- AND THE SAME MEASUREMENT HERE, where the margin is wider still: the
-- cap is read off a value forty layers deep, so the exponent the
-- statement grants is a hundred and seventy-three and the exponent the
-- program demands is ONE.  The crossing is the pair below, and it is the
-- row that could have failed -- at a factor of one the frame delivers
-- eighty against forty-one, which is the refutation this repair answers.
thruFigs : ℕ × ℕ × ℕ
thruFigs = deliveredThru , baseThru , Caps.cSize cThru

thruFigs≡ : thruFigs ≡ (80 , 41 , 173)
thruFigs≡ = refl

spendThru : ((deliveredThru ≤ᵇ 2 ^ 1 * baseThru) ≡ true)
          × ((deliveredThru ≤ᵇ 2 ^ 0 * baseThru) ≡ false)
spendThru = refl , refl

----------------------------------------------------------------------
-- AND THE DESCENT WHERE THE DRAIN ACTUALLY MAKES IT, which the rows
-- above do not reach: under a `from-inner` frame, from a node table that
-- already holds the `mergeAll-st` the queue was read out of.  The store
-- premise is the one that changes -- `nodesMax st` is no longer zero --
-- and it is the premise the drain re-establishes at every queued inner,
-- so a receipt at an empty table would have said nothing about it.
----------------------------------------------------------------------

pathInner : Path Γ₂ (obs (obs natᵗ)) (obs (obs natᵗ))
pathInner = from-inner mergeAllᵒ 0 1 ↠ root

readInner : ℕ × ℕ × ℕ
readInner =
  let r = subscribeE gas oThru pathInner 0 0 schedThru stThru
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs (obs natᵗ))} (proj₁ r)))
   , nodesMax stThru
   , nestDᵉ oThru + nestUnit eThru slots

premInner : (valCaps? cThru slots (obs (obs (obs natᵗ))) oThru ≡ true)
          × (capsOK? cThru schedThru stThru ≡ true)
premInner = refl , refl

readInner≡ : readInner ≡ (80 , 0 , 42)
readInner≡ = refl

-- the crossing again, and at the same one bit as through the frame
spendInner : ((proj₁ readInner ≤ᵇ 2 ^ 1 * proj₂ (proj₂ readInner)) ≡ true)
           × ((proj₁ readInner ≤ᵇ 2 ^ 0 * proj₂ (proj₂ readInner)) ≡ false)
spendInner = refl , refl

-- THE STORE READS ZERO HERE, which the middle figure says outright: the
-- installed node is an empty `mergeAll-st`.  So this row covers the PATH
-- the drain descends under and not the store it descends from; the
-- rows below do that.

----------------------------------------------------------------------
-- THE STORE AXIS, WHICH IS THE ONE THAT CAN STILL REFUTE.  `nodesMax st`
-- appears in the statement's PREMISE and `nodesMax st′` in its
-- conclusion, while the right-hand side mentions neither -- so a store
-- the descent grows past its own bound is a counterexample, and every
-- row above reads its store as zero.  These park a genuinely deep queue
-- in the table first: the same forty-layer payload the crossing rows
-- use, so the table's own nesting is large next to the base term.
----------------------------------------------------------------------

stDeep : EvalSt eThru
stDeep = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 (deepV 40 ∷ []) false)
                     (st-init eThru)

readDeep : ℕ × ℕ × ℕ
readDeep =
  let r = subscribeE gas oThru pathInner 0 0 schedThru stDeep
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs (obs natᵗ))} (proj₁ r)))
   , nodesMax stDeep
   , nestDᵉ oThru + nestUnit eThru slots

premDeep : (valCaps? cThru slots (obs (obs (obs natᵗ))) oThru ≡ true)
         × (capsOK? cThru schedThru stDeep ≡ true)
premDeep = refl , refl

readDeep≡ : readDeep ≡ (80 , 40 , 42)
readDeep≡ = refl

-- the crossing, at a store forty deep rather than empty
spendDeep : ((proj₁ readDeep ≤ᵇ 2 ^ 1 * proj₂ (proj₂ readDeep)) ≡ true)
          × ((proj₁ readDeep ≤ᵇ 2 ^ 0 * proj₂ (proj₂ readDeep)) ≡ false)
spendDeep = refl , refl

-- AND A STORE DEEPER THAN ANYTHING THE DESCENT EMITS, which is the
-- sharpest form of the axis: the parked queue is a hundred layers and
-- the emission eighty, so the `⊔` is decided by the store and the
-- statement is being asked whether a descent can carry a table it did
-- not build.  It can, and the crossing moves by exactly the one bit the
-- larger store costs -- which is the factor absorbing the store
-- linearly, not compounding with it.
stDeeper : EvalSt eThru
stDeeper = installNode 0 (mergeAll-st {t = natᵗ} nothing 0 (deepV 100 ∷ []) false)
                       (st-init eThru)

readDeeper : ℕ × ℕ × ℕ
readDeeper =
  let r = subscribeE gas oThru pathInner 0 0 schedThru stDeeper
  in nodesMax (proj₂ (proj₂ r))
       ⊔ nestDᵛˢ (proj₁ (splitBurst {A = Val Γ₂ (obs (obs natᵗ))} (proj₁ r)))
   , nodesMax stDeeper
   , nestDᵉ oThru + nestUnit eThru slots

-- THE CAP HAS TO BE WIDENED FOR THIS ROW, AND WHICH CONJUNCT FORCES IT
-- IS THE FINDING: `stBounded?`, the SIZE half.  `capsOK?` bounds what a
-- node holds, so a store deeper than the subscribed value's own cap is
-- not a state the statement is ever asked about -- the axis is capped
-- rather than free.  The cap here is therefore chosen to admit the
-- store and is NOT tight, which costs the row nothing: what it reports
-- is the crossing, and the crossing does not depend on the cap.
cDeeper : Caps
cDeeper = caps 2000 2000 2000

premDeeper : (valCaps? cDeeper slots (obs (obs (obs natᵗ))) oThru ≡ true)
           × (capsOK? cDeeper schedThru stDeeper ≡ true)
premDeeper = refl , refl

readDeeper≡ : readDeeper ≡ (100 , 100 , 42)
readDeeper≡ = refl

-- the store now DECIDES the `⊔` -- a hundred against the eighty emitted
-- -- and the crossing moves by exactly one bit against the forty-deep
-- row above, which is the factor absorbing the store linearly
spendDeeper : ((proj₁ readDeeper ≤ᵇ 2 ^ 2 * proj₂ (proj₂ readDeeper)) ≡ true)
            × ((proj₁ readDeeper ≤ᵇ 2 ^ 1 * proj₂ (proj₂ readDeeper)) ≡ false)
spendDeeper = refl , refl
