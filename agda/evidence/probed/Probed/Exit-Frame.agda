-- THE EXIT FRAME AND THE FLATTENER'S DRY OBLIGATION — `from-inner`
-- confirmed not to emit dry events and to carry its payload and store
-- unchanged; `thru-outer` confirmed not to emit dry events when the
-- store bound affords the descent.

-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.

-- FROM-INNER: FIN = FALSE IS THE ONLY REACHABLE PATH HERE.  The
-- `from-inner` frame dispatches on `fin`: when false it is an identity
-- — the same values and an empty event list come straight back — and
-- when true it checks whether any registration is alive-through before
-- deciding to drain.  Every row below takes `fin = false`, which is the
-- path the exit frame occupies between the inner source's first arrival
-- and its completion.  All three conjuncts of the carried row compare
-- zero against zero -- both halves of the payload pair and the store:
-- the element type is `natᵗ`, whose values carry neither deliveries nor
-- hop depth, so the payload is the origin by construction and the rows
-- are DEGENERATE there.  The dry row holds by the identity of `any` on an
-- empty list, which the `fin = false` arm always returns.  What these
-- two rows buy is the statement being instantiable at a real program
-- point, not a coverage claim on its argument space.

-- THRU-OUTER DRY: THE PREMISE IS WHAT SAYS NO DRY EVENT IS POSSIBLE.
-- `subscribeInner` branches on the rank of the `Acc` witness: rank zero
-- returns a dry event, rank `suc r` descends.  The premise reads the HOP
-- half of the payload pair — the entry invariant's rank conjunct, the
-- same one `thru-outer-frame-carried` carries — and it implies the rank
-- at which each arriving observable is subscribed is at least one, so
-- the dry branch is unreachable.  The rows use the same programs and
-- the same points as the `Probed.Hop-Edge` carried rows: the dry check
-- there was omitted because neither conjunct of `FrameCarries` names
-- it, and what these rows add is the dry field confirmed false at the
-- same points.  Both figures are LOAD-BEARING: the handed reading being
-- positive says the outer source did emit, and the rank being strictly
-- above it says the dry branch would not have fired even if it could.
-- The COUNT half is read separately and is saturated at every point --
-- handed equals held, so the delivery conjunct of the `⊑` premise is
-- decided rather than afforded, which is the axis the predecessor
-- currency had no column for at all.

-- THE BOUNDARY: no row below runs `thru-outer` over a stored STATE
-- where the rank is already spent — the dry branch is unreachable from
-- a root, and the park branch installs rather than subscribes, so
-- nothing here says what the frame does when it subscribes an inner
-- whose rank is zero.
--
-- TARGET: from-inner-carried @c53537
-- TARGET: from-inner-dry @16a4ef
-- TARGET: thru-outer-frame-dry @42ee6f
module Probed.Exit-Frame where

open import Data.Bool using (Bool; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using () renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent)
open import Rx.Exp using (Ctx; Closed; Tm; Fn; Val; natᵗ; obs; _×ᵗ_;
  ofᵉ; scanᵉ; mergeAllᵉ; strmᵗ; nat̂; fstᵗ; varᵗ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; depthᵉ; rdᵉ; ε)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Stream; Sched; EvalSt; NodeId; NodeState;
  AllOp; subscribeE; rootWitness; rootTri; root; _↠_; sched-init; st-init;
  mintNode; installNode; mergeAll-st; from-inner; thru-outer; mergeAllᵒ;
  splitBurst; stepFrame; stHop; dryEvent)
open import Verify-Rank-Sufficient.Carried using (valsRd)
open import Verify-Rank-Sufficient.Path-Fits
  using (from-inner-carried; from-inner-dry; thru-outer-frame-dry)
open import Probed.Apparatus using (Confirms; Below)

----------------------------------------------------------------------
-- THE FLATTENER'S FRAME AT THE SAME POINTS THE HOP-EDGE ROWS TAKE IT,
-- confirming that no dry event appears in the event list the frame
-- produces.  The `Ap` module is assembled the same way: mint the node,
-- install the merge state, subscribe the outer under the frame, and
-- hand the frame what the burst hands it.
----------------------------------------------------------------------

module Ap {n} {Γ : Ctx n} (ins : Slots Γ) (op : AllOp)
          (node : NodeState Γ) (prog : Closed Γ (obs natᵗ))
          (src : Closed Γ (obs (obs natᵗ))) where

  ψ : Fin n → Rd₃
  ψ = slotRd ins

  ac : Acc _≺_ (rootTri prog ins)
  ac = rootWitness prog ins

  nid : NodeId
  nid = proj₁ (mintNode (sched-init prog ins))

  r : Stream Γ (obs (obs natᵗ)) × Sched Γ × EvalSt prog
  r = subscribeE ac src (thru-outer op nid ↠ root) 0 0
        (proj₂ (mintNode (sched-init prog ins)))
        (installNode nid node (st-init prog))

  sp : List (Val Γ (obs (obs natᵗ)))
     × List (InstEvent (Val Γ (obs natᵗ))) × Bool
  sp = splitBurst (proj₁ r)

  vals : List (Val Γ (obs (obs natᵗ)))
  vals = proj₁ sp

  fin : Bool
  fin = proj₂ (proj₂ sp)

  sd : Sched Γ
  sd = proj₁ (proj₂ r)

  st : EvalSt prog
  st = proj₂ (proj₂ r)

  sf : List (Val Γ (obs natᵗ)) × List (InstEvent (Val Γ (obs natᵗ)))
     × Bool × Sched Γ × EvalSt prog
  sf = stepFrame ac 0 0 (thru-outer op nid) root vals fin sd st

  bound : ℕ
  bound = depthᵉ ψ src

  -- the payload the frame is held to: the outer's own reading, whose
  -- hop half is `bound` definitionally and whose count half is the
  -- axis the predecessor currency projected away
  Rin : Rd
  Rin = proj₂ (rdᵉ ψ ε src)

  rank : ℕ
  rank = proj₁ (proj₂ (rootTri prog ins))

  -- the event list is the dry channel: false says no dry event was
  -- produced and a true here would immediately refute the target
  dry : Bool
  dry = any dryEvent (proj₁ (proj₂ sf))

  -- radix 1000, low digit first: what the frame was handed, the
  -- bound it is held to, the rank, and the dry flag (last)
  packed : ℕ
  packed = proj₂ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * bound
         + 1000000 * rank
         + 1000000000 * (if dry then 1 else 0)

  -- radix 1000, low digit first: the count the frame was handed, and
  -- the count half of the payload it is held to
  counts : ℕ
  counts = proj₁ (valsRd ψ (obs (obs natᵗ)) vals)
         + 1000 * proj₁ Rin

----------------------------------------------------------------------
-- THE CLOSED CONTEXT
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

----------------------------------------------------------------------
-- THE INNER AND OUTER, copied from `Probed.Hop-Edge` so that the
-- same points are instantiated and the two families can be read
-- against each other without rebuilding the harness.
----------------------------------------------------------------------

deepen : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen = strmᵗ (mergeAllᵉ nothing (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ [])))

deepen2 : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ)
deepen2 = strmᵗ (mergeAllᵉ nothing (ofᵉ (strmᵗ (mergeAllᵉ nothing
            (ofᵉ (fstᵗ (varᵗ (here refl)) ∷ []))) ∷ [])))

liveSeed : Tm Γ₀ [] [] [] (obs natᵗ)
liveSeed = strmᵗ (mergeAllᵉ nothing
             (ofᵉ (strmᵗ (ofᵉ (nat̂ 0 ∷ [])) ∷ [])))

folded : Fn Γ₀ [] [] [] (obs natᵗ ×ᵗ natᵗ) (obs natᵗ) →
         List (Tm Γ₀ [] [] [] natᵗ) → Closed Γ₀ (obs natᵗ)
folded f xs = scanᵉ f liveSeed (ofᵉ xs)

src₁ src₂ src₃ : Closed Γ₀ (obs (obs natᵗ))
src₁ = ofᵉ (strmᵗ (folded deepen (nat̂ 0 ∷ [])) ∷ [])
src₂ = ofᵉ (strmᵗ (folded deepen (nat̂ 0 ∷ nat̂ 1 ∷ [])) ∷ [])
src₃ = ofᵉ (strmᵗ (folded deepen2 (nat̂ 0 ∷ nat̂ 1 ∷ [])) ∷ [])

mrg : Closed Γ₀ (obs (obs natᵗ)) → Closed Γ₀ (obs natᵗ)
mrg = mergeAllᵉ nothing

module A₁ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₁) src₁
module A₂ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₂) src₂
module A₃ = Ap ins₀ mergeAllᵒ (mergeAll-st {t = obs natᵗ} nothing 0 [] false)
              (mrg src₃) src₃

----------------------------------------------------------------------
-- THE DRY FIGURES, one per family.  Each is zero: the frame produced
-- no dry event at any of these points, and the rank column (third
-- digit) is strictly above the bound (second), confirming the premise
-- `suc Rin ≤ Rst` holds and was not vacuously satisfied.
--
-- Read low digit first at radix 1000: handed, bound, rank, dry.
----------------------------------------------------------------------

packed₁-is : A₁.packed ≡ 3002002
packed₁-is = refl

packed₂-is : A₂.packed ≡ 4003003
packed₂-is = refl

packed₃-is : A₃.packed ≡ 6005005
packed₃-is = refl

-- THE COUNT AXIS, read low digit first at radix 1000: what the frame
-- was handed, and the count half of the payload it is held to.  Both
-- are positive at every point and EQUAL at every point, so the `⊑`
-- premise is SATURATED on this half — decided rather than afforded, and
-- a reading that undercharged the outer by one delivery crosses here.
counts₁-is : A₁.counts ≡ 1001
counts₁-is = refl

counts₂-is : A₂.counts ≡ 2002
counts₂-is = refl

counts₃-is : A₃.counts ≡ 2002
counts₃-is = refl

----------------------------------------------------------------------
-- THE TARGET AT THREE POINTS, one per outer source.  The premise is
-- `suc A.bound ≤ A.rank`, which is DECIDED at each point and holds
-- by `Below` — a false premise would have made `Below` unsolvable,
-- and the packed figures confirm the rank exceeds the bound by one.
-- The rows prove by `refl` because the dry flag computed false.
----------------------------------------------------------------------

dryRow₁ : Confirms (thru-outer-frame-dry A₁.ac 0 0 mergeAllᵒ A₁.nid root
  A₁.ψ A₁.Rin A₁.rank Below A₁.vals A₁.fin A₁.sd A₁.st (Below , Below) Below)
dryRow₁ = refl

dryRow₂ : Confirms (thru-outer-frame-dry A₂.ac 0 0 mergeAllᵒ A₂.nid root
  A₂.ψ A₂.Rin A₂.rank Below A₂.vals A₂.fin A₂.sd A₂.st (Below , Below) Below)
dryRow₂ = refl

dryRow₃ : Confirms (thru-outer-frame-dry A₃.ac 0 0 mergeAllᵒ A₃.nid root
  A₃.ψ A₃.Rin A₃.rank Below A₃.vals A₃.fin A₃.sd A₃.st (Below , Below) Below)
dryRow₃ = refl

----------------------------------------------------------------------
-- THE EXIT FRAME SECTION.  A flat closed program with one nat value
-- in the burst and `fin = false` anchors the `Acc` witness.  The
-- element type is `natᵗ` — nat values carry no hop depth — so both
-- conjuncts of the carried row compare zero against zero and the rows
-- are degenerate in their payload half.  The dry row holds because
-- the `fin = false` arm of `innerReact` always returns an empty
-- event list.
----------------------------------------------------------------------

prog₀ : Closed Γ₀ natᵗ
prog₀ = ofᵉ (nat̂ 0 ∷ [])

-- the burst handed to the from-inner frame: one nat value
vals₀ : List (Val Γ₀ natᵗ)
vals₀ = 0 ∷ []

module Fi where
  ψ : Fin 0 → Rd₃
  ψ = λ ()

  ac : Acc _≺_ (rootTri prog₀ ins₀)
  ac = rootWitness prog₀ ins₀

  sd : Sched Γ₀
  sd = sched-init prog₀ ins₀

  st : EvalSt prog₀
  st = st-init prog₀

  -- fin = false: innerReact is identity; event list is empty
  sf : List (Val Γ₀ natᵗ) × List (InstEvent (Val Γ₀ natᵗ))
     × Bool × Sched Γ₀ × EvalSt prog₀
  sf = stepFrame ac 0 0 (from-inner {s = natᵗ} mergeAllᵒ 0 1) root
         vals₀ false sd st

  -- handed: the hop half at `vals₀` is 0 (nat values carry no depth)
  -- returned: same list = 0; store in and out: 0
  -- dry: any dryEvent [] = false (event list is empty)
  packed : ℕ
  packed = proj₂ (valsRd {Γ = Γ₀} ψ natᵗ vals₀)
         + 1000 * proj₂ (valsRd {Γ = Γ₀} ψ natᵗ (proj₁ sf))
         + 1000000 * stHop {Γ = Γ₀} ψ st
         + 1000000000 * stHop {Γ = Γ₀} ψ (proj₂ (proj₂ (proj₂ (proj₂ sf))))

fi-packed-is : Fi.packed ≡ 0
fi-packed-is = refl

----------------------------------------------------------------------
-- THE TWO EXIT-FRAME TARGETS, AT THIS POINT.  Both hypotheses hold by
-- `Below` at zero, and the carried row proves its two `≤` conjuncts
-- the same way; the dry row proves its `≡ false` conclusion by `refl`
-- because the event list the identity arm returns is empty.
----------------------------------------------------------------------

fromInnerCarried : Confirms (from-inner-carried Fi.ac 0 0 mergeAllᵒ 0 1 root
  Fi.ψ (0 , 0) 0 vals₀ false Fi.sd Fi.st (Below , Below) Below)
fromInnerCarried = (Below , Below) , Below

fromInnerDry : Confirms (from-inner-dry Fi.ac 0 0 mergeAllᵒ 0 1 root
  Fi.ψ (0 , 0) 0 vals₀ false Fi.sd Fi.st (Below , Below) Below)
fromInnerDry = refl
