-- THE REGISTRY'S DEPTH ALONG ONE CHAIN, walked frame by frame.
--
-- `chainStep` IS `foldPath`, so a statement about what one chain leaves
-- in the registry is an induction over the path with one leaf per
-- clause -- and the quantity that survives the induction is not the
-- registry alone but the POTENTIAL: the nesting of the values in flight
-- plus the depth of the path still to come, scaled by the factor that
-- path can still apply to them.  Every frame spends its own charge into
-- one of the three and never into two, which is why the potential is
-- what the walk carries and the registry is only read off it: a map
-- frame trades its factor for the values it produces, and a thru-outer
-- spends one unit of depth into the registration it mints.
--
-- WHY THE TWO STEP LEAVES ARE SEPARATE.  One says the registry does not
-- outrun the potential; the other says the potential itself survives
-- the frame.  Only the second is an invariant, and stating them
-- together would make the induction's own hypothesis a conjunct of the
-- thing being proven at every frame kind.
module Verify-Budget-Sufficient.Regs-Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤;
  ≤⇒≤ᵇ; ≤ᵇ⇒≤; m^n>0; *-zeroʳ; *-distribˡ-⊔; *-identityˡ; *-mono-≤; +-assoc; n≤1+n; m≤n+m)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong; cong₂)

open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to; T⇒≡true; ≤ᵇ-widen; ≤ᵇ-true)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; Source; InstEvent; close; exhausted;
  InstEmit; hot; cold)
open import Relation.Nullary using (yes; no)
open import Rx.Exp using (Ty; Ctx; Closed; Val; Fn; Tm; applyFn; sizeᵉ; sizeᵗ; sizeᵛ; _×ᵗ_; obs; _≟ᵗ_; input; ofᵉ;
  emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ; evalTm;
  unfoldμ)
open import Rx.Layer-Count using (layᵉ; layᵛ; layᵗ; muDepthᵉ; muDepthᵛ;
  lay-unfoldμ; muDepth-unfoldμ)
open import Rx.Slots using (Slots; slotsSize; shared; scripted)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; NodeId; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; foldPath; stepFrame; dispatchShare; thruWalk; shareGo;
  shareAdmit; shareLatch; iterSize; NodeState; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; takeDispatch; takeVals; lookupNode; mergeAllᵒ; switchᵒ; exhaustᵒ; mergeAllDrain;
  subscribeInner; subscribeE; splitBurst; hasRoom; Stream; pushBurst; splitEvents;
  subscribeSharedSlot; installNode; memberSource)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; thruWalk-nest; nodeNestAt; stepFrame-emit-scan; stepFrame-nodes-inner; capsDrainOK;
  FaceOK)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures
  using (thruWrap-vals; takeVals-all; pathLen; boundedNode; setNode-bounded; all-++-intro;
  n≤2^bitsᴺ; bitsᴺ)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nest-inflate; dropSource-nest; nestUnit; cutThrough-nest)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; sizeCount; iterSize-mono-count; iterSize-2^)
open import Verify-Budget-Sufficient.Keeps-Ring
  using (subscribeE-slots; size-unfoldμ)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Caps-Depth using (depthReact)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; iterSize-+; iterSize-mono-s; pathStrat?; pathFloor; parkStrat?;
  pathOrd?; pathPark?)
open import Verify-Budget-Sufficient.Nest-Subst using (applyFn-nest)

-- the potential, read off the values still in flight and the path they
-- have left to climb -- and SCALED by the path's own factor, because
-- what a frame does to a value is substitution and substitution is
-- multiplicative in this currency.  The factor is spent frame by frame:
-- each one hands its share to the value it produces, so the product
-- shrinks exactly as fast as the value it multiplies can grow.
valsΦ? : ∀ {n} {Γ : Ctx n} {s t} (B U : ℕ) (path : Path Γ s t)
  (vals : List (Val Γ s)) → Bool
valsΦ? {s = s} B U path vals =
  all (λ v → pathΦF B path * (nestDᵛ s v + pathΦD B path) ≤ᵇ U) vals

-- WHAT A FRAME OWES BEYOND THE POTENTIAL IT IS HANDED, which is
-- nothing at three of the five: they forward or substitute, and the
-- factor the path surrenders pays for it.  The outer frame does not
-- forward -- it SUBSCRIBES -- so what comes back is bounded by nothing
-- the incoming values say, and the only thing that does bound it is
-- the sighted grant the walk face already runs on.  Stating the debt
-- per frame rather than per statement is what keeps the fold uniform:
-- the forwarding arms discharge it with `tt`, and an arm that reaches
-- past its own values has to find a grant.
--
-- AND THE SCAN ARM READS THE TABLE, WHICH IS WHY IT IS NOT A UNIT.
-- The value a fold emits is its accumulator, and the accumulator was
-- in the node before any of these values arrived -- so no premise
-- about `vals` bounds it, at any budget.  What the grant has to carry
-- besides the table is a WIDTH: a fold THREADS, so a burst of k values
-- applies the step function k times in sequence, while the potential
-- surrenders the frame's factor once and charges its nesting once.
-- Both of those are read off the step function alone and neither
-- mentions the burst, so a state grant on its own leaves the premise
-- constant in the value count against a conclusion linear in it.  The
-- width is `length vals`, which is already in scope here, and the
-- factors are the ones `stepFrame-nodes-scan` is proven at -- a power
-- in the width rather than another summand, because one substitution
-- is multiplicative and iterating it puts the factor in the exponent.
-- AND THE DRAIN ARM READS THE QUEUE, WHICH IS A SECOND TABLE.  What a
-- `from-inner` hands on is what the inner run produced, and the inner
-- run SUBSCRIBES the observables the merge node was holding -- so this
-- arm too reaches past the values it was given, and for the same
-- structural reason the scan arm does.  What it does NOT need is the
-- scan arm's width: a queue does not thread, so draining k entries
-- runs the step function once per entry rather than k times in
-- sequence, and nothing accrues.  A FACTOR it does need, because a
-- subscription substitutes into the term it takes, and one occurrence
-- of the payload on each side of a sum doubles what leaves under a
-- ceiling that does not move.
--
-- SO THE GRANT IS THE ITERATION FACE'S, DENOMINATED IN CAPS.  The
-- factors are `nestFac` and `nestU` at a size cap the drain reports a
-- LEVEL for rather than fixing in advance, which is why the numeric
-- fit is quantified over every level within the descent's own count
-- instead of being read at one: the level is an output of the walk,
-- and a fit at a single level would be a fit at a number the caller
-- cannot name.

-- AND THE CAPS CONJUNCT MINTS A CEILING OBLIGATION ON A FACE THAT HAS
-- NO CEILING CURRENCY, which is a finding about this record rather
-- than about whoever discharges it.  The drain ledger it names opens
-- with a level ceiling, and that object is CONSUMED at every one of
-- its sites in proven code and produced at none.  The caps face
-- delivers the whole ledger anyway, off a walk record whose ceiling
-- half is a ring POSITION; this record carries no such package, and
-- neither does the frame fit above it nor the arm that discharges it.
--
-- WHICH IS WHY THE ARM UNDER IT IS SHAPE AND NOT A GRIND.  A
-- conclusion needing information no hypothesis carries does not become
-- reachable by a better proof, and what the ledger is short of is the
-- caps invariant itself, projected down to its registry component one
-- call above the fold both faces share.  The repair is to carry that
-- receipt unprojected rather than to mint a ceiling at the arm, which
-- would trade a counted gap for an uncounted one.  The arm's own
-- header holds the census, the deliverer, the frame that drops the
-- receipt and the coverage boundary.
InnerΦBody : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (B U : ℕ)
  (op : AllOp) (allNid inst : NodeId) (path : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
InnerΦBody {Γ = Γ} {e = e} {s = s} sf id now B U op allNid inst path vals fin sched st =
  Σ Caps λ c → Σ ℕ λ d → Σ ℕ λ W → Σ ℕ λ Lv → Σ ℕ λ G →
    FaceOK c (Sched.slots sched)
    × (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
         lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
         capsDrainOK c (Sched.slots sched) d Lv sf allNid path id now lim
           (pred act) q sched st)
    × (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
         lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
         drainW sf allNid path id now q sched st ≤ W)
    × (depthReact sf op allNid inst path id now vals sched st fin ≤ d)
    × (pathSz? (Caps.cSize (frameStep Lv c)) path ≡ true)
    × (suc (pathLen path) ≤ Caps.cSize (frameStep Lv c))
    × (pathStrat? path ≡ true)
    × (parkStrat? (pathFloor path) (lookupNode allNid (EvalSt.nodes st)) ≡ true)
    × (nodeNestAt allNid st ⊔ nestDᵛˢ vals ≤ G)
    × (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
         pathΦF B path
           * (nestFac (Caps.cSize (frameStep j c)) W
                * (G + nestU (Caps.cSize (frameStep j c))
                         (nestUnit e (Sched.slots sched)))
              + pathΦD B path) ≤ U)

-- AND THE TWO REGISTRY READINGS THE DESCENT UNDER THIS FRAME SPENDS,
-- carried for the reason the cell's own reading inside the body is:
-- neither follows from a caps receipt, which a caps-legal state the
-- evaluator never built already refutes.  They stand OUTSIDE the
-- existential rather than beside their sibling inside it, so a producer
-- holding them at the chain hands them straight over and nothing
-- between the walk and the descent has to carry them.
InnerΦFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (B U : ℕ)
  (op : AllOp) (allNid inst : NodeId) (path : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
InnerΦFit sf id now B U op allNid inst path vals fin sched st =
  (pathOrd? (Sched.nextNode sched) (thru-outer op allNid ↠ path) ≡ true)
  × (pathPark? path st ≡ true)
  × InnerΦBody sf id now B U op allNid inst path vals fin sched st

FrameΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (B U : ℕ)
  (f : Frame Γ s u) (path : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
FrameΦHyp sf id now B U (map-f _)  path vals fin sched st = ⊤
FrameΦHyp sf id now B U (take-f _) path vals fin sched st = ⊤
FrameΦHyp sf id now B U (from-inner op allNid inst) path vals fin sched st =
  InnerΦFit sf id now B U op allNid inst path vals fin sched st
FrameΦHyp sf id now B U (scan-f fn nid) path vals fin sched st =
  Σ ℕ λ G →
    (nodeNestAt nid st ⊔ nestDᵛˢ vals ≤ G)
    × (pathΦF B path
        * ((2 ^ sizeᵗ fn) ^ length vals * (G + length vals * nestDᵗ fn)
           + pathΦD B path) ≤ U)
FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st =
  Σ ℕ λ k → Σ ℕ λ G →
    ValsFit k (Sched.slots sched) G path vals
    × (pathΦF B path * (G + pathΦD B path) ≤ U)

-- THE THREE FRAMES THAT REGISTER NOTHING, each for its own reason and
-- none of them the potential's.  A map returns the state it was
-- handed; a scan rewrites the node table and nothing else, whichever
-- branch the accumulator's type test takes; and a take either passes
-- the prefix through or CUTS, and a cut keeps a sublist of the
-- registry it was handed.  So the registry the walk leaves is under
-- the one it entered on, with no budget spent at all -- which is what
-- lets the three arms be read off the entry registry instead of off a
-- premise the drain's counterexample shows they cannot have.
abstract
  stepFrame-regs-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (nid : NodeId) (p : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (scan-f fn nid) p vals fin sched st in
    regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      ≤ regsNestMax (EvalSt.registry st)
  stepFrame-regs-scan {u = u} sf id now fn nid p vals fin sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                    = ≤-refl
  ... | just (take-st _)           = ≤-refl
  ... | just (mergeAll-st _ _ _ _) = ≤-refl
  ... | just (switch-st _ _)       = ≤-refl
  ... | just (exhaust-st _ _)      = ≤-refl
  ... | just (scan-st {w} a) with w ≟ᵗ u
  ...   | no _     = ≤-refl
  ...   | yes refl = ≤-refl

  stepFrame-regs-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (nid : NodeId) (p : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
    let r = stepFrame sf id now (take-f nid) p vals fin sched st in
    regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      ≤ regsNestMax (EvalSt.registry st)
  stepFrame-regs-take sf id now nid p vals fin sched st
    with lookupNode nid (EvalSt.nodes st)
  ... | nothing                    = ≤-refl
  ... | just (scan-st _)           = ≤-refl
  ... | just (mergeAll-st _ _ _ _) = ≤-refl
  ... | just (switch-st _ _)       = ≤-refl
  ... | just (exhaust-st _ _)      = ≤-refl
  ... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
  ...   | true  = cutThrough-nest nid (EvalSt.delivered st) (EvalSt.regWatermark st)
                                  (EvalSt.dying st) (EvalSt.registry st)
  ...   | false = ≤-refl

postulate
  -- THE DRAIN FRAME'S OWN REGISTRATIONS, and this is the arm the
  -- counterexample lands at.  A `from-inner` takes its payload out of
  -- the *All node's queue rather than out of the burst, so a completion
  -- walk clears `valsΦ?` by computation at every budget -- `all` over
  -- an empty list -- and still subscribes a queued term, appending a
  -- registration whose path carries a fresh `thru-outer` frame.  The
  -- grant is what has to pay, and it is the one the potential's own arm
  -- already takes.
  --
  -- AND THE GRANT PAYS EXACTLY, WHICH IS WHAT THE INSTANTIATION SAYS.
  -- What the drain appends is a chain carrying the popped term's own
  -- flatten layers, and the popped term sat in the queue the grant's
  -- `G` is read off -- so the mint is the node's reading and not one
  -- layer more.  The rows below therefore stand at the node reading
  -- itself, a number the grant's own conjuncts put a floor under, and
  -- clear by ZERO at every rung.  A charge one layer above the queue
  -- would show as a constant margin; a charge that grew with anything
  -- else would cross.
  --
  -- REFUTED: Refuted.Drain-Regs-Nest
  -- PROBED: `Probed.Frame-Drain-Store` -- the same drain the nodes face
  --   is instantiated at, read on this axis: a queue reached by running
  --   an outer frame of three arrivals into a capacity-one merge, so
  --   two park and the drain pops the deeper one.  Covered: the mint at
  --   three rungs of a flatten ladder against an entry registry that
  --   stands still, each at the node reading and each at margin zero;
  --   and the gated term, which registers without unfolding.  NOT
  --   covered: the switch and exhaust arms, which keep no queue; an
  --   empty parent queue; and a nonempty path under the frame.
  -- RECOVERY: git show f38a902:agda/evidence/probed/Probed/Chain-Step-Regs-Rootward.agda
  --   restores a rootward-stacking program and its readings.
  stepFrame-nest-regs-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
    (path : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (from-inner op allNid inst ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U (from-inner op allNid inst) path vals fin sched st →
    regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame sf id now (from-inner op allNid inst) path vals fin sched st))))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U

  -- THE OUTER FRAME'S OWN, which is where the potential is the right
  -- charge rather than the frame's size: what a `thru-outer` registers
  -- is the subscribed value's frames over the REST of the path, and
  -- that is the potential exactly.
  --
  -- PROBED: `Probed.Thru-Outer-Store` -- the same frame and the same
  --   arrival ladder the nodes face is instantiated at, read on this
  --   axis: the chain a subscribe appends carries the arrival's own
  --   flatten layers, so the registry's fold climbs rung by rung while
  --   the entry registry stands still, and the potential covers it by a
  --   constant one throughout.  Covered: the merge arm at three rungs,
  --   at the budget the value premise licenses at burst zero.  Not
  --   covered: a nonempty path under the frame, since the root is what
  --   holds that budget at its floor; and the frame grant, which is a Σ
  --   and does not compute.
  stepFrame-nest-regs-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (path : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (thru-outer op nid ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st →
    regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame sf id now (thru-outer op nid) path vals fin sched st))))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U

-- ONE FRAME'S REGISTRATIONS, under the potential it was handed and the
-- frame grant beside it.  Only the two *All frames register at all, so
-- the other three arms spend neither premise: they are read off the
-- entry registry, which is the join's own left half.
stepFrame-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (B U : ℕ) →
  valsΦ? B U (f ↠ path) vals ≡ true →
  FrameΦHyp sf id now B U f path vals fin sched st →
  regsNestMax (EvalSt.registry
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
    ≤ regsNestMax (EvalSt.registry st) ⊔ U
stepFrame-nest-regs sf id now (map-f fn) path vals fin sched st B U _ _ =
  m≤m⊔n (regsNestMax (EvalSt.registry st)) U
stepFrame-nest-regs sf id now (scan-f fn nid) path vals fin sched st B U _ _ =
  ≤-trans (stepFrame-regs-scan sf id now fn nid path vals fin sched st)
          (m≤m⊔n (regsNestMax (EvalSt.registry st)) U)
stepFrame-nest-regs sf id now (take-f nid) path vals fin sched st B U _ _ =
  ≤-trans (stepFrame-regs-take sf id now nid path vals fin sched st)
          (m≤m⊔n (regsNestMax (EvalSt.registry st)) U)
stepFrame-nest-regs sf id now (from-inner op allNid inst) path vals fin sched st B U hΦ hF =
  stepFrame-nest-regs-inner sf id now op allNid inst path vals fin sched st B U hΦ hF
stepFrame-nest-regs sf id now (thru-outer op nid) path vals fin sched st B U hΦ hF =
  stepFrame-nest-regs-outer sf id now op nid path vals fin sched st B U hΦ hF

-- ONE MAP FRAME, and it is the clause the additive reading died at.  A
-- step function may name its payload on both sides of an additive
-- `nestDᵉ`, so ONE substitution installs the payload's nesting twice
-- while the path gives up only the function's own -- which is why the
-- potential carries the path's factor and not just its depth.  Here
-- the two moves cancel exactly: the frame surrenders two to its own
-- size, substitution may claim precisely that, and what is left is the
-- same product read one frame further down.
mapΦ : ∀ {n} {Γ : Ctx n} {s u t} (B U : ℕ) (fn : Fn Γ [] [] [] s u)
  (p : Path Γ u t) (vals : List (Val Γ s)) →
  valsΦ? B U (map-f fn ↠ p) vals ≡ true →
  valsΦ? B U p (map (applyFn fn) vals) ≡ true
mapΦ B U fn p [] h = refl
mapΦ {s = s} {u = u} B U fn p (v ∷ vs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ step)) (mapΦ B U fn p vs (∧-trueʳ h))
  where
  F = pathΦF B p
  E = 2 ^ sizeᵗ fn
  hv : E * F * (nestDᵛ s v + (nestDᵗ fn + pathΦD B p)) ≤ U
  hv = ≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ h))
  shape : F * (E * (nestDᵗ fn + nestDᵛ s v) + E * pathΦD B p)
            ≡ E * F * (nestDᵛ s v + (nestDᵗ fn + pathΦD B p))
  shape = solve 5 (λ f e d nt np →
            f :* (e :* (nt :+ d) :+ e :* np)
              := e :* f :* (d :+ (nt :+ np)))
          refl F E (nestDᵛ s v) (nestDᵗ fn) (pathΦD B p)
  step : F * (nestDᵛ u (applyFn fn v) + pathΦD B p) ≤ U
  step =
    ≤-trans (*-monoʳ-≤ F (+-monoˡ-≤ (pathΦD B p) (applyFn-nest fn v)))
    (≤-trans (*-monoʳ-≤ F (+-monoʳ-≤ (E * (nestDᵗ fn + nestDᵛ s v))
                (nest-inflate E (pathΦD B p) (m^n>0 2 (sizeᵗ fn)))))
    (≤-trans (≤-reflexive shape) hv))

-- a UNIFORM bound over the emitted list becomes the pointwise
-- predicate the potential is stated as, and nothing else is needed:
-- the depth of each value is under the maximum, and the maximum is
-- what the grant bounds.
Φ-of-bound : ∀ {n} {Γ : Ctx n} {u t} (B U G : ℕ) (p : Path Γ u t)
  (vs : List (Val Γ u)) → nestDᵛˢ vs ≤ G →
  pathΦF B p * (G + pathΦD B p) ≤ U → valsΦ? B U p vs ≡ true
Φ-of-bound B U G p []       hb hfit = refl
Φ-of-bound {u = u} B U G p (v ∷ vs) hb hfit =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
            (≤-trans (*-monoʳ-≤ (pathΦF B p)
                       (+-monoˡ-≤ (pathΦD B p)
                         (≤-trans (m≤m⊔n (nestDᵛ u v) (nestDᵛˢ vs)) hb)))
                     hfit)))
          (Φ-of-bound B U G p vs
            (≤-trans (m≤n⊔m (nestDᵛ u v) (nestDᵛˢ vs)) hb) hfit)

-- AND THE READING BACK, which is what a consumer needs to NAME a
-- grant: the pointwise predicate bounds every value's depth under the
-- same product, so it bounds their maximum under it too.  The path's
-- own depth does not come back out -- at the empty list there is
-- nothing to have carried it -- so this reads the values alone and a
-- consumer that wants the path's share takes it from the premise it
-- was handed.
Φ-to-bound : ∀ {n} {Γ : Ctx n} {u t} (B U : ℕ) (p : Path Γ u t)
  (vs : List (Val Γ u)) → valsΦ? B U p vs ≡ true →
  pathΦF B p * nestDᵛˢ vs ≤ U
Φ-to-bound B U p []       h =
  ≤-trans (≤-reflexive (*-zeroʳ (pathΦF B p))) z≤n
Φ-to-bound {u = u} B U p (v ∷ vs) h =
  ≤-trans (≤-reflexive (*-distribˡ-⊔ (pathΦF B p) (nestDᵛ u v) (nestDᵛˢ vs)))
          (⊔-lub head (Φ-to-bound B U p vs (∧-trueʳ h)))
  where
  head : pathΦF B p * nestDᵛ u v ≤ U
  head =
    ≤-trans (*-monoʳ-≤ (pathΦF B p) (m≤m+n (nestDᵛ u v) (pathΦD B p)))
            (≤ᵇ⇒≤ _ U (T-to (∧-trueˡ h)))

-- AND A CHEAPER PATH INHERITS A DEARER ONE'S RECEIPT, which is the
-- whole of what a hand-over spends at its fan-out.  The predicate is
-- pointwise and its two path-denominated inputs occur monotonically in
-- it, so a path under another in BOTH is under it at every value at
-- once -- no reading of what the values carry, and no induction on the
-- paths.
valsΦ?-mono : ∀ {n} {Γ : Ctx n} {u t} (B U : ℕ) (p q : Path Γ u t)
  (vs : List (Val Γ u)) →
  pathΦF B p ≤ pathΦF B q → pathΦD B p ≤ pathΦD B q →
  valsΦ? B U q vs ≡ true → valsΦ? B U p vs ≡ true
valsΦ?-mono B U p q []       hF hD h = refl
valsΦ?-mono {u = u} B U p q (v ∷ vs) hF hD h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
            (≤-trans (*-mono-≤ hF (+-monoʳ-≤ (nestDᵛ u v) hD))
                     (≤ᵇ⇒≤ _ U (T-to (∧-trueˡ h))))))
          (valsΦ?-mono B U p q vs hF hD (∧-trueʳ h))

-- THE OUTER FRAME, DISCHARGED FROM THE GRANT.  The frame's own arm
-- says nothing about what a subscription returns, so the bound cannot
-- come from the values handed in; it comes from the walk face, which
-- already proves that a sighted walk emits nothing deeper than the
-- grant it ran under.  What the potential then has to afford is the
-- grant rather than the arrival, and that is what the size-cap factor
-- at this frame is for -- at a factor of one the two sides trade at a
-- rate the arrival's depth outruns, which is what running it said.
--
-- REFUTED: `Refuted.Thru-Subscribe-Nest` -- eighty against forty-one,
--   at a payload forty `*All` layers deep behind a step function
--   naming it on both sides of a `mapᵉ` sum.  The depth is a free
--   parameter of the witness, so the grant-free reading is closed to
--   no constant and this one carries a grant.
thruΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
  FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st →
  valsΦ? B U path
    (proj₁ (stepFrame sf id now (thru-outer op nid) path vals fin sched st))
    ≡ true
thruΦ sf id now op nid path vals fin sched st B U (k , G , hfit , hnum) =
  subst (λ vs → valsΦ? B U path vs ≡ true)
        (sym (thruWrap-vals op nid fin
               (thruWalk sf op nid path id now vals sched st)))
        (Φ-of-bound B U G path
          (proj₁ (thruWalk sf op nid path id now vals sched st))
          (proj₁ (thruWalk-nest G sf op nid path id now vals sched st
                   (thruFit-vals k (Sched.slots sched) G sf op nid path id now
                     vals sched st refl hfit)))
          hnum)

-- THE SCAN FRAME'S OUTPUT IS THE ACCUMULATOR'S IMAGE, AND THE
-- ACCUMULATOR IS IN THE NODE TABLE, so this arm reads a payload the
-- values handed in do not measure.  The unconditional reading pays the
-- factor the map clause is proven from, and that factor is spent
-- against the value the walk handed over -- which is not the value the
-- fold emits -- so it is FALSE, and the grant is what replaces it
-- rather than a weakening of it.
--
-- WHY NO CONSTANT REPAIRS IT.  Let the step function be the first
-- projection.  Then it charges nothing and the emit IS the stored
-- value, so the premise reads one numeral -- depth zero, under a
-- charge of zero -- and holds at `U = 0`, the strongest budget there
-- is, while the emit leaves at whatever depth the table was carrying.
-- Doubling the stored depth doubles what leaves and moves the premise
-- not at all, so the gap is a parameter of the STATE and no constant
-- and no term in `vals`, `path` or `B` closes it.
--
-- AND A GRANT OVER THE NODE ALONE DOES NOT EITHER, which is the half
-- that fixed the arm's factors.  A fold THREADS, so its k-th output is
-- the step function applied k times in sequence, while the potential
-- surrenders `2 ^ sizeᵗ fn` once and charges `nestDᵗ fn` once -- both
-- read off the step function alone, neither mentioning the burst.  So
-- a state grant on its own leaves the premise constant in the value
-- count against a conclusion linear in it, and the factor buys a fixed
-- number of values rather than a bound.  What closes it is a width,
-- and one substitution being MULTIPLICATIVE is what puts that width in
-- the exponent rather than under another summand.
--
-- REFUTED: `Refuted.Scan-Acc-Nest.stepFrame-nest-Φ-scan-absurd` at a
--   stored depth of forty, and
--   `Refuted.Scan-Acc-Nest.stepFrame-nest-Φ-scan-wide-absurd` at
--   eighty -- the pair is what puts the gap in the stored depth
--   rather than in a constant.
-- REFUTED: `Refuted.Scan-Phi-Burst.scan-Φ-burst-absurd` kills the
--   store-grant-only reading against a CONSTANT-in-burst frame charge,
--   which it states itself rather than importing: the accumulator is a
--   bare `ofᵉ`, so every grant a state can carry is discharged for
--   nothing and the premise still holds at the budget such a frame
--   surrenders, while sixty-five folds leave sixty-five layers.  Its
--   `live-factor` pins what the arm's factor is worth today against
--   that reading, so a further repricing fails there naming a number.
--   `Refuted.Scan-Fold-Burst` is the same witness read on the
--   iteration's quantity, which is what makes the two faces
--   comparable.
scanΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
  (nid : NodeId) (path : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
  FrameΦHyp sf id now B U (scan-f fn nid) path vals fin sched st →
  valsΦ? B U path
    (proj₁ (stepFrame sf id now (scan-f fn nid) path vals fin sched st))
    ≡ true
scanΦ sf id now fn nid path vals fin sched st B U (G , hst , hnum) =
  Φ-of-bound B U ((2 ^ sizeᵗ fn) ^ length vals * (G + length vals * nestDᵗ fn))
    path (proj₁ r) bound hnum
  where
  r = stepFrame sf id now (scan-f fn nid) path vals fin sched st
  bound : nestDᵛˢ (proj₁ r)
        ≤ (2 ^ sizeᵗ fn) ^ length vals * (G + length vals * nestDᵗ fn)
  bound =
    ≤-trans
      (stepFrame-emit-scan (length vals) sf id now fn nid path vals fin
        sched st ≤-refl)
      (*-monoʳ-≤ ((2 ^ sizeᵗ fn) ^ length vals)
        (+-monoˡ-≤ (length vals * nestDᵗ fn) hst))

-- THE INNER FRAME'S OUTPUT DOES NOT COME FROM THE FRAME AT ALL -- it
-- is what the inner run produced -- and the frame's factor is one, so
-- there is nothing here to pay a deepening with.  The unconditional
-- reading asks that an inner run cannot hand out a value deeper than
-- the potential the outer walk was already carrying, and that is
-- FALSE: a completion walk carries no value, so its premise reads
-- `all _ []` -- true at EVERY budget -- while the drained values' own
-- depth is read straight against that budget with no factor in front
-- to absorb anything.  A queue holding a payload `k` layers deep under
-- a step function naming it twice drains `2 * k`, and nothing in
-- `vals`, `path` or `B` moves with `k`.
--
-- SO THE GRANT REPLACES A FALSE STATEMENT RATHER THAN WEAKENING A TRUE
-- ONE, and it is the family's own per-frame obligation rather than a
-- hypothesis on this signature -- the same place the `thru-outer` arm
-- already carries its debt, and for the same structural reason: the
-- drain under this frame subscribes too, reaching `subscribeInner`
-- through `mergeAllDrain`, so what comes back is bounded by nothing
-- the incoming values say.  The walk face hands the emitted depth over
-- on its own, read at the ONE entry `innerFinish` looks up rather than
-- at the whole table, so there is no join to project out of and the
-- store the grant names is this node's queue; the level the descent
-- reports is an output, which is why the grant's numeric fit is
-- quantified over the levels the descent's own count admits.
--
-- REFUTED: `Refuted.Inner-Drain-Nest.stepFrame-nest-Φ-inner-absurd` at
--   double occurrence, and
--   `Refuted.Inner-Drain-Nest.stepFrame-nest-Φ-inner-trip-absurd` at
--   triple -- the pair is what puts the gap in the occurrence count
--   rather than in a constant.
innerΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
  FrameΦHyp sf id now B U (from-inner op allNid inst) path vals fin sched st →
  valsΦ? B U path
    (proj₁ (stepFrame sf id now (from-inner op allNid inst) path vals
                      fin sched st))
    ≡ true
innerΦ {e = e} sf id now op allNid inst path vals fin sched st B U
       (stR , stK , c , d , W , Lv , G , face , hdr , hw , hdp , hpk , hpl , stP , stQ , hst , hnum) =
  Φ-of-bound B U (nestFac S′ W * (G + nestU S′ (nestUnit e (Sched.slots sched))))
    path (proj₁ r) bound (hnum j (proj₁ (proj₂ INNER)))
  where
  r = stepFrame sf id now (from-inner op allNid inst) path vals fin sched st

  INNER = stepFrame-nodes-inner c d (Sched.slots sched) W Lv sf id now op
            allNid inst path vals fin sched st ⦃ face ⦄ refl hdr hw hdp hpk hpl stP stQ stR stK

  j = proj₁ INNER

  S′ = Caps.cSize (frameStep j c)

  bound : nestDᵛˢ (proj₁ r)
        ≤ nestFac S′ W * (G + nestU S′ (nestUnit e (Sched.slots sched)))
  bound =
    ≤-trans (proj₂ (proj₂ (proj₂ INNER)))
      (*-monoʳ-≤ (nestFac S′ W)
        (+-monoˡ-≤ (nestU S′ (nestUnit e (Sched.slots sched))) hst))

-- THE TAKE FRAME CARRIES A FACTOR OF ONE AND NO DEPTH, so its
-- hypothesis and its conclusion are the SAME predicate read either
-- side of the gate, and the whole of what it owes is that the values
-- it lets through are among the ones handed to it.  They are: the
-- gate emits a PREFIX of its input on the arm that has a counter and
-- nothing at all on the arms that do not, so the reading survives
-- pointwise rather than being re-derived, and the factor of one is
-- spent only against `1 * F ≡ F`.
takeDispatchΦ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (p : Val Γ s → Bool) (nid : NodeId) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (m : Maybe (NodeState Γ)) →
  all p vals ≡ true →
  all p (proj₁ (takeDispatch {t = t} {e = e} nid vals fin sched st m)) ≡ true
takeDispatchΦ p nid vals fin sched st (just (take-st k)) h
  with proj₂ (proj₂ (takeVals k vals))
... | true  = takeVals-all p k vals h
... | false = takeVals-all p k vals h
takeDispatchΦ p nid vals fin sched st nothing                     h = refl
takeDispatchΦ p nid vals fin sched st (just (scan-st _))          h = refl
takeDispatchΦ p nid vals fin sched st (just (mergeAll-st _ _ _ _)) h = refl
takeDispatchΦ p nid vals fin sched st (just (switch-st _ _))      h = refl
takeDispatchΦ p nid vals fin sched st (just (exhaust-st _ _))     h = refl

stepFrame-nest-Φ-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (nid : NodeId) (path : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (B U : ℕ) →
  valsΦ? B U (take-f nid ↠ path) vals ≡ true →
  valsΦ? B U path
    (proj₁ (stepFrame sf id now (take-f nid) path vals fin sched st))
    ≡ true
stepFrame-nest-Φ-take {Γ = Γ} {t = t} {e = e} {s = s}
                      sf id now nid path vals fin sched st B U hΦ =
  takeDispatchΦ {t = t} {e = e} p nid vals fin sched st
    (lookupNode nid (EvalSt.nodes st)) hΦ′
  where
  p : Val Γ s → Bool
  p v = pathΦF B path * (nestDᵛ s v + pathΦD B path) ≤ᵇ U

  hΦ′ : all p vals ≡ true
  hΦ′ = subst (λ F → all (λ v → F * (nestDᵛ s v + pathΦD B path) ≤ᵇ U) vals
                       ≡ true)
              (*-identityˡ (pathΦF B path)) hΦ

-- THE POTENTIAL ACROSS ONE FRAME, which is the induction's own
-- hypothesis: every frame kind either hands its factor to the value it
-- produces or spends a unit of depth into what it mints, and never
-- both.  The map clause is the one that is DERIVED rather than
-- assumed, and it is derived from the substitution bound directly --
-- so the shape of this whole statement is tested at the frame kind
-- where the currency was chosen, instead of asserted at all five.
stepFrame-nest-Φ : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (B U : ℕ) →
  valsΦ? B U (f ↠ path) vals ≡ true →
  FrameΦHyp sf id now B U f path vals fin sched st →
  valsΦ? B U path (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true
stepFrame-nest-Φ sf id now (map-f fn) path vals fin sched st B U hΦ _ =
  mapΦ B U fn path vals hΦ
stepFrame-nest-Φ sf id now (scan-f fn nid) path vals fin sched st B U _ hF =
  scanΦ sf id now fn nid path vals fin sched st B U hF
stepFrame-nest-Φ sf id now (take-f nid) path vals fin sched st B U hΦ _ =
  stepFrame-nest-Φ-take sf id now nid path vals fin sched st B U hΦ
stepFrame-nest-Φ sf id now (from-inner op allNid inst) path vals fin sched st B U _ hF =
  innerΦ sf id now op allNid inst path vals fin sched st B U hF
stepFrame-nest-Φ sf id now (thru-outer op nid) path vals fin sched st B U _ hF =
  thruΦ sf id now op nid path vals fin sched st B U hF

-- THE SIZE READING OF A BURST, which is the currency every side
-- condition that must see through a defer gate is denominated in: the
-- nesting measures read ZERO into a deferred body, and size does not.
valsSz? : ∀ {n} {Γ : Ctx n} {s} (V : ℕ) (vals : List (Val Γ s)) → Bool
valsSz? {s = s} V vals = all (λ v → sizeᵛ s v ≤ᵇ V) vals

valsSz?-mono : ∀ {n} {Γ : Ctx n} {s} (V V′ : ℕ) (vals : List (Val Γ s)) →
  V ≤ V′ → valsSz? V vals ≡ true → valsSz? V′ vals ≡ true
valsSz?-mono V V′ []       h _  = refl
valsSz?-mono {s = s} V V′ (v ∷ vs) h hv =
  ∧-intro (≤ᵇ-widen (sizeᵛ s v) h (∧-trueˡ hv))
          (valsSz?-mono V V′ vs h (∧-trueʳ hv))

-- ONE FRAME'S SIZE STEP, AND THE FRAME IS READ AT THE PROGRAM'S CAP
-- WHILE THE VALUES ARE READ AT THE LEVEL.  That split is not a
-- convenience: it is what `sizeStep` computes.  A `map-f` emits
-- `applyFn fn v`, and `evalWith` sends `pairᵗ` to BOTH arms, so a
-- duplicator of `k` leaves takes a value of size `V` to `(k-1) + k·V`
-- -- a PRODUCT of the frame's size and the value's.  `sizeStep S L` is
-- `S·(1+2L)`, which covers `S + S·L` with room and nothing larger, so
-- the frame's factor has to be the base cap `S` for one level to pay.
--
-- WHAT DEFEATS IT IS THE RATE, AND `scanVals` FOLDS.  A `scan-f`
-- answers with its accumulator, and each output is the step function
-- applied to the PREVIOUS one, so a burst of k values applies it k
-- times in sequence and whatever the function adds accrues k times
-- while one level buys one factor.  No reading of the frame and no
-- reading of the store at a fixed level survives that.
--
-- THE REPAIR IS PROVEN ONE FACE OVER, AND IT FIXES THE COUNT EXACTLY.
-- `scanVals-size` already prices this arm in this very currency: from
-- an accumulator and arriving values both read at `B`, every output AND
-- the stored residue land at `iterSize S (length vals * suc (sizeᵗ fn))
-- B` -- a rung per pairing and per node of the step function.  So the
-- count owed is the burst's own LENGTH, and emphatically not the width
-- cap: that count is separately unavailable, since `iterFold`
-- exponentiates per fold and a count reading `cWid` would iterate the
-- tower function once per instant, which is the finding carried at
-- `sizeCount`.  A length is a structural quantity the walk already
-- sums; a cap is a recurrence, and the two are not a widening apart.
--
-- AND THAT LEMMA LOCATES WHAT IS ACTUALLY OPEN.  It asks for the
-- accumulator read at the SAME `B` as the values, and it PRESERVES that
-- reading -- the residue lands where the outputs do -- so the obstacle
-- is the walk's ENTRY reading of the store and not the step.  Which is
-- the direction finding recorded below, now with the step half of it
-- discharged one face over rather than merely conjectured.
--
-- AND THE COUNT IS NOT THE SCAN ARM'S ALONE, WHICH IS WHERE THE SPLIT
-- BY FRAME KIND STOPS PAYING.  `scan-f` is the only arm that applies
-- its function in SEQUENCE, and `map-f` applies it to each value
-- independently, which is the reading the first paragraph prices.  But
-- the two arms crossing into an inner subscription do not merely
-- concatenate what someone else computed: `thruConsume` SUBSCRIBES the
-- arriving observable and hands back its whole synchronous burst, and
-- `innerFinish` at a mergeAll drains the node's queue by subscribing
-- what is parked there.  What runs at those arms is a program that
-- arrived as a VALUE, so the frame's own syntax says nothing about
-- what it costs.  The count owed there is the arriving observables'
-- OWN size -- the same move `map-f` already made, denominated in what
-- runs rather than in what is written.
--
-- REFUTED: `Refuted.Frame-Step-Size-Store` -- the scan arm at the
--   smallest frame there is, against a store the statement quantifies
--   over and says nothing about.  The same witness dies against
--   `boundedNode` at the base cap, so the premise is named rather
--   than invented.
-- REFUTED: `Refuted.Frame-Step-Size-Level` -- both halves.  With no
--   reading of the frame at all the conclusion needs information no
--   hypothesis carries, and a three-leaf duplicator beats the level by
--   inspection.  Reading the frame at the LEVEL instead does not
--   repair it: both factors are then capped at `L`, the emission is
--   quadratic in `L` and one level is linear in it, and the crossing
--   arrives at `j = 1` for every `S ≥ 2`.
-- REFUTED: `Refuted.Frame-Step-Size-Fold` -- the store-conditioned
--   repair, at the strongest store premise there is: every node bounded
--   at the arriving values' own level.  All three premises hold and the
--   conclusion still fails, because the fold adds a fixed amount per
--   value while the ceiling is fixed in the burst.  The rows fire at a
--   `scan-f` and at no other arm.
-- REFUTED: `Refuted.Frame-Step-Size-Cross` -- the constant charge at
--   BOTH crossing arms, which is what the split by frame kind left
--   standing.  `sizeᵉ` at a map adds while `sizeᵛ` at a product
--   doubles, so a duplication chain of syntax size `3 + 4k` emits at
--   `2 ^ suc k - 1`; the outer arm dies on the arriving observable and
--   the inner arm on the same program parked in the node's queue,
--   where `boundedNode` is what supplies the premise.  The second row
--   is the one that decides the repair: the cap is tied to the
--   program's own size and the arm still fails, so no polynomial tie
--   between `S` and `B` saves a constant count.  The STORE halves are
--   untouched -- this witness leaves the queue empty and installs no
--   node -- and neither is evidence for the other.
-- DEAD ROUTE: conditioning this on a store reading at the level, and
--   threading that through the walk that spends it, is STRUCTURALLY
--   dead -- and what kills it is the DIRECTION, not the threading.  The
--   scan arm emits a stored value into a conclusion capped at the
--   values' ladder, so it needs the store's cap to sit BELOW that
--   ladder.  The only levelled store reading this development has is
--   the caps face's, whose walk advances the level by an EXISTENTIAL
--   per frame and per fanned entry, budgeted by a step count rather
--   than by one; that ladder therefore climbs at least as fast as this
--   one and strictly faster at exactly the storing frames, so the store
--   cap overtakes the value cap at a chain's second scan.  No premise
--   fixes a direction.
-- DEAD ROUTE: re-denominating the conclusion onto that existential
--   ladder instead, so that the store is carried at the level and the
--   consumer's own accounting moves with it.  The caps walk's ceiling
--   is its fold COUNT, and `iterSize` taken at that count is by
--   construction the NEXT instant's size cap; the walk that spends
--   this conclusion has to land under the CURRENT instant's nesting
--   cap, and the only lemma delivering that admits levels no larger
--   than a small polynomial in the base cap.  So the two ladders are
--   not a restatement apart -- one is elementary in the cap and the
--   other is the caps recurrence itself -- and no widening crosses
--   the gap in the direction the consumer needs.

-- WHAT ONE UNFOLDING COSTS, IN RUNGS.  A `μ` is subscribed by
-- substituting the program into itself, so its SYNTAX squares while
-- the layer count does not move at all -- and a rung is affine in the
-- bound, so a count of rungs fixed by the layers buys a fixed factor
-- and cannot cover a multiplicity.  What can cover it is a block of
-- rungs bought against the squaring, and the μ NESTING decides how
-- many such blocks there are.
--
-- AND THAT BLOCK IS DENOMINATED IN THE BOUND'S BIT LENGTH, WHICH IS
-- THE WHOLE OF WHY IT IS AFFORDABLE.  A rung MULTIPLIES, so the count
-- of them that reaches a bound is its logarithm: `bitsᴺ B` of them
-- already carry `B` past `B * B`.  Each level of nesting adds one such
-- block read at the bound reached so far, which is what lets every
-- statement below stay at the caller's own `B` rather than quantify a
-- bound its consumers would then have to join over.
--
-- WHAT A SQUARING BLOCK DOES NOT BUY IS THE DELIVERIES, AND THAT IS
-- THE SECOND BLOCK.  A subscription runs its synchronous sources
-- inside its own frame, and a scanning step may plant its accumulator
-- at as many occurrences as the step spells -- so the cell multiplies
-- once per value delivered, by a factor the SYNTAX buys and no depth
-- reading sees.  A program of size `B` spends it on a fan of `m` and a
-- burst of `a` with `m + a ≤ B`, reaching `m ^ a`; a rung multiplies
-- by at least four, so `bitsᴺ B` rungs cover one such factor and
-- `B * bitsᴺ B` of them cover every delivery the syntax can pay for.
--
-- AND IT IS CHARGED AT EVERY LEVEL RATHER THAN ONCE AT THE TOP,
-- because an unfolding is descended into at the SQUARED bound and
-- writes its own sources there.  Charging inside the recursion is also
-- what keeps the `μ` arm a transport: the leading rungs pay the
-- squaring, this level's delivery block is slack the arm drops, and
-- what remains is the same charge read at `B * B`.
-- DEAD ROUTE: paying the deliveries as a FLAT summand beside the
--   telescope -- `+ B`, or any `f B` however large.  The `μ` arm hands
--   the recursion `B * B`, so the premise it must supply names
--   `f (B * B)` while the one it holds names `f B`, and those run the
--   wrong way for every non-constant `f`.  The same arm kills a
--   premise relating the two parameters, `B ≤ S`, since `S` is passed
--   through the unfolding unchanged while `B` squares.
-- DEAD ROUTE: sizing the block at `B` rather than at `B * bitsᴺ B`,
--   on arithmetic rather than on shape.  One iteration multiplies by
--   `2 * S`, which the premises floor at four, so `B` of them buy
--   `4 ^ B` against a cell the syntax drives to `m ^ a` at
--   `m + a ≤ B` -- which maximises near `(B / 2) ^ (B / 2)` and
--   overtakes `4 ^ B` once `B` passes thirty-odd.  Not refutable by
--   instantiation: the crossing first needs a stored value of some
--   `10 ^ 26` nodes, so the block is sized by this arithmetic and
--   never by a row.
-- DEAD ROUTE: instantiating anything that reads this count at a
--   NESTING of two or more, which is the price the second block
--   charges and it is paid in coverage.  The count itself computes in
--   seconds at any nesting -- some three and a half million rungs at
--   two levels of a twenty-node program -- but a row must compare
--   against the `iterSize` tower that many rungs index, and a rung
--   MULTIPLIES, so the tower is millions of digits reached one
--   multiplication at a time.  Measured as not finishing in five
--   hundred seconds at ONE level of a program of a hundred and forty.
--   Nor does a smaller program recover it, since separating this
--   count from a blinded one needs a multiplicity large enough to
--   outrun the blinded reading, and every reading of this shape now
--   carries a delivery group that clears what a small program builds.
--   One level at a twenty-node program is what remains reachable, and
--   it is where the crossing against the layer-only denomination
--   lives.
descRungsᴺ : ℕ → ℕ → ℕ
descRungsᴺ zero    B = B * bitsᴺ B
descRungsᴺ (suc d) B = bitsᴺ B + B * bitsᴺ B + descRungsᴺ d (B * B)

-- WHAT A DESCENT IS CHARGED, WHICH IS THE RUNGS PLUS THE OPERATORS.
-- Those are the two things a subscription spends: one rung per
-- operator it runs, and one rung block per level of `μ` it has to
-- unfold on the way -- carrying, at every level including the
-- outermost, what that level's own deliveries cost.  So a program
-- carrying no `μ` still charges a block, and only the OPERATOR half is
-- read off the layers.
descChg : ∀ {n} {Γ : Ctx n} (t : Ty) → ℕ → Val Γ t → ℕ
descChg t B v = descRungsᴺ (muDepthᵛ t v) B + layᵛ t v

-- AND A BURST JOINS BY MAX FOR THE REASON A PAIR DOES.  A frame handed
-- several observables subscribes each of them, and what each one emits
-- is a run of that arrival alone -- so a conclusion stated PER
-- DELIVERED VALUE is bounded by the costliest arrival and not by their
-- sum.  The join is over the WHOLE charge rather than over its two
-- summands separately, since an arrival's unfoldings and its operators
-- are spent by one and the same run.  What the arrivals do share is
-- the sink node they drain into, and its table is read entry by entry,
-- so that half joins the same way.
descChgˢ : ∀ {n} {Γ : Ctx n} (t : Ty) → ℕ → List (Val Γ t) → ℕ
descChgˢ t B []       = 0
descChgˢ t B (v ∷ vs) = descChg t B v ⊔ descChgˢ t B vs

-- WHAT A NODE HAS PARKED, AT THE SAME CHARGE.  Only a merge queues: a
-- switch holds at most the node id of the inner it is currently
-- running, an exhaust holds two bits, and the two leaf states hold
-- values the drain never subscribes.  So every other shape parks
-- nothing, and that is a fact about the node table rather than a
-- default.
parkedChg : ∀ {n} {Γ : Ctx n} → ℕ → NodeState Γ → ℕ
parkedChg B (scan-st _)               = 0
parkedChg B (take-st _)               = 0
parkedChg B (mergeAll-st {t} _ _ q _) = descChgˢ (obs t) B q
parkedChg B (switch-st _ _)           = 0
parkedChg B (exhaust-st _ _)          = 0

-- SPELLED AS ITS OWN RECURSION RATHER THAN THROUGH `lookupNode`,
-- because this count stands inside a TYPE and a `with` over a `Maybe`
-- reduces for nobody.  A node the table does not hold parks nothing.
parkedChgAt : ∀ {n} {Γ : Ctx n} → ℕ → NodeId →
  List (NodeId × NodeState Γ) → ℕ
parkedChgAt B nid []            = 0
parkedChgAt B nid ((k , s) ∷ r) =
  if k ≡ᵇ nid then parkedChg B s else parkedChgAt B nid r

-- WHAT A LOOKUP HANDS BACK when every stored node is bounded.  The
-- receipt has to be abstracted by the SAME `with` that abstracts the
-- evaluator's own dispatch, or the two are about different scrutinees;
-- that is why it is a predicate over the `Maybe` rather than an
-- equation.  The caps face pairs this with a width reading, which is
-- the half nothing here can supply.
NodeSz : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeSz B nothing   = ⊤
NodeSz B (just ns) = boundedNode B ns ≡ true

lookupNode-sz : ∀ {n} {Γ : Ctx n} (B : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) nodes ≡ true →
  NodeSz B (lookupNode nid nodes)
lookupNode-sz B nid []            h = tt
lookupNode-sz B nid ((k , s) ∷ r) h with k ≡ᵇ nid
... | true  = ∧-trueˡ h
... | false = lookupNode-sz B nid r (∧-trueʳ h)

-- WHAT THE COUNT READS AT A LOOKUP, abstracted by the same `with` that
-- abstracts the evaluator's dispatch for the reason the store reading
-- beside it is: the count spells its own recursion, so a clause that
-- has scrutinised the table still has to be told the two walks agreed.
-- A cell the table does not hold parks nothing, which is the `nothing`
-- arm rather than an omission.
NodeChg : ∀ {n} {Γ : Ctx n} → ℕ → ℕ → Maybe (NodeState Γ) → Set
NodeChg B L nothing   = L ≡ 0
NodeChg B L (just ns) = L ≡ parkedChg B ns

parkedChgAt-lookup : ∀ {n} {Γ : Ctx n} (B : ℕ) (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  NodeChg B (parkedChgAt B nid nodes) (lookupNode nid nodes)
parkedChgAt-lookup B nid []            = refl
parkedChgAt-lookup B nid ((k , s) ∷ r) with k ≡ᵇ nid
... | true  = refl
... | false = parkedChgAt-lookup B nid r

-- WHAT ONE SUBSCRIPTION DELIVERS, WHICH IS WHAT BOTH CROSSING ARMS
-- BOTTOM OUT IN.  A frame that runs an observable -- the drain
-- entering its node's queue, the outer arm entering an arrival --
-- reaches a descent and nothing else, so this is the single claim
-- underneath both: running a program of size at most `B` delivers
-- within the rungs its own LAYERS and the telescope buy.
--
-- AND IT READS NO TABLE, WHICH IS THE PART THAT IS LOAD-BEARING RATHER
-- THAN TIDY.  What a subscription emits is a function of the program's
-- own syntax and of the slot definitions standing behind whatever it
-- names; the nodes already installed are other subscriptions' state,
-- and the burst returned here is at the SOURCE's type, before the path
-- carries anything through them.  A statement conditioned on the table
-- instead would have to be re-established after every entry of a fold,
-- and a fold's rungs then COMPOSE BY ADDITION -- which is exactly the
-- max the drain above needs and cannot then have.
--
-- AND THE TWO HALVES SHARE A SUBJECT AND A CHARGE, NOT A STATEMENT.
-- With both doors bodied, this and its store sibling stand at the SAME
-- descent, at the same arguments, under the same
-- `iterSize S (layᵉ o + slotsSize sl) B` -- so the currency a per-frame
-- ceiling has to supply is asked for once rather than twice.  What does
-- not join is the shape: the store half reads a TABLE it did not build,
-- so it carries a level the premise already reaches and a boundedness
-- hypothesis on the entering nodes, while what a run DELIVERS is a
-- function of the program alone and needs neither.  One ceiling
-- therefore serves both, and the table premise stays the store side's
-- own to re-establish.
--
-- REFUTED: `Refuted.Frame-Step-Size-Slot.stepFrame-sz-outer-own-absurd`
--   -- the telescope-free reading of what a run delivers, at the sister
--   arm, whose charge is this one read at an arrival rather than at a
--   parked entry.
--
-- PROBED: `Probed.Drain-Count-Slot` at the shape the summand exists
--   for -- a bare slot reference, whose layers are zero and whose whole
--   charge is the telescope -- at two depths behind the reference, the
--   refutation's own program and state.  Each depth reports `false` at
--   the telescope-free rung and `true` at the repaired one, and the
--   charge moves with the slot, fifty-one to fifty-five, while the
--   emission doubles: the axis is measure-side and the rows could have
--   failed on it.  What that buys is that the telescope is LEGIBLE from
--   the schedule a subscription is handed, not that the summand's size
--   is right -- this family spends four units of slot syntax per
--   doubling and a rung admits size geometrically, so the summand
--   dominates once it is in the charge at all.
--
-- PROBED: `Probed.Cross-Count-Store` at the complementary shape, a
--   twelve-rung duplication chain written out, where the layers are the
--   charge and the telescope is the rounding: `false` against the
--   constant the crossing used to carry, `true` against thirteen.
--   Neither probe reaches a `scripted` slot whose definition a
--   subscription does not run, an operator other than `mergeAllᵒ` at
--   the path's inner end, or a program family whose emission outruns
--   four units of slot syntax per doubling.
--
-- PROBED: `Probed.Slot-Telescope-Sum` at a telescope of ELEVEN shared
--   slots, each naming the one below and doubling it, entered at the
--   top reference so one subscription runs the whole chain.  This is
--   what decides the JOIN rather than the summand's reach: a max over
--   the telescope is FALSE here, prices one rung of a chain of ten, and
--   fails the conclusion at seventeen hundred against a delivered two
--   thousand, where the stated sum holds.  No row can fail on the
--   sum's other side -- it charges slots the run never names.
--
-- PROBED: `Probed.Slot-Named-Twice` at the join a chain cannot reach: a
--   DIAMOND, whose apex names ONE eight-rung shared slot twice, so the
--   sum charges once what two references reach.  It costs nothing on
--   either axis.  Not the size -- the single value delivered is the
--   size one reference delivers, so what is entered is the binding and
--   not the definition.  And not the length -- the share connects on
--   the first reference and has already fired when the second
--   registers, against a control with the same rungs written inline at
--   both arms, which delivers twice.  One diamond over one shared slot
--   at one door.
--
-- PROBED: `Probed.Slot-Two-Depths` at the shape the diamond is not: a
--   LATTICE, where two DIFFERENT slots each name a third and the apex
--   names those two, so the share is reached through each arm's own
--   definition and the arms meet it three layers apart.  Depth buys
--   the second arm nothing -- the share connects on whichever arm the
--   walk reaches first and has already fired when the other registers,
--   against a control with the same rungs inline in both arms, which
--   delivers twice -- so the sum is not short there either.  Two arms
--   over one share, every slot `shared`, and no arm reaching the share
--   twice itself.
--
-- PROBED: `Probed.Subscribe-Inner-Doors` at the two doors every other
--   row subscribed past, each entered where its rule bites -- a switch
--   holding an inner it must cut, an exhaust already busy -- and both
--   deliver the merge door's burst UNCHANGED, which the two equalities
--   pin.  The door is invisible HERE by construction: an operator
--   enters only by being built into the path, and a subscription does
--   not push its own burst through that frame, so the cut and the drop
--   act on later emits, which is the drain's statement.  Each door is
--   read at the telescope-free rung and the repaired one, `false` then
--   `true`, at one arrival shape with zero layers of its own.

-- AND THE CHARGE CARRIES THE UNFOLDINGS, WHICH IS THE EDGE ITS STORE
-- SIBLING FAILS AT TOO -- one repair rather than the store side's own.
-- A `μ` is subscribed by UNFOLDING, and unfolding plants a copy of the
-- whole program at every mention of the recursive occurrence; the layer
-- count charges nothing for the `μ` and nothing under the `defer` those
-- mentions must stand under, so a rung count fixed by the layers is
-- fixed before the multiplicity is chosen -- and a rung is affine in
-- the bound, so a fixed count buys a fixed factor.  No table is
-- carrying that here: there is no door, no queue and no cell, only what
-- one subscription hands back, which is why the block `descRungsᴺ` adds
-- per level of nesting is the whole of the difference.
-- REFUTED: `Refuted.Subscribe-Sz-Mu` -- the layer-only denomination
--   this charge replaces, at a one-shot source whose single emission is
--   the deferred subtree the copies sit in, entered at `root` on the
--   initial table with the crossing bracketed on both sides at the same
--   rungs.
-- PROBED: `Probed.Subscribe-Mu-Blocks` at the region every other row
--   over this statement declined -- the refutation's own family at four
--   mentions, ONE level of nesting, read at the smallest bound the
--   premise admits, since a larger one is a weaker reading.  The layer
--   count is nought there, so the layer-only level fails where the
--   charge clears it: the block is what buys the multiplicity, and the
--   crossing the refutation sits on is closed by the denomination and
--   not by the program being small.  What the row does not buy is the
--   rate at EVERY bound, which is asymptotic and which no instantiation
--   decides; the mentions are four, the telescope is one scripted slot,
--   and nothing is read past a `root` entry, so no door stands in the
--   way.  Nesting past one level is not merely unreached but
--   unreachable, for the reason `descRungsᴺ`'s own header records.
postulate
  subscribeE-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (o : Closed Γ u) (κ : Path Γ u t) (id : Id)
    (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
    valsSz? (iterSize S (descChg (obs u) B o + slotsSize (Sched.slots sched)) B)
      (proj₁ (splitBurst {A = Val Γ t}
        (proj₁ (subscribeE g o κ id now sched st))))
      ≡ true

-- ONE ARRIVAL SUBSCRIBED, READ AT WHAT IT HANDS BACK.  The door mints
-- the inner's exit-frame instance and then does exactly one thing with
-- it, and gas alone decides which: with none the arrival is answered
-- by a dry close, which carries no value at all, so the delivered list
-- is EMPTY and the bound holds on nothing; with some it is the general
-- descent entered at the caller's path under a `from-inner`
-- decoration, and what this splits is the very burst that returns.
--
-- SO NEITHER SIDE MOVES AT THE DOOR.  The charge reads the program and
-- not the path it is subscribed at, the record update touches no slot,
-- and the split is a projection rather than a step -- which is what
-- lets it cross verbatim rather than climbing a rung here.
subscribeInner-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id)
  (now : Tick) (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
  valsSz? (iterSize S (descChg (obs u) B o + slotsSize (Sched.slots sched)) B)
    (proj₁ (proj₂ (subscribeInner sf op allNid κ id now o sched st)))
    ≡ true
subscribeInner-sz g0 op allNid κ id now o sched st S B 2≤S hb = refl
subscribeInner-sz (gs fuel) op allNid κ id now o sched st S B 2≤S hb =
  subscribeE-sz fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ)
    id now (record sched { nextNode = suc (Sched.nextNode sched) }) st
    S B 2≤S hb

-- THE TELESCOPE A SUBSCRIPTION HANDS ON IS THE ONE IT WAS HANDED,
-- which is what lets a charge keyed on the slots survive a fold: the
-- schedule's only edit here is the instance counter.
subscribeInner-slots : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id)
  (now : Tick) (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e) →
  Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
    (subscribeInner sf op allNid κ id now o sched st))))))
    ≡ Sched.slots sched
subscribeInner-slots g0 op allNid κ id now o sched st = refl
subscribeInner-slots (gs fuel) op allNid κ id now o sched st =
  subscribeE-slots fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ)
    id now (record sched { nextNode = suc (Sched.nextNode sched) }) st

-- WHAT A RUN DELIVERS, WHICH IS THE ONE THING THE INNER ARM CANNOT
-- READ OFF ITS ARGUMENTS.  The drain subscribes the programs its node
-- has parked, so what comes back is bounded by what RUNNING them
-- emits -- and the charge is the queue's LAYERS, joined by max because
-- each entry is subscribed separately and every delivered value comes
-- out of one entry's run.  That join is what the fold below buys: the
-- head is the leaf read at its own layer count and the tail is this
-- walk at the schedule the head handed on, and each widens onto the
-- max.
--
-- AND THE TELESCOPE IS A SUMMAND BECAUSE THE PARKED SYNTAX IS NOT THE
-- PROGRAM.  A queue entry may NAME a shared slot, and then its layers
-- and its size both read the reference while the run reads the
-- definition; no premise over the queue or the table can see the
-- difference, so the only reading of "what this drain runs" available
-- to the statement is the queue's own depth plus the whole telescope
-- standing behind whatever it names.  That is the same summand the
-- outer arm carries, arrived at from the store side rather than the
-- arrival side, which is why the two arms of the count now agree in
-- shape.
--
-- AND THE NODE TABLE IS NOT A PREMISE HERE, WHICH IS WHAT MAKES THE
-- FOLD GO THROUGH.  Every entry is subscribed at the state its
-- predecessor left, so a premise about the table would have to be
-- re-established per entry at a rung the predecessor climbed, and the
-- conclusion would then be a rung per entry rather than the max.  What
-- survives that threading is exactly what does not mention the state:
-- the queue's syntax, which no entry edits, and the telescope, which
-- the subscription hands on unchanged.
--
-- REFUTED: `Refuted.Drain-Queue-Slot` -- the telescope-free reading, at
--   a queue parking one slot reference, twice with the bound tied to
--   the slot's own definition.
mergeAllDrain-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ o → sizeᵉ o ≤ᵇ B) q ≡ true →
  valsSz? (iterSize S (descChgˢ (obs s) B q + slotsSize (Sched.slots sched)) B)
    (proj₁ (mergeAllDrain sf allNid κ id now lim act q sched st)) ≡ true
mergeAllDrain-sz sf allNid κ id now lim act [] sched st S B 2≤S hq = refl
mergeAllDrain-sz {s = s} sf allNid κ id now lim act (o ∷ q) sched st S B 2≤S hq
  with hasRoom lim act
... | false = refl
... | true =
  all-++-intro
    (λ v → sizeᵛ s v ≤ᵇ iterSize S (descChgˢ (obs s) B (o ∷ q)
                                     + slotsSize (Sched.slots sched)) B)
    vs vs′ headFits tailFits
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  sl = Sched.slots sched

  r₁ = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  vs = proj₁ (proj₂ r₁)
  done = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

  vs′ = proj₁ (mergeAllDrain sf allNid κ id now lim
                 (if done then act else suc act) q sched₁ st₁)

  headFits : valsSz? (iterSize S (descChgˢ (obs s) B (o ∷ q) + slotsSize sl) B)
               vs ≡ true
  headFits =
    valsSz?-mono (iterSize S (descChg (obs s) B o + slotsSize sl) B)
      (iterSize S (descChgˢ (obs s) B (o ∷ q) + slotsSize sl) B) vs
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl)
          (m≤m⊔n (descChg (obs s) B o) (descChgˢ (obs s) B q))))
      (subscribeInner-sz sf mergeAllᵒ allNid κ id now o sched st S B 2≤S
        (∧-trueˡ hq))

  tailAtSched : valsSz? (iterSize S (descChgˢ (obs s) B q + slotsSize sl) B)
                  vs′ ≡ true
  tailAtSched =
    subst (λ z → valsSz? (iterSize S (descChgˢ (obs s) B q + slotsSize z) B)
                   vs′ ≡ true)
          (subscribeInner-slots sf mergeAllᵒ allNid κ id now o sched st)
          (mergeAllDrain-sz sf allNid κ id now lim
             (if done then act else suc act) q sched₁ st₁ S B 2≤S
             (∧-trueʳ hq))

  tailFits : valsSz? (iterSize S (descChgˢ (obs s) B (o ∷ q) + slotsSize sl) B)
               vs′ ≡ true
  tailFits =
    valsSz?-mono (iterSize S (descChgˢ (obs s) B q + slotsSize sl) B)
      (iterSize S (descChgˢ (obs s) B (o ∷ q) + slotsSize sl) B) vs′
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl)
          (m≤n⊔m (descChg (obs s) B o) (descChgˢ (obs s) B q))))
      tailAtSched

-- THE TWO FRAME KINDS THE READING CANNOT SEE.  A map hands its values
-- on and touches no cell at all; a take rewrites its own counter, and a
-- counter is not among the quantities the bound prices.  So both cross
-- a store bound VERBATIM where the general step widens by a rung -- and
-- the difference is load-bearing exactly where the widening is
-- unaffordable, at a subscription's own burst, whose level is fixed by
-- the program's layers before the burst is walked.
flatFrame? : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Bool
flatFrame? (map-f _)  = true
flatFrame? (take-f _) = true
flatFrame? _          = false

-- ONE FLAT FRAME AT A FIXED BOUND.  The map arm hands the table back
-- untouched, and every take arm writes a counter the reading admits at
-- any bound whatever -- the cut's included, which moves the registry
-- and the schedule and no cell but that one.
stepFrame-sz-store-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (M : ℕ) →
  flatFrame? f ≡ true →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f κ vals fin sched st))))))
    ≡ true
stepFrame-sz-store-flat sf id now (map-f fn) κ vals fin sched st M hf h = h
stepFrame-sz-store-flat sf id now (take-f nid) κ vals fin sched st M hf h
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = h
... | just (scan-st _)           = h
... | just (mergeAll-st _ _ _ _) = h
... | just (switch-st _ _)       = h
... | just (exhaust-st _ _)      = h
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | true  = setNode-bounded M nid (take-st 0) (EvalSt.nodes st) refl h
...   | false = setNode-bounded M nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                  (EvalSt.nodes st) refl h
stepFrame-sz-store-flat sf id now (scan-f _ _)      κ vals fin sched st M () h
stepFrame-sz-store-flat sf id now (from-inner _ _ _) κ vals fin sched st M () h
stepFrame-sz-store-flat sf id now (thru-outer _ _)  κ vals fin sched st M () h

-- A WHOLE BURST THROUGH ONE FLAT FRAME, which is the induction the
-- fixed bound survives: every emit is stepped at the bound the emit
-- before it left, and a frame that never raises it leaves the fold
-- where it started.
pushBurst-sz-store-flat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ u t)
  (bs : Stream Γ s) (sched : Sched Γ) (st : EvalSt e) (M : ℕ) →
  flatFrame? f ≡ true →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (pushBurst sf id now f κ bs sched st))))
    ≡ true
pushBurst-sz-store-flat sf id now f κ []         sched st M hf h = h
pushBurst-sz-store-flat sf id now f κ (em ∷ ems) sched st M hf h =
  pushBurst-sz-store-flat sf id now f κ ems
    (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r)))) M hf
    (stepFrame-sz-store-flat sf id now f κ
      (proj₁ (splitEvents (InstEmit.events em)))
      (proj₂ (proj₂ (splitEvents (InstEmit.events em))))
      sched st M hf h)
  where
  r = stepFrame sf id now f κ (proj₁ (splitEvents (InstEmit.events em)))
        (proj₂ (proj₂ (splitEvents (InstEmit.events em)))) sched st

postulate
  -- A SHARED SLOT'S DEFINITION, WHICH THE REFERENCE ITSELF DOES NOT
  -- PRICE.  `input` charges no layers whatever, so nothing in the
  -- program term bounds what the slot holds and the entire climb a
  -- connect may spend is bought by the TELESCOPE summand -- which is
  -- why the premise here carries no program reading beside it.  That is
  -- the statement's content and not a gap in it: the definition behind
  -- the reference is counted once, where the telescope counts it, and a
  -- reading keyed on the reference would be reading nought.
  --
  -- AND THREE OF THE FOUR DOORS WRITE NOTHING.  A join at a live share
  -- registers, a spent one answers out of the completed list, and only
  -- the FIRST arrival walks the definition -- so what the leaf owes is
  -- that one walk, at a level the telescope has already paid for.
  -- DEAD ROUTE: the SUBSTITUTING telescope -- each hop a duplication
  --   applied to the slot beneath it, which is the shape `Rx.Clos-Size`
  --   exists because it broke the value face's key -- cannot cross this
  --   statement, and the obstruction is arithmetic rather than a matter
  --   of reaching far enough.  The premise iterates `sizeStep S` once
  --   per UNIT of the summand, and at the smallest `S` admitted one
  --   iteration already multiplies by four, where a substituting hop
  --   multiplies the emission by two and cannot be written for less than
  --   a unit of slot syntax.  So the axis moves the BOUND faster than
  --   the store however far the telescope is walked, and no
  --   instantiation of it is a counterexample.
  -- PROBED: `Probed.Parked-Slot-Store` at the program whose OWN layers
  --   are nought -- a bare reference to a shared slot -- so the whole
  --   climb rests on the telescope.  Read at two depths behind the same
  --   reference, since one more rung doubles the emission while moving
  --   the charge by four units of slot syntax; the telescope-free
  --   reading fails at both.  So the summand REACHES the written table,
  --   never that its size is right: one slot, one queue entry, and the
  --   merging door alone.
  -- PROBED: `Probed.Slot-Cascade-Store` at a STRATIFIED telescope, where
  --   the connect re-enters this door on the definition it resolves and
  --   one subscription walks a chain of slots the call never names.
  --   Every upper slot is a bare reference, so the subscribed slot's own
  --   reading is one unit of syntax while the slot the cascade lands on
  --   holds the emission.  Read at one hop and at two: the stated sum
  --   holds, and the charge over the named slot, the charge over the
  --   named slot plus the one passed through, and the telescope-free
  --   charge all fail.  So the summand is owed the connect's TRANSITIVE
  --   reach and not the reference's entry -- which is a claim about the
  --   slots it ranges over.  Whether it is a sum or a maximum is not
  --   reachable: the charge is geometric in the summand, so the largest
  --   slot alone clears the table by a margin that would need a stored
  --   value of half a million units to cross.
  subscribeSharedSlot-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sl : Slots Γ) (g : Gas) (i : Fin n) (d : Closed Γ (lookup Γ i))
    (κ : Path Γ (lookup Γ i) t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
    Sched.slots sched ≡ sl →
    iterSize S (slotsSize sl) B ≤ M →
    all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    (1 ≤ᵇ B) ≡ true →
    all (λ kv → boundedNode M (proj₂ kv))
        (EvalSt.nodes
          (proj₂ (proj₂ (subscribeSharedSlot g i d κ id now sched st))))
      ≡ true

  -- THE SEED AND THE CELL A SCAN WRITES, the one arm whose own charge
  -- is not the descent's.  The node is minted before the source is
  -- subscribed and its cell holds the REIFIED seed, so what has to fit
  -- is a term's evaluation rather than a program's layers -- and the
  -- two are denominated differently: the proven bound on an evaluated
  -- term is a rung count in that term's SYNTAX, where the premise buys
  -- one rung for the whole operator.  The burst then rewrites the same
  -- cell once per arriving value at the step function's own draw, which
  -- is a second charge in the same currency.
  --
  -- SO THE ARM IS A LEAF FOR AN ARITHMETIC REASON AND NOT A STRUCTURAL
  -- ONE.  The recursion into the source is available and every one of
  -- its premises transports; what does not transport is the cell.
  -- AND THE ARRIVALS ARE WHY THE CHARGE CARRIES A DELIVERY BLOCK AND
  -- NOT TWO DEPTH COUNTS.  A synchronous source buys arrivals without
  -- buying depth, so a reading denominated in unfoldings and layers
  -- holds its exponent FIXED across a crossing whose stored cell a
  -- wrapping step doubles per arrival -- affine against geometric.
  -- What answers it is a count that grows with the SIZE bound, which
  -- is what a delivery block is; no hypothesis available here is a
  -- substitute, since the arrivals are the source's own text.
  -- REFUTED: `Refuted.Subscribe-Store-Scan-Arrivals` -- the DEPTH-ONLY
  --   denomination this premise replaces, spelled out locally there so
  --   the witness survives the live charge moving.  A scan whose step
  --   rebuilds its accumulator at two occurrences, over a synchronous
  --   run, entered at `root` on the initial table with the least `M`
  --   that reading admits.  The crossing is bracketed: three arrivals
  --   fewer and the claim HOLDS at the very same program shape, so what
  --   failed was the arrival count and not the gas, the telescope, or
  --   the arithmetic of `iterSize`.  The same witness carries up to
  --   `subscribeE-sz-store`, whose bound was spelled in that same
  --   currency -- so what it killed was the charge and not this arm.
  -- DEAD ROUTE: the SUBSTITUTING telescope is bound-side HERE TOO, and
  --   for the same arithmetic the sibling slot statement records: this
  --   premise iterates `sizeStep S` once per unit of `descChg` plus the
  --   summand alike, so a hop that doubles what a layer delivers buys
  --   the bound at least four times what it buys the cell.  So no
  --   instantiation of that axis is a counterexample, however far the
  --   telescope is walked.
  -- PROBED: `Probed.Cross-Count-Outer-Store` at the very state that
  --   killed the constant, a scan whose step stores the arriving datum
  --   back as a one-shot observable, subscribed at all three doors.
  --   One installed node per witness, so nothing about a table whose
  --   entries accumulate across frames.
  -- PROBED: `Probed.Parked-Queue-Store` at a node that already holds a
  --   parked queue when the program is subscribed: admitting one
  --   beside a queue of two leaves the reading where an empty queue
  --   leaves it, since what is read is the program's own run.  One
  --   queue depth and the merging door alone, which is the only shape
  --   that parks at all.
  -- PROBED: `Probed.Cell-Chain-Store` at a table whose cells were
  --   written in SERIES, which every row above declines: a reifying
  --   scan under a `mergeAll` under a second reifying scan, arriving
  --   as ONE value, so the subscription writes three cells where the
  --   control writes one.  Both tables are read at the same two rungs
  --   and need the same one: a cell holding what the cell below it
  --   emitted is priced by the emission and not by its position, so
  --   the series does not compound and counting the layers once is not
  --   short.  One chain, of one length, with the telescope a single
  --   scripted slot -- so nothing about a chain whose cells resolve a
  --   SLOT, where the summand would do the work.
  -- PROBED: `Probed.Slot-Cascade-Store` at exactly that shape, a scan
  --   whose source is a bare reference to a SHARED slot, so subscribing
  --   the cell connects the definition behind it.  The term's own
  --   descent charge is ONE there -- which is the whole of what reading
  --   the program buys when the reference charges nought -- and the
  --   summand carries the climb: the stated charge holds and the
  --   telescope-free one fails.  One slot, one connect, no queue.
  subscribeE-sz-store-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u s}
    (sl : Slots Γ) (g : Gas) (f : Fn Γ [] [] [] (u ×ᵗ s) u)
    (z : Tm Γ [] [] [] u) (b : Closed Γ s) (κ : Path Γ u t)
    (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
    Sched.slots sched ≡ sl →
    iterSize S (descChg (obs u) B (scanᵉ f z b) + slotsSize sl) B ≤ M →
    all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    (sizeᵉ (scanᵉ f z b) ≤ᵇ B) ≡ true →
    all (λ kv → boundedNode M (proj₂ kv))
        (EvalSt.nodes
          (proj₂ (proj₂ (subscribeE g (scanᵉ f z b) κ id now sched st))))
      ≡ true

  -- THE BURST A CROSSING DOOR PUSHES BACK THROUGH ITSELF, which is all
  -- that is left of the door once the subscription underneath it is a
  -- checked recursion.  The mint, the initial cell and the descent into
  -- the source belong to the caller now; what stays here is the fold
  -- that hands the source's own synchronous emission to the frame the
  -- door has just built above it.
  --
  -- AND IT IS KEYED ON THE SOURCE PROGRAM RATHER THAN ON THE BURST,
  -- deliberately.  An arbitrary burst at this type is unbounded and a
  -- statement over one would be false, so what makes the fold
  -- affordable is that these emits are what subscribing `b` produced --
  -- which is why the equation naming that subscription is a premise
  -- rather than a convenience, and why the table the fold enters at is
  -- the one that subscription left.
  --
  -- WHAT IT OWES, AND WHERE THE ROUTE AND THE STATEMENT COME APART.  A
  -- `thru-outer` frame SUBSCRIBES what it is handed, so each emit
  -- re-enters the descent at the ARRIVING VALUE's own charge, and the
  -- obvious route spends the delivered bound on that arrival and then
  -- climbs again for what re-subscribing it writes -- asking for the
  -- arrival's charge and the telescope a SECOND time, which the door's
  -- single rung does not carry and which no caller could supply either,
  -- since a crossing arm holds exactly the ceiling its parent was
  -- handed.  What keeps the statement from being short in that
  -- direction is that a rung at least quadruples where a layer of
  -- payload at most doubles, and an arrival's charge IS bounded by the
  -- charge of the program that wrote it -- unfoldings included, which
  -- is what the block per level of nesting buys.
  -- REFUTED: `Refuted.Burst-Mu-Square` -- the layer-only denomination
  --   this premise replaces, where the copies an unfolding plants are a
  --   free parameter of the program and no count of rungs fixed by the
  --   layers moves with them.
  -- DEAD ROUTE: reading this leaf's block by INSTANTIATION at all, at
  --   the `μ` a source hands OUT rather than runs and at one handed out
  --   from INSIDE another.  Both families were built and both are now
  --   beyond reach, for two reasons that close from opposite sides.  A
  --   block is geometric in the bound, so at a program of some hundred
  --   and fifty nodes it names hundreds of thousands of rungs, and the
  --   `iterSize` tower a row compares against is reached one
  --   multiplication at a time -- measured as not finishing in five
  --   hundred seconds at one nesting level.  Shrinking the program does
  --   not recover it: separating a block from no block needs a
  --   multiplicity large enough to outrun the blinded reading, and that
  --   reading now carries a delivery group of its own which clears
  --   every table a small program can build.  So the block's RATE is
  --   settled by the arithmetic written into `descRungsᴺ`'s header and
  --   never by a row at this leaf.
  -- PROBED: `Probed.Cross-Burst-Slack` at a merging door over a
  --   reifying scan fed a duplication chain, whose emission is
  --   exponential in the layers the scan is charged for and whose
  --   re-subscription PARKS that payload in a cell of its own -- so the
  --   fold writes rather than merely bookkeeping.  Read at the tightest
  --   `S` the statement admits, at two chain lengths and down all three
  --   doors: the fold's table clears at exactly the rung the
  --   subscription's table needs, and four further layers move that
  --   need by two rungs -- read as a CLIMB in rungs from the program's
  --   own size, so what the rows settle is that no second block is
  --   owed, whatever the charge that buys the first is spelled as.
  --   Nothing about a `μ` under the door, and nothing about an emission
  --   the TELESCOPE manufactures, where the layer count is 0 and the
  --   rungs are bought by `slotsSize` alone.
  -- RECOVERY: `git show 248bbf8` restores the two harnesses, in
  --   `Probed/Burst-Mu-Door.agda` and `Probed/Mu-Compose.agda` -- the
  --   μ-under-a-door family, the composed nesting threaded through the
  --   EMISSION position, and the liveness rows that say the fold writes
  --   rather than merely bookkeeping.
  pushBurst-sz-store-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (g : Gas) (op : AllOp) (nid : NodeId)
    (b : Closed Γ (obs u)) (κ : Path Γ u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e)
    (r : Stream Γ (obs u) × Sched Γ × EvalSt e) (S B M : ℕ) → 2 ≤ S →
    Sched.slots sched ≡ sl →
    r ≡ subscribeE g b (thru-outer op nid ↠ κ) id now sched st →
    iterSize S (descRungsᴺ (muDepthᵉ b) B + suc (layᵉ b) + slotsSize sl) B ≤ M →
    all (λ kv → boundedNode M (proj₂ kv))
        (EvalSt.nodes (proj₂ (proj₂ r))) ≡ true →
    (sizeᵉ b ≤ᵇ B) ≡ true →
    all (λ kv → boundedNode M (proj₂ kv))
        (EvalSt.nodes
          (proj₂ (proj₂
            (pushBurst g id now (thru-outer op nid) κ
              (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))))))
      ≡ true


-- THE SIZE PREMISE THROUGH ONE CONSTRUCTOR, which every arm needs and
-- none needs differently: a subterm is smaller, so the bound the caller
-- supplied for the whole program already pays for it.
sz-sub : ∀ (a o B : ℕ) → a ≤ o → (o ≤ᵇ B) ≡ true → (a ≤ᵇ B) ≡ true
sz-sub a o B h hb = ≤ᵇ-true a B (≤-trans h (≤ᵇ⇒≤ o B (T-to hb)))

-- AND THE LEVEL PREMISE THE SAME WAY.  A rung is monotone in the count
-- it is taken at, so a subterm charging fewer layers than its parent
-- meets whatever ceiling the parent met -- at the SAME rung, which is
-- the whole point: the descent may not climb one per operator.
lay-sub : ∀ (S B M j j′ : ℕ) → 2 ≤ S → j ≤ j′ →
  iterSize S j′ B ≤ M → iterSize S j B ≤ M
lay-sub S B M j j′ 2≤S h le =
  ≤-trans (iterSize-mono-count S B (≤-trans (s≤s z≤n) 2≤S) h) le

-- AND THE OPERATOR HALF OF THE CHARGE MOVES ALONE, which is what keeps
-- every non-`μ` arm a transport rather than a restatement: a
-- constructor other than `μ` leaves the nesting exactly where it was,
-- so the block of rungs the unfoldings bought is common to both sides
-- and only the layer summand has to shrink.
muLay-sub : ∀ (S B M d j j′ s : ℕ) → 2 ≤ S → j ≤ j′ →
  iterSize S (descRungsᴺ d B + j′ + s) B ≤ M →
  iterSize S (descRungsᴺ d B + j + s) B ≤ M
muLay-sub S B M d j j′ s 2≤S h le =
  lay-sub S B M (descRungsᴺ d B + j + s) (descRungsᴺ d B + j′ + s) 2≤S
    (+-monoˡ-≤ s (+-monoʳ-≤ (descRungsᴺ d B) h)) le

-- ONE SQUARING, PAID FOR IN RUNGS.  A rung at least doubles, so
-- `bitsᴺ B` of them carry a bound past `2 ^ bitsᴺ B * B` and
-- therefore past `B * B` -- and that is the whole of why the charge can
-- afford an unfolding while staying a count logarithmic in the bound.
muStep : ∀ (S B : ℕ) → 1 ≤ S → B * B ≤ iterSize S (bitsᴺ B) B
muStep S B 1≤S =
  ≤-trans (*-mono-≤ (n≤2^bitsᴺ B) ≤-refl) (iterSize-2^ S (bitsᴺ B) B 1≤S)

-- AND ONE UNFOLDING'S CHARGE, WHICH IS THAT SQUARING SPENT.  The
-- caller's ceiling holds the block for `suc d` levels at bound `B`; the
-- unfolding is descended into at `B * B`, and the leading `bitsᴺ B`
-- rungs of that block are exactly what carries the bound there -- so
-- the remaining block, read at the squared bound, is what the recursion
-- inherits.  The level's own delivery rungs are left over, and the
-- descent simply does not spend them: an unfolding delivers nothing by
-- itself, so dropping them is slack rather than a gap.
muUnfold-le : ∀ (S B M d L s : ℕ) → 2 ≤ S →
  iterSize S (descRungsᴺ (suc d) B + L + s) B ≤ M →
  iterSize S (descRungsᴺ d (B * B) + L + s) (B * B) ≤ M
muUnfold-le S B M d L s 2≤S le =
  ≤-trans (iterSize-mono-s S (descRungsᴺ d (B * B) + L + s) (muStep S B 1≤S))
    (≤-trans (≤-reflexive (sym (iterSize-+ S (bitsᴺ B) (descRungsᴺ d (B * B) + L + s) B)))
      (lay-sub S B M (bitsᴺ B + (descRungsᴺ d (B * B) + L + s))
        (descRungsᴺ (suc d) B + L + s) 2≤S ineq le))
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S
  R : ℕ
  R = descRungsᴺ d (B * B)
  eq : bitsᴺ B + (R + L + s) ≡ bitsᴺ B + R + L + s
  eq = sym (trans (cong (_+ s) (+-assoc (bitsᴺ B) R L))
                  (+-assoc (bitsᴺ B) (R + L) s))
  ineq : bitsᴺ B + (R + L + s) ≤ descRungsᴺ (suc d) B + L + s
  ineq = ≤-trans (≤-reflexive eq)
           (+-monoˡ-≤ s (+-monoˡ-≤ L
             (+-monoˡ-≤ R (m≤m+n (bitsᴺ B) (B * bitsᴺ B)))))

-- THE TWO TRANSPORTS AT A DOOR, WHICH IS THE ONE CONSTRUCTOR SHAPE THE
-- THREE CROSSINGS SHARE.  Each charges one layer and one syntax node
-- over its source and nothing else, so the door's own arithmetic is
-- named once here rather than spelled out at three arms that would
-- then drift apart.
crossLe : ∀ (S B M d L s : ℕ) → 2 ≤ S →
  iterSize S (descRungsᴺ d B + suc L + s) B ≤ M →
  iterSize S (descRungsᴺ d B + L + s) B ≤ M
crossLe S B M d L s 2≤S le =
  muLay-sub S B M d L (suc L) s 2≤S (n≤1+n L) le

crossSz : ∀ (a B : ℕ) → (suc a ≤ᵇ B) ≡ true → (a ≤ᵇ B) ≡ true
crossSz a B hb = sz-sub a (suc a) B (n≤1+n a) hb

-- WHAT ONE SUBSCRIPTION WRITES INTO THE TABLE, which is what every
-- store arm reduces to once its own door and its own gas are taken
-- off it.  The cells the subscription installs hold that run's
-- emission -- reified, so priced by the program's LAYERS -- with the
-- telescope beside them for the slots the run connects.
--
-- AND IT IS STATED AT A LEVEL THE PROGRAM ALREADY REACHES, NOT AS A
-- CLIMB FROM THE PREMISE'S OWN.  That is what makes it composable
-- across a burst the count joins by MAX: a statement handing back one
-- rung per subscription would compound over the fold, and the join
-- says the subscriptions do not compound.  So the level is carried as
-- a parameter with the program's charge under it, and every
-- consumer's job is to show the level is never raised rather than to
-- add rungs up.
--
-- AND THE BODY IS WHAT SAYS ONE RUNG COVERS ONE OPERATOR.  Four arms
-- descend at the caller's own level with the premises transported by
-- the two subterm lemmas above; two frame kinds cross a burst without
-- moving the table at all; and what is left over is the four leaves,
-- each owing something the descent cannot hand it -- a definition
-- behind a reference, a cell in a currency the premise is not stated
-- in, an arrival that re-enters at its own level, and a substitution
-- that squares the size.
--
-- AND NOTHING IS CHARGED FOR THE PATH, which is sound rather than an
-- omission: `κ` is a CONTINUATION and not something this call walks.
-- What the subscription emits is handed back UP to whoever asked for
-- it, and the path is spent only as the decoration a later crossing
-- subscribes its own arrival under -- where that arrival's layers pay
-- for what it writes.  No node state holds a path either, so nothing
-- the reading prices can grow with one.  What it does cost is that a
-- `κ` no ancestor ever built is admitted at the same level, since the
-- charge is bought by the subscribed program alone.
--
-- DEAD ROUTE: telling the `+` apart from a `⊔` by INSTANTIATION.
--   Both summands sit inside a PREMISE, so enlarging the charge
--   strengthens that premise and WEAKENS the statement -- no witness
--   can refute the sum on either axis, however much it delivers, and
--   a row at the joined reading that comes out true says the sum
--   bought slack rather than that it was wrong.  The gap is
--   unreachable besides: a rung multiplies, so the two readings are a
--   geometric factor apart and every emission a slot telescope can
--   produce sits far below both.  What the sum COSTS is paid by the
--   consumers that must supply the premise, so it is decided at the
--   call sites and not by any state this statement can be entered at.

-- AND THE UNFOLDINGS ARE IN THE DENOMINATION, WHICH IS WHAT MAKES THE
-- `μ` ARM A RECURSION RATHER THAN A LEAF.  A rung is affine in the
-- bound, so a rung count fixed by the SYNTAX buys a fixed factor; one
-- unfold copies the whole program once per mention of its own recursive
-- occurrence, and the layer count charges nothing for the `μ` or for
-- the `defer` those mentions must stand under.  The mentions are a free
-- parameter, so the level cannot be fixed by the layers -- it grows
-- with the BOUND instead, a block of rungs per level of nesting, and
-- the arm below descends into the unfolding at the squared bound those
-- rungs have already paid for.
-- REFUTED: `Refuted.Burst-Mu-Square` -- the layer-only denomination
--   this charge replaces, at a plain merging door over a one-shot
--   source whose single emission is a `μ`, entered at an empty table
--   with the crossing bracketed on both sides so what fails is the
--   multiplicity and not the door or the arithmetic.

-- AND THIS IS THE ASSEMBLY WHOSE OWN CONCLUSION WAS INSTANTIATED, not
-- merely its leaves -- which is why the charge under it counts
-- deliveries at all.  A real body over postulated leaves computes
-- exactly as a postulate does, so a witness could be entered against
-- it directly, and one was: the defect was the CURRENCY the body and
-- its leaves share rather than any clause of either, so no arm of the
-- recursion could have been moved to repair it.  That is the
-- retroactive shape, and the reason an assembly is worth instantiating
-- even while it typechecks.
-- REFUTED: `Refuted.Subscribe-Store-Scan-Arrivals` -- the DEPTH-ONLY
--   denomination this bound replaces, by the same witness that kills
--   the `scanᵉ` leaf, entered against this statement directly since the
--   two bounds were spelled identically and this program is an
--   ordinary closed term.
subscribeE-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
  (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (descChg (obs u) B o + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵉ o ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (subscribeE g o κ id now sched st))))
    ≡ true
subscribeE-sz-store {Γ = Γ} {u = u} sl g (input i) κ id now sched st S B M
                    2≤S slEq le hns hb
  with Sched.slots sched i
... | shared d =
      subscribeSharedSlot-sz-store sl g i d κ id now sched st S B M
        2≤S slEq
        (lay-sub S B M (slotsSize sl)
          (descChg {Γ = Γ} (obs u) B (input i) + slotsSize sl) 2≤S
          (m≤n+m (slotsSize sl) (descChg {Γ = Γ} (obs u) B (input i))) le)
        hns hb
... | scripted (hot _) with memberSource (toℕ i) (EvalSt.completedSources st)
...   | true  = hns
...   | false = hns
subscribeE-sz-store sl g (input i) κ id now sched st S B M 2≤S slEq le hns hb
  | scripted (cold sync [])       = hns
subscribeE-sz-store sl g (input i) κ id now sched st S B M 2≤S slEq le hns hb
  | scripted (cold sync (d ∷ ds)) = hns
subscribeE-sz-store sl g (ofᵉ ts) κ id now sched st S B M 2≤S slEq le hns hb = hns
subscribeE-sz-store sl g emptyᵉ   κ id now sched st S B M 2≤S slEq le hns hb = hns
subscribeE-sz-store sl g (mapᵉ f b) κ id now sched st S B M 2≤S slEq le hns hb =
  pushBurst-sz-store-flat g id now (map-f f) κ
    (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) M refl
    (subscribeE-sz-store sl g b (map-f f ↠ κ) id now sched st S B M 2≤S slEq
      (muLay-sub S B M (muDepthᵉ b) (layᵉ b) (suc (layᵗ f ⊔ layᵉ b))
        (slotsSize sl) 2≤S
        (≤-trans (m≤n⊔m (layᵗ f) (layᵉ b)) (n≤1+n _)) le)
      hns
      (sz-sub (sizeᵉ b) (suc (sizeᵗ f + sizeᵉ b)) B
        (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ f)) (n≤1+n _)) hb))
  where SE = subscribeE g b (map-f f ↠ κ) id now sched st
subscribeE-sz-store sl g (takeᵉ c b) κ id now sched st S B M 2≤S slEq le hns hb
  with evalTm c
... | zero  = hns
... | suc k =
      pushBurst-sz-store-flat g id now (take-f nid) κ
        (proj₁ SE) (proj₁ (proj₂ SE)) (proj₂ (proj₂ SE)) M refl
        (subscribeE-sz-store sl g b (take-f nid ↠ κ) id now sched₁ st₀ S B M
          2≤S slEq
          (muLay-sub S B M (muDepthᵉ b) (layᵉ b) (suc (layᵗ c ⊔ layᵉ b))
            (slotsSize sl) 2≤S
            (≤-trans (m≤n⊔m (layᵗ c) (layᵉ b)) (n≤1+n _)) le)
          (setNode-bounded M nid (take-st (suc k)) (EvalSt.nodes st) refl hns)
          (sz-sub (sizeᵉ b) (suc (sizeᵗ c + sizeᵉ b)) B
            (≤-trans (m≤n+m (sizeᵉ b) (sizeᵗ c)) (n≤1+n _)) hb))
      where
      nid    = Sched.nextNode sched
      sched₁ = record sched { nextNode = suc (Sched.nextNode sched) }
      st₀    = installNode nid (take-st (suc k)) st
      SE     = subscribeE g b (take-f nid ↠ κ) id now sched₁ st₀
subscribeE-sz-store sl g (scanᵉ f z b) κ id now sched st S B M 2≤S slEq le hns hb =
  subscribeE-sz-store-scan sl g f z b κ id now sched st S B M 2≤S slEq le hns hb
subscribeE-sz-store {u = u} sl g (mergeAllᵉ lim b) κ id now sched st S B M
                    2≤S slEq le hns hb =
  pushBurst-sz-store-outer sl g mergeAllᵒ nid b κ id now sched₁ st₀ SE
    S B M 2≤S slEq refl le
    (subscribeE-sz-store sl g b (thru-outer mergeAllᵒ nid ↠ κ) id now
      sched₁ st₀ S B M 2≤S slEq
      (crossLe S B M (muDepthᵉ b) (layᵉ b) (slotsSize sl) 2≤S le)
      (setNode-bounded M nid (mergeAll-st {t = u} lim 0 [] false)
        (EvalSt.nodes st) refl hns)
      (crossSz (sizeᵉ b) B hb))
    (crossSz (sizeᵉ b) B hb)
  where
  nid    = Sched.nextNode sched
  sched₁ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid (mergeAll-st {t = u} lim 0 [] false) st
  SE     = subscribeE g b (thru-outer mergeAllᵒ nid ↠ κ) id now sched₁ st₀
subscribeE-sz-store sl g (switchAllᵉ b) κ id now sched st S B M 2≤S slEq le hns hb =
  pushBurst-sz-store-outer sl g switchᵒ nid b κ id now sched₁ st₀ SE
    S B M 2≤S slEq refl le
    (subscribeE-sz-store sl g b (thru-outer switchᵒ nid ↠ κ) id now
      sched₁ st₀ S B M 2≤S slEq
      (crossLe S B M (muDepthᵉ b) (layᵉ b) (slotsSize sl) 2≤S le)
      (setNode-bounded M nid (switch-st nothing false)
        (EvalSt.nodes st) refl hns)
      (crossSz (sizeᵉ b) B hb))
    (crossSz (sizeᵉ b) B hb)
  where
  nid    = Sched.nextNode sched
  sched₁ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid (switch-st nothing false) st
  SE     = subscribeE g b (thru-outer switchᵒ nid ↠ κ) id now sched₁ st₀
subscribeE-sz-store sl g (exhaustAllᵉ b) κ id now sched st S B M 2≤S slEq le hns hb =
  pushBurst-sz-store-outer sl g exhaustᵒ nid b κ id now sched₁ st₀ SE
    S B M 2≤S slEq refl le
    (subscribeE-sz-store sl g b (thru-outer exhaustᵒ nid ↠ κ) id now
      sched₁ st₀ S B M 2≤S slEq
      (crossLe S B M (muDepthᵉ b) (layᵉ b) (slotsSize sl) 2≤S le)
      (setNode-bounded M nid (exhaust-st false false)
        (EvalSt.nodes st) refl hns)
      (crossSz (sizeᵉ b) B hb))
    (crossSz (sizeᵉ b) B hb)
  where
  nid    = Sched.nextNode sched
  sched₁ = record sched { nextNode = suc (Sched.nextNode sched) }
  st₀    = installNode nid (exhaust-st false false) st
  SE     = subscribeE g b (thru-outer exhaustᵒ nid ↠ κ) id now sched₁ st₀
subscribeE-sz-store sl g0 (μᵉ body) κ id now sched st S B M 2≤S slEq le hns hb = hns
subscribeE-sz-store sl (gs fuel) (μᵉ body) κ id now sched st S B M
                    2≤S slEq le hns hb =
  subscribeE-sz-store sl fuel (unfoldμ body) κ id now sched st S (B * B) M
    2≤S slEq le′ hns hb′
  where
  le′ : iterSize S (descChg (obs _) (B * B) (unfoldμ body) + slotsSize sl)
          (B * B) ≤ M
  le′ = subst (λ z → iterSize S (z + slotsSize sl) (B * B) ≤ M)
          (sym (cong₂ _+_
                 (cong (λ d → descRungsᴺ d (B * B)) (muDepth-unfoldμ body))
                 (lay-unfoldμ body)))
          (muUnfold-le S B M (muDepthᵉ body) (layᵉ body) (slotsSize sl) 2≤S le)

  mB : sizeᵉ (μᵉ body) ≤ B
  mB = ≤ᵇ⇒≤ (sizeᵉ (μᵉ body)) B (T-to hb)

  hb′ : (sizeᵉ (unfoldμ body) ≤ᵇ B * B) ≡ true
  hb′ = ≤ᵇ-true (sizeᵉ (unfoldμ body)) (B * B)
          (≤-trans (size-unfoldμ body) (*-mono-≤ mB mB))
subscribeE-sz-store sl g (varᵉ ()) κ id now sched st S B M 2≤S slEq le hns hb
subscribeE-sz-store {u = u} sl g (deferᵉ body) κ id now sched st S B M
                    2≤S slEq le hns hb =
  setNode-bounded M (Sched.nextNode sched)
    (mergeAll-st {t = u} nothing 0 [] false) (EvalSt.nodes st) refl hns

-- ONE ARRIVAL SUBSCRIBED, WHICH IS THE STORE SIDE'S LAST DOOR.  A
-- crossing frame mints the inner's exit-frame instance and then does
-- exactly one thing with it, and which of the two is decided by gas
-- alone: with none, the arrival is answered by a dry close and the
-- table is handed back untouched, so the premise IS the conclusion;
-- with some, it is the general descent entered at the caller's path
-- under a `from-inner` decoration, and the minted instance moves only
-- the scheduler's node counter, which the reading does not price.
--
-- SO THE DECORATION IS FREE AND THE ARRIVAL'S CHARGE IS UNCHANGED: the
-- charge reads the program, not the path it is subscribed at, and the
-- record update touches no slot -- which is what lets the level cross
-- this door verbatim rather than climbing a rung at it.
subscribeInner-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (sf : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (descChg (obs u) B o + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵛ (obs u) o ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner sf op allNid κ id now o sched st)))))))
    ≡ true
subscribeInner-sz-store sl g0 op allNid κ id now o sched st S B M
                        2≤S slEq le hns hb = hns
subscribeInner-sz-store sl (gs fuel) op allNid κ id now o sched st S B M
                        2≤S slEq le hns hb =
  subscribeE-sz-store sl fuel o
    (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st S B M
    2≤S slEq le hns hb

-- WHAT A DRAIN LEAVES IN THE TABLE, WHICH IS AGAIN A FOLD CARRYING A
-- LEVEL RATHER THAN CLIMBING ONE.  Each parked entry is subscribed at
-- the state its predecessor left, so an induction handing the table a
-- rung per entry would end at the queue's SUM -- and the reading this
-- arm owes joins the entries by max.  What is carried instead is one
-- level high enough for the whole queue: the head entry's own charge
-- sits under the join, so the leaf leaves the level where it found it
-- and the tail inherits it unchanged.
--
-- AND THE TELESCOPE SURVIVES THE FOLD for the reason it survives the
-- crossing's: a subscription hands on the slots it was handed, so the
-- level can be named once at the schedule the drain entered with.
mergeAllDrain-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id)
  (now : Tick) (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (descChgˢ (obs s) B q + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ B) q ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (mergeAllDrain sf allNid κ id now lim act q sched st)))))))
    ≡ true
mergeAllDrain-sz-store sl sf allNid κ id now lim act [] sched st S B M
                       2≤S slEq le hns hq = hns
mergeAllDrain-sz-store {s = s} sl sf allNid κ id now lim act (o ∷ q) sched st
                       S B M 2≤S slEq le hns hq
  with hasRoom lim act
... | false = hns
... | true =
  mergeAllDrain-sz-store sl sf allNid κ id now lim
    (if done then act else suc act) q sched₁ st₁ S B M 2≤S
    (trans (subscribeInner-slots sf mergeAllᵒ allNid κ id now o sched st) slEq)
    tailLe headBound (∧-trueʳ hq)
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  r₁ = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

  headBound : all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st₁) ≡ true
  headBound =
    subscribeInner-sz-store sl sf mergeAllᵒ allNid κ id now o sched st
      S B M 2≤S slEq
      (≤-trans (iterSize-mono-count S B 1≤S
                 (+-monoˡ-≤ (slotsSize sl)
                   (m≤m⊔n (descChg (obs s) B o) (descChgˢ (obs s) B q))))
               le)
      hns (∧-trueˡ hq)

  tailLe : iterSize S (descChgˢ (obs s) B q + slotsSize sl) B ≤ M
  tailLe =
    ≤-trans (iterSize-mono-count S B 1≤S
              (+-monoˡ-≤ (slotsSize sl)
                (m≤n⊔m (descChg (obs s) B o) (descChgˢ (obs s) B q))))
            le

-- THE QUEUE A DRAIN HANDS BACK IS PRICED BY THE QUEUE IT ENTERED,
-- which is the half the fold above does not say: that one is about the
-- table, and the cell the finish writes back carries the entries the
-- drain could not admit.  Nothing about those entries is a trace of
-- anything the drain ran -- they are the syntax the value premise
-- already bounds -- so the statement is generic in the bound and the
-- widening happens once, at the site that needs the level.
mergeAllDrain-queue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
  (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
  (sched : Sched Γ) (st : EvalSt e) (C : ℕ) →
  all (λ o → sizeᵉ o ≤ᵇ C) q ≡ true →
  all (λ o → sizeᵉ o ≤ᵇ C)
      (proj₁ (proj₂ (proj₂ (proj₂
        (mergeAllDrain sf allNid κ id now lim act q sched st)))))
    ≡ true
mergeAllDrain-queue sf allNid κ id now lim act [] sched st C hq = refl
mergeAllDrain-queue sf allNid κ id now lim act (o ∷ q) sched st C hq
  with hasRoom lim act
... | false = hq
... | true =
  mergeAllDrain-queue sf allNid κ id now lim (if done then act else suc act)
    q sched₁ st₁ C (∧-trueʳ hq)
  where
  r₁ = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  done = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

-- AND ALONG THE WHOLE PATH, state by state.  The frames' debts cannot
-- be collected in one bundle up front: each is owed at the state the
-- walk has reached by the time that frame runs, so the predicate has
-- to step alongside the fold it guards.  Four frame kinds contribute
-- nothing, so on a path with no outer frame this is a tuple of units.
--
-- AND THE SINK IS NOT A LEAF OF IT, WHICH IS WHAT THE UNIT CLAUSE USED
-- TO SAY.  A `share-sink` hands the values to every chain the registry
-- admits, and each of those walks a path of its OWN, so the debt is per
-- admitted entry, at the state the fan-out fold reaches it in, and the
-- predicate telescopes through the fold exactly as it does through a
-- chain.  What the sink is charged is a price the walk's own ledger
-- picks -- an exponent in the size cap and a square of it in depth --
-- and that pays for an admitted chain whose own leaf is a `root` and
-- for no other, since a chain ending at a second hand-over carries the
-- sink's price multiplied by its frames'.
mutual
  PathΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (B U : ℕ) (path : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  PathΦHyp sf gas id now B U root vals fin sched st = ⊤
  PathΦHyp sf gas id now B U (share-sink i) vals fin sched st =
    DispatchΦHyp sf gas id now B U i vals fin sched st
  PathΦHyp sf gas id now B U (f ↠ p) vals fin sched st =
    FrameΦHyp sf id now B U f p vals fin sched st
    × PathΦHyp sf gas id now B U p
        (proj₁ (stepFrame sf id now f p vals fin sched st))
        (proj₁ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st))))
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))

  -- one dispatch level, and it owes nothing when the telescope is spent
  -- -- that arm of the evaluator returns the state untouched.
  DispatchΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (B U : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  DispatchΦHyp {t = t} sf zero id now B U i vals fin sched st = ⊤
  DispatchΦHyp {t = t} sf (suc gas) id now B U i vals fin sched st =
    ShareGoΦHyp {t = t} sf gas id now B U i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  -- the fan-out fold's own obligations: a cancelled registration is
  -- skipped and owes nothing, and a delivered one owes the potential at
  -- ITS path plus that path's own walk debt.
  ShareGoΦHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (B U : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  ShareGoΦHyp sf gas id now B U i vals fin [] sched st = ⊤
  ShareGoΦHyp {t = t} sf gas id now B U i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then ShareGoΦHyp {t = t} sf gas id now B U i vals fin ps sched st
    else ((valsΦ? B U p vals ≡ true)
      × PathΦHyp sf gas id now B U p vals fin sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
      × ShareGoΦHyp {t = t} sf gas id now B U i vals fin ps
          (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st }))))
          (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- THE WALK, AND THE FAN-OUT IT RE-ENTERS, in the evaluator's own
-- recursion: a chain descends to a sink, the sink spends one level of
-- the dispatch telescope, and the fold re-enters a chain per admitted
-- registration.  Nothing here is arithmetic -- every clause is the same
-- three-way join, and the only inequality that is not a projection is
-- the frame leaf's.
mutual
  foldPath-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U path vals ≡ true →
    PathΦHyp sf gas id now B U path vals fin sched st →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U
  foldPath-nest-regs sf gas id now envSrc root vals evs fin sched st B U hΦ _ =
    m≤m⊔n (regsNestMax (EvalSt.registry st)) U
  foldPath-nest-regs sf gas id now envSrc (share-sink i) vals evs fin sched st B U hΦ hD =
    dispatchShare-nest-regs sf gas id now i vals fin sched st B U hD
  foldPath-nest-regs sf gas id now envSrc (f ↠ p) vals evs fin sched st B U hΦ (hF , hR) =
    ≤-trans (foldPath-nest-regs sf gas id now envSrc p
               (proj₁ step) (evs ++ proj₁ (proj₂ step))
               (proj₁ (proj₂ (proj₂ step)))
               (proj₁ (proj₂ (proj₂ (proj₂ step))))
               (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U
               (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR)
            (⊔-lub (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ hF)
                   (m≤n⊔m (regsNestMax (EvalSt.registry st)) U))
    where
    step = stepFrame sf id now f p vals fin sched st

  -- THE SINK'S THREE ARMS, and only the fold is work.  Out of dispatch
  -- gas the state is returned untouched; the latch writes the completed
  -- and dying ledgers and not the registry; and the finishing arm only
  -- DROPS registrations, which a join cannot be raised by.
  dispatchShare-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    DispatchΦHyp sf gas id now B U i vals fin sched st →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U
  dispatchShare-nest-regs sf zero id now i vals fin sched st B U _ =
    m≤m⊔n (regsNestMax (EvalSt.registry st)) U
  dispatchShare-nest-regs sf (suc gas) id now i vals false sched st B U hS =
    shareGo-nest-regs sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B U hS
  dispatchShare-nest-regs {t = t} sf (suc gas) id now i vals true sched st B U hS =
    ≤-trans (dropSource-nest (toℕ i)
              (EvalSt.registry (proj₂ (proj₂ (shareGo {t = t} sf gas id now i vals true
                (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st))))))
            (shareGo-nest-regs sf gas id now i vals true
              (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B U hS)

  -- ONE ADMITTED REGISTRATION AT A TIME, and the join telescopes: each
  -- chain leaves the registry under the registry it entered on joined
  -- with the charge, and the next chain enters on that one.
  shareGo-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    ShareGoΦHyp sf gas id now B U i vals fin ps sched st →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U
  shareGo-nest-regs sf gas id now i vals fin [] sched st B U _ =
    m≤m⊔n (regsNestMax (EvalSt.registry st)) U
  shareGo-nest-regs sf gas id now i vals fin ((rid , p) ∷ ps) sched st B U hS
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nest-regs sf gas id now i vals fin ps sched st B U hS
  ... | false =
    ≤-trans (shareGo-nest-regs sf gas id now i vals fin ps
               (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B U
               (proj₂ (proj₂ hS)))
            (⊔-lub (foldPath-nest-regs sf gas id now (toℕ i) p vals
                      (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
                      B U (proj₁ hS) (proj₁ (proj₂ hS)))
                   (m≤n⊔m (regsNestMax (EvalSt.registry st)) U))
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    FP  = foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched st₀
