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

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.ListAction using (all; any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; map; length)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤;
  ≤⇒≤ᵇ; ≤ᵇ⇒≤; m^n>0; *-zeroʳ; *-distribˡ-⊔; *-identityˡ; *-mono-≤; +-comm;
  +-assoc; +-identityʳ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to; T⇒≡true; ≤ᵇ-widen)
open import Rx.Prim using (Gas; g0; gs; Id; Tick; Source; InstEvent; close; exhausted)
open import Relation.Nullary using (yes; no)
open import Rx.Exp using (Ctx; Closed; Val; Fn; applyFn; sizeᵉ; sizeᵗ; sizeᵛ; _×ᵗ_; obs; _≟ᵗ_)
open import Rx.Layer-Count using (layᵉ; layᵛˢ)
open import Rx.Slots using (Slots; slotsSize)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; NodeId; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; foldPath; stepFrame; dispatchShare; thruWalk; shareGo;
  shareAdmit; shareLatch; iterSize; NodeState; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; takeDispatch; takeVals; lookupNode; scanVals; mergeAllᵒ; switchᵒ; exhaustᵒ;
  mergeAllDrain; innerFinish; aliveThroughᶠ; subscribeInner; subscribeE;
  splitBurst; hasRoom;
  thruConsume; thruWrap; switchKill; mergeAllBump)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; thruWalk-nest; nodeNestAt; stepFrame-emit-scan;
  stepFrame-nodes-inner; capsDrainOK; FaceOK; switchKill-slots;
  switchKill-nodes; burstsOK; burstsHead)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures
  using (thruWrap-vals; takeVals-all; pathLen; boundedNode; setNode-bounded;
  boundedNode-widen; all-impl; all-++-intro)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nest-inflate; dropSource-nest; nestUnit; cutThrough-nest)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; sizeCount; iterSize-infl; iterSize-mono-count)
open import Verify-Budget-Sufficient.Keeps-Ring
  using (subscribeE-slots; thruConsume-slots; stepFrame-slots)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Caps-Depth using (depthReact)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; frameSz?; applyFn-iterSize)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using (scanVals-size)
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
InnerΦFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (B U : ℕ)
  (op : AllOp) (allNid inst : NodeId) (path : Path Γ s t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) → Set
InnerΦFit {Γ = Γ} {e = e} {s = s} sf id now B U op allNid inst path vals fin sched st =
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
    × (nodeNestAt allNid st ⊔ nestDᵛˢ vals ≤ G)
    × (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
         pathΦF B path
           * (nestFac (Caps.cSize (frameStep j c)) W
                * (G + nestU (Caps.cSize (frameStep j c))
                         (nestUnit e (Sched.slots sched)))
              + pathΦD B path) ≤ U)

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
       (c , d , W , Lv , G , face , hdr , hw , hdp , hpk , hpl , hst , hnum) =
  Φ-of-bound B U (nestFac S′ W * (G + nestU S′ (nestUnit e (Sched.slots sched))))
    path (proj₁ r) bound (hnum j (proj₁ (proj₂ INNER)))
  where
  r = stepFrame sf id now (from-inner op allNid inst) path vals fin sched st

  INNER = stepFrame-nodes-inner c d (Sched.slots sched) W Lv sf id now op
            allNid inst path vals fin sched st ⦃ face ⦄ refl hdr hw hdp hpk hpl

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

-- WHAT A NODE HAS PARKED, IN LAYERS.  Only a merge queues: a switch
-- holds at most the node id of the inner it is currently running, an
-- exhaust holds two bits, and the two leaf states hold values the
-- drain never subscribes.  So every other shape parks nothing, and
-- that is a fact about the node table rather than a default.
parkedLay : ∀ {n} {Γ : Ctx n} → NodeState Γ → ℕ
parkedLay (scan-st _)               = 0
parkedLay (take-st _)               = 0
parkedLay (mergeAll-st {t} _ _ q _) = layᵛˢ (obs t) q
parkedLay (switch-st _ _)           = 0
parkedLay (exhaust-st _ _)          = 0

-- SPELLED AS ITS OWN RECURSION RATHER THAN THROUGH `lookupNode`,
-- because this count stands inside a TYPE and a `with` over a `Maybe`
-- reduces for nobody.  A node the table does not hold parks nothing.
parkedLayAt : ∀ {n} {Γ : Ctx n} → NodeId →
  List (NodeId × NodeState Γ) → ℕ
parkedLayAt nid []            = 0
parkedLayAt nid ((k , s) ∷ r) =
  if k ≡ᵇ nid then parkedLay s else parkedLayAt nid r

-- THE COUNT ONE FRAME CHARGES THE LADDER, AND IT IS A PROPERTY OF THE
-- KIND.  A `map-f` substitutes into each arriving value independently,
-- so it pays one rung per node of its own function and the burst does
-- not enter.  A `scan-f` THREADS, so it pays those rungs ONCE PER
-- arriving value, plus the pairing that precedes each step.  A take
-- computes no value of its own, passing a prefix through, so one rung
-- covers it.

-- THE TWO CROSSING ARMS DELIVER NOTHING THEY DRAINED: each SUBSCRIBES
-- a program that arrived at runtime, and running that program's own
-- synchronous chain is a computation whose emission is exponential in
-- the program's syntax.  So a count for either is a reading of what
-- RUNS, and the arms differ only in WHERE that program is -- an outer
-- crossing has it in its own argument list, an inner one reaches it
-- through the store.

-- AND THE INNER ARM READS WHAT ITS NODE HAS PARKED, which is what the
-- node table is handed to this count for.  A `mergeAllᵒ` exit spends
-- the subscription of whatever its own `*All` node has queued, so the
-- queue is the thing to price and its LAYERS are what a subscription
-- runs -- the same reading the outer arm takes of its arrivals, at the
-- other place an arriving program can sit.  The join is MAX for the
-- reason it is there: the drain subscribes each entry separately and
-- every delivered value comes out of one entry's run.  The four node
-- shapes that park nothing charge nothing, because an exit that
-- subscribes nothing runs nothing.
--
-- AND THAT REMOVES THE ARM'S OWN CHANNEL TO THE LEVEL, which is the
-- whole of what the change buys.  A charge denominated in the store
-- BOUND climbs with the walk whatever is parked, so the arm broke a
-- linear ledger a rung before the outer one did and no repair to the
-- outer reading could reach it.  A charge denominated in the parked
-- PROGRAM reaches the level only the way an arrival's does, through
-- the size a rung admits -- so the two arms now stand or fall on one
-- statement instead of two.
--
-- REFUTED: `Refuted.Walk-Ceil-Drain` -- this arm against the whole
--   ledger a chain door supplies, at a parked chain the entry store
--   reading admits.  What survives the restatement is the LEVEL
--   channel the arm shares with its sibling: the store premise bounds
--   what is parked by the level and nothing bounds the level by the
--   program, so a deep enough parked chain still overruns the ledger.
--   What does not survive is the arm's own head start.

-- AND THE TELESCOPE IS PART OF THE OUTER READING, because arriving
-- syntax is not what runs whenever it NAMES a slot: a variable prices
-- at one node and connecting it runs the whole of that slot's shared
-- definition.  The telescope is charged WHOLE rather than resolved,
-- which over-charges a frame naming no slot and is the same
-- displacement the width ceiling takes -- there a slot head reads zero
-- at the node and the telescope's own ceiling pays for it separately.
-- A resolving count would chase slot references transitively, and what
-- terminates that chase is the telescope's stratification, a property
-- of the telescope and not of this frame.

-- AND THE OUTER ARM READS THE ARRIVAL'S OPERATOR LAYERS, which is what
-- a subscription actually spends and is why its charge does not climb
-- with the walk's level.  Each substitution multiplies, so a k-layer
-- chain emits at two to the k and k rungs pay for it.  What the ladder
-- multiplies besides that is the arrival's DATA, and data emits itself,
-- so a reading of the arrival's SIZE prices the run only where the
-- arrival's syntax IS the run -- and the walk manufactures the other
-- shape.
--
-- AND A LAYER COUNT IS THE ONLY CANDIDATE THE WALK CANNOT GROW.  A
-- frame applies a CLOSED function, and applying one REIFIES the arrival
-- into the term: a count charging a function's SYNTAX therefore goes
-- from nothing to the arrival's own size in a single `map-f` step and
-- then climbs with the level exactly as `sizeᵛ` does, while a reified
-- datum contributes no layer however large.  Both separations are
-- machine-exhibited rather than argued.  The size reading parts from a
-- spine reading at a reified arrival, where the spine still covers the
-- emission with no rung bought, at a margin of two nodes
-- (`Probed.Cross-Count-Data`); the syntax and layer readings part on a
-- value one frame manufactured, and there the layer count is also
-- smaller at the duplication chain and agrees exactly at the reified
-- arrival (`Probed.Cross-Count-Spine`).
--
-- AND THE BURST JOINS BY MAX, WHICH IS A CLAIM ABOUT THE CONCLUSION
-- AND NOT A CHOICE OF SLACK.  What this count buys is a bound stated
-- PER DELIVERED VALUE, and every delivered value comes out of ONE
-- arrival's run; the arrivals share only the sink node they drain
-- into, whose table is read entry by entry.  So a sum would be honest
-- only if a burst COMPOUNDED -- one arrival's emission feeding
-- another's inside the same frame, or the shared node carrying a
-- quantity neither arrival produced alone -- and it does not, at any
-- of the three sinks, whose admission rules differ exactly where that
-- would show.  The sum is what put the
-- charge outside the ledger's priceable set through the burst WIDTH,
-- and the max removes that channel: what remains is an arrival's own
-- layers, which the level reaches only through the size a rung admits.
--
-- AND WHAT IT LEAVES OWED IS A SCAN'S WIDTH.  An arriving scan emits
-- per element while a layer count reads one layer for it, so the rungs
-- this arm buys are a bound on the arrival's chain and not yet on what
-- a threading operator inside that chain multiplies.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross` and
--   `Refuted.Frame-Step-Size-Cross-Store` -- one rung, at the
--   value and the store halves respectively.
-- REFUTED: `Refuted.Frame-Step-Size-Slot` -- the outer arm read at the
--   arriving values alone, with no telescope summand.
-- REFUTED: `Refuted.Drain-Queue-Slot` -- the inner arm read at the
--   parked queue alone, which is the same hole one door over: a parked
--   `input i` carries no layer and runs a whole shared definition.
szCount : ∀ {n} {Γ : Ctx n} {s u} → Slots Γ →
  List (NodeId × NodeState Γ) → Frame Γ s u → List (Val Γ s) → ℕ
szCount sl ns (map-f fn)              vals = sizeᵗ fn
szCount sl ns (scan-f fn nid)         vals = length vals * suc (sizeᵗ fn)
szCount sl ns (take-f nid)            vals = 1
szCount sl ns (from-inner _ allNid _) vals = parkedLayAt allNid ns + slotsSize sl
szCount {s = s} sl ns (thru-outer _ _) vals =
  layᵛˢ s vals + slotsSize sl

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

-- ONE SUBSTITUTION PER VALUE, INDEPENDENTLY, which is the whole of the
-- map arm: `evalWith` prices a term's evaluation at one fold per syntax
-- node and the values never meet, so the burst does not enter the
-- count.
mapSz : ∀ {n} {Γ : Ctx n} {s u} (S V : ℕ) → 1 ≤ S →
  (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
  valsSz? V vals ≡ true →
  valsSz? (iterSize S (sizeᵗ fn) V) (map (applyFn fn) vals) ≡ true
mapSz S V 1≤S fn []       h = refl
mapSz S V 1≤S fn (v ∷ vs) h =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ (applyFn-iterSize S V 1≤S fn v
                              (≤ᵇ⇒≤ _ V (T-to (∧-trueˡ h))))))
          (mapSz S V 1≤S fn vs (∧-trueʳ h))

-- A PREFIX IS NOT A COMPUTATION, so the take arm spends its rung on
-- nothing and the reading only has to be widened.  It is hoisted out of
-- the clause because both sides of the evaluator's own exhaustion test
-- deliver the same prefix, and a `where` reaches only the last of them.
takeSz : ∀ {n} {Γ : Ctx n} {s} (S B : ℕ) → 1 ≤ S →
  (k : ℕ) (vals : List (Val Γ s)) →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S 1 B) (proj₁ (takeVals k vals)) ≡ true
takeSz {s = s} S B 1≤S k vals hv =
  valsSz?-mono B (iterSize S 1 B) (proj₁ (takeVals k vals))
    (iterSize-infl S 1≤S 1 B)
    (takeVals-all (λ v → sizeᵛ s v ≤ᵇ B) k vals hv)

-- WHAT THE COUNT READS AT A LOOKUP, abstracted by the same `with` that
-- abstracts the evaluator's dispatch for the reason the store reading
-- beside it is: the count spells its own recursion, so a clause that
-- has scrutinised the table still has to be told the two walks agreed.
-- A cell the table does not hold parks nothing, which is the `nothing`
-- arm rather than an omission.
NodeLay : ∀ {n} {Γ : Ctx n} → ℕ → Maybe (NodeState Γ) → Set
NodeLay L nothing   = L ≡ 0
NodeLay L (just ns) = L ≡ parkedLay ns

parkedLayAt-lookup : ∀ {n} {Γ : Ctx n} (nid : NodeId)
  (nodes : List (NodeId × NodeState Γ)) →
  NodeLay (parkedLayAt nid nodes) (lookupNode nid nodes)
parkedLayAt-lookup nid []            = refl
parkedLayAt-lookup nid ((k , s) ∷ r) with k ≡ᵇ nid
... | true  = refl
... | false = parkedLayAt-lookup nid r

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
postulate
  subscribeE-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (o : Closed Γ u) (κ : Path Γ u t) (id : Id)
    (now : Tick) (sched : Sched Γ) (st : EvalSt e)
    (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
    valsSz? (iterSize S (layᵉ o + slotsSize (Sched.slots sched)) B)
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
-- SO NEITHER SIDE MOVES AT THE DOOR.  `layᵉ` reads the program and not
-- the path it is subscribed at, the record update touches no slot, and
-- the split is a projection rather than a step -- which is what lets
-- the charge cross verbatim rather than climbing a rung here.
subscribeInner-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t) (id : Id)
  (now : Tick) (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
  valsSz? (iterSize S (layᵉ o + slotsSize (Sched.slots sched)) B)
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
  valsSz? (iterSize S (layᵛˢ (obs s) q + slotsSize (Sched.slots sched)) B)
    (proj₁ (mergeAllDrain sf allNid κ id now lim act q sched st)) ≡ true
mergeAllDrain-sz sf allNid κ id now lim act [] sched st S B 2≤S hq = refl
mergeAllDrain-sz {s = s} sf allNid κ id now lim act (o ∷ q) sched st S B 2≤S hq
  with hasRoom lim act
... | false = refl
... | true =
  all-++-intro
    (λ v → sizeᵛ s v ≤ᵇ iterSize S (layᵛˢ (obs s) (o ∷ q)
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

  headFits : valsSz? (iterSize S (layᵛˢ (obs s) (o ∷ q) + slotsSize sl) B)
               vs ≡ true
  headFits =
    valsSz?-mono (iterSize S (layᵉ o + slotsSize sl) B)
      (iterSize S (layᵛˢ (obs s) (o ∷ q) + slotsSize sl) B) vs
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl) (m≤m⊔n (layᵉ o) (layᵛˢ (obs s) q))))
      (subscribeInner-sz sf mergeAllᵒ allNid κ id now o sched st S B 2≤S
        (∧-trueˡ hq))

  tailAtSched : valsSz? (iterSize S (layᵛˢ (obs s) q + slotsSize sl) B)
                  vs′ ≡ true
  tailAtSched =
    subst (λ z → valsSz? (iterSize S (layᵛˢ (obs s) q + slotsSize z) B)
                   vs′ ≡ true)
          (subscribeInner-slots sf mergeAllᵒ allNid κ id now o sched st)
          (mergeAllDrain-sz sf allNid κ id now lim
             (if done then act else suc act) q sched₁ st₁ S B 2≤S
             (∧-trueʳ hq))

  tailFits : valsSz? (iterSize S (layᵛˢ (obs s) (o ∷ q) + slotsSize sl) B)
               vs′ ≡ true
  tailFits =
    valsSz?-mono (iterSize S (layᵛˢ (obs s) q + slotsSize sl) B)
      (iterSize S (layᵛˢ (obs s) (o ∷ q) + slotsSize sl) B) vs′
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl) (m≤n⊔m (layᵉ o) (layᵛˢ (obs s) q))))
      tailAtSched

-- ONE WIDENING, SPENT BY EVERY ARM THAT PASSES ITS ARRIVALS THROUGH.
valsSz?-rung : ∀ {n} {Γ : Ctx n} {s} (S B L : ℕ) → 2 ≤ S →
  (vals : List (Val Γ s)) → valsSz? B vals ≡ true →
  valsSz? (iterSize S L B) vals ≡ true
valsSz?-rung S B L 2≤S vals hv =
  valsSz?-mono B (iterSize S L B) vals
    (iterSize-infl S (≤-trans (s≤s z≤n) 2≤S) L B) hv

-- THE FINISH IS THE DISPATCH AND ONE DRAIN.  Every arm but the merge
-- hands its arrivals straight back, so it is the incoming reading
-- widened; the merge arm concatenates what the drain emitted, and that
-- is the only place the charge is spent.  Stating it over an abstract
-- `Maybe` rather than over the table is what lets the frame above
-- scrutinise the cell once and hand both readings of it down.
--
-- AND `L` IS THE CELL'S OWN DEPTH WHILE THE CHARGE IS THAT PLUS THE
-- TELESCOPE, which keeps the abstraction honest: the cell reading is
-- what the frame above can hand down, and the telescope is what
-- neither the cell nor the arrivals mention.  Adding it in the
-- conclusion rather than asking the caller for a combined number is
-- what lets the `NodeLay` receipt stay a statement about the cell.
innerFinish-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
  (id : Id) (now : Tick) (vals : List (Val Γ s)) (sched : Sched Γ)
  (st : EvalSt e) (S B L : ℕ) → 2 ≤ S →
  (mns : Maybe (NodeState Γ)) → NodeLay L mns → NodeSz B mns →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S (L + slotsSize (Sched.slots sched)) B)
    (proj₁ (innerFinish sf op allNid inst κ id now vals sched st mns)) ≡ true

innerFinish-sz sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  nothing hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (scan-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (take-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (switch-st _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (exhaust-st _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz {s = s} sf mergeAllᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (mergeAll-st {w} lim act q od)) hL hb hv with w ≟ᵗ s
... | no  _    = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
... | yes refl =
  all-++-intro (λ v → sizeᵛ s v ≤ᵇ iterSize S (L + slotsSize (Sched.slots sched)) B) vals _
    (valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv)
    (subst (λ z → valsSz? (iterSize S (z + slotsSize (Sched.slots sched)) B)
                    (proj₁ (mergeAllDrain sf allNid κ id now lim (pred act) q
                              sched st)) ≡ true)
           (sym hL)
           (mergeAllDrain-sz sf allNid κ id now lim (pred act) q sched st
              S B 2≤S hb))

innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  nothing hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (scan-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (take-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (mergeAll-st _ _ _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (exhaust-st _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (switch-st nothing _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf switchᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (switch-st (just c₀) od)) hL hb hv with c₀ ≡ᵇ inst
... | true  = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
... | false = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv

innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  nothing hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (scan-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (take-st _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (mergeAll-st _ _ _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (switch-st _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv
innerFinish-sz sf exhaustᵒ allNid inst κ id now vals sched st S B L 2≤S
  (just (exhaust-st _ _)) hL hb hv = valsSz?-rung S B (L + slotsSize (Sched.slots sched)) 2≤S vals hv

-- THE INNER CROSSING, WHICH IS THE DISPATCH ABOVE PLUS TWO GATES.  A
-- frame that is not finishing, and one whose instance still has a live
-- registration under it, deliver their arrivals unchanged; only the
-- third gate reaches the node table at all, and there the cell is
-- scrutinised ONCE and its two readings -- what it has parked and what
-- it is bounded by -- are handed down together.  So the whole arm
-- reduces to one statement about what a drain delivers, and that is
-- the leaf.
--
-- DEAD ROUTE: charging this arm the size of its own arriving values is
--   STRUCTURALLY dead, and not merely too weak.  What the arm
--   subscribes is what the `*All` node has PARKED, so it is in the
--   store and not in `vals` -- the drain runs a program this
--   statement's arguments do not mention, and no reading of `vals` is
--   a reading of it.  That is what sends the charge to the node table
--   rather than to the arrivals.
-- REFUTED: `Refuted.Frame-Step-Size-Cross.stepFrame-sz-inner-absurd`
--   -- one rung, which is the charge this reading replaces.
-- REFUTED: `Refuted.Drain-Queue-Slot` -- the same reading with the
--   telescope summand dropped, which is where the drain leaf under
--   this body died.
stepFrame-sz-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S (parkedLayAt allNid (EvalSt.nodes st)
                        + slotsSize (Sched.slots sched)) B)
    (proj₁ (stepFrame sf id now (from-inner op allNid inst) path vals fin
              sched st)) ≡ true
stepFrame-sz-inner sf id now op allNid inst path vals false sched st S B
  2≤S hns hv =
  valsSz?-rung S B (parkedLayAt allNid (EvalSt.nodes st)
                     + slotsSize (Sched.slots sched)) 2≤S vals hv
stepFrame-sz-inner sf id now op allNid inst path vals true sched st S B
  2≤S hns hv with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  =
  valsSz?-rung S B (parkedLayAt allNid (EvalSt.nodes st)
                     + slotsSize (Sched.slots sched)) 2≤S vals hv
... | false =
  innerFinish-sz sf op allNid inst path id now vals sched st S B
    (parkedLayAt allNid (EvalSt.nodes st)) 2≤S
    (lookupNode allNid (EvalSt.nodes st))
    (parkedLayAt-lookup allNid (EvalSt.nodes st))
    (lookupNode-sz B allNid (EvalSt.nodes st) hns) hv

-- ONE ARRIVAL CONSUMED, WHICH IS THE SAME LEAF THE DRAIN SPENDS READ AT
-- THE OTHER DOOR.  Every operator arm either hands back nothing -- a
-- cell of the wrong kind or the wrong payload type, a full lane, a busy
-- exhaust -- or subscribes the arrival exactly once, so the step is the
-- single-subscription claim or a triviality, and there is no third
-- shape for the fold above to carry.
--
-- AND THE SWITCH ARM SUBSCRIBES AT THE SCHEDULE ITS CUT RETURNED rather
-- than at the one it was handed, which is why the charge is transported
-- rather than read straight off.  The cut edits the live set and the
-- registry and leaves the telescope alone, so the reading taken at the
-- cut's schedule IS the reading at this one -- and that is a fact about
-- the cut, not an accident of the caller.
thruConsume-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (id : Id)
  (now : Tick) (o : Val Γ (obs u)) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S → (sizeᵉ o ≤ᵇ B) ≡ true →
  valsSz? (iterSize S (layᵉ o + slotsSize (Sched.slots sched)) B)
    (proj₁ (thruConsume sf op nid κ id now o sched st)) ≡ true
thruConsume-sz {u = u} sf mergeAllᵒ nid κ id now o sched st S B 2≤S ho
  with lookupNode nid (EvalSt.nodes st)
... | nothing               = refl
... | just (scan-st _)      = refl
... | just (take-st _)      = refl
... | just (switch-st _ _)  = refl
... | just (exhaust-st _ _) = refl
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ u
...   | no _ = refl
...   | yes refl with hasRoom lim act
...     | false = refl
...     | true  =
  subscribeInner-sz sf mergeAllᵒ nid κ id now o sched st S B 2≤S ho

thruConsume-sz sf switchᵒ nid κ id now o sched st S B 2≤S ho
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = refl
... | just (scan-st _)           = refl
... | just (take-st _)           = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (exhaust-st _ _)      = refl
... | just (switch-st cur od) =
  subst (λ z → valsSz? (iterSize S (layᵉ o + slotsSize z) B)
                 (proj₁ (proj₂ (subscribeInner sf switchᵒ nid κ id now o
                    (proj₁ (proj₂ (switchKill cur sched st)))
                    (proj₂ (proj₂ (switchKill cur sched st))))))
                 ≡ true)
        (switchKill-slots cur sched st)
        (subscribeInner-sz sf switchᵒ nid κ id now o
           (proj₁ (proj₂ (switchKill cur sched st)))
           (proj₂ (proj₂ (switchKill cur sched st))) S B 2≤S ho)

thruConsume-sz sf exhaustᵒ nid κ id now o sched st S B 2≤S ho
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = refl
... | just (scan-st _)           = refl
... | just (take-st _)           = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st true od)  = refl
... | just (exhaust-st false od) =
  subscribeInner-sz sf exhaustᵒ nid κ id now o sched st S B 2≤S ho

-- THE WALK OVER WHAT ARRIVED, WHICH IS THE DRAIN'S FOLD ONE DOOR OVER.
-- The head is the step above read at its own arrival's layers and the
-- tail is this walk at the schedule the step handed on, and each widens
-- onto the max the arrivals join to -- so the charge is a join and not a
-- sum, exactly as the queue's is, and for the same reason: every
-- delivered value comes out of ONE arrival's run.
--
-- AND THE TELESCOPE SURVIVES THE FOLD because a consumption hands on
-- the slots it was handed, whichever arm it took.  That is what lets a
-- charge keyed on the telescope be stated once at the head schedule
-- rather than re-read per entry -- and it is the same property the
-- queue's fold rests on, which is why the two arms' counts agree in
-- shape rather than merely in size.
thruWalk-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t) (id : Id)
  (now : Tick) (vals : List (Val Γ (obs u))) (sched : Sched Γ)
  (st : EvalSt e) (S B : ℕ) → 2 ≤ S → valsSz? B vals ≡ true →
  valsSz? (iterSize S (layᵛˢ (obs u) vals + slotsSize (Sched.slots sched)) B)
    (proj₁ (thruWalk sf op nid κ id now vals sched st)) ≡ true
thruWalk-sz sf op nid κ id now [] sched st S B 2≤S hv = refl
thruWalk-sz {u = u} sf op nid κ id now (o ∷ os) sched st S B 2≤S hv =
  all-++-intro
    (λ v → sizeᵛ u v ≤ᵇ iterSize S (layᵛˢ (obs u) (o ∷ os)
                                     + slotsSize (Sched.slots sched)) B)
    vs vs′ headFits tailFits
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  sl = Sched.slots sched

  r₁ = thruConsume sf op nid κ id now o sched st
  vs = proj₁ r₁
  sched₁ = proj₁ (proj₂ (proj₂ r₁))
  st₁ = proj₂ (proj₂ (proj₂ r₁))

  vs′ = proj₁ (thruWalk sf op nid κ id now os sched₁ st₁)

  headFits : valsSz? (iterSize S (layᵛˢ (obs u) (o ∷ os) + slotsSize sl) B)
               vs ≡ true
  headFits =
    valsSz?-mono (iterSize S (layᵉ o + slotsSize sl) B)
      (iterSize S (layᵛˢ (obs u) (o ∷ os) + slotsSize sl) B) vs
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl) (m≤m⊔n (layᵉ o) (layᵛˢ (obs u) os))))
      (thruConsume-sz sf op nid κ id now o sched st S B 2≤S (∧-trueˡ hv))

  tailAtSched : valsSz? (iterSize S (layᵛˢ (obs u) os + slotsSize sl) B)
                  vs′ ≡ true
  tailAtSched =
    subst (λ z → valsSz? (iterSize S (layᵛˢ (obs u) os + slotsSize z) B)
                   vs′ ≡ true)
          (thruConsume-slots sf op nid κ id now o sched st)
          (thruWalk-sz sf op nid κ id now os sched₁ st₁ S B 2≤S (∧-trueʳ hv))

  tailFits : valsSz? (iterSize S (layᵛˢ (obs u) (o ∷ os) + slotsSize sl) B)
               vs′ ≡ true
  tailFits =
    valsSz?-mono (iterSize S (layᵛˢ (obs u) os + slotsSize sl) B)
      (iterSize S (layᵛˢ (obs u) (o ∷ os) + slotsSize sl) B) vs′
      (iterSize-mono-count S B 1≤S
        (+-monoˡ-≤ (slotsSize sl) (m≤n⊔m (layᵉ o) (layᵛˢ (obs u) os))))
      tailAtSched

-- THE FRAME THAT RUNS AN ARRIVING SUBSCRIPTION, READ AT WHAT ARRIVES.
-- Its program is in its own argument list, so the count takes the
-- arrivals' layers plus the telescope standing behind whatever they
-- name -- and the whole arm is the walk above, since the wrap that
-- closes the frame edits the node cell and never the values.
--
-- AND THE NODE TABLE IS NOT A PREMISE, which is what the fold bought
-- here as it did at the queue: every arrival is consumed at the state
-- its predecessor left, so a premise about the table would be owed
-- again per entry and the conclusion would climb a rung per arrival
-- rather than stand at the join.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross.stepFrame-sz-outer-absurd`
--   -- one rung, which is the charge this reading replaces.
-- REFUTED: `Refuted.Frame-Step-Size-Slot.stepFrame-sz-outer-own-absurd`
--   -- the arm charged the arriving values ALONE, at an observable
--   that names a shared slot.  The second row puts one more rung
--   behind the slot and moves the cap with it: the emission doubles,
--   the rung it is measured against grows quadratically, and that
--   count does not move at all.
stepFrame-sz-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S (szCount (Sched.slots sched) (EvalSt.nodes st)
                        (thru-outer {Γ = Γ} {u = u} op nid) vals) B)
    (proj₁ (stepFrame sf id now (thru-outer op nid) path vals fin
              sched st)) ≡ true
stepFrame-sz-outer {u = u} sf id now op nid path vals fin sched st S B 2≤S hv =
  subst (λ ws → valsSz? (iterSize S (layᵛˢ (obs u) vals
                                      + slotsSize (Sched.slots sched)) B)
                  ws ≡ true)
        (sym (thruWrap-vals op nid fin
               (thruWalk sf op nid path id now vals sched st)))
        (thruWalk-sz sf op nid path id now vals sched st S B 2≤S hv)

-- ONE FRAME'S SIZE STEP, SPLIT BY KIND, over the store the frame reads.
-- Three arms are bodies here and the two that cross into an inner
-- subscription are leaves: a take passes a prefix of what arrived, a
-- map substitutes independently, and the scan -- the arm every
-- unconditional reading of this statement died at -- is `scanVals-size`
-- read at the very bound the arriving values stand at, its accumulator
-- premise met by the store reading.
--
-- THE STORE PREMISE IS A RESTATEMENT AND IT IS EARNED, not a hypothesis
-- taken because a call site happens to offer one: the unconditional
-- form is refuted below, so the conditioned form is the true statement
-- replacing a false one rather than a weaker statement replacing a
-- strong one.  And the frame's OWN size reading is not among the
-- premises, which is what the count bought: once the ladder climbs by
-- the function's node count rather than by one, nothing has to know
-- that count is small.
stepFrame-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  valsSz? (iterSize S (szCount (Sched.slots sched) (EvalSt.nodes st) f vals) B)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

stepFrame-sz sf id now (map-f fn) path vals fin sched st S B 2≤S hns hv =
  mapSz S B (≤-trans (s≤s z≤n) 2≤S) fn vals hv

stepFrame-sz {u = u} sf id now (scan-f fn nid) path vals fin sched st S B 2≤S hns hv
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-sz B nid (EvalSt.nodes st) hns
... | nothing                   | _ = refl
... | just (take-st _)          | _ = refl
... | just (mergeAll-st _ _ _ _) | _ = refl
... | just (switch-st _ _)      | _ = refl
... | just (exhaust-st _ _)     | _ = refl
... | just (scan-st {w} ac)     | hb with w ≟ᵗ u
...   | no _    = refl
...   | yes refl =
  proj₁ (scanVals-size S B 2≤S fn ac vals (≤ᵇ⇒≤ _ B (T-to hb)) hv)

stepFrame-sz sf id now (take-f nid) path vals fin sched st S B 2≤S hns hv
  with lookupNode nid (EvalSt.nodes st)
... | nothing                   = refl
... | just (scan-st _)          = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)      = refl
... | just (exhaust-st _ _)     = refl
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | true  = takeSz S B (≤-trans (s≤s z≤n) 2≤S) k vals hv
...   | false = takeSz S B (≤-trans (s≤s z≤n) 2≤S) k vals hv

stepFrame-sz sf id now (from-inner op allNid inst) path vals fin sched st S B 2≤S hns hv =
  stepFrame-sz-inner sf id now op allNid inst path vals fin sched st S B
    2≤S hns hv

stepFrame-sz sf id now (thru-outer op nid) path vals fin sched st S B 2≤S hns hv =
  stepFrame-sz-outer sf id now op nid path vals fin sched st S B 2≤S hv

-- WIDENING A STORE READING IS FREE UPWARD, which is what lets one
-- premise serve every level above the one it was taken at.
nodesSz-widen : ∀ {n} {Γ : Ctx n} {B B′ : ℕ} → B ≤ B′ →
  (ns : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) ns ≡ true →
  all (λ kv → boundedNode B′ (proj₂ kv)) ns ≡ true
nodesSz-widen le ns h =
  all-impl _ _ (λ kv → boundedNode-widen le (proj₂ kv)) ns h

-- ONE CLIMB OF THE STORE READING, named because a `where` reaches only
-- the last clause of a `with` block and every kind that leaves the table
-- alone needs the same widening.
stepWiden : ∀ {n} {Γ : Ctx n} (S B k : ℕ) → 2 ≤ S →
  (ns : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode B (proj₂ kv)) ns ≡ true →
  all (λ kv → boundedNode (iterSize S k B) (proj₂ kv)) ns ≡ true
stepWiden S B k 2≤S ns h =
  nodesSz-widen (iterSize-infl S (≤-trans (s≤s z≤n) 2≤S) k B) ns h

-- THE WRAP THAT CLOSES A `thru-outer` FRAME CANNOT MOVE THE STORE
-- READING.  Whichever door it is, it rewrites exactly the cell it just
-- read and changes only that cell's own-done flag -- and no flag is
-- among what the reading prices, which is a scan's accumulator and a
-- merge queue's entries.  So the level the fold below arrives at is
-- the level the frame leaves, and the arm's whole content is the fold.
thruWrap-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (op : AllOp) (nid : NodeId) (fin : Bool) (M : ℕ)
  (r : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂ r)))) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (thruWrap op nid fin r))))))
    ≡ true
thruWrap-sz-store op nid false M (vs , bs , sched , st) h = h
thruWrap-sz-store mergeAllᵒ nid true M (vs , bs , sched , st) h
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-sz M nid (EvalSt.nodes st) h
... | just (mergeAll-st lim act q od) | hb =
      setNode-bounded M nid (mergeAll-st lim act q true) (EvalSt.nodes st) hb h
... | just (scan-st _)      | _ = h
... | just (take-st _)      | _ = h
... | just (switch-st _ _)  | _ = h
... | just (exhaust-st _ _) | _ = h
... | nothing               | _ = h
thruWrap-sz-store switchᵒ nid true M (vs , bs , sched , st) h
  with lookupNode nid (EvalSt.nodes st)
... | just (switch-st cur od)    =
      setNode-bounded M nid (switch-st cur true) (EvalSt.nodes st) refl h
... | just (scan-st _)           = h
... | just (take-st _)           = h
... | just (mergeAll-st _ _ _ _) = h
... | just (exhaust-st _ _)      = h
... | nothing                    = h
thruWrap-sz-store exhaustᵒ nid true M (vs , bs , sched , st) h
  with lookupNode nid (EvalSt.nodes st)
... | just (exhaust-st act od)   =
      setNode-bounded M nid (exhaust-st act true) (EvalSt.nodes st) refl h
... | just (scan-st _)           = h
... | just (take-st _)           = h
... | just (mergeAll-st _ _ _ _) = h
... | just (switch-st _ _)       = h
... | nothing                    = h

postulate
  -- WHAT ONE SUBSCRIPTION WRITES INTO THE TABLE, which is what every
  -- store arm reduces to once its own door and its own gas are taken
  -- off it.  The cells the subscription installs hold that run's
  -- emission -- reified, so priced by the program's LAYERS -- with the
  -- telescope beside them for the slots the run connects.
  --
  -- AND IT IS STATED AT A LEVEL THE PROGRAM ALREADY REACHES, NOT AS A
  -- CLIMB FROM THE PREMISE'S OWN.  That is what makes it composable
  -- across a burst the count joins by MAX: a statement handing back
  -- one rung per subscription would compound over the fold, and the
  -- join says the subscriptions do not compound.  So the level is
  -- carried as a parameter with the program's charge under it, and
  -- every consumer's job is to show the level is never raised rather
  -- than to add rungs up.
  --
  -- AND NOTHING IS CHARGED FOR THE PATH, which is sound rather than an
  -- omission: `κ` is a CONTINUATION and not something this call walks.
  -- What the subscription emits is handed back UP to whoever asked for
  -- it, and the path is spent only as the decoration a later crossing
  -- subscribes its own arrival under -- where that arrival's layers
  -- pay for what it writes.  No node state holds a path either, so
  -- nothing the reading prices can grow with one.  What it does cost is
  -- that a `κ` no ancestor ever built is admitted at the same level,
  -- since the charge is bought by the subscribed program alone.
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
  -- PROBED: `Probed.Parked-Slot-Store` at the program whose OWN layers
  --   are nought -- a bare reference to a shared slot -- so the first
  --   summand contributes nothing and the telescope carries the whole
  --   climb.  Read at two depths behind the same reference, since one
  --   more rung doubles the emission while moving the charge by four
  --   units of slot syntax; the telescope-free reading fails at both.
  --   So the summand REACHES the written table, never that its size is
  --   right: one slot, one queue entry, and the merging door alone.
  subscribeE-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sl : Slots Γ) (g : Gas) (o : Closed Γ u) (κ : Path Γ u t)
    (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
    Sched.slots sched ≡ sl →
    iterSize S (layᵉ o + slotsSize sl) B ≤ M →
    all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    (sizeᵉ o ≤ᵇ B) ≡ true →
    all (λ kv → boundedNode M (proj₂ kv))
        (EvalSt.nodes (proj₂ (proj₂ (subscribeE g o κ id now sched st))))
      ≡ true

-- ONE ARRIVAL SUBSCRIBED, WHICH IS THE STORE SIDE'S LAST DOOR.  A
-- crossing frame mints the inner's exit-frame instance and then does
-- exactly one thing with it, and which of the two is decided by gas
-- alone: with none, the arrival is answered by a dry close and the
-- table is handed back untouched, so the premise IS the conclusion;
-- with some, it is the general descent entered at the caller's path
-- under a `from-inner` decoration, and the minted instance moves only
-- the scheduler's node counter, which the reading does not price.
--
-- SO THE DECORATION IS FREE AND THE ARRIVAL'S CHARGE IS UNCHANGED:
-- `layᵉ` reads the program, not the path it is subscribed at, and the
-- record update touches no slot -- which is what lets the level cross
-- this door verbatim rather than climbing a rung at it.
subscribeInner-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (sf : Gas) (op : AllOp) (allNid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (layᵉ o + slotsSize sl) B ≤ M →
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

-- THE MERGE DOOR'S BUMP IS INVISIBLE TO THE READING.  It rewrites the
-- cell it read and moves only the live count, which is not among what
-- the reading prices -- so the cell it writes back is bounded by the
-- very receipt the lookup handed out.
mergeAllBump-bounded : ∀ {n} {Γ : Ctx n} (M : ℕ) (nid : NodeId) (done : Bool)
  (ns : List (NodeId × NodeState Γ)) →
  all (λ kv → boundedNode M (proj₂ kv)) ns ≡ true →
  all (λ kv → boundedNode M (proj₂ kv)) (mergeAllBump nid done ns) ≡ true
mergeAllBump-bounded M nid done ns h
  with lookupNode nid ns | lookupNode-sz M nid ns h
... | just (mergeAll-st lim act q od) | hb =
      setNode-bounded M nid
        (mergeAll-st lim (if done then act else suc act) q od) ns hb h
... | just (scan-st _)      | _ = h
... | just (take-st _)      | _ = h
... | just (switch-st _ _)  | _ = h
... | just (exhaust-st _ _) | _ = h
... | nothing               | _ = h

-- ONE ARRIVAL CONSUMED, WHICH IS THE STORE SIDE'S DOOR DISPATCH.  Every
-- arm either leaves the table alone -- a cell of the wrong kind or the
-- wrong payload type, a busy exhaust -- or subscribes the arrival
-- exactly once and rewrites the cell it read, and every one of those
-- rewrites is invisible to the reading: a merge's bump moves the live
-- count, a switch stores which inner it now holds, an exhaust its busy
-- flag, and none of the three is priced.
--
-- AND THE ONE DOOR THAT WRITES WITHOUT SUBSCRIBING PARKS THE ARRIVAL,
-- which costs the level nothing at all: the queue gains a term the
-- value premise already bounds, and the level stands above that bound
-- because it stands above `B`.
--
-- AND THE SWITCH ARM SUBSCRIBES AT THE STATE ITS CUT RETURNED rather
-- than at the one it was handed, so both premises are transported
-- across the cut.  The cut moves no node and leaves the telescope
-- alone, and that is a fact about the cut rather than an accident of
-- this caller.
thruConsume-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (sf : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs u))
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (layᵉ o + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (sizeᵛ (obs u) o ≤ᵇ B) ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂
        (thruConsume sf op nid κ id now o sched st)))))
    ≡ true

thruConsume-sz-store {u = u} sl sf mergeAllᵒ nid κ id now o sched st S B M
                     2≤S slEq le hns ho
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-sz M nid (EvalSt.nodes st) hns
... | nothing               | _ = hns
... | just (scan-st _)      | _ = hns
... | just (take-st _)      | _ = hns
... | just (switch-st _ _)  | _ = hns
... | just (exhaust-st _ _) | _ = hns
... | just (mergeAll-st {w} lim act q od) | hb with w ≟ᵗ u
...   | no _ = hns
...   | yes refl with hasRoom lim act
...     | true =
  mergeAllBump-bounded M nid
    (proj₁ (proj₂ (proj₂ (proj₂
      (subscribeInner sf mergeAllᵒ nid κ id now o sched st)))))
    (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (subscribeInner sf mergeAllᵒ nid κ id now o sched st)))))))
    (subscribeInner-sz-store sl sf mergeAllᵒ nid κ id now o sched st
       S B M 2≤S slEq le hns ho)
...     | false =
  setNode-bounded M nid (mergeAll-st lim act (q ++ o ∷ []) od)
    (EvalSt.nodes st)
    (all-++-intro (λ o′ → sizeᵉ o′ ≤ᵇ M) q (o ∷ []) hb
      (∧-intro
        (≤ᵇ-widen (sizeᵉ o)
          (≤-trans (iterSize-infl S (≤-trans (s≤s z≤n) 2≤S)
                      (layᵉ o + slotsSize sl) B)
                   le)
          ho)
        refl))
    hns

thruConsume-sz-store sl sf switchᵒ nid κ id now o sched st S B M
                     2≤S slEq le hns ho
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = hns
... | just (scan-st _)           = hns
... | just (take-st _)           = hns
... | just (mergeAll-st _ _ _ _) = hns
... | just (exhaust-st _ _)      = hns
... | just (switch-st cur od) =
  setNode-bounded M nid _
    (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (subscribeInner sf switchᵒ nid κ id now o
         (proj₁ (proj₂ (switchKill cur sched st)))
         (proj₂ (proj₂ (switchKill cur sched st))))))))))
    refl
    (subscribeInner-sz-store sl sf switchᵒ nid κ id now o
       (proj₁ (proj₂ (switchKill cur sched st)))
       (proj₂ (proj₂ (switchKill cur sched st))) S B M 2≤S
       (trans (switchKill-slots cur sched st) slEq) le
       (subst (λ ns → all (λ kv → boundedNode M (proj₂ kv)) ns ≡ true)
              (sym (switchKill-nodes cur sched st)) hns)
       ho)

thruConsume-sz-store sl sf exhaustᵒ nid κ id now o sched st S B M
                     2≤S slEq le hns ho
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = hns
... | just (scan-st _)           = hns
... | just (take-st _)           = hns
... | just (mergeAll-st _ _ _ _) = hns
... | just (switch-st _ _)       = hns
... | just (exhaust-st true od)  = hns
... | just (exhaust-st false od) =
  setNode-bounded M nid _
    (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
      (subscribeInner sf exhaustᵒ nid κ id now o sched st)))))))
    refl
    (subscribeInner-sz-store sl sf exhaustᵒ nid κ id now o sched st
       S B M 2≤S slEq le hns ho)

-- THE FOLD OVER THE BURST, CARRYING A LEVEL RATHER THAN CLIMBING ONE.
-- Each arrival is consumed at the state its predecessor left, so an
-- induction that gave the table a rung per entry would end at the
-- arrivals' SUM -- and the count joins them by max.  What is carried
-- instead is one level high enough for the whole burst: the head's own
-- charge sits under the join, so the leaf above leaves the level where
-- it found it, and the tail inherits the same level unchanged.
--
-- AND THE TELESCOPE SURVIVES THE FOLD, which is what lets the level be
-- named once at the head schedule: a consumption hands on the slots it
-- was handed, whichever door it took.
thruWalk-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sl : Slots Γ) (sf : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
  (id : Id) (now : Tick) (vals : List (Val Γ (obs u)))
  (sched : Sched Γ) (st : EvalSt e) (S B M : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (layᵛˢ (obs u) vals + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂
        (thruWalk sf op nid κ id now vals sched st)))))
    ≡ true
thruWalk-sz-store sl sf op nid κ id now [] sched st S B M 2≤S slEq le hns hv = hns
thruWalk-sz-store {u = u} sl sf op nid κ id now (o ∷ os) sched st S B M
                  2≤S slEq le hns hv =
  thruWalk-sz-store sl sf op nid κ id now os sched₁ st₁ S B M 2≤S
    (trans (thruConsume-slots sf op nid κ id now o sched st) slEq)
    tailLe headBound (∧-trueʳ hv)
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  r₁ = thruConsume sf op nid κ id now o sched st
  sched₁ = proj₁ (proj₂ (proj₂ r₁))
  st₁ = proj₂ (proj₂ (proj₂ r₁))

  headBound : all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st₁) ≡ true
  headBound =
    thruConsume-sz-store sl sf op nid κ id now o sched st S B M 2≤S slEq
      (≤-trans (iterSize-mono-count S B 1≤S
                 (+-monoˡ-≤ (slotsSize sl)
                   (m≤m⊔n (layᵉ o) (layᵛˢ (obs u) os))))
               le)
      hns (∧-trueˡ hv)

  tailLe : iterSize S (layᵛˢ (obs u) os + slotsSize sl) B ≤ M
  tailLe =
    ≤-trans (iterSize-mono-count S B 1≤S
              (+-monoˡ-≤ (slotsSize sl)
                (m≤n⊔m (layᵉ o) (layᵛˢ (obs u) os))))
            le

-- THE OUTER ARM'S STORE HALF, ASSEMBLED.  Its count is the object the
-- value half spends -- the arrivals' layers joined by max, plus the
-- telescope -- and the arm is the fold under the wrap, so the level the
-- conclusion names is exactly the level the fold is asked to hold.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross-Store.stepFrame-sz-store-outer-absurd`
--   -- one rung, which is the charge this reading replaces.
stepFrame-sz-store-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
  (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode
                (iterSize S (szCount (Sched.slots sched) (EvalSt.nodes st)
                              (thru-outer {Γ = Γ} {u = u} op nid) vals) B)
                (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (thru-outer op nid)
                                       path vals fin sched st))))))
    ≡ true
stepFrame-sz-store-outer {u = u} sf id now op nid path vals fin sched st S B
                         2≤S hns hv =
  thruWrap-sz-store op nid fin
    (iterSize S (layᵛˢ (obs u) vals + slotsSize (Sched.slots sched)) B)
    (thruWalk sf op nid path id now vals sched st)
    (thruWalk-sz-store (Sched.slots sched) sf op nid path id now vals sched st
      S B (iterSize S (layᵛˢ (obs u) vals + slotsSize (Sched.slots sched)) B)
      2≤S refl ≤-refl
      (stepWiden S B (layᵛˢ (obs u) vals + slotsSize (Sched.slots sched))
        2≤S (EvalSt.nodes st) hns)
      hv)

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
  iterSize S (layᵛˢ (obs s) q + slotsSize sl) B ≤ M →
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
                   (m≤m⊔n (layᵉ o) (layᵛˢ (obs s) q))))
               le)
      hns (∧-trueˡ hq)

  tailLe : iterSize S (layᵛˢ (obs s) q + slotsSize sl) B ≤ M
  tailLe =
    ≤-trans (iterSize-mono-count S B 1≤S
              (+-monoˡ-≤ (slotsSize sl)
                (m≤n⊔m (layᵉ o) (layᵛˢ (obs s) q))))
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

-- THE FINISH IS THE DISPATCH AND ONE DRAIN, READ AT THE TABLE.  Every
-- arm but the merge leaves the table as it found it or writes a flag
-- the reading does not price -- a switch releasing the inner it held,
-- an exhaust clearing its busy bit -- so the whole arm's content is
-- the drain, and the cell written back over it carries two things: the
-- table the drain threaded and the entries it declined.
--
-- AND THE CELL IS SCRUTINISED BY THE CALLER, not here, which is what
-- lets `L` be the cell's own parked depth while the level is that plus
-- the telescope: the frame above reads the cell once and hands both
-- readings of it down, and neither the cell nor the arrivals mention
-- the slots.
innerFinish-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sl : Slots Γ) (sf : Gas) (op : AllOp) (allNid inst : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (vals : List (Val Γ s))
  (sched : Sched Γ) (st : EvalSt e) (S B M L : ℕ) → 2 ≤ S →
  Sched.slots sched ≡ sl →
  iterSize S (L + slotsSize sl) B ≤ M →
  all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  (mns : Maybe (NodeState Γ)) → NodeLay L mns → NodeSz B mns →
  all (λ kv → boundedNode M (proj₂ kv))
      (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂
        (innerFinish sf op allNid inst κ id now vals sched st mns))))))
    ≡ true

innerFinish-sz-store sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns nothing hL hb = hns
innerFinish-sz-store sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (scan-st _)) hL hb = hns
innerFinish-sz-store sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (take-st _)) hL hb = hns
innerFinish-sz-store sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (switch-st _ _)) hL hb = hns
innerFinish-sz-store sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (exhaust-st _ _)) hL hb = hns
innerFinish-sz-store {s = s} sl sf mergeAllᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (mergeAll-st {w} lim act q od)) hL hb
  with w ≟ᵗ s
... | no  _    = hns
... | yes refl =
  setNode-bounded M allNid (mergeAll-st lim act′ q′ od) (EvalSt.nodes st′)
    qAtM drained
  where
  1≤S : 1 ≤ S
  1≤S = ≤-trans (s≤s z≤n) 2≤S

  B≤M : B ≤ M
  B≤M = ≤-trans (iterSize-infl S 1≤S (L + slotsSize sl) B) le

  r = mergeAllDrain sf allNid κ id now lim (pred act) q sched st
  act′ = proj₁ (proj₂ (proj₂ r))
  q′ = proj₁ (proj₂ (proj₂ (proj₂ r)))
  st′ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r))))

  drained : all (λ kv → boundedNode M (proj₂ kv)) (EvalSt.nodes st′) ≡ true
  drained =
    mergeAllDrain-sz-store sl sf allNid κ id now lim (pred act) q sched st
      S B M 2≤S slEq
      (subst (λ z → iterSize S (z + slotsSize sl) B ≤ M) hL le)
      hns hb

  qAtM : boundedNode M (mergeAll-st lim act′ q′ od) ≡ true
  qAtM =
    all-impl (λ o → sizeᵉ o ≤ᵇ B) (λ o → sizeᵉ o ≤ᵇ M)
      (λ o → ≤ᵇ-widen (sizeᵉ o) B≤M) q′
      (mergeAllDrain-queue sf allNid κ id now lim (pred act) q sched st B hb)

innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns nothing hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (scan-st _)) hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (take-st _)) hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (mergeAll-st _ _ _ _)) hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (exhaust-st _ _)) hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (switch-st nothing _)) hL hb = hns
innerFinish-sz-store sl sf switchᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (switch-st (just c₀) od)) hL hb
  with c₀ ≡ᵇ inst
... | true  =
  setNode-bounded M allNid (switch-st nothing od) (EvalSt.nodes st) refl hns
... | false = hns

innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns nothing hL hb = hns
innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (scan-st _)) hL hb = hns
innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (take-st _)) hL hb = hns
innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (mergeAll-st _ _ _ _)) hL hb = hns
innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (switch-st _ _)) hL hb = hns
innerFinish-sz-store sl sf exhaustᵒ allNid inst κ id now vals sched st
  S B M L 2≤S slEq le hns (just (exhaust-st act od)) hL hb =
  setNode-bounded M allNid (exhaust-st false od) (EvalSt.nodes st) refl hns

-- THE INNER ARM'S STORE HALF, ASSEMBLED.  It is the dispatch above
-- plus two gates: a frame that is not finishing, and one whose
-- instance still has a live registration under it, leave the table
-- untouched, so only the third gate reaches it at all.  The level the
-- conclusion names is exactly the level the finish is asked to hold,
-- and the cell is read ONCE and its two readings -- what it has parked
-- and what it is bounded by -- handed down together.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross-Store.stepFrame-sz-store-inner-absurd`
--   -- one rung, which is the charge this reading replaces.
stepFrame-sz-store-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode
                (iterSize S (parkedLayAt allNid (EvalSt.nodes st)
                              + slotsSize (Sched.slots sched)) B)
                (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                                       path vals fin sched st))))))
    ≡ true
stepFrame-sz-store-inner sf id now op allNid inst path vals false sched st
                         S B 2≤S hns hv =
  stepWiden S B (parkedLayAt allNid (EvalSt.nodes st)
                  + slotsSize (Sched.slots sched)) 2≤S (EvalSt.nodes st) hns
stepFrame-sz-store-inner sf id now op allNid inst path vals true sched st
                         S B 2≤S hns hv
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  =
  stepWiden S B (parkedLayAt allNid (EvalSt.nodes st)
                  + slotsSize (Sched.slots sched)) 2≤S (EvalSt.nodes st) hns
... | false =
  innerFinish-sz-store (Sched.slots sched) sf op allNid inst path id now vals
    sched st S B
    (iterSize S (parkedLayAt allNid (EvalSt.nodes st)
                  + slotsSize (Sched.slots sched)) B)
    (parkedLayAt allNid (EvalSt.nodes st)) 2≤S refl ≤-refl
    (stepWiden S B (parkedLayAt allNid (EvalSt.nodes st)
                     + slotsSize (Sched.slots sched)) 2≤S (EvalSt.nodes st) hns)
    (lookupNode allNid (EvalSt.nodes st))
    (parkedLayAt-lookup allNid (EvalSt.nodes st))
    (lookupNode-sz B allNid (EvalSt.nodes st) hns)

-- THE STORE SIDE OF THE SAME STEP, and the reason the walk can carry
-- its own store premise rather than importing one: at the three arms
-- that compute, a frame writes at most the entry it read, and the only
-- entry whose content GREW is the scan's, which `scanVals-size` prices
-- at the very level the outputs landed at.  Everything else either
-- leaves the table alone or writes a take counter, which the reading is
-- blind to.  The two crossing arms are NOT in that description: their
-- subscription installs the inner program's own nodes, so the table
-- the conclusion is about is not the table the premise read.
stepFrame-sz-store : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (S B : ℕ) → 2 ≤ S →
  all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
  valsSz? B vals ≡ true →
  all (λ kv → boundedNode (iterSize S (szCount (Sched.slots sched) (EvalSt.nodes st) f vals) B)
                (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
    ≡ true

stepFrame-sz-store sf id now (map-f fn) path vals fin sched st S B 2≤S hns hv =
  stepWiden S B (sizeᵗ fn) 2≤S (EvalSt.nodes st) hns

stepFrame-sz-store {u = u} sf id now (scan-f fn nid) path vals fin sched st S B 2≤S hns hv
  with lookupNode nid (EvalSt.nodes st)
     | lookupNode-sz B nid (EvalSt.nodes st) hns
... | nothing                    | _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
... | just (take-st _)           | _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
... | just (mergeAll-st _ _ _ _) | _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
... | just (switch-st _ _)       | _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
... | just (exhaust-st _ _)      | _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
... | just (scan-st {w} ac)      | hb with w ≟ᵗ u
...   | no _ =
  stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns
...   | yes refl =
  setNode-bounded _ nid (scan-st (proj₂ (scanVals fn ac vals))) (EvalSt.nodes st)
    (T⇒≡true _ (≤⇒≤ᵇ (proj₂ (scanVals-size S B 2≤S fn ac vals
                              (≤ᵇ⇒≤ _ B (T-to hb)) hv))))
    (stepWiden S B (length vals * suc (sizeᵗ fn)) 2≤S (EvalSt.nodes st) hns)

stepFrame-sz-store sf id now (take-f nid) path vals fin sched st S B 2≤S hns hv
  with lookupNode nid (EvalSt.nodes st)
... | nothing                    = stepWiden S B 1 2≤S (EvalSt.nodes st) hns
... | just (scan-st _)           = stepWiden S B 1 2≤S (EvalSt.nodes st) hns
... | just (mergeAll-st _ _ _ _) = stepWiden S B 1 2≤S (EvalSt.nodes st) hns
... | just (switch-st _ _)       = stepWiden S B 1 2≤S (EvalSt.nodes st) hns
... | just (exhaust-st _ _)      = stepWiden S B 1 2≤S (EvalSt.nodes st) hns
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | true  = setNode-bounded _ nid (take-st 0) (EvalSt.nodes st) refl
                  (stepWiden S B 1 2≤S (EvalSt.nodes st) hns)
...   | false = setNode-bounded _ nid (take-st (proj₁ (proj₂ (takeVals k vals))))
                  (EvalSt.nodes st) refl
                  (stepWiden S B 1 2≤S (EvalSt.nodes st) hns)

stepFrame-sz-store sf id now (from-inner op allNid inst) path vals fin sched st S B
                   2≤S hns hv =
  stepFrame-sz-store-inner sf id now op allNid inst path vals fin sched st S B
    2≤S hns hv

stepFrame-sz-store sf id now (thru-outer op nid) path vals fin sched st S B
                   2≤S hns hv =
  stepFrame-sz-store-outer sf id now op nid path vals fin sched st S B
    2≤S hns hv

-- WHAT ONE FRAME CAN CHARGE, IN THE TWO QUANTITIES A ROUND ALREADY
-- CAPS.  The scan is the only kind whose count reads the burst, so the
-- uniform ceiling is a width times a size -- and the width is exactly
-- what `burstsOK` carries along a path, frame by frame, in the shape
-- this walk carries its size receipt.
--
-- AND THIS IS WHERE THE CROSSING ARMS' REPAIR HAS TO LAND, RATHER
-- THAN AT THE FRAME.  Charging a crossing frame the size of what it
-- subscribes is plausible one line up; it is impossible here.  Both
-- quantities the ceiling is denominated in read the PROGRAM, the
-- frame's own size test is `true` on a crossing arm and so ties
-- nothing, and the arriving observable is a runtime value bounded
-- only by the LEVEL.  The ceiling is quadratic in the cap while the
-- level is the caps recurrence, so the gap widens with the cap
-- instead of closing.  A count that reads what runs therefore forces
-- the frame ceiling itself to move, and with it the level budget the
-- consumer concludes at.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross-Count` -- the size-reading
--   count against this ceiling, at the level one rung above the cap
--   and the width the consumer passes.

-- AND THE DENOMINATION THAT SURVIVES IS ALREADY PROVEN ONE FACE OVER,
-- which is why the crossing arms are EXCLUDED here rather than charged
-- a constant.  The burst face charges a subscription its own `sizeᵉ` --
-- literally `suc (sizeᵉ o)` as the ops count handed to `opIterD` -- and
-- prices that against the LEVEL rather than the cap:
-- `opIterD-dominated-at` asks only `m ≤ sizeAt S J` and still lands the
-- climb inside `lvls S W d J (dCapᶜ S W R d (4 + k) J)`.  A ceiling
-- `W * (suc S ⊔ sizeAt S J)` pays every arm of `szCount` outright, the
-- crossing ones by the second branch.  What blocks it is not this
-- ceiling but the LEDGER that spends it: the consumer's budget premise
-- is LINEAR in the path length, one fixed `Ch` per frame, and a charge
-- that grows with the level cannot be written as a multiple of any
-- level-free quantity.  So the arms are excluded until that ledger is
-- a climb rather than a product.
frameCh : ℕ → ℕ → ℕ
frameCh S W = W * suc S

-- WHICH ARMS THE CEILING CANNOT ADMIT ON THEIR SYNTAX ALONE.  Three
-- frame kinds charge a count read off the PROGRAM -- a function's own
-- size, once or once per arriving value -- and both quantities this
-- ceiling is denominated in are program quantities, so those three are
-- paid outright.  The two crossings charge what they SUBSCRIBE: the
-- outer the arrivals' layers, the inner the layers parked in a table it
-- did not build.  Neither is a function of the frame's syntax, and the
-- frame's own size test is `true` on both, so nothing local ties them.
crossFrame? : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → Bool
crossFrame? (thru-outer _ _)   = true
crossFrame? (from-inner _ _ _) = true
crossFrame? _                  = false

-- THE THREE PROGRAM-READING ARMS AGAINST THE CEILING, and the width
-- premise is what makes the scan arm fit rather than a bound on its
-- burst: the count is a width times a successor size and the ceiling is
-- exactly that product, so the scan arm is an equality and the other two
-- spend the ceiling's own positivity.
--
-- AND THE EXCLUSION IS A REFUTATION'S REPAIR RATHER THAN A WEAKENING:
-- the crossing arm is machine-false under the reading that made this
-- uniform, so the conditioned statement replaces a false one instead of
-- shrinking a true one.
szCount≤ch : ∀ {n} {Γ : Ctx n} {s u} (S W : ℕ) → 1 ≤ W →
  (sl : Slots Γ) (ns : List (NodeId × NodeState Γ)) (f : Frame Γ s u)
  (vals : List (Val Γ s)) →
  crossFrame? f ≡ false →
  frameSz? S f ≡ true → length vals ≤ W →
  szCount sl ns f vals ≤ frameCh S W
szCount≤ch S W 1≤W sl ns (map-f fn) vals _ hf hw =
  ≤-trans (≤ᵇ⇒≤ (sizeᵗ fn) S (T-to hf))
          (≤-trans (≤-trans (m≤m+n S 1) (≤-reflexive (+-comm S 1))) 1≤ch)
  where
  1≤ch : suc S ≤ frameCh S W
  1≤ch = ≤-trans (≤-reflexive (sym (*-identityˡ (suc S)))) (*-mono-≤ 1≤W ≤-refl)
szCount≤ch S W 1≤W sl ns (scan-f fn nid) vals _ hf hw =
  *-mono-≤ hw (s≤s (≤ᵇ⇒≤ (sizeᵗ fn) S (T-to hf)))
szCount≤ch S W 1≤W sl ns (take-f nid) vals _ hf hw =
  ≤-trans (s≤s z≤n) (≤-trans (≤-reflexive (sym (*-identityˡ 1)))
                             (*-mono-≤ 1≤W (s≤s z≤n)))
szCount≤ch S W 1≤W sl ns (from-inner _ _ _) vals () hf hw
szCount≤ch S W 1≤W sl ns (thru-outer _ _)   vals () hf hw

-- AND THE TWO CROSSINGS AT THE SAME CEILING, WHICH IS THE ONE PLACE THE
-- WALK'S LEDGER IS STILL AN ASSERTION.  The telescope half is a program
-- constant and a standing premise on the burst face already reads it
-- against the size cap; what is unheld is the LAYER half.  An outer
-- crossing charges the JOIN of its arrivals' layer counts, so the burst
-- width does not multiply it and the whole question is one value's
-- count; an inner one charges the deepest entry parked at its node,
-- which the frame did not write and the walk's own premises never
-- mention.
--
-- SO WHAT THIS ASKS FOR IS A LAYER BOUND ON A RUNTIME VALUE, and no
-- hypothesis of the walk carries one: the size receipt the walk climbs
-- reads syntax rather than layers, and a reified payload contributes
-- syntax without contributing a layer.  The gap is therefore in the
-- direction that costs nothing to state and everything to source --
-- which is why this is a leaf here rather than an arm of the discharge
-- above it.
--
-- REFUTED: `Refuted.Frame-Step-Size-Cross-Count` -- the same arm with
--   the count reading the arrivals' SIZE instead of their layers, at
--   the level one rung above the cap and the width the consumer
--   passes.  It is what forced the layer denomination this leaf is
--   stated in, and it does not reach this statement.
postulate
  crossCount≤ch : ∀ {n} {Γ : Ctx n} {s u} (S W : ℕ) → 2 ≤ S → 1 ≤ W →
    (sl : Slots Γ) (ns : List (NodeId × NodeState Γ)) (f : Frame Γ s u)
    (vals : List (Val Γ s)) →
    crossFrame? f ≡ true →
    slotsSize sl ≤ S → length vals ≤ W →
    szCount sl ns f vals ≤ frameCh S W

-- ONE FRAME'S CHARGE AGAINST ONE FRAME'S CEILING, uniform in the kind,
-- which is the shape a walk can spend: the walk reaches its frames
-- through a path and has no case analysis of its own to offer.  The
-- split is by the predicate rather than by the constructor, so the two
-- halves stay separately attackable while the consumer sees one fact.
szCountFits : ∀ {n} {Γ : Ctx n} {s u} (S W : ℕ) → 2 ≤ S → 1 ≤ W →
  (sl : Slots Γ) (ns : List (NodeId × NodeState Γ)) (f : Frame Γ s u)
  (vals : List (Val Γ s)) →
  frameSz? S f ≡ true → slotsSize sl ≤ S → length vals ≤ W →
  szCount sl ns f vals ≤ frameCh S W
szCountFits S W 2≤S 1≤W sl ns (map-f fn) vals hf hsl hw =
  szCount≤ch S W 1≤W sl ns (map-f fn) vals refl hf hw
szCountFits S W 2≤S 1≤W sl ns (scan-f fn nid) vals hf hsl hw =
  szCount≤ch S W 1≤W sl ns (scan-f fn nid) vals refl hf hw
szCountFits S W 2≤S 1≤W sl ns (take-f nid) vals hf hsl hw =
  szCount≤ch S W 1≤W sl ns (take-f nid) vals refl hf hw
szCountFits S W 2≤S 1≤W sl ns (from-inner op allNid inst) vals hf hsl hw =
  crossCount≤ch S W 2≤S 1≤W sl ns (from-inner op allNid inst) vals refl hsl hw
szCountFits S W 2≤S 1≤W sl ns (thru-outer op nid) vals hf hsl hw =
  crossCount≤ch S W 2≤S 1≤W sl ns (thru-outer op nid) vals refl hsl hw

-- WHAT THE SIZE WALK CARRIES THAT NO FRAME CAN RE-ESTABLISH, and the
-- shape is the one this face already uses for every walk-scoped
-- hypothesis: a burst WIDTH at each step, because the scan's count
-- reads it and nothing bounds it locally, and -- at a sink alone -- one
-- store reading per admitted registration.  The frame clause is
-- deliberately silent about the store: a frame's own table is proven
-- to survive it, so hypothesising it there would ask the caller for
-- what `stepFrame-sz-store` already delivers.  A fan-out is where the
-- reading genuinely cannot be carried: each admitted chain reads a
-- table the chains before it in the same fan have written, and no
-- receipt taken at the sink survives that.
--
-- AND THE CHARGE READS THE STATE THE FRAME STANDS AT, not the level
-- it stands at, which is what the inner crossing needs and no other
-- kind uses.  What that arm subscribes is parked in the node table, so
-- the table is what has to be handed over; the level is then nowhere
-- in the count, and a frame's charge depends on the walk only through
-- the state the frames above it left.
--
-- AND THE LEVEL RIDES ALONG BECAUSE THE CHARGE IS NOT ONE PER FRAME.
-- A frame costs `szCount` rungs, so the reading a fan-out entry is
-- owed sits at whatever the frames above it climbed to.  A fan-out
-- entry reads a table the entries BEFORE it in the same fan have
-- already written, so its level is not the fan's entry level either;
-- the fold advances by an increment it does not compute, since what
-- one entry's whole run adds to the table is a `foldPath` and not a
-- frame count.
--
-- SO THE LEVEL IS BOUNDED RATHER THAN LEDGERED, WHICH IS WHERE THE
-- CEILING COMES FROM.  Every advance -- the frame's computed one and
-- the fold's existential one alike -- is held under one ABSOLUTE
-- number the predicate takes as a parameter, so a consumer meets the
-- ceiling ONCE, on one comparison, instead of paying a term per frame
-- and a term per entry.  A per-entry LEDGER is what cannot work: an
-- entry's own walk reaches a sink of its own, so a ledger accumulating
-- a cap per entry is exponential in the dispatch gas, and no exponent
-- a walk factor carries covers that.  A ceiling has no such recurrence
-- because it is not a sum.  The obligation does not vanish -- whoever
-- PRODUCES this predicate owes the ceiling at every advance -- it
-- moves from a consumer's arithmetic into the producer's statement.
--
-- THE CONDITIONING IS EARNED AND NOT CONVENIENT.  The unconditioned
-- step does not survive this module's own header, twice over, so what
-- stands here is the true statement replacing a false one; the width
-- is the axis those witnesses move, and the store is the axis the
-- first of them moves.
mutual
  walkSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (S W C k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  walkSzOK S W C k sf gas id now root           vals fin sched st = ⊤
  walkSzOK S W C k sf gas id now (share-sink i) vals fin sched st =
    dispatchSzOK S W C k sf gas id now i vals fin sched st
  walkSzOK S W C k sf gas id now (f ↠ p)        vals fin sched st =
    (length vals ≤ W)
    × (k + szCount (Sched.slots sched) (EvalSt.nodes st) f vals ≤ C)
    × walkSzOK S W C (k + szCount (Sched.slots sched) (EvalSt.nodes st) f vals)
        sf gas id now p
        (proj₁ (stepFrame sf id now f p vals fin sched st))
        (proj₁ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st))))
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))

  -- one level of the dispatch telescope; the spent arm owes nothing
  dispatchSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S W C k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  dispatchSzOK {t = t} S W C k sf zero      id now i vals fin sched st = ⊤
  dispatchSzOK {t = t} S W C k sf (suc gas) id now i vals fin sched st =
    shareGoSzOK {t = t} S W C k sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  -- the fold, entry by entry and at the state each leaves: a cancelled
  -- registration owes nothing and moves neither state nor level, a
  -- delivered one owes the table reading its own walk enters at, that
  -- walk's own receipts, and an advance under the ceiling for what its
  -- run left behind
  shareGoSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S W C k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  shareGoSzOK S W C k sf gas id now i vals fin [] sched st = ⊤
  shareGoSzOK {t = t} S W C k sf gas id now i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then shareGoSzOK {t = t} S W C k sf gas id now i vals fin ps sched st
    else ((all (λ kv → boundedNode (iterSize S k S) (proj₂ kv))
                (EvalSt.nodes st) ≡ true)
      × walkSzOK S W C k sf gas id now p vals fin sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
      × Σ ℕ λ k′ →
        (k + k′ ≤ C)
      × shareGoSzOK {t = t} S W C (k + k′) sf gas id now i vals fin ps
          (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st }))))
          (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- THE SINK'S OWN SHARE OF THE LEDGER, which is the one clause of the
-- walk that is not a frame and the one term of the budget premise that
-- is not a path length.  A `share-sink` hands the same values to every
-- chain the registry admits, so what it owes is per ADMITTED ENTRY at
-- the state the fold reaches it in -- and the fold's own advance is an
-- existential the entry's whole run supplies rather than a frame count
-- the walk can add up.
--
-- SO THE TERM IS A REGISTRY WIDTH TIMES A FRAME CEILING, which is the
-- shape the consumer's budget premise already sets aside and the reason
-- this is stated over the same ledger as the frame clause rather than
-- beside it.
--
-- DEAD ROUTE: accumulating the fan's advance into the walk's own level
--   ledger, one ceiling per admitted entry.  An entry's walk reaches a
--   sink of its own, so the ledger recurs through the dispatch gas and
--   is exponential in it, while every quantity the consumer can afford
--   is polynomial in the cap.  It is the same finding the ceiling
--   parameter of this predicate exists for, arriving at the producer.
postulate
  dispatchSzOK-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S W C k : ℕ) → 2 ≤ S → 1 ≤ W →
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    slotsSize (Sched.slots sched) ≤ S →
    burstsOK W sf gas id now (share-sink i) vals fin sched st →
    k + n * (S * frameCh S W) ≤ C →
    dispatchSzOK S W C k sf gas id now i vals fin sched st

-- THE WALK'S LEDGER SPENT FRAME BY FRAME, and this is where a budget
-- premise that is a PRODUCT becomes a ceiling that is a comparison.
-- The premise sets aside one frame ceiling per frame of the path and a
-- registry's worth for the sink; each frame then draws one of them and
-- hands the rest on, so the level the walk has climbed to is under the
-- ceiling at every step without any frame having to know what the
-- frames after it will charge.
--
-- AND WHAT MAKES THE INDUCTION GO THROUGH IS THAT EVERY PREMISE
-- TRANSPORTS ALONG THE STEP: the path receipt by its own recursion, the
-- burst package by its own, the telescope because a frame cannot write
-- a slot, and the ledger because the frame's draw is exactly the term
-- the length lost.  Nothing here is re-established at a frame -- which
-- is what says the ceiling is a fixed product and not a climb.
walkSzOK-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (S W C k : ℕ) → 2 ≤ S → 1 ≤ W →
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  pathSz? S p ≡ true →
  slotsSize (Sched.slots sched) ≤ S →
  burstsOK W sf gas id now p vals fin sched st →
  k + pathLen p * frameCh S W + n * (S * frameCh S W) ≤ C →
  walkSzOK S W C k sf gas id now p vals fin sched st
walkSzOK-go S W C k 2≤S 1≤W sf gas id now root vals fin sched st
            hp hsl hbo hb = tt
walkSzOK-go {n = n} S W C k 2≤S 1≤W sf gas id now (share-sink i) vals fin sched st
            hp hsl hbo hb =
  dispatchSzOK-go S W C k 2≤S 1≤W sf gas id now i vals fin sched st hsl hbo
    (≤-trans (≤-reflexive (cong (_+ (n * (S * frameCh S W))) (sym (+-identityʳ k)))) hb)
walkSzOK-go {n = n} {e = e} S W C k 2≤S 1≤W sf gas id now (f ↠ p) vals fin sched st
            hp hsl hbo hb =
  burstsHead W sf gas id now (f ↠ p) vals fin sched st hbo
  , ≤-trans (+-monoʳ-≤ k szFits) hstep
  , walkSzOK-go S W C (k + szCount (Sched.slots sched) (EvalSt.nodes st) f vals)
      2≤S 1≤W sf gas id now p (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
      hptail
      (≤-trans (≤-reflexive
                 (cong slotsSize (stepFrame-slots sf id now f p vals fin sched st)))
               hsl)
      (proj₂ (proj₂ hbo))
      hrec
  where
  step = stepFrame sf id now f p vals fin sched st
  Ch = frameCh S W
  hpmid : ((suc (pathLen p) ≤ᵇ S) ∧ pathSz? S p) ≡ true
  hpmid = ∧-trueʳ {a = frameSz? S f} hp
  hptail : pathSz? S p ≡ true
  hptail = ∧-trueʳ {a = suc (pathLen p) ≤ᵇ S} hpmid
  szFits : szCount (Sched.slots sched) (EvalSt.nodes st) f vals ≤ Ch
  szFits = szCountFits S W 2≤S 1≤W (Sched.slots sched) (EvalSt.nodes st) f vals
             (∧-trueˡ hp) hsl
             (burstsHead W sf gas id now (f ↠ p) vals fin sched st hbo)
  hstep : k + Ch ≤ C
  hstep = ≤-trans (m≤m+n (k + Ch) (n * (S * Ch)))
            (≤-trans (+-monoˡ-≤ (n * (S * Ch))
                       (+-monoʳ-≤ k (m≤m+n Ch (pathLen p * Ch))))
                     hb)
  hrec : k + szCount (Sched.slots sched) (EvalSt.nodes st) f vals
           + pathLen p * Ch + n * (S * Ch) ≤ C
  hrec = ≤-trans (+-monoˡ-≤ (n * (S * Ch))
                   (+-monoˡ-≤ (pathLen p * Ch) (+-monoʳ-≤ k szFits)))
           (≤-trans (≤-reflexive
                      (cong (_+ (n * (S * Ch)))
                            (+-assoc k Ch (pathLen p * Ch))))
                    hb)

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
