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
open import Data.Nat.Properties using (≤-trans; ≤-refl; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤; ≤⇒≤ᵇ;
  ≤ᵇ⇒≤; m^n>0; *-zeroʳ; *-distribˡ-⊔; *-identityˡ; *-mono-≤; +-comm)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to; T⇒≡true; ≤ᵇ-widen)
open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Relation.Nullary using (yes; no)
open import Rx.Exp using (Ctx; Closed; Val; Fn; applyFn; sizeᵗ; sizeᵛ; _×ᵗ_; obs; _≟ᵗ_)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; NodeId; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; foldPath; stepFrame; dispatchShare; thruWalk; shareGo;
  shareAdmit; shareLatch; iterSize; NodeState; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; takeDispatch; takeVals; lookupNode; scanVals)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; thruWalk-nest; nodeNestAt; stepFrame-emit-scan;
  stepFrame-nodes-inner; capsDrainOK; FaceOK)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures
  using (thruWrap-vals; takeVals-all; pathLen; boundedNode; setNode-bounded;
  boundedNode-widen; all-impl)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; nest-inflate; dropSource-nest; nestUnit; cutThrough-nest)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; sizeCount; iterSize-infl)
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
  -- REFUTED: Refuted.Drain-Regs-Nest
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

-- THE COUNT ONE FRAME CHARGES THE LADDER, AND IT IS A PROPERTY OF THE
-- KIND.  A `map-f` substitutes into each arriving value independently,
-- so it pays one rung per node of its own function and the burst does
-- not enter.  A `scan-f` THREADS, so it pays those rungs ONCE PER
-- arriving value, plus the pairing that precedes each step.  Every
-- other kind computes no value of its own -- a take passes a prefix
-- through, and the two crossing into an inner subscription deliver
-- what they drained -- so one rung covers them.
szCount : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → List (Val Γ s) → ℕ
szCount (map-f fn)         vals = sizeᵗ fn
szCount (scan-f fn nid)    vals = length vals * suc (sizeᵗ fn)
szCount (take-f nid)       vals = 1
szCount (from-inner _ _ _) vals = 1
szCount (thru-outer _ _)   vals = 1

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
  valsSz? (iterSize S (szCount f vals) B)
    (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

postulate
  -- THE TWO FRAMES THAT RUN A SUBSCRIPTION, and both statements are
  -- FALSE as they stand: the program that runs arrives as a value, so
  -- the count has to read it and a constant cannot.  They are left
  -- standing only until the count moves, since raising it re-prices
  -- every level the walk above them spends.
  --
  -- REFUTED: `Refuted.Frame-Step-Size-Cross.stepFrame-sz-inner-absurd`
  --   and `Refuted.Frame-Step-Size-Cross.stepFrame-sz-outer-absurd`.
  stepFrame-sz-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
    (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
    all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    valsSz? B vals ≡ true →
    valsSz? (iterSize S 1 B)
      (proj₁ (stepFrame sf id now (from-inner op allNid inst) path vals fin
                sched st)) ≡ true

  stepFrame-sz-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
    all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    valsSz? B vals ≡ true →
    valsSz? (iterSize S 1 B)
      (proj₁ (stepFrame sf id now (thru-outer op nid) path vals fin
                sched st)) ≡ true

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
  stepFrame-sz-outer sf id now op nid path vals fin sched st S B
    2≤S hns hv

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
  all (λ kv → boundedNode (iterSize S (szCount f vals) B) (proj₂ kv))
      (EvalSt.nodes
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
    ≡ true

postulate
  -- THE STORE HALVES OF THE SAME TWO FRAMES, and both are FALSE for
  -- the same reason their value halves are: a scan installed by the
  -- subscription stores what the subscription emitted, and `reify`
  -- carries a product value into a term of its own size.  So the
  -- quantity that has to be charged is one, and it reaches the table
  -- only by being written there.  Left standing only until the count
  -- moves, since raising it re-prices every level the walk spends.
  --
  -- REFUTED: `Refuted.Frame-Step-Size-Cross-Store.stepFrame-sz-store-inner-absurd`
  --   and `Refuted.Frame-Step-Size-Cross-Store.stepFrame-sz-store-outer-absurd`.
  stepFrame-sz-store-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
    (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
    all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    valsSz? B vals ≡ true →
    all (λ kv → boundedNode (iterSize S 1 B) (proj₂ kv))
        (EvalSt.nodes
          (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (from-inner op allNid inst)
                                         path vals fin sched st))))))
      ≡ true

  stepFrame-sz-store-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S B : ℕ) → 2 ≤ S →
    all (λ kv → boundedNode B (proj₂ kv)) (EvalSt.nodes st) ≡ true →
    valsSz? B vals ≡ true →
    all (λ kv → boundedNode (iterSize S 1 B) (proj₂ kv))
        (EvalSt.nodes
          (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now (thru-outer op nid)
                                         path vals fin sched st))))))
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
frameCh : ℕ → ℕ → ℕ
frameCh S W = W * suc S

szCount≤ch : ∀ {n} {Γ : Ctx n} {s u} (S W : ℕ) → 1 ≤ W →
  (f : Frame Γ s u) (vals : List (Val Γ s)) →
  frameSz? S f ≡ true → length vals ≤ W →
  szCount f vals ≤ frameCh S W
szCount≤ch S W 1≤W (map-f fn) vals hf hw =
  ≤-trans (≤ᵇ⇒≤ (sizeᵗ fn) S (T-to hf))
          (≤-trans (≤-trans (m≤m+n S 1) (≤-reflexive (+-comm S 1))) 1≤ch)
  where
  1≤ch : suc S ≤ frameCh S W
  1≤ch = ≤-trans (≤-reflexive (sym (*-identityˡ (suc S)))) (*-mono-≤ 1≤W ≤-refl)
szCount≤ch S W 1≤W (scan-f fn nid) vals hf hw =
  *-mono-≤ hw (s≤s (≤ᵇ⇒≤ (sizeᵗ fn) S (T-to hf)))
szCount≤ch S W 1≤W (take-f nid) vals hf hw =
  ≤-trans (s≤s z≤n) (≤-trans (≤-reflexive (sym (*-identityˡ 1)))
                             (*-mono-≤ 1≤W (s≤s z≤n)))
szCount≤ch S W 1≤W (from-inner _ _ _) vals hf hw =
  ≤-trans (s≤s z≤n) (≤-trans (≤-reflexive (sym (*-identityˡ 1)))
                             (*-mono-≤ 1≤W (s≤s z≤n)))
szCount≤ch S W 1≤W (thru-outer _ _) vals hf hw =
  ≤-trans (s≤s z≤n) (≤-trans (≤-reflexive (sym (*-identityˡ 1)))
                             (*-mono-≤ 1≤W (s≤s z≤n)))

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
-- AND THE LEVEL RIDES ALONG BECAUSE THE CHARGE IS NOT ONE PER FRAME.
-- A frame costs `szCount` rungs, so the reading a fan-out entry is
-- owed sits at whatever the frames above it climbed to -- which is
-- exactly the index the consumer threads.  The fold does NOT advance
-- it entry by entry, and that is the reading's own weakness rather
-- than an oversight: chains in one fan write a table their successors
-- read, so a level fixed across the fold is a claim about the fan and
-- not a consequence of the walk.
--
-- THE CONDITIONING IS EARNED AND NOT CONVENIENT.  The unconditioned
-- step is refuted in this module's own header, twice, so what stands
-- here is the true statement replacing a false one; the width is the
-- axis those refutations move, and the store is the axis the first of
-- them moves.
mutual
  walkSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (S W k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (p : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  walkSzOK S W k sf gas id now root           vals fin sched st = ⊤
  walkSzOK S W k sf gas id now (share-sink i) vals fin sched st =
    dispatchSzOK S W k sf gas id now i vals fin sched st
  walkSzOK S W k sf gas id now (f ↠ p)        vals fin sched st =
    (length vals ≤ W)
    × walkSzOK S W (k + szCount f vals) sf gas id now p
        (proj₁ (stepFrame sf id now f p vals fin sched st))
        (proj₁ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st))))
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))

  -- one level of the dispatch telescope; the spent arm owes nothing
  dispatchSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S W k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  dispatchSzOK {t = t} S W k sf zero      id now i vals fin sched st = ⊤
  dispatchSzOK {t = t} S W k sf (suc gas) id now i vals fin sched st =
    shareGoSzOK {t = t} S W k sf gas id now i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  -- the fold, entry by entry and at the state each leaves: a cancelled
  -- registration owes nothing, a delivered one owes the table reading
  -- its own walk enters at and that walk's own width receipts
  shareGoSzOK : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (S W k : ℕ) (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  shareGoSzOK S W k sf gas id now i vals fin [] sched st = ⊤
  shareGoSzOK {t = t} S W k sf gas id now i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then shareGoSzOK {t = t} S W k sf gas id now i vals fin ps sched st
    else ((all (λ kv → boundedNode (iterSize S k S) (proj₂ kv))
                (EvalSt.nodes st) ≡ true)
      × walkSzOK S W k sf gas id now p vals fin sched
          (record st { delivered = rid ∷ EvalSt.delivered st })
      × shareGoSzOK {t = t} S W k sf gas id now i vals fin ps
          (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st }))))
          (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })))))

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
