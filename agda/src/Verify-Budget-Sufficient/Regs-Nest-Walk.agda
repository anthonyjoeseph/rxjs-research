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
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-trans; ≤-refl; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤; ≤⇒≤ᵇ;
  ≤ᵇ⇒≤; m^n>0; *-zeroʳ; *-distribˡ-⊔; *-identityˡ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to; T⇒≡true; ≤ᵇ-widen)
open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; Fn; applyFn; sizeᵗ; sizeᵛ; _×ᵗ_; obs)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; NodeId; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; foldPath; stepFrame; dispatchShare; thruWalk; shareGo;
  shareAdmit; shareLatch; iterSize; NodeState; scan-st; take-st; mergeAll-st; switch-st;
  exhaust-st; takeDispatch; takeVals; lookupNode)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nestDᵛˢ; thruWalk-nest; nodeNestAt; stepFrame-emit-scan;
  stepFrame-nodes-inner; capsDrainOK; FaceOK)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures using (thruWrap-vals; takeVals-all; pathLen)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; pathNestD; nest-inflate; dropSource-nest; nestUnit)
open import Verify-Budget-Sufficient.Caps using (Caps; frameStep; sizeCount)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW)
open import Verify-Budget-Sufficient.Caps-Depth using (depthReact)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; regsSz?; frameSz?)
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
  all (λ v → pathΦF B path * (nestDᵛ s v + pathNestD path) ≤ᵇ U) vals

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
              + pathNestD path) ≤ U)

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
           + pathNestD path) ≤ U)
FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st =
  Σ ℕ λ k → Σ ℕ λ G →
    ValsFit k (Sched.slots sched) G path vals
    × (pathΦF B path * (G + pathNestD path) ≤ U)

postulate
  -- ONE FRAME'S REGISTRATIONS, under the potential it was handed.  The
  -- charge is the potential rather than the frame's own size because
  -- what a `thru-outer` mints is the subscribed value's frames over the
  -- rest of the path, which is the potential exactly.
  --
  -- AND THE FRAME GRANT IS CARRIED, because `valsΦ?` alone is FALSE
  -- here.  The drain frame takes its payload out of the *All node's
  -- queue rather than out of the burst, so a completion walk clears the
  -- premise by computation at every budget -- `all` over an empty list
  -- -- and still subscribes a queued term, appending a registration
  -- whose path carries the fresh `thru-outer` frame.  The grant is the
  -- one the potential's own arm already takes, and taking the same one
  -- is what keeps the two faces discharged from a single fit.
  --
  -- REFUTED: Refuted.Drain-Regs-Nest
  -- RECOVERY: git show f38a902:agda/evidence/probed/Probed/Chain-Step-Regs-Rootward.agda
  --   restores a rootward-stacking program and its readings.
  stepFrame-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (f ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U f path vals fin sched st →
    regsNestMax (EvalSt.registry
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
      ≤ regsNestMax (EvalSt.registry st) ⊔ U

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
  hv : E * F * (nestDᵛ s v + (nestDᵗ fn + pathNestD p)) ≤ U
  hv = ≤ᵇ⇒≤ _ _ (T-to (∧-trueˡ h))
  shape : F * (E * (nestDᵗ fn + nestDᵛ s v) + E * pathNestD p)
            ≡ E * F * (nestDᵛ s v + (nestDᵗ fn + pathNestD p))
  shape = solve 5 (λ f e d nt np →
            f :* (e :* (nt :+ d) :+ e :* np)
              := e :* f :* (d :+ (nt :+ np)))
          refl F E (nestDᵛ s v) (nestDᵗ fn) (pathNestD p)
  step : F * (nestDᵛ u (applyFn fn v) + pathNestD p) ≤ U
  step =
    ≤-trans (*-monoʳ-≤ F (+-monoˡ-≤ (pathNestD p) (applyFn-nest fn v)))
    (≤-trans (*-monoʳ-≤ F (+-monoʳ-≤ (E * (nestDᵗ fn + nestDᵛ s v))
                (nest-inflate E (pathNestD p) (m^n>0 2 (sizeᵗ fn)))))
    (≤-trans (≤-reflexive shape) hv))

-- a UNIFORM bound over the emitted list becomes the pointwise
-- predicate the potential is stated as, and nothing else is needed:
-- the depth of each value is under the maximum, and the maximum is
-- what the grant bounds.
Φ-of-bound : ∀ {n} {Γ : Ctx n} {u t} (B U G : ℕ) (p : Path Γ u t)
  (vs : List (Val Γ u)) → nestDᵛˢ vs ≤ G →
  pathΦF B p * (G + pathNestD p) ≤ U → valsΦ? B U p vs ≡ true
Φ-of-bound B U G p []       hb hfit = refl
Φ-of-bound {u = u} B U G p (v ∷ vs) hb hfit =
  ∧-intro (T⇒≡true _ (≤⇒≤ᵇ
            (≤-trans (*-monoʳ-≤ (pathΦF B p)
                       (+-monoˡ-≤ (pathNestD p)
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
    ≤-trans (*-monoʳ-≤ (pathΦF B p) (m≤m+n (nestDᵛ u v) (pathNestD p)))
            (≤ᵇ⇒≤ _ U (T-to (∧-trueˡ h)))

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
--   store-grant-only reading at this arm's OWN currency: the
--   accumulator is a bare `ofᵉ`, so every grant a state can carry is
--   discharged for nothing and the premise still holds at the budget
--   the frame surrenders, while sixty-five folds leave sixty-five
--   layers.  `Refuted.Scan-Fold-Burst` is the same witness read on
--   the iteration's quantity, which is what makes the two faces
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
  p v = pathΦF B path * (nestDᵛ s v + pathNestD path) ≤ᵇ U

  hΦ′ : all p vals ≡ true
  hΦ′ = subst (λ F → all (λ v → F * (nestDᵛ s v + pathNestD path) ≤ᵇ U) vals
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
-- AND THE FRAME READING IS STILL NOT ENOUGH, BECAUSE ONE ARM EMITS THE
-- NODE STORE.  A `scan-f` answers with its accumulator, fetched out of
-- `EvalSt.nodes`, and its own syntax may be a projection that hands
-- that accumulator straight back -- so the emitted size is the STORED
-- value's, which neither reading here sees.  What is owed is the store
-- reading `stBounded?` already makes at a `scan-st`, threaded through
-- the walk at the level, and the two walks that spend this leaf carry
-- no such premise today.
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
postulate
  stepFrame-sz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (S j : ℕ) →
    frameSz? S f ≡ true →
    valsSz? (iterSize S j S) vals ≡ true →
    valsSz? (iterSize S (suc j) S)
      (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true

-- THE REGISTRY STAYS PRICED ACROSS A FRAME, AT AN ACCUMULATED LEVEL --
-- and the level is what makes the statement true, not how it is
-- phrased.  A subscribing frame registers the walked path with its head
-- swapped plus one frame per syntax node of the INNER OBSERVABLE it
-- received, and an inner is a runtime value, structurally unrelated to
-- the program a fixed cap is read from: that is the whole content of
-- both refutations below, each of which builds an inner FROM the cap
-- and beats it.
--
-- SO THE ARRIVING VALUES' SIZE IS A PREMISE, AND ONE FRAME COSTS ONE
-- LEVEL.  `sizeᵛ` at an observable IS `sizeᵉ`, so the size reading
-- bounds the inner's syntax outright and every witness of that family
-- dies against it; the registered length is then the walked length plus
-- the inner's, both under the level, and `sizeStep` pays for exactly
-- that sum, being `S + 2·X` at `X` the level in hand.  A fixed cap has
-- nothing to pay with, which is why no repair of the hypotheses alone
-- survives while this one does.
--
-- AND THE CURRENCY IS THE SIZE SIBLINGS', DELIBERATELY, SO A WALK
-- THREADING BOTH SPENDS ONE COUNT.  The registry costs exactly one
-- level per frame; the values cost one where the frame is read at the
-- base cap and one PLUS a reported growth index where it is not, so
-- the level a walk arrives at is always the values' and the registry
-- reading widens up to meet it.  At `j = 0` the iterate is the cap
-- itself, definitionally, so an entry reading transports for free.

-- DEAD ROUTE: reading the registered path as a TAIL of the walked one,
--   so that the cap transfers with no premise at all.  The share sink
--   registers a tail and the take frame filters, but a subscribing
--   frame descends into the value it received: the `mapᵉ` clause of the
--   subscribe recursion pushes one frame per operator of the body onto
--   the continuation before it reaches the leaf that registers, so what
--   lands in the registry is the walked path UNDER the body, not a
--   suffix of it.
-- DEAD ROUTE: and a ROOM LEDGER at a fixed ceiling does not repair it,
--   which is the more useful half because it says why the caps face
--   accumulates.  Carrying `pathLen p + L ≤ B` over the registry closes
--   the frame clause and closes the sink's ADMISSION, but not the sink's
--   RE-ENTRY: a chain fans into chains, so the level the ledger must
--   reserve is the cumulative depth of the fan-out rather than the depth
--   of the path in hand, and no ceiling fixed before the walk starts
--   bounds it.  That is why the level is existential downstream, and it
--   is a fact about the fan-out rather than about how the bound is
--   phrased.
-- DEAD ROUTE: and neither does deleting this face and reading the
--   registry off the caps face's own levelled walk, which is the repair
--   the redundancy note below invites.  The projector and the levelled
--   walk predicate both exist and the two walks do rewrite clause for
--   clause, but the consumer does not: the depth cascade is what spends
--   these walks, and its own ceiling is a PREMISE of the lemma that
--   produces the caps receipt, so a cascade taking that receipt would be
--   proving its ceiling from its ceiling.  The caps face sits ABOVE the
--   depth cascade, not beside it, and that ordering is what the
--   redundancy reading misses.
-- REFUTED: `Refuted.Subscribe-Inner-Regs-Base` -- the subscribe this
--   statement's two subscribing frames perform does not preserve a
--   fixed cap, symbolically and at every cap.
-- REFUTED: `Refuted.Caps-Face` -- the same statement one level up was
--   deleted as false and redundant against `subscribeE-caps`, which is
--   ground because it reports at a level.
postulate
  stepFrame-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (S j : ℕ) →
    valsSz? (iterSize S j S) vals ≡ true →
    pathSz? (iterSize S j S) (f ↠ path) ≡ true →
    regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
    regsSz? (iterSize S (suc j) S) (EvalSt.registry
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st)))))) ≡ true

-- AND ALONG THE WHOLE PATH, state by state.  The frames' debts cannot
-- be collected in one bundle up front: each is owed at the state the
-- walk has reached by the time that frame runs, so the predicate has
-- to step alongside the fold it guards.  Four frame kinds contribute
-- nothing, so on a path with no outer frame this is a tuple of units.
--
-- AND THE SINK IS NOT A LEAF OF IT, WHICH IS WHAT THE UNIT CLAUSE USED
-- TO SAY.  A `share-sink` hands the values to every chain the registry
-- admits, and each of those walks a path of its OWN -- so the potential
-- the sink was handed says nothing about what those chains carry, since
-- the sink's own factor is one and its own depth is zero while an
-- admitted path has both.  The debt is therefore per admitted entry, at
-- the state the fan-out fold reaches it in, and the predicate telescopes
-- through the fold exactly as it does through a chain.
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
