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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n;
  ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m^n>0;
  *-zeroʳ; *-distribˡ-⊔)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:=_; _:+_; _:*_; con)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Vec using (lookup)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to; T⇒≡true)
open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; Fn; applyFn; sizeᵗ; _×ᵗ_; obs)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; NodeId; AllOp; map-f; scan-f;
  take-f; from-inner; thru-outer; foldPath; stepFrame; dispatchShare; thruWalk; shareGo;
  shareAdmit; shareLatch)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; thruWalk-nest)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures using (thruWrap-vals)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; pathNestD; nest-inflate; dropSource-nest)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using (pathSz?; regsSz?; frameSz?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (shareAdmit-caps)
open import Verify-Budget-Sufficient.Measures using (pathLen; ∧-true; dropSource-all)
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
-- nothing at four of the five: they forward or substitute, and the
-- factor the path surrenders pays for it.  The outer frame does not
-- forward -- it SUBSCRIBES -- so what comes back is bounded by nothing
-- the incoming values say, and the only thing that does bound it is
-- the sighted grant the walk face already runs on.  Stating the debt
-- per frame rather than per statement is what keeps the fold uniform:
-- four arms discharge it with `tt`, and only the arm that has a
-- subscription under it has to find a grant.
FrameΦHyp : ∀ {n} {Γ : Ctx n} {s u t} (B U : ℕ) (f : Frame Γ s u)
  (path : Path Γ u t) (vals : List (Val Γ s)) (sched : Sched Γ) → Set
FrameΦHyp B U (map-f _)           path vals sched = ⊤
FrameΦHyp B U (scan-f _ _)        path vals sched = ⊤
FrameΦHyp B U (take-f _)          path vals sched = ⊤
FrameΦHyp B U (from-inner _ _ _)  path vals sched = ⊤
FrameΦHyp B U (thru-outer op nid) path vals sched =
  Σ ℕ λ k → Σ ℕ λ G →
    ValsFit k (Sched.slots sched) G path vals
    × (pathΦF B path * (G + pathNestD path) ≤ U)

postulate
  -- ONE FRAME'S REGISTRATIONS, under the potential it was handed.  The
  -- charge is the potential rather than the frame's own size because
  -- what a `thru-outer` mints is the subscribed value's frames over the
  -- rest of the path, which is the potential exactly.
  --
  -- INSTANTIATION SAID THE TIE IS EXACT, at the one shape that can
  -- deepen a registration at all: *All frames stacked ROOTWARD of the
  -- leaf, over a `deferᵉ` at an iterated observable type, read at two
  -- stack depths.  The fold moved with the stack and was EQUAL either
  -- side of the chain at both -- a frame is charged the `thru-outer`
  -- frames the observable it carries will push, and where that count
  -- stops at a defer gate the defer's own registration adds back the
  -- frame the gate dropped.  So this leaf has no slack to spend at the
  -- shapes reached so far, and a frame kind that raised the fold by one
  -- would refute it.
  --
  -- RECOVERY: git show f38a902:agda/evidence/probed/Probed/Chain-Step-Regs-Rootward.agda
  --   restores that program and its readings.
  stepFrame-nest-regs : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (f ↠ path) vals ≡ true →
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
  FrameΦHyp B U (thru-outer op nid) path vals sched →
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

postulate
  -- THE SCAN FRAME SUBSTITUTES BY THE SAME RULE and pays the same
  -- factor, but it also reads and writes a node, so its emitted value
  -- is the accumulator's image rather than the payload's and the
  -- substitution above cannot be pointed at it unchanged.
  --
  -- RECOVERY: git show 8175756:agda/evidence/probed/Probed/Step-Frame-Nest-Phi.agda
  --   restores the harness that walked the refuting term through the
  --   map clause -- the same shape a scan clause has to be run at.
  stepFrame-nest-Φ-scan : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (nid : NodeId) (path : Path Γ u t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U (scan-f fn nid ↠ path) vals ≡ true →
    valsΦ? B U path
      (proj₁ (stepFrame sf id now (scan-f fn nid) path vals fin sched st))
      ≡ true

  -- THE TAKE FRAME CARRIES A FACTOR OF ONE AND NO DEPTH, so its
  -- hypothesis and its conclusion are the same statement read either
  -- side of the gate: what is owed is only that the values it lets
  -- through are among the ones handed to it.
  stepFrame-nest-Φ-take : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (nid : NodeId) (path : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (take-f nid ↠ path) vals ≡ true →
    valsΦ? B U path
      (proj₁ (stepFrame sf id now (take-f nid) path vals fin sched st))
      ≡ true

  -- THE INNER FRAME'S OUTPUT DOES NOT COME FROM THE FRAME AT ALL -- it
  -- is what the inner run produced -- and the frame's factor is one, so
  -- there is nothing here to pay a deepening with.  What has to hold is
  -- that an inner run cannot hand out a value deeper than the potential
  -- the outer walk was already carrying.
  stepFrame-nest-Φ-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
    (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U (from-inner op allNid inst ↠ path) vals ≡ true →
    valsΦ? B U path
      (proj₁ (stepFrame sf id now (from-inner op allNid inst) path vals
                        fin sched st))
      ≡ true

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
  FrameΦHyp B U f path vals sched →
  valsΦ? B U path (proj₁ (stepFrame sf id now f path vals fin sched st)) ≡ true
stepFrame-nest-Φ sf id now (map-f fn) path vals fin sched st B U hΦ _ =
  mapΦ B U fn path vals hΦ
stepFrame-nest-Φ sf id now (scan-f fn nid) path vals fin sched st B U hΦ _ =
  stepFrame-nest-Φ-scan sf id now fn nid path vals fin sched st B U hΦ
stepFrame-nest-Φ sf id now (take-f nid) path vals fin sched st B U hΦ _ =
  stepFrame-nest-Φ-take sf id now nid path vals fin sched st B U hΦ
stepFrame-nest-Φ sf id now (from-inner op allNid inst) path vals fin sched st B U hΦ _ =
  stepFrame-nest-Φ-inner sf id now op allNid inst path vals fin sched st B U hΦ
stepFrame-nest-Φ sf id now (thru-outer op nid) path vals fin sched st B U _ hF =
  thruΦ sf id now op nid path vals fin sched st B U hF

-- THE REGISTRY STAYS PRICED ACROSS A FRAME, which is what lets a walk
-- that starts under a size cap reach a sink still able to say what the
-- registry holds.  As stated it is read at ONE cap, and that reading is
-- the part still owed: the two frames that subscribe register paths
-- built by descending into the subscribed body, so the registered
-- length is the walked length plus the body's own, and no premise here
-- bounds a body.  What the walk face pays for the same fact is a ROOM
-- budget rather than a cap — a length ledger carried at a fixed ceiling
-- with the subscribe depth reserved inside it, and the depth bounded by
-- the GAS rather than by any size.  So the repair is a premise, and the
-- premise is not a size: it is the room the walk has left.
--
-- The reading is worse than one missing hypothesis, and that is the
-- useful half.  A frame's OUTPUT values are bigger than its input ones
-- by one `iterSize` step, so any room budget derived from the payload
-- GROWS along the walk while the path shortens by one frame per step.
-- A single ceiling covering both ends is therefore not a matter of
-- picking a larger one; the two quantities move apart.  The walk face's
-- ledger works because its budget comes from the gas, which is spent
-- rather than grown.

-- DEAD ROUTE: reading the registered path as a TAIL of the walked one,
--   so that the cap transfers with no premise at all.  The share sink
--   registers a tail and the take frame filters, but a subscribing
--   frame descends into the value it received: the `mapᵉ` clause of the
--   subscribe recursion pushes one frame per operator of the body onto
--   the continuation before it reaches the leaf that registers, so what
--   lands in the registry is the walked path UNDER the body, not a
--   suffix of it.
postulate
  stepFrame-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (S : ℕ) →
    pathSz? S (f ↠ path) ≡ true →
    regsSz? S (EvalSt.registry st) ≡ true →
    regsSz? S (EvalSt.registry
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st)))))) ≡ true

-- AND THE PRICE SURVIVES A WHOLE CHAIN, which is what a fold over a
-- selection needs and the frame law alone does not give: the next chain
-- runs at the state the last one left.  The sink is what makes this more
-- than the frame law iterated -- the fan-out registers on behalf of
-- paths the registry already holds, and the admitted list inherits the
-- registry's own receipt, so the cap the walk entered under is the cap
-- it leaves under.
mutual
  foldPath-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B : ℕ) →
    pathSz? B path ≡ true →
    regsSz? B (EvalSt.registry st) ≡ true →
    regsSz? B (EvalSt.registry
      (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st)))) ≡ true
  foldPath-regsSz sf gas id now envSrc root vals evs fin sched st B _ hreg = hreg
  foldPath-regsSz sf gas id now envSrc (share-sink i) vals evs fin sched st B _ hreg =
    dispatchShare-regsSz sf gas id now i vals fin sched st B hreg
  foldPath-regsSz sf gas id now envSrc (f ↠ p) vals evs fin sched st B hpz hreg =
    foldPath-regsSz sf gas id now envSrc p
      (proj₁ step) (evs ++ proj₁ (proj₂ step))
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step)))) B
      hpTail (stepFrame-regsSz sf id now f p vals fin sched st B hpz hreg)
    where
    step = stepFrame sf id now f p vals fin sched st
    hpTail : pathSz? B p ≡ true
    hpTail = proj₂ (∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p)
                     (proj₂ (∧-true (frameSz? B f)
                              ((suc (pathLen p) ≤ᵇ B) ∧ pathSz? B p) hpz)))

  dispatchShare-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B : ℕ) →
    regsSz? B (EvalSt.registry st) ≡ true →
    regsSz? B (EvalSt.registry
      (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st)))) ≡ true
  dispatchShare-regsSz sf zero id now i vals fin sched st B hreg = hreg
  dispatchShare-regsSz sf (suc gas) id now i vals false sched st B hreg =
    shareGo-regsSz sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B
      (shareAdmit-caps B i (EvalSt.registry st) hreg) hreg
  dispatchShare-regsSz {t = t} sf (suc gas) id now i vals true sched st B hreg =
    dropSource-all (λ en → pathSz? B (proj₂ (proj₂ (proj₂ en)))) (toℕ i)
      (EvalSt.registry (proj₂ (proj₂ GO))) went
    where
    GO = shareGo {t = t} sf gas id now i vals true
           (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st)
    went : regsSz? B (EvalSt.registry (proj₂ (proj₂ GO))) ≡ true
    went = shareGo-regsSz sf gas id now i vals true
             (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B
             (shareAdmit-caps B i (EvalSt.registry st) hreg) hreg

  shareGo-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B : ℕ) →
    all (λ rp → pathSz? B (proj₂ rp)) ps ≡ true →
    regsSz? B (EvalSt.registry st) ≡ true →
    regsSz? B (EvalSt.registry
      (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st)))) ≡ true
  shareGo-regsSz sf gas id now i vals fin [] sched st B _ hreg = hreg
  shareGo-regsSz sf gas id now i vals fin ((rid , p) ∷ ps) sched st B hps hreg
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-regsSz sf gas id now i vals fin ps sched st B
                  (proj₂ (∧-true (pathSz? B p) _ hps)) hreg
  ... | false =
    shareGo-regsSz sf gas id now i vals fin ps
      (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B
      (proj₂ (∧-true (pathSz? B p) _ hps))
      (foldPath-regsSz sf gas id now (toℕ i) p vals EVS fin sched st₀ B
        (proj₁ (∧-true (pathSz? B p) _ hps)) hreg)
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    EVS = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas id now (toℕ i) p vals EVS fin sched st₀

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
    FrameΦHyp B U f p vals sched
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
            (⊔-lub (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ)
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
