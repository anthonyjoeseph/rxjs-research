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
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_; z≤n)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; *-monoʳ-≤; +-monoˡ-≤; +-monoʳ-≤; ≤⇒≤ᵇ;
  ≤ᵇ⇒≤; m^n>0; *-zeroʳ; *-distribˡ-⊔)
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
  shareAdmit; shareLatch; iterSize)
open import Rx.Nest-Depth using (nestDᵛ; nestDᵗ)
open import Verify-Budget-Sufficient.Nest-Walk using (nestDᵛˢ; thruWalk-nest)
open import Verify-Budget-Sufficient.Depth-Sighted using (ValsFit; thruFit-vals)
open import Verify-Budget-Sufficient.Measures using (thruWrap-vals)
open import Verify-Budget-Sufficient.Nest-Store
  using (regsNestMax; pathNestD; nest-inflate; dropSource-nest)
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

-- AND THE WHOLE FOLD FOR ONE STEP OF THE LEVEL, WHICH IS NOT THE
-- FRAME STATEMENT ABOVE SUMMED UP.  The count is DETERMINED -- one
-- call, one step -- rather than a witness chosen after the fact, and
-- nothing in it is denominated in the path's length or in how deep a
-- sink re-enters.  That is why the fold's price is stated here at all
-- instead of being derived from the frame's.
--
-- AND ONE LEVEL SUFFICES BECAUSE OF WHAT `regsSz?` CHARGES.  It is an
-- `all` over the registry, so the price is per ENTRY -- many short
-- entries cost what one costs, and only a single entry getting LONGER
-- can move it.  A subscribing frame lengthens no standing entry: it
-- swaps its own head for a `from-inner` and registers a NEW chain
-- carrying one frame per operator of the inner it received.  So the
-- quantity under test is the longest single registration, which
-- outruns the walked path by the inner's own count -- and the values'
-- size premise caps exactly that, `sizeᵛ` at an observable being
-- `sizeᵉ`.  `sizeStep S L` is `S·(1+2L)`, which dominates both the
-- added length and the added frames.
--
-- AND THE PATH IS READ AT THE LEVEL RATHER THAN AT THE CAP, because a
-- fold is entered mid-flight as often as at a door: the caller reads
-- its arrival at the program's cap and widens once, while a chain the
-- fan-out re-enters carries whatever the levels before it reached.
--
-- REFUTED: `Refuted.Chain-Step-Regs-Cap` -- the fixed-cap form this
--   replaces, at a five-node inner and a six-frame chain against a cap
--   of six.  Both premises hold and the registered chain has length
--   eight, so what broke was the length ledger rather than any size
--   reading, and no further hypothesis repairs it.
-- DEAD ROUTE: composing the frame statement above along the path, so
--   that the fold needs no statement of its own.  Each frame costs a
--   level, so a chain costs its own length in levels and a sink
--   re-enters chains that cost theirs -- and the level range that
--   asks for is dead in `Refuted.Sink-Level-Range`, at the smallest
--   cap the caps invariant admits.  What blocks it is the arithmetic
--   rather than the composition: the size reading is an exponential
--   of the level and the affordable range is a cap squared plus a
--   cap, so sharpening the walk factor buys a constant and the two
--   separate at every cap.
--
-- PROBED: `Probed.Chain-Step-Regs-Level` -- the ROOTWARD re-entry, over
--   a stack of one to eight `mergeAllᵉ` flattens whose sources are each
--   other, every figure read off a state the evaluator reached and
--   every depth pinned to the arm that measures a real `chainStep`.
--   The registered length grows by exactly ONE per flatten level while
--   the inner's own size grows by four, so the descent does not recurse
--   and the one axis that could refute this form is closed along that
--   route.  NOT COVERED: the SIDEWAYS re-entry at a `share-sink`, which
--   `Probed.Chain-Step-Regs-Share` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Share` -- the SIDEWAYS re-entry, where
--   `foldPath` and `dispatchShare` are mutually recursive and the depth
--   is the share telescope rather than the syntax.  One five-slot
--   context, a scripted driver at slot zero and four `mergeAllᵉ` shares
--   above it, rooted at each of the five slots in turn, so one arrival
--   crosses zero to four share boundaries inside a single `chainStep`.
--   Every row is pinned to the arm that measures a real step, and the
--   step's emit count is read alongside the lengths: it is the crossing
--   count plus one at every depth, so the telescope is entered and not
--   merely built.  The maximum registered path length is TWO before the
--   step and two after it at every one of the five depths -- the
--   sideways route lengthens no registered path at all, while the
--   registry count tracks the telescope and is unchanged across the
--   step.  NOT COVERED: a telescope deeper than four, and a share
--   fanning out to more than one chain, which
--   `Probed.Chain-Step-Regs-Fan` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Fan` -- the DIAMOND, the share shape
--   both re-entry sweeps left out: each of them fans every share to
--   exactly one registered chain and so measures a share as a relay.
--   Width is varied in the PROGRAM rather than in the telescope, `w`
--   branches of the root reading one `input`, over three slots at
--   widths one to four; and two further rows put a width-`w` fan over
--   a share whose own def is a two-way fan, which is where width
--   compounds with depth.  The emit count separates a relay from a
--   fan outright and reads as the fan: the compounded rows deliver
--   twice their width, not their width.  The maximum registered path
--   length is THREE before the step and three after it in every row,
--   width one through four and compounded alike -- so a fan multiplies
--   registry ENTRIES and the emit stream, and lengthens no entry.
--   NOT COVERED: the operator KIND at the frames of a sinking chain,
--   which `Probed.Chain-Step-Regs-Cut` takes up.
--
-- PROBED: `Probed.Chain-Step-Regs-Cut` -- the CUTTING arm, against a
--   flatten control of the same shape.  A `takeᵉ` whose count expires
--   on the stepped arrival, at the leaf and again on the def of a share
--   so the cut sits BETWEEN two sinks; plus a mixed row where one
--   branch of a width-two share cuts and the other survives, which is
--   where `shareGo`'s ordering is observable.  No cut leaves a longer
--   entry registered than the control does: the cut rows come back
--   SHORTER, and the survivor of the mixed row sits at exactly the
--   control's length.  NOT COVERED, and the rows say so themselves:
--   `switchAllᵉ` and `exhaustAllᵉ` read identical to the control
--   because a FIRST arrival gives neither anything to cut, so their
--   real arm needs a second `chainStep`; and every row that does cut
--   SHRINKS the registry, which satisfies a growth bound whatever the
--   frames did -- those rows are evidence about the length conjunct
--   alone, which is the only unbounded one but not the only one.
-- PROBED: `Probed.Chain-Step-Regs-Second` -- the SECOND arrival, which
--   closes both gaps the cutting sweep named.  The inner is a scripted
--   slot timed past the outer, so it is still live when the second
--   arrival lands and the first arrival's full `cascade` supplies the
--   state; then `switchAllᵉ` really abandons and `exhaustAllᵉ` really
--   refuses.  Both now read STRICTLY BELOW the flatten control's
--   registry rather than identical to it, which is what says the
--   cutting arm was taken; and no row shrinks -- the control grows by
--   the inner it registers, both cutting arms hold level -- so the SIZE
--   conjunct is under test here for the first time, not merely the
--   length one.  Registered length is flat at the control's on every
--   row, the share-def cut included.  NOT COVERED: the inner never
--   fires, so no arrival ever comes FROM one -- which
--   `Probed.Chain-Step-Regs-Inner` takes up -- and what an abandoned
--   inner's own delivery would do after its registration is dropped is
--   unmeasured.
--
-- PROBED: `Probed.Chain-Step-Regs-Inner` -- the arrival that comes FROM
--   an inner, which is the re-entry every sweep above steps past: all
--   of them step an outer's arrival, and an inner registered by a
--   flatten re-enters `foldPath` mid-flight, carrying the sighted path
--   the outer built.  It is the second-arrival sweep's program with one
--   line of its script changed -- the inner is due BETWEEN two outer
--   values instead of past them all -- and the shift is pinned by a
--   provenance CONTRAST rather than by a bare number: the stepped
--   arrival's source differs from the first arrival's under the
--   retiming and equals it under the sibling's timing, so the two
--   readings together say the door was entered at an inner.  Registered
--   length comes back no longer than the same program's flatten control
--   at the same step, on every arm -- so the one unbounded conjunct is
--   not lengthened by the frames a mid-flight path arrives carrying.
--   NOT COVERED: one level of nesting, so an arrival from an inner OF
--   an inner is not reached; the inner is a bare slot read, so nothing
--   here carries operators of its own into the registered chain, which
--   is the quantity `Refuted.Chain-Step-Regs-Cap` moves; and the
--   stepped arrival is the SECOND overall, so a door met after several
--   inner deliveries have landed is unmeasured.
--
-- PROBED: `Probed.Chain-Step-Regs-Ops` -- an inner that CARRIES
--   OPERATORS, which is the axis `Refuted.Chain-Step-Regs-Cap` moves
--   to break the fixed-cap form and which every sweep above leaves
--   still: all of them register an inner that is a bare slot read, so
--   no registered chain in any of them gains a frame of the inner's
--   own.  Three operator counts over the second-arrival program, read
--   as a SUM of registered lengths because the entry a step adds is
--   shorter than the longest one already standing and a maximum is
--   therefore flat while the registry gains frames.  The merge arm
--   grows by exactly one more than the operator count at each count,
--   against a switch arm that grows by nothing at any of them -- so
--   the frames pushed are the inner's, and the axis is live in a RUN
--   and not only in a constructed state.  The growth sits under the
--   inner's own syntax, which is the quantity the arrival's size
--   premise bounds, so a level covers what the cap could not.  The
--   registry is then read ENTRY BY ENTRY, matched on the id each was
--   registered under, because the sum is a lens and not the charge:
--   `regsSz?` is an `all`, so many short entries cost what one costs
--   and only a single entry getting LONGER can move the price.  No
--   entry standing before a step is longer after it, on either arm at
--   any count, over a surviving set the rows count rather than assume
--   -- so every frame the total records arrives as a NEW entry and
--   the charge is untouched by the growth.  NOT COVERED: the
--   operators are identity maps and one nesting level, so a frame
--   reading its argument's syntax is unmeasured; and every row
--   registers one new entry per step, so a step registering several
--   is reached only through the held row.
postulate
  foldPath-regsSz : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (S j : ℕ) →
    1 ≤ S →
    valsSz? (iterSize S j S) vals ≡ true →
    pathSz? (iterSize S j S) path ≡ true →
    regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
    regsSz? (iterSize S (suc j) S)
      (EvalSt.registry (proj₂ (proj₂
        (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≡ true

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
