-- Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
-- framePark-step … shareAdmit-park
module Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves where

open import Data.Bool    using (Bool; true)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; map; [])
open import Data.Bool.ListAction using (all)
open import Data.Nat     using (ℕ)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim      using (Tick; Id; Gas; Source; InstEvent)
open import Rx.Exp       using
  (Ctx; Closed; Val; Fn; _×ᵗ_; obs; applyFn; inputsBelowᵉ; inputsBelowᵗ;
   inputsBelowᵛ)
open import Rx.Evaluator using
  (Frame; Path; Sched; EvalSt; RegId; _↠_; stepFrame; subscribeE;
   foldPath; shareAdmit; shareLatch; NodeId; AllOp;
   scan-f; take-f; from-inner; thru-outer;
   Arrival; arrTy; chainsOf; chainStep; cascadeLatch)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstStrat?; capsOK?; framePark?; frameStrat?; pathFloor; pathPark?; pathStrat?;
   regStrat?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsStrat?)

-- THE TWO FACTS THE STRATIFICATION THREAD CANNOT GET BY REDUCTION, and
-- they sit together because they fail for the same reason: each is
-- asked of a state or a burst the EVALUATOR produced, where the caps
-- clique carries a receipt and this reading has none.

-- (1) THE FRAME-KEYED PARK READING ACROSS ONE STEP.  `pushBurst` steps
-- the SAME frame once per emit, so its recursion asks the reading of a
-- state the previous emit produced -- and there the frame is a
-- VARIABLE, so `framePark?` does not reduce and no clause can supply
-- it.  Every other site holds a frame constructor and pays by `refl`.
--
-- WHY THE PAYLOAD READING IS A HYPOTHESIS RATHER THAN AN ECONOMY.  Only
-- a `from-inner` frame names a node, and the only write to that node's
-- queue along a step is the drain's reinstall, whose residue is a
-- SUFFIX of what was read -- a reading of the shape `all` survives
-- that.  What could break it is an ENQUEUE, and the only thing enqueued
-- is an observable the frame's own payload carried, which is exactly
-- what the premise reads.
postulate
  framePark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    valsStrat? (pathFloor κ) vals ≡ true →
    framePark? (pathFloor κ) f st ≡ true →
    framePark? (pathFloor κ) f
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame g id now f κ vals fin sched st)))))
        ≡ true

-- (2) WHAT A SUBSCRIBE EMITS IS READ AT THE CHAIN IT WAS SUBSCRIBED
-- UNDER.  Every `pushBurst` in this development pushes a burst
-- `subscribeE` just produced, and the frame it pushes it through will
-- SUBSCRIBE the payloads again -- so the walk needs their reading, and
-- the caps receipt does not carry it.
--
-- IT IS A LEAF RATHER THAN A FOURTH CONJUNCT, and the choice is about
-- where the work lands rather than about strength.  The conjunct form
-- is the same statement proven by the same simultaneous induction the
-- caps clique already runs, so nothing here forecloses it; stating it
-- separately is what lets the registration premise reach its call sites
-- now instead of behind a rewrite of every witness tuple in the clique.
  subscribeE-burstStrat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (b : Closed Γ u) (κ : Path Γ u t)
    (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
    pathStrat? κ ≡ true →
    inputsBelowᵉ (pathFloor κ) b ≡ true →
    burstStrat? (pathFloor κ) (proj₁ (subscribeE g b κ bid now sched st)) ≡ true

-- (3) WHAT A FRAME HANDS THE REST OF ITS CHAIN.  The delivery walk steps
-- one frame and recurses on the tail with the payload that frame
-- produced, so it needs a reading of an OUTPUT the caps receipt reports
-- only a cap for.  The frame's own closure is the other half and that is
-- why it is a hypothesis: a `map` builds its output by applying a term
-- the frame carries, so the output can mention exactly what that term
-- does and nothing lower.
--
-- THE FLOOR DOES NOT MOVE ACROSS A FRAME, which is what makes one
-- statement cover the whole walk: `pathFloor` reports the TERMINAL's
-- floor from anywhere along the chain, so a push and a pop leave it
-- where it was.
  stepFrame-valsStrat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    frameStrat? (pathFloor κ) f ≡ true →
    valsStrat? (pathFloor κ) vals ≡ true →
    valsStrat? (pathFloor κ)
      (proj₁ (stepFrame g id now f κ vals fin sched st)) ≡ true

-- (4) THE CHAIN-KEYED PARK READING ACROSS ONE FRAME STEP, which is (1)
-- lifted off a single frame onto the tail the walk is about to enter.
-- It is a separate statement rather than a corollary because the tail's
-- frames are not the one that stepped: what has to survive is a reading
-- of nodes the step did not name.
  pathPark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    valsStrat? (pathFloor κ) vals ≡ true →
    pathPark? κ st ≡ true →
    pathPark? κ
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame g id now f κ vals fin sched st)))))
        ≡ true

-- (5) WHAT A SHARE HANDS THE CHAINS IT ADMITTED.  This is the one place
-- the registry reading is SPENT rather than established, and the two
-- halves come apart cleanly.  The chain half is `regStrat?`'s second
-- conjunct carried across the admission filter, since admitting drops
-- entries and never rewrites one.  The value half is the disjunct's
-- other side: a share delivers at slot `i`, whose values the sink's own
-- walk already reads below `i`, and an admitted continuation's floor
-- sits at or above `i` -- so the reading widens by monotonicity rather
-- than being claimed afresh.  The payload's TYPE is free, and the walk
-- needs it to be: its fan hypothesis quantifies the values separately
-- from the slot, and nothing in either half reads them.
  shareAdmit-strat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (i : Fin n) (vals : List (Val Γ s)) (st : EvalSt e) →
    regStrat? (EvalSt.registry st) ≡ true →
    valsStrat? (toℕ i) vals ≡ true →
    (all (λ rp → pathStrat? {n} {Γ} {lookup Γ i} {t} (proj₂ rp))
         (shareAdmit i (EvalSt.registry st)) ≡ true)
    × (all (λ rp → valsStrat? (pathFloor {n} {Γ} {lookup Γ i} {t} (proj₂ rp)) vals)
           (shareAdmit i (EvalSt.registry st)) ≡ true)

-- (6) AND THE PARK READING OVER THOSE SAME CHAINS, in the two shapes the
-- fan-out asks for it: at the latched state it starts from, and again
-- after a sibling chain has folded.  They are one postulate because the
-- fan-out spends them in one place and neither is derivable from the
-- other -- the first is about a state the walk was handed, the second
-- about one the walk produced.
  shareAdmit-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (i : Fin n) (fin : Bool) (st : EvalSt e) →
    all (λ rp → pathPark? {n} {Γ} {lookup Γ i} {t} (proj₂ rp) (shareLatch i fin st))
        (shareAdmit i (EvalSt.registry st)) ≡ true

  foldPath-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (p : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (ps : List (RegId × Path Γ u t)) →
    all (λ rp → pathPark? (proj₂ rp) st) ps ≡ true →
    all (λ rp → pathPark? (proj₂ rp)
           (proj₂ (proj₂ (foldPath sf gas id now envSrc p vals evs fin sched st))))
        ps ≡ true

-- (7) AND THE CASCADE'S THREE, WHICH ARE (5) AND (6) ARRIVING FROM THE
-- OTHER FACE.  The share reaches its chains through `shareAdmit` and the
-- cascade through `chainsOf`, and neither filter can be rearranged into
-- the other -- one is keyed by a SLOT, the other by an ARRIVAL's source
-- -- so the entry reading is owed once per face.  The chain reading is
-- the admission filter's own conjunct carried across, exactly as its
-- share sibling is; what makes the park pair leaves rather than
-- corollaries is the same thing as at every other park statement: a
-- chain's frames name nodes, and no conjunct of the caps receipt prices
-- what those nodes have parked.
  chainsOf-strat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (st : EvalSt e) →
    regStrat? (EvalSt.registry st) ≡ true →
    all (λ rc → pathStrat? {n} {Γ} {arrTy a} {t} (proj₂ rc))
        (chainsOf a st) ≡ true

  cascade-admit-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (a : Arrival Γ) (st : EvalSt e) →
    all (λ rc → pathPark? {n} {Γ} {arrTy a} {t} (proj₂ rc) (cascadeLatch a st))
        (chainsOf a st) ≡ true

-- and the cascade's fold-through, which is `foldPath-park` one face
-- over: the tail's chains are read at the state the HEAD chain's step
-- produced, and they are not the chain that stepped
  chainStep-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
    (sched : Sched Γ) (st : EvalSt e)
    (chains : List (RegId × Path Γ (arrTy a) t)) →
    all (λ rc → pathPark? (proj₂ rc) st) chains ≡ true →
    all (λ rc → pathPark? (proj₂ rc)
           (proj₂ (proj₂ (chainStep id a path sched st)))) chains ≡ true

-- THE PARK READING WHERE NO PREMISE CARRIES IT.  Every other park
-- statement here MOVES the reading across a step and takes it as a
-- hypothesis; the caps face can, because its walk threads `framePark?`
-- from the top.  The burst face's nodry half cannot: its hypotheses
-- record has no park field, and the mergeAll drain subscribes exactly
-- what the predicate reads, so the obligation arrives at a site with
-- nothing above it to ask.
--
-- IT IS STATED OVER `capsOK?` AND NOT DERIVED FROM IT, which is the
-- finding rather than an economy: the invariant prices what a node has
-- QUEUED for size and for width and reads no floor at all, so a floor-
-- keyed reading of that queue has no conjunct to come out of.  The
-- repair is a park field on the walk's hypotheses record, cascading
-- through every producer of it -- the cost of the fact being true, and
-- the reason the drain is not weakened to avoid it.
  frame-parkStrat : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (f : Frame Γ s u) (κ : Path Γ u t)
    (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    pathStrat? (f ↠ κ) ≡ true →
    framePark? (pathFloor κ) f st ≡ true

-- (9) WHAT ONE HOP LEAVES BELOW THE FLOOR, ONE HEAD AT A TIME.  The
-- five heads do not rebuild a payload the same way -- a `map` applies
-- a template, a `scan` folds one against a value it keeps in the
-- store, and the other three re-emit what they were handed or what
-- they subscribed -- so a single fact over a frame VARIABLE could not
-- reduce at any of them, and every head's obligation arrived as the
-- same opaque premise with no way to tell which owed the store
-- anything.  Split, the `map` head owes it NOTHING: its statement
-- mentions no state at all.
--
-- AND `framePark?` IS A PATH PREDICATE THAT DOES SEE THE STORE, which
-- is what lets the two subscribing heads state theirs.  It reads the
-- node a `from-inner` names, and the tier threads it from the top, so
-- their store half is a conjunct that EXISTS and is spent here rather
-- than a fact owed to nobody.  Where the predicate reads `true` -- at
-- a `scan-f`, whose accumulator is a node it does not name -- there is
-- no conjunct to come out of, and `capsOK?` stands in its place; that
-- one head is the residue, not the whole reading.

  scan-strat-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (c : Caps) (k : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nd : NodeId) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    inputsBelowᵗ k fn ≡ true →
    all (inputsBelowᵛ k s) vals ≡ true →
    all (inputsBelowᵛ k u)
      (proj₁ (stepFrame sf nid now (scan-f fn nd) κ vals fin sched st)) ≡ true

  take-strat-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (k : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (nd : NodeId) (κ : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    all (inputsBelowᵛ k s) vals ≡ true →
    all (inputsBelowᵛ k s)
      (proj₁ (stepFrame sf nid now (take-f nd) κ vals fin sched st)) ≡ true

  inner-strat-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (k : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (allNid inst : NodeId) (κ : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    framePark? k (from-inner {s = s} op allNid inst) st ≡ true →
    all (inputsBelowᵛ k s) vals ≡ true →
    all (inputsBelowᵛ k s)
      (proj₁ (stepFrame sf nid now (from-inner op allNid inst) κ vals fin sched st))
        ≡ true

  thru-strat-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (c : Caps) (k : ℕ) (sf : Gas) (nid : Id) (now : Tick)
    (op : AllOp) (nd : NodeId) (κ : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    capsOK? c sched st ≡ true →
    all (inputsBelowᵛ k (obs u)) vals ≡ true →
    all (inputsBelowᵛ k u)
      (proj₁ (stepFrame sf nid now (thru-outer op nd) κ vals fin sched st)) ≡ true

-- and the template head's route is walked already, at a hereditary
-- value predicate whose term-side reading has the same shape: the
-- induction runs over the TERM with the type as an index, and only the
-- stream arm does any work
-- TWIN: `applyFn-hopSpn`
  map-strat-step : ∀ {n} {Γ : Ctx n} {s u}
    (k : ℕ) (fn : Fn Γ [] [] [] s u) (vals : List (Val Γ s)) →
    inputsBelowᵗ k fn ≡ true →
    all (inputsBelowᵛ k s) vals ≡ true →
    all (inputsBelowᵛ k u) (map (applyFn fn) vals) ≡ true
