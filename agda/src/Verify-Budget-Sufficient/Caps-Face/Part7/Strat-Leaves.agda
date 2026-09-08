-- Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
-- framePark-step … shareAdmit-park
module Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves where

open import Data.Bool    using (Bool; true)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; map; [])
open import Data.Bool.ListAction using (all)
open import Data.Maybe   using (just; nothing)
open import Data.Nat     using (ℕ)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Gas; Source; InstEvent)
open import Rx.Exp       using
  (Ctx; Closed; Val; Fn; Tm; _×ᵗ_; obs; applyFn; evalTm; _≟ᵗ_; inputsBelowᵉ;
   inputsBelowᵗ; inputsBelowᵛ)
open import Rx.Evaluator using
  (Frame; Path; Sched; EvalSt; RegId; _↠_; stepFrame; subscribeE;
   foldPath; shareAdmit; shareLatch; NodeId; AllOp; scanVals; lookupNode;
   installNode;
   scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
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
-- WHY BOTH THE PAYLOAD AND THE CLOSURE ARE HYPOTHESES, and they are
-- not there for the same reason.  TWO frame shapes name a node and
-- their writes are not alike.  A `from-inner` reinstalls a queue whose
-- residue is a SUFFIX of what was read, so an `all`-shaped reading
-- survives it outright; what could break that one is an ENQUEUE, and
-- the only thing enqueued is an observable the frame's own payload
-- carried, which is exactly what the vals premise reads.  A `scan-f`
-- OVERWRITES its cell with the frame's closure applied to that
-- payload, so no part of the old reading survives and the new one is
-- bought rather than transported -- by the closure premise, without
-- which the statement is FALSE and not merely unproven.  That is the
-- one sanctioned justification for a premise: the conditioned form
-- REPLACES a false statement rather than weakening a true one.
postulate
  framePark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    frameStrat? (pathFloor κ) f ≡ true →
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
--
-- AND WHAT IT OWES IS DISJOINTNESS, NOT ARITHMETIC -- which is why the
-- closure premise cannot close it the way it closes (1).  The step
-- writes the STEPPED frame's own node, so the tail's reading survives
-- exactly when that write does not ALIAS a node some tail frame names,
-- and no reading of the closure says anything about which node the tail
-- points at.  The frame half of the vocabulary for that is proven --
-- `frameAbove` in `Verify-Budget-Sufficient.Node-Fresh` already has an
-- arm at every node-naming shape, and `stepFrame-fresh` spends it --
-- and what is missing is only its lift onto a path.
--
-- DEAD ROUTE: transporting the tail's reading by the SUFFIX property
--   (1) rests on.  It held while a reinstall was the only reachable
--   write, and stopped holding when the park reading gained an arm at a
--   cell a step OVERWRITES: an `all` reading tolerates losing a prefix
--   and nothing tolerates a replacement.  The aliasing obligation was
--   always there -- a `from-inner` step can write a node the tail names
--   too -- so what the arm removed is the property that made this row
--   look tractable, not the property that made it true.
  pathPark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (g : Gas) (id : Id) (now : Tick)
    (f : Frame Γ s u) (κ : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    pathStrat? κ ≡ true →
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
-- finding rather than an economy: the invariant prices what a node
-- HOLDS -- a drain's queue, a scan's accumulator -- for size and for
-- width and reads no floor at all, so a floor-keyed reading of either
-- cell has no conjunct to come out of.  The
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
-- than a fact owed to nobody.  A `scan-f` names a node too, and the
-- predicate now has an ARM there rather than reading `true` at a cell
-- it declines to name -- so that head spends a conjunct as well, and
-- the reading covers every node a frame declares instead of the one
-- shape it happened to have been written for.

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

-- and the fold's own transport, which reports BOTH halves because the
-- accumulator it hands on is the one the next emit reads: a step that
-- proved only the outputs would leave the cell it just overwrote
-- unread, and the cell is the whole reason this statement exists.  The
-- same shelf carries this shape at several other measures, and each is
-- a nil clause returning the accumulator untouched and a cons clause
-- that steps it and recurses.
-- TWIN: `scanVals-hopSpn`
  scanVals-strat : ∀ {n} {Γ : Ctx n} {s u}
    (k : ℕ) (fn : Fn Γ [] [] [] (u ×ᵗ s) u)
    (ac : Val Γ u) (vs : List (Val Γ s)) →
    inputsBelowᵗ k fn ≡ true →
    inputsBelowᵛ k u ac ≡ true →
    all (inputsBelowᵛ k s) vs ≡ true →
    (inputsBelowᵛ k u (proj₂ (scanVals fn ac vs)) ≡ true)
    × (all (inputsBelowᵛ k u) (proj₁ (scanVals fn ac vs)) ≡ true)

-- WHAT A CLOSED TERM'S VALUE READS, which the arm made load-bearing:
-- the scan seed arrives as a TERM and the cell it is installed into is
-- read as a VALUE, so the arm's premise cannot be discharged at any
-- install site without this.  The route is an induction over the term
-- with the environment generalised, and only the stream arm does work;
-- the same induction is already walked at the hop measure, where the
-- empty environment contributes an empty slope sum and the closed case
-- falls out of the open one.  What does NOT transfer is the arithmetic:
-- the mirror concludes a ≤ and this concludes a conjunction, so the
-- clauses correspond and the residue at each does not.
-- TWIN: `hopD-evalTm`
  evalTm-strat : ∀ {n} {Γ : Ctx n} {u}
    (k : ℕ) (z : Tm Γ [] [] [] u) →
    inputsBelowᵗ k z ≡ true →
    inputsBelowᵛ k u (evalTm z) ≡ true

-- WHAT AN INSTALL LEAVES AT ITS OWN CELL.  The arm reads the node the
-- frame NAMES, and a subscribe that mints a scan installs that cell in
-- the same breath as it builds the frame -- so at the install site the
-- reading is about a cell whose contents are in hand rather than about
-- one the state happens to carry.  It is a leaf and not a reduction
-- because `lookupNode` walks an assoc list: the roundtrip holds at the
-- head by the identifier test and at the tail by recursion, and the
-- evaluator's own type test sits on top of it, so nothing here reduces
-- at a variable identifier.
  installNode-scanPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (k : ℕ) (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (ac : Val Γ u) (st : EvalSt e) →
    inputsBelowᵛ k u ac ≡ true →
    framePark? k (scan-f fn nid) (installNode nid (scan-st ac) st) ≡ true

-- WHAT A SUBSCRIBE DOES TO A CELL IT DOES NOT OWN, and this is the
-- DISJOINTNESS half of the store question rather than a second
-- arithmetic.  A subscribe mints its nodes from the scheduler's
-- counter, so it writes only cells the frame in hand cannot name -- but
-- the reading is stated at a frame that is a VARIABLE here, and nothing
-- in the frame says which node it names.  The freshness vocabulary that
-- would settle it exists one face over at the node level and has no
-- lift to a reading keyed by a frame, which is why this is stated
-- rather than derived.
  subscribeE-framePark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w}
    (k : ℕ) (g : Gas) (b : Closed Γ w) (κ : Path Γ w t)
    (bid : Id) (now : Tick) (f : Frame Γ s u)
    (sched : Sched Γ) (st : EvalSt e) →
    framePark? k f st ≡ true →
    framePark? k f (proj₂ (proj₂ (subscribeE g b κ bid now sched st))) ≡ true

-- WHAT THE SCAN HEAD LEAVES BELOW THE FLOOR, and it is a BODY because
-- the park reading now has an arm at this node.  The head dispatches on
-- the cell, and every shape but one emits nothing at all -- so the
-- reading holds by the empty list, and the single live branch is the
-- fold, whose accumulator premise is exactly what the arm carries.  The
-- type test the evaluator runs is what turns that premise into a
-- statement about the head's own payload type; until it fires there is
-- no output to read.
scan-strat-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (k : ℕ) (sf : Gas) (nid : Id) (now : Tick)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nd : NodeId) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  framePark? k (scan-f fn nd) st ≡ true →
  inputsBelowᵗ k fn ≡ true →
  all (inputsBelowᵛ k s) vals ≡ true →
  all (inputsBelowᵛ k u)
    (proj₁ (stepFrame sf nid now (scan-f fn nd) κ vals fin sched st)) ≡ true
scan-strat-step {u = u} k sf nid now fn nd κ vals fin sched st hpk hfn hib
  with lookupNode nd (EvalSt.nodes st)
... | nothing                    = refl
... | just (take-st _)           = refl
... | just (mergeAll-st _ _ _ _) = refl
... | just (switch-st _ _)       = refl
... | just (exhaust-st _ _)      = refl
... | just (scan-st {w} acc) with w ≟ᵗ u
...   | yes refl = proj₂ (scanVals-strat k fn acc vals hfn hpk hib)
...   | no _     = refl
