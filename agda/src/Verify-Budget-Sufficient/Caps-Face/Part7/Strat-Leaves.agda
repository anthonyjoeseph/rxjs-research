-- Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
-- framePark-step … shareAdmit-park
module Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves where

open import Data.Bool    using (Bool; true)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; map; [])
open import Data.Bool.ListAction using (all)
open import Data.Maybe   using (just; nothing)
open import Data.Nat     using (ℕ; suc; _≤_)
open import Data.Unit    using (⊤)
open import Data.Vec     using (lookup)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Gas; Source; InstEvent)
open import Rx.Exp       using
  (Ctx; Closed; Val; Fn; Tm; _×ᵗ_; obs; applyFn; evalTm; _≟ᵗ_; inputsBelowᵉ;
   inputsBelowᵗ; inputsBelowᵛ)
open import Rx.Evaluator using
  (Frame; Path; Sched; EvalSt; RegId; _↠_; root; share-sink;
   stepFrame; subscribeE;
   foldPath; shareAdmit; shareLatch; NodeId; AllOp; scanVals; lookupNode;
   installNode;
   scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
   map-f; scan-f; take-f; from-inner; thru-outer;
   Arrival; arrTy; chainsOf; chainStep; cascadeLatch)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstStrat?; capsOK?; framePark?; frameStrat?; parkStrat?; pathFloor;
   pathPark?; pathStrat?; regStrat?)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsStrat?)
open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ)
open import Verify-Budget-Sufficient.Node-Fresh using
  (FreshC; frameAbove; stepFrame-fresh; subscribeE-nodes-below)
open import Verify-Budget-Sufficient.Node-Table using (lookupNode-setNode)

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
-- WHICH CELLS THE PARK READING WILL ASK ABOUT, as a bound on their ids.
-- Only two frame shapes name a node, so this is the exact DUAL of the
-- freshness ring's own frame predicate: that one says which cell a
-- frame WRITES and asks it to sit at or above a watermark, this says
-- which cell a frame READS and asks it to sit strictly below one.  The
-- three silent shapes are free because the reading does not reach the
-- store at them at all, which is the same economy that lets most call
-- sites discharge the reading itself by `refl`.
parkBelow : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Set
parkBelow w (from-inner _ allNid _) = suc allNid ≤ w
parkBelow w (scan-f _ nd)           = suc nd ≤ w
parkBelow w _                       = ⊤

-- THE SAME READING OVER A WHOLE CHAIN, as a bound on the cells the chain
-- will ask about.  A path asks its frames one at a time and each frame
-- asks about one cell, so the predicate is the frame-level one repeated
-- -- and the two terminals are free because a chain that has reached the
-- root or a sink has no frame left to read through.
pathBelow : ∀ {n} {Γ : Ctx n} {u t} → ℕ → Path Γ u t → Set
pathBelow w root           = ⊤
pathBelow w (share-sink _) = ⊤
pathBelow w (f ↠ p)        = parkBelow w f × pathBelow w p

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

-- (4) THAT A WALKED CHAIN ADMITS A WATERMARK, which is the whole residue
-- of the step-side park reading now that its transport is a body.  The
-- witness is the head's own smallest node: a chain is built outward-in
-- and every frame is minted before the descent that extends it, so the
-- head is the YOUNGEST cell in the chain and everything the tail reads
-- was minted earlier.  That is a fact about chains the evaluator BUILDS.
--
-- AND IT IS NOT ONE THE TYPE CARRIES, which is why the row is FALSITY
-- rather than hard: a `Frame` and a `Path` are independent arguments
-- here, so the statement quantifies over pairs no descent ever produces
-- -- a head naming a cell BELOW one its tail reads refutes it outright.
-- The repair is not a hypothesis: it is a field on `WalkHyps`, which
-- obliges every producer of a chain to supply the ordering and every
-- consumer to re-establish it, where a premise would oblige only the one
-- caller that happens to exist.  The scheduler's counter cannot stand in
-- for the witness -- it bounds what the tail reads and sits ABOVE the
-- head, which is the wrong side of the ring's own inequality.
  step-chain-below : ∀ {n} {Γ : Ctx n} {s u t}
    (f : Frame Γ s u) (κ : Path Γ u t) (sched : Sched Γ) →
    Σ ℕ λ w → (w ≤ Sched.nextNode sched) × frameAbove w f × pathBelow w κ

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

-- WHAT AN INSTALL LEAVES AT ITS OWN CELL, and it is a BODY over the
-- node table's own roundtrip rather than the leaf this once was.  The
-- arm reads the node the frame NAMES, and a subscribe that mints a scan
-- installs that cell in the same breath as it builds the frame -- so
-- the reading is about a cell whose contents are in hand rather than
-- about one the state happens to carry.  What makes it one `cong` is
-- that `parkStrat?` asks NO type test at this arm: it binds the
-- accumulator's own index, so the cell answers at whatever type it
-- holds and the install site never has to align two of them.
installNode-scanPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (k : ℕ) (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
  (ac : Val Γ u) (st : EvalSt e) →
  inputsBelowᵛ k u ac ≡ true →
  framePark? k (scan-f fn nid) (installNode nid (scan-st ac) st) ≡ true
installNode-scanPark k fn nid ac st hac =
  trans (cong (parkStrat? k)
           (lookupNode-setNode nid (scan-st ac) (EvalSt.nodes st))) hac

-- THE TRANSPORT ITSELF, KEYED ON THE FREEZE AND NOT ON WHAT CAUSED IT.
-- A subscribe and a step reach this reading by different routes and
-- leave the same fact behind -- everything strictly below a watermark
-- reads back unchanged -- so the case split over the frame is written
-- once and each caller supplies its own freeze.  The three silent shapes
-- are free because the reading does not reach the store at them at all.
frozen-framePark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (k w : ℕ) (f : Frame Γ s u) (st st′ : EvalSt e) →
  (∀ j → suc j ≤ w →
     lookupNode j (EvalSt.nodes st′) ≡ lookupNode j (EvalSt.nodes st)) →
  parkBelow w f →
  framePark? k f st ≡ true →
  framePark? k f st′ ≡ true
frozen-framePark k w (map-f _)        st st′ hfz hb hp = hp
frozen-framePark k w (take-f _)       st st′ hfz hb hp = hp
frozen-framePark k w (thru-outer _ _) st st′ hfz hb hp = hp
frozen-framePark k w (scan-f _ nd) st st′ hfz hb hp =
  trans (cong (parkStrat? k) (hfz nd hb)) hp
frozen-framePark k w (from-inner _ a _) st st′ hfz hb hp =
  trans (cong (parkStrat? k) (hfz a hb)) hp

-- WHAT A SUBSCRIBE DOES TO A CELL IT DOES NOT OWN, and this is the
-- DISJOINTNESS half of the store question rather than a second
-- arithmetic.  A subscribe writes nothing below the watermark it was
-- handed -- everything it writes, it minted -- so a frame naming a cell
-- minted EARLIER reads that cell back unchanged and the whole reading
-- travels by one `cong`.  The node-level half was proven long before
-- the park reading existed; what was missing was only the observation
-- that a frame reads ONE cell, which is what makes the lift a case
-- split rather than an induction.
--
-- THE PREMISE REPLACES A FALSE STATEMENT rather than weakening a true
-- one, which is the one sanctioned justification for adding a
-- hypothesis.  Unconditioned, the frame may name a cell the subscribe
-- is about to MINT: the reading holds vacuously at the miss beforehand
-- and fails at the seed the scan clause installs there.
-- REFUTED: `Refuted.Subscribe-Frame-Park`
subscribeE-framePark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u w}
  (k : ℕ) (g : Gas) (b : Closed Γ w) (κ : Path Γ w t)
  (bid : Id) (now : Tick) (f : Frame Γ s u)
  (sched : Sched Γ) (st : EvalSt e) →
  parkBelow (Sched.nextNode sched) f →
  framePark? k f st ≡ true →
  framePark? k f (proj₂ (proj₂ (subscribeE g b κ bid now sched st))) ≡ true
subscribeE-framePark k g b κ bid now f sched st hb hp =
  frozen-framePark k (Sched.nextNode sched) f st _
    (subscribeE-nodes-below g b κ bid now sched st) hb hp

-- AND THE CHAIN-LEVEL TRANSPORT, which is the frame one under an
-- induction and nothing else.  `pathPark?` reads each frame at the floor
-- of the chain BELOW it, and the freeze does not look at floors at all,
-- so the recursion carries whatever floor the path names and no
-- arithmetic enters.
frozen-pathPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (w : ℕ) (κ : Path Γ u t) (st st′ : EvalSt e) →
  (∀ j → suc j ≤ w →
     lookupNode j (EvalSt.nodes st′) ≡ lookupNode j (EvalSt.nodes st)) →
  pathBelow w κ →
  pathPark? κ st ≡ true →
  pathPark? κ st′ ≡ true
frozen-pathPark w root           st st′ hfz hb hp = refl
frozen-pathPark w (share-sink _) st st′ hfz hb hp = refl
frozen-pathPark w (f ↠ p) st st′ hfz (hbf , hbp) hp =
  ∧-intro (frozen-framePark (pathFloor p) w f st st′ hfz hbf (∧-trueˡ hp))
          (frozen-pathPark w p st st′ hfz hbp (∧-trueʳ hp))

-- (4) THE CHAIN-KEYED PARK READING ACROSS ONE FRAME STEP, and it is the
-- subscribe's statement one construct up rather than a second mechanism.
-- A step writes the STEPPED frame's own cell, so what the tail loses is
-- exactly what it ALIASES -- and the ring already freezes everything
-- strictly below a watermark the head sits at or above, so pinning the
-- tail's read cells under that watermark is the whole of it.  The
-- closure premises the free form carried are gone: they priced what the
-- write CONTAINS, and the question was never about the contents.
--
-- THE WATERMARK IS THE HEAD'S SMALLEST NODE, not the scheduler's, which
-- is why it is quantified rather than computed.  A `from-inner` head
-- names two cells and only the *All's own is old enough to bound the
-- tail, so a caller picks the witness its own chain supports and no
-- minimum-of-ids function has to exist.
--
-- DEAD ROUTE: transporting the tail's reading by the SUFFIX property
--   the frame-level statement rests on.  It held while a reinstall was
--   the only reachable write, and stopped holding when the park reading
--   gained an arm at a cell a step OVERWRITES: an `all` reading tolerates
--   losing a prefix and nothing tolerates a replacement.
pathPark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (w : ℕ) (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  w ≤ Sched.nextNode sched → frameAbove w f → pathBelow w κ →
  pathPark? κ st ≡ true →
  pathPark? κ
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame g id now f κ vals fin sched st)))))
      ≡ true
pathPark-step w g id now f κ vals fin sched st hw hf hb hp =
  frozen-pathPark w κ st _
    (FreshC.frozen
      (stepFrame-fresh w g id now f κ vals fin sched st hw hf)) hb hp
