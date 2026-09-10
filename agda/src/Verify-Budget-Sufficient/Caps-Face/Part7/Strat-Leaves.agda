-- Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves
-- framePark-step … shareAdmit-park
module Verify-Budget-Sufficient.Caps-Face.Part7.Strat-Leaves where

open import Data.Bool    using (Bool; true; false; _∧_)
open import Data.Fin     using (Fin; toℕ)
open import Data.List    using (List; map; [])
open import Data.Bool.ListAction using (all)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Nat     using (ℕ; suc; _≤_; _≤ᵇ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤ᵇ⇒≤; m≤m⊔n; m≤n⊔m; n≤1+n)
open import Data.Unit    using (⊤; tt)
open import Data.Vec     using (lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Relation.Nullary using (yes; no)

open import Rx.Prim      using (Tick; Id; Gas; g0; gs; Source; InstEvent)
open import Rx.Exp       using
  (Ctx; Closed; Val; Fn; Tm; _×ᵗ_; obs; applyFn; evalTm; _≟ᵗ_; inputsBelowᵉ;
   inputsBelowᵗ; inputsBelowᵛ)
open import Rx.Evaluator using
  (Frame; Path; Sched; EvalSt; RegId; _↠_; root; share-sink; stepFrame; subscribeE; foldPath;
  shareAdmit; shareLatch; NodeId; NodeState; AllOp; lookupNode; thruConsume; mergeAllDrain;
  subscribeInner; installNode; scan-st; take-st; mergeAll-st; switch-st; exhaust-st; map-f;
  scan-f; take-f; from-inner; thru-outer; Arrival; arrTy; chainsOf; chainStep; cascadeLatch)
open import Verify-Budget-Sufficient.Caps using (Caps)
open import Verify-Budget-Sufficient.Caps-Face.Part1 using
  (burstStrat?; capsOK?; framePark?; frameAbove?; frameRead; frameStrat?; parkStrat?; pathCell;
  pathFloor; pathOrd?; pathOrd?-mono; pathOrd?-read; pathPark?; pathRead; pathStrat?; regOrd?;
  regPark?; regPark?-nodes; regStrat?)
open import Verify-Budget-Sufficient.Delivery-Walk using
  (chainsGo-chQ; shareAdmit-chQ)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (valsStrat?)
open import Verify-Budget-Sufficient.Caps-Face.Part5 using (scanVals-strat)
open import Decide using (∧-intro; ∧-trueˡ; ∧-trueʳ; T-to)
open import Verify-Budget-Sufficient.Node-Fresh using
  (FreshC; frameAbove; frozen-setNode; stepFrame-fresh; subscribeE-fresh;
   subscribeE-nodes-below)
open import Verify-Budget-Sufficient.Node-Table using (lookupNode-setNode)
open import Verify-Budget-Sufficient.Delivery-Counter using
  (foldPath-nextNode; chainStep-nextNode)
open import Verify-Budget-Sufficient.Measures using (∧-true; all-impl)

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
-- not there for the same reason.  THREE frame shapes name a node and
-- their writes are not alike.  A `from-inner` reinstalls a queue whose
-- residue is a SUFFIX of what was read and a `thru-outer` APPENDS to
-- one, so an `all`-shaped reading survives both outright; what could
-- break either is the ENQUEUE, and the only thing enqueued is an
-- observable the frame's own payload carried, which is exactly what
-- the vals premise reads.  A `scan-f`
-- OVERWRITES its cell with the frame's closure applied to that
-- payload, so no part of the old reading survives and the new one is
-- bought rather than transported -- by the closure premise, without
-- which the statement is FALSE and not merely unproven.  That is the
-- one sanctioned justification for a premise: the conditioned form
-- REPLACES a false statement rather than weakening a true one.
-- WHICH CELLS THE PARK READING WILL ASK ABOUT, as a bound on their ids.
-- Only three frame shapes name a node, so this is the exact DUAL of
-- the freshness ring's own frame predicate: that one says which cell a
-- frame WRITES and asks it to sit at or above a watermark, this says
-- which cell a frame READS and asks it to sit strictly below one.  The
-- two silent shapes are free because the reading does not reach the
-- store at them at all, which is the same economy that lets most call
-- sites discharge the reading itself by `refl`.
parkBelow : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Set
parkBelow w (from-inner _ allNid _) = suc allNid ≤ w
parkBelow w (scan-f _ nd)           = suc nd ≤ w
parkBelow w (thru-outer _ nid)      = suc nid ≤ w
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

-- (4) THAT THE CHAINS A CASCADE REACHES ARE ORDERED, which is where the
-- step-side park reading's residue comes to rest now that its transport
-- is a body.  A chain is built outward-in: every frame is minted before
-- the descent that extends it, so a head is the YOUNGEST cell in the
-- chain and everything its tail reads was minted earlier and sits below
-- the counter.  That is a fact about chains the evaluator BUILDS, and it
-- is stated at the door the built chains come through rather than over
-- an arbitrary frame-and-path pair, which no descent ever produces.
--
-- IT IS THE PARK PAIR'S THIRD MEMBER AND SITS BESIDE THEM FOR THE SAME
-- REASON: the share reaches its chains through `shareAdmit` and the
-- cascade through `chainsOf`, and neither filter rearranges into the
-- other, so each face spends the registry's reading through its own
-- filter.

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

-- AND THE FOLD-THROUGH IS NOT THAT STATEMENT: it TAKES the reading as a
-- hypothesis and moves it across a step, so an arbitrary registry
-- reaches its conclusion only through its own premise.
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

-- WHAT THE DRAIN LEAVES IN THE OWNER'S CELL, and the reading is the
-- only part of it a caller can use.  A drain WRITES that cell -- the
-- flatten's live count moves as each inner is subscribed -- so nothing
-- freezes it, and the reinstall the caller then performs owes the new
-- cell's reading at an ARBITRARY floor against the old one's at the
-- same floor.  What the drain never does is put a term in that queue
-- that was not already in it, so the old cell's reading at any floor is
-- the ENTRY queue's at that floor, and `drain-queue-all` carries it the
-- rest of the way to the residue.
--
-- THAT ARGUMENT IS TRUE AND THE STATEMENT WAS STILL FALSE, because the
-- hypothesis said nothing about WHICH node it read.  The no-room arm
-- returns immediately with the state untouched, so at an empty table
-- the cell is `nothing` and the wildcard arm of the floor check calls
-- that true: the premise was satisfiable at ANY entry queue and
-- constrained nothing.  The repair IDENTIFIES the node.  With the
-- owner's cell known to hold this very queue on entry, the untouched
-- post-state reads back as the queue's own, so the premise IS the
-- conclusion in exactly the arm that broke, and stays an ordinary
-- reading about the drain's own cell everywhere else.  The caller
-- already matches on that node, so what it owes is the match's own
-- equation and no new fact.
--
-- ONLY THE QUEUE IS SHARED WITH THE DRAIN'S ARGUMENTS, and the cell's
-- other three fields are free.  The floor check on a flatten cell reads
-- the queue and nothing else, so a cap, a live count and an outer-done
-- flag pinned to the drain's own would buy the statement nothing --
-- and they would cost it its consumer, which drains at a live count one
-- below the one the cell it matched on carries.
--
  -- REFUTED: `Refuted.MergeAllDrain-OwnerQueue`.
  mergeAllDrain-ownerQueue : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    {lim₀ : Maybe ℕ} {act₀ : ℕ} {od : Bool}
    (i : ℕ) (g : Gas) (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s))
    (sched : Sched Γ) (st : EvalSt e) →
    lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim₀ act₀ q od) →
    parkStrat? i (lookupNode allNid (EvalSt.nodes
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
        (mergeAllDrain g allNid κ id now lim act q sched st)))))))) ≡ true →
    all (inputsBelowᵉ i) q ≡ true

-- THE ONE CELL A WALK CANNOT FREEZE, and it is the outer's own.  Every
-- other reading a payload's step has to carry across `thruConsume` is
-- moved by freshness -- the cells the chain below reads sit under a
-- watermark the step does not write.  This one does not: the flatten's
-- consume ENQUEUES into exactly the cell the reading is about, so there
-- is no watermark that both covers it and excludes the write, and no
-- rearrangement of the freshness argument reaches it.
--
-- WHAT KEEPS IT TRUE IS THE PAYLOAD, NOT THE WRITE, which is why the
-- statement takes the payload's own reading as its premise: an enqueue
-- extends the queue by `o`, whose inputs the walk already reads below
-- the sink's floor, and every other arm of the consume leaves the cell
-- as it found it.
--
  -- PROBED: `Probed.ThruConsume-CellPark`.  The ENQUEUE arm only -- a
  --   capacity-zero flatten node taking `input fzero` at floor 1, where
  --   the extended queue's reading reduces through the payload premise.
  --   That is the arm the statement is about and the only one covered:
  --   the subscribing arm, the two non-flatten heads and a NON-EMPTY
  --   starting queue are all untouched, and the last of those is where a
  --   second writer's content would have to show up.
  thruConsume-cellPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (g : Gas) (op : AllOp) (nid : NodeId) (κ : Path Γ u t)
    (id : Id) (now : Tick) (o : Val Γ (obs u))
    (sched : Sched Γ) (st : EvalSt e) →
    inputsBelowᵛ (pathFloor κ) (obs u) o ≡ true →
    parkStrat? (pathFloor κ) (lookupNode nid (EvalSt.nodes st)) ≡ true →
    parkStrat? (pathFloor κ)
      (lookupNode nid (EvalSt.nodes (proj₂ (proj₂ (proj₂
        (thruConsume g op nid κ id now o sched st)))))) ≡ true

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

-- AND THE OUTER'S OWN CELL AT THE INSTALL THAT MINTS IT, which is the
-- degenerate half of the same lemma: a flatten's node is born with an
-- EMPTY queue, so the reading holds at every floor and the only content
-- left is that the lookup finds what was just written.  The scan sibling
-- carries a seed and so owes one; this owes none, and stating it is
-- still worth a line because the alternative is the defer clause
-- unfolding the node table by hand.
installNode-thruPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : ℕ) (op : AllOp) (nid : NodeId) (st : EvalSt e) →
  framePark? k (thru-outer {u = u} op nid)
    (installNode nid (mergeAll-st {t = u} nothing 0 [] false) st) ≡ true
installNode-thruPark {u = u} k op nid st =
  cong (parkStrat? k)
    (lookupNode-setNode nid (mergeAll-st {t = u} nothing 0 [] false)
       (EvalSt.nodes st))

-- AND THE SAME WHERE THE CELL IS ABSTRACT, which is what a head that
-- does not know which flatten it is installing needs: the two lemmas
-- above fix `ns` and pay the reading themselves, and a head handed the
-- cell as a parameter can only be handed the reading beside it.  All
-- that is left is that the lookup finds what was just written.
installNode-cellPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (k : ℕ) (op : AllOp) (nid : NodeId) (ns : NodeState Γ) (st : EvalSt e) →
  parkStrat? k (just ns) ≡ true →
  framePark? k (thru-outer {u = u} op nid) (installNode nid ns st) ≡ true
installNode-cellPark k op nid ns st h =
  trans (cong (parkStrat? k) (lookupNode-setNode nid ns (EvalSt.nodes st))) h

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
frozen-framePark k w (thru-outer _ nid) st st′ hfz hb hp =
  trans (cong (parkStrat? k) (hfz nid hb)) hp
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

-- THE COMPUTED WATERMARK MEETS THE ASKED-FOR ONE, in both directions
-- and neither is arithmetic.  The read side is a fold, so its bound
-- distributes over the chain by the two halves of a join; the write
-- side is a decision, so its soundness is the `≤ᵇ` reflection at each
-- arm.  Together they are what lets a caller stop choosing a witness.
frameRead-below : ∀ {n} {Γ : Ctx n} {s u} (w : ℕ) (f : Frame Γ s u) →
  frameRead f ≤ w → parkBelow w f
frameRead-below w (map-f _)          h = tt
frameRead-below w (take-f _)         h = tt
frameRead-below w (thru-outer _ _)   h = h
frameRead-below w (scan-f _ _)       h = h
frameRead-below w (from-inner _ _ _) h = h

pathRead-below : ∀ {n} {Γ : Ctx n} {u t} (w : ℕ) (κ : Path Γ u t) →
  pathRead κ ≤ w → pathBelow w κ
pathRead-below w root           h = tt
pathRead-below w (share-sink _) h = tt
pathRead-below w (f ↠ p) h =
  frameRead-below w f (≤-trans (m≤m⊔n (frameRead f) (pathRead p)) h)
  , pathRead-below w p (≤-trans (m≤n⊔m (frameRead f) (pathRead p)) h)

-- AND THE TWO READINGS ACROSS ANY STEP THAT IS FRESH ABOVE THE CHAIN,
-- which is every step this development takes.  A freshness receipt says
-- exactly two things -- the counter rose and nothing below the watermark
-- moved -- and those are precisely the two hypotheses the transports
-- want, so a caller with such a receipt owes no arithmetic of its own.
-- Stating them over the receipt rather than over each operation is what
-- keeps the clique's call sites one line apiece: the operation appears
-- only in the receipt the caller already has to produce.
fresh-pathPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (κ : Path Γ u t) (nx nx′ : ℕ) (st st′ : EvalSt e) →
  FreshC (pathRead κ) nx nx′ (EvalSt.nodes st) (EvalSt.nodes st′) →
  pathPark? κ st ≡ true →
  pathPark? κ st′ ≡ true
fresh-pathPark κ nx nx′ st st′ fr hp =
  frozen-pathPark (pathRead κ) κ st st′ (FreshC.frozen fr)
    (pathRead-below (pathRead κ) κ ≤-refl) hp

fresh-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (κ : Path Γ u t) (nx nx′ : ℕ) (st st′ : EvalSt e) →
  FreshC (pathRead κ) nx nx′ (EvalSt.nodes st) (EvalSt.nodes st′) →
  pathOrd? nx κ ≡ true →
  pathOrd? nx′ κ ≡ true
fresh-ord κ nx nx′ st st′ fr ho = pathOrd?-mono _ _ κ (FreshC.nxMono fr) ho

-- AND THE ONE A MINT SPENDS, which is the freeze at the counter rather
-- than at a step's watermark.  An install writes a cell the counter has
-- not handed out yet, and a chain whose order reading holds against that
-- counter reads strictly below it -- so the write is invisible to the
-- reading, and the bound the transport wants is exactly what the order
-- reading hands back.
installNode-pathPark : ∀ {n} {Γ : Ctx n} {u t} {e : Closed Γ t}
  (nid : NodeId) (ns : NodeState Γ) (κ : Path Γ u t) (st : EvalSt e) →
  pathRead κ ≤ nid →
  pathPark? κ st ≡ true →
  pathPark? κ (installNode nid ns st) ≡ true
installNode-pathPark nid ns κ st hb hp =
  frozen-pathPark (pathRead κ) κ st (installNode nid ns st)
    (frozen-setNode (pathRead κ) nid ns (EvalSt.nodes st) hb)
    (pathRead-below (pathRead κ) κ ≤-refl) hp

-- AND THE SAME AT THE CHAIN, which is what a caller re-entering after a
-- subscribe needs and the frame form cannot give it: a subscribe writes
-- only cells its own mint handed out, all at or above the counter it was
-- entered at, so a chain reading below that counter reads back
-- unchanged.  Its bound is the order reading's, exactly as the install's
-- is.
subscribeE-pathPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u w}
  (g : Gas) (b : Closed Γ w) (β : Path Γ w t) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  pathRead κ ≤ Sched.nextNode sched →
  pathPark? κ st ≡ true →
  pathPark? κ (proj₂ (proj₂ (subscribeE g b β bid now sched st))) ≡ true
subscribeE-pathPark g b β κ bid now sched st hb hp =
  frozen-pathPark (Sched.nextNode sched) κ st _
    (subscribeE-nodes-below g b β bid now sched st)
    (pathRead-below (Sched.nextNode sched) κ hb) hp

-- AND THE ORDER HALF OF THE SAME RE-ENTRY, which is one counter step
-- and no case split: the reading bounds the chain's reads from ABOVE by
-- the counter, and a subscribe only raises it.
subscribeE-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u w}
  (g : Gas) (b : Closed Γ w) (β : Path Γ w t) (κ : Path Γ u t)
  (bid : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  pathOrd? (Sched.nextNode sched) κ ≡ true →
  pathOrd? (Sched.nextNode
             (proj₁ (proj₂ (subscribeE g b β bid now sched st)))) κ ≡ true
subscribeE-ord g b β κ bid now sched st ho =
  pathOrd?-mono _ _ κ
    (FreshC.nxMono
      (subscribeE-fresh (Sched.nextNode sched) g b β bid now sched st ≤-refl))
    ho

-- AND THE SAME THREE ACROSS A PAYLOAD'S SUBSCRIBE, which is the one
-- re-entry a drain performs and the one the three above cannot be
-- applied to directly: the payload is subscribed under a MINTED
-- instance cell, so the counter the transports are stated at is not the
-- one the caller holds.  The gas floor is the whole reason these are
-- three lemmas and not three call-site applications -- at `g0` nothing
-- is subscribed at all and the state is returned untouched, so the two
-- arms of every one of them are genuinely different proofs.
subscribeInner-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u w}
  (g : Gas) (op : AllOp) (allNid : NodeId) (β : Path Γ w t) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs w))
  (sched : Sched Γ) (st : EvalSt e) →
  pathOrd? (Sched.nextNode sched) κ ≡ true →
  pathOrd? (Sched.nextNode (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
    (subscribeInner g op allNid β id now o sched st))))))) κ ≡ true
subscribeInner-ord g0 op allNid β κ id now o sched st ho =
  pathOrd?-mono _ _ κ (n≤1+n (Sched.nextNode sched)) ho
subscribeInner-ord (gs fuel) op allNid β κ id now o sched st ho =
  subscribeE-ord fuel o (from-inner op allNid (Sched.nextNode sched) ↠ β) κ id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st
    (pathOrd?-mono _ _ κ (n≤1+n (Sched.nextNode sched)) ho)

subscribeInner-pathPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u w}
  (g : Gas) (op : AllOp) (allNid : NodeId) (β : Path Γ w t) (κ : Path Γ u t)
  (id : Id) (now : Tick) (o : Val Γ (obs w))
  (sched : Sched Γ) (st : EvalSt e) →
  pathRead κ ≤ Sched.nextNode sched →
  pathPark? κ st ≡ true →
  pathPark? κ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
    (subscribeInner g op allNid β id now o sched st)))))) ≡ true
subscribeInner-pathPark g0 op allNid β κ id now o sched st hb hp = hp
subscribeInner-pathPark (gs fuel) op allNid β κ id now o sched st hb hp =
  subscribeE-pathPark fuel o (from-inner op allNid (Sched.nextNode sched) ↠ β) κ
    id now (record sched { nextNode = suc (Sched.nextNode sched) }) st
    (≤-trans hb (n≤1+n (Sched.nextNode sched))) hp

subscribeInner-cellPark : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u w}
  (k : ℕ) (g : Gas) (op : AllOp) (allNid : NodeId) (β : Path Γ w t)
  (κ : Path Γ u t) (id : Id) (now : Tick) (o : Val Γ (obs w))
  (sched : Sched Γ) (st : EvalSt e) →
  suc allNid ≤ Sched.nextNode sched →
  parkStrat? k (lookupNode allNid (EvalSt.nodes st)) ≡ true →
  parkStrat? k (lookupNode allNid (EvalSt.nodes (proj₂ (proj₂ (proj₂ (proj₂ (proj₂
    (subscribeInner g op allNid β id now o sched st)))))))) ≡ true
subscribeInner-cellPark k g0 op allNid β κ id now o sched st hb hp = hp
subscribeInner-cellPark {u = u} k (gs fuel) op allNid β κ id now o sched st hb hp =
  subscribeE-framePark k fuel o (from-inner op allNid (Sched.nextNode sched) ↠ β)
    id now (thru-outer {u = u} op allNid)
    (record sched { nextNode = suc (Sched.nextNode sched) }) st
    (≤-trans hb (n≤1+n (Sched.nextNode sched))) hp

frameAbove?-sound : ∀ {n} {Γ : Ctx n} {s u} (w : ℕ) (f : Frame Γ s u) →
  frameAbove? w f ≡ true → frameAbove w f
frameAbove?-sound w (map-f _)          h = tt
frameAbove?-sound w (scan-f _ nid)     h = ≤ᵇ⇒≤ w nid (T-to h)
frameAbove?-sound w (take-f nid)       h = ≤ᵇ⇒≤ w nid (T-to h)
frameAbove?-sound w (thru-outer _ nid) h = ≤ᵇ⇒≤ w nid (T-to h)
frameAbove?-sound w (from-inner _ a i) h =
  ≤ᵇ⇒≤ w a (T-to (∧-trueˡ h)) , ≤ᵇ⇒≤ w i (T-to (∧-trueʳ h))

-- (4) THE CHAIN-KEYED PARK READING ACROSS ONE FRAME STEP, and it is the
-- subscribe's statement one construct up rather than a second mechanism.
-- A step writes the STEPPED frame's own cell, so what the tail loses is
-- exactly what it ALIASES -- and the ring already freezes everything
-- strictly below a watermark the head sits at or above, so pinning the
-- tail's read cells under that watermark is the whole of it.  The
-- closure premises the free form carried are gone: they priced what the
-- write CONTAINS, and the question was never about the contents.
--
-- THE WATERMARK IS THE TAIL'S OWN READING, so the statement asks for
-- the chain's ORDER and nothing else.  The earlier form quantified the
-- watermark and left every caller to produce one, which put a Σ where
-- an `all` has to go and made the residue a fact about a frame and a
-- path that arrive as independent arguments.  Read off the tail, the
-- bound is the walk's own conjunct.
--
-- DEAD ROUTE: transporting the tail's reading by the SUFFIX property
--   the frame-level statement rests on.  It held while a reinstall was
--   the only reachable write, and stopped holding when the park reading
--   gained an arm at a cell a step OVERWRITES: an `all` reading tolerates
--   losing a prefix and nothing tolerates a replacement.
pathPark-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  pathOrd? (Sched.nextNode sched) (f ↠ κ) ≡ true →
  pathPark? κ st ≡ true →
  pathPark? κ
    (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame g id now f κ vals fin sched st)))))
      ≡ true
pathPark-step g id now f κ vals fin sched st ho hp =
  frozen-pathPark (pathRead κ) κ st _
    (FreshC.frozen
      (stepFrame-fresh (pathRead κ) g id now f κ vals fin sched st
        (pathOrd?-read (Sched.nextNode sched) κ (proj₂ SQ))
        (frameAbove?-sound (pathRead κ) f (proj₁ SQ))))
    (pathRead-below (pathRead κ) κ ≤-refl) hp
  where
  SP = ∧-true (pathCell (f ↠ κ) ≤ᵇ Sched.nextNode sched)
              (frameAbove? (pathRead κ) f ∧ pathOrd? (Sched.nextNode sched) κ) ho
  SQ = ∧-true (frameAbove? (pathRead κ) f)
              (pathOrd? (Sched.nextNode sched) κ) (proj₂ SP)

-- AND THE ORDER ITSELF ACROSS THE SAME STEP, which is the counter's
-- half: the chain loses its head and the counter only rises, so the
-- tail's ordering is the head's minus one hop, widened once by the
-- monotonicity the freshness ring already reports.
pathOrd-step : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (g : Gas) (id : Id) (now : Tick)
  (f : Frame Γ s u) (κ : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) →
  pathOrd? (Sched.nextNode sched) (f ↠ κ) ≡ true →
  pathOrd?
    (Sched.nextNode
      (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame g id now f κ vals fin sched st))))))
    κ ≡ true
pathOrd-step g id now f κ vals fin sched st ho =
  pathOrd?-mono _ _ κ
    (FreshC.nxMono
      (stepFrame-fresh (pathRead κ) g id now f κ vals fin sched st
        (pathOrd?-read (Sched.nextNode sched) κ (proj₂ SQ))
        (frameAbove?-sound (pathRead κ) f (proj₁ SQ))))
    (proj₂ SQ)
  where
  SP = ∧-true (pathCell (f ↠ κ) ≤ᵇ Sched.nextNode sched)
              (frameAbove? (pathRead κ) f ∧ pathOrd? (Sched.nextNode sched) κ) ho
  SQ = ∧-true (frameAbove? (pathRead κ) f)
              (pathOrd? (Sched.nextNode sched) κ) (proj₂ SP)

-- AND THE SAME ORDER OVER A SIBLING'S WORK, which is the fan-out's
-- shape rather than the descent's: the chains a fold did not walk are
-- the SAME chains afterwards, so nothing about the reading changes and
-- the only thing that moves is the counter it is read against.  Both are
-- bodies over one counter leaf apiece, which is what makes them
-- corollaries rather than a second mechanism -- and it is why the
-- ordering could be made Boolean at all: a Σ cannot ride in an `all`,
-- and the fan-out owes its chains pointwise.
foldPath-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
  (p : Path Γ u t) (vals : List (Val Γ u))
  (evs : List (InstEvent (Val Γ t))) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (ps : List (RegId × Path Γ u t)) →
  all (λ rp → pathOrd? (Sched.nextNode sched) (proj₂ rp)) ps ≡ true →
  all (λ rp → pathOrd?
         (Sched.nextNode
           (proj₁ (proj₂ (foldPath sf gas id now envSrc p vals evs fin sched st))))
         (proj₂ rp))
      ps ≡ true
foldPath-ord sf gas id now envSrc p vals evs fin sched st ps h =
  all-impl _ _
    (λ rp → pathOrd?-mono _ _ (proj₂ rp)
              (foldPath-nextNode sf gas id now envSrc p vals evs fin sched st))
    ps h

chainStep-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (path : Path Γ (arrTy a) t)
  (sched : Sched Γ) (st : EvalSt e)
  (chains : List (RegId × Path Γ (arrTy a) t)) →
  all (λ rc → pathOrd? (Sched.nextNode sched) (proj₂ rc)) chains ≡ true →
  all (λ rc → pathOrd?
         (Sched.nextNode (proj₁ (proj₂ (chainStep id a path sched st))))
         (proj₂ rc))
      chains ≡ true
chainStep-ord id a path sched st chains h =
  all-impl _ _
    (λ rc → pathOrd?-mono _ _ (proj₂ rc)
              (chainStep-nextNode id a path sched st))
    chains h

------------------------------------------------------------------
-- THE FOUR ENTRY READINGS, EACH A FILTER OF ONE THE REGISTRY CARRIES.
--
-- Each was once a leaf whose free form is REFUTED, and the premise
-- that repairs it is not a call site's convenience: it is the
-- registry-wide reading `capsOK?` now carries, owed by whatever WRITES
-- what it reads.  With that premise in hand nothing here is
-- mathematics -- an admission filter drops entries and rewrites none,
-- so the reading travels through it -- and the two park rows add only
-- a node-table transport, since neither latch touches the store the
-- reading looks at.
------------------------------------------------------------------

-- the cascade's latch is a completion mark and a scratch reset, and
-- the store it leaves is the one it was handed.  Cased on the same
-- flag `cascadeLatch-caps` is
cascadeLatch-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  EvalSt.nodes st ≡ EvalSt.nodes (cascadeLatch a st)
cascadeLatch-nodes a st with Arrival.isLast a
... | true  = refl
... | false = refl

shareAdmit-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (sched : Sched Γ) (st : EvalSt e) →
  regOrd? (Sched.nextNode sched) (EvalSt.registry st) ≡ true →
  all (λ rp → pathOrd? {n} {Γ} {lookup Γ i} {t} (Sched.nextNode sched) (proj₂ rp))
      (shareAdmit i (EvalSt.registry st)) ≡ true
shareAdmit-ord i sched st h =
  shareAdmit-chQ (λ {u} _ κ → pathOrd? (Sched.nextNode sched) κ) i
    (EvalSt.registry st) h

cascade-admit-ord : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  regOrd? (Sched.nextNode sched) (EvalSt.registry st) ≡ true →
  all (λ rc → pathOrd? {n} {Γ} {arrTy a} {t} (Sched.nextNode sched) (proj₂ rc))
      (chainsOf a st) ≡ true
cascade-admit-ord a sched st h =
  chainsGo-chQ (λ {u} _ κ → pathOrd? (Sched.nextNode sched) κ) a
    (EvalSt.registry st) h

shareAdmit-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (i : Fin n) (fin : Bool) (st : EvalSt e) →
  regPark? (EvalSt.registry st) st ≡ true →
  all (λ rp → pathPark? {n} {Γ} {lookup Γ i} {t} (proj₂ rp) (shareLatch i fin st))
      (shareAdmit i (EvalSt.registry st)) ≡ true
shareAdmit-park i false st h =
  shareAdmit-chQ (λ {u} _ κ → pathPark? κ st) i (EvalSt.registry st) h
shareAdmit-park i true  st h =
  shareAdmit-chQ (λ {u} _ κ → pathPark? κ (shareLatch i true st)) i
    (EvalSt.registry st)
    (regPark?-nodes (EvalSt.registry st) st (shareLatch i true st) refl h)

cascade-admit-park : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (st : EvalSt e) →
  regPark? (EvalSt.registry st) st ≡ true →
  all (λ rc → pathPark? {n} {Γ} {arrTy a} {t} (proj₂ rc) (cascadeLatch a st))
      (chainsOf a st) ≡ true
cascade-admit-park a st h =
  chainsGo-chQ (λ {u} _ κ → pathPark? κ (cascadeLatch a st)) a
    (EvalSt.registry st)
    (regPark?-nodes (EvalSt.registry st) st (cascadeLatch a st)
       (cascadeLatch-nodes a st) h)

-- THE TWO READINGS ACROSS A WHOLE WALK, and neither is a new fact.  A
-- walk mints strictly ABOVE the counter it entered at, so every cell
-- the chain reads is frozen under it and the counter only rises --
-- which is exactly the pair `FreshC` records.  `subscribeE-fresh` is
-- that receipt and the two `fresh-` transports spend it, so this is one
-- composition; it is stated once because every push site needs it, and
-- the order reading is what unlocks the freezing premise, since a chain
-- whose cells outran the counter is a chain no run built
subscribeE-readings : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (g : Gas) (b : Closed Γ u) (κ : Path Γ u t) (id : Id) (now : Tick)
  (sched : Sched Γ) (st : EvalSt e) →
  pathOrd? (Sched.nextNode sched) κ ≡ true →
  pathPark? κ st ≡ true →
  let r = subscribeE g b κ id now sched st
  in (pathOrd? (Sched.nextNode (proj₁ (proj₂ r))) κ ≡ true)
     × (pathPark? κ (proj₂ (proj₂ r)) ≡ true)
subscribeE-readings g b κ id now sched st ho hp =
    fresh-ord κ (Sched.nextNode sched) (Sched.nextNode (proj₁ (proj₂ r))) st
      (proj₂ (proj₂ r)) FR ho
  , fresh-pathPark κ (Sched.nextNode sched) (Sched.nextNode (proj₁ (proj₂ r))) st
      (proj₂ (proj₂ r)) FR hp
  where
  r  = subscribeE g b κ id now sched st
  FR = subscribeE-fresh (pathRead κ) g b κ id now sched st
         (pathOrd?-read (Sched.nextNode sched) κ ho)
