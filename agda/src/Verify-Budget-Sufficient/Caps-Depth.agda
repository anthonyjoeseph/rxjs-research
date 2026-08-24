-- THE DEPTH MIRROR: how deep a RUN nests its subscribes.

-- The subscribe clique in .Subscribe-Face carries a sufficiency
-- hypothesis for the budget (`nest o sl cs ≤ bud`) and for the operator
-- count (`suc (sizeᵉ b) ≤ ops`).  It needs a third, for the DEPTH FUEL
-- `dep`, because one arc of its cycle spends a unit of it — a frame's
-- payload walk runs at `dep` minus one, on the refreshed budget — and
-- at `dep = 0` there is nothing to descend into, while the walk still
-- re-enters the family.  A probe module since DELETED showed that gap is
-- structural: `fLvlD S W zero` makes no recursive call (that is what
-- carries the family's termination) and a depth-zero walk STRICTLY
-- overshoots it, so no rearrangement closes those clauses.  They have
-- to be unreachable, and only a hypothesis can make them so.

-- WHAT THE CURRENCY IS, AND WHY NOTHING SMALLER WORKS.  Three cheaper
-- candidates are machine-refuted and must not be re-proposed:
--
--   · bare positivity, "1 ≤ dep maintained by descent" — Mu-Nest-Probe
--     § 1: the maintenance step at dep = 1 demands 1 ≤ 0;
--   · any measure of the SYNTAX or of the subscribed VALUE —
--     Mu-Nest-Probe § 2 (the share edge's callee is a stored def
--     structurally unrelated to the caller's `input i`) and
--     Nest-Budget-Probe § 3 (a `scanᵉ` under an *All mints payloads
--     whose nesting is the FOLD COUNT, while the carrier's own syntax
--     stands still).  Depth demand is dynamic; no static measure
--     dominates it;
--   · the evaluator's own GAS.  It threads perfectly — the peel
--     discipline at Rx.Evaluator was designed as exactly this
--     bridge — but it is FALSE at the only instantiation planned for
--     `dep`: `capsAt` runs at `d := capsH e sl id` and the instant's gas
--     sits one `blowH` story ABOVE that (Rx.Evaluator, "a
--     stratification, not a domination").  A hypothesis known false at
--     its own supply site is not a hypothesis.

-- SO THE CURRENCY IS THE RUN ITSELF.  Each head below shadows one
-- evaluator head, clause for clause, taking the SAME arguments and
-- returning the `⊔` of its callees' mirrors on the SAME expressions —
-- recomputing the evaluator's intermediates exactly as the clause's own
-- `let` does.  Two clauses add a `suc`, and they are the two arcs the
-- caps proof spends `dep` on:
--
--   · `depthFrame`'s thru-outer — `stepFrame`'s payload walk, the one
--     arc that re-reads the budget (Subscribe-Face's `stepFrame-caps`
--     comment names it), and
--   · `depthFinC`'s `yes refl` — `innerFinish`'s concat drain, one
--     subscribe per parked inner.

-- NOT at `subscribeInner`'s gas peel, NOT at μ, NOT at the share
-- connect: the mirror mirrors where the CAPS PROOF spends, not where
-- the evaluator peels gas.  Being the depth this very run reaches, it is
-- the WEAKEST hypothesis that can close the clique, so any later
-- discharge argument factors through it.

-- SOME CLAUSES ARE DELIBERATELY TOO BIG, and that is free.  Where the
-- evaluator dispatches on a Bool whose branches subscribe the same
-- things or nothing (`flattenDrain`'s capacity gate, `innerReact`'s
-- liveness test, `subscribeSharedSlot`'s two joins, `thruConsume`'s
-- concat/exhaust node reads), the mirror ignores the test and reports
-- the SPENDING branch.  A mirror above the truth only ever demands more
-- depth, and it saves the consuming clause a projection.  Where the
-- dispatch is TYPE-FORCING or the branches thread different states
-- (`innerFinish`'s `w ≟ᵗ s`, `subscribeE`'s slot and take count,
-- `thruConsume`'s switch, `shareGo`'s cancellation), it cannot be
-- ignored, and the scrutinee becomes a real argument of a helper head
-- rather than a `with` — so the mirror stays free of with-abstraction
-- and every consumer can read its equations off the clause list.

-- NOT `abstract`, on purpose: the whole point is that a caps clause's
-- hypothesis REDUCES in that clause's own pattern context, to a `⊔` of
-- its callees' mirrors.  Opaque, every supply would need a rewrite.

-- WHAT IS STILL OWED, AND IT IS OWED AT THE TOP.  `dep` is instantiated
-- nowhere yet.  When it is (`capsAt`, .Caps, reads
-- `d := capsH e sl id`), the obligation is ONE statement —
-- `depthChain`/`depthE` at the instant's own entry arguments ≤
-- `capsH e sl id` — the very inequality Rx.Evaluator records as
-- "owed by the signature pass rather than by this definition ...
-- Reported, not assumed".  Two facts about it are already known: the
-- gas bridge does NOT suffice (the stratification above), and any real
-- proof must count DELIVERIES, not just static nesting
-- (Nest-Count-Probe: stories per instant = deliveries × nesting).
module Verify-Budget-Sufficient.Caps-Depth where

open import Data.Bool    using (Bool; true; false; if_then_else_)
open import Data.Nat     using (ℕ; zero; suc; _⊔_; _≤_; z≤n)
open import Data.Nat.Properties using (≤-trans; m≤m⊔n; m≤n⊔m; ⊔-lub)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec     using (lookup)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim  using (Gas; g0; gs; Id; Tick; Source;
                            InstEmit; InstEvent; close; exhausted)
open import Rx.Exp   using (Ctx; Closed; Val; obs; _≟ᵗ_; evalTm; unfoldμ; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
  flattenᵉ; switchAllᵉ; exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Slots using (Slot; scripted; shared)
open import Rx.Evaluator
  using (Sched; EvalSt; Arrival; NodeId; RegId; Path; Frame; AllOp; Stream; NodeState; scan-st;
  take-st; flatten-st; switch-st; exhaust-st; flattenᵒ; switchᵒ; exhaustᵒ;
  root; share-sink; _↠_; map-f; scan-f; take-f; from-inner; thru-outer; mintNode; installNode;
  lookupNode; register; splitEvents; switchKill; shareLatch; shareAdmit; subscribeE;
  subscribeInner; thruConsume; stepFrame; foldPath; chainStep; arrVal; arrSource; arrTick;
  arrTy; budgetAt)

------------------------------------------------------------------
-- THE FAMILY.  One head per evaluator head on the subscribe path, with
-- that head's own argument list; the four helper heads carry a
-- scrutinee as a real argument, last.
------------------------------------------------------------------

depthE : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
       → Gas → Closed Γ u → Path Γ u t → Id → Tick
       → Sched Γ → EvalSt e → ℕ

-- the `input` slot read: only a `shared` def is subscribed, and its `d`
-- comes out of the constructor, so the slot cannot be ignored
depthSlot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Gas → (i : Fin n) → Path Γ (lookup Γ i) t → Id → Tick
          → Sched Γ → EvalSt e → Slot Γ (toℕ i) (lookup Γ i) → ℕ

-- a take's count: the `suc k` branch installs a node whose state reads
-- `k`, so the two branches do not agree
depthTake : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
          → Gas → Closed Γ u → Path Γ u t → Id → Tick
          → Sched Γ → EvalSt e → Val Γ _ → ℕ

depthShSlot : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
            → Gas → (i : Fin n) → Closed Γ (lookup Γ i)
            → Path Γ (lookup Γ i) t → Id → Tick
            → Sched Γ → EvalSt e → ℕ

depthConn : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Gas → (i : Fin n) → Closed Γ (lookup Γ i)
          → Path Γ (lookup Γ i) t → Id → Tick
          → Sched Γ → EvalSt e → ℕ

depthAll : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
         → Gas → AllOp → NodeState Γ → Closed Γ (obs u) → Path Γ u t
         → Id → Tick → Sched Γ → EvalSt e → ℕ

depthInner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
           → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
           → Val Γ (obs u) → Sched Γ → EvalSt e → ℕ

depthWalk : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
          → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
          → List (Val Γ (obs u)) → Sched Γ → EvalSt e → ℕ

depthConsume : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
             → Gas → AllOp → NodeId → Path Γ u t → Id → Tick
             → Val Γ (obs u) → Sched Γ → EvalSt e → ℕ

-- switchAll's node read: the outgoing inner's cut runs BEFORE the new
-- subscribe, so the state that subscribe sees depends on the read
depthConsumeS : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
              → Gas → NodeId → Path Γ u t → Id → Tick
              → Val Γ (obs u) → Sched Γ → EvalSt e → Maybe (NodeState Γ) → ℕ

depthDrain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           → Gas → NodeId → Path Γ s t → Id → Tick
           → List (Closed Γ s) → Sched Γ → EvalSt e → ℕ

depthFin : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
         → Gas → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
         → List (Val Γ s) → Sched Γ → EvalSt e → Maybe (NodeState Γ) → ℕ

-- SPENDING ARC 2 lives in this head's `yes` clause
depthFinC : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s w}
          → Gas → NodeId → Path Γ s t → Id → Tick
          → List (Closed Γ w) → Sched Γ → EvalSt e → Dec (w ≡ s) → ℕ

depthReact : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
           → Gas → AllOp → NodeId → NodeId → Path Γ s t → Id → Tick
           → List (Val Γ s) → Sched Γ → EvalSt e → Bool → ℕ

depthFrame : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
           → Gas → Id → Tick → Frame Γ s u → Path Γ u t
           → List (Val Γ s) → Bool → Sched Γ → EvalSt e → ℕ

depthBurst : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
           → Gas → Id → Tick → Frame Γ s u → Path Γ u t
           → Stream Γ s → Sched Γ → EvalSt e → ℕ

depthFold : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
          → Gas → ℕ → Id → Tick → Source → Path Γ u t
          → List (Val Γ u) → List (InstEvent (Val Γ t)) → Bool
          → Sched Γ → EvalSt e → ℕ

depthDisp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
          → Gas → ℕ → Id → Tick → (i : Fin n)
          → List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e → ℕ

depthShareGo : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             → Gas → ℕ → Id → Tick → (i : Fin n)
             → List (Val Γ (lookup Γ i)) → Bool
             → List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e → ℕ


------------------------------------------------------------------
-- THE SUBSCRIBE SIDE
------------------------------------------------------------------

depthE fuel (input i) κ id now sched st =
  depthSlot fuel i κ id now sched st (Sched.slots sched i)
-- one-shots and the two parking constructors reach no subscribe at all
depthE fuel (ofᵉ ts)     κ id now sched st = 0
depthE fuel emptyᵉ       κ id now sched st = 0
depthE fuel (deferᵉ b)   κ id now sched st = 0
depthE g0   (μᵉ body)    κ id now sched st = 0
depthE fuel (varᵉ ())    κ id now sched st
-- a chain edge: the source at one more frame, then its burst back
-- through that frame — the same sweep, never a nesting level
depthE fuel (mapᵉ f b) κ id now sched st =
  depthE fuel b (map-f f ↠ κ) id now sched st
  ⊔ depthBurst fuel id now (map-f f) κ (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where r = subscribeE fuel b (map-f f ↠ κ) id now sched st
depthE fuel (takeᵉ count b) κ id now sched st =
  depthTake fuel b κ id now sched st (evalTm count)
depthE fuel (scanᵉ f seed b) κ id now sched st =
  depthE fuel b (scan-f f nid ↠ κ) id now sched₁ st₀
  ⊔ depthBurst fuel id now (scan-f f nid) κ (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (scan-st (evalTm seed)) st
  r      = subscribeE fuel b (scan-f f nid ↠ κ) id now sched₁ st₀
-- the four *All edges delegate whole
depthE {u = u} fuel (flattenᵉ lim b) κ id now sched st =
  depthAll fuel flattenᵒ (flatten-st {t = u} lim 0 [] false) b κ id now sched st
depthE fuel (switchAllᵉ b)  κ id now sched st =
  depthAll fuel switchᵒ (switch-st nothing false) b κ id now sched st
depthE fuel (exhaustAllᵉ b) κ id now sched st =
  depthAll fuel exhaustᵒ (exhaust-st false false) b κ id now sched st
-- a μ's re-entry: the unfolding is LARGER than the μ, so it is a fresh
-- entry rather than a chain edge — and it is NOT a spend here, because
-- `op-step-mu` already charges it one nesting level on the caps side
depthE (gs fuel) (μᵉ body) κ id now sched st =
  depthE fuel (unfoldμ body) κ id now sched st

depthSlot fuel i κ id now sched st (shared d) =
  depthShSlot fuel i d κ id now sched st
depthSlot fuel i κ id now sched st (scripted _) = 0

depthTake fuel b κ id now sched st zero = 0
depthTake fuel b κ id now sched st (suc k) =
  depthE fuel b (take-f nid ↠ κ) id now sched₁ st₀
  ⊔ depthBurst fuel id now (take-f nid) κ (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid (take-st (suc k)) st
  r      = subscribeE fuel b (take-f nid ↠ κ) id now sched₁ st₀

-- a spent share and a mid-flight join subscribe NOTHING, so the mirror
-- reports the connect unconditionally and the other two branches simply
-- never use their hypothesis
depthShSlot fuel i d κ id now sched st = depthConn fuel i d κ id now sched st

-- the connect's `burstCompleted` test runs AFTER the def's subscribe and
-- both branches keep it, so the mirror is constant in it
depthConn g0 i d κ id now sched st = 0
depthConn (gs fuel′) i d κ id now sched st =
  depthE fuel′ d (share-sink i) id now sched
    (register (toℕ i) κ
      (record st { connectedShares = toℕ i ∷ EvalSt.connectedShares st }))

depthAll fuel op initialState b κ id now sched st =
  depthE fuel b (thru-outer op nid ↠ κ) id now sched₁ st₀
  ⊔ depthBurst fuel id now (thru-outer op nid) κ
      (proj₁ r) (proj₁ (proj₂ r)) (proj₂ (proj₂ r))
  where
  nid    = proj₁ (mintNode sched)
  sched₁ = proj₂ (mintNode sched)
  st₀    = installNode nid initialState st
  r      = subscribeE fuel b (thru-outer op nid ↠ κ) id now sched₁ st₀

-- a subscribe with no gas installs nothing.  With gas it peels one and
-- enters the payload — a nesting level on the evaluator's own reckoning,
-- but NOT a `suc` here: the caps side charges a payload subscribe
-- through `inner-step`, off the frame that installed it
depthInner g0 op allNid κ id now o sched st = 0
depthInner (gs fuel) op allNid κ id now o sched st =
  depthE fuel o (from-inner op allNid (Sched.nextNode sched) ↠ κ) id now
    (record sched { nextNode = suc (Sched.nextNode sched) }) st

depthWalk fuel op nid κ id now []       sched₀ st₀ = 0
depthWalk fuel op nid κ id now (o ∷ os) sched₀ st₀ =
  depthConsume fuel op nid κ id now o sched₀ st₀
  ⊔ depthWalk fuel op nid κ id now os
      (proj₁ (proj₂ (proj₂ r))) (proj₂ (proj₂ (proj₂ r)))
  where r = thruConsume fuel op nid κ id now o sched₀ st₀

-- a flatten with a free lane always subscribes; its park and exhaust's
-- busy-drop subscribe nothing, and both non-parking branches subscribe
-- at the INCOMING state, so those two node reads are ignored
depthConsume fuel flattenᵒ nid κ id now o sched₀ st₀ =
  depthInner fuel flattenᵒ nid κ id now o sched₀ st₀
depthConsume fuel exhaustᵒ nid κ id now o sched₀ st₀ =
  depthInner fuel exhaustᵒ nid κ id now o sched₀ st₀
depthConsume fuel switchᵒ  nid κ id now o sched₀ st₀ =
  depthConsumeS fuel nid κ id now o sched₀ st₀ (lookupNode nid (EvalSt.nodes st₀))

depthConsumeS fuel nid κ id now o sched₀ st₀ (just (switch-st cur od)) =
  depthInner fuel switchᵒ nid κ id now o
    (proj₁ (proj₂ (switchKill cur sched₀ st₀)))
    (proj₂ (proj₂ (switchKill cur sched₀ st₀)))
depthConsumeS fuel nid κ id now o sched₀ st₀ _ = 0

-- the drain stops at the first inner that stays open; the mirror walks
-- the whole queue, which is above the truth and costs the consuming
-- clause nothing
depthDrain fuel allNid κ id now []      sched₀ st₀ = 0
depthDrain fuel allNid κ id now (o ∷ q) sched₀ st₀ =
  depthInner fuel flattenᵒ allNid κ id now o sched₀ st₀
  ⊔ depthDrain fuel allNid κ id now q
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r)))))
  where r = subscribeInner fuel flattenᵒ allNid κ id now o sched₀ st₀

-- switch clears a slot, exhaust clears a flag, and every catch-all
-- hands the payload straight back: the flatten drain is the only finish
-- that subscribes anything, and at an unbounded limit its queue is
-- empty, which is the counter decrement the merge face used to be
depthFin {s = s} fuel flattenᵒ allNid inst κ id now vals sched st
         (just (flatten-st {t = w} lim act q od)) =
  depthFinC fuel allNid κ id now q sched st (w ≟ᵗ s)
depthFin fuel op allNid inst κ id now vals sched st nd = 0

-- SPENDING ARC 2: a drain is a WALK under this finishing frame, so it
-- runs at one less depth, exactly as a thru-outer's walk does
depthFinC fuel allNid κ id now q sched st (yes refl) =
  suc (depthDrain fuel allNid κ id now q sched st)
depthFinC fuel allNid κ id now q sched st (no _) = 0

-- a fin that is absorbed by a live sibling registration finishes
-- nothing; the mirror reports the finish either way
depthReact fuel op allNid inst κ id now vals sched st false = 0
depthReact fuel op allNid inst κ id now vals sched st true =
  depthFin fuel op allNid inst κ id now vals sched st
    (lookupNode allNid (EvalSt.nodes st))

------------------------------------------------------------------
-- THE FRAME SIDE
------------------------------------------------------------------

-- map/scan/take reshape values and subscribe nothing
depthFrame fuel id now (map-f fn)      κ vals fin sched st = 0
depthFrame fuel id now (scan-f fn nid) κ vals fin sched st = 0
depthFrame fuel id now (take-f nid)    κ vals fin sched st = 0
depthFrame fuel id now (from-inner op allNid inst) κ vals fin sched st =
  depthReact fuel op allNid inst κ id now vals sched st fin
-- SPENDING ARC 1, and the only place the depth fuel splits: a frame is
-- the one arc of the cycle that RE-READS the budget, and `fLvlD S W
-- (suc d) J` unfolds to its payload walk at `d`
depthFrame fuel id now (thru-outer op nid) κ vals fin sched st =
  suc (depthWalk fuel op nid κ id now vals sched st)

depthBurst fuel id now f κ []         sched st = 0
depthBurst {Γ = Γ} {u = u} fuel id now f κ (em ∷ ems) sched st =
  depthFrame fuel id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st
  ⊔ depthBurst fuel id now f κ ems
      (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
  where
  -- `A` pinned as .Subscribe-Face pins it, so the two `sp`s are the same
  -- term and a consumer's projections meet these without a rewrite
  sp = splitEvents {A = Val Γ u} (InstEmit.events em)
  r  = stepFrame fuel id now f κ (proj₁ sp) (proj₂ (proj₂ sp)) sched st

------------------------------------------------------------------
-- THE DELIVERY SIDE.  A delivery threads the SYNC fuel unchanged and
-- climbs no nesting level of its own; it reaches frames, and those
-- frames are where the depth goes.
------------------------------------------------------------------

depthFold sf gas id now envSrc root vals evs fin sched st = 0
depthFold sf gas id now envSrc (share-sink i) vals evs fin sched st =
  depthDisp sf gas id now i vals fin sched st
depthFold sf gas id now envSrc (f ↠ path′) vals evs fin sched st =
  depthFrame sf id now f path′ vals fin sched st
  ⊔ depthFold sf gas id now envSrc path′ (proj₁ r) (evs ++ proj₁ (proj₂ r))
      (proj₁ (proj₂ (proj₂ r)))
      (proj₁ (proj₂ (proj₂ (proj₂ r)))) (proj₂ (proj₂ (proj₂ (proj₂ r))))
  where r = stepFrame sf id now f path′ vals fin sched st

depthDisp sf zero      id now i vals fin sched st = 0
depthDisp sf (suc gas) id now i vals fin sched st =
  depthShareGo sf gas id now i vals fin
    (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

-- A CANCELLED CHAIN DELIVERS NOTHING, and the surviving one delivers at
-- a state the cancelled branch never builds — so unlike the other Bool
-- dispatches this one cannot be collapsed to its spending branch.  It is
-- collapsed the OTHER way instead: the tail is reported at BOTH states,
-- so the mirror covers whichever the test picks and the consuming clause
-- reads its case off a projection rather than off a with-abstraction.
-- Both tails recurse on `ps`, so the walk still terminates on the list
depthShareGo sf gas id now i vals fin []               sched₀ st₀ = 0
depthShareGo sf gas id now i vals fin ((rid , p) ∷ ps) sched₀ st₀ =
  depthShareGo sf gas id now i vals fin ps sched₀ st₀
  ⊔ (depthFold sf gas id now (toℕ i) p vals closes fin sched₀ st₁
     ⊔ depthShareGo sf gas id now i vals fin ps (proj₁ (proj₂ r)) (proj₂ (proj₂ r)))
  where
  closes = if fin then close (toℕ i) exhausted ∷ [] else []
  st₁    = record st₀ { delivered = rid ∷ EvalSt.delivered st₀ }
  r      = foldPath sf gas id now (toℕ i) p vals closes fin sched₀ st₁

------------------------------------------------------------------
-- ONE ARRIVAL INTO ONE CHAIN — outside the block, since nothing above
-- calls it.  The gas it reads is the instant's own, which is where the
-- top-level obligation named in this module's head will land
------------------------------------------------------------------

depthChain : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
           → Id → (a : Arrival Γ) → Path Γ (arrTy a) t
           → Sched Γ → EvalSt e → ℕ
depthChain {n = n} {e = e} id a path sched st =
  depthFold (budgetAt e (Sched.slots sched) id) n id (arrTick a) (arrSource a)
            path (arrVal a ∷ [])
            (if Arrival.isLast a then close (arrSource a) exhausted ∷ [] else [])
            (Arrival.isLast a) sched st

------------------------------------------------------------------
-- ONE ARRIVAL INTO EVERY LIVE CHAIN, mirroring `cascadeGo` clause for
-- clause.  This is the DELIVERY side's top measure, and it is separate
-- because the delivery machinery — `chainStep`, `foldPath`, `stepFrame`
-- — sits wholly outside `depthE`'s induction, so a subscribe-side bound
-- reaches none of it.  The walk's `cascadeGo-go`
-- reads its per-chain premise off this head, so the two clauses must
-- match the evaluator's exactly or the projections stop being definitional.
--
-- NO `with` HERE, AND THE REASON IS `depthShareGo`'s, VERBATIM.  A
-- cancelled chain delivers nothing, so the honest measure would skip it
-- and branch on `any (_≡ᵇ rid) (EvalSt.cancelled st)` — but the consumer
-- (`cascadeGo-go`) already with-abstracts that same scrutinee, and a
-- with-abstraction does NOT rewrite the types of already-bound
-- hypotheses.  The depth premise would stay stuck on the unabstracted
-- test in every branch, and no case analysis could unstick it.
--
-- So this head is collapsed the OTHER way, exactly as `depthShareGo`'s
-- cons clause is: the tail is reported at BOTH states, so the mirror
-- covers whichever the test picks and the consuming clause reads its
-- case off a PROJECTION instead.  That lands the clause in the shape
-- `a ⊔ (b ⊔ c)`, which is precisely what `lub3-l/m/r` below project —
-- the live chain runs at the delivered-marked state and the rest at the
-- state that chain left, which is where `chainStep` puts them
------------------------------------------------------------------

depthCascade : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
             → (a : Arrival Γ) → Id
             → List (RegId × Path Γ (arrTy a) t)
             → Sched Γ → EvalSt e → ℕ
depthCascade a id []                   sched st = 0
depthCascade a id ((rid , c) ∷ chains) sched st =
  depthCascade a id chains sched st
  ⊔ (depthChain id a c sched st₀
     ⊔ depthCascade a id chains (proj₁ (proj₂ cs)) (proj₂ (proj₂ cs)))
  where
  st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
  cs  = chainStep id a c sched st₀

------------------------------------------------------------------
-- PROJECTING A THREE-CALLEE CLAUSE.  `depthShareGo`'s cons clause is the
-- only one above with three callees, `a ⊔ (b ⊔ c)`, and a consumer needs
-- each summand separately.
--
-- THE BOUNDS ARE EXPLICIT AND MUST STAY SO.  `_⊔_` is a DEFINED RECURSIVE
-- function on ℕ, not a constructor, so `_a ⊔ (b ⊔ c) ≟ A ⊔ (B ⊔ C)` is
-- not a first-order match: Agda reports `blocked on _a` and gives up.  An
-- implicit-bound version typechecks fine as a DEFINITION — its bounds are
-- variables — and then fails at every CALL.  That is the whole of the
-- Stage-A build failure it caused, and `Lub3-Probe` records it.
--
-- Naming the bounds turns the INVERSION into a CHECK, which just unfolds
-- both sides.  The one-level projections elsewhere in the clique get away
-- with `m≤m⊔n _ _` only because both ends of their `≤-trans` are already
-- pinned, leaving no `⊔` to invert; that is not licence to omit bounds
-- here.  Call these with the summands bound by name in the consuming
-- clause's own `where`.
------------------------------------------------------------------

lub3-l : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → a ≤ d
lub3-l a b c h = ≤-trans (m≤m⊔n a (b ⊔ c)) h

lub3-m : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → b ≤ d
lub3-m a b c h = ≤-trans (m≤m⊔n b c) (≤-trans (m≤n⊔m a (b ⊔ c)) h)

lub3-r : ∀ a b c {d} → a ⊔ (b ⊔ c) ≤ d → c ≤ d
lub3-r a b c h = ≤-trans (m≤n⊔m b c) (≤-trans (m≤n⊔m a (b ⊔ c)) h)
