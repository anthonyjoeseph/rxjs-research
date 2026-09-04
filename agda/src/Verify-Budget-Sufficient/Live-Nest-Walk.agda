-- THE LIVE LIST'S DEPTH ALONG ONE CHAIN, walked frame by frame -- the
-- third and last of the chain's arms to stop being one postulate, and
-- the only one whose per-frame leaf cannot be paid out of the
-- potential alone.
--
-- WHY THE POTENTIAL IS NOT ENOUGH HERE, and it is a property of the
-- currency rather than of the walk.  The nesting-DEPTH measures read
-- ZERO into a deferred body -- that truncation is what makes the fixed
-- point safe -- so an outer frame handed a deferred observable sees a
-- potential of zero and mints a live whose pending payload is the body
-- itself, at whatever depth the body has.  A charge built from the
-- depth measures is blind to exactly that step, which is what killed
-- the additive reading of this arm.  What is not blind to it is SIZE,
-- and depth is under size everywhere; so the outer frame's side
-- condition here is a size bound on the values reaching it, and the
-- four other frame kinds owe nothing.
--
-- AND THE CONCLUSION CARRIES TWO TERMS THE WALKED PATH DOES NOT SAY.
-- A scripted cold slot's subscribe mints a live out of SCRIPT data, so
-- the slots are in it; and a share sink fans into registry chains that
-- mint their own, so the registry's join is in it for the same reason
-- the nodes arm carries it.  Both reproduce across a frame at no cost:
-- a frame never rewrites the slots, and the registry's own frame leaf
-- is already proven to step.
--
-- REFUTED: Refuted.Chain-Step-Live-Additive
module Verify-Budget-Sufficient.Live-Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; foldr; length)
open import Data.Nat using (ℕ; zero; suc; pred; _+_; _*_; _⊔_; _≤_; _≡ᵇ_)
open import Data.Nat.Properties
  using (≤-trans; ⊔-lub; ⊔-monoˡ-≤; m≤m⊔n; m≤n⊔m; m≤m+n; n≤1+n)
open import Data.Vec using (lookup)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; obs; sizeᵉ; _≟ᵗ_)
open import Rx.Slots using (Slots)
open import Rx.Frame-Width using (dWᵉ)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId; AllOp; NodeId; map-f; scan-f;
  take-f; from-inner; thru-outer; scan-st; take-st; mergeAll-st; switch-st; exhaust-st;
  mergeAllᵒ; switchᵒ; exhaustᵒ; innerFinish; mergeAllDrain; aliveThroughᶠ; lookupNode;
  takeVals; foldPath; stepFrame; dispatchShare; shareGo; shareAdmit; shareLatch;
  subscribeInner; hasRoom)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Measures using (pathLen)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; regsNestMax; nestUnit; sweepLive-nest)
open import Verify-Budget-Sufficient.Caps
  using (Caps; frameStep; sizeCount; frameStep-mono-j)
open import Verify-Budget-Sufficient.Nest-Walk
  using (FaceOK; faceHere; capsDrainOK; nestValOK?-widen)
open import Verify-Budget-Sufficient.Nest-Ceiling using (ceil-sweep-step)
open import Verify-Budget-Sufficient.Nest-Cap using (nestFac; nestU)
open import Verify-Budget-Sufficient.Nest-Burst using (drainW; innerW; drainW-here; drainW-tail)
open import Verify-Budget-Sufficient.Caps-Depth using (depthFin; depthDrain; depthInner)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsΦ?; FrameΦHyp; PathΦHyp; DispatchΦHyp; ShareGoΦHyp; valsSz?; stepFrame-nest-Φ;
  stepFrame-nest-regs; foldPath-nest-regs)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; capsOK?; nestValOK?; nestClosOK?; capsOK?-mono)
open import Verify-Budget-Sufficient.Caps-Face.Part3 using (pathSz?-⊑)
open import Verify-Budget-Sufficient.Caps-Face.Part4 using (foldPath-slots)

-- WHAT AN OUTER FRAME OWES BEYOND THE POTENTIAL, stated at the one
-- kind that can subscribe.  A size bound rather than a depth one,
-- because the mint reaches through the gate the depth measures stop
-- at; and stated per frame rather than per statement so that four
-- arms discharge it with a unit and the fold stays uniform.
FrameLiveHyp : ∀ {n} {Γ : Ctx n} {s u t} (U : ℕ) (f : Frame Γ s u)
  (path : Path Γ u t) (vals : List (Val Γ s)) → Set
FrameLiveHyp U (map-f _)          path vals = ⊤
FrameLiveHyp U (scan-f _ _)       path vals = ⊤
FrameLiveHyp U (take-f _)         path vals = ⊤
FrameLiveHyp U (from-inner _ _ _) path vals = ⊤
FrameLiveHyp U (thru-outer _ _) path vals = valsSz? U vals ≡ true

-- the same shape `PathΦHyp` has, and threaded by the same fold: the
-- values a frame sees are the ones the frames above it produced, so a
-- side condition on them has to step alongside the walk rather than
-- being stated once at the chain's head.
mutual
  PathLiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (U : ℕ) (path : Path Γ u t)
    (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) → Set
  PathLiveHyp sf gas id now U root vals fin sched st = ⊤
  PathLiveHyp sf gas id now U (share-sink i) vals fin sched st =
    DispatchLiveHyp sf gas id now U i vals fin sched st
  PathLiveHyp sf gas id now U (f ↠ p) vals fin sched st =
    FrameLiveHyp U f p vals
    × PathLiveHyp sf gas id now U p
        (proj₁ (stepFrame sf id now f p vals fin sched st))
        (proj₁ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st))))
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))
        (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f p vals fin sched st)))))

  DispatchLiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (U : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) → Set
  DispatchLiveHyp {t = t} sf zero id now U i vals fin sched st = ⊤
  DispatchLiveHyp {t = t} sf (suc gas) id now U i vals fin sched st =
    ShareGoLiveHyp {t = t} sf gas id now U i vals fin
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i fin st)

  ShareGoLiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (U : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) → Set
  ShareGoLiveHyp sf gas id now U i vals fin [] sched st = ⊤
  ShareGoLiveHyp {t = t} sf gas id now U i vals fin ((rid , p) ∷ ps) sched st =
    if any (_≡ᵇ rid) (EvalSt.cancelled st)
    then ShareGoLiveHyp {t = t} sf gas id now U i vals fin ps sched st
    else (PathLiveHyp sf gas id now U p vals fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })
      × ShareGoLiveHyp {t = t} sf gas id now U i vals fin ps
          (proj₁ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st }))))
          (proj₂ (proj₂ (foldPath sf gas id now (toℕ i) p vals
            (if fin then close (toℕ i) exhausted ∷ [] else []) fin sched
            (record st { delivered = rid ∷ EvalSt.delivered st })))))

-- THE TWO KINDS THAT CAN MINT, and the split is the finding rather
-- than a filing choice.  Four frame kinds cannot touch the live list
-- at all -- a map rewrites values, a scan writes its accumulator, a
-- take writes its counter and may SWEEP, which only ever drops
-- entries -- so their arms are proven below out of the schedule the
-- step hands back unchanged.  What is left is the outer frame, which
-- subscribes what it is handed, and the completion frame, which
-- subscribes out of the *All node's QUEUE.  Those are the leaves.
postulate
  -- THE OUTER FRAME'S MINTS.  It subscribes the arrivals it is handed,
  -- so what it can put on the live list is read off THOSE values --
  -- which is why the side condition at this kind is a size bound on
  -- them and a unit at every other.
  --
  -- AND IT IS THE ONE OF THE LIVE LIST'S THREE MINTS THAT READS IN
  -- NEITHER OF THE OTHER TWO'S DENOMINATIONS.  Those read in the caps
  -- face's LEVEL-INDEXED ledger: the subscribe out of a parked queue
  -- already takes its caps at a stepped level, and the sink's arm
  -- restates off the dispatch ledger at a level with no affordability
  -- premise at all -- which is the shape the potential face's own sink
  -- arm is PROVEN in, so the ledger absorbing the fan-out's climb is a
  -- fact and not a plan.  This one is not moved there, and for a
  -- different reason than it looked: its conclusion never needed the
  -- round's ceiling at all, so there is no level to index.  What read
  -- as a statement pinned to one level was a size reading charged
  -- against the potential's number, and the block below is why the two
  -- separate.  Hence the sink's three refutations close a route this
  -- arm does not take.
  --
  -- AND THE SIZE BUDGET IS THE CURRENCY THIS CONCLUSION WAS ALWAYS
  -- OWED, because the two measures disagree at exactly the gate this
  -- arm mints across.  What lands on the live list is a PENDING value,
  -- and the only clause minting a nested one subscribes a `deferᵉ`,
  -- whose pending entry is the BODY.  So the fold the conclusion
  -- reads is the body's nesting -- while the potential's measure is
  -- ZERO on the value it was handed, since depth truncates at a defer
  -- and size crosses it (`suc` of the body's).  The ceiling was
  -- therefore never paying for this arm's own mint: it was standing in
  -- for a reading the size premise delivers outright, through the
  -- proven `nestDᵉ≤sizeᵉ`, and it is the potential premise that is
  -- silent here rather than the size one.  Hence the size budget is
  -- its own number and the conclusion joins THAT.
  --
  -- PROBED: `Probed.Chain-Step-Live-Deferred` reaches this arm by
  --   RUNNING a whole chain over it, at the one program shape that can
  --   move the fold: a `mapᵉ` over the async input handing the outer
  --   *All a deferred nest per arrival, so the chain the evaluator
  --   presents subscribes it here and the live it mints carries the
  --   body.  Covered: the fold rising 0 to 1 and 0 to 3 as the nest
  --   deepens, against a syntactic charge of eighteen and twenty-six
  --   that the tree proves the size cap dominates -- so both sides move
  --   and the ordering is load-bearing on the depth axis.  TIED at this
  --   frame ALONE -- the node id taken from the run, since a step at an
  --   id the table does not hold is the identity, and the value the
  --   program itself emits -- with the three premises LEFT STANDING, so
  --   the row asserts the arm with the potential and the value bound
  --   unasked.  AND THE GRANT IS UNSPENT AT BOTH DEPTHS: at depth ONE
  --   the fold of 1 sits under a slot vocabulary of 2, and at depth
  --   THREE the fold of 3 is over that vocabulary and is carried by
  --   the size budget alone -- both rows standing at a potential grant
  --   of ZERO, at a budget that is the value's own size rather than a
  --   number chosen to clear the fold.  Not covered: a fold already
  --   nonzero at entry, where the growth would compound rather than
  --   start at zero.
  stepFrame-nest-live-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (path : Path Γ u t) (vals : List (Val Γ (obs u))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U V : ℕ) →
    valsΦ? B U (thru-outer op nid ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st →
    valsSz? V vals ≡ true →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live
        (proj₁ (proj₂ (proj₂ (proj₂
          (stepFrame sf id now (thru-outer op nid) path vals fin sched st))))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched) ⊔ V

  -- THE SINGLE SUBSCRIPTION, AND THIS IS WHERE THE GATE IS PRICED.
  -- The drain walks its queue and mints once per parked entry, and
  -- both readings the conclusion joins are `⊔`-folds -- so the queue
  -- combines by max rather than accumulating, and what the whole walk
  -- can leave on the live list is what ONE subscribe leaves.  That is
  -- why the recursion is a real body below and this is the only thing
  -- still asserted.
  --
  -- AND NO LARGER NUMBER WOULD HAVE REPAIRED IT, WHICH IS WHAT FIXES
  -- THE CURRENCY.  The depth measure TRUNCATES at the gate -- that is
  -- what makes a recursive body safe -- so a parked term reads zero
  -- wherever the NODE is read, which is the one state quantity the
  -- consuming fit's store residue is built above, alongside incoming
  -- values the drain does not carry.  Subscribing the entry puts the
  -- body itself on the live list at observable type, where the
  -- truncation does not apply and the fold reads its full depth.  So a
  -- premise bounding the queue's NESTING is satisfied by the
  -- counterexample unchanged, and the increment this statement has to
  -- cover is the subscribed body's own depth against a residue of zero.
  --
  -- SO ONLY THE CAP-DERIVED SIDE CAN PAY, and the entry's own park
  -- receipt is what carries it: the caps ledger comes in at the level,
  -- and that receipt reads `sizeᵉ` -- one unit per gate layer, where
  -- the depth reads none.  That is which premise is load-bearing here
  -- and it is what a discharge spends.  The registry face's drain arm
  -- fell to the same emptiness at the same node and takes the same
  -- bundle, so two faces discharge from ONE producer.
  --
  -- REFUTED: `Refuted.Drain-Live-Defer`, at the corner two earlier
  --   findings leave open: `Refuted.Chain-Step-Live-Nest` found the
  --   gate's mint and its repair is the arrival grant this statement
  --   now carries, `Refuted.Drain-Regs-Nest` found the drain arm
  --   reading a payload no walk handed it -- on the registry axis,
  --   where the same emptiness clears the same premise.
  -- PROBED: `Probed.Frame-Drain-Live` reaches this subscribe through
  --   the completion frame and the drain that run it, by a door the
  --   running families do not have: an unlimited outer never refuses
  --   room, so its queue is empty on every row, and bounding the limit
  --   does not fix it either, since a queue fills only while an earlier
  --   inner is still ACTIVE and every inner those families build
  --   finishes inside its own subscribe burst.  The frame above
  --   quantifies over an arbitrary state, so a parked queue is
  --   installed instead.  Covered: one parked entry, a gated nest, at
  --   depths zero through four, with the incoming live list empty, the
  --   slot telescope scripted and the registry empty so the reaction
  --   reaches the finish.  Not covered: the switch and exhaust ops,
  --   whose finish arms drain nothing; and the hypotheses, which carry
  --   a quantified numeric conjunct and do not compute -- so a row is
  --   evidence about the CONCLUSION, unconditional where green.
  subscribeInner-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (c : Caps) (sl : Slots Γ) (d W Lv G B U : ℕ) (sf : Gas) (op : AllOp)
    (allNid : NodeId) (κ : Path Γ s t) (id : Id) (now : Tick)
    (o : Closed Γ s) (sched : Sched Γ) (st : EvalSt e) →
    ⦃ _ : FaceOK c sl ⦄ →
    Sched.slots sched ≡ sl →
    capsOK? (frameStep Lv c) sched st ≡ true →
    nestValOK? (frameStep Lv c) (obs s) o ≡ true →
    nestClosOK? (frameStep Lv c) sl o ≡ true →
    sizeᵉ o ≤ Caps.cSize (frameStep Lv c) →
    dWᵉ n sl o ≤ Caps.cWid (frameStep Lv c) →
    innerW sf op allNid κ id now o sched st ≤ W →
    depthInner sf op allNid κ id now o sched st ≤ d →
    pathSz? (Caps.cSize (frameStep Lv c)) κ ≡ true →
    suc (pathLen κ) ≤ Caps.cSize (frameStep Lv c) →
    (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
       pathΦF B κ
         * (nestFac (Caps.cSize (frameStep j c)) W
              * (G + nestU (Caps.cSize (frameStep j c)) (nestUnit e sl))
            + pathΦD B κ) ≤ U) →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
        (subscribeInner sf op allNid κ id now o sched st)))))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum sl ⊔ U

-- WIDENING INTO THE CONCLUSION, which is all four of the arms that do
-- not mint.  The conclusion joins the incoming fold with two terms a
-- frame never writes, so a step that hands its own schedule back is
-- discharged by the join's own left projections and by nothing about
-- the frame.
live-into : ∀ {n} {Γ : Ctx n} {S : ℕ} (sched : Sched Γ) (U : ℕ) →
  foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched) ⊔ S ⊔ U
live-into {S = S} sched U = ≤-trans (m≤m⊔n _ S) (m≤m⊔n _ U)

-- AND THE SAME AT TWO NUMBERS, which is what the frame step's
-- conclusion joins once the size demand stops borrowing the ceiling.
live-into₂ : ∀ {n} {Γ : Ctx n} {S : ℕ} (sched : Sched Γ) (U V : ℕ) →
  foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched) ⊔ S ⊔ U ⊔ V
live-into₂ sched U V = ≤-trans (live-into sched U) (m≤m⊔n _ V)

-- THE DRAIN'S OWN RECURSION, AND IT COSTS WHAT ONE SUBSCRIPTION COSTS.
-- `mergeAllDrain` walks the parked inners and hands back the last
-- schedule, and the conclusion's two readings are both `⊔`-folds -- so
-- the queue combines by max and the bound is RE-ESTABLISHED at every
-- entry rather than accumulated.  What makes that composable is that
-- the join the statement is bounded by is idempotent in its own two
-- right summands: the tail's bound is stated against the head's
-- schedule, and collapsing the two is three projections.
--
-- AND THE SLOT TELESCOPE IS A PARAMETER RATHER THAN A READING, which
-- is what removes the obligation this recursion would otherwise carry.
-- Stated over `Sched.slots sched` the tail would need the slots
-- PRESERVED across a subscribe before the induction could even be
-- typed; the caps bundle already carries the equation at every entry,
-- so taking the telescope abstractly and letting the bundle supply it
-- is strictly cheaper than proving preservation.
mergeAllDrain-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (sl : Slots Γ) (d W Lv G B U : ℕ) (sf : Gas) (allNid : NodeId)
  (κ : Path Γ s t) (id : Id) (now : Tick) (lim : Maybe ℕ) (act : ℕ)
  (q : List (Closed Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c sl ⦄ →
  capsDrainOK c sl d Lv sf allNid κ id now lim act q sched st →
  drainW sf allNid κ id now q sched st ≤ W →
  depthDrain sf allNid κ id now q sched st ≤ d →
  pathSz? (Caps.cSize (frameStep Lv c)) κ ≡ true →
  suc (pathLen κ) ≤ Caps.cSize (frameStep Lv c) →
  (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
     pathΦF B κ
       * (nestFac (Caps.cSize (frameStep j c)) W
            * (G + nestU (Caps.cSize (frameStep j c)) (nestUnit e sl))
          + pathΦD B κ) ≤ U) →
  foldr (λ l acc → liveNest l ⊔ acc) 0
    (Sched.live (proj₁ (proj₂ (proj₂ (proj₂ (proj₂
      (mergeAllDrain sf allNid κ id now lim act q sched st)))))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum sl ⊔ U
mergeAllDrain-nest-live c sl d W Lv G B U sf allNid κ id now lim act []
  sched st hcd hw hd hpk hpl hu = live-into sched U
mergeAllDrain-nest-live c sl d W Lv G B U sf allNid κ id now lim act (o ∷ q)
  sched st hcd hw hd hpk hpl hu
  with hasRoom lim act
... | false = live-into sched U
... | true  = ≤-trans IH₀ (⊔-lub (⊔-lub SUB₀ S≤) U≤)
  where
  B̂     = proj₁ hcd
  Ŝ     = proj₁ (proj₂ hcd)
  ceilQ = proj₁ (proj₂ (proj₂ hcd))
  hcdA  = proj₂ (proj₂ (proj₂ hcd))

  r₁     = subscribeInner sf mergeAllᵒ allNid κ id now o sched st
  done   = proj₁ (proj₂ (proj₂ (proj₂ r₁)))
  sched₁ = proj₁ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))
  st₁    = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ r₁))))

  tailΣ = proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcdA)))))))
  r₀    = proj₁ tailΣ
  step″ = frameStep-mono-j c (FaceOK.fSize faceHere) (m≤m+n Lv r₀)

  -- the head is subscribed one level up, where its closure key is
  -- stated; the other five premises widen onto that frame by the
  -- step's own monotonicity
  stepʰ = frameStep-mono-j c (FaceOK.fSize faceHere) (n≤1+n Lv)

  SUB₀ = subscribeInner-nest-live c sl d W (suc Lv) G B U sf mergeAllᵒ allNid κ id now
           o sched st
           (proj₁ hcdA)
           (capsOK?-mono (frameStep Lv c) (frameStep (suc Lv) c) sched st stepʰ
              (proj₁ (proj₂ hcdA)))
           (nestValOK?-widen (obs _) o stepʰ (proj₁ (proj₂ (proj₂ hcdA))))
           (proj₁ (proj₂ (proj₂ (proj₂ hcdA))))
           (≤-trans (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hcdA))))) (proj₁ stepʰ))
           (≤-trans (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hcdA))))))
                    (proj₁ (proj₂ stepʰ)))
           (≤-trans (drainW-here sf allNid κ id now o q sched st) hw)
           (≤-trans (m≤m⊔n _ _) hd)
           (pathSz?-⊑ κ stepʰ hpk) (≤-trans hpl (proj₁ stepʰ)) hu

  IH₀ = mergeAllDrain-nest-live c sl d W (Lv + r₀) G B U sf allNid κ id now lim
          (if done then act else suc act) q sched₁ st₁
          (B̂ , Ŝ
             , ceil-sweep-step c d Lv B̂ (suc (length q + Ŝ)) r₀
                 (FaceOK.fSize faceHere) (proj₁ (proj₂ tailΣ)) ceilQ
             , proj₂ (proj₂ tailΣ))
          (≤-trans (drainW-tail sf allNid κ id now o q sched st) hw)
          (≤-trans (m≤n⊔m _ _) hd)
          (pathSz?-⊑ κ step″ hpk) (≤-trans hpl (proj₁ step″))
          hu

  S≤ = ≤-trans (m≤n⊔m (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                      (slotsNestSum sl))
               (m≤m⊔n _ U)

  U≤ = m≤n⊔m _ U

-- THE COMPLETION FRAME'S DISPATCH, and it is CHECKED rather than
-- asserted: a step that is not a `fin`, a `fin` whose inner is still
-- held open by a live registration, a switch or exhaust finish, and a
-- merge finish whose node is absent or holds another element type all
-- hand their schedule straight back.  What survives is the one route
-- that runs the queue, which is where the leaf sits.
innerFinish-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (c : Caps) (d W Lv G B U : ℕ) (sf : Gas) (op : AllOp)
  (allNid inst : NodeId) (p : Path Γ s t) (id : Id) (now : Tick)
  (vals : List (Val Γ s)) (sched : Sched Γ) (st : EvalSt e) →
  ⦃ _ : FaceOK c (Sched.slots sched) ⦄ →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     capsDrainOK c (Sched.slots sched) d Lv sf allNid p id now lim
       (pred act) q sched st) →
  (∀ (lim : Maybe ℕ) (act : ℕ) (q : List (Closed Γ s)) (od : Bool) →
     lookupNode allNid (EvalSt.nodes st) ≡ just (mergeAll-st lim act q od) →
     drainW sf allNid p id now q sched st ≤ W) →
  depthFin sf op allNid inst p id now vals sched st
    (lookupNode allNid (EvalSt.nodes st)) ≤ d →
  pathSz? (Caps.cSize (frameStep Lv c)) p ≡ true →
  suc (pathLen p) ≤ Caps.cSize (frameStep Lv c) →
  (∀ (j : ℕ) → j ≤ sizeCount c d ⊔ Caps.cSize c →
     pathΦF B p
       * (nestFac (Caps.cSize (frameStep j c)) W
            * (G + nestU (Caps.cSize (frameStep j c))
                     (nestUnit e (Sched.slots sched)))
          + pathΦD B p) ≤ U) →
  foldr (λ l acc → liveNest l ⊔ acc) 0
    (Sched.live
      (proj₁ (proj₂ (proj₂ (proj₂
        (innerFinish sf op allNid inst p id now vals sched st
          (lookupNode allNid (EvalSt.nodes st))))))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched) ⊔ U
innerFinish-nest-live c d W Lv G B U sf switchᵒ allNid inst p id now vals sched st
  hdr hw hdp hpk hpl hu
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = live-into sched U
... | just (scan-st _)           = live-into sched U
... | just (take-st _)           = live-into sched U
... | just (mergeAll-st _ _ _ _) = live-into sched U
... | just (exhaust-st _ _)      = live-into sched U
... | just (switch-st nothing _) = live-into sched U
... | just (switch-st (just c₀) od) with c₀ ≡ᵇ inst
...   | false = live-into sched U
...   | true  = live-into sched U
innerFinish-nest-live c d W Lv G B U sf exhaustᵒ allNid inst p id now vals sched st
  hdr hw hdp hpk hpl hu
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                    = live-into sched U
... | just (scan-st _)           = live-into sched U
... | just (take-st _)           = live-into sched U
... | just (mergeAll-st _ _ _ _) = live-into sched U
... | just (switch-st _ _)       = live-into sched U
... | just (exhaust-st _ _)      = live-into sched U
innerFinish-nest-live {s = s} c d W Lv G B U sf mergeAllᵒ allNid inst p id now vals sched st
  hdr hw hdp hpk hpl hu
  with lookupNode allNid (EvalSt.nodes st)
... | nothing                = live-into sched U
... | just (scan-st _)       = live-into sched U
... | just (take-st _)       = live-into sched U
... | just (switch-st _ _)   = live-into sched U
... | just (exhaust-st _ _)  = live-into sched U
... | just (mergeAll-st {w} lim act q od) with w ≟ᵗ s
...   | no  _    = live-into sched U
...   | yes refl =
        mergeAllDrain-nest-live c (Sched.slots sched) d W Lv G B U sf allNid p id now
          lim (pred act) q sched st
          (hdr lim act q od refl) (hw lim act q od refl)
          (≤-trans (n≤1+n _) hdp) hpk hpl hu

-- THE COMPLETION FRAME'S MINTS.  A `from-inner` runs the finish only
-- on a `fin` that no live registration absorbs, so both of the routes
-- that hand the payload straight back are discharged here and what is
-- left is the finish's own dispatch.
stepFrame-nest-live-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
  (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
  (path : Path Γ s t) (vals : List (Val Γ s)) (fin : Bool)
  (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
  valsΦ? B U (from-inner op allNid inst ↠ path) vals ≡ true →
  FrameΦHyp sf id now B U (from-inner op allNid inst) path vals fin sched st →
  foldr (λ l acc → liveNest l ⊔ acc) 0
    (Sched.live
      (proj₁ (proj₂ (proj₂ (proj₂
        (stepFrame sf id now (from-inner op allNid inst) path vals fin sched st))))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched) ⊔ U
stepFrame-nest-live-inner sf id now op allNid inst path vals false sched st B U _ _ =
  live-into sched U
stepFrame-nest-live-inner sf id now op allNid inst path vals true sched st B U _
  (c , d , W , Lv , G , fok , hdr , hw , hdp , hpk , hpl , hG , hu)
  with any (aliveThroughᶠ inst st) (EvalSt.registry st)
... | true  = live-into sched U
... | false =
      innerFinish-nest-live c d W Lv G B U sf op allNid inst path id now vals sched st
        ⦃ fok ⦄ hdr hw hdp hpk hpl hu

-- ONE FRAME'S MINTS, assembled.  The three arms below are the ones the
-- step hands back its own schedule from, so each is the incoming fold
-- widened into the conclusion's join; the take arm is the only one
-- that rewrites the list at all, and it does so by SWEEPING, whose
-- monotonicity is already proven.

-- AND THE CONCLUSION JOINS TWO NUMBERS, WHICH IS WHICH ARMS NEED
-- WHICH.  Four kinds hand their own schedule back and read no number
-- at all, so they widen into either.  What is left is the two that
-- mint, and they are priced in currencies that do not convert: the
-- completion frame subscribes out of a parked queue and takes its
-- reading from the caps ledger, so the round's CEILING is the only
-- thing paying for it, while the outer frame subscribes the values it
-- was handed and is priced off their SIZE.  So the ceiling is
-- load-bearing for exactly one arm, and it is not the arm that used to
-- borrow it.
stepFrame-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (B U V : ℕ) →
  valsΦ? B U (f ↠ path) vals ≡ true →
  FrameΦHyp sf id now B U f path vals fin sched st →
  FrameLiveHyp V f path vals →
  foldr (λ l acc → liveNest l ⊔ acc) 0
    (Sched.live
      (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
    ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
        ⊔ slotsNestSum (Sched.slots sched) ⊔ U ⊔ V
stepFrame-nest-live sf id now (map-f fn) path vals fin sched st B U V _ _ _ =
  live-into₂ sched U V
stepFrame-nest-live {u = u} sf id now (scan-f fn nid) path vals fin sched st B U V _ _ _
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = live-into₂ sched U V
... | just (take-st _)       = live-into₂ sched U V
... | just (mergeAll-st _ _ _ _) = live-into₂ sched U V
... | just (switch-st _ _)   = live-into₂ sched U V
... | just (exhaust-st _ _)  = live-into₂ sched U V
... | just (scan-st {w} _) with w ≟ᵗ u
...   | yes refl = live-into₂ sched U V
...   | no _     = live-into₂ sched U V
stepFrame-nest-live sf id now (take-f nid) path vals fin sched st B U V _ _ _
  with lookupNode nid (EvalSt.nodes st)
... | nothing                = live-into₂ sched U V
... | just (scan-st _)       = live-into₂ sched U V
... | just (mergeAll-st _ _ _ _) = live-into₂ sched U V
... | just (switch-st _ _)   = live-into₂ sched U V
... | just (exhaust-st _ _)  = live-into₂ sched U V
... | just (take-st k) with proj₂ (proj₂ (takeVals k vals))
...   | false = live-into₂ sched U V
...   | true  =
        ≤-trans (sweepLive-nest _ (Sched.live sched)) (live-into₂ sched U V)
stepFrame-nest-live sf id now (from-inner op allNid inst) path vals fin sched st B U V hΦ hF _ =
  ≤-trans (stepFrame-nest-live-inner sf id now op allNid inst path vals fin sched st
             B U hΦ hF)
          (m≤m⊔n _ V)
stepFrame-nest-live sf id now (thru-outer op nid) path vals fin sched st B U V hΦ hF hL =
  ≤-trans (stepFrame-nest-live-outer sf id now op nid path vals fin sched st
             B U V hΦ hF hL)
          (⊔-monoˡ-≤ V (m≤m⊔n _ U))

-- FOUR KINDS OWE NOTHING AND ONE OWES THE BOUND, which is the whole
-- content of the side condition read at one frame.
frameLive-of-sz : ∀ {n} {Γ : Ctx n} {s u t} (U : ℕ) (f : Frame Γ s u)
  (path : Path Γ u t) (vals : List (Val Γ s)) →
  valsSz? U vals ≡ true → FrameLiveHyp U f path vals
frameLive-of-sz U (map-f _)          path vals _ = tt
frameLive-of-sz U (scan-f _ _)       path vals _ = tt
frameLive-of-sz U (take-f _)         path vals _ = tt
frameLive-of-sz U (from-inner _ _ _) path vals _ = tt
frameLive-of-sz U (thru-outer _ _)   path vals h = h

-- THE WALK, AND THE FAN-OUT IT RE-ENTERS.  Four facts per frame and no
-- more: the live leaf for what this frame minted, the slots' invariance
-- for the term the script mints are charged to, the registry's frame
-- leaf for the term the share fan-out is charged to, and the
-- potential's own step law.  The sink's clause spends the same four one
-- level out -- the fan-out's own walks, the slots across a whole chain,
-- and the registry arm's fan-out theorem.
mutual
  foldPath-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U V : ℕ) →
    valsΦ? B U path vals ≡ true →
    PathΦHyp sf gas id now B U path vals fin sched st →
    PathLiveHyp sf gas id now V path vals fin sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U ⊔ V
  foldPath-nest-live sf gas id now envSrc root vals evs fin sched st B U V hΦ _ _ =
    ≤-trans (≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                                     (slotsNestSum (Sched.slots sched)))
                              (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
                     (m≤m⊔n _ U))
            (m≤m⊔n _ V)
  foldPath-nest-live sf gas id now envSrc (share-sink i) vals evs fin sched st B U V hΦ hD hDL =
    dispatchShare-nest-live sf gas id now i vals fin sched st B U V hD hDL
  foldPath-nest-live sf gas id now envSrc (f ↠ p) vals evs fin sched st B U V hΦ (hF , hR) (hL , hLR) =
    ≤-trans (foldPath-nest-live sf gas id now envSrc p
               (proj₁ step) (evs ++ proj₁ (proj₂ step))
               (proj₁ (proj₂ (proj₂ step)))
               (proj₁ (proj₂ (proj₂ (proj₂ step))))
               (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U V
               (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR hLR)
            (⊔-lub (⊔-lub (⊔-lub (⊔-lub liveStep slotStep) regStep) intoU) intoV)
    where
    step = stepFrame sf id now f p vals fin sched st
    L = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    S = slotsNestSum (Sched.slots sched)
    R = regsNestMax (EvalSt.registry st)
    intoL : L ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoL = ≤-trans (≤-trans (≤-trans (m≤m⊔n L S) (m≤m⊔n (L ⊔ S) R))
                             (m≤m⊔n (L ⊔ S ⊔ R) U))
                    (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoS : S ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoS = ≤-trans (≤-trans (≤-trans (m≤n⊔m L S) (m≤m⊔n (L ⊔ S) R))
                             (m≤m⊔n (L ⊔ S ⊔ R) U))
                    (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoR : R ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoR = ≤-trans (≤-trans (m≤n⊔m (L ⊔ S) R) (m≤m⊔n (L ⊔ S ⊔ R) U))
                    (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoU : U ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoU = ≤-trans (m≤n⊔m (L ⊔ S ⊔ R) U) (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoV : V ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoV = m≤n⊔m (L ⊔ S ⊔ R ⊔ U) V
    liveStep : foldr (λ l acc → liveNest l ⊔ acc) 0
                 (Sched.live (proj₁ (proj₂ (proj₂ (proj₂ step)))))
                 ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    liveStep =
      ≤-trans (stepFrame-nest-live sf id now f p vals fin sched st B U V hΦ hF hL)
              (⊔-lub (⊔-lub (⊔-lub intoL intoS) intoU) intoV)
    slotStep : slotsNestSum (Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ step)))))
                 ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    slotStep =
      subst (_≤ L ⊔ S ⊔ R ⊔ U ⊔ V)
            (cong slotsNestSum
              (sym (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))))
            intoS
    regStep : regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ step)))))
                ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    regStep =
      ≤-trans (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ hF)
              (⊔-lub intoR intoU)

  -- THE SINK, and the live list is the one field two of its three arms
  -- move.  Out of dispatch gas nothing moves; the latch writes ledgers;
  -- and the finishing arm SWEEPS the list against the surviving
  -- registry, which only ever drops entries.
  dispatchShare-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U V : ℕ) →
    DispatchΦHyp sf gas id now B U i vals fin sched st →
    DispatchLiveHyp sf gas id now V i vals fin sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U ⊔ V
  dispatchShare-nest-live sf zero id now i vals fin sched st B U V _ _ =
    ≤-trans (≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                                     (slotsNestSum (Sched.slots sched)))
                              (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
                     (m≤m⊔n _ U))
            (m≤m⊔n _ V)
  dispatchShare-nest-live sf (suc gas) id now i vals false sched st B U V hS hSL =
    shareGo-nest-live sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B U V hS hSL
  dispatchShare-nest-live {t = t} sf (suc gas) id now i vals true sched st B U V hS hSL =
    ≤-trans (sweepLive-nest _
              (Sched.live (proj₁ (proj₂ (shareGo {t = t} sf gas id now i vals true
                (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st))))))
            (shareGo-nest-live sf gas id now i vals true
              (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B U V hS hSL)

  -- ONE ADMITTED REGISTRATION AT A TIME, and all three components
  -- telescope: the live list under the one the chain entered on, the
  -- slots unmoved because no chain ever rewrites them, and the registry
  -- under the registry arm's own walk theorem.
  shareGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B U V : ℕ) →
    ShareGoΦHyp sf gas id now B U i vals fin ps sched st →
    ShareGoLiveHyp sf gas id now V i vals fin ps sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (shareGo sf gas id now i vals fin ps sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U ⊔ V
  shareGo-nest-live sf gas id now i vals fin [] sched st B U V _ _ =
    ≤-trans (≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                                     (slotsNestSum (Sched.slots sched)))
                              (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
                     (m≤m⊔n _ U))
            (m≤m⊔n _ V)
  shareGo-nest-live sf gas id now i vals fin ((rid , p) ∷ ps) sched st B U V hS hSL
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nest-live sf gas id now i vals fin ps sched st B U V hS hSL
  ... | false =
    ≤-trans (shareGo-nest-live sf gas id now i vals fin ps
               (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B U V
               (proj₂ (proj₂ hS)) (proj₂ hSL))
            (⊔-lub (⊔-lub (⊔-lub (⊔-lub headLive headSlots) headRegs) intoU) intoV)
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    EVS = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas id now (toℕ i) p vals EVS fin sched st₀
    L = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    S = slotsNestSum (Sched.slots sched)
    R = regsNestMax (EvalSt.registry st)
    intoS : S ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoS = ≤-trans (≤-trans (≤-trans (m≤n⊔m L S) (m≤m⊔n (L ⊔ S) R))
                             (m≤m⊔n (L ⊔ S ⊔ R) U))
                    (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoR : R ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoR = ≤-trans (≤-trans (m≤n⊔m (L ⊔ S) R) (m≤m⊔n (L ⊔ S ⊔ R) U))
                    (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoU : U ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoU = ≤-trans (m≤n⊔m (L ⊔ S ⊔ R) U) (m≤m⊔n (L ⊔ S ⊔ R ⊔ U) V)
    intoV : V ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    intoV = m≤n⊔m (L ⊔ S ⊔ R ⊔ U) V
    headLive : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ FP)))
                 ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    headLive = foldPath-nest-live sf gas id now (toℕ i) p vals EVS fin sched st₀ B U V
                 (proj₁ hS) (proj₁ (proj₂ hS)) (proj₁ hSL)
    headSlots : slotsNestSum (Sched.slots (proj₁ (proj₂ FP))) ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    headSlots =
      subst (_≤ L ⊔ S ⊔ R ⊔ U ⊔ V)
            (cong slotsNestSum
              (sym (foldPath-slots sf gas id now (toℕ i) p vals EVS fin sched st₀)))
            intoS
    headRegs : regsNestMax (EvalSt.registry (proj₂ (proj₂ FP))) ≤ L ⊔ S ⊔ R ⊔ U ⊔ V
    headRegs =
      ≤-trans (foldPath-nest-regs sf gas id now (toℕ i) p vals EVS fin sched st₀ B U
                 (proj₁ hS) (proj₁ (proj₂ hS)))
              (⊔-lub intoR intoU)
