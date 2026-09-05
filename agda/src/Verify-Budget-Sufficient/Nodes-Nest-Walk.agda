-- THE NODES MAP'S DEPTH ALONG ONE CHAIN, walked frame by frame -- the
-- same induction the registry arm runs, over the same potential, at
-- the other place a frame can store.
--
-- AND IT CARRIES THE REGISTRY'S JOIN, WHICH THE REGISTRY ARM DOES NOT
-- HAVE TO.  A chain that reaches a share does not stop there: the sink
-- fans the same values into every registration on the share, and each
-- of those walks its OWN path and stores at its own node.  Those paths
-- live in the registry, so what the fan-out can leave in the nodes map
-- is bounded by the registry's own nesting and by nothing the walked
-- path says.  The registry arm needs no such term because the fan-out
-- lands in the very place it is already measuring; the nodes arm is
-- measuring somewhere else, so the term has to be in the statement.
--
-- THE INDUCTION CLOSES BECAUSE THE REGISTRY ARM IS ALREADY PROVEN TO
-- STEP.  Carrying a second component would ordinarily cost a second
-- invariant, but the frame leaf for the registry says exactly that the
-- stepped registry is under the entry registry joined with the charge
-- -- so the extra term reproduces itself at each frame and collapses
-- into the same three-way join it started as.
--
-- REFUTED: Refuted.Share-Sink-Nodes
module Verify-Budget-Sufficient.Nodes-Nest-Walk where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; foldr; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔_; _≤_; _≡ᵇ_)
open import Data.Vec using (lookup)
open import Data.Nat.Properties using
  (≤-trans; ≤-refl; ≤-reflexive; ⊔-lub; ⊔-mono-≤; m≤m⊔n; m≤n⊔m; m≤m+n;
   *-identityˡ; *-monoˡ-≤; *-monoʳ-≤; +-monoˡ-≤)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; sizeᵗ; obs)
open import Rx.Nest-Depth using (nestDᵗ)
open import Rx.Evaluator
  using (Sched; EvalSt; Path; Frame; root; share-sink; _↠_; RegId;
         NodeId; AllOp; map-f; scan-f; take-f; from-inner; thru-outer;
         foldPath; stepFrame; dispatchShare;
         shareGo; shareAdmit; shareLatch)
open import Verify-Budget-Sufficient.Nest-Store using (nodeNest; regsNestMax)
open import Verify-Budget-Sufficient.Nest-Walk
  using (nodesMax; nestDᵛˢ; nodeNestAt;
         stepFrame-nodes-cell-scan; stepFrame-nodes-cell-take)
open import Verify-Budget-Sufficient.Walk-Factor using (pathΦF; pathΦD; pathΦF-pos)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsΦ?; FrameΦHyp; PathΦHyp; DispatchΦHyp; ShareGoΦHyp;
         stepFrame-nest-Φ; stepFrame-nest-regs; foldPath-nest-regs)

postulate
  -- THE DRAIN FRAME'S OWN WRITE, which is the arm the burst reading
  -- leaves open in the other direction.  A `from-inner` takes a term
  -- OUT of its parent *All's queue and may install the head it
  -- subscribes, so the cell it rewrites is the one the fit's ceiling
  -- half is stated over rather than one the walk handed it -- and the
  -- grant it carries is a whole drain ledger rather than a single
  -- entry, so the arm is read off that ledger and not off the values.
  --
  -- AND WHAT COVERS IT IS THE `suc` A LAYER COSTS, not the grant.  The
  -- frame pops a term the entry table was already reading and
  -- subscribes it, and that subscription DOES write: a synchronous
  -- source delivers inside the very frame that made it, so a full
  -- *All parks and a cell appears that did not exist on entry.  What
  -- it parks is what sat UNDER the popped term's own outermost layer,
  -- and the measure charges that layer one `suc` -- so the fresh cell
  -- is strictly shallower than the term the pop removed, and the entry
  -- reading covers the exit reading with the budget unspent.  Behind
  -- the gate the same arm is covered the other way round: a deferred
  -- term is priced at zero however deep it is, and the drain unfolds
  -- none of it.
  --
  -- PROBED: `Probed.Frame-Drain-Store` -- a queue reached by running,
  --   the parent merge filled at capacity one by an outer frame of
  --   three arrivals so that two park.  Covered: the pop, at three
  --   rungs of a flatten ladder, standing at margin ZERO where the
  --   queue's two terms coincide; the subscribe that parks, where the
  --   fresh cell lands one layer under the term that was popped; and
  --   the gated term, unmoved at two rungs whose ungated twin parks
  --   three layers.  Every row stands at a budget of zero, which is
  --   what the empty burst licenses.  NOT covered: the switch and
  --   exhaust arms, which keep no queue; an empty parent queue; and a
  --   nonempty path under the frame.
  --
  -- RECOVERY: git show 6dcc8b1:agda/evidence/probed/Probed/Chain-Step-Abs-Charge.agda
  --   restores a chain runner that reaches a real drain at the second
  --   cascade of two families, with the node ids taken from the run.
  stepFrame-nest-nodes-inner : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (allNid inst : NodeId)
    (path : Path Γ s t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (from-inner op allNid inst ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U (from-inner op allNid inst) path vals fin sched st →
    nodesMax (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame sf id now (from-inner op allNid inst) path vals fin sched st)))))
      ≤ nodesMax st ⊔ U

  -- THE OUTER FRAME'S MINT.  A `thru-outer` receives an OBSERVABLE and
  -- subscribes it, so what it leaves in the table is the *All node the
  -- new subscription hangs from -- a cell that did not exist when the
  -- walk started, and therefore one no reading of the entry table
  -- bounds.  Its grant is a value fit rather than a ceiling, because
  -- what the mint's depth is a function of is the subscribed value.
  --
  -- BUT THE FRESH CELL IS NOT WHAT THE READING SEES, and the arm the
  -- proof has to pay for is the OTHER one.  A head's install carries no
  -- payload and the measure prices it at zero -- which is proven beside
  -- the install and not merely observed -- so an arrival that
  -- SUBSCRIBES moves this fold not at all.  The write that does move it
  -- is the arrival that does not subscribe: a full *All PARKS its
  -- observable in the node's queue, and the queue is the one cell the
  -- measure reads through.  So the value fit is the right grant for a
  -- reason one word off the one above: what the frame stores is the
  -- arriving value itself, not a cell shaped by it.
  --
  -- PROBED: `Probed.Thru-Outer-Store` -- the merge arm at capacity ONE
  --   handed two arrivals, so the first subscribes and stays active and
  --   the second has nowhere to go but the queue, at three rungs of a
  --   flatten ladder and at the budget the value premise itself
  --   licenses at burst zero.  Covered: the fold climbing with the
  --   arrivals' depth against an entry table of zero, pinned at the
  --   parked cell as well as at the fold so the reading is attributed
  --   rather than assumed, and clearing the budget by a CONSTANT one at
  --   every rung.  Not covered: the switch and exhaust arms, which kill
  --   or drop rather than queue; an entry queue already nonempty, where
  --   the park compounds instead of starting from zero; and the frame
  --   grant, which is a Σ and does not compute -- so a row is evidence
  --   about the CONCLUSION, unconditional where green.
  stepFrame-nest-nodes-outer : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (path : Path Γ u t)
    (vals : List (Val Γ (obs u))) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (thru-outer op nid ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U (thru-outer op nid) path vals fin sched st →
    nodesMax (proj₂ (proj₂ (proj₂ (proj₂
      (stepFrame sf id now (thru-outer op nid) path vals fin sched st)))))
      ≤ nodesMax st ⊔ U

-- ONE FRAME'S NODE STORES, under the potential it was handed.  Only
-- three of the five kinds store at all -- a scan writes its
-- accumulator, an inner frame writes its parent *All's queue, and an
-- outer frame mints the *All node the subscription hangs from.  A map
-- leaves the table untouched and a take writes a COUNTER, which
-- `nodeNest` prices at zero, so those two arms pay nothing at all.
--
-- THE SCAN IS THE ONE THE BURST READING KILLED, AND THE GRANT IS WHAT
-- PAYS IT.  The cell holds the accumulator, which the fold has been
-- building rather than a thing the walk handed over, so the potential
-- alone buys a fixed number of values and not a bound.  What closes it
-- is the frame grant the registry arm already takes: a ceiling `G` on
-- the entry cell joined with the values in flight, under a power in
-- the burst WIDTH -- which is the currency `stepFrame-nodes-cell-scan`
-- is proven in.  The path's factor is at least one, so the frame's own
-- arithmetic is readable against the potential the path is charged in,
-- and the arm closes with no term left over.
--
-- AND THE `⊔` IS WHAT FORCED THE CELL READING.  The sibling that
-- bounds the WHOLE table does so by a PRODUCT, so the table it found
-- goes inside the factor and a conclusion of the form `what was there
-- ⊔ a budget` cannot pay for it -- no budget mints the inflation of a
-- quantity it does not read.  A scan writes exactly one cell, so the
-- honest split is the untouched cells on the left of the join and the
-- written one on the right.
--
-- REFUTED: `Refuted.Scan-Nodes-Burst` -- a step function that deepens
--   its own accumulator, folded over a burst of naturals.  `valsΦ?`
--   charges `2 ^ sizeᵗ fn` times the step's own nesting once per value
--   and takes the maximum, so the budget is a CONSTANT in the burst
--   length; the fold threads, so the stored depth is linear in it.
--   Sixty-five values leave the cell at sixty-five against a budget of
--   sixty-four, from a table reading zero, and every further value
--   widens the gap -- so no larger `U` repairs it.  That is what the
--   grant is here for, and it is why the premise may not be dropped.
stepFrame-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
  (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
  (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
  (B U : ℕ) →
  valsΦ? B U (f ↠ path) vals ≡ true →
  FrameΦHyp sf id now B U f path vals fin sched st →
  foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
    (EvalSt.nodes
      (proj₂ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
    ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st) ⊔ U
stepFrame-nest-nodes sf id now (map-f fn) path vals fin sched st B U _ _ =
  m≤m⊔n (nodesMax st) U
stepFrame-nest-nodes sf id now (take-f nid) path vals fin sched st B U _ _ =
  ≤-trans (stepFrame-nodes-cell-take sf id now nid path vals fin sched st)
          (m≤m⊔n (nodesMax st) U)
stepFrame-nest-nodes sf id now (scan-f fn nid) path vals fin sched st B U _ (G , hG , hU) =
  ≤-trans (stepFrame-nodes-cell-scan (length vals) sf id now fn nid path vals
             fin sched st ≤-refl)
          (⊔-mono-≤ ≤-refl grant)
  where
  L = length vals
  E = (2 ^ sizeᵗ fn) ^ L
  X = E * (G + L * nestDᵗ fn)
  -- the ceiling is spent here and nowhere else: it is what turns the
  -- entry cell the step names into a quantity the potential can hold
  shrink : E * ((nodeNestAt nid st ⊔ nestDᵛˢ vals) + L * nestDᵗ fn) ≤ X
  shrink = *-monoʳ-≤ E (+-monoˡ-≤ (L * nestDᵗ fn) hG)
  -- and the factor's positivity is what lets the frame's own
  -- arithmetic be read against the potential the path is charged in
  factor : X ≤ pathΦF B path * (X + pathΦD B path)
  factor =
    ≤-trans (m≤m+n X (pathΦD B path))
            (≤-trans (≤-reflexive (sym (*-identityˡ (X + pathΦD B path))))
                     (*-monoˡ-≤ (X + pathΦD B path) (pathΦF-pos B path)))
  grant : E * ((nodeNestAt nid st ⊔ nestDᵛˢ vals) + L * nestDᵗ fn) ≤ U
  grant = ≤-trans shrink (≤-trans factor hU)
stepFrame-nest-nodes sf id now (from-inner op allNid inst) path vals fin sched st B U hΦ hF =
  stepFrame-nest-nodes-inner sf id now op allNid inst path vals fin sched st B U hΦ hF
stepFrame-nest-nodes sf id now (thru-outer op nid) path vals fin sched st B U hΦ hF =
  stepFrame-nest-nodes-outer sf id now op nid path vals fin sched st B U hΦ hF

-- THE WALK, AND THE FAN-OUT IT RE-ENTERS.  The frame clause spends
-- three facts and no more: the nodes leaf for what this frame stored,
-- the registry leaf for the term the statement carries, and the
-- potential's own step law -- which is the same one the registry walk
-- spends, so the two arms stay in lockstep and a frame kind that broke
-- one would break both.  The sink's clause spends the registry's whole
-- fan-out bound, which is a theorem of the registry arm rather than an
-- assumption of this one.
mutual
  foldPath-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (envSrc : Source)
    (path : Path Γ u t) (vals : List (Val Γ u))
    (evs : List (InstEvent (Val Γ t))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U path vals ≡ true →
    PathΦHyp sf gas id now B U path vals fin sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  foldPath-nest-nodes sf gas id now envSrc root vals evs fin sched st B U hΦ _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  foldPath-nest-nodes sf gas id now envSrc (share-sink i) vals evs fin sched st B U hΦ hD =
    dispatchShare-nest-nodes sf gas id now i vals fin sched st B U hD
  foldPath-nest-nodes sf gas id now envSrc (f ↠ p) vals evs fin sched st B U hΦ (hF , hR) =
    ≤-trans (foldPath-nest-nodes sf gas id now envSrc p
               (proj₁ step) (evs ++ proj₁ (proj₂ step))
               (proj₁ (proj₂ (proj₂ step)))
               (proj₁ (proj₂ (proj₂ (proj₂ step))))
               (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U
               (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR)
            (⊔-lub (⊔-lub (≤-trans (stepFrame-nest-nodes sf id now f p vals fin sched st B U hΦ hF)
                                   (⊔-lub (≤-trans (m≤m⊔n N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U)))
                          (≤-trans (stepFrame-nest-regs sf id now f p vals fin sched st B U hΦ hF)
                                   (⊔-lub (≤-trans (m≤n⊔m N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U))))
                   (m≤n⊔m (N ⊔ R) U))
    where
    step = stepFrame sf id now f p vals fin sched st
    N = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    R = regsNestMax (EvalSt.registry st)

  -- THE SINK, and none of its three arms touches the node map itself.
  -- Out of dispatch gas the state is returned untouched; the latch
  -- writes the completed and dying ledgers; and the finishing arm
  -- rewrites the registry and the live set.  So the whole of the map's
  -- growth is the fold's.
  dispatchShare-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    DispatchΦHyp sf gas id now B U i vals fin sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  dispatchShare-nest-nodes sf zero id now i vals fin sched st B U _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  dispatchShare-nest-nodes sf (suc gas) id now i vals false sched st B U hS =
    shareGo-nest-nodes sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B U hS
  dispatchShare-nest-nodes sf (suc gas) id now i vals true sched st B U hS =
    shareGo-nest-nodes sf gas id now i vals true
      (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B U hS

  -- ONE ADMITTED REGISTRATION AT A TIME.  The join telescopes on both
  -- components at once: the map is bounded by the map it entered on
  -- joined with the registry it entered on, and the REGISTRY it entered
  -- on is bounded by the one this fold started at -- which is the
  -- registry arm's own walk theorem, spent here rather than assumed.
  shareGo-nest-nodes : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    ShareGoΦHyp sf gas id now B U i vals fin ps sched st →
    foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0
      (EvalSt.nodes (proj₂ (proj₂ (shareGo sf gas id now i vals fin ps sched st))))
      ≤ foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  shareGo-nest-nodes sf gas id now i vals fin [] sched st B U _ =
    ≤-trans (m≤m⊔n (foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st))
                   (regsNestMax (EvalSt.registry st)))
            (m≤m⊔n _ U)
  shareGo-nest-nodes sf gas id now i vals fin ((rid , p) ∷ ps) sched st B U hS
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nest-nodes sf gas id now i vals fin ps sched st B U hS
  ... | false =
    ≤-trans (shareGo-nest-nodes sf gas id now i vals fin ps
               (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B U (proj₂ (proj₂ hS)))
            (⊔-lub (⊔-lub (foldPath-nest-nodes sf gas id now (toℕ i) p vals
                             EVS fin sched st₀ B U
                             (proj₁ hS) (proj₁ (proj₂ hS)))
                          (≤-trans (foldPath-nest-regs sf gas id now (toℕ i) p vals
                                      EVS fin sched st₀ B U
                                      (proj₁ hS) (proj₁ (proj₂ hS)))
                                   (⊔-lub (≤-trans (m≤n⊔m N R) (m≤m⊔n _ U))
                                          (m≤n⊔m (N ⊔ R) U))))
                   (m≤n⊔m (N ⊔ R) U))
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    EVS = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas id now (toℕ i) p vals EVS fin sched st₀
    N = foldr (λ kv acc → nodeNest (proj₂ kv) ⊔ acc) 0 (EvalSt.nodes st)
    R = regsNestMax (EvalSt.registry st)
