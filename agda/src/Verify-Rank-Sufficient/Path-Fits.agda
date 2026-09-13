-- THE PRODUCER OF A CHAIN'S FITS CERTIFICATE.  Everything under the
-- door consumes one — the chain fold reads it constructor by
-- constructor — and until this module nothing in `src` built one, which
-- is why the frame shelf's entries and the sink's obligation both sat
-- with a consumer that could never be reached.

-- THE RESIDUE IS PINNED BY A FUNCTION, WHICH IS THE WHOLE DESIGN
-- DECISION HERE.  `through` quantifies its outgoing bound
-- existentially, so a producer is free to pick it — and picking it
-- LARGE is not the easy way out it looks like, because the bound it
-- picks is what the rest of the walk is then held to: a deeper frame's
-- dryness is stated over every payload its incoming bound admits, so a
-- slack residue makes the obligations underneath STRICTLY HARDER.  The
-- certificate is therefore not vacuous, and a producer has to choose
-- the residue tightly or fail further down.

-- WHICH SPLITS THE FIVE FRAMES INTO TWO GROUPS, AND THE SPLIT IS NOT A
-- MATTER OF EFFORT.  Three of them price their own output out of what
-- they were handed: a prefix and an inner's exit hand back what came
-- in, and a flattener hands back one more.  Those are path-local, so
-- the walk below recurses through them.  A TEMPLATE and a FOLD are not:
-- what a template emits is its body evaluated at the payload, and what
-- a fold emits is an accumulator refolded once per DELIVERY of its
-- source — and a payload bound reads hops, not deliveries, so two
-- payloads admitted by the same bound drive a fold a different number
-- of times.  No function of the frame and the incoming bound can price
-- either, and the shelf says the same thing from its side: its template
-- entry is pinned at the readings of a source EXPRESSION, which a chain
-- step does not carry.  So those two are pinned at the HEADROOM the
-- tail leaves instead of at a figure read off the frame — the largest
-- bound the rest of the path can still afford, which is a function of
-- what the walk does hold.

-- AND THE PREMISE IS THE PATH'S OWN FLATTENER COUNT, which is the one
-- quantity the recursion needs and the only one it can compute.  Each
-- flattener spends one of the store bound's headroom, so a path with k
-- of them needs k to spare — and the rank an arrival enters at supplies
-- exactly the program's own reading above the payload, which is where
-- the leaf below sends the remaining risk.  The count charges a
-- template and a fold NOTHING, so the headroom those two are pinned at
-- is the whole of what is left rather than a share of it: that makes
-- each of them a stronger statement, which is the safe direction for a
-- gap.
module Verify-Rank-Sufficient.Path-Fits where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties using (≤-trans; ≤-reflexive; m≤m+n;
  m≤n+m; m∸n+n≡m; +-suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (refl; sym)

open import Rx.Prim using (Fuel; Tick; Id; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val; Fn; _×ᵗ_)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd₃; depthᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Frame; Path; root; share-sink; _↠_;
  map-f; scan-f; take-f; from-inner; thru-outer; NodeId; AllOp;
  Sched; EvalSt; Arrival; arrTy; arrVal; arrTick; arrivalWitness;
  RegId; chainsOf; chainStep; cascadeLatch; sched-next; cascade;
  foldPath; shareAdmit; shareLatch; stHop)
open import Verify-Rank-Sufficient.Fits using (PathFits; at-root; at-sink;
  through; FrameDryUnder; ShareDryUnder; arrivalRank;
  ChainsFit; ArrivalFits; DrainFits; ShareChainsFit)
open import Verify-Rank-Sufficient.Fold-Path using (dispatchShare-dry-free)
open import Verify-Rank-Sufficient.Push-Carried using (FrameCarries;
  take-frame-carried; thru-outer-frame-carried)
open import Verify-Rank-Sufficient.Push-Dry using (FrameDry;
  map-frame-dry; scan-frame-dry; take-frame-dry)

----------------------------------------------------------------------
-- WHAT A STEP COSTS THE STORE BOUND.  Only the flattener spends, and it
-- spends one: entering an inner is the hop edge and the residue it
-- hands back is one above what it was given.  Everything else hands
-- back a bound no larger, so it costs nothing.
----------------------------------------------------------------------

frameHop : ∀ {n} {Γ : Ctx n} {s u} → Frame Γ s u → ℕ
frameHop (map-f _)          = 0
frameHop (scan-f _ _)       = 0
frameHop (take-f _)         = 0
frameHop (from-inner _ _ _) = 0
frameHop (thru-outer _ _)   = 1

pathHops : ∀ {n} {Γ : Ctx n} {s t} → Path Γ s t → ℕ
pathHops root           = 0
pathHops (share-sink i) = 0
pathHops (f ↠ κ)        = frameHop f + pathHops κ

-- THE HEADROOM A TAIL LEAVES, and why the subtraction is total rather
-- than a truncation to be checked.  The walk's premise already puts the
-- tail's own flatteners under the store's figure, so the difference is
-- real at every point the recursion reaches and the tail's premise
-- holds by equality rather than by a bound.
headroom-fits : ∀ {n} {Γ : Ctx n} {s t} (Rin : ℕ) (κ : Path Γ s t)
  (Rst : ℕ) → Rin + pathHops κ ≤ Rst →
  (Rst ∸ pathHops κ) + pathHops κ ≤ Rst
headroom-fits Rin κ Rst h =
  ≤-reflexive (m∸n+n≡m (≤-trans (m≤n+m (pathHops κ) Rin) h))

----------------------------------------------------------------------
-- THE LEAVES OF THE WALK, and there are fewer than the five arms
-- suggest: the dry shelf already carries three of the four dry
-- obligations outright, so only the two frames that re-enter the
-- evaluator are owed anything.
----------------------------------------------------------------------

-- THREE OF THE FOUR DRY OBLIGATIONS ARE ALREADY DISCHARGED, AND
-- UNCONDITIONALLY.  A template, a fold and a prefix each reach no
-- `subscribeE` at all, so their dry-freedom holds at every payload and
-- every store rather than under a bound -- and the dry shelf proves
-- exactly that form.  The conditioned form this walk consumes is the
-- unconditional one with two hypotheses it does not read, so the
-- adapter below is the whole of the work, and no leaf is owed for any
-- of the three.
dry-under : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u)
  (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) →
  FrameDry {e = e} ac id now f κ →
  FrameDryUnder {e = e} ac id now f κ ψ Rin Rst
dry-under ac id now f κ ψ Rin Rst d vals fin sd st _ _ =
  d vals fin sd st

-- LEAVING an inner, which is the edge the flattener's own entry already
-- paid for: the values are the inner's and cross unchanged, so both the
-- bound and the store come back where they were
--
-- PROBED: `Probed.Exit-Frame` — both statements instantiated at one
--   flat program on the `fin = false` arm, where the frame is the
--   identity.  What that buys is INSTANTIABILITY and not coverage, and
--   the rows say so themselves: the element type carries no hop depth,
--   so both conjuncts of the carried row compare nought against nought,
--   and the dry row holds by `any` on the empty list the identity arm
--   returns.  NOT covered, and it is where the whole risk sits: the
--   `fin = true` arm, which is the one that inspects the registrations
--   and decides whether to drain.
postulate
  from-inner-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp)
    (allNode innerInstance : NodeId) (κ : Path Γ s t) (ψ : Fin n → Rd₃)
    (Rin Rst : ℕ) →
    FrameCarries {e = e} ac id now
      (from-inner {s = s} op allNode innerInstance) κ ψ Rin Rin Rst

  from-inner-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp)
    (allNode innerInstance : NodeId) (κ : Path Γ s t) (ψ : Fin n → Rd₃)
    (Rin Rst : ℕ) →
    FrameDryUnder {e = e} ac id now
      (from-inner {s = s} op allNode innerInstance) κ ψ Rin Rst

-- THE FLATTENER, which is the only frame that subscribes, so it is the
-- only one of the three where dryness is reachable at all.  It is held
-- under the same headroom its carried entry is: one above the incoming
-- bound has to fit under the store's
--
-- PROBED: `Probed.Exit-Frame` — three outer sources at wrapping rates
--   one, two and three, taken at the points the carried rows already
--   stand at, with the dry channel read.  LOAD-BEARING on both halves:
--   the handed reading is positive, so the outer did emit, and the rank
--   exceeds the bound by exactly one at every point, so the premise is
--   decided rather than afforded — a rank equal to the bound is the
--   refutation this would have reported.  NOT covered: a frame
--   subscribing an inner whose rank is already spent, which is the only
--   shape the dry branch is reachable from and is not reachable from a
--   root at all.
postulate
  thru-outer-frame-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) → suc Rin ≤ Rst →
    FrameDryUnder {e = e} ac id now (thru-outer op nid) κ ψ Rin Rst

----------------------------------------------------------------------
-- THE SINK'S PREMISE, WHICH IS THE DOOR'S CURRENCY ONE LEVEL IN.  The
-- fan-out is a leaf of this WALK and not a step of it — the chains the
-- dispatch enters are registered on the share and are not steps of the
-- path standing here — but it is no longer a leaf of the PROOF.  The
-- dispatch's own fold is a body, so what the sink reduces to is one
-- FLATTENER COUNT per admitted chain, stated in the same currency the
-- arrival's door is stated in and mentioning dryness nowhere.
--
-- AND THE BOUND EACH CHAIN IS HELD TO IS A JOIN WITH ITS OWN STATE.
-- The admitted chains are folded threading one state, so a premise
-- fixing the entering bound for all of them describes a run where the
-- fan-out writes nothing; joining each chain's own store reading on
-- asks instead at a bound the chain demonstrably sits under, which is
-- a residue the fold hands itself rather than one indexed by how many
-- registrations the share carries.
----------------------------------------------------------------------

ShareChainsHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} →
  Acc _≺_ τ → ℕ → Id → Tick → (i : Fin n) → (Fin n → Rd₃) → ℕ → ℕ →
  List (Val Γ (lookup Γ i)) → Bool →
  List (RegId × Path Γ (lookup Γ i) t) → Sched Γ → EvalSt e → Set
ShareChainsHop ac gas id now i ψ Rin Rst vals fin [] sd st = ⊤
ShareChainsHop {e = e} ac gas id now i ψ Rin Rst vals fin
  ((rid , p) ∷ ps) sd st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = ShareChainsHop {e = e} ac gas id now i ψ Rin Rst vals fin
                ps sd st
... | false =
      let st′ = record st { delivered = rid ∷ EvalSt.delivered st }
          out = foldPath ac gas id now (toℕ i) p vals
                  (if fin then close (toℕ i) exhausted ∷ [] else [])
                  fin sd st′
      in (Rin + pathHops p ≤ stHop ψ st′ ⊔ Rst)
         × ShareChainsHop {e = e} ac gas id now i ψ Rin Rst vals fin ps
             (proj₁ (proj₂ out)) (proj₂ (proj₂ out))

ShareHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} →
  Acc _≺_ τ → ℕ → Id → Tick → (i : Fin n) → (Fin n → Rd₃) → ℕ → ℕ →
  List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e → Set
ShareHop {e = e} ac gas id now i ψ Rin Rst vals fin sd st =
  ShareChainsHop {e = e} ac gas id now i ψ Rin Rst vals fin
    (shareAdmit i (EvalSt.registry st)) sd (shareLatch i fin st)

-- AND THE LEAF ITSELF, WHICH SAYS A REGISTERED CHAIN CARRIES NO MORE
-- FLATTENERS THAN THE BOUND IT IS ENTERED UNDER AFFORDS.  It is the
-- door's own claim at the fan-out's registry rather than at the
-- arrival's, and the two are separated by which list is walked: the
-- door reads `chainsOf`, this reads what the share admits.
--
-- AND INSTANTIATING IT COSTS WHAT RUNNING THE PROGRAM COSTS, PAID IN A
-- TYPE.  Each conjunct is cheap, reading the store at the state its
-- chain is ENTERED under; the recursive TAIL is taken at the state
-- that chain's `foldPath` RETURNS, so deciding the next chain's
-- cancellation test normalises the evaluator inside the type, once per
-- chain and compounding.  That is a property of this shape and not of
-- any harness, and it is what bounds the coverage below.
--
-- PROBED: `Probed.Sink-Dry` — one WRITING chain, where the store reads
--   one at subscribe, the dispatch's write lands, and the admitted list
--   is non-empty, so the premise recursed rather than meeting its `⊤`
--   arm; and TWO non-writing chains, which reach one hand-off of the
--   tail's threaded state against a join of nought, where a chain
--   carrying any flattener refutes.  NOT reached: a SECOND hand-off —
--   the state one chain returns being read by a chain that is not the
--   last, which is where a join drifting per chain would first show.
--   Three chains exhausted sixteen gigabytes without finishing, writing
--   and non-writing alike, so the axis is the width the tail recurses
--   on rather than the depth a chain writes.  Also unreached:
--   observable-valued share slots, whose left side would read positive
--   where every row here reads nought; completing dispatches; a spent
--   counter; and stores deepened by an earlier cascade step.
postulate
  share-chain-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
    (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (ψ : Fin n → Rd₃) (Rin Rst : ℕ) → Rin ≤ Rst →
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sd : Sched Γ) (st : EvalSt e) →
    ShareHop {e = e} ac gas id now i ψ Rin Rst vals fin sd st

-- THE TWO ARMS WHOSE RESIDUE IS NOT READ OFF THE FRAME, pinned at the
-- HEADROOM THE TAIL LEAVES rather than at a figure of their own.  What
-- a map or a scan hands on is read off the SOURCE EXPRESSION — an
-- event count for one, a seed and a delivery count for the other — and
-- a chain records the frame, not what it was built from, so the walk
-- can supply neither.  What it CAN supply is the largest bound the rest
-- of the path can still afford: everything below this frame has to fit
-- under `Rst` after its own flatteners are paid for, so `Rst ∸ pathHops
-- κ` is exactly that and the tail's premise holds by subtraction.  The
-- claim is therefore that these two frames stay inside the headroom,
-- which is what a frame-shaped statement can say and an existential
-- residue cannot.
--
-- AND THE ASYMMETRY IS FORCED FOR THE FOLD, NOT CHOSEN.  Its outputs
-- are the successive ACCUMULATORS, so what it hands back is a function
-- of the store and the step and the payload enters only as the step's
-- second argument — a step ignoring that argument cuts the payload out
-- of the answer, and then no bound on the payload bounds the output.
-- The headroom pin is what survives that: it is read off the STORE
-- bound, which is the side the accumulator comes from.
--
-- REFUTED: `Refuted.Scan-Store` — the symmetric form, where the fold's
--   residue is its own incoming bound.
postulate
  map-head-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (fn : Fn Γ [] [] [] s u)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) →
    FrameCarries {e = e} ac id now (map-f fn) κ ψ
      Rin (Rst ∸ pathHops κ) Rst

  scan-head-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (nid : NodeId)
    (κ : Path Γ u t) (ψ : Fin n → Rd₃) (Rin Rst : ℕ) →
    FrameCarries {e = e} ac id now (scan-f fn nid) κ ψ
      Rin (Rst ∸ pathHops κ) Rst

----------------------------------------------------------------------
-- THE WALK.  One clause per path constructor, and one per frame under
-- the step constructor, so the two leaf arms are visible as arms rather
-- than hidden inside a catch-all.
--
-- AND IT IS MUTUAL WITH THE FAN-OUT, WHICH IS WHERE THE DISPATCH
-- COUNTER EARNS ITS KEEP.  A sink hands its values to chains that are
-- themselves walked, so the walk re-enters itself through the machine
-- rather than through the path — and nothing about the path is smaller
-- on the other side.  What is smaller is the counter the evaluator
-- peels at every share boundary, so the three below descend on it
-- first and on their own structure second: the walk on the path, the
-- fan-out on the admitted list.
----------------------------------------------------------------------

pathFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (ψ : Fin n → Rd₃)
  (Rst : ℕ) (κ : Path Γ u t) (Rin : ℕ) → Rin + pathHops κ ≤ Rst →
  PathFits {e = e} ac gas id now ψ Rst κ Rin

share-sink-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (ψ : Fin n → Rd₃) (Rin Rst : ℕ) → Rin ≤ Rst →
  ShareDryUnder {e = e} ac gas id now i ψ Rin Rst

shareChainsFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ}
  (ac : Acc _≺_ τ) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
  (ψ : Fin n → Rd₃) (Rin Rst : ℕ)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ (lookup Γ i) t))
  (sd : Sched Γ) (st : EvalSt e) →
  ShareChainsHop {e = e} ac gas id now i ψ Rin Rst vals fin ps sd st →
  ShareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin ps sd st

pathFits ac gas id now ψ Rst root Rin h = at-root

pathFits ac gas id now ψ Rst (share-sink i) Rin h =
  at-sink (share-sink-dry ac gas id now i ψ Rin Rst
            (≤-trans (m≤m+n Rin 0) h))

pathFits ac gas id now ψ Rst (map-f fn ↠ κ) Rin h =
  through (map-head-carried ac id now fn κ ψ Rin Rst)
          (dry-under ac id now (map-f fn) κ ψ Rin Rst
            (map-frame-dry ac id now fn κ))
          (pathFits ac gas id now ψ Rst κ (Rst ∸ pathHops κ)
            (headroom-fits Rin κ Rst h))

pathFits ac gas id now ψ Rst (scan-f fn nid ↠ κ) Rin h =
  through (scan-head-carried ac id now fn nid κ ψ Rin Rst)
          (dry-under ac id now (scan-f fn nid) κ ψ Rin Rst
            (scan-frame-dry ac id now fn nid κ))
          (pathFits ac gas id now ψ Rst κ (Rst ∸ pathHops κ)
            (headroom-fits Rin κ Rst h))

pathFits ac gas id now ψ Rst (take-f nid ↠ κ) Rin h =
  through (take-frame-carried ac id now nid κ ψ Rin Rst)
          (dry-under ac id now (take-f nid) κ ψ Rin Rst
            (take-frame-dry ac id now nid κ))
          (pathFits ac gas id now ψ Rst κ Rin h)

pathFits ac gas id now ψ Rst (from-inner op k j ↠ κ) Rin h =
  through (from-inner-carried ac id now op k j κ ψ Rin Rst)
          (from-inner-dry ac id now op k j κ ψ Rin Rst)
          (pathFits ac gas id now ψ Rst κ Rin h)

pathFits ac gas id now ψ Rst (thru-outer op nid ↠ κ) Rin h =
  through (thru-outer-frame-carried ac id now op nid κ ψ Rin Rst fit)
          (thru-outer-frame-dry ac id now op nid κ ψ Rin Rst fit)
          (pathFits ac gas id now ψ Rst κ (suc Rin) h′)
  where
  h′ : suc Rin + pathHops κ ≤ Rst
  h′ = ≤-trans (≤-reflexive (sym (+-suc Rin (pathHops κ)))) h

  fit : suc Rin ≤ Rst
  fit = ≤-trans (m≤m+n (suc Rin) (pathHops κ)) h′

-- THE SINK'S BODY.  A spent counter reaches the dispatch's clamp, which
-- emits nothing at all; every other reaches the fan-out's fold, and
-- what that fold needs is the walk applied at each admitted chain.
share-sink-dry ac zero id now i ψ Rin Rst h vals fin sd st hv hs = refl
share-sink-dry {e = e} ac (suc gas) id now i ψ Rin Rst h vals fin sd st
  hv hs =
  dispatchShare-dry-free {e = e} ac gas id now i vals fin sd st hv
    (shareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin
      (shareAdmit i (EvalSt.registry st)) sd (shareLatch i fin st)
      (share-chain-hop ac gas id now i ψ Rin Rst h vals fin sd st))

shareChainsFit ac gas id now i ψ Rin Rst vals fin []       sd st hp = tt
shareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin
  ((rid , p) ∷ ps) sd st hp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin
                ps sd st hp
... | false =
      pathFits ac gas id now ψ (stHop ψ st′ ⊔ Rst) p Rin (proj₁ hp)
      , shareChainsFit {e = e} ac gas id now i ψ Rin Rst vals fin ps
          (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) (proj₂ hp)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  out = foldPath ac gas id now (toℕ i) p vals
          (if fin then close (toℕ i) exhausted ∷ [] else []) fin sd st′

----------------------------------------------------------------------
-- THE PREMISE, MIRRORING THE OBLIGATION IT DISCHARGES.  `ChainsFit`
-- threads one state across the chains an arrival reaches and skips a
-- cancelled registration, so a premise stated over the list flat would
-- not line up with it clause for clause.  This recursion is the same
-- recursion with the fit replaced by the one number the walk above
-- needs, which is what makes the body below a transport rather than a
-- proof.
----------------------------------------------------------------------

-- ONE CHAIN'S HEADROOM.  The walk needs the arriving payload plus the
-- chain's flatteners to fit under the rank the arrival enters at, and
-- that rank is the program's own reading ABOVE the join the payload
-- sits in — so what this really asks is that a registered chain carry
-- no more flatteners than the program reads, which is the form the
-- remaining risk of this face is now stated in.
HopsFitAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  (a : Arrival Γ) → Sched Γ → EvalSt e → Path Γ (arrTy a) t → Set
HopsFitAt a sched st c =
  let ψ = slotRd (Sched.slots sched) in
  depthᵛ ψ (arrTy a) (arrVal a) + pathHops c ≤ arrivalRank a sched st

ChainsHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  (a : Arrival Γ) → Id → List (RegId × Path Γ (arrTy a) t) →
  Sched Γ → EvalSt e → Set
ChainsHop a id []               sched st = ⊤
ChainsHop {e = e} a id ((rid , c) ∷ cs) sched st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = ChainsHop {e = e} a id cs sched st
... | false =
      let st′ = record st { delivered = rid ∷ EvalSt.delivered st }
          out = chainStep id a c sched st′
      in HopsFitAt a sched st′ c
         × ChainsHop {e = e} a id cs (proj₁ (proj₂ out)) (proj₂ (proj₂ out))

ArrivalHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Id → Arrival Γ → Sched Γ → EvalSt e → Set
ArrivalHop {e = e} id a sched st =
  ChainsHop {e = e} a id (chainsOf a st) sched (cascadeLatch a st)

DrainHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  Fuel → Id → Sched Γ → EvalSt e → Set
DrainHop zero    id sched st = ⊤
DrainHop (suc k) id sched st with sched-next sched
... | inj₁ _            = ⊤
... | inj₂ (a , sched′) =
      ArrivalHop id a sched′ st
      × DrainHop k (suc id) (proj₁ (proj₂ (cascade a id sched′ st)))
                            (proj₂ (proj₂ (cascade a id sched′ st)))

----------------------------------------------------------------------
-- THE TRANSPORT.  Each of the three is the same recursion as the
-- obligation it builds, so the only content is the walk above applied
-- at each chain — which is what makes the whole of the remaining risk
-- land on ONE leaf, in a currency (a count of flatteners against the
-- program's reading) that no longer mentions dryness at all.
----------------------------------------------------------------------

chainsFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (a : Arrival Γ) (id : Id) (cs : List (RegId × Path Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  ChainsHop {e = e} a id cs sched st → ChainsFit {e = e} a id cs sched st
chainsFit a id []               sched st hp = tt
chainsFit {n = n} {e = e} a id ((rid , c) ∷ cs) sched st hp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = chainsFit {e = e} a id cs sched st hp
... | false =
      pathFits (arrivalWitness a sched st′) n id (arrTick a)
        (slotRd (Sched.slots sched)) (arrivalRank a sched st′) c
        (depthᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a))
        (proj₁ hp)
      , chainsFit {e = e} a id cs (proj₁ (proj₂ out)) (proj₂ (proj₂ out))
          (proj₂ hp)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  out = chainStep id a c sched st′

arrivalFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (id : Id) (a : Arrival Γ) (sched : Sched Γ) (st : EvalSt e) →
  ArrivalHop {e = e} id a sched st → ArrivalFits {e = e} id a sched st
arrivalFits {e = e} id a sched st hp =
  chainsFit {e = e} a id (chainsOf a st) sched (cascadeLatch a st) hp

drainFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
  (fuel : Fuel) (id : Id) (sched : Sched Γ) (st : EvalSt e) →
  DrainHop {e = e} fuel id sched st → DrainFits {e = e} fuel id sched st
drainFits zero    id sched st hp = tt
drainFits {e = e} (suc k) id sched st hp with sched-next sched
... | inj₁ _            = tt
... | inj₂ (a , sched′) =
      arrivalFits {e = e} id a sched′ st (proj₁ hp)
      , drainFits {e = e} k (suc id)
          (proj₁ (proj₂ (cascade a id sched′ st)))
          (proj₂ (proj₂ (cascade a id sched′ st))) (proj₂ hp)
