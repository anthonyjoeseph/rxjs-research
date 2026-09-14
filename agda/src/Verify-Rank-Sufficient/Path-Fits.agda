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

-- AND ALL FIVE FRAMES ARE PATH-LOCAL NOW, WHICH IS WHAT THE WIDER
-- PAYLOAD CURRENCY BOUGHT AND THE WHOLE REASON THIS MODULE LOST A
-- SHELF.  A bound in the per-value reading carries the DELIVERY COUNT
-- beside the hop, and the delivery count is exactly what a template
-- applied to a bound needs to be read against — so what a `map-f` or a
-- `scan-f` hands on is now a function of the frame and the bound it was
-- entered under, spelled once on the shelf and spent here.  A prefix
-- and an inner's exit hand back what came in; a flattener hands back
-- one more hop at the same count.  Five arms, five residues, no head.

-- SO THE PREMISE IS THREADED RATHER THAN COUNTED.  The old one summed
-- the path's flatteners and asked the total to fit, which is the only
-- premise a walk whose two heads were pinned at a HEADROOM could state;
-- the residue now being computable frame by frame, the premise is the
-- same recursion as the walk itself — carry the bound through each
-- frame's own residue and ask each flattener for its one hop where the
-- flattener stands.  That is strictly stronger where a template shrinks
-- a reading and strictly weaker nowhere, and it is stated in the
-- currency the shelf is stated in, so every arm discharges by handing
-- the shelf entry its own hypothesis.
module Verify-Rank-Sufficient.Path-Fits where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _∸_; _≤_; _<_; _≡ᵇ_; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Data.Nat.Induction using (<-wellFounded-fast)
open import Induction.WellFounded using (Acc; acc)

open import Rx.Prim using (Fuel; Tick; Id; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Strat-Order using (_≺_)
open import Rx.Hop-Depth using (Rd; Rd₃; rdᵛ)
open import Rx.Slot-Read using (slotRd)
open import Rx.Evaluator using (Frame; Path; root; share-sink; _↠_;
  map-f; scan-f; take-f; from-inner; thru-outer; NodeId; AllOp;
  Sched; EvalSt; Arrival; arrTy; arrVal; arrTick; arrivalWitness;
  RegId; AtFloor; chainsOf; chainStep; cascadeLatch; sched-next; cascade;
  foldPath; shareAdmit; shareLatch; stHop; floorFalls)
open import Verify-Rank-Sufficient.Fits using (PathFits; at-root; at-sink;
  through; FrameDryUnder; ShareDryUnder; arrivalRank;
  ChainsFit; ArrivalFits; DrainFits; ShareChainsFit)
open import Verify-Rank-Sufficient.Fold-Path using (dispatchShare-dry-free)
open import Verify-Rank-Sufficient.Push-Carried using (FrameCarries;
  mapRd; map-frame-carried; scan-frame-carried; take-frame-carried;
  thru-outer-frame-carried)
open import Verify-Rank-Sufficient.Push-Dry using (FrameDry;
  map-frame-dry; scan-frame-dry; take-frame-dry)

----------------------------------------------------------------------
-- WHAT THE WALK IS OWED, THREADED.  One clause per constructor, each
-- carrying the bound forward through that frame's own residue — the
-- same residues the shelf's entries hand back, so every arm of the walk
-- below meets its entry at a bound that is already the right one.
--
-- ONLY TWO CLAUSES ASK FOR ANYTHING.  A flattener asks for its one hop
-- of store headroom WHERE IT STANDS, which is what makes the premise
-- sensitive to a template above it shrinking the reading; and a sink
-- asks that the payload's hop sit under the store's, which is the
-- dispatch's own entry condition.  The root asks nothing, and neither
-- do the three frames whose residue is a transport.
----------------------------------------------------------------------

PathUnder : ∀ {n} {Γ : Ctx n} {lo s t} → (Fin n → Rd₃) → ℕ →
  Path Γ lo s t → Rd → Set
PathUnder ψ Rst root                    Rin = ⊤
PathUnder ψ Rst (share-sink i _)        Rin = proj₂ Rin ≤ Rst
PathUnder ψ Rst (map-f fn ↠ κ)          Rin = PathUnder ψ Rst κ
                                                (mapRd ψ Rin fn)
PathUnder ψ Rst (scan-f fn nid ↠ κ)     Rin = PathUnder ψ Rst κ
                                                (mapRd ψ Rin fn)
PathUnder ψ Rst (take-f nid ↠ κ)        Rin = PathUnder ψ Rst κ Rin
PathUnder ψ Rst (from-inner o a i ↠ κ)  Rin = PathUnder ψ Rst κ Rin
PathUnder ψ Rst (thru-outer op nid ↠ κ) Rin =
  suc (proj₂ Rin) ≤ Rst
  × PathUnder ψ Rst κ (proj₁ Rin , suc (proj₂ Rin))

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
dry-under : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u} {τ} {lo}
  (ac : Acc _≺_ τ) (id : Id) (now : Tick) (f : Frame Γ s u)
  (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) →
  FrameDry {e = e} ac id now f κ →
  FrameDryUnder {e = e} ac id now f κ ψ Rin Rst
dry-under ac id now f κ ψ Rin Rst d vals fin sd st _ _ =
  d vals fin sd st

-- LEAVING an inner, which is the edge the flattener's own entry already
-- paid for: the values are the inner's and cross unchanged, so both the
-- bound and the store come back where they were
--
-- DEAD ROUTE: closing the dry half as an unreachable branch under the
--   registration's own floor test.  The test sits inside the SLOT arm of
--   the subscribe, downstream of the inner's subscription rather than a
--   gate on it, so the frame fires whatever the test decides — and the
--   arm it guards is denominated in the FLOOR while every dry close on
--   this face is minted at RANK zero.  A floor decision cannot reach a
--   rank obligation, so nothing about the exits below narrows this.
-- DEAD ROUTE: instantiating either statement on the `fin = false` arm,
--   where the frame is the identity.  It was the only arm ever reached
--   and it buys INSTANTIABILITY rather than coverage: the element type
--   carries neither deliveries nor hop depth, so all three conjuncts of
--   the carried row compare nought against nought — both halves of the
--   payload pair and the store — and the dry row holds by `any` on the
--   empty list the identity arm returns.  Where the whole risk sits is
--   the `fin = true` arm, which inspects the registrations and decides
--   whether to drain, and no row on the false arm narrows it however
--   many are added.
-- RECOVERY: git show 11c6fcf:agda/evidence/probed/Probed/Exit-Frame.agda
--   restores the wrapping-rate corpus both dead routes above were
--   measured on, with the dry channel read beside the carried rows.
--   The programs and the plumbing are what transfer; the rows have to
--   be re-run, since they were taken against a reading this tier is
--   replacing.
-- RECOVERY: git show 873c905:agda/evidence/probed/Probed/Inner-Bound.agda
--   restores a harness that reaches a flattener INSIDE a share's def and
--   reads the queued value back out of the machine's own node table by
--   `refl`.  That is the plumbing the `fin = true` arm wants and the
--   reason the file is worth naming after its own target went: its rows
--   expired with the input bound, its programs did not.
postulate
  from-inner-carried : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp)
    (allNode innerInstance : NodeId) (κ : Path Γ lo s t) (ψ : Fin n → Rd₃)
    (Rin : Rd) (Rst : ℕ) →
    FrameCarries {e = e} ac id now
      (from-inner {s = s} op allNode innerInstance) κ ψ Rin Rin Rst

  from-inner-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp)
    (allNode innerInstance : NodeId) (κ : Path Γ lo s t) (ψ : Fin n → Rd₃)
    (Rin : Rd) (Rst : ℕ) →
    FrameDryUnder {e = e} ac id now
      (from-inner {s = s} op allNode innerInstance) κ ψ Rin Rst

-- THE FLATTENER, which is the only frame that subscribes, so it is the
-- only one of the three where dryness is reachable at all.  It is held
-- under the same headroom its carried entry is: one above the incoming
-- bound has to fit under the store's.
--
-- AND THAT HEADROOM IS NOW IN THE WRONG CURRENCY, WHICH PUTS THIS
-- STATEMENT AT SHAPE.  The premise is a fact about the READING, while
-- the arm it exists to refuse turns on the RANK — the machine tests the
-- delivered inner's observable nesting against the component it stands
-- at and takes the dry exit on the negative answer.  Those became two
-- quantities when the rank stopped pricing what a run delivers, so no
-- hypothesis this statement carries can decide that arm and a
-- restatement is guaranteed rather than merely likely.  What it wants
-- is a bound on the nesting of the values the frame is HANDED; what
-- discharges that bound is that a subscription cannot deliver an
-- observable written deeper than the one it was reading.  Neither is
-- local to this row — the values are quantified freely one level down,
-- so the premise has to be threaded to the walk that knows which burst
-- they came out of, and that thread is the restatement's real cost.
--
-- DEAD ROUTE: reading the dry channel at three outer sources wrapping
--   at rates one, two and three, taken at the points the carried rows
--   already stand at.  Every half was load-bearing while it ran — the
--   handed reading positive, so the outer did emit; the rank exceeding
--   the HOP half by exactly one at every point, so the premise was
--   decided rather than afforded; the DELIVERY half saturated, handed
--   equal to held at one, two and two, so a reading that undercharged
--   the outer by a single delivery would have crossed.  The rows are
--   gone because the hop guard refuses before the outer emits at all,
--   which empties every figure they compared and leaves them agreeing
--   with themselves.  And the shape that was never reached is still
--   never reached: a frame subscribing an inner whose rank is already
--   spent is the only shape the dry branch is reachable from, and it is
--   not reachable from a root.
postulate
  thru-outer-frame-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ} {lo}
    (ac : Acc _≺_ τ) (id : Id) (now : Tick) (op : AllOp) (nid : NodeId)
    (κ : Path Γ lo u t) (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) →
    suc (proj₂ Rin) ≤ Rst →
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

ShareChainsHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo} →
  Acc _≺_ τ → Acc _<_ (n ∸ lo) → Id → Tick → (i : Fin n) →
  (Fin n → Rd₃) → Rd → ℕ →
  List (Val Γ (lookup Γ i)) → Bool →
  List (RegId × Path Γ lo (lookup Γ i) t) → Sched Γ → EvalSt e → Set
ShareChainsHop ac acl id now i ψ Rin Rst vals fin [] sd st = ⊤
ShareChainsHop {e = e} ac acl id now i ψ Rin Rst vals fin
  ((rid , p) ∷ ps) sd st
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = ShareChainsHop {e = e} ac acl id now i ψ Rin Rst vals fin
                ps sd st
... | false =
      let st′ = record st { delivered = rid ∷ EvalSt.delivered st }
          out = foldPath ac acl id now (toℕ i) p vals
                  (if fin then close (toℕ i) exhausted ∷ [] else [])
                  fin sd st′
      in PathUnder ψ (stHop ψ st′ ⊔ Rst) p Rin
         × ShareChainsHop {e = e} ac acl id now i ψ Rin Rst vals fin ps
             (proj₁ (proj₂ out)) (proj₂ (proj₂ out))

ShareHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo} →
  Acc _≺_ τ → Acc _<_ (n ∸ lo) → Id → Tick → (i : Fin n) → lo ≤ toℕ i →
  (Fin n → Rd₃) → Rd → ℕ →
  List (Val Γ (lookup Γ i)) → Bool → Sched Γ → EvalSt e → Set
ShareHop {e = e} ac (acc rs) id now i below ψ Rin Rst vals fin sd st =
  ShareChainsHop {e = e} ac (rs (floorFalls i below)) id now i ψ Rin Rst vals fin
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
-- AND AS WRITTEN IT IS FALSE, WHICH IS A GAP BETWEEN WHAT THE PREMISE
-- CARRIES AND WHAT THE WALK READS.  The one hypothesis bounds the
-- payload that ENTERS the dispatch; the walk is read along each
-- admitted chain, and a chain's own frames move the payload before its
-- flattener is reached — a fold re-wraps its accumulator, so the
-- reading after the fold is the fold's and not the dispatched value's.
-- No bound on what enters can bound what the chain has made of it.
--
-- AND THE MACHINE IS NOT DRY WHERE THE WITNESS STANDS, WHICH IS WHAT
-- MAKES THIS A RESTATEMENT RATHER THAN A LOSS.  The rank a dispatch is
-- actually entered under is `arrivalRank`, a SUM whose term-depth
-- summand alone clears the crossing by a wide margin at the witness.
-- So the point is legal under the premise as written and unreachable at
-- every call site: a true form carries the registry's own reading — the
-- fact the entry invariant already knows about the chains a share
-- admits — inward, rather than deriving it from the entering payload.
--
-- REFUTED: `Refuted.Share-Chain`
-- RECOVERY: git show 19ce2c6:agda/evidence/probed/Probed/Sink-Dry.agda
--   restores the three-chain share harness and its store figures — the
--   expensive half of instantiating this leaf, and reusable against
--   whatever the restatement turns out to be.  Its rows are not: one is
--   the refuted point above and the rest are the `⊤` arm.
postulate
  share-chain-hop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo}
    (ac : Acc _≺_ τ) (acl : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick)
    (i : Fin n) (below : lo ≤ toℕ i)
    (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) → proj₂ Rin ≤ Rst →
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sd : Sched Γ) (st : EvalSt e) →
    ShareHop {e = e} ac acl id now i below ψ Rin Rst vals fin sd st

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

pathFits : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u} {τ} {lo}
  (ac : Acc _≺_ τ) (acl : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick)
  (ψ : Fin n → Rd₃)
  (Rst : ℕ) (κ : Path Γ lo u t) (Rin : Rd) → PathUnder ψ Rst κ Rin →
  PathFits {e = e} ac acl id now ψ Rst κ Rin

share-sink-dry : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo}
  (ac : Acc _≺_ τ) (acl : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick)
  (i : Fin n) (below : lo ≤ toℕ i)
  (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ) → proj₂ Rin ≤ Rst →
  ShareDryUnder {e = e} ac acl id now i below ψ Rin Rst

shareChainsFit : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {τ} {lo}
  (ac : Acc _≺_ τ) (acl : Acc _<_ (n ∸ lo)) (id : Id) (now : Tick)
  (i : Fin n)
  (ψ : Fin n → Rd₃) (Rin : Rd) (Rst : ℕ)
  (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
  (ps : List (RegId × Path Γ lo (lookup Γ i) t))
  (sd : Sched Γ) (st : EvalSt e) →
  ShareChainsHop {e = e} ac acl id now i ψ Rin Rst vals fin ps sd st →
  ShareChainsFit {e = e} ac acl id now i ψ Rin Rst vals fin ps sd st

pathFits ac acl id now ψ Rst root Rin h = at-root

pathFits ac acl id now ψ Rst (share-sink i below) Rin h =
  at-sink (share-sink-dry ac acl id now i below ψ Rin Rst h)

pathFits ac acl id now ψ Rst (map-f fn ↠ κ) Rin h =
  through (map-frame-carried ac id now fn κ ψ Rin Rst)
          (dry-under ac id now (map-f fn) κ ψ Rin Rst
            (map-frame-dry ac id now fn κ))
          (pathFits ac acl id now ψ Rst κ (mapRd ψ Rin fn) h)

pathFits ac acl id now ψ Rst (scan-f fn nid ↠ κ) Rin h =
  through (scan-frame-carried ac id now fn nid κ ψ Rin Rst)
          (dry-under ac id now (scan-f fn nid) κ ψ Rin Rst
            (scan-frame-dry ac id now fn nid κ))
          (pathFits ac acl id now ψ Rst κ (mapRd ψ Rin fn) h)

pathFits ac acl id now ψ Rst (take-f nid ↠ κ) Rin h =
  through (take-frame-carried ac id now nid κ ψ Rin Rst)
          (dry-under ac id now (take-f nid) κ ψ Rin Rst
            (take-frame-dry ac id now nid κ))
          (pathFits ac acl id now ψ Rst κ Rin h)

pathFits ac acl id now ψ Rst (from-inner op k j ↠ κ) Rin h =
  through (from-inner-carried ac id now op k j κ ψ Rin Rst)
          (from-inner-dry ac id now op k j κ ψ Rin Rst)
          (pathFits ac acl id now ψ Rst κ Rin h)

pathFits ac acl id now ψ Rst (thru-outer op nid ↠ κ) Rin h =
  through (thru-outer-frame-carried ac id now op nid κ ψ Rin Rst
            (proj₁ h))
          (thru-outer-frame-dry ac id now op nid κ ψ Rin Rst (proj₁ h))
          (pathFits ac acl id now ψ Rst κ
            (proj₁ Rin , suc (proj₂ Rin)) (proj₂ h))

-- THE SINK'S BODY, AND THE PEEL IS MATCHED HERE FOR THE SAME REASON THE
-- DISPATCH MATCHES IT.  The fan-out stands a floor above the chain that
-- reached it, so what the fold needs is the walk applied at each
-- admitted chain under the peeled witness — and matching is what makes
-- the descent one the termination checker can follow.  There is no
-- spent-counter arm to write: the clamp it answered for has no type.
share-sink-dry {e = e} ac (acc rs) id now i below ψ Rin Rst h vals fin sd st
  hv hs =
  dispatchShare-dry-free {e = e} ac (acc rs) id now i below vals fin sd st hv
    (shareChainsFit {e = e} ac (rs (floorFalls i below)) id now i ψ Rin Rst
      vals fin
      (shareAdmit i (EvalSt.registry st)) sd (shareLatch i fin st)
      (share-chain-hop ac (acc rs) id now i below ψ Rin Rst h vals fin sd st))

shareChainsFit ac acl id now i ψ Rin Rst vals fin []       sd st hp = tt
shareChainsFit {e = e} ac acl id now i ψ Rin Rst vals fin
  ((rid , p) ∷ ps) sd st hp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = shareChainsFit {e = e} ac acl id now i ψ Rin Rst vals fin
                ps sd st hp
... | false =
      pathFits ac acl id now ψ (stHop ψ st′ ⊔ Rst) p Rin (proj₁ hp)
      , shareChainsFit {e = e} ac acl id now i ψ Rin Rst vals fin ps
          (proj₁ (proj₂ out)) (proj₂ (proj₂ out)) (proj₂ hp)
  where
  st′ = record st { delivered = rid ∷ EvalSt.delivered st }
  out = foldPath ac acl id now (toℕ i) p vals
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

-- ONE CHAIN'S HEADROOM.  The walk needs the ARRIVING VALUE'S OWN
-- READING, threaded down the chain, to keep each flattener under the
-- rank the arrival enters at — and that rank is the program's own
-- reading ABOVE the join the payload sits in, so what this really asks
-- is that a registered chain not flatten past what the program reads.
-- That is the form the remaining risk of this face is now stated in.
--
-- AND THE PAYLOAD ENTERS IN FULL RATHER THAN AT ITS HOP, which is the
-- one place the widening is visible from outside this module: a value's
-- reading carries the delivery count a template has to be read against,
-- and dropping it here would put the walk back where its two heads were
-- unstatable.
HopsFitAt : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  (a : Arrival Γ) → Sched Γ → EvalSt e → AtFloor Γ (arrTy a) t → Set
HopsFitAt a sched st c =
  let ψ = slotRd (Sched.slots sched) in
  PathUnder ψ (arrivalRank a sched st) (proj₂ c)
    (rdᵛ ψ (arrTy a) (arrVal a))

ChainsHop : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} →
  (a : Arrival Γ) → Id → List (RegId × AtFloor Γ (arrTy a) t) →
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
  (a : Arrival Γ) (id : Id) (cs : List (RegId × AtFloor Γ (arrTy a) t))
  (sched : Sched Γ) (st : EvalSt e) →
  ChainsHop {e = e} a id cs sched st → ChainsFit {e = e} a id cs sched st
chainsFit a id []               sched st hp = tt
chainsFit {n = n} {e = e} a id ((rid , c) ∷ cs) sched st hp
  with any (_≡ᵇ rid) (EvalSt.cancelled st)
... | true  = chainsFit {e = e} a id cs sched st hp
... | false =
      pathFits (arrivalWitness a sched st′) (<-wellFounded-fast (n ∸ proj₁ c))
        id (arrTick a)
        (slotRd (Sched.slots sched)) (arrivalRank a sched st′) (proj₂ c)
        (rdᵛ (slotRd (Sched.slots sched)) (arrTy a) (arrVal a))
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
