-- THE JOIN'S LEAVES, AT THE POINT THE PARENT SPENDS THEM.  The chain
-- descent is a body over a `⊔`-fold now, and what the fold takes as
-- parameters are the two obligations at ONE edge: that a frame's own
-- spend fits under the position's ceiling, and that the ceiling
-- survives the step that frame makes.  Both are stated at a single
-- `Frame` and a single `Path`, which is the smallest unit this measure
-- has, and both sides of each reduce -- so the rows below read them at
-- states rather than symbolically, and at each arm of `depthFrame`
-- that charges rather than at whichever one a program hands over.
--
-- THIS IS WHAT THE DECOMPOSITION WAS FOR, and it is the whole reading:
-- the parent's own conclusion is CLOSED to instantiation -- the descent
-- does not return at a state a chain has stepped, for a doubling
-- recorded at `depthShareGo` that no instrument gets past -- while
-- these leaves, carved off the same statement, are numerals.  A green
-- row here is therefore evidence about a region the parent's own rows
-- could never reach.
--
-- THE POINT IS THE CHAIN THE ROUND ADMITS FIRST, reused from
-- `Probed.Depth-Sighted` rather than rebuilt, so these rows stand at
-- the same arrival, schedule and state its own descent figure is
-- pinned at.  `shapeFigs` reports what that path IS -- a `from-inner`
-- head over three frames, at the second tick of source one -- because
-- the head decides which arm of `depthFrame` the frame row exercises,
-- and three of the five arms are flatly nought and could not fail.
-- This one is not: `from-inner` charges the react.
--
-- NON-VACUITY IS PINNED, NOT ASSERTED.  `splitP` is total, and its two
-- degenerate arms hand back a `take-f` whose spend is nought -- a row
-- taken there could not fail.  The tag equation says the arm was not
-- taken: five is the `from-inner` head, and it is read in the same
-- build as the rows.
--
-- WHAT IS NOT COVERED IS ONE LEAF, and the obstruction is not the one
-- the other two had.  `share-fold-fit` is `depthFold` again, so it
-- inherits the parent's own barrier and no instrument reaches it.
-- `share-step-fit` is reached: its `rid` and `p` are a `shareAdmit`
-- entry, and the figures below establish which shares leave one --
-- a share over a source that COMPLETES leaves none, and one over a
-- source that cannot leaves two.
-- TARGET: frame-depth-fit @9d21e7
-- TARGET: chain-fit-step @266bd8
-- TARGET: share-step-fit @81b8f2
module Probed.Depth-Join where

open import Data.Bool using (Bool; false; true)
open import Data.List using (List; _∷_; []; drop)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; suc; _+_; _*_)
open import Data.Nat.Properties using (≤ᵇ⇒≤)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (Gas; hot)
open import Data.Vec using (lookup) renaming ([] to []ⱽ; _∷_ to _∷ⱽ_)
open import Rx.Exp using (Ty; Val; natᵗ; obs; Ctx; Closed; input; ofᵉ; mapᵉ;
  mergeAllᵉ; strmᵗ; nat̂)
open import Rx.Slots using (Slots; scripted; shared)
open import Rx.Evaluator
  using (Sched; Arrival; Path; Frame; root; share-sink; _↠_; map-f; scan-f; take-f; from-inner;
  thru-outer; arrTy; arrVal; budgetAt)

open import Data.List renaming (length to lengthL) using ()
open import Data.Fin using (zero) renaming (suc to fsuc)
open import Rx.Evaluator using (shareAdmit; EvalSt; mergeAllᵒ; RegId; memberSource;
  subscribeE; sched-init; st-init)

open import Refuted.Demand-Programs using (Γ₂; progU; progF; sucGF)
open import Probed.Depth-Sighted
  using (uArr; uPth; uSc; uSt; slotsT; deep; wSched; wSt; after1; slotsF)
open import Probed.Root using (sh₂; S2)
open import Probed.Apparatus using (Confirms)
open import Verify-Budget-Sufficient.Caps-Face.Part7.Arrival-Caps
  using (frame-depth-fit; chain-fit-step; share-step-fit)

-- WHICH FRAME HEADS THE PATH, WHICH IS WHAT DECIDES WHETHER THE ROWS
-- BELOW COULD FAIL.  Three of `depthFrame`'s five arms are flatly
-- nought, so a row at one of them is unfalsifiable however tight it
-- reads; the tag names the arm, and the length says the path is not
-- the empty one.
pathTag : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t → ℕ
pathTag root                   = 0
pathTag (share-sink _)         = 1
pathTag (map-f _ ↠ _)          = 2
pathTag (scan-f _ _ ↠ _)       = 3
pathTag (take-f _ ↠ _)         = 4
pathTag (from-inner _ _ _ ↠ _) = 5
pathTag (thru-outer _ _ ↠ _)   = 6

pathLen : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t → ℕ
pathLen root           = 0
pathLen (share-sink _) = 0
pathLen (_ ↠ p)        = suc (pathLen p)

shapeFigs : ℕ
shapeFigs = pathTag uPth + 10 * pathLen uPth
          + 100 * Arrival.tick uArr + 10000 * Arrival.source uArr

shapeFigs≡ : shapeFigs ≡ 10235
shapeFigs≡ = refl

-- THE EDGE, SPLIT OFF THE PATH THE EVALUATOR BUILT.  The leaves quantify
-- over a frame and the path below it, and the point has to supply both;
-- taking them off `uPth` is what keeps this a reachable edge rather than
-- a pair written down beside a state that never saw them.  The
-- degenerate arms are total fillers, and `shapeFigs` above says which
-- arm is live.
record Split (v : Ty) : Set where
  constructor spl
  field
    {mid} : Ty
    hd    : Frame Γ₂ v mid
    tl    : Path Γ₂ mid natᵗ

splitP : ∀ {v} → Path Γ₂ v natᵗ → Split v
splitP root           = spl (take-f 0) root
splitP (share-sink i) = spl (take-f 0) (share-sink i)
splitP (f ↠ p)        = spl f p

uSpl : Split (arrTy uArr)
uSpl = splitP uPth

uSf : Gas
uSf = budgetAt (progU 8 2) (Sched.slots uSc) 2

uVals : List (Val Γ₂ (arrTy uArr))
uVals = arrVal uArr ∷ []

uFin : Bool
uFin = Arrival.isLast uArr

-- THE FRAME'S OWN SPEND, at the head the tag names.  Both premises are
-- reflexivity at the tightest value each admits -- the slots are the
-- schedule's own and the gas is the budget the descent itself opens
-- with -- so nothing is weakened to make the row stand.
frameRow : Confirms
  (frame-depth-fit (Sched.slots uSc) uSf 2 (Arrival.tick uArr)
     (Split.hd uSpl) (Split.tl uSpl) uVals uFin uSc uSt refl refl)
frameRow = ≤ᵇ⇒≤ _ _ tt

-- AND THAT THE POSITION'S CEILING SURVIVES THE STEP THAT FRAME MAKES,
-- which is the obligation the fold could not discharge for itself and
-- the reason the invariant is the ceiling rather than the store.  The
-- slots conjunct is `refl` and the ceiling conjunct is a comparison
-- between two numerals at states one `stepFrame` apart.
stepRow : Confirms
  (chain-fit-step (Sched.slots uSc) uSf 2 (Arrival.tick uArr)
     (Split.hd uSpl) (Split.tl uSpl) uVals uFin uSc uSt refl refl)
stepRow = refl , ≤ᵇ⇒≤ _ _ tt

-- THE OTHER ARM THAT CHARGES, at a frame this tree already builds.
-- `from-inner` above is one of `depthFrame`'s two live arms and
-- `thru-outer` is the other -- a successor above the react, so the
-- larger of the two -- and the reason no row above reaches it is that
-- the corpus does not head a chain with one.  `Probed.Depth-Sighted`
-- assembles exactly that frame for its own walk rows, so the arm is
-- reachable here by spending its state rather than by finding a
-- program, and the row below is the leaf read at it.
--
-- WHAT THIS ROW IS AND IS NOT.  The frame and its state are ASSEMBLED
-- -- a `mergeAll` node installed over the initial state -- not walked
-- to by a run, so this is evidence about the ARM and not about a
-- position a cascade hands out.  That is the weaker half of what the
-- class wants and the half nothing else supplies: the two rows above
-- stand at a reached edge whose arm cannot fail the way this one can.
-- The nesting is read at two depths so a pass that only survives a
-- flat inner is not one, and the gas is the budget the statement
-- names rather than the pad the walk rows use.
tSf : Gas
tSf = budgetAt (progU 8 2) slotsT 0

thruRow1 : Confirms
  (frame-depth-fit {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 1 ∷ []) false wSched wSt refl refl)
thruRow1 = ≤ᵇ⇒≤ _ _ tt

thruRow4 : Confirms
  (frame-depth-fit {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 4 ∷ []) false wSched wSt refl refl)
thruRow4 = ≤ᵇ⇒≤ _ _ tt

-- AND THE CEILING SURVIVES THAT FRAME'S STEP TOO, which is the second
-- leaf read at the arm the first pair could not reach.
thruStep4 : Confirms
  (chain-fit-step {e = progU 8 2} slotsT tSf 0 0
     (thru-outer mergeAllᵒ 7) (root {Γ = Γ₂} {t = natᵗ})
     (deep 4 ∷ []) false wSched wSt refl refl)
thruStep4 = refl , ≤ᵇ⇒≤ _ _ tt

-- WHETHER THE ROUND OFFERS A REGISTRATION AT ALL, which is what
-- `share-step-fit` wants and what nothing here has been able to
-- supply.  Its `rid` and `p` are exactly a `shareAdmit` entry, so the
-- question is whether the shared slot has any at the point these rows
-- stand at -- a corpus fact, read off the registry rather than
-- guessed, and a nought is a boundary rather than a failure.
admitFig : ℕ
admitFig = lengthL (shareAdmit zero (EvalSt.registry uSt))

admitFig≡ : admitFig ≡ 0
admitFig≡ = refl

-- AND THE POINT IS NOT ONE FAMILY OVER, which is what this figure was
-- written to test and what it refutes.  The round above defers its
-- shared slot behind a capacity-one outer, so a natural reading of the
-- empty admit list is that the slot is merely unspent yet -- and the
-- width family subscribes every inner at the root, the shared one
-- included, so on that reading its registry should carry the entry at
-- the very first arrival.  It does not.  The figure reads the count
-- and the head of the first admitted path together, because a nought
-- count hands the extractor its degenerate filler, and it reports
-- exactly that pair: no entry, and `root` standing in for the path.
--
-- SO THE BOUNDARY IS WIDER THAN A DEFERRED CONNECT, and what makes it
-- so is NOT established here.  Two families whose shared slots are
-- connected in opposite ways agree, which rules out the connect's
-- timing as the whole story and leaves the question at `shareAdmit`'s
-- own guard -- whether a slot subscribed as a program appears in the
-- registry under the source index the admit filters on at all.  That
-- is a reading of the registration path, not another program.
fSt : EvalSt (progF 3 2)
fSt = proj₂ (after1 (progF 3 2) slotsF (sucGF 1 2 2 3 2))

-- THE FILLER IS A PARAMETER, and that is forced rather than tidy: a
-- type-changing path has no `root`, so the obs-typed admit below could
-- not reuse a fixed one.  Passing it keeps the tag of the empty case
-- under the caller's control, which is what lets a nought count be
-- told apart from a real head at the same figure.
record Adm {n} (Γ : Ctx n) (v t : Ty) : Set where
  constructor adm
  field
    rid : RegId
    pth : Path Γ v t

firstAdm : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t
         → List (RegId × Path Γ v t) → Adm Γ v t
firstAdm fill []            = adm 0 fill
firstAdm _    ((r , p) ∷ _) = adm r p

fAdm : Adm Γ₂ natᵗ natᵗ
fAdm = firstAdm root (shareAdmit zero (EvalSt.registry fSt))

admFig : ℕ
admFig = lengthL (shareAdmit zero (EvalSt.registry fSt))
       + 10 * suc (pathTag (Adm.pth fAdm))

admFig≡ : admFig ≡ 10
admFig≡ = refl

-- AND WHAT EMPTIES IT IS THE DEF, WHICH IS NEITHER OF THE TWO THINGS
-- THE WRAPPER CONTROLS.  Reading the admit list alone cannot separate
-- three ways of arriving at a nought -- the slot was never connected
-- because the fuel ran dry at the edge, the slot connected and the
-- entry is simply not admitted, or the entry was written and then
-- taken back -- and only the last of those says anything about the
-- statement's index.  The figure reads the whole registry beside the
-- two latches the connect sets, so one run decides among them: the
-- units are the registrations standing at that point -- the width
-- family subscribes its scripted slot once per copy, so that digit is
-- not a nought and the flags are carried clear of it -- the thousands
-- say whether source nought has completed, the ten-thousands whether
-- it ever connected at all.
--
-- IT IS THE THIRD, AND THAT NAMES THE OBSTRUCTION.  The slot connects
-- and completes in the same call, because `sharedConnect` subscribes
-- the def and asks whether the burst it got back completed -- and the
-- def here is built from one-shots under a scan, so it exhausts inside
-- its own connect burst and the branch that latches it drops every
-- registration on that source before returning.  The registration IS
-- written; it does not survive the call that writes it.  So the
-- emptiness is a property of the DEF being synchronous, which both
-- families share and neither wrapper alters -- which is why connecting
-- eagerly and connecting late agreed.  `Probed.Root` had already read
-- the general fact off a one-shot def; what the flags add is that this
-- corpus reaches it by the connect-and-latch route rather than by a
-- fuel that ran dry before the edge, which is the reading that would
-- have pointed at the gas instead of at the program.
--
-- SO WHAT `share-step-fit` WANTS IS A SHARE WHOSE DEF OUTLIVES ITS OWN
-- CONNECT, and the telescope invariant is what puts that out of this
-- corpus's reach rather than out of reach: a slot's def may reference
-- only STRICTLY EARLIER slots, so a nought-indexed share can name no
-- scripted source at all and every def available to it is sync by
-- construction.  A share at a LATER index over a scripted slot below
-- it is the shape that clears this, and `Probed.Root` builds one -- a
-- share over an empty hot, which never fires and so never completes,
-- whose registrations are pinned there as still standing at the root
-- exit.  The row is unpointed by THIS corpus and not by its own index,
-- and the point it wants already exists one module over.
b2n : Bool → ℕ
b2n false = 0
b2n true  = 1

regFig : ℕ
regFig = lengthL (EvalSt.registry fSt)
       + 1000 * b2n (memberSource 0 (EvalSt.completedSources fSt))
       + 10000 * b2n (memberSource 0 (EvalSt.connectedShares fSt))

regFig≡ : regFig ≡ 11004
regFig≡ = refl

-- AND HERE IS THAT SHARE, SPENT.  `Probed.Root` assembles a slot pair
-- whose upper member is a share over an empty hot -- a source that
-- never fires and so never completes -- and its root subscribe leaves
-- the share's own registrations standing, which is the one thing the
-- corpus above cannot produce.  Reading the admit list there gives
-- `share-step-fit` the `rid` and `p` it quantifies over, at the state
-- and schedule the same run returns, so the row below is the leaf read
-- at a registration the evaluator actually wrote rather than at a pair
-- put beside a state that never held them.
--
-- NON-VACUITY IS PINNED THE SAME WAY THE ADMIT NOUGHTS WERE.  A nought
-- count would hand the extractor its `root` filler and the row would
-- stand at a degenerate path, which is exactly the failure the two
-- figures above were written to detect; `admShare` reports the count
-- beside the head's arm so a fallback cannot pass for a point.
rTri : _
rTri = subscribeE (budgetAt S2 sh₂ 0) S2 root 0 0
                  (sched-init S2 sh₂) (st-init S2)

rSc : Sched Γ₂
rSc = proj₁ (proj₂ rTri)

rSt : EvalSt S2
rSt = proj₂ (proj₂ rTri)

rAdms : List (RegId × Path Γ₂ natᵗ natᵗ)
rAdms = shareAdmit (fsuc zero) (EvalSt.registry rSt)

rAdm : Adm Γ₂ natᵗ natᵗ
rAdm = firstAdm root rAdms

admShare : ℕ
admShare = lengthL rAdms + 10 * suc (pathTag (Adm.pth rAdm))

admShare≡ : admShare ≡ 62
admShare≡ = refl

rSf : Gas
rSf = budgetAt S2 sh₂ 0

shareStepRow : Confirms
  (share-step-fit sh₂ rSf 8 0 0 (fsuc zero)
     (3 ∷ []) false (Adm.rid rAdm) (Adm.pth rAdm) rSc rSt refl refl)
shareStepRow = refl , ≤ᵇ⇒≤ _ _ tt

-- AND AT THE OTHER REGISTRATION, AND AT THE CLOSING DELIVERY.  One
-- point is a foothold rather than coverage, and the two axes worth
-- moving first are the ones the statement itself branches on.  The
-- share carries TWO admitted entries -- both inners of the root
-- mergeAll subscribe the same slot -- so the second is a different
-- `rid` at the same arm, which is what says the row is not standing on
-- whichever entry happened to be first.  And `fin` is a genuine branch
-- in the statement rather than a parameter: at `true` the fold is
-- handed a close emit to carry and at `false` an empty list, so a pass
-- at one says nothing about the other.
rAdm2 : Adm Γ₂ natᵗ natᵗ
rAdm2 = firstAdm root (drop 1 rAdms)

-- the second entry is a DIFFERENT registration at the same arm, which
-- is what makes the row below more than a restatement of the one above
admPair : ℕ
admPair = lengthL (drop 1 rAdms) + 10 * suc (pathTag (Adm.pth rAdm2))

admPair≡ : admPair ≡ 61
admPair≡ = refl

shareStepRow2 : Confirms
  (share-step-fit sh₂ rSf 8 0 0 (fsuc zero)
     (3 ∷ []) false (Adm.rid rAdm2) (Adm.pth rAdm2) rSc rSt refl refl)
shareStepRow2 = refl , ≤ᵇ⇒≤ _ _ tt

shareStepFin : Confirms
  (share-step-fit sh₂ rSf 8 0 0 (fsuc zero)
     (3 ∷ []) true (Adm.rid rAdm) (Adm.pth rAdm) rSc rSt refl refl)
shareStepFin = refl , ≤ᵇ⇒≤ _ _ tt

----------------------------------------------------------------------
-- THE `thru-outer` ARM, WHICH THE ROWS ABOVE COULD NOT REACH.  Every
-- registration a share admits at `S2` is `from-inner` headed, because
-- the share is subscribed as an INNER of the root fan.  A `thru-outer`
-- head is written by `subscribeAll`, which subscribes its OUTER under
-- one -- so the share has to BE the outer, and an outer is typed
-- `obs u`.  The slot must therefore carry an observable type, and
-- `Rx.Slots` permits exactly one way to do that: `scripted` is barred
-- at a non-data type (its script could emit the program being walked),
-- while `shared` is walked and so may carry one.  That is not a
-- restriction to work around -- it is the shape the arm needs anyway,
-- since only a shared slot has an admit list at all.
----------------------------------------------------------------------

Γₒ : Ctx 2
Γₒ = natᵗ ∷ⱽ obs natᵗ ∷ⱽ []ⱽ

-- slot 0 is a hot that never fires and never completes, which is what
-- keeps the registration alive past its own connect: a def that
-- completes synchronously has its registration dropped inside
-- `sharedConnect`, which is what `regFig` pinned above.  The def lifts
-- that silence to `obs natᵗ` rather than sourcing anything itself, so
-- the telescope is satisfied by index alone.
shₒ : Slots Γₒ
shₒ zero              = scripted {ok = tt} (hot [])
shₒ (fsuc zero)       = shared (mapᵉ (strmᵗ (ofᵉ [])) (input zero)) {ok = tt}
shₒ (fsuc (fsuc ()))

Sₒ : Closed Γₒ natᵗ
Sₒ = mergeAllᵉ nothing (input (fsuc zero))

oTri : _
oTri = subscribeE (budgetAt Sₒ shₒ 0) Sₒ root 0 0
                  (sched-init Sₒ shₒ) (st-init Sₒ)

oSc : Sched Γₒ
oSc = proj₁ (proj₂ oTri)

oSt : EvalSt Sₒ
oSt = proj₂ (proj₂ oTri)

oAdms : List (RegId × Path Γₒ (obs natᵗ) natᵗ)
oAdms = shareAdmit (fsuc zero) (EvalSt.registry oSt)

-- the filler is `share-sink`, tag 1, and NOT a `thru-outer` of its
-- own: an empty list must not read as the arm being reached, which is
-- the whole job this figure does.
oAdm : Adm Γₒ (obs natᵗ) natᵗ
oAdm = firstAdm (share-sink (fsuc zero)) oAdms

admOuter : ℕ
admOuter = lengthL oAdms + 10 * suc (pathTag (Adm.pth oAdm))

admOuter≡ : admOuter ≡ 71
admOuter≡ = refl

-- the delivered value is an OBSERVABLE, since that is what the arm
-- consumes: `thru-outer` subscribes its payload and grafts the burst.
-- A one-element cold rather than an empty one, so the subscribe it
-- provokes actually carries something.
oVals : List (Val Γₒ (lookup Γₒ (fsuc zero)))
oVals = ofᵉ (nat̂ 7 ∷ []) ∷ []

oSf : Gas
oSf = budgetAt Sₒ shₒ 0

shareStepOuter : Confirms
  (share-step-fit shₒ oSf 8 0 0 (fsuc zero)
     oVals false (Adm.rid oAdm) (Adm.pth oAdm) oSc oSt refl refl)
shareStepOuter = refl , ≤ᵇ⇒≤ _ _ tt

shareStepOuterFin : Confirms
  (share-step-fit shₒ oSf 8 0 0 (fsuc zero)
     oVals true (Adm.rid oAdm) (Adm.pth oAdm) oSc oSt refl refl)
shareStepOuterFin = refl , ≤ᵇ⇒≤ _ _ tt

-- WHERE THE CHAIN SINKS, WHICH IS THE OTHER AXIS AND THE RISKIER ONE.
-- `foldPath` ends a chain either at `root` -- pure, returning the
-- schedule and store it was handed -- or at `share-sink`, which
-- re-enters `dispatchShare` and fans the same values out to every
-- chain of a LATER share.  Only the second can move the store, so a
-- row that ends at `root` has exercised the frame and not the
-- recursion.  Pinned rather than read off the program shape.
pathEnd : ∀ {n} {Γ : Ctx n} {v t} → Path Γ v t → ℕ
pathEnd root           = 0
pathEnd (share-sink _) = 1
pathEnd (_ ↠ p)        = pathEnd p

endFig : ℕ
endFig = pathEnd (Adm.pth rAdm) + 10 * pathEnd (Adm.pth rAdm2)
       + 100 * pathEnd (Adm.pth oAdm)

endFig≡ : endFig ≡ 0
endFig≡ = refl

----------------------------------------------------------------------
-- SO REACH IT: A SHARE REGISTERED ON A LATER SHARE.  The telescope
-- allows slot 2's def to name input 1, and a shared def subscribing
-- another share registers with `share-sink` as its tail rather than
-- `root` -- so one more slot puts a `thru-outer` head and the
-- recursive tail on the SAME chain, which is the region both previous
-- families miss.  Slot 1's def still never completes, which is what
-- keeps both registrations standing past their connects.
----------------------------------------------------------------------

Γₜ : Ctx 3
Γₜ = natᵗ ∷ⱽ obs natᵗ ∷ⱽ natᵗ ∷ⱽ []ⱽ

shₜ : Slots Γₜ
shₜ zero                     = scripted {ok = tt} (hot [])
shₜ (fsuc zero)              = shared (mapᵉ (strmᵗ (ofᵉ [])) (input zero)) {ok = tt}
shₜ (fsuc (fsuc zero))       = shared (mergeAllᵉ nothing (input (fsuc zero))) {ok = tt}
shₜ (fsuc (fsuc (fsuc ())))

Sₜ : Closed Γₜ natᵗ
Sₜ = input (fsuc (fsuc zero))

tTri : _
tTri = subscribeE (budgetAt Sₜ shₜ 0) Sₜ root 0 0
                  (sched-init Sₜ shₜ) (st-init Sₜ)

tSc : Sched Γₜ
tSc = proj₁ (proj₂ tTri)

tSt : EvalSt Sₜ
tSt = proj₂ (proj₂ tTri)

tAdms : List (RegId × Path Γₜ (obs natᵗ) natᵗ)
tAdms = shareAdmit (fsuc zero) (EvalSt.registry tSt)

tAdm : Adm Γₜ (obs natᵗ) natᵗ
tAdm = firstAdm (share-sink (fsuc zero)) tAdms

-- length, head arm and tail in one numeral: one entry, `thru-outer`
-- headed, sinking into a share and not the root.  The filler shares
-- the tail digit, so the count is what separates it from a real hit.
outerSink : ℕ
outerSink = lengthL tAdms + 10 * suc (pathTag (Adm.pth tAdm))
          + 1000 * pathEnd (Adm.pth tAdm)

outerSink≡ : outerSink ≡ 1071
outerSink≡ = refl

tVals : List (Val Γₜ (lookup Γₜ (fsuc zero)))
tVals = ofᵉ (nat̂ 7 ∷ []) ∷ []

kSf : Gas
kSf = budgetAt Sₜ shₜ 0

shareStepSink : Confirms
  (share-step-fit shₜ kSf 8 0 0 (fsuc zero)
     tVals false (Adm.rid tAdm) (Adm.pth tAdm) tSc tSt refl refl)
shareStepSink = refl , ≤ᵇ⇒≤ _ _ tt

shareStepSinkFin : Confirms
  (share-step-fit shₜ kSf 8 0 0 (fsuc zero)
     tVals true (Adm.rid tAdm) (Adm.pth tAdm) tSc tSt refl refl)
shareStepSinkFin = refl , ≤ᵇ⇒≤ _ _ tt
