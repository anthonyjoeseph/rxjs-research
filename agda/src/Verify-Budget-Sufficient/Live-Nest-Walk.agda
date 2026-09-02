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

open import Data.Bool using (Bool; true; false; _∧_; if_then_else_)
open import Data.Bool.ListAction using (any)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_; foldr)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using (≤-trans; ⊔-lub; m≤m⊔n; m≤n⊔m; m≤m+n; ≤-reflexive; +-suc)
open import Data.Vec using (lookup)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; sym; subst)

open import Rx.Prim using (Gas; Id; Tick; Source; InstEvent; close; exhausted)
open import Rx.Exp using (Ctx; Closed; Val)
open import Rx.Evaluator
  using (Sched; EvalSt; Frame; Path; root; share-sink; _↠_; RegId;
         map-f; scan-f; take-f; from-inner; thru-outer;
         iterSize; foldPath; stepFrame; dispatchShare;
         shareGo; shareAdmit; shareLatch)
open import Verify-Budget-Sufficient.Keeps-Ring using (KeepsC; stepFrame-keeps)
open import Verify-Budget-Sufficient.Measures using (pathLen; ∧-true)
open import Verify-Budget-Sufficient.Nest-Store
  using (liveNest; slotsNestSum; regsNestMax; sweepLive-nest)
open import Verify-Budget-Sufficient.Caps using (iterSize-infl; iterSize-mono-count)
open import Verify-Budget-Sufficient.Regs-Nest-Walk
  using (valsΦ?; FrameΦHyp; PathΦHyp; DispatchΦHyp; ShareGoΦHyp; valsSz?; valsSz?-mono;
         stepFrame-nest-Φ; stepFrame-nest-regs; stepFrame-regsSz; stepFrame-sz;
         foldPath-nest-regs)
open import Verify-Budget-Sufficient.Caps-Face.Part1
  using (pathSz?; regsSz?; frameSz?; pathSz?-widen)
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

postulate
  -- ONE FRAME'S MINTS.  Four kinds mint nothing at all; the outer
  -- frame subscribes what it is handed, and a deferred body's depth is
  -- under its size, which is the bound the side condition supplies.
  --
  -- AND A THIRD MINT SITE IS WHY THE WALK'S OWN PREMISES DO NOT
  -- SUFFICE.  A completion frame subscribes out of the *All node's
  -- QUEUE, and a queued gate mints a live carrying its body -- so the
  -- arm that mints there is the arm the side condition reads as a
  -- unit, and the walk reaching it is empty-handed by construction,
  -- which clears the potential at every budget including the smallest.
  -- The slot sum does not move with a term the slots never held.
  --
  -- AND NO LARGER NUMBER WOULD HAVE REPAIRED IT, WHICH IS WHAT FIXES
  -- THE GRANT'S CURRENCY.  The depth measure TRUNCATES at the gate --
  -- that is what makes a recursive body safe -- so a parked term reads
  -- zero in the conclusion's own currency while the live it mints
  -- reads the body.  A premise bounding the queue's NESTING is
  -- therefore satisfied by the counterexample unchanged.  A SIZE sees
  -- past the gate, one unit per layer, and the frame grant is
  -- denominated in exactly that.
  --
  -- SO THE FRAME GRANT IS CARRIED, AND IT IS THE SAME ONE THE REGISTRY
  -- ARM TAKES.  That arm fell to the same emptiness at the same frame
  -- and was repaired this way, and its drain conjunct names the node
  -- by a `lookupNode` equation, so the queued terms are under a
  -- cap-derived size rather than under anything the walk holds.  Two
  -- faces discharged from ONE fit is what makes the repair worth
  -- taking over a grant minted here: a producer that can supply the
  -- registry arm supplies this one with the same witness, and the
  -- consumers already thread it alongside.
  --
  -- REFUTED: `Refuted.Drain-Live-Defer`, at the corner two earlier
  --   findings leave open: `Refuted.Chain-Step-Live-Nest` found the
  --   gate's mint and its repair is the arrival grant this statement
  --   now carries, `Refuted.Drain-Regs-Nest` found the drain arm
  --   reading a payload no walk handed it -- on the registry axis,
  --   where the same emptiness clears the same premise.
  -- PROBED: `Probed.Chain-Step-Live-Deferred` reaches this leaf by
  --   RUNNING a whole chain over it, at the one program shape that can
  --   move the fold: a `mapᵉ` over the async input handing the outer
  --   *All a deferred nest per arrival, so the chain the evaluator
  --   presents subscribes it and the live it mints carries the body.
  --   Covered: the fold rising 0 to 1 and 0 to 3 as the nest deepens,
  --   against a syntactic charge of eighteen and twenty-six that the
  --   tree proves the size cap dominates -- so both sides move and the
  --   ordering is load-bearing on the depth axis.  Not covered: one
  --   frame in isolation, since the rows read the composite; and a
  --   fold already nonzero at entry, where the growth would compound
  --   rather than start from zero.
  --   AND THE COMPLETION ARM IS NOT REACHED BY THAT PROGRAM AT ALL,
  --   which is a bound on the harness rather than on the sweep: its
  --   outer *All is unlimited, so room is never refused and the queue
  --   the drain subscribes out of stays empty on every row.  Bounding
  --   the limit is not enough to fix it either -- a queue fills only
  --   while an earlier inner is still ACTIVE, and every inner this
  --   family builds completes inside its own subscribe burst, so the
  --   count is back at zero before the next arrival is read.  Reaching
  --   the arm therefore needs a program whose map produces TWO KINDS of
  --   inner off the arriving value: one that outlives its burst to hold
  --   the slot, and the deferred nest that queues behind it.  That is a
  --   new program family and not a parameter of this one.
  stepFrame-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u}
    (sf : Gas) (id : Id) (now : Tick) (f : Frame Γ s u) (path : Path Γ u t)
    (vals : List (Val Γ s)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
    (B U : ℕ) →
    valsΦ? B U (f ↠ path) vals ≡ true →
    FrameΦHyp sf id now B U f path vals fin sched st →
    FrameLiveHyp U f path vals →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live
        (proj₁ (proj₂ (proj₂ (proj₂ (stepFrame sf id now f path vals fin sched st))))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched) ⊔ U

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

-- THE REGISTRY-SIDE GRANT, and it is the one thing the walk cannot get
-- from the path it is walking.  At a sink the values leave this chain
-- for chains that live in the REGISTRY, and their side conditions are
-- owed at their own paths -- so what has to be supplied is a reading of
-- the registry, not another reading of this path.
--
-- IT CARRIES THE WALK'S OWN AFFORDABILITY BECAUSE BOTH CHEAPER FORMS
-- ARE FALSE.  Priced at one number for the values entering the sink
-- and another for the registry's chains, with nothing between them, it
-- falls to a single `map-f`: legality bounds a chain's SYNTAX and the
-- conclusion bounds the VALUES that syntax produces, so what is
-- missing is a RELATION between the two numbers rather than a bigger
-- one.  Related, but read at the level the walk STANDS at, it falls
-- again -- a fanned-into chain climbs from there by its own length,
-- and that length is bounded by the registry's reading rather than by
-- anything the caller can offer.  The two ranges then cross at the
-- smallest cap the invariant admits, so no ceiling is choosable.
--
-- SO THE LEVEL LEDGER IS THE CAPS FACE'S RATHER THAN THIS ARM'S OWN,
-- and that needs no further counterexample.  A FLAT ceiling fails on
-- its own reading: the hop asks for the entry level plus the size
-- reading there, so taking the entry level to BE the ceiling asks past
-- it at once.  What absorbs an exponential climb is a ledger indexed
-- by remaining nesting depth, and the caps face already carries one --
-- `chainStep-caps` proves its climb survives a fan-out, and it is paid
-- out of the instant's fuel rather than out of the cap.
--
-- AND THAT LEDGER IS UNAFFORDABLE HERE, SO WHAT MOVES IS THE MECHANISM
-- AND NOT THE NUMBER.  Reading the affordability ONCE, at the top of
-- that ledger, is the only form the counterexamples leave standing,
-- and the walked ceiling does not reach it: a ladder that at least
-- exponentiates per rung cannot be closed under a ceiling that is one
-- exponential, however the arithmetic is arranged, and no hypothesis
-- available at this hop changes which of the two towers.  What is left
-- standing is a receipt that SHRINKS along the path and names no level
-- at all -- the shape the potential face already carries -- so this arm
-- is owed a different CURRENCY rather than a larger number in the one
-- it has.
--
-- REFUTED: `Refuted.Share-Live-Afford`, `Refuted.Share-Live-Level`
-- REFUTED: `Refuted.Sink-Level-Range`
-- DEAD ROUTE: picking the level ceiling at a caller and restating
--   this hop downward.  Every caller's ceiling is capped by what
--   `iterSize≤walkFac` affords, and one hop asks past it at every cap.
-- DEAD ROUTE: reading the affordability once at the caps face's top
--   level instead, which is what the three counterexamples leave.
--   `sizeCount` iterates `lvls`, and `exp-lvls` puts each rung above
--   two to the one below, so the count towers with the deliveries;
--   `nestWalkAt` is a single exponential of a cap cubed, and
--   `iterSize-2^` doubles per fold -- so the walked side is past the
--   ceiling by the ladder's second rung.
postulate
  walk-share-LiveHyp : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (S U Lv j : ℕ) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (sched : Sched Γ) (st : EvalSt e) →
    iterSize S Lv S ≤ U →
    1 ≤ S →
    valsSz? (iterSize S j S) vals ≡ true →
    regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
    j ≤ Lv →
    DispatchLiveHyp sf gas id now U i vals fin sched st

-- THE SIZE SIDE CONDITION, DISCHARGED BY THE SAME WALK IT GUARDS.  The
-- values a frame sees are the ones the frames above it produced, so
-- the bound has to step: it is read at the LEVEL the walk has reached
-- rather than at one number, and each frame moves the level by one.
--
-- AND THE LEVEL BUDGET IS A PARAMETER, NOT THE SIZE CAP.  Reading it as
-- the cap is exactly right for ONE chain entered at level zero -- a
-- path legal under the cap has at most a cap's worth of frames -- and
-- it is wrong the moment a caller walks a second chain, because the
-- level it enters at is whatever the first chain left.  A selection of
-- `W` chains reaches a level on the order of `W` caps, so a budget
-- pinned to the cap is unsatisfiable there however the arithmetic is
-- arranged, and the affordability the caller owes is the one thing
-- that has to widen with it.  Keeping the two apart is what lets one
-- statement serve both: `Lv := S` recovers the single-chain reading.
walk-LiveHyp-go : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u}
  (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (S U Lv j : ℕ) (path : Path Γ u t)
  (vals : List (Val Γ u)) (fin : Bool) (sched : Sched Γ) (st : EvalSt e) →
  iterSize S Lv S ≤ U →
  1 ≤ S →
  valsSz? (iterSize S j S) vals ≡ true →
  pathSz? S path ≡ true →
  regsSz? (iterSize S j S) (EvalSt.registry st) ≡ true →
  j + pathLen path ≤ Lv →
  PathLiveHyp sf gas id now U path vals fin sched st
walk-LiveHyp-go sf gas id now S U Lv j root vals fin sched st _ _ _ _ _ _ = tt
walk-LiveHyp-go sf gas id now S U Lv j (share-sink i) vals fin sched st afford 1≤S hsz _ hreg hj =
  walk-share-LiveHyp sf gas id now S U Lv j i vals fin sched st
    afford 1≤S hsz hreg j≤Lv
  where
  j≤Lv : j ≤ Lv
  j≤Lv = ≤-trans (m≤m+n j 0) hj
walk-LiveHyp-go sf gas id now S U Lv j (f ↠ p) vals fin sched st afford 1≤S hsz hpz hreg hj =
    hHead
  , walk-LiveHyp-go sf gas id now S U Lv (suc j) p
      (proj₁ step)
      (proj₁ (proj₂ (proj₂ step)))
      (proj₁ (proj₂ (proj₂ (proj₂ step))))
      (proj₂ (proj₂ (proj₂ (proj₂ step))))
      afford
      1≤S
      (stepFrame-sz sf id now f p vals fin sched st S j hfz hsz)
      hpTail
      (stepFrame-regsSz sf id now f p vals fin sched st S j hsz
         (pathSz?-widen (f ↠ p) (iterSize-infl S 1≤S j S) hpz) hreg)
      (≤-trans (≤-reflexive (sym (+-suc j (pathLen p)))) hj)
  where
  step = stepFrame sf id now f p vals fin sched st
  j≤Lv : j ≤ Lv
  j≤Lv = ≤-trans (m≤m+n j (pathLen (f ↠ p))) hj
  atU : valsSz? U vals ≡ true
  atU = valsSz?-mono (iterSize S j S) U vals
          (≤-trans (iterSize-mono-count S S 1≤S j≤Lv) afford) hsz
  hHead : FrameLiveHyp U f p vals
  hHead = frameLive-of-sz U f p vals atU
  hfz : frameSz? S f ≡ true
  hfz = proj₁ (∧-true (frameSz? S f)
                 ((suc (pathLen p) ≤ᵇ S) ∧ pathSz? S p) hpz)
  hpTail : pathSz? S p ≡ true
  hpTail = proj₂ (∧-true (suc (pathLen p) ≤ᵇ S) (pathSz? S p)
                    (proj₂ (∧-true (frameSz? S f)
                             ((suc (pathLen p) ≤ᵇ S) ∧ pathSz? S p) hpz)))

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
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    valsΦ? B U path vals ≡ true →
    PathΦHyp sf gas id now B U path vals fin sched st →
    PathLiveHyp sf gas id now U path vals fin sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (foldPath sf gas id now envSrc path vals evs fin sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  foldPath-nest-live sf gas id now envSrc root vals evs fin sched st B U hΦ _ _ =
    ≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                            (slotsNestSum (Sched.slots sched)))
                     (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
            (m≤m⊔n _ U)
  foldPath-nest-live sf gas id now envSrc (share-sink i) vals evs fin sched st B U hΦ hD hDL =
    dispatchShare-nest-live sf gas id now i vals fin sched st B U hD hDL
  foldPath-nest-live sf gas id now envSrc (f ↠ p) vals evs fin sched st B U hΦ (hF , hR) (hL , hLR) =
    ≤-trans (foldPath-nest-live sf gas id now envSrc p
               (proj₁ step) (evs ++ proj₁ (proj₂ step))
               (proj₁ (proj₂ (proj₂ step)))
               (proj₁ (proj₂ (proj₂ (proj₂ step))))
               (proj₂ (proj₂ (proj₂ (proj₂ step)))) B U
               (stepFrame-nest-Φ sf id now f p vals fin sched st B U hΦ hF) hR hLR)
            (⊔-lub (⊔-lub (⊔-lub liveStep slotStep) regStep) (m≤n⊔m (L ⊔ S ⊔ R) U))
    where
    step = stepFrame sf id now f p vals fin sched st
    L = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    S = slotsNestSum (Sched.slots sched)
    R = regsNestMax (EvalSt.registry st)
    intoL : L ≤ L ⊔ S ⊔ R ⊔ U
    intoL = ≤-trans (≤-trans (m≤m⊔n L S) (m≤m⊔n (L ⊔ S) R)) (m≤m⊔n (L ⊔ S ⊔ R) U)
    intoS : S ≤ L ⊔ S ⊔ R ⊔ U
    intoS = ≤-trans (≤-trans (m≤n⊔m L S) (m≤m⊔n (L ⊔ S) R)) (m≤m⊔n (L ⊔ S ⊔ R) U)
    intoR : R ≤ L ⊔ S ⊔ R ⊔ U
    intoR = ≤-trans (m≤n⊔m (L ⊔ S) R) (m≤m⊔n (L ⊔ S ⊔ R) U)
    intoU : U ≤ L ⊔ S ⊔ R ⊔ U
    intoU = m≤n⊔m (L ⊔ S ⊔ R) U
    liveStep : foldr (λ l acc → liveNest l ⊔ acc) 0
                 (Sched.live (proj₁ (proj₂ (proj₂ (proj₂ step)))))
                 ≤ L ⊔ S ⊔ R ⊔ U
    liveStep =
      ≤-trans (stepFrame-nest-live sf id now f p vals fin sched st B U hΦ hF hL)
              (⊔-lub (⊔-lub intoL intoS) intoU)
    slotStep : slotsNestSum (Sched.slots (proj₁ (proj₂ (proj₂ (proj₂ step)))))
                 ≤ L ⊔ S ⊔ R ⊔ U
    slotStep =
      subst (_≤ L ⊔ S ⊔ R ⊔ U)
            (cong slotsNestSum
              (sym (KeepsC.slotsEq (stepFrame-keeps sf id now f p vals fin sched st))))
            intoS
    regStep : regsNestMax (EvalSt.registry (proj₂ (proj₂ (proj₂ (proj₂ step)))))
                ≤ L ⊔ S ⊔ R ⊔ U
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
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    DispatchΦHyp sf gas id now B U i vals fin sched st →
    DispatchLiveHyp sf gas id now U i vals fin sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (dispatchShare {t = t} sf gas id now i vals fin sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  dispatchShare-nest-live sf zero id now i vals fin sched st B U _ _ =
    ≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                            (slotsNestSum (Sched.slots sched)))
                     (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
            (m≤m⊔n _ U)
  dispatchShare-nest-live sf (suc gas) id now i vals false sched st B U hS hSL =
    shareGo-nest-live sf gas id now i vals false
      (shareAdmit i (EvalSt.registry st)) sched st B U hS hSL
  dispatchShare-nest-live {t = t} sf (suc gas) id now i vals true sched st B U hS hSL =
    ≤-trans (sweepLive-nest _
              (Sched.live (proj₁ (proj₂ (shareGo {t = t} sf gas id now i vals true
                (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st))))))
            (shareGo-nest-live sf gas id now i vals true
              (shareAdmit i (EvalSt.registry st)) sched (shareLatch i true st) B U hS hSL)

  -- ONE ADMITTED REGISTRATION AT A TIME, and all three components
  -- telescope: the live list under the one the chain entered on, the
  -- slots unmoved because no chain ever rewrites them, and the registry
  -- under the registry arm's own walk theorem.
  shareGo-nest-live : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (sf : Gas) (gas : ℕ) (id : Id) (now : Tick) (i : Fin n)
    (vals : List (Val Γ (lookup Γ i))) (fin : Bool)
    (ps : List (RegId × Path Γ (lookup Γ i) t))
    (sched : Sched Γ) (st : EvalSt e) (B U : ℕ) →
    ShareGoΦHyp sf gas id now B U i vals fin ps sched st →
    ShareGoLiveHyp sf gas id now U i vals fin ps sched st →
    foldr (λ l acc → liveNest l ⊔ acc) 0
      (Sched.live (proj₁ (proj₂ (shareGo sf gas id now i vals fin ps sched st))))
      ≤ foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
          ⊔ slotsNestSum (Sched.slots sched)
          ⊔ regsNestMax (EvalSt.registry st) ⊔ U
  shareGo-nest-live sf gas id now i vals fin [] sched st B U _ _ =
    ≤-trans (≤-trans (m≤m⊔n (foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched))
                            (slotsNestSum (Sched.slots sched)))
                     (m≤m⊔n _ (regsNestMax (EvalSt.registry st))))
            (m≤m⊔n _ U)
  shareGo-nest-live sf gas id now i vals fin ((rid , p) ∷ ps) sched st B U hS hSL
    with any (_≡ᵇ rid) (EvalSt.cancelled st)
  ... | true  = shareGo-nest-live sf gas id now i vals fin ps sched st B U hS hSL
  ... | false =
    ≤-trans (shareGo-nest-live sf gas id now i vals fin ps
               (proj₁ (proj₂ FP)) (proj₂ (proj₂ FP)) B U
               (proj₂ (proj₂ hS)) (proj₂ hSL))
            (⊔-lub (⊔-lub (⊔-lub headLive headSlots) headRegs)
                   (m≤n⊔m (L ⊔ S ⊔ R) U))
    where
    st₀ = record st { delivered = rid ∷ EvalSt.delivered st }
    EVS = if fin then close (toℕ i) exhausted ∷ [] else []
    FP  = foldPath sf gas id now (toℕ i) p vals EVS fin sched st₀
    L = foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live sched)
    S = slotsNestSum (Sched.slots sched)
    R = regsNestMax (EvalSt.registry st)
    intoS : S ≤ L ⊔ S ⊔ R ⊔ U
    intoS = ≤-trans (≤-trans (m≤n⊔m L S) (m≤m⊔n (L ⊔ S) R)) (m≤m⊔n (L ⊔ S ⊔ R) U)
    intoR : R ≤ L ⊔ S ⊔ R ⊔ U
    intoR = ≤-trans (m≤n⊔m (L ⊔ S) R) (m≤m⊔n (L ⊔ S ⊔ R) U)
    intoU : U ≤ L ⊔ S ⊔ R ⊔ U
    intoU = m≤n⊔m (L ⊔ S ⊔ R) U
    headLive : foldr (λ l acc → liveNest l ⊔ acc) 0 (Sched.live (proj₁ (proj₂ FP)))
                 ≤ L ⊔ S ⊔ R ⊔ U
    headLive = foldPath-nest-live sf gas id now (toℕ i) p vals EVS fin sched st₀ B U
                 (proj₁ hS) (proj₁ (proj₂ hS)) (proj₁ hSL)
    headSlots : slotsNestSum (Sched.slots (proj₁ (proj₂ FP))) ≤ L ⊔ S ⊔ R ⊔ U
    headSlots =
      subst (_≤ L ⊔ S ⊔ R ⊔ U)
            (cong slotsNestSum
              (sym (foldPath-slots sf gas id now (toℕ i) p vals EVS fin sched st₀)))
            intoS
    headRegs : regsNestMax (EvalSt.registry (proj₂ (proj₂ FP))) ≤ L ⊔ S ⊔ R ⊔ U
    headRegs =
      ≤-trans (foldPath-nest-regs sf gas id now (toℕ i) p vals EVS fin sched st₀ B U
                 (proj₁ hS) (proj₁ (proj₂ hS)))
              (⊔-lub intoR intoU)
