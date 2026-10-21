{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A FLATMAP'S LANES: a lane's rise, its end, the queue refilled.
module adequacy.Climbs.Lanes where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-assoc; ++-conicalˡ; ++-conicalʳ; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (suc; pred)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Placed.Order using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Gapped using (module Gapping)
open import adequacy.Lift using (module Lifting)
open import adequacy.Lift.Order using (module LiftingOrder)
open import adequacy.Lowers using (module Lowering)
open import adequacy.Frame using (module Framing)
open import adequacy.Frame.Repool using (module FramingRepool)
open import adequacy.Grow using (module Growing)
open import adequacy.Fork using (module Forking)
open import adequacy.Taken using (module Taking)
open import adequacy.Names using (module Naming)
open import adequacy.Local using (module Locality)
open import adequacy.Retag using (module Retagging)
open import adequacy.Replant using (module Replanting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Weaken.Heaps using (module WeakeningHeaps)
open import adequacy.Every using (module Everywhere)
open import adequacy.Every.Gating using (module EverywhereGated)
open import adequacy.Alike using (module Aliking)
open import adequacy.Shift using (module Shifting)
open import adequacy.Leaves.Union using (tw-assoc; tw-swap)
open import adequacy.Shift.Walk using (module ShiftWalk)
open import adequacy.Kept using (module Keeping)

open import adequacy.Climbs.Base using (module ClimbBase)
open import adequacy.Climbs.Take using (module ClimbTake)
open import adequacy.Climbs.Flat using (module ClimbFlat)
open import adequacy.Climbs.Flat.Plant using (module ClimbFlatPlant)
open Events∞



module ClimbLanes (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open SortingWalk R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Feed; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; fired; Path; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; outers; outersL; outers-⊕; unsub; Owes; Settled; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Spot; spot; ∧-join; Each; Lingers; Tied; seen; seenL; pinned-trans; ∧-split; false≢; owned-to; lv-tie; tw-tie; Twin; tw-union; tw-trans; tw-sym; tw-refl; Leaves; Restful; lv-trans; lv-union; lv-refl; tw-rest; tw-if; rf-union; rf-rest)
  open StrongHeld R using (Strong; Carried; carried; closing; Meets; Heads; DoneBy; module Eaching; module Lingering)
  open StrongAgainst.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs; StackAs; Ticked; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots; SrcOf; src-of) renaming (Placed to Placedᴬ)
  open Pure R using (Timer; cascade; wkTimer)
  open Moving R using (pairs-r; pairs-split; plant-self; takes; takesᴸ; stage; takes-plant; plant; plantᴸ; planted; plantedᴸ; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant; joiners-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open EverywhereGated.Settling R using (settled-plant; settled-retag)
  open EverywhereGated.Gating R using (gated-alike; gated-path; gated-plant; gated-retag)
  open Tearing R using (cuts; attached-alike; cuts-switches; fresh-path; fresh-lanes; part-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; apart-l; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Forking R using (walk-planted)
  open Aliking R using (walk-grow; compile-cong; laneAt-wk; ObsRel)
  open Taking R using (tick-ix0)
  open Naming R using (pre; pairs-↭; names-plant-↭; fresh-plant; fresh-new; wk-pairs; wk-img; to-img)
  open Ghosting R using (residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; passed; Past; Lefts; LeftsL; OnEnd)
  open GhostingPaths R using (each-sub; each-lanes; module Far; module Calling; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; Rises; rises; Called; landed; rose; Aloft; aloft; hop-sorted; each-back; hopped-pre; lefts-up; lefts-subst; lefts-subst₂)
  open Gapping R using (Gapped; alike; gap-map; gap-scan; gap-take; gap-flat; gap-just; gap-connect; gap-live; gap-shut; gap-ended; gapM-refl; gapL-refl; gapL-mid; feed-gapped; gapped-past; gapped-sane; gapped-placed; gapped-deep)
  open Lowering R using (Keeps; queue-keeps; store-keeps; keeps-trans)
  open Lifting R using (emit-shut; emit-run; spread-past; behind-fire; fire-lingers; kont-onward; feed-onward; src-onward; burst-poll; burst-play; cut-onward)
  open LiftingOrder R using (sub-onward; emit-void; run-meets; run-at; heads-lift)
  open Locality R using (stored-at; stored-hit; live-apart; flatReads; cut-in; module Heaps)
  open Growing R using (wkTree; wkLanes; wkPath; wkPathᴸ)
  open Retagging R using (module Body; fed-owed; fed-retag; envP; joiners-path; retag; unsub-retag; begun-retag; names-retag)
  open Everywhere.Spending R using (spent-retag)
  open EverywhereGated.Holding R using (holds-alike; holds-path; holds-plant; holds-retag)
  open Keeping R using (seen-planted)
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pooledL-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag; tw-alike)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined)
  open FramingRepool R using (Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; lefts-planted; merged-queued; merged-kept; healed-off; module Framed; flat-stays)
  open ClimbTake R using (rise; open-code; writes; reads)
  open ClimbFlat R using (calling-open; opened-⊕; shut-code; settledᵒ; settleᵒ₂; settleᵒ₁; flat-gone; merged-pool; heading-∘; lanes-one; ghost-lift; startAt; tw-leftover; module Restaged; module Settles)
  open ClimbFlatPlant R using (pending-flags; queue-open; apart-unplant; lane-begin)

  -- A lane's cut, the one its path passes.
  laneOf : ∀ {h Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → Kit.Cut h
  laneOf (one-this {c = c}) = c
  laneOf (one-next o)       = laneOf o

  laneOf-in : ∀ {h Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL) → laneOf o ∈ᴸ cuts ls
  laneOf-in one-this     = here refl
  laneOf-in (one-next o) = there (laneOf-in o)

  -- The observer a one-step lane path walks to: the lane's.
  walk-lane : ∀ {h Δ A B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL) op (f : A → _) fl (W : Here h Δ B)
            → Here.obs (walkLanes op f fl W πL) ≡ Canon.Flat′.laneO op f (Here.env W) (Here.obs W) fl (laneOf o)
  walk-lane one-this     op f fl W = refl
  walk-lane (one-next o) op f fl W = walk-lane o op f fl W

  -- The lane a one-step path lifts through is live.
  lane-live : ∀ {h} {H : Heapᴹ h} {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
            → ∀ {s bs S as} → LiftsLane H πL s bs S as → At.val H (Kit.live (laneOf o)) ≡ true
  lane-live one-this     (lifts-this lv _) = lv
  lane-live (one-next o) (lifts-next L)    = lane-live o L

  -- The step a one-step lane path lifts is the lane's own.
  lane-step : ∀ {h} {H : Heapᴹ h} {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
            → ∀ {s bs S as} → LiftsLane H πL s bs S as → S ≡ s
  lane-step one-this     (lifts-this _ lifts-here) = refl
  lane-step (one-next o) (lifts-next L)            = lane-step o L

  -- A lane's lift ended leaves what the lane's leftover leaves.
  lane-lefts : ∀ {h} {H : Heapᴹ h} {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
             → ∀ {l s bs S as} (LL : LiftsLane H πL s bs S as) → LeftsL H l LL → OnEnd s (Leaves l (At.leftover H {B = ⊤} u))
  lane-lefts one-this     (lifts-this _ lifts-here) (ll , _) = ll
  lane-lefts (one-next o) (lifts-next L)            ll       = lane-lefts o L ll

  -- The parts of the lanes a one-step path lifts through: those it
  -- passes, the lane's, those after.
  lanes-at : ∀ {h} (H : Heapᴹ h) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL
           → ∀ {s bs S as} → LiftsLane H πL s bs S as → ∀ {c′} → At.part H u ≡ just c′ → At.partLanes H ls ≡ bs ++ c′ ∷ as
  lanes-at H one-this (lifts-this lv _) pu rewrite lv | pu = refl
  lanes-at H (one-next {l = l} {ls = ls} o) (lifts-next {bs = bs} {as = as} L) {c′} pu =
    trans (lanes-one H l ls) (trans (cong (At.partLanes H (l ∷ []) ++_) (lanes-at H o L pu)) (sym (++-assoc (At.partLanes H (l ∷ [])) bs (c′ ∷ as))))

  -- The same, the lane's own part gone: it shows nothing.
  lanes-gone : ∀ {h} (H : Heapᴹ h) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL
             → ∀ {s bs S as} → LiftsLane H πL s bs S as → At.part H u ≡ nothing → At.partLanes H ls ≡ bs ++ as
  lanes-gone H one-this (lifts-this lv _) pu rewrite lv | pu = refl
  lanes-gone H (one-next {l = l} {ls = ls} o) (lifts-next {bs = bs} {as = as} L) pu =
    trans (lanes-one H l ls) (trans (cong (At.partLanes H (l ∷ []) ++_) (lanes-gone H o L pu)) (sym (++-assoc (At.partLanes H (l ∷ [])) bs as)))

  -- A flatMap holding a lane is open.
  merged-on : ∀ {h} (H : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) (bs : List (U.Node Δ B)) c as qs pl
            → At.merged H op g o (bs ++ c ∷ as) qs pl ≡ just (U.flatMapᶜ op g o (bs ++ c ∷ as) qs pl)
  merged-on H op g (just _) bs      c as qs pl = refl
  merged-on H op g nothing  []      c as qs pl = refl
  merged-on H op g nothing  (_ ∷ _) c as qs pl = refl

  -- A lane's own sub names no outer above it.
  one-outers : ∀ {h Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → outersL πL ≡ []
  one-outers one-this    = refl
  one-outers (one-next o) = one-outers o

  -- A value out of a lane: its guard read open, one operator up, the
  -- flatMap showing the lane past it.
  climb-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
              {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
              (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {y : B}
            → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (sends y) → Called st m₁ (ρ ⊕ in-lanes πL)
  climb-lanes st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {f} {fl} {oc} {k} {r} {po} {t = t} {ls} ρ πL o {y}
    cl@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr ; lefts = lt ; kept = kp }
    with lifts-split ρ (in-lanes πL) L in eqL
       | reads (subst (λ W → _ ≗ Observer.next W y) (trans (cong Here.obs (walk-⊕ ρ (in-lanes πL) top)) (walk-lane o op f fl (walk ρ top))) cd)
  ... | _ , lifts-lanes {bs = bs′} {l = l} {S = S₁} {as = as′} LL _ _ _ , Lρ | k₁ , f₁ , p₁ =
    rise kp (rises {sg′ = sends y} p₁ (one-lower ρ (one-lanes o)) (record
      { sane = sn ; placed = pd ; deep = dp ; ctl = refl
      ; code = ≗-trans (f₁ same⊑ (At.val hp (Kit.live (laneOf o))))
                 (≗-trans (wk-same (Kit.when (At.val hp (Kit.live (laneOf o))) (Observer.next (wkObs same⊑ (Here.obs (walk ρ top))) y)))
                   (≗-trans (open-code (lane-live o LL)) (wk-same (Observer.next (Here.obs (walk ρ top)) y))))
      ; stack = sk
      ; lifted = _ , pm
                 , S , subst (λ S′ → Lifts hp ρ (U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S)
                             (lane-step o LL) Lρ , sg
      ; rest-heads = tt
      ; lefts = lefts-subst (λ S′ → U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po)
                            (lane-step o LL) (lefts-up ρ (in-lanes πL) eqL lt)
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = sorted-⇝ so p₁ ; behind = bh ; lingers = lgr ; flags = done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl) ; kept = inj₁ refl }))
    where
      pm = trans (cong (λ ls′ → At.merged hp op (λ a j → U.subscribe (f a) j) (At.part hp t) ls′ (At.val hp (FlatKit.Flat.queue fl)) po)
                       (lanes-at hp o LL pv))
                 (merged-on hp op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ c′ as′ (At.val hp (FlatKit.Flat.queue fl)) po)


  -- A send, one step: the sink's callback run, what follows owed.
  sendStep : ∀ {h} {hp : Heapᴹ h} {q w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {X} {s : Sink h X} {x} {n : Act h ⊤}
           → a ≗ send s x n
           → Σ (Act h ⊤) λ n′ → n′ ≗ n
             × (mach ⟨ hp , q , run a σ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ hp , q , run (Callbacks.onNext (cbs hp s) x) same⊑ (push (rest n′) σ K) ⟩ clk ts bs td lg en mk)
  sendStep (send≗ refl e) = _ , e , then refl now

  -- An act at a value, read at one equal to it.
  at-val : ∀ {a} {X : Set a} {w} {F : X → Act w ⊤} {G : Act w ⊤} {y z : X} → y ≡ z → F z ≗ G → F y ≗ G
  at-val refl e = e

  -- Every subscription along a path against what the walk hands its
  -- kernel.
  mutual
    holds-walk : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (W : Here h Δ A)
               → At.Holds H t (Here.env W) (Here.obs W) → At.Holds H u (Here.env (walk π W)) (Here.obs (walk π W))
    holds-walk H here          W hs                    = hs
    holds-walk H (in-map π)    W hs                    = holds-walk H π _ hs
    holds-walk H (in-scan π)   W hs                    = holds-walk H π _ hs
    holds-walk H (in-take π)   W (_ , hs)              = holds-walk H π _ hs
    holds-walk H (in-outer π)  W (_ , _ , _ , hso , _) = holds-walk H π _ hso
    holds-walk H {t = flatMapˢ op f fl _ _ _ _ _ _} (in-lanes π) W (_ , _ , _ , _ , _ , _ , hl) = holdsL-walk H {op = op} {f = f} {fl = fl} π W hl
    holds-walk H (in-source π) W (_ , _ , _ , hs , _)  = holds-walk H π _ hs
    holds-walk H (in-body π)   W (_ , _ , _ , _ , hs)  = holds-walk H π _ hs
    holds-walk H (in-defer π)  W (_ , hs)              = holds-walk H π _ hs

    holdsL-walk : ∀ {h} (H : Heapᴹ h) {Δ A B Δ′ A′ op f fl} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (W : Here h Δ B)
                → At.HoldsLanes H {A = A} op f (Here.env W) (Here.obs W) fl ls
                → At.Holds H u (Here.env (walkLanes op f fl W π)) (Here.obs (walkLanes op f fl W π))
    holdsL-walk H (this-lane π) W (_ , hs , _) = holds-walk H π _ hs
    holdsL-walk H {op = op} {f = f} {fl = fl} (next-lane π) W (_ , _ , hl) = holdsL-walk H {op = op} {f = f} {fl = fl} π W hl

  -- What a lane's end runs past its guard.
  laneEnd : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)} {v : Sub h Δ B} {πL : PathLanes ls v}
          → Path T (flatMapˢ op f fl oc k r pl u ls) → OneLane πL → Act h ⊤
  laneEnd {op = op} {f} {fl} ρ o = Observer.complete (Canon.Flat′.lane op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl same⊑ (laneOf o))

  -- What a freed slot's refill runs.
  dequeueAt : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
            → Path T (flatMapˢ op f fl oc k r pl u ls) → Act h ⊤
  dequeueAt {op = op} {f} {fl} ρ = Canon.Flat′.dequeue op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl

  -- The heap a lane's end leaves: its cut dropped, then its count down.
  unlive : ∀ {h} → Heapᴹ h → Kit.Cut h → Heapᴹ h
  unlive H c = store H (Kit.live c) (lift false)

  freed : ∀ {h A} → Heapᴹ h → Kit.Cut h → FlatKit.Flat A h → Heapᴹ h
  freed H c fl = store (unlive H c) (FlatKit.Flat.active fl) (lift (pred (At.val (unlive H c) (FlatKit.Flat.active fl))))

  -- A switch dropped turns none on.
  drop-true : ∀ {h} (H : Heapᴹ h) (d c : Kit.Cut h) → At.val (unlive H d) (Kit.live c) ≡ true → At.val H (Kit.live c) ≡ true
  drop-true H d c e with look-either H (Kit.live d) (Kit.live c) {lift false}
  ... | inj₁ n = ⊥-elim (f≢t (trans (sym (cong lower (stored-hit H (Kit.live d) (Kit.live c) n))) e))
    where f≢t : false ≢ true
          f≢t ()
  ... | inj₂ q = trans (cong lower (sym q)) e

  -- A switch dropped turns none on, read forward.
  drop-false : ∀ {h} (H : Heapᴹ h) (d c : Kit.Cut h) → At.val H (Kit.live c) ≡ false → At.val (unlive H d) (Kit.live c) ≡ false
  drop-false H d c e with look-either H (Kit.live d) (Kit.live c) {lift false}
  ... | inj₁ n = cong lower (stored-hit H (Kit.live d) (Kit.live c) n)
  ... | inj₂ q = trans (cong lower q) e

  -- One lane's term of the count, the count past it one more.
  if-suc : ∀ {b₁ b₂ : Bool} {x y} → b₁ ≡ b₂ → suc x ≡ y → suc (if b₁ then suc x else x) ≡ (if b₂ then suc y else y)
  if-suc {true}  refl e = cong suc e
  if-suc {false} refl e = e

  if-off : ∀ {b₁ b₂ : Bool} {x y} → b₁ ≡ false → b₂ ≡ true → x ≡ y → suc (if b₁ then suc x else x) ≡ (if b₂ then suc y else y)
  if-off refl refl e = cong suc e

  -- A live lane's switch dropped: the count one down.
  count-unlive : ∀ {h} (H : Heapᴹ h) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
               → AllPairs _≢_ (laneNames ls) → At.val H (Kit.live (laneOf o)) ≡ true
               → suc (At.count (unlive H (laneOf o)) ls) ≡ At.count H ls
  count-unlive H (one-this {c = c} {k} {t = s₀} {ls′}) (nl ∷ _) e =
    if-off (cong lower (stored-at H (Kit.live c) (lift false))) e
           (Heaps.count-lives H (unlive H c) ls′ λ m → look-store H (Kit.live c) _ (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) (cut-in ls′ m))))))
  count-unlive H (one-next {l = lane c k s₀} {ls = ls′} o) ps@(nl ∷ _) e =
    if-suc (cong lower (look-store H (Kit.live (laneOf o)) (Kit.live c) (λ eq → lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) (cut-in ls′ (laneOf-in o))))) (sym eq))))
           (count-unlive H o (pairs-r (names s₀) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) e)

  -- A lane ended: every other lane's gate as it was, its own listed.
  gatedL-freed : ∀ {h} (H : Heapᴹ h) {A Δ B} (fl : FlatKit.Flat A h) {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
               → AllPairs _≢_ (laneNames ls) → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls)
               → ∀ {X} → laneOf o ∈ᴸ X
               → At.GatedLanes H X ls → At.GatedLanes (freed H (laneOf o) fl) X ls
  gatedL-freed H fl (one-this {c = c} {k} {t = s₀} {ls′}) (nl ∷ _) (na ∷ nas) cu (_ , g₂ , g₃) =
    (λ _ → inj₁ cu)
    , gated-alike s₀ (λ j m →
        trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ˡ m)))))
              (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ˡ m)))))) g₂
    , Heaps.gatedL-alike H (freed H c fl) ls′ (λ j m →
        trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))
              (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))) g₃
  gatedL-freed H fl (one-next {l = lane c k s₀} {ls = ls′} o) ps@(nl ∷ _) nas cu (g₁ , g₂ , g₃) =
    (λ e → sum-map₂ (Heaps.cut-alike H (freed H (laneOf o) fl) k s₀ ag) (g₁ (trans (sym ec) e)))
    , gated-alike s₀ ag g₂
    , gatedL-freed H fl o (pairs-r (names s₀) P) (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))) cu g₃
    where
      P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      d∈ = cut-in ls′ (laneOf-in o)
      ec = cong lower (trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (lookupᴬ nas (here refl)))
                             (look-store H (Kit.live (laneOf o)) (Kit.live c) (λ eq → lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) d∈))) (sym eq))))
      ag : Alike H (freed H (laneOf o) fl) (names s₀)
      ag j m = trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) j (lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                     (look-store H (Kit.live (laneOf o)) j (λ eq → lookupᴬ (apart-r (names s₀) P m) d∈ (sym eq)))

  -- A freed slot's refill read: the sink, handed on.
  refillAt : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
           → Path T (flatMapˢ op f fl oc k r pl u ls) → Act h ⊤
  refillAt {op = op} {f} {fl} ρ = readRef (FlatKit.Flat.refill fl) λ τ → Canon.Flat′.handOn op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl (same⊑ ⨾ τ)

  -- A lane's end touches neither the refill cell nor any sink.
  refill-freed : ∀ {h} (H : Heapᴹ h) {A} (c : Kit.Cut h) (fl : FlatKit.Flat A h)
               → At.val (freed H c fl) (FlatKit.Flat.refill fl) ≡ At.val H (FlatKit.Flat.refill fl)
  refill-freed H c fl = trans (cong lower (look-store (unlive H c) (FlatKit.Flat.active fl) (FlatKit.Flat.refill fl) (λ ())))
                              (cong lower (look-store H (Kit.live c) (FlatKit.Flat.refill fl) (λ ())))

  queue-freed : ∀ {h} (H : Heapᴹ h) {A} (c : Kit.Cut h) (fl : FlatKit.Flat A h)
              → At.val (freed H c fl) (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
  queue-freed H c fl = trans (cong lower (look-store (unlive H c) (FlatKit.Flat.active fl) (FlatKit.Flat.queue fl) (λ ())))
                             (cong lower (look-store H (Kit.live c) (FlatKit.Flat.queue fl) (λ ())))

  -- A queue written reads what was written.
  queue-stored : ∀ {h} (H : Heapᴹ h) {A} (fl : FlatKit.Flat A h) ys → At.val (store H (FlatKit.Flat.queue fl) (lift ys)) (FlatKit.Flat.queue fl) ≡ ys
  queue-stored H fl ys = cong lower (stored-at H (FlatKit.Flat.queue fl) (lift ys))

  -- A lane's path open: what it opens from is.
  one-open : ∀ {h} (H : Heapᴹ h) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL) {b}
           → openedL H b πL ≡ true → b ≡ true
  one-open H one-this     e = proj₂ (∧-split _ e)
  one-open H (one-next o) e = one-open H o e

  slot-freed : ∀ {h} (H : Heapᴹ h) {A X} (c : Kit.Cut h) (fl : FlatKit.Flat A h) (s : Sink h X) → cbs (freed H c fl) s ≡ cbs H s
  slot-freed H c fl s = trans (look-store (unlive H c) (FlatKit.Flat.active fl) s (λ ())) (look-store H (Kit.live c) s (λ ()))

  -- A lane cut shows no part.
  lane-dead : ∀ {h} (H : Heapᴹ h) {Δ B} {c : Kit.Cut h} {k} {s : Sub h Δ B} → look H (Kit.live c) ≡ lift false
            → At.partLanes H (lane c k s ∷ []) ≡ []
  lane-dead H e rewrite e = refl

  -- A lane ended: the lanes' parts all but its own, the rest apart from
  -- its cut and the count.
  lanes-freed : ∀ {h} (H : Heapᴹ h) {A Δ B} (fl : FlatKit.Flat A h) {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
              → AllPairs _≢_ (laneNames ls) → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls)
              → ∀ {s bs S as} → LiftsLane H πL s bs S as → At.partLanes (freed H (laneOf o) fl) ls ≡ bs ++ as
  lanes-freed H fl one-this (nl ∷ ps) (na ∷ nas) (lifts-this {c = c} {k} {t = s₀} {ls = ls′} lv L) =
    trans (lanes-one (freed H c fl) (lane c k s₀) ls′)
          (trans (cong (_++ At.partLanes (freed H c fl) ls′)
                       (lane-dead (freed H c fl) {c = c} {k} {s₀} (trans (look-store (unlive H c) (FlatKit.Flat.active fl) (Kit.live c) na) (stored-at H (Kit.live c) (lift false)))))
    (partLanes-alike H (freed H c fl) ls′ λ j m →
      trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))
            (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))))
  lanes-freed H fl (one-next {l = lane c k s₀} {ls = ls′} o) ps@(nl ∷ _) nas (lifts-next {bs = bs} {as = as} L) =
    trans (lanes-one (freed H (laneOf o) fl) (lane c k s₀) ls′)
          (trans (cong₂ _++_ el (lanes-freed H fl o (pairs-r (names s₀) P) (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))) L))
                 (sym (++-assoc (At.partLanes H (lane c k s₀ ∷ [])) bs as)))
    where
      P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      d∈ = cut-in ls′ (laneOf-in o)
      el = lane1-alike H (freed H (laneOf o) fl) {c = c} {k} {s₀}
             (trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (lookupᴬ nas (here refl)))
                    (look-store H (Kit.live (laneOf o)) (Kit.live c) (λ eq → lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) d∈))) (sym eq))))
             (part-alike H (freed H (laneOf o) fl) s₀ λ j m →
               trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) j (lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                     (look-store H (Kit.live (laneOf o)) j (λ eq → lookupᴬ (apart-r (names s₀) P m) d∈ (sym eq))))

  -- One lane's term of the pool, a node joined in front moved past it.
  tw-slot : ∀ {Γ C} (v : Bool) {lu P P₂ S S₂ : U.Node Γ C} → Twin (U.unionᶜ lu P) P₂ → Twin S S₂
          → Twin (U.unionᶜ lu (if v then P else U.unionᶜ S P)) (if v then P₂ else U.unionᶜ S₂ P₂)
  tw-slot true  t _ = t
  tw-slot false {lu} {P} {S = S} t s =
    tw-trans (tw-sym (tw-assoc lu S P)) (tw-trans (tw-union (tw-swap lu S) (tw-refl P)) (tw-trans (tw-assoc S lu P) (tw-union s t)))

  -- A live lane ended: the pool runs what it ran and the lane's leftover
  -- besides.
  pooledL-freed : ∀ {h} (H : Heapᴹ h) {A Δ B} (fl : FlatKit.Flat A h) {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
                → AllPairs _≢_ (laneNames ls) → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls)
                → At.val H (Kit.live (laneOf o)) ≡ true
                → ∀ {C} → Twin (U.unionᶜ (At.leftover H {B = C} u) (At.pooledL H {B = C} ls)) (At.pooledL (freed H (laneOf o) fl) {B = C} ls)
  pooledL-freed H fl (one-this {c = c} {k} {t = s₀} {ls′}) (nl ∷ _) (na ∷ nas) lv {C} =
    subst₂ (λ v v₂ → Twin (U.unionᶜ (At.leftover H {B = C} s₀) (if v then At.pooledL H {B = C} ls′ else U.unionᶜ (At.leftover H {B = C} s₀) (At.pooledL H ls′)))
                          (if v₂ then At.pooledL H₂ {B = C} ls′ else U.unionᶜ (At.leftover H₂ {B = C} s₀) (At.pooledL H₂ ls′)))
           (sym lv) (sym (cong lower (trans (look-store (unlive H c) (FlatKit.Flat.active fl) (Kit.live c) na) (stored-at H (Kit.live c) (lift false)))))
           (tw-union (tw-alike (leftover-alike H H₂ {B = C} s₀ ag)) (tw-alike (pooledL-alike H H₂ ls′ agL)))
    where
      H₂ = freed H c fl
      ag : Alike H H₂ (names s₀)
      ag j m = trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                     (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ˡ m)))))
      agL : Alike H H₂ (laneNames ls′)
      agL j m = trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))
                      (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))
  pooledL-freed H fl {u = u} (one-next {l = lane c k s₀} {ls = ls′} o) ps@(nl ∷ _) nas lv {C} =
    subst (λ v₂ → Twin (U.unionᶜ (At.leftover H {B = C} u) (At.pooledL H {B = C} (lane c k s₀ ∷ ls′)))
                       (if v₂ then At.pooledL H₂ {B = C} ls′ else U.unionᶜ (At.leftover H₂ {B = C} s₀) (At.pooledL H₂ ls′)))
          (sym ec)
          (tw-slot (At.val H (Kit.live c))
             (pooledL-freed H fl o (pairs-r (names s₀) P) (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))) lv)
             (tw-alike (leftover-alike H H₂ {B = C} s₀ ag)))
    where
      H₂ = freed H (laneOf o) fl
      P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      d∈ = cut-in ls′ (laneOf-in o)
      ec : At.val H₂ (Kit.live c) ≡ At.val H (Kit.live c)
      ec = cong lower (trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (lookupᴬ nas (here refl)))
                             (look-store H (Kit.live (laneOf o)) (Kit.live c) (λ eq → lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) d∈))) (sym eq))))
      ag : Alike H H₂ (names s₀)
      ag j m = trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) j (lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                     (look-store H (Kit.live (laneOf o)) j (λ eq → lookupᴬ (apart-r (names s₀) P m) d∈ (sym eq)))

  -- A lane ended revives no lane's part.
  lanes-none : ∀ {h} (H : Heapᴹ h) {A Δ B} (fl : FlatKit.Flat A h) {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
             → AllPairs _≢_ (laneNames ls) → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls)
             → At.partLanes H ls ≡ [] → At.partLanes (freed H (laneOf o) fl) ls ≡ []
  lanes-none H fl (one-this {c = c} {k} {t = s₀} {ls′}) (nl ∷ _) (na ∷ nas) e =
    trans (lanes-one (freed H c fl) (lane c k s₀) ls′)
          (trans (cong (_++ At.partLanes (freed H c fl) ls′)
                       (lane-dead (freed H c fl) {c = c} {k} {s₀} (trans (look-store (unlive H c) (FlatKit.Flat.active fl) (Kit.live c) na) (stored-at H (Kit.live c) (lift false)))))
          (trans (partLanes-alike H (freed H c fl) ls′ λ j m →
                    trans (look-store (unlive H c) (FlatKit.Flat.active fl) j (lookupᴬ nas (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m)))))
                          (look-store H (Kit.live c) j (lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m))))))
                 (++-conicalʳ (At.partLanes H (lane c k s₀ ∷ [])) _ (trans (sym (lanes-one H (lane c k s₀) ls′)) e))))
  lanes-none H fl (one-next {l = lane c k s₀} {ls = ls′} o) ps@(nl ∷ _) nas e =
    trans (lanes-one (freed H (laneOf o) fl) (lane c k s₀) ls′)
          (cong₂ _++_ (trans el (++-conicalˡ (At.partLanes H (lane c k s₀ ∷ [])) _ e′))
                      (lanes-none H fl o (pairs-r (names s₀) P) (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) m))))
                                  (++-conicalʳ (At.partLanes H (lane c k s₀ ∷ [])) _ e′)))
    where
      e′ = trans (sym (lanes-one H (lane c k s₀) ls′)) e
      P  = pairs-r (quietName k) (pairs-r (cutNames c) ps)
      d∈ = cut-in ls′ (laneOf-in o)
      el = lane1-alike H (freed H (laneOf o) fl) {c = c} {k} {s₀}
             (trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (lookupᴬ nas (here refl)))
                    (look-store H (Kit.live (laneOf o)) (Kit.live c) (λ eq → lookupᴬ nl (there (++⁺ʳ (quietName k) (++⁺ʳ (names s₀) d∈))) (sym eq))))
             (part-alike H (freed H (laneOf o) fl) s₀ λ j m →
               trans (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) j (lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ˡ m)))))
                     (look-store H (Kit.live (laneOf o)) j (λ eq → lookupᴬ (apart-r (names s₀) P m) d∈ (sym eq))))

  -- A lane path seen past a lane's end only if seen before it: a switch
  -- dropped turns none on, and beneath each lane the heap alike.
  seenL-drop : ∀ {h} (H : Heapᴹ h) {A} (d : Kit.Cut h) (fl : FlatKit.Flat A h) {Δ B} {ls : List (Lane h Δ B)}
             → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls)
             → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → Alike H (freed H d fl) (names x))
             → ∀ {Δ′ A′} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → seenL (freed H d fl) πL ≡ true → seenL H πL ≡ true
  seenL-drop H d fl (na ∷ _) al (this-lane {c = c} ψ) sn =
    cong₂ _∧_ (drop-true H d c (trans (sym (cong lower (look-store (unlive H d) (FlatKit.Flat.active fl) (Kit.live c) na))) (proj₁ sp)))
              (trans (sym (seen-alike H (freed H d fl) ψ (al (this-lane here)))) (proj₂ sp))
    where sp = ∧-split (At.val (freed H d fl) (Kit.live c)) sn
  seenL-drop H d fl nas al (next-lane {l = lane c k s} πL) sn =
    seenL-drop H d fl (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k) (++⁺ʳ (names s) m)))) (λ π → al (next-lane π)) πL sn

  -- A LANE ENDED AND ITS SLOT FREED: its cut dropped and the count down,
  -- nothing else of the heap or the tree moved.  Parts hold only with
  -- the lane's own part gone: a live lane's part is its flatMap's.
  module Freed {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) where
    H′ = freed H (laneOf o) fl

    -- The lane's cut and the count the flatMap's own cells: its node's
    -- clauses read the count down with the lane gone, the rest of the
    -- tree by the frame.
    w₀ = flatMapˢ op f fl oc k r pl t ls

    ns : List (Name h)
    ns = (_ , Kit.live (laneOf o)) ∷ (_ , FlatKit.Flat.active fl) ∷ []

    fr-mine : All (_∈ᴸ names w₀) ns
    fr-mine = ++⁺ʳ (flatNames fl) (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) (cut-in ls (laneOf-in o))))))
              ∷ here refl ∷ []

    fr-off : Offʰ H H′ ns
    fr-off = off-++ {H = H} {H₁ = unlive H (laneOf o)} {H₂ = H′} ((_ , Kit.live (laneOf o)) ∷ []) (off-store H (Kit.live (laneOf o))) (off-store (unlive H (laneOf o)) (FlatKit.Flat.active fl))

    -- The outer's names apart from the lane's cut and the count.
    fr-apart : AllPairs _≢_ (names w₀) → ∀ {x} → x ∈ᴸ names t → All (x ≢_) ns
    fr-apart fr@(a₀ ∷ _) m =
      lookupᴬ (apart-r (names t) P m) (cut-in ls (laneOf-in o))
      ∷ (λ eq → lookupᴬ a₀ (there (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ m)))))))) (sym eq)) ∷ []
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) fr)))

    fr-part : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.part (freed H (laneOf o) fl) t ≡ At.part H t
    fr-part fr = part-alike H H′ t (Heaps.keeps H H′ fr-off (λ m → m) (fr-apart fr))

    fr-lanes-apart : AllPairs _≢_ (names w₀) → AllPairs _≢_ (laneNames ls)
    fr-lanes-apart fr = pairs-r (names t) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) fr))))

    fr-count-apart : AllPairs _≢_ (names w₀) → ∀ {n} → n ∈ᴸ laneNames ls → _≢_ {A = Name h} (_ , FlatKit.Flat.active fl) n
    fr-count-apart (a₀ ∷ _) m = lookupᴬ a₀ (there (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) m))))))))

    -- Beneath a lane, apart from the lane's cut and the count.
    fr-under : AllPairs _≢_ (names w₀) → ∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → ∀ {n} → n ∈ᴸ names x → All (n ≢_) ns
    fr-under fr ψ m = (λ eq → lookupᴬ (live-apart ψ (fr-lanes-apart fr) (laneOf-in o)) m (sym eq)) ∷ (λ eq → fr-count-apart fr (lanes-path ψ m) (sym eq)) ∷ []

    -- No part revived: the outer's and the queue as they were, the lanes'
    -- parts only fewer, and no switch beneath turned on.
    fr-gone : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → Gone H (freed H (laneOf o) fl) (flatMapˢ op f fl oc k r pl t ls)
    fr-gone fr@(a₀ ∷ _) = record { gone-part = gp ; gone-live = lv ; gone-held = λ hd → trans (store-held (unlive H (laneOf o)) (FlatKit.Flat.active fl) hd) (store-held H (Kit.live (laneOf o)) hd) }
      where
        gp : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path w₀ x → At.part H x ≡ nothing → At.part H′ x ≡ nothing
        gp here e =
          subst₂ (λ o′ Q → At.merged H′ op (λ a j → U.subscribe (f a) j) o′ (At.partLanes H′ ls) Q pl ≡ nothing) (sym (fr-part fr)) (sym (queue-freed H (laneOf o) fl))
                 (merged-kept H H′ op (λ a j → U.subscribe (f a) j) (At.part H t) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl
                              (lanes-none H fl o (fr-lanes-apart fr) (tabulateᴬ (fr-count-apart fr))) e)
        gp {x = x} (in-outer ψ) e = trans (part-alike H H′ x (Heaps.keeps H H′ fr-off (λ m → m) (λ m → fr-apart fr (names-path ψ m)))) e
        gp {x = x} (in-lanes ψ) e = trans (part-alike H H′ x (Heaps.keeps H H′ fr-off (λ m → m) (fr-under fr ψ))) e
        na : ∀ {Δ′ A′ i p c k′ tk} {s : Sub h Δ′ A′} → Path w₀ (takeWhileˢ i p c k′ tk s) → _≢_ {A = Name h} (_ , FlatKit.Flat.active fl) (_ , Kit.live c)
        na (in-outer ψ) = lookupᴬ a₀ (there (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path ψ (here refl))))))))))
        na (in-lanes ψ) = fr-count-apart fr (lanes-path ψ (here refl))
        lv : Lives H H′ w₀
        lv {c = c} ψ e = drop-true H (laneOf o) c (trans (sym (cong lower (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (na ψ)))) e)

    fr-done : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.val (freed H (laneOf o) fl) (FlatKit.Flat.outerDone fl) ≡ At.val H (FlatKit.Flat.outerDone fl)
    fr-done (a₀ ∷ a₁ ∷ _) =
      trans (cong lower (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (FlatKit.Flat.outerDone fl) (lookupᴬ a₀ (here refl))))
            (cong lower (look-store H (Kit.live (laneOf o)) (FlatKit.Flat.outerDone fl)
              (λ eq → lookupᴬ a₁ (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) (cut-in ls (laneOf-in o))))))))) (sym eq))))

    fr-held : ∀ (c : Kit.Cut h) → look H′ (Kit.held c) ≡ look H (Kit.held c)
    fr-held c = fr-off (Kit.held c) ((λ ()) ∷ (λ ()) ∷ [])

    fr-quiet : ∀ (k′ : Maybe (Quiet h)) → Alike H H′ (quietName k′)
    fr-quiet nothing  j ()
    fr-quiet (just q) j (here refl) = fr-off q ((λ ()) ∷ (λ ()) ∷ [])

    fr-so : AllPairs _≢_ (names w₀) → Alike H H′ (names t)
    fr-so fr = Heaps.keeps H H′ fr-off (λ m → m) (fr-apart fr)

    fr-lane : AllPairs _≢_ (names w₀) → ∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → Alike H H′ (names x)
    fr-lane fr πL = Heaps.keeps H H′ fr-off (λ m → m) (fr-under fr πL)

    -- The count one down with the lane gone, the lanes' cell untouched,
    -- every other cell beneath the flatMap alike.
    fr-holds : AllPairs _≢_ (names w₀) → At.val H (Kit.live (laneOf o)) ≡ true → ∀ {E o′} → At.Holds H w₀ E o′ → At.Holds H′ w₀ E o′
    fr-holds fr lv {E} {o′} (rf , sl , a , hs , ac , (gone , eq , ga) , hl) =
      trans (refill-freed H (laneOf o) fl) rf
      , Heaps.slot-alike H H′ r (slot-freed H (laneOf o) fl r) sl
      , attached-alike oc k (fr-held oc) (fr-quiet k) a
      , holds-alike t (fr-so fr) hs
      , trans (cong lower (stored-at (unlive H (laneOf o)) (FlatKit.Flat.active fl) _))
              (trans (cong pred (trans (cong lower (look-store H (Kit.live (laneOf o)) (FlatKit.Flat.active fl) (λ e → fr-count-apart fr d∈ (sym e))))
                                       (trans ac (sym (count-unlive H o (fr-lanes-apart fr) lv)))))
                     (sym (Heaps.count-lives (unlive H (laneOf o)) H′ ls λ m → look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) _ (fr-count-apart fr (cut-in ls m)))))
      , ( gone
        , trans (cong (λ z → lower z ++ gone) (fr-off (FlatKit.Flat.lanes fl) ((λ ()) ∷ (λ ()) ∷ [])))
                (trans eq (trans (cuts-switches H ls) (sym (cuts-switches H′ ls))))
        , tabulateᴬ λ {c} m →
            trans (cong lower (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c)
                                (fr-count-apart fr (cut-in ls (subst (c ∈ᴸ_) (trans eq (cuts-switches H ls)) (++⁺ʳ (At.val H (FlatKit.Flat.lanes fl)) m))))))
                  (drop-false H (laneOf o) c (lookupᴬ ga m)))
      , holdsL ls (λ π → π) hl
      where
        d∈ = cut-in ls (laneOf-in o)
        holdsL : ∀ (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
               → At.HoldsLanes H {A = A} op f E o′ fl ls′ → At.HoldsLanes H′ {A = A} op f E o′ fl ls′
        holdsL []                   em hl′ = hl′
        holdsL (lane c′ k′ s ∷ ls′) em (a′ , hs′ , hl′) =
          attached-alike c′ k′ (fr-held c′) (fr-quiet k′) a′
          , holds-alike s (fr-lane fr (em (this-lane here))) hs′
          , holdsL ls′ (λ π → em (next-lane π)) hl′

    -- The ended lane's gate now shut, its cut still owed: it was live, so
    -- not among the gone, so its flatMap lists it.  Every other gate as it
    -- was.
    fr-gated : AllPairs _≢_ (names w₀) → At.val H (Kit.live (laneOf o)) ≡ true → ∀ {E o′} → At.Holds H w₀ E o′ → At.Gated H w₀ → At.Gated H′ w₀
    fr-gated fr lv (_ , _ , _ , _ , _ , (gone , eq , ga) , _) (g₁ , g₂) =
      gated-alike t (fr-so fr) g₁
      , subst (λ X → At.GatedLanes H′ X ls) (cong lower (sym (fr-off (FlatKit.Flat.lanes fl) ((λ ()) ∷ (λ ()) ∷ []))))
          (gatedL-freed H fl o (fr-lanes-apart fr) (tabulateᴬ (fr-count-apart fr)) listed g₂)
      where
        listed : laneOf o ∈ᴸ At.val H (FlatKit.Flat.lanes fl)
        listed = [ (λ m → m) , (λ m → ⊥-elim (true≢false (trans (sym lv) (lookupᴬ ga m)))) ]′
                   (∈-++⁻ (At.val H (FlatKit.Flat.lanes fl)) (subst (laneOf o ∈ᴸ_) (sym (trans eq (cuts-switches H ls))) (laneOf-in o)))

    -- What lies under the flatMap untouched.
    fr-spent : AllPairs _≢_ (names w₀) → At.Spent H w₀ → At.Spent H′ w₀
    fr-spent fr (c₁ , c₂) = Heaps.cut-alike H H′ k t (fr-so fr) c₁ , spentL ls (λ π → π) c₂
      where
        spentL : ∀ (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
               → At.SpentLanes H ls′ → At.SpentLanes H′ ls′
        spentL []                   em sp = sp
        spentL (lane c′ k′ s ∷ ls′) em (s₁ , s₂) = Heaps.cut-alike H H′ k′ s (fr-lane fr (em (this-lane here))) s₁ , spentL ls′ (λ π → em (next-lane π)) s₂

    fr-fed : AllPairs _≢_ (names w₀) → ∀ ν → At.Fed H w₀ ν → At.Fed H′ w₀ ν
    fr-fed fr ν (f₁ , f₂) = Heaps.fed-alike H H′ t (fr-so fr) ν f₁ , fedL ls (λ π → π) f₂
      where
        fedL : ∀ (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
             → At.FedLanes H ls′ ν → At.FedLanes H′ ls′ ν
        fedL []                   em fd = fd
        fedL (lane c′ k′ s ∷ ls′) em (d₁ , d₂) = Heaps.fed-alike H H′ s (fr-lane fr (em (this-lane here))) ν d₁ , fedL ls′ (λ π → em (next-lane π)) d₂

    -- A lane past the drop is seen only if seen before it.
    fr-seL : AllPairs _≢_ (names w₀) → ∀ {Δ′ A′} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → seenL H′ πL ≡ true → seenL H πL ≡ true
    fr-seL fr = seenL-drop H (laneOf o) fl (tabulateᴬ (fr-count-apart fr)) (fr-lane fr)

    fr-revive : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → is-just (At.part (freed H (laneOf o) fl) (flatMapˢ op f fl oc k r pl t ls)) ≡ true → is-just (At.part H (flatMapˢ op f fl oc k r pl t ls)) ≡ true
    fr-revive fr j with At.part H w₀ in e
    ... | just _  = refl
    ... | nothing = ⊥-elim (true≢false (trans (sym j) (cong is-just (Gone.gone-part (fr-gone fr) here e))))

    -- What the flatMap leaves running alike: its outer's names and every
    -- lane's beneath its cut apart from the write.
    fr-left : AllPairs _≢_ (names w₀) → ∀ {C} → At.leftover H′ {B = C} w₀ ≡ At.leftover H {B = C} w₀
    fr-left fr = cong₂ U.unionᶜ (leftover-alike H H′ t (fr-so fr)) (leftL ls (λ π → π))
      where
        leftL : ∀ {C} (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
              → At.leftoverL H′ {B = C} ls′ ≡ At.leftoverL H {B = C} ls′
        leftL []                   em = refl
        leftL (lane c′ k′ s ∷ ls′) em = cong₂ U.unionᶜ (leftover-alike H H′ s (fr-lane fr (em (this-lane here)))) (leftL ls′ (λ π → em (next-lane π)))

    -- A lane's ties seen only through lanes still on, each alike.
    fr-lingersL : AllPairs _≢_ (names w₀) → LingersL H ls → LingersL H′ ls
    fr-lingersL fr lL = record
      { poolsL = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls′ = ls₀} πL sn e → lv-tie (LingersL.poolsL lL πL (fr-seL fr πL sn) (trans (sym (pt πL)) e)) (proj₁ (tw-alike (pooled-from H H′ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → m) (fr-lane fr πL))))
      ; restsL = λ {src = src₀} πL sn e pn pe → tw-tie (LingersL.restsL lL πL (fr-seL fr πL sn) (trans (sym (pt πL)) e) (trans (sym (pt (πL ⊕ᴸ in-source here))) pn) pe)
                                                (tw-alike (leftover-from H H′ {B = ⊤} {x = src₀} (λ m → m) (fr-lane fr (πL ⊕ᴸ in-source here)))) }
      where
        pt : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → At.part H′ x ≡ At.part H x
        pt {x = x} πL = part-alike H H′ x (fr-lane fr πL)

    -- No part left: what the flatMap leaves running alike beneath it.
    fr-lingering : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.part (freed H (laneOf o) fl) (flatMapˢ op f fl oc k r pl t ls) ≡ nothing → Lingering H (freed H (laneOf o) fl) (flatMapˢ op f fl oc k r pl t ls) (flatMapˢ op f fl oc k r pl t ls)
    fr-lingering fr gn = record
      { ling-revive = λ j → ⊥-elim (true≢false (trans (sym j) (cong is-just gn)))
      ; ling-rested = λ {C} → tw-alike (fr-left fr {C})
      ; ling-below  = λ lg → Linger.lg-flat H′ (λ e → ⊥-elim (true≢false (trans (sym (cong is-just e)) (cong is-just gn))))
                                (lingers-alike H H′ (fr-so fr) (lingers-sub H lg (in-outer here) refl))
                                (fr-lingersL fr (lingersL-of H lg)) }

    -- The pool moved as the lane ends: what the flatMap leaves running
    -- alike beneath it, the pool tied by what it is owed.
    fr-repooled : AllPairs _≢_ (names w₀) → ∀ pl′ → (is-just (At.part H′ (flatMapˢ op f fl oc k r pl′ t ls)) ≡ true → is-just (At.part H w₀) ≡ true)
                → (∀ {c} → At.part H w₀ ≡ just c → Leaves pl (At.pooled H fl t ls) × Restful pl → Leaves pl′ (At.pooled H′ fl t ls) × Restful pl′)
                → Lingering H H′ w₀ (flatMapˢ op f fl oc k r pl′ t ls)
    fr-repooled fr pl′ rv tie = record
      { ling-revive = rv
      ; ling-rested = λ {C} → tw-alike (fr-left fr {C})
      ; ling-below  = λ lg → Linger.lg-flat H′ (pool lg)
                                (lingers-alike H H′ (fr-so fr) (lingers-sub H lg (in-outer here) refl))
                                (fr-lingersL fr (lingersL-of H lg)) }
      where
        pool : Lingers H w₀ → ∀ {c} → At.part H′ (flatMapˢ op f fl oc k r pl′ t ls) ≡ just c → Leaves pl′ (At.pooled H′ fl t ls) × Restful pl′
        pool lg x = tie e₀ (Lingers.pools lg here refl e₀)
          where e₀ = proj₂ (just-of (rv (cong is-just x)))

    -- The lane's rest taken into the pool: the freed lane's leftover is
    -- what the pool now adds, and the lane's own node leaves alike it.
    fr-settled : AllPairs _≢_ (names w₀) → (l : U.Node Δ B) → Leaves l (At.leftover H {B = ⊤} u) → At.val H (Kit.live (laneOf o)) ≡ true
               → (is-just (At.part H′ (flatMapˢ op f fl oc k r (U.unionᶜ pl (U.restᶜ l)) t ls)) ≡ true → is-just (At.part H w₀) ≡ true)
               → Lingering H H′ w₀ (flatMapˢ op f fl oc k r (U.unionᶜ pl (U.restᶜ l)) t ls)
    fr-settled fr l lu lv rv = fr-repooled fr _ rv λ _ (t₀ , rf) →
        lv-trans (lv-union t₀ (lv-trans (proj₁ (tw-rest l)) (lv-trans lu (proj₁ (tw-leftover H u)))))
          (lv-trans (proj₁ (tw-assoc D Pl Lu))
            (lv-trans (lv-union (lv-refl D) (proj₁ (tw-swap Pl Lu)))
              (lv-union (proj₁ D₂) (proj₁ (pooledL-freed H fl o (fr-lanes-apart fr) (tabulateᴬ (fr-count-apart fr)) lv)))))
      , rf-union rf rf-rest
      where
        D  = if At.val H (FlatKit.Flat.outerDone fl) then At.leftover H {B = B} t else U.idleᶜ
        Pl = At.pooledL H {B = B} ls
        Lu = At.leftover H {B = B} u
        D₂ : Twin D (if At.val H′ (FlatKit.Flat.outerDone fl) then At.leftover H′ {B = B} t else U.idleᶜ)
        D₂ = subst (λ b → Twin D (if b then At.leftover H′ {B = B} t else U.idleᶜ)) (sym (fr-done fr))
               (tw-if (At.val H (FlatKit.Flat.outerDone fl)) (tw-alike (leftover-alike H H′ t (fr-so fr))) (tw-refl U.idleᶜ))

    module Wr (fs : AllPairs _≢_ (names T)) = Wrote H H′ ρ fr-off fr-mine fs
    module Sh (fs : AllPairs _≢_ (names T)) = Shift H H′ ρ fr-off fr-mine fs
    module Fr (fs : AllPairs _≢_ (names T)) (lv : At.val H (Kit.live (laneOf o)) ≡ true) =
      Framed H H′ ρ fr-off fr-mine fs
        (record { holds = λ {E} {o′} → fr-holds (fresh-path ρ fs) lv {E} {o′} ; gated = λ {E} {o′} → fr-gated (fresh-path ρ fs) lv {E} {o′} ; spent = fr-spent (fresh-path ρ fs) ; left = fr-left (fresh-path ρ fs) })
        (fr-fed (fresh-path ρ fs))
        (keeps-trans (store-keeps H (Kit.live (laneOf o)) _ (λ ()) (λ ()) (λ ()) (λ ()))
                     (store-keeps (unlive H (laneOf o)) (FlatKit.Flat.active fl) _ (λ ()) (λ ()) (λ ()) (λ ())))

    -- No flag moved: the done flag and the outer alike, a lane seen
    -- after only if before, every cell beneath a lane alike.
    fr-flags₀ : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → ∀ {xs} → DoneBy H (flatMapˢ op f fl oc k r pl t ls) xs → DoneBy (freed H (laneOf o) fl) (flatMapˢ op f fl oc k r pl t ls) xs
    fr-flags₀ fr {xs} d =
      Flag.db-flat H′ {ns = xs} (flagged-moved H H′ {fl = fl} {so = t} (fr-done fr) (fr-part fr) (d here refl))
        (flags-alike H H′ (fr-so fr) (Flag.db-sub H d (in-outer here) refl))
        (λ {Δ′} {A′} {B′} {op′} {f′} {fl′} {oc′} {k′} {r′} {pl′} {so′} {ls′} πL′ sn → flagged-moved H H′ {fl = fl′} {so = so′} (cong lower (fr-lane fr {x = flatMapˢ op′ f′ fl′ oc′ k′ r′ pl′ so′ ls′} πL′ (FlatKit.Flat.outerDone fl′) (flag-in {t = flatMapˢ op′ f′ fl′ oc′ k′ r′ pl′ so′ ls′} here)))
                                            (part-at H H′ {t = flatMapˢ op′ f′ fl′ oc′ k′ r′ pl′ so′ ls′} (in-outer here) (fr-lane fr {x = flatMapˢ op′ f′ fl′ oc′ k′ r′ pl′ so′ ls′} πL′)) (Flag.dbL-of H d πL′ (fr-seL fr πL′ sn)))

    -- Through the frame, the flatMap repooled or not.
    fr-shift : AllPairs _≢_ (names T) → ∀ pl′ → (is-just (At.part H′ (flatMapˢ op f fl oc k r pl′ t ls)) ≡ true → is-just (At.part H w₀) ≡ true)
             → DoneBy H T (outers ρ) → DoneBy H′ (plant ρ (flatMapˢ op f fl oc k r pl′ t ls)) (outers ρ)
    fr-shift fs pl′ rv d =
      Sh.shift-flags fs (flatMapˢ op f fl oc k r pl′ t ls) {ns₀ = []} (λ ()) rv
        (λ d₀ → repool (fr-flags₀ (fresh-path ρ fs) (subst (DoneBy H w₀) (++-identityʳ (outers ρ)) d₀)))
        (subst (DoneBy H T) (sym (++-identityʳ (outers ρ))) d)
      where
        repool : DoneBy H′ w₀ (outers ρ) → DoneBy H′ (flatMapˢ op f fl oc k r pl′ t ls) (outers ρ)
        repool d′ = Flag.db-flat H′ {ns = outers ρ} (d′ here refl) (Flag.db-sub H′ d′ (in-outer here) refl) (Flag.dbL-of H′ d′)

    fr-flags : AllPairs _≢_ (names T) → DoneBy H T (outers ρ) → DoneBy H′ T (outers ρ)
    fr-flags fs d = subst (λ t′ → DoneBy H′ t′ (outers ρ)) (plant-self ρ) (fr-shift fs pl (fr-revive (fresh-path ρ fs)) d)

    fr-fifo : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.val (freed H (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
    fr-fifo (a₀ ∷ _ ∷ a₂ ∷ _) = cong lower (Heaps.keeps H H′ fr-off (λ m → m) ap (FlatKit.Flat.queue fl) (here refl))
      where
        ap : ∀ {x} → x ∈ᴸ (_ , FlatKit.Flat.queue fl) ∷ [] → All (x ≢_) ns
        ap (here refl) = lookupᴬ a₂ (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) (cut-in ls (laneOf-in o))))))))
                       ∷ (λ eq → lookupᴬ a₀ (there (here refl)) (sym eq)) ∷ []

    fr-lanes : AllPairs _≢_ (names w₀) → ∀ {s bs S as} → LiftsLane H πL s bs S as → At.partLanes H′ ls ≡ bs ++ as
    fr-lanes fr@(a₀ ∷ _) =
      lanes-freed H fl o (pairs-r (names t) P)
                  (tabulateᴬ λ m → lookupᴬ a₀ (there (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) m)))))))))
      where P = pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) fr)))

    -- One lane's joiners: a lane on past the drop was on before it, its
    -- part alike.
    told-lane : ∀ {C} (i : C ∈ᴸ Δ) (b′ b : Bool) → (b′ ≡ true → b ≡ true) → (m m′ : Maybe (U.Node Δ B)) → m′ ≡ m
              → (L L′ : List (U.Node Δ B)) → untoldᴸ i L′ ⊆ᴾ untoldᴸ i L
              → untoldᴸ i (if b′ then At.consᴹ H′ m′ L′ else L′) ⊆ᴾ untoldᴸ i (if b then At.consᴹ H m L else L)
    told-lane i false false _ m m′ _    L L′ sL = sL
    told-lane i false true  _ m m′ _    L L′ sL = λ x → ≡-⊆ (sym (cons-untold H i m L)) (++⁺ʳ (untoldᴹ i m) (sL x))
    told-lane i true  b     t m m′ refl L L′ sL with t refl
    ... | refl = λ x → ≡-⊆ (sym (cons-untold H i m L)) (++-mono (untoldᴹ i m) (untoldᴹ i m) (λ y → y) sL (≡-⊆ (cons-untold H′ i m L′) x))

    toldL : AllPairs _≢_ (names w₀) → ∀ {C} (i : C ∈ᴸ Δ) (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
          → All (_≢_ {A = Name h} (_ , FlatKit.Flat.active fl)) (laneNames ls′)
          → untoldᴸ i (At.partLanes H′ ls′) ⊆ᴾ untoldᴸ i (At.partLanes H ls′)
    toldL fr i []                   em nas = λ x → x
    toldL fr i (lane c k′ s ∷ ls′) em nas =
      told-lane i (At.val H′ (Kit.live c)) (At.val H (Kit.live c))
        (λ e → drop-true H (laneOf o) c (trans (sym (cong lower (look-store (unlive H (laneOf o)) (FlatKit.Flat.active fl) (Kit.live c) (lookupᴬ nas (here refl))))) e))
        (At.part H s) (At.part H′ s) (part-alike H H′ s (fr-lane fr (em (this-lane here))))
        (At.partLanes H ls′) (At.partLanes H′ ls′)
        (toldL fr i ls′ (λ π → em (next-lane π)) (tabulateᴬ λ m → lookupᴬ nas (++⁺ʳ (cutNames c) (++⁺ʳ (quietName k′) (++⁺ʳ (names s) m)))))

    -- The lane's cut and the count, at the flatMap: no part revived, no
    -- joiner newly untold, its heads by its outer's and its lanes' still
    -- on.
    fr-heading : AllPairs _≢_ (names w₀) → ∀ {q} → Heading H H′ q w₀ w₀
    fr-heading fr {q} = record
      { head-revive = fr-revive fr
      ; head-told   = λ i e₀ e′ m →
          ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H t) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀))
            (++-mono (untoldᴹ i (At.part H t)) (untoldᴹ i (At.part H′ t)) (≡-⊆ (cong (untoldᴹ i) (fr-part fr)))
                     (++-mono (untoldᴸ i (At.partLanes H ls)) (untoldᴸ i (At.partLanes H′ ls)) (toldL fr i ls (λ π → π) (tabulateᴬ (fr-count-apart fr))) (λ y → y))
                     (≡-⊆ (cong (untold i) (sym (merged-eq H′ op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl e′))) m))
      ; head-below  = λ ev → Build.each-flat H′ (Heads q) {op = op} {f} {fl} {oc} {k} {r} {pl} {so = t} {ls}
                               (root ev) (λ x → Each.pools ev here refl (proj₂ (just-of (fr-revive fr (cong is-just x)))))
                               (each-alike H H′ (fr-so fr) (each-sub ev (in-outer here) refl))
                               (lanes ev) }
      where
        G = λ a j → U.subscribe (f a) j
        root : Each H (Heads q) w₀ → ∀ {c} → At.part H′ w₀ ≡ just c → Heads q c
        root ev x =
          subst (Heads q) (trans (cong (λ Q → U.flatMapᶜ op G (At.part H′ t) (At.partLanes H′ ls) Q pl) (sym (fr-fifo fr)))
                                 (merged-eq H′ op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl x))
            (heads-flat op G (At.part H′ t) (At.partLanes H′ ls) (At.val H (FlatKit.Flat.queue fl)) pl (Each.pools ev here refl e₀)
              (λ e → Each.parts ev (in-outer here) refl (trans (sym (fr-part fr)) e))
              (each-lanes {H = H′} {P = Heads q} ls (λ {_} {_} {x} πL sL e → Each.parts ev (in-lanes πL) (fr-seL fr πL sL) (trans (sym (part-alike H H′ x (fr-lane fr πL))) e))))
          where e₀ = proj₂ (just-of (fr-revive fr (cong is-just x)))
        lanes : Each H (Heads q) w₀ → EachL H′ (Heads q) ls
        lanes ev = record
          { partsL = λ {_} {_} {x} πL sn e → EachL.partsL eL πL (fr-seL fr πL sn) (trans (sym (part-alike H H′ x (fr-lane fr πL))) e)
          ; poolsL = λ {_} {_} {_} {op₀} {f₀} {fl₀} {oc₀} {k₀} {r₀} {pl₀} {so₀} {ls₀} πL sn e →
              EachL.poolsL eL πL (fr-seL fr πL sn) (trans (sym (part-alike H H′ (flatMapˢ op₀ f₀ fl₀ oc₀ k₀ r₀ pl₀ so₀ ls₀) (fr-lane fr πL))) e)
          ; restsL = λ {_} {_} {_} {S₀} {c₀} {b₀} {kb₀} {k₀} {fd₀} {rp₀} {e₀} {rt₀} {src₀} {bd₀} πL sn e pn pe →
              EachL.restsL eL πL (fr-seL fr πL sn) (trans (sym (part-alike H H′ (connectˢ S₀ c₀ b₀ kb₀ k₀ fd₀ rp₀ e₀ rt₀ src₀ bd₀) (fr-lane fr πL))) e)
                (trans (sym (part-alike H H′ src₀ (fr-lane fr (πL ⊕ᴸ in-source here)))) pn) pe }
          where eL = eachL-of H ev

    fr-behind : AllPairs _≢_ (names T) → ∀ {q} → Untold H q T → Ends H T → Each H (Heads q) T → Each H′ (Heads q) T
    fr-behind fs {q} ut en bh = subst (λ t′ → Each H′ (Heads q) t′) (plant-self ρ) (Sh.shift-behind fs w₀ ut en (fr-heading (fresh-path ρ fs)) bh)
