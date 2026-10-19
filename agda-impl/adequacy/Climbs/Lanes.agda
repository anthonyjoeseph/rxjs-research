{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A FLATMAP'S LANES: a lane's rise, its end, the queue refilled.
module adequacy.Climbs.Lanes where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-assoc; ++-conicalˡ; ++-conicalʳ; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
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
open import Data.Nat using (suc; pred; _≡ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; skip; Pos; Timeline; Agree; ix)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane)
open import adequacy.Placed using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Gapped using (module Gapping)
open import adequacy.Lift using (module Lifting)
open import adequacy.Lowers using (module Lowering)
open import adequacy.Frame using (module Framing)
open import adequacy.Grow using (module Growing)
open import adequacy.Fork using (module Forking)
open import adequacy.Taken using (module Taking)
open import adequacy.Names using (module Naming)
open import adequacy.Local using (module Locality)
open import adequacy.Retag using (module Retagging)
open import adequacy.Replant using (module Replanting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Every using (module Everywhere)
open import adequacy.Alike using (module Aliking)
open import adequacy.Shift using (module Shifting)
open import adequacy.Kept using (module Keeping)

open import adequacy.Climbs.Base using (module ClimbBase)
open import adequacy.Climbs.Take using (module ClimbTake)
open import adequacy.Climbs.Flat using (module ClimbFlat)

open Events∞

module ClimbLanes (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open Sorting R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Strong; Carried; Books; Feed; carried; closing; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; Queue; Kernels; Meaning; fired; Owned; Path; Spot; spot; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; ∧-join; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; Meets; Each; Heads; Lingers; DoneBy; outers; outersL; outers-⊕; Tied; unsub; Owes; Settled; seen; seenL; pinned-trans; ∧-split; false≢; module Canon; owned-to; module Eaching; module Lingering) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs; StackAs; Ticked; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots; SrcOf; src-of) renaming (Placed to Placedᴬ)
  open Pure R using (Timer; cascade; wkTimer)
  open Moving R using (pairs-r; pairs-split; plant-self; takes; takesᴸ; stage; takes-plant; plant; plantᴸ; planted; plantedᴸ; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant; joiners-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open Everywhere.Settling R using (settled-plant; settled-retag)
  open Everywhere.Gating R using (gated-alike; gated-path; gated-plant; gated-retag)
  open Tearing R using (cuts; attached-alike; cuts-switches; fresh-path; fresh-lanes; part-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; apart-l; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Forking R using (walk-planted)
  open Aliking R using (walk-grow; compile-cong; laneAt-wk; ObsRel)
  open Taking R using (tick-ix0)
  open Naming R using (pre; pairs-↭; names-plant-↭; fresh-plant; fresh-new; wk-pairs; wk-img; to-img)
  open Ghosting R using (each-sub; each-lanes; module Far; module Calling; residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; Rises; rises; Called; landed; rose; passed; Past; Aloft; aloft; hop-sorted; each-back; hopped-pre)
  open Gapping R using (Gapped; alike; gap-map; gap-scan; gap-take; gap-flat; gap-just; gap-connect; gap-live; gap-shut; gap-ended; gapM-refl; gapL-refl; gapL-mid; feed-gapped; gapped-past; gapped-sane; gapped-placed; stepped-deep)
  open Lowering R using (Keeps; queue-keeps; store-keeps; keeps-trans)
  open Lifting R using (sub-onward; emit-shut; emit-void; run-meets; run-at; emit-run; spread-past; behind-fire; fire-lingers; kont-onward; feed-onward; src-onward; burst-poll; burst-play; cut-onward; heads-lift)
  open Locality R using (stored-at; stored-hit; live-apart; flatReads; cut-in; module Heaps)
  open Growing R using (wkTree; wkLanes; wkPath; wkPathᴸ)
  open Retagging R using (module Body; fed-owed; fed-retag; envP; joiners-path; retag; unsub-retag; begun-retag; names-retag)
  open Everywhere.Spending R using (spent-retag)
  open Everywhere.Holding R using (holds-alike; holds-path; holds-plant; holds-retag)
  open Keeping R using (seen-planted)
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; let-go; grip; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pin-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag)
  open Framing R using (merged-eq; heads-flat; Untold; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off)
    renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open Everywhere R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; merged-queued; merged-kept; healed-off)
  open ClimbTake R using (rise; open-code; writes; reads)
  open ClimbFlat R using (calling-open; opened-⊕; shut-code; settledᵒ; settleᵒ₂; settleᵒ₁; flat-gone; merged-pool; heading-∘; lanes-one; ghost-lift; startAt; pending-flags; queue-open; apart-unplant; lane-begin; module Restaged; module Settles)
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
    cl@record { sane = sn ; placed = pd ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr ; kept = kp }
    with lifts-split ρ (in-lanes πL) L
       | reads (subst (λ W → _ ≗ Observer.next W y) (trans (cong Here.obs (walk-⊕ ρ (in-lanes πL) top)) (walk-lane o op f fl (walk ρ top))) cd)
  ... | _ , lifts-lanes {bs = bs′} {l = l} {S = S₁} {as = as′} LL _ _ _ , Lρ | k₁ , f₁ , p₁ =
    rise kp (rises {sg′ = sends y} p₁ (one-lower ρ (one-lanes o)) (record
      { sane = sn ; placed = pd ; ctl = refl
      ; code = ≗-trans (f₁ same⊑ (At.val hp (Kit.live (laneOf o))))
                 (≗-trans (wk-same (Kit.when (At.val hp (Kit.live (laneOf o))) (Observer.next (wkObs same⊑ (Here.obs (walk ρ top))) y)))
                   (≗-trans (open-code (lane-live o LL)) (wk-same (Observer.next (Here.obs (walk ρ top)) y))))
      ; stack = sk
      ; lifted = _ , pm
                 , S , subst (λ S′ → Lifts hp ρ (U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S)
                             (lane-step o LL) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = sorted-⇝ so p₁ ; behind = bh ; lingers = lgr
      ; flags = done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl) ; kept = inj₁ refl }))
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

    fr-part : AllPairs _≢_ (names w₀) → At.part H′ t ≡ At.part H t
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
    fr-gone : AllPairs _≢_ (names w₀) → Gone H H′ w₀
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

    fr-done : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.outerDone fl) ≡ At.val H (FlatKit.Flat.outerDone fl)
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

    fr-revive : AllPairs _≢_ (names w₀) → is-just (At.part H′ w₀) ≡ true → is-just (At.part H w₀) ≡ true
    fr-revive fr j with At.part H w₀ in e
    ... | just _  = refl
    ... | nothing = ⊥-elim (true≢false (trans (sym j) (cong is-just (Gone.gone-part (fr-gone fr) here e))))

    -- No part left: what the flatMap leaves running alike beneath it, and a
    -- lane's ties seen only through lanes still on.
    fr-lingering : AllPairs _≢_ (names w₀) → At.part H′ w₀ ≡ nothing → Lingering H H′ w₀ w₀
    fr-lingering fr gn = record
      { ling-revive = λ j → ⊥-elim (true≢false (trans (sym j) (cong is-just gn)))
      ; ling-rested = λ {C} → pin-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} t so-al) (leftL ls (λ π → π)))
      ; ling-below  = λ lg → Linger.lg-flat H′ (λ e → ⊥-elim (true≢false (trans (sym (cong is-just e)) (cong is-just gn))))
                                (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                                (lanes-lg (lingersL-of H lg)) }
      where
        so-al = fr-so fr
        lane-al : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → Alike H H′ (names x)
        lane-al = fr-lane fr
        pt : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls x → At.part H′ x ≡ At.part H x
        pt {x = x} πL = part-alike H H′ x (lane-al πL)
        seL : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (πL : PathLanes ls x) → seenL H′ πL ≡ true → seenL H πL ≡ true
        seL = fr-seL fr
        leftL : ∀ {C} (ls′ : List (Lane h Δ B)) → (∀ {Δ′ A′} {x : Sub h Δ′ A′} → PathLanes ls′ x → PathLanes ls x)
              → At.leftoverL H′ {B = C} ls′ ≡ At.leftoverL H {B = C} ls′
        leftL []                   em = refl
        leftL (lane c′ k′ s ∷ ls′) em = cong₂ U.unionᶜ (leftover-alike H H′ s (lane-al (em (this-lane here)))) (leftL ls′ (λ π → em (next-lane π)))
        lanes-lg : LingersL H ls → LingersL H′ ls
        lanes-lg lL = record
          { poolsL = λ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls′ = ls₀} πL sn e → pinned-trans (LingersL.poolsL lL πL (seL πL sn) (trans (sym (pt πL)) e)) (pin-alike (pooled-from H H′ {op = op₀} {f = f₀} {fl = fl₀} {oc = oc₀} {k = k₀} {r = r₀} {pl = pl₀} {so = so₀} {ls = ls₀} (λ m → m) (lane-al πL)))
          ; restsL = λ {src = src₀} πL sn e pn pe → pinned-trans (LingersL.restsL lL πL (seL πL sn) (trans (sym (pt πL)) e) (trans (sym (pt (πL ⊕ᴸ in-source here))) pn) pe)
                                                    (pin-alike (leftover-from H H′ {B = ⊤} {x = src₀} (λ m → m) (lane-al (πL ⊕ᴸ in-source here)))) }

    module Wr (fs : AllPairs _≢_ (names T)) = Wrote H H′ ρ fr-off fr-mine fs
    module Sh (fs : AllPairs _≢_ (names T)) = Shift H H′ ρ fr-off fr-mine fs

    fr-owned : AllPairs _≢_ (names T) → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
    fr-owned fs = Sh.wr-owned fs (fr-gone (fresh-path ρ fs))

    fr-queue : AllPairs _≢_ (names T) → ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
    fr-queue _ = queue-keeps (keeps-trans (store-keeps H (Kit.live (laneOf o)) _ (λ ()) (λ ()) (λ ()) (λ ()))
                                           (store-keeps (unlive H (laneOf o)) (FlatKit.Flat.active fl) _ (λ ()) (λ ()) (λ ()) (λ ())))

    fr-lingers : AllPairs _≢_ (names T) → At.part H′ w₀ ≡ nothing → Ends H T → Lingers H T → Lingers H′ T
    fr-lingers fs gn en lg = subst (λ t′ → Lingers H′ t′) (plant-self ρ) (Sh.shift-lingers fs w₀ en (fr-lingering (fresh-path ρ fs) gn) lg)

    -- No flag moved: the done flag and the outer alike, a lane seen
    -- after only if before, every cell beneath a lane alike.
    fr-flags₀ : AllPairs _≢_ (names w₀) → ∀ {xs} → DoneBy H w₀ xs → DoneBy H′ w₀ xs
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

    fr-lifts : AllPairs _≢_ (names T) → ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
    fr-lifts fs = Wr.wr-lifts fs

    fr-opened : AllPairs _≢_ (names T) → ∀ b → opened H′ b ρ ≡ opened H b ρ
    fr-opened fs = Wr.wr-opened fs

    fr-fifo : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
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
            (heads-flat op G (At.part H t) (At.part H′ t) (At.partLanes H ls) (At.partLanes H′ ls) (At.val H (FlatKit.Flat.queue fl)) pl
              (subst (Heads q) (sym (merged-eq H op G (At.part H t) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀)) (Each.parts ev here refl e₀))
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

    fr-kernels : AllPairs _≢_ (names T) → At.val H (Kit.live (laneOf o)) ≡ true → Kernels H T → Kernels H′ T
    fr-kernels fs lv = Wr.wr-kernels fs (λ {E} {o′} → fr-holds (fresh-path ρ fs) lv {E} {o′}) (λ {E} {o′} → fr-gated (fresh-path ρ fs) lv {E} {o′}) (fr-spent (fresh-path ρ fs))

    fr-meaning : AllPairs _≢_ (names T) → Meaning H T → Meaning H′ T
    fr-meaning fs = Wr.wr-meaning fs (fr-fed (fresh-path ρ fs))

  -- A FLATMAP'S QUEUE WRITTEN: its own cell, read by its node alone;
  -- its children's parts and everything above it as they were.
  module Dequeued {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (ys : List A) where
    H′ = store H (FlatKit.Flat.queue fl) (lift ys)

    -- The queue the flatMap's own cell: its node's clauses read alike,
    -- the rest of the tree by the frame.
    w₀ = flatMapˢ op f fl oc k r pl t ls

    ns : List (Name h)
    ns = (_ , FlatKit.Flat.queue fl) ∷ []

    mine : All (_∈ᴸ names w₀) ns
    mine = there (there (here refl)) ∷ []

    module Wr (fs : AllPairs _≢_ (names T)) = Wrote H H′ ρ (off-store H (FlatKit.Flat.queue fl)) mine fs
    module Sh (fs : AllPairs _≢_ (names T)) = Shift H H′ ρ (off-store H (FlatKit.Flat.queue fl)) mine fs

    dq-queue : AllPairs _≢_ (names T) → ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
    dq-queue _ = queue-keeps (store-keeps H (FlatKit.Flat.queue fl) _ (λ ()) (λ ()) (λ ()) (λ ()))

    -- The queue no read of the node's own clauses.
    dq-alike : AllPairs _≢_ (names w₀) → Alike H H′ (flatReads fl oc k r t ls)
    dq-alike (a₀ ∷ _ ∷ a₂ ∷ _) j (here e)  = look-store H (FlatKit.Flat.queue fl) j (λ eq → lookupᴬ a₀ (there (here refl)) (sym (trans eq e)))
    dq-alike (a₀ ∷ _ ∷ a₂ ∷ _) j (there m) = look-store H (FlatKit.Flat.queue fl) j (lookupᴬ a₂ m)

    -- A queue's head taken off revives no part: the flatMap's part
    -- stood on the queue, its children's on names the queue is not.
    dq-gone : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Gone H H′ w₀
    dq-gone fr@(_ ∷ _ ∷ a₂ ∷ _) {y} {ys′} nq = record { gone-part = gp ; gone-live = lives-off {H = H} {H′ = H′} (off-store H (FlatKit.Flat.queue fl)) nl ; gone-held = store-held H (FlatKit.Flat.queue fl) }
      where
        gp : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path w₀ x → At.part H x ≡ nothing → At.part H′ x ≡ nothing
        gp here         e = ⊥-elim (merged-queued H op (λ a j → U.subscribe (f a) j) (At.part H t) (At.partLanes H ls) pl
                              (subst (λ qs → At.merged H op (λ a j → U.subscribe (f a) j) (At.part H t) (At.partLanes H ls) qs pl ≡ nothing) nq e))
        gp {x = x} (in-outer ψ) e = trans (part-alike H H′ x (λ j m → Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr) j (names-path ψ m))) e
        gp {x = x} (in-lanes ψ) e = trans (part-alike H H′ x (λ j m → Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr) j (lanes-path ψ m))) e
        nl : ∀ {Δ′ A′ i p c k′ tk} {s : Sub h Δ′ A′} → Path w₀ (takeWhileˢ i p c k′ tk s) → All (_≢_ (_ , Kit.live c)) ns
        nl (in-outer ψ) =
          (λ eq → lookupᴬ a₂ (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path ψ (here refl)))))))) (sym eq)) ∷ []
        nl (in-lanes ψ) =
          (λ eq → lookupᴬ a₂ (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) (lanes-path ψ (here refl)))))))) (sym eq)) ∷ []

    dq-owned : AllPairs _≢_ (names T) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′
             → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
    dq-owned fs nq = Sh.wr-owned fs (dq-gone (fresh-path ρ fs) nq)

    dq-part : AllPairs _≢_ (names w₀) → At.part H′ t ≡ At.part H t
    dq-part fr = part-alike H H′ t (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr))

    dq-lanes : AllPairs _≢_ (names w₀) → At.partLanes H′ ls ≡ At.partLanes H ls
    dq-lanes fr = partLanes-alike H H′ ls (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr))

    dq-done : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.outerDone fl) ≡ At.val H (FlatKit.Flat.outerDone fl)
    dq-done (_ ∷ a₁ ∷ _) = cong lower (look-store H (FlatKit.Flat.queue fl) (FlatKit.Flat.outerDone fl) (λ eq → lookupᴬ a₁ (here refl) (sym eq)))

    -- No flag of the node's moved: the done flag, the outer and the
    -- lanes alike.
    dq-flags₀ : AllPairs _≢_ (names w₀) → ∀ {xs} → DoneBy H w₀ xs → DoneBy H′ w₀ xs
    dq-flags₀ fr {xs} d =
      Flag.db-flat H′ {ns = xs} (flagged-moved H H′ {fl = fl} {so = t} (dq-done fr) (dq-part fr) (d here refl))
        (flags-alike H H′ (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)) (Flag.db-sub H d (in-outer here) refl))
        (flagsL-alike H H′ (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)) (Flag.dbL-of H d))

    -- A queue's head taken off: the node's parts and ties alike, its
    -- heads by what the queue is owed.
    dq-revive : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → is-just (At.part H′ w₀) ≡ true → is-just (At.part H w₀) ≡ true
    dq-revive fr nq j with At.part H w₀ in e
    ... | just _  = refl
    ... | nothing = ⊥-elim (true≢false (trans (sym j) (cong is-just (Gone.gone-part (dq-gone fr nq) here e))))

    dq-heading : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → ∀ {q}
               → (∀ {c c′} → At.part H w₀ ≡ just c → At.part H′ w₀ ≡ just c′ → Heads q c → Heads q c′) → Heading H H′ q w₀ w₀
    dq-heading fr nq {q} hd = record
      { head-revive = dq-revive fr nq
      ; head-told   = λ i e₀ e′ m →
          ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H t) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀))
            (≡-⊆ (cong₂ (λ o L → untoldᴹ i o ++ untoldᴸ i L ++ untold i pl) (dq-part fr) (dq-lanes fr))
              (≡-⊆ (cong (untold i) (sym (merged-eq H′ op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl e′))) m))
      ; head-below  = λ ev → Build.each-flat H′ (Heads q) {op = op} {f} {fl} {oc} {k} {r} {pl} {so = t} {ls}
                               (λ x → hd (proj₂ (j₀ x)) x (Each.parts ev here refl (proj₂ (j₀ x))))
                               (λ x → Each.pools ev here refl (proj₂ (j₀ x)))
                               (each-alike H H′ so-al (each-sub ev (in-outer here) refl))
                               (eachL-alike H H′ ls-al (eachL-of H ev)) }
      where
        G = λ a j → U.subscribe (f a) j
        so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        j₀ : ∀ {c} → At.part H′ w₀ ≡ just c → Σ (U.Node Δ B) λ b → At.part H w₀ ≡ just b
        j₀ x = just-of (dq-revive fr nq (cong is-just x))

    dq-holds : AllPairs _≢_ (names w₀) → ∀ {E o} → At.Holds H w₀ E o → At.Holds H′ w₀ E o
    dq-holds fr {E} {o} = Heaps.holds-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike fr) {E} {o}

    dq-gated : AllPairs _≢_ (names w₀) → At.Gated H w₀ → At.Gated H′ w₀
    dq-gated fr = Heaps.gated-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike fr)

    dq-spent : AllPairs _≢_ (names w₀) → At.Spent H w₀ → At.Spent H′ w₀
    dq-spent fr = Heaps.spent-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike fr)

    dq-fed : AllPairs _≢_ (names w₀) → ∀ ν → At.Fed H w₀ ν → At.Fed H′ w₀ ν
    dq-fed fr = Heaps.fed-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike fr)

    dq-opened : AllPairs _≢_ (names T) → ∀ b → opened H′ b ρ ≡ opened H b ρ
    dq-opened fs = Wr.wr-opened fs

    dq-lifts : AllPairs _≢_ (names T) → ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
    dq-lifts fs = Wr.wr-lifts fs

    dq-kernels : AllPairs _≢_ (names T) → Kernels H T → Kernels H′ T
    dq-kernels fs = Wr.wr-kernels fs (λ {E} {o} → dq-holds (fresh-path ρ fs) {E} {o}) (λ _ → dq-gated (fresh-path ρ fs)) (dq-spent (fresh-path ρ fs))

    dq-meaning : AllPairs _≢_ (names T) → Meaning H T → Meaning H′ T
    dq-meaning fs = Wr.wr-meaning fs (dq-fed (fresh-path ρ fs))

  -- The machine at a new heap running a callback, the call's rest owed
  -- past it.
  resend : (m₁ : Mach) → Heapᴹ (Conf.world (Mach.conf m₁)) → {w : World} → w ⊑ Conf.world (Mach.conf m₁) → Stack w ⊤
         → Act (Conf.world (Mach.conf m₁)) ⊤ → Act (Conf.world (Mach.conf m₁)) ⊤ → Mach
  resend (mach ⟨ _ , q , _ ⟩ clk ts bs td lg en mk) H ϑ K a n = mach ⟨ H , q , run a same⊑ (push (rest n) ϑ K) ⟩ clk ts bs td lg en mk

  -- A queue read whose continuations agree, case by case.
  readF-cases : ∀ {w X} {r : Ref w (fifo X)} {k k′ : List X → Act w ⊤} → (∀ x → k x ≗ k′ x) → Kit.readF r k ≗ Kit.readF r k′
  readF-cases e = readRef≗ refl λ σ x → wk≗ σ (e x)

  -- A dequeue at the queue it reads: empty, the settle; else the head's
  -- lane begun.
  dequeueOf : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
            → Path T (flatMapˢ op f fl oc k r pl u ls) → List A → Act h ⊤
  dequeueOf {op = op} {f} {fl} ρ []       = Canon.Flat′.settle op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl
  dequeueOf {fl = fl}          ρ (y ∷ ys) = writeRef (FlatKit.Flat.queue fl) ys (startAt ρ y)

  dequeue-cases : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) → dequeueAt ρ ≗ Kit.readF (FlatKit.Flat.queue fl) (dequeueOf ρ)
  dequeue-cases ρ = readF-cases λ where
    []      → ≗-refl (dequeueOf ρ [])
    (y ∷ ys) → ≗-refl (dequeueOf ρ (y ∷ ys))

  -- What a flatMap's settle tests, read off a heap.
  settleᵇ : ∀ {h A} → Heapᴹ h → FlatKit.Flat A h → Bool
  settleᵇ H fl = At.val H (FlatKit.Flat.outerDone fl) ∧ (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val H (FlatKit.Flat.queue fl))

  -- Whether a flatMap's ghost ends with a lane: its outer gone, no lane
  -- beside it, nothing queued.
  settledᵍ : ∀ {Γ A B} → Maybe (U.Node Γ A) → List (U.Node Γ B) → List (U.Node Γ B) → List A → Bool
  settledᵍ o bs as qs = is-nothing o ∧ null bs ∧ null as ∧ null qs

  settled-nil : ∀ {Γ A B} (o : Maybe (U.Node Γ A)) (bs as : List (U.Node Γ B)) (qs : List A)
              → settledᵍ o bs as qs ≡ true → o ≡ nothing × bs ≡ [] × as ≡ [] × qs ≡ []
  settled-nil nothing  []      []      []      refl = refl , refl , refl , refl
  settled-nil (just _) _       _       _       ()
  settled-nil nothing  (_ ∷ _) _       _       ()
  settled-nil nothing  []      (_ ∷ _) _       ()
  settled-nil nothing  []      []      (_ ∷ _) ()

  -- Something left: the flatMap held.
  merged-held : ∀ {h} (G : Heapᴹ h) {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) (bs as : List (U.Node Γ B)) (qs : List A) pl
              → settledᵍ o bs as qs ≡ false → is-just (At.merged G op g o (bs ++ as) qs pl) ≡ true
  merged-held G op g (just _) _       _       _       pl _  = refl
  merged-held G op g nothing  (_ ∷ _) _       _       pl _  = refl
  merged-held G op g nothing  []      (_ ∷ _) _       pl _  = refl
  merged-held G op g nothing  []      []      (_ ∷ _) pl _  = refl
  merged-held G op g nothing  []      []      []      pl ()

  -- A lane's end with nothing beside it: the flatMap's own end.
  lane-end : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) {o bs as qs} l c pl → o ≡ nothing → bs ≡ [] → as ≡ [] → qs ≡ []
           → U.laneˢ op g o bs l (U.endˢ c) as qs pl ≡ U.endˢ c
  lane-end op g l c pl refl refl refl refl = refl

  -- A lane's end with the outer or a lane beside it, nothing queued: the
  -- pool takes the lane's rest.
  lane-open : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) bs l c as pl → settledᵍ o bs as [] ≡ false
            → U.laneˢ op g o bs l (U.endˢ c) as [] pl ≡ U.skipˢ c (U.flatMapᶜ op g o (bs ++ as) [] (U.unionᶜ pl (U.restᶜ l)))
  lane-open op g nothing  []      l c []      pl ()
  lane-open op g nothing  []      l c (_ ∷ _) pl _ = refl
  lane-open op g nothing  (_ ∷ _) l c []      pl _ = refl
  lane-open op g nothing  (_ ∷ _) l c (_ ∷ _) pl _ = refl
  lane-open op g (just _) []      l c []      pl _ = refl
  lane-open op g (just _) []      l c (_ ∷ _) pl _ = refl
  lane-open op g (just _) (_ ∷ _) l c []      pl _ = refl
  lane-open op g (just _) (_ ∷ _) l c (_ ∷ _) pl _ = refl

  merged-live : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) bs as pl → settledᵍ o bs as [] ≡ false
              → At.merged G op g o (bs ++ as) [] pl ≡ just (U.flatMapᶜ op g o (bs ++ as) [] pl)
  merged-live G op g nothing  []      []      pl ()
  merged-live G op g nothing  []      (_ ∷ _) pl _ = refl
  merged-live G op g nothing  (_ ∷ _) as      pl _ = refl
  merged-live G op g (just _) bs      as      pl _ = refl

  -- At a lane's close, the done flag reads the outer's part gone: the
  -- call leaves unset only flags above the flatMap and inside the lane.
  lane-done : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
              {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
              (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) {ks}
            → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks)
            → At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.outerDone fl) ≡ is-nothing (At.part (Conf.heap (Mach.conf m₁)) t)
  lane-done {m₁ = m₁} {T = T} {fl = fl} {oc} {k} {t = t} ρ {πL} _ cl with Calling.lifted cl
  ... | _ , _ , L , _ with lifts-split ρ (in-lanes πL) L
  ...   | _ , _ , Lρ =
    proj₂ (subst (DoneBy (Conf.heap (Mach.conf m₁)) T) (outers-⊕ ρ (in-lanes πL)) (Calling.flags cl) ρ (lifts-seen Lρ))
          (λ m → [ (λ a → outers-apart ρ fs a (there (here refl))) , (λ b → lookupᴬ (apart-r (flatNames fl) (fresh-path ρ fs) (there (here refl)))
                     (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names t) (outersL-in πL b))))) refl) ]′ (++⁻ (outers ρ) m))
    where fs = Books.fresh (Calling.books cl)

  null-++ : ∀ {a} {X : Set a} (xs ys : List X) → null (xs ++ ys) ≡ null xs ∧ null ys
  null-++ []      ys = refl
  null-++ (_ ∷ _) ys = refl

  -- A freed slot's settle tests what the ghost's lane end tests: the
  -- done flag, the outer's part gone; the count, the lanes beside it.
  lane-settles : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                 {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) {ks}
               → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks)
               → ∀ {s bs S as} → LiftsLane (Conf.heap (Mach.conf m₁)) πL s bs S as
               → settleᵇ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) fl
                 ≡ settledᵍ (At.part (Conf.heap (Mach.conf m₁)) t) bs as (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.queue fl))
  lane-settles {m₁ = m₁} {T = T} {fl = fl} {t = t} {ls = ls} ρ o cl {bs = bs} {as = as} LL =
    cong₂ _∧_ (trans (Freed.fr-done hp ρ o (fresh-path ρ fs)) (lane-done ρ o cl))
      (trans (cong₂ _∧_ beside (cong null (queue-freed hp (laneOf o) fl))) (∧-assoc (null bs) (null as) _))
    where
      hp = Conf.heap (Mach.conf m₁)
      H₂ = freed hp (laneOf o) fl
      fs = Books.fresh (Calling.books cl)
      beside : (At.val H₂ (FlatKit.Flat.active fl) ≡ᵇ 0) ≡ null bs ∧ null as
      beside = trans (Settles.active-lanes H₂ ρ (Freed.fr-kernels hp ρ o fs (lane-live o LL) (Calling.kernels cl)))
                     (trans (cong null (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL)) (null-++ bs as))

  -- A freed slot settling short of the end, the outer or a lane left,
  -- nothing queued: the pool takes the lane's rest, the ghost past the
  -- lane's skip.
  lane-ghost : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) → AllPairs _≢_ (names T)
             → ∀ {g q S bs l S₁ as} → Sane [] g → Placed g []
             → LiftsLane H πL (U.endˢ q) bs S₁ as
             → settledᵍ (At.part H t) bs as (At.val H (FlatKit.Flat.queue fl)) ≡ false
             → At.val (freed H (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ []
             → Lifts H ρ (U.laneˢ op (λ a i → U.subscribe (f a) i) (At.part H t) bs l S₁ as (At.val H (FlatKit.Flat.queue fl)) pl) S
             → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part (freed H (laneOf o) fl) (Restaged.T′ (freed H (laneOf o) fl) ρ (U.unionᶜ pl (U.restᶜ l))) ≡ just g″
               × Sane [] g″ × Placed g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
  lane-ghost H {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} ρ o fs {q = q} {bs = bs} {l} {S₁} {as} sn pd LL st e₀ L sg =
    ghost-lift H H₂ ρ (flatMapˢ op f fl oc k r pl′ t ls) fs (Freed.fr-off H ρ o) (Freed.fr-mine H ρ o) {κ = []}
      (subst (λ s → Lifts H ρ s _) lane-eq L) node alike sn pd sg
    where
      H₂  = freed H (laneOf o) fl
      G   = λ a i → U.subscribe (f a) i
      pl′ = U.unionᶜ pl (U.restᶜ l)
      fr  = fresh-path ρ fs
      eH  : At.val H (FlatKit.Flat.queue fl) ≡ []
      eH  = trans (sym (Freed.fr-fifo H ρ o fr)) e₀
      st′ : settledᵍ (At.part H t) bs as [] ≡ false
      st′ = subst (λ qs → settledᵍ (At.part H t) bs as qs ≡ false) eH st
      lane-eq : U.laneˢ op G (At.part H t) bs l S₁ as (At.val H (FlatKit.Flat.queue fl)) pl ≡ U.skipˢ q (U.flatMapᶜ op G (At.part H t) (bs ++ as) [] pl′)
      lane-eq = trans (cong₂ (λ S′ qs → U.laneˢ op G (At.part H t) bs l S′ as qs pl) (lane-step o LL) eH)
                      (lane-open op G (At.part H t) bs l q as pl st′)
      node : At.part H₂ (flatMapˢ op f fl oc k r pl′ t ls) ≡ just (U.flatMapᶜ op G (At.part H t) (bs ++ as) [] pl′)
      node = trans (cong₂ (λ x ys → At.merged H₂ op G x ys (At.val H₂ (FlatKit.Flat.queue fl)) pl′) (Freed.fr-part H ρ o fr) (Freed.fr-lanes H ρ o fr LL))
                   (trans (cong (λ qs → At.merged H₂ op G (At.part H t) (bs ++ as) qs pl′) e₀)
                          (merged-live H₂ op G (At.part H t) bs as pl′ st′))

  -- A lane's end, its pool taking the lane's last ghost rested, which is
  -- what the lane still runs: with nothing queued, and with the queue's
  -- head taken off.  The heads: the pool taking what the lane ran heads
  -- where the lane did; the queue's head taken off, the flatMap heads as
  -- it did.
  -- DEAD ROUTE: a frame, the sibling moves' `Heaps` route.  The pool gains
  --   `l`'s rest, and `lifts-lanes` leaves `l` free, tied to the heap only
  --   through its earliest: no `Alike` reaches it.
  -- DEAD ROUTE: `heads-flat` for the queue's head taken off: it holds the
  --   queue fixed.
  module Settling {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks bs′ l S′ as′ S}
                  (cl : Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks))
                  (L : Lifts (Conf.heap (Mach.conf m₁)) ρ (U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part (Conf.heap (Mach.conf m₁)) t) bs′ l S′ as′
                                                         (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.queue fl)) pl) S)
                  (sg : U.step g ≡ S) where
    H   = Conf.heap (Mach.conf m₁)
    q   = Conf.pos (Mach.conf m₁)
    H₂  = freed H (laneOf o) fl
    pl′ = U.unionᶜ pl (U.restᶜ l)
    w₀  = flatMapˢ op f fl oc k r pl t ls
    v   = flatMapˢ op f fl oc k r pl′ t ls
    fs  = Books.fresh (Calling.books cl)
    fr  = fresh-path ρ fs

    postulate
      settle-told     : ∀ {A′} (i : A′ ∈ᴸ Δ) {b₀} → At.part H₂ w₀ ≡ just b₀ → untold i pl′ ⊆ᴾ untold i b₀
      settle-heads    : ∀ {c} → At.part H₂ w₀ ≡ just c → Heads q pl → Heads q pl′
      settle-lingering : Lingering H H₂ w₀ v
      next-heads      : ∀ ys {c c′} → At.part H₂ w₀ ≡ just c → At.part (Dequeued.H′ H₂ ρ ys) w₀ ≡ just c′ → Heads q c → Heads q c′
      next-lingering  : ∀ ys → Lingering H (Dequeued.H′ H₂ ρ ys) w₀ v

    settle-heading : Heading H H₂ q w₀ v
    settle-heading = heading-∘ (Freed.fr-heading H ρ o fr) (Restaged.repool-heading H₂ ρ pl′ (λ {A′} i {b₀} → settle-told {A′} i {b₀}) settle-heads)

    settle-lingers : Lingers H₂ (Restaged.T′ H₂ ρ pl′)
    settle-lingers = Freed.Sh.shift-lingers H ρ o fs v (ended-past cl) settle-lingering (Calling.lingers cl)

    -- The queue's head taken off needs it there to take.
    next-heading : ∀ ys {y ys′} → At.val H₂ (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Heading H (Dequeued.H′ H₂ ρ ys) q w₀ w₀
    next-heading ys nq = heading-∘ (Freed.fr-heading H ρ o fr) (Dequeued.dq-heading H₂ ρ ys fr nq (next-heads ys))

    next-lingers : ∀ ys → Lingers (Dequeued.H′ H₂ ρ ys) (Restaged.T′ (Dequeued.H′ H₂ ρ ys) ρ pl′)
    next-lingers ys = Shift.shift-lingers H (Dequeued.H′ H₂ ρ ys) ρ (off-++ {H = H} {H₁ = H₂} {H₂ = Dequeued.H′ H₂ ρ ys} (Freed.ns H ρ o) (Freed.fr-off H ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                        (all-++⁺ (Freed.fr-mine H ρ o) (Dequeued.mine H₂ ρ ys)) fs v (ended-past cl) (next-lingering ys) (Calling.lingers cl)

  -- A freed slot with nothing queued: the flatMap's settle read.  Its
  -- outer done and no lane left, its end one operator up, the call's
  -- rest owed in a frame; else the pool.
  lane-settle : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks}
                (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (closes ks))
              → At.val (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ []
              → ∀ {a n} → m₁ ⇝ resend m₁ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (Calling.ϑ cl) (Calling.K cl) a n
              → a ≗ dequeueOf ρ [] → n ≗ ⟦ ks ⟧ᶜ → Called st m₁ (ρ ⊕ in-lanes πL)
  lane-settle st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {op = op} {f} {fl} {oc} {k} {r} {po} {t = t} {ls} ρ πL o {ks}
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = gu , S , L , sg , hl ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; kept = kp } eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L | reads {hp = freed hp (laneOf o) fl} ea
  ... | _ , lifts-lanes {bs = bs′} {l = l} {as = as′} LL _ _ _ , Lρ | k₁ , f₁ , p₁
    with reads {hp = freed hp (laneOf o) fl}
           (≗-trans (f₁ same⊑ (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.outerDone fl)))
                    (wk-same (settleᵒ₁ (Here.obs (walk ρ top)) fl (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.outerDone fl)))))
  ...   | k₂ , f₂ , p₂
    with reads {hp = freed hp (laneOf o) fl}
           (≗-trans (f₂ same⊑ (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.active fl)))
                    (wk-same (settleᵒ₂ (Here.obs (walk ρ top)) fl (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.outerDone fl))
                                       (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.active fl)))))
  ...     | k₃ , f₃ , p₃
    with settleᵇ (freed hp (laneOf o) fl) fl in eq
  ...       | true =
    rise kp (rises {sg′ = closes []} path (one-lower ρ (one-lanes o)) (record
      { sane = sn ; placed = pd ; ctl = refl
      ; code = ≗-trans e₃ (≗-trans (open-code {m = Observer.complete O} eq) (seq-done _))
      ; stack = stk
      ; lifted = flat-gone H₂ {op = op} {f} {fl} {oc} {k} {r} {po} {u = t} {ls} (trans (Freed.fr-part hp ρ o (fresh-path ρ fs)) eo)
                           (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (cong₂ _++_ ebs eas)) eq₀
               , S , Freed.fr-lifts hp ρ o fs (subst (λ s′ → Lifts hp ρ s′ S) (lane-end op G l q po eo ebs eas eqs)
                                              (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S)
                                                     (lane-step o LL) Lρ)) , sg
               , healed-off hp H₂ ρ fs (Heaps.keep hp H₂ (Freed.fr-off hp ρ o) (lookupᴬ (Freed.fr-mine hp ρ o)))
                            (trans (cong₂ (λ o′ L′ → At.merged hp op G o′ L′ (At.val H₂ (FlatKit.Flat.queue fl)) po) (Freed.fr-part hp ρ o (fresh-path ρ fs))
                                          (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (sym (lanes-gone hp o LL gu))))
                                   (cong (λ Q → At.merged hp op G (At.part hp t) (At.partLanes hp ls) Q po) (queue-freed hp (laneOf o) fl)))
                            (healed-split ρ (in-lanes πL) hl)
      ; owned = owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o fs ow)
      ; kernels = Freed.fr-kernels hp ρ o fs (lane-live o LL) kn ; meaning = Freed.fr-meaning hp ρ o fs mn ; queue = Freed.fr-queue hp ρ o fs qu
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Freed.fr-behind hp ρ o fs (tells-past cl) (ended-past cl) bh
      ; lingers = Freed.fr-lingers hp ρ o fs (flat-gone H₂ {op = op} {f} {fl} {oc} {k} {r} {po} {u = t} {ls} (trans (Freed.fr-part hp ρ o (fresh-path ρ fs)) eo)
                                             (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (cong₂ _++_ ebs eas)) eq₀) (ended-past cl) lgr
      ; flags = Freed.fr-flags hp ρ o fs (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl)) ; kept = inj₁ refl }))
    where
      H₂   = freed hp (laneOf o) fl
      O    = Here.obs (walk ρ top)
      G    = λ a j → U.subscribe (f a) j
      path = ⇝-trans p (⇝-trans p₁ (⇝-trans p₂ p₃))
      e₃   = ≗-trans (f₃ same⊑ (At.val H₂ (FlatKit.Flat.queue fl)))
               (wk-same (settledᵒ O (At.val H₂ (FlatKit.Flat.outerDone fl)) (At.val H₂ (FlatKit.Flat.active fl)) (At.val H₂ (FlatKit.Flat.queue fl))))
      stk  = restAs ks (≗-trans (wk-same n) eks) sk
      nl   = settled-nil (At.part hp t) bs′ as′ (At.val hp (FlatKit.Flat.queue fl)) (trans (sym (lane-settles ρ o cl LL)) eq)
      eo   = proj₁ nl
      ebs  = proj₁ (proj₂ nl)
      eas  = proj₁ (proj₂ (proj₂ nl))
      eqs  = proj₂ (proj₂ (proj₂ nl))
  ...       | false
    with lane-ghost hp ρ o fs sn pd LL (trans (sym (lane-settles ρ o cl LL)) eq) eq₀ Lρ sg
  ...         | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; tree = Restaged.T′ H₂ ρ pl′
        ; ctlAs = runAs (Restaged.pool-calls H₂ ρ pl′ []) ec (Restaged.pool-stack H₂ ρ pl′ stk)
        ; meets = pg
        ; owned′ = owned-to (Restaged.pool-owned H₂ ρ pl′ stk [] ec (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o fs ow)))
        ; kernels = Restaged.pool-kernels H₂ ρ pl′ (Freed.fr-kernels hp ρ o fs (lane-live o LL) kn)
        ; meaning = Restaged.pool-meaning H₂ ρ pl′ (Freed.fr-meaning hp ρ o fs mn)
        ; queue = Restaged.pool-queue H₂ ρ pl′ (Freed.fr-queue hp ρ o fs qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked H₂ ρ pl′ clk stk (proj₁ ck , proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind′ = Eaching.each-to _ _ (Freed.Sh.shift-behind hp ρ o fs v (tells-past cl) (ended-past cl) (Settling.settle-heading ρ πL o cl Lρ sg) bh)
        ; lingers′ = Lingering.lingers-to _ (Settling.settle-lingers ρ πL o cl Lρ sg)
        ; flags = let-go H₂ (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs) (lifts-seen (lifts-planted ρ v (Freed.fr-lifts hp ρ o fs Lρ))) ju
                    (subst (DoneBy H₂ (plant ρ v)) (sym (outers-planted ρ v)) (Freed.fr-shift hp ρ o fs pl′ rv (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl)))) })
      , passed ag pp)
    where
      H₂   = freed hp (laneOf o) fl
      O    = Here.obs (walk ρ top)
      pl′  = U.unionᶜ po (U.restᶜ l)
      v    = flatMapˢ op f fl oc k r pl′ t ls
      G′   = λ a j → U.subscribe (f a) j
      rv   = λ j → Freed.fr-revive hp ρ o (fresh-path ρ fs)
                     (trans (sym (merged-pool H₂ op G′ (At.part H₂ t) (At.partLanes H₂ ls) (At.val H₂ (FlatKit.Flat.queue fl)) po pl′)) j)
      ju   = subst₂ (λ o′ L → is-just (At.merged H₂ op G′ o′ L (At.val H₂ (FlatKit.Flat.queue fl)) pl′) ≡ true)
                    (sym (Freed.fr-part hp ρ o (fresh-path ρ fs))) (sym (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL))
                    (subst (λ Q → is-just (At.merged H₂ op G′ (At.part hp t) (bs′ ++ as′) Q pl′) ≡ true) (sym (Freed.fr-fifo hp ρ o (fresh-path ρ fs)))
                           (merged-held H₂ op G′ (At.part hp t) bs′ as′ (At.val hp (FlatKit.Flat.queue fl)) pl′ (trans (sym (lane-settles ρ o cl LL)) eq)))
      path = ⇝-trans p (⇝-trans p₁ (⇝-trans p₂ p₃))
      e₃   = ≗-trans (f₃ same⊑ (At.val H₂ (FlatKit.Flat.queue fl)))
               (wk-same (settledᵒ O (At.val H₂ (FlatKit.Flat.outerDone fl)) (At.val H₂ (FlatKit.Flat.active fl)) (At.val H₂ (FlatKit.Flat.queue fl))))
      stk  = restAs ks (≗-trans (wk-same n) eks) sk
      ec   = ≗-trans (≗-trans e₃ (shut-code eq)) (Restaged.pool-code H₂ ρ pl′ [])

  -- A freed slot with a value queued: the queue's head taken, its lane
  -- begun where the end was.
  lane-next : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
              {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
              (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks}
              (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (closes ks))
            → ∀ {y ys} → At.val (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ y ∷ ys
            → ∀ {a n} → m₁ ⇝ resend m₁ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (Calling.ϑ cl) (Calling.K cl) a n
            → a ≗ dequeueOf ρ (y ∷ ys) → n ≗ ⟦ ks ⟧ᶜ → Hopped st m₁
  lane-next st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {f} {fl} {oc} {k} {r} {po} {t = t} {ls} ρ πL o {ks}
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = gn , S , L , sg , _ ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; kept = kp } {y} {ys} eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L | writes {hp = freed hp (laneOf o) fl} ea
  ... | _ , lifts-lanes {bs = bs′} {l = l} {as = as′} LL ee lf pb , Lρ | n′ , e′ , p′ =
    hopped-pre (⇝-trans p p′) (lane-begin st (record
      { sane = sn ; placed = pd ; ctl = refl ; code = e′
      ; opens = trans (Dequeued.dq-opened H₂ ρ ys fs true)
                  (trans (Freed.fr-opened hp ρ o fs true) (one-open hp o (trans (sym (opened-⊕ hp true ρ (in-lanes πL))) (calling-open (ρ ⊕ in-lanes πL) cl))))
      ; stack = stk
      ; lifted = S , L₇ , sg
      ; owned = Dequeued.dq-owned H₂ ρ ys fs eq₀ (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o fs ow))
      ; kernels = Dequeued.dq-kernels H₂ ρ ys fs (Freed.fr-kernels hp ρ o fs (lane-live o LL) kn)
      ; meaning = Dequeued.dq-meaning H₂ ρ ys fs (Freed.fr-meaning hp ρ o fs mn)
      ; queue = Dequeued.dq-queue H₂ ρ ys fs (Freed.fr-queue hp ρ o fs qu)
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (⇝-trans p p′)
      ; behind = subst (λ t′ → Each H₃ (Heads q) t′) (plant-self ρ)
                   (Shift.shift-behind hp H₃ ρ (off-++ {H = hp} {H₁ = H₂} {H₂ = H₃} (Freed.ns hp ρ o) (Freed.fr-off hp ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                                       (all-++⁺ (Freed.fr-mine hp ρ o) (Dequeued.mine H₂ ρ ys)) fs w₀ (tells-past cl) (ended-past cl) (Settling.next-heading ρ πL o cl Lρ sg ys eq₀) bh)
      ; lingers = Settling.next-lingers ρ πL o cl Lρ sg ys
      ; flags = let-go H₃ (planted ρ P₀) (pairs-r (names w₀) (apart-unplant ρ fs)) (trans (seen-planted H₃ ρ P₀) (lifts-seen L₇)) refl
                  (subst (DoneBy H₃ (plant ρ P₀)) (sym (outers-planted ρ P₀))
                    (Dequeued.Sh.shift-flags H₂ ρ ys fs P₀ {ns₀ = []} (λ ()) (λ _ → ju₂) (λ _ → pending-flags H₃) (subst (DoneBy H₂ _) (sym (++-identityʳ (outers ρ))) d₂)))
      ; inner = Dequeued.dq-flags₀ H₂ ρ ys (fresh-path ρ fs) (Flag.db-sub H₂ (let-go H₂ ρ fs s₂ ju₂ d₂) ρ s₂) }))
    where
      H₂  = freed hp (laneOf o) fl
      H₃  = Dequeued.H′ H₂ ρ ys
      w₀  = flatMapˢ op f fl oc k r po t ls
      G   = λ a j → U.subscribe (f a) j
      pl′ = U.unionᶜ po (U.restᶜ l)
      stk = restAs ks (≗-trans (wk-same n) eks) sk
      F   = λ (x : Maybe (U.Node _ _)) (zs : List (U.Node _ _)) (qs : List _) → U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op G x (G y (q ++ [ ix 1 ]) ∷ zs) qs pl′)
      L₁  = subst (λ qs → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l (U.endˢ q) as′ qs po) S)
                  (trans (sym (queue-freed hp (laneOf o) fl)) eq₀)
                  (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S) (lane-step o LL) Lρ)
      L₄  = Dequeued.dq-lifts H₂ ρ ys fs (Freed.fr-lifts hp ρ o fs L₁)
      L₅  = subst (λ x → Lifts H₃ ρ (F x (bs′ ++ as′) ys) S) (sym (trans (Dequeued.dq-part H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-part hp ρ o (fresh-path ρ fs)))) L₄
      L₆  = subst (λ zs → Lifts H₃ ρ (F (At.part H₃ t) zs ys) S) (sym (trans (Dequeued.dq-lanes H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL))) L₅
      L₇  = subst (λ qs → Lifts H₃ ρ (F (At.part H₃ t) (At.partLanes H₃ ls) qs) S) (sym (queue-stored H₂ fl ys)) L₆
      P₀  = pendingˢ (f y) (q ++ [ ix 1 ])
      d₂  = Freed.fr-flags hp ρ o fs (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl))
      s₂  = lifts-seen (Freed.fr-lifts hp ρ o fs L₁)
      ju₂ = subst (λ Q → is-just (At.merged H₂ op G (At.part H₂ t) (At.partLanes H₂ ls) Q po) ≡ true) (sym eq₀)
                  (queue-open H₂ op G (At.part H₂ t) (At.partLanes H₂ ls) y ys po)

  -- A freed slot's queue read, by what it holds.
  lane-queue : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
               {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks}
               (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (closes ks))
             → ∀ qs → At.val (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ qs
             → ∀ {a n} → m₁ ⇝ resend m₁ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (Calling.ϑ cl) (Calling.K cl) a n
             → a ≗ dequeueOf ρ qs → n ≗ ⟦ ks ⟧ᶜ → Called st m₁ (ρ ⊕ in-lanes πL)
  lane-queue st ρ πL o cl []       e p ea eks = lane-settle st ρ πL o cl e p ea eks
  lane-queue st ρ πL o cl (y ∷ ys) e p ea eks = landed (lane-next st ρ πL o cl e p ea eks)

  -- A lane's freed slot handed on: the queue read.
  lane-dequeue : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                 {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks}
                 (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (closes ks))
               → ∀ {a n} → m₁ ⇝ resend m₁ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) (Calling.ϑ cl) (Calling.K cl) a n
               → a ≗ dequeueAt ρ → n ≗ ⟦ ks ⟧ᶜ → Called st m₁ (ρ ⊕ in-lanes πL)
  lane-dequeue st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {fl = fl} ρ πL o cl@record { ctl = refl } p ea eks
    with reads {hp = freed hp (laneOf o) fl} (≗-trans ea (dequeue-cases ρ))
  ... | k₁ , f₁ , p₁ = lane-queue st ρ πL o cl _ refl (⇝-trans p p₁)
          (≗-trans (f₁ same⊑ _) (wk-same (dequeueOf ρ (At.val (freed hp (laneOf o) fl) (FlatKit.Flat.queue fl))))) eks

  -- A lane ended: its guard read open, its cut dropped, the count down,
  -- the refill sent.
  close-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {ks}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (closes ks) → Called st m₁ (ρ ⊕ in-lanes πL)
  close-lanes st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {f} {fl} {oc} {k} {r} {po} {t = t} {ls} ρ πL o {ks}
    cl@record { ctl = refl ; code = cd ; lifted = _ , _ , L , _ ; kernels = kn }
    with lifts-split ρ (in-lanes πL) L
       | reads (subst (λ W → _ ≗ (Observer.complete W >>ᴬ ⟦ ks ⟧ᶜ)) (trans (cong Here.obs (walk-⊕ ρ (in-lanes πL) top)) (walk-lane o op f fl (walk ρ top))) cd)
  ... | _ , lifts-lanes LL _ _ _ , _ | k₁ , f₁ , p₁
    with writes (≗-trans (f₁ same⊑ (At.val hp (Kit.live (laneOf o))))
                   (bind≗ (≗-trans (wk-same (Kit.when (At.val hp (Kit.live (laneOf o))) (laneEnd ρ o))) (open-code (lane-live o LL))) λ _ → wk-same ⟦ ks ⟧ᶜ))
  ...   | n₂ , e₂ , p₂ with reads {hp = unlive hp (laneOf o)} e₂
  ...     | k₃ , f₃ , p₃ with writes {hp = unlive hp (laneOf o)} (f₃ same⊑ (At.val (unlive hp (laneOf o)) (FlatKit.Flat.active fl)))
  ...       | n₄ , e₄ , p₄
    with reads {hp = freed hp (laneOf o) fl} (≗-trans e₄ (bind≗ (wk-same (refillAt ρ)) λ _ → wk-same ⟦ ks ⟧ᶜ))
  ...         | k₅ , f₅ , p₅
    with sendStep {hp = freed hp (laneOf o) fl}
           (at-val {F = k₅ same⊑} (trans (refill-freed hp (laneOf o) fl) (proj₁ (holds-walk hp ρ top (Kernels.holds kn)))) (f₅ same⊑ (just r)))
  ...           | n₆ , e₆ , p₆ =
    lane-dequeue st ρ πL o cl (⇝-trans p₁ (⇝-trans p₂ (⇝-trans p₃ (⇝-trans p₄ (⇝-trans p₅ p₆)))))
                 (at-val {F = λ c → Callbacks.onNext c tt} (slot-freed hp (laneOf o) fl r)
                         (proj₁ (proj₁ (proj₂ (holds-walk hp ρ top (Kernels.holds kn)))) tt))
                 (≗-trans e₆ (wk-same ⟦ ks ⟧ᶜ))

  -- A signal out of a lane.
  call-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
               {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {sg : Signal T B}
             → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) sg → Called st m₁ (ρ ⊕ in-lanes πL)
  call-lanes st ρ πL o {sends _}  cl = climb-lanes st ρ πL o cl
  call-lanes st ρ πL o {closes _} cl = close-lanes st ρ πL o cl
