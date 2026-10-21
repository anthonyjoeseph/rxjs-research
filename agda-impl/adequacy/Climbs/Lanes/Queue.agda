{-# OPTIONS --guardedness #-}

module adequacy.Climbs.Lanes.Queue where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (_≡ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; skip; Pos; Timeline; ix)
open import denotation.MonotonicList using (Agree)
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
open import adequacy.Sane using (Sane)
open import adequacy.Deep using (Deep)
open import adequacy.Placed.Order using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Bool.Properties using (∧-assoc)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Ghost.Paths using (module GhostingPaths)
open import adequacy.Gapped using (module Gapping)
open import adequacy.Lift using (module Lifting)
open import adequacy.Lift.Order using (module LiftingOrder)
open import adequacy.Lowers using (module Lowering)
open import adequacy.Frame using (module Framing)
open import adequacy.Told using (Tells; untold; untoldᴹ; untoldᴸ; untoldʳ)
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
open import adequacy.Shift.Walk using (module ShiftWalk)
open import adequacy.Kept using (module Keeping)

open import adequacy.Climbs.Base using (module ClimbBase)
open import adequacy.Climbs.Take using (module ClimbTake)
open import adequacy.Climbs.Flat using (module ClimbFlat)
open import adequacy.Climbs.Flat.Plant using (module ClimbFlatPlant)
open import adequacy.Climbs.Lanes using (module ClimbLanes)
open Events∞

module ClimbLanesQueue (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open SortingWalk R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Feed; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; fired; Path; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; outers; outersL; outers-⊕; unsub; Owes; Settled; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Spot; spot; ∧-join; Each; Lingers; Tied; seen; seenL; pinned-trans; ∧-split; false≢; owned-to; lv-tie; Leaves; Restful)
  open StrongHeld R using (Strong; Carried; carried; closing; Meets; Heads; DoneBy; module Eaching; module Lingering; Untold) renaming (Ended to Ends)
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
  open Ghosting R using (residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; passed; Past; Lefts; LeftsL)
  open GhostingPaths R using (each-sub; each-lanes; module Far; module Calling; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; Rises; rises; Called; landed; rose; Aloft; aloft; hop-sorted; each-back; hopped-pre; lefts-up; lefts-subst; lefts-subst₂; lefts-split)
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
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ⊆-⊑; _⊑[_/_]_; Bound; Pred; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pooled-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag; tw-alike)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; rested-all; just-of; scan-part; scan-defined)
  open FramingRepool R using (none-of; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; lefts-planted; merged-queued; merged-kept; healed-off; module Framed; flat-stays; heads-union)
  open ClimbTake R using (rise; open-code; writes; reads)
  open ClimbFlat R using (rest-pool-⊑; calling-open; opened-⊕; shut-code; settledᵒ; settleᵒ₂; settleᵒ₁; flat-gone; merged-pool; heading-∘; lingering-∘; pool-heads; lanes-one; ghost-lift; startAt; module Restaged; module Settles)
  open ClimbFlatPlant R using (pending-flags; queue-open; apart-unplant; lane-begin)
  open ClimbLanes R using (module Freed; at-val; climb-lanes; dequeueAt; freed; holds-walk; lane-live; lane-lefts; lane-step; laneEnd; laneOf; lanes-gone; one-open; one-outers; queue-freed; queue-stored; refill-freed; refillAt; sendStep; slot-freed; unlive; walk-lane)

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

    -- The queue no read of the node's own clauses.
    dq-alike : AllPairs _≢_ (names w₀) → Alike H H′ (flatReads fl oc k r t ls)
    dq-alike (a₀ ∷ _ ∷ a₂ ∷ _) j (here e)  = look-store H (FlatKit.Flat.queue fl) j (λ eq → lookupᴬ a₀ (there (here refl)) (sym (trans eq e)))
    dq-alike (a₀ ∷ _ ∷ a₂ ∷ _) j (there m) = look-store H (FlatKit.Flat.queue fl) j (lookupᴬ a₂ m)

    module Fr (fs : AllPairs _≢_ (names T)) =
      Framed H H′ ρ (off-store H (FlatKit.Flat.queue fl)) mine fs
        (flat-stays H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike (fresh-path ρ fs)))
        (Heaps.fed-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} t ls (dq-alike (fresh-path ρ fs)))
        (store-keeps H (FlatKit.Flat.queue fl) _ (λ ()) (λ ()) (λ ()) (λ ()))

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

    dq-part : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.part (store H (FlatKit.Flat.queue fl) (lift ys)) t ≡ At.part H t
    dq-part fr = part-alike H H′ t (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr))

    dq-lanes : AllPairs _≢_ (names w₀) → At.partLanes H′ ls ≡ At.partLanes H ls
    dq-lanes fr = partLanes-alike H H′ ls (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr))

    dq-done : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → At.val (store H (FlatKit.Flat.queue fl) (lift ys)) (FlatKit.Flat.outerDone fl) ≡ At.val H (FlatKit.Flat.outerDone fl)
    dq-done (_ ∷ a₁ ∷ _) = cong lower (look-store H (FlatKit.Flat.queue fl) (FlatKit.Flat.outerDone fl) (λ eq → lookupᴬ a₁ (here refl) (sym eq)))

    -- No flag of the node's moved: the done flag, the outer and the
    -- lanes alike.
    dq-flags₀ : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl t ls)) → ∀ {xs} → DoneBy H (flatMapˢ op f fl oc k r pl t ls) xs → DoneBy (store H (FlatKit.Flat.queue fl) (lift ys)) (flatMapˢ op f fl oc k r pl t ls) xs
    dq-flags₀ fr {xs} d =
      Flag.db-flat H′ {ns = xs} (flagged-moved H H′ {fl = fl} {so = t} (dq-done fr) (dq-part fr) (d here refl))
        (flags-alike H H′ (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)) (Flag.db-sub H d (in-outer here) refl))
        (flagsL-alike H H′ (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)) (Flag.dbL-of H d))

    -- A queue's head taken off: the node's parts and ties alike, its
    -- heads by its parts' and its pool's, whatever is queued.
    dq-revive : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → is-just (At.part H′ w₀) ≡ true → is-just (At.part H w₀) ≡ true
    dq-revive fr nq j with At.part H w₀ in e
    ... | just _  = refl
    ... | nothing = ⊥-elim (true≢false (trans (sym j) (cong is-just (Gone.gone-part (dq-gone fr nq) here e))))

    dq-heading : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → ∀ {q} {E : Pred _} → Heading H H′ q E w₀ w₀
    dq-heading fr nq {q} = record
      { head-revive = dq-revive fr nq
      ; head-told   = λ i _ e₀ e′ → ⊆-⊑ λ m →
          ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H t) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀))
            (≡-⊆ (cong₂ (λ o L → untoldᴹ i o ++ untoldᴸ i L ++ untold i pl) (dq-part fr) (dq-lanes fr))
              (≡-⊆ (cong (untold i) (sym (merged-eq H′ op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl e′))) m))
      ; head-below  = λ ev → Build.each-flat H′ (Heads q) {op = op} {f} {fl} {oc} {k} {r} {pl} {so = t} {ls}
                               (root ev)
                               (λ x → Each.pools ev here refl (proj₂ (j₀ x)))
                               (each-alike H H′ so-al (each-sub ev (in-outer here) refl))
                               (eachL-alike H H′ ls-al (eachL-of H ev)) }
      where
        G = λ a j → U.subscribe (f a) j
        so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        j₀ : ∀ {c} → At.part H′ w₀ ≡ just c → Σ (U.Node Δ B) λ b → At.part H w₀ ≡ just b
        j₀ x = just-of (dq-revive fr nq (cong is-just x))
        root : Each H (Heads q) w₀ → ∀ {c} → At.part H′ w₀ ≡ just c → Heads q c
        root ev x =
          subst (Heads q) (merged-eq H′ op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl x)
            (heads-flat op G (At.part H′ t) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl (Each.pools ev here refl (proj₂ (j₀ x)))
              (λ e → Each.parts ev (in-outer here) refl (trans (sym (dq-part fr)) e))
              (each-lanes {H = H′} {P = Heads q} ls (λ {_} {_} {x} πL sL e →
                Each.parts ev (in-lanes πL) (trans (sym (seenL-alike H H′ πL ls-al)) sL) (trans (sym (part-alike H H′ x (λ j m → ls-al j (lanes-path πL m)))) e))))

    -- A queue's head taken off: what the flatMap leaves running and
    -- its pool's ties read no queue.
    dq-lingering : AllPairs _≢_ (names w₀) → ∀ {y ys′} → At.val H (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Lingering H H′ w₀ w₀
    dq-lingering fr@(_ ∷ a₁ ∷ _) nq = record
      { ling-revive = dq-revive fr nq
      ; ling-rested = λ {C} → tw-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} t so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
      ; ling-below  = λ lg → Linger.lg-flat H′ (pool lg)
                               (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                               (lingersL-alike H H′ ls-al (lingersL-of H lg)) }
      where
        so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {t} {ls} (dq-alike fr)
        pool : Lingers H w₀ → ∀ {c} → At.part H′ w₀ ≡ just c → Leaves pl (At.pooled H′ fl t ls) × Restful pl
        pool lg x = lv-tie (Lingers.pools lg here refl (proj₂ (just-of (dq-revive fr nq (cong is-just x)))))
                           (proj₁ (tw-alike (pooled-alike H H′ fl t ls (look-store H (FlatKit.Flat.queue fl) (FlatKit.Flat.outerDone fl) (λ eq → lookupᴬ a₁ (here refl) (sym eq))) so-al ls-al)))

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
      beside = trans (Settles.active-lanes H₂ ρ (Freed.Fr.kernels hp ρ o fs (lane-live o LL) (Calling.kernels cl)))
                     (trans (cong null (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL)) (null-++ bs as))

  -- A freed slot settling short of the end, the outer or a lane left,
  -- nothing queued: the pool takes the lane's rest, the ghost past the
  -- lane's skip.
  lane-ghost : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) → AllPairs _≢_ (names T)
             → ∀ {g q S bs l S₁ as} → Sane [] g → Placed g [] → Deep g []
             → LiftsLane H πL (U.endˢ q) bs S₁ as
             → settledᵍ (At.part H t) bs as (At.val H (FlatKit.Flat.queue fl)) ≡ false
             → At.val (freed H (laneOf o) fl) (FlatKit.Flat.queue fl) ≡ []
             → Lifts H ρ (U.laneˢ op (λ a i → U.subscribe (f a) i) (At.part H t) bs l S₁ as (At.val H (FlatKit.Flat.queue fl)) pl) S
             → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part (freed H (laneOf o) fl) (Restaged.T′ (freed H (laneOf o) fl) ρ (U.unionᶜ pl (U.restᶜ l))) ≡ just g″
               × Sane [] g″ × Placed g″ [] × Deep g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
  lane-ghost H {op = op} {f} {fl} {oc} {k} {r} {pl} {t} {ls} ρ o fs {q = q} {bs = bs} {l} {S₁} {as} sn pd dp LL st e₀ L sg =
    ghost-lift H H₂ ρ (flatMapˢ op f fl oc k r pl′ t ls) fs (Freed.fr-off H ρ o) (Freed.fr-mine H ρ o) {κ = []}
      (subst (λ s → Lifts H ρ s _) lane-eq L) node alike sn pd dp sg
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

  -- Every lane's rest heads no earlier than q.
  RestL : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ B} → List (Lane h Δ B) → Set
  RestL H q []                = ⊤
  RestL H q (lane _ _ s ∷ ls) = Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} s)) × RestL H q ls

  -- Every lane's rest but the one a path picks heads no earlier than q.
  OthersL : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} → OneLane πL → Set
  OthersL H q (one-this {ls = ls})       = RestL H q ls
  OthersL H q (one-next {l = lane _ _ s} o) = Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} s)) × OthersL H q o

  rest-headsL : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ B} (ls : List (Lane h Δ B)) → RestL H q ls → Heads q (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls))
  rest-headsL H q []                _        ()
  rest-headsL H q (lane _ _ s ∷ ls) (h , hs) =
    heads-union (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} s)) (U.restˢ (At.leftover H {B = ⊤} s))
                (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls)) (U.restˢ (At.leftoverL H {B = ⊤} ls)) h (rest-headsL H q ls hs)

  rest-headsO : ∀ {h} (H : Heapᴹ h) (q : Pos) {Δ B} {ls : List (Lane h Δ B)} {u : Sub h Δ B} {πL : PathLanes ls u} (o : OneLane πL)
              → Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} u)) → OthersL H q o → Heads q (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls))
  rest-headsO H q (one-this {t = t} {ls}) hu hs =
    heads-union (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} t)) (U.restˢ (At.leftover H {B = ⊤} t))
                (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls)) (U.restˢ (At.leftoverL H {B = ⊤} ls)) hu (rest-headsL H q ls hs)
  rest-headsO H q (one-next {l = lane _ _ s} {ls} o) hu (h , hs) =
    heads-union (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} s)) (U.restˢ (At.leftover H {B = ⊤} s))
                (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls)) (U.restˢ (At.leftoverL H {B = ⊤} ls)) h (rest-headsO H q o hu hs)

  -- A lane's end that settles the flatMap: what the flatMap leaves running
  -- is its ended outer's rest, the lane's own and every other lane's.
  module LaneRest {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) {ks}
                  (cl : Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks)) where
    private
      H = Conf.heap (Mach.conf m₁)
      q = Conf.pos (Mach.conf m₁)

    postulate
      -- The ended outer, and the lanes beside the ending one, leave
      -- running nothing heading before the run.
      -- Owed: the pool's heads and its tie to the freed lanes' leftovers
      -- as they stood before the settling lane's end; the climb keeps
      -- neither.
      --
      -- DEAD ROUTE: `Calling.behind`'s pools and `Lingers.pools` reach the pool only while the flatMap holds a part, and the settling lane's end leaves it none, so neither reaches a freed lane here
      outer-ended-heads : At.part H t ≡ nothing → Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} t))
      others-heads      : OthersL H q o

    lane-rest-heads : At.part H t ≡ nothing → Heads q (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} (flatMapˢ op f fl oc k r pl t ls)))
    lane-rest-heads eo =
      heads-union (U.restᶜ {B = ⊤} (At.leftover H {B = ⊤} t)) (U.restˢ (At.leftover H {B = ⊤} t))
                  (U.restᶜ {B = ⊤} (At.leftoverL H {B = ⊤} ls)) (U.restˢ (At.leftoverL H {B = ⊤} ls))
                  (outer-ended-heads eo) (rest-headsO H q o (Calling.rest-heads cl) others-heads)

  -- A lane's end, its pool taking the lane's last ghost rested, which is
  -- what the lane still runs: with nothing queued, and with the queue's
  -- head taken off.  The heads: the pool taking what the lane ran heads
  -- where the lane did; the queue's head taken off, the flatMap heads as
  -- it did.
  module Settling {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) (o : OneLane πL) {ks bs′ l S′ as′ S}
                  (cl : Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks))
                  (L : Lifts (Conf.heap (Mach.conf m₁)) ρ (U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part (Conf.heap (Mach.conf m₁)) t) bs′ l S′ as′
                                                         (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.queue fl)) pl) S)
                  (sg : U.step g ≡ S) (LL : LiftsLane (Conf.heap (Mach.conf m₁)) πL (U.endˢ (Conf.pos (Mach.conf m₁))) bs′ S′ as′)
                  (ll : LeftsL (Conf.heap (Mach.conf m₁)) l LL) where
    H   = Conf.heap (Mach.conf m₁)
    q   = Conf.pos (Mach.conf m₁)
    H₂  = freed H (laneOf o) fl
    pl′ = U.unionᶜ pl (U.restᶜ l)
    w₀  = flatMapˢ op f fl oc k r pl t ls
    v   = flatMapˢ op f fl oc k r pl′ t ls
    fs  = Books.fresh (Calling.books cl)
    fr  = fresh-path ρ fs

    -- The ended lane's last ghost tells its joiners past `q` at a bound
    -- binder's end, as the outer's does in `Climbs.Flat`: `l` was the
    -- lane's part at this `q`, the freed lane is in no part, and `ll` ties
    -- only its meaning.
    --
    -- DEAD ROUTE: over `untold`, a rest's joiners counted: a connect in the lane whose body ended with its source still pending leaves that source's joiner in `l`'s rest and in no part
    -- DEAD ROUTE: at every end `c`: a connect still live keeps its running source in the rest, holding a joiner older than any the part holds, which tells past `q` at no end between it and `q`
    postulate
      lane-ghost-told : ∀ {A′} (i : A′ ∈ᴸ Δ) {c} → Bound H ρ i c → Tells q c (untold i l)

    settle-rest-told : ∀ {A′} (i : A′ ∈ᴸ Δ) {c} → Bound H ρ i c → ∀ {b₀} → At.part H₂ w₀ ≡ just b₀ → untoldʳ i l ⊑[ q / c ] untold i b₀
    settle-rest-told i b _ _ = rested-all i l (lane-ghost-told i b)

    settle-told : ∀ {A′} (i : A′ ∈ᴸ Δ) {c} → Bound H ρ i c → ∀ {b₀} → At.part H₂ w₀ ≡ just b₀ → untold i pl′ ⊑[ q / c ] untold i b₀
    settle-told i b e = rest-pool-⊑ H₂ op (λ a j → U.subscribe (f a) j) (At.part H₂ t) (At.partLanes H₂ ls) (At.val H₂ (FlatKit.Flat.queue fl)) pl l i e (settle-rest-told i b e)

    settle-lingering : Lingering H H₂ w₀ v
    settle-lingering = Freed.fr-settled H ρ o fr l (lane-lefts o LL ll) (lane-live o LL)
                         (λ j → Freed.fr-revive H ρ o fr (trans (sym (merged-pool H₂ op (λ a j′ → U.subscribe (f a) j′) (At.part H₂ t) (At.partLanes H₂ ls) (At.val H₂ (FlatKit.Flat.queue fl)) pl pl′)) j))

    settle-heads : ∀ {c} → At.part H₂ w₀ ≡ just c → Heads q pl → Heads q pl′
    settle-heads e = pool-heads l (proj₂ (Lingers.pools (Calling.lingers cl) ρ (lifts-seen L) (proj₂ (just-of (Freed.fr-revive H ρ o fr (cong is-just e))))))
                       (lane-lefts o LL ll) (Calling.rest-heads cl)

    next-lingering : ∀ ys {y ys′} → At.val H₂ (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Lingering H (Dequeued.H′ H₂ ρ ys) w₀ v
    next-lingering ys nq = lingering-∘ settle-lingering (Dequeued.dq-lingering H₂ (planted ρ v) ys fr nq)

    settle-heading : Heading H H₂ q (Bound H ρ) w₀ v
    settle-heading = heading-∘ (Freed.fr-heading H ρ o fr) (Restaged.repool-heading H₂ ρ pl′ (λ {A′} i {c} b {b₀} → settle-told {A′} i {c} b {b₀}) settle-heads)

    settle-lingers : Lingers H₂ (Restaged.T′ H₂ ρ pl′)
    settle-lingers = Freed.Sh.shift-lingers H ρ o fs v (Calling.ended cl) settle-lingering (Calling.lingers cl)

    -- The queue's head taken off needs it there to take.
    next-heading : ∀ ys {y ys′} → At.val H₂ (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → ∀ {E : Pred _} → Heading H (Dequeued.H′ H₂ ρ ys) q E w₀ w₀
    next-heading ys nq = heading-∘ (Freed.fr-heading H ρ o fr) (Dequeued.dq-heading H₂ ρ ys fr nq)

    next-lingers : ∀ ys {y ys′} → At.val H₂ (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Lingers (Dequeued.H′ H₂ ρ ys) (Restaged.T′ (Dequeued.H′ H₂ ρ ys) ρ pl′)
    next-lingers ys nq = Shift.shift-lingers H (Dequeued.H′ H₂ ρ ys) ρ (off-++ {H = H} {H₁ = H₂} {H₂ = Dequeued.H′ H₂ ρ ys} (Freed.ns H ρ o) (Freed.fr-off H ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                        (all-++⁺ (Freed.fr-mine H ρ o) (Dequeued.mine H₂ ρ ys)) fs v (Calling.ended cl) (next-lingering ys nq) (Calling.lingers cl)

    next-ended : ∀ ys {y ys′} → At.val H₂ (FlatKit.Flat.queue fl) ≡ y ∷ ys′ → Ends (Dequeued.H′ H₂ ρ ys) (Restaged.T′ (Dequeued.H′ H₂ ρ ys) ρ pl′)
    next-ended ys nq = Shift.shift-ended H (Dequeued.H′ H₂ ρ ys) ρ (off-++ {H = H} {H₁ = H₂} {H₂ = Dequeued.H′ H₂ ρ ys} (Freed.ns H ρ o) (Freed.fr-off H ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                        (all-++⁺ (Freed.fr-mine H ρ o) (Dequeued.mine H₂ ρ ys)) fs v (Calling.ended cl) (next-lingering ys nq)

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
    cl@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; stack = sk ; lifted = gu , S , L , sg , hl ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; lefts = lt ; kept = kp } eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L in eqQ | reads {hp = freed hp (laneOf o) fl} ea
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
      { sane = sn ; placed = pd ; deep = dp ; ctl = refl
      ; code = ≗-trans e₃ (≗-trans (open-code {m = Observer.complete O} eq) (seq-done _))
      ; stack = stk
      ; lifted = flat-gone H₂ {op = op} {f} {fl} {oc} {k} {r} {po} {u = t} {ls} (trans (Freed.fr-part hp ρ o (fresh-path ρ fs)) eo)
                           (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (cong₂ _++_ ebs eas)) eq₀
               , S , Freed.Wr.wr-lifts hp ρ o fs Lq , sg
               , healed-off hp H₂ ρ fs (Heaps.keep hp H₂ (Freed.fr-off hp ρ o) (lookupᴬ (Freed.fr-mine hp ρ o)))
                            (trans (cong₂ (λ o′ L′ → At.merged hp op G o′ L′ (At.val H₂ (FlatKit.Flat.queue fl)) po) (Freed.fr-part hp ρ o (fresh-path ρ fs))
                                          (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (sym (lanes-gone hp o LL gu))))
                                   (cong (λ Q → At.merged hp op G (At.part hp t) (At.partLanes hp ls) Q po) (queue-freed hp (laneOf o) fl)))
                            (healed-split ρ (in-lanes πL) hl)
      ; owned = owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.Sh.wr-owned hp ρ o fs (Freed.fr-gone hp ρ o (fresh-path ρ fs)) ow)
      ; kernels = Freed.Fr.kernels hp ρ o fs (lane-live o LL) kn ; meaning = Freed.Fr.meaning hp ρ o fs (lane-live o LL) mn ; queue = Freed.Fr.queue hp ρ o fs (lane-live o LL) qu
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Freed.fr-behind hp ρ o fs (Calling.told cl) (Calling.ended cl) bh
      ; lingers = Freed.Fr.lingers hp ρ o fs (lane-live o LL) (Calling.ended cl)
                    (Freed.fr-lingering hp ρ o (fresh-path ρ fs)
                      (flat-gone H₂ {op = op} {f} {fl} {oc} {k} {r} {po} {u = t} {ls} (trans (Freed.fr-part hp ρ o (fresh-path ρ fs)) eo)
                                 (trans (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL) (cong₂ _++_ ebs eas)) eq₀)) lgr ; lefts = Freed.Fr.wr-lefts hp ρ o fs (lane-live o LL) Lq
                  (lefts-subst (λ s′ → s′) (lane-end op G l q po eo ebs eas eqs)
                    (lefts-subst (λ S′ → U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) (lane-step o LL) (lefts-up ρ (in-lanes πL) eqQ lt)))
      ; rest-heads = subst (λ x → Heads q (U.restᶜ {B = ⊤} x)) (sym (Freed.fr-left hp ρ o (fresh-path ρ fs))) (LaneRest.lane-rest-heads ρ o cl eo)
      ; flags = Freed.fr-flags hp ρ o fs (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl)) ; kept = inj₁ refl
      ; told = Freed.fr-told hp ρ o fs (Calling.told cl) (Calling.ended cl) ; ended = Freed.fr-ended hp ρ o fs (Calling.ended cl) }))
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
      Lq   = subst (λ s′ → Lifts hp ρ s′ S) (lane-end op G l q po eo ebs eas eqs)
               (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S) (lane-step o LL) Lρ)
  ...       | false
    with lane-ghost hp ρ o fs sn pd dp LL (trans (sym (lane-settles ρ o cl LL)) eq) eq₀ Lρ sg
  ...         | g″ , pg , sn″ , pd″ , dp″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; deep = dp″ ; tree = Restaged.T′ H₂ ρ pl′
        ; ctlAs = runAs (Restaged.pool-calls H₂ ρ pl′ []) ec (Restaged.pool-stack H₂ ρ pl′ stk)
        ; meets = pg
        ; owned′ = owned-to (Restaged.pool-owned H₂ ρ pl′ stk [] ec (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.Sh.wr-owned hp ρ o fs (Freed.fr-gone hp ρ o (fresh-path ρ fs)) ow)))
        ; kernels = Restaged.pool-kernels H₂ ρ pl′ (Freed.Fr.kernels hp ρ o fs (lane-live o LL) kn)
        ; meaning = Restaged.pool-meaning H₂ ρ pl′ (Freed.Fr.meaning hp ρ o fs (lane-live o LL) mn)
        ; queue = Restaged.pool-queue H₂ ρ pl′ (Freed.Fr.queue hp ρ o fs (lane-live o LL) qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked H₂ ρ pl′ clk stk (proj₁ ck , proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind′ = Eaching.each-to _ _ (Freed.Sh.shift-behind hp ρ o fs v (Calling.told cl) (Calling.ended cl) (Settling.settle-heading ρ πL o cl Lρ sg LL ll) bh)
        ; lingers′ = Lingering.lingers-to _ (Settling.settle-lingers ρ πL o cl Lρ sg LL ll) ; flags = let-go H₂ (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs) (lifts-seen (lifts-planted ρ v (Freed.Wr.wr-lifts hp ρ o fs Lρ))) ju
                    (subst (DoneBy H₂ (plant ρ v)) (sym (outers-planted ρ v)) (Freed.fr-shift hp ρ o fs pl′ rv (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl))))
        ; told = Freed.Sh.shift-told hp ρ o fs v (Calling.told cl) (Calling.ended cl) (Settling.settle-heading ρ πL o cl Lρ sg LL ll)
        ; ended = Freed.Sh.shift-ended hp ρ o fs v (Calling.ended cl) (Settling.settle-lingering ρ πL o cl Lρ sg LL ll) })
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
      ll   = subst (λ w → Lefts hp (proj₁ (proj₂ w))) eqQ (proj₁ (lefts-split ρ (in-lanes πL) L lt))

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
    cl@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; stack = sk ; lifted = gn , S , L , sg , _ ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; lefts = lt ; kept = kp } {y} {ys} eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L in eqN | writes {hp = freed hp (laneOf o) fl} ea
  ... | _ , lifts-lanes {bs = bs′} {l = l} {as = as′} LL ee lf pb , Lρ | n′ , e′ , p′ =
    hopped-pre (⇝-trans p p′) (lane-begin st (record
      { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; code = e′
      ; opens = trans (Dequeued.Fr.wr-opened H₂ ρ ys fs true)
                  (trans (Freed.Wr.wr-opened hp ρ o fs true) (one-open hp o (trans (sym (opened-⊕ hp true ρ (in-lanes πL))) (calling-open (ρ ⊕ in-lanes πL) cl))))
      ; stack = stk
      ; lifted = S , L₇ , sg
      ; lefts = lt₇
      ; owned = Dequeued.Fr.wr-owned H₂ ρ ys fs (Dequeued.dq-gone H₂ ρ ys (fresh-path ρ fs) eq₀) (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.Sh.wr-owned hp ρ o fs (Freed.fr-gone hp ρ o (fresh-path ρ fs)) ow))
      ; kernels = Dequeued.Fr.kernels H₂ ρ ys fs (Freed.Fr.kernels hp ρ o fs (lane-live o LL) kn)
      ; meaning = Dequeued.Fr.meaning H₂ ρ ys fs (Freed.Fr.meaning hp ρ o fs (lane-live o LL) mn)
      ; queue = Dequeued.Fr.queue H₂ ρ ys fs (Freed.Fr.queue hp ρ o fs (lane-live o LL) qu)
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (⇝-trans p p′)
      ; behind = subst (λ t′ → Each H₃ (Heads q) t′) (plant-self ρ)
                   (Shift.shift-behind hp H₃ ρ (off-++ {H = hp} {H₁ = H₂} {H₂ = H₃} (Freed.ns hp ρ o) (Freed.fr-off hp ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                                       (all-++⁺ (Freed.fr-mine hp ρ o) (Dequeued.mine H₂ ρ ys)) fs w₀ (Calling.told cl) (Calling.ended cl) (Settling.next-heading ρ πL o cl Lρ sg LL ll ys eq₀) bh)
      ; lingers = Settling.next-lingers ρ πL o cl Lρ sg LL ll ys eq₀ ; ended = Settling.next-ended ρ πL o cl Lρ sg LL ll ys eq₀
      ; told = subst (λ t′ → Untold H₃ q t′) (plant-self ρ)
                 (Shift.shift-told hp H₃ ρ (off-++ {H = hp} {H₁ = H₂} {H₂ = H₃} (Freed.ns hp ρ o) (Freed.fr-off hp ρ o) (off-store H₂ (FlatKit.Flat.queue fl)))
                                   (all-++⁺ (Freed.fr-mine hp ρ o) (Dequeued.mine H₂ ρ ys)) fs w₀ (Calling.told cl) (Calling.ended cl) (Settling.next-heading ρ πL o cl Lρ sg LL ll ys eq₀))
     ; flags = let-go H₃ (planted ρ P₀) (pairs-r (names w₀) (apart-unplant ρ fs)) (trans (seen-planted H₃ ρ P₀) (lifts-seen L₇)) refl
                  (subst (DoneBy H₃ (plant ρ P₀)) (sym (outers-planted ρ P₀))
                    (Dequeued.Fr.shift-flags H₂ ρ ys fs P₀ {ns₀ = []} (λ ()) (λ _ → ju₂) (λ _ → pending-flags H₃) (subst (DoneBy H₂ _) (sym (++-identityʳ (outers ρ))) d₂)))
      ; inner = Dequeued.dq-flags₀ H₂ ρ ys (fresh-path ρ fs) (Flag.db-sub H₂ (let-go H₂ ρ fs s₂ ju₂ d₂) ρ s₂) }))
    where
      H₂  = freed hp (laneOf o) fl
      H₃  = Dequeued.H′ H₂ ρ ys
      w₀  = flatMapˢ op f fl oc k r po t ls
      G   = λ a j → U.subscribe (f a) j
      pl′ = U.unionᶜ po (U.restᶜ l)
      stk = restAs ks (≗-trans (wk-same n) eks) sk
      ll  = subst (λ w → Lefts hp (proj₁ (proj₂ w))) eqN (proj₁ (lefts-split ρ (in-lanes πL) L lt))
      F   = λ (x : Maybe (U.Node _ _)) (zs : List (U.Node _ _)) (qs : List _) → U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op G x (G y (q ++ [ ix 1 ]) ∷ zs) qs pl′)
      L₁  = subst (λ qs → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l (U.endˢ q) as′ qs po) S)
                  (trans (sym (queue-freed hp (laneOf o) fl)) eq₀)
                  (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S) (lane-step o LL) Lρ)
      L₄  = Dequeued.Fr.wr-lifts H₂ ρ ys fs (Freed.Wr.wr-lifts hp ρ o fs L₁)
      L₅  = subst (λ x → Lifts H₃ ρ (F x (bs′ ++ as′) ys) S) (sym (trans (Dequeued.dq-part H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-part hp ρ o (fresh-path ρ fs)))) L₄
      L₆  = subst (λ zs → Lifts H₃ ρ (F (At.part H₃ t) zs ys) S) (sym (trans (Dequeued.dq-lanes H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL))) L₅
      L₇  = subst (λ qs → Lifts H₃ ρ (F (At.part H₃ t) (At.partLanes H₃ ls) qs) S) (sym (queue-stored H₂ fl ys)) L₆
      lt₁ = lefts-subst (λ qs → U.laneˢ op G (At.part hp t) bs′ l (U.endˢ q) as′ qs po) (trans (sym (queue-freed hp (laneOf o) fl)) eq₀)
              (lefts-subst (λ S′ → U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) (lane-step o LL) (lefts-up ρ (in-lanes πL) eqN lt))
      lt₄ = Dequeued.Fr.wr-lefts H₂ ρ ys fs (Freed.Wr.wr-lifts hp ρ o fs L₁) (Freed.Fr.wr-lefts hp ρ o fs (lane-live o LL) L₁ lt₁)
      lt₅ = lefts-subst (λ x → F x (bs′ ++ as′) ys) (sym (trans (Dequeued.dq-part H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-part hp ρ o (fresh-path ρ fs)))) lt₄
      lt₆ = lefts-subst (λ zs → F (At.part H₃ t) zs ys) (sym (trans (Dequeued.dq-lanes H₂ ρ ys (fresh-path ρ fs)) (Freed.fr-lanes hp ρ o (fresh-path ρ fs) LL))) lt₅
      lt₇ = lefts-subst (λ qs → F (At.part H₃ t) (At.partLanes H₃ ls) qs) (sym (queue-stored H₂ fl ys)) lt₆
      P₀  = pendingˢ (f y) (q ++ [ ix 1 ])
      d₂  = Freed.fr-flags hp ρ o fs (done-up ρ (in-lanes πL) (one-outers o) (Calling.flags cl))
      s₂  = lifts-seen (Freed.Wr.wr-lifts hp ρ o fs L₁)
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
