{-# OPTIONS --guardedness #-}

module adequacy.Climbs.Flat.Plant where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Nat using (suc; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; skip; Pos; Timeline; ix; <ᵖ-below)
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
open import Data.Bool using (Bool; true; false; if_then_else_; _∨_)
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
open import adequacy.Shift.Walk using (module ShiftWalk)
open import adequacy.Kept using (module Keeping)

open import adequacy.Climbs.Base using (module ClimbBase)
open import adequacy.Climbs.Take using (module ClimbTake)
open import adequacy.Climbs.Flat using (module ClimbFlat)
open Events∞

module ClimbFlatPlant (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open SortingWalk R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Feed; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; fired; Path; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; outers; outersL; outers-⊕; unsub; Owes; Settled; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Spot; spot; ∧-join; Each; Lingers; Tied; seen; seenL; pinned-trans; ∧-split; false≢; owned-to)
  open StrongHeld R using (Strong; Carried; carried; closing; Meets; Heads; DoneBy; module Eaching; module Lingering)
  open StrongAgainst.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs; StackAs; Ticked; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots; SrcOf; src-of) renaming (Placed to Placedᴬ)
  open Pure R using (Timer; cascade; wkTimer)
  open Moving R using (pairs-r; pairs-split; plant-self; takes; takesᴸ; stage; takes-plant; plant; plantᴸ; planted; plantedᴸ; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant; joiners-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open EverywhereGated.Settling R using (settled-plant; settled-retag)
  open EverywhereGated.Gating R using (gated-alike; gated-path; gated-plant; gated-retag)
  open Tearing R using (holds-at; cuts; attached-alike; cuts-switches; fresh-path; fresh-lanes; part-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; apart-l; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Forking R using (walk-planted)
  open Aliking R using (walk-grow; compile-cong; laneAt-wk; ObsRel)
  open Taking R using (tick-ix0)
  open Naming R using (pre; pairs-↭; names-plant-↭; fresh-plant; fresh-new; wk-pairs; wk-img; to-img)
  open Ghosting R using (residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; passed; Past)
  open GhostingPaths R using (each-sub; each-lanes; module Far; module Calling; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; Rises; rises; Called; landed; rose; Aloft; aloft; hop-sorted; each-back; hopped-pre)
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
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pin-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined)
  open FramingRepool R using (heads-repool; Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; tick-under; healed-off; module Framed; flat-stays)
  open ClimbTake R using (rise; open-code; writes; reads)
  open ClimbFlat R using (module Restaged; admitAt; calling-open; close-outer; gatedL-mono; opened-⊕; outer-live; rerun; roomy; startAt)

  -- A PLANT AS OPEN AS WHAT IT REPLACES: every gate above reads only
  -- whether a node is open, so the parts above open as before, and every
  -- flag above reads as before.
  module _ {h} (H : Heapᴹ h) where
    private
      jmap : ∀ {X Y : Set₁} (g : X → Y) (m m′ : Maybe X) → is-just m ≡ is-just m′ → is-just (At.mapᴹ H g m) ≡ is-just (At.mapᴹ H g m′)
      jmap g nothing  nothing  _ = refl
      jmap g (just _) (just _) _ = refl
      jmap g nothing  (just _) ()
      jmap g (just _) nothing  ()

      jtake : ∀ {Δ A} i (p : A → Bool) (tk : Strongly.Taking R Δ A) (m m′ : Maybe (U.Node Δ A)) → is-just m ≡ is-just m′
            → is-just (At.taking? H i p tk m) ≡ is-just (At.taking? H i p tk m′)
      jtake i p taking       m m′ e = jmap (U.takeWhileᶜ i p) m m′ e
      jtake i p (ending _ _) m m′ e = refl
      jtake i p taken        m m′ e = refl

      jif : ∀ b {X : Set₁} {m m′ : Maybe X} → is-just m ≡ is-just m′ → is-just (if b then m else nothing) ≡ is-just (if b then m′ else nothing)
      jif true  e = e
      jif false e = refl

      jmerged : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o o′ : Maybe (U.Node Δ A)) (ls ls′ : List (U.Node Δ B)) qs pl
              → is-just o ≡ is-just o′ → null ls ≡ null ls′ → is-just (At.merged H op g o ls qs pl) ≡ is-just (At.merged H op g o′ ls′ qs pl)
      jmerged op g nothing  nothing  []      []      qs pl _ _ = refl
      jmerged op g nothing  nothing  []      (_ ∷ _) qs pl _ ()
      jmerged op g nothing  nothing  (_ ∷ _) []      qs pl _ ()
      jmerged op g nothing  nothing  (_ ∷ _) (_ ∷ _) qs pl _ _ = refl
      jmerged op g nothing  (just _) ls      ls′     qs pl () _
      jmerged op g (just _) nothing  ls      ls′     qs pl () _
      jmerged op g (just _) (just _) ls      ls′     qs pl _ _ = refl

      jconn : ∀ {Δ A B} r e (t : U.Node Δ A) (s s′ : Maybe (U.Node Δ A)) (b b′ : Maybe (U.Node (A ∷ Δ) B))
            → is-just s ≡ is-just s′ → is-just b ≡ is-just b′ → is-just (At.connected H r e t s b) ≡ is-just (At.connected H r e t s′ b′)
      jconn r e        t s        s′       nothing  nothing  _  _  = refl
      jconn r e        t s        s′       nothing  (just _) _  ()
      jconn r e        t s        s′       (just _) nothing  _  ()
      jconn r e        t (just _) (just _) (just _) (just _) _  _  = refl
      jconn r e        t (just _) nothing  (just _) (just _) () _
      jconn r e        t nothing  (just _) (just _) (just _) () _
      jconn r (just _) t nothing  nothing  (just _) (just _) _  _  = refl
      jconn r nothing  t nothing  nothing  (just _) (just _) _  _  = refl

      fcons : ∀ {X : Set₁} (m m′ : Maybe X) (xs xs′ : List X) → is-just m ≡ is-just m′ → null xs ≡ null xs′ → null (At.consᴹ H m xs) ≡ null (At.consᴹ H m′ xs′)
      fcons nothing  nothing  xs xs′ _ e = e
      fcons (just _) (just _) xs xs′ _ _ = refl
      fcons nothing  (just _) xs xs′ () _
      fcons (just _) nothing  xs xs′ () _

      fif : ∀ b {X : Set₁} {xs xs′ ys ys′ : List X} → null xs ≡ null xs′ → null ys ≡ null ys′ → null (if b then xs else ys) ≡ null (if b then xs′ else ys′)
      fif true  e _ = e
      fif false _ e = e

    jnot : ∀ {X : Set₁} (m m′ : Maybe X) → is-just m ≡ is-just m′ → is-nothing m ≡ is-nothing m′
    jnot nothing  nothing  _ = refl
    jnot (just _) (just _) _ = refl
    jnot nothing  (just _) ()
    jnot (just _) nothing  ()

    mutual
      part-just-plant : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                      → is-just (At.part H v) ≡ is-just (At.part H u) → is-just (At.part H (plant π v)) ≡ is-just (At.part H t)
      part-just-plant here v j = j
      part-just-plant (in-map {f = f} {t = s} π) v j = jmap (U.mapᶜ f) (At.part H (plant π v)) (At.part H s) (part-just-plant π v j)
      part-just-plant (in-scan {f = f} {r} {t = s} π) v j = jmap (U.scanᶜ f (At.val H r)) (At.part H (plant π v)) (At.part H s) (part-just-plant π v j)
      part-just-plant (in-take {i = i} {p} {c} {tk = tk} {t = s} π) v j =
        jif (At.val H (Kit.live c)) (jtake i p tk (At.part H (plant π v)) (At.part H s) (part-just-plant π v j))
      part-just-plant (in-outer {op = op} {f} {fl} {pl = pl} {t = so} {ls} π) v j =
        jmerged op (λ a q → U.subscribe (f a) q) (At.part H (plant π v)) (At.part H so) (At.partLanes H ls) (At.partLanes H ls)
          (At.val H (FlatKit.Flat.queue fl)) pl (part-just-plant π v j) refl
      part-just-plant (in-lanes {op = op} {f} {fl} {pl = pl} {t = so} {ls} πL) v j =
        jmerged op (λ a q → U.subscribe (f a) q) (At.part H so) (At.part H so) (At.partLanes H (plantᴸ πL v)) (At.partLanes H ls)
          (At.val H (FlatKit.Flat.queue fl)) pl refl (lanes-just-plant πL v j)
      part-just-plant (in-source {e = e} {rp} {rt} {t = s} {bd} π) v j =
        jconn rp e rt (At.part H (plant π v)) (At.part H s) (At.part H bd) (At.part H bd) (part-just-plant π v j) refl
      part-just-plant (in-body {e = e} {rp} {rt} {t = s} {bd} π) v j =
        jconn rp e rt (At.part H s) (At.part H s) (At.part H (plant π v)) (At.part H bd) refl (part-just-plant π v j)
      part-just-plant (in-defer π) v j = part-just-plant π v j

      lanes-just-plant : ∀ {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) (v : Sub h Δ′ A′)
                       → is-just (At.part H v) ≡ is-just (At.part H u) → null (At.partLanes H (plantᴸ πL v)) ≡ null (At.partLanes H ls)
      lanes-just-plant (this-lane {c = c} {t = s} {ls} π) v j =
        fif (At.val H (Kit.live c)) (fcons (At.part H (plant π v)) (At.part H s) (At.partLanes H ls) (At.partLanes H ls) (part-just-plant π v j) refl) refl
      lanes-just-plant (next-lane {l = lane c k s} {ls} πL) v j =
        fif (At.val H (Kit.live c)) (fcons (At.part H s) (At.part H s) (At.partLanes H (plantᴸ πL v)) (At.partLanes H ls) refl (lanes-just-plant πL v j))
            (lanes-just-plant πL v j)

    mutual
      flags-swap : ∀ {ns Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′)
                 → is-just (At.part H v) ≡ is-just (At.part H u) → DoneBy H v ns → DoneBy H t ns → DoneBy H (plant π v) ns
      flags-swap here v j dv d = dv
      flags-swap {ns} (in-map π) v j dv d = Flag.db-map H {ns = ns} (flags-swap π v j dv (Flag.db-sub H d (in-map here) refl))
      flags-swap {ns} (in-scan π) v j dv d = Flag.db-scan H {ns = ns} (flags-swap π v j dv (Flag.db-sub H d (in-scan here) refl))
      flags-swap {ns} (in-take {c = c} π) v j dv d =
        Flag.db-take H {ns = ns} (λ ok → flags-swap π v j dv (Flag.db-sub H d (in-take here) (seen-take (At.val H (Kit.live c)) ok)))
      flags-swap {ns} (in-outer {t = so} π) v j dv d =
        Flag.db-flat H {ns = ns} (proj₁ (d here refl) , λ m̸ → trans (proj₂ (d here refl) m̸) (jnot (At.part H so) (At.part H (plant π v)) (sym (part-just-plant π v j))))
          (flags-swap π v j dv (Flag.db-sub H d (in-outer here) refl)) (Flag.dbL-of H d)
      flags-swap {ns} (in-lanes πL) v j dv d =
        Flag.db-flat H {ns = ns} (d here refl) (Flag.db-sub H d (in-outer here) refl) (flags-swapL πL v j dv (Flag.dbL-of H d))
      flags-swap {ns} (in-source {e = e} π) v j dv d =
        Flag.db-connect H {ns = ns} (λ jb → flags-swap π v j dv (Flag.db-sub H d (in-source here) (∧-join jb refl)))
          (λ js → Flag.db-sub H d (in-body here) (∧-join (subst (λ z → (z ∨ is-just e) ≡ true) (part-just-plant π v j) js) refl))
      flags-swap {ns} (in-body π) v j dv d =
        Flag.db-connect H {ns = ns} (λ jb → Flag.db-sub H d (in-source here) (∧-join (trans (sym (part-just-plant π v j)) jb) refl))
          (λ js → flags-swap π v j dv (Flag.db-sub H d (in-body here) (∧-join js refl)))
      flags-swap {ns} (in-defer π) v j dv d = Flag.db-defer H {ns = ns} (flags-swap π v j dv (Flag.db-sub H d (in-defer here) refl))

      flags-swapL : ∀ {ns Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) (v : Sub h Δ′ A′)
                  → is-just (At.part H v) ≡ is-just (At.part H u) → DoneBy H v ns → DoneByL H ls ns → DoneByL H (plantᴸ πL v) ns
      flags-swapL {ns} (this-lane π) v j dv dL = Flag.dbL-cons H {ns = ns} (λ lv → flags-swap π v j dv (Flag.dbL-head H dL lv)) (Flag.dbL-tail H dL)
      flags-swapL {ns} (next-lane {l = lane c k s} πL) v j dv dL = Flag.dbL-cons H {ns = ns} (Flag.dbL-head H dL) (flags-swapL πL v j dv (Flag.dbL-tail H dL))

    -- A pending node holds no flatMap.
    pending-flags : ∀ {ns Δ A} {s : T.Obs Timeline Δ A} {q} → DoneBy H (pendingˢ s q) ns
    pending-flags () _

    -- A flatMap open by a live lane, or by a queued value.
    lane-opens : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) b (x : U.Node Δ B) (xs : List (U.Node Δ B)) qs pl
              → b ≡ true → is-just (At.merged H op g o (if b then x ∷ xs else xs) qs pl) ≡ true
    lane-opens op g nothing  b x xs qs pl refl = refl
    lane-opens op g (just _) b x xs qs pl refl = refl

    queue-open : ∀ {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) (ls : List (U.Node Δ B)) y ys pl
               → is-just (At.merged H op g o ls (y ∷ ys) pl) ≡ true
    queue-open op g nothing  []      y ys pl = refl
    queue-open op g nothing  (_ ∷ _) y ys pl = refl
    queue-open op g (just _) ls      y ys pl = refl

  -- A plant over a plant: the outer one alone.
  mutual
    plant-planted : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v w : Sub h Δ′ A′) → plant (planted π v) w ≡ plant π w
    plant-planted here          v w = refl
    plant-planted (in-map π)    v w rewrite plant-planted π v w = refl
    plant-planted (in-scan π)   v w rewrite plant-planted π v w = refl
    plant-planted (in-take π)   v w rewrite plant-planted π v w = refl
    plant-planted (in-outer π)  v w rewrite plant-planted π v w = refl
    plant-planted (in-lanes π)  v w rewrite plantᴸ-planted π v w = refl
    plant-planted (in-source π) v w rewrite plant-planted π v w = refl
    plant-planted (in-body π)   v w rewrite plant-planted π v w = refl
    plant-planted (in-defer π)  v w rewrite plant-planted π v w = refl

    plantᴸ-planted : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v w : Sub h Δ′ A′) → plantᴸ (plantedᴸ π v) w ≡ plantᴸ π w
    plantᴸ-planted (this-lane π) v w rewrite plant-planted π v w = refl
    plantᴸ-planted (next-lane π) v w rewrite plantᴸ-planted π v w = refl

  -- A plant weakened: the weakened node planted down the weakened path.
  mutual
    wk-plant : ∀ {h g Δ A Δ′ A′} (τ : h ⊑ g) {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) (v : Sub h Δ′ A′) → wkTree τ (plant π v) ≡ plant (wkPath τ π) (wkTree τ v)
    wk-plant τ here          v = refl
    wk-plant τ (in-map π)    v rewrite wk-plant τ π v = refl
    wk-plant τ (in-scan π)   v rewrite wk-plant τ π v = refl
    wk-plant τ (in-take π)   v rewrite wk-plant τ π v = refl
    wk-plant τ (in-outer π)  v rewrite wk-plant τ π v = refl
    wk-plant τ (in-lanes π)  v rewrite wk-plantᴸ τ π v = refl
    wk-plant τ (in-source π) v rewrite wk-plant τ π v = refl
    wk-plant τ (in-body π)   v rewrite wk-plant τ π v = refl
    wk-plant τ (in-defer π)  v rewrite wk-plant τ π v = refl

    wk-plantᴸ : ∀ {h g Δ B Δ′ A′} (τ : h ⊑ g) {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) (v : Sub h Δ′ A′)
              → wkLanes τ (plantᴸ π v) ≡ plantᴸ (wkPathᴸ τ π) (wkTree τ v)
    wk-plantᴸ τ (this-lane π) v rewrite wk-plant τ π v = refl
    wk-plantᴸ τ (next-lane π) v rewrite wk-plantᴸ τ π v = refl

  -- A node replaced by a pending one: what it named apart from all the
  -- tree names besides.
  apart-unplant : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) {s q} → AllPairs _≢_ (names t)
                → AllPairs _≢_ (names u ++ names (plant π (pendingˢ s q)))
  apart-unplant {t = t} {u} π {s} {q} fs =
    pairs-↭ (subst (λ x → names x ↭ names u ++ names (plant π (pendingˢ s q))) (trans (plant-planted π (pendingˢ s q) u) (plant-self π))
                   (names-plant-↭ (planted π (pendingˢ s q)) u (↭-reflexive (sym (++-identityʳ (names u)))))) fs

  -- A LANE ABOUT TO BEGIN: the flatMap at the path's end starting a lane
  -- for `y` where the run is, its path open; the ghost's step the
  -- flatMap's skip, the lane subscribed under the run's `ix 1`, the pool
  -- `pl′`.
  record Begins (g : U.Node [] R) (ℓ : Load) (m : Mach) {Δ A B op f fl oc k r pl} {T : Sub (Conf.world (Mach.conf m)) [] R}
                {t : Sub (Conf.world (Mach.conf m)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (y : A) (pl′ : U.Node Δ B) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      deep    : Deep g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m)
      {act}   : Act (Conf.world (Mach.conf m)) ⊤
      {K}     : Stack w ⊤
      ctl     : Conf.ctl (Mach.conf m) ≡ run act ϑ K
      code    : act ≗ startAt ρ y
      opens   : opened (Conf.heap (Mach.conf m)) true ρ ≡ true
      stack   : StackAs T (Conf.pos (Mach.conf m)) ϑ K (Mach.bursts m)
      lifted  : Σ (U.Step [] R) λ S
                → Lifts (Conf.heap (Mach.conf m)) ρ
                    (U.skipˢ (Conf.pos (Mach.conf m) ++ [ ix 0 ])
                      (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part (Conf.heap (Mach.conf m)) t)
                        (U.subscribe (f y) (Conf.pos (Mach.conf m) ++ [ ix 1 ]) ∷ At.partLanes (Conf.heap (Mach.conf m)) ls)
                        (At.val (Conf.heap (Mach.conf m)) (FlatKit.Flat.queue fl)) pl′)) S
                  × U.step g ≡ S
      owned   : Owned (Conf.heap (Mach.conf m)) T (runAs [] (≗-refl _) stack)
      kernels : Kernels (Conf.heap (Mach.conf m)) T
      meaning : Meaning (Conf.heap (Mach.conf m)) T
      queue   : Queue (Conf.heap (Mach.conf m)) (Conf.pos (Mach.conf m)) (Mach.clock m) (Mach.timers m) T
      books   : Books T (runAs [] (≗-refl _) stack) m
      sorted  : Σ Pos λ lo → WellMach lo m
      behind  : Each (Conf.heap (Mach.conf m)) (Heads (Conf.pos (Mach.conf m))) T
      lingers : Lingers (Conf.heap (Mach.conf m)) (Restaged.T′ (Conf.heap (Mach.conf m)) ρ pl′)
      -- The flags as the lane, still pending, will read them; and the
      -- flatMap's own.
      flags   : DoneBy (Conf.heap (Mach.conf m)) (plant ρ (pendingˢ (f y) (Conf.pos (Mach.conf m) ++ [ ix 1 ]))) []
      inner   : DoneBy (Conf.heap (Mach.conf m)) (flatMapˢ op f fl oc k r pl t ls) []

  -- The two cells a lane's start writes past its world's growth: the
  -- count and the list.
  wrote : ∀ {h v A} → h ⊑ v → FlatKit.Flat A h → List (Name v)
  wrote τ fl = (_ , wkR τ (FlatKit.Flat.active fl)) ∷ (_ , wkR τ (FlatKit.Flat.lanes fl)) ∷ []

  -- Neither is a cell the queue reads.
  wrote-keeps : ∀ {h v A} {τ : h ⊑ v} {fl : FlatKit.Flat A h} {H H′ : Heapᴹ v} → Offʰ H H′ (wrote τ fl) → Keeps H H′
  wrote-keeps off = record
    { spends = λ hd e → trans (cong lower (off hd ((λ ()) ∷ (λ ()) ∷ []))) e
    ; gates  = λ l e → trans (cong lower (off l ((λ ()) ∷ (λ ()) ∷ []))) e
    ; slots  = λ s → off s ((λ ()) ∷ (λ ()) ∷ [])
    ; subs   = λ r → off r ((λ ()) ∷ (λ ()) ∷ []) }

  -- A WORLD GROWN BY A LANE'S START: the old heap weakened into `base`,
  -- then the count raised and the cut listed, nothing else written; the
  -- cut live past the old names, holding nothing.
  record Grown {h v} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) {A} (fl : FlatKit.Flat A h) (c : Kit.Cut v) : Set₁ where
    field
      base    : Heapᴹ v
      grows   : Grows τ H base
      moved   : Offʰ base H′ (wrote τ fl)
      count   : At.val H′ (wkR τ (FlatKit.Flat.active fl)) ≡ suc (At.val H (FlatKit.Flat.active fl))
      listed  : At.val H′ (wkR τ (FlatKit.Flat.lanes fl)) ≡ c ∷ wkEl (list Kit.cutTy) τ (At.val H (FlatKit.Flat.lanes fl))
      live    : At.val H′ (Kit.live c) ≡ true
      unheld  : At.val H′ (Kit.held c) ≡ nothing
      outside : ∀ {k} (i : h ∋ k) → All (λ n → _≢_ {A = Name v} (k , wk∋ τ i) n) (cutNames c)

  -- A NODE SPLICED: the heap moved only at the new node's names and the
  -- node replanted, its own clauses carried across both moves.  Every
  -- clause above it reads its own names, apart from the new node's, and
  -- the new node unsubscribes as the old did.
  module Spliced {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u) (v : Sub h Δ A)
                 {ns : List (Name h)} (off : Offʰ H H′ ns) (mine : All (_∈ᴸ names v) ns) (fs : AllPairs _≢_ (names (plant ρ v))) where
    private
      offV : Offʰ H H′ (names v)
      offV = Heaps.keep H H′ off (lookupᴬ mine)

    sp-kernels : unsub u ≡ unsub v → (Owes v → Owes u) → (Settled u → Settled v) → (∀ {E o} → At.Holds H u E o → At.Holds H′ v E o)
               → (At.Gated H u → At.Gated H′ v) → (At.Spent H u → At.Spent H′ v) → Kernels H T → Kernels H′ (plant ρ v)
    sp-kernels ue ov sv hv gv dv kn = record { holds   = holds-path ρ v fs offV ue hv (Kernels.holds kn) ; gated = gated-path ρ v fs offV gv dv (Kernels.gated kn)
                                             ; settled = settled-plant H′ ρ v ov sv (Kernels.settled kn) }

    sp-meaning : (∀ ν → At.Fed H u ν → At.Fed H′ v ν) → Meaning H T → Meaning H′ (plant ρ v)
    sp-meaning fv mn = record { fed = Heaps.fed-path H H′ ρ v fs offV fv _ (Meaning.fed mn) }

  -- A LANE'S START RUN: the observer read open, the count up, the cut
  -- allocated and listed, the run at the lane's subscription under `ix 1`,
  -- the rest of the call behind it; the world grown along `grow`, all else
  -- the machine keeps carried along.
  record Started {h} (H : Heapᴹ h) (q : Pos) {w} (ϑ : w ⊑ h) (K : Stack w ⊤) clk (ts : List (Timer h)) (bs : List (Maybe (Playing h)))
                 (td : List (Todo h)) lg en mk {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (y : A) (a : Act h ⊤) : Set₁ where
    field
      {v}     : World
      grow    : h ⊑ v
      heap′   : Heapᴹ v
      cut′    : Kit.Cut v
      {act′}  : Act v ⊤
      {back′} : Act v ⊤
      {ϑ′}    : w ⊑ v
      {ts′}   : List (Timer v)
      {bs′}   : List (Maybe (Playing v))
      {td′}   : List (Todo v)
      runs    : mach ⟨ H , q , run a ϑ K ⟩ clk ts bs td lg en mk
                ⇝ mach ⟨ heap′ , q ++ [ ix 1 ] , run act′ same⊑ (push (back q back′) ϑ′ K) ⟩ clk ts′ bs′ td′ lg en mk
      seq′    : ϑ′ ≡ ϑ ⨾ grow
      timers′ : ts′ ≡ mapList (wkTimer grow) ts
      bursts′ : bs′ ≡ mapList (mapMaybe (wkPlaying grow)) bs
      todo′   : td′ ≡ mapList (wkTodo grow) td
      grown   : Grown grow H heap′ fl cut′
      deep    : q ≢ []
      code′   : act′ ≗ compile (f y) (Here.env (walk ρ top)) grow
                  (Kit.guarded cut′ (Canon.Flat′.lane op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl grow cut′)) (λ σ → Kit.attach (Kit.wkCut σ cut′))
      rests′  : back′ ≗ done tt

  postulate
    -- A lane about to begin runs to its subscription: the observer read
    -- open along the path, then the start's reads, writes and two
    -- allocations, all silent.
    begin-path : ∀ {g ℓ h} {H : Heapᴹ h} {q w} {ϑ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {T : Sub h [] R} {Δ A B op f fl oc k r pl}
                   {t : Sub h Δ A} {ls : List (Lane h Δ B)} {ρ : Path T (flatMapˢ op f fl oc k r pl t ls)} {y : A} {pl′}
               → Begins g ℓ (mach ⟨ H , q , run a ϑ K ⟩ clk ts bs td lg en mk) ρ y pl′ → Started H q ϑ K clk ts bs td lg en mk ρ y a

  -- A stack read at a frame and bursts equal to its own.
  stack-cast : ∀ {h} {t : Sub h [] R} {p w} {ϑ₁ ϑ₂ : w ⊑ h} {K : Stack w ⊤} {xs₁ xs₂}
             → ϑ₂ ≡ ϑ₁ → xs₂ ≡ xs₁ → StackAs t p ϑ₁ K xs₁ → StackAs t p ϑ₂ K xs₂
  stack-cast refl refl sk = sk

  ticked-cast : ∀ {h} {t : Sub h [] R} {n p w} {ϑ₁ ϑ₂ : w ⊑ h} {K : Stack w ⊤} {xs₁ xs₂} (e : ϑ₂ ≡ ϑ₁) (e′ : xs₂ ≡ xs₁)
                {sk : StackAs t p ϑ₁ K xs₁} → Ticked t n sk → Ticked t n (stack-cast e e′ sk)
  ticked-cast refl refl tk = tk

  -- A LIFT READ THROUGH THE WEAKENING: every part along the path reads as
  -- it did, so the step lifts alike.
  module Lifted {h v} {τ : h ⊑ v} {H : Heapᴹ h} {H′ : Heapᴹ v} (gr : Grows τ H H′) where
    open Weakened′ τ using (grow-part; grow-partᴸ)

    mutual
      lifts-grow : ∀ {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} {ρ : Path t u} {s S} → Lifts H ρ s S → Lifts H′ (wkPath τ ρ) s S
      lifts-grow lifts-here = lifts-here
      lifts-grow (lifts-map L) = lifts-map (lifts-grow L)
      lifts-grow (lifts-scan {f = f} {r = r} {s = s} {S = S} L) =
        subst (λ a → Lifts H′ _ s (U.scanˢ f a S)) (Grows.cells gr r) (lifts-scan (lifts-grow L))
      lifts-grow (lifts-take {c = c} lv L) = lifts-take (trans (Grows.cells gr (Kit.live c)) lv) (lifts-grow L)
      lifts-grow (lifts-outer {op = op} {f = f} {fl = fl} {pl = pl} {ls = ls} {s = s} {S = S} {o₀ = o₀} of pb L) =
        subst₂ (λ L′ Q → Lifts H′ _ s (U.outerˢ op (λ a q → U.subscribe (f a) q) o₀ S L′ Q pl)) (grow-partᴸ gr ls) (Grows.cells gr (FlatKit.Flat.queue fl))
          (lifts-outer (subst (OuterFirst S) (sym (grow-partᴸ gr ls)) of)
                       (subst (λ L′ → PoolBehind pl (U.outerOf (just o₀)) (U.earliest L′)) (sym (grow-partᴸ gr ls)) pb) (lifts-grow L))
      lifts-grow (lifts-lanes {op = op} {f = f} {fl = fl} {pl = pl} {t = t} {s = s} {bs = bs} {l = l} {S = S} {as = as} {q = q} LL e lf pb) =
        subst₂ (λ x Q → Lifts H′ _ s (U.laneˢ op (λ a q → U.subscribe (f a) q) x bs l S as Q pl)) (grow-part gr t) (Grows.cells gr (FlatKit.Flat.queue fl))
          (lifts-lanes (liftsLane-grow LL) e (subst (λ x → LaneFirst x q) (sym (grow-part gr t)) lf)
                       (subst (λ x → PoolBehind pl (U.outerOf x) (U.found q bs l S as)) (sym (grow-part gr t)) pb))
      lifts-grow (lifts-source {bd = bd} pb sf L) = lifts-source (trans (grow-part gr bd) pb) sf (lifts-grow L)
      lifts-grow (lifts-body {t = t} pt bf L) = lifts-body (trans (grow-part gr t) pt) bf (lifts-grow L)
      lifts-grow (lifts-shut {t = t} pt e rb L) = lifts-shut (trans (grow-part gr t) pt) e rb (lifts-grow L)
      lifts-grow (lifts-defer L) = lifts-defer (lifts-grow L)

      liftsLane-grow : ∀ {Δ B Δ′ C} {ls : List (Lane h Δ B)} {u : Sub h Δ′ C} {πL : PathLanes ls u} {s bs S as}
                     → LiftsLane H πL s bs S as → LiftsLane H′ (wkPathᴸ τ πL) s bs S as
      liftsLane-grow (lifts-this {c = c} {ls = ls} {s = s} {S = S} lv L) =
        subst (LiftsLane H′ _ s [] S) (grow-partᴸ gr ls) (lifts-this (trans (Grows.cells gr (Kit.live c)) lv) (lifts-grow L))
      liftsLane-grow (lifts-next {l = l} {s = s} {bs = bs} {S = S} {as = as} LL) =
        subst (λ X → LiftsLane H′ _ s (X ++ bs) S as) (grow-partᴸ gr (l ∷ [])) (lifts-next (liftsLane-grow LL))

  -- A LANE BEGUN, IN THE GROWN WORLD: the tree weakened along the growth,
  -- the flatMap its pool `pl′` and the new lane first, pending where it
  -- subscribes.
  module Begun {h} {H : Heapᴹ h} {q w} {ϑ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {T : Sub h [] R} {Δ A B op f fl oc k r pl}
               {t : Sub h Δ A} {ls : List (Lane h Δ B)} {ρ : Path T (flatMapˢ op f fl oc k r pl t ls)} {y : A}
               (s : Started H q ϑ K clk ts bs td lg en mk ρ y a) (pl′ : U.Node Δ B) where
    open Started s

    v′ : Sub v Δ B
    v′ = flatMapˢ op f (FlatKit.wkFlat grow fl) (Kit.wkCut grow oc) (mapMaybe (wk∋ grow) k) (wk∋ grow r) pl′ (wkTree grow t)
           (lane cut′ nothing (pendingˢ (f y) (q ++ [ ix 1 ])) ∷ wkLanes grow ls)

    T′ : Sub v [] R
    T′ = plant (wkPath grow ρ) v′

    ι : Path v′ (pendingˢ (f y) (q ++ [ ix 1 ]))
    ι = in-lanes (this-lane here)

    π′ : Path T′ (pendingˢ (f y) (q ++ [ ix 1 ]))
    π′ = planted (wkPath grow ρ) v′ ⊕ ι

    open Grown grown using (base; grows; moved)

    module Wk = Weakened grow
    module Wk′ = Weakened′ grow

    -- The flatMap's skip as the grown world reads it.
    skipped : U.Step Δ B
    skipped = U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part base (wkTree grow t))
                (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes base (wkLanes grow ls)) (At.val base (wkR grow (FlatKit.Flat.queue fl))) pl′)

    skipped-grow : skipped ≡ U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part H t)
                     (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)
    skipped-grow = trans (cong₂ (λ o L → sk o L (At.val base (wkR grow (FlatKit.Flat.queue fl)))) (Wk′.grow-part grows t) (Wk′.grow-partᴸ grows ls))
                         (cong (sk (At.part H t) (At.partLanes H ls)) (Grows.cells grows (FlatKit.Flat.queue fl)))
      where sk = λ o L Q → U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) o (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ L) Q pl′)

    postulate
      -- The ghost past the flatMap's skip, the lift read in the grown
      -- world: the splice alone.  `ghost-lift` gives it once the names
      -- are fresh, which the leaf does not carry.
      bg-ghosted : ∀ {g S} → Sane [] g → Placed g [] → Deep g [] → Lifts base (wkPath grow ρ) skipped S → U.step g ≡ S
                 → Σ (U.Node [] R) λ g″ → At.part heap′ T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
                   × Σ Pos λ k′ → Σ (Events∞ R) λ r′ → (∀ n → Agree n (residual g) (skip k′ r′)) × Past (Events∞.force r′) (residual g″)

    -- The lane's run compiled where it begins: the env and observer
    -- the growth carried along the path, the lane's observer read in
    -- either world.
    bg-code : Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ v) λ υ → wkEnv υ E′ ≡ Here.env (walk π′ top)
              × act′ ≗ compile (f y) E′ υ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
    bg-code = subst (λ X → Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ v) λ υ → wkEnv υ E′ ≡ Here.env X × act′ ≗ compile (f y) E′ υ (Here.obs X) (Here.kont X))
                (sym walkL)
                (_ , Here.env (walk ρ top) , grow , eR
                 , ≗-trans code′ (compile-cong (f y) (Here.env (walk ρ top)) grow (laneAt-wk grow op f fl cut′ eR oR) (λ _ _ → ≗-refl _)))
      where
        oR : ObsRel (wkObs grow (Here.obs (walk ρ top))) (Here.obs (walk (wkPath grow ρ) top))
        oR = proj₁ (walk-grow grow ρ)
        eR : wkEnv grow (Here.env (walk ρ top)) ≡ Here.env (walk (wkPath grow ρ) top)
        eR = proj₂ (proj₂ (walk-grow grow ρ))
        walkL : walk π′ top ≡ walk ι (walk (wkPath grow ρ) top)
        walkL = trans (walk-⊕ (planted (wkPath grow ρ) v′) ι top) (cong (walk ι) (walk-planted (wkPath grow ρ) v′ top))

    -- The stack grown, then the lane planted: every frame where it was.
    bg-stack : StackAs T q ϑ K bs → StackAs T′ q ϑ′ K bs′
    bg-stack sk = stack-cast seq′ (trans bursts′ (sym (pure-map _ bs))) (restack {v = v′} kin-lane (wkPath grow ρ) (Wk.grow-stack sk))

    stk′ : StackAs T q ϑ K bs → StackAs T′ (q ++ [ ix 1 ]) same⊑ (push (back q back′) ϑ′ K) bs′
    stk′ sk = backAs q [] (<ᵖ-below q []) (≗-trans (wk-same back′) rests′) (bg-stack sk)

    -- The new lane sits in a pool, never under a connect's source.
    bg-alone : (sk : StackAs T q ϑ K bs) → All (λ j → ¬ SrcOf T′ π′ (proj₂ j)) (stackJobs T′ (stk′ sk))
    bg-alone _ = tabulateᴬ λ _ → λ { (src-of β e) → not-src wrap-lane (planted (wkPath grow ρ) v′) β e }

    ca′ : StackAs T q ϑ K bs → CtlAs T′ (q ++ [ ix 1 ]) (run act′ same⊑ (push (back q back′) ϑ′ K)) bs′
    ca′ sk = subAs π′ bg-code (stk′ sk) (bg-alone sk)

    bg-ticked : (sk : StackAs T q ϑ K bs) → Ticked T clk sk → Ticked T′ clk (bg-stack sk)
    bg-ticked sk tk = ticked-cast seq′ (trans bursts′ (sym (pure-map _ bs))) (reticked {v = v′} kin-lane (wkPath grow ρ) (Wk.grow-stack sk) (Wk.grow-ticked sk tk))

    -- The splice alone, each in the grown world.
    postulate
      bg-owns     : (sk : StackAs T q ϑ K bs) → Owned base (wkTree grow T) (runAs [] (≗-refl _) (Wk.grow-stack sk)) → Owned heap′ T′ (ca′ sk)
      bg-heads    : Each base (Heads q) (wkTree grow T) → Each heap′ (Heads (q ++ [ ix 1 ])) T′
      bg-lingered : Lingers base (wkTree grow (Restaged.T′ H ρ pl′)) → Lingers heap′ T′

    -- The growth, then the splice.
    bg-ghost : ∀ {g S} → Sane [] g → Placed g [] → Deep g []
             → Lifts H ρ (U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part H t)
                           (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)) S
             → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part heap′ T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r′ → (∀ n → Agree n (residual g) (skip k′ r′)) × Past (Events∞.force r′) (residual g″)
    bg-ghost {S = S} sn pd dp L sg = bg-ghosted sn pd dp (subst (λ x → Lifts base (wkPath grow ρ) x S) (sym skipped-grow) (Lifted.lifts-grow grows L)) sg

    bg-owned : (sk : StackAs T q ϑ K bs) → Owned H T (runAs [] (≗-refl _) sk) → Owned heap′ T′ (ca′ sk)
    bg-owned sk ow = bg-owns sk (Wk′.grow-run grows sk ow)

    bg-behind : Each H (Heads q) T → Each heap′ (Heads (q ++ [ ix 1 ])) T′
    bg-behind bh = bg-heads (Wk′.grow-each grows bh)

    bg-lingers : Lingers H (Restaged.T′ H ρ pl′) → Lingers heap′ T′
    bg-lingers lg = bg-lingered (Wk′.grow-lingers grows lg)

    -- The flatMap before the start, in the grown world.
    u₀ : Sub v Δ B
    u₀ = wkTree grow (flatMapˢ op f fl oc k r pl t ls)

    -- The flatMap's own clauses across the start: the new lane pending,
    -- counted and listed, holding nothing.
    module Hp = Heaps base heap′

    t′  = wkTree grow t
    ls′ = wkLanes grow ls
    oc′ = Kit.wkCut grow oc
    k′  = mapMaybe (wk∋ grow) k
    r′  = wk∋ grow r
    fl′ = FlatKit.wkFlat grow fl

    -- The flatMap's reads past its count and its list.
    Reads : List (Name v)
    Reads = drop 2 (flatReads fl′ oc′ k′ r′ t′ ls′)

    postulate
      -- No name the flatMap reads past its count and list is one of them.
      bg-apart : AllPairs _≢_ (names T) → ∀ {x} → x ∈ᴸ Reads → All (x ≢_) (wrote grow fl)

    bg-reads : AllPairs _≢_ (names T) → Alike base heap′ Reads
    bg-reads fs = Hp.keeps moved (λ m → m) (bg-apart fs)

    bg-count : At.val heap′ (wkR grow (FlatKit.Flat.active fl)) ≡ suc (At.val base (wkR grow (FlatKit.Flat.active fl)))
    bg-count = trans (Grown.count grown) (cong suc (sym (Grows.cells grows (FlatKit.Flat.active fl))))

    bg-listed : At.val heap′ (wkR grow (FlatKit.Flat.lanes fl)) ≡ cut′ ∷ At.val base (wkR grow (FlatKit.Flat.lanes fl))
    bg-listed = trans (Grown.listed grown) (cong (cut′ ∷_) (sym (Grows.cells grows (FlatKit.Flat.lanes fl))))

    module Reading (fs : AllPairs _≢_ (names T)) where
      ag : Alike base heap′ Reads
      ag = bg-reads fs

      agT : Alike base heap′ (names t′)
      agT j m = ag j (there (++⁺ʳ (cutNames oc′) (++⁺ʳ (quietName k′) (there (++⁺ˡ m)))))

      agL : Alike base heap′ (laneNames ls′)
      agL j m = ag j (inL m)
        where inL : ∀ {x} → x ∈ᴸ laneNames ls′ → x ∈ᴸ Reads
              inL m = there (++⁺ʳ (cutNames oc′) (++⁺ʳ (quietName k′) (there (++⁺ʳ (names t′) m))))

      lv : Hp.Lives ls′
      lv {c} m = agL (Kit.live c) (cut-in ls′ m)

    bg-fed : AllPairs _≢_ (names T) → ∀ ν → At.Fed base u₀ ν → At.Fed heap′ v′ ν
    bg-fed fs ν (d₁ , d₂) = Hp.fed-alike t′ agT ν d₁ , (lift tt , Hp.fedL-alike ls′ agL ν d₂)
      where open Reading fs

    bg-spent : AllPairs _≢_ (names T) → At.Spent base u₀ → At.Spent heap′ v′
    bg-spent fs (c₁ , c₂) = Hp.cut-alike k′ t′ agT c₁ , (lift tt , Hp.spentL-alike ls′ agL c₂)
      where open Reading fs

    bg-gated : AllPairs _≢_ (names T) → At.Gated base u₀ → At.Gated heap′ v′
    bg-gated fs (g₁ , g₂) =
      gated-alike t′ agT g₁
      , subst (λ X → At.GatedLanes heap′ X (lane cut′ nothing (pendingˢ (f y) (q ++ [ ix 1 ])) ∷ ls′)) (sym bg-listed)
              ((λ _ → inj₁ (here refl)) , lift tt , gatedL-mono there ls′ (Hp.gatedL-alike ls′ agL g₂))
      where open Reading fs

    bg-holds : AllPairs _≢_ (names T) → ∀ {E o} → At.Holds base u₀ E o → At.Holds heap′ v′ E o
    bg-holds fs {E} {o} (rf , sl , a , hs , ac , (gone , eq , ga) , hl) =
      trans (cong lower (ag (FlatKit.Flat.refill fl′) (here refl))) rf
      , Hp.slot-alike r′ (ag r′ (there (++⁺ʳ (cutNames oc′) (++⁺ʳ (quietName k′) (here refl))))) sl
      , attached-alike oc′ k′ (ag (Kit.held oc′) (there (there (here refl)))) (λ j m → ag j (there (++⁺ʳ (cutNames oc′) (++⁺ˡ m)))) a
      , holds-alike t′ agT hs
      , trans bg-count (trans (cong suc (trans ac (sym (Hp.count-lives ls′ lv))))
                              (cong (λ b → if b then suc (At.count heap′ ls′) else At.count heap′ ls′) (sym (Grown.live grown))))
      , ( gone
        , trans (cong (_++ gone) bg-listed) (cong (cut′ ∷_) (trans eq (trans (cuts-switches base ls′) (sym (cuts-switches heap′ ls′)))))
        , tabulateᴬ λ {c} m → trans (cong lower (lv (subst (c ∈ᴸ_) (trans eq (cuts-switches base ls′)) (++⁺ʳ (At.val base (FlatKit.Flat.lanes fl′)) m))))
                                    (lookupᴬ ga m) )
      , ( lift (Grown.unheld grown) , lift tt
        , Hp.holdsL-alike ls′ agL {op = op} {f = f} {E = E} {o = o} {fl = fl′} hl )
      where open Reading fs

    bg-settled : Settled u₀ → Settled v′
    bg-settled (b , st , sl) = b , st , tt , tt , sl

    -- The count and the list, both the flatMap's own.
    bg-mine : All (_∈ᴸ names v′) (wrote grow fl)
    bg-mine = here refl ∷ there (there (there (here refl))) ∷ []

    -- The new lane's cut: the only names the start adds.
    bg-names : names v′ ↭ cutNames cut′ ++ names (wkTree grow (flatMapˢ op f fl oc k r pl t ls))
    bg-names = pre (flatNames (FlatKit.wkFlat grow fl)) {cutNames cut′} (pre (cutNames (Kit.wkCut grow oc)) {cutNames cut′} (pre (quietName (mapMaybe (wk∋ grow) k)) {cutNames cut′}
                 (pre (_ ∷ []) {cutNames cut′} (pre (names (wkTree grow t)) {cutNames cut′} ↭-refl′))))

    bg-fresh : AllPairs _≢_ (names T) → AllPairs _≢_ (names T′)
    bg-fresh fs = fresh-plant (wkPath grow ρ) v′ bg-names (((λ ()) ∷ []) ∷ [] ∷ []) (wk-pairs grow T fs)
      (fresh-new grow (λ m∈ → let (_ , _ , e) = wk-img grow T m∈ in to-img grow e)
        ((λ { {_ , _} (i , refl) e → lookupᴬ (Grown.outside grown i) (here refl) (sym e) })
         ∷ (λ { {_ , _} (i , refl) e → lookupᴬ (Grown.outside grown i) (there (here refl)) (sym e) }) ∷ []))

    module Sp (fs : AllPairs _≢_ (names T)) = Spliced base heap′ (wkPath grow ρ) v′ moved bg-mine (bg-fresh fs)

    -- The tree grown, then spliced.
    bg-kernels : AllPairs _≢_ (names T) → Kernels H T → Kernels heap′ T′
    bg-kernels fs kn = Sp.sp-kernels fs refl (λ ()) bg-settled (λ {E} {o} → bg-holds fs {E} {o}) (λ g → bg-gated fs g) (λ d → bg-spent fs d) (Growths.kernels-grow grow grows kn)

    bg-meaning : AllPairs _≢_ (names T) → Meaning H T → Meaning heap′ T′
    bg-meaning fs mn = Sp.sp-meaning fs (bg-fed fs) (Wk′.grow-meaning grows mn)

    -- The tree grown, the count and list written, the lane planted: the
    -- run one level down, past the start's own position.
    bg-queue : Queue H q clk ts T → Queue heap′ (q ++ [ ix 1 ]) clk ts′ T′
    bg-queue qu = subst (λ ts″ → Queue heap′ (q ++ [ ix 1 ]) clk ts″ T′) (trans (pure-map (wkTimer grow) ts) (sym timers′))
                    (record { timed = Queue.timed qu′ ; joined = Queue.joined qu′ ; ordered = Queue.ordered qu′
                            ; ahead = ahead-under q 1 (λ e → ⊥-elim (deep e)) (Queue.ahead qu′) })
      where qu′ = plant-queue heap′ (wkPath grow ρ) v′ refl refl (λ _ → refl) (queue-keeps (wrote-keeps {τ = grow} {fl = fl} moved) (Wk′.grow-queue grows qu))

    -- The flags across the start: the lane swapped in for its pending
    -- node in the grown world, then the count and list written.
    bg-flags : AllPairs _≢_ (names T) → ∀ {s S} → Lifts H ρ s S → DoneBy H (plant ρ (pendingˢ (f y) (q ++ [ ix 1 ]))) []
             → DoneBy H (flatMapˢ op f fl oc k r pl t ls) [] → DoneBy heap′ T′ []
    bg-flags fs L dF dI = let-go heap′ (planted ρw v′) (bg-fresh fs) sh (alive heap′ (Grown.live grown)) r₂
      where
        open Reading fs
        ρw = wkPath grow ρ
        P₀ = pendingˢ (f y) (q ++ [ ix 1 ])
        G  = λ a j → U.subscribe (f a) j
        sw₀ : seen base ρw ≡ true
        sw₀ = lifts-seen (Lifted.lifts-grow grows L)
        alive : ∀ G′ → At.val G′ (Kit.live cut′) ≡ true → is-just (At.part G′ v′) ≡ true
        alive G′ lv = lane-opens G′ op G (At.part G′ t′) (At.val G′ (Kit.live cut′)) (U.subscribe (f y) (q ++ [ ix 1 ])) (At.partLanes G′ ls′)
                        (At.val G′ (FlatKit.Flat.queue fl′)) pl′ lv
        lvb : At.val base (Kit.live cut′) ≡ true
        lvb = trans (sym (cong lower (moved (Kit.live cut′) ((λ e → lookupᴬ (Grown.outside grown (FlatKit.Flat.active fl)) (here refl) (sym e))
                                                           ∷ (λ e → lookupᴬ (Grown.outside grown (FlatKit.Flat.lanes fl)) (here refl) (sym e)) ∷ []))))
                    (Grown.live grown)
        i₁ : DoneBy base u₀ []
        i₁ = Wk′.grow-flags grows dI
        c₁ : DoneBy base (plant ρw P₀) []
        c₁ = subst (λ x → DoneBy base x []) (wk-plant grow ρ (pendingˢ (f y) (q ++ [ ix 1 ]))) (Wk′.grow-flags grows dF)
        v₁ : DoneBy base v′ []
        v₁ = Flag.db-flat base {ns = []} (i₁ here refl) (Flag.db-sub base i₁ (in-outer here) refl)
               (Flag.dbL-cons base {ns = []} (λ _ → pending-flags base) (Flag.dbL-of base i₁))
        sw : DoneBy base T′ []
        sw = subst (λ x → DoneBy base x []) (plant-planted ρw P₀ v′) (flags-swap base (planted ρw P₀) v′ (alive base lvb) v₁ c₁)
        g₁ : DoneBy base T′ (outers (planted ρw v′))
        g₁ = grip base (planted ρw v′) (bg-fresh fs) (trans (seen-planted base ρw v′) sw₀) (alive base lvb) sw
        X = outers (planted ρw v′)
        fv = fresh-path (planted ρw v′) (bg-fresh fs)
        vd : AllPairs _≢_ (names v′) → At.val heap′ (FlatKit.Flat.outerDone fl′) ≡ At.val base (FlatKit.Flat.outerDone fl′)
        vd (a₀ ∷ a₁ ∷ _) = cong lower (moved (FlatKit.Flat.outerDone fl′) ((λ e → lookupᴬ a₀ (here refl) (sym e)) ∷ (λ e → lookupᴬ a₁ (there (here refl)) e) ∷ []))
        fb : DoneBy base v′ (X ++ []) → DoneBy heap′ v′ X
        fb d₀ = Flag.db-flat heap′ {ns = X} (flagged-moved base heap′ {fl = fl′} {so = t′} (vd fv) (part-alike base heap′ t′ agT) (d here refl))
                  (flags-alike base heap′ agT (Flag.db-sub base d (in-outer here) refl))
                  (Flag.dbL-cons heap′ {ns = X} (λ _ → pending-flags heap′) (flagsL-alike base heap′ agL (Flag.dbL-tail base (Flag.dbL-of base d))))
          where d = subst (DoneBy base v′) (++-identityʳ X) d₀
        r₁ : DoneBy heap′ (plant (planted ρw v′) v′) X
        r₁ = Shift.shift-flags base heap′ {T = T′} {u = v′} (planted ρw v′) moved bg-mine (bg-fresh fs) v′ {ns₀ = []} (λ ()) (λ _ → alive base lvb) fb
               (subst (DoneBy base T′) (sym (++-identityʳ X)) g₁)
        r₂ : DoneBy heap′ T′ X
        r₂ = subst (λ x → DoneBy heap′ x X) (plant-planted ρw v′ v′) r₁
        pw : AllPairs _≢_ (names u₀ ++ names (plant ρw P₀))
        pw = apart-unplant ρw (wk-pairs grow T fs)
        al : Alike base heap′ (names (plant ρw P₀))
        al j m = moved j (let A′ = apart-l (names u₀) pw m in lookupᴬ A′ (here refl) ∷ lookupᴬ A′ (there (there (there (here refl)))) ∷ [])
        sh : seen heap′ (planted ρw v′) ≡ true
        sh = trans (seen-planted heap′ ρw v′) (trans (sym (seen-planted heap′ ρw P₀))
               (trans (seen-alike base heap′ (planted ρw P₀) al) (trans (seen-planted base ρw P₀) sw₀)))

  -- The ghost's admit with room: the lane first, nothing dropped.
  admit-room : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) q a (ls : List (U.Node Γ B)) qs d → roomy op (length ls) ≡ true
             → U.admit op g q a ls qs d ≡ (g a q ∷ ls , qs , U.idleᶜ)
  admit-room (T.mergeᶠ nothing)  g q a ls      qs d _  = refl
  admit-room (T.mergeᶠ (just n)) g q a ls      qs d e  rewrite e = refl
  admit-room T.switchᶠ           g q a ls      qs d ()
  admit-room T.exhaustᶠ          g q a []      qs d _  = refl
  admit-room T.exhaustᶠ          g q a (_ ∷ _) qs d ()

  -- An outer's value admitted: the flatMap's skip under it.
  outer-admit : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) o q a o′ ls qs p {ls′ qs′ d}
              → U.admit op g (q ++ [ ix 1 ]) a ls qs (U.restsᶜ ls) ≡ (ls′ , qs′ , d)
              → U.outerˢ op g o (U.outˢ q a o′) ls qs p ≡ U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op g (just o′) ls′ qs′ (U.unionᶜ p d))
  outer-admit op g o q a o′ ls qs p e rewrite e = refl

  postulate
    -- An outer's value reaching its flatMap: the count its lanes, each
    -- live lane showing.
    --
    -- Not a fact of the kernels: a lane's part is gone before its cut is
    -- dropped, while its own end climbs to `close-lanes`; no outer value
    -- arrives in between, and no field of the call says so.
    lanes-counted : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                    {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                    (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {y : A}
                  → Calling g ℓ m₁ (ρ ⊕ in-outer here) (sends y)
                  → At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl) ≡ length (At.partLanes (Conf.heap (Mach.conf m₁)) ls)

  -- A lane begun: counted, cut, listed and subscribed under the run's
  -- `ix 1`, the run at the lane's pending node; the ghost past the
  -- flatMap's skip, the lane its own.
  lane-begin : ∀ {g m} (st : Strong g m) {m₀ Δ A B op f fl oc k r pl} {T : Sub (Conf.world (Mach.conf m₀)) [] R}
               {t : Sub (Conf.world (Mach.conf m₀)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₀)) Δ B)}
               {ρ : Path T (flatMapˢ op f fl oc k r pl t ls)} {y : A} {pl′}
             → Begins g (loadOf st) m₀ ρ y pl′ → Hopped st m₀
  lane-begin st {m₀ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {pl′ = pl′}
    b@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; stack = sk ; lifted = S , L , sg ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
             ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr
             ; flags = dF ; inner = dI }
    with begin-path b
  ... | sr with Begun.bg-ghost sr pl′ sn pd dp L sg
  ...   | g″ , pg , sn″ , pd″ , dp″ , k″ , r″ , ag , pp =
    g″ , _ , Started.runs sr
    , carried (record
      { sane = sn″ ; placed = pd″ ; deep = dp″ ; tree = Begun.T′ sr pl′ ; ctlAs = Begun.ca′ sr pl′ sk ; meets = pg
      ; owned′ = owned-to (Begun.bg-owned sr pl′ sk ow) ; kernels = Begun.bg-kernels sr pl′ fs kn ; meaning = Begun.bg-meaning sr pl′ fs mn
      ; queue = subst (λ ts″ → Queue (Started.heap′ sr) (q ++ [ ix 1 ]) clk ts″ (Begun.T′ sr pl′)) refl (Begun.bg-queue sr pl′ qu)
      ; books = record { fresh = Begun.bg-fresh sr pl′ fs
                       ; clocked = trans (proj₁ ck) (sym (tick-under q 1 (Started.deep sr))) , proj₁ ck , Begun.bg-ticked sr pl′ sk (proj₂ ck)
                       ; paidUp = trans (Started.todo′ sr) (cong (mapList (wkTodo (Started.grow sr))) pu) ; running = rn }
      ; sorted = sorted-⇝ so (Started.runs sr) ; behind′ = Eaching.each-to _ _ (Begun.bg-behind sr pl′ bh) ; lingers′ = Lingering.lingers-to _ (Begun.bg-lingers sr pl′ lgr)
      ; flags = Begun.bg-flags sr pl′ fs L dF dI })
    , passed ag pp

  -- An admitted value with room: its lane begun where the value is, the
  -- ghost's admit the runtime's.
  outer-start : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
              → roomy op (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl)) ≡ true
              → ∀ {a} → m₁ ⇝ rerun m₁ (Calling.ϑ cl) (Calling.K cl) a → a ≗ startAt ρ y → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)
  outer-start st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} ρ {y}
    cl@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr ; kept = kp } rm p c
    with lifts-split ρ (in-outer here) L
  ... | _ , lifts-outer {o₀ = o₀} _ _ lifts-here , Lρ = lane-begin st (record
      { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; code = c
      ; opens = proj₂ (∧-split _ (trans (sym (opened-⊕ hp true ρ (in-outer here))) (calling-open (ρ ⊕ in-outer here) cl)))
      ; stack = sk
      ; lifted = S , subst (λ o → Lifts hp ρ (U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op G o (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ LS) QS (U.unionᶜ po U.idleᶜ))) S)
                           (sym pv)
                           (subst (λ s′ → Lifts hp ρ s′ S)
                                  (outer-admit op G o₀ q y c′ LS QS po
                                     (admit-room op G (q ++ [ ix 1 ]) y LS QS (U.restsᶜ LS) (subst (λ n → roomy op n ≡ true) (lanes-counted ρ cl) rm)))
                                  Lρ)
                 , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so p ; behind = bh ; lingers = Restaged.pool-idle hp ρ (U.unionᶜ po U.idleᶜ) fs refl (ended-past cl) lgr
      ; flags = flags-swap hp ρ (pendingˢ (f y) (q ++ [ ix 1 ])) (sym (cong (λ o′ → is-just (At.merged hp op G o′ LS QS po)) pv)) (pending-flags hp) d₀
      ; inner = Flag.db-sub hp d₀ ρ (lifts-seen Lρ) })
    where
      G  = λ a j → U.subscribe (f a) j
      LS = At.partLanes hp ls
      QS = At.val hp (FlatKit.Flat.queue fl)
      d₀ = let-go hp (ρ ⊕ in-outer here) fs (lifts-seen L) (cong is-just pv) (Calling.flags cl)

  postulate
    -- A bounded merge full: the value queued, the ghost past the outer's
    -- skip, the value its queue's last.
    outer-queued : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {n f fl oc k r pl}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                   (ρ : Path T (flatMapˢ (T.mergeᶠ (just n)) f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
                 → (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl) <ᵇ n) ≡ false
                 → ∀ {a} → a ≗ Kit.modifyF (FlatKit.Flat.queue fl) (_++ [ y ]) → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)

    -- An exhaust busy: the value dropped, the ghost past the outer's skip.
    outer-drop : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f fl oc k r pl}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                 (ρ : Path T (flatMapˢ T.exhaustᶠ f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
               → (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl) ≡ᵇ 0) ≡ false
               → ∀ {a} → a ≗ done tt → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)

    -- A switch admitting: its lanes killed, their rests the pool's, a lane
    -- begun for the value.
    outer-switch : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f fl oc k r pl}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                   (ρ : Path T (flatMapˢ T.switchᶠ f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
                 → ∀ {a} → a ≗ admitAt ρ T.switchᶠ y → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)

  -- A bounded merge's count read: room, a lane begun; else queued.
  room-n : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {n f fl oc k r pl}
           {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
           (ρ : Path T (flatMapˢ (T.mergeᶠ (just n)) f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
         → (b : Bool) → b ≡ (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl) <ᵇ n)
         → ∀ {a} → m₁ ⇝ rerun m₁ (Calling.ϑ cl) (Calling.K cl) a
         → a ≗ (if b then startAt ρ y else Kit.modifyF (FlatKit.Flat.queue fl) (_++ [ y ])) → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)
  room-n st ρ cl true  e p c = outer-start st ρ cl (sym e) p c
  room-n st ρ cl false e p c = outer-queued st ρ cl (sym e) c

  -- An exhaust's count read: idle, a lane begun; else dropped.
  room-x : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f fl oc k r pl}
           {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
           (ρ : Path T (flatMapˢ T.exhaustᶠ f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
         → (b : Bool) → b ≡ (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.active fl) ≡ᵇ 0)
         → ∀ {a} → m₁ ⇝ rerun m₁ (Calling.ϑ cl) (Calling.K cl) a → a ≗ Kit.when b (startAt ρ y) → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)
  room-x st ρ cl true  e p c = outer-start st ρ cl (sym e) p c
  room-x st ρ cl false e p c = outer-drop st ρ cl (sym e) c

  -- A value admitted, by the flatMap's policy.
  admits : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
           {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
           (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {y : A} (cl : Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y))
         → ∀ {a} → m₁ ⇝ rerun m₁ (Calling.ϑ cl) (Calling.K cl) a → a ≗ admitAt ρ op y → Hopped st (rerun m₁ (Calling.ϑ cl) (Calling.K cl) a)
  admits st {op = T.mergeᶠ nothing} ρ cl p c = outer-start st ρ cl refl p c
  admits st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = T.mergeᶠ (just n)} {fl = fl} ρ {y} cl p c with reads c
  ... | k₂ , f₂ , p₂ = hopped-pre p₂ (room-n st ρ cl (At.val hp (FlatKit.Flat.active fl) <ᵇ n) refl (⇝-trans p p₂)
                         (≗-trans (f₂ same⊑ (At.val hp (FlatKit.Flat.active fl)))
                                  (wk-same (if At.val hp (FlatKit.Flat.active fl) <ᵇ n then startAt ρ y else Kit.modifyF (FlatKit.Flat.queue fl) (_++ [ y ])))))
  admits st {op = T.switchᶠ} ρ cl p c = outer-switch st ρ cl c
  admits st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = T.exhaustᶠ} {fl = fl} ρ {y} cl p c with reads c
  ... | k₂ , f₂ , p₂ = hopped-pre p₂ (room-x st ρ cl (At.val hp (FlatKit.Flat.active fl) ≡ᵇ 0) refl (⇝-trans p p₂)
                         (≗-trans (f₂ same⊑ (At.val hp (FlatKit.Flat.active fl)))
                                  (wk-same (Kit.when (At.val hp (FlatKit.Flat.active fl) ≡ᵇ 0) (startAt ρ y)))))

  -- A value reaching a flatMap's outer: its guard read open, the value
  -- admitted.
  climb-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {y : A}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (sends y) → Called st m₁ (ρ ⊕ in-outer here)
  climb-outer st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {oc = oc} ρ {y} cl@record { ctl = refl ; code = cd }
    with reads (subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-outer here) top) cd)
  ... | k₁ , f₁ , p₁ = landed (hopped-pre p₁ (admits st ρ cl p₁
        (≗-trans (f₁ same⊑ (At.val hp (Kit.live oc)))
                 (≗-trans (wk-same (Kit.when (At.val hp (Kit.live oc)) (admitAt ρ op y))) (open-code (outer-live ρ cl))))))

  -- A signal reaching a flatMap's outer.
  call-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
               (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {sg : Signal T A}
             → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) sg → Called st m₁ (ρ ⊕ in-outer here)
  call-outer st ρ {sends _}  cl = climb-outer st ρ cl
  call-outer st ρ {closes _} cl = close-outer st ρ cl
