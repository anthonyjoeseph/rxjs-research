{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A TAKE: its rise, and its end.
module adequacy.Climbs.Take where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.Nat.Properties using (≤-refl)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (_<_; z≤n)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; last; ix; <ᵖ-below)
open import denotation.MonotonicList using (Agree)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted using (_≤ᵖ_; ≤ᵖ-child)
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
open import Data.Bool using (Bool; true; false; if_then_else_)
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

open Events∞

module ClimbTake (R : Set) where
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
  open Tearing R using (cuts; attached-alike; cuts-switches; fresh-path; fresh-lanes; part-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; apart-l; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Forking R using (walk-planted)
  open Aliking R using (walk-grow; compile-cong; laneAt-wk; ObsRel)
  open Taking R using (tick-ix0)
  open Naming R using (pre; pairs-↭; names-plant-↭; fresh-plant; fresh-new; wk-pairs; wk-img; to-img)
  open Ghosting R using (residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; passed; Past; Lefts)
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
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pin-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag; tw-alike)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined)
  open FramingRepool R using (Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (take-part; take-pass; takes-less; end-code; lifts-planted; lefts-planted; height-planted; out-step; out-code; and-false; ending-part)
  -- A TAKE ENDED: the take a stage on, `ending` where the run is over
  -- what its source's failing value left, nothing else of the tree
  -- moved, and the completion its one call owed: ahead of the stack when
  -- exclusive, behind the failing value under `ix 0` when inclusive.
  module Ended {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A i p c k} {u : Sub h Δ A} (ρ : Path T (takeWhileˢ i p c k taking u))
               (q : Pos) (c′ : U.Node Δ A) where
    w₀ = takeWhileˢ i p c k taking u
    v  = takeWhileˢ i p c k (Strongly.ending q c′) u
    T′ = plant ρ v

    kin : Kin w₀ v
    kin = kin-end

    postulate
      -- Past the take's end, no part of the planted tree heads at the
      -- run's own position: the one event there is the value the take
      -- ended over, and the take now heads under `last`.
      out-deeper : Each H (Heads q) T′ → Each H (Heads (q ++ [ ix 0 ])) T′

      -- The ghost alike the planted tree's part: both step to the take's
      -- end, the part through its `ending`.
      --
      -- `Lefts` ties every free node the lift carries, a connect's
      -- source node among them, to its node's leftover in meaning.
      --
      -- DEAD ROUTE: a body over `ghost-lift`.  The take's end lifts to the root as an end wherever no flatMap or connect above turns it into a skip, so there is no skip to lift past; and where it crosses a connect's source, `U.sourceˢ` reads the source node `lifts-source` leaves free.
      end-ghost : ∀ {g S} → Sane [] g → Placed g [] → Deep g [] → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
              → (L : Lifts H ρ (U.endˢ (q ++ [ last ])) S) → Lefts H L → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ [] × (∀ n → Agree n (residual g) (residual g″))

    end-stack : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
    end-stack = restack kin ρ

    -- A live take over its source's part.
    take-live : At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′ → At.part H w₀ ≡ just (U.takeWhileᶜ i p c′)
    take-live lv pv rewrite lv | pv = refl

    -- The take's own heads and ties, ended: its part the source's,
    -- `ending` owing what the source left, nothing below it seen.
    end-heading : At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′ → Heading H H q w₀ v
    end-heading lv pv = record
      { head-revive = λ _ → cong is-just (take-live lv pv)
      ; head-told   = λ j e₀ e′ m →
          subst (λ b → _ ∈ᴸ untold j b) (just-injective (trans (sym (take-live lv pv)) e₀))
                (subst (λ b → _ ∈ᴸ untold j b) (sym (just-injective (trans (sym (ending-part H {i = i} {p} {c} {k} {u} {q} {c′} lv)) e′))) m)
      ; head-below  = λ _ → Build.each-take H (Heads q)
          (λ e hk → subst (Heads q) (just-injective (trans (sym (ending-part H {i = i} {p} {c} {k} {u} {q} {c′} lv)) e))
                          (λ hk′ → subst (q ≤ᵖ_) (just-injective hk′) (≤ᵖ-child q (inj₁ refl))) hk)
          (λ ok → ⊥-elim (and-false (At.val H (Kit.live c)) ok)) }

    end-lingering : At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′ → Lingering H H w₀ v
    end-lingering lv pv = record
      { ling-revive = λ _ → cong is-just (take-live lv pv)
      ; ling-rested = tw-alike {x = At.leftover H u} refl
      ; ling-below  = λ _ → Linger.lg-take H (λ ok → ⊥-elim (and-false (At.val H (Kit.live c)) ok)) }

    end-ticked : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (end-stack sk)
    end-ticked n sk = reticked kin ρ {n = n} sk

    end-owned : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (e : act ≗ ⟦ take1C (planted ρ v) ∷ [] ⟧ᶜ)
              → Owned H T (runAs [] (≗-refl _) sk) → Owned H T′ (runAs (take1C (planted ρ v) ∷ []) e (end-stack sk))
    end-owned sk e ow = owned-run kin ρ sk [] e refl ow

    out-owned : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {N : Act h ⊤} (sk : StackAs T q ϑ K bs) (e : wkAct same⊑ N ≗ ⟦ take1C (planted ρ v) ∷ [] ⟧ᶜ)
              → Owned H T (runAs [] (≗-refl _) sk)
              → Owned H T′ (runAs [] (≗-refl _) (backAs q (take1C (planted ρ v) ∷ []) (<ᵖ-below q {ix 0} []) e (end-stack sk)))
    out-owned sk e ow =
      owned-move H (runAs [] (≗-refl _) (backAs q (take1C (planted ρ v) ∷ []) (<ᵖ-below q {ix 0} []) e (end-stack sk))) refl refl refl
        (owned-run kin ρ sk [] (≗-refl _) refl ow)

    end-behind : AllPairs _≢_ (names T) → Untold H q T → Ends H T → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
               → Each H (Heads q) T → Each H (Heads q) T′
    end-behind fs ut en lv pv = Shift.shift-behind H H ρ (λ j _ → refl) [] fs v ut en (end-heading lv pv)

    end-flags : AllPairs _≢_ (names T) → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′ → DoneBy H T (outers ρ) → DoneBy H T′ (outers (planted ρ v))
    end-flags fs lv pv d =
      subst (DoneBy H T′) (sym (outers-planted ρ v))
        (Shift.shift-flags H H ρ (λ j _ → refl) [] fs v (λ ()) (λ _ → cong is-just (take-part H {i = i} {p = p} {c = c} {k = k} {u = u} lv pv))
          (λ _ → Flag.db-take H {ns = outers ρ} (λ ok → false≢ (proj₂ (∧-split (At.val H (Kit.live c)) ok)))) (subst (DoneBy H T) (sym (++-identityʳ (outers ρ))) d))

    end-lingers : AllPairs _≢_ (names T) → Ends H T → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′ → Lingers H T → Lingers H T′
    end-lingers fs en lv pv = Shift.shift-lingers H H ρ (λ j _ → refl) [] fs v en (end-lingering lv pv)

    out-behind : AllPairs _≢_ (names T) → Untold H q T → Ends H T → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
               → Each H (Heads q) T → Each H (Heads (q ++ [ ix 0 ])) T′
    out-behind fs ut en lv pv bh = out-deeper (end-behind fs ut en lv pv bh)

    -- The take's stage read by its part alone: no kernel, feed or queue
    -- clause moves.
    end-kernels : Kernels H T → Kernels H T′
    end-kernels kn = record { holds   = holds-plant H {t = T} ρ v refl (λ hs → hs) (Kernels.holds kn)
                            ; gated   = gated-plant H {t = T} ρ v (λ g → g) (λ d → d) (Kernels.gated kn)
                            ; settled = settled-plant H {t = T} ρ v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

    end-meaning : Meaning H T → Meaning H T′
    end-meaning mn = record { fed = fed-plant H {t = T} ρ v (λ _ fd → fd) _ (Meaning.fed mn) }

    end-queue : ∀ {clk ts} → Queue H q clk ts T → Queue H q clk ts T′
    end-queue = plant-queue H ρ v refl refl (λ _ → refl)

    out-queue : ∀ {clk ts} → Queue H q clk ts T → Queue H (q ++ [ ix 0 ]) clk ts T′
    out-queue qu = record { timed = Queue.timed (end-queue qu) ; joined = Queue.joined (end-queue qu)
                          ; ordered = Queue.ordered qu ; ahead = ahead-under q 0 (λ _ → z≤n) (Queue.ahead qu) }

  -- A value an exclusive takeWhile fails on: its guard read, the take
  -- ended, its completion the agenda's call.
  take-end : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {p c k}
             {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ false p c k taking u)) {y : A} → p y ≡ false
           → Calling g ℓ m₁ (ρ ⊕ in-take here) (sends y)
           → Σ (U.Node [] R) λ g″ → Σ Mach λ m₀ → m₁ ⇝ m₀ × Σ (Carried g″ m₀) λ cr
             → (∀ n → Agree n (residual g) (residual g″)) × load m₀ (Carried.tree cr) ⊏ load m₁ T
  take-end {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    cl@record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; lefts = lt ; flags = dn }
    with lifts-split ρ (in-take here) L in eqE | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f
    with Ended.end-ghost hp ρ q c′ sn pl dp lv pv (subst (λ s → Lifts hp ρ s S) (cong (U.taking false p q y c′) py) Lρ)
                         (lefts-subst (λ s → s) (cong (U.taking false p q y c′) py) (lefts-up ρ (in-take here) eqE lt)) sg
  ...   | g″ , pg , sn″ , pl″ , dp″ , ag =
    g″ , _ , then refl now
    , record
        { sane = sn″ ; placed = pl″ ; deep = dp″ ; tree = Ended.T′ hp ρ q c′
        ; ctlAs = runAs (take1C (planted ρ v) ∷ []) e (Ended.end-stack hp ρ q c′ sk)
        ; meets = pg
        ; owned′ = owned-to (Ended.end-owned hp ρ q c′ sk e ow)
        ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.end-queue hp ρ q c′ qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind′ = Eaching.each-to _ _ (Ended.end-behind hp ρ q c′ fs (tells-past cl) (ended-past cl) lv pv bh) ; lingers′ = Lingering.lingers-to _ (Ended.end-lingers hp ρ q c′ fs (ended-past cl) lv pv lgr) ; flags = let-go hp (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs) (lifts-seen (lifts-planted ρ v Lρ))
                         (cong is-just (ending-part hp {i = false} {p = p} {c = c} {k = k} {u = u} lv)) (Ended.end-flags hp ρ q c′ fs lv pv (done-up ρ (in-take here) refl dn)) }
    , ag , inj₂ (pend-plant {t = T} ρ v refl , inj₁ (takes-less ρ v ≤-refl))
    where
      v = takeWhileˢ false p c k (Strongly.ending q c′) u
      e = ≗-trans (f same⊑ (At.val hp (Kit.live c))) (≗-trans (wk-same _) (≗-trans (end-code lv py)
            (subst (λ W → _ ≗ (under last (Observer.complete (Here.obs W)) (Kit.cut c) >>ᴬ done tt)) (sym (walk-planted ρ v top)) (seq-done _))))

  -- A value an inclusive takeWhile fails on: its guard read, delivered
  -- under `ix 0`, the take `ending` where the run is, its completion a
  -- call owed back where the take was.
  take-out : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {p c k}
             {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ true p c k taking u)) {y : A} → p y ≡ false
           → Calling g ℓ m₁ (ρ ⊕ in-take here) (sends y) → Rises g (load m₁ T) m₁ (ρ ⊕ in-take here)
  take-out {g} {m₁ = mach ⟨ hp , q , run _ ϑ K ⟩ clk ts bs td lg en mk} {T = T} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    cl@record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; lefts = lt ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L in eqO | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f
    with out-step {hp = hp} {q = q} {clk} {ts} {bs} {td} {lg} {en} {mk} {ϑ = ϑ} {K = K}
                  (≗-trans (f same⊑ (At.val hp (Kit.live c))) (≗-trans (wk-same _) (out-code lv py)))
  ...   | M′ , N′ , eM , eN , path =
    rises {σ′ = planted ρ v} {sg′ = sends y} (then refl path) (subst (_< height (ρ ⊕ in-take here)) (sym (height-planted ρ v)) (one-lower ρ one-take)) (record
      { sane = sn ; placed = pl ; deep = dp ; ctl = refl
      ; code = subst (λ W → M′ ≗ Observer.next (Here.obs W) y) (sym (walk-planted ρ v top)) eM
      ; stack = st
      ; lifted = U.endingᶜ (q ++ [ last ]) c′ , ending-part hp {i = true} {p = p} {c = c} {k = k} {u = u} lv , S
               , lifts-planted ρ v (subst (λ s → Lifts hp ρ s S) (cong (U.taking true p q y c′) py) Lρ) , sg
      ; lefts = lefts-planted ρ v refl (subst (λ s → Lifts hp ρ s S) (cong (U.taking true p q y c′) py) Lρ)
                  (lefts-subst (λ s → s) (cong (U.taking true p q y c′) py) (lefts-up ρ (in-take here) eqO lt))
      ; owned = Ended.out-owned hp ρ q c′ sk e ow
      ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.out-queue hp ρ q c′ qu
      ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                       ; clocked = trans (proj₁ ck) (sym (tick-ix0 q)) , proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck)
                       ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl path) ; behind = Ended.out-behind hp ρ q c′ fs (tells-past cl) (ended-past cl) lv pv bh ; lingers = Ended.end-lingers hp ρ q c′ fs (ended-past cl) lv pv lgr ; flags = Ended.end-flags hp ρ q c′ fs lv pv (done-up ρ (in-take here) refl dn)
      ; kept = inj₂ (inj₂ (pend-plant {t = T} ρ v refl , inj₁ (takes-less ρ v ≤-refl))) })
    where
      v = takeWhileˢ true p c k (Strongly.ending q c′) u
      X = under last (Observer.complete (Here.obs (walk ρ top))) (Kit.cut c)
      e = ≗-trans (wk-same N′) (≗-trans eN
            (subst (λ W → X ≗ (under last (Observer.complete (Here.obs W)) (Kit.cut c) >>ᴬ done tt)) (sym (walk-planted ρ v top)) (seq-done X)))
      st = backAs q (take1C (planted ρ v) ∷ []) (<ᵖ-below q {ix 0} []) e (Ended.end-stack hp ρ q c′ sk)

  -- The signal risen, held to the call's load.
  rise : ∀ {g m} {st : Strong g m} {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v}
       → load m₁ T ≼ loadOf st → Rises g (load m₁ T) m₁ σ → Called st m₁ σ
  rise le (rises path lt cl) = rose path lt (relevel cl le)

  -- A guard read open: what it guards.
  open-code : ∀ {w} {b : Bool} {m : Act w ⊤} → b ≡ true → Kit.when b m ≗ m
  open-code refl = ≗-refl _

  -- A live take over a gone source is gone.
  gone-take : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} → At.val H (Kit.live c) ≡ true
            → At.part H u ≡ nothing → At.part H (takeWhileˢ i p c k taking u) ≡ nothing
  gone-take H lv gn rewrite lv | gn = refl

  -- A signal through a takeWhile.  A value passed one operator up; or
  -- failing, delivered first when inclusive, then the completion climbs,
  -- then the cut.  The failing value cannot stop at the completion owed
  -- with the ghost alike unless the take's stage counts: the control's
  -- work rises.  An end through a live take: its guard read open, one
  -- operator up, the take showing its source's end.
  call-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u)) {sg : Signal T A}
            → Calling g (loadOf st) m₁ (ρ ⊕ in-take here) sg → Called st m₁ (ρ ⊕ in-take here)
  call-take st {i = i} {p} ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-take here) L
  ...   | _ , lifts-take lv lifts-here , Lρ with p y in py | i
  ...     | true  | _     = rise (Calling.kept cl) (take-pass ρ py cl)
  ...     | false | true  = rise (Calling.kept cl) (take-out ρ py cl)
  ...     | false | false with take-end ρ py cl
  ...       | g″ , m₀ , path , cr , ag , lt = landed (g″ , m₀ , path , carried cr , lowered ag (inj₁ (⊏-≼ lt (Calling.kept cl))))
  call-take st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ {closes ks}
    record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg , hl ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; lefts = lt ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L in eqC | subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rose {sg′ = closes ks} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; deep = dp ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (bind≗ (≗-trans (wk-same _) (open-code lv)) λ _ → wk-same _)
      ; stack = sk
      ; lifted = gone-take hp {i = i} {p = p} {c = c} {k = k} {u = u} lv gn , S , Lρ , sg , healed-split ρ (in-take here) hl
      ; lefts = lefts-up ρ (in-take here) eqC lt
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; lingers = lgr ; flags = done-up ρ (in-take here) refl dn ; kept = kp })

  -- A write, one step: the cell stored, what follows it run.
  writes : ∀ {h} {hp : Heapᴹ h} {q w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {t} {r : Ref h t} {z} {n : Act h ⊤}
         → a ≗ writeRef r z n
         → Σ (Act h ⊤) λ n′ → n′ ≗ n × (mach ⟨ hp , q , run a σ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ store hp r (lift z) , q , run n′ σ K ⟩ clk ts bs td lg en mk)
  writes (writeRef≗ refl refl e) = _ , e , then refl now

  -- A read, one step: the cell's value handed to what follows it.
  reads : ∀ {h} {hp : Heapᴹ h} {q w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {t} {r : Ref h t}
            {k : ∀ {v} → h ⊑ v → El v t → Act v ⊤}
        → a ≗ readRef r k
        → Σ (∀ {v} → h ⊑ v → El v t → Act v ⊤) λ k′ → (∀ {v} (τ : h ⊑ v) x → k′ τ x ≗ k τ x)
          × (mach ⟨ hp , q , run a σ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ hp , q , run (k′ same⊑ (At.val hp r)) σ K ⟩ clk ts bs td lg en mk)
  reads (readRef≗ refl f) = _ , f , then refl now
