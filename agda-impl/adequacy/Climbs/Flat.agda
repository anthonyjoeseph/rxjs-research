{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A FLATMAP'S OUTER: its rise, its close, a lane begun.
module adequacy.Climbs.Flat where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
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
open import Data.Nat using (ℕ; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; skip; Pos; Timeline; _<ᵖ_)
open import denotation.MonotonicList using (Agree)
import denotation.Unfold as U
open import denotation.MonotonicList.Events using () renaming (sub to subᴾ)
open import adequacy.Sorted.Walk using (module SortingWalk)
open import adequacy.Sorted using (_≤ᵖ_)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Strong.Against using (module StrongAgainst)
open import adequacy.Strong.Held using (module StrongHeld)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane; SaneS; step-sane)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Stepper using (placed-after; Placedˢ; step-skips; step-deep; afterᴱ; _≃_)
open import adequacy.Deep using (Deep; Deepˢ)
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
open import adequacy.Shift.Walk using (module ShiftWalk)
open import adequacy.Kept using (module Keeping)

open import adequacy.Climbs.Base using (module ClimbBase)
open import adequacy.Climbs.Take using (module ClimbTake)
open Events∞



module ClimbFlat (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open SortingWalk R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Feed; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; fired; Path; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; outers; outersL; outers-⊕; unsub; Owes; Settled; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Books; Queue; Kernels; Meaning; Owned; Spot; spot; ∧-join; Each; Leaves; Lingers; Tied; Pinned; pinned; unpinned; Restful; rf-idle; rf-rest; rf-union; restful-pinned; pinned-sym; rest-pinned; union-pinned; bursts-pinned; under-pinned; seen; seenL; pinned-trans; ∧-split; false≢; owned-to; tw-trans; Twin; lv-swap; lv-trans; tw-bursting; tw-idle; tw-idleʳ; tw-idleˡ; tw-refl; tw-rest; tw-restᵀ; tw-sym; tw-under; tw-union)
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
  open Ghosting R using (residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; passed; Past; Lefts)
  open GhostingPaths R using (each-sub; each-lanes; module Far; module Calling; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; lefts-split; Rises; rises; Called; landed; rose; Aloft; aloft; hop-sorted; each-back; hopped-pre; lefts-up; lefts-subst; lefts-subst₂)
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
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; pooledL-alike; leftover-from; pooled-from; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag; tw-alike)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined)
  open FramingRepool R using (heads-repool; Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; lefts-planted; tick-under; healed-off; module Framed; flat-stays)
  open ClimbTake R using (rise; open-code; writes; reads)

  -- A climbing signal's path reads open: an emitter whose observer path
  -- is closed skips, each operator it passes guarded it on the way up,
  -- and nothing the path passes is cut while it climbs.
  postulate
    calling-open : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} (σ : Path T v) {sg : Signal T A}
                 → Calling g ℓ m₁ σ sg → opened (Conf.heap (Mach.conf m₁)) true σ ≡ true

  -- A path's openness read down a joined path: the first part's, handed on.
  mutual
    opened-⊕ : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′ Δ″ A″} {t : Sub h Δ A} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} o (ρ : Path t u) (s : Path u v)
             → opened H o (ρ ⊕ s) ≡ opened H (opened H o ρ) s
    opened-⊕ H o here          s = refl
    opened-⊕ H o (in-map p)    s = opened-⊕ H o p s
    opened-⊕ H o (in-scan p)   s = opened-⊕ H o p s
    opened-⊕ H o (in-take p)   s = opened-⊕ H _ p s
    opened-⊕ H o (in-outer p)  s = opened-⊕ H _ p s
    opened-⊕ H o (in-lanes p)  s = openedL-⊕ H o p s
    opened-⊕ H o (in-source p) s = opened-⊕ H _ p s
    opened-⊕ H o (in-body p)   s = opened-⊕ H o p s
    opened-⊕ H o (in-defer p)  s = opened-⊕ H o p s

    openedL-⊕ : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′ Δ″ A″} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} {v : Sub h Δ″ A″} o (π : PathLanes ls u) (s : Path u v)
              → openedL H o (π ⊕ᴸ s) ≡ opened H (openedL H o π) s
    openedL-⊕ H o (this-lane p) s = opened-⊕ H _ p s
    openedL-⊕ H o (next-lane p) s = openedL-⊕ H o p s

  -- A flatMap's outer signals only while its cut is live.
  outer-live : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
               (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {sg : Signal T A}
             → Calling g ℓ m₁ (ρ ⊕ in-outer here) sg → At.val (Conf.heap (Mach.conf m₁)) (Kit.live oc) ≡ true
  outer-live {m₁ = m₁} ρ cl =
    proj₁ (∧-split _ (trans (sym (opened-⊕ (Conf.heap (Mach.conf m₁)) true ρ (in-outer here))) (calling-open (ρ ⊕ in-outer here) cl)))

  -- A pair of lists both empty.
  nulls : ∀ {a b} {X : Set a} {Y : Set b} (xs : List X) (ys : List Y) → (null xs ∧ null ys) ≡ true → xs ≡ [] × ys ≡ []
  nulls []      []      refl = refl , refl
  nulls []      (_ ∷ _) ()
  nulls (_ ∷ _) _       ()

  -- A guard read shut: nothing.
  shut-code : ∀ {w} {b : Bool} {m : Act w ⊤} → b ≡ false → Kit.when b m ≗ done tt
  shut-code refl = ≗-refl _

  -- A flatMap's settle, read a cell at a time: its done flag, its count,
  -- its queue.
  settledᵒ : ∀ {h} {A B : Set} → Observer B h → Bool → ℕ → List A → Act h ⊤
  settledᵒ o d n qs = Kit.when (d ∧ (n ≡ᵇ 0) ∧ null qs) (Observer.complete o)

  settleᵒ₂ : ∀ {h A B} → Observer B h → FlatKit.Flat A h → Bool → ℕ → Act h ⊤
  settleᵒ₂ o fl d n = Kit.readF (FlatKit.Flat.queue fl) (settledᵒ o d n)

  settleᵒ₁ : ∀ {h A B} → Observer B h → FlatKit.Flat A h → Bool → Act h ⊤
  settleᵒ₁ o fl d = Kit.readB (FlatKit.Flat.active fl) (settleᵒ₂ o fl d)

  settleᵒ : ∀ {h A B} → Observer B h → FlatKit.Flat A h → Act h ⊤
  settleᵒ o fl = Kit.readB (FlatKit.Flat.outerDone fl) (settleᵒ₁ o fl)

  -- A flatMap with its outer gone, no lane live and nothing queued shows
  -- nothing.
  flat-gone : ∀ {h} (H : Heapᴹ h) {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
            → At.part H u ≡ nothing → At.partLanes H ls ≡ [] → At.val H (FlatKit.Flat.queue fl) ≡ []
            → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ nothing
  flat-gone H e₁ e₂ e₃ rewrite e₁ | e₂ | e₃ = refl

  -- A flatMap is open whatever its pool.
  merged-pool : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q (pl pl′ : U.Node Δ B)
              → is-just (At.merged G op g o L Q pl′) ≡ is-just (At.merged G op g o L Q pl)
  merged-pool G op g nothing  []      []      pl pl′ = refl
  merged-pool G op g nothing  []      (_ ∷ _) pl pl′ = refl
  merged-pool G op g nothing  (_ ∷ _) Q       pl pl′ = refl
  merged-pool G op g (just _) L       Q       pl pl′ = refl

  -- Lanes gated against a list are gated against any list holding it.
  gatedL-mono : ∀ {h} {H : Heapᴹ h} {Δ B} {X Y : List (Kit.Cut h)} → (∀ {c} → c ∈ᴸ X → c ∈ᴸ Y)
              → (ls : List (Lane h Δ B)) → At.GatedLanes H X ls → At.GatedLanes H Y ls
  gatedL-mono sub []                g              = g
  gatedL-mono sub (lane c k s ∷ ls) (g₁ , g₂ , g₃) = (λ e → [ (λ m → inj₁ (sub m)) , inj₂ ]′ (g₁ e)) , g₂ , gatedL-mono sub ls g₃

  -- Two moves at one node, one after the other.
  heading-∘ : ∀ {h} {H₁ H₂ H₃ : Heapᴹ h} {q Δ A} {u v w : Sub h Δ A} → Heading H₁ H₂ q u v → Heading H₂ H₃ q v w → Heading H₁ H₃ q u w
  heading-∘ record { head-revive = r₁ ; head-told = t₁ ; head-below = b₁ } record { head-revive = r₂ ; head-told = t₂ ; head-below = b₂ } = record
    { head-revive = λ j → r₁ (r₂ j)
    ; head-told   = λ i e₀ e₂ m → t₁ i e₀ (proj₂ (just-of (r₂ (cong is-just e₂)))) (t₂ i (proj₂ (just-of (r₂ (cong is-just e₂)))) e₂ m)
    ; head-below  = λ ev → b₂ (b₁ ev) }

  lingering-∘ : ∀ {h} {H₁ H₂ H₃ : Heapᴹ h} {Δ A} {u v w : Sub h Δ A} → Lingering H₁ H₂ u v → Lingering H₂ H₃ v w → Lingering H₁ H₃ u w
  lingering-∘ record { ling-revive = r₁ ; ling-rested = p₁ ; ling-below = b₁ } record { ling-revive = r₂ ; ling-rested = p₂ ; ling-below = b₂ } = record
    { ling-revive = λ j → r₁ (r₂ j)
    ; ling-rested = λ {C} → tw-trans (p₁ {C}) (p₂ {C})
    ; ling-below  = λ lg → b₂ (b₁ lg) }

  -- A leftover read at another type leaves as it did.
  mutual
    tw-leftover : ∀ {h} (H : Heapᴹ h) {Δ A B C} (s : Sub h Δ A) → Twin (At.leftover H {B = B} s) (At.leftover H {B = C} s)
    tw-leftover H (pendingˢ s q)                     = tw-restᵀ (U.subscribe s q)
    tw-leftover H (coldˢ s hd ph)                    = tw-idle
    tw-leftover H (ofˢ p i xs)                       = tw-idle
    tw-leftover H doneˢ                              = tw-idle
    tw-leftover H (mapˢ f s)                         = tw-leftover H s
    tw-leftover H (scanˢ f r s)                      = tw-leftover H s
    tw-leftover H (takeWhileˢ i p c k tk s)          = tw-leftover H s
    tw-leftover H (flatMapˢ op f fl oc k r pl so ls) = tw-union (tw-leftover H so) (tw-leftoverL H ls)
    tw-leftover H (connectˢ S c b kb k fd rp e rt src bd) =
      tw-union (tw-bursting rp n) (tw-under (U.live n) (tw-refl (At.leftover H {B = ⊤} bd)))
      where n = At.sourced H (At.part H src) (At.leftover H src)
    tw-leftover H (joinˢ j sk l x st)                = tw-idle
    tw-leftover H (deferˢ k s)                       = tw-leftover H s

    tw-leftoverL : ∀ {h} (H : Heapᴹ h) {Δ A B C} (ls : List (Lane h Δ A)) → Twin (At.leftoverL H {B = B} ls) (At.leftoverL H {B = C} ls)
    tw-leftoverL H []                = tw-idle
    tw-leftoverL H (lane c k s ∷ ls) = tw-union (tw-leftover H s) (tw-leftoverL H ls)

  -- An untold list split at its pool.
  told-split : ∀ (xs ys zs : List Pos) {ws} → xs ⊆ᴾ ws → ys ⊆ᴾ ws → zs ⊆ᴾ ws → (xs ++ ys ++ zs) ⊆ᴾ ws
  told-split xs ys zs sx sy sz m = [ sx , (λ m′ → [ sy , sz ]′ (∈-++⁻ ys m′)) ]′ (∈-++⁻ xs m)

  -- A FLATMAP'S POOL RESTAGED: the node at the path's end with a new
  -- pool, the calls, the stack and every field carried across.
  module Restaged {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) (pl′ : U.Node Δ B) where
    w₀ = flatMapˢ op f fl oc k r pl u ls
    v  = flatMapˢ op f fl oc k r pl′ u ls
    T′ = plant ρ v

    kin : Kin w₀ v
    kin = kin-pool

    pool-idling : pl′ ≡ U.unionᶜ pl U.idleᶜ → Lingering H H w₀ v
    pool-idling e = record
      { ling-revive = λ j → trans (sym (merged-pool H op _ (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′)) j
      ; ling-rested = λ {C} → tw-alike {Γ = Δ} {A = C} {x = At.leftover H {B = C} w₀} refl
      ; ling-below  = λ lg → Linger.lg-flat H (pool lg) (lingers-sub H lg (in-outer here) refl) (lingersL-of H lg) }
      where
        pool : Lingers H w₀ → ∀ {c} → At.part H v ≡ just c → Leaves pl′ (At.pooled H fl u ls) × Restful pl′
        pool lg x with Lingers.pools lg here refl
                         (proj₂ (just-of (trans (sym (merged-pool H op _ (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′)) (cong is-just x))))
        ... | t , rf = subst (λ p → Leaves p (At.pooled H fl u ls) × Restful p) (sym e) (lv-trans (proj₁ (tw-sym (tw-idleʳ pl))) t , rf-union rf rf-idle)

    -- The pool moved in place: every clause but the pool's alike.
    repool-heading : ∀ {q} → (∀ {A′} (i : A′ ∈ᴸ Δ) {b₀} → At.part H w₀ ≡ just b₀ → untold i pl′ ⊆ᴾ untold i b₀)
                   → (∀ {c} → At.part H w₀ ≡ just c → Heads q pl → Heads q pl′) → Heading H H q w₀ v
    repool-heading {q} told hp = record
      { head-revive = revive
      ; head-told   = λ i {b₀} e₀ e′ m →
          told-split (untoldᴹ i (At.part H u)) (untoldᴸ i (At.partLanes H ls)) (untold i pl′)
            (λ m′ → ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H u) (At.partLanes H ls) Q pl e₀)) (++⁺ˡ m′))
            (λ m′ → ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H u) (At.partLanes H ls) Q pl e₀)) (++⁺ʳ (untoldᴹ i (At.part H u)) (++⁺ˡ m′)))
            (told i e₀)
            (≡-⊆ (cong (untold i) (sym (merged-eq H op G (At.part H u) (At.partLanes H ls) Q pl′ e′))) m)
      ; head-below  = λ ev → Build.each-flat H (Heads q) {op = op} {f} {fl} {oc} {k} {r} {pl′} {so = u} {ls}
                               (root ev) (pool ev) (each-sub ev (in-outer here) refl) (eachL-of H ev) }
      where
        G = λ a j → U.subscribe (f a) j
        Q = At.val H (FlatKit.Flat.queue fl)
        revive : is-just (At.part H v) ≡ true → is-just (At.part H w₀) ≡ true
        revive j = trans (sym (merged-pool H op G (At.part H u) (At.partLanes H ls) Q pl pl′)) j
        pool : Each H (Heads q) w₀ → ∀ {c} → At.part H v ≡ just c → Heads q pl′
        pool ev x = hp e₀ (Each.pools ev here refl e₀)
          where e₀ = proj₂ (just-of (revive (cong is-just x)))
        root : Each H (Heads q) w₀ → ∀ {c} → At.part H v ≡ just c → Heads q c
        root ev x =
          subst (Heads q) (merged-eq H op G (At.part H u) (At.partLanes H ls) Q pl′ x)
            (heads-repool op G (At.part H u) (At.partLanes H ls) Q pl pl′
              (subst (Heads q) (sym (merged-eq H op G (At.part H u) (At.partLanes H ls) Q pl e₀)) (Each.parts ev here refl e₀))
              (pool ev x))
          where e₀ = proj₂ (just-of (revive (cong is-just x)))

    pool-calls : List (Call T) → List (Call T′)
    pool-calls = rehomes kin ρ

    pool-code : (ks : List (Call T)) → ⟦ ks ⟧ᶜ ≗ ⟦ pool-calls ks ⟧ᶜ
    pool-code ks = subst (λ z → ⟦ ks ⟧ᶜ ≗ z) (sym (rehomes-code kin ρ ks)) (≗-refl ⟦ ks ⟧ᶜ)

    pool-stack : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
    pool-stack = restack kin ρ

    pool-ticked : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (pool-stack sk)
    pool-ticked n sk = reticked kin ρ {n = n} sk

    pool-owned : ∀ {w q bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (ks : List (Call T)) (e : act ≗ ⟦ pool-calls ks ⟧ᶜ)
               → Owned H T (runAs ks (≗-refl _) sk) → Owned H T′ (runAs (pool-calls ks) e (pool-stack sk))
    pool-owned sk ks e ow = owned-run kin ρ sk ks e tt ow

    pool-idle : AllPairs _≢_ (names T) → pl′ ≡ U.unionᶜ pl U.idleᶜ → Ends H T → Lingers H T → Lingers H T′
    pool-idle fs e en = Shift.shift-lingers H H ρ (λ j _ → refl) [] fs v en (pool-idling e)

    -- The pool read by its part alone: no kernel, feed or queue clause
    -- moves.
    pool-kernels : Kernels H T → Kernels H T′
    pool-kernels kn = record { holds   = holds-plant H {t = T} ρ v refl (λ hs → hs) (Kernels.holds kn)
                             ; gated   = gated-plant H {t = T} ρ v (λ g → g) (λ d → d) (Kernels.gated kn)
                             ; settled = settled-plant H {t = T} ρ v (λ ow → ow) (λ st → st) (Kernels.settled kn) }

    pool-meaning : Meaning H T → Meaning H T′
    pool-meaning mn = record { fed = fed-plant H {t = T} ρ v (λ _ fd → fd) _ (Meaning.fed mn) }

    pool-queue : ∀ {q clk ts} → Queue H q clk ts T → Queue H q clk ts T′
    pool-queue = plant-queue H ρ v refl refl (λ _ → refl)

  -- A lane's parts, the first apart.
  lanes-one : ∀ {h} (H : Heapᴹ h) {Δ B} (l : Lane h Δ B) ls → At.partLanes H (l ∷ ls) ≡ At.partLanes H (l ∷ []) ++ At.partLanes H ls
  lanes-one H (lane c k s) ls with At.val H (Kit.live c) | At.part H s
  ... | true  | just _  = refl
  ... | true  | nothing = refl
  ... | false | _       = refl

  -- A lane in the list, the flatMap open.
  merged-cons : ∀ {h} (H : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) (o : Maybe (U.Node Δ A)) bs c as qs pl
              → At.merged H op g o (bs ++ c ∷ as) qs pl ≡ just (U.flatMapᶜ op g o (bs ++ c ∷ as) qs pl)
  merged-cons H op g nothing  []      c as qs pl = refl
  merged-cons H op g nothing  (_ ∷ _) c as qs pl = refl
  merged-cons H op g (just _) bs      c as qs pl = refl

  -- A SKIP LIFTED: each ancestor skips to a node its own part reads but
  -- for the gaps the sources it climbed through fed their bodies.
  mutual
    skip-lift : ∀ {h} (H : Heapᴹ h) {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) {κ k c c₀ S}
              → Lifts H π (U.skipˢ k c) S → At.part H u ≡ just c₀ → Gapped κ c c₀
              → Σ Pos λ k′ → Σ (U.Node Δ A) λ g′ → Σ (U.Node Δ A) λ g″ → S ≡ U.skipˢ k′ g′ × At.part H t ≡ just g″ × Gapped κ g′ g″
    skip-lift H here lifts-here pc gc = _ , _ , _ , refl , pc , gc
    skip-lift H (in-map π) (lifts-map L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite pg = k′ , _ , _ , refl , refl , gap-map gp
    skip-lift H (in-scan π) (lifts-scan L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite pg = k′ , _ , _ , refl , refl , gap-scan gp
    skip-lift H (in-take π) (lifts-take lv L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite lv | pg = k′ , _ , _ , refl , refl , gap-take gp
    skip-lift H (in-outer {fl = fl} {ls = ls} π) (lifts-outer _ _ L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite pg =
      k′ , _ , _ , refl , refl , gap-flat (λ _ _ → alike) (gap-just gp) (gapL-refl (At.partLanes H ls)) alike
    skip-lift H (in-lanes {op = op} {f} {fl} {pl = pl} {t = so} πL) (lifts-lanes {bs = bs} {as = as} LL _ _ _) pc gc with skip-liftL H πL LL pc gc
    ... | k′ , c′ , c″ , refl , eq , gp rewrite eq =
      k′ , _ , _ , refl , merged-cons H op (λ a q → U.subscribe (f a) q) (At.part H so) bs c″ as (At.val H (FlatKit.Flat.queue fl)) pl
         , gap-flat (λ _ _ → alike) (gapM-refl (At.part H so)) (gapL-mid bs as gp) alike
    skip-lift H (in-source π) (lifts-source {b₀ = b₀} pb sf L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite sf | pg | pb = _ , _ , _ , refl , refl , gap-connect (feed-gapped (here refl) k′ b₀) (gap-live gp)
    skip-lift H (in-body π) (lifts-body pt _ L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite pt | pg = k′ , _ , _ , refl , refl , gap-connect gp (gap-live alike)
    skip-lift H (in-body π) (lifts-shut pt refl _ L) pc gc with skip-lift H π L pc gc
    ... | k′ , g′ , g″ , refl , pg , gp rewrite pt | pg = k′ , _ , _ , refl , refl , gap-connect (gap-shut gp) (gap-ended alike)
    skip-lift H (in-defer π) (lifts-defer L) pc gc = skip-lift H π L pc gc

    skip-liftL : ∀ {h} (H : Heapᴹ h) {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (πL : PathLanes ls u) {κ k c c₀ bs S as}
               → LiftsLane H πL (U.skipˢ k c) bs S as → At.part H u ≡ just c₀ → Gapped κ c c₀
               → Σ Pos λ k′ → Σ (U.Node Δ B) λ c′ → Σ (U.Node Δ B) λ c″ → S ≡ U.skipˢ k′ c′ × At.partLanes H ls ≡ bs ++ c″ ∷ as × Gapped κ c′ c″
    skip-liftL H (this-lane π) (lifts-this lv L) pc gc with skip-lift H π L pc gc
    ... | k′ , c′ , c″ , refl , pg , gp rewrite lv | pg = k′ , c′ , c″ , refl , refl , gp
    skip-liftL H (next-lane {l = l} {ls} πL) (lifts-next L) pc gc with skip-liftL H πL L pc gc
    ... | k′ , c′ , c″ , refl , eq , gp =
      k′ , c′ , c″ , refl , trans (lanes-one H l ls) (trans (cong (At.partLanes H (l ∷ []) ++_) eq) (sym (++-assoc (At.partLanes H (l ∷ [])) _ _))) , gp

  -- A SKIP CLIMBING TO THE ROOT: the ghost past the root's skip, the
  -- planted tree's part what it skipped to, but for gaps.
  ghost-lift : ∀ {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {w₀ : Sub h Δ A} (ρ : Path T w₀) (v : Sub h Δ A)
             → AllPairs _≢_ (names T) → ∀ {ns} → Offʰ H H′ ns → All (_∈ᴸ names w₀) ns
             → ∀ {κ k c c₀ S g} → Lifts H ρ (U.skipˢ k c) S → At.part H′ v ≡ just c₀ → Gapped κ c c₀
             → Sane [] g → Placed g [] → Deep g [] → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part H′ (plant ρ v) ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
  ghost-lift H H′ ρ v fs off mine {g = g} L pv gv sn pd dp sg
    with skip-lift H′ (planted ρ v) (lifts-planted ρ v (Wrote.wr-lifts H H′ ρ off mine fs L)) pv gv
  ... | k′ , g′ , g″ , refl , pg , gp =
    g″ , pg , gapped-sane gp (subst (SaneS []) sg (step-sane g sn)) , gapped-placed gp pd′ , gapped-deep gp dp′
       , k′ , U.stateᴺ g′ [] , (λ n → subst (λ s → Agree n (residual g) (afterᴱ [] s)) sg (_≃_.agreeing (step-skips g sn pd) n))
       , gapped-past gp dp′
    where pd′ = proj₂ (subst (Placedˢ []) sg (placed-after g sn pd))
          dp′ = subst (Deepˢ []) sg (step-deep g sn pd dp)

  -- An outer ended with lanes or a queue left skips to the pool.
  outer-end : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) (o : U.Node Γ A) q (ls : List (U.Node Γ B)) (qs : List A) p
            → (null ls ∧ null qs) ≡ false → U.outerˢ op g o (U.endˢ q) ls qs p ≡ U.skipˢ q (U.flatMapᶜ op g nothing ls qs (U.unionᶜ p (U.restᶜ o)))
  outer-end op g o q []      []      p ()
  outer-end op g o q []      (_ ∷ _) p _ = refl
  outer-end op g o q (_ ∷ _) []      p _ = refl
  outer-end op g o q (_ ∷ _) (_ ∷ _) p _ = refl

  merged-open : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) (ls : List (U.Node Δ B)) (qs : List A) pl
              → (null ls ∧ null qs) ≡ false → At.merged G op g nothing ls qs pl ≡ just (U.flatMapᶜ op g nothing ls qs pl)
  merged-open G op g []      []      pl ()
  merged-open G op g []      (_ ∷ _) pl _ = refl
  merged-open G op g (_ ∷ _) []      pl _ = refl
  merged-open G op g (_ ∷ _) (_ ∷ _) pl _ = refl

  -- A FLATMAP'S OUTER ENDED: its done flag written, nothing else of the
  -- heap or the tree moved; settled, the count read as the live lanes.
  module Settles {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) where
    H′ = store H (FlatKit.Flat.outerDone fl) (lift true)

    done-read : At.val H′ (FlatKit.Flat.outerDone fl) ≡ true
    done-read = cong lower (stored-at H (FlatKit.Flat.outerDone fl) (lift true))

    -- A lane, live, holds a part.
    Parted : ∀ {Δ′ B′} → Lane h Δ′ B′ → Set
    Parted (lane c _ s) = At.val H (Kit.live c) ≡ true → is-just (At.part H s) ≡ true

    -- SUSPECT: `Kernels` records the count, not the parts; a lane whose
    -- body has completed and not yet dropped its live flag would be live
    -- with no part.  The fact may need its own field.
    postulate
      live-parted : Kernels H T → All Parted ls

    parted-null : ∀ {X : Set₁} (m : Maybe X) (xs : List X) → is-just m ≡ true → false ≡ null (At.consᴹ H m xs)
    parted-null (just x) xs _  = refl
    parted-null nothing  xs ()

    -- With every live lane parted, the count is zero exactly when no
    -- part is.
    count-null : ∀ {Δ′ B′} (ls′ : List (Lane h Δ′ B′)) → All Parted ls′ → (At.count H ls′ ≡ᵇ 0) ≡ null (At.partLanes H ls′)
    count-null []                 []       = refl
    count-null (lane c k s ∷ ls′) (p ∷ ps) with At.val H (Kit.live c) | p
    ... | true  | p′ = parted-null (At.part H s) (At.partLanes H ls′) (p′ refl)
    ... | false | _  = count-null ls′ ps

    active-count : Kernels H T → At.val H (FlatKit.Flat.active fl) ≡ At.count H ls
    active-count kn with holds-at ρ (Kernels.holds kn)
    ... | _ , _ , (_ , _ , _ , _ , ac , _) = ac

    active-lanes : Kernels H T → (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ≡ null (At.partLanes H ls)
    active-lanes kn = trans (cong (_≡ᵇ 0) (active-count kn)) (count-null ls (live-parted kn))

    -- The done flag the flatMap's own cell: its node's clauses read
    -- alike, the rest of the tree by the frame.
    w₀ = flatMapˢ op f fl oc k r pl u ls

    ns : List (Name h)
    ns = (_ , FlatKit.Flat.outerDone fl) ∷ []

    mine : All (_∈ᴸ names w₀) ns
    mine = there (here refl) ∷ []

    sd-off : Offʰ H H′ (names w₀)
    sd-off = Heaps.keep H H′ (off-store H (FlatKit.Flat.outerDone fl)) (lookupᴬ mine)

    -- The done flag no read of the node's own clauses.
    sd-alike : AllPairs _≢_ (names w₀) → Alike H H′ (flatReads fl oc k r u ls)
    sd-alike (a₀ ∷ a₁ ∷ _) j (here e)  = look-store H (FlatKit.Flat.outerDone fl) j (λ eq → lookupᴬ a₀ (here refl) (sym (trans eq e)))
    sd-alike (a₀ ∷ a₁ ∷ _) j (there m) = look-store H (FlatKit.Flat.outerDone fl) j (lookupᴬ a₁ (there m))

    module Fr (fs : AllPairs _≢_ (names T)) =
      Framed H H′ ρ (off-store H (FlatKit.Flat.outerDone fl)) mine fs
        (flat-stays H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike (fresh-path ρ fs)))
        (Heaps.fed-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike (fresh-path ρ fs)))
        (store-keeps H (FlatKit.Flat.outerDone fl) _ (λ ()) (λ ()) (λ ()) (λ ()))

    sd-part-at : ∀ pl′ → AllPairs _≢_ (names w₀) → At.part H′ (flatMapˢ op f fl oc k r pl′ u ls) ≡ At.part H (flatMapˢ op f fl oc k r pl′ u ls)
    sd-part-at pl′ fr@(_ ∷ a₁ ∷ _) =
      part-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl′} u ls (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.queue fl) (lookupᴬ a₁ (here refl)))
                (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)) (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr))

    sd-part : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl u ls)) → At.part (store H (FlatKit.Flat.outerDone fl) (lift true)) (flatMapˢ op f fl oc k r pl u ls) ≡ At.part H (flatMapˢ op f fl oc k r pl u ls)
    sd-part = sd-part-at pl

    sd-active : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.active fl) ≡ At.val H (FlatKit.Flat.active fl)
    sd-active (a₀ ∷ _) = cong lower (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.active fl) (λ eq → lookupᴬ a₀ (here refl) (sym eq)))

    sd-fifo : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl u ls)) → At.val (store H (FlatKit.Flat.outerDone fl) (lift true)) (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
    sd-fifo (_ ∷ a₁ ∷ _) = cong lower (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.queue fl) (lookupᴬ a₁ (here refl)))

    -- At the flatMap and below it, every part as it was.
    sd-same : AllPairs _≢_ (names w₀) → ∀ {Δ′ A′} {v : Sub h Δ′ A′} (ψ : Path w₀ v) → At.part H′ v ≡ At.part H v
    sd-same fr here                 = sd-part fr
    sd-same fr {v = v} (in-outer ψ) = part-alike H H′ v (λ j m → Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr) j (names-path ψ m))
    sd-same fr {v = v} (in-lanes ψ) = part-alike H H′ v (λ j m → Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr) j (lanes-path ψ m))

    -- No take beneath the flatMap switched by its done flag.
    sd-live : AllPairs _≢_ (names w₀) → Lives H H′ w₀
    sd-live (_ ∷ a₁ ∷ _) = lives-off {H = H} {H′ = H′} (off-store H (FlatKit.Flat.outerDone fl)) nl
      where
        nl : ∀ {Δ′ A′ i p c k′ tk} {s : Sub h Δ′ A′} → Path w₀ (takeWhileˢ i p c k′ tk s) → All (_≢_ (_ , Kit.live c)) ns
        nl (in-outer ψ) =
          (λ eq → lookupᴬ a₁ (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ (names-path ψ (here refl))))))))) (sym eq)) ∷ []
        nl (in-lanes ψ) =
          (λ eq → lookupᴬ a₁ (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names u) (lanes-path ψ (here refl))))))))) (sym eq)) ∷ []

    sd-gone : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl u ls)) → Gone H (store H (FlatKit.Flat.outerDone fl) (lift true)) (flatMapˢ op f fl oc k r pl u ls)
    sd-gone fr = record { gone-part = λ ψ e → trans (sd-same fr ψ) e ; gone-live = sd-live fr ; gone-held = store-held H (FlatKit.Flat.outerDone fl) }

    -- Nothing left: the flatMap gone, no pool of it held; its children's
    -- leftovers and ties alike.
    sd-lingering : AllPairs _≢_ (names (flatMapˢ op f fl oc k r pl u ls)) → At.part (store H (FlatKit.Flat.outerDone fl) (lift true)) (flatMapˢ op f fl oc k r pl u ls) ≡ nothing → Lingering H (store H (FlatKit.Flat.outerDone fl) (lift true)) (flatMapˢ op f fl oc k r pl u ls) (flatMapˢ op f fl oc k r pl u ls)
    sd-lingering fr gn = record
      { ling-revive = λ j → ⊥-elim (true≢false (trans (sym j) (cong is-just gn)))
      ; ling-rested = λ {C} → tw-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} u so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
      ; ling-below  = λ lg → Linger.lg-flat H′ (λ e → ⊥-elim (true≢false (trans (sym (cong is-just e)) (cong is-just gn))))
                                (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                                (lingersL-alike H H′ ls-al (lingersL-of H lg)) }
      where
        so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)
        ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)

    -- Below the flatMap, what the done flag is not; at it, its part.
    sd-heads : AllPairs _≢_ (names w₀) → ∀ {q} → Each H (Heads q) w₀ → Each H′ (Heads q) w₀
    sd-heads fr = each-same H H′ se (sd-same fr)
      where
        se : ∀ {Δ′ A′} {v : Sub h Δ′ A′} (ψ : Path w₀ v) → seen H′ ψ ≡ seen H ψ
        se here         = refl
        se (in-outer ψ) = seen-alike H H′ ψ (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr))
        se (in-lanes ψ) = seenL-alike H H′ ψ (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr))

    -- THE POOL MOVED WITH THE FLAG: every read of the node's clauses
    -- alike, the pool `pl′` heading, telling and tying by what it is owed.
    module Repool (fr : AllPairs _≢_ (names w₀)) (pl′ : U.Node Δ B) where
      v = flatMapˢ op f fl oc k r pl′ u ls
      G = λ a j → U.subscribe (f a) j

      so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)
      ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)

      revive : is-just (At.part H′ v) ≡ true → is-just (At.part H w₀) ≡ true
      revive j = trans (sym (merged-pool H op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′))
                       (trans (sym (cong is-just (sd-part-at pl′ fr))) j)

      flat-eq : U.flatMapᶜ op G (At.part H′ u) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl′
              ≡ U.flatMapᶜ op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′
      flat-eq = trans (cong₂ (λ o L → U.flatMapᶜ op G o L (At.val H′ (FlatKit.Flat.queue fl)) pl′) (part-alike H H′ u so-al) (partLanes-alike H H′ ls ls-al))
                      (cong (λ Q → U.flatMapᶜ op G (At.part H u) (At.partLanes H ls) Q pl′) (sd-fifo fr))

      lingering : (∀ {c} → At.part H w₀ ≡ just c → Leaves pl (At.pooled H fl u ls) × Restful pl → Leaves pl′ (At.pooled H′ fl u ls) × Restful pl′) → Lingering H H′ w₀ v
      lingering tie = record
        { ling-revive = revive
        ; ling-rested = λ {C} → tw-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} u so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
        ; ling-below  = λ lg → Linger.lg-flat H′ (pool lg)
                                 (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                                 (lingersL-alike H H′ ls-al (lingersL-of H lg)) }
        where
          pool : Lingers H w₀ → ∀ {c} → At.part H′ v ≡ just c → Leaves pl′ (At.pooled H′ fl u ls) × Restful pl′
          pool lg x = tie e₀ (Lingers.pools lg here refl e₀)
            where e₀ = proj₂ (just-of (revive (cong is-just x)))

      heading : ∀ {q} → (∀ {A′} (i : A′ ∈ᴸ Δ) {b₀} → At.part H w₀ ≡ just b₀ → untold i pl′ ⊆ᴾ untold i b₀)
              → (∀ {c} → At.part H w₀ ≡ just c → Heads q pl → Heads q pl′) → Heading H H′ q w₀ v
      heading {q} told hp = record
        { head-revive = revive
        ; head-told   = λ i {b₀} e₀ e′ m →
            told-split (untoldᴹ i (At.part H′ u)) (untoldᴸ i (At.partLanes H′ ls)) (untold i pl′)
              (λ m′ → ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀))
                          (++⁺ˡ (≡-⊆ (cong (untoldᴹ i) (part-alike H H′ u so-al)) m′)))
              (λ m′ → ≡-⊆ (cong (untold i) (merged-eq H op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀))
                          (++⁺ʳ (untoldᴹ i (At.part H u)) (++⁺ˡ (≡-⊆ (cong (untoldᴸ i) (partLanes-alike H H′ ls ls-al)) m′))))
              (told i e₀)
              (≡-⊆ (cong (untold i) (sym (merged-eq H′ op G (At.part H′ u) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl′ e′))) m)
        ; head-below  = λ ev → Build.each-flat H′ (Heads q) {op = op} {f} {fl} {oc} {k} {r} {pl′} {so = u} {ls}
                                 (root ev) (pool ev)
                                 (each-sub (sd-heads fr ev) (in-outer here) refl) (eachL-of H′ (sd-heads fr ev)) }
        where
          pool : Each H (Heads q) w₀ → ∀ {c} → At.part H′ v ≡ just c → Heads q pl′
          pool ev x = hp e₀ (Each.pools ev here refl e₀)
            where e₀ = proj₂ (just-of (revive (cong is-just x)))
          root : Each H (Heads q) w₀ → ∀ {c} → At.part H′ v ≡ just c → Heads q c
          root ev x =
            subst (Heads q) (trans (sym flat-eq) (merged-eq H′ op G (At.part H′ u) (At.partLanes H′ ls) (At.val H′ (FlatKit.Flat.queue fl)) pl′ x))
              (heads-repool op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′
                (subst (Heads q) (sym (merged-eq H op G (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl e₀)) (Each.parts ev here refl e₀))
                (pool ev x))
            where e₀ = proj₂ (just-of (revive (cong is-just x)))

    sd-behind : AllPairs _≢_ (names T) → ∀ {q} → Each H (Heads q) T → Each H′ (Heads q) T
    sd-behind fs = Fr.wr-behind fs (sd-part (fresh-path ρ fs)) (sd-heads (fresh-path ρ fs))

    settle-eq : AllPairs _≢_ (names w₀) → Kernels H T → ((At.val H′ (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val H′ (FlatKit.Flat.queue fl)))
                              ≡ (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl)))
    settle-eq fr kn = trans (cong (λ n → (n ≡ᵇ 0) ∧ null (At.val H′ (FlatKit.Flat.queue fl))) (sd-active fr))
                      (trans (cong (λ qs → (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null qs) (sd-fifo fr))
                          (cong (λ x → x ∧ null (At.val H (FlatKit.Flat.queue fl))) (active-lanes kn)))

    -- THE FLAG WRITTEN: every flag below the flatMap read alike, its own
    -- reading the outer gone.
    sd-flags₀ : ∀ {xs} pl′ → AllPairs _≢_ (names w₀) → ((cell _ , FlatKit.Flat.outerDone fl) ∈ᴸ xs → ⊥) → At.part H u ≡ nothing
              → DoneBy H w₀ (xs ++ ns) → DoneBy H′ (flatMapˢ op f fl oc k r pl′ u ls) xs
    sd-flags₀ {xs} pl′ fr@(_ ∷ a₁ ∷ _) nx gn d =
      Flag.db-flat H′ ((λ m → ⊥-elim (nx m)) , (λ _ → trans done-read (sym (cong is-nothing (trans (part-alike H H′ u soA) gn)))))
        (flags-alike H H′ soA (Flag.relist H {ns = xs ++ ns} {t = u} (λ _ m → ++⁺ˡ m) (λ mu m → [ (λ a → a) , (λ { (here refl) → ⊥-elim (doneU mu) }) ]′ (++⁻ xs m))
                                (Flag.db-sub H d (in-outer here) refl)))
        (flagsL-alike H H′ lsA (Flag.relistL H {ns = xs ++ ns} {ls = ls} (λ _ m → ++⁺ˡ m) (λ ml m → [ (λ a → a) , (λ { (here refl) → ⊥-elim (doneL ml) }) ]′ (++⁻ xs m))
                                  (Flag.dbL-of H d)))
      where
        soA = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)
        lsA = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)
        doneU : (cell _ , FlatKit.Flat.outerDone fl) ∈ᴸ names u → ⊥
        doneU mu = lookupᴬ a₁ (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ˡ mu))))))) refl
        doneL : (cell _ , FlatKit.Flat.outerDone fl) ∈ᴸ laneNames ls → ⊥
        doneL ml = lookupᴬ a₁ (there (there (there (++⁺ʳ (cutNames oc) (++⁺ʳ (quietName k) (there (++⁺ʳ (names u) ml))))))) refl

    -- Through the frame: the flag no longer held, the flatMap repooled
    -- or not.
    sd-shift : AllPairs _≢_ (names T) → ∀ pl′ → (is-just (At.part H′ (flatMapˢ op f fl oc k r pl′ u ls)) ≡ true → is-just (At.part H w₀) ≡ true)
             → At.part H u ≡ nothing → DoneBy H T (outers (ρ ⊕ in-outer here)) → DoneBy H′ (plant ρ (flatMapˢ op f fl oc k r pl′ u ls)) (outers ρ)
    sd-shift fs pl′ rv gn d =
      Fr.shift-flags fs (flatMapˢ op f fl oc k r pl′ u ls) (lookupᴬ mine) rv
        (sd-flags₀ pl′ (fresh-path ρ fs) (λ m → outers-apart ρ fs m (there (here refl))) gn) (subst (DoneBy H T) (outers-⊕ ρ (in-outer here)) d)

    sd-flags : AllPairs _≢_ (names T) → At.part H u ≡ nothing → DoneBy H T (outers (ρ ⊕ in-outer here)) → DoneBy H′ T (outers ρ)
    sd-flags fs gn d =
      subst (λ t → DoneBy H′ t (outers ρ)) (plant-self ρ) (sd-shift fs pl (λ j → trans (cong is-just (sym (sd-part (fresh-path ρ fs)))) j) gn d)

    -- Lanes or a queue left: the flatMap held, so every flag above it let go.
    sd-landed : AllPairs _≢_ (names T) → ∀ pl′ → At.part H u ≡ nothing → (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl))) ≡ false
              → ∀ {s S} → Lifts H ρ s S → DoneBy H T (outers (ρ ⊕ in-outer here)) → DoneBy H′ (plant ρ (flatMapˢ op f fl oc k r pl′ u ls)) []
    sd-landed fs pl′ gn nl L d =
      let-go H′ (planted ρ v′) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v′ refl)) fs) (lifts-seen (lifts-planted ρ v′ (Fr.wr-lifts fs L))) (cong is-just open′)
        (subst (DoneBy H′ (plant ρ v′)) (sym (outers-planted ρ v′)) (sd-shift fs pl′ (λ _ → cong is-just open₀) gn d))
      where
        G    = λ a j → U.subscribe (f a) j
        v′   = flatMapˢ op f fl oc k r pl′ u ls
        open₀ : At.part H w₀ ≡ just (U.flatMapᶜ op G nothing (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl)
        open₀ = trans (cong (λ x → At.merged H op G x (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl) gn)
                     (merged-open H op G (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl nl)
        open′ : At.part H′ v′ ≡ just (U.flatMapᶜ op G nothing (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)
        open′ = trans (sd-part-at pl′ (fresh-path ρ fs))
                      (trans (cong (λ x → At.merged H op G x (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′) gn)
                             (merged-open H op G (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′ nl))

    -- Lanes or a queue left: the pool takes what the outer left running,
    -- the ghost past the outer's skip.
    pool-ghost : AllPairs _≢_ (names T) → ∀ (o₀ : U.Node Δ A) {g q S} → Sane [] g → Placed g [] → Deep g [] → At.part H u ≡ nothing
               → (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl))) ≡ false
               → Lifts H ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl) S
               → U.step g ≡ S
               → Σ (U.Node [] R) λ g″ → At.part H′ (Restaged.T′ H′ ρ (U.unionᶜ pl (U.restᶜ o₀))) ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
                 × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
    pool-ghost fs o₀ {q = q} sn pd dp gn nl L sg =
      ghost-lift H H′ ρ (flatMapˢ op f fl oc k r pl′ u ls) fs (off-store H (FlatKit.Flat.outerDone fl)) mine {κ = []}
        (subst (λ s → Lifts H ρ s _) (outer-end op G o₀ q (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl nl) L)
        (trans (sd-part-at pl′ (fresh-path ρ fs))
               (trans (cong (λ x → At.merged H op G x (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′) gn)
                      (merged-open H op G (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′ nl)))
        alike sn pd dp sg
      where
        G   = λ a j → U.subscribe (f a) j
        pl′ = U.unionᶜ pl (U.restᶜ o₀)

  -- Heads read off a step pinned alike.
  heads-pinned : ∀ {Γ A B q} {st : U.Step Γ A} {st′ : U.Step Γ B} → Pinned st st′
               → (∀ {k} → U.headˢ st′ ≡ just k → q ≤ᵖ k) → ∀ {k} → U.headˢ st ≡ just k → q ≤ᵖ k
  heads-pinned pinned   h e = h e
  heads-pinned unpinned h ()

  -- Two rests side by side head where either does.
  heads-union : ∀ {Γ B q} (x : U.Node Γ B) sx y sy → (∀ {k} → U.headˢ sx ≡ just k → q ≤ᵖ k) → (∀ {k} → U.headˢ sy ≡ just k → q ≤ᵖ k)
              → ∀ {k} → U.headˢ (U.unionˢ x sx y sy) ≡ just k → q ≤ᵖ k
  heads-union x (U.skipˢ k x′) y (U.skipˢ k′ y′) hx hy e with k <ᵖ k′
  ... | true  = hx e
  ... | false = hy e
  heads-union x (U.skipˢ _ _)   y (U.outˢ _ _ _) hx hy e = hx e
  heads-union x (U.skipˢ _ _)   y (U.endˢ _)     hx hy e = hx e
  heads-union x (U.skipˢ _ _)   y U.hushˢ        hx hy e = hx e
  heads-union x (U.outˢ _ _ _)  y sy             hx hy e = hy e
  heads-union x (U.endˢ _)      y sy             hx hy e = hy e
  heads-union x U.hushˢ         y sy             hx hy e = hy e

  -- A sub whose close the run calls: what it leaves running heads no
  -- earlier than the run.
  postulate
    closed-rest-heads : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                          (σ : Path T v) {ks} → Calling g ℓ m₁ σ (closes ks)
                        → Heads (Conf.pos (Mach.conf m₁)) (U.restᶜ {B = ⊤} (At.leftover (Conf.heap (Mach.conf m₁)) {B = ⊤} v))

  -- The pool taking a closed node's rest heads where the pool did and
  -- the closed sub's leftover does.
  pool-heads : ∀ {Δ B q} {pl : U.Node Δ B} {A′} (o₀ : U.Node Δ A′) {C} {lf : U.Node Δ C} → Restful pl → Leaves o₀ lf
             → Heads q (U.restᶜ {B = ⊤} lf) → Heads q pl → Heads q (U.unionᶜ pl (U.restᶜ o₀))
  pool-heads {pl = pl} o₀ rf lo hl hp =
    heads-union pl (U.restˢ pl) (U.restᶜ o₀) (U.restˢ o₀)
      (heads-pinned (pinned-sym (restful-pinned rf)) hp)
      (heads-pinned (pinned-trans (rest-pinned o₀) (Leaves.pins lo)) hl)

  -- Lanes or a queue left: the pool takes the outer's last ghost
  -- rested, which is what the outer still runs; its heads and ties
  -- where the outer's were.
  -- DEAD ROUTE: a frame, the sibling moves' `Heaps` route.  The pool gains
  --   `o₀`'s rest, and `lifts-outer` leaves `o₀` free: no heap cell says
  --   what it runs, so no `Alike` reaches it.
  module Closing {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {ks} (o₀ : U.Node Δ A) {S}
                 (cl : Calling g ℓ m₁ (ρ ⊕ in-outer here) (closes ks))
                 (L : Lifts (Conf.heap (Mach.conf m₁)) ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ (Conf.pos (Mach.conf m₁)))
                            (At.partLanes (Conf.heap (Mach.conf m₁)) ls) (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.queue fl)) pl) S)
                 (sg : U.step g ≡ S) (lo : Leaves o₀ (At.leftover (Conf.heap (Mach.conf m₁)) {B = ⊤} u)) where
    H   = Conf.heap (Mach.conf m₁)
    q   = Conf.pos (Mach.conf m₁)
    pl′ = U.unionᶜ pl (U.restᶜ o₀)
    fs  = Books.fresh (Calling.books cl)

    module P = Settles.Repool H ρ (fresh-path ρ fs) pl′

    -- The done flag reads unset until the end climbs to the flatMap.
    unset : At.val H (FlatKit.Flat.outerDone fl) ≡ false
    unset = proj₁ (Calling.flags cl ρ (lifts-seen L)) (subst (_ ∈ᴸ_) (sym (outers-⊕ ρ (in-outer here))) (++⁺ʳ (outers ρ) (here refl)))

    -- The pool leaves as the lanes' rests while the flag is unset; the
    -- outer's rest as its leftover, which the flag now pools beside them.
    close-tied : ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just c
               → Leaves pl (At.pooled H fl u ls) → Leaves pl′ (At.pooled (Settles.H′ H ρ) fl u ls)
    close-tied _ t =
      subst (λ d → Leaves pl′ (U.unionᶜ (if d then At.leftover (Settles.H′ H ρ) u else U.idleᶜ) (At.pooledL (Settles.H′ H ρ) ls))) (sym (Settles.done-read H ρ))
        (lv-swap
          (lv-trans (subst (λ d → Leaves pl (U.unionᶜ (if d then At.leftover H u else U.idleᶜ) (At.pooledL H ls))) unset t)
            (lv-trans (proj₁ (tw-idleˡ (At.pooledL H ls))) (proj₁ (tw-alike (pooledL-alike H (Settles.H′ H ρ) ls P.ls-al)))))
          (lv-trans (proj₁ (tw-rest o₀))
            (lv-trans lo (proj₁ (tw-trans (tw-leftover H u) (tw-alike (leftover-alike H (Settles.H′ H ρ) u P.so-al)))))))

    postulate
      close-told  : ∀ {A′} (i : A′ ∈ᴸ Δ) {b₀} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just b₀ → untold i pl′ ⊆ᴾ untold i b₀

    close-heads : ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just c → Heads q pl → Heads q pl′
    close-heads e₀ = pool-heads o₀ (proj₂ (Lingers.pools (Calling.lingers cl) ρ (lifts-seen L) e₀)) lo (closed-rest-heads (ρ ⊕ in-outer here) cl)

    close-heading : Heading H (Settles.H′ H ρ) q (flatMapˢ op f fl oc k r pl u ls) (flatMapˢ op f fl oc k r pl′ u ls)
    close-heading = P.heading (λ {A′} i {b₀} → close-told {A′} i {b₀}) close-heads

    close-lingers : Lingers (Settles.H′ H ρ) (Restaged.T′ (Settles.H′ H ρ) ρ pl′)
    close-lingers = Settles.Fr.shift-lingers H ρ fs (Restaged.v (Settles.H′ H ρ) ρ pl′) (ended-past cl) (P.lingering (λ e₀ tr → close-tied e₀ (proj₁ tr) , rf-union (proj₂ tr) rf-rest)) (Calling.lingers cl)

  -- A flatMap's outer ended: its guard read open, its done flag written,
  -- its count and queue read.  Nothing left: the flatMap's end one
  -- operator up.  Else the lanes run on, the pool taking what the outer
  -- left running.
  close-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {ks}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (closes ks) → Called st m₁ (ρ ⊕ in-outer here)
  close-outer st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} ρ {ks}
    cl@record { sane = sn ; placed = pd ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg , hl ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; lefts = lt ; flags = dn ; kept = kp }
    with lifts-split ρ (in-outer here) L in eqF
       | reads (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-outer here) top) cd)
  ... | _ , lifts-outer {o₀ = o₀} _ _ lifts-here , Lρ | k₁ , f₁ , p₁
    with writes (≗-trans (f₁ same⊑ (At.val hp (Kit.live oc)))
                   (bind≗ (≗-trans (wk-same (Kit.when (At.val hp (Kit.live oc))
                                              (writeRef (FlatKit.Flat.outerDone fl) true (settleᵒ (Here.obs (walk ρ top)) fl))))
                                   (open-code (outer-live ρ cl)))
                          λ _ → wk-same ⟦ ks ⟧ᶜ))
  ...   | n₂ , e₂ , p₂ with reads {hp = Settles.H′ hp ρ} e₂
  ...     | k₃ , f₃ , p₃
    with reads {hp = Settles.H′ hp ρ}
           (≗-trans (f₃ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)))
              (bind≗ (wk-same (settleᵒ₁ (Here.obs (walk ρ top)) fl (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ))
  ...       | k₄ , f₄ , p₄
    with reads {hp = Settles.H′ hp ρ}
           (≗-trans (f₄ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl)))
              (bind≗ (wk-same (settleᵒ₂ (Here.obs (walk ρ top)) fl (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl))
                                          (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ))
  ...         | k₅ , f₅ , p₅
    with (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)) in eq
  ...           | true =
    rise kp (rises {sg′ = closes ks} path (one-lower ρ one-outer) (record
      { sane = sn ; placed = pd ; deep = dp ; ctl = refl
      ; code = ≗-trans e₅ (bind≗ (open-code {m = Observer.complete o} (trans (cong (λ x → x ∧ b) (Settles.done-read hp ρ)) eq)) λ _ → ≗-refl ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; lifted = trans (Settles.sd-part hp ρ (fresh-path ρ fs)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl)) , S
               , Settles.Fr.wr-lifts hp ρ fs Lo , sg
               , healed-off hp (Settles.H′ hp ρ) ρ fs (Settles.sd-off hp ρ) (Settles.sd-part hp ρ (fresh-path ρ fs)) (healed-split ρ (in-outer here) hl)
      ; owned = Settles.Fr.wr-owned hp ρ fs (Settles.sd-gone hp ρ (fresh-path ρ fs)) ow ; kernels = Settles.Fr.kernels hp ρ fs kn ; meaning = Settles.Fr.meaning hp ρ fs mn
      ; queue = Settles.Fr.queue hp ρ fs qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Settles.sd-behind hp ρ fs bh
      ; lingers = Settles.Fr.lingers hp ρ fs (ended-past cl) (Settles.sd-lingering hp ρ (fresh-path ρ fs) (trans (Settles.sd-part hp ρ (fresh-path ρ fs)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl)))) lgr ; lefts = Settles.Fr.wr-lefts hp ρ fs Lo
                  (lefts-subst₂ (λ ls′ qs′ → U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) ls′ qs′ po) (proj₁ nl) (proj₂ nl) (lefts-up ρ (in-outer here) eqF lt))
      ; flags = Settles.sd-flags hp ρ fs gn dn ; kept = inj₁ refl }))
    where
      o    = Here.obs (walk ρ top)
      nl   = nulls (At.partLanes hp ls) (At.val hp (FlatKit.Flat.queue fl)) (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq)
      Lo   = subst₂ (λ ls′ qs′ → Lifts hp ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) ls′ qs′ po) S) (proj₁ nl) (proj₂ nl) Lρ
      b    = (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl))
      path = ⇝-trans p₁ (⇝-trans p₂ (⇝-trans p₃ (⇝-trans p₄ p₅)))
      e₅   = ≗-trans (f₅ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))
               (bind≗ (wk-same (settledᵒ o (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)) (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl))
                                         (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ)
  ...           | false
    with Settles.pool-ghost hp ρ fs o₀ sn pd dp gn (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq) Lρ sg
  ...             | g″ , pg , sn″ , pd″ , dp″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; deep = dp″ ; tree = Restaged.T′ (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))
        ; ctlAs = runAs (Restaged.pool-calls (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) ks) ec (Restaged.pool-stack (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk)
        ; meets = pg
        ; owned′ = owned-to (Restaged.pool-owned (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk ks ec (Settles.Fr.wr-owned hp ρ fs (Settles.sd-gone hp ρ (fresh-path ρ fs)) ow))
        ; kernels = Restaged.pool-kernels (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.kernels hp ρ fs kn)
        ; meaning = Restaged.pool-meaning (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.meaning hp ρ fs mn)
        ; queue = Restaged.pool-queue (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.queue hp ρ fs qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path
        ; behind′ = Eaching.each-to _ _ (Settles.Fr.shift-behind hp ρ fs (Restaged.v (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))) (tells-past cl) (ended-past cl) (Closing.close-heading ρ o₀ cl Lρ sg lo) bh)
        ; lingers′ = Lingering.lingers-to _ (Closing.close-lingers ρ o₀ cl Lρ sg lo) ; flags = Settles.sd-landed hp ρ fs (U.unionᶜ po (U.restᶜ o₀)) gn (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq) Lρ dn })
      , passed ag pp)
    where
      o    = Here.obs (walk ρ top)
      b    = (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl))
      v    = flatMapˢ op f fl oc k r (U.unionᶜ po (U.restᶜ o₀)) u ls
      lo   = proj₁ (subst (λ w → Lefts hp (proj₁ (proj₂ w))) eqF (proj₁ (lefts-split ρ (in-outer here) L lt)))
      path = ⇝-trans p₁ (⇝-trans p₂ (⇝-trans p₃ (⇝-trans p₄ p₅)))
      e₅   = ≗-trans (f₅ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))
               (bind≗ (wk-same (settledᵒ o (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)) (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl))
                                         (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ)
      ec   = ≗-trans (≗-trans e₅ (bind≗ (shut-code {m = Observer.complete o} (trans (cong (λ x → x ∧ b) (Settles.done-read hp ρ)) eq)) λ _ → ≗-refl ⟦ ks ⟧ᶜ))
                     (Restaged.pool-code (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) ks)

  -- The machine with its running act replaced, the rest as it was.
  rerun : (m₁ : Mach) {w : World} → w ⊑ Conf.world (Mach.conf m₁) → Stack w ⊤ → Act (Conf.world (Mach.conf m₁)) ⊤ → Mach
  rerun (mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk) ϑ K a = mach ⟨ hp , q , run a ϑ K ⟩ clk ts bs td lg en mk

  -- A flatMap's admit and lane start, under the observer and scope its
  -- path walks to.
  admitAt : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
          → Path T (flatMapˢ op f fl oc k r pl u ls) → T.FlatOp → A → Act h ⊤
  admitAt {op = op} {f} {fl} ρ = Canon.Flat′.admit op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl

  startAt : ∀ {h} {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
          → Path T (flatMapˢ op f fl oc k r pl u ls) → A → Act h ⊤
  startAt {op = op} {f} {fl} ρ y = Canon.Flat′.start op f (Here.env (walk ρ top)) (Here.obs (walk ρ top)) fl (compile (f y) (Here.env (walk ρ top)))

  -- Whether an admit begins its lane at once, the active count read; a
  -- switch kills its lanes first.
  roomy : T.FlatOp → ℕ → Bool
  roomy (T.mergeᶠ nothing)  _ = true
  roomy (T.mergeᶠ (just n)) c = c <ᵇ n
  roomy T.switchᶠ           _ = false
  roomy T.exhaustᶠ          c = c ≡ᵇ 0
