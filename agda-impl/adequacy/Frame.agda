{-# OPTIONS --guardedness #-}

-- THE FRAME: a write at one node's own cell, against everything the
-- relation holds of the rest of the tree.
module adequacy.Frame where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here)
import Data.List.Relation.Unary.Any as Any
open import Data.Sum using ([_,_]′)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import denotation.MonotonicList using (Events∞; Timeline)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Record using (module Recording)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Local using (module Locality)
open import adequacy.Lowers using (module Lowering)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Placed using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (if_then_else_)
open import adequacy.Ghost using (module Ghosting)

open Events∞

module Framing (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; reading; begin; launch; Read; read; feed)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; spent?; store; look; stored) renaming (go to goᴵ)
  open Heap using (World; _⊑_; Handle; Quiet) renaming (same to same⊑)
  open Sorting R using (WellMach; WellStep; silentʷ; valueʷ; preserve; Beyond)
  open Run (Pureᴾ R) using (Act; writeRef; Observer; Subject; _>>ᴬ_; module Kit; module FlatKit)
  open Recording R using (silent-keeps; value-notes)
  open Strongly R using (Strong; strong-begin; Carried; Books; carried; closing; Sub; pendingˢ; coldˢ; ofˢ; doneˢ; mapˢ; scanˢ; takeWhileˢ;
    flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; lane; here; module At; Queue; Kernels; Meaning; fired; waiting; Owned; Path; Spot; spot; done≗;
    Call; emitC; kontC; take1C; take2C; bodyC; feedC; finC; srcC; Taking; taking; taken; feeding; finishing; PathLanes; this-lane; next-lane;
    in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; names; ≗-refl; Meets; Each; Heads; rootObs;
    seen; seenL; isTaking; seen-up; seen-join; ∧-split; ∧-join) renaming (ending to endingᵗ; ⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs;
    StackAs; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots) renaming (Placed to Placedᴬ)
  open Pure R using (End; finished; dry; cutOff; recorder; Timer; cascade)
  open Moving R using (pend; takes; takes-plant; plant; planted; Waits; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant;
    joiners-plant; holds-plant; gated-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open Tearing R using (part-alike; look-store; get-put-same; fresh-path; Site; takeSite; bodySite; siteCall; siteHeap; torn-take-part; torn-body-part; torn-take-each; torn-body-each)
  open Unsubbing R using (_⇝_; now; then; ⇝-trans; site-tears; ≗-trans; wk-same; bind≗)
  open Locality R using (site-holds; site-gated)
  open Lowering R using (site-lowers; queue-lowers; torn-owned; fed-lowers)
  open Sequencing R using (seq-assoc)
  open Ghosting R using (module Alike; module Inner; module Far; module Climbing; Has; atOut; atEnd; pastOut; pastSkip; Sent; sentHere; sentLater; Owed; Ending; Alike; tail-out; tail-skip; has-agree; _≋_; same-agree; residual; begun; Reached; launchedʰ; silentʰ; valueʰ; _↦_; silentᵗ; valueᵗ; Stands; cutʰ; finʰ; dryʰ; sorted-step; sorted-⇝; sorted-value; Mirror; Inner; Logged; Shows; silentˢ; valueˢ; completeˢ; drainedˢ; inner-launch; ≋-refl; ≋-trans; Steps; after; steps-after; Past; agrees; skipped; skip-same; past-same; past-pre; work; weight; left; leftᴸ; Load; _⊏_; _≼_; load; lex-trans; ⊏-trans; ≼-trans; ⊏-≼; Measure; _≺_; ≺-wf; measure; loadOf; Gain; passed; lowered; showing; gain-past; Hopped; onward; if-silent; Hops; opening; firstCall; owned-move; SourceFirst; BodyFirst; OuterFirst; PoolBehind; RestBehind; LaneFirst; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; lifts-split; liftsL-split; Far; far; Off; beyond-apart; far-apart; Opt; Pooled; Rested; Clear; ClearL; all-zip; opt-zip; clear-zip; clearL-zip; opt-each; lane-only; seenL-only; ∨-true; each-lanes; each-sub; clear-each; clearL-each; walk-⊕; walkL-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; Last; whole; snoc; LastL; oneL; snocL; view; viewL; height; heightL; height-⊕; heightL-⊕; height-one; heightL-one; one-lower; opened; openedL; Climbing; reclimb; relevel; Rises; rises; Climbed; landed; rose; Aloft; aloft; hop-sorted; heads-back; each-back; hopped-pre)
  open Read

  -- A scan's part, its accumulator written: its source's part, the
  -- accumulator the value written, the source's names apart from it.
  scan-part : ∀ {h} (H : Heapᴹ h) {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → AllPairs _≢_ (names (scanˢ f r u))
            → ∀ {c′} z → At.part H u ≡ just c′ → At.part (store H r (lift z)) (scanˢ f r u) ≡ just (U.scanᶜ f z c′)
  scan-part H {r = r} {u} (nr ∷ _) z pu
    rewrite get-put-same H r {y = stored (lift z) same⊑}
          | part-alike H (store H r (lift z)) u (λ j m → look-store H r j (lookupᴬ nr m)) | pu = refl

  -- A WRITE AT A SCAN'S ACCUMULATOR, FRAMED: nothing the relation holds
  -- reads an accumulator but the parts above it, and an ancestor's lift
  -- reads only its siblings and its own cells.
  postulate
    scan-owned   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} z → Owned H T ca → Owned (store H r (lift z)) T ca
    scan-kernels : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z → Kernels H T → Kernels (store H r (lift z)) T
    scan-meaning : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ z → Meaning H T → Meaning (store H r (lift z)) T
    scan-queue   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} → Path T (scanˢ f r u) → AllPairs _≢_ (names T)
                 → ∀ {p clk ts} z → Queue H p clk ts T → Queue (store H r (lift z)) p clk ts T
    scan-lifts   : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u)) → AllPairs _≢_ (names T)
                 → ∀ {s S} z → Lifts H ρ s S → Lifts (store H r (lift z)) ρ s S

    -- The parts above the scan move with it, each still heading no
    -- sooner than where the run is: a part's next event is bounded by
    -- its children's, and the scan's is its source's.
    scan-behind  : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                   (ρ : Path T (scanˢ f r u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-scan here) y
                 → Each (store (Conf.heap (Mach.conf m₁)) r (lift (f (At.val (Conf.heap (Mach.conf m₁)) r) y))) (Heads (Conf.pos (Mach.conf m₁))) T
