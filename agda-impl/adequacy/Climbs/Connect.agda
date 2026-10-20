{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A CONNECT: a value fed to its subject, its source's end.
module adequacy.Climbs.Connect where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
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
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList.Events using (Events∞; skip; Pos; Timeline; _<ᵖ_)
open import denotation.MonotonicList using (Agree)
import denotation.Unfold as U
import denotation.MonotonicList as ML
import denotation.MonotonicList.Events as Ev
open import denotation.NonExpansive using (tailᴱ-ne)
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
open import adequacy.Deep using (Deep; deep-rest; ordered-retyped)
open import adequacy.Placed.Order using (Placed)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (true; false; if_then_else_; _∧_; _∨_)
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
open import adequacy.Retag using (Retag; module Retagging; at-here)
open import adequacy.Retag.Shut using (tells; module RetagShut)
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

module ClimbConnect (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open SortingWalk R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Feed; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; joiner; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; joinˢ; deferˢ; Lane; here; module At; fired; Path; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; ending; taken; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; outers; outersL; outers-⊕; unsub; Owes; Settled; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open StrongAgainst R using (Leaves; Twin; Restful; rf-rest; rf-idle; rf-union; rf-burst; rf-under; tail-agreeᵀ; restful-meaning; restful-deep; Books; Queue; Kernels; Meaning; Owned; Spot; spot; ∧-join; Each; Lingers; Tied; seen; seenL; pinned-trans; ∧-split; false≢; owned-to)
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
  open GhostingPaths R using (each-sub; each-lanes; module Far; module Calling; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; Healed; HealedL; healed-split; healed-end; lifts-seen; Rises; rises; Called; landed; rose; Aloft; aloft; hop-sorted; each-back; hopped-pre; lefts-up; lefts-subst; lefts-subst₂; lefts-split)
  open Gapping R using (Gapped; alike; gap-map; gap-scan; gap-take; gap-flat; gap-just; gap-connect; gap-live; gap-shut; gap-ended; gap-tied; gapM-refl; gapL-refl; gapL-mid; feed-gapped; gapped-past; gapped-sane; gapped-placed; gapped-deep)
  open Lowering R using (Keeps; queue-keeps; store-keeps; keeps-trans)
  open Lifting R using (emit-shut; emit-run; spread-past; behind-fire; fire-lingers; kont-onward; feed-onward; src-onward; burst-poll; burst-play; cut-onward)
  open LiftingOrder R using (sub-onward; emit-void; run-meets; run-at; heads-lift)
  open Locality R using (stored-at; stored-hit; live-apart; flatReads; cut-in; module Heaps)
  open Growing R using (wkTree; wkLanes; wkPath; wkPathᴸ)
  open Retagging R using (module Body; fed-owed; fed-retag; envP; joiners-path; retag; unsub-retag; begun-retag; names-retag)
  open RetagShut R using (part-shut)
  open Everywhere.Spending R using (spent-retag)
  open EverywhereGated.Holding R using (holds-alike; holds-path; holds-plant; holds-retag)
  open Keeping R using (seen-planted)
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; conn-left; lingers-sub; lingersL-of; module Linger; module Build; DoneByL; seen-take; Steady; nowAt; fed-at; part-retag; just-connected; flags-retag; sourced-heap; tw-alike)
  open ShiftWalk R using (let-go; grip)
  open Framing R using (merged-eq; heads-flat; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined)
  open FramingRepool R using (Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (conn-kept; module Stays; conn-stays)
  open ClimbTake R using (writes; reads)
  open ClimbFlat R using (calling-open; opened-⊕; heading-∘; lingering-∘; ghost-lift)
  -- A connect's body retagged, its feed restaged: the kernels read it
  -- alike.
  body-holds : ∀ {h} (H : Heapᴹ h) {Δ A B S c b kb k fd₁ fd₂ rp e rt} {src : Sub h Δ A} (g : Retag (A ∷ Δ)) (bd : Sub h (A ∷ Δ) B) {E o}
             → At.Holds H (connectˢ S c b kb k fd₁ rp e rt src bd) E o → At.Holds H (connectˢ S c b kb k fd₂ rp e rt src (retag g bd)) E o
  body-holds H {kb = kb} g bd (a , vb , sb , hs , hb) = a , vb , subst (At.Stashed H kb) (sym (unsub-retag g bd)) sb , hs , holds-retag H g bd hb

  body-gated : ∀ {h} (H : Heapᴹ h) {Δ A B S c b kb k fd₁ fd₂ rp e rt} {src : Sub h Δ A} (g : Retag (A ∷ Δ)) (bd : Sub h (A ∷ Δ) B)
             → At.Gated H (connectˢ S c b kb k fd₁ rp e rt src bd) → At.Gated H (connectˢ S c b kb k fd₂ rp e rt src (retag g bd))
  body-gated H g bd (f₁ , gs , gb) = f₁ , gs , gated-retag H g bd gb

  body-spent : ∀ {h} (H : Heapᴹ h) {Δ A B S c b kb k fd₁ fd₂ rp e rt} {src : Sub h Δ A} (g : Retag (A ∷ Δ)) (bd : Sub h (A ∷ Δ) B)
             → At.Spent H (connectˢ S c b kb k fd₁ rp e rt src bd) → At.Spent H (connectˢ S c b kb k fd₂ rp e rt src (retag g bd))
  body-spent H {kb = nothing} g bd (c₁ , c₂) = c₁ , c₂
  body-spent H {kb = just _}  g bd (c₁ , c₂) = c₁ , spent-retag H g bd c₂

  body-settled : ∀ {h} (H : Heapᴹ h) {Δ A B S c b kb k fd₁ fd₂ rp e rt} {src : Sub h Δ A} (g : Retag (A ∷ Δ)) (bd : Sub h (A ∷ Δ) B)
               → Settled (connectˢ S c b kb k fd₁ rp e rt src bd) → Settled (connectˢ S c b kb k fd₂ rp e rt src (retag g bd))
  body-settled H {kb = kb} g bd (b₁ , b₂ , s₁ , s₂) = b₁ , begun-retag g kb bd b₂ , s₁ , settled-retag H g bd s₂

  -- A connect's open part reads only its children's.
  conn-≡ : ∀ {h} (G G′ : Heapᴹ h) {Δ A B} r (e : Maybe Pos) (t : U.Node Δ A) s (mb : Maybe (U.Node (A ∷ Δ) B))
         → At.connected G′ r e t s mb ≡ At.connected G r e t s mb
  conn-≡ G G′ r e        t s        nothing  = refl
  conn-≡ G G′ r e        t (just _) (just _) = refl
  conn-≡ G G′ r (just _) t nothing  (just _) = refl
  conn-≡ G G′ r nothing  t nothing  (just _) = refl

  -- A CONNECT'S FEED RESTAGED IN PLACE: the source alike, the body
  -- retagged by what the feed owes it.
  module Refed {h} (G : Heapᴹ h) {Δ A B Sj c b kb k rp e rt} {u : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} (fd′ : Feed A h) (q : Pos) where
    g  = at-here {A} {Δ} (At.owing G fd′)
    w₀ = connectˢ Sj c b kb k idle rp e rt u bd
    v  = connectˢ Sj c b kb k fd′ rp e rt u (retag g bd)

    -- The connect's part a new node, the body fed: what it heads, tells
    -- and revives read off it; the body retagged, its parts as open as
    -- before, its heads, ties and leftover kept.
    postulate
      re-revive   : is-just (At.part G v) ≡ true → is-just (At.part G w₀) ≡ true
      re-told     : ∀ {A′} (i : A′ ∈ᴸ Δ) {b₀ b′} → At.part G w₀ ≡ just b₀ → At.part G v ≡ just b′ → untold i b′ ⊆ᴾ untold i b₀
      re-root     : Each G (Heads q) w₀ → ∀ {n} → At.part G v ≡ just n → Heads q n
      re-just     : is-just (At.part G (retag g bd)) ≡ is-just (At.part G bd)
      re-heads    : Each G (Heads q) bd → Each G (Heads q) (retag g bd)
      re-lingers  : Lingers G bd → Lingers G (retag g bd)
      re-leftover : At.leftover G {B = ⊤} (retag g bd) ≡ At.leftover G {B = ⊤} bd

    heading : Heading G G q w₀ v
    heading = record
      { head-revive = re-revive
      ; head-told   = re-told
      ; head-below  = λ ev → Build.each-connect G (Heads q)
          (re-root ev)
          (λ x pn pe → Each.rests ev here refl (proj₂ (just-of (re-revive (cong is-just x)))) pn pe)
          (λ j → each-sub ev (in-source here) (cong (λ z → z ∧ true) (trans (sym re-just) j)))
          (λ j → re-heads (each-sub ev (in-body here) (cong (λ z → z ∧ true) j))) }

    lingering : Lingering G G w₀ v
    lingering = record
      { ling-revive = re-revive
      ; ling-rested = λ {C} → tw-alike (conn-left {B = C} rp {n = At.sourced G (At.part G u) (At.leftover G u)} refl re-leftover)
      ; ling-below  = λ lg → Linger.lg-connect G
          (λ x pn pe → Lingers.rests lg here refl (proj₂ (just-of (re-revive (cong is-just x)))) pn pe)
          (λ jb → lingers-sub G lg (in-source here) (cong (λ z → z ∧ true) (trans (sym re-just) jb)))
          (λ js → re-lingers (lingers-sub G lg (in-body here) (cong (λ z → z ∧ true) js))) }

  -- A call through a connect's source: its subject still open.
  src-open : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
             {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
             (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {sg : Signal T A}
           → Calling g ℓ m₁ (ρ ⊕ in-source here) sg → At.val (Conf.heap (Mach.conf m₁)) (Subject.closed Sj) ≡ false
  src-open {m₁ = m₁} {Sj = Sj} ρ cl
    with At.val (Conf.heap (Mach.conf m₁)) (Subject.closed Sj)
       | trans (sym (opened-⊕ (Conf.heap (Mach.conf m₁)) true ρ (in-source here))) (calling-open (ρ ⊕ in-source here) cl)
  ... | false | _  = refl
  ... | true  | ()

  -- A call through a connect's source: every subscriber its subject
  -- holds joined before where the run is.  A join is made where the run
  -- is, by an event that reached the body, never the source's own.
  postulate
    joined-before : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                    {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                    (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {sg : Signal T A}
                  → Calling g ℓ m₁ (ρ ⊕ in-source here) sg
                  → All (λ s → proj₂ s <ᵖ Conf.pos (Mach.conf m₁) ≡ true) (At.val (Conf.heap (Mach.conf m₁)) (Subject.subscribers Sj))

  -- A CONNECT FEEDING: the feed restaged from `idle` to the source's
  -- value at the run's position, owed to the subscribers the feed read,
  -- the ghost past the source's skip.
  module Feeds {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B Sj c b kb k rp e rt} {u : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
               (ρ : Path T (connectˢ Sj c b kb k idle rp e rt u bd)) (y : A) (q : Pos) where
    fd′ = feeding y q (At.val H (Subject.subscribers Sj))
    module Bd = Body H Sj c b kb k idle fd′ rp e rt u (at-here (At.owing H fd′)) bd
    w₀ = connectˢ Sj c b kb k idle rp e rt u bd
    v  = Bd.w₂
    T′ = plant ρ v

    kin : Kin w₀ v
    kin = kin-feed {g = at-here (At.owing H fd′)}

    g₀ : Retag (A ∷ Δ)
    g₀ = at-here (At.owing H fd′)

    part-v : At.part H v ≡ At.connected H rp e rt (At.part H u) (At.part H (retag g₀ bd))
    part-v = refl

    -- The body retagged keeps a part.  `part-retag` gives it from a
    -- `Steady` retag, which needs the subject open: the call site has
    -- that from `Calling`, these hypotheses do not.
    postulate
      retag-parted : ∀ {b₀} → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
                   → At.part H bd ≡ just b₀ → is-just (At.part H (retag g₀ bd)) ≡ true

    -- The body's part retagged is its part fed the source's value, but
    -- for gaps.  The subscribers the feed read hold the value as the
    -- meaning feeds it (`Meaning`, `At.Joined`); every other joiner, and
    -- every lane or deferred node reached no sooner than `q` (`Heads`),
    -- holds it as a skip no part holds.
    postulate
      retag-fed : ∀ {b₀ b₁} → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
                → At.part H bd ≡ just b₀ → At.part H (retag g₀ bd) ≡ just b₁ → Gapped q (U.feed (here refl) q (just y) b₀) b₁

    -- The connect's part, the feed restaged: its body's part fed the
    -- source's value, but for gaps.
    fed-part : ∀ {b₀ c′} → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
             → At.part H bd ≡ just b₀ → At.part H u ≡ just c′
             → Σ (U.Node (A ∷ Δ) B) λ b₁ → At.part H v ≡ just (U.connectᶜ rp b₁ (U.live c′)) × Gapped q (U.feed (here refl) q (just y) b₀) b₁
    fed-part {b₀} {c′} jn mn bh pb pv = go (At.part H (retag g₀ bd)) refl
      where
        go : ∀ m → At.part H (retag g₀ bd) ≡ m
           → Σ (U.Node (A ∷ Δ) B) λ b₁ → At.part H v ≡ just (U.connectᶜ rp b₁ (U.live c′)) × Gapped q (U.feed (here refl) q (just y) b₀) b₁
        go (just b₁) eb =
          b₁ , trans part-v (trans (cong (λ s → At.connected H rp e rt s (At.part H (retag g₀ bd))) pv) (cong (At.connected H rp e rt (just c′)) eb))
             , retag-fed jn mn bh pb eb
        go nothing eb with () ← trans (sym (retag-parted jn mn bh pb)) (cong is-just eb)

    -- The ghost past the source's skip: the connect's part what it
    -- skipped to, but for gaps, and the heap untouched.
    fed-ghost : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
              → ∀ {g S c′} → Sane [] g → Placed g [] → Deep g [] → At.part H u ≡ just c′
              → Lifts H (ρ ⊕ in-source here) (U.outˢ q y c′) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
    fed-ghost fs jn mn bh sn pd dp pv L sg with lifts-split ρ (in-source here) L
    ... | _ , lifts-source pb sf lifts-here , Lρ with fed-part jn mn bh pb pv
    ...   | b₁ , pv′ , gp rewrite sf = ghost-lift H H ρ v fs (λ _ _ → refl) [] {κ = q} Lρ pv′ (gap-connect gp (gap-live alike)) sn pd dp sg

    -- The connect's own heads and ties, the feed restaged: the body's
    -- joiners retold what the feed owes them.
    -- DEAD ROUTE: a frame.  The part is a new node, the body fed, so
    --   no `Alike` relates it; a node fact over `fed-part`'s `Gapped`.
    module Re = Refed H {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {rp = rp} {e = e} {rt = rt} {u = u} {bd = bd} fd′ q

    fed-heading : Heading H H q w₀ v
    fed-heading = Re.heading

    fed-lingering : Lingering H H w₀ v
    fed-lingering = Re.lingering

    fed-stack : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
    fed-stack = restack kin ρ

    fed-ticked : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (fed-stack sk)
    fed-ticked n sk = reticked kin ρ {n = n} sk

    fed-owned : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (e : act ≗ ⟦ feedC (planted ρ v) ∷ [] ⟧ᶜ)
              → Owned H T (runAs [] (≗-refl _) sk) → Owned H T′ (runAs (feedC (planted ρ v) ∷ []) e (fed-stack sk))
    fed-owned sk e ow = owned-run kin ρ sk [] e refl ow

    -- Every part heads no sooner than the run, the feed restaged.
    fed-behind : AllPairs _≢_ (names T) → Untold H q T → Ends H T → Each H (Heads q) T → Each H (Heads q) T′
    fed-behind fs ut en = Shift.shift-behind H H ρ (λ j _ → refl) [] fs v ut en fed-heading

    fed-lingers : AllPairs _≢_ (names T) → Ends H T → Lingers H T → Lingers H T′
    fed-lingers fs en = Shift.shift-lingers H H ρ (λ j _ → refl) [] fs v en fed-lingering

    -- The feed read by the connect's own joiners alone, each a subscriber
    -- the feed read.
    --
    -- REFUTED: 26b032ed of the feed restaged with each joiner left holding what it held, by a connect of an `of` whose body is a joined subscription
    fed-joins : At.Joined H (subjects T) (joiners T []) → ∀ ν → At.Fed H w₀ ν → At.Fed H v ν
    fed-joins jn = fed-owed H Sj c b kb k fd′ rp e rt u bd (envP ρ [])
                     (λ m → lookupᴬ (proj₂ jn) (joiners-path ρ [] (++⁺ʳ (joiners u (envP ρ [])) m)))

    fed-kernels : Kernels H T → Kernels H T′
    fed-kernels kn = record { holds   = holds-plant H {t = T} ρ v refl (λ {E} {o} → body-holds H {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H fd′)) bd {E} {o}) (Kernels.holds kn)
                            ; gated   = gated-plant H {t = T} ρ v (body-gated H {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H fd′)) bd) (body-spent H {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H fd′)) bd) (Kernels.gated kn)
                            ; settled = settled-plant H {t = T} ρ v Bd.body-owes (body-settled H {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H fd′)) bd) (Kernels.settled kn) }

    fed-meaning : At.Joined H (subjects T) (joiners T []) → Meaning H T → Meaning H T′
    fed-meaning jn mn = record { fed = fed-plant H {t = T} ρ v (fed-joins jn) _ (Meaning.fed mn) }

    fed-queue : ∀ {clk ts} → Queue H q clk ts T → Queue H q clk ts T′
    fed-queue = plant-queue H ρ v Bd.body-pendings Bd.body-subjects Bd.body-joiners

  -- A connect's source signals its subject only with no feed under way:
  -- the subject's subscribers are fed before the source runs again.
  postulate
    src-idle : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
               (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {sg : Signal T A}
             → Calling g ℓ m₁ (ρ ⊕ in-source here) sg → fd ≡ idle

  -- A value reaching a connect's subject: the subscribers read, the feed
  -- owed them, the ghost past the source's skip.
  climb-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                 (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {y : A}
               → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) (sends y) → Called st m₁ (ρ ⊕ in-source here)
  climb-source st ρ cl with src-idle ρ cl
  climb-source st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {Sj} {c} {b} {kb} {k} {e = e} {rp} {rt} {u = u} {bd} ρ {y}
    cl@record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr } | refl
    with subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-source here) top) cd
  ... | readRef≗ refl f with Feeds.fed-ghost hp ρ y q fs (Queue.joined qu) mn bh sn pl dp pv L sg
  ...   | g″ , pg , sn″ , pl″ , dp″ , k′ , r , ag , pp with lifts-split ρ (in-source here) L
  ...     | _ , lifts-source pb _ _ , Lρ =
    landed (g″ , _ , then refl now
      , carried (record
        { sane = sn″ ; placed = pl″ ; deep = dp″ ; tree = Feeds.T′ hp ρ y q
        ; ctlAs = runAs (feedC (planted ρ v) ∷ []) (≗-trans (f same⊑ ss) (seq-done _)) (Feeds.fed-stack hp ρ y q sk)
        ; meets = pg
        ; owned′ = owned-to (Feeds.fed-owned hp ρ y q sk (≗-trans (f same⊑ ss) (seq-done _)) ow)
        ; kernels = Feeds.fed-kernels hp ρ y q kn ; meaning = Feeds.fed-meaning hp ρ y q (Queue.joined qu) mn ; queue = Feeds.fed-queue hp ρ y q qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Feeds.Bd.body-names hp ρ y q))) fs
                         ; clocked = proj₁ ck , Feeds.fed-ticked hp ρ y q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind′ = Eaching.each-to _ _ (Feeds.fed-behind hp ρ y q fs (tells-past cl) (ended-past cl) bh) ; lingers′ = Lingering.lingers-to _ (Feeds.fed-lingers hp ρ y q fs (ended-past cl) lgr) ; flags = let-go hp (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Feeds.Bd.body-names hp ρ y q))) fs)
                    (trans (seen-planted hp ρ v) (lifts-seen Lρ)) ju
                    (subst (DoneBy hp (plant ρ v)) (sym (outers-planted ρ v))
                           (Shift.shift-flags hp hp ρ (λ j _ → refl) [] fs v {ns₀ = []} (λ ()) rv fb (subst (DoneBy hp T) (sym (++-identityʳ (outers ρ))) d₀))) })
      , passed ag pp)
    where
      ss = At.val hp (Subject.subscribers Sj)
      v  = Feeds.v hp ρ y q
      w₀ = connectˢ Sj c b kb k idle rp e rt u bd
      d₀ = done-up ρ (in-source here) refl (Calling.flags cl)
      g = at-here (At.owing hp (Feeds.fd′ hp ρ y q))
      -- The subject open as the value reaches it: every live joiner of
      -- the body waiting, the feed's retag keeping it so.
      cf : At.val hp (Subject.closed Sj) ≡ false
      cf = src-open ρ cl
      kh : Steady hp g ((idle , At.told hp Sj e) ∷ nowAt hp ρ [])
      kh (here refl) (lift f) lv rewrite proj₂ (f lv) (λ ()) | cf = refl
      kh (there x) f lv = refl
      fbd = proj₂ (fed-at hp ρ (Meaning.fed mn))
      -- Below the connect: its source's flags as they were, its body's
      -- through the retag.
      fb : DoneBy hp w₀ (outers ρ ++ []) → DoneBy hp v (outers ρ)
      fb d = Flag.db-connect hp
        (λ jb → Flag.db-sub hp d′ (in-source here) (cong (λ z → z ∧ true) (trans (sym (part-retag hp g bd kh fbd)) jb)))
        (λ js → flags-retag hp g bd kh fbd (Flag.db-sub hp d′ (in-body here) (cong (λ z → z ∧ true) js)))
        where d′ = subst (DoneBy hp w₀) (++-identityʳ (outers ρ)) d
      -- The connect stands, its body fed.
      ju : is-just (At.part hp v) ≡ true
      ju = cong is-just (proj₁ (proj₂ (Feeds.fed-part hp ρ y q (Queue.joined qu) mn bh pb pv)))
      rv : is-just (At.part hp v) ≡ true → is-just (At.part hp w₀) ≡ true
      rv j = trans (sym (just-connected hp rp e rt refl (part-retag hp g bd kh fbd))) j

  -- A CONNECT FINISHING: its subject closed, the feed restaged from `idle`
  -- to the source's end at the run's position, owed to the subscribers
  -- the feed read, ahead of the calls the end owed, the ghost past the
  -- source's skip.
  module Fins {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B Sj c b kb k rp e rt} {u : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
              (ρ : Path T (connectˢ Sj c b kb k idle rp e rt u bd)) (q : Pos) where
    H′ = store H (Subject.closed Sj) (lift true)
    fd′ = finishing q (At.val H′ (Subject.subscribers Sj))
    module Bd = Body H′ Sj c b kb k idle fd′ rp e rt u (at-here (At.owing H′ fd′)) bd
    v  = Bd.w₂
    T′ = plant ρ v

    -- The subject's closed flag the connect's own cell, its node's clauses
    -- reading alike and the rest of the tree by the frame; then the feed
    -- restaged, read by the body's meaning alone.
    w₀ = connectˢ Sj c b kb k idle rp e rt u bd

    ns : List (Name h)
    ns = (_ , Subject.closed Sj) ∷ []

    mine : All (_∈ᴸ names w₀) ns
    mine = there (here refl) ∷ []

    module Wr (fs : AllPairs _≢_ (names T)) = Wrote H H′ ρ (off-store H (Subject.closed Sj)) mine fs

    -- The connect's kernel reads none of its subject's cells.
    fin-rest : AllPairs _≢_ (names w₀) → Alike H H′ (drop 2 (names w₀))
    fin-rest (_ ∷ a₁ ∷ _) j m = look-store H (Subject.closed Sj) j (lookupᴬ a₁ m)

    -- The closed flag read by no part: the node's heads and ties as they
    -- were.
    fin-au : AllPairs _≢_ (names w₀) → Alike H H′ (names u)
    fin-au (_ ∷ a₁ ∷ _) j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))) eq)

    fin-ab : AllPairs _≢_ (names w₀) → Alike H H′ (names bd)
    fin-ab (_ ∷ a₁ ∷ _) j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names u) m))))) eq)

    -- The body finished is the body shut, but for gaps: retagged to what
    -- the finish owes, its part stands, holding the end the ghost's shut
    -- tells.  Each of the connect's own live joiners, the subject open,
    -- waits holding nothing (`Meaning`), and joined before the finish:
    -- the shut tells it under its own position, as the finish owes it.
    --
    -- REFUTED: 021fc08d of the body shut with no joiner's position read, by a live joiner joined at the finish's own position
    fin-shut : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → Meaning H T → At.val H (Subject.closed Sj) ≡ false
             → All (λ s → proj₂ s <ᵖ q ≡ true) (At.val H (Subject.subscribers Sj))
             → ∀ {b₀} → At.part H bd ≡ just b₀
             → Σ (U.Node (A ∷ Δ) B) λ b₁ → At.part H′ (retag (at-here (At.owing H′ fd′)) bd) ≡ just b₁
               × Gapped q (U.shut (here refl) q b₀) (U.shut (here refl) q b₁)
    fin-shut fs jn mn cf bf {b₀} pb = go (At.part H (retag g₀ bd)) refl
      where
        g₀ = at-here (At.owing H′ fd′)
        E = Sj ∷ envP ρ []
        sub : ∀ {sk j} → joiner Sj sk j ∈ᴸ joiners bd E → (sk , j) ∈ᴸ At.val H (Subject.subscribers Sj)
        sub m = lookupᴬ (proj₂ jn) (joiners-path ρ [] (++⁺ʳ (joiners u (envP ρ [])) m))
        hy : ∀ {C} (x : C ∈ᴸ A ∷ Δ) {j sk l st} → joiner (lookupᴬ E x) sk j ∈ᴸ joiners bd E
           → At.Fed H (joinˢ j sk l x st) ((idle , At.told H Sj e) ∷ nowAt H ρ []) → At.val H l ≡ true
           → tells (here refl) q x j (g₀ x j st) ≡ tells (here refl) q x j st
        hy (here refl) m (lift f) lv rewrite proj₂ (f lv) (λ ()) | cf | lookupᴬ bf (sub m) = refl
        hy (there x)   m f        lv = refl
        sh : U.shutᴹ (here refl) q (At.part H (retag g₀ bd)) ≡ just (U.shut (here refl) q b₀)
        sh = trans (part-shut H (here refl) q g₀ bd E hy (proj₂ (fed-at H ρ (Meaning.fed mn)))) (cong (U.shutᴹ (here refl) q) pb)
        al : At.part H′ (retag g₀ bd) ≡ At.part H (retag g₀ bd)
        al = part-alike H H′ (retag g₀ bd) (subst (Alike H H′) (sym (names-retag g₀ bd)) (fin-ab (fresh-path ρ fs)))
        go : ∀ m → At.part H (retag g₀ bd) ≡ m
           → Σ (U.Node (A ∷ Δ) B) λ b₁ → At.part H′ (retag g₀ bd) ≡ just b₁ × Gapped q (U.shut (here refl) q b₀) (U.shut (here refl) q b₁)
        go (just b₁) eb = b₁ , trans al eb
          , subst (Gapped q (U.shut (here refl) q b₀)) (sym (just-injective (trans (cong (U.shutᴹ (here refl) q) (sym eb)) sh))) alike
        go nothing eb with () ← trans (cong (U.shutᴹ (here refl) q) (sym eb)) sh

    -- The ghost past the source's end: the connect shut, its source ended
    -- on what the source left running.  Read at `e = just q`, which the
    -- end staged on its way up: with `e` `nothing` the heap reads no part
    -- past a dead source.  The ghost's rest and the heap's are tied in
    -- meaning through the source's leftover, `Lefts` on one side and
    -- `Lingers` on the other, never in form.
    fin-ghost : AllPairs _≢_ (names T) → Lingers H T → At.Joined H (subjects T) (joiners T []) → Meaning H T
              → At.val H (Subject.closed Sj) ≡ false → All (λ s → proj₂ s <ᵖ q ≡ true) (At.val H (Subject.subscribers Sj))
              → ∀ {g S} → Sane [] g → Placed g [] → Deep g [] → At.part H u ≡ nothing → e ≡ just q
              → (L : Lifts H (ρ ⊕ in-source here) (U.endˢ q) S) → Lefts H L → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H′ T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × Deep g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
    fin-ghost fs lg jn mn cf bf sn pd dp pu eq L lt sg with lifts-split ρ (in-source here) L | lefts-split ρ (in-source here) L lt
    ... | _ , lifts-source {c₀ = c₀} {b₀ = b₀} pb sf lifts-here , Lρ | (lc , _) , _ with fin-shut fs jn mn cf bf pb
    ...   | b₁ , pb′ , gb rewrite sf =
      ghost-lift H H′ ρ v fs (off-store H (Subject.closed Sj)) mine {κ = q} Lρ pv′ (gap-connect gb (gap-tied ag cs dt)) sn pd dp sg
      where
        pv′ : At.part H′ v ≡ just (U.connectᶜ rp (U.shut (here refl) q b₁) (U.ended q rt))
        pv′ = trans (cong₂ (At.connected H′ rp e rt) (trans (part-alike H H′ u (fin-au (fresh-path ρ fs))) pu) pb′)
                    (cong (λ x → At.connected H′ rp x rt nothing (just b₁)) eq)
        pw : At.part H w₀ ≡ just (U.connectᶜ rp (U.shut (here refl) q b₀) (U.ended q rt))
        pw = trans (cong₂ (At.connected H rp e rt) pu pb) (cong (λ x → At.connected H rp x rt nothing (just b₀)) eq)
        lr = Lingers.rests lg ρ (lifts-seen Lρ) pw pu eq
        d⊤ : ∀ ρ′ → Deep (U.restᶜ c₀) ρ′ → Deep (U.restᶜ {B = ⊤} c₀) ρ′
        d⊤ ρ′ d = ordered-retyped (U.cutᴺ c₀ ρ′) (proj₁ d) , proj₂ d
        dt : ∀ ρ′ → Deep (U.restᶜ c₀) ρ′ → Deep rt ρ′
        dt ρ′ d = restful-deep (proj₂ lr) (proj₂ (proj₂ (proj₁ lr) ρ′ (Leaves.deep lc ρ′ (d⊤ ρ′ d))))
        cs : ∀ ρ′ → Deep (U.restᶜ c₀) ρ′ → ∀ n → ML.Agreeᵀ n (U.cutᴺ c₀ ρ′) (U.cutᴺ rt ρ′)
        cs ρ′ d n = tail-agreeᵀ (U.cutᴺ c₀ ρ′) (U.cutᴺ rt ρ′)
                      (ML.agree-trans (Leaves.agree lc ρ′ (d⊤ ρ′ d) n) (ML.agree-sym (Leaves.agree (proj₁ (proj₁ lr)) ρ′ (deep-rest {c = rt} (dt ρ′ d)) n)))
        ag : ∀ ρ′ → Deep (U.restᶜ c₀) ρ′ → ∀ n → Agree n (U.meaning (U.restᶜ c₀) ρ′) (U.meaning rt ρ′)
        ag ρ′ d n = subst (Agree n (ML.tailᴱ (U.cutᴺ c₀ ρ′))) (sym (restful-meaning (proj₂ lr) ρ′)) (tailᴱ-ne (cs ρ′ d n))

    fin-part : AllPairs _≢_ (names (connectˢ Sj c b kb k idle rp e rt u bd)) → At.part (store H (Subject.closed Sj) (lift true)) (connectˢ Sj c b kb k idle rp e rt u bd) ≡ At.part H (connectˢ Sj c b kb k idle rp e rt u bd)
    fin-part fr = trans (cong₂ (At.connected H′ rp e rt) (part-alike H H′ u (fin-au fr)) (part-alike H H′ bd (fin-ab fr)))
                        (conn-≡ H H′ rp e rt (At.part H u) (At.part H bd))

    fin-revive : AllPairs _≢_ (names (connectˢ Sj c b kb k idle rp e rt u bd)) → is-just (At.part (store H (Subject.closed Sj) (lift true)) (connectˢ Sj c b kb k idle rp e rt u bd)) ≡ true → is-just (At.part H (connectˢ Sj c b kb k idle rp e rt u bd)) ≡ true
    fin-revive fr j = trans (cong is-just (sym (fin-part fr))) j

    fin-kept : AllPairs _≢_ (names w₀) → Heading H H′ q w₀ w₀
    fin-kept fr = record
      { head-revive = fin-revive fr
      ; head-told   = λ i e₀ e′ m → ≡-⊆ (cong (untold i) (just-injective (trans (sym e′) (trans (fin-part fr) e₀)))) m
      ; head-below  = each-same H H′ se same }
      where
        se : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path w₀ x) → seen H′ ψ ≡ seen H ψ
        se here          = refl
        se (in-source ψ) = cong₂ _∧_ (cong is-just (part-alike H H′ bd (fin-ab fr))) (seen-alike H H′ ψ (fin-au fr))
        se (in-body ψ)   = cong₂ _∧_ (cong (λ x → is-just x ∨ is-just e) (part-alike H H′ u (fin-au fr))) (seen-alike H H′ ψ (fin-ab fr))
        same : ∀ {Δ′ A′} {x : Sub h Δ′ A′} (ψ : Path w₀ x) → At.part H′ x ≡ At.part H x
        same here                   = fin-part fr
        same {x = x} (in-source ψ)  = part-alike H H′ x (λ j m → fin-au fr j (names-path ψ m))
        same {x = x} (in-body ψ)    = part-alike H H′ x (λ j m → fin-ab fr j (names-path ψ m))

    fin-lkept : AllPairs _≢_ (names w₀) → Lingering H H′ w₀ w₀
    fin-lkept fr = record
      { ling-revive = fin-revive fr
      ; ling-rested = λ {C} → tw-alike (conn-left {B = C} rp src-eq (leftover-alike H H′ {B = ⊤} bd (fin-ab fr)))
      ; ling-below  = λ lg → Linger.lg-connect H′
          (λ x pn pe → subst (λ z → Twin rt z × Restful rt) (sym (leftover-alike H H′ {B = ⊤} u (fin-au fr)))
                         (Lingers.rests lg here refl (trans (sym (fin-part fr)) x) (trans (sym (part-alike H H′ u (fin-au fr))) pn) pe))
          (λ jb → lingers-alike H H′ (fin-au fr) (lingers-sub H lg (in-source here)
                    (cong (λ z → z ∧ true) (trans (cong is-just (sym (part-alike H H′ bd (fin-ab fr)))) jb))))
          (λ js → lingers-alike H H′ (fin-ab fr) (lingers-sub H lg (in-body here)
                    (cong (λ z → z ∧ true) (trans (cong (λ x → is-just x ∨ is-just e) (sym (part-alike H H′ u (fin-au fr)))) js)))) }
      where
        src-eq : At.sourced H′ (At.part H′ u) (At.leftover H′ u) ≡ At.sourced H (At.part H u) (At.leftover H u)
        src-eq = trans (cong₂ (At.sourced H′) (part-alike H H′ u (fin-au fr)) (leftover-alike H H′ u (fin-au fr)))
                       (sourced-heap H H′ (At.part H u) (At.leftover H u))

    -- The connect's own heads and ties, the finish restaged, as the
    -- feed's.
    module Re = Refed H′ {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {rp = rp} {e = e} {rt = rt} {u = u} {bd = bd} fd′ q

    fin-heading : AllPairs _≢_ (names w₀) → Heading H H′ q w₀ v
    fin-heading fr = heading-∘ (fin-kept fr) Re.heading

    fin-lingering : AllPairs _≢_ (names w₀) → Lingering H H′ w₀ v
    fin-lingering fr = lingering-∘ (fin-lkept fr) Re.lingering

    module Sh (fs : AllPairs _≢_ (names T)) = Shift H H′ ρ (off-store H (Subject.closed Sj)) mine fs

    -- The closed flag read by no part: the connect's own clause reads its
    -- children's parts alone, theirs names apart from the flag.
    fin-gone : AllPairs _≢_ (names (connectˢ Sj c b kb k idle rp e rt u bd)) → Gone H (store H (Subject.closed Sj) (lift true)) (connectˢ Sj c b kb k idle rp e rt u bd)
    fin-gone (_ ∷ a₁ ∷ _) = record { gone-part = gp ; gone-live = lives-off {H = H} {H′ = H′} (off-store H (Subject.closed Sj)) nl ; gone-held = store-held H (Subject.closed Sj) }
      where
        au : Alike H H′ (names u)
        au j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))) eq)
        ab : Alike H H′ (names bd)
        ab j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names u) m))))) eq)
        gp : ∀ {Δ′ A′} {x : Sub h Δ′ A′} → Path w₀ x → At.part H x ≡ nothing → At.part H′ x ≡ nothing
        gp here z =
          subst₂ (λ s′ b′ → At.connected H′ rp e rt s′ b′ ≡ nothing) (sym (part-alike H H′ u au)) (sym (part-alike H H′ bd ab))
                 (conn-kept H H′ rp e rt (At.part H u) (At.part H bd) z)
        gp {x = x} (in-source ψ) z = trans (part-alike H H′ x (λ j m → au j (names-path ψ m))) z
        gp {x = x} (in-body ψ)   z = trans (part-alike H H′ x (λ j m → ab j (names-path ψ m))) z
        nl : ∀ {Δ′ A′ i p c′ k′ tk} {s : Sub h Δ′ A′} → Path w₀ (takeWhileˢ i p c′ k′ tk s) → All (_≢_ (_ , Kit.live c′)) ns
        nl (in-source ψ) = (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ (names-path ψ (here refl))))))) (sym eq)) ∷ []
        nl (in-body ψ)   = (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names u) (names-path ψ (here refl))))))) (sym eq)) ∷ []

    kin : Kin w₀ v
    kin = kin-fin {g = at-here (At.owing H′ fd′)}

    fin-calls : List (Call T) → List (Call T′)
    fin-calls = rehomes kin ρ

    fin-code : (ks : List (Call T)) → ⟦ ks ⟧ᶜ ≗ ⟦ fin-calls ks ⟧ᶜ
    fin-code ks = subst (λ z → ⟦ ks ⟧ᶜ ≗ z) (sym (rehomes-code kin ρ ks)) (≗-refl ⟦ ks ⟧ᶜ)

    fin-stack : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
    fin-stack = restack kin ρ

    fin-ticked : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (fin-stack sk)
    fin-ticked n sk = reticked kin ρ {n = n} sk

    fin-owned : AllPairs _≢_ (names T) → ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (ks : List (Call T))
                (e : act ≗ ⟦ finC (planted ρ v) ∷ fin-calls ks ⟧ᶜ)
              → Owned H T (runAs ks (≗-refl _) sk) → Owned H′ T′ (runAs (finC (planted ρ v) ∷ fin-calls ks) e (fin-stack sk))
    fin-owned fs sk ks e ow = owned-run kin ρ sk ks e refl (Sh.wr-owned fs (fin-gone (fresh-path ρ fs)) ow)

    fin-queue : AllPairs _≢_ (names T) → ∀ {clk ts} → Queue H q clk ts T → Queue H′ q clk ts T′
    fin-queue _ qu = plant-queue H′ ρ v Bd.body-pendings Bd.body-subjects Bd.body-joiners (queue-keeps (store-keeps H (Subject.closed Sj) _ (λ ()) (λ ()) (λ ()) (λ ())) qu)

    fin-behind : AllPairs _≢_ (names T) → Untold H q T → Ends H T → Each H (Heads q) T → Each H′ (Heads q) T′
    fin-behind fs ut en = Sh.shift-behind fs v ut en (fin-heading (fresh-path ρ fs))

    fin-lingers : AllPairs _≢_ (names T) → Ends H T → Lingers H T → Lingers H′ T′
    fin-lingers fs en = Sh.shift-lingers fs v en (fin-lingering (fresh-path ρ fs))

    -- The finish read by the connect's own joiners alone, each a
    -- subscriber the finish read, the closed flag apart from the list:
    -- whatever each held before the subject closed, it is told its end.
    --
    -- REFUTED: 26b032ed of the finish staged with each joiner left holding what it held, by a connect of an `of` whose body is a joined subscription
    fin-joins : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → ∀ ν → At.Fed H w₀ ν → At.Fed H′ v ν
    fin-joins fs jn ν (f₁ , f₂) =
      Heaps.fed-alike H H′ u (fin-au fr) ν f₁
      , fed-retag H′ (at-here (At.owing H′ fd′)) bd (Sj ∷ envP ρ []) hy (Heaps.fed-alike H H′ bd (fin-ab fr) _ f₂)
      where
        fr = fresh-path ρ fs
        apart : _≢_ {A = Name h} (_ , Subject.subscribers Sj) (_ , Subject.closed Sj)
        apart with fr
        ... | a₀ ∷ _ = lookupᴬ a₀ (here refl)
        ow : ∀ {sk j} → joiner Sj sk j ∈ᴸ joiners bd (Sj ∷ envP ρ []) → At.Owed H′ fd′ sk j
        ow m = subst (λ z → _ ∈ᴸ z) (sym (cong lower (look-store H (Subject.closed Sj) (Subject.subscribers Sj) (λ eq → apart (sym eq)))))
                     (lookupᴬ (proj₂ jn) (joiners-path ρ [] (++⁺ʳ (joiners u (envP ρ [])) m)))
        hy : ∀ {C} (x : C ∈ᴸ A ∷ Δ) {j sk l st} → joiner (lookupᴬ (Sj ∷ envP ρ []) x) sk j ∈ᴸ joiners bd (Sj ∷ envP ρ [])
           → At.Fed H′ (joinˢ j sk l x st) ((idle , At.told H Sj e) ∷ ν)
           → At.Fed H′ (joinˢ j sk l x (at-here (At.owing H′ fd′) x j st)) ((fd′ , At.told H′ Sj e) ∷ ν)
        hy (here refl) m _ = lift λ _ → (λ _ → refl) , λ no → ⊥-elim (no (ow m))
        hy (there x)   m f = f

    fin-kernels : AllPairs _≢_ (names T) → Kernels H T → Kernels H′ T′
    fin-kernels fs kn = record { holds   = holds-plant H′ {t = T} ρ v refl (λ {E} {o} → body-holds H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd {E} {o}) (Kernels.holds kn′)
                               ; gated   = gated-plant H′ {t = T} ρ v (body-gated H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (body-spent H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (Kernels.gated kn′)
                               ; settled = settled-plant H′ {t = T} ρ v Bd.body-owes (body-settled H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (Kernels.settled kn′) }
      where
        st = conn-stays H H′ {S = Sj} {c} {b} {kb} {k} {idle} {rp} {e} {rt} u bd (fin-rest (fresh-path ρ fs))
        kn′ = Wr.wr-kernels fs (λ {E} {o} → Stays.holds st {E} {o}) (λ {E} {o} → Stays.gated st {E} {o}) (Stays.spent st) kn

    fin-meaning : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → Meaning H T → Meaning H′ T′
    fin-meaning fs jn mn = record { fed = Heaps.fed-path H H′ ρ v (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v Bd.body-names)) fs)
                                            (subst (Offʰ H H′) Bd.body-names (Heaps.keep H H′ (off-store H (Subject.closed Sj)) (lookupᴬ mine))) (fin-joins fs jn) _ (Meaning.fed mn) }

  -- A connect's source ended: its subject closed, the subscribers read,
  -- their finish owed ahead of the calls the end owed.
  close-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                 (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {ks}
               → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) (closes ks) → Called st m₁ (ρ ⊕ in-source here)
  close-source st ρ cl with src-idle ρ cl
  close-source st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {Sj} {c} {b} {kb} {k} {e = e} {rp} {rt} {u = u} {bd} ρ {ks}
    cl@record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg , hl ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; lefts = lt } | refl
    with writes (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-source here) top) cd)
  ... | n′ , en , path₁ with reads {hp = Fins.H′ hp ρ q} en
  ...   | k′ , f , path₂ with Fins.fin-ghost hp ρ q fs lgr (Queue.joined qu) mn (src-open ρ cl) (joined-before ρ cl) sn pl dp gn (healed-end ρ hl gn) L lt sg
  ...     | g″ , pg , sn″ , pl″ , dp″ , k″ , r , ag , pp with lifts-split ρ (in-source here) L
  ...       | _ , lifts-source {b₀ = b₀} pb _ _ , Lρ =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pl″ ; deep = dp″ ; tree = Fins.T′ hp ρ q
        ; ctlAs = runAs (finC (planted ρ v) ∷ Fins.fin-calls hp ρ q ks) ec (Fins.fin-stack hp ρ q sk)
        ; meets = pg
        ; owned′ = owned-to (Fins.fin-owned hp ρ q fs sk ks ec ow)
        ; kernels = Fins.fin-kernels hp ρ q fs kn ; meaning = Fins.fin-meaning hp ρ q fs (Queue.joined qu) mn ; queue = Fins.fin-queue hp ρ q fs qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Fins.Bd.body-names hp ρ q))) fs
                         ; clocked = proj₁ ck , Fins.fin-ticked hp ρ q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind′ = Eaching.each-to _ _ (Fins.fin-behind hp ρ q fs (tells-past cl) (ended-past cl) bh) ; lingers′ = Lingering.lingers-to _ (Fins.fin-lingers hp ρ q fs (ended-past cl) lgr) ; flags = let-go H′ (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Fins.Bd.body-names hp ρ q))) fs)
                    (trans (seen-planted H′ ρ v) (lifts-seen (lifts-off hp H′ ρ fs off₀ Lρ))) ju
                    (subst (DoneBy H′ (plant ρ v)) (sym (outers-planted ρ v))
                           (Fins.Sh.shift-flags hp ρ q fs v {ns₀ = []} (λ ()) rv fb (subst (DoneBy hp T) (sym (++-identityʳ (outers ρ))) d₀))) })
      , passed ag pp)
    where
      path = ⇝-trans path₁ path₂
      ss = At.val (Fins.H′ hp ρ q) (Subject.subscribers Sj)
      v  = Fins.v hp ρ q
      H′ = Fins.H′ hp ρ q
      fr = fresh-path ρ fs
      w₀ = connectˢ Sj c b kb k idle rp e rt u bd
      au = Fins.fin-au hp ρ q fr
      ab = Fins.fin-ab hp ρ q fr
      off₀ = Heaps.keep hp H′ (off-store hp (Subject.closed Sj)) (lookupᴬ (Fins.mine hp ρ q))
      d₀ = done-up ρ (in-source here) refl (Calling.flags cl)
      g = at-here (At.owing H′ (Fins.fd′ hp ρ q))
      -- The subject still open as the end reaches it: every live joiner
      -- of the body waiting, open before the restage and after.
      cf : At.val hp (Subject.closed Sj) ≡ false
      cf = src-open ρ cl
      kh : Steady hp g ((idle , At.told hp Sj e) ∷ nowAt hp ρ [])
      kh (here refl) (lift f) lv rewrite proj₂ (f lv) (λ ()) | cf = refl
      kh (there x) f lv = refl
      ab′ = subst (Alike hp H′) (sym (names-retag g bd)) ab
      fbd = proj₂ (fed-at hp ρ (Meaning.fed mn))
      -- Below the connect: its source's flags and its body's, read alike.
      fb : DoneBy hp w₀ (outers ρ ++ []) → DoneBy H′ v (outers ρ)
      fb d = Flag.db-connect H′
        (λ jb → flags-alike hp H′ au (Flag.db-sub hp d′ (in-source here) (cong (λ z → z ∧ true) (trans (sym (part-retag hp g bd kh fbd)) (trans (cong is-just (sym (part-alike hp H′ (retag g bd) ab′))) jb)))))
        (λ js → flags-alike hp H′ ab′
                  (flags-retag hp g bd kh fbd
                    (Flag.db-sub hp d′ (in-body here) (cong (λ z → z ∧ true) (trans (cong (λ x → is-just x ∨ is-just e) (sym (part-alike hp H′ u au))) js)))))
        where d′ = subst (DoneBy hp w₀) (++-identityʳ (outers ρ)) d
      -- The connect stands: its source gone, its end staged, its body on.
      ju : is-just (At.part H′ v) ≡ true
      ju = trans (just-connected H′ rp _ rt (cong is-just (trans (part-alike hp H′ u au) gn))
                                            (trans (cong is-just (part-alike hp H′ (retag g bd) ab′)) (trans (part-retag hp g bd kh fbd) (cong is-just pb))))
                 (subst (λ e′ → is-just (At.connected H′ rp e′ rt nothing (just b₀)) ≡ true) (sym (healed-end ρ hl gn)) refl)
      -- Open after, open before: the retag keeps every live joiner open.
      rv : is-just (At.part H′ v) ≡ true → is-just (At.part hp w₀) ≡ true
      rv j = trans (cong is-just (sym (conn-≡ hp H′ rp e rt (At.part hp u) (At.part hp bd))))
                   (trans (sym (just-connected H′ rp e rt (cong is-just (part-alike hp H′ u au))
                                                         (trans (cong is-just (part-alike hp H′ (retag g bd) ab′)) (part-retag hp g bd kh fbd)))) j)
      ec = ≗-trans (f same⊑ ss) (bind≗ (≗-refl (Strongly.code R (finC (planted ρ v)))) λ _ → ≗-trans (wk-same ⟦ ks ⟧ᶜ) (Fins.fin-code hp ρ q ks))

  -- A signal reaching a connect's subject.
  call-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {sg : Signal T A}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) sg → Called st m₁ (ρ ⊕ in-source here)
  call-source st ρ {sends _}  cl = climb-source st ρ cl
  call-source st ρ {closes _} cl = close-source st ρ cl
