{-# OPTIONS --guardedness #-}

-- THE CLIMB, SHARED: the moves every operator's rise is made of.
module adequacy.Climbs.Base where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.Nat.Properties using (≤-refl; +-monoʳ-<; +-monoˡ-<)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_; ↭-reflexive) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (_∷_)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (suc; _<_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)

open import denotation.MonotonicList.Events using (Events∞; Pos; Timeline; last; ix; tick)
open import denotation.MonotonicList using (agree-refl)
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
open import adequacy.Shift.Walk using (module ShiftWalk)
open import adequacy.Kept using (module Keeping)

open Events∞

module ClimbBase (R : Set) where
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
  open FramingRepool R using (Untold; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off) renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open WeakeningHeaps R using () renaming (module GrownHeaps to Weakened′)
  open EverywhereGated R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read

  handleOf : ∀ {h} {t : Sub h [] R} → Spot t → Maybe (Handle h)
  handleOf (spot {u = coldˢ _ hd _} _) = just hd
  handleOf _                           = nothing

  -- A spent burst owes nothing: no live cold is its spot.
  spent-spot : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {b} (x : BurstAs t (just b)) {S} → spent? H (Playing.handle b) ≡ true
             → ∀ {Δ A s hd v} (π : Path t (coldˢ {Δ = Δ} {A} s hd v)) → spent? H hd ≡ false → spot π ∈ᴸ burstSpots t x ++ S → spot π ∈ᴸ S
  spent-spot H (playsAs _) sp π nsp (here e) = ⊥-elim (true≢false (trans (sym sp) (subst (λ z → spent? H z ≡ false) (just-injective (cong handleOf e)) nsp)))
  spent-spot H (firesAs _) sp π nsp (here e) = ⊥-elim (true≢false (trans (sym sp) (subst (λ z → spent? H z ≡ false) (just-injective (cong handleOf e)) nsp)))
  spent-spot H (playsAs _) sp π nsp (there i) = i
  spent-spot H (firesAs _) sp π nsp (there i) = i

  -- A spent burst dropped: what the stack under it owes is all that is
  -- owed.
  owned-spent : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p₀ c₀ bs₀ b w p} {σ : w ⊑ h} {K bs} {x : BurstAs t (just b)} {hᴷ} {K′ : StackAs t p σ K bs}
                (ca₀ : CtlAs t p₀ c₀ bs₀) → spent? H (Playing.handle b) ≡ true
              → agenda t ca₀ ≡ stackJobs t K′ → bursts t ca₀ ≡ stackBursts t K′ → begins t ca₀ ≡ sources t (stackJobs t K′)
              → Owned H t (burstAs x hᴷ K′) → Owned H t ca₀
  owned-spent H {t} {x = x} ca₀ sp ag bu be ow = record
    { ofs    = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ofs ow π)
    ; plays  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (spent-spot H x sp π nsp (Owned.plays ow π nsp))
    ; fires  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (spent-spot H x sp π nsp (Owned.fires ow π nsp))
    ; begun  = λ π → subst (λ z → _ ∈ᴸ z) (sym be) (Owned.begun ow π)
    ; ends   = λ π l → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.ends ow π l)
    ; cuts   = λ π l → proj₁ (Owned.cuts ow π l) , subst (λ z → _ ∈ᴸ z) (sym ag) (proj₂ (Owned.cuts ow π l))
    ; feeds  = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.feeds ow π)
    ; fins   = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (Owned.fins ow π)
    ; bodies = λ π i → Owned.bodies ow π (subst (λ z → _ ∈ᴸ z) ag i)
    ; placed = subst (All (Placedᴬ t)) (sym ag) (Owned.placed ow) }

  -- A spent burst dropped, the stack it holds over resumed.
  drop-held : ∀ {h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {K clk ts b bs lg en mk} → spent? hp (Playing.handle b) ≡ true
            → step (mach ⟨ hp , p , held σ K ⟩ clk ts (just b ∷ bs) [] lg en mk) ≡ silent (feed (mach ⟨ hp , p , held σ K ⟩ clk ts bs [] lg en mk) goᴵ)
  drop-held sp rewrite sp = refl

  -- A spent burst dropped, the stack resumed: the turn over nothing, or
  -- what follows the cold's start, about to run.  The ghost alike, a
  -- burst fewer.
  burst-spent : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
              → Mach.bursts m ≡ just b ∷ bs → spent? (Conf.heap (Mach.conf m)) (Playing.handle b) ≡ true
              → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-spent {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk} {K = K} {b = b} {bs = bs} {σ = σ}
    cr@record { tree = t ; ctlAs = burstAs x bottomᴴ bottomAs ; meets = mt ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned′ = owned-to (owned-spent hp calmAs sp refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
  burst-spent {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk} {K = K} {b = b} {bs = bs} {σ = σ}
    cr@record { tree = t ; ctlAs = burstAs x restᴴ (restAs ks e K″) ; meets = mt ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; deep = Carried.deep cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned′ = owned-to (owned-spent hp (runAs ks e K″) sp refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

  -- A burst's frame stepped: found spent, polled, or played.
  burst-onward : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-onward {m = m} {b = b} cr c bq eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b) in sp | Playing.polled b in pl
  ... | true  | _     = burst-spent cr c bq sp eq
  ... | false | false = burst-poll cr c bq sp pl eq
  ... | false | true  = burst-play cr c bq sp pl eq

  -- A signal through a map: a value mapped, an end as it is.
  mapᵍ : ∀ {h} {T : Sub h [] R} {A B} → (A → B) → Signal T A → Signal T B
  mapᵍ f (sends y)   = sends (f y)
  mapᵍ f (closes ks) = closes ks

  -- A signal through a map, one operator up.
  call-map : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
             (ρ : Path T (mapˢ f u)) {sg : Signal T A} → Calling g ℓ m₁ (ρ ⊕ in-map here) sg → Calling g ℓ m₁ ρ (mapᵍ f sg)
  call-map {m₁ = m₁} {f = f} ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-map here) top) (Calling.code cl))
    (U.mapᶜ f c′ , cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) pv , S , Lρ , sg) (done-up ρ (in-map here) refl (Calling.flags cl))
  call-map {m₁ = m₁} {f = f} ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg , hl with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-map here) top) (Calling.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) gn , S , Lρ , sg , healed-split ρ (in-map here) hl) (done-up ρ (in-map here) refl (Calling.flags cl))

  -- A signal through a defer, as it is.
  call-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (deferˢ k u)) {sg : Signal T A} → Calling g ℓ m₁ (ρ ⊕ in-defer here) sg → Calling g ℓ m₁ ρ sg
  call-defer ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (c′ , pv , S , Lρ , sg) (done-up ρ (in-defer here) refl (Calling.flags cl))
  call-defer ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg , hl with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (gn , S , Lρ , sg , healed-split ρ (in-defer here) hl) (done-up ρ (in-defer here) refl (Calling.flags cl))

  -- A body's cut owed ahead of the agenda, its body gone.
  owned-body : ∀ {h} (H : Heapᴹ h) {t : Sub h [] R} {p c bs p₀ c₀ bs₀} {ca : CtlAs t p c bs} (ca₀ : CtlAs t p₀ c₀ bs₀)
               {Δ A B Sj cc b kb k fd e rp rt q} {s : Sub h Δ A} {bd : Sub h (A ∷ Δ) B} (ρ : Path t (connectˢ Sj cc b kb k fd rp e rt s bd))
             → agenda t ca₀ ≡ (q , bodyC ρ) ∷ agenda t ca → bursts t ca₀ ≡ bursts t ca → begins t ca₀ ≡ begins t ca
             → At.part H bd ≡ nothing → Owned H t ca → Owned H t ca₀
  owned-body H {t} {ca = ca} ca₀ {q = q} ρ ag bu be gn ow = record
    { ofs    = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.ofs ow π))
    ; plays  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.plays ow π nsp)
    ; fires  = λ π nsp → subst (λ z → _ ∈ᴸ z) (sym bu) (Owned.fires ow π nsp)
    ; begun  = λ π → subst (λ z → _ ∈ᴸ z) (sym be) (Owned.begun ow π)
    ; ends   = λ π l → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.ends ow π l))
    ; cuts   = λ π l → proj₁ (Owned.cuts ow π l) , subst (λ z → _ ∈ᴸ z) (sym ag) (there (proj₂ (Owned.cuts ow π l)))
    ; feeds  = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.feeds ow π))
    ; fins   = λ π → subst (λ z → _ ∈ᴸ z) (sym ag) (there (Owned.fins ow π))
    ; bodies = λ π i → bodied π (subst (λ z → _ ∈ᴸ z) ag i)
    ; placed = subst (All (Placedᴬ t)) (sym ag) (tt ∷ Owned.placed ow) }
    where
      bodied : ∀ {Δ′ A′ B′ Sj′ c′ b′ kb′ k′ fd′ e′ rp′ rt′ q′} {s′ : Sub _ Δ′ A′} {bd′ : Sub _ (A′ ∷ Δ′) B′}
               (π : Path t (connectˢ Sj′ c′ b′ kb′ k′ fd′ rp′ e′ rt′ s′ bd′)) → (q′ , bodyC π) ∈ᴸ (q , bodyC ρ) ∷ agenda t ca → At.part H bd′ ≡ nothing
      bodied π (here refl) = gn
      bodied π (there i)   = Owned.bodies ow π i

  -- A connect over a gone body is gone.
  gone-connect : ∀ {h} (H : Heapᴹ h) {Δ A B Sj c b kb k fd e rp rt} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B}
               → At.part H u ≡ nothing → At.part H (connectˢ Sj c b kb k fd rp e rt t u) ≡ nothing
  gone-connect H {t = t} gn rewrite gn with At.part H t
  ... | just _  = refl
  ... | nothing = refl

  -- An end lifted out of a body is the connect's end.
  body-end : ∀ {h} {H : Heapᴹ h} {Δ A B Sj c b kb k fd e rp rt} {t : Sub h Δ A} {u : Sub h (A ∷ Δ) B} {q S}
           → Lifts H (in-body {S = Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} (here {t = u})) (U.endˢ q) S → S ≡ U.endˢ q
  body-end (lifts-body _ _ lifts-here)   = refl
  body-end (lifts-shut _ _ _ lifts-here) = refl

  -- A signal out of a connect's body.  A value as it is: beside its
  -- source, or past its source's end.  An end the connect's completion
  -- delivered, its cut owed after it, the body gone as a `bodyC` owed
  -- asks.
  call-body : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
              {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
              (ρ : Path T (connectˢ Sj c b kb k fd rp e rt t u)) {sg : Signal T B}
            → Calling g (loadOf st) m₁ (ρ ⊕ in-body here) sg → Called st m₁ (ρ ⊕ in-body here)
  call-body st {m₁ = m₁} {e = e} {rp} {rt} ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-body here) L
  ...   | _ , lifts-body pt _ lifts-here , Lρ = rose now (one-lower ρ one-body) (recall cl {sg′ = sends y} refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Calling.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg) (done-up ρ (in-body here) refl (Calling.flags cl)))
  ...   | _ , lifts-shut pt refl _ lifts-here , Lρ = rose now (one-lower ρ one-body) (recall cl {sg′ = sends y} refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Calling.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg) (done-up ρ (in-body here) refl (Calling.flags cl)))
  call-body st {m₁ = m₁} {T = T} {Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {u} ρ {closes ks}
    record { sane = sn ; placed = pl ; deep = dp ; ctl = cx ; code = cd ; stack = sk ; lifted = gn , S , L , sg , hl ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-body here) L
  ... | _ , Lb , Lρ = rose {sg′ = closes (bodyC ρ ∷ ks)} now (one-lower ρ one-body) (record
      { sane = sn ; placed = pl ; deep = dp ; ctl = cx
      ; code = ≗-trans (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-body here) top) cd) (seq-assoc (Observer.complete (Here.obs (walk ρ top))) (Kit.cut c) ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; lifted = gone-connect (Conf.heap (Mach.conf m₁)) {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = t} {u = u} gn
               , S , subst (λ s → Lifts (Conf.heap (Mach.conf m₁)) ρ s S) (body-end Lb) Lρ , sg , healed-split ρ (in-body here) hl
      ; owned = owned-body (Conf.heap (Mach.conf m₁)) (runAs (bodyC ρ ∷ ks) (≗-refl ⟦ bodyC ρ ∷ ks ⟧ᶜ) sk) ρ refl refl refl gn ow
      ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = so ; behind = bh ; lingers = lgr ; flags = done-up ρ (in-body here) refl dn ; kept = kp })

  -- A live take's part, its source's lifted.
  take-part : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} {c′} → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
            → At.part H (takeWhileˢ i p c k taking u) ≡ just (U.takeWhileᶜ i p c′)
  take-part H lv pv rewrite lv | pv = refl

  -- A guard read open over a predicate holding: what it guards.
  pass-code : ∀ {w} {b q : Bool} {m n : Act w ⊤} → b ≡ true → q ≡ true → Kit.when b (if q then m else n) ≗ m
  pass-code refl refl = ≗-refl _

  -- A value a live takeWhile passes: its guard read, one operator up,
  -- the tree's load as it was.
  take-pass : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k taking u)) {y : A} → p y ≡ true
            → Calling g ℓ m₁ (ρ ⊕ in-take here) (sends y) → Rises g (load m₁ T) m₁ (ρ ⊕ in-take here)
  take-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    record { sane = sn ; placed = pl ; deep = dp ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rises {sg′ = sends y} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; deep = dp ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (≗-trans (wk-same _) (pass-code lv py))
      ; stack = sk
      ; lifted = U.takeWhileᶜ i p c′ , take-part hp {i = i} {p = p} {c = c} {k = k} {u = u} lv pv , S , subst (λ s → Lifts hp ρ s S) (cong (U.taking i p q y c′) py) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; lingers = lgr ; flags = done-up ρ (in-take here) refl dn ; kept = inj₁ refl })

  -- A plant counting fewer stages than what it replaced counts fewer.
  mutual
    takes-less : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ρ : Path t x) (v : Sub h Δ′ A′) → takes v < takes x → takes (plant ρ v) < takes t
    takes-less here                    v lt = lt
    takes-less (in-map ρ)              v lt = takes-less ρ v lt
    takes-less (in-scan ρ)             v lt = takes-less ρ v lt
    takes-less (in-take {tk = tk} ρ)   v lt = +-monoʳ-< (stage tk) (takes-less ρ v lt)
    takes-less (in-outer {ls = ls} ρ)  v lt = +-monoˡ-< (takesᴸ ls) (takes-less ρ v lt)
    takes-less (in-lanes {t = so} ρ)   v lt = +-monoʳ-< (takes so) (takes-lessᴸ ρ v lt)
    takes-less (in-source {bd = bd} ρ) v lt = +-monoˡ-< (takes bd) (takes-less ρ v lt)
    takes-less (in-body {t = s} ρ)     v lt = +-monoʳ-< (takes s) (takes-less ρ v lt)
    takes-less (in-defer ρ)            v lt = takes-less ρ v lt

    takes-lessᴸ : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (ρ : PathLanes ls x) (v : Sub h Δ′ A′)
                → takes v < takes x → takesᴸ (plantᴸ ρ v) < takesᴸ ls
    takes-lessᴸ (this-lane {ls = ls} ρ)          v lt = +-monoˡ-< (takesᴸ ls) (takes-less ρ v lt)
    takes-lessᴸ (next-lane {l = lane c k s} ρ)   v lt = +-monoʳ-< (takes s) (takes-lessᴸ ρ v lt)

  -- A guard read open over a predicate failing, an exclusive take's:
  -- the completion and the cut.
  end-code : ∀ {w} {b q : Bool} {m x : Act w ⊤} → b ≡ true → q ≡ false → Kit.when b (if q then m else (done tt >>ᴬ x)) ≗ x
  end-code refl refl = ≗-refl _

  -- A lift reads no part on its path, so a plant at the path's end
  -- lifts as what it replaced.
  mutual
    lifts-planted : ∀ {h} {H : Heapᴹ h} {Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ρ : Path t x) (v : Sub h Δ′ A′) {s S}
                  → Lifts H ρ s S → Lifts H (planted ρ v) s S
    lifts-planted here         v lifts-here                = lifts-here
    lifts-planted (in-map ρ)   v (lifts-map L)             = lifts-map (lifts-planted ρ v L)
    lifts-planted (in-scan ρ)  v (lifts-scan L)            = lifts-scan (lifts-planted ρ v L)
    lifts-planted (in-take ρ)  v (lifts-take lv L)         = lifts-take lv (lifts-planted ρ v L)
    lifts-planted (in-outer ρ) v (lifts-outer of pb L)     = lifts-outer of pb (lifts-planted ρ v L)
    lifts-planted (in-lanes πL) v (lifts-lanes L ea lf pb) = lifts-lanes (liftsL-planted πL v L) ea lf pb
    lifts-planted (in-source ρ) v (lifts-source pb sf L)   = lifts-source pb sf (lifts-planted ρ v L)
    lifts-planted (in-body ρ)  v (lifts-body pt bf L)      = lifts-body pt bf (lifts-planted ρ v L)
    lifts-planted (in-body ρ)  v (lifts-shut pt e rb L)    = lifts-shut pt e rb (lifts-planted ρ v L)
    lifts-planted (in-defer ρ) v (lifts-defer L)           = lifts-defer (lifts-planted ρ v L)

    liftsL-planted : ∀ {h} {H : Heapᴹ h} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (πL : PathLanes ls x) (v : Sub h Δ′ A′) {s bs S as}
                   → LiftsLane H πL s bs S as → LiftsLane H (plantedᴸ πL v) s bs S as
    liftsL-planted (this-lane ρ) v (lifts-this lv L) = lifts-this lv (lifts-planted ρ v L)
    liftsL-planted (next-lane πL) v (lifts-next L)   = lifts-next (liftsL-planted πL v L)

  -- A plant is as high as the path it replaced.
  mutual
    height-planted : ∀ {h Δ A Δ′ A′} {t : Sub h Δ A} {x : Sub h Δ′ A′} (ρ : Path t x) (v : Sub h Δ′ A′) → height (planted ρ v) ≡ height ρ
    height-planted here          v = refl
    height-planted (in-map ρ)    v = cong suc (height-planted ρ v)
    height-planted (in-scan ρ)   v = cong suc (height-planted ρ v)
    height-planted (in-take ρ)   v = cong suc (height-planted ρ v)
    height-planted (in-outer ρ)  v = cong suc (height-planted ρ v)
    height-planted (in-lanes πL) v = heightL-planted πL v
    height-planted (in-source ρ) v = cong suc (height-planted ρ v)
    height-planted (in-body ρ)   v = cong suc (height-planted ρ v)
    height-planted (in-defer ρ)  v = cong suc (height-planted ρ v)

    heightL-planted : ∀ {h Δ B Δ′ A′} {ls : List (Lane h Δ B)} {x : Sub h Δ′ A′} (πL : PathLanes ls x) (v : Sub h Δ′ A′)
                    → heightL (plantedᴸ πL v) ≡ heightL πL
    heightL-planted (this-lane ρ)  v = cong suc (height-planted ρ v)
    heightL-planted (next-lane πL) v = heightL-planted πL v

  -- Under any label off the root, likewise.
  tick-under : ∀ r i → r ≢ [] → tick (r ++ [ ix i ]) ≡ tick r
  tick-under []           i e = ⊥-elim (e refl)
  tick-under (ix _ ∷ _)   i _ = refl
  tick-under (subᴾ _ ∷ _) i _ = refl
  tick-under (last ∷ _)   i _ = refl

  -- A run under `ix 0`: one step down, its rest owed back where it was.
  out-step : ∀ {h} {hp : Heapᴹ h} {q clk ts bs td lg en mk} {w} {ϑ : w ⊑ h} {K : Stack w ⊤} {act M N : Act h ⊤}
           → act ≗ under (ix 0) M N
           → Σ (Act h ⊤) λ M′ → Σ (Act h ⊤) λ N′ → M′ ≗ M × N′ ≗ N
             × mach ⟨ hp , q , run act ϑ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ hp , q ++ [ ix 0 ] , run M′ same⊑ (push (back q N′) ϑ K) ⟩ clk ts bs td lg en mk
  out-step (under≗ eM eN) = _ , _ , eM , eN , then refl now

  -- A guard read open over a predicate failing, an inclusive take's: the
  -- failing value under `ix 0`, the rest after it.
  out-code : ∀ {w} {b q : Bool} {m M N : Act w ⊤} → b ≡ true → q ≡ false → Kit.when b (if q then m else under (ix 0) M N) ≗ under (ix 0) M N
  out-code refl refl = ≗-refl _

  -- A switch read beside a stage that is not taking.
  and-false : ∀ b → b ∧ false ≡ true → ⊥
  and-false true  ()
  and-false false ()

  -- A queue left: the flatMap open.
  merged-queued : ∀ {h} (G : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) o L pl {y ys} → At.merged G op g o L (y ∷ ys) pl ≡ nothing → ⊥
  merged-queued G op g nothing  []      pl ()
  merged-queued G op g nothing  (_ ∷ _) pl ()
  merged-queued G op g (just _) L       pl ()

  -- A flatMap stays shut with its lanes still shut.
  merged-kept : ∀ {h} (G G′ : Heapᴹ h) {Δ A B} op (g : A → Pos → U.Node Δ B) o L Q pl {L′} → (L ≡ [] → L′ ≡ [])
              → At.merged G op g o L Q pl ≡ nothing → At.merged G′ op g o L′ Q pl ≡ nothing
  merged-kept G G′ op g nothing  []      []      pl f e rewrite f refl = refl
  merged-kept G G′ op g nothing  []      (_ ∷ _) pl f ()
  merged-kept G G′ op g nothing  (_ ∷ _) Q       pl f ()
  merged-kept G G′ op g (just _) L       Q       pl f ()

  -- A connect stays shut.
  conn-kept : ∀ {h} (G G′ : Heapᴹ h) {Δ A B} r (e : Maybe Pos) (t : U.Node Δ A) s (b : Maybe (U.Node (A ∷ Δ) B))
            → At.connected G r e t s b ≡ nothing → At.connected G′ r e t s b ≡ nothing
  conn-kept G G′ r e        t s        nothing  _ = refl
  conn-kept G G′ r nothing  t nothing  (just _) _ = refl
  conn-kept G G′ r (just _) t nothing  (just _) ()
  conn-kept G G′ r e        t (just _) (just _) ()

  -- A write within a node its part unmoved: every connect above that
  -- reads its source gone, as before.
  mutual
    healed-off : ∀ {h} (H H′ : Heapᴹ h) {q} {Δ A Δ′ A′} {t : Sub h Δ A} {u : Sub h Δ′ A′} (π : Path t u) → AllPairs _≢_ (names t)
               → Offʰ H H′ (names u) → At.part H′ u ≡ At.part H u → Healed H q π → Healed H′ q π
    healed-off H H′ here ps off eq _ = lift tt
    healed-off H H′ (in-map {f = f} {t = s} π) ps off eq hl = healed-off H H′ π (fresh-path (in-map {f = f} {t = s} here) ps) off eq hl
    healed-off H H′ (in-scan {f = f} {r} {t = s} π) ps off eq hl = healed-off H H′ π (fresh-path (in-scan {f = f} {r} {t = s} here) ps) off eq hl
    healed-off H H′ (in-take {i = i} {p} {c} {k} {tk} {t = s} π) ps off eq hl = healed-off H H′ π (fresh-path (in-take {i = i} {p} {c} {k} {tk} {t = s} here) ps) off eq hl
    healed-off H H′ (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = s} {ls} π) ps off eq hl =
      healed-off H H′ π (fresh-path (in-outer {op = op} {f} {fl} {oc} {k} {r} {pl} {t = s} {ls} here) ps) off eq hl
    healed-off H H′ (in-lanes {fl = fl} {oc} {k} {r} {t = so} π) ps off eq hl =
      healedL-off H H′ π (pairs-r (names so) (pairs-r ((_ , r) ∷ []) (pairs-r (quietName k) (pairs-r (cutNames oc) (pairs-r (flatNames fl) ps))))) off eq hl
    healed-off H H′ (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps off eq (x , hl) =
      (λ z → x (trans (sym (part-path H H′ π fp off eq)) z)) , healed-off H H′ π fp off eq hl
      where fp = fresh-path (in-source {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} here) ps
    healed-off H H′ (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} π) ps off eq hl =
      healed-off H H′ π (fresh-path (in-body {S = S} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = src} {bd} here) ps) off eq hl
    healed-off H H′ (in-defer {k = k} {t = s} π) ps off eq hl = healed-off H H′ π (fresh-path (in-defer {k = k} {t = s} here) ps) off eq hl

    healedL-off : ∀ {h} (H H′ : Heapᴹ h) {q} {Δ B Δ′ A′} {ls : List (Lane h Δ B)} {u : Sub h Δ′ A′} (π : PathLanes ls u) → AllPairs _≢_ (laneNames ls)
                → Offʰ H H′ (names u) → At.part H′ u ≡ At.part H u → HealedL H q π → HealedL H′ q π
    healedL-off H H′ (this-lane {c = c} {k} {t = s} {ls} π) ps off eq hl = healed-off H H′ π (fresh-lanes (this-lane {c = c} {k} {t = s} {ls} here) ps) off eq hl
    healedL-off H H′ (next-lane {l = lane c k s} π) ps off eq hl = healedL-off H H′ π (pairs-r (names s) (pairs-r (quietName k) (pairs-r (cutNames c) ps))) off eq hl

  -- A map's part held exactly where what it maps is.
  map-just : ∀ {h} (G : Heapᴹ h) {X Y : Set₁} (g : X → Y) m → is-just (At.mapᴹ G g m) ≡ is-just m
  map-just G g nothing  = refl
  map-just G g (just _) = refl

  -- A live take ending shows its end owed.
  ending-part : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} {q c′} → At.val H (Kit.live c) ≡ true
              → At.part H (takeWhileˢ i p c k (Strongly.ending q c′) u) ≡ just (U.endingᶜ (q ++ [ last ]) c′)
  ending-part H lv rewrite lv = refl

  -- A WRITE NO READ OF A NODE'S KERNEL SEES: its holds, gates and spent
  -- alike.
  record Stays {h} (H H′ : Heapᴹ h) {Δ A} (u : Sub h Δ A) : Set₁ where
    field
      holds : ∀ {E o} → At.Holds H u E o → At.Holds H′ u E o
      gated : ∀ {E o} → At.Holds H u E o → At.Gated H u → At.Gated H′ u
      spent : At.Spent H u → At.Spent H′ u

  flat-stays : ∀ {h} (H H′ : Heapᴹ h) {Δ A B op f fl oc k r pl} (so : Sub h Δ A) (ls : List (Lane h Δ B))
             → Alike H H′ (flatReads fl oc k r so ls) → Stays H H′ (flatMapˢ op f fl oc k r pl so ls)
  flat-stays H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} so ls ag = record
    { holds = λ {E} {o} → Heaps.holds-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} so ls ag {E} {o}
    ; gated = λ _ → Heaps.gated-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} so ls ag
    ; spent = Heaps.spent-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} so ls ag }

  conn-stays : ∀ {h} (H H′ : Heapᴹ h) {Δ A B S c b kb k fd rp e rt} (src : Sub h Δ A) (bd : Sub h (A ∷ Δ) B)
             → Alike H H′ (drop 2 (names (connectˢ S c b kb k fd rp e rt src bd))) → Stays H H′ (connectˢ S c b kb k fd rp e rt src bd)
  conn-stays H H′ {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd ag = record
    { holds = λ {E} {o} → Heaps.holds-conn H H′ {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd ag {E} {o}
    ; gated = λ _ → Heaps.gated-conn H H′ {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd ag
    ; spent = Heaps.spent-conn H H′ {S = S} {c} {b} {kb} {k} {fd} {rp} {e} {rt} src bd ag }

  -- A WRITE AT A NODE, FRAMED: its kernel, its feeds and the queue alike,
  -- so every record of the tree carried across.
  module Framed {h} (H H′ : Heapᴹ h) {T : Sub h [] R} {Δ A} {u : Sub h Δ A} (ρ : Path T u)
                {ns : List (Name h)} (off : Offʰ H H′ ns) (mine : All (_∈ᴸ names u) ns) (fs : AllPairs _≢_ (names T))
                (st : Stays H H′ u) (fv : ∀ ν → At.Fed H u ν → At.Fed H′ u ν) (kp : Keeps H H′) where
    open Wrote H H′ ρ off mine fs public
    open Shift H H′ ρ off mine fs public

    kernels : Kernels H T → Kernels H′ T
    kernels = wr-kernels (λ {E} {o} → Stays.holds st {E} {o}) (λ {E} {o} → Stays.gated st {E} {o}) (Stays.spent st)

    meaning : Meaning H T → Meaning H′ T
    meaning = wr-meaning fv

    queue : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
    queue = queue-keeps kp

    -- Nothing left at the node: its ties as they were.
    lingers : Ends H T → Lingering H H′ u u → Lingers H T → Lingers H′ T
    lingers en lg l = subst (Lingers H′) (plant-self ρ) (shift-lingers u en lg l)
