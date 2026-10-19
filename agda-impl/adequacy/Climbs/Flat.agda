{-# OPTIONS --guardedness #-}

-- THE CLIMB THROUGH A FLATMAP'S OUTER: its rise, its close, a lane begun.
module adequacy.Climbs.Flat where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
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
open import Data.Nat using (ℕ; suc; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; skip; Pos; Timeline; Agree; ix; <ᵖ-below)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane; SaneS; step-sane)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (placed-after; Placedˢ; step-skips; afterᴱ; _≃_)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
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

open Events∞

module ClimbFlat (R : Set) where
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
  open Tearing R using (holds-at; cuts; attached-alike; cuts-switches; fresh-path; fresh-lanes; part-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; apart-l; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
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
  open Framing R using (merged-eq; heads-flat; heads-repool; Untold; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike; lifts-off)
    renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open Everywhere R using (module Growths)
  open Replanting R using (Kin; kin-end; kin-pool; kin-feed; kin-fin; kin-lane; rehomes; rehomes-code; restack; reticked; owned-run; module Shift; Heading; Lingering; Gone; store-held; Lives; lives-off; ahead-under)
  open Read
  open ClimbBase R using (lifts-planted; tick-under; healed-off; module Framed; flat-stays)
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
    ; ling-rested = λ {C} → pinned-trans (p₁ {C}) (p₂ {C})
    ; ling-below  = λ lg → b₂ (b₁ lg) }

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

    -- A pool joined with an idle one ties what it tied.
    -- SUSPECT: `step (unionᶜ p idleᶜ)` reads `restˢ p`, not `step p`; for
    --   a pool not `Restful` (a `framesᶜ` stepping to a skip) the two part.
    postulate
      idle-tied : ∀ {Γ A B} {p : U.Node Γ A} {x : U.Node Γ B} → Tied p x → Tied (U.unionᶜ p U.idleᶜ) x

    pool-idling : pl′ ≡ U.unionᶜ pl U.idleᶜ → Lingering H H w₀ v
    pool-idling e = record
      { ling-revive = λ j → trans (sym (merged-pool H op _ (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′)) j
      ; ling-rested = λ {C} → pin-alike {Γ = Δ} {A = C} {x = At.leftover H {B = C} w₀} refl
      ; ling-below  = λ lg → Linger.lg-flat H (pool lg) (lingers-sub H lg (in-outer here) refl) (lingersL-of H lg) }
      where
        pool : Lingers H w₀ → ∀ {c} → At.part H v ≡ just c → Tied pl′ (At.pooled H fl u ls)
        pool lg x = subst (λ p → Tied p (At.pooled H fl u ls)) (sym e)
          (idle-tied {p = pl} {x = At.pooled H fl u ls} (Lingers.pools lg here refl
            (proj₂ (just-of (trans (sym (merged-pool H op _ (At.part H u) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl pl′)) (cong is-just x))))))

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
             → Sane [] g → Placed g [] → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part H′ (plant ρ v) ≡ just g″ × Sane [] g″ × Placed g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
  ghost-lift H H′ ρ v fs off mine {g = g} L pv gv sn pd sg
    with skip-lift H′ (planted ρ v) (lifts-planted ρ v (Wrote.wr-lifts H H′ ρ off mine fs L)) pv gv
  ... | k′ , g′ , g″ , refl , pg , gp =
    g″ , pg , gapped-sane gp (subst (SaneS []) sg (step-sane g sn)) , gapped-placed gp pd′
       , k′ , U.stateᴺ g′ [] , (λ n → subst (λ s → Agree n (residual g) (afterᴱ [] s)) sg (_≃_.agreeing (step-skips g sn pd) n))
       , gapped-past gp (stepped-deep sn pd sg)
    where pd′ = proj₂ (subst (Placedˢ []) sg (placed-after g sn pd))

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
      ; ling-rested = λ {C} → pin-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} u so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
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

      lingering : (∀ {c} → At.part H w₀ ≡ just c → Tied pl (At.pooled H fl u ls) → Tied pl′ (At.pooled H′ fl u ls)) → Lingering H H′ w₀ v
      lingering tie = record
        { ling-revive = revive
        ; ling-rested = λ {C} → pin-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} u so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
        ; ling-below  = λ lg → Linger.lg-flat H′ (pool lg)
                                 (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                                 (lingersL-alike H H′ ls-al (lingersL-of H lg)) }
        where
          pool : Lingers H w₀ → ∀ {c} → At.part H′ v ≡ just c → Tied pl′ (At.pooled H′ fl u ls)
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
    pool-ghost : AllPairs _≢_ (names T) → ∀ (o₀ : U.Node Δ A) {g q S} → Sane [] g → Placed g [] → At.part H u ≡ nothing
               → (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl))) ≡ false
               → Lifts H ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl) S
               → U.step g ≡ S
               → Σ (U.Node [] R) λ g″ → At.part H′ (Restaged.T′ H′ ρ (U.unionᶜ pl (U.restᶜ o₀))) ≡ just g″ × Sane [] g″ × Placed g″ []
                 × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
    pool-ghost fs o₀ {q = q} sn pd gn nl L sg =
      ghost-lift H H′ ρ (flatMapˢ op f fl oc k r pl′ u ls) fs (off-store H (FlatKit.Flat.outerDone fl)) mine {κ = []}
        (subst (λ s → Lifts H ρ s _) (outer-end op G o₀ q (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl nl) L)
        (trans (sd-part-at pl′ (fresh-path ρ fs))
               (trans (cong (λ x → At.merged H op G x (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′) gn)
                      (merged-open H op G (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′ nl)))
        alike sn pd sg
      where
        G   = λ a j → U.subscribe (f a) j
        pl′ = U.unionᶜ pl (U.restᶜ o₀)

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
                 (sg : U.step g ≡ S) where
    H   = Conf.heap (Mach.conf m₁)
    q   = Conf.pos (Mach.conf m₁)
    pl′ = U.unionᶜ pl (U.restᶜ o₀)
    fs  = Books.fresh (Calling.books cl)

    module P = Settles.Repool H ρ (fresh-path ρ fs) pl′

    postulate
      close-tied  : ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just c
                  → Tied pl (At.pooled H fl u ls) → Tied pl′ (At.pooled (Settles.H′ H ρ) fl u ls)
      close-told  : ∀ {A′} (i : A′ ∈ᴸ Δ) {b₀} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just b₀ → untold i pl′ ⊆ᴾ untold i b₀
      close-heads : ∀ {c} → At.part H (flatMapˢ op f fl oc k r pl u ls) ≡ just c → Heads q pl → Heads q pl′

    close-heading : Heading H (Settles.H′ H ρ) q (flatMapˢ op f fl oc k r pl u ls) (flatMapˢ op f fl oc k r pl′ u ls)
    close-heading = P.heading (λ {A′} i {b₀} → close-told {A′} i {b₀}) close-heads

    close-lingers : Lingers (Settles.H′ H ρ) (Restaged.T′ (Settles.H′ H ρ) ρ pl′)
    close-lingers = Settles.Fr.shift-lingers H ρ fs (Restaged.v (Settles.H′ H ρ) ρ pl′) (ended-past cl) (P.lingering close-tied) (Calling.lingers cl)

  -- A flatMap's outer ended: its guard read open, its done flag written,
  -- its count and queue read.  Nothing left: the flatMap's end one
  -- operator up.  Else the lanes run on, the pool taking what the outer
  -- left running.
  close-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {ks}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (closes ks) → Called st m₁ (ρ ⊕ in-outer here)
  close-outer st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} ρ {ks}
    cl@record { sane = sn ; placed = pd ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg , hl ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-outer here) L
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
      { sane = sn ; placed = pd ; ctl = refl
      ; code = ≗-trans e₅ (bind≗ (open-code {m = Observer.complete o} (trans (cong (λ x → x ∧ b) (Settles.done-read hp ρ)) eq)) λ _ → ≗-refl ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; lifted = trans (Settles.sd-part hp ρ (fresh-path ρ fs)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl)) , S
               , Settles.Fr.wr-lifts hp ρ fs (subst₂ (λ ls′ qs′ → Lifts hp ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) ls′ qs′ po) S)
                                               (proj₁ nl) (proj₂ nl) Lρ) , sg
               , healed-off hp (Settles.H′ hp ρ) ρ fs (Settles.sd-off hp ρ) (Settles.sd-part hp ρ (fresh-path ρ fs)) (healed-split ρ (in-outer here) hl)
      ; owned = Settles.Fr.wr-owned hp ρ fs (Settles.sd-gone hp ρ (fresh-path ρ fs)) ow ; kernels = Settles.Fr.kernels hp ρ fs kn ; meaning = Settles.Fr.meaning hp ρ fs mn
      ; queue = Settles.Fr.queue hp ρ fs qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Settles.sd-behind hp ρ fs bh
      ; lingers = Settles.Fr.lingers hp ρ fs (ended-past cl) (Settles.sd-lingering hp ρ (fresh-path ρ fs) (trans (Settles.sd-part hp ρ (fresh-path ρ fs)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl)))) lgr
      ; flags = Settles.sd-flags hp ρ fs gn dn ; kept = inj₁ refl }))
    where
      o    = Here.obs (walk ρ top)
      b    = (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl))
      path = ⇝-trans p₁ (⇝-trans p₂ (⇝-trans p₃ (⇝-trans p₄ p₅)))
      e₅   = ≗-trans (f₅ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))
               (bind≗ (wk-same (settledᵒ o (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)) (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl))
                                         (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ)
      nl   = nulls (At.partLanes hp ls) (At.val hp (FlatKit.Flat.queue fl)) (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq)
  ...           | false
    with Settles.pool-ghost hp ρ fs o₀ sn pd gn (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq) Lρ sg
  ...             | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; tree = Restaged.T′ (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))
        ; ctlAs = runAs (Restaged.pool-calls (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) ks) ec (Restaged.pool-stack (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk)
        ; meets = pg
        ; owned′ = owned-to (Restaged.pool-owned (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk ks ec (Settles.Fr.wr-owned hp ρ fs (Settles.sd-gone hp ρ (fresh-path ρ fs)) ow))
        ; kernels = Restaged.pool-kernels (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.kernels hp ρ fs kn)
        ; meaning = Restaged.pool-meaning (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.meaning hp ρ fs mn)
        ; queue = Restaged.pool-queue (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.Fr.queue hp ρ fs qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path
        ; behind′ = Eaching.each-to _ _ (Settles.Fr.shift-behind hp ρ fs (Restaged.v (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))) (tells-past cl) (ended-past cl) (Closing.close-heading ρ o₀ cl Lρ sg) bh)
        ; lingers′ = Lingering.lingers-to _ (Closing.close-lingers ρ o₀ cl Lρ sg)
        ; flags = Settles.sd-landed hp ρ fs (U.unionᶜ po (U.restᶜ o₀)) gn (trans (sym (Settles.settle-eq hp ρ (fresh-path ρ fs) kn)) eq) Lρ dn })
      , passed ag pp)
    where
      o    = Here.obs (walk ρ top)
      b    = (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl))
      v    = flatMapˢ op f fl oc k r (U.unionᶜ po (U.restᶜ o₀)) u ls
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
    open Weakened τ using (grow-part; grow-partᴸ)

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

    -- The flatMap's skip as the grown world reads it.
    skipped : U.Step Δ B
    skipped = U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part base (wkTree grow t))
                (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes base (wkLanes grow ls)) (At.val base (wkR grow (FlatKit.Flat.queue fl))) pl′)

    skipped-grow : skipped ≡ U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part H t)
                     (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)
    skipped-grow = trans (cong₂ (λ o L → sk o L (At.val base (wkR grow (FlatKit.Flat.queue fl)))) (Wk.grow-part grows t) (Wk.grow-partᴸ grows ls))
                         (cong (sk (At.part H t) (At.partLanes H ls)) (Grows.cells grows (FlatKit.Flat.queue fl)))
      where sk = λ o L Q → U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) o (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ L) Q pl′)

    postulate
      -- The ghost past the flatMap's skip, the lift read in the grown
      -- world: the splice alone.  `ghost-lift` gives it once the names
      -- are fresh, which the leaf does not carry.
      bg-ghosted : ∀ {g S} → Sane [] g → Placed g [] → Lifts base (wkPath grow ρ) skipped S → U.step g ≡ S
                 → Σ (U.Node [] R) λ g″ → At.part heap′ T′ ≡ just g″ × Sane [] g″ × Placed g″ []
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
    bg-ghost : ∀ {g S} → Sane [] g → Placed g []
             → Lifts H ρ (U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part H t)
                           (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)) S
             → U.step g ≡ S
             → Σ (U.Node [] R) λ g″ → At.part heap′ T′ ≡ just g″ × Sane [] g″ × Placed g″ []
               × Σ Pos λ k′ → Σ (Events∞ R) λ r′ → (∀ n → Agree n (residual g) (skip k′ r′)) × Past (Events∞.force r′) (residual g″)
    bg-ghost {S = S} sn pd L sg = bg-ghosted sn pd (subst (λ x → Lifts base (wkPath grow ρ) x S) (sym skipped-grow) (Lifted.lifts-grow grows L)) sg

    bg-owned : (sk : StackAs T q ϑ K bs) → Owned H T (runAs [] (≗-refl _) sk) → Owned heap′ T′ (ca′ sk)
    bg-owned sk ow = bg-owns sk (Wk.grow-run grows sk ow)

    bg-behind : Each H (Heads q) T → Each heap′ (Heads (q ++ [ ix 1 ])) T′
    bg-behind bh = bg-heads (Wk.grow-each grows bh)

    bg-lingers : Lingers H (Restaged.T′ H ρ pl′) → Lingers heap′ T′
    bg-lingers lg = bg-lingered (Wk.grow-lingers grows lg)

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
    bg-meaning fs mn = Sp.sp-meaning fs (bg-fed fs) (Wk.grow-meaning grows mn)

    -- The tree grown, the count and list written, the lane planted: the
    -- run one level down, past the start's own position.
    bg-queue : Queue H q clk ts T → Queue heap′ (q ++ [ ix 1 ]) clk ts′ T′
    bg-queue qu = subst (λ ts″ → Queue heap′ (q ++ [ ix 1 ]) clk ts″ T′) (trans (pure-map (wkTimer grow) ts) (sym timers′))
                    (record { timed = Queue.timed qu′ ; joined = Queue.joined qu′ ; ordered = Queue.ordered qu′
                            ; ahead = ahead-under q 1 (λ e → ⊥-elim (deep e)) (Queue.ahead qu′) })
      where qu′ = plant-queue heap′ (wkPath grow ρ) v′ refl refl (λ _ → refl) (queue-keeps (wrote-keeps {τ = grow} {fl = fl} moved) (Wk.grow-queue grows qu))

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
        i₁ = Wk.grow-flags grows dI
        c₁ : DoneBy base (plant ρw P₀) []
        c₁ = subst (λ x → DoneBy base x []) (wk-plant grow ρ (pendingˢ (f y) (q ++ [ ix 1 ]))) (Wk.grow-flags grows dF)
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
    b@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = S , L , sg ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
             ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr
             ; flags = dF ; inner = dI }
    with begin-path b
  ... | sr with Begun.bg-ghost sr pl′ sn pd L sg
  ...   | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    g″ , _ , Started.runs sr
    , carried (record
      { sane = sn″ ; placed = pd″ ; tree = Begun.T′ sr pl′ ; ctlAs = Begun.ca′ sr pl′ sk ; meets = pg
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
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr ; kept = kp } rm p c
    with lifts-split ρ (in-outer here) L
  ... | _ , lifts-outer {o₀ = o₀} _ _ lifts-here , Lρ = lane-begin st (record
      { sane = sn ; placed = pd ; ctl = refl ; code = c
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
