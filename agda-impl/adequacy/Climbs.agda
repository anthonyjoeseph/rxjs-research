{-# OPTIONS --guardedness #-}

-- THE CLIMB: a value carried from its emitter up a path, each
-- operator's callback one rise; and the close, its teardown.
module adequacy.Climbs where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length; drop) renaming (map to mapList)
open import Data.List.Properties using (++-assoc; ++-conicalˡ; ++-conicalʳ; ++-identityʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ; ++⁻)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′) renaming (map₂ to sum-map₂)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m<n⇒m<1+n; +-monoʳ-<; +-monoˡ-<)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ; tabulate to tabulateᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.List.Relation.Binary.Permutation.Propositional using (_↭_) renaming (refl to ↭-refl′)
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; tail)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-nothing; is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; pred; _<_; _≤_; z≤n; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; skip; Pos; Timeline; Agree; agree-refl; at; last; ix; tick; _<ᵖ_; <ᵖ-tick; <ᵖ-trans; <ᵖ-below)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (module Sorting; _≤ᵖ_; ≤ᵖ-child)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane; SaneS; sane-out; step-sane)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (placed-after; Placedˢ; step-skips; afterᴱ; _≃_)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; note; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_; _∨_)
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
open import adequacy.Retag using (Retag; module Retagging; at-here)
open import adequacy.Replant using (module Replanting)
open import adequacy.Restages using (module Staging)
open import adequacy.Weaken using (module Weakening)
open import adequacy.Every using (module Everywhere)
open import adequacy.Alike using (module Aliking)
open import adequacy.Shift using (module Shifting)

open Events∞

module Ascending (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; _∋_; Handle; Sink; Quiet; wk∋; slot; cell) renaming (same to same⊑)
  open Sorting R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Strong; Carried; Books; Feed; carried; closing; Sub; flatNames; cutNames; quietName; laneNames; pendingˢ; Name; names; subjects; joiners; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; here; module At; Queue; Kernels; Meaning; fired; Owned; Path; Spot; spot; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; Meets; Each; Heads; Lingers; DoneBy; outers; outersL; outers-⊕; Tied; unsub; Owes; Settled; seen; seenL; pinned-trans; ∧-split; false≢; module Canon; owned-to; module Eaching; module Lingering) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs; StackAs; Ticked; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots; SrcOf; src-of) renaming (Placed to Placedᴬ)
  open Pure R using (Timer; cascade; wkTimer)
  open Moving R using (pairs-r; pairs-split; plant-self; takes; takesᴸ; stage; takes-plant; plant; plantᴸ; planted; plantedᴸ; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant; joiners-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open Everywhere.Settling R using (settled-plant; settled-retag)
  open Everywhere.Gating R using (gated-alike; gated-path; gated-plant; gated-retag)
  open Tearing R using (cuts; attached-alike; cuts-switches; fresh-path; takeSite; bodySite; look-store; look-either; Alike; part-alike; partLanes-alike; part-flat; apart-r; each-same; seen-alike; seenL-alike; names-path; lanes-path) renaming (Off to Offʰ)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Forking R using (walk-planted)
  open Aliking R using (walk-grow; compile-cong; laneAt-wk; ObsRel)
  open Taking R using (tick-ix0)
  open Naming R using (pre; fresh-plant; fresh-new; wk-pairs; wk-img; to-img)
  open Ghosting R using (each-sub; each-lanes; module Far; module Calling; residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; done-up; lifts-seen; Rises; rises; Called; landed; rose; passed; Past; Aloft; aloft; hop-sorted; each-back; hopped-pre)
  open Gapping R using (Gapped; alike; gap-map; gap-scan; gap-take; gap-flat; gap-just; gap-connect; gap-live; gap-shut; gap-ended; gapM-refl; gapL-refl; gapL-mid; feed-gapped; gapped-past; gapped-sane; gapped-placed; stepped-deep)
  open Lowering R using (Keeps; queue-keeps; store-keeps; keeps-trans)
  open Lifting R using (sub-onward; emit-shut; emit-void; run-meets; run-at; emit-run; spread-past; behind-fire; fire-lingers; kont-onward; feed-onward; src-onward; burst-poll; burst-play; cut-onward; heads-lift)
  open Locality R using (stored-at; stored-hit; live-apart; flatReads; cut-in; module Heaps)
  open Growing R using (wkTree; wkLanes; wkPath; wkPathᴸ)
  open Retagging R using (module Body; fed-owed; envP; joiners-path; retag; unsub-retag; begun-retag)
  open Everywhere.Spending R using (spent-retag)
  open Everywhere.Holding R using (holds-alike; holds-path; holds-plant; holds-retag)
  open Shifting R using (module Flag; flags-alike; flagsL-alike; outers-planted; outers-apart; outersL-in; let-go; flag-in; flagged-moved; part-at; cons-untold; ≡-⊆; ++-mono; _⊆ᴾ_; eachL-of; each-alike; eachL-alike; EachL; LingersL; lingers-alike; lingersL-alike; leftover-alike; leftoverL-alike; leftover-from; pooled-from; pin-alike; conn-left; lingers-sub; lingersL-of; module Linger; module Build)
  open Framing R using (merged-eq; heads-flat; Untold; untold; untoldᴹ; untoldᴸ; just-of; scan-part; scan-defined; none-of; tells-past; ended-past; scan-kernels; scan-meaning; scan-lifts; scan-behind; module Wrote; plant-queue; off-store; off-++; lane1-alike)
    renaming (Ended to Ends)
  open Staging R using (not-src; wrap-lane)
  open Weakening R using (Grows; pure-map) renaming (module Grown to Weakened)
  open Everywhere R using (module Growths)
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
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
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
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
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
  ... | gn , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-map here) top) (Calling.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) gn , S , Lρ , sg) (done-up ρ (in-map here) refl (Calling.flags cl))

  -- A signal through a defer, as it is.
  call-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (deferˢ k u)) {sg : Signal T A} → Calling g ℓ m₁ (ρ ⊕ in-defer here) sg → Calling g ℓ m₁ ρ sg
  call-defer ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (c′ , pv , S , Lρ , sg) (done-up ρ (in-defer here) refl (Calling.flags cl))
  call-defer ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (gn , S , Lρ , sg) (done-up ρ (in-defer here) refl (Calling.flags cl))

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
    record { sane = sn ; placed = pl ; ctl = cx ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-body here) L
  ... | _ , Lb , Lρ = rose {sg′ = closes (bodyC ρ ∷ ks)} now (one-lower ρ one-body) (record
      { sane = sn ; placed = pl ; ctl = cx
      ; code = ≗-trans (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-body here) top) cd) (seq-assoc (Observer.complete (Here.obs (walk ρ top))) (Kit.cut c) ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; lifted = gone-connect (Conf.heap (Mach.conf m₁)) {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = t} {u = u} gn
               , S , subst (λ s → Lifts (Conf.heap (Mach.conf m₁)) ρ s S) (body-end Lb) Lρ , sg
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
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rises {sg′ = sends y} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
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

  -- A map's part held exactly where what it maps is.
  map-just : ∀ {h} (G : Heapᴹ h) {X Y : Set₁} (g : X → Y) m → is-just (At.mapᴹ G g m) ≡ is-just m
  map-just G g nothing  = refl
  map-just G g (just _) = refl

  -- A live take ending shows its end owed.
  ending-part : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} {q c′} → At.val H (Kit.live c) ≡ true
              → At.part H (takeWhileˢ i p c k (Strongly.ending q c′) u) ≡ just (U.endingᶜ (q ++ [ last ]) c′)
  ending-part H lv rewrite lv = refl

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
      -- DEAD ROUTE: a body over `ghost-lift`.  The take's end lifts to the root as an end wherever no flatMap or connect above turns it into a skip, so there is no skip to lift past; and where it crosses a connect's source, `U.sourceˢ` reads the source node `lifts-source` leaves free.
      end-ghost : ∀ {g S} → Sane [] g → Placed g [] → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
              → Lifts H ρ (U.endˢ (q ++ [ last ])) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × (∀ n → Agree n (residual g) (residual g″))

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
      ; ling-rested = pin-alike {x = At.leftover H u} refl
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
    cl@record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; flags = dn }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f
    with Ended.end-ghost hp ρ q c′ sn pl lv pv (subst (λ s → Lifts hp ρ s S) (cong (U.taking false p q y c′) py) Lρ) sg
  ...   | g″ , pg , sn″ , pl″ , ag =
    g″ , _ , then refl now
    , record
        { sane = sn″ ; placed = pl″ ; tree = Ended.T′ hp ρ q c′
        ; ctlAs = runAs (take1C (planted ρ v) ∷ []) e (Ended.end-stack hp ρ q c′ sk)
        ; meets = pg
        ; owned′ = owned-to (Ended.end-owned hp ρ q c′ sk e ow)
        ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.end-queue hp ρ q c′ qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind′ = Eaching.each-to _ _ (Ended.end-behind hp ρ q c′ fs (tells-past cl) (ended-past cl) lv pv bh) ; lingers′ = Lingering.lingers-to _ (Ended.end-lingers hp ρ q c′ fs (ended-past cl) lv pv lgr)
        ; flags = let-go hp (planted ρ v) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs) (lifts-seen (lifts-planted ρ v Lρ))
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
    cl@record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f
    with out-step {hp = hp} {q = q} {clk} {ts} {bs} {td} {lg} {en} {mk} {ϑ = ϑ} {K = K}
                  (≗-trans (f same⊑ (At.val hp (Kit.live c))) (≗-trans (wk-same _) (out-code lv py)))
  ...   | M′ , N′ , eM , eN , path =
    rises {σ′ = planted ρ v} {sg′ = sends y} (then refl path) (subst (_< height (ρ ⊕ in-take here)) (sym (height-planted ρ v)) (one-lower ρ one-take)) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = subst (λ W → M′ ≗ Observer.next (Here.obs W) y) (sym (walk-planted ρ v top)) eM
      ; stack = st
      ; lifted = U.endingᶜ (q ++ [ last ]) c′ , ending-part hp {i = true} {p = p} {c = c} {k = k} {u = u} lv , S
               , lifts-planted ρ v (subst (λ s → Lifts hp ρ s S) (cong (U.taking true p q y c′) py) Lρ) , sg
      ; owned = Ended.out-owned hp ρ q c′ sk e ow
      ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.out-queue hp ρ q c′ qu
      ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                       ; clocked = trans (proj₁ ck) (sym (tick-ix0 q)) , proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck)
                       ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl path) ; behind = Ended.out-behind hp ρ q c′ fs (tells-past cl) (ended-past cl) lv pv bh ; lingers = Ended.end-lingers hp ρ q c′ fs (ended-past cl) lv pv lgr
      ; flags = Ended.end-flags hp ρ q c′ fs lv pv (done-up ρ (in-take here) refl dn)
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
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rose {sg′ = closes ks} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (bind≗ (≗-trans (wk-same _) (open-code lv)) λ _ → wk-same _)
      ; stack = sk
      ; lifted = gone-take hp {i = i} {p = p} {c = c} {k = k} {u = u} lv gn , S , Lρ , sg
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

  -- A WRITE AT A SCAN'S ACCUMULATOR, ITS FRAME: no part beneath the scan
  -- reads the accumulator, and no tie of the scan's does.
  module Scanned {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B} {f : B → A → B} {r} {u : Sub h Δ A} (ρ : Path T (scanˢ f r u))
                 (fs : AllPairs _≢_ (names T)) (z : B) where
    H′ = store H r (lift z)

    module Sh = Shift H H′ ρ (off-store H r) (here refl ∷ []) fs

    -- The scan's source, apart from its accumulator.
    scan-alike : Alike H H′ (names u)
    scan-alike j m with fresh-path ρ fs
    ... | a ∷ _ = look-store H r j (lookupᴬ a m)

    -- The accumulator read by the scan's part alone: held as it was, its
    -- source's leftover and ties alike.
    scan-revive : is-just (At.part H′ (scanˢ f r u)) ≡ true → is-just (At.part H (scanˢ f r u)) ≡ true
    scan-revive j = trans (map-just H (U.scanᶜ f (At.val H r)) (At.part H u))
                          (trans (cong is-just (sym (part-alike H H′ u scan-alike)))
                                 (trans (sym (map-just H′ (U.scanᶜ f (At.val H′ r)) (At.part H′ u))) j))

    scan-lingering : Lingering H H′ (scanˢ f r u) (scanˢ f r u)
    scan-lingering = record
      { ling-revive = scan-revive
      ; ling-rested = λ {C} → pin-alike (leftover-alike H H′ {B = C} u scan-alike)
      ; ling-below  = λ lg → Linger.lg-scan H′ (lingers-alike H H′ scan-alike (lingers-sub H lg (in-scan here) refl)) }

    scan-owned : ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
    scan-owned = Sh.wr-owned record { gone-part = λ ψ e → none-of (trans (scan-defined H ρ fs z (ρ ⊕ ψ)) (cong is-just e)) ; gone-live = scan-live ; gone-held = store-held H r }
      where
        -- No take beneath the scan switched by its accumulator.
        scan-live : Lives H H′ (scanˢ f r u)
        scan-live with fresh-path ρ fs
        ... | a ∷ _ = lives-off {H = H} {H′ = H′} (off-store H r) nl
          where
            nl : ∀ {Δ′ A′ i p c k tk} {s : Sub h Δ′ A′} → Path (scanˢ f r u) (takeWhileˢ i p c k tk s) → All (_≢_ (_ , Kit.live c)) ((_ , r) ∷ [])
            nl (in-scan ψ) = (λ eq → lookupᴬ a (names-path ψ (here refl)) (sym eq)) ∷ []

    scan-queue : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
    scan-queue = queue-keeps (store-keeps H r _ (λ ()) (λ ()) (λ ()) (λ ()))

    -- The accumulator no flag: every flag below the scan read alike.
    scan-flags : DoneBy H T (outers ρ) → DoneBy H′ T (outers ρ)
    scan-flags d = subst (λ t → DoneBy H′ t (outers ρ)) (plant-self ρ)
      (Sh.shift-flags (scanˢ f r u) (λ ()) scan-revive
        (λ d₀ → Flag.db-scan H′ (flags-alike H H′ scan-alike (Flag.db-sub H (subst (DoneBy H (scanˢ f r u)) (++-identityʳ (outers ρ)) d₀) (in-scan here) refl)))
        (subst (DoneBy H T) (sym (++-identityʳ (outers ρ))) d))

    scan-lingers : Ends H T → Lingers H T → Lingers H′ T
    scan-lingers en lg = subst (λ t → Lingers H′ t) (plant-self ρ) (Sh.shift-lingers (scanˢ f r u) en scan-lingering lg)

  -- A value through a scan: its cell read and written, the accumulated
  -- value one operator up, the tree's load as it was.
  scan-pass : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
            → Calling g ℓ m₁ (ρ ⊕ in-scan here) (sends y) → Rises g (load m₁ T) m₁ (ρ ⊕ in-scan here)
  scan-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {f = f} {r = r} {u = u} ρ {y}
    cl@record { sane = sn ; placed = pl ; ϑ = ϑ ; K = K ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr ; flags = dn ; kept = kp }
    with lifts-split ρ (in-scan here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-scan here) top) cd
  ... | _ , lifts-scan lifts-here , Lρ | readRef≗ refl k =
    rises {sg′ = sends z} (then refl (proj₂ (proj₂ wr))) (one-lower ρ one-scan) (record
      { sane = sn ; placed = pl ; ctl = refl ; code = proj₁ (proj₂ wr) ; stack = sk
      ; lifted = U.scanᶜ f z c′ , scan-part hp {f = f} {r = r} {u = u} (fresh-path ρ fs) z pv , S , scan-lifts hp ρ fs z Lρ , sg
      ; owned = Scanned.scan-owned hp ρ fs z ow ; kernels = scan-kernels hp ρ fs z kn ; meaning = scan-meaning hp ρ fs z mn ; queue = Scanned.scan-queue hp ρ fs z qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl (proj₂ (proj₂ wr))) ; behind = scan-behind ρ cl ; lingers = Scanned.scan-lingers hp ρ fs z (ended-past cl) lgr
      ; flags = Scanned.scan-flags hp ρ fs z (done-up ρ (in-scan here) refl dn) ; kept = inj₁ refl })
    where z = f (At.val hp r) y
          wr = writes {σ = ϑ} {K = K} {clk = clk} {ts} {bs} {td} {lg} {en} {mk} (≗-trans (k same⊑ (At.val hp r)) (wk-same _))

  -- A signal through a scan: a value accumulated; an end as it is, the
  -- scan's cell unread.
  call-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {sg : Signal T A}
            → Calling g (loadOf st) m₁ (ρ ⊕ in-scan here) sg → Called st m₁ (ρ ⊕ in-scan here)
  call-scan st ρ {sends y} cl = rise (Calling.kept cl) (scan-pass ρ cl)
  call-scan st {m₁ = m₁} {f = f} {r} ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg with lifts-split ρ (in-scan here) L
  ...   | _ , lifts-scan lifts-here , Lρ = rose now (one-lower ρ one-scan) (recall cl {sg′ = closes ks} refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-scan here) top) (Calling.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.scanᶜ f (At.val (Conf.heap (Mach.conf m₁)) r))) gn , S , Lρ , sg) (done-up ρ (in-scan here) refl (Calling.flags cl)))

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

  -- A flatMap whose pool heads no sooner heads no sooner with it.
  postulate
    heads-repool : ∀ {Δ A B q} op (g : A → Pos → U.Node Δ B) o L Q (pl pl′ : U.Node Δ B)
                 → Heads q (U.flatMapᶜ op g o L Q pl) → Heads q pl′ → Heads q (U.flatMapᶜ op g o L Q pl′)

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

    postulate
      active-lanes : Kernels H T → (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ≡ null (At.partLanes H ls)

    -- The done flag the flatMap's own cell: its node's clauses read
    -- alike, the rest of the tree by the frame.
    w₀ = flatMapˢ op f fl oc k r pl u ls

    ns : List (Name h)
    ns = (_ , FlatKit.Flat.outerDone fl) ∷ []

    mine : All (_∈ᴸ names w₀) ns
    mine = there (here refl) ∷ []

    module Wr (fs : AllPairs _≢_ (names T)) = Wrote H H′ ρ (off-store H (FlatKit.Flat.outerDone fl)) mine fs
    module Sh (fs : AllPairs _≢_ (names T)) = Shift H H′ ρ (off-store H (FlatKit.Flat.outerDone fl)) mine fs

    -- The done flag no read of the node's own clauses.
    sd-alike : AllPairs _≢_ (names w₀) → Alike H H′ (flatReads fl oc k r u ls)
    sd-alike (a₀ ∷ a₁ ∷ _) j (here e)  = look-store H (FlatKit.Flat.outerDone fl) j (λ eq → lookupᴬ a₀ (here refl) (sym (trans eq e)))
    sd-alike (a₀ ∷ a₁ ∷ _) j (there m) = look-store H (FlatKit.Flat.outerDone fl) j (lookupᴬ a₁ (there m))

    sd-part-at : ∀ pl′ → AllPairs _≢_ (names w₀) → At.part H′ (flatMapˢ op f fl oc k r pl′ u ls) ≡ At.part H (flatMapˢ op f fl oc k r pl′ u ls)
    sd-part-at pl′ fr@(_ ∷ a₁ ∷ _) =
      part-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl′} u ls (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.queue fl) (lookupᴬ a₁ (here refl)))
                (Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)) (Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr))

    sd-part : AllPairs _≢_ (names w₀) → At.part H′ w₀ ≡ At.part H w₀
    sd-part = sd-part-at pl

    sd-active : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.active fl) ≡ At.val H (FlatKit.Flat.active fl)
    sd-active (a₀ ∷ _) = cong lower (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.active fl) (λ eq → lookupᴬ a₀ (here refl) (sym eq)))

    sd-fifo : AllPairs _≢_ (names w₀) → At.val H′ (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
    sd-fifo (_ ∷ a₁ ∷ _) = cong lower (look-store H (FlatKit.Flat.outerDone fl) (FlatKit.Flat.queue fl) (lookupᴬ a₁ (here refl)))

    sd-holds : AllPairs _≢_ (names w₀) → ∀ {E o} → At.Holds H w₀ E o → At.Holds H′ w₀ E o
    sd-holds fr {E} {o} = Heaps.holds-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike fr) {E} {o}

    sd-gated : AllPairs _≢_ (names w₀) → At.Gated H w₀ → At.Gated H′ w₀
    sd-gated fr = Heaps.gated-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike fr)

    sd-spent : AllPairs _≢_ (names w₀) → At.Spent H w₀ → At.Spent H′ w₀
    sd-spent fr = Heaps.spent-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike fr)

    sd-fed : AllPairs _≢_ (names w₀) → ∀ ν → At.Fed H w₀ ν → At.Fed H′ w₀ ν
    sd-fed fr = Heaps.fed-flat H H′ {op = op} {f} {fl} {oc} {k} {r} {pl} u ls (sd-alike fr)

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

    sd-owned : AllPairs _≢_ (names T) → ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
    sd-owned fs = Sh.wr-owned fs record { gone-part = λ ψ e → trans (sd-same (fresh-path ρ fs) ψ) e ; gone-live = sd-live (fresh-path ρ fs) ; gone-held = store-held H (FlatKit.Flat.outerDone fl) }

    sd-queue : AllPairs _≢_ (names T) → ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
    sd-queue _ = queue-keeps (store-keeps H (FlatKit.Flat.outerDone fl) _ (λ ()) (λ ()) (λ ()) (λ ()))

    -- Nothing left: the flatMap gone, no pool of it held; its children's
    -- leftovers and ties alike.
    sd-lingering : AllPairs _≢_ (names w₀) → At.part H′ w₀ ≡ nothing → Lingering H H′ w₀ w₀
    sd-lingering fr gn = record
      { ling-revive = λ j → ⊥-elim (true≢false (trans (sym j) (cong is-just gn)))
      ; ling-rested = λ {C} → pin-alike (cong₂ U.unionᶜ (leftover-alike H H′ {B = C} u so-al) (leftoverL-alike H H′ {B = C} ls ls-al))
      ; ling-below  = λ lg → Linger.lg-flat H′ (λ e → ⊥-elim (true≢false (trans (sym (cong is-just e)) (cong is-just gn))))
                                (lingers-alike H H′ so-al (lingers-sub H lg (in-outer here) refl))
                                (lingersL-alike H H′ ls-al (lingersL-of H lg)) }
      where
        so-al = Heaps.flat-so H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)
        ls-al = Heaps.flat-ls H H′ {fl = fl} {oc} {k} {r} {u} {ls} (sd-alike fr)

    sd-lingers : AllPairs _≢_ (names T) → At.part H′ w₀ ≡ nothing → Ends H T → Lingers H T → Lingers H′ T
    sd-lingers fs gn en lg = subst (λ t → Lingers H′ t) (plant-self ρ) (Sh.shift-lingers fs w₀ en (sd-lingering (fresh-path ρ fs) gn) lg)

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

    sd-lifts : AllPairs _≢_ (names T) → ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
    sd-lifts fs = Wr.wr-lifts fs

    sd-kernels : AllPairs _≢_ (names T) → Kernels H T → Kernels H′ T
    sd-kernels fs = Wr.wr-kernels fs (λ {E} {o} → sd-holds (fresh-path ρ fs) {E} {o}) (λ _ → sd-gated (fresh-path ρ fs)) (sd-spent (fresh-path ρ fs))

    sd-meaning : AllPairs _≢_ (names T) → Meaning H T → Meaning H′ T
    sd-meaning fs = Wr.wr-meaning fs (sd-fed (fresh-path ρ fs))

    sd-behind : AllPairs _≢_ (names T) → ∀ {q} → Each H (Heads q) T → Each H′ (Heads q) T
    sd-behind fs = Wr.wr-behind fs (sd-part (fresh-path ρ fs)) (sd-heads (fresh-path ρ fs))

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
      Sh.shift-flags fs (flatMapˢ op f fl oc k r pl′ u ls) (lookupᴬ mine) rv
        (sd-flags₀ pl′ (fresh-path ρ fs) (λ m → outers-apart ρ fs m (there (here refl))) gn) (subst (DoneBy H T) (outers-⊕ ρ (in-outer here)) d)

    sd-flags : AllPairs _≢_ (names T) → At.part H u ≡ nothing → DoneBy H T (outers (ρ ⊕ in-outer here)) → DoneBy H′ T (outers ρ)
    sd-flags fs gn d =
      subst (λ t → DoneBy H′ t (outers ρ)) (plant-self ρ) (sd-shift fs pl (λ j → trans (cong is-just (sym (sd-part (fresh-path ρ fs)))) j) gn d)

    -- Lanes or a queue left: the flatMap held, so every flag above it let go.
    sd-landed : AllPairs _≢_ (names T) → ∀ pl′ → At.part H u ≡ nothing → (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl))) ≡ false
              → ∀ {s S} → Lifts H ρ s S → DoneBy H T (outers (ρ ⊕ in-outer here)) → DoneBy H′ (plant ρ (flatMapˢ op f fl oc k r pl′ u ls)) []
    sd-landed fs pl′ gn nl L d =
      let-go H′ (planted ρ v′) (subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v′ refl)) fs) (lifts-seen (lifts-planted ρ v′ (sd-lifts fs L))) (cong is-just open′)
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
    close-lingers = Settles.Sh.shift-lingers H ρ fs (Restaged.v (Settles.H′ H ρ) ρ pl′) (ended-past cl) (P.lingering close-tied) (Calling.lingers cl)

  -- A flatMap's outer ended: its guard read open, its done flag written,
  -- its count and queue read.  Nothing left: the flatMap's end one
  -- operator up.  Else the lanes run on, the pool taking what the outer
  -- left running.
  close-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) {ks}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-outer here) (closes ks) → Called st m₁ (ρ ⊕ in-outer here)
  close-outer st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} ρ {ks}
    cl@record { sane = sn ; placed = pd ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
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
               , Settles.sd-lifts hp ρ fs (subst₂ (λ ls′ qs′ → Lifts hp ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) ls′ qs′ po) S)
                                               (proj₁ nl) (proj₂ nl) Lρ) , sg
      ; owned = Settles.sd-owned hp ρ fs ow ; kernels = Settles.sd-kernels hp ρ fs kn ; meaning = Settles.sd-meaning hp ρ fs mn
      ; queue = Settles.sd-queue hp ρ fs qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Settles.sd-behind hp ρ fs bh
      ; lingers = Settles.sd-lingers hp ρ fs (trans (Settles.sd-part hp ρ (fresh-path ρ fs)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl))) (ended-past cl) lgr
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
        ; owned′ = owned-to (Restaged.pool-owned (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk ks ec (Settles.sd-owned hp ρ fs ow))
        ; kernels = Restaged.pool-kernels (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-kernels hp ρ fs kn)
        ; meaning = Restaged.pool-meaning (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-meaning hp ρ fs mn)
        ; queue = Restaged.pool-queue (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-queue hp ρ fs qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path
        ; behind′ = Eaching.each-to _ _ (Settles.Sh.shift-behind hp ρ fs (Restaged.v (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))) (tells-past cl) (ended-past cl) (Closing.close-heading ρ o₀ cl Lρ sg) bh)
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
             ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; lingers = lgr }
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
      ; sorted = sorted-⇝ so (Started.runs sr) ; behind′ = Eaching.each-to _ _ (Begun.bg-behind sr pl′ bh) ; lingers′ = Lingering.lingers-to _ (Begun.bg-lingers sr pl′ lgr) })
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
      ; sorted = sorted-⇝ so p ; behind = bh ; lingers = Restaged.pool-idle hp ρ (U.unionᶜ po U.idleᶜ) fs refl (ended-past cl) lgr })
    where
      G  = λ a j → U.subscribe (f a) j
      LS = At.partLanes hp ls
      QS = At.val hp (FlatKit.Flat.queue fl)

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
                                            (part-at H H′ (in-outer {t = so′} here) (fr-lane fr πL′)) (Flag.dbL-of H d πL′ (fr-seL fr πL′ sn)))

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
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = _ , S , L , sg ; owned = ow
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
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
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
      ; lingers = Settling.next-lingers ρ πL o cl Lρ sg ys }))
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

  src-≡ : ∀ {h} (G G′ : Heapᴹ h) {Δ A} (s : Maybe (U.Node Δ A)) t → At.sourced G′ s t ≡ At.sourced G s t
  src-≡ G G′ (just _) t = refl
  src-≡ G G′ nothing  t = refl

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
      ; ling-rested = λ {C} → pin-alike (conn-left {B = C} rp {n = At.sourced G (At.part G u) (At.leftover G u)} refl re-leftover)
      ; ling-below  = λ lg → Linger.lg-connect G
          (λ x pn pe → Lingers.rests lg here refl (proj₂ (just-of (re-revive (cong is-just x)))) pn pe)
          (λ jb → lingers-sub G lg (in-source here) (cong (λ z → z ∧ true) (trans (sym re-just) jb)))
          (λ js → re-lingers (lingers-sub G lg (in-body here) (cong (λ z → z ∧ true) js))) }

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

    -- The connect's part, the feed restaged: its body's part fed the
    -- source's value, but for gaps.  The subscribers the feed read hold
    -- the value as the meaning feeds it (`Meaning`, `At.Joined`); every
    -- other joiner, and every lane or deferred node reached no sooner
    -- than `q` (`Heads`), holds it as a skip no part holds.
    postulate
      fed-part : ∀ {b₀ c′} → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
               → At.part H bd ≡ just b₀ → At.part H u ≡ just c′
               → Σ (U.Node (A ∷ Δ) B) λ b₁ → At.part H v ≡ just (U.connectᶜ rp b₁ (U.live c′)) × Gapped q (U.feed (here refl) q (just y) b₀) b₁

    -- The ghost past the source's skip: the connect's part what it
    -- skipped to, but for gaps, and the heap untouched.
    fed-ghost : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → Meaning H T → Each H (Heads q) T
              → ∀ {g S c′} → Sane [] g → Placed g [] → At.part H u ≡ just c′
              → Lifts H (ρ ⊕ in-source here) (U.outˢ q y c′) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)
    fed-ghost fs jn mn bh sn pd pv L sg with lifts-split ρ (in-source here) L
    ... | _ , lifts-source pb sf lifts-here , Lρ with fed-part jn mn bh pb pv
    ...   | b₁ , pv′ , gp rewrite sf = ghost-lift H H ρ v fs (λ _ _ → refl) [] {κ = q} Lρ pv′ (gap-connect gp (gap-live alike)) sn pd sg

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
    cl@record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr } | refl
    with subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-source here) top) cd
  ... | readRef≗ refl f with Feeds.fed-ghost hp ρ y q fs (Queue.joined qu) mn bh sn pl pv L sg
  ...   | g″ , pg , sn″ , pl″ , k′ , r , ag , pp =
    landed (g″ , _ , then refl now
      , carried (record
        { sane = sn″ ; placed = pl″ ; tree = Feeds.T′ hp ρ y q
        ; ctlAs = runAs (feedC (planted ρ v) ∷ []) (≗-trans (f same⊑ ss) (seq-done _)) (Feeds.fed-stack hp ρ y q sk)
        ; meets = pg
        ; owned′ = owned-to (Feeds.fed-owned hp ρ y q sk (≗-trans (f same⊑ ss) (seq-done _)) ow)
        ; kernels = Feeds.fed-kernels hp ρ y q kn ; meaning = Feeds.fed-meaning hp ρ y q (Queue.joined qu) mn ; queue = Feeds.fed-queue hp ρ y q qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Feeds.Bd.body-names hp ρ y q))) fs
                         ; clocked = proj₁ ck , Feeds.fed-ticked hp ρ y q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind′ = Eaching.each-to _ _ (Feeds.fed-behind hp ρ y q fs (tells-past cl) (ended-past cl) bh) ; lingers′ = Lingering.lingers-to _ (Feeds.fed-lingers hp ρ y q fs (ended-past cl) lgr) })
      , passed ag pp)
    where
      ss = At.val hp (Subject.subscribers Sj)
      v  = Feeds.v hp ρ y q

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

    -- The ghost past the source's end: the connect shut, its source ended
    -- on what the source left running.
    --
    -- With `e` staged `nothing` the first conjunct fails for a root connect:
    -- `connected` reads `nothing` past a dead source, and nothing ever
    -- stages `e` as `just`.  Staging `e = just q` here revives the connect's
    -- part, which `fin-kept`, `fin-lkept` and `fin-gone` deny, and its rest
    -- then needs `Tied rt` to the leftover beyond `Tied`'s first pin.
    --
    -- DEAD ROUTE: a body over `ghost-lift`.  The end lifts to a skip whose node ends its source on `restᶜ c₀`, `c₀` the source node `lifts-source` leaves free and `Passed` ties to nothing on the heap once its part is gone; and the heap's rest is `Tied` to the leftover only at its first step.
    postulate
      fin-ghost   : ∀ {g S} → Sane [] g → Placed g [] → At.part H u ≡ nothing
              → Lifts H (ρ ⊕ in-source here) (U.endˢ q) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H′ T′ ≡ just g″ × Sane [] g″ × Placed g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)

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

    fin-holds : AllPairs _≢_ (names w₀) → ∀ {E o} → At.Holds H w₀ E o → At.Holds H′ w₀ E o
    fin-holds fr {E} {o} = Heaps.holds-conn H H′ {S = Sj} {c} {b} {kb} {k} {idle} {rp} {e} {rt} u bd (fin-rest fr) {E} {o}

    fin-gated : AllPairs _≢_ (names w₀) → At.Gated H w₀ → At.Gated H′ w₀
    fin-gated fr = Heaps.gated-conn H H′ {S = Sj} {c} {b} {kb} {k} {idle} {rp} {e} {rt} u bd (fin-rest fr)

    fin-spent : AllPairs _≢_ (names w₀) → At.Spent H w₀ → At.Spent H′ w₀
    fin-spent fr = Heaps.spent-conn H H′ {S = Sj} {c} {b} {kb} {k} {idle} {rp} {e} {rt} u bd (fin-rest fr)

    fin-fed : AllPairs _≢_ (names w₀) → ∀ ν → At.Fed H w₀ ν → At.Fed H′ w₀ ν
    fin-fed fr = Heaps.fed-conn H H′ {S = Sj} {c} {b} {kb} {k} {idle} {rp} {e} {rt} u bd (fin-rest fr)

    -- The closed flag read by no part: the node's heads and ties as they
    -- were.
    fin-au : AllPairs _≢_ (names w₀) → Alike H H′ (names u)
    fin-au (_ ∷ a₁ ∷ _) j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ˡ m))))) eq)

    fin-ab : AllPairs _≢_ (names w₀) → Alike H H′ (names bd)
    fin-ab (_ ∷ a₁ ∷ _) j m = look-store H (Subject.closed Sj) j (λ eq → lookupᴬ a₁ (++⁺ʳ (cutNames c) (there (++⁺ʳ (quietName kb) (++⁺ʳ (quietName k) (++⁺ʳ (names u) m))))) eq)

    fin-part : AllPairs _≢_ (names w₀) → At.part H′ w₀ ≡ At.part H w₀
    fin-part fr = trans (cong₂ (At.connected H′ rp e rt) (part-alike H H′ u (fin-au fr)) (part-alike H H′ bd (fin-ab fr)))
                        (conn-≡ H H′ rp e rt (At.part H u) (At.part H bd))

    fin-revive : AllPairs _≢_ (names w₀) → is-just (At.part H′ w₀) ≡ true → is-just (At.part H w₀) ≡ true
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
      ; ling-rested = λ {C} → pin-alike (conn-left {B = C} rp src-eq (leftover-alike H H′ {B = ⊤} bd (fin-ab fr)))
      ; ling-below  = λ lg → Linger.lg-connect H′
          (λ x pn pe → subst (Tied rt) (sym (leftover-alike H H′ {B = ⊤} u (fin-au fr)))
                         (Lingers.rests lg here refl (trans (sym (fin-part fr)) x) (trans (sym (part-alike H H′ u (fin-au fr))) pn) pe))
          (λ jb → lingers-alike H H′ (fin-au fr) (lingers-sub H lg (in-source here)
                    (cong (λ z → z ∧ true) (trans (cong is-just (sym (part-alike H H′ bd (fin-ab fr)))) jb))))
          (λ js → lingers-alike H H′ (fin-ab fr) (lingers-sub H lg (in-body here)
                    (cong (λ z → z ∧ true) (trans (cong (λ x → is-just x ∨ is-just e) (sym (part-alike H H′ u (fin-au fr)))) js)))) }
      where
        src-eq : At.sourced H′ (At.part H′ u) (At.leftover H′ u) ≡ At.sourced H (At.part H u) (At.leftover H u)
        src-eq = trans (cong₂ (At.sourced H′) (part-alike H H′ u (fin-au fr)) (leftover-alike H H′ u (fin-au fr)))
                       (src-≡ H H′ (At.part H u) (At.leftover H u))

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
    fin-gone : AllPairs _≢_ (names w₀) → Gone H H′ w₀
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
    -- subscriber the finish read, the closed flag apart from the list.
    --
    -- REFUTED: 26b032ed of the finish staged with each joiner left holding what it held, by a connect of an `of` whose body is a joined subscription
    fin-joins : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → ∀ ν → At.Fed H′ w₀ ν → At.Fed H′ v ν
    fin-joins fs jn = fed-owed H′ Sj c b kb k fd′ rp e rt u bd (envP ρ [])
                        (λ m → subst (λ z → _ ∈ᴸ z) (sym (cong lower (look-store H (Subject.closed Sj) (Subject.subscribers Sj) (λ eq → apart (sym eq)))))
                                     (lookupᴬ (proj₂ jn) (joiners-path ρ [] (++⁺ʳ (joiners u (envP ρ [])) m))))
      where
        apart : _≢_ {A = Name h} (_ , Subject.subscribers Sj) (_ , Subject.closed Sj)
        apart with fresh-path ρ fs
        ... | a₀ ∷ _ = lookupᴬ a₀ (here refl)

    fin-kernels : AllPairs _≢_ (names T) → Kernels H T → Kernels H′ T′
    fin-kernels fs kn = record { holds   = holds-plant H′ {t = T} ρ v refl (λ {E} {o} → body-holds H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd {E} {o}) (Kernels.holds kn′)
                               ; gated   = gated-plant H′ {t = T} ρ v (body-gated H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (body-spent H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (Kernels.gated kn′)
                               ; settled = settled-plant H′ {t = T} ρ v Bd.body-owes (body-settled H′ {S = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd₁ = idle} {fd₂ = fd′} {rp = rp} {e = e} {rt = rt} {src = u} (at-here (At.owing H′ fd′)) bd) (Kernels.settled kn′) }
      where kn′ = Wr.wr-kernels fs (λ {E} {o} → fin-holds (fresh-path ρ fs) {E} {o}) (λ _ → fin-gated (fresh-path ρ fs)) (fin-spent (fresh-path ρ fs)) kn

    fin-meaning : AllPairs _≢_ (names T) → At.Joined H (subjects T) (joiners T []) → Meaning H T → Meaning H′ T′
    fin-meaning fs jn mn = record { fed = fed-plant H′ {t = T} ρ v (fin-joins fs jn) _ (Meaning.fed (Wr.wr-meaning fs (fin-fed (fresh-path ρ fs)) mn)) }

  -- A connect's source ended: its subject closed, the subscribers read,
  -- their finish owed ahead of the calls the end owed.
  close-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                 (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {ks}
               → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) (closes ks) → Called st m₁ (ρ ⊕ in-source here)
  close-source st ρ cl with src-idle ρ cl
  close-source st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {Sj} {c} {b} {kb} {k} {e = e} {rp} {rt} {u = u} {bd} ρ {ks}
    cl@record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; lingers = lgr } | refl
    with writes (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-source here) top) cd)
  ... | n′ , en , path₁ with reads {hp = Fins.H′ hp ρ q} en
  ...   | k′ , f , path₂ with Fins.fin-ghost hp ρ q sn pl gn L sg
  ...     | g″ , pg , sn″ , pl″ , k″ , r , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pl″ ; tree = Fins.T′ hp ρ q
        ; ctlAs = runAs (finC (planted ρ v) ∷ Fins.fin-calls hp ρ q ks) ec (Fins.fin-stack hp ρ q sk)
        ; meets = pg
        ; owned′ = owned-to (Fins.fin-owned hp ρ q fs sk ks ec ow)
        ; kernels = Fins.fin-kernels hp ρ q fs kn ; meaning = Fins.fin-meaning hp ρ q fs (Queue.joined qu) mn ; queue = Fins.fin-queue hp ρ q fs qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v (Fins.Bd.body-names hp ρ q))) fs
                         ; clocked = proj₁ ck , Fins.fin-ticked hp ρ q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind′ = Eaching.each-to _ _ (Fins.fin-behind hp ρ q fs (tells-past cl) (ended-past cl) bh) ; lingers′ = Lingering.lingers-to _ (Fins.fin-lingers hp ρ q fs (ended-past cl) lgr) })
      , passed ag pp)
    where
      path = ⇝-trans path₁ path₂
      ss = At.val (Fins.H′ hp ρ q) (Subject.subscribers Sj)
      v  = Fins.v hp ρ q
      ec = ≗-trans (f same⊑ ss) (bind≗ (≗-refl (Strongly.code R (finC (planted ρ v)))) λ _ → ≗-trans (wk-same ⟦ ks ⟧ᶜ) (Fins.fin-code hp ρ q ks))

  -- A signal reaching a connect's subject.
  call-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {sg : Signal T A}
              → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) sg → Called st m₁ (ρ ⊕ in-source here)
  call-source st ρ {sends _}  cl = climb-source st ρ cl
  call-source st ρ {closes _} cl = close-source st ρ cl

  -- A signal at the root: a value recorded next, the ghost's step
  -- showing it; an end the run's end asked of the record, the ghost's
  -- step its end.
  call-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {sg : Signal T R} → Calling g ℓ m₁ {T = T} here sg → Hopped st m₁
  call-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} {T} {sends y}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ ke ; stack = sk ; lifted = c′ , pv , _ , lifts-here , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } ; sorted = so ; behind = bh ; lingers = lgr ; flags = dn } =
    g , _ , then refl now
    , carried (record
        { sane = sn ; placed = pl ; tree = T ; ctlAs = noteAs [] (ke tt) sk ; meets = c′ , pv , sg
        ; owned′ = owned-to (owned-move hp (noteAs [] (ke tt) sk) refl refl refl ow) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } 
        ; sorted = sorted-⇝ so (then refl now) ; behind′ = Eaching.each-to _ _ bh ; lingers′ = Lingering.lingers-to _ lgr ; flags = dn })
    , showing (agrees (λ n → agree-refl n _)) (λ ())
  call-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} {sg = closes _}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ _ ; lifted = _ , _ , lifts-here , sg ; books = record { running = refl } } =
    g , _ , then refl now , closing refl refl sg sn pl , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator called, by the operator.
  call-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → ∀ {sg} → Calling g (loadOf st) m₁ (ρ ⊕ s) sg → Called st m₁ (ρ ⊕ s)
  call-step st ρ one-map       cl = rose now (one-lower ρ one-map) (call-map ρ cl)
  call-step st ρ one-scan      cl = call-scan st ρ cl
  call-step st ρ one-take      cl = call-take st ρ cl
  call-step st ρ one-outer     cl = call-outer st ρ cl
  call-step st ρ (one-lanes o) cl = call-lanes st ρ _ o cl
  call-step st ρ one-source    cl = call-source st ρ cl
  call-step st ρ one-body      cl = call-body st ρ cl
  call-step st ρ one-defer     cl = rose now (one-lower ρ one-defer) (call-defer ρ cl)

  -- A SIGNAL CLIMBS TO A RE-ENTRY CONFIGURATION: one operator at a time,
  -- from the path's far end, each step to a shorter path.
  call : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
         (σ : Path T v) {sg : Signal T A} → height σ < n → Calling g (loadOf st) m₁ σ sg → Hopped st m₁
  call st zero    σ () cl
  call st (suc n) σ lt cl with view σ
  ... | whole      = call-root st cl
  ... | snoc ρ s o with call-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (call st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  soar : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Aloft g (loadOf st) m₁) → Hopped st m′
  soar st (m₁ , path , aloft {σ = σ} cl) = hopped-pre path (call st (suc (height σ)) σ ≤-refl cl)

  postulate
    -- A takeWhile the ghost holds the path to: its completion begun
    -- under its failing value, its cut the frame's rest.  Only there:
    -- `Lifts` reads every step it passes held, so no signal is aloft on
    -- a hidden path.
    take1-enter : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
                → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → seen (Conf.heap (Mach.conf m)) π ≡ true → ∀ {m′} → step m ≡ silent m′
                → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

    -- A hidden takeWhile's completion, as a hidden `of`'s value
    -- (`emit-void`): what the ghost shows of it, the hidden part's rest.
    take1-void : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
               → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr

    -- A spent `of` the ghost holds, reading its observer open: its
    -- completion begun at its end.
    last-enter : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
               → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
               → seen (Conf.heap (Mach.conf m)) π ≡ true → ∀ {m′} → step m ≡ silent m′
               → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

    -- A hidden spent `of` reading its observer open: its end climbs to
    -- its guard, as a hidden value does (`emit-void`).
    last-void : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr

    -- A connect's feed of its source's end: no subscriber left, the
    -- agenda on; or the next subscriber's completion begun.
    fin-enter : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
              → firstCall (Carried.ctlAs cr) ≡ just (finC π) → ∀ {m′} → step m ≡ silent m′
              → Σ Mach λ m₁ → m′ ⇝ m₁ × (Hopped (carried cr) m₁ ⊎ Aloft g (load m (Carried.tree cr)) m₁)

  -- A takeWhile's completion delivered under its failing value, then
  -- its cut.
  take1-onward : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
               → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → Hops cr
  take1-onward {m = m} cr π fc with seen (Conf.heap (Mach.conf m)) π in sn
  ... | false = take1-void cr π fc sn
  ... | true  = λ eq → soar (carried cr) (take1-enter cr π fc sn eq)

  -- A spent `of` the ghost holds: its completion delivered at its end.
  emit-last : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ true → Hops cr
  emit-last cr π fc op sn eq = soar (carried cr) (last-enter cr π fc op sn eq)

  -- The rest of a connect's feed of its source's end.
  fin-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
               (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
             → firstCall (Carried.ctlAs cr) ≡ just (finC π) → Hops cr
  fin-onward cr π fc eq with fin-enter cr π fc eq
  ... | m₁ , path , inj₁ hp = hopped-pre path hp
  ... | m₁ , path , inj₂ af = soar (carried cr) (m₁ , path , af)

  -- The agenda's first call an open `of` the ghost holds: every sibling
  -- its path passes heads past the `of`'s base, no earlier than the run
  -- (`Carried.behind`) and not under it.
  -- DEAD ROUTE: a per-frame order.  A stack frame's calls are ordered
  --   against the current position only by `backAs`'s `q <ᵖ p`, which
  --   does not make `q` a prefix of `p`: a frame at `q` beside `p`
  --   holding an `of` has its next value ahead of this one.
  others-past : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ true → Clear (Conf.heap (Mach.conf m)) (Far p) π
  others-past {m = m} cr {p = p} π fc op sn =
    clear-zip {P = Heads p} {Q = Off p} {R′ = Far p} (λ {Γ} {A} {c} → far-apart {p} {Γ} {A} {c}) π
      (clear-each (subst (λ q → Each (Conf.heap (Mach.conf m)) (Heads q) (Carried.tree cr))
                         (run-at (Carried.ctlAs cr) fc (Owned.placed (Carried.owned cr))) (Carried.behind cr)) π sn refl)
      (spread-past cr π fc op sn)

  -- The agenda's first call an open `of` the ghost holds: the ghost's
  -- step is that `of`'s, lifted.
  emit-lifts : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
             → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
             → seen (Conf.heap (Mach.conf m)) π ≡ true → Lifts (Conf.heap (Mach.conf m)) π (U.step (U.ofᶜ p i (x ∷ xs))) (U.step g)
  emit-lifts cr π fc op sn with heads-lift cr π sn (others-past cr π fc op sn)
  ... | c , pc , L = subst (λ c′ → Lifts _ π _ (U.step c′)) (just-injective (trans (sym pc) (run-meets (Carried.ctlAs cr) fc (Carried.meets cr)))) L

  -- An open `of` the ghost holds: its value on its way up, the ghost's
  -- step that value lifted.
  emit-open : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
            → seen (Conf.heap (Mach.conf m)) π ≡ true → ∀ {m′} → step m ≡ silent m′ → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁
  emit-open cr π fc op sn = emit-run cr π fc op (emit-lifts cr π fc op sn)

  -- An `of`'s next value climbs the observers above it: to the root's
  -- note, past a skip (a connect's feed, a lane admitted), or to a
  -- takeWhile's end.
  emit-onward : ∀ {g m} (cr : Carried g m) {Δ A p i xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i xs))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-onward {m = m} cr {xs = []} π fc with opened (Conf.heap (Mach.conf m)) true π in op | seen (Conf.heap (Mach.conf m)) π in sn
  ... | false | _     = emit-shut cr π fc op
  ... | true  | false = last-void cr π fc op sn
  ... | true  | true  = emit-last cr π fc op sn
  emit-onward {m = m} cr {xs = x ∷ xs} π fc with opened (Conf.heap (Mach.conf m)) true π in op | seen (Conf.heap (Mach.conf m)) π in sn
  ... | false | _     = emit-shut cr π fc op
  ... | true  | false = emit-void cr π fc op sn
  ... | true  | true  = λ eq → soar (carried cr) (emit-open cr π fc op sn eq)

  -- CODE RUNS SILENTLY ON TO A RE-ENTRY STATE: a subscription begun, the
  -- agenda's first call, or the agenda done and its stack resumed: a
  -- frame's rest, a scope's continuation at the position it puts back, a
  -- burst held, the turn.  The ghost alike, the control's work less.
  run-onward : ∀ {g m w act K} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ run {B = ⊤} act σ K
             → Hops cr
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs _ _ _ _ } refl eq = sub-onward (λ {g} {m} → emit-onward {g} {m}) cr refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (emitC π ∷ _) _ _ } refl eq = emit-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (kontC lf π ∷ _) _ _ } refl eq = kont-onward cr lf π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take1C π ∷ _) _ _ } refl eq = take1-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take2C π ∷ _) _ _ } refl eq = cut-onward cr (takeSite π) refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (bodyC π ∷ _) _ _ } refl eq = cut-onward cr (bodySite π) refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (feedC π ∷ _) _ _ } refl eq = feed-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (finC π ∷ _) _ _ } refl eq = fin-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (srcC π ∷ _) _ _ } refl eq = src-onward cr π refl eq
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) bottomAs ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned′ = owned-to (owned-move hp calmAs refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (restAs ks e K″) ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned′ = owned-to (owned-move hp (runAs ks e K″) refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (backAs q ks qp e K″) ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned′ = owned-to (owned-move hp (runAs ks e K″) refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn
        ; queue = record { timed = Queue.timed qu ; joined = Queue.joined qu ; ordered = Queue.ordered qu
                         ; ahead = map (λ { (c , a) → c , <ᵖ-trans q p _ qp a }) (Queue.ahead qu) }
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind′ = Eaching.each-to _ _ (each-back qp (Carried.behind cr)) ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (playsAs π) hᴷ K″) ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (playsAs π) hᴷ K″ ; meets = mt
        ; owned′ = owned-to (owned-move hp (burstAs (playsAs π) hᴷ K″) refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (firesAs π) hᴷ K″) ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (firesAs π) hᴷ K″ ; meets = mt
        ; owned′ = owned-to (owned-move hp (burstAs (firesAs π) hᴷ K″) refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs bottomᴴ bottomAs) ; meets = mt ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned′ = owned-to (owned-move hp calmAs refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs restᴴ (restAs ks e K‴)) ; meets = mt ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K‴ ; meets = mt
        ; owned′ = owned-to (owned-move hp (runAs ks e K‴) refl refl refl (Carried.owned cr)) ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ (proj₂ ck) ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

  -- Past a value recorded, the run runs the stepped ghost: the record's
  -- continuation is the agenda, about to run.
  note-onward : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
              → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
              → ∀ {t q a′ m′} → step m ≡ value t q a′ m′ → Mirror g′ m′
  note-onward {g} {m = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk}
    cr@record { tree = t ; ctlAs = noteAs ks ke K ; meets = g″ , pe , st″ ; books = record { running = refl } } refl stp refl
    with trans (sym st″) stp
  ... | refl = _ , now , carried (record
        { sane = sane-out {g = g} (Carried.sane cr) stp
        ; placed = proj₂ (subst (Placedˢ []) stp (placed-after g (Carried.sane cr) (Carried.placed cr)))
        ; tree = t ; ctlAs = runAs ks ke K ; meets = pe
        ; owned′ = owned-to (record { ofs = Owned.ofs (Carried.owned cr) ; plays = Owned.plays (Carried.owned cr) ; fires = Owned.fires (Carried.owned cr) ; begun = Owned.begun (Carried.owned cr)
                         ; ends = Owned.ends (Carried.owned cr) ; cuts = Owned.cuts (Carried.owned cr) ; feeds = Owned.feeds (Carried.owned cr) ; fins = Owned.fins (Carried.owned cr) ; bodies = Owned.bodies (Carried.owned cr)
                         ; placed = Owned.placed (Carried.owned cr) })
        ; kernels = Carried.kernels cr ; meaning = Carried.meaning cr ; queue = Carried.queue cr
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = refl } 
        ; sorted = sorted-value (Carried.sorted cr) refl ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })

  -- A popped timer's burst, spent, dropped: the turn again.
  drop-spent : ∀ {h} {hp : Heapᴹ h} {p w} {σ : w ⊑ h} {ts lg en mk} (tm : Timer h)
             → spent? hp (Timer.handle tm) ≡ true
             → step (mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts
                       (just (record { sink = Timer.sink tm ; handle = Timer.handle tm ; at′ = Timer.at′ tm
                                     ; under′ = cascade tm ; index = 0 ; frame = Timer.frame tm ; polled = false }) ∷ []) [] lg en mk)
               ≡ silent (mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts [] [] lg en mk)
  drop-spent _ sp rewrite sp = refl

  -- The queue's head spent: the rest of the queue still every live
  -- pending frame.
  timed-spent : ∀ {h} {H : Heapᴹ h} {tm ts ps} → At.spentʰ H (Timer.handle tm) ≡ true → At.Timed H (tm ∷ ts) ps → At.Timed H ts ps
  timed-spent {H = H} {tm} {ts} sp (_ ∷ as , bs) = as , map keep bs
    where
      keep : ∀ {x} → (At.spentʰ H (Timer.handle x) ≡ false → x ∈ᴸ tm ∷ ts) → At.spentʰ H (Timer.handle x) ≡ false → x ∈ᴸ ts
      keep f nsp with f nsp
      ... | here refl = ⊥-elim (true≢false (trans (sym sp) nsp))
      ... | there i   = i

  -- The queue's head popped: the rest due no earlier than it.
  ahead-pop : ∀ {h} {p : Pos} {clk} {tm : Timer h} {ts}
            → Linked (λ x y → cascade x <ᵖ cascade y ≡ true) (tm ∷ ts)
            → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) (tm ∷ ts)
            → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) ts
  ahead-pop {p = p} {tm = tm} lk (_ ∷ ah) = go (later lk) ah
    where
      go : ∀ {clk xs} → All (λ x → cascade tm <ᵖ cascade x ≡ true) xs → All (λ x → clk ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
         → All (λ x → Timer.due tm ≤ Timer.due x × p <ᵖ cascade x ≡ true) xs
      go []       []             = []
      go {xs = x ∷ _} (c ∷ cs) ((_ , a) ∷ as) = (<ᵖ-tick (Timer.due tm) (Timer.due x) (subᴾ (Timer.from tm) ∷ []) (subᴾ (Timer.from x) ∷ []) c , a) ∷ go cs as

  -- THE TURN POPPING A TIMER: a spent one's burst dropped a step later,
  -- the ghost alike, a timer fewer; a live one's cold fired, the same
  -- meaning node with its burst held, a timer fewer.
  turn-pops : ∀ {g m w} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ bottom
            → Mach.bursts m ≡ [] → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  turn-pops {m = mach ⟨ _ , _ , _ ⟩ _ [] _ _ _ _ _} record { books = record { paidUp = refl } } refl refl ()
  turn-pops {g} {mach ⟨ hp , p , _ ⟩ _ (tm ∷ ts) _ _ lg en mk} {σ = σ}
    cr@record { tree = t ; ctlAs = calmAs ; meets = mt ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl refl
    with spent? hp (Timer.handle tm) in sp
  ... | true =
    g , mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts [] [] lg en mk , then (drop-spent tm sp) now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt ; owned′ = Carried.owned′ cr
        ; kernels = kn ; meaning = mn
        ; queue = record { timed = timed-spent {H = hp} sp (Queue.timed q) ; joined = Queue.joined q
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then (drop-spent tm sp) now) ; behind′ = Carried.behind′ cr ; lingers′ = Carried.lingers′ cr ; flags = Carried.flags cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₁ ≤-refl))))
  ... | false with proj₁ (Queue.timed q)
  ...   | inj₁ s ∷ _ = ⊥-elim (true≢false (trans (sym s) sp))
  ...   | inj₂ i ∷ _ with pendings-path {t = t} i
  ...     | waits {τ = τ} {e = e} {u = u} {x = x} {sk = sk} {hd = hd} {fr = fr} π =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = plant π v
        ; ctlAs = burstAs (firesAs (planted π v)) bottomᴴ bottomAs
        ; meets = trans (part-plant hp {t = t} π v refl) mt
        ; owned′ = owned-to (owned-pop hp {t = t} π (Carried.owned cr))
        ; kernels = record { holds = holds-plant hp {t = t} π v refl (λ h → h) (Kernels.holds kn)
                           ; gated = gated-plant hp {t = t} π v (λ _ → lift (λ _ → refl)) (λ s → s) (Kernels.gated kn)
                           ; settled = settled-plant hp {t = t} π v (λ ()) (λ s → s) (Kernels.settled kn) }
        ; meaning = record { fed = fed-plant hp {t = t} π v (λ _ f → f) _ (Meaning.fed mn) }
        ; queue = record { timed = timed-pop hp {t = t} π (Queue.timed q) (Queue.ordered q) fs
                         ; joined = subst₂ (At.Joined hp) (sym (subjects-plant {t = t} π v refl)) (sym (joiners-plant {t = t} π v (λ _ → refl) _)) (Queue.joined q)
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = t} π v refl)) fs ; clocked = refl , tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl now ; behind′ = Eaching.each-to _ _ (behind-fire cr π) ; lingers′ = Lingering.lingers-to _ (fire-lingers cr π) })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (pend-plant {t = t} π v refl , inj₂ (takes-plant {t = t} π v refl , inj₁ ≤-refl))))
    where v = coldˢ sk hd (fired τ e (at u x fr))

  -- The stepper is the meaning, as sets.
