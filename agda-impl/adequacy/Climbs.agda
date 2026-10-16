{-# OPTIONS --guardedness #-}

-- THE CLIMB: a value carried from its emitter up a path, each
-- operator's callback one rise; and the close, its teardown.
module adequacy.Climbs where

open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m<n⇒m<1+n)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; tail)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; Pos; Timeline; agree-refl; at; _<ᵖ_; <ᵖ-tick; <ᵖ-trans)
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
open import adequacy.Sane using (Sane; sane-out)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (placed-after; Placedˢ)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; note; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Lift using (module Lifting)
open import adequacy.Frame using (module Framing)

open Events∞

module Ascending (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; drained; step; trace; shown; reading; begin; launch; Read; read; feed)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; spent?; store; look; stored) renaming (go to goᴵ)
  open Heap using (World; _⊑_; Handle; Quiet) renaming (same to same⊑)
  open Sorting R using (WellMach; WellStep; silentʷ; valueʷ; preserve; Beyond)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; Observer; Subject; _>>ᴬ_; module Kit; module FlatKit)
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
  open Lifting R using (turn-dry; sub-onward; emit-shut; emit-void; emit-run; shut-step; spread-past; behind-fire; take-out; take-end; climb-outer; climb-lanes; climb-source; kont-onward; feed-onward; src-onward; burst-poll; burst-play; note-least; tear-cut; torn-fed; torn-holds; torn-gated; torn-queue; torn-part; torn-behind; cut-onward; Below; below; under-++; far-lt; far-gt; below-map; below-scan; below-take; below-outer; below-lane; below-source; below-body; below-shut; beforeᴹ; before-head; shut-head; before-far; before-not; source-first; body-first; body-step; rest-behind; ended-shut; FarE; earliest-far; earliest-split; earliest-found; outer-first; lane-first; pool-outer; pool-lane; flat-outer; go-lane; flat-lane; Peek; peek-nothing; peek-just; peek; lanes-cons; held-flat; held-lanes; held-src; held-shut; lift-up; lift-up-lanes; heads-lift)
  open Framing R using (scan-part; scan-owned; scan-kernels; scan-meaning; scan-queue; scan-lifts; scan-behind)
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
    cr@record { tree = t ; ctlAs = burstAs x bottomᴴ bottomAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-spent hp calmAs sp refl refl refl ow ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
  burst-spent {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk} {K = K} {b = b} {bs = bs} {σ = σ}
    cr@record { tree = t ; ctlAs = burstAs x restᴴ (restAs ks e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl sp eq
    with trans (sym eq) (drop-held {hp = hp} {p = p} {σ = σ} {K = K} {clk = clk} {ts = ts} {b = b} {bs = bs} {lg = lg} {en = en} {mk = mk} sp)
  ... | refl =
    g , _ , now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-spent hp (runAs ks e K″) sp refl refl refl ow ; kernels = kn ; meaning = mn ; queue = q
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr eq now ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

  -- A burst's frame stepped: found spent, polled, or played.
  burst-onward : ∀ {g m w K b bs} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ held σ K
               → Mach.bursts m ≡ just b ∷ bs → ∀ {m′} → step m ≡ silent m′ → Hopped (carried cr) m′
  burst-onward {m = m} {b = b} cr c bq eq with spent? (Conf.heap (Mach.conf m)) (Playing.handle b) in sp | Playing.polled b in pl
  ... | true  | _     = burst-spent cr c bq sp eq
  ... | false | false = burst-poll cr c bq sp pl eq
  ... | false | true  = burst-play cr c bq sp pl eq

  -- A value through a map: mapped, one operator up.
  climb-map : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (ρ : Path T (mapˢ f u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-map here) y → Climbing g ℓ m₁ ρ (f y)
  climb-map {m₁ = m₁} {f = f} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-map here) top) (Climbing.code cl))
    (U.mapᶜ f c′ , cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) pv , S , Lρ , sg)

  -- A value through a defer, as it is.
  climb-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (deferˢ k u)) {y : A} → Climbing g ℓ m₁ (ρ ⊕ in-defer here) y → Climbing g ℓ m₁ ρ y
  climb-defer ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Climbing.code cl))
    (c′ , pv , S , Lρ , sg)

  -- A value out of a connect's body, as it is: beside its source, or
  -- past its source's end.
  climb-body : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt} {t : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B} (ρ : Path T (connectˢ Sj c b kb k fd rp e rt t u)) {y : B}
             → Climbing g ℓ m₁ (ρ ⊕ in-body here) y → Climbing g ℓ m₁ ρ y
  climb-body {m₁ = m₁} {e = e} {rp} {rt} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-body here) L
  ...   | _ , lifts-body pt _ lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg)
  ...   | _ , lifts-shut pt refl _ lifts-here , Lρ = reclimb cl
    (subst (λ W → Climbing.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Climbing.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg)

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
            → Climbing g ℓ m₁ (ρ ⊕ in-take here) y → Rises g (load m₁ T) m₁ (ρ ⊕ in-take here)
  take-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rises (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (≗-trans (wk-same _) (pass-code lv py))
      ; stack = sk
      ; lifted = U.takeWhileᶜ i p c′ , take-part hp {i = i} {p = p} {c = c} {k = k} {u = u} lv pv , S , subst (λ s → Lifts hp ρ s S) (cong (U.taking i p q y c′) py) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = inj₁ refl })

  -- The value risen, held to the climb's load.
  rise : ∀ {g m} {st : Strong g m} {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v}
       → load m₁ T ≼ loadOf st → Rises g (load m₁ T) m₁ σ → Climbed st m₁ σ
  rise le (rises path lt cl) = rose path lt (relevel cl le)

  -- A write, one step: the cell stored, what follows it run.
  writes : ∀ {h} {hp : Heapᴹ h} {q w} {σ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {t} {r : Ref h t} {z} {n : Act h ⊤}
         → a ≗ writeRef r z n
         → Σ (Act h ⊤) λ n′ → n′ ≗ n × (mach ⟨ hp , q , run a σ K ⟩ clk ts bs td lg en mk ⇝ mach ⟨ store hp r (lift z) , q , run n′ σ K ⟩ clk ts bs td lg en mk)
  writes (writeRef≗ refl refl e) = _ , e , then refl now

  -- A value through a scan: its cell read and written, the accumulated
  -- value one operator up, the tree's load as it was.
  scan-pass : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
            → Climbing g ℓ m₁ (ρ ⊕ in-scan here) y → Rises g (load m₁ T) m₁ (ρ ⊕ in-scan here)
  scan-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {f = f} {r = r} {u = u} ρ {y}
    cl@record { sane = sn ; placed = pl ; ϑ = ϑ ; K = K ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; kept = kp }
    with lifts-split ρ (in-scan here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-scan here) top) cd
  ... | _ , lifts-scan lifts-here , Lρ | readRef≗ refl k =
    rises (then refl (proj₂ (proj₂ wr))) (one-lower ρ one-scan) (record
      { sane = sn ; placed = pl ; ctl = refl ; code = proj₁ (proj₂ wr) ; stack = sk
      ; lifted = U.scanᶜ f z c′ , scan-part hp (fresh-path ρ fs) z pv , S , scan-lifts hp ρ fs z Lρ , sg
      ; owned = scan-owned hp ρ fs z ow ; kernels = scan-kernels hp ρ fs z kn ; meaning = scan-meaning hp ρ fs z mn ; queue = scan-queue hp ρ fs z qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl (proj₂ (proj₂ wr))) ; behind = scan-behind ρ cl ; kept = inj₁ refl })
    where z = f (At.val hp r) y
          wr = writes {σ = ϑ} {K = K} {clk = clk} {ts} {bs} {td} {lg} {en} {mk} (≗-trans (k same⊑ (At.val hp r)) (wk-same _))

  climb-scan : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
             → Climbing g (loadOf st) m₁ (ρ ⊕ in-scan here) y → Climbed st m₁ (ρ ⊕ in-scan here)
  climb-scan st ρ cl = rise (Climbing.kept cl) (scan-pass ρ cl)

  -- A value through a takeWhile: passed one operator up; or failing,
  -- delivered first when inclusive, then the completion climbs, then
  -- the cut.  The failing value cannot stop at the completion owed with
  -- the ghost alike unless the take's stage counts: the control's work
  -- rises.
  climb-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u)) {y : A}
             → Climbing g (loadOf st) m₁ (ρ ⊕ in-take here) y → Climbed st m₁ (ρ ⊕ in-take here)
  climb-take st {i = i} {p} ρ {y} cl with Climbing.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-take here) L
  ...   | _ , lifts-take lv lifts-here , Lρ with p y in py | i
  ...     | true  | _     = rise (Climbing.kept cl) (take-pass ρ py cl)
  ...     | false | true  = rise (Climbing.kept cl) (take-out ρ py cl)
  ...     | false | false with take-end ρ py cl
  ...       | g″ , m₀ , path , cr , ag , lt = landed (g″ , m₀ , path , carried cr , lowered ag (inj₁ (⊏-≼ lt (Climbing.kept cl))))

  -- A value at the root: recorded next, the ghost's step showing it.
  climb-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {y : R} → Climbing g ℓ m₁ {T = T} here y → Hopped st m₁
  climb-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk} {T}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ ke ; stack = sk ; lifted = c′ , pv , _ , lifts-here , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } ; sorted = so ; behind = bh } =
    g , _ , then refl now
    , carried (record
        { sane = sn ; placed = pl ; tree = T ; ctlAs = noteAs [] (ke tt) sk ; meets = c′ , pv , sg
        ; owned = owned-move hp (noteAs [] (ke tt) sk) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } 
        ; sorted = sorted-⇝ so (then refl now) ; behind = bh })
    , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator climbed, by the operator.
  climb-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → ∀ {y} → Climbing g (loadOf st) m₁ (ρ ⊕ s) y → Climbed st m₁ (ρ ⊕ s)
  climb-step st ρ one-map       cl = rose now (one-lower ρ one-map) (climb-map ρ cl)
  climb-step st ρ one-scan      cl = climb-scan st ρ cl
  climb-step st ρ one-take      cl = climb-take st ρ cl
  climb-step st ρ one-outer     cl = climb-outer st ρ cl
  climb-step st ρ (one-lanes o) cl = climb-lanes st ρ _ o cl
  climb-step st ρ one-source    cl = climb-source st ρ cl
  climb-step st ρ one-body      cl = rose now (one-lower ρ one-body) (climb-body ρ cl)
  climb-step st ρ one-defer     cl = rose now (one-lower ρ one-defer) (climb-defer ρ cl)

  -- A VALUE CLIMBS TO A RE-ENTRY CONFIGURATION: one operator at a time,
  -- from the path's far end, each step to a shorter path.
  climb : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
          (σ : Path T v) {y : A} → height σ < n → Climbing g (loadOf st) m₁ σ y → Hopped st m₁
  climb st zero    σ () cl
  climb st (suc n) σ lt cl with view σ
  ... | whole      = climb-root st cl
  ... | snoc ρ s o with climb-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (climb st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  soar : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Aloft g (loadOf st) m₁) → Hopped st m′
  soar st (m₁ , path , aloft {σ = σ} cl) = hopped-pre path (climb st (suc (height σ)) σ ≤-refl cl)

  -- A COMPLETION ON ITS WAY UP: the observer the path walks to about
  -- to be told its source has ended, the calls `ks` owed after it.  The
  -- node it leaves is gone: the call that owed the end is spent, so the
  -- `of` is done, the take taken, the joiner told.  The ghost's step is
  -- that end lifted along the path.
  record Closing (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
                 (σ : Path T v) : Set₁ where
    field
      sane    : Sane [] g
      placed  : Placed g []
      {w}     : World
      {ϑ}     : w ⊑ Conf.world (Mach.conf m₁)
      {act}   : Act (Conf.world (Mach.conf m₁)) ⊤
      {K}     : Stack w ⊤
      {ks}    : List (Call T)
      ctl     : Conf.ctl (Mach.conf m₁) ≡ run act ϑ K
      code    : act ≗ (Observer.complete (Here.obs (walk σ top)) >>ᴬ ⟦ ks ⟧ᶜ)
      stack   : StackAs T (Conf.pos (Mach.conf m₁)) ϑ K (Mach.bursts m₁)
      gone    : At.part (Conf.heap (Mach.conf m₁)) v ≡ nothing
      lifted  : Σ (U.Step [] R) λ S → Lifts (Conf.heap (Mach.conf m₁)) σ (U.endˢ (Conf.pos (Mach.conf m₁))) S × U.step g ≡ S
      owned   : Owned (Conf.heap (Mach.conf m₁)) T (runAs ks (≗-refl _) stack)
      kernels : Kernels (Conf.heap (Mach.conf m₁)) T
      meaning : Meaning (Conf.heap (Mach.conf m₁)) T
      queue   : Queue (Conf.heap (Mach.conf m₁)) (Conf.pos (Mach.conf m₁)) (Mach.clock m₁) (Mach.timers m₁) T
      books   : Books T (runAs ks (≗-refl _) stack) m₁
      sorted  : Σ Pos λ lo → WellMach lo m₁
      behind  : Each (Conf.heap (Mach.conf m₁)) (Heads (Conf.pos (Mach.conf m₁))) T
      kept    : load m₁ T ≼ ℓ

  -- The same completion, restated at another path.
  reclose : ∀ {g ℓ m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              {v′ : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} {σ : Path T v} (cl : Closing g ℓ m₁ σ) {σ′ : Path T v′}
          → Closing.act cl ≗ (Observer.complete (Here.obs (walk σ′ top)) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)
          → At.part (Conf.heap (Mach.conf m₁)) v′ ≡ nothing
          → Σ (U.Step [] R) (λ S → Lifts (Conf.heap (Mach.conf m₁)) σ′ (U.endˢ (Conf.pos (Mach.conf m₁))) S × U.step g ≡ S)
          → Closing g ℓ m₁ σ′
  reclose cl cd gn lf = record
    { sane = Closing.sane cl ; placed = Closing.placed cl ; ctl = Closing.ctl cl ; code = cd ; stack = Closing.stack cl ; gone = gn
    ; lifted = lf ; owned = Closing.owned cl ; kernels = Closing.kernels cl ; meaning = Closing.meaning cl ; queue = Closing.queue cl
    ; books = Closing.books cl ; sorted = Closing.sorted cl ; behind = Closing.behind cl ; kept = Closing.kept cl }

  -- One operator closed: a re-entry configuration reached, or the
  -- completion one operator higher, the path shorter.
  data Closed {g m} (st : Strong g m) (m₁ : Mach) {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (σ : Path T v) : Set₁ where
    landed : Hopped st m₁ → Closed st m₁ σ
    rose   : ∀ {m₂ Δ′ A′} {T′ : Sub (Conf.world (Mach.conf m₂)) [] R} {v′ : Sub (Conf.world (Mach.conf m₂)) Δ′ A′} {σ′ : Path T′ v′}
           → m₁ ⇝ m₂ → height σ′ < height σ → Closing g (loadOf st) m₂ σ′ → Closed st m₁ σ

  -- Some completion on its way up.
  data Afloat (g : U.Node [] R) (ℓ : Load) (m₁ : Mach) : Set₁ where
    afloat : ∀ {Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A} {σ : Path T v}
           → Closing g ℓ m₁ σ → Afloat g ℓ m₁

  -- A completion through a map, as it is.
  close-map : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : A → B} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
              (ρ : Path T (mapˢ f u)) → Closing g ℓ m₁ (ρ ⊕ in-map here) → Closing g ℓ m₁ ρ
  close-map {m₁ = m₁} {f = f} {u} ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-map here) top) (Closing.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) (Closing.gone cl))
    (S , Lρ , sg)

  -- A completion through a scan, as it is: the scan's cell unread.
  close-scan : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (scanˢ f r u)) → Closing g ℓ m₁ (ρ ⊕ in-scan here) → Closing g ℓ m₁ ρ
  close-scan {m₁ = m₁} {f = f} {r} {u} ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-scan here) L
  ...   | _ , lifts-scan lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-scan here) top) (Closing.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.scanᶜ f (At.val (Conf.heap (Mach.conf m₁)) r))) (Closing.gone cl))
    (S , Lρ , sg)

  -- A completion through a defer, as it is.
  close-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
                (ρ : Path T (deferˢ k u)) → Closing g ℓ m₁ (ρ ⊕ in-defer here) → Closing g ℓ m₁ ρ
  close-defer ρ cl with Closing.lifted cl
  ... | S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = reclose cl
    (subst (λ W → Closing.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ Closing.ks cl ⟧ᶜ)) (walk-⊕ ρ (in-defer here) top) (Closing.code cl))
    (Closing.gone cl) (S , Lρ , sg)

  -- A guard read open: what it guards.
  open-code : ∀ {w} {b : Bool} {m : Act w ⊤} → b ≡ true → Kit.when b m ≗ m
  open-code refl = ≗-refl _

  -- A live take over a gone source is gone.
  gone-take : ∀ {h} (H : Heapᴹ h) {Δ A} {i p c k} {u : Sub h Δ A} → At.val H (Kit.live c) ≡ true
            → At.part H u ≡ nothing → At.part H (takeWhileˢ i p c k taking u) ≡ nothing
  gone-take H lv gn rewrite lv | gn = refl

  -- A completion through a live takeWhile: its guard read open, one
  -- operator up, the take showing its source's end.
  close-take : ∀ {g m} (st : Strong g m) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {i p c k tk}
               {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ i p c k tk u))
             → Closing g (loadOf st) m₁ (ρ ⊕ in-take here) → Closed st m₁ (ρ ⊕ in-take here)
  close-take st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {i = i} {p = p} {c = c} {k = k} {u = u} ρ
    record { sane = sn ; placed = pl ; ks = ks ; ctl = refl ; code = cd ; stack = sk ; gone = gn ; lifted = S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rose (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (bind≗ (≗-trans (wk-same _) (open-code lv)) λ _ → wk-same _)
      ; stack = sk
      ; gone = gone-take hp {i = i} {p = p} {c = c} {k = k} {u = u} lv gn
      ; lifted = S , Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = kp })

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

  -- A connect's body ended: the connect's completion delivered, its
  -- cut owed after it, the body gone as a `bodyC` owed asks.
  close-body : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
               {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {u : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
               (ρ : Path T (connectˢ Sj c b kb k fd rp e rt t u))
             → Closing g (loadOf st) m₁ (ρ ⊕ in-body here) → Closed st m₁ (ρ ⊕ in-body here)
  close-body st {m₁ = m₁} {T = T} {Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {u} ρ
    record { sane = sn ; placed = pl ; ks = ks ; ctl = cx ; code = cd ; stack = sk ; gone = gn ; lifted = S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-body here) L
  ... | _ , Lb , Lρ = rose now (one-lower ρ one-body) (record
      { sane = sn ; placed = pl ; ks = bodyC ρ ∷ ks ; ctl = cx
      ; code = ≗-trans (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-body here) top) cd) (seq-assoc (Observer.complete (Here.obs (walk ρ top))) (Kit.cut c) ⟦ ks ⟧ᶜ)
      ; stack = sk
      ; gone = gone-connect (Conf.heap (Mach.conf m₁)) {Sj = Sj} {c = c} {b = b} {kb = kb} {k = k} {fd = fd} {e = e} {rp = rp} {rt = rt} {t = t} {u = u} gn
      ; lifted = S , subst (λ s → Lifts (Conf.heap (Mach.conf m₁)) ρ s S) (body-end Lb) Lρ , sg
      ; owned = owned-body (Conf.heap (Mach.conf m₁)) (runAs (bodyC ρ ∷ ks) (≗-refl ⟦ bodyC ρ ∷ ks ⟧ᶜ) sk) ρ refl refl refl gn ow
      ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = so ; behind = bh ; kept = kp })

  postulate
    -- A flatMap's outer ended: its done flag written, settled: the
    -- flatMap ends if no lane is left, or the lanes run on.
    close-outer : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls))
                → Closing g (loadOf st) m₁ (ρ ⊕ in-outer here) → Closed st m₁ (ρ ⊕ in-outer here)

    -- A lane ended: shut, the active count down, the next queued value
    -- begun or the flatMap ended past its outer's end.
    close-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B Δ′ C} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                  {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ′ C}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL
                → Closing g (loadOf st) m₁ (ρ ⊕ in-lanes πL) → Closed st m₁ (ρ ⊕ in-lanes πL)

    -- A connect's source ended: its subject closed, the finish of its
    -- subscribers owed.
    close-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                   {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                   (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd))
                 → Closing g (loadOf st) m₁ (ρ ⊕ in-source here) → Closed st m₁ (ρ ⊕ in-source here)

  -- A completion at the root: the run's end asked of the record, the
  -- ghost's step its end.
  close-root : ∀ {g m} (st : Strong g m) {ℓ m₁} {T : Sub (Conf.world (Mach.conf m₁)) [] R} → Closing g ℓ m₁ {T = T} here → Hopped st m₁
  close-root {g} st {m₁ = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk}
    record { sane = sn ; placed = pl ; ctl = refl ; code = eff≗ _ ; lifted = _ , lifts-here , sg ; books = record { running = refl } } =
    g , _ , then refl now , closing refl refl sg sn pl , showing (agrees (λ n → agree-refl n _)) (λ ())

  -- One operator closed, by the operator.
  close-step : ∀ {g m} (st : Strong g m) {m₁ Δ A Δ′ A′} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               {v : Sub (Conf.world (Mach.conf m₁)) Δ′ A′} (ρ : Path T u) {s : Path u v} → One s → Closing g (loadOf st) m₁ (ρ ⊕ s) → Closed st m₁ (ρ ⊕ s)
  close-step st ρ one-map       cl = rose now (one-lower ρ one-map) (close-map ρ cl)
  close-step st ρ one-scan      cl = rose now (one-lower ρ one-scan) (close-scan ρ cl)
  close-step st ρ one-take      cl = close-take st ρ cl
  close-step st ρ one-outer     cl = close-outer st ρ cl
  close-step st ρ (one-lanes o) cl = close-lanes st ρ _ o cl
  close-step st ρ one-source    cl = close-source st ρ cl
  close-step st ρ one-body      cl = close-body st ρ cl
  close-step st ρ one-defer     cl = rose now (one-lower ρ one-defer) (close-defer ρ cl)

  -- A COMPLETION CLIMBS TO A RE-ENTRY CONFIGURATION, as a value does.
  close : ∀ {g m} (st : Strong g m) (n : ℕ) {m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {v : Sub (Conf.world (Mach.conf m₁)) Δ A}
          (σ : Path T v) → height σ < n → Closing g (loadOf st) m₁ σ → Hopped st m₁
  close st zero    σ () cl
  close st (suc n) σ lt cl with view σ
  ... | whole      = close-root st cl
  ... | snoc ρ s o with close-step st ρ o cl
  ...   | landed hp         = hp
  ...   | rose path lt′ cl′ = hopped-pre path (close st n _ (≤-trans lt′ (≤-pred lt)) cl′)

  float : ∀ {g m m′} (st : Strong g m) → Σ Mach (λ m₁ → m′ ⇝ m₁ × Afloat g (loadOf st) m₁) → Hopped st m′
  float st (m₁ , path , afloat {σ = σ} cl) = hopped-pre path (close st (suc (height σ)) σ ≤-refl cl)

  postulate
    -- A takeWhile's completion begun under its failing value, its cut
    -- the frame's rest.
    take1-enter : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
                → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → ∀ {m′} → step m ≡ silent m′
                → Σ Mach λ m₁ → m′ ⇝ m₁ × Afloat g (load m (Carried.tree cr)) m₁

    -- A spent `of`'s completion begun at its end.
    last-enter : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
               → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → ∀ {m′} → step m ≡ silent m′
               → Σ Mach λ m₁ → m′ ⇝ m₁ × Afloat g (load m (Carried.tree cr)) m₁

    -- A connect's feed of its source's end: no subscriber left, the
    -- agenda on; or the next subscriber's completion begun.
    fin-enter : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
                (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
              → firstCall (Carried.ctlAs cr) ≡ just (finC π) → ∀ {m′} → step m ≡ silent m′
              → Σ Mach λ m₁ → m′ ⇝ m₁ × (Hopped (carried cr) m₁ ⊎ Afloat g (load m (Carried.tree cr)) m₁)

  -- A takeWhile's completion delivered under its failing value, then
  -- its cut.
  take1-onward : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
               → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → Hops cr
  take1-onward cr π fc eq = float (carried cr) (take1-enter cr π fc eq)

  -- A spent `of`'s completion delivered at its end.
  emit-last : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-last cr π fc eq = float (carried cr) (last-enter cr π fc eq)

  -- The rest of a connect's feed of its source's end.
  fin-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
               (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
             → firstCall (Carried.ctlAs cr) ≡ just (finC π) → Hops cr
  fin-onward cr π fc eq with fin-enter cr π fc eq
  ... | m₁ , path , inj₁ hp = hopped-pre path hp
  ... | m₁ , path , inj₂ af = float (carried cr) (m₁ , path , af)

  -- An agenda under way: the ghost is the tree's part.
  run-meets : ∀ {h} {t : Sub h [] R} {p c bs} (ca : CtlAs t p c bs) {n g k} → firstCall ca ≡ just k → Meets ca n g → n ≡ just g
  run-meets (runAs (_ ∷ _) _ _) refl mt = mt
  run-meets (runAs [] _ _)      ()
  run-meets calmAs              ()
  run-meets (noteAs _ _ _)      ()
  run-meets (subAs _ _ _)       ()
  run-meets (burstAs _ _ _)     ()

  -- The agenda's first call an `of` at `p`: the run is at `p`.
  run-at : ∀ {h} {t : Sub h [] R} {q c bs} (ca : CtlAs t q c bs) {Δ A p i xs} {π : Path t (ofˢ {Δ = Δ} {A} p i xs)}
         → firstCall ca ≡ just (emitC π) → All (Placedᴬ t) (agenda t ca) → q ≡ p
  run-at (runAs (_ ∷ _) _ _) refl (pl ∷ _) = pl
  run-at (runAs [] _ _)      ()
  run-at calmAs              ()
  run-at (noteAs _ _ _)      ()
  run-at (subAs _ _ _)       ()
  run-at (burstAs _ _ _)     ()

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

  -- An `of` the ghost does not hold: the ghost alike, the load lighter.
  emit-unseen : ∀ {g m} (cr : Carried g m) {Δ A p i x xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i (x ∷ xs)))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → opened (Conf.heap (Mach.conf m)) true π ≡ true
              → seen (Conf.heap (Mach.conf m)) π ≡ false → Hops cr
  emit-unseen cr π fc op sn eq with emit-void cr π fc op sn eq
  ... | g″ , m₀ , path , cr₀ , ag , lt = g″ , m₀ , path , carried cr₀ , lowered ag (inj₁ lt)

  -- An `of`'s next value climbs the observers above it: to the root's
  -- note, past a skip (a connect's feed, a lane admitted), or to a
  -- takeWhile's end.
  emit-onward : ∀ {g m} (cr : Carried g m) {Δ A p i xs} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i xs))
              → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-onward cr {xs = []} π fc = emit-last cr π fc
  emit-onward {m = m} cr {xs = x ∷ xs} π fc with opened (Conf.heap (Mach.conf m)) true π in op | seen (Conf.heap (Mach.conf m)) π in sn
  ... | false | _     = emit-shut cr π fc op
  ... | true  | false = emit-unseen cr π fc op sn
  ... | true  | true  = λ eq → soar (carried cr) (emit-open cr π fc op sn eq)

  -- CODE RUNS SILENTLY ON TO A RE-ENTRY STATE: a subscription begun, the
  -- agenda's first call, or the agenda done and its stack resumed: a
  -- frame's rest, a scope's continuation at the position it puts back, a
  -- burst held, the turn.  The ghost alike, the control's work less.
  run-onward : ∀ {g m w act K} {σ : w ⊑ Conf.world (Mach.conf m)} (cr : Carried g m) → Conf.ctl (Mach.conf m) ≡ run {B = ⊤} act σ K
             → Hops cr
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs _ _ _ } refl eq = sub-onward cr refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (emitC π ∷ _) _ _ } refl eq = emit-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (kontC π ∷ _) _ _ } refl eq = kont-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take1C π ∷ _) _ _ } refl eq = take1-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (take2C π ∷ _) _ _ } refl eq = cut-onward cr (takeSite π) refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (bodyC π ∷ _) _ _ } refl eq = cut-onward cr (bodySite π) refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (feedC π ∷ _) _ _ } refl eq = feed-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (finC π ∷ _) _ _ } refl eq = fin-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (srcC π ∷ _) _ _ } refl eq = src-onward cr π refl eq
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) bottomAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-move hp calmAs refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (restAs ks e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-move hp (runAs ks e K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (backAs q ks qp e K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K″ ; meets = mt
        ; owned = owned-move hp (runAs ks e K″) refl refl refl ow ; kernels = kn ; meaning = mn
        ; queue = record { timed = Queue.timed qu ; joined = Queue.joined qu ; ordered = Queue.ordered qu
                         ; ahead = map (λ { (c , a) → c , <ᵖ-trans q p _ qp a }) (Queue.ahead qu) }
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = each-back qp (Carried.behind cr) })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (playsAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (playsAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (playsAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs (firesAs π) hᴷ K″) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = burstAs (firesAs π) hᴷ K″ ; meets = mt
        ; owned = owned-move hp (burstAs (firesAs π) hᴷ K″) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ ck ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl now) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₂ (refl , m<n⇒m<1+n ≤-refl))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs bottomᴴ bottomAs) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt
        ; owned = owned-move hp calmAs refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))
  run-onward {g} {mach ⟨ hp , p , _ ⟩ clk ts _ _ lg en mk}
    cr@record { tree = t ; ctlAs = runAs [] (done≗ refl) (reholdAs overAs restᴴ (restAs ks e K‴)) ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = refl ; running = rn } } refl refl =
    g , _ , then refl (then refl now)
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = runAs ks e K‴ ; meets = mt
        ; owned = owned-move hp (runAs ks e K‴) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = proj₂ (proj₂ ck) ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then refl (then refl now)) ; behind = Carried.behind cr })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (refl , inj₂ (refl , inj₂ (refl , inj₁ ≤-refl)))))

  -- Past a value recorded, the run runs the stepped ghost: the record's
  -- continuation is the agenda, about to run.
  note-onward : ∀ {g g′ m w a k K} {σ : w ⊑ Conf.world (Mach.conf m)} → Carried g m
              → Conf.ctl (Mach.conf m) ≡ asking {B = ⊤} (note a) k σ K → U.step g ≡ U.outˢ (Conf.pos (Mach.conf m)) a g′
              → ∀ {t q a′ m′} → step m ≡ value t q a′ m′ → Mirror g′ m′
  note-onward {g} {m = mach ⟨ hp , p , _ ⟩ clk ts bs td lg en mk}
    cr@record { tree = t ; ctlAs = noteAs ks ke K ; meets = g″ , pe , st″ ; owned = ow ; books = record { running = refl } } refl stp refl
    with trans (sym st″) stp
  ... | refl = _ , now , carried (record
        { sane = sane-out {g = g} (Carried.sane cr) stp
        ; placed = proj₂ (subst (Placedˢ []) stp (placed-after g (Carried.sane cr) (Carried.placed cr)))
        ; tree = t ; ctlAs = runAs ks ke K ; meets = pe
        ; owned = record { ofs = Owned.ofs ow ; plays = Owned.plays ow ; fires = Owned.fires ow ; begun = Owned.begun ow
                         ; ends = Owned.ends ow ; cuts = Owned.cuts ow ; feeds = Owned.feeds ow ; fins = Owned.fins ow ; bodies = Owned.bodies ow
                         ; placed = Owned.placed ow }
        ; kernels = Carried.kernels cr ; meaning = Carried.meaning cr ; queue = Carried.queue cr
        ; books = record { fresh = Books.fresh (Carried.books cr) ; clocked = Books.clocked (Carried.books cr)
                         ; paidUp = Books.paidUp (Carried.books cr) ; running = refl } 
        ; sorted = sorted-value (Carried.sorted cr) refl ; behind = Carried.behind cr })

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
    cr@record { tree = t ; ctlAs = calmAs ; meets = mt ; owned = ow ; kernels = kn ; meaning = mn ; queue = q
              ; books = record { fresh = fs ; paidUp = refl ; running = rn } } refl refl refl
    with spent? hp (Timer.handle tm) in sp
  ... | true =
    g , mach ⟨ hp , p , held σ bottom ⟩ (Timer.due tm) ts [] [] lg en mk , then (drop-spent tm sp) now
    , carried (record
        { sane = Carried.sane cr ; placed = Carried.placed cr ; tree = t ; ctlAs = calmAs ; meets = mt ; owned = ow
        ; kernels = kn ; meaning = mn
        ; queue = record { timed = timed-spent {H = hp} sp (Queue.timed q) ; joined = Queue.joined q
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = fs ; clocked = tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl (then (drop-spent tm sp) now) ; behind = Carried.behind cr })
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
        ; owned = owned-pop hp {t = t} π ow
        ; kernels = record { holds = holds-plant hp {t = t} π v refl (λ h → h) (Kernels.holds kn)
                           ; gated = gated-plant hp {t = t} π v (λ _ → lift (λ _ → refl)) (λ s → s) (Kernels.gated kn) }
        ; meaning = record { fed = fed-plant hp {t = t} π v (λ _ f → f) _ (Meaning.fed mn) }
        ; queue = record { timed = timed-pop hp {t = t} π (Queue.timed q) (Queue.ordered q) fs
                         ; joined = subst₂ (At.Joined hp) (sym (subjects-plant {t = t} π v refl)) (sym (joiners-plant {t = t} π v (λ _ → refl) _)) (Queue.joined q)
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = t} π v refl)) fs ; clocked = refl , tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl now ; behind = behind-fire cr π })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (pend-plant {t = t} π v refl , inj₂ (takes-plant {t = t} π v refl , inj₁ ≤-refl))))
    where v = coldˢ sk hd (fired τ e (at u x fr))

  -- The stepper is the meaning, as sets.
