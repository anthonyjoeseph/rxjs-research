{-# OPTIONS --guardedness #-}

-- THE CLIMB: a value carried from its emitter up a path, each
-- operator's callback one rise; and the close, its teardown.
module adequacy.Climbs where

open import Data.List using (List; []; _∷_; _++_; [_]; null; length) renaming (map to mapList)
open import Data.List.Properties using (++-assoc)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any as Any
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; m<n⇒m<1+n; +-monoʳ-<; +-monoˡ-<)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map) renaming (lookup to lookupᴬ)
open import Data.List.Relation.Unary.All.Properties using () renaming (++⁺ to all-++⁺)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; _∷_)
open import Data.List.Relation.Unary.Linked using (Linked; _∷_; tail)
open import Data.List.Membership.Propositional using () renaming (_∈_ to _∈ᴸ_)
open import Level using (lift; lower)
open import Data.Maybe using (Maybe; just; nothing; is-nothing) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ; zero; suc; pred; _<_; _≤_; _≡ᵇ_; _<ᵇ_)
open import Data.Product using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂)

open import denotation.MonotonicList using (Events∞; skip; Pos; Timeline; Agree; agree-refl; at; last; ix; tick; _<ᵖ_; <ᵖ-tick; <ᵖ-trans; <ᵖ-below)
import denotation.Unfold as U
open import denotation.MonotonicList using () renaming (sub to subᴾ)
open import adequacy.Sorted using (module Sorting)
open import operation.Machine using (module Machine)
open import adequacy.Strong using (module Strongly)
open import adequacy.Moves using (module Moving)
open import adequacy.Torn using (module Tearing)
open import adequacy.Unsub using (module Unsubbing)
open import adequacy.Seq using (module Sequencing)
open import adequacy.Sane using (Sane; sane-out)
open import adequacy.Placed using (Placed)
open import adequacy.Stepper using (placed-after; Placedˢ)
open import denotation.Denote using (⟦_⟧)
import Tree as T
open import operation.PureObservable using (Out; note; Pureᴾ; module Pure)
open import operation.AbstractObservable using (module Heap; module Run; fifo; list) renaming (module Machine to Shared)
open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import adequacy.Ghost using (module Ghosting)
open import adequacy.Lift using (module Lifting)
open import adequacy.Frame using (module Framing)
open import adequacy.Grow using (module Growing)
open import adequacy.Restage using (module Restaging)
open import adequacy.Local using (module Locality)

open Events∞

module Ascending (R : Set) where
  open Machine R using (Mach; mach; Playing; Step; silent; value; complete; step; Read; feed; Todo; wkPlaying; wkTodo)
  open Shared Timeline (Out R) using (Conf; Heapᴹ; Stack; ⟨_,_,_⟩; held; run; asking; bottom; push; back; rest; spent?; store; Callbacks; cbs; look; wkVal) renaming (go to goᴵ)
  open Heap using (World; _⊑_; _⨾_; Handle; Sink; Quiet; wk∋; slot) renaming (same to same⊑)
  open Sorting R using (WellMach)
  open Run (Pureᴾ R) using (Ref; Act; writeRef; readRef; send; El; Observer; _>>ᴬ_; module Kit; module FlatKit; module Subject; under; done; wkAct; wkObs; compile; wkR; wkEl; Env; wkEnv)
  open Strongly R using (Strong; Carried; Books; carried; closing; Sub; pendingˢ; Name; names; CbRel; coldˢ; ofˢ; mapˢ; scanˢ; takeWhileˢ; flatMapˢ; connectˢ; deferˢ; Lane; here; module At; Queue; Kernels; Meaning; fired; Owned; Path; Spot; spot; done≗; Call; emitC; kontC; take1C; idle; feeding; finishing; take2C; bodyC; feedC; finC; srcC; taking; PathLanes; this-lane; next-lane; lane; in-map; in-scan; in-take; in-outer; in-lanes; in-source; in-body; in-defer; _⊕_; _⊕ᴸ_; Here; walk; walkLanes; top; _≗_; eff≗; readRef≗; writeRef≗; send≗; under≗; ≗-refl; Meets; Each; Heads; seen; ∧-split; module Canon) renaming (⟦_⟧ to ⟦_⟧ᶜ)
  open Strongly.Against R using (calmAs; noteAs; runAs; subAs; burstAs; firesAs; playsAs; overAs; bottomAs; restAs; backAs; reholdAs; bottomᴴ; restᴴ; BurstAs; StackAs; Ticked; CtlAs; agenda; bursts; begins; sources; stackJobs; stackBursts; burstSpots; SrcOf) renaming (Placed to Placedᴬ)
  open Pure R using (Timer; cascade; wkTimer)
  open Moving R using (takes; takesᴸ; stage; takes-plant; plant; plantᴸ; planted; plantedᴸ; waits; pendings-path; part-plant; pend-plant; names-plant; subjects-plant; joiners-plant; holds-plant; settled-plant; gated-plant; fed-plant; timed-pop; owned-pop; later; true≢false)
  open Tearing R using (fresh-path; takeSite; bodySite; look-store)
  open Unsubbing R using (_⇝_; ⇝-trans; now; then; ≗-trans; wk≗; wk-same; bind≗)
  open Sequencing R using (seq-assoc; seq-done)
  open Restaging R using (walk-planted; tick-ix0)
  open Ghosting R using (module Far; module Calling; residual; _⊏_; begun; sorted-⇝; sorted-value; Mirror; agrees; Load; _≼_; load; ⊏-≼; loadOf; lowered; showing; Hopped; Hops; firstCall; owned-move; Lifts; lifts-here; lifts-map; lifts-scan; lifts-take; lifts-outer; OuterFirst; LaneFirst; PoolBehind; lifts-lanes; lifts-source; lifts-body; lifts-shut; lifts-defer; LiftsLane; lifts-this; lifts-next; lifts-split; Far; Off; far-apart; Clear; clear-zip; clear-each; walk-⊕; One; one-map; one-scan; one-take; one-outer; one-lanes; one-source; one-body; one-defer; OneLane; one-this; one-next; whole; snoc; view; height; heightL; one-lower; opened; openedL; Calling; Signal; sends; closes; recall; relevel; Rises; rises; Called; landed; rose; passed; Past; Aloft; aloft; hop-sorted; each-back; hopped-pre)
  open Lifting R using (sub-onward; emit-shut; emit-void; emit-run; spread-past; behind-fire; kont-onward; feed-onward; src-onward; burst-poll; burst-play; cut-onward; heads-lift)
  open Locality R using (stored-at)
  open Growing R using (wkTree; wkLanes; wkPath)
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
    (U.mapᶜ f c′ , cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) pv , S , Lρ , sg)
  call-map {m₁ = m₁} {f = f} ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg with lifts-split ρ (in-map here) L
  ...   | _ , lifts-map lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-map here) top) (Calling.code cl))
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.mapᶜ f)) gn , S , Lρ , sg)

  -- A signal through a defer, as it is.
  call-defer : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {k} {u : Sub (Conf.world (Mach.conf m₁)) Δ A}
               (ρ : Path T (deferˢ k u)) {sg : Signal T A} → Calling g ℓ m₁ (ρ ⊕ in-defer here) sg → Calling g ℓ m₁ ρ sg
  call-defer ρ {sends y} cl with Calling.lifted cl
  ... | c′ , pv , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (c′ , pv , S , Lρ , sg)
  call-defer ρ {closes ks} cl with Calling.lifted cl
  ... | gn , S , L , sg with lifts-split ρ (in-defer here) L
  ...   | _ , lifts-defer lifts-here , Lρ = recall cl refl
    (subst (λ W → Calling.act cl ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-defer here) top) (Calling.code cl))
    (gn , S , Lρ , sg)

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
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg))
  ...   | _ , lifts-shut pt refl _ lifts-here , Lρ = rose now (one-lower ρ one-body) (recall cl {sg′ = sends y} refl
    (subst (λ W → Calling.act cl ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-body here) top) (Calling.code cl))
    (_ , cong₂ (At.connected (Conf.heap (Mach.conf m₁)) rp e rt) pt pv , S , Lρ , sg))
  call-body st {m₁ = m₁} {T = T} {Sj} {c} {b} {kb} {k} {fd} {e} {rp} {rt} {t = t} {u} ρ {closes ks}
    record { sane = sn ; placed = pl ; ctl = cx ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
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
      ; sorted = so ; behind = bh ; kept = kp })

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
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rises {sg′ = sends y} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (≗-trans (wk-same _) (pass-code lv py))
      ; stack = sk
      ; lifted = U.takeWhileᶜ i p c′ , take-part hp {i = i} {p = p} {c = c} {k = k} {u = u} lv pv , S , subst (λ s → Lifts hp ρ s S) (cong (U.taking i p q y c′) py) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = inj₁ refl })

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
    v  = takeWhileˢ i p c k (Strongly.ending q c′) u
    T′ = plant ρ v

    postulate
      end-stack   : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
      end-ticked  : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (end-stack sk)
      end-owned   : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (e : act ≗ ⟦ take1C (planted ρ v) ∷ [] ⟧ᶜ)
              → At.val H (Kit.live c) ≡ true → Owned H T (runAs [] (≗-refl _) sk) → Owned H T′ (runAs (take1C (planted ρ v) ∷ []) e (end-stack sk))
      end-kernels : Kernels H T → Kernels H T′
      end-meaning : Meaning H T → Meaning H T′
      end-queue   : ∀ {clk ts} → Queue H q clk ts T → Queue H q clk ts T′
      end-behind  : Each H (Heads q) T → Each H (Heads q) T′
      out-owned   : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {N : Act h ⊤} (sk : StackAs T q ϑ K bs) (e : wkAct same⊑ N ≗ ⟦ take1C (planted ρ v) ∷ [] ⟧ᶜ)
              → At.val H (Kit.live c) ≡ true → Owned H T (runAs [] (≗-refl _) sk)
              → Owned H T′ (runAs [] (≗-refl _) (backAs q (take1C (planted ρ v) ∷ []) (<ᵖ-below q {ix 0} []) e (end-stack sk)))
      out-queue   : ∀ {clk ts} → Queue H q clk ts T → Queue H (q ++ [ ix 0 ]) clk ts T′
      out-behind  : Each H (Heads q) T → Each H (Heads (q ++ [ ix 0 ])) T′
      end-ghost : ∀ {g S} → Sane [] g → Placed g [] → At.val H (Kit.live c) ≡ true → At.part H u ≡ just c′
              → Lifts H ρ (U.endˢ (q ++ [ last ])) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ [] × (∀ n → Agree n (residual g) (residual g″))

  -- A value an exclusive takeWhile fails on: its guard read, the take
  -- ended, its completion the agenda's call.
  take-end : ∀ {g ℓ m₁ Δ A} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {p c k}
             {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (takeWhileˢ false p c k taking u)) {y : A} → p y ≡ false
           → Calling g ℓ m₁ (ρ ⊕ in-take here) (sends y)
           → Σ (U.Node [] R) λ g″ → Σ Mach λ m₀ → m₁ ⇝ m₀ × Σ (Carried g″ m₀) λ cr
             → (∀ n → Agree n (residual g) (residual g″)) × load m₀ (Carried.tree cr) ⊏ load m₁ T
  take-end {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {p = p} {c = c} {k = k} {u = u} ρ {y} py
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f
    with Ended.end-ghost hp ρ q c′ sn pl lv pv (subst (λ s → Lifts hp ρ s S) (cong (U.taking false p q y c′) py) Lρ) sg
  ...   | g″ , pg , sn″ , pl″ , ag =
    g″ , _ , then refl now
    , record
        { sane = sn″ ; placed = pl″ ; tree = Ended.T′ hp ρ q c′
        ; ctlAs = runAs (take1C (planted ρ v) ∷ []) e (Ended.end-stack hp ρ q c′ sk)
        ; meets = pg
        ; owned = Ended.end-owned hp ρ q c′ sk e lv ow
        ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.end-queue hp ρ q c′ qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind = Ended.end-behind hp ρ q c′ bh }
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
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh ; kept = kp }
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
      ; owned = Ended.out-owned hp ρ q c′ sk e lv ow
      ; kernels = Ended.end-kernels hp ρ q c′ kn ; meaning = Ended.end-meaning hp ρ q c′ mn ; queue = Ended.out-queue hp ρ q c′ qu
      ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                       ; clocked = trans (proj₁ ck) (sym (tick-ix0 q)) , proj₁ ck , Ended.end-ticked hp ρ q c′ clk sk (proj₂ ck)
                       ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl path) ; behind = Ended.out-behind hp ρ q c′ bh
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
           ; behind = bh ; kept = kp }
    with lifts-split ρ (in-take here) L | subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-take here) top) cd
  ... | _ , lifts-take lv lifts-here , Lρ | readRef≗ refl f =
    rose {sg′ = closes ks} (then refl now) (one-lower ρ one-take) (record
      { sane = sn ; placed = pl ; ctl = refl
      ; code = ≗-trans (f same⊑ _) (bind≗ (≗-trans (wk-same _) (open-code lv)) λ _ → wk-same _)
      ; stack = sk
      ; lifted = gone-take hp {i = i} {p = p} {c = c} {k = k} {u = u} lv gn , S , Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl now) ; behind = bh ; kept = kp })

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

  -- A value through a scan: its cell read and written, the accumulated
  -- value one operator up, the tree's load as it was.
  scan-pass : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {f : B → A → B} {r}
              {u : Sub (Conf.world (Mach.conf m₁)) Δ A} (ρ : Path T (scanˢ f r u)) {y : A}
            → Calling g ℓ m₁ (ρ ⊕ in-scan here) (sends y) → Rises g (load m₁ T) m₁ (ρ ⊕ in-scan here)
  scan-pass {g} {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {f = f} {r = r} {u = u} ρ {y}
    cl@record { sane = sn ; placed = pl ; ϑ = ϑ ; K = K ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; kept = kp }
    with lifts-split ρ (in-scan here) L | subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-scan here) top) cd
  ... | _ , lifts-scan lifts-here , Lρ | readRef≗ refl k =
    rises {sg′ = sends z} (then refl (proj₂ (proj₂ wr))) (one-lower ρ one-scan) (record
      { sane = sn ; placed = pl ; ctl = refl ; code = proj₁ (proj₂ wr) ; stack = sk
      ; lifted = U.scanᶜ f z c′ , scan-part hp {f = f} {r = r} {u = u} (fresh-path ρ fs) z pv , S , scan-lifts hp ρ fs z Lρ , sg
      ; owned = scan-owned hp ρ fs z ow ; kernels = scan-kernels hp ρ fs z kn ; meaning = scan-meaning hp ρ fs z mn ; queue = scan-queue hp ρ fs z qu
      ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (then refl (proj₂ (proj₂ wr))) ; behind = scan-behind ρ cl ; kept = inj₁ refl })
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
    (cong (At.mapᴹ (Conf.heap (Mach.conf m₁)) (U.scanᶜ f (At.val (Conf.heap (Mach.conf m₁)) r))) gn , S , Lρ , sg))

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

  -- A FLATMAP'S POOL RESTAGED: the node at the path's end with a new
  -- pool, the calls, the stack and every field carried across.
  module Restaged {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) (pl′ : U.Node Δ B) where
    v  = flatMapˢ op f fl oc k r pl′ u ls
    T′ = plant ρ v

    postulate
      pool-calls   : (ks : List (Call T)) → Σ (List (Call T′)) λ ks′ → ⟦ ks ⟧ᶜ ≗ ⟦ ks′ ⟧ᶜ
      pool-stack   : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
      pool-ticked  : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (pool-stack sk)
      pool-owned   : ∀ {w q bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (ks : List (Call T))
                     (e : act ≗ ⟦ proj₁ (pool-calls ks) ⟧ᶜ)
                   → Owned H T (runAs ks (≗-refl _) sk) → Owned H T′ (runAs (proj₁ (pool-calls ks)) e (pool-stack sk))
      pool-kernels : Kernels H T → Kernels H T′
      pool-meaning : Meaning H T → Meaning H T′
      pool-queue   : ∀ {q clk ts} → Queue H q clk ts T → Queue H q clk ts T′
      pool-behind  : ∀ {q} → Each H (Heads q) T → Each H (Heads q) T′

  -- A FLATMAP'S OUTER ENDED: its done flag written, nothing else of the
  -- heap or the tree moved; settled, the count read as the live lanes.
  module Settles {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {u : Sub h Δ A} {ls : List (Lane h Δ B)}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl u ls)) where
    H′ = store H (FlatKit.Flat.outerDone fl) (lift true)

    done-read : At.val H′ (FlatKit.Flat.outerDone fl) ≡ true
    done-read = cong lower (stored-at H (FlatKit.Flat.outerDone fl) (lift true))

    postulate
      sd-active    : At.val H′ (FlatKit.Flat.active fl) ≡ At.val H (FlatKit.Flat.active fl)
      sd-fifo      : At.val H′ (FlatKit.Flat.queue fl) ≡ At.val H (FlatKit.Flat.queue fl)
      sd-part      : ∀ {Δ′ A′} (v : Sub h Δ′ A′) → At.part H′ v ≡ At.part H v
      sd-lifts     : ∀ {Δ′ A′ Δ″ A″} {t : Sub h Δ′ A′} {v : Sub h Δ″ A″} {σ : Path t v} {s S} → Lifts H σ s S → Lifts H′ σ s S
      sd-owned     : ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
      sd-kernels   : Kernels H T → Kernels H′ T
      sd-meaning   : Meaning H T → Meaning H′ T
      sd-queue     : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
      sd-behind    : ∀ {q} → Each H (Heads q) T → Each H′ (Heads q) T
      active-lanes : Kernels H T → (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ≡ null (At.partLanes H ls)

    settle-eq : Kernels H T → ((At.val H′ (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val H′ (FlatKit.Flat.queue fl)))
                              ≡ (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl)))
    settle-eq kn = trans (cong (λ n → (n ≡ᵇ 0) ∧ null (At.val H′ (FlatKit.Flat.queue fl))) sd-active)
                   (trans (cong (λ qs → (At.val H (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null qs) sd-fifo)
                          (cong (λ x → x ∧ null (At.val H (FlatKit.Flat.queue fl))) (active-lanes kn)))

    -- Lanes or a queue left: the pool takes what the outer left running,
    -- the ghost past the outer's skip.
    postulate
      pool-ghost : ∀ (o₀ : U.Node Δ A) {g q S} → Sane [] g → Placed g [] → At.part H u ≡ nothing
                 → (null (At.partLanes H ls) ∧ null (At.val H (FlatKit.Flat.queue fl))) ≡ false
                 → OuterFirst {A = A} (U.endˢ q) (At.partLanes H ls) → PoolBehind pl (U.outerOf (just o₀)) (U.earliest (At.partLanes H ls))
                 → Lifts H ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) (At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl) S
                 → U.step g ≡ S
                 → Σ (U.Node [] R) λ g″ → At.part H′ (Restaged.T′ H′ ρ (U.unionᶜ pl (U.restᶜ o₀))) ≡ just g″ × Sane [] g″ × Placed g″ []
                   × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)

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
              ; behind = bh ; kept = kp }
    with lifts-split ρ (in-outer here) L
       | reads (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-outer here) top) cd)
  ... | _ , lifts-outer {o₀ = o₀} of pb lifts-here , Lρ | k₁ , f₁ , p₁
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
      ; lifted = trans (Settles.sd-part hp ρ (flatMapˢ op f fl oc k r po u ls)) (flat-gone hp {op = op} {f} {fl} {oc} {k} {r} {po} {u = u} {ls} gn (proj₁ nl) (proj₂ nl)) , S
               , Settles.sd-lifts hp ρ (subst₂ (λ ls′ qs′ → Lifts hp ρ (U.outerˢ op (λ a j → U.subscribe (f a) j) o₀ (U.endˢ q) ls′ qs′ po) S)
                                               (proj₁ nl) (proj₂ nl) Lρ) , sg
      ; owned = Settles.sd-owned hp ρ ow ; kernels = Settles.sd-kernels hp ρ kn ; meaning = Settles.sd-meaning hp ρ mn
      ; queue = Settles.sd-queue hp ρ qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Settles.sd-behind hp ρ bh ; kept = inj₁ refl }))
    where
      o    = Here.obs (walk ρ top)
      b    = (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl) ≡ᵇ 0) ∧ null (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl))
      path = ⇝-trans p₁ (⇝-trans p₂ (⇝-trans p₃ (⇝-trans p₄ p₅)))
      e₅   = ≗-trans (f₅ same⊑ (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))
               (bind≗ (wk-same (settledᵒ o (At.val (Settles.H′ hp ρ) (FlatKit.Flat.outerDone fl)) (At.val (Settles.H′ hp ρ) (FlatKit.Flat.active fl))
                                         (At.val (Settles.H′ hp ρ) (FlatKit.Flat.queue fl)))) λ _ → wk-same ⟦ ks ⟧ᶜ)
      nl   = nulls (At.partLanes hp ls) (At.val hp (FlatKit.Flat.queue fl)) (trans (sym (Settles.settle-eq hp ρ kn)) eq)
  ...           | false
    with Settles.pool-ghost hp ρ o₀ sn pd gn (trans (sym (Settles.settle-eq hp ρ kn)) eq) of pb Lρ sg
  ...             | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; tree = Restaged.T′ (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀))
        ; ctlAs = runAs (proj₁ (Restaged.pool-calls (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) ks)) ec (Restaged.pool-stack (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk)
        ; meets = pg
        ; owned = Restaged.pool-owned (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) sk ks ec (Settles.sd-owned hp ρ ow)
        ; kernels = Restaged.pool-kernels (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-kernels hp ρ kn)
        ; meaning = Restaged.pool-meaning (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-meaning hp ρ mn)
        ; queue = Restaged.pool-queue (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-queue hp ρ qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind = Restaged.pool-behind (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) (Settles.sd-behind hp ρ bh) })
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
                     (proj₂ (Restaged.pool-calls (Settles.H′ hp ρ) ρ (U.unionᶜ po (U.restᶜ o₀)) ks))

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

  -- A WORLD GROWN BY A LANE'S START: every name the old heap held where it
  -- was, weakened, but the count up and the cut listed; the cut live and
  -- holding nothing.
  record Grown {h v} (τ : h ⊑ v) (H : Heapᴹ h) (H′ : Heapᴹ v) {A} (fl : FlatKit.Flat A h) (c : Kit.Cut v) : Set₁ where
    field
      count   : At.val H′ (wkR τ (FlatKit.Flat.active fl)) ≡ suc (At.val H (FlatKit.Flat.active fl))
      listed  : At.val H′ (wkR τ (FlatKit.Flat.lanes fl)) ≡ c ∷ wkEl (list Kit.cutTy) τ (At.val H (FlatKit.Flat.lanes fl))
      live    : At.val H′ (Kit.live c) ≡ true
      unheld  : At.val H′ (Kit.held c) ≡ nothing
      cells   : ∀ {t} (x : Ref h t) → _≢_ {A = Name h} (_ , x) (_ , FlatKit.Flat.active fl) → _≢_ {A = Name h} (_ , x) (_ , FlatKit.Flat.lanes fl)
              → At.val H′ (wkR τ x) ≡ wkEl t τ (At.val H x)
      slots   : ∀ {X} (s : Sink h X) → CbRel (cbs H′ (wk∋ τ s)) (wkVal (slot X) τ (cbs H s))
      stashes : ∀ (u : Quiet h) → look H′ (wk∋ τ u) ≗ wkAct τ (look H u)
      handles : ∀ (hd : Handle h) → At.spentʰ H′ (wk∋ τ hd) ≡ At.spentʰ H hd

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

    -- A lane begins off the root: an outer's value is sent under a label.
    begin-deep : ∀ {g ℓ h} {H : Heapᴹ h} {q w} {ϑ : w ⊑ h} {K : Stack w ⊤} {clk ts bs td lg en mk} {a : Act h ⊤} {T : Sub h [] R} {Δ A B op f fl oc k r pl}
                   {t : Sub h Δ A} {ls : List (Lane h Δ B)} {ρ : Path T (flatMapˢ op f fl oc k r pl t ls)} {y : A} {pl′}
               → Begins g ℓ (mach ⟨ H , q , run a ϑ K ⟩ clk ts bs td lg en mk) ρ y pl′ → q ≢ []

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

    π′ : Path T′ (pendingˢ (f y) (q ++ [ ix 1 ]))
    π′ = planted (wkPath grow ρ) v′ ⊕ in-lanes (this-lane here)

    postulate
      bg-ghost : ∀ {g S} → Sane [] g → Placed g []
               → Lifts H ρ (U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op (λ a j → U.subscribe (f a) j) (At.part H t)
                             (U.subscribe (f y) (q ++ [ ix 1 ]) ∷ At.partLanes H ls) (At.val H (FlatKit.Flat.queue fl)) pl′)) S
               → U.step g ≡ S
               → Σ (U.Node [] R) λ g″ → At.part heap′ T′ ≡ just g″ × Sane [] g″ × Placed g″ []
                 × Σ Pos λ k′ → Σ (Events∞ R) λ r′ → (∀ n → Agree n (residual g) (skip k′ r′)) × Past (Events∞.force r′) (residual g″)
      bg-code  : Σ World λ u → Σ (Env Δ u) λ E′ → Σ (u ⊑ v) λ υ → wkEnv υ E′ ≡ Here.env (walk π′ top)
                 × act′ ≗ compile (f y) E′ υ (Here.obs (walk π′ top)) (Here.kont (walk π′ top))
      bg-stack : StackAs T q ϑ K bs → StackAs T′ q ϑ′ K bs′

    stk′ : StackAs T q ϑ K bs → StackAs T′ (q ++ [ ix 1 ]) same⊑ (push (back q back′) ϑ′ K) bs′
    stk′ sk = backAs q [] (<ᵖ-below q []) (≗-trans (wk-same back′) rests′) (bg-stack sk)

    postulate
      -- The new lane sits in a pool, never under a connect's source.
      bg-alone : (sk : StackAs T q ϑ K bs) → All (λ j → ¬ SrcOf T′ π′ (proj₂ j)) (stackJobs T′ (stk′ sk))

    ca′ : StackAs T q ϑ K bs → CtlAs T′ (q ++ [ ix 1 ]) (run act′ same⊑ (push (back q back′) ϑ′ K)) bs′
    ca′ sk = subAs π′ bg-code (stk′ sk) (bg-alone sk)

    postulate
      bg-ticked  : (sk : StackAs T q ϑ K bs) → Ticked T clk sk → Ticked T′ clk (bg-stack sk)
      bg-owned   : (sk : StackAs T q ϑ K bs) → Owned H T (runAs [] (≗-refl _) sk) → Owned heap′ T′ (ca′ sk)
      bg-kernels : Kernels H T → Kernels heap′ T′
      bg-meaning : Meaning H T → Meaning heap′ T′
      bg-queue   : Queue H q clk ts T → Queue heap′ (q ++ [ ix 1 ]) clk ts′ T′
      bg-behind  : Each H (Heads q) T → Each heap′ (Heads (q ++ [ ix 1 ])) T′
      bg-fresh   : AllPairs _≢_ (names T) → AllPairs _≢_ (names T′)

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
             ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh }
    with begin-path b
  ... | sr with Begun.bg-ghost sr pl′ sn pd L sg
  ...   | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    g″ , _ , Started.runs sr
    , carried (record
      { sane = sn″ ; placed = pd″ ; tree = Begun.T′ sr pl′ ; ctlAs = Begun.ca′ sr pl′ sk ; meets = pg
      ; owned = Begun.bg-owned sr pl′ sk ow ; kernels = Begun.bg-kernels sr pl′ kn ; meaning = Begun.bg-meaning sr pl′ mn
      ; queue = subst (λ ts″ → Queue (Started.heap′ sr) (q ++ [ ix 1 ]) clk ts″ (Begun.T′ sr pl′)) refl (Begun.bg-queue sr pl′ qu)
      ; books = record { fresh = Begun.bg-fresh sr pl′ fs
                       ; clocked = trans (proj₁ ck) (sym (tick-under q 1 (begin-deep b))) , proj₁ ck , Begun.bg-ticked sr pl′ sk (proj₂ ck)
                       ; paidUp = trans (Started.todo′ sr) (cong (mapList (wkTodo (Started.grow sr))) pu) ; running = rn }
      ; sorted = sorted-⇝ so (Started.runs sr) ; behind = Begun.bg-behind sr pl′ bh })
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
              ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; kept = kp } rm p c
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
      ; sorted = sorted-⇝ so p ; behind = bh })
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

  -- A lane's parts, the first apart.
  lanes-one : ∀ {h} (H : Heapᴹ h) {Δ B} (l : Lane h Δ B) ls → At.partLanes H (l ∷ ls) ≡ At.partLanes H (l ∷ []) ++ At.partLanes H ls
  lanes-one H (lane c k s) ls with At.val H (Kit.live c) | At.part H s
  ... | true  | just _  = refl
  ... | true  | nothing = refl
  ... | false | _       = refl

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

  -- A value out of a lane: its guard read open, one operator up, the
  -- flatMap showing the lane past it.
  climb-lanes : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
              {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
              (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (πL : PathLanes ls u) → OneLane πL → ∀ {y : B}
            → Calling g (loadOf st) m₁ (ρ ⊕ in-lanes πL) (sends y) → Called st m₁ (ρ ⊕ in-lanes πL)
  climb-lanes st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {op = op} {f} {fl} {oc} {k} {r} {po} {t = t} {ls} ρ πL o {y}
    cl@record { sane = sn ; placed = pd ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so ; behind = bh ; kept = kp }
    with lifts-split ρ (in-lanes πL) L
       | reads (subst (λ W → _ ≗ Observer.next W y) (trans (cong Here.obs (walk-⊕ ρ (in-lanes πL) top)) (walk-lane o op f fl (walk ρ top))) cd)
  ... | _ , lifts-lanes {bs = bs′} {l = l} {S = S₁} {as = as′} LL _ _ _ , Lρ | k₁ , f₁ , p₁ =
    rise kp (rises {sg′ = sends y} p₁ (one-lower ρ (one-lanes o)) (record
      { sane = sn ; placed = pd ; ctl = refl
      ; code = ≗-trans (f₁ same⊑ (At.val hp (Kit.live (laneOf o))))
                 (≗-trans (wk-same (Kit.when (At.val hp (Kit.live (laneOf o))) (Observer.next (wkObs same⊑ (Here.obs (walk ρ top))) y)))
                   (≗-trans (open-code (lane-live o LL)) (wk-same (Observer.next (Here.obs (walk ρ top)) y))))
      ; stack = sk
      ; lifted = _ , trans (cong (λ ls′ → At.merged hp op (λ a j → U.subscribe (f a) j) (At.part hp t) ls′ (At.val hp (FlatKit.Flat.queue fl)) po)
                                 (lanes-at hp o LL pv))
                           (merged-on hp op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ c′ as′ (At.val hp (FlatKit.Flat.queue fl)) po)
                 , S , subst (λ S′ → Lifts hp ρ (U.laneˢ op (λ a j → U.subscribe (f a) j) (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S)
                             (lane-step o LL) Lρ , sg
      ; owned = ow ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = sorted-⇝ so p₁ ; behind = bh ; kept = inj₁ refl }))


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

  -- A LANE ENDED AND ITS SLOT FREED: its cut dropped and the count down,
  -- nothing else of the heap or the tree moved.  Parts hold only with
  -- the lane's own part gone: a live lane's part is its flatMap's.
  module Freed {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B}
               (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) where
    H′ = freed H (laneOf o) fl

    postulate
      fr-part    : At.part H u ≡ nothing → ∀ {Δ′ A′} (v : Sub h Δ′ A′) → At.part H′ v ≡ At.part H v
      fr-lanes   : ∀ {s bs S as} → LiftsLane H πL s bs S as → At.part H u ≡ nothing → At.partLanes H′ ls ≡ bs ++ as
      fr-lifts   : ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
      fr-owned   : ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
      fr-kernels : Kernels H T → Kernels H′ T
      fr-meaning : Meaning H T → Meaning H′ T
      fr-queue   : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
      fr-behind  : ∀ {q} → Each H (Heads q) T → Each H′ (Heads q) T
      fr-opened  : ∀ b → opened (freed H (laneOf o) fl) b ρ ≡ opened H b ρ

  -- A FLATMAP'S QUEUE WRITTEN: its own cell, read by its node alone;
  -- its children's parts and everything above it as they were.
  module Dequeued {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)}
                  (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) (ys : List A) where
    H′ = store H (FlatKit.Flat.queue fl) (lift ys)

    postulate
      dq-part    : At.part H′ t ≡ At.part H t
      dq-lanes   : At.partLanes H′ ls ≡ At.partLanes H ls
      dq-opened  : ∀ b → opened (store H (FlatKit.Flat.queue fl) (lift ys)) b ρ ≡ opened H b ρ
      dq-lifts   : ∀ {s S} → Lifts H ρ s S → Lifts H′ ρ s S
      dq-owned   : ∀ {p ctl bs} {ca : CtlAs T p ctl bs} → Owned H T ca → Owned H′ T ca
      dq-kernels : Kernels H T → Kernels H′ T
      dq-meaning : Meaning H T → Meaning H′ T
      dq-queue   : ∀ {q clk ts} → Queue H q clk ts T → Queue H′ q clk ts T
      dq-behind  : ∀ {q} → Each H (Heads q) T → Each H′ (Heads q) T

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

  -- A lane's end with nothing beside it: the flatMap's own end.
  lane-end : ∀ {Γ A B} op (g : A → Pos → U.Node Γ B) {o bs as qs} l c pl → o ≡ nothing → bs ≡ [] → as ≡ [] → qs ≡ []
           → U.laneˢ op g o bs l (U.endˢ c) as qs pl ≡ U.endˢ c
  lane-end op g l c pl refl refl refl refl = refl

  postulate
    -- A freed slot's settle tests what the ghost's lane end tests: the
    -- done flag, the outer's part gone; the count, the lanes beside it.
    --
    -- Not a fact of the kernels: an outer's part is gone before its done
    -- flag is written, while its own end climbs to `close-outer`.  No
    -- lane ends in between, and no field of the call says so.
    lane-settles : ∀ {g ℓ m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {op f fl oc k r pl}
                   {t : Sub (Conf.world (Mach.conf m₁)) Δ A} {ls : List (Lane (Conf.world (Mach.conf m₁)) Δ B)} {u : Sub (Conf.world (Mach.conf m₁)) Δ B}
                   (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL) {ks}
                 → Calling g ℓ m₁ (ρ ⊕ in-lanes πL) (closes ks)
                 → ∀ {s bs S as} → LiftsLane (Conf.heap (Mach.conf m₁)) πL s bs S as
                 → settleᵇ (freed (Conf.heap (Mach.conf m₁)) (laneOf o) fl) fl
                   ≡ settledᵍ (At.part (Conf.heap (Mach.conf m₁)) t) bs as (At.val (Conf.heap (Mach.conf m₁)) (FlatKit.Flat.queue fl))

    -- A freed slot settling short of the end, the outer or a lane left:
    -- the pool takes the lane's rest, the ghost past the lane's skip.
    lane-ghost : ∀ {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B op f fl oc k r pl} {t : Sub h Δ A} {ls : List (Lane h Δ B)} {u : Sub h Δ B}
                 (ρ : Path T (flatMapˢ op f fl oc k r pl t ls)) {πL : PathLanes ls u} (o : OneLane πL)
               → ∀ {g q S bs l S₁ as j} → Sane [] g → Placed g [] → At.part H u ≡ nothing
               → LiftsLane H πL (U.endˢ q) bs S₁ as
               → settledᵍ (At.part H t) bs as (At.val H (FlatKit.Flat.queue fl)) ≡ false
               → U.earliest (bs ++ l ∷ as) ≡ U.found j bs l S₁ as → LaneFirst (At.part H t) j
               → PoolBehind pl (U.outerOf (At.part H t)) (U.found j bs l S₁ as)
               → Lifts H ρ (U.laneˢ op (λ a i → U.subscribe (f a) i) (At.part H t) bs l S₁ as (At.val H (FlatKit.Flat.queue fl)) pl) S
               → U.step g ≡ S
               → Σ (U.Node [] R) λ g″ → At.part (freed H (laneOf o) fl) (Restaged.T′ (freed H (laneOf o) fl) ρ (U.unionᶜ pl (U.restᶜ l))) ≡ just g″
                 × Sane [] g″ × Placed g″ []
                 × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)

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
    cl@record { sane = sn ; placed = pd ; ctl = refl ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
              ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
              ; behind = bh ; kept = kp } eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L | reads {hp = freed hp (laneOf o) fl} ea
  ... | _ , lifts-lanes {bs = bs′} {l = l} {as = as′} LL ee lf pb , Lρ | k₁ , f₁ , p₁
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
      ; lifted = flat-gone H₂ {op = op} {f} {fl} {oc} {k} {r} {po} {u = t} {ls} (trans (Freed.fr-part hp ρ o gn t) eo)
                           (trans (Freed.fr-lanes hp ρ o LL gn) (cong₂ _++_ ebs eas)) eq₀
               , S , Freed.fr-lifts hp ρ o (subst (λ s′ → Lifts hp ρ s′ S) (lane-end op G l q po eo ebs eas eqs)
                                              (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S)
                                                     (lane-step o LL) Lρ)) , sg
      ; owned = owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o ow)
      ; kernels = Freed.fr-kernels hp ρ o kn ; meaning = Freed.fr-meaning hp ρ o mn ; queue = Freed.fr-queue hp ρ o qu
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so path ; behind = Freed.fr-behind hp ρ o bh ; kept = inj₁ refl }))
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
    with lane-ghost hp ρ o sn pd gn LL (trans (sym (lane-settles ρ o cl LL)) eq) ee lf pb Lρ sg
  ...         | g″ , pg , sn″ , pd″ , k″ , r″ , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pd″ ; tree = Restaged.T′ H₂ ρ pl′
        ; ctlAs = runAs (proj₁ (Restaged.pool-calls H₂ ρ pl′ [])) ec (Restaged.pool-stack H₂ ρ pl′ stk)
        ; meets = pg
        ; owned = Restaged.pool-owned H₂ ρ pl′ stk [] ec (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o ow))
        ; kernels = Restaged.pool-kernels H₂ ρ pl′ (Freed.fr-kernels hp ρ o kn)
        ; meaning = Restaged.pool-meaning H₂ ρ pl′ (Freed.fr-meaning hp ρ o mn)
        ; queue = Restaged.pool-queue H₂ ρ pl′ (Freed.fr-queue hp ρ o qu)
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Restaged.pool-ticked H₂ ρ pl′ clk stk (proj₁ ck , proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind = Restaged.pool-behind H₂ ρ pl′ (Freed.fr-behind hp ρ o bh) })
      , passed ag pp)
    where
      H₂   = freed hp (laneOf o) fl
      O    = Here.obs (walk ρ top)
      pl′  = U.unionᶜ po (U.restᶜ l)
      v    = flatMapˢ op f fl oc k r pl′ t ls
      path = ⇝-trans p (⇝-trans p₁ (⇝-trans p₂ p₃))
      e₃   = ≗-trans (f₃ same⊑ (At.val H₂ (FlatKit.Flat.queue fl)))
               (wk-same (settledᵒ O (At.val H₂ (FlatKit.Flat.outerDone fl)) (At.val H₂ (FlatKit.Flat.active fl)) (At.val H₂ (FlatKit.Flat.queue fl))))
      stk  = restAs ks (≗-trans (wk-same n) eks) sk
      ec   = ≗-trans (≗-trans e₃ (shut-code eq)) (proj₂ (Restaged.pool-calls H₂ ρ pl′ []))

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
              ; behind = bh ; kept = kp } {y} {ys} eq₀ {n = n} p ea eks
    with lifts-split ρ (in-lanes πL) L | writes {hp = freed hp (laneOf o) fl} ea
  ... | _ , lifts-lanes {bs = bs′} {l = l} {as = as′} LL ee lf pb , Lρ | n′ , e′ , p′ =
    hopped-pre (⇝-trans p p′) (lane-begin st (record
      { sane = sn ; placed = pd ; ctl = refl ; code = e′
      ; opens = trans (Dequeued.dq-opened H₂ ρ ys true)
                  (trans (Freed.fr-opened hp ρ o true) (one-open hp o (trans (sym (opened-⊕ hp true ρ (in-lanes πL))) (calling-open (ρ ⊕ in-lanes πL) cl))))
      ; stack = stk
      ; lifted = S , L₇ , sg
      ; owned = Dequeued.dq-owned H₂ ρ ys (owned-move H₂ (runAs [] (≗-refl _) stk) refl refl refl (Freed.fr-owned hp ρ o ow))
      ; kernels = Dequeued.dq-kernels H₂ ρ ys (Freed.fr-kernels hp ρ o kn)
      ; meaning = Dequeued.dq-meaning H₂ ρ ys (Freed.fr-meaning hp ρ o mn)
      ; queue = Dequeued.dq-queue H₂ ρ ys (Freed.fr-queue hp ρ o qu)
      ; books = record { fresh = fs ; clocked = proj₁ ck , proj₁ ck , proj₂ ck ; paidUp = pu ; running = rn }
      ; sorted = sorted-⇝ so (⇝-trans p p′) ; behind = Dequeued.dq-behind H₂ ρ ys (Freed.fr-behind hp ρ o bh) }))
    where
      H₂  = freed hp (laneOf o) fl
      H₃  = Dequeued.H′ H₂ ρ ys
      G   = λ a j → U.subscribe (f a) j
      pl′ = U.unionᶜ po (U.restᶜ l)
      stk = restAs ks (≗-trans (wk-same n) eks) sk
      F   = λ (x : Maybe (U.Node _ _)) (zs : List (U.Node _ _)) (qs : List _) → U.skipˢ (q ++ [ ix 0 ]) (U.flatMapᶜ op G x (G y (q ++ [ ix 1 ]) ∷ zs) qs pl′)
      L₁  = subst (λ qs → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l (U.endˢ q) as′ qs po) S)
                  (trans (sym (queue-freed hp (laneOf o) fl)) eq₀)
                  (subst (λ S′ → Lifts hp ρ (U.laneˢ op G (At.part hp t) bs′ l S′ as′ (At.val hp (FlatKit.Flat.queue fl)) po) S) (lane-step o LL) Lρ)
      L₄  = Dequeued.dq-lifts H₂ ρ ys (Freed.fr-lifts hp ρ o L₁)
      L₅  = subst (λ x → Lifts H₃ ρ (F x (bs′ ++ as′) ys) S) (sym (trans (Dequeued.dq-part H₂ ρ ys) (Freed.fr-part hp ρ o gn t))) L₄
      L₆  = subst (λ zs → Lifts H₃ ρ (F (At.part H₃ t) zs ys) S) (sym (trans (Dequeued.dq-lanes H₂ ρ ys) (Freed.fr-lanes hp ρ o LL gn))) L₅
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

  -- A CONNECT FEEDING: the feed restaged from `idle` to the source's
  -- value at the run's position, owed to the subscribers the feed read,
  -- the ghost past the source's skip.
  module Feeds {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B Sj c b kb k rp e rt} {u : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
               (ρ : Path T (connectˢ Sj c b kb k idle rp e rt u bd)) (y : A) (q : Pos) where
    v  = connectˢ Sj c b kb k (feeding y q (At.val H (Subject.subscribers Sj))) rp e rt u bd
    T′ = plant ρ v

    postulate
      fed-stack   : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
      fed-ticked  : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (fed-stack sk)
      fed-owned   : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (e : act ≗ ⟦ feedC (planted ρ v) ∷ [] ⟧ᶜ)
              → Owned H T (runAs [] (≗-refl _) sk) → Owned H T′ (runAs (feedC (planted ρ v) ∷ []) e (fed-stack sk))
      fed-kernels : Kernels H T → Kernels H T′
      fed-meaning : Meaning H T → Meaning H T′
      fed-queue   : ∀ {clk ts} → Queue H q clk ts T → Queue H q clk ts T′
      fed-behind  : Each H (Heads q) T → Each H (Heads q) T′
      fed-ghost   : ∀ {g S c′} → Sane [] g → Placed g [] → At.part H u ≡ just c′
              → Lifts H (ρ ⊕ in-source here) (U.outˢ q y c′) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H T′ ≡ just g″ × Sane [] g″ × Placed g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)

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
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = c′ , pv , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh } | refl
    with subst (λ W → _ ≗ Observer.next (Here.obs W) y) (walk-⊕ ρ (in-source here) top) cd
  ... | readRef≗ refl f with Feeds.fed-ghost hp ρ y q sn pl pv L sg
  ...   | g″ , pg , sn″ , pl″ , k′ , r , ag , pp =
    landed (g″ , _ , then refl now
      , carried (record
        { sane = sn″ ; placed = pl″ ; tree = Feeds.T′ hp ρ y q
        ; ctlAs = runAs (feedC (planted ρ v) ∷ []) (≗-trans (f same⊑ ss) (seq-done _)) (Feeds.fed-stack hp ρ y q sk)
        ; meets = pg
        ; owned = Feeds.fed-owned hp ρ y q sk (≗-trans (f same⊑ ss) (seq-done _)) ow
        ; kernels = Feeds.fed-kernels hp ρ y q kn ; meaning = Feeds.fed-meaning hp ρ y q mn ; queue = Feeds.fed-queue hp ρ y q qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Feeds.fed-ticked hp ρ y q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so (then refl now) ; behind = Feeds.fed-behind hp ρ y q bh })
      , passed ag pp)
    where
      ss = At.val hp (Subject.subscribers Sj)
      v  = connectˢ Sj c b kb k (feeding y q ss) rp e rt u bd

  -- A CONNECT FINISHING: its subject closed, the feed restaged from `idle`
  -- to the source's end at the run's position, owed to the subscribers
  -- the feed read, ahead of the calls the end owed, the ghost past the
  -- source's skip.
  module Fins {h} (H : Heapᴹ h) {T : Sub h [] R} {Δ A B Sj c b kb k rp e rt} {u : Sub h Δ A} {bd : Sub h (A ∷ Δ) B}
              (ρ : Path T (connectˢ Sj c b kb k idle rp e rt u bd)) (q : Pos) where
    H′ = store H (Subject.closed Sj) (lift true)
    v  = connectˢ Sj c b kb k (finishing q (At.val H′ (Subject.subscribers Sj))) rp e rt u bd
    T′ = plant ρ v

    postulate
      fin-calls   : (ks : List (Call T)) → Σ (List (Call T′)) λ ks′ → ⟦ ks ⟧ᶜ ≗ ⟦ ks′ ⟧ᶜ
      fin-stack   : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} → StackAs T p′ ϑ K bs → StackAs T′ p′ ϑ K bs
      fin-ticked  : ∀ {w p′ bs} {ϑ : w ⊑ h} {K : Stack w ⊤} n (sk : StackAs T p′ ϑ K bs) → Ticked T n sk → Ticked T′ n (fin-stack sk)
      fin-owned   : ∀ {w bs} {ϑ : w ⊑ h} {K : Stack w ⊤} {act} (sk : StackAs T q ϑ K bs) (ks : List (Call T))
                    (e : act ≗ ⟦ finC (planted ρ v) ∷ proj₁ (fin-calls ks) ⟧ᶜ)
              → Owned H T (runAs ks (≗-refl _) sk) → Owned H′ T′ (runAs (finC (planted ρ v) ∷ proj₁ (fin-calls ks)) e (fin-stack sk))
      fin-kernels : Kernels H T → Kernels H′ T′
      fin-meaning : Meaning H T → Meaning H′ T′
      fin-queue   : ∀ {clk ts} → Queue H q clk ts T → Queue H′ q clk ts T′
      fin-behind  : Each H (Heads q) T → Each H′ (Heads q) T′
      fin-ghost   : ∀ {g S} → Sane [] g → Placed g [] → At.part H u ≡ nothing
              → Lifts H (ρ ⊕ in-source here) (U.endˢ q) S → U.step g ≡ S
              → Σ (U.Node [] R) λ g″ → At.part H′ T′ ≡ just g″ × Sane [] g″ × Placed g″ []
                × Σ Pos λ k′ → Σ (Events∞ R) λ r → (∀ n → Agree n (residual g) (skip k′ r)) × Past (Events∞.force r) (residual g″)

  -- A connect's source ended: its subject closed, the subscribers read,
  -- their finish owed ahead of the calls the end owed.
  close-source : ∀ {g m} (st : Strong g m) {m₁ Δ A B} {T : Sub (Conf.world (Mach.conf m₁)) [] R} {Sj c b kb k fd e rp rt}
                 {u : Sub (Conf.world (Mach.conf m₁)) Δ A} {bd : Sub (Conf.world (Mach.conf m₁)) (A ∷ Δ) B}
                 (ρ : Path T (connectˢ Sj c b kb k fd rp e rt u bd)) {ks}
               → Calling g (loadOf st) m₁ (ρ ⊕ in-source here) (closes ks) → Called st m₁ (ρ ⊕ in-source here)
  close-source st ρ cl with src-idle ρ cl
  close-source st {m₁ = mach ⟨ hp , q , _ ⟩ clk ts bs td lg en mk} {T = T} {Sj} {c} {b} {kb} {k} {e = e} {rp} {rt} {u = u} {bd} ρ {ks}
    record { sane = sn ; placed = pl ; ctl = refl ; code = cd ; stack = sk ; lifted = gn , S , L , sg ; owned = ow
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = rn } ; sorted = so
           ; behind = bh } | refl
    with writes (subst (λ W → _ ≗ (Observer.complete (Here.obs W) >>ᴬ ⟦ ks ⟧ᶜ)) (walk-⊕ ρ (in-source here) top) cd)
  ... | n′ , en , path₁ with reads {hp = Fins.H′ hp ρ q} en
  ...   | k′ , f , path₂ with Fins.fin-ghost hp ρ q sn pl gn L sg
  ...     | g″ , pg , sn″ , pl″ , k″ , r , ag , pp =
    landed (g″ , _ , path
      , carried (record
        { sane = sn″ ; placed = pl″ ; tree = Fins.T′ hp ρ q
        ; ctlAs = runAs (finC (planted ρ v) ∷ proj₁ (Fins.fin-calls hp ρ q ks)) ec (Fins.fin-stack hp ρ q sk)
        ; meets = pg
        ; owned = Fins.fin-owned hp ρ q sk ks ec ow
        ; kernels = Fins.fin-kernels hp ρ q kn ; meaning = Fins.fin-meaning hp ρ q mn ; queue = Fins.fin-queue hp ρ q qu
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = T} ρ v refl)) fs
                         ; clocked = proj₁ ck , Fins.fin-ticked hp ρ q clk sk (proj₂ ck) ; paidUp = pu ; running = rn }
        ; sorted = sorted-⇝ so path ; behind = Fins.fin-behind hp ρ q bh })
      , passed ag pp)
    where
      path = ⇝-trans path₁ path₂
      ss = At.val (Fins.H′ hp ρ q) (Subject.subscribers Sj)
      v  = connectˢ Sj c b kb k (finishing q ss) rp e rt u bd
      ec = ≗-trans (f same⊑ ss) (bind≗ (≗-refl (Strongly.code R (finC (planted ρ v)))) λ _ → ≗-trans (wk-same ⟦ ks ⟧ᶜ) (proj₂ (Fins.fin-calls hp ρ q ks)))

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
           ; kernels = kn ; meaning = mn ; queue = qu ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } ; sorted = so ; behind = bh } =
    g , _ , then refl now
    , carried (record
        { sane = sn ; placed = pl ; tree = T ; ctlAs = noteAs [] (ke tt) sk ; meets = c′ , pv , sg
        ; owned = owned-move hp (noteAs [] (ke tt) sk) refl refl refl ow ; kernels = kn ; meaning = mn ; queue = qu
        ; books = record { fresh = fs ; clocked = ck ; paidUp = pu ; running = refl } 
        ; sorted = sorted-⇝ so (then refl now) ; behind = bh })
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
    -- A takeWhile's completion begun under its failing value, its cut
    -- the frame's rest.
    take1-enter : ∀ {g m} (cr : Carried g m) {Δ A i p c k q n} {s : Sub _ Δ A} (π : Path (Carried.tree cr) (takeWhileˢ i p c k (Strongly.ending q n) s))
                → firstCall (Carried.ctlAs cr) ≡ just (take1C π) → ∀ {m′} → step m ≡ silent m′
                → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

    -- A spent `of`'s completion begun at its end.
    last-enter : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
               → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → ∀ {m′} → step m ≡ silent m′
               → Σ Mach λ m₁ → m′ ⇝ m₁ × Aloft g (load m (Carried.tree cr)) m₁

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
  take1-onward cr π fc eq = soar (carried cr) (take1-enter cr π fc eq)

  -- A spent `of`'s completion delivered at its end.
  emit-last : ∀ {g m} (cr : Carried g m) {Δ A p i} (π : Path (Carried.tree cr) (ofˢ {Δ = Δ} {A} p i []))
            → firstCall (Carried.ctlAs cr) ≡ just (emitC π) → Hops cr
  emit-last cr π fc eq = soar (carried cr) (last-enter cr π fc eq)

  -- The rest of a connect's feed of its source's end.
  fin-onward : ∀ {g m} (cr : Carried g m) {Δ A B S c b kb k r ss e rp rt} {s : Sub _ Δ A} {bd : Sub _ (A ∷ Δ) B}
               (π : Path (Carried.tree cr) (connectˢ S c b kb k (finishing r ss) rp e rt s bd))
             → firstCall (Carried.ctlAs cr) ≡ just (finC π) → Hops cr
  fin-onward cr π fc eq with fin-enter cr π fc eq
  ... | m₁ , path , inj₁ hp = hopped-pre path hp
  ... | m₁ , path , inj₂ af = soar (carried cr) (m₁ , path , af)

  -- An agenda under way: the ghost is the tree's part.
  run-meets : ∀ {h} {t : Sub h [] R} {p c bs} (ca : CtlAs t p c bs) {n g k} → firstCall ca ≡ just k → Meets ca n g → n ≡ just g
  run-meets (runAs (_ ∷ _) _ _) refl mt = mt
  run-meets (runAs [] _ _)      ()
  run-meets calmAs              ()
  run-meets (noteAs _ _ _)      ()
  run-meets (subAs _ _ _ _)     ()
  run-meets (burstAs _ _ _)     ()

  -- The agenda's first call an `of` at `p`: the run is at `p`.
  run-at : ∀ {h} {t : Sub h [] R} {q c bs} (ca : CtlAs t q c bs) {Δ A p i xs} {π : Path t (ofˢ {Δ = Δ} {A} p i xs)}
         → firstCall ca ≡ just (emitC π) → All (Placedᴬ t) (agenda t ca) → q ≡ p
  run-at (runAs (_ ∷ _) _ _) refl (pl ∷ _) = pl
  run-at (runAs [] _ _)      ()
  run-at calmAs              ()
  run-at (noteAs _ _ _)      ()
  run-at (subAs _ _ _ _)     ()
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
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = subAs _ _ _ _ } refl eq = sub-onward cr refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (emitC π ∷ _) _ _ } refl eq = emit-onward cr π refl eq
  run-onward {m = mach ⟨ _ , _ , _ ⟩ _ _ _ _ _ _ _} cr@record { ctlAs = runAs (kontC lf π ∷ _) _ _ } refl eq = kont-onward cr lf π refl eq
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
                           ; gated = gated-plant hp {t = t} π v (λ _ → lift (λ _ → refl)) (λ s → s) (Kernels.gated kn)
                           ; settled = settled-plant {t = t} π v (λ ()) (λ s → s) (Kernels.settled kn) }
        ; meaning = record { fed = fed-plant hp {t = t} π v (λ _ f → f) _ (Meaning.fed mn) }
        ; queue = record { timed = timed-pop hp {t = t} π (Queue.timed q) (Queue.ordered q) fs
                         ; joined = subst₂ (At.Joined hp) (sym (subjects-plant {t = t} π v refl)) (sym (joiners-plant {t = t} π v (λ _ → refl) _)) (Queue.joined q)
                         ; ordered = tail (Queue.ordered q) ; ahead = ahead-pop {p = p} (Queue.ordered q) (Queue.ahead q) }
        ; books = record { fresh = subst (AllPairs _≢_) (sym (names-plant {t = t} π v refl)) fs ; clocked = refl , tt ; paidUp = refl ; running = rn } 
        ; sorted = hop-sorted cr refl now ; behind = behind-fire cr π })
    , lowered (λ n → agree-refl n _) (inj₁ (inj₂ (pend-plant {t = t} π v refl , inj₂ (takes-plant {t = t} π v refl , inj₁ ≤-refl))))
    where v = coldˢ sk hd (fired τ e (at u x fr))

  -- The stepper is the meaning, as sets.
