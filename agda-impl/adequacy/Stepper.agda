{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips included: a sane, placed ghost's
-- meaning is what its step shows, then the meaning of the node it
-- leaves.  Stated at the root, where no connect's source is in scope;
-- inside a body the step is the run's next event only if it comes before
-- each running source's, its pool's and each ended source's rest.
module adequacy.Stepper where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; Timeline; From; Frame; idle; ix; _<ᵖ_; _∪_;
  <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-below)
open import denotation.MonotonicList using (Agree; Agreeᵀ; stop; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agreeᵀ-refl; agreeᵀ-sym; agree-trans)
open import denotation.NonExpansive using (Agreeˢ; _,ˢ_; beside-ne; body-ne; before-agree; ∪-ne; burstOn-ne)
open Agreeˢ using (nowˢ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Mode; runs; over; loose; Told)
open import adequacy.Placed.Order using (Atop; Ordered; ordered; Placed; Placedᴹ; Placedᴸ; Within)
open import adequacy.Placed.Keys using (ordered-≈)
open import adequacy.Deep using (Deep; Deepˢ)

------------------------------------------------------------------------
-- Alike: the same events at the same positions, skips and what a cut
-- leaves running included, to any depth.

record _≃_ {A : Set} (x y : Events A) : Set where
  constructor alike
  field agreeing : ∀ n → Agree n x y

open _≃_
open Events∞

-- What a step shows, then the meaning of the node it leaves.
afterᴱ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Events A
afterᴱ ρ (U.outˢ k a c′) = out k a (U.stateᴺ c′ ρ)
afterᴱ ρ (U.skipˢ k c′)  = skip k (U.stateᴺ c′ ρ)
afterᴱ ρ (U.endˢ k)      = end k
afterᴱ ρ U.hushˢ         = hush

-- What a step shows sits atop the stepped node's meaning, and that node
-- is placed.
Placedˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Placedˢ ρ (U.outˢ k a c) = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.skipˢ k c)  = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.endˢ k)     = ⊤
Placedˢ ρ U.hushˢ        = ⊤

-- What the stepped node holds within it is placed.
Withinˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Withinˢ ρ (U.outˢ k a c) = Within c ρ
Withinˢ ρ (U.skipˢ k c)  = Within c ρ
Withinˢ ρ (U.endˢ k)     = ⊤
Withinˢ ρ U.hushˢ        = ⊤

-- A node in order showing its step leaves the stepped node in order,
-- atop what the step shows.
placed-step : ∀ {Γ A} (ρ : NEnv Γ) (s : U.Step Γ A) {x : Events A} → x ≃ afterᴱ ρ s → Ordered x → Withinˢ ρ s → Placedˢ ρ s
placed-step ρ (U.outˢ k a c) e o w = proj₁ (ordered (ordered-≈ _ _ (agreeing e) o)) , proj₂ (ordered (ordered-≈ _ _ (agreeing e) o)) , w
placed-step ρ (U.skipˢ k c)  e o w = proj₁ (ordered (ordered-≈ _ _ (agreeing e) o)) , proj₂ (ordered (ordered-≈ _ _ (agreeing e) o)) , w
placed-step ρ (U.endˢ k)     e o w = tt
placed-step ρ U.hushˢ        e o w = tt

------------------------------------------------------------------------
-- THE STEPPER IS THE MEANING, in any scope: what a node's step shows is
-- its next event once each running source in scope shows its next step
-- only past it.  A joiner reads its source only as fed, so a source step
-- the body has not been fed would show first.

-- A source step shown as an event: a value, else a skip.
shows : ∀ {A} → Pos → Maybe A → Events∞ A → Events A
shows q (just a) σ = out q a σ
shows q nothing  σ = skip q σ

-- A source's next step shows past `k`; of no step, the source has none.
Clearᴱ : ∀ {A} → Maybe Pos → Events A → Set
Clearᴱ h        hush           = ⊤
Clearᴱ nothing  (out _ _ _)    = ⊥
Clearᴱ nothing  (skip _ _)     = ⊥
Clearᴱ nothing  (end _)        = ⊥
Clearᴱ (just k) e@(out _ _ _)  = k <ᵖ M′.shownAt e ≡ true
Clearᴱ (just k) e@(skip _ _)   = k <ᵖ M′.shownAt e ≡ true
Clearᴱ (just k) e@(end _)      = k <ᵖ M′.shownAt e ≡ true

-- Each source in scope clear of a step at `h`; an ended one asks
-- nothing, its joiners told.
Clear : ∀ {Γ} → All (λ _ → Mode) Γ → Maybe Pos → NEnv Γ → Set
Clear []ᴬ          h []ᴬ      = ⊤
Clear (runs ∷ᴬ ν)  h (e ∷ᴬ ρ) = Clearᴱ h e × Clear ν h ρ
Clear (over ∷ᴬ ν)  h (e ∷ᴬ ρ) = Clear ν h ρ
Clear (loose ∷ᴬ ν) h (e ∷ᴬ ρ) = Clearᴱ h e × Clear ν h ρ

-- A node's meaning is what its step shows, then the stepped node's,
-- when its sources are clear of the step.
Skips : ∀ {Γ A} → All (λ _ → Mode) Γ → U.Node Γ A → NEnv Γ → Set
Skips ν c ρ = Clear ν (U.headˢ (U.step c)) ρ → U.meaning c ρ ≃ afterᴱ ρ (U.step c)

Skipsᴹ : ∀ {Γ A} → All (λ _ → Mode) Γ → Maybe (U.Node Γ A) → NEnv Γ → Set
Skipsᴹ ν nothing  ρ = ⊤
Skipsᴹ ν (just c) ρ = Skips ν c ρ

Skipsᴸ : ∀ {Γ A} → All (λ _ → Mode) Γ → List (U.Node Γ A) → NEnv Γ → Set
Skipsᴸ ν []       ρ = ⊤
Skipsᴸ ν (c ∷ cs) ρ = Skips ν c ρ × Skipsᴸ ν cs ρ

-- A source clear of no step has none.
hush-clear : ∀ {A} (e : Events A) → Clearᴱ nothing e → e ≡ hush
hush-clear hush        _ = refl
hush-clear (out _ _ _) ()
hush-clear (skip _ _)  ()
hush-clear (end _)     ()

clear-hush : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (i : A ∈ Γ) → Told (lookup ν i) nothing → Clear ν nothing ρ → lookup ρ i ≡ hush
clear-hush (runs ∷ᴬ ν)  (e ∷ᴬ ρ) (here refl) t (c , _) = hush-clear e c
clear-hush (loose ∷ᴬ ν) (e ∷ᴬ ρ) (here refl) t (c , _) = hush-clear e c
clear-hush (over ∷ᴬ ν)  (e ∷ᴬ ρ) (here refl) () _
clear-hush (runs ∷ᴬ ν)  (e ∷ᴬ ρ) (there i)   t (_ , c) = clear-hush ν ρ i t c
clear-hush (loose ∷ᴬ ν) (e ∷ᴬ ρ) (there i)   t (_ , c) = clear-hush ν ρ i t c
clear-hush (over ∷ᴬ ν)  (e ∷ᴬ ρ) (there i)   t c       = clear-hush ν ρ i t c

-- A value changed, or a running total, keeps the step's position.
head-map : ∀ {Γ A B} (f : A → B) (s : U.Step Γ A) → U.headˢ (U.mapˢ f s) ≡ U.headˢ s
head-map f (U.outˢ k a c) = refl
head-map f (U.skipˢ k c)  = refl
head-map f (U.endˢ k)     = refl
head-map f U.hushˢ        = refl

head-scan : ∀ {Γ A B} (f : B → A → B) z (s : U.Step Γ A) → U.headˢ (U.scanˢ f z s) ≡ U.headˢ s
head-scan f z (U.outˢ k a c) = refl
head-scan f z (U.skipˢ k c)  = refl
head-scan f z (U.endˢ k)     = refl
head-scan f z U.hushˢ        = refl

-- A source's next step shows at or past `k`, or it has none.
Floorᴱ : ∀ {A} → Pos → Events A → Set
Floorᴱ k hush         = ⊤
Floorᴱ k (out q _ _)  = (q ++ [ ix 0 ]) <ᵖ k ≡ false
Floorᴱ k (skip q _)   = (q ++ [ ix 0 ]) <ᵖ k ≡ false
Floorᴱ k (end c)      = (c ++ [ ix 0 ]) <ᵖ k ≡ false

Floor : ∀ {Γ} → All (λ _ → Mode) Γ → Pos → NEnv Γ → Set
Floor []ᴬ          k []ᴬ      = ⊤
Floor (runs ∷ᴬ ν)  k (e ∷ᴬ ρ) = Floorᴱ k e × Floor ν k ρ
Floor (over ∷ᴬ ν)  k (e ∷ᴬ ρ) = Floor ν k ρ
Floor (loose ∷ᴬ ν) k (e ∷ᴬ ρ) = Floorᴱ k e × Floor ν k ρ

-- Clear of a step past `k′`, clear of one at `k′`'s predecessors.
clearᴱ-lower : ∀ {A k k′} (e : Events A) → k′ <ᵖ k ≡ true → Clearᴱ (just k) e → Clearᴱ (just k′) e
clearᴱ-lower                 hush        lt c = tt
clearᴱ-lower {k = k} {k′} (out q a σ) lt c = <ᵖ-trans k′ k (q ++ [ ix 0 ]) lt c
clearᴱ-lower {k = k} {k′} (skip q σ)  lt c = <ᵖ-trans k′ k (q ++ [ ix 0 ]) lt c
clearᴱ-lower {k = k} {k′} (end c′)    lt c = <ᵖ-trans k′ k (c′ ++ [ ix 0 ]) lt c

clear-lower : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) {k k′} → k′ <ᵖ k ≡ true → Clear ν (just k) ρ → Clear ν (just k′) ρ
clear-lower []ᴬ          []ᴬ      lt c        = tt
clear-lower (runs ∷ᴬ ν)  (e ∷ᴬ ρ) lt (ce , c) = clearᴱ-lower e lt ce , clear-lower ν ρ lt c
clear-lower (over ∷ᴬ ν)  (e ∷ᴬ ρ) lt c        = clear-lower ν ρ lt c
clear-lower (loose ∷ᴬ ν) (e ∷ᴬ ρ) lt (ce , c) = clearᴱ-lower e lt ce , clear-lower ν ρ lt c

clearᴱ-floor : ∀ {A k} (e : Events A) → Clearᴱ (just k) e → Floorᴱ k e
clearᴱ-floor         hush        c = tt
clearᴱ-floor {k = k} (out q a σ) c = <ᵖ-asym k (q ++ [ ix 0 ]) c
clearᴱ-floor {k = k} (skip q σ)  c = <ᵖ-asym k (q ++ [ ix 0 ]) c
clearᴱ-floor {k = k} (end c′)    c = <ᵖ-asym k (c′ ++ [ ix 0 ]) c

clear-floor : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) {k} → Clear ν (just k) ρ → Floor ν k ρ
clear-floor []ᴬ          []ᴬ      c        = tt
clear-floor (runs ∷ᴬ ν)  (e ∷ᴬ ρ) (ce , c) = clearᴱ-floor e ce , clear-floor ν ρ c
clear-floor (over ∷ᴬ ν)  (e ∷ᴬ ρ) c        = clear-floor ν ρ c
clear-floor (loose ∷ᴬ ν) (e ∷ᴬ ρ) (ce , c) = clearᴱ-floor e ce , clear-floor ν ρ c

floorᴱ-agree : ∀ {A k} {e e′ : Events A} → Agree 1 e e′ → Floorᴱ k e′ → Floorᴱ k e
floorᴱ-agree (out⁼ _ _)  f = f
floorᴱ-agree (skip⁼ _ _) f = f
floorᴱ-agree end⁼        f = f
floorᴱ-agree hush⁼       f = f

-- The body's step shows first: the source's, if any, not before it.
Shy : ∀ {Δ Γ A B} → U.Step Δ B → U.Step Γ A → Set
Shy sb (U.outˢ q _ _) = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
Shy sb (U.skipˢ q _)  = U.beforeˢ (q ++ [ ix 0 ]) sb ≡ false
Shy sb (U.endˢ c)     = U.beforeˢ (c ++ [ ix 0 ]) sb ≡ false
Shy sb U.hushˢ        = ⊤

-- A joiner shows what it was fed, then its end once told it; untold and
-- fed nothing, it shows nothing while its source is clear.
join-skips : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) p xs e (ρ : NEnv Γ) → Told (lookup ν i) e → Skips ν (U.joinᶜ i p xs e) ρ
join-skips i p ((q , just a) ∷ xs) e ρ t cl = alike λ where
  zero    → stop
  (suc d) → out⁼ (agreeᵀ-refl d idle) (agree-refl d _)
join-skips i p ((q , nothing) ∷ xs) e ρ t cl = alike λ where
  zero    → stop
  (suc d) → skip⁼ (agreeᵀ-refl d idle) (agree-refl d _)
join-skips i p [] (just c) ρ t cl = alike λ d → agree-refl d (end c)
join-skips {ν = ν} i p [] nothing ρ t cl =
  alike λ d → subst (λ x → Agree d (M′.rejoin p x) hush) (sym (clear-hush ν ρ i t cl)) (agree-refl d hush)

postulate
  -- A value changed, a running total, or a take keep what a step shows
  -- and what it leaves.
  after-map  : ∀ {Γ A B} (ρ : NEnv Γ) (f : A → B) (s : U.Step Γ A) {x : Events A} → x ≃ afterᴱ ρ s → M′.mapᴱ f x ≃ afterᴱ ρ (U.mapˢ f s)
  after-scan : ∀ {Γ A B} (ρ : NEnv Γ) (f : B → A → B) z (s : U.Step Γ A) {x : Events A} → x ≃ afterᴱ ρ s → M′.scanᴱ f z x ≃ afterᴱ ρ (U.scanˢ f z s)
  after-take : ∀ {Γ A} (ρ : NEnv Γ) i (p : A → Bool) (s : U.Step Γ A) {x : Events A} → x ≃ afterᴱ ρ s → M′.takeWhileᴱ i p x ≃ afterᴱ ρ (U.takeWhileˢ i p s)

  -- A take's step sits at or past its source's: clear of it, clear of
  -- the source's.
  clear-take : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {ρ : NEnv Γ} i (p : A → Bool) (s : U.Step Γ A) → Clear ν (U.headˢ (U.takeWhileˢ i p s)) ρ → Clear ν (U.headˢ s) ρ

  -- A timer's frames, a burst, a list: their steps are their runs.
  frames-after : ∀ {Γ A t} (ρ : NEnv Γ) τ e (m : From A t) → M′.frames τ e m ≃ afterᴱ ρ (U.framesˢ τ e m)
  burst-after  : ∀ {Γ A t} (ρ : NEnv Γ) τ r i (b : Frame A t) → M′.burst τ r i b ≃ afterᴱ ρ (U.burstˢ τ r i b)
  of-after     : ∀ {Γ A} (ρ : NEnv Γ) p i (xs : List A) → M′.ofᴱ p i xs ≃ afterᴱ ρ (U.ofˢ p i xs)

  -- A flatMap's pool, outer and lanes, run by its step as by `go`: the
  -- pool's skip first, else the earlier of the outer and the lanes,
  -- each part stepping as it does alone.
  flat-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} op (g : A → Pos → U.Node Γ B) o ls qs pl (ρ : NEnv Γ)
             → Sane ν (U.flatMapᶜ op g o ls qs pl) → Placed (U.flatMapᶜ op g o ls qs pl) ρ
             → Skipsᴹ ν o ρ → Skipsᴸ ν ls ρ → Skips ν (U.flatMapᶜ op g o ls qs pl) ρ

  -- A body reading its source's step at `q` runs alike fed it, the
  -- source past it; at the source's end, alike shut.
  --
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Sane.agda restores `sane-feed`, which a stepper over a meaning with no tails fed its sources' steps through
  feed-alike : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) q (a : Maybe A) (σ : Events∞ A) {e : Events A} (ρ : NEnv Γ)
             → Sane (runs ∷ᴬ ν) b → e ≃ shows q a σ → ∀ d → Agreeˢ d (U.stateᴺ b (e ∷ᴬ ρ)) (U.stateᴺ (U.feed (here refl) q a b) (force σ ∷ᴬ ρ))
  shut-alike : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) c {e : Events A} (ρ : NEnv Γ)
             → Sane (runs ∷ᴬ ν) b → e ≃ end c → ∀ d → Agreeˢ d (U.stateᴺ b (e ∷ᴬ ρ)) (U.stateᴺ (U.shut (here refl) c b) (end c ∷ᴬ ρ))

  -- A node whose step shows past `k`, among sources showing nothing
  -- before `k`, shows nothing before it.
  floor : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) k → Sane ν c → Placed c ρ
        → U.beforeˢ k (U.step c) ≡ true → Floor ν k ρ → M′.before k (U.meaning c ρ) ≡ true

  -- A connect's body stepping no later than its source's step steps
  -- strictly before it: no body event lies at the source's step or where
  -- it shows.
  --
  -- DEAD ROUTE: exact agreement with a ghost anchored in its sources'
  --   step history.  The ghost is the witness's open part (`part`), which
  --   keeps no count of a source's steps, and a silent run is matched by
  --   the residual as a set alone (`Ahead`), so no field of the witness
  --   can keep the count a lane's pre-join skips need.
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Stepper.agda restores the stepper over a meaning with no tails, node by node
  shy-before : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
             → Sane (runs ∷ᴬ ν) b → Sane ν s → Placed b (U.meaning s ρ ∷ᴬ ρ) → Placed s ρ → Shy (U.step b) (U.step s)
             → ∀ k → U.headˢ (U.step b) ≡ just k → U.beforeˢ k (U.step s) ≡ true

  -- A node that never shows again leaves nothing running when cut.
  hushed-cut : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Sane ν s → Placed s ρ
             → U.meaning s ρ ≡ hush → ∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle

  -- Past its source's end, a connect runs its source's rest's skip
  -- first when it shows before the body's; else the body's, shut.
  ended-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) c (t : U.Node Γ A) (ρ : NEnv Γ)
              → Sane ν (U.connectᶜ r b (U.ended c t)) → Placed (U.connectᶜ r b (U.ended c t)) ρ
              → Skips (over ∷ᴬ ν) b (end c ∷ᴬ ρ) → Skips ν (U.connectᶜ r b (U.ended c t)) ρ

  -- A defer's subscription: a skip, then its program subscribed, fed the
  -- source steps it noticed.
  defer-skips : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (l : Later Timeline Γ A) p ns (ρ : NEnv Γ) → Placed (U.deferᶜ l p ns) ρ → Skips ν (U.deferᶜ l p ns) ρ

  -- A rest's steps are its tail's pins.  `Sane` says nothing of a rest.
  rest-skips     : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (n : U.Node Γ A) (ρ : NEnv Γ) → Skips ν (U.restᶜ {B = B} n) ρ
  union-skips    : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (x y : U.Node Γ B) (ρ : NEnv Γ) → Skips ν (U.unionᶜ x y) ρ
  bursting-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (t : U.Node Γ A) (ρ : NEnv Γ) → Skips ν (U.burstingᶜ {B = B} r t) ρ
  under-skips    : ∀ {Γ A C B} {ν : All (λ _ → Mode) Γ} (s : U.Source Γ A) (b : U.Node (A ∷ Γ) C) (ρ : NEnv Γ) → Skips ν (U.underᶜ {B = B} s b) ρ

-- A source's step shown first: the body fed it, its next event later.
module SourceFirst {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
                   (sb : Sane (runs ∷ᴬ ν) b) (pb : Placed b (U.meaning s ρ ∷ᴬ ρ)) where

  β : Events∞ B
  β = U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)

  σ : Events∞ A
  σ = U.stateᴺ s ρ

  -- What the source shows, as a state the connect can read.
  as : Events A → Events∞ A
  as e .force = e
  as e .cut   = U.cutᴺ s ρ

  as-alike : ∀ {e} → U.meaning s ρ ≃ e → ∀ d → Agreeˢ d σ (as e)
  as-alike al d = agreeᵀ-refl d _ ,ˢ agreeing al d

  -- The body's meaning shows after the source's shown step.
  body-floor : ∀ {e} k → U.meaning s ρ ≃ e → Floorᴱ k e → U.beforeˢ k (U.step b) ≡ true → Clear ν (just k) ρ
             → M′.before k (U.meaning b (U.meaning s ρ ∷ᴬ ρ)) ≡ true
  body-floor k al fe fb cl = floor b (U.meaning s ρ ∷ᴬ ρ) k sb pb fb (floorᴱ-agree (agreeing al 1) fe , clear-floor ν ρ cl)

  -- The connect reads its source's step at `q` as the source shows it.
  side-shows : ∀ q (a : Maybe A) (β₁ : Events∞ B) σ₁ d
             → Agree d (M′.beside r β₁ (as (shows q a σ₁))) (M′.ahead r β₁ (as (shows q a σ₁)) (q ++ [ ix 0 ]) (M′.before (q ++ [ ix 0 ]) (force β₁)))
  side-shows q (just x) β₁ σ₁ d = agree-refl d _
  side-shows q nothing  β₁ σ₁ d = agree-refl d _

  -- Past the shown step, the connect runs on: the body as fed, the
  -- source from its next node.
  shown-next : ∀ q (a : Maybe A) (b″ : U.Node (A ∷ Γ) B) (s″ : U.Node Γ A) d
             → Agree d (M′.ahead r (U.stateᴺ b″ (U.meaning s″ ρ ∷ᴬ ρ)) (as (shows q a (U.stateᴺ s″ ρ))) (q ++ [ ix 0 ]) true)
                       (skip (q ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r b″ (U.live s″)) ρ))
  shown-next q a        b″ s″ zero    = stop
  shown-next q (just x) b″ s″ (suc d) = skip⁼ (agreeᵀ-refl d _) (agree-refl d _)
  shown-next q nothing  b″ s″ (suc d) = skip⁼ (agreeᵀ-refl d _) (agree-refl d _)

  fed-first : ∀ q (a : Maybe A) (s′ : U.Node Γ A) → U.meaning s ρ ≃ shows q a (U.stateᴺ s′ ρ)
            → U.beforeˢ (q ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (q ++ [ ix 0 ])) ρ
            → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ skip (q ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r (U.feed (here refl) q a b) (U.live s′)) ρ)
  fed-first q a s′ al fb cl = alike λ d → agree-trans (beside-ne r (fa d) (as-alike al d)) (top d)
    where
      σ′ = U.stateᴺ s′ ρ
      b′ = U.feed (here refl) q a b
      β′ = U.stateᴺ b′ (U.meaning s′ ρ ∷ᴬ ρ)
      k  = q ++ [ ix 0 ]
      fa = feed-alike b q a σ′ ρ sb al
      flag : M′.before k (U.meaning b′ (U.meaning s′ ρ ∷ᴬ ρ)) ≡ true
      flag = trans (sym (before-agree k (nowˢ (fa 1)))) (body-floor k al (shown a) fb cl)
        where shown : ∀ a → Floorᴱ k (shows q a σ′)
              shown (just _) = <ᵖ-irrefl k
              shown nothing  = <ᵖ-irrefl k
      target = skip k (U.stateᴺ (U.connectᶜ r b′ (U.live s′)) ρ)
      top : ∀ d → Agree d (M′.beside r β′ (as (shows q a σ′))) target
      top d = agree-trans (side-shows q a β′ σ′ d) (subst (λ f → Agree d (M′.ahead r β′ (as (shows q a σ′)) k f) target) (sym flag) (shown-next q a b′ s′ d))

  shut-first : ∀ c → U.meaning s ρ ≃ end c → U.beforeˢ (c ++ [ ix 0 ]) (U.step b) ≡ true → Clear ν (just (c ++ [ ix 0 ])) ρ
             → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ skip (c ++ [ ix 0 ]) (U.stateᴺ (U.connectᶜ r (U.shut (here refl) c b) (U.ended c (U.restᶜ s))) ρ)
  shut-first c al fb cl = alike λ d → agree-trans (beside-ne r (sa d) (as-alike al d)) (top d)
    where
      b′ = U.shut (here refl) c b
      β′ = U.stateᴺ b′ (end c ∷ᴬ ρ)
      k  = c ++ [ ix 0 ]
      sa = shut-alike b c ρ sb al
      flag : M′.before k (U.meaning b′ (end c ∷ᴬ ρ)) ≡ true
      flag = trans (sym (before-agree k (nowˢ (sa 1)))) (body-floor k al (<ᵖ-irrefl k) fb cl)
      target = skip k (U.stateᴺ (U.connectᶜ r b′ (U.ended c (U.restᶜ s))) ρ)
      -- Past its end the source runs on as its rest.
      next : ∀ d → Agree d (M′.ahead r β′ (as (end c)) k true) target
      rest : ∀ d → Agreeˢ d (M′.onward∞ (as (end c)) (end c)) (U.stateᴺ (U.restᶜ s) ρ)
      rest d = agreeᵀ-refl d _ ,ˢ agree-refl d _
      next zero    = stop
      next (suc d) = skip⁼ (∪-ne (burstOn-ne r (rest d)) (agreeᵀ-refl d _)) (beside-ne r (agreeᵀ-refl d _ ,ˢ agree-refl d _) (rest d))
      top : ∀ d → Agree d (M′.beside r β′ (as (end c))) target
      top d = subst (λ f → Agree d (M′.ahead r β′ (as (end c)) k f) target) (sym flag) (next d)

-- What the body's step heads at, the connect's does.
head-body : ∀ {Γ A B} r (src : U.Source Γ A) (t : U.Step (A ∷ Γ) B) → U.headˢ (U.bodyˢ r src t) ≡ U.headˢ t
head-body r src (U.outˢ k a b) = refl
head-body r src (U.skipˢ k b)  = refl
head-body r src (U.endˢ c)     = refl
head-body r src U.hushˢ        = refl

-- The body's step shown first: the connect shows it, the source carried.
module BodyFirst {Γ A B} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ) where

  env : NEnv (A ∷ Γ)
  env = U.meaning s ρ ∷ᴬ ρ

  β : Events∞ B
  β = U.stateᴺ b env

  σ : Events∞ A
  σ = U.stateᴺ s ρ

  onward : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
         → ∀ (b′ : U.Node (A ∷ Γ) B) d
         → Agree d (M′.ahead r (U.stateᴺ b′ env) σ K (M′.before K (U.meaning b′ env))) (M′.side r (U.stateᴺ b′ env) σ (U.meaning s ρ))
  onward eq K sd b′ d = subst (λ x → Agree d _ (M′.side r (U.stateᴺ b′ env) σ x)) (sym eq) (subst (Agree d _) (sym (sd (U.stateᴺ b′ env))) (agree-refl d _))

  -- The body's step, run beside the source as the connect runs it.
  past : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
       → ∀ t d → Agree (suc d) (M′.body r σ K (afterᴱ env t)) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  past eq K sd (U.outˢ k a b′) d = out⁼ (agreeᵀ-refl d _) (onward eq K sd b′ d)
  past eq K sd (U.skipˢ k b′)  d = skip⁼ (agreeᵀ-refl d _) (onward eq K sd b′ d)
  past eq K sd (U.endˢ c)      d = end⁼
  past eq K sd U.hushˢ         d = hush⁼

  -- The source showing at `K`, past the body's step.
  shown : ∀ {e} → U.meaning s ρ ≡ e → ∀ K → (∀ (β′ : Events∞ B) → M′.side r β′ σ e ≡ M′.ahead r β′ σ K (M′.before K (force β′)))
        → ∀ t → U.meaning b env ≃ afterᴱ env t → M′.before K (U.meaning b env) ≡ false
        → ∀ d → Agree d (M′.side r β σ e) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  shown eq K sd t al fl zero    = stop
  shown eq K sd t al fl (suc d) =
    subst (λ x → Agree (suc d) x _) (sym (sd β))
      (subst (λ f → Agree (suc d) (M′.ahead r β σ K f) _) (sym fl)
        (agree-trans (body-ne r (agreeᵀ-refl (suc d) _ ,ˢ agree-refl (suc d) _) (agreeing al (suc d))) (past eq K sd t d)))

  left : U.meaning s ρ ≡ hush → (∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle) → ∀ (b′ : U.Node (A ∷ Γ) B) d
       → Agreeᵀ d (U.cutᴺ b′ env) (M′.burstOn r σ ∪ U.cutᴺ b′ env)
  left eq hc b′ d = subst (λ x → Agreeᵀ d (U.cutᴺ b′ env) (M′.runOn r x (U.cutᴺ s ρ) ∪ U.cutᴺ b′ env)) (sym eq)
                      (agreeᵀ-sym (∪-ne (hc d) (agreeᵀ-refl d _)))

  still : U.meaning s ρ ≡ hush → ∀ (b′ : U.Node (A ∷ Γ) B) d → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ (U.meaning s ρ))
  still eq b′ d = subst (λ x → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ x)) (sym eq) (agree-refl d _)

  -- The source hushed: the connect is its body, nothing left running.
  hushed : U.meaning s ρ ≡ hush → (∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle)
         → ∀ t → U.meaning b env ≃ afterᴱ env t → ∀ d → Agree d (U.meaning b env) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  hushed eq hc t al zero = stop
  hushed eq hc (U.outˢ k a b′) al (suc d) = agree-trans (agreeing al (suc d)) (out⁼ (left eq hc b′ d) (still eq b′ d))
  hushed eq hc (U.skipˢ k b′)  al (suc d) = agree-trans (agreeing al (suc d)) (skip⁼ (left eq hc b′ d) (still eq b′ d))
  hushed eq hc (U.endˢ c)      al (suc d) = agreeing al (suc d)
  hushed eq hc U.hushˢ         al (suc d) = agreeing al (suc d)

  -- The source shown at `e`: hushed, or past the body's step.
  main : ∀ t (e : Events A) → U.meaning s ρ ≡ e → U.meaning b env ≃ afterᴱ env t → Clearᴱ (U.headˢ t) e
       → (U.meaning s ρ ≡ hush → ∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle)
       → ∀ d → Agree d (M′.side r β σ e) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  main t      hush         eq al ce hc d = hushed eq (hc eq) t al d
  main U.hushˢ (out _ _ _) eq al () hc d
  main U.hushˢ (skip _ _)  eq al () hc d
  main U.hushˢ (end _)     eq al () hc d
  main t@(U.outˢ k a b′) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.outˢ k a b′) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.outˢ k a b′) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.skipˢ k b′) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (out q x τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (skip q τ) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d
  main t@(U.endˢ k) (end q) eq al ce hc d = shown eq (q ++ [ ix 0 ]) (λ _ → refl) t al (trans (before-agree (q ++ [ ix 0 ]) (agreeing al 1)) (<ᵖ-asym k (q ++ [ ix 0 ]) ce)) d

-- Of no step, a step hushed.
head-none : ∀ {Γ A} (t : U.Step Γ A) → U.headˢ t ≡ nothing → t ≡ U.hushˢ
head-none U.hushˢ refl = refl

-- A meaning showing nothing before `k` shows past `k`.
shown-past : ∀ {A} k (e : Events A) → M′.before k e ≡ true → Clearᴱ (just k) e
shown-past k hush        h = tt
shown-past k (out q a σ) h = <ᵖ-trans k q (q ++ [ ix 0 ]) h (<ᵖ-below q [])
shown-past k (skip q σ)  h = <ᵖ-trans k q (q ++ [ ix 0 ]) h (<ᵖ-below q [])
shown-past k (end c)     h = <ᵖ-trans k c (c ++ [ ix 0 ]) h (<ᵖ-below c [])

-- A hushed body beside a source whose step is hushed too.
quiet : ∀ {Δ Γ A C} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Skips ν s ρ → Clear ν nothing ρ
      → ∀ t → U.step s ≡ t → Shy {Δ = Δ} {B = C} U.hushˢ t → Clearᴱ nothing (U.meaning s ρ)
quiet {ν = ν} s ρ sks cl U.hushˢ es _ =
  subst (Clearᴱ nothing) (sym (agreed (agreeing (sks (subst (λ t → Clear ν (U.headˢ t) ρ) (sym es) cl)) 1) es)) tt
  where agreed : ∀ {x} → Agree 1 x (afterᴱ ρ (U.step s)) → U.step s ≡ U.hushˢ → x ≡ hush
        agreed a e with U.step s | e
        agreed hush⁼ e | .U.hushˢ | refl = refl
quiet s ρ sks cl (U.outˢ q a s′) es ()
quiet s ρ sks cl (U.skipˢ q s′)  es ()
quiet s ρ sks cl (U.endˢ c)      es ()

-- A connect's body stepping no later than its source's step, among
-- sources clear of the body's step: the source's meaning shows past it.
shy-clear : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
          → Sane (runs ∷ᴬ ν) b → Sane ν s → Placed b (U.meaning s ρ ∷ᴬ ρ) → Placed s ρ → Skips ν s ρ → Shy (U.step b) (U.step s)
          → Clear ν (U.headˢ (U.step b)) ρ → Clearᴱ (U.headˢ (U.step b)) (U.meaning s ρ)
shy-clear {ν = ν} b s ρ sb ss pb ps sks shy cl with U.headˢ (U.step b) in hb
... | just k  = shown-past k (U.meaning s ρ) (floor s ρ k ss ps (shy-before b s ρ sb ss pb ps shy k hb) (clear-floor ν ρ cl))
... | nothing = quiet {ν = ν} s ρ sks cl (U.step s) refl (subst (λ t → Shy t (U.step s)) (head-none (U.step b) hb) shy)

-- A connect's body showing first: what it shows, the source carried.
body-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
           → Sane (runs ∷ᴬ ν) b → Sane ν s → Placed b (U.meaning s ρ ∷ᴬ ρ) → Placed s ρ
           → Skips (runs ∷ᴬ ν) b (U.meaning s ρ ∷ᴬ ρ) → Skips ν s ρ → Shy (U.step b) (U.step s)
           → Clear ν (U.headˢ (U.bodyˢ r (U.live s) (U.step b))) ρ
           → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ afterᴱ ρ (U.bodyˢ r (U.live s) (U.step b))
body-skips {ν = ν} r b s ρ sb ss pb ps skb sks shy cl =
  alike (BodyFirst.main r b s ρ (U.step b) (U.meaning s ρ) refl (skb (ce , cl′)) ce (λ eq → hushed-cut s ρ ss ps eq))
  where cl′ = subst (λ h → Clear ν h ρ) (head-body r (U.live s) (U.step b)) cl
        ce  = shy-clear b s ρ sb ss pb ps sks shy cl′

-- A node's skips, read off its step.
back : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} {s : U.Node Γ A} {ρ : NEnv Γ} {t} → U.step s ≡ t
     → (Clear ν (U.headˢ t) ρ → U.meaning s ρ ≃ afterᴱ ρ t) → Skips ν s ρ
back refl k = k

-- A connect runs its source's step first when it shows before the
-- body's, the body fed it; else the body's.
connect-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
              → Sane ν (U.connectᶜ r b (U.live s)) → Placed (U.connectᶜ r b (U.live s)) ρ
              → Skips (runs ∷ᴬ ν) b (U.meaning s ρ ∷ᴬ ρ) → Skips ν s ρ → Skips ν (U.connectᶜ r b (U.live s)) ρ
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl with U.step s in es
... | U.outˢ q a s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.fed-first r b s ρ sb (proj₁ (proj₂ pl)) q (just a) s′ (sks (clear-lower ν ρ (<ᵖ-below q []) cl)) fb cl
...   | false = body-skips r b s ρ sb ss (proj₁ (proj₂ pl)) (proj₂ (proj₂ pl)) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.skipˢ q s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.fed-first r b s ρ sb (proj₁ (proj₂ pl)) q nothing s′ (sks (clear-lower ν ρ (<ᵖ-below q []) cl)) fb cl
...   | false = body-skips r b s ρ sb ss (proj₁ (proj₂ pl)) (proj₂ (proj₂ pl)) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.endˢ c with U.beforeˢ (c ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.shut-first r b s ρ sb (proj₁ (proj₂ pl)) c (sks (clear-lower ν ρ (<ᵖ-below c []) cl)) fb cl
...   | false = body-skips r b s ρ sb ss (proj₁ (proj₂ pl)) (proj₂ (proj₂ pl)) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.hushˢ =
  body-skips r b s ρ sb ss (proj₁ (proj₂ pl)) (proj₂ (proj₂ pl)) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) tt) cl

-- Node by node, each part stepping as it does alone.
--
-- REFUTED: 3e2af71f stated of every node, by a told joiner under a live source
-- REFUTED: 082ad778 stated without the body sane, by a joiner told its end
mutual
  skips : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ → Skips ν c ρ
  skips (U.framesᶜ τ e m)  ρ _ _ _ = frames-after ρ τ e m
  skips (U.burstᶜ τ r i b) ρ _ _ _ = burst-after ρ τ r i b
  skips (U.ofᶜ p i xs)     ρ _ _ _ = of-after ρ p i xs
  skips {ν = ν} (U.mapᶜ f c) ρ sn (_ , pl) cl =
    after-map ρ f (U.step c) (skips c ρ sn pl (subst (λ h → Clear ν h ρ) (head-map f (U.step c)) cl))
  skips {ν = ν} (U.scanᶜ f z c) ρ sn (_ , pl) cl =
    after-scan ρ f z (U.step c) (skips c ρ sn pl (subst (λ h → Clear ν h ρ) (head-scan f z (U.step c)) cl))
  skips {ν = ν} (U.takeWhileᶜ i p c) ρ sn (_ , pl) cl = after-take ρ i p (U.step c) (skips c ρ sn pl (clear-take {ν = ν} {ρ = ρ} i p (U.step c) cl))
  skips (U.flatMapᶜ op g o ls qs pl) ρ sn@(so , sl , _) pd@(_ , po , pls , _) cl =
    flat-skips op g o ls qs pl ρ sn pd (skipsᴹ o ρ so po) (skipsᴸ ls ρ sl pls) cl
  skips {ν = ν} (U.joinᶜ i p xs e) ρ sn _ cl = join-skips {ν = ν} i p xs e ρ sn cl
  skips (U.connectᶜ r b (U.live s)) ρ sn@(sb , ss) pd@(_ , pb , ps) cl =
    connect-skips r b s ρ sn pd (skips b (U.meaning s ρ ∷ᴬ ρ) sb pb) (skips s ρ ss ps) cl
  skips (U.connectᶜ r b (U.ended c t)) ρ sb pd@(_ , pb) cl = ended-skips r b c t ρ sb pd (skips b (end c ∷ᴬ ρ) sb pb) cl
  skips {ν = ν} (U.deferᶜ l p ns) ρ _ pd cl = defer-skips {ν = ν} l p ns ρ pd cl
  skips (U.endingᶜ p n)   ρ _ _ _  = alike λ d → agree-refl d (end p)
  skips {ν = ν} (U.restᶜ n)       ρ _ _ cl = rest-skips {ν = ν} n ρ cl
  skips U.idleᶜ           ρ _ _ _  = alike λ d → agree-refl d hush
  skips {ν = ν} (U.unionᶜ x y)    ρ _ _ cl = union-skips {ν = ν} x y ρ cl
  skips {ν = ν} (U.burstingᶜ r t) ρ _ _ cl = bursting-skips {ν = ν} r t ρ cl
  skips {ν = ν} (U.underᶜ s b)    ρ _ _ cl = under-skips {ν = ν} s b ρ cl

  skipsᴹ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ → Skipsᴹ ν o ρ
  skipsᴹ nothing  ρ _ _ = tt
  skipsᴹ (just c) ρ s p = skips c ρ s p

  skipsᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ → Skipsᴸ ν ls ρ
  skipsᴸ []       ρ _        _        = tt
  skipsᴸ (c ∷ cs) ρ (s , ss) (p , ps) = skips c ρ s p , skipsᴸ cs ρ ss ps

-- THE STEPPER IS THE MEANING, skips included: at the root no source is
-- in scope to show first.
step-skips : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → U.meaning g []ᴬ ≃ afterᴱ []ᴬ (U.step g)
step-skips g sn pl = skips g []ᴬ sn pl tt

postulate
  -- What a sane, placed ghost's step leaves holds its parts placed.
  --
  -- REFUTED: d2d13661 without the step coming first, by a merge whose joiner lane shows its source's earlier event
  -- REFUTED: c8c55884 over a placing with each live joiner joined before its source, by a lane admitted past its source's next event
  within-step : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Withinˢ []ᴬ (U.step g)

  -- What a sane, placed ghost in order to every depth steps to is in
  -- order to every depth: the stepped node runs what the meaning runs
  -- past the step, and a rest the step opens is a part it held.
  step-deep : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Deep g []ᴬ → Deepˢ []ᴬ (U.step g)

-- A STEP KEEPS THE GHOST PLACED: atop what the step shows.
placed-after : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Placedˢ []ᴬ (U.step g)
placed-after g sn pl = placed-step []ᴬ (U.step g) (step-skips g sn pl) (proj₁ pl) (within-step g sn pl)
