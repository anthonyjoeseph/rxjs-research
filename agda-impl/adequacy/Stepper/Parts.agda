{-# OPTIONS --guardedness #-}

module adequacy.Stepper.Parts where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; [_,_])
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; Timeline; From; Frame; ix; _<ᵖ_; <ᵖ-trans;
  <ᵖ-asym; <ᵖ-below)
open import denotation.MonotonicList using (Agree; stop; stopᵀ; out⁼; skip⁼; end⁼; hush⁼)
open import denotation.NonExpansive using (Agreeˢ)
open import adequacy.Stepper.Past using (<ᵖ-past; Belowᴱ; Clear; Firsts; Past; Pastᴱ; Skips; Skipsᴸ; Skipsᴹ; Underᵐ; _≃_; afterᴱ;
  shows)

open Agreeˢ using (nowˢ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Mode; runs; over; loose; RestedS)
open import adequacy.Placed.Order using (still; Placed)
open import adequacy.Env using (Same; nagree-refl)

open _≃_
open Events∞

-- `ρ′` is `ρ` past source `i`'s step at `q` showing `a`: that source
-- runs on from what the step left, every other alike at every depth.
data Fed {A} (q : Pos) (a : Maybe A) : ∀ {Γ} → A ∈ Γ → NEnv Γ → NEnv Γ → Set₁ where
  fed-here  : ∀ {Γ} {e} (σ : Events∞ A) {ρ ρ′ : NEnv Γ} → e ≃ shows q a σ → Same ρ ρ′ → Fed q a (here refl) (e ∷ᴬ ρ) (force σ ∷ᴬ ρ′)
  fed-there : ∀ {B Γ} {i : A ∈ Γ} {e e′ : Events B} {ρ ρ′ : NEnv Γ} → e ≃ e′ → Fed q a i ρ ρ′ → Fed q a (there i) (e ∷ᴬ ρ) (e′ ∷ᴬ ρ′)

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

  -- A node reading a running source's step at `q` runs alike fed it,
  -- the source past it; a body at its source's end, alike shut.
  --
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Sane.agda restores `sane-feed`, which a stepper over a meaning with no tails fed its sources' steps through
  feed-alikeⁱ : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (i : A ∈ Γ) q (a : Maybe A) (c : U.Node Γ B) {ρ ρ′ : NEnv Γ}
              → Sane ν c → lookup ν i ≡ runs → Fed q a i ρ ρ′ → ∀ d → Agreeˢ d (U.stateᴺ c ρ) (U.stateᴺ (U.feed i q a c) ρ′)
  shut-alike : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) c {e : Events A} (ρ : NEnv Γ)
             → Sane (runs ∷ᴬ ν) b → e ≃ end c → ∀ d → Agreeˢ d (U.stateᴺ b (e ∷ᴬ ρ)) (U.stateᴺ (U.shut (here refl) c b) (end c ∷ᴬ ρ))

  -- A defer: the meaning starts with the step's event, else past a
  -- running source's shown event.
  first-defer : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (l : Later Timeline Γ A) p ns (ρ : NEnv Γ) → Placed (U.deferᶜ l p ns) ρ → Firsts ν (U.deferᶜ l p ns) ρ

  -- A rest-like's meaning starts with its step's event, else past a
  -- running source's shown event.
  first-rest     : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (n : U.Node Γ A) (ρ : NEnv Γ) → Firsts ν (U.restᶜ {B = B} n) ρ
  first-union    : ∀ {Γ B} {ν : All (λ _ → Mode) Γ} (x y : U.Node Γ B) (ρ : NEnv Γ) → Firsts ν (U.unionᶜ x y) ρ
  first-bursting : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (t : U.Node Γ A) (ρ : NEnv Γ) → Firsts ν (U.burstingᶜ {B = B} r t) ρ
  first-under    : ∀ {Γ A C B} {ν : All (λ _ → Mode) Γ} (s : U.Source Γ A) (b : U.Node (A ∷ Γ) C) (ρ : NEnv Γ) → Firsts ν (U.underᶜ {B = B} s b) ρ



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

-- What the body's step heads at, the connect's does.
head-body : ∀ {Γ A B} r (src : U.Source Γ A) (t : U.Step (A ∷ Γ) B) → U.headˢ (U.bodyˢ r src t) ≡ U.headˢ t
head-body r src (U.outˢ k a b) = refl
head-body r src (U.skipˢ k b)  = refl
head-body r src (U.endˢ c)     = refl
head-body r src U.hushˢ        = refl

-- Where an event sits; a hush, nowhere.
posᴱ : ∀ {A} → Events A → Pos
posᴱ (out q _ _) = q
posᴱ (skip q _)  = q
posᴱ (end c)     = c
posᴱ hush        = []

hush? : ∀ {A} (x : Events A) → x ≡ hush ⊎ x ≢ hush
hush? (out _ _ _) = inj₂ (λ ())
hush? (skip _ _)  = inj₂ (λ ())
hush? (end _)     = inj₂ (λ ())
hush? hush        = inj₁ refl

hushˢ? : ∀ {Γ A} (t : U.Step Γ A) → t ≡ U.hushˢ ⊎ t ≢ U.hushˢ
hushˢ? (U.outˢ _ _ _) = inj₂ (λ ())
hushˢ? (U.skipˢ _ _)  = inj₂ (λ ())
hushˢ? (U.endˢ _)     = inj₂ (λ ())
hushˢ? U.hushˢ        = inj₁ refl

-- A past event, read at where it sits.
pastᴱ-pos : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (t : U.Step Γ A) (x : Events A) → Pastᴱ ν ρ t x → x ≢ hush × Past ν (posᴱ x) (U.headˢ t) ρ
pastᴱ-pos ν ρ t (out q a σ) p = (λ ()) , p
pastᴱ-pos ν ρ t (skip q σ)  p = (λ ()) , p
pastᴱ-pos ν ρ t (end c)     p = (λ ()) , p
pastᴱ-pos ν ρ t hush        ()

pos-pastᴱ : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (t : U.Step Γ A) (x : Events A) → x ≢ hush → Past ν (posᴱ x) (U.headˢ t) ρ → Pastᴱ ν ρ t x
pos-pastᴱ ν ρ t (out q a σ) nh p = p
pos-pastᴱ ν ρ t (skip q σ)  nh p = p
pos-pastᴱ ν ρ t (end c)     nh p = p
pos-pastᴱ ν ρ t hush        nh p = ⊥-elim (nh refl)

-- A connect's body event sits where the body's did.
pastᴱ-body : ∀ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) r (σ : Events∞ A) K (t : U.Step Γ B) (x : Events B) → x ≢ hush
           → Past ν (posᴱ x) (U.headˢ t) ρ → Pastᴱ ν ρ t (M′.body r σ K x)
pastᴱ-body ν ρ r σ K t (out q a β) nh p = p
pastᴱ-body ν ρ r σ K t (skip q β)  nh p = p
pastᴱ-body ν ρ r σ K t (end c)     nh p = p
pastᴱ-body ν ρ r σ K t hush        nh p = ⊥-elim (nh refl)

before-pos : ∀ {A} K (x : Events A) → x ≢ hush → M′.before K x ≡ K <ᵖ posᴱ x
before-pos K (out q a σ) nh = refl
before-pos K (skip q σ)  nh = refl
before-pos K (end c)     nh = refl
before-pos K hush        nh = ⊥-elim (nh refl)

-- Something shows at or before `K`: not a hush.
before-false : ∀ {A} K (x : Events A) → M′.before K x ≡ false → x ≢ hush
before-false K (out q a σ) f = λ ()
before-false K (skip q σ)  f = λ ()
before-false K (end c)     f = λ ()
before-false K hush        ()

pos-shown : ∀ {A} (x : Events A) → x ≢ hush → posᴱ x <ᵖ M′.shownAt x ≡ true
pos-shown (out q a σ) nh = <ᵖ-below q []
pos-shown (skip q σ)  nh = <ᵖ-below q []
pos-shown (end c)     nh = <ᵖ-below c []
pos-shown hush        nh = ⊥-elim (nh refl)

belowᴱ-shown : ∀ {A} (x : Events A) h m → Belowᴱ x h m → M′.shownAt x <ᵖ h ≡ true × Underᵐ m (M′.shownAt x)
belowᴱ-shown (out q a σ) h m b = b
belowᴱ-shown (skip q σ)  h m b = b
belowᴱ-shown (end c)     h m b = b
belowᴱ-shown hush        h m ()

<ᵖ-either : ∀ a h k → a <ᵖ k ≡ true → a <ᵖ h ≡ true ⊎ h <ᵖ k ≡ true
<ᵖ-either a h k ak with a <ᵖ h in ah
... | true  = inj₁ refl
... | false = inj₂ (<ᵖ-past h a k ah ak)

-- A past witness re-read: each running source's shown event moved to the
-- new bounds, or else `R`.
pickᴱ : ∀ {A} {R : Set} (x : Events A) h m h′ m′ → (∀ a → a <ᵖ h ≡ true → Underᵐ m a → (a <ᵖ h′ ≡ true × Underᵐ m′ a) ⊎ R)
      → Belowᴱ x h m → Belowᴱ x h′ m′ ⊎ R
pickᴱ (out q a σ) h m h′ m′ f (b , u) = f _ b u
pickᴱ (skip q σ)  h m h′ m′ f (b , u) = f _ b u
pickᴱ (end c)     h m h′ m′ f (b , u) = f _ b u
pickᴱ hush        h m h′ m′ f ()

pick : ∀ {Γ} {R : Set} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) h m h′ m′ → (∀ a → a <ᵖ h ≡ true → Underᵐ m a → (a <ᵖ h′ ≡ true × Underᵐ m′ a) ⊎ R)
     → Past ν h m ρ → Past ν h′ m′ ρ ⊎ R
pick []ᴬ          []ᴬ      h m h′ m′ f ()
pick (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h m h′ m′ f (inj₁ b) = map₁ inj₁ (pickᴱ e h m h′ m′ f b)
pick (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h m h′ m′ f (inj₂ p) = map₁ inj₂ (pick ν ρ h m h′ m′ f p)
pick (over ∷ᴬ ν)  (e ∷ᴬ ρ) h m h′ m′ f p        = pick ν ρ h m h′ m′ f p
pick (loose ∷ᴬ ν) (e ∷ᴬ ρ) h m h′ m′ f (inj₁ b) = map₁ inj₁ (pickᴱ e h m h′ m′ f b)
pick (loose ∷ᴬ ν) (e ∷ᴬ ρ) h m h′ m′ f (inj₂ p) = map₁ inj₂ (pick ν ρ h m h′ m′ f p)

move : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) h m h′ m′ → (∀ a → a <ᵖ h ≡ true → Underᵐ m a → a <ᵖ h′ ≡ true × Underᵐ m′ a)
     → Past ν h m ρ → Past ν h′ m′ ρ
move ν ρ h m h′ m′ f p with pick {R = ⊥} ν ρ h m h′ m′ (λ a b u → inj₁ (f a b u)) p
... | inj₁ q = q
... | inj₂ ()

-- Where a step's event shows.
shownˢ : ∀ {Γ A} → U.Step Γ A → Pos
shownˢ (U.outˢ q _ _) = q ++ [ ix 0 ]
shownˢ (U.skipˢ q _)  = q ++ [ ix 0 ]
shownˢ (U.endˢ c)     = c ++ [ ix 0 ]
shownˢ U.hushˢ        = []

under-shownˢ : ∀ {Γ A} (t : U.Step Γ A) a → t ≢ U.hushˢ → Underᵐ (U.headˢ t) a → a <ᵖ shownˢ t ≡ true
under-shownˢ (U.outˢ q x c) a nh u = <ᵖ-trans a q (q ++ [ ix 0 ]) u (<ᵖ-below q [])
under-shownˢ (U.skipˢ q c)  a nh u = <ᵖ-trans a q (q ++ [ ix 0 ]) u (<ᵖ-below q [])
under-shownˢ (U.endˢ q)     a nh u = <ᵖ-trans a q (q ++ [ ix 0 ]) u (<ᵖ-below q [])
under-shownˢ U.hushˢ        a nh u = ⊥-elim (nh refl)

under-before : ∀ {Γ A} (t : U.Step Γ A) k a → U.beforeˢ k t ≡ false → Underᵐ (U.headˢ t) a → a <ᵖ k ≡ true
under-before (U.outˢ q x c) k a f u = still a q k u f
under-before (U.skipˢ q c)  k a f u = still a q k u f
under-before (U.endˢ q)     k a f u = still a q k u f
under-before U.hushˢ        k a () u

-- A step heading strictly before `k`.
Overᵐ : Maybe Pos → Pos → Set
Overᵐ nothing  k = ⊥
Overᵐ (just j) k = j <ᵖ k ≡ true

under-or : ∀ m a k → a <ᵖ k ≡ true → Underᵐ m a ⊎ Overᵐ m k
under-or nothing  a k ak = inj₁ tt
under-or (just j) a k ak = <ᵖ-either a j k ak

over-before : ∀ {Γ A} (t : U.Step Γ A) k → Overᵐ (U.headˢ t) k → U.beforeˢ k t ≡ false
over-before (U.outˢ q x c) k o = <ᵖ-asym q k o
over-before (U.skipˢ q c)  k o = <ᵖ-asym q k o
over-before (U.endˢ q)     k o = <ᵖ-asym q k o
over-before U.hushˢ        k ()

agree-shown : ∀ {Γ A} (ρ : NEnv Γ) (t : U.Step Γ A) (x : Events A) → Agree 1 x (afterᴱ ρ t) → x ≢ hush → t ≢ U.hushˢ × shownˢ t ≡ M′.shownAt x
agree-shown ρ (U.outˢ k a c) _ (out⁼ _ _)  nh = (λ ()) , refl
agree-shown ρ (U.skipˢ k c)  _ (skip⁼ _ _) nh = (λ ()) , refl
agree-shown ρ (U.endˢ k)     _ end⁼        nh = (λ ()) , refl
agree-shown ρ U.hushˢ        _ hush⁼       nh = ⊥-elim (nh refl)

agree-hush : ∀ {Γ A} (ρ : NEnv Γ) (t : U.Step Γ A) → Agree 1 hush (afterᴱ ρ t) → t ≡ U.hushˢ
agree-hush ρ (U.outˢ k a c) ()
agree-hush ρ (U.skipˢ k c)  ()
agree-hush ρ (U.endˢ k)     ()
agree-hush ρ U.hushˢ        hush⁼ = refl

-- A connect over a showing source: the source's step first when it
-- shows before the body's, else the body's.
source-split : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (tb : U.Step (A ∷ Γ) B) (s : U.Node Γ A) (ts : U.Step Γ A) → ts ≢ U.hushˢ
             → (U.beforeˢ (shownˢ ts) tb ≡ true × Σ (U.Node Γ B) (λ n → U.sourceˢ r b tb s ts ≡ U.skipˢ (shownˢ ts) n))
             ⊎ (U.beforeˢ (shownˢ ts) tb ≡ false × U.sourceˢ r b tb s ts ≡ U.bodyˢ r (U.live s) tb)
source-split r b tb s (U.outˢ q a s′) nh with U.beforeˢ (q ++ [ ix 0 ]) tb
... | true  = inj₁ (refl , _ , refl)
... | false = inj₂ (refl , refl)
source-split r b tb s (U.skipˢ q s′) nh with U.beforeˢ (q ++ [ ix 0 ]) tb
... | true  = inj₁ (refl , _ , refl)
... | false = inj₂ (refl , refl)
source-split r b tb s (U.endˢ c) nh with U.beforeˢ (c ++ [ ix 0 ]) tb
... | true  = inj₁ (refl , _ , refl)
... | false = inj₂ (refl , refl)
source-split r b tb s U.hushˢ nh = ⊥-elim (nh refl)

side-ahead : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) (x : Events A) → x ≢ hush
           → M′.side r β σ x ≡ M′.ahead r β σ (M′.shownAt x) (M′.before (M′.shownAt x) (force β))
side-ahead r β σ (out q a τ) nh = refl
side-ahead r β σ (skip q τ)  nh = refl
side-ahead r β σ (end c)     nh = refl
side-ahead r β σ hush        nh = ⊥-elim (nh refl)

ahead-split : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) k
            → (M′.before k (force β) ≡ true × Σ (Events∞ B) (λ τ → M′.ahead r β σ k (M′.before k (force β)) ≡ skip k τ))
            ⊎ (M′.before k (force β) ≡ false × M′.ahead r β σ k (M′.before k (force β)) ≡ M′.body r σ k (force β))
ahead-split r β σ k with M′.before k (force β)
... | true  = inj₁ (refl , _ , refl)
... | false = inj₂ (refl , refl)

-- The body's first event, run beside its source.
one-body : ∀ {Γ A B} (ρ : NEnv Γ) (env : NEnv (A ∷ Γ)) r (σ : Events∞ A) k (src : U.Source Γ A) (t : U.Step (A ∷ Γ) B) {x : Events B}
         → Agree 1 x (afterᴱ env t) → Agree 1 (M′.body r σ k x) (afterᴱ ρ (U.bodyˢ r src t))
one-body ρ env r σ k src (U.outˢ j a c) (out⁼ _ _)  = out⁼ stopᵀ stop
one-body ρ env r σ k src (U.skipˢ j c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-body ρ env r σ k src (U.endˢ c)     end⁼        = end⁼
one-body ρ env r σ k src U.hushˢ        hush⁼       = hush⁼

one-bodyˢ : ∀ {Γ A B} (ρ : NEnv Γ) (env : NEnv (A ∷ Γ)) r (src : U.Source Γ A) (t : U.Step (A ∷ Γ) B) {x : Events B}
          → Agree 1 x (afterᴱ env t) → Agree 1 x (afterᴱ ρ (U.bodyˢ r src t))
one-bodyˢ ρ env r src (U.outˢ j a c) (out⁼ _ _)  = out⁼ stopᵀ stop
one-bodyˢ ρ env r src (U.skipˢ j c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-bodyˢ ρ env r src (U.endˢ c)     end⁼        = end⁼
one-bodyˢ ρ env r src U.hushˢ        hush⁼       = hush⁼

-- A connect over a hushed source takes its body's step.
source-hush : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (tb : U.Step (A ∷ Γ) B) (s : U.Node Γ A) (ts : U.Step Γ A)
            → ts ≡ U.hushˢ → U.sourceˢ r b tb s ts ≡ U.bodyˢ r (U.live s) tb
source-hush r b tb s .U.hushˢ refl = refl

-- An ended connect: its rest's skip first when it shows before the
-- body's, else the body's step, every joiner told.
ended-split : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (tb : U.Step (A ∷ Γ) B) c (t : U.Node Γ A) (ts : U.Step Γ A) → RestedS ts → ts ≢ U.hushˢ
            → (U.beforeˢ (shownˢ ts) tb ≡ true × Σ (U.Node Γ B) (λ n → U.endedˢ r b tb c t ts ≡ U.skipˢ (shownˢ ts) n))
            ⊎ (U.beforeˢ (shownˢ ts) tb ≡ false × U.endedˢ r b tb c t ts ≡ U.shutˢᵗ r c t tb)
ended-split r b tb c t (U.skipˢ q t′) rs nh with U.beforeˢ (q ++ [ ix 0 ]) tb
... | true  = inj₁ (refl , _ , refl)
... | false = inj₂ (refl , refl)
ended-split r b tb c t U.hushˢ rs nh = ⊥-elim (nh refl)

ended-hush : ∀ {Γ A B} r (b : U.Node (A ∷ Γ) B) (tb : U.Step (A ∷ Γ) B) c (t : U.Node Γ A) (ts : U.Step Γ A)
           → ts ≡ U.hushˢ → U.endedˢ r b tb c t ts ≡ U.shutˢᵗ r c t tb
ended-hush r b tb c t .U.hushˢ refl = refl

head-shut : ∀ {Γ A B} r c (t : U.Node Γ A) (tb : U.Step (A ∷ Γ) B) → U.headˢ (U.shutˢᵗ r c t tb) ≡ U.headˢ tb
head-shut r c t (U.outˢ k a b) = refl
head-shut r c t (U.skipˢ k b)  = refl
head-shut r c t (U.endˢ e)     = refl
head-shut r c t U.hushˢ        = refl

-- The body's first event, run beside its ended source.
one-shut : ∀ {Γ A B} (ρ : NEnv Γ) (env : NEnv (A ∷ Γ)) r (σ : Events∞ A) k c (t : U.Node Γ A) (tb : U.Step (A ∷ Γ) B) {x : Events B}
         → Agree 1 x (afterᴱ env tb) → Agree 1 (M′.body r σ k x) (afterᴱ ρ (U.shutˢᵗ r c t tb))
one-shut ρ env r σ k c t (U.outˢ j a b) (out⁼ _ _)  = out⁼ stopᵀ stop
one-shut ρ env r σ k c t (U.skipˢ j b)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-shut ρ env r σ k c t (U.endˢ e)     end⁼        = end⁼
one-shut ρ env r σ k c t U.hushˢ        hush⁼       = hush⁼

one-shutˢ : ∀ {Γ A B} (ρ : NEnv Γ) (env : NEnv (A ∷ Γ)) r c (t : U.Node Γ A) (tb : U.Step (A ∷ Γ) B) {x : Events B}
          → Agree 1 x (afterᴱ env tb) → Agree 1 x (afterᴱ ρ (U.shutˢᵗ r c t tb))
one-shutˢ ρ env r c t (U.outˢ j a b) (out⁼ _ _)  = out⁼ stopᵀ stop
one-shutˢ ρ env r c t (U.skipˢ j b)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-shutˢ ρ env r c t (U.endˢ e)     end⁼        = end⁼
one-shutˢ ρ env r c t U.hushˢ        hush⁼       = hush⁼

-- A connect's meaning starts with its step's event, else past a running
-- source's shown event: read off its source's first event and its body's.
-- The body's event lies strictly past the source's shown one when it is
-- that witness, so it never ties the connect's step.  Live or ended, a
-- connect differs only in what its body's env heads with, how it takes
-- the body's step, and how it routes its source's.

-- A body fed its source's step, the source past it, alike.
feed-alike : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) q (a : Maybe A) (σ : Events∞ A) {e : Events A} (ρ : NEnv Γ)
           → Sane (runs ∷ᴬ ν) b → e ≃ shows q a σ → ∀ d → Agreeˢ d (U.stateᴺ b (e ∷ᴬ ρ)) (U.stateᴺ (U.feed (here refl) q a b) (force σ ∷ᴬ ρ))
feed-alike b q a σ ρ sb al = feed-alikeⁱ (here refl) q a b sb refl (fed-here σ al (λ m → nagree-refl m ρ))
