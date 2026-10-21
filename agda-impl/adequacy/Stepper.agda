{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips included: a sane, placed ghost's
-- meaning is what its step shows, then the meaning of the node it
-- leaves.  Stated at the root, where no connect's source is in scope;
-- inside a body the step is the run's next event only if it comes before
-- each running source's, its pool's and each ended source's rest.
module adequacy.Stepper where

open import Data.Bool using (Bool; true; false; T)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; map₁; [_,_])
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; map₂; uncurry)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)

open import Tree using (Later)
open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; Timeline; From; Frame; idle; ix; sub; last; _<ᵖ_; _∪_; Tail; pin;
  <ᵖ-trans; <ᵖ-irrefl; <ᵖ-asym; <ᵖ-below; <ᵖ-split; <ᵖ-step; <ᵖ-part)
open import denotation.MonotonicList using (Agree; Agreeᵀ; stop; stopᵀ; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agreeᵀ-refl; agreeᵀ-sym; agree-trans)
open import denotation.NonExpansive using (Agreeˢ; _,ˢ_; beside-ne; body-ne; before-agree; ∪-ne; burstOn-ne)
open Agreeˢ using (nowˢ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane; Saneᴹ; Saneᴸ; Mode; runs; over; loose; Told; Rested; RestedS; step-rested)
open import adequacy.Placed.Order using (Alien; Atop; Ordered; Prefix; every; ordered; still; Placed; Placedᴹ; Placedᴸ; Sides; Within)
open import adequacy.Placed.Keys using (ahead-quiet; ordered-≈; prefix-refl)
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

-- What lies before the step's head, if it has one.
Underᵐ : Maybe Pos → Pos → Set
Underᵐ nothing  s = ⊤
Underᵐ (just k) s = s <ᵖ k ≡ true

-- A source shown before `h` and before the step's head `m`.
Belowᴱ : ∀ {A} → Events A → Pos → Maybe Pos → Set
Belowᴱ hush          h m = ⊥
Belowᴱ e@(out _ _ _) h m = M′.shownAt e <ᵖ h ≡ true × Underᵐ m (M′.shownAt e)
Belowᴱ e@(skip _ _)  h m = M′.shownAt e <ᵖ h ≡ true × Underᵐ m (M′.shownAt e)
Belowᴱ e@(end _)     h m = M′.shownAt e <ᵖ h ≡ true × Underᵐ m (M′.shownAt e)

Past : ∀ {Γ} → All (λ _ → Mode) Γ → Pos → Maybe Pos → NEnv Γ → Set
Past []ᴬ          h m []ᴬ      = ⊥
Past (runs ∷ᴬ ν)  h m (e ∷ᴬ ρ) = Belowᴱ e h m ⊎ Past ν h m ρ
Past (over ∷ᴬ ν)  h m (e ∷ᴬ ρ) = Past ν h m ρ
Past (loose ∷ᴬ ν) h m (e ∷ᴬ ρ) = Belowᴱ e h m ⊎ Past ν h m ρ

-- A meaning starting past a running source's shown event, which shows
-- before the step too.
Pastᴱ : ∀ {Γ A} → All (λ _ → Mode) Γ → NEnv Γ → U.Step Γ A → Events A → Set
Pastᴱ ν ρ t hush        = ⊥
Pastᴱ ν ρ t (out q _ _) = Past ν q (U.headˢ t) ρ
Pastᴱ ν ρ t (skip q _)  = Past ν q (U.headˢ t) ρ
Pastᴱ ν ρ t (end q)     = Past ν q (U.headˢ t) ρ

-- A meaning starting with its step's event, else a joiner's.
First : ∀ {Γ A} → All (λ _ → Mode) Γ → NEnv Γ → U.Step Γ A → Events A → Set
First ν ρ t x = Agree 1 x (afterᴱ ρ t) ⊎ Pastᴱ ν ρ t x

Firsts : ∀ {Γ A} → All (λ _ → Mode) Γ → U.Node Γ A → NEnv Γ → Set
Firsts ν c ρ = First ν ρ (U.step c) (U.meaning c ρ)

-- At or past `s`, then past `h`: past `k` once past `s`.
<ᵖ-past : ∀ k s h → s <ᵖ k ≡ false → s <ᵖ h ≡ true → k <ᵖ h ≡ true
<ᵖ-past k s h f b with <ᵖ-split k s f
... | inj₁ lt   = <ᵖ-trans k s h lt b
... | inj₂ refl = b

-- A source shown before `h`, before what lies past `h`; before a step's
-- head, before a later one's.
belowᴱ-on : ∀ {A} (e : Events A) h h′ m → Belowᴱ e h m → h <ᵖ h′ ≡ true → Belowᴱ e h′ m
belowᴱ-on hush        h h′ m () lt
belowᴱ-on (out q a σ) h h′ m (b , u) lt = <ᵖ-trans (q ++ [ ix 0 ]) h h′ b lt , u
belowᴱ-on (skip q σ)  h h′ m (b , u) lt = <ᵖ-trans (q ++ [ ix 0 ]) h h′ b lt , u
belowᴱ-on (end c)     h h′ m (b , u) lt = <ᵖ-trans (c ++ [ ix 0 ]) h h′ b lt , u

belowᴱ-under : ∀ {A} (e : Events A) h m m′ → (∀ s → Underᵐ m s → Underᵐ m′ s) → Belowᴱ e h m → Belowᴱ e h m′
belowᴱ-under hush        h m m′ f ()
belowᴱ-under (out q a σ) h m m′ f (b , u) = b , f _ u
belowᴱ-under (skip q σ)  h m m′ f (b , u) = b , f _ u
belowᴱ-under (end c)     h m m′ f (b , u) = b , f _ u

past-on : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) h h′ m → Past ν h m ρ → h <ᵖ h′ ≡ true → Past ν h′ m ρ
past-on []ᴬ          []ᴬ      h h′ m ()       lt
past-on (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h h′ m (inj₁ b) lt = inj₁ (belowᴱ-on e h h′ m b lt)
past-on (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h h′ m (inj₂ p) lt = inj₂ (past-on ν ρ h h′ m p lt)
past-on (over ∷ᴬ ν)  (e ∷ᴬ ρ) h h′ m p        lt = past-on ν ρ h h′ m p lt
past-on (loose ∷ᴬ ν) (e ∷ᴬ ρ) h h′ m (inj₁ b) lt = inj₁ (belowᴱ-on e h h′ m b lt)
past-on (loose ∷ᴬ ν) (e ∷ᴬ ρ) h h′ m (inj₂ p) lt = inj₂ (past-on ν ρ h h′ m p lt)

past-under : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) h m m′ → (∀ s → Underᵐ m s → Underᵐ m′ s) → Past ν h m ρ → Past ν h m′ ρ
past-under []ᴬ          []ᴬ      h m m′ f ()
past-under (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h m m′ f (inj₁ b) = inj₁ (belowᴱ-under e h m m′ f b)
past-under (runs ∷ᴬ ν)  (e ∷ᴬ ρ) h m m′ f (inj₂ p) = inj₂ (past-under ν ρ h m m′ f p)
past-under (over ∷ᴬ ν)  (e ∷ᴬ ρ) h m m′ f p        = past-under ν ρ h m m′ f p
past-under (loose ∷ᴬ ν) (e ∷ᴬ ρ) h m m′ f (inj₁ b) = inj₁ (belowᴱ-under e h m m′ f b)
past-under (loose ∷ᴬ ν) (e ∷ᴬ ρ) h m m′ f (inj₂ p) = inj₂ (past-under ν ρ h m m′ f p)

-- The same head, the same positions under it.
under-≡ : ∀ {m m′} → m ≡ m′ → ∀ s → Underᵐ m s → Underᵐ m′ s
under-≡ refl s u = u

-- A take's step heads at or past its source's.
under-take : ∀ {Γ A} i (p : A → Bool) (t : U.Step Γ A) s → Underᵐ (U.headˢ t) s → Underᵐ (U.headˢ (U.takeWhileˢ i p t)) s
under-take i     p (U.skipˢ k c)  s u = u
under-take i     p (U.endˢ k)     s u = u
under-take i     p U.hushˢ        s u = u
under-take true  p (U.outˢ k a c) s u with p a
... | true  = u
... | false = <ᵖ-trans s k (k ++ [ ix 0 ]) u (<ᵖ-below k [])
under-take false p (U.outˢ k a c) s u with p a
... | true  = u
... | false = <ᵖ-trans s k (k ++ [ last ]) u (<ᵖ-below k [])

-- A value changed, a running total, or a take start where their source
-- does, a take's end just past it.
past-map : ∀ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (f : A → B) (t : U.Step Γ A) (x : Events A) → Pastᴱ ν ρ t x → Pastᴱ ν ρ (U.mapˢ f t) (M′.mapᴱ f x)
past-map ν ρ f t hush        ()
past-map ν ρ f t (out q a σ) pa = past-under ν ρ q _ _ (under-≡ (sym (head-map f t))) pa
past-map ν ρ f t (skip q σ)  pa = past-under ν ρ q _ _ (under-≡ (sym (head-map f t))) pa
past-map ν ρ f t (end c)     pa = past-under ν ρ c _ _ (under-≡ (sym (head-map f t))) pa

past-scan : ∀ {Γ A B} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (f : B → A → B) z (t : U.Step Γ A) (x : Events A) → Pastᴱ ν ρ t x → Pastᴱ ν ρ (U.scanˢ f z t) (M′.scanᴱ f z x)
past-scan ν ρ f z t hush        ()
past-scan ν ρ f z t (out q a σ) pa = past-under ν ρ q _ _ (under-≡ (sym (head-scan f z t))) pa
past-scan ν ρ f z t (skip q σ)  pa = past-under ν ρ q _ _ (under-≡ (sym (head-scan f z t))) pa
past-scan ν ρ f z t (end c)     pa = past-under ν ρ c _ _ (under-≡ (sym (head-scan f z t))) pa

past-take : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) i (p : A → Bool) (t : U.Step Γ A) (x : Events A) → Pastᴱ ν ρ t x → Pastᴱ ν ρ (U.takeWhileˢ i p t) (M′.takeWhileᴱ i p x)
past-take ν ρ i     p t hush        ()
past-take ν ρ i     p t (skip q σ)  pa = past-under ν ρ q _ _ (under-take i p t) pa
past-take ν ρ i     p t (end c)     pa = past-under ν ρ c _ _ (under-take i p t) pa
past-take ν ρ true  p t (out q a σ) pa with p a
... | true  = past-under ν ρ q _ _ (under-take true p t) pa
... | false = past-on ν ρ q (q ++ [ ix 0 ]) _ (past-under ν ρ q _ _ (under-take true p t) pa) (<ᵖ-below q [])
past-take ν ρ false p t (out q a σ) pa with p a
... | true  = past-under ν ρ q _ _ (under-take false p t) pa
... | false = past-on ν ρ q (q ++ [ last ]) _ (past-under ν ρ q _ _ (under-take false p t) pa) (<ᵖ-below q [])

-- One event agreed, its value changed, totalled or taken.
one-map : ∀ {Γ A B} (ρ : NEnv Γ) (f : A → B) (t : U.Step Γ A) {x : Events A} → Agree 1 x (afterᴱ ρ t) → Agree 1 (M′.mapᴱ f x) (afterᴱ ρ (U.mapˢ f t))
one-map ρ f (U.outˢ k a c) (out⁼ _ _)  = out⁼ stopᵀ stop
one-map ρ f (U.skipˢ k c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-map ρ f (U.endˢ k)     end⁼        = end⁼
one-map ρ f U.hushˢ        hush⁼       = hush⁼

one-scan : ∀ {Γ A B} (ρ : NEnv Γ) (f : B → A → B) z (t : U.Step Γ A) {x : Events A} → Agree 1 x (afterᴱ ρ t) → Agree 1 (M′.scanᴱ f z x) (afterᴱ ρ (U.scanˢ f z t))
one-scan ρ f z (U.outˢ k a c) (out⁼ _ _)  = out⁼ stopᵀ stop
one-scan ρ f z (U.skipˢ k c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-scan ρ f z (U.endˢ k)     end⁼        = end⁼
one-scan ρ f z U.hushˢ        hush⁼       = hush⁼

one-take : ∀ {Γ A} (ρ : NEnv Γ) i (p : A → Bool) (t : U.Step Γ A) {x : Events A} → Agree 1 x (afterᴱ ρ t) → Agree 1 (M′.takeWhileᴱ i p x) (afterᴱ ρ (U.takeWhileˢ i p t))
one-take ρ i     p (U.skipˢ k c)  (skip⁼ _ _) = skip⁼ stopᵀ stop
one-take ρ i     p (U.endˢ k)     end⁼        = end⁼
one-take ρ i     p U.hushˢ        hush⁼       = hush⁼
one-take ρ true  p (U.outˢ k a c) (out⁼ _ _) with p a
... | true  = out⁼ stopᵀ stop
... | false = out⁼ stopᵀ stop
one-take ρ false p (U.outˢ k a c) (out⁼ _ _) with p a
... | true  = out⁼ stopᵀ stop
... | false = end⁼

-- A running source's shown event, before what the joiner shows.
past-at : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (i : A ∈ Γ) {h m} → Told (lookup ν i) nothing → Belowᴱ (lookup ρ i) h m → Past ν h m ρ
past-at (runs ∷ᴬ ν)  (e ∷ᴬ ρ) (here refl) t  b = inj₁ b
past-at (loose ∷ᴬ ν) (e ∷ᴬ ρ) (here refl) t  b = inj₁ b
past-at (over ∷ᴬ ν)  (e ∷ᴬ ρ) (here refl) () b
past-at (runs ∷ᴬ ν)  (e ∷ᴬ ρ) (there i)   t  b = inj₂ (past-at ν ρ i t b)
past-at (loose ∷ᴬ ν) (e ∷ᴬ ρ) (there i)   t  b = inj₂ (past-at ν ρ i t b)
past-at (over ∷ᴬ ν)  (e ∷ᴬ ρ) (there i)   t  b = past-at ν ρ i t b

-- Joined apart from where its source shows next and not before it, the
-- joiner's skip lies past where the source's event shows.
apart-past : ∀ p q → p ≢ q → p <ᵖ q ≡ false → (q ++ [ ix 0 ]) <ᵖ (p ++ [ ix 0 ]) ≡ true
apart-past p q ne f with <ᵖ-split q p f
... | inj₁ qp   = <ᵖ-past (q ++ [ ix 0 ]) p (p ++ [ ix 0 ]) (<ᵖ-step q p qp) (<ᵖ-below p [])
... | inj₂ refl = ⊥-elim (ne refl)

apart-end : ∀ p c → p ≢ c → p <ᵖ c ≡ false → (c ++ [ ix 0 ]) <ᵖ (p ++ [ last ]) ≡ true
apart-end p c ne f with <ᵖ-split c p f
... | inj₁ cp   = <ᵖ-past (c ++ [ ix 0 ]) p (p ++ [ last ]) (<ᵖ-step c p cp) (<ᵖ-below p [])
... | inj₂ refl = ⊥-elim (ne refl)

-- Where the source shows, before what it delivers to a joiner.
shown-sub : ∀ q p → (q ++ [ ix 0 ]) <ᵖ (q ++ [ sub p ]) ≡ true
shown-sub q p = <ᵖ-part q [] [] refl

-- An unfed joiner shows its source rejoined: nothing, or past where the
-- source's next step shows.
rejoin-first : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) (i : A ∈ Γ) p → Told (lookup ν i) nothing
             → (e : Events A) → lookup ρ i ≡ e → Alien p e → First ν ρ U.hushˢ (M′.rejoin p e)
rejoin-first ν ρ i p t hush        eq al = inj₁ hush⁼
rejoin-first ν ρ i p t (out q a σ) eq al with p <ᵖ q in f
... | true  = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (q ++ [ sub p ]) nothing) (sym eq) (shown-sub q p , tt)))
... | false = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (p ++ [ ix 0 ]) nothing) (sym eq) (apart-past p q (λ pq → proj₁ (every al) (inj₁ (subst (Prefix p) pq (prefix-refl p)))) f , tt)))
rejoin-first ν ρ i p t (skip q σ)  eq al with p <ᵖ q in f
... | true  = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (q ++ [ sub p ]) nothing) (sym eq) (shown-sub q p , tt)))
... | false = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (p ++ [ ix 0 ]) nothing) (sym eq) (apart-past p q (λ pq → proj₁ (every al) (inj₁ (subst (Prefix p) pq (prefix-refl p)))) f , tt)))
rejoin-first ν ρ i p t (end c)     eq al with p <ᵖ c in f
... | true  = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (c ++ [ sub p ]) nothing) (sym eq) (shown-sub c p , tt)))
... | false = inj₂ (past-at ν ρ i t (subst (λ e → Belowᴱ e (p ++ [ last ]) nothing) (sym eq) (apart-end p c (λ pc → every al (inj₁ (subst (Prefix p) pc (prefix-refl p)))) f , tt)))

-- A joiner shows what it was fed, then its end once told it, else its
-- source rejoined.
first-join : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (i : A ∈ Γ) p xs e (ρ : NEnv Γ) → Told (lookup ν i) e → Alien p (lookup ρ i)
           → Firsts ν (U.joinᶜ i p xs e) ρ
first-join ν i p ((q , just a) ∷ xs) e ρ t al = inj₁ (out⁼ stopᵀ stop)
first-join ν i p ((q , nothing) ∷ xs) e ρ t al = inj₁ (skip⁼ stopᵀ stop)
first-join ν i p [] (just c) ρ t al = inj₁ end⁼
first-join ν i p [] nothing ρ t al = rejoin-first ν ρ i p t (lookup ρ i) refl al

-- What a source shown at or past `k` shows before, lies past `k`.
aboveᴱ : ∀ {A} k h m (e : Events A) → Floorᴱ k e → Belowᴱ e h m → k <ᵖ h ≡ true
aboveᴱ k h m hush        f ()
aboveᴱ k h m (out q a σ) f b = <ᵖ-past k (q ++ [ ix 0 ]) h f (proj₁ b)
aboveᴱ k h m (skip q σ)  f b = <ᵖ-past k (q ++ [ ix 0 ]) h f (proj₁ b)
aboveᴱ k h m (end c)     f b = <ᵖ-past k (c ++ [ ix 0 ]) h f (proj₁ b)

above : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) k h m → Floor ν k ρ → Past ν h m ρ → k <ᵖ h ≡ true
above []ᴬ          []ᴬ      k h m f        ()
above (runs ∷ᴬ ν)  (e ∷ᴬ ρ) k h m (fe , f) (inj₁ b) = aboveᴱ k h m e fe b
above (runs ∷ᴬ ν)  (e ∷ᴬ ρ) k h m (fe , f) (inj₂ p) = above ν ρ k h m f p
above (over ∷ᴬ ν)  (e ∷ᴬ ρ) k h m f        p        = above ν ρ k h m f p
above (loose ∷ᴬ ν) (e ∷ᴬ ρ) k h m (fe , f) (inj₁ b) = aboveᴱ k h m e fe b
above (loose ∷ᴬ ν) (e ∷ᴬ ρ) k h m (fe , f) (inj₂ p) = above ν ρ k h m f p

past-before : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) k (t : U.Step Γ A) (x : Events A) → Floor ν k ρ → Pastᴱ ν ρ t x → M′.before k x ≡ true
past-before ν ρ k t hush        f ()
past-before ν ρ k t (out q _ _) f p = above ν ρ k q _ f p
past-before ν ρ k t (skip q _)  f p = above ν ρ k q _ f p
past-before ν ρ k t (end q)     f p = above ν ρ k q _ f p

before-after : ∀ {Γ A} (ρ : NEnv Γ) k (t : U.Step Γ A) → M′.before k (afterᴱ ρ t) ≡ U.beforeˢ k t
before-after ρ k (U.outˢ q a c) = refl
before-after ρ k (U.skipˢ q c)  = refl
before-after ρ k (U.endˢ q)     = refl
before-after ρ k U.hushˢ        = refl

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

  -- A flatMap, a defer: the meaning starts with
  -- the step's event, else past a running source's shown event.
  first-flat  : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} op (g : A → Pos → U.Node Γ B) o ls qs pl (ρ : NEnv Γ)
              → Sane ν (U.flatMapᶜ op g o ls qs pl) → Placed (U.flatMapᶜ op g o ls qs pl) ρ → Firsts ν (U.flatMapᶜ op g o ls qs pl) ρ
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
module Beside {Γ A B} (ν : All (λ _ → Mode) Γ) (m₀ : Mode) r (ρ : NEnv Γ) (x₀ : Events A)
              (e : Events A) (σ : Events∞ A) (ts : U.Step Γ A) (β : Events∞ B) (tb : U.Step (A ∷ Γ) B)
              (bodyF : U.Step (A ∷ Γ) B → U.Step Γ B) (step : U.Step Γ B)
              (entry : ∀ {h m} → Past (m₀ ∷ᴬ ν) h m (x₀ ∷ᴬ ρ) → Belowᴱ e h m ⊎ Past ν h m ρ)
              (head-F : U.headˢ (bodyF tb) ≡ U.headˢ tb)
              (one-F : ∀ k {x} → Agree 1 x (afterᴱ (x₀ ∷ᴬ ρ) tb) → Agree 1 (M′.body r σ k x) (afterᴱ ρ (bodyF tb)))
              (one-Fˢ : ∀ {x} → Agree 1 x (afterᴱ (x₀ ∷ᴬ ρ) tb) → Agree 1 x (afterᴱ ρ (bodyF tb)))
              (quiet : ts ≡ U.hushˢ → step ≡ bodyF tb)
              (route : ts ≢ U.hushˢ → (U.beforeˢ (shownˢ ts) tb ≡ true × Σ (U.Node Γ B) (λ n → step ≡ U.skipˢ (shownˢ ts) n))
                                     ⊎ (U.beforeˢ (shownˢ ts) tb ≡ false × step ≡ bodyF tb)) where

  env : NEnv (A ∷ Γ)
  env = x₀ ∷ᴬ ρ

  mb : Events B
  mb = force β

  K : Pos
  K = M′.shownAt e

  -- The body's past event: the head entry's witness, or one in scope.
  seen : Pastᴱ (m₀ ∷ᴬ ν) env tb mb → mb ≢ hush × (Belowᴱ e (posᴱ mb) (U.headˢ tb) ⊎ Past ν (posᴱ mb) (U.headˢ tb) ρ)
  seen pa = map₂ entry (pastᴱ-pos (m₀ ∷ᴬ ν) env tb mb pa)

  case-seen : ∀ {X : Set} → Pastᴱ (m₀ ∷ᴬ ν) env tb mb
            → (mb ≢ hush → Belowᴱ e (posᴱ mb) (U.headˢ tb) → X) → (mb ≢ hush → Past ν (posᴱ mb) (U.headˢ tb) ρ → X) → X
  case-seen pa f g = uncurry (λ nh → [_,_] (f nh) (g nh)) (seen pa)

  -- The body's event is no witness past the source's when the body shows
  -- at or before it.
  below-false : ∀ {m} → Belowᴱ e (posᴱ mb) m → M′.before K mb ≡ false → mb ≢ hush → ⊥
  below-false bl ff nh = ⊥-elim (subst T (trans (sym (proj₁ (belowᴱ-shown e (posᴱ mb) _ bl))) (trans (sym (before-pos K mb nh)) ff)) tt)

  -- The source shown first, past a body stepping no later.
  skip-past : U.beforeˢ K tb ≡ false → M′.before K mb ≡ true → First (m₀ ∷ᴬ ν) env tb mb → Past ν K (U.headˢ tb) ρ
  skip-past bf bt (inj₁ ag) = ⊥-elim (subst T (trans (sym bt) (trans (before-agree K ag) (trans (before-after env K tb) bf))) tt)
  skip-past bf bt (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (subst T (trans (sym (under-before tb K K bf (proj₂ (belowᴱ-shown e (posᴱ mb) (U.headˢ tb) bl)))) (<ᵖ-irrefl K)) tt))
    (λ nh px → move ν ρ (posᴱ mb) (U.headˢ tb) K (U.headˢ tb) (λ a ab u → under-before tb K a bf u , u) px)

  -- The body shown first, past a source step `k` showing no earlier.
  skip-body : ∀ k → U.beforeˢ k tb ≡ true → k <ᵖ posᴱ mb ≡ false → M′.before K mb ≡ false → First (m₀ ∷ᴬ ν) env tb mb
            → Past ν (posᴱ mb) (just k) ρ
  skip-body k bt kf ff (inj₁ ag) =
    ⊥-elim (subst T (trans (sym bt) (trans (sym (before-after env k tb)) (trans (sym (before-agree k ag)) (trans (before-pos k mb (before-false K mb ff)) kf)))) tt)
  skip-body k bt kf ff (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (below-false bl ff nh))
    (λ nh px → move ν ρ (posᴱ mb) (U.headˢ tb) (posᴱ mb) (just k) (λ a ab u → ab , still a (posᴱ mb) k ab kf) px)

  -- The body's step taken, shown first.
  body-body : M′.before K mb ≡ false → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ (bodyF tb) (M′.body r σ K mb)
  body-body ff (inj₁ ag) = inj₁ (one-F K ag)
  body-body ff (inj₂ pa) = case-seen pa
    (λ nh bl → ⊥-elim (below-false bl ff nh))
    (λ nh px → inj₂ (pastᴱ-body ν ρ r σ K (bodyF tb) mb nh (past-under ν ρ (posᴱ mb) _ _ (under-≡ (sym head-F)) px)))

  -- The body's step taken, the source shown first.
  body-skip : ∀ {τ} → U.beforeˢ K tb ≡ false → M′.before K mb ≡ true → First (m₀ ∷ᴬ ν) env tb mb
            → First ν ρ (bodyF tb) (skip K τ)
  body-skip bf bt fb = inj₂ (past-under ν ρ K _ _ (under-≡ (sym head-F)) (skip-past bf bt fb))

  -- The source hushed: the connect is its body.
  hushed : e ≡ hush → First ν ρ ts e → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ step (M′.side r β σ e)
  hushed eq fs fb = subst (λ x → First ν ρ step (M′.side r β σ x)) (sym eq) (subst (λ t → First ν ρ t mb) (sym (quiet (hushes fs))) (body fb))
    where
      hushes : First ν ρ ts e → ts ≡ U.hushˢ
      hushes (inj₁ ag) = agree-hush ρ ts (subst (λ x → Agree 1 x (afterᴱ ρ ts)) eq ag)
      hushes (inj₂ pa) = ⊥-elim (proj₁ (pastᴱ-pos ν ρ ts e pa) eq)
      past : mb ≢ hush × (Belowᴱ e (posᴱ mb) (U.headˢ tb) ⊎ Past ν (posᴱ mb) (U.headˢ tb) ρ) → First ν ρ (bodyF tb) mb
      past (nh , inj₁ bl) = ⊥-elim (subst (λ x → Belowᴱ x (posᴱ mb) (U.headˢ tb)) eq bl)
      past (nh , inj₂ px) = inj₂ (pos-pastᴱ ν ρ _ mb nh (past-under ν ρ (posᴱ mb) _ _ (under-≡ (sym head-F)) px))
      body : First (m₀ ∷ᴬ ν) env tb mb → First ν ρ (bodyF tb) mb
      body (inj₁ ag) = inj₁ (one-Fˢ ag)
      body (inj₂ pa) = case-seen pa (λ nh bl → past (nh , inj₁ bl)) (λ nh px → past (nh , inj₂ px))

  -- What the connect shows: the source's shown step when the body shows
  -- past it, else the body's event.
  Shape : Events B → Set
  Shape M = (M′.before K mb ≡ true × Σ (Events∞ B) (λ τ → M ≡ skip K τ)) ⊎ (M′.before K mb ≡ false × M ≡ M′.body r σ K mb)

  -- The source shown, its step agreeing: the connect takes whichever
  -- step shows first.
  told : e ≢ hush → Agree 1 e (afterᴱ ρ ts) → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ step M
  told nh ag fb sp with agree-shown ρ ts e ag nh
  ... | tnh , sh with route tnh | sp
  ...   | inj₁ (sbt , n , eqS) | inj₁ (bt , τ , refl) =
            subst (λ t → First ν ρ t (skip K τ)) (sym eqS) (inj₁ (subst (λ k → Agree 1 (skip K τ) (skip k _)) (sym sh) (skip⁼ stopᵀ stop)))
  ...   | inj₁ (sbt , n , eqS) | inj₂ (bf , refl) =
            subst (λ t → First ν ρ t (M′.body r σ K mb)) (sym eqS)
              (inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf)
                (skip-body (shownˢ ts) sbt (subst (λ k → k <ᵖ posᴱ mb ≡ false) (sym sh) (trans (sym (before-pos K mb (before-false K mb bf))) bf)) bf fb)))
  ...   | inj₂ (sbf , eqS) | inj₁ (bt , τ , refl) =
            subst (λ t → First ν ρ t (skip K τ)) (sym eqS) (body-skip (subst (λ k → U.beforeˢ k tb ≡ false) sh sbf) bt fb)
  ...   | inj₂ (sbf , eqS) | inj₂ (bf , refl) =
            subst (λ t → First ν ρ t (M′.body r σ K mb)) (sym eqS) (body-body bf fb)

  -- The source preempted by a running source's witness `px`, the body's
  -- step taken: the witness kept, or the body's when it shows first.
  bodied : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ (bodyF tb) M
  bodied nh px fb (inj₂ (bf , refl)) = body-body bf fb
  bodied nh px fb (inj₁ (bt , τ , refl))
    with pick ν ρ (posᴱ e) (U.headˢ ts) K (U.headˢ tb) (λ a ab u → map₁ ((<ᵖ-trans a (posᴱ e) K ab (pos-shown e nh)) ,_) (under-or (U.headˢ tb) a K (<ᵖ-trans a (posᴱ e) K ab (pos-shown e nh)))) px
  ... | inj₁ p = inj₂ (past-under ν ρ K _ _ (under-≡ (sym head-F)) p)
  ... | inj₂ o = body-skip (over-before tb K o) bt fb

  -- The source preempted, its step taken: the witness kept, or the body's
  -- when it shows first.
  skipped : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → (tnh : ts ≢ U.hushˢ) → U.beforeˢ (shownˢ ts) tb ≡ true
          → ∀ n {M} → Shape M → First ν ρ (U.skipˢ (shownˢ ts) n) M
  skipped nh px fb tnh sbt n (inj₁ (bt , τ , refl)) =
    inj₂ (move ν ρ (posᴱ e) (U.headˢ ts) K (just (shownˢ ts)) (λ a ab u → <ᵖ-trans a (posᴱ e) K ab (pos-shown e nh) , under-shownˢ ts a tnh u) px)
  skipped nh px fb tnh sbt n (inj₂ (bf , refl))
    with pick ν ρ (posᴱ e) (U.headˢ ts) (posᴱ mb) (just (shownˢ ts)) (λ a ab u → map₁ (_, under-shownˢ ts a tnh u) (<ᵖ-either a (posᴱ mb) (shownˢ ts) (under-shownˢ ts a tnh u))) px
  ... | inj₁ p  = inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf) p)
  ... | inj₂ hk = inj₂ (pastᴱ-body ν ρ r σ K _ mb (before-false K mb bf) (skip-body (shownˢ ts) sbt (<ᵖ-asym (posᴱ mb) (shownˢ ts) hk) bf fb))

  preempted : e ≢ hush → Past ν (posᴱ e) (U.headˢ ts) ρ → First (m₀ ∷ᴬ ν) env tb mb → ∀ {M} → Shape M → First ν ρ step M
  preempted nh px fb sp with hushˢ? ts
  ... | inj₁ eqt = subst (λ t → First ν ρ t _) (sym (quiet eqt)) (bodied nh px fb sp)
  ... | inj₂ tnh with route tnh
  ...   | inj₂ (sbf , eqS)     = subst (λ t → First ν ρ t _) (sym eqS) (bodied nh px fb sp)
  ...   | inj₁ (sbt , n , eqS) = subst (λ t → First ν ρ t _) (sym eqS) (skipped nh px fb tnh sbt n sp)

  conn : First ν ρ ts e → First (m₀ ∷ᴬ ν) env tb mb → First ν ρ step (M′.side r β σ e)
  conn fs fb = by (hush? e) fs
    where
      shape : Shape (M′.ahead r β σ K (M′.before K mb))
      shape = ahead-split r β σ K
      by : e ≡ hush ⊎ e ≢ hush → First ν ρ ts e → First ν ρ step (M′.side r β σ e)
      by (inj₁ eq) fs′       = hushed eq fs′ fb
      by (inj₂ nh) (inj₁ ag) = subst (First ν ρ step) (sym (side-ahead r β σ e nh)) (told nh ag fb shape)
      by (inj₂ nh) (inj₂ pa) = subst (First ν ρ step) (sym (side-ahead r β σ e nh)) (preempted nh (proj₂ (pastᴱ-pos ν ρ ts e pa)) fb shape)

-- A rest-like's meaning starts with its step's event, else past a
-- running source's shown event.
first-rested : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (t : U.Node Γ A) (ρ : NEnv Γ) → Rested t → Firsts ν t ρ
first-rested ν (U.restᶜ n)       ρ _ = first-rest {ν = ν} n ρ
first-rested ν U.idleᶜ           ρ _ = inj₁ hush⁼
first-rested ν (U.unionᶜ x y)    ρ _ = first-union {ν = ν} x y ρ
first-rested ν (U.burstingᶜ r t) ρ _ = first-bursting {ν = ν} r t ρ
first-rested ν (U.underᶜ s b)    ρ _ = first-under {ν = ν} s b ρ

-- A node's meaning starts with the event its step shows, else past
-- a running source's shown event: a joiner's.
first : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) → Sane ν c → Placed c ρ → Firsts ν c ρ
first (U.framesᶜ τ e m)  ρ _ _ = inj₁ (agreeing (frames-after ρ τ e m) 1)
first (U.burstᶜ τ r i b) ρ _ _ = inj₁ (agreeing (burst-after ρ τ r i b) 1)
first (U.ofᶜ p i xs)     ρ _ _ = inj₁ (agreeing (of-after ρ p i xs) 1)
first {ν = ν} (U.mapᶜ f c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-map ρ f (U.step c) ag)
... | inj₂ pa = inj₂ (past-map ν ρ f (U.step c) (U.meaning c ρ) pa)
first {ν = ν} (U.scanᶜ f z c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-scan ρ f z (U.step c) ag)
... | inj₂ pa = inj₂ (past-scan ν ρ f z (U.step c) (U.meaning c ρ) pa)
first {ν = ν} (U.takeWhileᶜ i p c) ρ sn (_ , pl) with first c ρ sn pl
... | inj₁ ag = inj₁ (one-take ρ i p (U.step c) ag)
... | inj₂ pa = inj₂ (past-take ν ρ i p (U.step c) (U.meaning c ρ) pa)
first (U.flatMapᶜ op g o ls qs pl) ρ sn pd = first-flat op g o ls qs pl ρ sn pd
first {ν = ν} (U.joinᶜ i p xs e) ρ sn (_ , al) = first-join ν i p xs e ρ sn al
first {ν = ν} (U.connectᶜ r b (U.live s)) ρ (sb , ss) (_ , pb , ps , _) =
  Beside.conn ν runs r ρ (U.meaning s ρ) (U.meaning s ρ) (U.stateᴺ s ρ) (U.step s) (U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)) (U.step b)
    (U.bodyˢ r (U.live s)) (U.step (U.connectᶜ r b (U.live s))) (λ p → p) (head-body r (U.live s) (U.step b))
    (λ k → one-body ρ _ r (U.stateᴺ s ρ) k (U.live s) (U.step b)) (one-bodyˢ ρ _ r (U.live s) (U.step b))
    (source-hush r b (U.step b) s (U.step s)) (source-split r b (U.step b) s (U.step s))
    (first s ρ ss ps) (first b (U.meaning s ρ ∷ᴬ ρ) sb pb)
first {ν = ν} (U.connectᶜ r b (U.ended c t)) ρ (sb , rt) (_ , pb) =
  Beside.conn ν over r ρ (end c) (U.meaning t ρ) (U.stateᴺ t ρ) (U.step t) (U.stateᴺ b (end c ∷ᴬ ρ)) (U.step b)
    (U.shutˢᵗ r c t) (U.step (U.connectᶜ r b (U.ended c t))) inj₂ (head-shut r c t (U.step b))
    (λ k → one-shut ρ _ r (U.stateᴺ t ρ) k c t (U.step b)) (one-shutˢ ρ _ r c t (U.step b))
    (ended-hush r b (U.step b) c t (U.step t)) (ended-split r b (U.step b) c t (U.step t) (step-rested t rt))
    (first-rested ν t ρ rt) (first b (end c ∷ᴬ ρ) sb pb)
first {ν = ν} (U.deferᶜ l p ns) ρ _ pd = first-defer {ν = ν} l p ns ρ pd
first (U.endingᶜ p n)   ρ _ _ = inj₁ end⁼
first {ν = ν} (U.restᶜ n)       ρ _ _ = first-rest {ν = ν} n ρ
first U.idleᶜ           ρ _ _ = inj₁ hush⁼
first {ν = ν} (U.unionᶜ x y)    ρ _ _ = first-union {ν = ν} x y ρ
first {ν = ν} (U.burstingᶜ r t) ρ _ _ = first-bursting {ν = ν} r t ρ
first {ν = ν} (U.underᶜ s b)    ρ _ _ = first-under {ν = ν} s b ρ

-- A node whose step shows past `k`, among sources showing nothing
-- before `k`, shows nothing before it.
floor : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (c : U.Node Γ A) (ρ : NEnv Γ) k → Sane ν c → Placed c ρ
      → U.beforeˢ k (U.step c) ≡ true → Floor ν k ρ → M′.before k (U.meaning c ρ) ≡ true
floor {ν = ν} c ρ k sn pl bs fl with first c ρ sn pl
... | inj₁ ag = trans (before-agree k ag) (trans (before-after ρ k (U.step c)) bs)
... | inj₂ pa = past-before ν ρ k (U.step c) (U.meaning c ρ) fl pa

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

  kept-side : U.meaning s ρ ≡ hush → ∀ (b′ : U.Node (A ∷ Γ) B) d → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ (U.meaning s ρ))
  kept-side eq b′ d = subst (λ x → Agree d (U.meaning b′ env) (M′.side r (U.stateᴺ b′ env) σ x)) (sym eq) (agree-refl d _)

  -- The source hushed: the connect is its body, nothing left running.
  hushed : U.meaning s ρ ≡ hush → (∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle)
         → ∀ t → U.meaning b env ≃ afterᴱ env t → ∀ d → Agree d (U.meaning b env) (afterᴱ ρ (U.bodyˢ r (U.live s) t))
  hushed eq hc t al zero = stop
  hushed eq hc (U.outˢ k a b′) al (suc d) = agree-trans (agreeing al (suc d)) (out⁼ (left eq hc b′ d) (kept-side eq b′ d))
  hushed eq hc (U.skipˢ k b′)  al (suc d) = agree-trans (agreeing al (suc d)) (skip⁼ (left eq hc b′ d) (kept-side eq b′ d))
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

-- Not past just beyond `q`, and neither `q` nor just beyond it: before
-- `q`.
shy-order : ∀ q k → (q ++ [ ix 0 ]) <ᵖ k ≡ false → k ≢ q → k ≢ q ++ [ ix 0 ] → k <ᵖ q ≡ true
shy-order q k f n₀ n₁ with <ᵖ-split k (q ++ [ ix 0 ]) f
... | inj₂ e = ⊥-elim (n₁ e)
... | inj₁ lt with k <ᵖ q in kq
...   | true  = refl
...   | false with <ᵖ-split q k kq
...     | inj₂ refl = ⊥-elim (n₀ refl)
...     | inj₁ qk with trans (sym lt) (<ᵖ-step q k qk)
...       | ()

head-before : ∀ {Γ B} x k (sb : U.Step Γ B) → U.headˢ sb ≡ just k → U.beforeˢ x sb ≡ x <ᵖ k
head-before x k (U.outˢ _ _ _) refl = refl
head-before x k (U.skipˢ _ _)  refl = refl
head-before x k (U.endˢ _)     refl = refl
head-before x k U.hushˢ        ()

-- Apart from its source's step and where that shows, a shy body steps
-- strictly before it.
shy-at : ∀ {Δ Γ A B} k (sb : U.Step Δ B) (t : U.Step Γ A) → U.headˢ sb ≡ just k → Shy sb t
       → (∀ q → U.headˢ t ≡ just q → k ≢ q × k ≢ q ++ [ ix 0 ]) → U.beforeˢ k t ≡ true
shy-at k sb (U.outˢ q _ _) hb shy ap = shy-order q k (trans (sym (head-before (q ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap q refl)) (proj₂ (ap q refl))
shy-at k sb (U.skipˢ q _)  hb shy ap = shy-order q k (trans (sym (head-before (q ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap q refl)) (proj₂ (ap q refl))
shy-at k sb (U.endˢ c)     hb shy ap = shy-order c k (trans (sym (head-before (c ++ [ ix 0 ]) k sb hb)) shy) (proj₁ (ap c refl)) (proj₂ (ap c refl))
shy-at k sb U.hushˢ        hb shy ap = refl

-- A connect's body stepping no later than its source's step, among
-- sources clear of the body's step: the source's meaning shows past it.
shy-clear : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
          → Sane ν s → Placed s ρ → Sides (U.step b) (U.step s) → Skips ν s ρ → Shy (U.step b) (U.step s)
          → Clear ν (U.headˢ (U.step b)) ρ → Clearᴱ (U.headˢ (U.step b)) (U.meaning s ρ)
shy-clear {ν = ν} b s ρ ss ps sd sks shy cl with U.headˢ (U.step b) in hb
... | just k  = shown-past k (U.meaning s ρ) (floor s ρ k ss ps (shy-at k (U.step b) (U.step s) hb shy (λ q → sd k q refl)) (clear-floor ν ρ cl))
... | nothing = quiet {ν = ν} s ρ sks cl (U.step s) refl (subst (λ t → Shy t (U.step s)) (head-none (U.step b) hb) shy)

-- A tail run silent is idle.
tail-hush : ∀ {A} (t : Tail) → M′.tailᴱ {A} t ≡ hush → t ≡ idle
tail-hush (pin k r) ()
tail-hush idle      _ = refl

map-hush : ∀ {A B} (f : A → B) (x : Events A) → M′.mapᴱ f x ≡ hush → x ≡ hush
map-hush f (out k a r) ()
map-hush f (skip k r)  ()
map-hush f (end k)     ()
map-hush f hush        _ = refl

scan-hush : ∀ {A B} (f : B → A → B) z (x : Events A) → M′.scanᴱ f z x ≡ hush → x ≡ hush
scan-hush f z (out k a r) ()
scan-hush f z (skip k r)  ()
scan-hush f z (end k)     ()
scan-hush f z hush        _ = refl

taking-loud : ∀ {A} i (p : A → Bool) k a b r → M′.taking i p k a b r ≢ hush
taking-loud i     p k a true  r ()
taking-loud true  p k a false r ()
taking-loud false p k a false r ()

take-hush : ∀ {A} i (p : A → Bool) (x : Events A) → M′.takeWhileᴱ i p x ≡ hush → x ≡ hush
take-hush i p (out k a r) eq = ⊥-elim (taking-loud i p k a (p a) r eq)
take-hush i p (skip k r)  ()
take-hush i p (end k)     ()
take-hush i p hush        _ = refl

body-loud : ∀ {A B} r (σ : Events∞ A) q (y : Events B) → y ≢ hush → M′.body r σ q y ≢ hush
body-loud r σ q (out k a β) nh ()
body-loud r σ q (skip k β)  nh ()
body-loud r σ q (end c)     nh ()
body-loud r σ q hush        nh _ = nh refl

skip-loud : ∀ {A} k (τ : Events∞ A) → skip k τ ≢ hush
skip-loud k τ ()

-- A connect silent: its source silent, and its body.
side-hush : ∀ {A B} r (β : Events∞ B) (σ : Events∞ A) (x : Events A) → M′.side r β σ x ≡ hush → x ≡ hush × force β ≡ hush
side-hush r β σ x eq with hush? x
... | inj₁ ex = ex , subst (λ y → M′.side r β σ y ≡ hush) ex eq
... | inj₂ nx with ahead-split r β σ (M′.shownAt x)
...   | inj₁ (bt , τ , ea) = ⊥-elim (skip-loud _ τ (trans (sym ea) (trans (sym (side-ahead r β σ x nx)) eq)))
...   | inj₂ (bf , ea)     = ⊥-elim (body-loud r σ _ (force β) (before-false _ (force β) bf) (trans (sym ea) (trans (sym (side-ahead r β σ x nx)) eq)))

run-hush : ∀ {A} r (x : Events A) t → x ≡ hush → M′.runOn r x t ≡ t
run-hush r .hush t refl = refl

idle-∪ : ∀ {t u} → t ≡ idle → u ≡ idle → t ∪ u ≡ idle
idle-∪ refl refl = refl

head-hush : ∀ {A} (x : Events A) → M′.head x ≡ nothing → x ≡ hush
head-hush (out k a r) ()
head-hush (skip k r)  ()
head-hush (end k)     ()
head-hush hush        _ = refl

earliest-none : ∀ {B} (ls : List (Events∞ B)) → M′.earliest ls ≡ M′.none → All (λ l → M′.head (force l) ≡ nothing) ls
earliest-none []       _ = []ᴬ
earliest-none (l ∷ ls) with M′.head (force l) in hl | M′.earliest ls in el
... | nothing | M′.none           = λ _ → hl ∷ᴬ earliest-none ls el
... | nothing | M′.found _ _ _ _  = λ ()
... | just k  | M′.none           = λ ()
... | just k  | M′.found k′ _ _ _ with k <ᵖ k′
...   | true  = λ ()
...   | false = λ ()

earliest-found : ∀ {B} (ls : List (Events∞ B)) {k bs l as} → M′.earliest ls ≡ M′.found k bs l as → M′.head (force l) ≡ just k
earliest-found []        ()
earliest-found (l₀ ∷ ls) with M′.head (force l₀) in hl | M′.earliest ls in el
... | nothing | M′.none            = λ ()
... | nothing | M′.found k bs c as = λ { refl → earliest-found ls el }
... | just k  | M′.none            = λ { refl → hl }
... | just k  | M′.found k′ bs c as with k <ᵖ k′
...   | true  = λ { refl → hl }
...   | false = λ { refl → earliest-found ls el }

outer-hush : ∀ {B} op (e : Events∞ (M′.MonotonicList B)) ls qs t (x : Events (M′.MonotonicList B)) → M′.outer op e ls qs t x ≡ hush → x ≡ hush
outer-hush op e ls qs t (out q m r) with M′.admit op (q ++ [ ix 1 ]) m ls qs
... | _ , _ , _ = λ ()
outer-hush op e ls       qs       t (skip q r) ()
outer-hush op e []       []       t (end c)    ()
outer-hush op e []       (m ∷ qs) t (end c)    ()
outer-hush op e (l ∷ ls) qs       t (end c)    ()
outer-hush op e ls       qs       t hush       _ = refl

lane-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) bs l as qs t (x : Events B) → M′.lane op o bs l as qs t x ≡ hush → x ≡ hush
lane-hush op o        bs       l as       qs       t (out k b r) ()
lane-hush op o        bs       l as       qs       t (skip k r)  ()
lane-hush op o        bs       l as       (m ∷ qs) t (end c)     ()
lane-hush op nothing  []       l []       []       t (end c)     ()
lane-hush op nothing  []       l (a ∷ as) []       t (end c)     ()
lane-hush op nothing  (b ∷ bs) l as       []       t (end c)     ()
lane-hush op (just e) bs       l as       []       t (end c)     ()
lane-hush op o        bs       l as       qs       t hush        _ = refl

just-loud : ∀ {A} (x : Events A) {k} → M′.head x ≡ just k → x ≢ hush
just-loud (out k a r) _ ()
just-loud (skip k r)  _ ()
just-loud (end k)     _ ()
just-loud hush        () _

race-loud : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) k bs (l : Events∞ B) as qs t
          → M′.head (force l) ≡ just k → M′.race op o k bs l as qs t ≢ hush
race-loud op nothing  k bs l as qs t hl eq = just-loud (force l) hl (lane-hush op nothing bs l as qs t (force l) eq)
race-loud op (just e) k bs l as qs t hl with M′.head (force e) in he
... | nothing = λ eq → just-loud (force l) hl (lane-hush op (just e) bs l as qs t (force l) eq)
... | just k′ with k′ <ᵖ k
...   | true  = λ eq → just-loud (force e) he (outer-hush op e (bs ++ l ∷ as) qs t (force e) eq)
...   | false = λ eq → just-loud (force l) hl (lane-hush op (just e) bs l as qs t (force l) eq)

parts-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) ls qs t → M′.parts op o ls qs t ≡ hush
           → M′.headᴼ o ≡ nothing × All (λ l → M′.head (force l) ≡ nothing) ls
parts-hush op o ls qs t with M′.earliest ls in el
... | M′.found k bs l as = λ eq → ⊥-elim (race-loud op o k bs l as qs t (earliest-found ls el) eq)
... | M′.none with o
...   | nothing = λ _ → refl , earliest-none ls el
...   | just e  = λ eq → cong M′.head (outer-hush op e ls qs t (force e) eq) , earliest-none ls el

-- A flatMap's run silent: nothing its ended parts left, its outer gone
-- or silent, and every lane silent.
go-hush : ∀ {B} op (o : Maybe (Events∞ (M′.MonotonicList B))) ls qs t → M′.go op o ls qs t ≡ hush
        → t ≡ idle × M′.headᴼ o ≡ nothing × All (λ l → M′.head (force l) ≡ nothing) ls
go-hush op o ls qs idle      eq = refl , parts-hush op o ls qs idle eq
go-hush op o ls qs (pin k u) with M′.ahead-of k o ls in ah
... | true  = λ ()
... | false = λ eq → ⊥-elim (bool-split (trans (sym ah) (uncurry (ahead-quiet k o ls) (parts-hush op o ls qs (pin k u) eq))))
  where bool-split : false ≡ true → ⊥
        bool-split ()

-- A rest-like that never shows again leaves nothing running.
rested-idle : ∀ {Γ A} (t : U.Node Γ A) (ρ : NEnv Γ) → Rested t → U.meaning t ρ ≡ hush → U.cutᴺ t ρ ≡ idle
rested-idle (U.restᶜ n)               ρ _ eq = tail-hush _ eq
rested-idle U.idleᶜ                   ρ _ _  = refl
rested-idle (U.unionᶜ x y)            ρ _ eq = tail-hush _ eq
rested-idle (U.burstingᶜ r t)         ρ _ eq = tail-hush _ eq
rested-idle (U.underᶜ (U.live s) b)   ρ _ eq = tail-hush _ eq
rested-idle (U.underᶜ (U.ended c t) b) ρ _ eq = tail-hush _ eq
rested-idle (U.framesᶜ τ e m)            ρ () _
rested-idle (U.burstᶜ τ r k f)           ρ () _
rested-idle (U.ofᶜ p k xs)               ρ () _
rested-idle (U.mapᶜ f c)                 ρ () _
rested-idle (U.scanᶜ f z c)              ρ () _
rested-idle (U.takeWhileᶜ k p c)         ρ () _
rested-idle (U.flatMapᶜ op g o ls qs pl) ρ () _
rested-idle (U.joinᶜ j p xs e)           ρ () _
rested-idle (U.connectᶜ r b s)           ρ () _
rested-idle (U.deferᶜ l p ns)            ρ () _
rested-idle (U.endingᶜ p n)              ρ () _

-- A node that never shows again leaves nothing running when cut.
mutual
  cut-idle : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Sane ν s → Placed s ρ
           → U.meaning s ρ ≡ hush → U.cutᴺ s ρ ≡ idle
  cut-idle (U.framesᶜ τ e m)  ρ _ _ _ = refl
  cut-idle (U.burstᶜ τ r i b) ρ _ _ _ = refl
  cut-idle (U.ofᶜ p i xs)     ρ _ _ _ = refl
  cut-idle (U.mapᶜ f c)         ρ sn (_ , pl) eq = cut-idle c ρ sn pl (map-hush f _ eq)
  cut-idle (U.scanᶜ f z c)      ρ sn (_ , pl) eq = cut-idle c ρ sn pl (scan-hush f z _ eq)
  cut-idle (U.takeWhileᶜ i p c) ρ sn (_ , pl) eq = cut-idle c ρ sn pl (take-hush i p _ eq)
  cut-idle (U.flatMapᶜ op g o ls qs pl) ρ (so , sl , _) (_ , po , pls , _) eq
    with go-hush _ (U.outerᴺ g o ρ) (U.states ls ρ) _ (U.cutᴺ pl ρ) eq
  ... | te , ho , hl = idle-∪ (cut-idleᴼ g o ρ so po ho) (idle-∪ (cut-idleᴸ ls ρ sl pls hl) te)
  cut-idle (U.joinᶜ i p xs e) ρ _ _ _ = refl
  cut-idle (U.connectᶜ r b (U.live s)) ρ (sb , ss) (_ , pb , ps , _) eq with side-hush r (U.stateᴺ b (U.meaning s ρ ∷ᴬ ρ)) (U.stateᴺ s ρ) (U.meaning s ρ) eq
  ... | es , eb = idle-∪ (trans (run-hush r _ _ es) (cut-idle s ρ ss ps es)) (cut-idle b _ sb pb eb)
  cut-idle (U.connectᶜ r b (U.ended c t)) ρ (sb , rt) (_ , pb) eq with side-hush r (U.stateᴺ b (end c ∷ᴬ ρ)) (U.stateᴺ t ρ) (U.meaning t ρ) eq
  ... | et , eb = idle-∪ (trans (run-hush r _ _ et) (rested-idle t ρ rt et)) (cut-idle b _ sb pb eb)
  cut-idle (U.deferᶜ l p ns)  ρ _ _ _ = refl
  cut-idle (U.endingᶜ p n)    ρ _ _ ()
  cut-idle (U.restᶜ n)        ρ _ _ eq = rested-idle (U.restᶜ n) ρ tt eq
  cut-idle U.idleᶜ            ρ _ _ _  = refl
  cut-idle (U.unionᶜ x y)     ρ _ _ eq = rested-idle (U.unionᶜ x y) ρ tt eq
  cut-idle (U.burstingᶜ r t)  ρ _ _ eq = rested-idle (U.burstingᶜ r t) ρ tt eq
  cut-idle (U.underᶜ s b)     ρ _ _ eq = rested-idle (U.underᶜ s b) ρ tt eq

  cut-idleᴼ : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} (g : A → Pos → U.Node Γ B) (o : Maybe (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴹ ν o → Placedᴹ o ρ
            → M′.headᴼ (U.outerᴺ g o ρ) ≡ nothing → M′.cutᴼ (U.outerᴺ g o ρ) ≡ idle
  cut-idleᴼ g nothing  ρ _ _ _  = refl
  cut-idleᴼ g (just c) ρ s p ho = cut-idle c ρ s p (map-hush _ (U.meaning c ρ) (head-hush _ ho))

  cut-idleᴸ : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (ls : List (U.Node Γ A)) (ρ : NEnv Γ) → Saneᴸ ν ls → Placedᴸ ls ρ
            → All (λ l → M′.head (force l) ≡ nothing) (U.states ls ρ) → M′.cuts (U.states ls ρ) ≡ idle
  cut-idleᴸ []       ρ _        _        _          = refl
  cut-idleᴸ (c ∷ cs) ρ (s , ss) (p , ps) (h ∷ᴬ hs) = idle-∪ (cut-idle c ρ s p (head-hush _ h)) (cut-idleᴸ cs ρ ss ps hs)

hushed-cut : ∀ {Γ A} {ν : All (λ _ → Mode) Γ} (s : U.Node Γ A) (ρ : NEnv Γ) → Sane ν s → Placed s ρ
           → U.meaning s ρ ≡ hush → ∀ d → Agreeᵀ d (U.cutᴺ s ρ) idle
hushed-cut s ρ ss ps eq d = subst (λ t → Agreeᵀ d t idle) (sym (cut-idle s ρ ss ps eq)) (agreeᵀ-refl d idle)

-- A connect's body showing first: what it shows, the source carried.
body-skips : ∀ {Γ A B} {ν : All (λ _ → Mode) Γ} r (b : U.Node (A ∷ Γ) B) (s : U.Node Γ A) (ρ : NEnv Γ)
           → Sane ν s → Placed s ρ → Sides (U.step b) (U.step s)
           → Skips (runs ∷ᴬ ν) b (U.meaning s ρ ∷ᴬ ρ) → Skips ν s ρ → Shy (U.step b) (U.step s)
           → Clear ν (U.headˢ (U.bodyˢ r (U.live s) (U.step b))) ρ
           → U.meaning (U.connectᶜ r b (U.live s)) ρ ≃ afterᴱ ρ (U.bodyˢ r (U.live s) (U.step b))
body-skips {ν = ν} r b s ρ ss ps sd skb sks shy cl =
  alike (BodyFirst.main r b s ρ (U.step b) (U.meaning s ρ) refl (skb (ce , cl′)) ce (λ eq → hushed-cut s ρ ss ps eq))
  where cl′ = subst (λ h → Clear ν h ρ) (head-body r (U.live s) (U.step b)) cl
        ce  = shy-clear b s ρ ss ps sd sks shy cl′

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
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (subst (Sides (U.step b)) (sym es) (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.skipˢ q s′ with U.beforeˢ (q ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.fed-first r b s ρ sb (proj₁ (proj₂ pl)) q nothing s′ (sks (clear-lower ν ρ (<ᵖ-below q []) cl)) fb cl
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (subst (Sides (U.step b)) (sym es) (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.endˢ c with U.beforeˢ (c ++ [ ix 0 ]) (U.step b) in fb
...   | true  = SourceFirst.shut-first r b s ρ sb (proj₁ (proj₂ pl)) c (sks (clear-lower ν ρ (<ᵖ-below c []) cl)) fb cl
...   | false = body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (subst (Sides (U.step b)) (sym es) (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) fb) cl
connect-skips {ν = ν} r b s ρ (sb , ss) pl skb sks cl | U.hushˢ =
  body-skips r b s ρ ss (proj₁ (proj₂ (proj₂ pl))) (subst (Sides (U.step b)) (sym es) (proj₂ (proj₂ (proj₂ pl)))) skb (back {ν = ν} {s = s} {ρ = ρ} es sks) (subst (Shy (U.step b)) (sym es) tt) cl

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
  skips (U.connectᶜ r b (U.live s)) ρ sn@(sb , ss) pd@(_ , pb , ps , _) cl =
    connect-skips r b s ρ sn pd (skips b (U.meaning s ρ ∷ᴬ ρ) sb pb) (skips s ρ ss ps) cl
  skips (U.connectᶜ r b (U.ended c t)) ρ sn@(sb , _) pd@(_ , pb) cl = ended-skips r b c t ρ sn pd (skips b (end c ∷ᴬ ρ) sb pb) cl
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
  -- DEAD ROUTE: exact agreement with a ghost anchored in its sources'
  --   step history.  The ghost is the witness's open part (`part`), which
  --   keeps no count of a source's steps, and a silent run is matched by
  --   the residual as a set alone (`Ahead`), so no field of the witness
  --   can keep the count a lane's pre-join skips need.
  within-step : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Withinˢ []ᴬ (U.step g)

  -- What a sane, placed ghost in order to every depth steps to is in
  -- order to every depth: the stepped node runs what the meaning runs
  -- past the step, and a rest the step opens is a part it held.
  step-deep : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Deep g []ᴬ → Deepˢ []ᴬ (U.step g)

-- A STEP KEEPS THE GHOST PLACED: atop what the step shows.
placed-after : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Placedˢ []ᴬ (U.step g)
placed-after g sn pl = placed-step []ᴬ (U.step g) (step-skips g sn pl) (proj₁ pl) (within-step g sn pl)
