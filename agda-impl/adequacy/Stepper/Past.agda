{-# OPTIONS --guardedness #-}

module adequacy.Stepper.Past where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; lookup) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; subst)

open import denotation.MonotonicList.Events using (Events; Events∞; out; skip; end; hush; Pos; idle; ix; sub; last; _<ᵖ_; <ᵖ-trans; <ᵖ-asym;
  <ᵖ-below; <ᵖ-split; <ᵖ-step; <ᵖ-part)
open import denotation.MonotonicList using (Agree; stop; stopᵀ; out⁼; skip⁼; end⁼; hush⁼; agree-refl; agreeᵀ-refl)
open import denotation.NonExpansive using (Agreeˢ)

open Agreeˢ using (nowˢ)
import denotation.MonotonicList as M′
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Mode; runs; over; loose; Told)
open import adequacy.Placed.Order using (Alien; Atop; Ordered; ordered; Placed; Prefix; Within; every)
open import adequacy.Placed.Keys using (ordered-≈; prefix-refl)

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

Firstᴹ : ∀ {Γ A} → All (λ _ → Mode) Γ → Maybe (U.Node Γ A) → NEnv Γ → Set
Firstᴹ ν nothing  ρ = ⊤
Firstᴹ ν (just c) ρ = Firsts ν c ρ

Firstᴸ : ∀ {Γ A} → All (λ _ → Mode) Γ → List (U.Node Γ A) → NEnv Γ → Set
Firstᴸ ν []       ρ = ⊤
Firstᴸ ν (c ∷ cs) ρ = Firsts ν c ρ × Firstᴸ ν cs ρ

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

Placedˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Placedˢ ρ (U.outˢ k a c) = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.skipˢ k c)  = Atop k (U.meaning c ρ) × Placed c ρ
Placedˢ ρ (U.endˢ k)     = ⊤
Placedˢ ρ U.hushˢ        = ⊤

Withinˢ : ∀ {Γ A} → NEnv Γ → U.Step Γ A → Set
Withinˢ ρ (U.outˢ k a c) = Within c ρ
Withinˢ ρ (U.skipˢ k c)  = Within c ρ
Withinˢ ρ (U.endˢ k)     = ⊤
Withinˢ ρ U.hushˢ        = ⊤

placed-step : ∀ {Γ A} (ρ : NEnv Γ) (s : U.Step Γ A) {x : Events A} → x ≃ afterᴱ ρ s → Ordered x → Withinˢ ρ s → Placedˢ ρ s
placed-step ρ (U.outˢ k a c) e o w = proj₁ (ordered (ordered-≈ _ _ (agreeing e) o)) , proj₂ (ordered (ordered-≈ _ _ (agreeing e) o)) , w
placed-step ρ (U.skipˢ k c)  e o w = proj₁ (ordered (ordered-≈ _ _ (agreeing e) o)) , proj₂ (ordered (ordered-≈ _ _ (agreeing e) o)) , w
placed-step ρ (U.endˢ k)     e o w = tt
placed-step ρ U.hushˢ        e o w = tt
