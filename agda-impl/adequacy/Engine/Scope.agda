{-# OPTIONS --guardedness #-}

-- A flatMap's lanes, read where its frame sits: per connect in scope,
-- whether its source runs (`modes`), and every running one clear of a
-- position (`Scope`).  A lane's meaning starts with its step's event, or
-- past a running source's shown event (`adequacy.Stepper.first`); so a
-- lane whose step heads after `q`, every running source clear of `q`,
-- heads after `q` in the meaning.
module adequacy.Engine.Scope where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (just)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)

open import denotation.MonotonicList.Events using (Pos; Events; Events∞; out; skip; end; hush; _<ᵖ_; <ᵖ-trans)
import denotation.MonotonicList as M′
open import denotation.Unfold using (NEnv; Node; Source; live; ended; Step; states; step; headˢ; meaning)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Sane using (Mode; runs; over; loose)
open import adequacy.Stepper.Past using (Clear; Clearᴱ; Belowᴱ; Past; First; Firstᴸ)
open import adequacy.Stepper.Flat using (agree-head)
open import adequacy.Engine.Meaning using (envAt; srcG)
open import adequacy.Engine.Race using (After)

modeᴳ : ∀ {Γ X} → Source Γ X → Mode
modeᴳ (live s)    = runs
modeᴳ (ended e t) = over

modes : ∀ {R Γ A} → Ctx R Γ A → All (λ _ → Mode) Γ
modes top                               = []ᴬ
modes (inMap f c)                       = modes c
modes (inScan f z c)                    = modes c
modes (inCut l a c)                     = modes c
modes (inLn b c)                        = modes c
modes (inTake i q w c)                  = modes c
modes (inOuter op f d n q ls c)         = modes c
modes (inLanes op f d n q o pre post c) = modes c
modes (inSrc k b c)                     = modes c
modes (inBody k o c)                    = modeᴳ (srcG k o) ∷ᴬ modes c

Scope : ∀ {R Γ A} → Pos → Ctx R Γ A → Set
Scope q c = Clear (modes c) (just q) (envAt c)

-- A source clear of `q` and shown before `h`: `h` is after `q`.
below-clear : ∀ {A} (e : Events A) q h m → Clearᴱ (just q) e → Belowᴱ e h m → q <ᵖ h ≡ true
below-clear hush        q h m ce ()
below-clear (out p a σ) q h m ce (b , _) = <ᵖ-trans q _ h ce b
below-clear (skip p σ)  q h m ce (b , _) = <ᵖ-trans q _ h ce b
below-clear (end p)     q h m ce (b , _) = <ᵖ-trans q _ h ce b

past-clear : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q h m → Clear ν (just q) ρ → Past ν h m ρ → q <ᵖ h ≡ true
past-clear []ᴬ          []ᴬ      q h m _        ()
past-clear (runs ∷ᴬ ν)  (e ∷ᴬ ρ) q h m (ce , _) (inj₁ b) = below-clear e q h m ce b
past-clear (runs ∷ᴬ ν)  (e ∷ᴬ ρ) q h m (_ , c)  (inj₂ p) = past-clear ν ρ q h m c p
past-clear (over ∷ᴬ ν)  (e ∷ᴬ ρ) q h m c        p        = past-clear ν ρ q h m c p
past-clear (loose ∷ᴬ ν) (e ∷ᴬ ρ) q h m (ce , _) (inj₁ b) = below-clear e q h m ce b
past-clear (loose ∷ᴬ ν) (e ∷ᴬ ρ) q h m (_ , c)  (inj₂ p) = past-clear ν ρ q h m c p

first-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A)
            → Clear ν (just q) ρ → First ν ρ t x → After q (headˢ t) → After q (M′.head x)
first-after ν ρ q t x           cl (inj₁ ag) a = subst (After q) (agree-head ρ t x ag) a
first-after ν ρ q t (out h _ _) cl (inj₂ pa) a = past-clear ν ρ q h (headˢ t) cl pa
first-after ν ρ q t (skip h _)  cl (inj₂ pa) a = past-clear ν ρ q h (headˢ t) cl pa
first-after ν ρ q t (end h)     cl (inj₂ pa) a = past-clear ν ρ q h (headˢ t) cl pa
first-after ν ρ q t hush        cl (inj₂ ()) a

firsts-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (ms : List (Node Γ A))
             → Clear ν (just q) ρ → Firstᴸ ν ms ρ → All (λ m → After q (headˢ (step m))) ms
             → All (λ l → After q (M′.head (Events∞.force l))) (states ms ρ)
firsts-after ν ρ q []       cl _        []ᴬ       = []ᴬ
firsts-after ν ρ q (m ∷ ms) cl (f , fs) (a ∷ᴬ as) = first-after ν ρ q (step m) (meaning m ρ) cl f a ∷ᴬ firsts-after ν ρ q ms cl fs as
