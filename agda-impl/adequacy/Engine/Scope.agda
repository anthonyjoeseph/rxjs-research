{-# OPTIONS --guardedness #-}

-- A node read where its frame sits: per connect in scope, whether its
-- source runs (`modes`), and every running one showing at or past a
-- position (`Scope`).  A node's meaning starts with its step's event, or
-- past a running source's shown event (`adequacy.Stepper.first`); so a
-- node whose step heads after `q` heads after `q` in the meaning
-- (`first-after`), and one whose step shows at or past `q` shows there
-- too (`first-floor`).  A connect's source is such a node, read in the
-- scope above it (`scope-src`).
module adequacy.Engine.Scope where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Relation.Unary.All using (All) renaming ([] to []ᴬ; _∷_ to _∷ᴬ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)

open import denotation.MonotonicList using (Agree; out⁼; skip⁼; end⁼; hush⁼)
open import denotation.MonotonicList.Events using (Pos; Events; Events∞; out; skip; end; hush; ix; _<ᵖ_; <ᵖ-trans; <ᵖ-asym; <ᵖ-below)
import denotation.MonotonicList as M′
open import denotation.Unfold using (NEnv; Node; Source; live; ended; Step; outˢ; skipˢ; endˢ; hushˢ; states; step; headˢ; meaning)
open import operation.PureObservable using (module Machine)
open Machine using (Ctx; top; inMap; inScan; inCut; inLn; inTake; inOuter; inLanes; inSrc; inBody)
open import adequacy.Sane using (Mode; runs; over; loose; Sane)
open import adequacy.Placed.Order using (Placed)
open import adequacy.Stepper using (first)
open import adequacy.Stepper.Past using (Floor; Floorᴱ; First; Firstᴸ; afterᴱ; above)
open import adequacy.Stepper.Flat using (agree-head)
open import adequacy.Engine.Meaning using (envAt; srcG; srcRun)
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
Scope q c = Floor (modes c) q (envAt c)

-- At or past a later position, at or past an earlier one.
≮-lower : ∀ s k k′ → k <ᵖ k′ ≡ true → s <ᵖ k′ ≡ false → s <ᵖ k ≡ false
≮-lower s k k′ lt f with s <ᵖ k in e
... | false = refl
... | true  = trans (sym (<ᵖ-trans s k k′ e lt)) f

floorᴱ-lower : ∀ {A} k k′ (e : Events A) → k <ᵖ k′ ≡ true → Floorᴱ k′ e → Floorᴱ k e
floorᴱ-lower k k′ hush        lt f = f
floorᴱ-lower k k′ (out q a σ) lt f = ≮-lower (q ++ [ ix 0 ]) k k′ lt f
floorᴱ-lower k k′ (skip q σ)  lt f = ≮-lower (q ++ [ ix 0 ]) k k′ lt f
floorᴱ-lower k k′ (end c)     lt f = ≮-lower (c ++ [ ix 0 ]) k k′ lt f

floor-lower : ∀ {Γ} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) k k′ → k <ᵖ k′ ≡ true → Floor ν k′ ρ → Floor ν k ρ
floor-lower []ᴬ          []ᴬ      k k′ lt f        = f
floor-lower (runs ∷ᴬ ν)  (e ∷ᴬ ρ) k k′ lt (fe , f) = floorᴱ-lower k k′ e lt fe , floor-lower ν ρ k k′ lt f
floor-lower (over ∷ᴬ ν)  (e ∷ᴬ ρ) k k′ lt f        = floor-lower ν ρ k k′ lt f
floor-lower (loose ∷ᴬ ν) (e ∷ᴬ ρ) k k′ lt (fe , f) = floorᴱ-lower k k′ e lt fe , floor-lower ν ρ k k′ lt f

first-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A)
            → Floor ν q ρ → First ν ρ t x → After q (headˢ t) → After q (M′.head x)
first-after ν ρ q t x           fl (inj₁ ag) a = subst (After q) (agree-head ρ t x ag) a
first-after ν ρ q t (out h _ _) fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t (skip h _)  fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t (end h)     fl (inj₂ pa) a = above ν ρ q h (headˢ t) fl pa
first-after ν ρ q t hush        fl (inj₂ ()) a

firsts-after : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (ms : List (Node Γ A))
             → Floor ν q ρ → Firstᴸ ν ms ρ → All (λ m → After q (headˢ (step m))) ms
             → All (λ l → After q (M′.head (Events∞.force l))) (states ms ρ)
firsts-after ν ρ q []       fl _        []ᴬ       = []ᴬ
firsts-after ν ρ q (m ∷ ms) fl (f , fs) (a ∷ᴬ as) = first-after ν ρ q (step m) (meaning m ρ) fl f a ∷ᴬ firsts-after ν ρ q ms fl fs as

-- Whatever is at `h` shows at or past `q`.
FloorAt : Pos → Maybe Pos → Set
FloorAt q nothing  = ⊤
FloorAt q (just h) = (h ++ [ ix 0 ]) <ᵖ q ≡ false

-- A node whose step shows at or past `q`, every running source in scope
-- at or past it, shows there in the meaning.
agree-floor : ∀ {Γ A} (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A) → Agree 1 x (afterᴱ ρ t) → FloorAt q (headˢ t) → Floorᴱ q x
agree-floor ρ q (outˢ h a n) _ (out⁼ _ _)  fa = fa
agree-floor ρ q (skipˢ h n)  _ (skip⁼ _ _) fa = fa
agree-floor ρ q (endˢ h)     _ end⁼        fa = fa
agree-floor ρ q hushˢ        _ hush⁼       fa = tt

past-floor : ∀ q h → q <ᵖ h ≡ true → (h ++ [ ix 0 ]) <ᵖ q ≡ false
past-floor q h lt = <ᵖ-asym q (h ++ [ ix 0 ]) (<ᵖ-trans q h (h ++ [ ix 0 ]) lt (<ᵖ-below h []))

first-floor : ∀ {Γ A} (ν : All (λ _ → Mode) Γ) (ρ : NEnv Γ) q (t : Step Γ A) (x : Events A)
            → Floor ν q ρ → First ν ρ t x → FloorAt q (headˢ t) → Floorᴱ q x
first-floor ν ρ q t x           fl (inj₁ ag) fa = agree-floor ρ q t x ag fa
first-floor ν ρ q t (out h _ _) fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t (skip h _)  fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t (end h)     fl (inj₂ pa) fa = past-floor q h (above ν ρ q h (headˢ t) fl pa)
first-floor ν ρ q t hush        fl (inj₂ ()) fa

-- A connect's source at or past `q`, if it runs.
FloorSrc : ∀ {Γ X} → Pos → Source Γ X → NEnv Γ → Set
FloorSrc q (live s)    ρ = Floorᴱ q (meaning s ρ)
FloorSrc q (ended e t) ρ = ⊤

scope-src : ∀ {Γ X} (ν : All (λ _ → Mode) Γ) q (g : Source Γ X) (ρ : NEnv Γ) → FloorSrc q g ρ → Floor ν q ρ
          → Floor (modeᴳ g ∷ᴬ ν) q (srcRun g ρ ∷ᴬ ρ)
scope-src ν q (live s)    ρ fs f = fs , f
scope-src ν q (ended e t) ρ fs f = f

-- A connect's source, if it runs: of the stepper's invariants, its step
-- at or past `q`.
SaneSrc : ∀ {Γ X} → All (λ _ → Mode) Γ → Source Γ X → Set
SaneSrc ν (live s)    = Sane ν s
SaneSrc ν (ended e t) = ⊤

PlacedSrc : ∀ {Γ X} → Source Γ X → NEnv Γ → Set
PlacedSrc (live s)    ρ = Placed s ρ
PlacedSrc (ended e t) ρ = ⊤

HeadFloor : ∀ {Γ X} → Pos → Source Γ X → Set
HeadFloor q (live s)    = FloorAt q (headˢ (step s))
HeadFloor q (ended e t) = ⊤

-- Its step at or past `q`, every running source above too: its meaning.
live-floor : ∀ {Γ X} (ν : All (λ _ → Mode) Γ) q (g : Source Γ X) (ρ : NEnv Γ) → SaneSrc ν g → PlacedSrc g ρ → HeadFloor q g → Floor ν q ρ
           → FloorSrc q g ρ
live-floor ν q (live s)    ρ sn pl hf fl = first-floor ν ρ q (step s) (meaning s ρ) fl (first {ν = ν} s ρ sn pl) hf
live-floor ν q (ended e t) ρ sn pl hf fl = tt
