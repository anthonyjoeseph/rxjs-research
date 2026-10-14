{-# OPTIONS --guardedness --large-indices #-}

-- THE RUN UP TO CALM POINTS.  A segment of the machine's trace against
-- the events the root is shown: a step on each side passes a guard, a
-- silent one on either side alone passes finitely often, and a calm
-- point resumes the run, unguarded only with fewer dead timers.
module adequacy.Segment where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Unit using (⊤; tt)
open import Data.List using ([]; _∷_)
open import Level using (lower)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList using (Events; Events∞; Pos; Frame; out; skip; end; hush; tick)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import operation.AbstractObservable using (module Run)
open import operation.PureObservable using (Pureᴾ; Sink; _⊑_; _⨾_; module Pure)
open import adequacy.Realize using (module Realizing)
open import adequacy.deliver.Context using (module Contexts)
open import adequacy.deliver.Mid using (module Middles)

module Seg (R : Set) where
  open Machine R using (Mach; ⟨_,_⟩; turn; burst; loop; run; ret; Stack; step; silent; shown; Trace; Trace∞; tau; out; end; idle; trace)
  open Realizing R using (Holding; firing; dead; _≗_)
  open Contexts R using (Ctx; obsC)
  open Middles R using (Mid; Back; module AtC)
  open Run (Pureᴾ R) using (Observer)
  open Pure R using (State; get)

  -- A calm point inside a segment no guard has passed must have fewer
  -- dead timers than where the segment began.
  Below : Maybe ℕ → Mach → Set
  Below (just k) m = dead m < k
  Below nothing  m = ⊤

  -- The relation's constructors, and a calm point to resume from.
  mutual
    data Seg (b : Maybe ℕ) : Trace → Events R → Set₁ where
      out~  : ∀ {p a l r} → Seg∞ (Trace∞.force l) (Events∞.force r) → Seg b (out (tick p) p a l) (out p a r)
      tau~  : ∀ {t p l r} → Seg∞ (Trace∞.force l) (Events∞.force r) → Seg b (tau t l) (skip p r)
      tauˡ  : ∀ {t l e} → Seg b (Trace∞.force l) e → Seg b (tau t l) e
      skipʳ : ∀ {m p r} → Seg b m (Events∞.force r) → Seg b m (skip p r)
      end~  : ∀ {p} → Seg b (end p) (end p)
      idle~ : Seg b idle hush
      calm~ : ∀ {m e} → Calm m e → Below b m → Seg b (trace m) e

    record Seg∞ (l : Trace) (r : Events R) : Set₁ where
      coinductive
      field force : Seg nothing l r

    -- CALM POINTS, where what is running is what the meaning has left to
    -- show: the machine at its loop, or about to step a live cold's frame
    -- from it, in whatever world the frame's deliveries have grown the
    -- heap to; or about to deliver at a hole, what it does on return
    -- given.
    data Calm : Mach → Events R → Set₁ where
      calm       : ∀ {h} {st : State h} {c} → Holding [] c st → Calm ⟨ st , turn ⟩ (U.unfold c)
      bursting   : ∀ {w h} {st : State h} {c A u τ} {s : Sink h A} {hd r i} {b : Frame A u} {σ : w ⊑ h}
                 → Holding (firing s hd τ r i b ∷ []) c st → lower (get (State.heap st) hd) ≡ false
                 → Calm ⟨ st , burst s hd u r i b σ loop ⟩ (U.unfold c)
      delivering : ∀ {h Δ A} {L : Pos → Set} {k : Ctx h Δ A} {t n fs c} {st : State h} {q a n′} {act w} {σ : w ⊑ h} {K : Stack w ⊤}
                 → Mid L k t (just n) fs c st → U.step n ≡ U.outˢ q a n′ → State.pos st ≡ q → AtC.Fore (State.heap st) k q
                 → act ≗ Observer.next (obsC k) a
                 → (∀ {v} (τ : h ⊑ v) {st′ : State v} {c′} → Back L τ k t q (just n′) fs c′ st′
                    → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ) K ⟩) (U.unfold c′))
                 → Calm ⟨ st , run act σ K ⟩ (U.unfold c)
      finishing  : ∀ {h Δ A} {L : Pos → Set} {k : Ctx h Δ A} {t n fs c} {st : State h} {q act w} {σ : w ⊑ h} {K : Stack w ⊤}
                 → Mid L k t (just n) fs c st → U.step n ≡ U.endˢ q → State.pos st ≡ q → AtC.Fore (State.heap st) k q
                 → act ≗ Observer.complete (obsC k)
                 → (∀ {v} (τ : h ⊑ v) {st′ : State v} {c′} → Back L τ k t q nothing fs c′ st′
                    → Seg nothing (trace ⟨ st′ , ret tt (σ ⨾ τ) K ⟩) (U.unfold c′))
                 → Calm ⟨ st , run act σ K ⟩ (U.unfold c)

  open Seg∞

  -- The machine passing silent steps only.
  infix 4 _⇒_
  data _⇒_ : Mach → Mach → Set₁ where
    here⇒ : ∀ {m} → m ⇒ m
    step⇒ : ∀ {m m₁ m′} → step m ≡ silent m₁ → m₁ ⇒ m′ → m ⇒ m′

  taus : ∀ {b m m′ e} → m ⇒ m′ → Seg b (trace m′) e → Seg b (trace m) e
  taus here⇒        s = s
  taus (step⇒ eq r) s = subst (λ x → Seg _ (shown x) _) (sym eq) (tauˡ (taus r s))

  -- The meaning passing silent steps only.
  data Skips : U.Node R → U.Node R → Set₁ where
    noneˢ : ∀ {c} → Skips c c
    skipˢ : ∀ {c p c₁ c′} → U.step c ≡ U.skipˢ p c₁ → Skips c₁ c′ → Skips c c′

  skipping : ∀ {b m c c′} → Skips c c′ → Seg b m (U.unfold c′) → Seg b m (U.unfold c)
  skipping noneˢ         s = s
  skipping (skipˢ eq sk) s = subst (λ x → Seg _ _ (U.shown x)) (sym eq) (skipʳ (skipping sk s))

  -- At least one silent step of the meaning, to a configuration where `P`.
  record Passes (c : U.Node R) (P : U.Node R → Set₁) : Set₁ where
    constructor passes
    field
      {c₁ c′} : U.Node R
      {p}     : Pos
      first   : U.step c ≡ U.skipˢ p c₁
      rest    : Skips c₁ c′
      holds   : P c′

  mapᴾ : ∀ {c} {P Q : U.Node R → Set₁} → (∀ {c′} → P c′ → Q c′) → Passes c P → Passes c Q
  mapᴾ f (passes e sk p) = passes e sk (f p)


  if-true : ∀ {ℓ ℓ′} {X : Set ℓ} {x : Bool} {a b : X} (P : X → Set ℓ′) → x ≡ true → P a → P (if x then a else b)
  if-true P refl p = p

  if-false : ∀ {ℓ ℓ′} {X : Set ℓ} {x : Bool} {a b : X} (P : X → Set ℓ′) → x ≡ false → P b → P (if x then a else b)
  if-false P refl p = p

  -- A segment resumed after a guard.
  later : ∀ {m e} → Seg nothing m e → Seg∞ m e
  force (later s) = s

  -- A frame's step silent at the root, the run resuming at a calm point.
  passing : ∀ {c m bd} {P : U.Node R → Set₁} → Passes c P → (∀ {c′} → P c′ → Seg nothing (trace m) (U.unfold c′))
          → Seg bd (shown (silent m)) (U.unfold c)
  passing (passes eq sk p) k = subst (λ x → Seg _ _ (U.shown x)) (sym eq) (tau~ (later (skipping sk (k p))))

