{-# OPTIONS --guardedness #-}

-- THE RUN UP TO CALM POINTS.  A segment of the machine's trace against
-- the events the root is shown: a step on each side passes a guard, a
-- silent one on either side alone passes finitely often, and a calm
-- point resumes the run, unguarded only with fewer dead timers.
module adequacy.Segment where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; _<_)
open import Data.Unit using (⊤)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import denotation.MonotonicList using (Events; Events∞; Pos; out; skip; end; hush; tick)
import denotation.Unfold as U
open import operation.Machine using (module Machine)
open import adequacy.Realize using (module Realizing)

module Seg (R : Set) where
  open Machine R using (Mach; step; silent; shown; Trace; Trace∞; tau; out; end; idle; trace)
  open Realizing R using (Calm; dead)

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

