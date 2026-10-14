{-# OPTIONS --guardedness #-}

-- THE CONFIGURATION, DENOTED.  A running program between two turns of
-- the loop is a tree of live subscriptions — one node per subscription
-- still open — and each node means what is left of its own events.
-- `Bound` relates the engine's state to such a tree, and the root's
-- remaining events to the tree's meaning.
--
-- The tree is the meaning's own configuration (`denotation.Unfold`) plus
-- one piece of ghost state: a connect's source is SHARED, held once with
-- its joiners pointing at it by index, where the meaning gives each
-- joiner its own copy.  A tree means the unfolding of its copy-out, each
-- joiner copying the source as it stands now, each lane still queued
-- subscribed against the sources as they stand now.
--
-- What is left of the root's events and the tree's meaning agree up to
-- finitely many `skip`s between any two events (`_≅_`): a skip the run
-- has already passed — a `defer`'s, a dropped prefix's on a join, an
-- outer element's on a `flatMap` — shows in the one and not the other.
module Config where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (_∷_; lookup)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (Timeline; Time; Pos; Frame; Events; Events∞; out; skip; end; hush; quiet)
import denotation.Unfold as U
open import denotation.Unfold using (Srcs; step; hushˢ; headˢ; unfold; shown; subscribe; Earliest; earliest)

open Events∞

------------------------------------------------------------------------
-- Agreeing up to finitely many skips

-- WEAK BISIMILARITY.  Values and completions match one for one, at the
-- same positions; between them either side may take finitely many extra
-- skips, and skips may also pair off, forever if both diverge silently.
mutual
  infix 4 _≅_ _≅∞_
  data _≅_ {A : Set} : Events A → Events A → Set where
    out≅  : ∀ {p a l r} → l ≅∞ r → out p a l ≅ out p a r
    skip≅ : ∀ {p l r} → l ≅∞ r → skip p l ≅ skip p r
    skipˡ : ∀ {p l y} → force l ≅ y → skip p l ≅ y
    skipʳ : ∀ {p x r} → x ≅ force r → x ≅ skip p r
    end≅  : ∀ {p} → end p ≅ end p
    hush≅ : hush ≅ hush

  record _≅∞_ {A : Set} (l r : Events∞ A) : Set where
    coinductive
    field force : force l ≅ force r

------------------------------------------------------------------------
-- The tree

mutual
  data Node : List Set → Set → Set₁ where
    -- A cold inside a frame, or about to start one: its burst at step
    -- `i` of the frame at `r`, on a timeline subscribed at tick `τ`.
    coldᶜ      : ∀ {Δ A t} → Time → Pos → ℕ → Frame A t → Node Δ A
    -- Nothing more, ever: a cold gone quiet.
    quietᶜ     : ∀ {Δ A} → Node Δ A
    mapᶜ       : ∀ {Δ A B} → (A → B) → Node Δ A → Node Δ B
    -- The accumulator so far.
    scanᶜ      : ∀ {Δ A B} → (B → A → B) → B → Node Δ A → Node Δ B
    takeWhileᶜ : ∀ {Δ A} → Bool → (A → Bool) → Node Δ A → Node Δ A
    -- The outer while it lasts, the lanes in flight newest first, and
    -- the elements queued.
    flatMapᶜ   : ∀ {Δ A B} → T.FlatOp → (A → Obs Timeline Δ B) → Maybe (Node Δ A) → List (Node Δ B) → List A → Node Δ B
    connectᶜ   : ∀ {Δ A B} → Source Δ A → Node (A ∷ Δ) B → Node Δ B
    -- Joined at `j`, the subject's first `m` events past.
    joinᶜ      : ∀ {Δ A} → Pos → ℕ → A ∈ Δ → Node Δ A

  -- A connect's source: live, or completed at a position.
  data Source (Δ : List Set) (A : Set) : Set₁ where
    live     : Node Δ A → Source Δ A
    finished : Pos → Source Δ A

-- THE COPY-OUT: the meaning's configuration, given each source in scope
-- as it stands now.
mutual
  copy : ∀ {Δ A} → Node Δ A → Srcs Δ → U.Node A
  copy (coldᶜ τ r i b)         σ = U.burstᶜ τ r i b
  copy quietᶜ                  σ = U.framesᶜ 0 [] (quiet {t = 0})
  copy (mapᶜ f c)              σ = U.mapᶜ f (copy c σ)
  copy (scanᶜ f z c)           σ = U.scanᶜ f z (copy c σ)
  copy (takeWhileᶜ i p c)      σ = U.takeWhileᶜ i p (copy c σ)
  copy (flatMapᶜ op f o ls qs) σ = U.flatMapᶜ op (λ a q → subscribe (f a) σ q) (copyᵒ o σ) (copyˡ ls σ) qs
  copy (connectᶜ s b)          σ = copy b (copyˢ s σ ∷ σ)
  copy (joinᶜ j m i)           σ = U.joinᶜ j m (lookup σ i)

  copyᵒ : ∀ {Δ A} → Maybe (Node Δ A) → Srcs Δ → Maybe (U.Node A)
  copyᵒ nothing  σ = nothing
  copyᵒ (just c) σ = just (copy c σ)

  copyˡ : ∀ {Δ A} → List (Node Δ A) → Srcs Δ → List (U.Node A)
  copyˡ []       σ = []
  copyˡ (c ∷ cs) σ = copy c σ ∷ copyˡ cs σ

  copyˢ : ∀ {Δ A} → Source Δ A → Srcs Δ → U.Node A
  copyˢ (live c)     σ = copy c σ
  copyˢ (finished p) σ = U.endᶜ p

-- WHAT A NODE MEANS: what is left of its events.
⟦_⟧ᶜ : ∀ {Δ A} → Node Δ A → Srcs Δ → Events A
⟦ c ⟧ᶜ σ = unfold (copy c σ)

------------------------------------------------------------------------
-- A tree with nothing pending

-- A configuration with no event to come.
Silent : ∀ {A} → U.Node A → Set
Silent c = headˢ (step c) ≡ nothing

silent-hush : ∀ {A} (s : U.Step A) → headˢ s ≡ nothing → s ≡ hushˢ
silent-hush hushˢ e = refl

-- NO FRAME TO COME: every cold gone quiet, every joiner's subject
-- silent.  A joiner of a completed subject is not dry — it has a
-- completion still to show.
mutual
  Dry : ∀ {Δ A} → Node Δ A → Srcs Δ → Set
  Dry (coldᶜ τ r i b)         σ = ⊥
  Dry quietᶜ                  σ = ⊤
  Dry (mapᶜ f c)              σ = Dry c σ
  Dry (scanᶜ f z c)           σ = Dry c σ
  Dry (takeWhileᶜ i p c)      σ = Dry c σ
  Dry (flatMapᶜ op f o ls qs) σ = Dryᵒ o σ × Dryˡ ls σ
  Dry (connectᶜ s b)          σ = Dryˢ s σ × Dry b (copyˢ s σ ∷ σ)
  Dry (joinᶜ j m i)           σ = Silent (lookup σ i)

  Dryᵒ : ∀ {Δ A} → Maybe (Node Δ A) → Srcs Δ → Set
  Dryᵒ nothing  σ = ⊤
  Dryᵒ (just c) σ = Dry c σ

  Dryˡ : ∀ {Δ A} → List (Node Δ A) → Srcs Δ → Set
  Dryˡ []       σ = ⊤
  Dryˡ (c ∷ cs) σ = Dry c σ × Dryˡ cs σ

  Dryˢ : ∀ {Δ A} → Source Δ A → Srcs Δ → Set
  Dryˢ (live c)     σ = Dry c σ
  Dryˢ (finished p) σ = ⊤

-- A dry tree steps to silence.
mutual
  dry-step : ∀ {Δ A} (c : Node Δ A) (σ : Srcs Δ) → Dry c σ → step (copy c σ) ≡ hushˢ
  dry-step (coldᶜ τ r i b) σ ()
  dry-step quietᶜ          σ d = refl
  dry-step (mapᶜ f c)      σ d rewrite dry-step c σ d = refl
  dry-step (scanᶜ f z c)   σ d rewrite dry-step c σ d = refl
  dry-step (takeWhileᶜ i p c) σ d rewrite dry-step c σ d = refl
  dry-step (flatMapᶜ op f nothing ls qs) σ (_ , dl) rewrite dry-earliest ls σ dl = refl
  dry-step (flatMapᶜ op f (just o) ls qs) σ (dᵒ , dl) rewrite dry-earliest ls σ dl | dry-step o σ dᵒ = refl
  dry-step (connectᶜ s b)  σ (_ , d) = dry-step b (copyˢ s σ ∷ σ) d
  dry-step (joinᶜ j m i)   σ d rewrite silent-hush (step (lookup σ i)) d = refl

  dry-earliest : ∀ {Δ A} (cs : List (Node Δ A)) (σ : Srcs Δ) → Dryˡ cs σ → earliest (copyˡ cs σ) ≡ Earliest.none
  dry-earliest []       σ d        = refl
  dry-earliest (c ∷ cs) σ (d , ds) rewrite dry-step c σ d | dry-earliest cs σ ds = refl

-- A dry tree means silence.
dry-hush : ∀ {Δ A} (c : Node Δ A) (σ : Srcs Δ) → Dry c σ → ⟦ c ⟧ᶜ σ ≡ hush
dry-hush c σ d = cong shown (dry-step c σ d)

dry-silent : ∀ {Δ A} (c : Node Δ A) (σ : Srcs Δ) → Dry c σ → Silent (copy c σ)
dry-silent c σ d = cong headˢ (dry-step c σ d)
