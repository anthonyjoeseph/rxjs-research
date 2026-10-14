{-# OPTIONS --guardedness #-}

-- THE CONFIGURATION, DENOTED.  A running program between two turns of
-- the loop is a tree of live subscriptions — one node per subscription
-- still open — and each node means what is left of its own events.
-- `Bound` relates the engine's state to such a tree, and the root's
-- remaining events to the tree's meaning.
--
-- The tree's meaning is built from the denotation's own stream functions,
-- so a node means exactly what the denotation would show from where the
-- run stands: a cold its pending frames, a `flatMap` its sorted merge of
-- the outer and the lanes in flight, a joiner its subject's remaining
-- events rejoined.
--
-- What is left of the root's events and the tree's meaning agree up to
-- finitely many `skip`s between any two events (`_≅_`): a skip the run
-- has already passed — a `defer`'s, a dropped prefix's on a join, an
-- outer element's on a `flatMap` — shows in the one and not the other.
module Config where

open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; lookup) renaming (map to mapᴬ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import Tree as T
open import Tree using (Obs)
open import denotation.MonotonicList using (MonotonicList; hot; Timeline; Time; Pos; Burst; Events; Events∞; out; skip; end; hush; burst;
  rejoin; mapᴱ; scanᴱ; takeWhileᴱ; go; none; earliest)
open import denotation.Denote using (approx; flatOp)

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

-- The events each connect in scope is still to show its joiners: the
-- source's remainder, or its completion once it has completed.
Hots : List Set → Set₁
Hots = All Events

hots : ∀ {Δ} → Hots Δ → All MonotonicList Δ
hots = mapᴬ hot

module Nodes (n : ℕ) where

  -- A connect's source: live, or completed at a position.
  mutual
    data Node : List Set → Set → Set₁ where
      -- A cold inside a frame, or about to start one: its burst at step
      -- `i` of the frame at `r`, on a timeline subscribed at tick `τ`.
      coldᶜ      : ∀ {Δ A} → Time → Pos → ℕ → Burst A → Node Δ A
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

    data Source (Δ : List Set) (A : Set) : Set₁ where
      live     : Node Δ A → Source Δ A
      finished : Pos → Source Δ A

  -- WHAT A NODE MEANS: what is left of its events, given what is left of
  -- each subject's.
  mutual
    ⟦_⟧ᶜ : ∀ {Δ A} → Node Δ A → Hots Δ → Events A
    ⟦ coldᶜ τ r i b ⟧ᶜ          ρ = burst τ r i b
    ⟦ quietᶜ ⟧ᶜ                 ρ = hush
    ⟦ mapᶜ f c ⟧ᶜ               ρ = mapᴱ f (⟦ c ⟧ᶜ ρ)
    ⟦ scanᶜ f z c ⟧ᶜ            ρ = scanᴱ f z (⟦ c ⟧ᶜ ρ)
    ⟦ takeWhileᶜ i p c ⟧ᶜ       ρ = takeWhileᴱ i p (⟦ c ⟧ᶜ ρ)
    ⟦ flatMapᶜ op f o ls qs ⟧ᶜ  ρ = go (flatOp op) (⟦ o ⟧ᵒ f ρ) (⟦ ls ⟧ˡ ρ) (map (λ a → approx n (f a) (hots ρ)) qs)
    ⟦ connectᶜ s b ⟧ᶜ           ρ = ⟦ b ⟧ᶜ (⟦ s ⟧ˢ ρ ∷ ρ)
    ⟦ joinᶜ j m i ⟧ᶜ            ρ = rejoin j m (lookup ρ i)

    ⟦_⟧ᵒ : ∀ {Δ A B} → Maybe (Node Δ A) → (A → Obs Timeline Δ B) → Hots Δ → Maybe (Events (MonotonicList B))
    ⟦ nothing ⟧ᵒ f ρ = nothing
    ⟦ just c ⟧ᵒ  f ρ = just (mapᴱ (λ a → approx n (f a) (hots ρ)) (⟦ c ⟧ᶜ ρ))

    ⟦_⟧ˡ : ∀ {Δ A} → List (Node Δ A) → Hots Δ → List (Events A)
    ⟦ [] ⟧ˡ     ρ = []
    ⟦ c ∷ cs ⟧ˡ ρ = ⟦ c ⟧ᶜ ρ ∷ ⟦ cs ⟧ˡ ρ

    ⟦_⟧ˢ : ∀ {Δ A} → Source Δ A → Hots Δ → Events A
    ⟦ live c ⟧ˢ     ρ = ⟦ c ⟧ᶜ ρ
    ⟦ finished p ⟧ˢ ρ = end p

  ------------------------------------------------------------------------
  -- A tree with nothing pending

  -- NO FRAME TO COME: every cold gone quiet, every joiner's subject
  -- silent.  A joiner of a completed subject is not dry — it has a
  -- completion still to show.
  mutual
    Dry : ∀ {Δ A} → Node Δ A → Hots Δ → Set
    Dry (coldᶜ τ r i b)         ρ = ⊥
    Dry quietᶜ                  ρ = ⊤
    Dry (mapᶜ f c)              ρ = Dry c ρ
    Dry (scanᶜ f z c)           ρ = Dry c ρ
    Dry (takeWhileᶜ i p c)      ρ = Dry c ρ
    Dry (flatMapᶜ op f o ls qs) ρ = Dryᵒ o ρ × Dryˡ ls ρ
    Dry (connectᶜ s b)          ρ = Dryˢ s ρ × Dry b (⟦ s ⟧ˢ ρ ∷ ρ)
    Dry (joinᶜ j m i)           ρ = lookup ρ i ≡ hush

    Dryᵒ : ∀ {Δ A} → Maybe (Node Δ A) → Hots Δ → Set
    Dryᵒ nothing  ρ = ⊤
    Dryᵒ (just c) ρ = Dry c ρ

    Dryˡ : ∀ {Δ A} → List (Node Δ A) → Hots Δ → Set
    Dryˡ []       ρ = ⊤
    Dryˡ (c ∷ cs) ρ = Dry c ρ × Dryˡ cs ρ

    Dryˢ : ∀ {Δ A} → Source Δ A → Hots Δ → Set
    Dryˢ (live c)     ρ = Dry c ρ
    Dryˢ (finished p) ρ = ⊤

  -- An outer that is over, or silent.
  data Silent {B : Set} : Maybe (Events (MonotonicList B)) → Set where
    gone  : Silent nothing
    quiet : Silent (just hush)

  earliest-hush : ∀ {B} {es : List (Events B)} → All (_≡ hush) es → earliest es ≡ none
  earliest-hush []          = refl
  earliest-hush (refl ∷ hs) rewrite earliest-hush hs = refl

  go-hush : ∀ {B} op (o : Maybe (Events (MonotonicList B))) es qs → Silent o → All (_≡ hush) es → go op o es qs ≡ hush
  go-hush op o es qs s hs with earliest es | earliest-hush hs
  go-hush op .nothing      es qs gone  hs | .none | refl = refl
  go-hush op .(just hush)  es qs quiet hs | .none | refl = refl

  -- A dry tree means silence.
  mutual
    dry-hush : ∀ {Δ A} (c : Node Δ A) (ρ : Hots Δ) → Dry c ρ → ⟦ c ⟧ᶜ ρ ≡ hush
    dry-hush (coldᶜ τ r i b) ρ ()
    dry-hush quietᶜ          ρ d = refl
    dry-hush (mapᶜ f c)      ρ d with ⟦ c ⟧ᶜ ρ | dry-hush c ρ d
    ... | .hush | refl = refl
    dry-hush (scanᶜ f z c)   ρ d with ⟦ c ⟧ᶜ ρ | dry-hush c ρ d
    ... | .hush | refl = refl
    dry-hush (takeWhileᶜ i p c) ρ d with ⟦ c ⟧ᶜ ρ | dry-hush c ρ d
    ... | .hush | refl = refl
    dry-hush (flatMapᶜ op f o ls qs) ρ (dᵒ , dl) =
      go-hush (flatOp op) (⟦ o ⟧ᵒ f ρ) (⟦ ls ⟧ˡ ρ) _ (dry-hushᵒ o f ρ dᵒ) (dry-hushˡ ls ρ dl)
    dry-hush (connectᶜ s b)  ρ (_ , d) = dry-hush b (⟦ s ⟧ˢ ρ ∷ ρ) d
    dry-hush (joinᶜ j m i)   ρ d with lookup ρ i | d
    ... | .hush | refl = refl

    dry-hushᵒ : ∀ {Δ A B} (o : Maybe (Node Δ A)) (f : A → Obs Timeline Δ B) (ρ : Hots Δ) → Dryᵒ o ρ → Silent (⟦ o ⟧ᵒ f ρ)
    dry-hushᵒ nothing  f ρ d = gone
    dry-hushᵒ (just c) f ρ d with ⟦ c ⟧ᶜ ρ | dry-hush c ρ d
    ... | .hush | refl = quiet

    dry-hushˡ : ∀ {Δ A} (cs : List (Node Δ A)) (ρ : Hots Δ) → Dryˡ cs ρ → All (_≡ hush) (⟦ cs ⟧ˡ ρ)
    dry-hushˡ []       ρ d        = []
    dry-hushˡ (c ∷ cs) ρ (d , ds) = dry-hush c ρ d ∷ dry-hushˡ cs ρ ds
