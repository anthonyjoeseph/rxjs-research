{-# OPTIONS --guardedness #-}

-- THE TOLD RUN'S ROWS, against the run's.  `told x S` subscribed at `q`
-- runs `S` at `q ⊕ [ ix 1 ]` (`σ`) and reads it back through its subject
-- as the first lane of a concat at `w`, the queued `of [ x ]` second.
-- Each row of `σ` at `l` has one image at `l ⊕ δ e`: a pin the connect's
-- own copy, an end the queued lane's end, any other row the lane's copy.
-- Every other row of the told run is silent, or the queued value, and
-- lies in the subscribe instant or under a row of `σ`.
module simultaneous.ToldRows where

open import Data.List using (List; []; _∷_; [_])
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Tree using (Obs; connect; connected; of)
open import denotation.Position using (_≟ᵖ_; Pos; Path; ix; sub; last; _⊕_; root)
open import denotation.Events using (Timeline; fresh)
open import denotation.EmissionSet using (Ev; out; skip; end; pin; EmissionSet; Few; DenEnv; enter; approx; _≺_)
open import denotation.Laws.Worlds using (Ok; Hots; GoodEnv; _⊑_; InvAt; Real; inside-⊑; real-init; world-after⁼; ok-step)
open import denotation.Laws.Modulus using (≺-≼-≺; ≺-ext)
open import denotation.Laws using (inv-approx)
open import simultaneous.SObs using (lone; module Elaborate)
open import simultaneous.Readings using (instantOf)
open import simultaneous.Attribution using (Shown; One; Live)
open import simultaneous.Listing using (Listed)
open import simultaneous.CarryBase using (Whole)

open Elaborate {C = Timeline} _≟ᵖ_ root (fresh (λ p → p)) lone using (concatˢ)

-- A run read through its own subject by a concat queueing one more row.
told : ∀ {Γ Y} → Y → Obs Timeline Γ Y → Obs Timeline Γ Y
told x s = connect s (concatˢ (connected (here refl)) (of (x ∷ [])))

module Told {Γ Y} n (S : Obs Timeline Γ Y) (x : Y) (env : DenEnv Γ) (genv : GoodEnv env) (q : Pos) (ok : Ok (Hots env) q) where

  σ : EmissionSet Y
  σ = enter (approx n S env) (q ⊕ [ ix 1 ])

  τ : EmissionSet Y
  τ = enter (approx n (told x S) env) q

  -- The first lane's subscription: the concat's first value's second child.
  w : Pos
  w = q ⊕ (ix 0 ∷ ix 0 ∷ ix 1 ∷ [])

  -- Where a row of `σ` shows again.
  δ : Ev Y → Path
  δ (out _) = [ sub w ]
  δ skip    = [ sub w ]
  δ (pin _) = [ ix 0 ]
  δ end     = sub w ∷ ix 1 ∷ last ∷ []

  -- A row and its image: the same, a pin pinned by its own connect or,
  -- in the subscribe burst, by the told connect.
  data Told : Ev Y → Ev Y → Set where
    t-out  : ∀ {a} → Told (out a) (out a)
    t-skip : Told skip skip
    t-end  : Told end end
    t-pin  : ∀ {r r′} → r′ ≡ r ⊎ r′ ≡ q → Told (pin r) (pin r′)

  postulate
    -- A row with few before it shows again.  A pin past an endless
    -- synchronous burst of `σ` does not: the told connect cuts its burst
    -- pins there.
    told-row        : ∀ {l e} → σ l e → Few σ l → Σ (Ev Y) λ e′ → τ (l ⊕ δ e) e′ × Told e e′
    told-listed : ∀ {l e} → σ l e → Listed σ l → Listed τ (l ⊕ δ e)
    told-inj      : ∀ {l₁ l₂ e₁ e₂} → σ l₁ e₁ → σ l₂ e₂ → l₁ ⊕ δ e₁ ≡ l₂ ⊕ δ e₂ → l₁ ≡ l₂
    told-source?    : ∀ {m e′} → τ m e′ → (Σ Pos λ l → Σ (Ev Y) λ e → σ l e × m ≡ l ⊕ δ e) ⊎ (∀ {l e} → σ l e → m ≡ l ⊕ δ e → ⊥)
    told-shown  : ∀ {X} {f : Y → List X} → f x ≡ [] → ∀ {m e′} → τ m e′ → Shown (One f) e′
               → Σ Pos λ l → Σ (Ev Y) λ e → σ l e × m ≡ l ⊕ δ e × Told e e′
    told-from       : ∀ {m e′} → τ m e′ → instantOf m ≡ instantOf q ⊎ Σ Pos λ l → Σ (Ev Y) λ e → σ l e × l ⊑ m
    told-live←      : ∀ {m e′ l e} → τ m e′ → σ l e → l ⊑ m → Live τ m → Live σ l
    told-listed←    : ∀ {m e′ l e} → τ m e′ → σ l e → l ⊑ m → Listed τ m → Listed σ l
    told-few←       : ∀ {m e′ l e} → τ m e′ → σ l e → l ⊑ m → Few τ m → Few σ l
    told-live   : ∀ {l e} → σ l e → Live σ l → Live τ (l ⊕ δ e)
    told-live-at    : ∀ {l} → Live σ l → Live τ l
    told-whole      : Whole σ → Whole τ

  -- `σ`'s invariant, at the told run's second child.
  invσ : InvAt (Hots env) (q ⊕ [ ix 1 ]) σ
  invσ = inv-approx n S env genv (q ⊕ [ ix 1 ]) (ok-step q ok)

  -- A pin of `σ` is of a subscription in its world, so past `q`.
  told-pin-past : ∀ {l r} → σ l (pin r) → q ≺ r
  told-pin-past {l} {r} y =
    ≺-≼-≺ {q} {q ⊕ [ ix 1 ]} {r} (≺-ext q [])
      (world-after⁼ (proj₁ (InvAt.pinned invσ y)) (real-init r (proj₁ rl) (subst Real (proj₂ rl) (InvAt.real invσ y))))
    where
      rl = inside-⊑ r l (proj₂ (InvAt.pinned invσ y))
