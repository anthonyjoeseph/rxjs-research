{-# OPTIONS --guardedness #-}

-- THE STEPPER IS THE MEANING, skips included: a sane, placed ghost's
-- meaning is what its step shows, then the meaning of the node it
-- leaves.  Stated at the root, where no connect's source is in scope;
-- inside a body the step is the run's next event only if it comes before
-- each running source's, its pool's and each ended source's rest.
module adequacy.Stepper where

open import Data.List using ([])
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.List.Relation.Unary.All using () renaming ([] to []ᴬ)

open import denotation.MonotonicList using (Events; out; skip; end; hush; Agree)
import denotation.Unfold as U
open import denotation.Unfold using (NEnv)
open import adequacy.Sane using (Sane)
open import adequacy.Placed using (Atop; Ordered; ordered; ordered-≈; Placed; Within)

------------------------------------------------------------------------
-- Alike: the same events at the same positions, skips and what a cut
-- leaves running included, to any depth.

record _≃_ {A : Set} (x y : Events A) : Set where
  constructor alike
  field agreeing : ∀ n → Agree n x y

open _≃_

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

postulate
  -- A joiner told its end while its source runs is fed the source's
  -- values by the stepper and shows them, where the meaning reads it as
  -- its end alone; so the ghost is sane.  A cut leaves running what its
  -- tail says, and the stepper runs it as the pool's and the rests' skips.
  --
  -- REFUTED: 3e2af71f stated of every node, by a told joiner under a live source
  -- REFUTED: 082ad778 stated without the body sane, by a joiner told its end
  -- DEAD ROUTE: exact agreement with a ghost anchored in its sources'
  --   step history.  The ghost is the witness's open part (`part`), which
  --   keeps no count of a source's steps, and a silent run is matched by
  --   the residual as a set alone (`Ahead`), so no field of the witness
  --   can keep the count a lane's pre-join skips need.
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Stepper.agda restores the stepper over a meaning with no tails, node by node
  -- RECOVERY: git show 43da74d9:agda-impl/adequacy/Sane.agda restores `sane-feed`, which that stepper fed its sources' steps through
  step-skips : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → U.meaning g []ᴬ ≃ afterᴱ []ᴬ (U.step g)

  -- What a sane, placed ghost's step leaves holds its parts placed.
  --
  -- REFUTED: d2d13661 without the step coming first, by a merge whose joiner lane shows its source's earlier event
  -- REFUTED: c8c55884 over a placing with each live joiner joined before its source, by a lane admitted past its source's next event
  within-step : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Withinˢ []ᴬ (U.step g)

-- A STEP KEEPS THE GHOST PLACED: atop what the step shows.
placed-after : ∀ {A} (g : U.Node [] A) → Sane []ᴬ g → Placed g []ᴬ → Placedˢ []ᴬ (U.step g)
placed-after g sn pl = placed-step []ᴬ (U.step g) (step-skips g sn pl) (proj₁ pl) (within-step g sn pl)
