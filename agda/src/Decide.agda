-- DECIDER↔PROPOSITION ADAPTERS: the little facts that move between a
-- `Bool`-valued decision procedure and a proposition about it — `≡ true`,
-- `T b`, `_≡ᵇ_`, `Maybe` injectivity, and the elimination of an absurd
-- equation.  Nothing here mentions a type of the rxjs model or of the
-- proof; it imports the standard library and nothing else, which is what
-- lets it sit below every tree.
--
-- WHY IT EXISTS, and it is a wiring finding rather than a tidy-up.  This
-- class had no home, so it accreted A COPY PER TREE: at the time this
-- module was created the repo held FOUR names for `true ≢ false` and TWO
-- byte-identical `∧-intro`s, one on each side of the tier boundary.  The
-- duplicate pair was invisible to `make dup-check`, whose normalisation
-- covers binder spelling and type synonyms but not redundant parentheses
-- (`a ∧ b ≡ true` against `(a ∧ b) ≡ true`), so the compiler could not
-- see it either — neither copy was ever in scope with the other.
--
-- AND IT IS WHAT KEEPS THE TIER DOORS NARROW.  A utility lemma reached
-- for across a tier boundary reads as a claim on that tier to anyone
-- counting the doors into it.  These are not claims on anything; they
-- are arithmetic.  With one home below every tree, each tier exports
-- exactly the statements it proves.
--
-- ONE MODULE, DELIBERATELY, AND NOT A `utils/` DIRECTORY (Anthony's
-- proposal, narrowed here).  The standing rule is ONE naming convention
-- per class of fact, because two conventions are the machine that
-- generates duplicates — and a directory named for its ROLE re-admits as
-- many conventions as it has files.  One module named for its CONTENT
-- makes "does this already exist?" a grep of one file.  Nothing here is
-- mutual with anything, so there is no SCC reason to split it, and the
-- cost of checking it is nil.
--
-- THE NAMES ARE NOT NORMALISED, AND THAT IS A RULING, NOT AN OVERSIGHT.
-- The class arrived with several conventions at once (`≡ᵇ-refl`,
-- `≡ᵇ→≡`, `just-injᵂ`), and renaming to one of them rewrites call sites
-- for no proof content.  The duplicate-generating mechanism is LOCALITY,
-- not spelling: with every such fact in one file, the check before
-- adding one is reading this file.  Match a neighbour's convention when
-- you add to it; do not launch a rename.
--
-- RECOVERY: git show 9a72dff:agda/src/Decide.agda restores the fifteen
--   adapters that went with the protocol face — the ∧/∨/not/if shelf,
--   the `≤ᵇ`/`≢ᵇ` order adapters, and `f≡t-absurd`.  Every one of them
--   was consumed by that face and by nothing else.
module Decide where

open import Data.Bool using (true)
open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong)

------------------------------------------------------------------
-- ℕ's Bool-valued equality
------------------------------------------------------------------

≡ᵇ-refl : ∀ (m : ℕ) → (m ≡ᵇ m) ≡ true
≡ᵇ-refl zero    = refl
≡ᵇ-refl (suc m) = ≡ᵇ-refl m

≡ᵇ-sym : ∀ (a b : ℕ) → (a ≡ᵇ b) ≡ (b ≡ᵇ a)
≡ᵇ-sym zero    zero    = refl
≡ᵇ-sym zero    (suc b) = refl
≡ᵇ-sym (suc a) zero    = refl
≡ᵇ-sym (suc a) (suc b) = ≡ᵇ-sym a b

≡ᵇ→≡ : ∀ (m k : ℕ) → (m ≡ᵇ k) ≡ true → m ≡ k
≡ᵇ→≡ zero    zero    _ = refl
≡ᵇ→≡ (suc m) (suc k) h = cong suc (≡ᵇ→≡ m k h)

------------------------------------------------------------------
-- Maybe
------------------------------------------------------------------

just-injᵂ : ∀ {A : Set} {x y : A} → _≡_ {A = Maybe A} (just x) (just y) → x ≡ y
just-injᵂ refl = refl

n≢jᵂ : ∀ {A : Set} {x : A} → _≡_ {A = Maybe A} nothing (just x) → ⊥
n≢jᵂ ()
