-- THE SUBSCRIBING STEP: `scan((acc,x) => acc |> mergeMap(g))`, which is
-- the one case `Spike.Burst` is rejected on -- it recurses into what its
-- predecessor EMITTED rather than into the predecessor.
--
-- IT GOES THROUGH, on the CHAIN LENGTH.  `Val c l` is a value observed at
-- count c carrying an accumulator chain of at most l links; a subscribing
-- step charges one link and a mapping step charges none, so subscribing to
-- a chain of `suc l` hops a list at `l` and the implicit index is the
-- measure.  The mutual pair is accepted lexicographically: the instant
-- count falls on the source hop, the chain length on the subscribing step,
-- the list on the element walk.
--
-- WHY THIS CARRIER AND NOT THE THREE BEFORE IT.  A store index, an array
-- index and a frame-stack depth all ASCEND where a subscription allocates,
-- which is exactly where the hop needs descent.  A chain link is minted
-- where the value is BUILT and spent where it is CONSUMED, so the polarity
-- is right; `chain` and `spent` below are both real code and pin the two
-- directions.  It is LOCAL in the sense the fuel proposal failed: the index
-- is read off the value, nobody supplies it, and no call site owes a
-- sufficiency proof -- the chain is unbounded ACROSS instants while every
-- individual value's index is finite.
--
-- THE TWO POSTULATES ARE DISCHARGED IN `Spike.Text`, and one of them was
-- FALSE.  Both are the same question, because a runtime observable value is
-- closed text with the environment substituted in, so what they assert is a
-- property of SUBSTITUTION.  It is additive, not flat -- the flat bound is
-- machine-refuted there, since the substituted variable sits under a link
-- and pays for it.  So a mapping step DOES mint a link, `mapOf` charges one
-- here, and a source emits at the measure of its own static text rather
-- than at zero, which `statOf` now carries.  The measure survives both
-- repairs unchanged, which is the result.
--
-- STILL ASSERTED: that a node's emissions really are substitution instances
-- of its text.  That is a claim about `Rx.Evaluator`, not about the measure.
module Spike.Chain where

open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (<⇒≤; ≤-trans; ≤-refl; n≤1+n)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Induction.WellFounded using (Acc; acc)
open import Data.Nat.Induction using (<-wellFounded)

module _ (n : ℕ) (statOf : Fin n → ℕ) where

  -- Val c ℓ : observed at count c, carrying an accumulator chain of
  -- length at most ℓ
  data Val : ℕ → ℕ → Set where
    natᵛ : ∀ {c ℓ} → ℕ → Val c ℓ
    obsᵛ : ∀ {c ℓ} → (h : Fin n) → (d : ℕ) → d < c → statOf h ≤ ℓ → Val c ℓ
    accᴹ : ∀ {c ℓ} → Fin n → Val c ℓ → Val c (suc ℓ)    -- map step: a link, and no hop
    accᴴ : ∀ {c ℓ} → Fin n → Val c ℓ → Val c (suc ℓ)    -- mergeMap step: one link

  postulate
    -- a source emits at the measure of its OWN STATIC TEXT
    srcOf : (h : Fin n) → (d : ℕ) → List (Val d (statOf h))
    mapOf : ∀ {c ℓ} → Fin n → Val c ℓ → Val c (suc ℓ)

  wkC : ∀ {c c′ ℓ} → c ≤ c′ → Val c ℓ → Val c′ ℓ
  wkC le (natᵛ x)      = natᵛ x
  wkC le (obsᵛ h d lt sl) = obsᵛ h d (≤-trans lt le) sl
  wkC le (accᴹ h v)    = accᴹ h (wkC le v)
  wkC le (accᴴ h v)    = accᴴ h (wkC le v)

  wkℓ : ∀ {c ℓ ℓ′} → ℓ ≤ ℓ′ → Val c ℓ → Val c ℓ′
  wkℓ le      (natᵛ x)      = natᵛ x
  wkℓ le      (obsᵛ h d lt sl) = obsᵛ h d lt (≤-trans sl le)
  wkℓ (s≤s le) (accᴹ h v)   = accᴹ h (wkℓ le v)
  wkℓ (s≤s le) (accᴴ h v)   = accᴴ h (wkℓ le v)

  wkLC : ∀ {c c′ ℓ} → c ≤ c′ → List (Val c ℓ) → List (Val c′ ℓ)
  wkLC le []       = []
  wkLC le (v ∷ vs) = wkC le v ∷ wkLC le vs

  wkLℓ : ∀ {c ℓ ℓ′} → ℓ ≤ ℓ′ → List (Val c ℓ) → List (Val c ℓ′)
  wkLℓ le []       = []
  wkLℓ le (v ∷ vs) = wkℓ le v ∷ wkLℓ le vs

  subV : ∀ {c ℓ} → Acc _<_ c → Val c ℓ → List (Val c ℓ)
  hopL : ∀ {c ℓ} → Acc _<_ c → List (Val c ℓ) → List (Val c ℓ)

  subV a         (natᵛ x)      = natᵛ x ∷ []
  subV (acc rec) (obsᵛ h d lt sl) = wkLℓ sl (wkLC (<⇒≤ lt) (hopL (rec lt) (srcOf h d)))
  subV a         (accᴹ h v)    = map (mapOf h) (subV a v)
  subV a         (accᴴ h v)    = wkLℓ (n≤1+n _) (hopL a (subV a v))

  hopL a []       = []
  hopL a (v ∷ vs) = subV a v ++ hopL a vs

  -- NON-VACUITY, and it is the locality claim itself: the fold's k-th
  -- accumulator carries a chain of length exactly k, so the chain is
  -- UNBOUNDED across instants while every individual value's index is
  -- finite and READ OFF THE VALUE.  Nobody supplies it and nothing has
  -- to prove it sufficient, which is what separates it from fuel.
  chain : ∀ {c} → Fin n → (k : ℕ) → Val c k
  chain h zero    = natᵛ zero
  chain h (suc k) = accᴴ h (chain h k)

  -- and the polarity that the three refuted carriers got backwards:
  -- `accᴴ` ASCENDS where the value is built, so `subV` DESCENDS where
  -- it is consumed.  Both directions are real code above.
  spent : ∀ {c} → Acc _<_ c → Fin n → (k : ℕ) → List (Val c k)
  spent a h k = subV a (chain h k)
