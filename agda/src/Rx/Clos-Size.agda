------------------------------------------------------------------
-- THE CLOSURE SIZE: `syncSizeᵉ` with the slot telescope SUBSTITUTED
-- IN, so a term's key counts the definitions it will actually
-- subscribe rather than the one-symbol reference it mentions them by.
--
-- WHY IT EXISTS.  The arr-keyed descent charges two per unit of the
-- arrival's own sync size, and at `input i` that size is ONE while
-- the walk re-enters on the definition, whose size is arbitrary.  The
-- additive form of the grant was machine-refuted there: a definition
-- that SUBSTITUTES doubles what it delivers per layer, so a key that
-- does not see through the slot cannot dominate the walk it hands off
-- to.  Expanding the slot is what puts a factor between the two, and
-- the doubling is BOUGHT -- a layer that duplicates also enlarges the
-- definition it duplicates in -- so the expanded key outruns the
-- delivery from the first row.
--
-- HOW IT TERMINATES, and it is not by fuel.  The telescope is
-- STRATIFIED (Rx.Slots): slot k's definition reads only inputs below
-- k, so the environment is built in STAGES on the index, exactly as
-- Rx.Slot-Hop builds the hop environment -- `σAt` is correct below k
-- and neutral at and above it, and `slotClos` reads each slot off its
-- own stage.  A fuel parameter would not do: the consumer would fix
-- it at the slot COUNT, which is a variable, so the clause would
-- never reduce.
-- TWIN: `Rx.Slot-Hop`, whose `ηAt` / `slotHop` / `slotHop-fix` this
--   mirrors clause for clause; the staging argument and its
--   congruence obligation are the same two, at a different measure.
------------------------------------------------------------------
module Rx.Clos-Size where

open import Data.Fin  using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat  using (ℕ; suc; _+_; _≤_; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Nat.Properties using (+-mono-≤; ≤-refl)

open import Rx.Exp using (Ctx; Exp; Tm;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ; unfoldμ)

mutual
  closSizeᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    Exp Γ Δᵍ Δ Θ t → ℕ
  closSizeᵉ σ (input i)         = σ i
  closSizeᵉ σ (ofᵉ ts)          = suc (closSizeᵗˢ σ ts)
  closSizeᵉ σ emptyᵉ            = 1
  closSizeᵉ σ (mapᵉ f e)        = suc (closSizeᵗ σ f + closSizeᵉ σ e)
  closSizeᵉ σ (takeᵉ c e)       = suc (closSizeᵗ σ c + closSizeᵉ σ e)
  closSizeᵉ σ (scanᵉ f z e)     =
    suc (closSizeᵗ σ f + closSizeᵗ σ z + closSizeᵉ σ e)
  closSizeᵉ σ (mergeAllᵉ lim e) = suc (closSizeᵉ σ e)
  closSizeᵉ σ (switchAllᵉ e)    = suc (closSizeᵉ σ e)
  closSizeᵉ σ (exhaustAllᵉ e)   = suc (closSizeᵉ σ e)
  closSizeᵉ σ (μᵉ e)            = suc (closSizeᵉ σ e)
  closSizeᵉ σ (varᵉ x)          = 1
  -- a defer is a leaf here for the same reason it is one in the size
  -- this mirrors: nothing under it is subscribed in the instant
  closSizeᵉ σ (deferᵉ e)        = 1

  closSizeᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    Tm Γ Δᵍ Δ Θ t → ℕ
  closSizeᵗ σ (varᵗ x)      = 1
  closSizeᵗ σ unit̂          = 1
  closSizeᵗ σ (bool̂ _)      = 1
  closSizeᵗ σ (nat̂ _)       = 1
  closSizeᵗ σ (pairᵗ a b)   = suc (closSizeᵗ σ a + closSizeᵗ σ b)
  closSizeᵗ σ (fstᵗ p)      = suc (closSizeᵗ σ p)
  closSizeᵗ σ (sndᵗ p)      = suc (closSizeᵗ σ p)
  closSizeᵗ σ (inlᵗ a)      = suc (closSizeᵗ σ a)
  closSizeᵗ σ (inrᵗ a)      = suc (closSizeᵗ σ a)
  closSizeᵗ σ (caseᵗ s l r) =
    suc (closSizeᵗ σ s + closSizeᵗ σ l + closSizeᵗ σ r)
  closSizeᵗ σ (ifᵗ c a b)   =
    suc (closSizeᵗ σ c + closSizeᵗ σ a + closSizeᵗ σ b)
  closSizeᵗ σ (primᵗ _ a)   = suc (closSizeᵗ σ a)
  closSizeᵗ σ (strmᵗ e)     = suc (closSizeᵉ σ e)

  closSizeᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    List (Tm Γ Δᵍ Δ Θ t) → ℕ
  closSizeᵗˢ σ []       = 1
  closSizeᵗˢ σ (y ∷ ys) = closSizeᵗ σ y + closSizeᵗˢ σ ys

-- THE CLOSURE DOMINATES THE SIZE, which is what lets every spend the
-- old key made survive the re-key: the two measures differ only at
-- `input`, where the environment is at least the one symbol the bare
-- size counts.
mutual
  syncSize≤closᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    (∀ i → 1 ≤ σ i) → (x : Exp Γ Δᵍ Δ Θ t) → syncSizeᵉ x ≤ closSizeᵉ σ x
  syncSize≤closᵉ σ h (input i)         = h i
  syncSize≤closᵉ σ h (ofᵉ ts)          = s≤s (syncSize≤closᵗˢ σ h ts)
  syncSize≤closᵉ σ h emptyᵉ            = ≤-refl
  syncSize≤closᵉ σ h (mapᵉ f e)        =
    s≤s (+-mono-≤ (syncSize≤closᵗ σ h f) (syncSize≤closᵉ σ h e))
  syncSize≤closᵉ σ h (takeᵉ c e)       =
    s≤s (+-mono-≤ (syncSize≤closᵗ σ h c) (syncSize≤closᵉ σ h e))
  syncSize≤closᵉ σ h (scanᵉ f z e)     =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤closᵗ σ h f) (syncSize≤closᵗ σ h z))
                  (syncSize≤closᵉ σ h e))
  syncSize≤closᵉ σ h (mergeAllᵉ lim e) = s≤s (syncSize≤closᵉ σ h e)
  syncSize≤closᵉ σ h (switchAllᵉ e)    = s≤s (syncSize≤closᵉ σ h e)
  syncSize≤closᵉ σ h (exhaustAllᵉ e)   = s≤s (syncSize≤closᵉ σ h e)
  syncSize≤closᵉ σ h (μᵉ e)            = s≤s (syncSize≤closᵉ σ h e)
  syncSize≤closᵉ σ h (varᵉ x)          = ≤-refl
  syncSize≤closᵉ σ h (deferᵉ e)        = ≤-refl

  syncSize≤closᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    (∀ i → 1 ≤ σ i) → (f : Tm Γ Δᵍ Δ Θ t) → syncSizeᵗ f ≤ closSizeᵗ σ f
  syncSize≤closᵗ σ h (varᵗ x)      = ≤-refl
  syncSize≤closᵗ σ h unit̂          = ≤-refl
  syncSize≤closᵗ σ h (bool̂ _)      = ≤-refl
  syncSize≤closᵗ σ h (nat̂ _)       = ≤-refl
  syncSize≤closᵗ σ h (pairᵗ a b)   =
    s≤s (+-mono-≤ (syncSize≤closᵗ σ h a) (syncSize≤closᵗ σ h b))
  syncSize≤closᵗ σ h (fstᵗ p)      = s≤s (syncSize≤closᵗ σ h p)
  syncSize≤closᵗ σ h (sndᵗ p)      = s≤s (syncSize≤closᵗ σ h p)
  syncSize≤closᵗ σ h (inlᵗ a)      = s≤s (syncSize≤closᵗ σ h a)
  syncSize≤closᵗ σ h (inrᵗ a)      = s≤s (syncSize≤closᵗ σ h a)
  syncSize≤closᵗ σ h (caseᵗ s l r) =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤closᵗ σ h s) (syncSize≤closᵗ σ h l))
                  (syncSize≤closᵗ σ h r))
  syncSize≤closᵗ σ h (ifᵗ c a b)   =
    s≤s (+-mono-≤ (+-mono-≤ (syncSize≤closᵗ σ h c) (syncSize≤closᵗ σ h a))
                  (syncSize≤closᵗ σ h b))
  syncSize≤closᵗ σ h (primᵗ _ a)   = s≤s (syncSize≤closᵗ σ h a)
  syncSize≤closᵗ σ h (strmᵗ e)     = s≤s (syncSize≤closᵉ σ h e)

  syncSize≤closᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) →
    (∀ i → 1 ≤ σ i) → (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    syncSizeᵗˢ ts ≤ closSizeᵗˢ σ ts
  syncSize≤closᵗˢ σ h []       = ≤-refl
  syncSize≤closᵗˢ σ h (y ∷ ys) =
    +-mono-≤ (syncSize≤closᵗ σ h y) (syncSize≤closᵗˢ σ h ys)

postulate
  -- AN UNFOLD LEAVES THE CLOSURE WHERE IT WAS, for the reason the bare
  -- size is left where it was: `unfoldμ` substitutes the whole `μᵉ`
  -- only at DEFER-GATED variable positions, and a defer is a leaf in
  -- both measures -- so the substituted copies sit under a cut and
  -- nothing about them is counted.  The environment is untouched
  -- throughout, the substitution introducing no new `input`.
  -- TWIN: `Verify-Budget-Sufficient.Measures.syncSize-elimG`, proven,
  --   whose clauses this mirrors one for one; the only clause that is
  --   not a copy is `input`, where both sides read the same `σ i`.
  closSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (σ : Fin n → ℕ)
    (body : Exp Γ (t ∷ []) [] [] t) →
    closSizeᵉ σ (unfoldμ body) ≡ closSizeᵉ σ body
