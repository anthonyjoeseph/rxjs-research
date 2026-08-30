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
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Nat  using (ℕ; suc; _+_; _*_; _≤_; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Data.Nat.Properties
  using (+-mono-≤; ≤-refl; ≤-trans; ≤-reflexive;
         *-suc; *-distribˡ-+; *-identityʳ)

open import Rx.Exp using (Ctx; Exp; Tm;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ;
                          syncSizeᵉ; syncSizeᵗ; syncSizeᵗˢ; unfoldμ;
                          elimGExp; elimGTm; elimGTms)

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


-- THE CLOSURE IS THE SYNC SIZE TIMES A CEILING ON THE TELESCOPE, and
-- this is the reading a caps receipt can actually buy.  The two
-- measures run the SAME traversal and part company at exactly one
-- leaf, `input`, so a ceiling on the environment multiplies straight
-- through: every constructor's own `suc` is absorbed because a factor
-- of at least one is being paid at every node beneath it.  What it
-- converts is a quantity nothing prices -- a term's size THROUGH the
-- telescope -- into two the frame already carries, the term's own sync
-- size and a bound on the slots.
-- REFUTED: `Refuted.Nest-Clos-Stratified`, which is why the slot
--   ceiling has to be there: without it the ratio is unbounded in the
--   slot COUNT, and no fixed number of frame levels pays for it.
private
  mulSuc : ∀ (M y : ℕ) → 1 ≤ M → suc (M * y) ≤ M * suc y
  mulSuc M y 1≤M =
    ≤-trans (+-mono-≤ 1≤M (≤-refl {M * y})) (≤-reflexive (sym (*-suc M y)))

  mul-+ : ∀ (M a b : ℕ) → M * a + M * b ≡ M * (a + b)
  mul-+ M a b = sym (*-distribˡ-+ M a b)

  mul-1 : ∀ (M x : ℕ) → x ≤ M → x ≤ M * 1
  mul-1 M x h = ≤-trans h (≤-reflexive (sym (*-identityʳ M)))

  mulStep1 : ∀ (M s x : ℕ) → 1 ≤ M → x ≤ M * s → suc x ≤ M * suc s
  mulStep1 M s x 1≤M h = ≤-trans (s≤s h) (mulSuc M s 1≤M)

  mulStep2 : ∀ (M a b x y : ℕ) → 1 ≤ M → x ≤ M * a → y ≤ M * b →
    suc (x + y) ≤ M * suc (a + b)
  mulStep2 M a b x y 1≤M hx hy =
    mulStep1 M (a + b) (x + y) 1≤M
      (≤-trans (+-mono-≤ hx hy) (≤-reflexive (mul-+ M a b)))

  mulStep3 : ∀ (M a b c x y z : ℕ) → 1 ≤ M →
    x ≤ M * a → y ≤ M * b → z ≤ M * c →
    suc (x + y + z) ≤ M * suc (a + b + c)
  mulStep3 M a b c x y z 1≤M hx hy hz =
    mulStep1 M (a + b + c) (x + y + z) 1≤M
      (≤-trans (+-mono-≤ (≤-trans (+-mono-≤ hx hy) (≤-reflexive (mul-+ M a b))) hz)
               (≤-reflexive (mul-+ M (a + b) c)))

mutual
  closSize≤mulᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) (M : ℕ) →
    (∀ i → σ i ≤ M) → 1 ≤ M → (x : Exp Γ Δᵍ Δ Θ t) →
    closSizeᵉ σ x ≤ M * syncSizeᵉ x
  closSize≤mulᵉ σ M hσ 1≤M (input i)         = mul-1 M (σ i) (hσ i)
  closSize≤mulᵉ σ M hσ 1≤M (ofᵉ ts)          =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗˢ σ M hσ 1≤M ts)
  closSize≤mulᵉ σ M hσ 1≤M emptyᵉ            = mul-1 M 1 1≤M
  closSize≤mulᵉ σ M hσ 1≤M (mapᵉ f e)        =
    mulStep2 M _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M f) (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (takeᵉ c e)       =
    mulStep2 M _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M c) (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (scanᵉ f z e)     =
    mulStep3 M _ _ _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M f)
             (closSize≤mulᵗ σ M hσ 1≤M z) (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (mergeAllᵉ lim e) =
    mulStep1 M _ _ 1≤M (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (switchAllᵉ e)    =
    mulStep1 M _ _ 1≤M (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (exhaustAllᵉ e)   =
    mulStep1 M _ _ 1≤M (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (μᵉ e)            =
    mulStep1 M _ _ 1≤M (closSize≤mulᵉ σ M hσ 1≤M e)
  closSize≤mulᵉ σ M hσ 1≤M (varᵉ x)          = mul-1 M 1 1≤M
  closSize≤mulᵉ σ M hσ 1≤M (deferᵉ e)        = mul-1 M 1 1≤M

  closSize≤mulᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) (M : ℕ) →
    (∀ i → σ i ≤ M) → 1 ≤ M → (f : Tm Γ Δᵍ Δ Θ t) →
    closSizeᵗ σ f ≤ M * syncSizeᵗ f
  closSize≤mulᵗ σ M hσ 1≤M (varᵗ x)      = mul-1 M 1 1≤M
  closSize≤mulᵗ σ M hσ 1≤M unit̂          = mul-1 M 1 1≤M
  closSize≤mulᵗ σ M hσ 1≤M (bool̂ _)      = mul-1 M 1 1≤M
  closSize≤mulᵗ σ M hσ 1≤M (nat̂ _)       = mul-1 M 1 1≤M
  closSize≤mulᵗ σ M hσ 1≤M (pairᵗ a b)   =
    mulStep2 M _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M a) (closSize≤mulᵗ σ M hσ 1≤M b)
  closSize≤mulᵗ σ M hσ 1≤M (fstᵗ p)      =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M p)
  closSize≤mulᵗ σ M hσ 1≤M (sndᵗ p)      =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M p)
  closSize≤mulᵗ σ M hσ 1≤M (inlᵗ a)      =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M a)
  closSize≤mulᵗ σ M hσ 1≤M (inrᵗ a)      =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M a)
  closSize≤mulᵗ σ M hσ 1≤M (caseᵗ s l r) =
    mulStep3 M _ _ _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M s)
             (closSize≤mulᵗ σ M hσ 1≤M l) (closSize≤mulᵗ σ M hσ 1≤M r)
  closSize≤mulᵗ σ M hσ 1≤M (ifᵗ c a b)   =
    mulStep3 M _ _ _ _ _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M c)
             (closSize≤mulᵗ σ M hσ 1≤M a) (closSize≤mulᵗ σ M hσ 1≤M b)
  closSize≤mulᵗ σ M hσ 1≤M (primᵗ _ a)   =
    mulStep1 M _ _ 1≤M (closSize≤mulᵗ σ M hσ 1≤M a)
  closSize≤mulᵗ σ M hσ 1≤M (strmᵗ e)     =
    mulStep1 M _ _ 1≤M (closSize≤mulᵉ σ M hσ 1≤M e)

  closSize≤mulᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (σ : Fin n → ℕ) (M : ℕ) →
    (∀ i → σ i ≤ M) → 1 ≤ M → (ts : List (Tm Γ Δᵍ Δ Θ t)) →
    closSizeᵗˢ σ ts ≤ M * syncSizeᵗˢ ts
  closSize≤mulᵗˢ σ M hσ 1≤M []       = mul-1 M 1 1≤M
  closSize≤mulᵗˢ σ M hσ 1≤M (y ∷ ys) =
    ≤-trans (+-mono-≤ (closSize≤mulᵗ σ M hσ 1≤M y) (closSize≤mulᵗˢ σ M hσ 1≤M ys))
            (≤-reflexive (mul-+ M (syncSizeᵗ y) (syncSizeᵗˢ ys)))

-- AN UNFOLD LEAVES THE CLOSURE WHERE IT WAS, for the reason the bare
-- size is left where it was: `unfoldμ` substitutes the whole `μᵉ`
-- only at DEFER-GATED variable positions, and a defer is a leaf in
-- both measures -- so the substituted copies sit under a cut and
-- nothing about them is counted.  The environment is untouched
-- throughout, the substitution introducing no new `input`.
-- TWIN: `Verify-Budget-Sufficient.Measures.syncSize-elimG`, proven,
--   whose clauses this mirrors one for one; the only clause that is
--   not a copy is `input`, where both sides read the same `σ i`.
mutual
  closSize-elimG : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (σ : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (e : Exp Γ Δᵍ Δ Θ u) →
    closSizeᵉ σ (elimGExp x cl e) ≡ closSizeᵉ σ e
  closSize-elimG σ x cl (input i)       = refl
  closSize-elimG σ x cl (ofᵉ ts)        = cong suc (closSize-elimGᵗˢ σ x cl ts)
  closSize-elimG σ x cl emptyᵉ          = refl
  closSize-elimG σ x cl (mapᵉ f e)      =
    cong suc (cong₂ _+_ (closSize-elimGᵗ σ x cl f) (closSize-elimG σ x cl e))
  closSize-elimG σ x cl (takeᵉ c e)     =
    cong suc (cong₂ _+_ (closSize-elimGᵗ σ x cl c) (closSize-elimG σ x cl e))
  closSize-elimG σ x cl (scanᵉ f z e)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (closSize-elimGᵗ σ x cl f)
                                   (closSize-elimGᵗ σ x cl z))
                        (closSize-elimG σ x cl e))
  closSize-elimG σ x cl (mergeAllᵉ lim e) = cong suc (closSize-elimG σ x cl e)
  closSize-elimG σ x cl (switchAllᵉ e)  = cong suc (closSize-elimG σ x cl e)
  closSize-elimG σ x cl (exhaustAllᵉ e) = cong suc (closSize-elimG σ x cl e)
  closSize-elimG σ x cl (μᵉ e)          = cong suc (closSize-elimG σ (there x) cl e)
  closSize-elimG σ x cl (varᵉ y)        = refl
  closSize-elimG σ x cl (deferᵉ e)      = refl

  closSize-elimGᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (σ : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (f : Tm Γ Δᵍ Δ Θ u) →
    closSizeᵗ σ (elimGTm x cl f) ≡ closSizeᵗ σ f
  closSize-elimGᵗ σ x cl (varᵗ y)      = refl
  closSize-elimGᵗ σ x cl unit̂          = refl
  closSize-elimGᵗ σ x cl (bool̂ _)      = refl
  closSize-elimGᵗ σ x cl (nat̂ _)       = refl
  closSize-elimGᵗ σ x cl (pairᵗ a b)   =
    cong suc (cong₂ _+_ (closSize-elimGᵗ σ x cl a) (closSize-elimGᵗ σ x cl b))
  closSize-elimGᵗ σ x cl (fstᵗ p)      = cong suc (closSize-elimGᵗ σ x cl p)
  closSize-elimGᵗ σ x cl (sndᵗ p)      = cong suc (closSize-elimGᵗ σ x cl p)
  closSize-elimGᵗ σ x cl (inlᵗ a)      = cong suc (closSize-elimGᵗ σ x cl a)
  closSize-elimGᵗ σ x cl (inrᵗ a)      = cong suc (closSize-elimGᵗ σ x cl a)
  closSize-elimGᵗ σ x cl (caseᵗ s l r) =
    cong suc (cong₂ _+_ (cong₂ _+_ (closSize-elimGᵗ σ x cl s)
                                   (closSize-elimGᵗ σ x cl l))
                        (closSize-elimGᵗ σ x cl r))
  closSize-elimGᵗ σ x cl (ifᵗ c a b)   =
    cong suc (cong₂ _+_ (cong₂ _+_ (closSize-elimGᵗ σ x cl c)
                                   (closSize-elimGᵗ σ x cl a))
                        (closSize-elimGᵗ σ x cl b))
  closSize-elimGᵗ σ x cl (primᵗ _ a)   = cong suc (closSize-elimGᵗ σ x cl a)
  closSize-elimGᵗ σ x cl (strmᵗ e)     = cong suc (closSize-elimG σ x cl e)

  closSize-elimGᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u t} (σ : Fin n → ℕ) (x : t ∈ Δᵍ)
    (cl : Exp Γ [] [] [] t) (ts : List (Tm Γ Δᵍ Δ Θ u)) →
    closSizeᵗˢ σ (elimGTms x cl ts) ≡ closSizeᵗˢ σ ts
  closSize-elimGᵗˢ σ x cl []       = refl
  closSize-elimGᵗˢ σ x cl (y ∷ ys) =
    cong₂ _+_ (closSize-elimGᵗ σ x cl y) (closSize-elimGᵗˢ σ x cl ys)

closSize-unfoldμ : ∀ {n} {Γ : Ctx n} {t} (σ : Fin n → ℕ)
  (body : Exp Γ (t ∷ []) [] [] t) →
  closSizeᵉ σ (unfoldμ body) ≡ closSizeᵉ σ body
closSize-unfoldμ σ body = closSize-elimG σ (here refl) (μᵉ body) body
