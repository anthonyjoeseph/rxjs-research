-- WHAT `Spike.Chain` POSTULATED, DISCHARGED.  That module asserted two
-- things about the real evaluator: that a primitive source emits at chain
-- zero (`srcOf`) and that a mapping step mints no link (`mapOf`).  Both are
-- the SAME question, because `Val G (obs t) = Exp G [] [] [] t` -- a runtime
-- observable value is CLOSED text, and `ofE` holds terms, so every value a
-- node emits is step text with the environment substituted into it.  So the
-- question is what SUBSTITUTION does to the chain measure, and that is a
-- lemma rather than an assumption.
--
-- It is ADDITIVE, and `sub-links` proves it: substituting into text of
-- measure `a` from an environment bounded by `b` lands at `a + b`.  The
-- interesting clause is `mrgE`, where the substituted variable sits UNDER a
-- link and so pays for it -- which is why the bound cannot be `a ⊔ b`, and
-- why a fold whose step subscribes grows its accumulator's chain by one per
-- instant instead of holding it flat.  That is `Spike.Chain`'s `chain` with
-- a proof under it.
--
-- The two postulates come out as corollaries with their statements moved.
-- `mapOf` is FALSE as `Spike.Chain` states it -- a map function may contain
-- `strmT`, so a mapping step CAN mint links -- and harmless, because a map
-- does not hop: `sub-step` charges it additively and nothing recurses.
-- `srcOf` is right in shape and wrong in the constant: a primitive source
-- emits at the measure of its OWN TEXT, which is a static read-off rather
-- than zero, and `src-static` is that statement.
--
-- NOT COVERED: this is the measure under substitution only.  There is no
-- evaluator here, so nothing checks that a node's emissions are in fact
-- substitution instances of its text -- that is the remaining assumption,
-- and it is a claim about `Rx.Evaluator` rather than about the measure.
module Spike.Text where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ⊔-mono-≤; +-distribʳ-⊔; ⊔-identityʳ)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------
-- Text with de Bruijn value variables.  `strmT` is what makes a step
-- function able to build new program text, and it is the whole reason
-- the chain exists.
------------------------------------------------------------------

mutual
  data Tm (m : ℕ) : Set where
    varᵗ  : Fin m → Tm m
    natᵗ  : ℕ → Tm m
    strmᵗ : Ex m → Tm m

  data Ex (m : ℕ) : Set where
    ofᵉ  : List (Tm m) → Ex m
    mapᵉ : Tm (suc m) → Ex m → Ex m
    mrgᵉ : Ex m → Ex m
    scnᵉ : Tm (suc m) → Tm m → Ex m → Ex m

------------------------------------------------------------------
-- The chain measure, read off the text and nothing else
------------------------------------------------------------------

mutual
  linksT : ∀ {m} → Tm m → ℕ
  linksT (varᵗ _)  = 0
  linksT (natᵗ _)  = 0
  linksT (strmᵗ e) = linksE e

  linksE : ∀ {m} → Ex m → ℕ
  linksE (ofᵉ ts)     = linksL ts
  linksE (mapᵉ f e)   = linksT f ⊔ linksE e
  linksE (mrgᵉ e)     = suc (linksE e)      -- the link: a hop is charged here
  linksE (scnᵉ f z e) = linksT f ⊔ linksT z ⊔ linksE e

  linksL : ∀ {m} → List (Tm m) → ℕ
  linksL []       = 0
  linksL (t ∷ ts) = linksT t ⊔ linksL ts

------------------------------------------------------------------
-- Renaming, and that it leaves the measure alone
------------------------------------------------------------------

Ren : ℕ → ℕ → Set
Ren m k = Fin m → Fin k

liftR : ∀ {m k} → Ren m k → Ren (suc m) (suc k)
liftR ρ zero    = zero
liftR ρ (suc i) = suc (ρ i)

mutual
  renT : ∀ {m k} → Ren m k → Tm m → Tm k
  renT ρ (varᵗ i)  = varᵗ (ρ i)
  renT ρ (natᵗ x)  = natᵗ x
  renT ρ (strmᵗ e) = strmᵗ (renE ρ e)

  renE : ∀ {m k} → Ren m k → Ex m → Ex k
  renE ρ (ofᵉ ts)     = ofᵉ (renL ρ ts)
  renE ρ (mapᵉ f e)   = mapᵉ (renT (liftR ρ) f) (renE ρ e)
  renE ρ (mrgᵉ e)     = mrgᵉ (renE ρ e)
  renE ρ (scnᵉ f z e) = scnᵉ (renT (liftR ρ) f) (renT ρ z) (renE ρ e)

  renL : ∀ {m k} → Ren m k → List (Tm m) → List (Tm k)
  renL ρ []       = []
  renL ρ (t ∷ ts) = renT ρ t ∷ renL ρ ts

mutual
  ren-linksT : ∀ {m k} (ρ : Ren m k) (t : Tm m) → linksT (renT ρ t) ≡ linksT t
  ren-linksT ρ (varᵗ i)  = refl
  ren-linksT ρ (natᵗ x)  = refl
  ren-linksT ρ (strmᵗ e) = ren-linksE ρ e

  ren-linksE : ∀ {m k} (ρ : Ren m k) (e : Ex m) → linksE (renE ρ e) ≡ linksE e
  ren-linksE ρ (ofᵉ ts)     = ren-linksL ρ ts
  ren-linksE ρ (mapᵉ f e)   = cong₂ _⊔_ (ren-linksT (liftR ρ) f) (ren-linksE ρ e)
  ren-linksE ρ (mrgᵉ e)     = cong suc (ren-linksE ρ e)
  ren-linksE ρ (scnᵉ f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-linksT (liftR ρ) f) (ren-linksT ρ z)) (ren-linksE ρ e)

  ren-linksL : ∀ {m k} (ρ : Ren m k) (ts : List (Tm m)) → linksL (renL ρ ts) ≡ linksL ts
  ren-linksL ρ []       = refl
  ren-linksL ρ (t ∷ ts) = cong₂ _⊔_ (ren-linksT ρ t) (ren-linksL ρ ts)

------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------

Sub : ℕ → ℕ → Set
Sub m k = Fin m → Tm k

liftS : ∀ {m k} → Sub m k → Sub (suc m) (suc k)
liftS σ zero    = varᵗ zero
liftS σ (suc i) = renT suc (σ i)

mutual
  subT : ∀ {m k} → Sub m k → Tm m → Tm k
  subT σ (varᵗ i)  = σ i
  subT σ (natᵗ x)  = natᵗ x
  subT σ (strmᵗ e) = strmᵗ (subE σ e)

  subE : ∀ {m k} → Sub m k → Ex m → Ex k
  subE σ (ofᵉ ts)     = ofᵉ (subL σ ts)
  subE σ (mapᵉ f e)   = mapᵉ (subT (liftS σ) f) (subE σ e)
  subE σ (mrgᵉ e)     = mrgᵉ (subE σ e)
  subE σ (scnᵉ f z e) = scnᵉ (subT (liftS σ) f) (subT σ z) (subE σ e)

  subL : ∀ {m k} → Sub m k → List (Tm m) → List (Tm k)
  subL σ []       = []
  subL σ (t ∷ ts) = subT σ t ∷ subL σ ts

------------------------------------------------------------------
-- THE LEMMA.  Substituting into text of measure `a` from an environment
-- bounded by `b` lands at `a + b`.
------------------------------------------------------------------

Bounded : ∀ {m k} → Sub m k → ℕ → Set
Bounded σ b = ∀ i → linksT (σ i) ≤ b

lift-bounded : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b → Bounded (liftS σ) b
lift-bounded {σ = σ} bd zero    = z≤n
lift-bounded {σ = σ} bd (suc i) =
  ≤-trans (≤-reflexive (ren-linksT suc (σ i))) (bd i)

-- the shape every ⊔ clause needs: `+` over `⊔` on the right
⊔+ : ∀ {x y b} (a c : ℕ) → x ≤ a + b → y ≤ c + b → x ⊔ y ≤ (a ⊔ c) + b
⊔+ {b = b} a c p q =
  ≤-trans (⊔-mono-≤ p q) (≤-reflexive (sym (+-distribʳ-⊔ b a c)))

mutual
  sub-linksT : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b
             → (t : Tm m) → linksT (subT σ t) ≤ linksT t + b
  sub-linksT bd (varᵗ i)  = bd i
  sub-linksT bd (natᵗ x)  = z≤n
  sub-linksT bd (strmᵗ e) = sub-linksE bd e

  sub-linksE : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b
             → (e : Ex m) → linksE (subE σ e) ≤ linksE e + b
  sub-linksE bd (ofᵉ ts)   = sub-linksL bd ts
  sub-linksE bd (mapᵉ f e) =
    ⊔+ (linksT f) (linksE e) (sub-linksT (lift-bounded bd) f) (sub-linksE bd e)
  sub-linksE bd (mrgᵉ e)   = s≤s (sub-linksE bd e)
  sub-linksE bd (scnᵉ f z e) =
    ⊔+ (linksT f ⊔ linksT z) (linksE e)
       (⊔+ (linksT f) (linksT z) (sub-linksT (lift-bounded bd) f) (sub-linksT bd z))
       (sub-linksE bd e)

  sub-linksL : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b
             → (ts : List (Tm m)) → linksL (subL σ ts) ≤ linksL ts + b
  sub-linksL bd []       = z≤n
  sub-linksL bd (t ∷ ts) =
    ⊔+ (linksT t) (linksL ts) (sub-linksT bd t) (sub-linksL bd ts)

------------------------------------------------------------------
-- The two `Spike.Chain` postulates, restated as what is actually true
------------------------------------------------------------------

-- a single closed value substituted for the one free variable
one : Tm 0 → Sub 1 0
one v zero = v

one-bounded : (v : Tm 0) → Bounded (one v) (linksT v)
one-bounded v zero = ≤-refl

-- `mapOf`: a step function applied to a value.  NOT length-preserving --
-- a step may contain `strmT` and so mint links -- but bounded additively
-- by text it is read off, which is all the measure needs.
sub-step : (f : Tm 1) (v : Tm 0) → linksT (subT (one v) f) ≤ linksT f + linksT v
sub-step f v = sub-linksT (one-bounded v) f

-- `srcOf`: closed text needs no environment, so its measure is a static
-- read-off of the program and is not moved by subscribing to it.
nilS : Sub 0 0
nilS ()

nil-bounded : Bounded nilS 0
nil-bounded ()

src-static : (e : Ex 0) → linksE (subE nilS e) ≤ linksE e + 0
src-static e = sub-linksE nil-bounded e

-- and the growth `Spike.Chain`'s `chain` exhibits is exactly this bound
-- being TIGHT: the variable sits under a link, so it pays for one.
step-under-link : Tm 1
step-under-link = strmᵗ (mrgᵉ (ofᵉ (varᵗ zero ∷ [])))

grows-by-one : (v : Tm 0) → linksT (subT (one v) step-under-link) ≡ suc (linksT v)
grows-by-one v = cong suc (⊔-identityʳ (linksT v))

------------------------------------------------------------------
-- WHAT WOULD HAVE MADE THIS EASY, REFUTED.  A bound of `a ⊔ b` would
-- hold the chain FLAT across a fold, so the accumulator would need no
-- index at all -- and it is false, because the variable sits under a
-- link.  This is what forces `Spike.Chain`'s per-instant growth.
------------------------------------------------------------------

oneLink : Tm 0
oneLink = strmᵗ (mrgᵉ (ofᵉ []))

⊔-insufficient :
  ¬ (∀ (f : Tm 1) (v : Tm 0) → linksT (subT (one v) f) ≤ linksT f ⊔ linksT v)
⊔-insufficient h with h step-under-link oneLink
... | s≤s ()

-- and `Spike.Chain`'s `mapOf`, which claims a step mints no link
mapOf-mints : ¬ (∀ (f : Tm 1) (v : Tm 0) → linksT (subT (one v) f) ≡ linksT v)
mapOf-mints h with h step-under-link (natᵗ zero)
... | ()
