-- THE LAST ASSERTION, over the WHOLE OPERATOR SET.  `Spike.Text` proved the
-- chain measure additive under substitution on a four-constructor fragment,
-- which left two gaps: the other operators, and -- the sharp one -- `mue`
-- and `defere`.  Unfolding a `mue` substitutes the WHOLE loop into its own
-- body, so an additive bound would let a single unfolding DOUBLE the
-- measure and an unbounded number of them run it away, with no instant
-- boundary crossed to pay for it.  That would sink the mechanism.
--
-- IT DOES NOT, AND `defer-blind` IS WHY.  A `defere` subtree is not
-- subscribed within the instant, so it is a LEAF for a within-instant
-- measure and contributes zero whatever is inside it; a usable loop
-- variable exists only under a defer, so unfolding only ever rewrites
-- where the measure is not looking.  What is proved here is stronger than
-- that and cheaper to state: replacing EVERY defer body outright, with
-- anything at all, leaves the measure fixed on the nose.  Unfolding is one
-- instance of that shape, so no version of it can move the measure.
--
-- This is the same treatment `syncSizeE` already gives a defer, and for the
-- same reason -- that measure is preserved by unfolding on exactly this
-- argument, which makes it the worked precedent rather than a fresh guess.
--
-- WHAT IS TRANSCRIBED AND WHAT IS COLLAPSED.  The expression set is
-- COMPLETE -- all twelve of `Rx.Exp`'s constructors are here, so no
-- operator is exempt from either theorem.  Terms are collapsed to the three
-- shapes the measure can tell apart: a variable, a leaf carrying no stream,
-- and a `strmT` embedding.  The omitted term constructors are pairing,
-- projection, injection, `case`, `if` and the primitives, every one of which
-- is a max over its own subterms plus at most a binder -- which is `mapE`'s
-- shape and `scanE`'s, both discharged below.
--
-- Loop variables are untyped here.  The guarded/usable context split is what
-- makes "a usable variable is always under a defer" true, and `defer-blind`
-- does not need it: it holds for rewrites under a defer whether or not that
-- is where the variables are, which is why it is the statement worth having.
--
-- NOT COVERED: that the evaluator's emissions are substitution instances of
-- its text.  That is no longer an assertion -- `evalWith (strmT e) env`
-- IS `closeUnderFn e env` in `Rx.Exp`, a substitution -- so what is left is
-- transcription fidelity between this fragment and that module, which is
-- read rather than proved and goes away when the measure lands in `src`.
module Spike.Defer where

open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-reflexive; ⊔-mono-≤; +-distribʳ-⊔)
open import Data.Fin using (Fin; zero; suc)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (¬_)

------------------------------------------------------------------
-- The operator set, as `Rx.Exp` has it
------------------------------------------------------------------

mutual
  data Tm (m : ℕ) : Set where
    varᵗ  : Fin m → Tm m
    natᵗ  : ℕ → Tm m
    strmᵗ : Ex m → Tm m

  data Ex (m : ℕ) : Set where
    inputᵉ : ℕ → Ex m
    ofᵉ    : List (Tm m) → Ex m
    emptyᵉ : Ex m
    mapᵉ   : Tm (suc m) → Ex m → Ex m
    takeᵉ  : Tm m → Ex m → Ex m
    scanᵉ  : Tm (suc m) → Tm m → Ex m → Ex m
    mrgᵉ   : Ex m → Ex m              -- mergeAll
    swtᵉ   : Ex m → Ex m              -- switchAll
    exhᵉ   : Ex m → Ex m              -- exhaustAll
    μᵉ     : Ex m → Ex m
    varᵉ   : ℕ → Ex m
    deferᵉ : Ex m → Ex m

------------------------------------------------------------------
-- The chain measure.  A flattening operator charges a link; a defer
-- charges nothing and does not look inside.
------------------------------------------------------------------

mutual
  linksT : ∀ {m} → Tm m → ℕ
  linksT (varᵗ _)  = 0
  linksT (natᵗ _)  = 0
  linksT (strmᵗ e) = linksE e

  linksE : ∀ {m} → Ex m → ℕ
  linksE (inputᵉ _)    = 0
  linksE (ofᵉ ts)      = linksL ts
  linksE emptyᵉ        = 0
  linksE (mapᵉ f e)    = linksT f ⊔ linksE e
  linksE (takeᵉ c e)   = linksT c ⊔ linksE e
  linksE (scanᵉ f z e) = linksT f ⊔ linksT z ⊔ linksE e
  linksE (mrgᵉ e)      = suc (linksE e)
  linksE (swtᵉ e)      = suc (linksE e)
  linksE (exhᵉ e)      = suc (linksE e)
  linksE (μᵉ e)        = linksE e
  linksE (varᵉ _)      = 0
  linksE (deferᵉ _)    = 0            -- the next instant: not this one's cost

  linksL : ∀ {m} → List (Tm m) → ℕ
  linksL []       = 0
  linksL (t ∷ ts) = linksT t ⊔ linksL ts

------------------------------------------------------------------
-- Renaming and substitution of VALUE variables
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
  renE ρ (inputᵉ i)    = inputᵉ i
  renE ρ (ofᵉ ts)      = ofᵉ (renL ρ ts)
  renE ρ emptyᵉ        = emptyᵉ
  renE ρ (mapᵉ f e)    = mapᵉ (renT (liftR ρ) f) (renE ρ e)
  renE ρ (takeᵉ c e)   = takeᵉ (renT ρ c) (renE ρ e)
  renE ρ (scanᵉ f z e) = scanᵉ (renT (liftR ρ) f) (renT ρ z) (renE ρ e)
  renE ρ (mrgᵉ e)      = mrgᵉ (renE ρ e)
  renE ρ (swtᵉ e)      = swtᵉ (renE ρ e)
  renE ρ (exhᵉ e)      = exhᵉ (renE ρ e)
  renE ρ (μᵉ e)        = μᵉ (renE ρ e)
  renE ρ (varᵉ i)      = varᵉ i
  renE ρ (deferᵉ e)    = deferᵉ (renE ρ e)

  renL : ∀ {m k} → Ren m k → List (Tm m) → List (Tm k)
  renL ρ []       = []
  renL ρ (t ∷ ts) = renT ρ t ∷ renL ρ ts

mutual
  ren-linksT : ∀ {m k} (ρ : Ren m k) (t : Tm m) → linksT (renT ρ t) ≡ linksT t
  ren-linksT ρ (varᵗ i)  = refl
  ren-linksT ρ (natᵗ x)  = refl
  ren-linksT ρ (strmᵗ e) = ren-linksE ρ e

  ren-linksE : ∀ {m k} (ρ : Ren m k) (e : Ex m) → linksE (renE ρ e) ≡ linksE e
  ren-linksE ρ (inputᵉ i)    = refl
  ren-linksE ρ (ofᵉ ts)      = ren-linksL ρ ts
  ren-linksE ρ emptyᵉ        = refl
  ren-linksE ρ (mapᵉ f e)    = cong₂ _⊔_ (ren-linksT (liftR ρ) f) (ren-linksE ρ e)
  ren-linksE ρ (takeᵉ c e)   = cong₂ _⊔_ (ren-linksT ρ c) (ren-linksE ρ e)
  ren-linksE ρ (scanᵉ f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (ren-linksT (liftR ρ) f) (ren-linksT ρ z)) (ren-linksE ρ e)
  ren-linksE ρ (mrgᵉ e)      = cong suc (ren-linksE ρ e)
  ren-linksE ρ (swtᵉ e)      = cong suc (ren-linksE ρ e)
  ren-linksE ρ (exhᵉ e)      = cong suc (ren-linksE ρ e)
  ren-linksE ρ (μᵉ e)        = ren-linksE ρ e
  ren-linksE ρ (varᵉ i)      = refl
  ren-linksE ρ (deferᵉ e)    = refl

  ren-linksL : ∀ {m k} (ρ : Ren m k) (ts : List (Tm m)) → linksL (renL ρ ts) ≡ linksL ts
  ren-linksL ρ []       = refl
  ren-linksL ρ (t ∷ ts) = cong₂ _⊔_ (ren-linksT ρ t) (ren-linksL ρ ts)

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
  subE σ (inputᵉ i)    = inputᵉ i
  subE σ (ofᵉ ts)      = ofᵉ (subL σ ts)
  subE σ emptyᵉ        = emptyᵉ
  subE σ (mapᵉ f e)    = mapᵉ (subT (liftS σ) f) (subE σ e)
  subE σ (takeᵉ c e)   = takeᵉ (subT σ c) (subE σ e)
  subE σ (scanᵉ f z e) = scanᵉ (subT (liftS σ) f) (subT σ z) (subE σ e)
  subE σ (mrgᵉ e)      = mrgᵉ (subE σ e)
  subE σ (swtᵉ e)      = swtᵉ (subE σ e)
  subE σ (exhᵉ e)      = exhᵉ (subE σ e)
  subE σ (μᵉ e)        = μᵉ (subE σ e)
  subE σ (varᵉ i)      = varᵉ i
  subE σ (deferᵉ e)    = deferᵉ (subE σ e)

  subL : ∀ {m k} → Sub m k → List (Tm m) → List (Tm k)
  subL σ []       = []
  subL σ (t ∷ ts) = subT σ t ∷ subL σ ts

------------------------------------------------------------------
-- THEOREM 1.  Value substitution is additive, on the whole set.
------------------------------------------------------------------

Bounded : ∀ {m k} → Sub m k → ℕ → Set
Bounded σ b = ∀ i → linksT (σ i) ≤ b

lift-bounded : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b → Bounded (liftS σ) b
lift-bounded          bd zero    = z≤n
lift-bounded {σ = σ}  bd (suc i) =
  ≤-trans (≤-reflexive (ren-linksT suc (σ i))) (bd i)

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
  sub-linksE bd (inputᵉ i)  = z≤n
  sub-linksE bd (ofᵉ ts)    = sub-linksL bd ts
  sub-linksE bd emptyᵉ      = z≤n
  sub-linksE bd (mapᵉ f e)  =
    ⊔+ (linksT f) (linksE e) (sub-linksT (lift-bounded bd) f) (sub-linksE bd e)
  sub-linksE bd (takeᵉ c e) =
    ⊔+ (linksT c) (linksE e) (sub-linksT bd c) (sub-linksE bd e)
  sub-linksE bd (scanᵉ f z e) =
    ⊔+ (linksT f ⊔ linksT z) (linksE e)
       (⊔+ (linksT f) (linksT z) (sub-linksT (lift-bounded bd) f) (sub-linksT bd z))
       (sub-linksE bd e)
  sub-linksE bd (mrgᵉ e)    = s≤s (sub-linksE bd e)
  sub-linksE bd (swtᵉ e)    = s≤s (sub-linksE bd e)
  sub-linksE bd (exhᵉ e)    = s≤s (sub-linksE bd e)
  sub-linksE bd (μᵉ e)      = sub-linksE bd e
  sub-linksE bd (varᵉ i)    = z≤n
  sub-linksE bd (deferᵉ e)  = z≤n

  sub-linksL : ∀ {m k} {σ : Sub m k} {b} → Bounded σ b
             → (ts : List (Tm m)) → linksL (subL σ ts) ≤ linksL ts + b
  sub-linksL bd []       = z≤n
  sub-linksL bd (t ∷ ts) =
    ⊔+ (linksT t) (linksL ts) (sub-linksT bd t) (sub-linksL bd ts)

------------------------------------------------------------------
-- THEOREM 2.  Nothing under a defer moves the measure -- so no
-- unfolding of a loop can, whatever it substitutes or how often.
------------------------------------------------------------------

-- the most violent rewrite there is: every defer body replaced outright
mutual
  gutT : ∀ {m} → Ex m → Tm m → Tm m
  gutT r (varᵗ i)  = varᵗ i
  gutT r (natᵗ x)  = natᵗ x
  gutT r (strmᵗ e) = strmᵗ (gutE r e)

  gutE : ∀ {m} → Ex m → Ex m → Ex m
  gutE r (inputᵉ i)    = inputᵉ i
  gutE r (ofᵉ ts)      = ofᵉ (gutL r ts)
  gutE r emptyᵉ        = emptyᵉ
  gutE r (mapᵉ f e)    = mapᵉ (gutT (renE suc r) f) (gutE r e)
  gutE r (takeᵉ c e)   = takeᵉ (gutT r c) (gutE r e)
  gutE r (scanᵉ f z e) = scanᵉ (gutT (renE suc r) f) (gutT r z) (gutE r e)
  gutE r (mrgᵉ e)      = mrgᵉ (gutE r e)
  gutE r (swtᵉ e)      = swtᵉ (gutE r e)
  gutE r (exhᵉ e)      = exhᵉ (gutE r e)
  gutE r (μᵉ e)        = μᵉ (gutE r e)
  gutE r (varᵉ i)      = varᵉ i
  gutE r (deferᵉ _)    = deferᵉ r        -- the body thrown away entirely

  gutL : ∀ {m} → Ex m → List (Tm m) → List (Tm m)
  gutL r []       = []
  gutL r (t ∷ ts) = gutT r t ∷ gutL r ts

mutual
  defer-blindT : ∀ {m} (r : Ex m) (t : Tm m) → linksT (gutT r t) ≡ linksT t
  defer-blindT r (varᵗ i)  = refl
  defer-blindT r (natᵗ x)  = refl
  defer-blindT r (strmᵗ e) = defer-blind r e

  defer-blind : ∀ {m} (r : Ex m) (e : Ex m) → linksE (gutE r e) ≡ linksE e
  defer-blind r (inputᵉ i)    = refl
  defer-blind r (ofᵉ ts)      = defer-blindL r ts
  defer-blind r emptyᵉ        = refl
  defer-blind r (mapᵉ f e)    =
    cong₂ _⊔_ (defer-blindT (renE suc r) f) (defer-blind r e)
  defer-blind r (takeᵉ c e)   = cong₂ _⊔_ (defer-blindT r c) (defer-blind r e)
  defer-blind r (scanᵉ f z e) =
    cong₂ _⊔_ (cong₂ _⊔_ (defer-blindT (renE suc r) f) (defer-blindT r z))
              (defer-blind r e)
  defer-blind r (mrgᵉ e)      = cong suc (defer-blind r e)
  defer-blind r (swtᵉ e)      = cong suc (defer-blind r e)
  defer-blind r (exhᵉ e)      = cong suc (defer-blind r e)
  defer-blind r (μᵉ e)        = defer-blind r e
  defer-blind r (varᵉ i)      = refl
  defer-blind r (deferᵉ e)    = refl

  defer-blindL : ∀ {m} (r : Ex m) (ts : List (Tm m)) → linksL (gutL r ts) ≡ linksL ts
  defer-blindL r []       = refl
  defer-blindL r (t ∷ ts) = cong₂ _⊔_ (defer-blindT r t) (defer-blindL r ts)

------------------------------------------------------------------
-- AND IT COULD HAVE FAILED.  Charging a defer the way a flattening
-- operator is charged breaks the blindness at once, which is what
-- makes the zero above load-bearing rather than a convention.
------------------------------------------------------------------

linksE′ : ∀ {m} → Ex m → ℕ
linksE′ (deferᵉ e) = suc (linksE e)
linksE′ e          = linksE e

charged-defer-sees-inside :
  ¬ (∀ {m} (r e : Ex m) → linksE′ (gutE r e) ≡ linksE′ e)
charged-defer-sees-inside h with h {0} (mrgᵉ emptyᵉ) (deferᵉ emptyᵉ)
... | ()
