-- THE SCAN CLAUSE'S EXPONENT: THE STORE'S BOUND OR THE SOURCE'S OWN
-- DELIVERY COUNT.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- THE CHOICE.  A scan refolds once per value its source DELIVERS, and
-- the live measure charges a power of the run's STORE BOUND for those
-- refolds.  The two quantities are not the same and the gap is where
-- the tier's falsity lives: a cascade that delivers inside one
-- subscribe frame refolds without the store learning anything.  So the
-- candidate is the source's own delivery count, read off the term, and
-- the question this file answers is whether a term carries one.
--
-- IT DOES, AND THE READING IS NOT AFFINE, WHICH IS THE FINDING.  The
-- live measure's slope is justified by being affine in a plugged
-- value's depth — one coefficient per clause, and a clause's
-- coefficient cannot move under substitution.  A delivery count is not
-- of that kind: a flattener's count is the PRODUCT of how many inners
-- arrive and how much each delivers, so its slope obeys the product
-- rule and needs both factors' slopes to state.  That is why three
-- readings appear below where the live measure has two.
--
-- AND THE RECURRENCE HAS TO BE SOLVED RATHER THAN BOUNDED, which is the
-- half that decides whether any of this can be computed at all.  A fold
-- whose step re-wraps its accumulator ONCE deepens by a constant per
-- refold, so its depth is LINEAR in the refold count; a bound of the
-- live clause's shape charges a power of at least two for the same
-- thing.  That distinction costs nothing while the exponent is a store
-- bound in the single digits and is fatal once it is a delivery count,
-- which is itself exponential in the source — a power of two raised to
-- a count in the hundreds is not a number any checker will produce.
-- `geom` is the solved sum, and it is what keeps the rows below
-- numerals.
--
-- THE BOUNDARY.  Three shapes are read coarsely and no row here reaches
-- them: a slot, whose count is taken straight off the telescope; a
-- flattener at an observable-typed emission, where the values handed
-- out are the inners' and this reading charges the inner's own count;
-- and every binding term other than a template.  The rows cover one
-- fold family with a merge as its only flattener, at four source
-- lengths.
--
-- FORK: dry-operator
module Probed.Delivery-Count where

open import Data.Bool using (if_then_else_; true)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _⊔′_; _≡ᵇ_; _≤ᵇ_)
open import Data.Fin using (Fin)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Exp using (Ctx; Closed; Exp; Tm;
                          input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                          mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                          μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                          inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ; natᵗ)
open import Rx.Hop-Depth using (varIx)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Operator-Root using (Γ₀; ins₀; η₀; SB;
                                        spread; liveSeed; burstOf; carried;
                                        e1; e2; e3; e4)

----------------------------------------------------------------------
-- THE SOLVED SUM.  `geom p R` is the number of terms a fold's constant
-- contributes after `R` refolds, each scaled by the step's slope once
-- per later refold.  Written as a recursion on the count rather than as
-- a quotient because the quotient's denominator vanishes at a slope of
-- one — the case that is both the common one and the one whose answer
-- has to stay small.
----------------------------------------------------------------------

geom : ℕ → ℕ → ℕ
geom p zero    = 1
geom p (suc R) = 1 + p * geom p R

----------------------------------------------------------------------
-- THE THREE READINGS AND THEIR SLOPES.
--
--   `dlvᵉ`  how many values the term delivers at the top of its own
--           subscribe burst
--   `edlᵉ`  how many values ONE value the term delivers can itself
--           deliver -- the quantity a flattener spends and the one a
--           term reading is usually blind to
--   `pdᵉ`   the slope of `dlvᵉ`, and `qdᵉ` the slope of `edlᵉ`, both in
--           the value plugged at the variable standing at index k
--
-- A template's own reading is `edlᵗ`: a term of observable type stands
-- for a stream, so its count is that stream's `dlvᵉ`, and the plug's
-- count arrives through the leaf clause of `pdᵗ` exactly as a depth
-- arrives through the live measure's.
----------------------------------------------------------------------

mutual
  dlvᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) →
         Exp Γ Δᵍ Δ Θ t → ℕ
  dlvᵉ ν (input i)          = ν i
  dlvᵉ ν (ofᵉ ts)           = length ts
  dlvᵉ ν emptyᵉ             = 0
  dlvᵉ ν (mapᵉ f e)         = dlvᵉ ν e
  dlvᵉ ν (takeᵉ c e)        = dlvᵉ ν e
  dlvᵉ ν (scanᵉ f z e)      = dlvᵉ ν e
  -- THE PRODUCT, and the clause the slope's shape is forced by: each
  -- inner that arrives is subscribed, and each delivers its own
  dlvᵉ ν (mergeAllᵉ lim e)  = dlvᵉ ν e * edlᵉ ν e
  dlvᵉ ν (switchAllᵉ e)     = dlvᵉ ν e * edlᵉ ν e
  dlvᵉ ν (exhaustAllᵉ e)    = dlvᵉ ν e * edlᵉ ν e
  dlvᵉ ν (μᵉ e)             = dlvᵉ ν e
  dlvᵉ ν (varᵉ x)           = 0
  -- nothing under a defer is subscribed within the instant, which is
  -- the one clause that makes the reading survive an unfold
  dlvᵉ ν (deferᵉ e)         = 0

  edlᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) →
         Exp Γ Δᵍ Δ Θ t → ℕ
  edlᵉ ν (input i)          = ν i
  edlᵉ ν (ofᵉ ts)           = edlᵗˢ ν ts
  edlᵉ ν emptyᵉ             = 0
  edlᵉ ν (mapᵉ f e)         = edlᵗ ν f + (pdᵗ ν 0 f ⊔′ 1) * edlᵉ ν e
  edlᵉ ν (takeᵉ c e)        = edlᵉ ν e
  -- THE SOLVED FOLD.  The accumulator starts at the seed's own count
  -- and each refold scales it by the step's slope and adds the step's
  -- constant; `dlvᵉ` of the source is how many refolds there are
  edlᵉ ν (scanᵉ f z e)      =
    edlᵗ ν z * (pdᵗ ν 0 f ^ dlvᵉ ν e)
      + edlᵗ ν f * geom (pdᵗ ν 0 f) (dlvᵉ ν e)
  edlᵉ ν (mergeAllᵉ lim e)  = edlᵉ ν e
  edlᵉ ν (switchAllᵉ e)     = edlᵉ ν e
  edlᵉ ν (exhaustAllᵉ e)    = edlᵉ ν e
  edlᵉ ν (μᵉ e)             = edlᵉ ν e
  edlᵉ ν (varᵉ x)           = 0
  edlᵉ ν (deferᵉ e)         = 0

  edlᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) →
         Tm Γ Δᵍ Δ Θ t → ℕ
  edlᵗ ν (varᵗ x)           = 0
  edlᵗ ν unit̂               = 0
  edlᵗ ν (bool̂ _)           = 0
  edlᵗ ν (nat̂ _)            = 0
  edlᵗ ν (pairᵗ a b)        = edlᵗ ν a ⊔′ edlᵗ ν b
  edlᵗ ν (fstᵗ p)           = edlᵗ ν p
  edlᵗ ν (sndᵗ p)           = edlᵗ ν p
  edlᵗ ν (inlᵗ a)           = edlᵗ ν a
  edlᵗ ν (inrᵗ a)           = edlᵗ ν a
  edlᵗ ν (caseᵗ s l r)      =
    (edlᵗ ν l ⊔′ edlᵗ ν r)
      + (pdᵗ ν 0 l ⊔′ pdᵗ ν 0 r ⊔′ 1) * edlᵗ ν s
  edlᵗ ν (ifᵗ c a b)        = edlᵗ ν a ⊔′ edlᵗ ν b
  edlᵗ ν (primᵗ _ a)        = 0
  -- a term of observable type IS a stream, so what it hands out is that
  -- stream's own top count
  edlᵗ ν (strmᵗ e)          = dlvᵉ ν e

  edlᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) →
          List (Tm Γ Δᵍ Δ Θ t) → ℕ
  edlᵗˢ ν []                = 0
  edlᵗˢ ν (y ∷ ys)          = edlᵗ ν y ⊔′ edlᵗˢ ν ys

  pdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
        Exp Γ Δᵍ Δ Θ t → ℕ
  pdᵉ ν k (input i)         = 0
  -- a literal source's count is its length, which no plug can move
  pdᵉ ν k (ofᵉ ts)          = 0
  pdᵉ ν k emptyᵉ            = 0
  pdᵉ ν k (mapᵉ f e)        = pdᵉ ν k e
  pdᵉ ν k (takeᵉ c e)       = pdᵉ ν k e
  pdᵉ ν k (scanᵉ f z e)     = pdᵉ ν k e
  -- THE PRODUCT RULE, and the reason this reading needs two slopes
  pdᵉ ν k (mergeAllᵉ lim e) =
    pdᵉ ν k e * edlᵉ ν e + dlvᵉ ν e * qdᵉ ν k e
  pdᵉ ν k (switchAllᵉ e)    =
    pdᵉ ν k e * edlᵉ ν e + dlvᵉ ν e * qdᵉ ν k e
  pdᵉ ν k (exhaustAllᵉ e)   =
    pdᵉ ν k e * edlᵉ ν e + dlvᵉ ν e * qdᵉ ν k e
  pdᵉ ν k (μᵉ e)            = pdᵉ ν k e
  pdᵉ ν k (varᵉ x)          = 0
  pdᵉ ν k (deferᵉ e)        = 0

  qdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
        Exp Γ Δᵍ Δ Θ t → ℕ
  qdᵉ ν k (input i)         = 0
  qdᵉ ν k (ofᵉ ts)          = pdᵗˢ ν k ts
  qdᵉ ν k emptyᵉ            = 0
  qdᵉ ν k (mapᵉ f e)        = pdᵗ ν (suc k) f + (pdᵗ ν 0 f ⊔′ 1) * qdᵉ ν k e
  qdᵉ ν k (takeᵉ c e)       = qdᵉ ν k e
  qdᵉ ν k (scanᵉ f z e)     =
    pdᵗ ν k z * (pdᵗ ν 0 f ^ dlvᵉ ν e)
      + (pdᵗ ν (suc k) f + qdᵉ ν k e) * geom (pdᵗ ν 0 f) (dlvᵉ ν e)
  qdᵉ ν k (mergeAllᵉ lim e) = qdᵉ ν k e
  qdᵉ ν k (switchAllᵉ e)    = qdᵉ ν k e
  qdᵉ ν k (exhaustAllᵉ e)   = qdᵉ ν k e
  qdᵉ ν k (μᵉ e)            = qdᵉ ν k e
  qdᵉ ν k (varᵉ x)          = 0
  qdᵉ ν k (deferᵉ e)        = 0

  pdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
        Tm Γ Δᵍ Δ Θ t → ℕ
  -- THE LEAF: the plug's own count arrives here and nowhere else
  pdᵗ ν k (varᵗ x)          = if varIx x ≡ᵇ k then 1 else 0
  pdᵗ ν k unit̂              = 0
  pdᵗ ν k (bool̂ _)          = 0
  pdᵗ ν k (nat̂ _)           = 0
  pdᵗ ν k (pairᵗ a b)       = pdᵗ ν k a ⊔′ pdᵗ ν k b
  pdᵗ ν k (fstᵗ p)          = pdᵗ ν k p
  pdᵗ ν k (sndᵗ p)          = pdᵗ ν k p
  pdᵗ ν k (inlᵗ a)          = pdᵗ ν k a
  pdᵗ ν k (inrᵗ a)          = pdᵗ ν k a
  pdᵗ ν k (caseᵗ s l r)     =
    (pdᵗ ν (suc k) l ⊔′ pdᵗ ν (suc k) r)
      + (pdᵗ ν 0 l ⊔′ pdᵗ ν 0 r ⊔′ 1) * pdᵗ ν k s
  pdᵗ ν k (ifᵗ c a b)       = pdᵗ ν k a ⊔′ pdᵗ ν k b
  pdᵗ ν k (primᵗ _ a)       = 0
  pdᵗ ν k (strmᵗ e)         = pdᵉ ν k e

  pdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ν : Fin n → ℕ) (k : ℕ) →
         List (Tm Γ Δᵍ Δ Θ t) → ℕ
  pdᵗˢ ν k []               = 0
  pdᵗˢ ν k (y ∷ ys)         = pdᵗ ν k y ⊔′ pdᵗˢ ν k ys

ν₀ : Fin 0 → ℕ
ν₀ = λ ()

----------------------------------------------------------------------
-- THE SEPARATION.  Two candidate exponents for one scan clause, taken
-- on one signature so that Agda decides whether they differ: the domain
-- carries the run's store bound and the scan's source, and each
-- candidate reads the half it reads.  That the store candidate ignores
-- its second component is not a strawman — it is exactly the finding,
-- since the refolds it is charged for are a property of the source.
----------------------------------------------------------------------

----------------------------------------------------------------------
-- THE SCAN WHOSE SOURCE IS THE QUESTION.  This is the inner half of the
-- imported family, named here because the exponent is a reading of a
-- SUBTERM and the separation has to be taken at one.  The fold spreads
-- three ways per source value and the flattener subscribes every layer,
-- so what reaches the outer fold is a count that triples with the
-- literals while the store bound the run is taken at stays six.
----------------------------------------------------------------------

src₄ : Closed Γ₀ natᵗ
src₄ = mergeAllᵉ nothing
  (scanᵉ spread liveSeed
    (ofᵉ (nat̂ 0 ∷ nat̂ 1 ∷ nat̂ 2 ∷ nat̂ 3 ∷ [])))

Point : Set
Point = ℕ × Closed Γ₀ natᵗ

expStore expSource : Point → ℕ
expStore (V , _)  = V
expSource (_ , b) = dlvᵉ ν₀ b

-- LOAD-BEARING, both: a store candidate that moved with the source
-- would say the live clause already sees the refolds, and a source
-- candidate reading under the bound would put the separation on the
-- wrong side of the crossing.  Fifty-four refolds per unit of allowance
-- is the gap the tier's falsity is made of.
_ : expStore (SB , src₄) ≡ 6                           -- LOAD-BEARING
_ = refl

_ : expSource (SB , src₄) ≡ 324                        -- LOAD-BEARING
_ = refl

exponent-fork : Separates expStore expSource
exponent-fork = separates-at (SB , src₄) (λ ())

----------------------------------------------------------------------
-- WHAT THE CANDIDATE BUYS, at the family the live reading is flat over.
-- The imported rows have the entry reading the SAME 532899 at every
-- source length while the depth handed out triples, so the two meet at
-- twelve literals.  The candidate moves with the source, and each row
-- is LOAD-BEARING in both directions: a count that stalled would leave
-- it as blind as the reading it replaces, and one that outran the
-- depths by a widening factor would say the product clause is charging
-- for inners that never arrive.
--
-- THE FIRST ROW IS TIGHT, three against three, which is what says the
-- domination is earned rather than bought with slack — and the margin
-- grows with the source, so the pair does not cross back.
----------------------------------------------------------------------

_ : dlvᵉ ν₀ e1 ≡ 3                                     -- LOAD-BEARING
_ = refl

_ : dlvᵉ ν₀ e2 ≡ 18                                    -- LOAD-BEARING
_ = refl

_ : dlvᵉ ν₀ e3 ≡ 81                                    -- LOAD-BEARING
_ = refl

_ : dlvᵉ ν₀ e4 ≡ 324                                   -- LOAD-BEARING
_ = refl

_ : (carried SB η₀ (burstOf e1 ins₀) ≤ᵇ dlvᵉ ν₀ e1) ≡ true   -- LOAD-BEARING
_ = refl

_ : (carried SB η₀ (burstOf e2 ins₀) ≤ᵇ dlvᵉ ν₀ e2) ≡ true   -- LOAD-BEARING
_ = refl

_ : (carried SB η₀ (burstOf e3 ins₀) ≤ᵇ dlvᵉ ν₀ e3) ≡ true   -- LOAD-BEARING
_ = refl

_ : (carried SB η₀ (burstOf e4 ins₀) ≤ᵇ dlvᵉ ν₀ e4) ≡ true   -- LOAD-BEARING
_ = refl
