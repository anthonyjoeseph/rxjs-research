-- A DOOR CAN PRICE A VARIABLE AT WHAT WILL BE PLUGGED INTO IT, AND THE
-- PRICE IS AN ENVIRONMENT RATHER THAN A SLOPE.
--
-- EVIDENCE, not a claim: `src` cannot import this file and nothing in
-- the proof may rest on it.  Checked by `make probed`, claimed by
-- `Probed.Main`.
--
-- WHAT THE TWO DEAD READINGS SHARE.  Both charge a fold a CLOSED FORM —
-- a power of one number times a sum of subterm readings — and both
-- price the accumulator at what the term says, which is a variable, and
-- a variable reads zero.  The repair the siblings' rows point at is a
-- slope: a coefficient saying how the reading scales in the plug.  That
-- is not what is needed, and the finding is that it is WEAKER than what
-- is available.  A slope is what you carry when the plug's reading is
-- unavailable; here it is available, because the fold KNOWS its own
-- accumulator — it starts at the seed and each refold is the step read
-- against the previous one.  So the clause iterates rather than
-- exponentiates, and the variable is read off an ENVIRONMENT the
-- iteration maintains.
--
-- WHAT THAT COSTS AND WHAT IT BUYS.  It costs the closed form: the fold
-- clause is a recursion on the refold count, so the reading is no longer
-- a constant-size arithmetic expression in its subterms' readings.  It
-- buys exactness, and exactness removes machinery rather than adding
-- it — the multiplicity family and the two delivery slopes exist only to
-- price a variable, and an environment prices it directly, so nothing
-- here reads a slope at all.  Three readings survive per expression:
-- what it delivers, what one delivered value itself delivers, and how
-- deep it is.
--
-- WHAT THE ROWS SAY, AND THEY SAY MORE THAN THE GUARD HOLDING.  Every
-- crossing the two dead readings produce is gone, at all three families
-- and at both bounds — and every row is TIGHT, reading exactly the depth
-- its own run hands out.  The two term readings were flat or geometric
-- against a linear rate; this one IS the rate.  Tightness is the part
-- worth having: a reading that merely dominated would leave open whether
-- it dominates by a margin that grows, which is what makes a bound
-- unusable as a descent measure however true it is.
--
-- THE BOUNDARY.  Three fold families, a merge as the only flattener, no
-- input and no recursion — so the slot clause and the defer cut are
-- carried over from the live reading untested here.  Nothing reaches a
-- switch or an exhaust root, a template that drops its argument, or a
-- case binder.  And nothing here measures what the iteration COSTS: the
-- refold counts these families reach are single digits, and a delivery
-- count is exponential in its source, so whether the clause is
-- computable at the counts `Probed.Delivery-Count` reaches is open and
-- is not a question these rows touch.
--
-- FORK: dry-operator
module Probed.Plug-Priced where

open import Data.Bool using (true)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; length)
open import Data.Nat using (ℕ; zero; suc; _*_; _⊔_; _⊔′_; _≤ᵇ_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim using (InstEvent; value; InstEmit)
open import Rx.Exp using (Ctx; Closed; Exp; Tm; Fn; obs; natᵗ;
                         input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ;
                         mergeAllᵉ; switchAllᵉ; exhaustAllᵉ;
                         μᵉ; varᵉ; deferᵉ;
                         varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ;
                         inlᵗ; inrᵗ; caseᵗ; ifᵗ; primᵗ; strmᵗ)
open import Rx.Hop-Depth using (varIx)
open import Rx.Evaluator using (Stream)

open import Probed.Apparatus using (Separates; separates-at)
open import Probed.Step-Fold using (narrow₁; narrow₂; narrow₃; narrow₄;
                                    wide₁; wide₂)
open import Probed.Swapped-Exponent using (hopD′ᵉ; ν₀; η₀)
open import Refuted.Sync-Count using (Γ₀; ins₀)
open import Refuted.Root-Refold using (burstAt; inner₁; inner₂; inner₃; inner₄)

----------------------------------------------------------------------
-- THE PLUG'S PRICE.  A term of observable type stands for a stream, so
-- what a door has to know about one is how much it delivers and how deep
-- it is — the pair below, and nothing else.  An expression carries a
-- third: how much it delivers at the TOP of its own burst, which is the
-- fold's refold count and is not the same as what one of its values
-- delivers.
----------------------------------------------------------------------

Rd : Set
Rd = ℕ × ℕ

Rd₃ : Set
Rd₃ = ℕ × ℕ × ℕ

_⊔ᴿ_ : Rd → Rd → Rd
(a , b) ⊔ᴿ (c , d) = a ⊔′ c , b ⊔′ d

Env : Set
Env = ℕ → Rd

-- the closed environment: a Θ-variable with nothing plugged into it
-- reads what the dead measures read at every variable
ε : Env
ε _ = 0 , 0

_▸_ : Env → Rd → Env
(ρ ▸ p) zero    = p
(ρ ▸ p) (suc k) = ρ k

-- the shape changes, each named so no clause below needs a `with` and
-- no reading is computed twice
slotOf : Rd → Rd₃
slotOf (c , h) = c , c , h

litOf : ℕ → Rd → Rd₃
litOf k (ev , h) = k , ev , h

-- THE HOP EDGE: entering an inner costs exactly one, and what the frame
-- then delivers is what one arriving inner delivers
flatten : Rd₃ → Rd₃
flatten (d , ev , h) = d * ev , ev , suc h

topOf : Rd₃ → Rd
topOf (d , _ , h) = d , h

----------------------------------------------------------------------
-- THE READING.  Every clause but two is the live one with its
-- coefficient deleted: the coefficient existed to scale a plug's reading
-- along the paths to its occurrences, and an occurrence now reads the
-- plug itself.  The two that are not are the binders, `mapᵉ` and
-- `scanᵉ`, which push onto the environment instead of multiplying.
----------------------------------------------------------------------

mutual
  rdᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd) (ρ : Env) →
        Exp Γ Δᵍ Δ Θ t → Rd₃
  rdᵉ ψ ρ (input i)         = slotOf (ψ i)
  rdᵉ ψ ρ (ofᵉ ts)          = litOf (length ts) (rdᵗˢ ψ ρ ts)
  rdᵉ ψ ρ emptyᵉ            = 0 , 0 , 0
  rdᵉ ψ ρ (mapᵉ f e)        = mapStep ψ ρ (rdᵉ ψ ρ e) f
  rdᵉ ψ ρ (takeᵉ c e)       = rdᵉ ψ ρ e
  rdᵉ ψ ρ (scanᵉ f z e)     = scanStep ψ ρ (rdᵉ ψ ρ e) z f
  rdᵉ ψ ρ (mergeAllᵉ lim e) = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (switchAllᵉ e)    = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (exhaustAllᵉ e)   = flatten (rdᵉ ψ ρ e)
  rdᵉ ψ ρ (μᵉ e)            = rdᵉ ψ ρ e
  rdᵉ ψ ρ (varᵉ x)          = 0 , 0 , 0
  rdᵉ ψ ρ (deferᵉ e)        = 0 , 0 , 0

  -- A TEMPLATE IS READ AGAINST ITS ARGUMENT, not scaled by a slope.  The
  -- join with the source's own depth is what a template that DROPS its
  -- argument needs: the source is still subscribed
  mapStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd) (ρ : Env) →
            Rd₃ → Fn Γ Δᵍ Δ Θ s t → Rd₃
  mapStep ψ ρ (d , ev , h) f = d , proj₁ r , proj₂ r ⊔′ h
    where r = rdᵗ ψ (ρ ▸ (ev , h)) f

  -- THE CLAUSE THE WHOLE FILE IS ABOUT.  The accumulator starts at the
  -- seed's own reading and each refold reads the step against the
  -- previous one — so the emitted fold the dead readings could not see
  -- is read at the accumulator it will actually be handed, refold by
  -- refold.  The source's top count is how many refolds there are
  scanStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd) (ρ : Env) →
             Rd₃ → Tm Γ Δᵍ Δ Θ t → Fn Γ Δᵍ Δ Θ s t → Rd₃
  scanStep ψ ρ (d , ev , h) z f = d , proj₁ a , proj₂ a ⊔′ h
    where a = foldGo ψ ρ (rdᵗ ψ ρ z) (ev , h) d f

  -- the accumulator's reading after each refold, joined over all of them
  -- because the fold EMITS every one and the claim is about the deepest
  foldGo : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s t} (ψ : Fin n → Rd) (ρ : Env)
           (acc src : Rd) (R : ℕ) → Fn Γ Δᵍ Δ Θ s t → Rd
  foldGo ψ ρ acc src zero    f = acc
  foldGo ψ ρ acc src (suc R) f =
    acc ⊔ᴿ foldGo ψ ρ (rdᵗ ψ (ρ ▸ (acc ⊔ᴿ src)) f) src R f

  rdᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd) (ρ : Env) →
        Tm Γ Δᵍ Δ Θ t → Rd
  -- THE LEAF, and the only clause that differs in kind from the dead
  -- readings: what is plugged here is read, not assumed absent
  rdᵗ ψ ρ (varᵗ x)      = ρ (varIx x)
  rdᵗ ψ ρ unit̂          = 0 , 0
  rdᵗ ψ ρ (bool̂ _)      = 0 , 0
  rdᵗ ψ ρ (nat̂ _)       = 0 , 0
  rdᵗ ψ ρ (pairᵗ a b)   = rdᵗ ψ ρ a ⊔ᴿ rdᵗ ψ ρ b
  rdᵗ ψ ρ (fstᵗ p)      = rdᵗ ψ ρ p
  rdᵗ ψ ρ (sndᵗ p)      = rdᵗ ψ ρ p
  rdᵗ ψ ρ (inlᵗ a)      = rdᵗ ψ ρ a
  rdᵗ ψ ρ (inrᵗ a)      = rdᵗ ψ ρ a
  rdᵗ ψ ρ (caseᵗ s l r) = caseStep ψ ρ (rdᵗ ψ ρ s) l r
  rdᵗ ψ ρ (ifᵗ c a b)   = rdᵗ ψ ρ a ⊔ᴿ rdᵗ ψ ρ b
  -- a PrimOp lands in natᵗ or boolᵗ: nothing plugged into it reaches a hop
  rdᵗ ψ ρ (primᵗ _ a)   = 0 , 0
  rdᵗ ψ ρ (strmᵗ e)     = topOf (rdᵉ ψ ρ e)

  caseStep : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u t} (ψ : Fin n → Rd) (ρ : Env) →
             Rd → Fn Γ Δᵍ Δ Θ s t → Fn Γ Δᵍ Δ Θ u t → Rd
  caseStep ψ ρ p l r = rdᵗ ψ (ρ ▸ p) l ⊔ᴿ rdᵗ ψ (ρ ▸ p) r

  rdᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd) (ρ : Env) →
         List (Tm Γ Δᵍ Δ Θ t) → Rd
  rdᵗˢ ψ ρ []       = 0 , 0
  rdᵗˢ ψ ρ (y ∷ ys) = rdᵗ ψ ρ y ⊔ᴿ rdᵗˢ ψ ρ ys

ψ₀ : Fin 0 → Rd
ψ₀ = λ ()

depthᴾ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} (ψ : Fin n → Rd) →
         Exp Γ Δᵍ Δ Θ t → ℕ
depthᴾ ψ e = proj₂ (topOf (rdᵉ ψ ε e))

----------------------------------------------------------------------
-- WHAT THE FRAME HANDS OUT, read at THIS measure.  A bound and the thing
-- it bounds have to be denominated alike, so the emissions are measured
-- by the reading under test and not by either dead one.  Only a `value`
-- carries a payload to subscribe, and the join because the claim is
-- about how deep one carrier can be.
----------------------------------------------------------------------

evHopᴾ : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd) →
         List (InstEvent (Closed Γ u)) → ℕ
evHopᴾ ψ []             = 0
evHopᴾ ψ (value v ∷ es) = depthᴾ ψ v ⊔ evHopᴾ ψ es
evHopᴾ ψ (_ ∷ es)       = evHopᴾ ψ es

carriedᴾ : ∀ {n} {Γ : Ctx n} {u} (ψ : Fin n → Rd) →
           Stream Γ (obs u) → ℕ
carriedᴾ ψ []         = 0
carriedᴾ ψ (em ∷ ems) = evHopᴾ ψ (InstEmit.events em) ⊔ carriedᴾ ψ ems

----------------------------------------------------------------------
-- THE READING, AT THE FAMILY THAT KILLED THE SWAP.  Its step emits a
-- FOLD whose source is the accumulator; the swapped reading priced that
-- accumulator at a variable and read three, nine, twenty-seven,
-- eighty-one.  Each row is LOAD-BEARING and could have failed either
-- way: a reading that still priced the variable at zero would climb
-- geometrically again, and one that stopped moving with the literals
-- would say the iteration is not running.
----------------------------------------------------------------------

_ : depthᴾ ψ₀ narrow₁ ≡ 1                              -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ narrow₂ ≡ 2                              -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ narrow₃ ≡ 3                              -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ narrow₄ ≡ 4                              -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- AND AT THE FAMILY THAT MADE THAT DEATH A RATE RATHER THAN A CONSTANT.
-- A second reference to the accumulator doubles the emitted fold's own
-- source per refold, which the swapped reading did not see at all — the
-- same numeral at both widths.  Here the two widths read alike in DEPTH
-- and the doubling is visible in the count instead, which is where it
-- belongs: the extra reference duplicates what is delivered, not how
-- deep it is.  Each row is LOAD-BEARING against a reading that confused
-- the two.
----------------------------------------------------------------------

_ : depthᴾ ψ₀ wide₁ ≡ 1                                -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ wide₂ ≡ 2                                -- LOAD-BEARING
_ = refl

_ : proj₁ (topOf (rdᵉ ψ₀ ε wide₂)) ≡ 2                 -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- AND AT THE ORIGINAL REFUTATION'S FAMILY, whose step emits a MERGE and
-- whose crossing is what the live reading dies of: flat at three while
-- the run climbs one per literal.  Each row is LOAD-BEARING against a
-- reading that had gone flat again.
----------------------------------------------------------------------

_ : depthᴾ ψ₀ inner₁ ≡ 1                               -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ inner₂ ≡ 2                               -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ inner₃ ≡ 3                               -- LOAD-BEARING
_ = refl

_ : depthᴾ ψ₀ inner₄ ≡ 4                               -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- WHAT THE RUNS HAND OUT, at the same reading.  Every one of these is
-- EQUAL to the door's, which is the finding: the reading is not a bound
-- over the run, it is the run's own depth computed from the term.  A row
-- that came in under the door would say the reading still carries slack
-- it has no reason to; one over it would be a crossing.
----------------------------------------------------------------------

_ : carriedᴾ ψ₀ (burstAt 1 narrow₁ ins₀) ≡ 1           -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 narrow₂ ins₀) ≡ 2           -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 narrow₃ ins₀) ≡ 3           -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 narrow₄ ins₀) ≡ 4           -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 wide₁ ins₀) ≡ 1             -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 wide₂ ins₀) ≡ 2             -- LOAD-BEARING
_ = refl

_ : carriedᴾ ψ₀ (burstAt 1 inner₄ ins₀) ≡ 4            -- LOAD-BEARING
_ = refl

----------------------------------------------------------------------
-- THE GUARD, AT EVERY ROW THE TWO DEAD READINGS CROSS AT.  Pinned by
-- `refl` so they move visibly if either side does, and taken at the
-- degenerate bound as well, so nothing here rests on the store having
-- room.
----------------------------------------------------------------------

_ : (carriedᴾ ψ₀ (burstAt 1 narrow₂ ins₀) ≤ᵇ depthᴾ ψ₀ narrow₂) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 narrow₄ ins₀) ≤ᵇ depthᴾ ψ₀ narrow₄) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 wide₂ ins₀) ≤ᵇ depthᴾ ψ₀ wide₂) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 0 narrow₂ ins₀) ≤ᵇ depthᴾ ψ₀ narrow₂) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 1 inner₄ ins₀) ≤ᵇ depthᴾ ψ₀ inner₄) ≡ true
_ = refl

_ : (carriedᴾ ψ₀ (burstAt 0 inner₂ ins₀) ≤ᵇ depthᴾ ψ₀ inner₂) ≡ true
_ = refl

----------------------------------------------------------------------
-- THE FORK.  The choice is between a fold clause in CLOSED FORM — a
-- power times a sum of subterm readings, which is what both dead
-- candidates are and what makes them blind to their own accumulator —
-- and one that ITERATES against an environment.  They are apart at the
-- first term the swap fails on, which is also the first term the
-- iteration is asked to run twice.
----------------------------------------------------------------------

Point : Set
Point = Closed Γ₀ (obs natᵗ)

closedForm iterated : Point → ℕ
closedForm e = hopD′ᵉ ν₀ η₀ e
iterated   e = depthᴾ ψ₀ e

plug-priced-fork : Separates closedForm iterated
plug-priced-fork = separates-at narrow₂ (λ ())
