------------------------------------------------------------------
-- THE REFOLD IS TYPE-PRESERVING, AND THAT IS THE WHOLE OF THE
-- CANDIDATE.
--
-- Every other fragment in this tree reads a DEPTH off a term, and
-- every one of them breaks on the same clause: the fold re-templates
-- its accumulator once per arriving value, so a template that nests
-- raises the depth per arrival and no clause can see how many
-- arrivals there are.  The candidate here does not price that clause
-- better.  It reads a different quantity — the ORDER of the
-- accumulator's TYPE — and the clause stops existing, because the
-- nesting a fold performs is an operation the type system already
-- knows returns what it was given.
--
-- `nestᵗ` is where that is visible.  Wrapping a value and flattening
-- it again is `obs t → obs t` and cannot be anything else, so the
-- template has the type of a step function whatever it does inside.
-- `evalTm`'s own signature is therefore the invariance theorem: the
-- depth world proves an accumulator's climb as a RATE with a real
-- induction under it, and the type world has it as the arrow the
-- evaluator already had to write down.
--
-- THE FRAGMENT IS UNTYPED EVERYWHERE ELSE IN THIS TREE, WHICH IS WHY
-- THIS FILE RESTATES A LANGUAGE INSTEAD OF IMPORTING ONE.  A value
-- there is `natᵛ` or `obsᵛ` with no index, so an order cannot be
-- written at all and the separation below cannot be posed.  The
-- language here is cut to the three heads the question needs and
-- claims nothing about the ones it drops.
--
-- WHAT THIS BUYS AND WHAT KILLS IT.  It buys: the climb is unbounded
-- at ONE type, and the inner hop's descent is the type's own
-- predecessor rather than a statement about runs.  What kills it as a
-- DESCENT ORDER is the last section — the structural walk runs the
-- other way and is unbounded where the hop's drop is one, and the
-- flatten/hop cycle returns to the reading it left.  A quantity a
-- cycle does not spend cannot be what orders the cycle.
--
-- SO THE READING SURVIVES ONLY WHERE IT IS NOT ASKED TO DESCEND: as
-- the INDEX of a store, saying what a handle may hold, with the
-- descent carried by the order handles were allocated in.  That
-- separation is the finding, and it is why this file states both
-- halves rather than picking one.
------------------------------------------------------------------
module Spike.Strata where

open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; zero; suc; _<_; _⊔_; s≤s; ≤-pred)
open import Data.Nat.Properties using (≤-refl; ⊔-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

------------------------------------------------------------------
-- THE LANGUAGE.  `obsᵛ` holds an expression, mirroring the real
-- development's `Val Γ (obs t) = Exp Γ [] [] [] t` — which is what
-- makes an observable value a TERM and the inner hop a real edge.
------------------------------------------------------------------

data Ty : Set where
  natᵗ : Ty
  obs  : Ty → Ty

data Val : Ty → Set
data Exp : Ty → Set

data Val where
  natᵛ : ℕ → Val natᵗ
  obsᵛ : ∀ {t} → Exp t → Val (obs t)

-- the step template, as a function of the accumulator alone: the
-- arriving value is data and the refold does not read it, so dropping
-- it costs the question nothing
data Tm : Ty → Set where
  accᵗ  : ∀ {t} → Tm t
  nestᵗ : ∀ {t} → Tm (obs t) → Tm (obs t)

data Exp where
  ofᵉ       : ∀ {t} → List (Val t) → Exp t
  mergeAllᵉ : ∀ {t} → Exp (obs t) → Exp t
  scanᵉ     : ∀ {t} → Tm t → Val t → Exp natᵗ → Exp t

-- wrap and flatten.  THE TYPE IS THE FINDING: `mergeAllᵉ ∘ ofᵉ` is
-- forced to land back where it started, so a nesting step is an
-- endomorphism however many times it is taken
evalTm : ∀ {t} → Tm t → Val t → Val t
evalTm accᵗ      a = a
evalTm (nestᵗ f) a = obsᵛ (mergeAllᵉ (ofᵉ (evalTm f a ∷ [])))

------------------------------------------------------------------
-- THE TWO READINGS.
------------------------------------------------------------------

-- read off the TYPE: how deep observables are written INTO IT
ord : Ty → ℕ
ord natᵗ    = 0
ord (obs t) = suc (ord t)

-- read off the TERM, mirroring the real `depᵗ`'s `strmᵗ` clause —
-- a wrap costs one, and nothing else does
hopDv : ∀ {t} → Val t → ℕ
hopD  : ∀ {t} → Exp t → ℕ
hopDl : ∀ {t} → List (Val t) → ℕ
hopDt : ∀ {t} → Tm t → ℕ

hopDv (natᵛ n) = 0
hopDv (obsᵛ e) = suc (hopD e)

hopDl []       = 0
hopDl (v ∷ vs) = hopDv v ⊔ hopDl vs

hopDt accᵗ      = 0
hopDt (nestᵗ f) = suc (hopDt f)

hopD (ofᵉ vs)       = hopDl vs
hopD (mergeAllᵉ e)  = hopD e
hopD (scanᵉ f z e)  = hopDt f ⊔ hopDv z ⊔ hopD e

------------------------------------------------------------------
-- THE SEPARATION.  One fold, one type, an unbounded climb.
------------------------------------------------------------------

-- k nesting steps, which is what a burst of k deliveries performs
nestⁿ : ℕ → Tm (obs natᵗ)
nestⁿ zero    = accᵗ
nestⁿ (suc k) = nestᵗ (nestⁿ k)

-- the accumulator after k deliveries, from the emptiest seed there is
accAfter : ℕ → Val (obs natᵗ)
accAfter k = evalTm (nestⁿ k) (obsᵛ (ofᵉ []))

-- THE TERM READING IS UNBOUNDED IN THE BURST.  Not a table of rows: a
-- family, so no wider bound absorbs it
hopD-climbs : ∀ k → hopDv (accAfter k) ≡ suc k
hopD-climbs zero    = refl
hopD-climbs (suc k) = cong suc (trans (⊔-identityʳ _) (hopD-climbs k))

-- the type reading of a value, which CANNOT consult the value: that is
-- the property, not a limitation of the definition
ordᵛ : ∀ {t} → Val t → ℕ
ordᵛ {t} _ = ord t

-- AND THE TYPE READING DOES NOT MOVE ACROSS THE SAME FAMILY, WHICH
-- AGDA ENFORCES RATHER THAN THIS FILE ASSERTING IT.  `accAfter` is a
-- family at ONE type, so every k gives the same closed numeral and the
-- statement closes by `refl` with k free — beside `hopD-climbs`, which
-- is the same family read the other way
ord-still : ∀ (k : ℕ) → ordᵛ (accAfter k) ≡ 1
ord-still k = refl

-- the same fact said where it actually bites: `evalTm`'s own arrow.
-- The depth world proves the analogous statement as a RATE with an
-- induction under it; here it is the signature, instantiated
refold-endo : ∀ {t} (f : Tm t) (a : Val t) → Val t
refold-endo f a = evalTm f a

------------------------------------------------------------------
-- THE EDGE THE CANDIDATE BUYS, AND THE EDGE IT OWES.
------------------------------------------------------------------

-- the type reading of an expression, which likewise cannot consult it
ordᵉ : ∀ {t} → Exp t → ℕ
ordᵉ {t} _ = ord t

-- what the hop subscribes: the expression an emitted observable holds
unwrap : ∀ {t} → Val (obs t) → Exp t
unwrap (obsᵛ e) = e

-- THE INNER HOP DESCENDS BY THE TYPE'S OWN PREDECESSOR.  Subscribing
-- to an emitted observable moves from `obs t` to `t`, so the drop is
-- the typing rule and not a theorem about what a run emits — stated
-- over the pair the recursion actually steps between.  This is the
-- edge every depth reading pays a real induction for
hop-drops : ∀ {t} (o : Val (obs t)) → ordᵉ (unwrap o) < ordᵛ o
hop-drops o = ≤-refl

-- the walk that flattens, written out so the claim below is about a
-- step this language takes rather than about an arrow alone
flatten : ∀ {t} → Exp (obs t) → Exp t
flatten e = mergeAllᵉ e

-- AND THE STRUCTURAL DESCENT RUNS THE OTHER WAY, which is the whole of
-- what is unsettled.  Flattening reads a source of order one ABOVE its
-- own result, so the walk into a subterm RAISES exactly the reading the
-- hop lowers — and the two cannot both be the strict component of one
-- order.  The candidate therefore buys the edge that breaks a depth
-- reading and owes the edge a depth reading gets for free
walk-climbs : ∀ {t} (e : Exp (obs t)) → ordᵉ (flatten e) < ordᵉ e
walk-climbs e = ≤-refl

------------------------------------------------------------------
-- AND THE CLIMB IS NOT BOUNDED BY THE DROP, WHICH SETTLES IT
-- AGAINST THE READING ALONE.
--
-- Above, the walk climbs by exactly one, so a reader may still hope
-- some pairing of the two edges recovers an order.  It does not, for
-- two reasons this section states as code.
--
-- FIRST, the climb is UNBOUNDED at one step.  A map's source and
-- target types are unrelated — in the real fragment `mapᵉ` is
-- `Fn s t → Exp s → Exp t` with nothing tying `s` to `t` — so the
-- descent into a source may raise the reading by any amount, while
-- every drop the hop offers is the type's single predecessor.
--
-- SECOND, and this is the sharper half, the round trip is NEUTRAL.
-- Flattening descends from `t` into a source at `obs t`, and the hop
-- out of that source's emission lands back at `t`.  The reading is
-- where it started, so it cannot be what the cycle spends: whatever
-- pays for a burst has to be found on the other edge, which is the
-- edge that a refold destroys.
------------------------------------------------------------------

-- a map whose source type is unconstrained by its result
data Exp′ : Ty → Set where
  emb   : ∀ {t} → Exp t → Exp′ t
  mapᵉ′ : ∀ {s t} → Val t → Exp′ s → Exp′ t

ord′ : ∀ {t} → Exp′ t → ℕ
ord′ {t} _ = ord t

obsⁿ : ℕ → Ty
obsⁿ zero    = natᵗ
obsⁿ (suc k) = obs (obsⁿ k)

ord-obsⁿ : ∀ k → ord (obsⁿ k) ≡ k
ord-obsⁿ zero    = refl
ord-obsⁿ (suc k) = cong suc (ord-obsⁿ k)

-- a source k strata above its own consumer, for any k
deepSrc : ∀ k → Exp′ (obsⁿ k)
deepSrc k = emb (ofᵉ [])

shallow : ∀ k → Exp′ natᵗ
shallow k = mapᵉ′ (natᵛ 0) (deepSrc k)

-- THE STRUCTURAL DESCENT RAISES THE READING BY AN ARBITRARY AMOUNT,
-- against a hop that only ever lowers it by one
walk-climbs-unbounded : ∀ k → ord′ (deepSrc k) ≡ k
walk-climbs-unbounded k = ord-obsⁿ k

walk-from-zero : ∀ k → ord′ (shallow k) ≡ 0
walk-from-zero k = refl

-- AND THE FLATTEN/HOP CYCLE RETURNS TO ITS OWN READING.  Left side is
-- where the walk into a flatten's source starts; right side is where
-- the hop out of that source's emission lands
roundtrip-neutral : ∀ {t} (e : Exp (obs t)) (o : Val (obs t)) →
                    ordᵉ (flatten e) ≡ ordᵉ (unwrap o)
roundtrip-neutral e o = refl
