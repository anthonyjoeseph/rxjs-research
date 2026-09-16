-- WHAT A DENOTATION BUYS, AND IT IS NOT A SECOND EVALUATOR.  Every
-- statement in this repo today is stated over the machine: a fuel, a
-- schedule, a state, and a stream read off `evaluate↓`.  That is enough
-- to say what one run does and useless for saying what a PROGRAM means,
-- because the machine's own bookkeeping — node ids, arrival ordinals,
-- the drain counter — is visible in the answer.  A denotation is the
-- object that is not: a `Beh` is what an expression means given its
-- slot table, with no fuel in it and nothing minted while reading it.
--
-- AND THE CLAIM THAT MAKES IT WORTH HAVING IS THE PAIR, NEVER EITHER
-- HALF.  `adequacy` alone is satisfiable by a denotation defined as the
-- machine's own limit, and `saturation` alone by one that denotes
-- nothing anybody runs.  Together they pin a program's `meaning` to be
-- exactly what the machine converges to: every run is a prefix of it,
-- and every prefix of it is reached by some run.
--
-- WHAT IS DELIBERATELY NOT STATED YET, so that nobody reads the pair as
-- more than it is: COMPOSITIONALITY.  Nothing below says `denote` of a
-- node is built from `denote` of its children, and until something
-- does, this face asserts a limit rather than a semantics — which is
-- the whole of the tier's work and why its rows read VACUITY.  The
-- equations want a `Beh`-level operator per former and a denotation of
-- `Fn`, and minting those now would be leaves for an assembly nobody
-- has written.

module Verify-Adequacy where

open import Data.List using (_++_)
open import Data.Nat using (_≤_)
open import Data.Product using (∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Ty; Closed)
open import Rx.Evaluator using (Stream)
open import Rx.Evaluator.Builder using (evaluate↓)
open import Rx.Slots using (Slots)

------------------------------------------------------------------
-- THE DOMAIN.
--
-- `Beh` is indexed by the slot context because a behaviour of this
-- language can carry VALUES, and a value's type is read against Γ — an
-- observable of observables denotes something whose elements are
-- themselves behaviours over the same table.
------------------------------------------------------------------

postulate
  -- DEAD ROUTE: choosing this domain's shape by instantiation, the way
  --   every other face here is de-risked.  A postulated SET has no
  --   elements, so there is nothing to compute with and no row decides
  --   between two candidate domains; what decides between them is the
  --   first compositionality equation, which is a statement rather than
  --   a program.  So this trio is the one place on the face where
  --   probing is not merely blocked but has no subject, and the tier
  --   above it is what supplies the requirement instead.
  Beh : ∀ {n} → Ctx n → Ty → Set

  -- DEAD ROUTE: denoting an expression by recursion on `Closed` alone.
  --   A compositional reading has to denote an OPEN expression, and
  --   `Exp` binds in three places at once — the guarded fixpoint
  --   variables, the let/`defer` variables, and the term variables a
  --   `Fn` closes over — so it wants an environment for all three.
  --   That environment is leaves for an assembly nobody has written: it
  --   is minted by the leg that states the first equation, which is the
  --   only thing that can say what it must carry.
  denote : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Beh Γ t

  -- WHAT THE OBSERVATION HANDS BACK IS FIXED FROM OUTSIDE THIS FACE.
  -- The protocol automaton reads an emit list and asks whether it is
  -- settled, so the well-formedness face is stated ACROSS this boundary
  -- — which makes a `Beh` that cannot say where its instants end a
  -- domain that face cannot use, however well it serves the pair below.
  --
  -- DEAD ROUTE: fixing the observation from the domain's side, by
  --   reading off whatever shape the first-order formers make natural.
  --   The consumer is a predicate demanded at a CUT POINT, so the
  --   requirement arrives from the tier above and not from here.
  observe : ∀ {n} {Γ : Ctx n} {t} → Beh Γ t → Stream Γ t

-- WHAT A PROGRAM MEANS, READ BACK AS A STREAM.  A body rather than a
-- fourth postulate, so that the domain and its observation are separate
-- leaves and the two claims below are stated over one name.
meaning : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Stream Γ t
meaning e ins = observe (denote e ins)

------------------------------------------------------------------
-- THE THREE CLAIMS.
------------------------------------------------------------------

postulate
  -- A FACT ABOUT THE MACHINE ALONE, WHICH IS WHY IT IS SEPARATE.  More
  -- fuel only ever EXTENDS a run; it never rewrites what a shorter one
  -- already emitted.  Folded into `adequacy` it would be restated every
  -- time the domain is, and without it "prefix of the limit" does not
  -- even describe a coherent family of runs to take a limit of.
  --
  -- PROBED: `Probed.Adequacy` reaches this conclusion at two programs
  --   and three fuel gaps.  One row grows — the remainder is pinned
  --   non-empty, so the EXISTENCE half is decided and not merely the
  --   prefix half — and two saturate, where the remainder is pinned
  --   EMPTY and a renumbered instant, a re-minted provenance or a
  --   re-ordered burst is the only available failure.  One of those
  --   two sits past a delivery, so the drain has stepped in the
  --   shorter run and its resumption ordinal is part of what is
  --   decided.  Not reached: any flattening program, any cold source,
  --   a source firing at more than one tick, and a fuel gap wider than
  --   the program's own horizon.
  run-monotone :
    ∀ {n} {Γ : Ctx n} {t} (fuel₁ fuel₂ : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) → fuel₁ ≤ fuel₂ →
    ∃ λ rest → evaluate↓ fuel₂ e ins ≡ evaluate↓ fuel₁ e ins ++ rest

  -- THE PAIR, AND NEITHER HALF IS THE CLAIM.  `adequacy` alone is
  -- satisfied by a denotation defined as the machine's own limit and
  -- `saturation` alone by one nobody can run; together they pin a
  -- program's `meaning` to exactly what the machine converges to.
  -- `saturation` is quantified over EVERY prefix, which is what keeps
  -- it from being discharged at the empty one: a `pre` reaching into
  -- the denotation's own tail is a demand for a fuel that reaches it.
  --
  -- DEAD ROUTE: de-risking either half by INSTANTIATION, ahead of the
  --   domain being defined.  Both are stated over `meaning`, which is
  --   `observe` of `denote` — two postulates, so the left side of each
  --   conclusion reduces at no program whatever and no row can be
  --   written at any point.  This is a coverage boundary rather than a
  --   difficulty, and it lifts the moment `denote` becomes a
  --   definition rather than ever being shown workable as it stands.
  adequacy :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) →
    ∃ λ rest → meaning e ins ≡ evaluate↓ fuel e ins ++ rest

  -- DEAD ROUTE: instantiating this one at a prefix the machine
  --   actually reached, which is the shape that would sidestep the
  --   boundary above.  It does not: the HYPOTHESIS is a containment in
  --   `meaning` too, so a row would have to discharge a premise about
  --   the postulated domain before its conclusion was ever asked for.
  --   Both sides are blocked here where only the conclusion is above.
  saturation :
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
      (pre : Stream Γ t) →
    (∃ λ rest → meaning e ins ≡ pre ++ rest) →
    ∃ λ fuel → ∃ λ rest → evaluate↓ fuel e ins ≡ pre ++ rest
