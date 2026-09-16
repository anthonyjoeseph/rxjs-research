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
--
-- AND `denote` IS STATED AT `Closed`, WHICH IS NARROWER THAN IT WILL
-- END UP.  A compositional reading has to denote an OPEN expression,
-- and `Exp` binds in three places at once — the guarded fixpoint
-- variables, the let/`defer` variables, and the term variables a `Fn`
-- closes over — so it wants an environment for all three.  That
-- environment is leaves for an assembly nobody has written: it is
-- minted by the leg that states the first compositionality equation,
-- which is the only thing that can say what it must carry.
------------------------------------------------------------------

postulate
  Beh : ∀ {n} → Ctx n → Ty → Set

  denote : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Beh Γ t

  observe : ∀ {n} {Γ : Ctx n} {t} → Beh Γ t → Stream Γ t

-- WHAT A PROGRAM MEANS, READ BACK AS A STREAM.  A body rather than a
-- fourth postulate, so that the domain and its observation are separate
-- leaves and the two claims below are stated over one name.
meaning : ∀ {n} {Γ : Ctx n} {t} → Closed Γ t → Slots Γ → Stream Γ t
meaning e ins = observe (denote e ins)

------------------------------------------------------------------
-- THE THREE CLAIMS.
--
-- `run-monotone` mentions nothing postulated and is the one row here a
-- program can refute today: more fuel only ever EXTENDS a run, it never
-- rewrites what a shorter one already emitted.  It is separate from
-- `adequacy` rather than folded into it because it is a fact about the
-- machine alone, so it survives every restatement of the domain above
-- it — and because without it "prefix of the limit" does not even
-- describe a coherent family of runs to take a limit of.
--
-- `saturation` is the half that stops the denotation running ahead of
-- the machine.  It is quantified over EVERY prefix, which is what keeps
-- it from being discharged at the empty one: a `pre` reaching into the
-- denotation's own tail is a demand for a fuel that reaches it.
------------------------------------------------------------------

postulate
  run-monotone :
    ∀ {n} {Γ : Ctx n} {t} (fuel₁ fuel₂ : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) → fuel₁ ≤ fuel₂ →
    ∃ λ rest → evaluate↓ fuel₂ e ins ≡ evaluate↓ fuel₁ e ins ++ rest

  adequacy :
    ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel)
      (e : Closed Γ t) (ins : Slots Γ) →
    ∃ λ rest → meaning e ins ≡ evaluate↓ fuel e ins ++ rest

  saturation :
    ∀ {n} {Γ : Ctx n} {t} (e : Closed Γ t) (ins : Slots Γ)
      (pre : Stream Γ t) →
    (∃ λ rest → meaning e ins ≡ pre ++ rest) →
    ∃ λ fuel → ∃ λ rest → evaluate↓ fuel e ins ≡ pre ++ rest
