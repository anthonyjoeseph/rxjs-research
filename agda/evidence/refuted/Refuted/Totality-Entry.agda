-- THE SUBSCRIBE CYCLE'S TOTALITY LEAF IS FALSE AS STATED, AND WHAT
-- KILLS IT IS THE ENTRY AND NOT THE PROGRAM.
--
-- The statement quantifies over EVERY accessibility witness, so it
-- claims a derivation at the machine's own result whatever triple the
-- caller entered at.  One clause of the evaluator compares a component
-- of that triple against a quantity of the term — the μ unfold's
-- synchronous size — and answers the negative case with a dry burst,
-- which no constructor of the relation produces.  A triple small enough
-- is therefore a counterexample at a program with no gate, no share and
-- no flattener in it at all: a `μ` whose body is a one-shot source,
-- entered at zero.
--
-- SO THIS IS NOT THE DRY FAMILY AGAIN, AND THE DIFFERENCE IS WHICH END
-- MOVES.  The witnesses against the top line are programs whose own
-- reading starves the guard at the entry `evaluate` builds, so they are
-- answered by deleting the arms.  This one is answered by nothing the
-- cutover does: with the arms gone the clause has to be told the guard
-- holds, and the statement as written carries no hypothesis that could
-- tell it.  The relation is spent at a derivation built AT THE
-- MACHINE'S OWN RESULT, and the machine's result at a starved entry is
-- a burst the relation cannot relate.
--
-- WHAT THE REPAIR HAS TO SUPPLY IS AN ENTRY INVARIANT TYING THE
-- WITNESS TO THE TERM.  `evaluate` enters at a triple it computes from
-- the program, so every call the top line makes satisfies one; the
-- statement simply does not say so.  Quantifying the triple freely is
-- what makes it refutable, and the conjunct that would close this
-- witness — the term's synchronous size under the triple's third
-- component — is exactly the strengthened return type the frame shelf
-- is being written to carry.  The witness is claimed beside the ⊥ for
-- that reason: it reports the ONE number the guard reads, so a repair
-- that moved the entry leaves it failing to typecheck rather than
-- quietly agreeing.
module Refuted.Totality-Entry where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.Vec using () renaming ([] to []ⱽ)
open import Induction.WellFounded using (Acc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Rx.Prim using (Id; Tick)
open import Rx.Exp using (Ctx; Closed; Exp; natᵗ; nat̂; ofᵉ; μᵉ; syncSizeᵉ; unfoldμ)
open import Rx.Slots using (Slots)
open import Rx.Strat-Order using (Tri; _≺_; ≺-wellFounded)
open import Rx.Evaluator using (Path; root; Sched; EvalSt; subscribeE;
  sched-init; st-init; hasDry)
open import Rx.Evaluator.Domain using (subscribeE⇓; subs-μ; subs-of)

----------------------------------------------------------------------
-- THE STATEMENT, WRITTEN OUT HERE RATHER THAN IMPORTED, for the reason
-- the sibling witnesses carry: `src` declares a postulate of exactly
-- this type, and a refutation that APPLIED it would be evidence about
-- whatever it says today rather than about the form it was taken
-- against.  A repair that adds the entry invariant makes the row below
-- fail to typecheck.
----------------------------------------------------------------------

SubscribeTotal : Set
SubscribeTotal =
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo}
  {τ : Tri} (ac : Acc _≺_ τ) (b : Closed Γ u) (κ : Path Γ lo u t)
  (id : Id) (now : Tick) (sched : Sched Γ) (st : EvalSt e) →
  subscribeE⇓ {e = e} b κ id now sched st
    (subscribeE {e = e} ac b κ id now sched st)

----------------------------------------------------------------------
-- THE PROGRAM, AND IT IS THE SMALLEST ONE THAT REACHES THE CLAUSE.  A
-- `μ` whose body never reads the var it binds unfolds to that body, so
-- the unfolding is a one-shot source and the run is finite — nothing
-- here depends on the recursion being live.  What the row spends is
-- the clause's GUARD, not its recursion.
----------------------------------------------------------------------

Γ₀ : Ctx 0
Γ₀ = []ⱽ

ins₀ : Slots Γ₀
ins₀ = λ ()

body : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
body = ofᵉ (nat̂ 1 ∷ [])

loop : Closed Γ₀ natᵗ
loop = μᵉ body

-- THE STARVED ENTRY.  The third component is what the μ clause reads,
-- and nothing in the statement relates it to the term, so it is chosen
-- freely here.
τ₀ : Tri
τ₀ = 0 , 0 , 0

-- THE CROSSING, PINNED BY `refl` AND CLAIMED BESIDE THE ⊥.  The
-- unfolding's synchronous size is what the clause compares against the
-- entry's third component, so this is the one number the guard reads —
-- and it is not below zero.
unfold-size : syncSizeᵉ (unfoldμ body) ≡ 3
unfold-size = refl

-- AND THE RESULT THE MACHINE ACTUALLY RETURNS AT THAT ENTRY, which is
-- the burst the relation has no constructor for.
dry-entry :
  hasDry (proj₁ (subscribeE {e = loop} (≺-wellFounded τ₀) loop
                   (root {lo = 0}) 0 0 (sched-init loop ins₀) (st-init loop)))
    ≡ true
dry-entry = refl

----------------------------------------------------------------------
-- THE REFUTATION.  The only constructor at a `μᵉ` hands the obligation
-- straight to the unfolding, and the only constructor at a one-shot
-- source demands the machine's burst be `oneShotBurst`'s — which is
-- wet.  Reading dryness off that equation is what turns the mismatch
-- into a `Bool` clash, rather than leaving it to unification inside a
-- record.
----------------------------------------------------------------------

wet-not-dry : false ≡ true → ⊥
wet-not-dry ()

subscribe-total-false : SubscribeTotal → ⊥
subscribe-total-false h
  with h {e = loop} {τ = τ₀} (≺-wellFounded τ₀) loop (root {lo = 0}) 0 0
         (sched-init loop ins₀) (st-init loop)
... | subs-μ (subs-of eq) = wet-not-dry (cong (λ z → hasDry (proj₁ z)) eq)
