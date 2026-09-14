-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN THAT IS A DERIVATION.  `The-Proof` draws `evaluate-well-formed`
-- and nothing else from this face: a canonical run's emit stream is
-- accepted by the protocol automaton, which is what lets the batcher be
-- quantified over WellFormed streams rather than arbitrary ones.
--
-- WHY THE BODY IS A SPLIT AND NOT A BARE POSTULATE.  Totality is the
-- descent's own output and is proven elsewhere; the bookkeeping is this
-- face's debt.  Stating the debt as ONE leaf over the two halves'
-- derivations, and splitting the descent's conclusion HERE, is what
-- keeps the leaf a leaf: the split is performed by a real body, so the
-- descent's theorem is CONSUMED rather than handed to a postulate as
-- its only use — which would earn it no reachability and would assert
-- that the two are sufficient without ever checking it.
--
-- AND THE SPLIT IS THE SHAPE THE DEBT IS OWED IN, not a convenience.
-- The two halves are stepped by different machinery — a subscribe frame
-- returns its burst in one go while the drain spends one unit per
-- arrival — so a bookkeeping argument is an induction over the drain
-- seeded at whatever the burst left, and the seam is where the seed is
-- handed over.  A leaf stated over the concatenation would have to
-- rediscover that seam inside its own proof.
--
-- AND THE SPLIT IS NOW THE RELATION'S OWN CONSTRUCTOR, WHICH IS WHAT
-- THE CUTOVER BOUGHT HERE.  The seam used to be recovered by a lemma
-- about lists — take a property of a concatenation apart into
-- properties of its two sides — and that lemma existed because the
-- property was read off the OUTPUT.  `eval-run` carries the two halves
-- as fields, so the split is a pattern match: nothing is rediscovered,
-- and the two seeds the leaf receives are the ones the run itself
-- passed rather than ones this module names again.
module Verify-Well-Formed where

open import Data.List using (_++_)
open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; root; sched-init; st-init)
open import Rx.Evaluator.Run using (evaluate)
open import Rx.Evaluator.Domain using (subscribeE⇓; drain⇓; eval-run)
open import Rx.Protocol using (WellFormed)
open import Verify-Rank-Sufficient using (evaluate⇓-total)

------------------------------------------------------------------
-- THE DEBT.  Everything the protocol argument needs about a run given
-- as its two derivations.  It is one leaf because nothing above it has
-- yet decided the shape the bookkeeping should take — a statement
-- carved into pieces against a machine whose recursion may still be
-- restated is inventory rather than progress.
------------------------------------------------------------------

postulate
  burst-drain-well-formed :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Fuel) (ins : Slots Γ) {burst rest : Stream Γ t} {sched′ st′} →
    subscribeE⇓ {e = e} e root 0 0 (sched-init e ins) (st-init e)
      (burst , sched′ , st′) →
    drain⇓ {e = e} fuel 1 sched′ st′ rest →
    WellFormed (burst ++ rest)

-- and the assembly, which is one match.  `evaluate⇓-total` hands over a
-- derivation at the run's own output; `eval-run` is the only
-- constructor of that family, so matching it IS the seam, and the
-- output it reassembles is `evaluate`'s by the same equation the
-- constructor was stated at.
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate fuel e ins)
evaluate-well-formed fuel e ins with evaluate⇓-total fuel e ins
... | eval-run s d = burst-drain-well-formed fuel ins s d
