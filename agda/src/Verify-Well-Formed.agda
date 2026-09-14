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
open import Data.Product using (∃; _,_; proj₁)
open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; root; sched-init; st-init)
open import Rx.Evaluator.Builder using (evaluate↓; evaluate!)
open import Rx.Evaluator.Domain using (evaluate⇓; subscribeE⇓; drain⇓; eval-run)
open import Rx.Protocol using (WellFormed)

------------------------------------------------------------------
-- THE DEBT.  Everything the protocol argument needs about a run given
-- as its two derivations.  It is one leaf because nothing above it has
-- yet decided the shape the bookkeeping should take — a statement
-- carved into pieces against a machine whose recursion may still be
-- restated is inventory rather than progress.
--
-- PROBED: the QuickCheck sweep, which decides this leaf's own
--   conclusion at every program it runs — `evaluate-well-formed` below
--   feeds the leaf the two derivations that run produced, and
--   `wellFormed?` is the same computation `WellFormed` is, so a sampled
--   program is an instantiation rather than a twin of one.  6200
--   programs over two depths, about a third of them carrying `μᵉ`, no
--   refutation.  The sweep is pinned to the harness it was run against
--   by `git show a0d882c6:agda/src/QuickCheck.agda`, since the
--   generator's fragment IS the coverage boundary.  Not reached:
--   anything off that fragment —
--   a context other than its two nat slots, a function returning an
--   observable, and any fuel but its own.
------------------------------------------------------------------

postulate
  burst-drain-well-formed :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Fuel) (ins : Slots Γ) {burst rest : Stream Γ t} {sched′ st′} →
    subscribeE⇓ {e = e} {lo = n} e root 0 0 (sched-init e ins) (st-init e)
      (burst , sched′ , st′) →
    drain⇓ {e = e} fuel 1 sched′ st′ rest →
    WellFormed (burst ++ rest)

-- and the assembly, which is one match.  The builder hands over a run
-- TOGETHER WITH its derivation, and `eval-run` is the only constructor
-- of that family, so matching it IS the seam — and the output the
-- constructor reassembles is the one the evaluator returns, because the
-- evaluator IS that pair's first projection.
--
-- THE MATCH GOES THROUGH A LOCAL RATHER THAN A `with`, and it is the
-- projection that forces it: the goal names the evaluator, the
-- derivation is about the pair, and `with` abstracts syntactic
-- occurrences rather than unfolding to find them.  Naming the pair
-- makes the goal mention it, which is all the refinement needs.
evaluate-well-formed :
  ∀ {n} {Γ : Ctx n} {t} (fuel : Fuel) (e : Closed Γ t) (ins : Slots Γ) →
  WellFormed (evaluate↓ fuel e ins)
evaluate-well-formed fuel e ins = go (evaluate! fuel e ins)
  where
  go : (w : ∃ λ out → evaluate⇓ fuel e ins out) → WellFormed (proj₁ w)
  go (_ , eval-run s d) = burst-drain-well-formed fuel ins s d
