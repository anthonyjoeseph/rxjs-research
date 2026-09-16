-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN THAT IS A DERIVATION.  `The-Proof` draws `evaluate-well-formed`
-- and nothing else from this face: a canonical run's emit stream is
-- accepted by the protocol automaton, which is what lets the batcher be
-- quantified over WellFormed streams rather than arbitrary ones.
--
-- THE SEAM IS THE RELATION'S OWN CONSTRUCTOR, WHICH IS WHAT THE
-- CUTOVER BOUGHT HERE.  The two halves are stepped by different
-- machinery — a subscribe frame returns its burst in one go while the
-- drain spends one unit per arrival — so a bookkeeping argument is an
-- induction over the drain seeded at whatever the burst left.  That
-- seam used to be recovered by a lemma about lists, because the
-- property was read off the OUTPUT; `eval-run` carries the two halves
-- as fields, so it is now a pattern match and the two seeds are the
-- ones the run itself passed.
--
-- AND THE COMPOSITE IS A BODY NOW, WHICH IS WHERE THE CARVE BUYS
-- SOMETHING.  The debt used to be ONE leaf over both derivations,
-- asserting a conclusion about the CONCATENATION — so the automaton's
-- state at the seam was named nowhere and every attempt on either half
-- would have had to rediscover it.  The two leaves below carry that
-- state explicitly, the composition of their conclusions is checked by
-- `Glue`'s fold law rather than assumed, and the final settle is its
-- own named step rather than something absorbed into a preservation
-- claim where it would be invisible.
--
-- WHAT THE SAMPLING SWEEP DECIDED, and it is recorded here rather than
-- as a receipt because the statement it instantiates is now proven:
-- 6200 programs over two depths, about a third carrying `μᵉ`, no
-- refutation of `WellFormed (evaluate↓ …)` — the harness's `wellFormed?`
-- is the same computation `WellFormed` is, pinned to
-- `git show a0d882c6:agda/src/QuickCheck.agda`.  It reaches NEITHER
-- leaf's conclusion, which mentions an intermediate automaton state the
-- harness never computes, and it reaches only derivations the BUILDER
-- produced while both leaves quantify over any at their indices —
-- `evaluate-deterministic` is the fact that would make those the same
-- set.
module Verify-Well-Formed where

open import Data.Bool using (true)
open import Data.List using (_++_)
open import Data.Maybe using (just)
open import Data.Product using (∃; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (Stream; Sched; EvalSt; root; sched-init; st-init)
open import Rx.Evaluator.Builder using (evaluate↓; evaluate!)
open import Rx.Evaluator.Domain using (evaluate⇓; subscribeE⇓; drain⇓; eval-run)
open import Rx.Protocol using (WellFormed; ProtocolSt; protocol-init; runProtocol;
  paidUp)
open import Verify-Well-Formed.Invariant using (BurstInv)
open import Verify-Well-Formed.Glue using (run-++-just; acceptPaid)

------------------------------------------------------------------
-- THE DEBT, IN TWO HALVES THAT MEET AT A NAMED STATE.
------------------------------------------------------------------

postulate
  -- THE ROOT FRAME.  Stated at the initial states rather than over an
  -- arbitrary invariant-satisfying one, so that it owes its own base
  -- case: the generic form would need that base case handed IN, and a
  -- proven base case handed to a postulate is a sufficiency claim
  -- nothing checks.  Its conclusion is the seam — the automaton's state
  -- after the burst, and the relation that state stands in to the
  -- evaluator's.
  --
  -- PROBED: `Probed.Seam` reaches this conclusion at a two-value
  --   source-free program and at a one-hot-slot program, which between
  --   them decide every field of the relation.  The source-free row
  --   decides the four the burst alone can reach — the fold arrives at
  --   a state at all, that state's live multiset shadows the registry,
  --   its horizon has not run ahead of the frame's own id, and its open
  --   instant is the frame's with nothing owed.  The hot row carries a
  --   non-empty live list and a real registration, so the schedule's
  --   well-typedness is CHECKED there rather than discharged by an
  --   empty domain.  Not reached: every flattening program, since the
  --   frame dispatch hands a `thru-outer` frame to a live postulate and
  --   nothing past it reduces; any COLD source, so every arrival not
  --   scheduled at tick zero; more than one scheduled source, so no row
  --   separates the live multiset's entries from one another.
  subscribeE-root-wf :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (ins : Slots Γ)
      {burst : Stream Γ t} {sched′ : Sched Γ} {st′ : EvalSt e} →
    subscribeE⇓ {e = e} {lo = n} e root 0 0 (sched-init e ins) (st-init e)
      (burst , sched′ , st′) →
    ∃ λ S₁ → (runProtocol protocol-init burst ≡ just S₁)
           × BurstInv {e = e} 0 sched′ st′ S₁

  -- THE DRAIN.  Generic in the seam state, because its induction is
  -- over the drain and every step of that induction re-enters this
  -- statement at a state the previous step produced — a form pinned to
  -- the root's own states could not be applied to itself.  It carries
  -- the final settle rather than leaving it to the composite, since
  -- the last instant is closed by the drain's own last step and no
  -- fact about the fold above supplies it.
  --
  -- PROBED: `Probed.Seam` reaches this conclusion at the state the root
  --   row above produced, so the rows compose into one run rather than
  --   standing at a hand-built state the machine cannot reach.  Two
  --   rows, and they split the statement: at a source-free program the
  --   drain emits nothing, so what is decided is the EXIT — a seam
  --   state is already paid up, and a relation admitting an unsettled
  --   instant fails there.  At a hot slot firing at tick zero the drain
  --   delivers, and the probe pins the emit count, so the fold runs
  --   over envelopes the drain MINTED and the row decides that a
  --   delivered arrival leaves the automaton paid up — the preservation
  --   half, and the envelope is pinned whole rather than by count, so
  --   the close it carries is part of what the row decides.  Not
  --   reached: every close but `exhausted` — nothing here CUTS, so the
  --   shadow field's `dying` condition is discharged vacuously at every
  --   row — and everything the row above does not reach.
  drain-wf :
    ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
      (fuel : Fuel) {sched : Sched Γ} {st : EvalSt e} {S : ProtocolSt}
      {rest : Stream Γ t} →
    BurstInv {e = e} 0 sched st S →
    drain⇓ {e = e} fuel 1 sched st rest →
    ∃ λ S₂ → (runProtocol S rest ≡ just S₂) × (paidUp S₂ ≡ true)

------------------------------------------------------------------
-- THE COMPOSITION.  Two runs meeting at a state, which is exactly the
-- shape `Glue` is written for.
------------------------------------------------------------------

burst-drain-well-formed :
  ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t}
    (fuel : Fuel) (ins : Slots Γ) {burst rest : Stream Γ t} {sched′ st′} →
  subscribeE⇓ {e = e} {lo = n} e root 0 0 (sched-init e ins) (st-init e)
    (burst , sched′ , st′) →
  drain⇓ {e = e} fuel 1 sched′ st′ rest →
  WellFormed (burst ++ rest)
burst-drain-well-formed fuel ins {burst} {rest} s d
  with subscribeE-root-wf ins s
... | (_ , eq₁ , inv) with drain-wf fuel inv d
... | (S₂ , eq₂ , paid)
  rewrite run-++-just protocol-init burst rest eq₁ eq₂ = acceptPaid S₂ paid

-- and the top line, which is one match.  The builder hands over a run
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
