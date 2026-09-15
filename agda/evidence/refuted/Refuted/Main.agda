-- THE REFUTATION ROOT.  `make refuted` checks this module, and nothing
-- else reaches it: `make gate-heavy` compiles `src/Main.agda`, which cannot
-- import this tree, and `make wiring` scans `agda/src` only.
--
-- Naming each witness here is what keeps this tree honest: a refutation
-- that is not listed is not checked, exactly as in src/Main.agda.
--
-- Read the recovered witnesses' STATEMENTS and not their verdicts: each
-- killed a reading of a quantity the descent does not have, so what
-- transfers is the adversarial state a family was built to reach, never
-- the conclusion drawn from it.
--
-- AND THREE WITNESSES LEFT WITH THE ARM THEY REACHED, WHICH IS HOW A
-- REFUTATION IS MEANT TO DIE.  They killed the top-line dry claim, the
-- hop's unconditioned premise and the totality leaf's entry quantifier
-- — three readings of a rank the run computed — and `src` can no longer
-- STATE any of them, because the run computes no rank.  What they were
-- evidence about is now a proof obligation rather than an answer the
-- machine gives, so there is nothing left for them to be false of.
--
-- RECOVERY: git show 919f115:agda/evidence/refuted/Refuted/
-- RECOVERY: git show ba1285b:agda/evidence/refuted/Refuted/Dry-Wrap.agda
module Refuted.Main where

-- the shape a frame shelf was about to be written in, taken before the
-- statement existed.  No figure is claimed beside it, and that is what
-- makes it the widest witness left here: the crossing is not a pair of
-- numerals that could drift apart under a repair, it is a RATE proven
-- for every burst length, so the witness cannot go quiet while the
-- mechanism under it stands
open import Refuted.Scan-Deepens using (scan-bounded-false)

-- and the shape that survived it, killed in turn.  The three figures
-- are claimed because the crossing is their ORDER: the depth walks in
-- on the entry store, survives one delivery, and is gone from the exit
-- store — so a repair moving any single end would leave a witness
-- reporting numbers that no longer meet.  It is beside the climb rather
-- than folded into it because the two die to different repairs: a
-- figure growing with the burst answers the climb and leaves this one
-- open at a burst of two, where the template deepens nothing
open import Refuted.Exit-Store using (exit-bounded-false;
  entry-is; kept-is; store-is)

-- and the repair that reads BOTH ends, refuted in turn at a template
-- whose two arms are the other two witnesses'.  Its four figures are
-- claimed because the finding is that the peak clears all of them at
-- once: a repair moving any single one would leave a witness reporting
-- numbers that no longer meet.  What is left after this is a factor in
-- the burst's LENGTH, which is the only quantity none of the three
-- reads
open import Refuted.Exit-Store using (both-ends-false;
  rise-tmpl-is; rise-entry-is; rise-store-is; interior-is)

-- and the entry bound the door was going to be paid out of, asked of a
-- DERIVATION, which is the statement the builder actually spends.  Its
-- two figures are claimed because the finding is the gap between them:
-- the definition writes an observable and the reference standing for it
-- reads nought, so no repair reading the TERM can close this — which is
-- what says the conjunct owed is over the SCHEDULE.  Its two siblings
-- asked the same thing of the MACHINE and went when the cutover deleted
-- the machine they read; this one goes on holding against whatever the
-- relation is restated to say
open import Refuted.Carried-Derived using (carried-derived-false;
  derived-def-depth; derived-ref-depth)

-- and the escape the climb left open, closed from the other side: not
-- whether the accumulator deepens, which is settled, but whether a RUN
-- can stand that deep beside a burst that long.  It can, at a one-line
-- plain rxjs pipeline, so the route that dissolved the obligation by
-- restricting it to reachable configurations is dead.  Its three
-- figures are claimed because the finding is their relationship — two
-- burst lengths against one static reading that does not move — and the
-- positive bound beside them names the currency a repair has to be
-- written in, never that a repair in it is true
open import Refuted.Scan-Reachable using (static-bounds-run-false;
  rows₃; rows₅; static₃; static₅; length-bound)

-- and the leaf that was going to pay for the climb, refuted in the one
-- quantity none of the witnesses above reads: the burst's LENGTH.  Its
-- the rate is claimed because the finding is that it does not move —
-- one wrap per delivery, whatever the burst — so the demand is a count
-- set against a rank the premises never relate it to, and an ordinary
-- five-element burst clears it.  The escape of a wider bound is not
-- available: the two quantities are independent, so any burst longer
-- than the rank does the same
open import Refuted.Scan-Length using (scan-fits-false; rate-is)

-- and the template drop asked WITHOUT the data hypothesis, which is
-- what makes that hypothesis the statement rather than a convenience:
-- reifying an observable argument writes a `strmᵗ` the template never
-- wrote, so the emission is as deep as whatever was handed in and the
-- margin is unbounded rather than off by one
open import Refuted.Template-Passes using (template-strict-false;
  row-deep-handed; row-passes-template; row-passes-emitted)

-- and the arm that makes its own environment, which is where the
-- reading ITSELF was wrong rather than any statement over it.  A
-- `caseᵗ` binds what its scrutinee evaluated to, so a branch wrapping
-- that binder climbs on top of a nesting a join prices as an
-- alternative.  Its figures are claimed because the finding is the gap
-- between two of them and because the other three pin the candidate to
-- the reading `src` carries everywhere else: a move underneath breaks a
-- numeral rather than leaving this quiet
open import Refuted.Case-Binds using (case-join-false;
  scrut-is; left-is; right-is; joined-is; emission-is)


-- and the same climb in the COUNT rather than the depth, which is what
-- says the fold's leaf is owed in a currency the entry does not carry.
-- Its two lists are claimed because the finding is their crossing: the
-- run's peak doubles per delivery while the reading gains one per
-- literal, so the rows meet once and part for good — and the three
-- rows that HOLD are why the bound reads true from small cases.  A
-- repair moving either end alone leaves a witness reporting numbers
-- that no longer meet
open import Refuted.Burst-Length using (sync-bounds-burst-false;
  peaks-are; sizes-are)

-- and the share connect's own arithmetic, asked without knowing the
-- slot is shared.  It is the shallowest witness in this tree and the
-- only one that needs no program at all: the count is over SHARED
-- slots, so a `scripted` one reads nought either side and the strict
-- drop fails at a table of one with the set empty.  No figure is
-- claimed because the finding is that they AGREE: the two readings
-- are the same numeral, and the premise holds at its floor beside
-- them, so there is no crossing to pin and nothing an arithmetic
-- repair could sharpen.  A move under `unconn` breaks a numeral here
-- rather than leaving the witness quiet
open import Refuted.Scripted-Connect using (connect-drops-false;
  row-before; row-after; row-absent)

-- and the two above COMPOSED, which is the entry's own reading taken
-- against a run rather than a leaf's.  A fold that re-wraps its
-- accumulator deepens it once per delivery, and the cascade decides
-- how many deliveries an instant carries, so the deepest value a run
-- emits doubles across the family while the figure the caller fixed
-- before the run existed does not move at all.  Both lists are claimed
-- because the finding is again a crossing, and this one is the sharper
-- kind: one side is CONSTANT, so no multiple of the reading and no
-- wider syntactic measure closes it.  The first row HOLDS, which is
-- why a syntactic rank reads true from small programs
open import Refuted.Entry-Depth using (entry-depth-bounds-run-false;
  run-peaks-are; entry-reads-are; no-connect-edge)

-- and the repair those three invite, killed in its own currency
-- rather than in arithmetic.  If no number fixed before a run can
-- bound what the run emits, the move is to stop denominating the
-- descent in a number at all and carry a domain predicate -- and the
-- only shape of one this evaluator could USE, since it cases on the
-- term and needs the child's proof, is the structural one, which is
-- `⊤`.  `sub-total` is claimed beside the refutation because it is
-- the whole content: the predicate is inhabited by plain recursion on
-- the term, so holding one is holding a copy of the term
open import Refuted.Domain-Predicate using
  (structural-domain-has-content-false; sub-total)
