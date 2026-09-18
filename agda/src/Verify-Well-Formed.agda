-- THE PROTOCOL HALF OF THE SANDWICH, AND IT IS ONE STATEMENT OVER A
-- RUN.  `The-Proof` draws `evaluate-accepted` and nothing else from
-- this face: no emit of a canonical run is rejected by the protocol
-- automaton, which is what lets the batcher be quantified over legal
-- streams rather than arbitrary ones.
--
-- AND ACCEPTANCE IS THE WHOLE OF WHAT IS OWED (Anthony, asking for a
-- claim that does not read the evaluator).  This face used to owe a
-- second half — that a run stops on an instant boundary, every
-- obligation paid — and `batch-agreement` never had a use for it: it
-- took the conjunction and immediately weakened it back to acceptance.
-- A statement about where the MACHINE stops is the one thing here that
-- could not be restated over the stream, so retiring it is what leaves
-- this face saying something about a stream's contents alone.
module Verify-Well-Formed where

open import Data.Nat using (zero; suc; _+_)
open import Data.Product using (_,_; proj₂)
open import Data.Nat.Properties using (m≤m+n; +-suc)
open import Relation.Binary.PropositionalEquality using (sym; subst; trans; cong₂)

open import Rx.Prim using (Fuel)
open import Rx.Exp using (Ctx; Closed; []ᵉ; uniqᵗ)
open import Rx.Envelope using (instEmitᵗ)
open import Rx.Envelope.Decode using (decodeStream; decodeStream-++)
open import Rx.Slots using (Slots)
open import Rx.Evaluator using (root; sched-init; st-init)
open import Rx.Evaluator.Domain using (subscribeE⇓; cascade⇓; drain⇓; evaluate⇓;
  drain-done; drain-empty; drain-step; eval-run)
open import Rx.Evaluator.Builder using (evaluate↓; evaluate!)
open import Rx.Protocol using (protocol-init; runProtocol; Accepted)
open import Rx.Protocol.Sound using (Sound; Sound-[]; Sound-++; sound-accepted)

-- Every clause the automaton checks — instant freshness, bracketing,
-- fan-out exactness, complete discipline — is a promise the evaluator
-- makes while producing the stream, so this is the half that is
-- structural in how the run is BUILT.  It is also prefix-closed, since
-- `runProtocol` short-circuits on rejection, which is what makes it
-- the half a compositional reading could ever descend through.
--
-- A sampling sweep of 6200 programs over two depths, about a third
-- carrying `μᵉ`, found no refutation of the conjunction this was a
-- half of; the harness's `wellFormed?` is a decision procedure for
-- that conjunction, pinned to `git show a0d882c6:agda/src/QuickCheck.agda`.
-- Every row sits at a derivation the BUILDER produced, while the
-- statement quantifies over any at its indices --
-- `evaluate-deterministic` is the fact that would make those the same
-- set.
--
-- DEAD ROUTE: obtaining this from a well-formed denotation, by
--   quantifying a leaf over every prefix of a program's meaning and
--   instantiating it at the run.  That route was stated against the
--   conjunction, whose final check demands settledness AT THE CUT, and
--   an instant's obligations span several emits, so a cut between them
--   is rejected.  What is true of an arbitrary prefix is this
--   statement ALONE, which needs no domain to say.

-- THE SEGMENT FORM, AND IT IS STRICTLY STRONGER THAN WHAT IS ASKED FOR.
-- Acceptance is a whole-stream claim from one fixed state, so it
-- decomposes into nothing; soundness is the segment form, and a run
-- is a CONCATENATION -- its root subscribe followed by one cascade
-- per unit of fuel, which is what `evaluate⇓`'s single constructor
-- says.  So the statement that has a route down through the
-- evaluator is this one, and acceptance falls out of it at the root.
--
-- THE WATERMARK IT EXITS AT IS READ OFF THE DRAIN RATHER THAN CHOSEN:
-- the counter enters at one, since the root subscribe spends the
-- zeroth instant, and advances by one per cascade -- so a run of
-- `fuel` cascades cannot leave a watermark above its successor.
-- Stating the exit bound as an existential
-- instead would be the weaker statement that composes with nothing --
-- the next segment needs a NUMBER to discharge its own entry bound.
--
-- DEAD ROUTE: quantifying the segment predicate over every sane state
--   rather than indexing it by the entry watermark.  Instant ids are
--   absolute arrival positions, so a segment that emits anything at
--   all is rejected out of any state whose watermark has passed its
--   first instant -- the unindexed predicate is satisfied by no
--   segment with content, while reading as the strongest form of it.
--
-- RECOVERY: git show 9f5e3339:agda/src/Verify-Well-Formed.agda restores
--   the seam carve -- two leaves meeting at a named automaton state, the
--   `BurstInv` relation they were denominated in, and `Glue`'s fold law
--   composing their conclusions.

-- THE SHAPE THESE TWO ARE TO BE RESTATED IN, ONCE THE SIMUL TREE
-- EXISTS (Anthony): ONE CLAUSE PER OPERATOR, AND THE INDUCTION IS THE
-- SYNTAX'S.  Both statements below quantify over a derivation and over
-- nothing syntactic, which is why neither decomposes -- a cascade from
-- an arbitrary closed program is every former at once, so there is no
-- case to split on and no hypothesis to descend into.  The replacement
-- reads: for each operator, given a WELL-FORMED simul tree ending in
-- that operator, the plain-world evaluation of its elaboration is
-- sound.  Every subtree's own well-formedness is then the hypothesis
-- the statements below lack, and the operators are a finite shipped
-- set, so the induction covers every syntax an author can write.

-- AND THE PREMISE IS NOT BOILERPLATE -- IT IS WHERE THE FORGERY IS
-- QUARANTINED.  Once the envelope is a VALUE rather than the machine's
-- own output, any term that can write a unique can write an envelope
-- carrying whatever instant it likes, so soundness is outright FALSE
-- over the plain tree.  A simul tree is not automatically safe either,
-- because its non-observable positions take arbitrary plain terms -- a
-- mapping function is an author's own term.  Well-formedness is the
-- structural predicate saying those embedded terms mint nothing, and
-- it is closed under every former, which is what makes it an
-- induction rather than a side condition rechecked at each node.

-- SO THE SOUNDNESS HALF IS A SECOND RELATION, NOT A STRENGTHENING OF
-- THE EXISTING CANDIDATE.  That candidate is quantified over the plain
-- tree, where the conjunct is false, so it cannot carry this and stays
-- exactly as it is -- guard measure and accessibility argument
-- untouched, spent as a black box for the plain subtrees an
-- elaboration emits.

-- TWO THINGS THE RESTATEMENT OWES, AND NEITHER IS MECHANICAL.  The
-- exit watermark has to be READ OFF THE RUN rather than chosen, which
-- is what the ledger supplies: a segment exits at the counter its own
-- end state carries, so the indices compose without the existential
-- this file records as dead.  And a cascade RESUMES stored machinery
-- rather than subscribing, so the soundness half wants an invariant on
-- the evaluator's state where the payload half provably needed none --
-- the fan-out that carries no payload is exactly the registration
-- traffic the protocol reads.

-- THE TWO LEAVES THE RUN DECOMPOSES INTO, AND NEITHER IS AN ASSEMBLY.
-- A cascade is one instant's worth of emission, so it opens at the
-- counter it is handed and closes before the next -- which is the
-- watermark step the drain's own `suc nextId` threads.  The root
-- subscribe is the same claim at the seed: it is the only segment that
-- runs before the counter has advanced at all, so its entry is zero
-- and its exit is one.
--
-- PROBED: `Probed.Protocol-Segments` instantiates both at states a run
--   actually enters -- the subscribe at the initial state, the cascade
--   at the state that subscribe's own burst left -- over a synchronous
--   two-value source and over a one-slot scripted arrival.  What the
--   rows reach is the seed segment and the first cascade after it, so
--   the entry watermark covered is zero and the exit watermarks are one
--   and two.  They do not reach a watermark further along, which is the
--   region the entry index exists for and the one where freshness can
--   reject an otherwise impeccable segment; and they reach no former
--   beyond a synchronous source and a slot, so nothing here covers a
--   flattener, a share, or a cascade carrying more than one emit.
postulate
  sound-cascade :
    ∀ {n} {Γ : Ctx n} {u} {e : Closed Γ (instEmitᵗ uniqᵗ u)}
      {a id sched st out sched′ st′} →
    cascade⇓ {e = e} a id sched st (out , sched′ , st′) →
    Sound id (suc id) (decodeStream out)

  sound-subscribe :
    ∀ {n} {Γ : Ctx n} {u} (e : Closed Γ (instEmitᵗ uniqᵗ u)) (ins : Slots Γ)
      {burst sched₀ st₀} →
    subscribeE⇓ {e = e} {lo = n} (_ , e , []ᵉ) root 0 0
      (sched-init e ins) (st-init e) (burst , sched₀ , st₀) →
    Sound 0 1 (decodeStream burst)

-- THE DRAIN IS THE INDUCTION, AND THE INDEXING IS WHAT MAKES IT ONE.
-- Each constructor hands its tail a counter one higher than its own,
-- so the exit watermark of a drain carrying `fuel` units is its entry
-- plus that fuel -- and the arithmetic is the whole content of the
-- step case, since `Sound-++` already composes the two segments once
-- their indices meet.
sound-drain :
  ∀ {n} {Γ : Ctx n} {u} {e : Closed Γ (instEmitᵗ uniqᵗ u)}
    (fuel : Fuel) {id sched st rest} →
  drain⇓ {e = e} fuel id sched st rest → Sound id (id + fuel) (decodeStream rest)
sound-drain zero    {id = id} drain-done      = Sound-[] (m≤m+n id 0)
sound-drain (suc k) {id = id} (drain-empty _) = Sound-[] (m≤m+n id (suc k))
sound-drain _ (drain-step {k = k} {nextId = id} {out = out} {rest = rest}
                                  _ c d) =
  subst (Sound _ _) (sym (decodeStream-++ out rest))
    (Sound-++ (decodeStream out) (decodeStream rest) (sound-cascade c)
      (subst (λ z → Sound (suc id) z (decodeStream rest)) (sym (+-suc id k))
        (sound-drain k d)))

-- AND THE RUN IS THEIR CONCATENATION, WHICH IS WHAT `eval-run` SAYS.
-- The exit watermark is one above the fuel rather than the fuel: the
-- root subscribe spends the zeroth instant, so the drain starts at one
-- and every cascade after it is offset by that seed.
sound-run :
  ∀ {n} {Γ : Ctx n} {u} {fuel : Fuel} {e : Closed Γ (instEmitᵗ uniqᵗ u)}
    {ins : Slots Γ} {out} →
  evaluate⇓ fuel e ins out → Sound 0 (suc fuel) (decodeStream out)
sound-run (eval-run {burst = burst} {rest = rest} s d) =
  subst (Sound _ _) (sym (decodeStream-++ burst rest))
    (Sound-++ (decodeStream burst) (decodeStream rest)
      (sound-subscribe _ _ s) (sound-drain _ d))

evaluate-sound :
  ∀ {n} {Γ : Ctx n} {u} (fuel : Fuel) (e : Closed Γ (instEmitᵗ uniqᵗ u))
    (ins : Slots Γ) →
  Sound 0 (suc fuel) (decodeStream (evaluate↓ fuel e ins))
evaluate-sound fuel e ins = sound-run (proj₂ (evaluate! fuel e ins))

evaluate-accepted :
  ∀ {n} {Γ : Ctx n} {u} (fuel : Fuel) (e : Closed Γ (instEmitᵗ uniqᵗ u))
    (ins : Slots Γ) →
  Accepted (runProtocol protocol-init (decodeStream (evaluate↓ fuel e ins)))
evaluate-accepted fuel e ins =
  sound-accepted (decodeStream (evaluate↓ fuel e ins))
                 (evaluate-sound fuel e ins)
