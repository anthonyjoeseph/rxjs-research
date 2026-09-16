-- SOUNDNESS: THE SEGMENT PREDICATE THE AUTOMATON'S RUN COMPOSES BY.
-- `Accepted (runProtocol protocol-init xs)` is a claim about one whole
-- stream from one fixed state, so it says nothing about a piece of one
-- and cannot be assembled from claims about pieces.  `Sound` is the
-- same claim with both endpoints removed: it runs from ANY state the
-- segment could legally be entered at and hands back a state the NEXT
-- segment can be entered at, which is what makes concatenation a lemma
-- rather than a coincidence.
--
-- WHY IT IS INDEXED BY TWO WATERMARKS AND NOT QUANTIFIED OVER EVERY
-- SANE STATE.  An instant id is an absolute arrival position, not a
-- relative offset, so a segment opening at instant `i` is rejected out
-- of any state whose watermark has already passed `i` -- the
-- freshness comparison is the automaton's, and it does not care that
-- the segment is otherwise impeccable.  A predicate quantified over
-- every sane state is therefore satisfied by NO segment that emits
-- anything at all, which is the trap: it reads as the strongest form
-- of the statement and is the empty one.  The entry bound is what
-- repairs it, and the exit bound is what the next segment needs to
-- have its own entry bound discharged.
--
-- WHAT `Sane` CARRIES, AND WHY IT IS NOT A POSTULATE.  A postulated
-- predicate here would be satisfiable by the empty one, under which
-- every stream is sound and the whole face asserts nothing -- the
-- upward-closed-witness trap wearing a different hat.  So it is
-- DEFINED, at the one invariant the automaton's own freshness check
-- reads.  It is expected to gain conjuncts as the operator cases are
-- written, and each one lands here rather than in a hypothesis.
module Rx.Protocol.Sound where

open import Data.List    using (List; []; _∷_; _++_)
open import Data.Maybe   using (just)
open import Data.Nat     using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-trans)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Rx.Prim using (Id; InstEmit)
open import Rx.Protocol using (ProtocolSt; Owed; protocol-init; stepProtocol;
  runProtocol; Accepted; accepted)

-- The automaton leaves an instant only through `settleInstant`, which
-- raises the watermark to the instant being left; so a state whose
-- open instant sits BELOW its own watermark is one no run can reach,
-- and a stream starting there is rejected for a reason about the
-- state rather than about the stream.
Sane : ProtocolSt → Set
Sane ps = ∀ (i : Id) (o : Owed) →
          ProtocolSt.current ps ≡ just (i , o) → ProtocolSt.horizon ps ≤ i

-- vacuous, and that is the content: the initial state has no open
-- instant, so there is nothing for the watermark to sit above
Sane-init : Sane protocol-init
Sane-init i o ()

-- A SEGMENT RUNS FROM WATERMARK `i` TO WATERMARK `j`.  No
-- `protocol-init`, so it is not about a whole stream; no final check,
-- so it is not about where a run stops.
--
-- IT IS A RECORD RATHER THAN A FUNCTION TYPE, AND THAT IS FORCED.  The
-- element type appears nowhere in the unfolding at the empty segment,
-- since the automaton's run over no emits is the state it was handed --
-- so a transparent definition leaves that parameter an unsolved meta at
-- every use of the empty law.  A record head is rigid, so the goal
-- pins it.
record Sound {A : Set} (i j : Id) (xs : List (InstEmit A)) : Set where
  field
    run : ∀ (ps : ProtocolSt) → Sane ps → ProtocolSt.horizon ps ≤ i →
          Σ ProtocolSt λ ps′ →
            (runProtocol ps xs ≡ just ps′) × Sane ps′ ×
            (ProtocolSt.horizon ps′ ≤ j)

Sound-[] : ∀ {A : Set} {i j : Id} → i ≤ j → Sound {A} i j []
Sound-[] i≤j .Sound.run ps sane hor = ps , refl , sane , ≤-trans hor i≤j

-- the run through a segment that succeeds is the run through its
-- pieces, which is what lets the concatenation below re-enter at the
-- state the first piece reached
runProtocol-split : ∀ {A : Set} (ps ps′ : ProtocolSt) (xs ys : List (InstEmit A)) →
  runProtocol ps xs ≡ just ps′ → runProtocol ps (xs ++ ys) ≡ runProtocol ps′ ys
runProtocol-split ps ps′ []       ys refl = refl
runProtocol-split ps ps′ (x ∷ xs) ys eq with stepProtocol x ps | eq
... | just ps₁ | eq′ = runProtocol-split ps₁ ps′ xs ys eq′

-- THE COMPOSITION LAW, AND IT IS THE WHOLE REASON FOR THE INDICES:
-- the first segment's EXIT bound is exactly the second's ENTRY bound,
-- so the two meet with nothing to prove between them.  This is the
-- shape `drain-step` already threads, which advances the instant
-- counter by one across each cascade.
Sound-++ : ∀ {A : Set} {i j k : Id} (xs ys : List (InstEmit A)) →
           Sound i j xs → Sound j k ys → Sound i k (xs ++ ys)
Sound-++ xs ys sx sy .Sound.run ps sane hor with Sound.run sx ps sane hor
... | ps′ , eq , sane′ , hor′ with Sound.run sy ps′ sane′ hor′
...   | ps″ , eq′ , sane″ , hor″ =
        ps″
      , subst (λ z → z ≡ just ps″) (sym (runProtocol-split ps ps′ xs ys eq)) eq′
      , sane″ , hor″

-- THE ONE PLACE A WHOLE-STREAM CLAIM REAPPEARS.  Everything above is
-- stated over segments; acceptance is recovered once, at the root, by
-- instantiating at the initial state -- whose watermark is the least
-- there is, so the entry bound is discharged for free and a run is
-- never asked where it may begin.
sound-accepted : ∀ {A : Set} {j : Id} (xs : List (InstEmit A)) →
                 Sound 0 j xs → Accepted (runProtocol protocol-init xs)
sound-accepted xs snd with Sound.run snd protocol-init Sane-init z≤n
... | ps′ , eq , _ , _ = subst Accepted (sym eq) accepted
