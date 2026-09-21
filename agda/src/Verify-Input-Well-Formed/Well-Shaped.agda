-- THE STREAM-ONLY HALF OF RUN SOUNDNESS.
--
-- `runProtocol` is a pure fold: `stepProtocol : InstEmit A → ProtocolSt
-- → Maybe ProtocolSt`, no lookahead, no input but the stream and its
-- own state.  So "this stream is accepted" can be characterised by an
-- inductive predicate over the stream ALONE, with the evaluator
-- nowhere in it -- and that is what this module is.
--
-- WHY THIS SHAPE, AND WHY IT IS NOT A GUESS.  Every earlier attempt at
-- a run-soundness invariant guessed a clause and was refuted by
-- measurement.  This one is DERIVED: `stepProtocol` has exactly seven
-- reachable sites at which it can return `nothing`, and `EmitOK`'s
-- premises are their complement, one for one.  The census, with the
-- two unreachable sites marked (`handoff` and `close _ cutPending` are
-- constructed nowhere in `Rx.Elaborate` -- only in `Rx.Envelope`'s
-- decoder):
--
--   1  settle delivery -> payOwed underflow     over-delivery      COUNT
--   2  settle delivery -> countIn s live = 0    unannounced source ORDER
--   3  applyEvents (value _) with done = true   value after end    ORDER
--   4  applyEvents (close ...) -> removeOne     unannounced close  ORDER
--   5  close _ cutPending -> cancelOwed         UNREACHABLE
--   6  handoff                                  UNREACHABLE
--   7  settleInstant -> allZero owed false      under-delivery     COUNT
--   8  openFresh -> horizon' <= i false         instants not fresh ORDER
--   9  enter -> paidOff owed true               emit after settle  COUNT
--
-- THREE OF THE SEVEN (1, 7, 9) ARE ONE SCALAR EQUATION seen from three
-- directions -- a source delivers, this instant, exactly as many times
-- as it has live announces.  That is the single place the evaluator's
-- state can reach the wire, and isolating it is this module's point.
-- The other four are ordering and bracketing facts about the stream.
--
-- WHAT THE SPLIT BUYS.  `emitOK-step` discharges `stepProtocol`'s
-- control flow -- the nested `with`s, `openFresh`, `enter` -- ONCE.
-- Whatever proves the evaluator's streams well-shaped never reasons
-- about `stepProtocol` again: only about `settle` and `applyEvents`,
-- which are plain folds.
module Verify-Input-Well-Formed.Well-Shaped where

open import Data.Bool  using (Bool; true; false)
open import Data.List  using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat   using (suc; _≤ᵇ_; _≡ᵇ_)
open import Data.Nat.Properties using ()
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Decide using (≡ᵇ-refl)
open import Rx.Prim using (Id; Source; InstEmit; _at_from_as_; InstEvent)
open import Rx.Protocol using (ProtocolSt; Owed; protocol-init; runProtocol; stepProtocol; settle; applyEvents; paidOff;
  allZero; Accepted; accepted)


------------------------------------------------------------------
-- plumbing
------------------------------------------------------------------

-- THE STATE, SPELLED OUT.  `stepProtocol` nests three `with`s -- on
-- `ProtocolSt.current ps`, then on `settleInstant ps`, then on
-- `settle`/`applyEvents` -- and a `with` or `rewrite` at the call site
-- abstracts NONE of the inner ones, because the terms they block on
-- are generated when `stepProtocol` reduces, not before.  Stating the
-- three step lemmas over a LITERAL record sidesteps all of it: with
-- `current` a constructor rather than a projection, every one of those
-- scrutinees is already a value and the whole chain computes.
-- `ProtocolSt` has eta, so gluing back to an abstract `ps` is one
-- `subst` over the one field the lemma fixed.
St : List Source → Id → Maybe (Id × Owed) → Bool → ProtocolSt
St l h c d = record { live = l ; horizon = h ; current = c ; done = d }

------------------------------------------------------------------
-- one emit
------------------------------------------------------------------

-- ONE EMIT'S OBLIGATIONS, indexed by the state it meets and the state
-- it leaves.  THREE CONSTRUCTORS, one per branch of `stepProtocol`'s
-- own `enter`, so that every premise is a fact the step literally
-- tests rather than a fact about a helper that then has to be
-- unfolded.  `settle` and `applyEvents` stay as equations in all
-- three: those are where sites 1-4 live, and an equation is the form
-- the eventual evaluator-side proof will produce, one fold at a time.
data EmitOK {A : Set} : ProtocolSt → InstEmit A → ProtocolSt → Set where

  -- THE OPEN INSTANT CONTINUES.  Site 9 is the `paidOff` premise: an
  -- instant that took on obligations and discharged them all is over,
  -- and a further emit into it is an error rather than a no-op.
  emit-same :
    ∀ {ps es i s k owed owed′ live′ owed″ done′}
    → ProtocolSt.current ps ≡ just (i , owed)
    → paidOff owed ≡ false
    → settle k s (ProtocolSt.live ps) owed ≡ just owed′
    → applyEvents es (ProtocolSt.live ps) owed′ (ProtocolSt.done ps)
        ≡ just (live′ , owed″ , done′)
    → EmitOK ps (es at i from s as k)
        (record { live = live′ ; horizon = ProtocolSt.horizon ps
                ; current = just (i , owed″) ; done = done′ })

  -- NOTHING IS OPEN: the stream's first emit, or the one after a
  -- cascade boundary.  Site 8 alone applies -- there is no departed
  -- instant to settle, so the horizon stands where it is.
  emit-open :
    ∀ {ps es i s k owed′ live′ owed″ done′}
    → ProtocolSt.current ps ≡ nothing
    → (ProtocolSt.horizon ps ≤ᵇ i) ≡ true
    → settle k s (ProtocolSt.live ps) [] ≡ just owed′
    → applyEvents es (ProtocolSt.live ps) owed′ (ProtocolSt.done ps)
        ≡ just (live′ , owed″ , done′)
    → EmitOK ps (es at i from s as k)
        (record { live = live′ ; horizon = ProtocolSt.horizon ps
                ; current = just (i , owed″) ; done = done′ })

  -- A DIFFERENT INSTANT IS OPEN and this emit leaves it.  Site 7 is
  -- `allZero owed` -- the departed instant discharged everything it
  -- owed, which is the UNDER-delivery direction of the count -- and
  -- site 8 is the `≤ᵇ` premise against the pushed horizon `suc j`.
  emit-next :
    ∀ {ps es i j s k owed owed′ live′ owed″ done′}
    → ProtocolSt.current ps ≡ just (j , owed)
    → (i ≡ᵇ j) ≡ false
    → allZero owed ≡ true
    → (suc j ≤ᵇ i) ≡ true
    → settle k s (ProtocolSt.live ps) [] ≡ just owed′
    → applyEvents es (ProtocolSt.live ps) owed′ (ProtocolSt.done ps)
        ≡ just (live′ , owed″ , done′)
    → EmitOK ps (es at i from s as k)
        (record { live = live′ ; horizon = suc j
                ; current = just (i , owed″) ; done = done′ })

-- the three step lemmas, each on a literal state
step-same :
  ∀ {A : Set} {l h d} {es : List (InstEvent A)} {i s k owed owed′ live′ owed″ done′}
  → paidOff owed ≡ false
  → settle k s l owed ≡ just owed′
  → applyEvents es l owed′ d ≡ just (live′ , owed″ , done′)
  → stepProtocol (es at i from s as k) (St l h (just (i , owed)) d)
      ≡ just (St live′ h (just (i , owed″)) done′)
step-same {i = i} peq seq aeq rewrite ≡ᵇ-refl i | peq | seq | aeq = refl

step-open :
  ∀ {A : Set} {l h d} {es : List (InstEvent A)} {i s k owed′ live′ owed″ done′}
  → (h ≤ᵇ i) ≡ true
  → settle k s l [] ≡ just owed′
  → applyEvents es l owed′ d ≡ just (live′ , owed″ , done′)
  → stepProtocol (es at i from s as k) (St l h nothing d)
      ≡ just (St live′ h (just (i , owed″)) done′)
step-open leq seq aeq rewrite leq | seq | aeq = refl

step-next :
  ∀ {A : Set} {l h d} {es : List (InstEvent A)} {i j s k owed owed′ live′ owed″ done′}
  → (i ≡ᵇ j) ≡ false
  → allZero owed ≡ true
  → (suc j ≤ᵇ i) ≡ true
  → settle k s l [] ≡ just owed′
  → applyEvents es l owed′ d ≡ just (live′ , owed″ , done′)
  → stepProtocol (es at i from s as k) (St l h (just (j , owed)) d)
      ≡ just (St live′ (suc j) (just (i , owed″)) done′)
step-next deq zeq leq seq aeq rewrite deq | zeq | leq | seq | aeq = refl

-- LEMMA B, AT ONE EMIT.  This is the whole of `stepProtocol`'s control
-- flow -- `enter`, `openFresh`, `settleInstant`, `go` -- discharged
-- once and for all.  Each arm is the matching step lemma, transported
-- along the one field the constructor pinned.
emitOK-step : ∀ {A : Set} {ps} {x : InstEmit A} {ps′}
            → EmitOK ps x ps′ → stepProtocol x ps ≡ just ps′
emitOK-step {A} {ps} {x = es at i from s as k} {ps′} (emit-same {owed = owed} ceq peq seq aeq) =
  subst (λ c → stepProtocol (es at i from s as k)
                 (St (ProtocolSt.live ps) (ProtocolSt.horizon ps) c
                     (ProtocolSt.done ps)) ≡ just ps′)
        (sym ceq)
        (step-same {l = ProtocolSt.live ps} {h = ProtocolSt.horizon ps}
                   {d = ProtocolSt.done ps} {es = es} {i = i} {s = s} {k = k}
                   {owed = owed} peq seq aeq)
emitOK-step {A} {ps} {x = es at i from s as k} {ps′} (emit-open ceq leq seq aeq) =
  subst (λ c → stepProtocol (es at i from s as k)
                 (St (ProtocolSt.live ps) (ProtocolSt.horizon ps) c
                     (ProtocolSt.done ps)) ≡ just ps′)
        (sym ceq)
        (step-open {l = ProtocolSt.live ps} {h = ProtocolSt.horizon ps}
                   {d = ProtocolSt.done ps} {es = es} {i = i} {s = s} {k = k}
                   leq seq aeq)
emitOK-step {A} {ps} {x = es at i from s as k} {ps′} (emit-next {j = j} {owed = owed} ceq deq zeq leq seq aeq) =
  subst (λ c → stepProtocol (es at i from s as k)
                 (St (ProtocolSt.live ps) (ProtocolSt.horizon ps) c
                     (ProtocolSt.done ps)) ≡ just ps′)
        (sym ceq)
        (step-next {l = ProtocolSt.live ps} {h = ProtocolSt.horizon ps}
                   {d = ProtocolSt.done ps} {es = es} {i = i} {j = j} {s = s}
                   {k = k} {owed = owed} deq zeq leq seq aeq)

------------------------------------------------------------------
-- a stream
------------------------------------------------------------------

-- THE LIST CLOSURE, INDEXED BY BOTH ENDS.  Carrying the output state
-- is what makes splicing free, and splicing is what the evaluator side
-- needs: a run is a subscribe burst followed by a drain, and a drain
-- is one cascade followed by a drain.
data WellShaped {A : Set} : ProtocolSt → List (InstEmit A) → ProtocolSt → Set where
  ws-nil  : ∀ {ps} → WellShaped ps [] ps
  ws-cons : ∀ {ps x ps′ xs ps″}
          → EmitOK ps x ps′ → WellShaped ps′ xs ps″ → WellShaped ps (x ∷ xs) ps″

-- splicing, and the reason for the second index
ws-++ : ∀ {A : Set} {ps ps′ ps″} {xs ys : List (InstEmit A)}
      → WellShaped ps xs ps′ → WellShaped ps′ ys ps″ → WellShaped ps (xs ++ ys) ps″
ws-++ ws-nil          w = w
ws-++ (ws-cons e ws)  w = ws-cons e (ws-++ ws w)

-- LEMMA B.  A well-shaped stream runs, and runs to the state the
-- derivation names -- an EQUATION, not an existential, which is what
-- lets callers compose without inventing a witness.
wellShaped-run : ∀ {A : Set} {ps ps′} {xs : List (InstEmit A)}
               → WellShaped ps xs ps′ → runProtocol ps xs ≡ just ps′
wellShaped-run ws-nil = refl
wellShaped-run {ps = ps} (ws-cons {x = x} e ws)
  rewrite emitOK-step e = wellShaped-run ws

-- and the form the top line asks for
wellShaped-accepted : ∀ {A : Set} {ps′} {xs : List (InstEmit A)}
                    → WellShaped protocol-init xs ps′
                    → Accepted (runProtocol protocol-init xs)
wellShaped-accepted ws rewrite wellShaped-run ws = accepted
