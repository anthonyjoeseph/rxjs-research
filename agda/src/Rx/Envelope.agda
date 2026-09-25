-- THE ANCHOR FOR THE IMPL ENVELOPE'S ABANDONED SHAPES, AND THEY FORM A
-- TREE CARRIED IN THE KEYS, NOT IN INDENTATION (Anthony).  One entry
-- each, keyed by a path -- `envelope/<question>/<route>: what
-- structurally blocked it; row N @ <sha>.` -- so that
-- `make find-prose Q='envelope/owed'` returns a whole subtree, where a
-- nested comment would lose its parent under grep.  The interior nodes
-- are the design questions: where the owed count lives, what triggers
-- the flush, how completion is signalled.  The row is the bug-cache
-- row that killed the shape, by index, with the SHA of the shape it
-- killed: that row passes under the next shape, so it cannot stay a
-- failing row, and the entry is what remembers it.
--
-- DEAD ROUTE envelope/lane/book-last: running the re-stamped outer
--   envelope AFTER the lane's inner streams moves its instant's first
--   appearance behind the values it caused, and the spec orders a burst's
--   batches by first appearance, value-less emits included, so the batches
--   come out permuted; row 9 @ 0de565ef.
-- DEAD ROUTE envelope/flush/end-mark: a mark emitted after an arrival, for
--   the root to read as its end, is an OUTER emit wherever its path
--   crosses a flattener -- `switchAllᵉ` cuts the live lane on it,
--   `exhaustAllᵉ` drops it while busy, a bounded `mergeAllᵉ` queues it.
--   Filtering it out before the outer loses it, and no in-body multicast
--   exists to route it around.  Row 4 is the program it had to fix.
-- DEAD ROUTE envelope/flush/root-merge: bracketing the subscribe burst as
--   `mergeAllᵉ` of the run and a one-emit `ofᵉ` puts a flattener above the
--   whole run, and the evaluator's cost is multiplicative in flattener
--   nesting (`typecheck-performance-numbers.md`), so it costs more than
--   the `batchSyncᵉ` it replaces.
-- DEAD ROUTE envelope/flush/sentinel-registration: a registration read as
--   the last of its arrival stays last only until something registers
--   after it -- the registry is appended and dispatched oldest-first, a
--   `deferᵉ` re-registration lands a tick late, and a cold slot has one
--   timeline per registration, so no one registration closes them all.
module Rx.Envelope where

open import Data.Bool using (true; false)
open import Data.List using (_∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Exp using (Ty; Ctx; Tm; unitᵗ; boolᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ;
                          varᵗ; unit̂; bool̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ;
                          inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; letᵗ; revᵗ; appendᵗ;
                          renTm; ext∈)

------------------------------------------------------------------
-- The protocol envelope, as a TYPE of the object language.
------------------------------------------------------------------

-- THE ENVELOPE STOPS BEING THE MACHINE'S AND BECOMES THE PROGRAM'S.
-- `Rx.Prim` declares the same four shapes in Agda, where they are the
-- return type of the evaluator and so are minted by the machine on
-- every emit whether the program asked for one or not.  Here they are
-- ordinary types the author-facing tree ELABORATES into, so an emit
-- carrying an envelope is an emit whose payload happens to be a tuple
-- and the evaluator owes nothing.  Nothing is duplicated between the
-- two: the meta-level record stays for the acceptance oracle and the
-- spec, which read a finished stream, while these are what a running
-- program manipulates.
--
-- THE TOKEN FIELDS STAND AT A TYPE PARAMETER AND NOT AT `natᵗ`, WHICH
-- IS THE WHOLE POINT OF THE ENCODING.  Instantiated at `uniqᵗ` the
-- fields are unforgeable, since no simul former reaches the only term
-- that makes one and the only eliminator is an equality; instantiated
-- at `unitᵗ` the very same shapes are what an AUTHOR may write, because
-- the sole inhabitant is `tt` and a slot standing there can carry no
-- claim about provenance at all.  One vocabulary, two instantiations,
-- and the difference between the machine's envelope and the author's is
-- a type argument rather than a second family.
--
-- THE PAYLOAD-FREE CASES ARE SPELLED AS NESTED SUMS OF `unitᵗ` because
-- the object language has no enumeration former and adding one would
-- cost a clause in every walk over `Ty` for no new expressive power.
-- Reading them is `caseᵗ`, twice, which is what a three-way match on
-- the meta-level datatype already compiles to.

-- cut / cutPending / exhausted
closeReasonᵗ : Ty
closeReasonᵗ = unitᵗ +ᵗ (unitᵗ +ᵗ unitᵗ)

-- subscribe / delivery / plumbing
emitKindᵗ : Ty
emitKindᵗ = unitᵗ +ᵗ (unitᵗ +ᵗ unitᵗ)

-- init / value / close / handoff / complete, at the token type `u` and
-- the payload type `a`.  `close` carries the source it ended and why;
-- `handoff` the source fanning out next; `complete` nothing.
instEventᵗ : Ty → Ty → Ty
instEventᵗ u a = u +ᵗ (a +ᵗ ((u ×ᵗ closeReasonᵗ) +ᵗ (u +ᵗ unitᵗ)))

-- events, then instant, then source, then kind — the field order of the
-- meta-level record, right-nested.
instEmitᵗ : Ty → Ty → Ty
instEmitᵗ u a = listᵗ (instEventᵗ u a) ×ᵗ (u ×ᵗ (u ×ᵗ emitKindᵗ))

-- what the MACHINE's emits stand at: tokens no program can write.  The
-- author's instantiation has no name yet because nothing stands at it
-- yet — the slot types that will are the purity ruling's, and a
-- definition minted ahead of its consumer is one nothing checks.
machineEmitᵗ : Ty → Ty
machineEmitᵗ a = instEmitᵗ uniqᵗ a


------------------------------------------------------------------
-- The envelope, as TERMS: the constructors and the one eliminator.
------------------------------------------------------------------

-- WITHOUT THESE THE TYPES ABOVE ARE UNUSABLE, AND THE REASON IS THAT
-- THE ENCODING IS NESTED SUMS.  Reading an event means `caseᵗ` four
-- times deep and weakening each arm past the scrutinees above it;
-- writing one means three `inrᵗ`s and remembering which.  Every
-- elaborated operator does both, so spelled out at each site the arm
-- order would be a convention held by eye across a tree of large
-- terms, and a `close` written where a `handoff` was meant typechecks.
-- Named here it is one definition, and every site reads as the arms it
-- names.

-- the five events.  `a` is the payload type, `u` the token type.
initᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
      → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
initᵛ tok = inlᵗ tok

valueᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
       → Tm Γ Δᵍ Δ Θ a → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
valueᵛ v = inrᵗ (inlᵗ v)

closeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
       → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ Θ closeReasonᵗ
       → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
closeᵛ tok r = inrᵗ (inrᵗ (inlᵗ (pairᵗ tok r)))

handoffᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
         → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
handoffᵛ tok = inrᵗ (inrᵗ (inrᵗ (inlᵗ tok)))

completeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a} → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
completeᵛ = inrᵗ (inrᵗ (inrᵗ (inrᵗ unit̂)))

-- insert one variable UNDER the head binder: what an arm of a nested
-- `caseᵗ` owes for each scrutinee bound above it.
wkᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s w r}
    → Tm Γ Δᵍ Δ (s ∷ Θ) r → Tm Γ Δᵍ Δ (s ∷ w ∷ Θ) r
wkᵛ = renTm (λ x → x) (λ x → x) (ext∈ there)

-- the eliminator: one arm per event, each binding exactly what that
-- event carries, so a reader checks the arms against the constructors
-- above rather than against a sum's shape.
eventCaseᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a r}
           → Tm Γ Δᵍ Δ Θ (instEventᵗ u a)
           → Tm Γ Δᵍ Δ (u ∷ Θ) r                      -- init: the token
           → Tm Γ Δᵍ Δ (a ∷ Θ) r                      -- value: the payload
           → Tm Γ Δᵍ Δ ((u ×ᵗ closeReasonᵗ) ∷ Θ) r    -- close: token and why
           → Tm Γ Δᵍ Δ (u ∷ Θ) r                      -- handoff: the token
           → Tm Γ Δᵍ Δ (unitᵗ ∷ Θ) r                  -- complete: nothing
           → Tm Γ Δᵍ Δ Θ r
eventCaseᵛ ev onInit onValue onClose onHandoff onComplete =
  caseᵗ ev onInit
    (caseᵗ (varᵗ (here refl)) (wkᵛ onValue)
      (caseᵗ (varᵗ (here refl)) (wkᵛ (wkᵛ onClose))
        (caseᵗ (varᵗ (here refl)) (wkᵛ (wkᵛ (wkᵛ onHandoff)))
                                  (wkᵛ (wkᵛ (wkᵛ onComplete))))))

-- an emit's four fields, and how one is built.  Right-nested, so the
-- projections are a chain of `sndᵗ` and spelling them out at a use site
-- says nothing about which field was meant.
eventsᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
        → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a) → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ u a))
eventsᵛ e = fstᵗ e

instantᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
         → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a) → Tm Γ Δᵍ Δ Θ u
instantᵛ e = fstᵗ (sndᵗ e)

sourceᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
        → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a) → Tm Γ Δᵍ Δ Θ u
sourceᵛ e = fstᵗ (sndᵗ (sndᵗ e))

kindᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
      → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a) → Tm Γ Δᵍ Δ Θ emitKindᵗ
kindᵛ e = sndᵗ (sndᵗ (sndᵗ e))

instEmitᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a}
          → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ u a))
          → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ Θ emitKindᵗ
          → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a)
instEmitᵛ evs inst src k = pairᵗ evs (pairᵗ inst (pairᵗ src k))

------------------------------------------------------------------
-- The two halves of every elaborated operator's envelope handling.
------------------------------------------------------------------

-- SPLITTING IS A REBUILD AND NOT A FILTER, WHICH IS THE ONE THING THIS
-- MIRROR DOES NOT SHARE WITH ITS TYPESCRIPT TWIN.  An event's TYPE
-- mentions the payload, so the bookkeeping of an incoming emit does not
-- typecheck in an outgoing one whose payload type differs — a `close`
-- means the same thing on both sides and is still a different term.
-- So the pass that peels the payloads out retags everything it keeps,
-- and an operator changing the payload type gets that for free rather
-- than owing a second walk.
splitEventsᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a b}
             → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ u a))
             → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ u b) ×ᵗ (listᵗ a ×ᵗ boolᵗ))
splitEventsᵛ {Θ = Θ} {u = u} {a = a} {b = b} evs =
  letᵗ (foldᵗ evs seed body) seed unreverse
  where
  -- the bookkeeping and the payloads, both reversed while the fold runs
  Acc : Ty
  Acc = listᵗ (instEventᵗ u b) ×ᵗ (listᵗ a ×ᵗ boolᵗ)

  seed : Tm _ _ _ Θ Acc
  seed = pairᵗ nilᵗ (pairᵗ nilᵗ (bool̂ false))

  body : Tm _ _ _ (instEventᵗ u a ∷ Acc ∷ Θ) Acc
  body = eventCaseᵛ (varᵗ (here refl))
    (keep (initᵛ (varᵗ (here refl))))
    (pairᵗ (fstᵗ acc)
           (pairᵗ (consᵗ (varᵗ (here refl)) (fstᵗ (sndᵗ acc)))
                  (sndᵗ (sndᵗ acc))))
    (keep (closeᵛ (fstᵗ (varᵗ (here refl))) (sndᵗ (varᵗ (here refl)))))
    (keep (handoffᵛ (varᵗ (here refl))))
    (pairᵗ (fstᵗ acc) (pairᵗ (fstᵗ (sndᵗ acc)) (bool̂ true)))
    where
    -- inside an arm: the event's own payload, then the fold's element
    -- and accumulator, then Θ
    acc : ∀ {x} → Tm _ _ _ (x ∷ instEventᵗ u a ∷ Acc ∷ Θ) Acc
    acc = varᵗ (there (there (here refl)))

    keep : ∀ {x} → Tm _ _ _ (x ∷ instEventᵗ u a ∷ Acc ∷ Θ) (instEventᵗ u b)
         → Tm _ _ _ (x ∷ instEventᵗ u a ∷ Acc ∷ Θ) Acc
    keep ev = pairᵗ (consᵗ ev (fstᵗ acc)) (sndᵗ acc)

  unreverse : Tm _ _ _ (Acc ∷ Θ) Acc
  unreverse = pairᵗ (revᵗ (fstᵗ (varᵗ (here refl))))
                    (pairᵗ (revᵗ (fstᵗ (sndᵗ (varᵗ (here refl)))))
                           (sndᵗ (sndᵗ (varᵗ (here refl)))))

-- and the other half: the events in the protocol's normalized order —
-- bookkeeping, then the payloads, then the completion if this emit is
-- the one carrying it — under the incoming envelope's own instant,
-- source and kind, none of which an operator of this shape may change.
reassembleᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ u a b}
            → Tm Γ Δᵍ Δ Θ (instEmitᵗ u a)
            → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ u b))
            → Tm Γ Δᵍ Δ Θ (listᵗ b) → Tm Γ Δᵍ Δ Θ boolᵗ
            → Tm Γ Δᵍ Δ Θ (instEmitᵗ u b)
reassembleᵛ env book vals fin =
  instEmitᵛ (appendᵗ book (appendᵗ payloads ending))
            (instantᵛ env) (sourceᵛ env) (kindᵛ env)
  where
  payloads = foldᵗ (revᵗ vals) nilᵗ (consᵗ (valueᵛ (varᵗ (here refl)))
                                           (varᵗ (there (here refl))))
  ending = ifᵗ fin (consᵗ completeᵛ nilᵗ) nilᵗ
