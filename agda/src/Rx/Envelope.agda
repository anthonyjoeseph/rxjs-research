module Rx.Envelope where

open import Rx.Exp using (Ty; unitᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_; listᵗ)

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
