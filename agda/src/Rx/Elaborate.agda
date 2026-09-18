module Rx.Elaborate where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality using (subst; refl)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; listᵗ; obs; _×ᵗ_; boolᵗ; natᵗ; uniqᵗ; input; ofᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  mapᵉ; scanᵉ; varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ;
  foldᵗ; ifᵗ; primᵗ; strmᵗ; letᵗ; revᵗ; renTm; renExp; ext∈; add; sub; mul; eqᵖ; ltᵖ; eqᵘ;
  notᵖ)
open import Rx.Envelope using (instEventᵗ; closeReasonᵗ; emitKindᵗ; eventsᵛ;
                               splitEventsᵛ; reassembleᵛ; instEmitᵛ; initᵛ;
                               valueᵛ; closeᵛ; completeᵛ)
open import Rx.SExp using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ;
                           mergeAllˢ; switchAllˢ; exhaustAllˢ; μˢ; varˢ; deferˢ;
                           varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ;
                           consˢ; inlˢ; inrˢ; caseˢ; foldˢ; ifˢ; primˢ; strmˢ;
                           plainᵗ; plainᶜ; emitᵗ; emitᶜ; emitᵛ)

------------------------------------------------------------------
-- The per-former plumbing the elaboration is a composition of.
------------------------------------------------------------------

-- WHAT THE PLAIN TREE CANNOT SAY, STATED ONE FORMER AT A TIME.  The
-- elaboration below is a real body, so every gap it has is a leaf here
-- with a signature, a name and a ledger row, rather than a paragraph
-- saying the body cannot be written.  The split the body makes is the
-- product of this leg: the STRUCTURE — every binder, both variable
-- cases, the whole of the author's term language and the type walk the
-- four contexts run over — needs nothing new and is written out; what
-- is left is the protocol traffic of six formers, and every one of them
-- is short a capability of the same two kinds.

-- MINTING IS THE FIRST KIND, AND WHAT IT COSTS IS PLACEMENT RATHER
-- THAN A FORMER.  A source coming alive owes an `init` naming a token
-- nothing has used, and the term language has no former at `uniqᵗ` at
-- all — a term that made a token would be a literal, and a program
-- that could write a token could forge a collision.  A token is drawn
-- from a BINDER, and a binder reads as one token per subscription
-- while a source owes one per time it comes alive; those are the same
-- arity, since coming alive IS being subscribed, and a mint standing
-- at an INNER's head is subscribed once per outer value, so the binder
-- reaches a per-delivery token too.  What the sources are short of is
-- therefore not a draw.

-- READING THE RUNNING INSTANT IS THE SECOND, AND WHICH INSTANT IS
-- WANTED DECIDES WHETHER IT IS REACHABLE.  Downstream of a source the
-- instant is not missing at all: the incoming emit IS an envelope, a
-- term can project its instant field, and a step that stamps its
-- output with the instant it was handed is an ordinary `Tm`.  A former
-- with NO input has nothing to read it off — but the two sources want
-- the SUBSCRIBE FRAME's instant and no other, since a cold's whole
-- emission leaves in one burst, and a frame is exactly what one token
-- bound above the walk names.  So the sources are written, and what is
-- left wanting an instant is the traffic a flattener forwards from a
-- LATER cascade, where no binder has the right arity.

-- FORWARDING IS THE THIRD KIND AND IT IS THE FLATTENERS' ALONE.  Their
-- values need nothing missing — a map projects each envelope to the
-- observables it carries and the plain flattener runs them — but an
-- operator delegating that way has CONSUMED the envelope, and the
-- outer's own bookkeeping goes with it.  Each row below says what that
-- costs at its own operator; between them they rule out every place
-- the plain palette offers to put traffic which must survive a cut, a
-- drop and a concurrency limit.

-- `takeᵖ` IS THE ONE GENUINE SURPRISE, AND IT IS NEITHER KIND.  The
-- author's operator and the plain one agree on everything that was in
-- doubt — both cut naively on values, mid-batch, and both owe the
-- closing envelope at the cut.  What they do not share is the LEVEL:
-- elaboration puts the author's values inside the envelope, so a plain
-- `takeᵉ` over an enveloped stream counts batches.

postulate
  -- THE ONE GAP THAT IS NEITHER A MINT NOR A READ, AND IT IS A LEVEL
  -- SHIFT.  A simul `take` cuts naively on the author's VALUES —
  -- mid-batch, without waiting for one to finish, and sending the
  -- closing envelope at the moment it cuts.  That is `takeᵉ`'s own
  -- behaviour exactly, down to truncating the arriving list and minting
  -- a close per victim on the cutting burst.  What it is not is
  -- `takeᵉ` AT THIS TYPE: elaboration puts the author's values inside
  -- the envelope, so an enveloped stream's own values are envelopes and
  -- a plain `takeᵉ` over it counts batches.  The operator is right and
  -- the level is wrong.
  -- DEAD ROUTE: count in a scan and cut with `takeᵉ`.  The counting and
  --   truncation halves are both a pure-function step's work; the ENDING
  --   half is not, since such a step cannot change how many emits pass
  --   through it, so nothing converts a budget over values into the emit
  --   index a subscription-time count has to name.
  takeᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
        → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ (emitᵗ t) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- AN AMBIENT INSTANT IS STILL WANTED HERE, AND THESE TWO ROUTES TO
  -- ONE ARE DEAD.  The subscribe frame is reached by a root `mintᵉ`,
  -- which is what the two sources stand on; a LATER cascade's instant
  -- is not, and a flattener is where two of them meet.
  -- DEAD ROUTE: bracket the frame with `batchSyncᵉ` AT A SOURCE and let
  --   the grouping stand in for the id.  It brackets a frame without
  --   NAMING one, and the bracket is per node, so two colds subscribed
  --   in one frame group separately and nothing joins the two groups.
  --   The bracket at a JOIN is a different route and is not refuted
  --   here: the flatteners are the only nodes where two sources meet,
  --   so a bracket there sees both bursts in one group.  What that
  --   reaches is the subscribe frame alone, since `batchSyncᵉ` hands
  --   every later value out as a singleton.
  -- DEAD ROUTE: build the id inline, out of a `mintᵉ`-bound token and a
  --   counter carried in a scan's state.  The MINT half of this is not
  --   what fails: a mint at an inner's head is subscribed once per
  --   outer value, so a draw per delivery is reachable.  What fails is
  --   the counter, and it fails on its own terms -- a scan's state
  --   advances per EMIT, so it cannot tell two emits of one cascade
  --   from two cascades, which is a property of the RUN and the run is
  --   the scheduler's.  A per-delivery draw does not repair that: it
  --   gives every delivery a DISTINCT id where the whole content of an
  --   instant is which deliveries SHARE one.

  -- the VALUES need nothing new: a map projects each envelope to the
  -- observables it carries, and the plain flattener runs them, their own
  -- emits being envelopes already.
  --
  -- AND THE ENVELOPE APPEARS TWICE IN THE ARGUMENT, WHICH IS EASY TO
  -- READ PAST AND CHANGES WHAT THE BLOCKER IS ABOUT.  `emitᵗ (obs t)`
  -- unfolds through `plainᵗ`'s observable clause, so the outer's
  -- payload is an observable of ENVELOPES and not of values: the
  -- argument is an enveloped stream of enveloped streams.  Both layers
  -- are already stamped when they arrive, which is why nothing below is
  -- a question about minting a token -- the inner's bookkeeping rides
  -- the inner's own emits, and only the OUTER's has nowhere to go.
  --
  -- THE MINT IS NOT WHAT BLOCKS THIS.  An inner observable is a CLOSED
  -- EXPRESSION, and subscribing one runs it through the same reduction
  -- path the outer subscribe took, `mintᵉ` clause included — so a mint
  -- at an inner's head draws a fresh token on every inner subscription,
  -- which is the dynamic count a flattener was said to need and to be
  -- unable to get.  The token is the INNER's to draw and never the
  -- flattener's, which is the division the TypeScript twin runs under,
  -- where the join mints nothing at all.  Nor does a flattener owe any
  -- of the three events it might: an inner's `init` and its exhausted
  -- `close` ride the inner's own burst, a switch's cancelling closes
  -- are `cutThrough`'s and are read off the registrations whose chain
  -- passes the node, and a `handoff` is a SHARE's announcement.
  --
  -- WHAT BLOCKS IT IS THE OUTER'S OWN BOOKKEEPING, WHICH IS TRAFFIC TO
  -- FORWARD RATHER THAN TRAFFIC TO WRITE.  Those events arrive already
  -- stamped, so nothing about an instant is missing; what is missing is
  -- anywhere to put them.  The TypeScript twin reassembles every output
  -- emit out of the carrier's bookkeeping together with the inner burst
  -- it caused, so an outer emit carrying NO observable still produces
  -- an emit — and the shape below produces none, which is a divergence
  -- decided by a program with a valueless outer emit rather than by any
  -- argument about tokens.
  -- DEAD ROUTE: elaborate the handoff and init events in the projecting
  --   map, which has the outer emit's instant but no token to name the
  --   inner source with.
  -- DEAD ROUTE: project the payloads with a `mapᵉ` and hand them to the
  --   plain flattener.  The map is the only consumer of the envelope,
  --   so the bookkeeping is consumed with it and every valueless outer
  --   emit vanishes.
  -- DEAD ROUTE: carry that bookkeeping on a LANE of the flattener, as a
  --   singleton observable emitted beside the payloads or prepended to
  --   the first of them.  A lane is what the concurrency argument
  --   COUNTS, so at `just 1` the bookkeeping queues behind a running
  --   inner; and a lane is what the two cutting flatteners dispose of,
  --   so a switch cuts it and an exhaust drops it.  The traffic that
  --   must not be lost is put in the one place each operator is free to
  --   discard.
  -- DEAD ROUTE: split the outer into a bookkeeping stream and a value
  --   stream and merge the two results.  Two consumers are two
  --   SUBSCRIPTIONS, so a cold outer runs twice; one subscription
  --   feeding two consumers is a share, and share identity is a BINDING
  --   rather than an expression, so no `Exp` former reaches one from
  --   inside an operator's body.
  mergeAllᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → Maybe ℕ → Exp Γ Δᵍ Δ Θ (emitᵗ (obs t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- the two cutting flatteners, blocked where `mergeAllᵖ` is — which is
  -- the outer's own bookkeeping, and sharply so: these two DISPOSE of
  -- lanes, so bookkeeping riding one is cut by a switch and dropped by
  -- an exhaust rather than merely delayed.  The `close` a switch owes
  -- the registration it drops is not a second blocker: the plain
  -- evaluator already mints those closes off the registration set, one
  -- per chain passing the node, with the per-victim reason decided by
  -- the cut ledger, and the elaboration inherits them by delegating
  -- rather than by writing any.
  -- DEAD ROUTE: the projecting step again — it sees the emit that causes
  --   the switch, and not the source being cut.
  switchAllᵖ exhaustAllᵖ :
              ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → Exp Γ Δᵍ Δ Θ (emitᵗ (obs t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

-- THE TWO ARMS OF A NESTED SUM THAT THIS ELABORATION NAMES, AND THEY
-- ARE HERE RATHER THAN BESIDE THE ENCODING BECAUSE ONE ELABORATION IS
-- THEIR ONLY CONSUMER.  `Rx.Envelope` owes the constructors, which
-- every operator needs; which REASON a source closes for and which
-- KIND of emit a subscribe burst is are this walk's vocabulary.
exhaustedᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Tm Γ Δᵍ Δ Θ closeReasonᵗ
exhaustedᵛ = inrᵗ (inrᵗ unit̂)

subscribeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Tm Γ Δᵍ Δ Θ emitKindᵗ
subscribeᵛ = inlᵗ unit̂

-- a run of `value` events, in order, ahead of whatever closes the list
valuesᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
        → List (Tm Γ Δᵍ Δ Θ a)
        → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ uniqᵗ a))
        → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ uniqᵗ a))
valuesᵛ []       rest = rest
valuesᵛ (v ∷ vs) rest = consᵗ (valueᵛ v) (valuesᵛ vs rest)

-- A COLD SOURCE IS ONE ENVELOPE, WHICH IS WHY THE FRAME TOKEN IS THE
-- WHOLE OF WHAT IT WAS SHORT OF.  Everything this former emits leaves
-- in the subscribe burst — the `init` naming the source, every value
-- the author wrote, the exhausted `close` and the `complete` — so the
-- one instant it has to name is the frame's, and a source that
-- INHERITED a later cascade's would be naming something it can never
-- be handed.  The mirror settles the field order and the kind:
-- `primitive-operators.ts`'s `of` builds exactly this list, stamps it
-- `SUBSCRIBE_FRAME`, and marks the emit `subscribe`.
--
-- THE SOURCE TOKEN IS MINTED AT THIS NODE AND THE INSTANT IS NOT, AND
-- the difference is the arity.  A source is a fresh identity per
-- subscription, which is `mintᵉ`'s own arity, so it is bound here; the
-- frame is one identity for every source alive in the same frame, so it
-- is bound once above the whole walk and read here.  Two colds side by
-- side therefore get two sources and one instant, which is what the
-- spec's grouping compares.
ofᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
    → Tm Γ Δᵍ Δ Θ uniqᵗ
    → List (Tm Γ Δᵍ Δ Θ (plainᵗ t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
ofᵖ {Θ = Θ} {t = t} frame ts = mintᵉ (ofᵉ (instEmitᵛ evs frame↑ src subscribeᵛ ∷ []))
  where
  ↑ : ∀ {r} → Tm _ _ _ Θ r → Tm _ _ _ (uniqᵗ ∷ Θ) r
  ↑ = renTm (λ x → x) (λ x → x) there

  src : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  src = varᵗ (here refl)

  frame↑ : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  frame↑ = ↑ frame

  evs : Tm _ _ _ (uniqᵗ ∷ Θ) (listᵗ (instEventᵗ uniqᵗ (plainᵗ t)))
  evs = consᵗ (initᵛ src)
              (valuesᵛ (map ↑ ts)
                       (consᵗ (closeᵛ src exhaustedᵛ) (consᵗ completeᵛ nilᵗ)))

-- THE EMPTY SRXJS SOURCE IS NOT THE EMPTY PLAIN ONE, and the gap is
-- one envelope rather than one event: it still brackets a subscribe
-- frame, so it emits an `init` and a `complete` where `emptyᵉ` emits
-- nothing at all.  It is `ofᵖ` at no values, which is what the mirror
-- writes too.
emptyᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
       → Tm Γ Δᵍ Δ Θ uniqᵗ → Exp Γ Δᵍ Δ Θ (emitᵗ t)
emptyᵖ frame = ofᵖ frame []

-- THE TWO FORMERS OF THIS LEG THAT WERE NEVER BLOCKED, AND WRITING
-- THEM IS WHAT SAYS SO.  Neither adds an event, mints anything or can
-- end the stream, so everything either needs is in the emit it was
-- handed: the payloads come out of the envelope, the author's step runs
-- over them, and what goes back in is the same envelope with new
-- payloads.  The instant is not missing here — it is READ off the
-- incoming emit, which is the finding the source rows above turn on.
--
-- ONE AUTHOR VALUE IS ONE PAYLOAD AND NOT ONE DELIVERY, which is the
-- whole of why these are folds rather than applications.  A plain emit
-- carries a LIST, so the author's pointwise step runs once per element
-- inside an emit and the plain former runs once per emit — two levels,
-- and the `letᵗ`s are how a term language with no application hands an
-- argument to a step.  The reversing pass each `foldᵗ` costs is paid
-- once per level.
mapᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t : Ty}
     → Fn Γ Δᵍ Δ Θ (plainᵗ s) (plainᵗ t)
     → Exp Γ Δᵍ Δ Θ (emitᵗ s) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
mapᵖ {Θ = Θ} {s = s} {t = t} f e = mapᵉ step e
  where
  -- the split of one emit: its bookkeeping already retagged at the
  -- outgoing payload, its payloads, and whether it completes
  S : Ty
  S = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ (plainᵗ s) ×ᵗ boolᵗ)

  arg : Tm _ _ _ (emitᵗ s ∷ Θ) (emitᵗ s)
  arg = varᵗ (here refl)

  -- the author's step is already a function of one payload, so it IS
  -- the fold's body once weakened past the accumulator and the split
  f↑ : Tm _ _ _ (plainᵗ s ∷ listᵗ (plainᵗ t) ∷ S ∷ emitᵗ s ∷ Θ) (plainᵗ t)
  f↑ = renTm (λ x → x) (λ x → x)
             (ext∈ (λ x → there (there (there x)))) f

  -- inside the `letᵗ`: the split, then the former's argument, then Θ
  body : Tm _ _ _ (S ∷ emitᵗ s ∷ Θ) (emitᵗ t)
  body = reassembleᵛ env (fstᵗ split)
                     (revᵗ (foldᵗ (fstᵗ (sndᵗ split)) nilᵗ
                                  (consᵗ f↑ (varᵗ (there (here refl))))))
                     (sndᵗ (sndᵗ split))
    where
    split = varᵗ (here refl)
    env   = varᵗ (there (here refl))

  step : Tm _ _ _ (emitᵗ s ∷ Θ) (emitᵗ t)
  step = letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ arg))
              (reassembleᵛ arg nilᵗ nilᵗ (bool̂ false))
              body

-- THE CARRIED VALUE IS A PAIR BECAUSE `scanᵉ`'S OUTPUT IS ITS STATE,
-- and what this former outputs is an EMIT while what the author's step
-- threads is a plain value.  So the plain scan carries both and a
-- `mapᵉ` projects, which is the same two-stage shape rxjs writes as
-- `scan` followed by `map`.
--
-- THE SEED'S EMIT COMPONENT IS UNOBSERVABLE.  A scan emits the result
-- of its FIRST application and never the seed, so the tokens below are
-- read by nothing and claim no freshness.  The seed needs an INHABITANT
-- of `uniqᵗ` and nothing more; a binder supplies one at the cost of a
-- `mintᵉ` per `scanˢ` for a token nothing reads.
scanᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t : Ty}
      → Fn Γ Δᵍ Δ Θ (plainᵗ t ×ᵗ plainᵗ s) (plainᵗ t)
      → Tm Γ Δᵍ Δ Θ (plainᵗ t)
      → Exp Γ Δᵍ Δ Θ (emitᵗ s) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
scanᵖ {Θ = Θ} {s = s} {t = t} f z e =
  mintᵉ (mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ step seed e'))
  where
  -- the carried value: the author's state, and the emit built for the
  -- delivery that produced it
  A : Ty
  A = plainᵗ t ×ᵗ emitᵗ t

  -- the step's argument: the carried value and the arriving emit
  P : Ty
  P = A ×ᵗ emitᵗ s

  -- the token bound by the enclosing mint, read by nothing
  tok : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  tok = varᵗ (here refl)

  -- shift the incoming arguments under the mint binder
  z' : Tm _ _ _ (uniqᵗ ∷ Θ) (plainᵗ t)
  z' = renTm (λ x → x) (λ x → x) there z

  f' : Fn _ _ _ (uniqᵗ ∷ Θ) (plainᵗ t ×ᵗ plainᵗ s) (plainᵗ t)
  f' = renTm (λ x → x) (λ x → x) (ext∈ there) f

  e' : Exp _ _ _ (uniqᵗ ∷ Θ) (emitᵗ s)
  e' = renExp (λ x → x) (λ x → x) there e

  seed : Tm _ _ _ (uniqᵗ ∷ Θ) A
  seed = pairᵗ z' (instEmitᵛ nilᵗ tok tok (inlᵗ unit̂))

  S : Ty
  S = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ (plainᵗ s) ×ᵗ boolᵗ)

  -- the inner fold's accumulator: the author's state, and the outputs
  -- of this delivery in reverse
  B : Ty
  B = plainᵗ t ×ᵗ listᵗ (plainᵗ t)

  arg : Tm _ _ _ (P ∷ uniqᵗ ∷ Θ) P
  arg = varᵗ (here refl)

  -- inside both `letᵗ`s: the step's argument, then the fold's element
  -- and accumulator, then the split, then the former's argument, then Θ
  f↑ : Tm _ _ _ ((plainᵗ t ×ᵗ plainᵗ s) ∷ plainᵗ s ∷ B ∷ S ∷ P ∷ uniqᵗ ∷ Θ) (plainᵗ t)
  f↑ = renTm (λ x → x) (λ x → x)
             (ext∈ (λ x → there (there (there (there x))))) f'

  -- the fold's body: pair the carried state with the arriving payload,
  -- run the step on it, and push the result onto both halves
  fbody : Tm _ _ _ (plainᵗ s ∷ B ∷ S ∷ P ∷ uniqᵗ ∷ Θ) B
  fbody = letᵗ (pairᵗ (fstᵗ (varᵗ (there (here refl)))) (varᵗ (here refl)))
               (varᵗ (there (here refl)))
               (letᵗ f↑ (varᵗ (there (there (here refl)))) rebuilt)
    where
    rebuilt : Tm _ _ _ (plainᵗ t ∷ (plainᵗ t ×ᵗ plainᵗ s) ∷ plainᵗ s ∷ B
                        ∷ S ∷ P ∷ uniqᵗ ∷ Θ) B
    rebuilt = pairᵗ (varᵗ (here refl))
                    (consᵗ (varᵗ (here refl))
                           (sndᵗ (varᵗ (there (there (there (here refl)))))))

  -- inside the `letᵗ`: the split, then the former's argument, then Θ
  body : Tm _ _ _ (S ∷ P ∷ uniqᵗ ∷ Θ) A
  body = letᵗ (foldᵗ (fstᵗ (sndᵗ split)) start fbody)
              (fstᵗ (varᵗ (there (here refl)))) out
    where
    split = varᵗ (here refl)
    start = pairᵗ (fstᵗ (fstᵗ (varᵗ (there (here refl))))) nilᵗ

    out : Tm _ _ _ (B ∷ S ∷ P ∷ uniqᵗ ∷ Θ) A
    out = pairᵗ (fstᵗ (varᵗ (here refl)))
                (reassembleᵛ (sndᵗ (varᵗ (there (there (here refl)))))
                             (fstᵗ (varᵗ (there (here refl))))
                             (revᵗ (sndᵗ (varᵗ (here refl))))
                             (sndᵗ (sndᵗ (varᵗ (there (here refl))))))

  step : Tm _ _ _ (P ∷ uniqᵗ ∷ Θ) A
  step = letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (sndᵗ arg)))
              (fstᵗ arg)
              body

------------------------------------------------------------------
-- The elaboration: one simul program down into one plain program.
------------------------------------------------------------------

-- THE ONE PLACE THE ENVELOPE IS WRITTEN, WHICH IS WHAT MAKES THE
-- PALETTE ARGUMENT A PROOF RATHER THAN A CONVENTION.  A simul program
-- names no token, so every instant and every source appearing in an
-- elaborated program is put there here; and since the evaluator runs
-- only the plain tree, the elaboration is also the sole route by which
-- a shipped operator's protocol behaviour reaches a run.  Anything an
-- author could do to an envelope, they did by choosing a former.

-- THE AUTHOR'S TERM LANGUAGE NEEDS NOTHING, AND THAT IS A RESULT AND
-- NOT A CONVENIENCE.  Every `STm` former translates to its plain
-- namesake with its subterms translated, because the type walk is
-- structural everywhere no observable occurs and the one place it is
-- not — an observable value — is where a term carries a PROGRAM, whose
-- elaboration already stands at the type the walk demands.  The prim
-- ops are matched one by one for a reduction reason and not a semantic
-- one: their argument and result types are concrete, so the walk is the
-- identity on each, and Agda needs the constructor in hand to see it.

-- THE SUBSCRIBE FRAME IS ONE TOKEN THE WHOLE WALK STANDS UNDER, AND
-- THAT IS THE ENTIRETY OF WHAT THE MIRROR'S CONSTANT SAYS.  The
-- TypeScript side stamps every subscribe burst with a single global
-- symbol and nothing in either tree ever COMPARES against it, so its
-- content is not an identity anyone reads back — it is that the bursts
-- of one frame carry the SAME token and a later cascade's do not.  One
-- `mintᵉ` above the walk supplies exactly that: in scope at every site
-- beneath, drawn once per subscription of the program, and unforgeable
-- where a literal would not be.  What it is NOT is an ambient instant,
-- which varies per arrival cascade; the frame is the one instant a
-- program can hold, and it is the one the sources need.
plainᶜ⁺ : List Ty → List Ty
plainᶜ⁺ Θ = plainᶜ Θ ++ uniqᵗ ∷ []

-- AND IT RIDES AT THE FAR END, WHICH IS WHAT KEEPS EVERY AUTHOR
-- VARIABLE'S INDEX UNMOVED.  A binder conses, so a token at the FRONT
-- would sit at a different depth under every binder the walk descends
-- through and every author chain would shift by one; at the end it is
-- reached by the telescope's own length and the author names inject
-- untouched.  The cost is the injection and nothing else.
frameᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} (Θ : List Ty)
       → Tm Γ Δᵍ Δ (plainᶜ⁺ Θ) uniqᵗ
frameᵛ Θ = varᵗ (∈-++⁺ʳ (plainᶜ Θ) (here refl))

mutual

  toPlain : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ Θ t
          → Exp (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (emitᵗ t)
  -- AN INPUT IS THE ONE SOURCE THIS BODY WRITES, AND IT IS A TRANSPORT
  -- BECAUSE THE SLOT ALREADY CARRIES ENVELOPES.  The shape on the table
  -- is a slot carrying PLAIN values that the elaboration wraps instead
  -- -- a sync bracket for a cold, a bare stamp for a hot -- which moves
  -- the envelope's construction OUT of the machine and into the term
  -- language, where every other elaborated behaviour already lives.

  -- THE BRANCH IS AVAILABLE FOR THE ASKING, and the cost is one
  -- argument.  Cold and hot are not distinguished by the type or by the
  -- term, so this body cannot split on them as it stands; they ARE
  -- distinguished by the slot telescope, so an elaboration INDEXED BY
  -- the telescope splits on them immediately.

  -- AND THE SPLIT'S HOT ARM IS WRITABLE WITH THE PALETTE AS IT STANDS,
  -- WHICH IS WHAT A MINT'S SCOPE BUYS AND ITS ARITY HIDES.  A hot's
  -- source must be ONE token every subscriber sees, and the mint binder
  -- reads as drawing per SUBSCRIPTION -- a COLD's arity -- so a hot
  -- looks unreachable and the nullary literal, which names a single
  -- reserved token, looks like the only other candidate; it is not one,
  -- since two hots standing at it would collapse onto one identifier.

  -- WHAT SETTLES IT IS THAT THE BINDER DRAWS PER SUBSCRIPTION OF ITS
  -- OWN NODE AND BINDS INTO THE VALUE TELESCOPE.  At the ROOT, one
  -- binder per slot draws once for the whole program, and every site
  -- beneath it -- inside a deferred body, inside an unrolled recursion,
  -- inside a resubscribed inner stream -- reads a token already
  -- substituted into its closure.  So "minted once at construction" is
  -- a question of SCOPE and not of a missing former, and what it costs
  -- is a renaming of the body's value variables.

  -- AN INSTANT IS NOT DRAWN BY A PROGRAM AT ALL, IT IS READ, AND
  -- MISSING THAT IS WHAT MADE IT LOOK UNREACHABLE.  A source token is
  -- drawn fresh, once per subscription, which is the arity `mintᵉ`
  -- has.  An instant is never drawn by whatever needs one: the running
  -- cascade already has an instant and so does the subscribe frame, and
  -- a source COPIES whichever of the two is current.  The TypeScript
  -- mirror puts this beyond doubt -- an instant is made in its driver
  -- and nowhere else, at the root frame and once per arrival, and every
  -- other site in the implementation reads it.

  -- A READ HAS THE TWO PROPERTIES A MINT CANNOT HAVE, AND HAS THEM FOR
  -- FREE.  It varies over time, so one source's subscribe burst and its
  -- later deliveries fall in different instants; and it is shared
  -- between siblings, so two colds coming alive in one frame read the
  -- same one.  Those are exactly the two a binder was argued to be
  -- unable to combine, and the argument only ever ruled out a MINT.

  -- AND A WINDOWING FORMER IS NOT THE REPAIR (Anthony: "this is not
  -- something we want to ever do").  Pairing the machine's ambient
  -- instant onto each emit would forge nothing, since the token could
  -- only be copied out of the run -- but the palette is the TypeScript
  -- one name for name, and rxjs has no such operator, so adding it
  -- would put the two implementations out of correspondence to buy a
  -- reading the slot telescope already splits cold from hot with.

  -- WHAT A SLOT'S DEF DOES AT THIS ARM, INSTANTIATED RATHER THAN READ
  -- OFF THE CODE.  The arm passes the slot STRAIGHT THROUGH: the input
  -- already stands at the envelope, so nothing is wrapped here and the
  -- program's own elaboration mints over whatever the slot hands it.  A
  -- `shared` def is then a program at the envelope that was itself
  -- elaborated, so it arrives already minted and the mint above it is a
  -- second layer.  Run at a def that is an elaborated source, the
  -- second layer costs nothing a consumer can see: the program
  -- evaluates, the input delivers, and the decoded emit is a single
  -- coherent envelope.  What the def DOES move is the ambient token,
  -- since instants are minted from one counter -- a source-free program
  -- reads its own frame at token 1 in an empty context, at 2 under a
  -- table of width one whatever the slot holds, and at 3 when the
  -- program actually reads a def.  So an instant is a token and not a
  -- frame ORDINAL, and a claim comparing one against a literal is
  -- comparing against the shape of the table.
  -- WHAT WAS COVERED, since a definition cannot carry a receipt and the
  -- rows were scratch: one cold def at one width, read at fuels 0, 1, 2
  -- and 3, with payload and fuel both varied so neither could be what
  -- the token was tracking.  Not covered: a hot def, a def reading
  -- another slot, and every table wider than one.
  toPlain {Γ = Γ} (inputˢ i)  = subst (Exp _ _ _ _) (lookup-map i emitᵗ Γ)
                                      (input i)
  toPlain {Θ = Θ} (ofˢ ts)    = ofᵖ (frameᵛ Θ) (toPlainTms ts)
  toPlain {Θ = Θ} emptyˢ      = emptyᵖ (frameᵛ Θ)
  toPlain (takeˢ k e)         = takeᵖ (toPlainTm k) (toPlain e)
  toPlain (mapˢ f e)          = mapᵖ (toPlainTm f) (toPlain e)
  toPlain (scanˢ f z e)       = scanᵖ (toPlainTm f) (toPlainTm z) (toPlain e)
  toPlain (mergeAllˢ k e)     = mergeAllᵖ k (toPlain e)
  toPlain (switchAllˢ e)      = switchAllᵖ (toPlain e)
  toPlain (exhaustAllˢ e)     = exhaustAllᵖ (toPlain e)
  toPlain (μˢ e)              = μᵉ (toPlain e)
  toPlain (varˢ x)            = varᵉ (∈-map⁺ emitᵗ x)
  toPlain {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (deferˢ {t = t} e) =
    deferᵉ (subst (λ ζ → Exp (emitᵛ Γ) [] ζ (plainᶜ⁺ Θ) (emitᵗ t))
                  (map-++ emitᵗ Δᵍ Δ) (toPlain e))

  toPlainTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → STm Γ Δᵍ Δ Θ t
            → Tm (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t)
  toPlainTm (varˢᵗ x)      = varᵗ (∈-++⁺ˡ (∈-map⁺ plainᵗ x))
  toPlainTm unitˢ          = unit̂
  toPlainTm (boolˢ b)      = bool̂ b
  toPlainTm (natˢ k)       = nat̂ k
  toPlainTm (pairˢ a b)    = pairᵗ (toPlainTm a) (toPlainTm b)
  toPlainTm (fstˢ p)       = fstᵗ (toPlainTm p)
  toPlainTm (sndˢ p)       = sndᵗ (toPlainTm p)
  toPlainTm nilˢ           = nilᵗ
  toPlainTm (consˢ h t)    = consᵗ (toPlainTm h) (toPlainTm t)
  toPlainTm (inlˢ a)       = inlᵗ (toPlainTm a)
  toPlainTm (inrˢ b)       = inrᵗ (toPlainTm b)
  toPlainTm (caseˢ s l r)  = caseᵗ (toPlainTm s) (toPlainTm l) (toPlainTm r)
  toPlainTm (foldˢ l z f)  = foldᵗ (toPlainTm l) (toPlainTm z) (toPlainTm f)
  toPlainTm (ifˢ c a b)    = ifᵗ (toPlainTm c) (toPlainTm a) (toPlainTm b)
  toPlainTm (primˢ add a)  = primᵗ add  (toPlainTm a)
  toPlainTm (primˢ sub a)  = primᵗ sub  (toPlainTm a)
  toPlainTm (primˢ mul a)  = primᵗ mul  (toPlainTm a)
  toPlainTm (primˢ eqᵖ a)  = primᵗ eqᵖ  (toPlainTm a)
  toPlainTm (primˢ ltᵖ a)  = primᵗ ltᵖ  (toPlainTm a)
  toPlainTm (primˢ eqᵘ a)  = primᵗ eqᵘ  (toPlainTm a)
  toPlainTm (primˢ notᵖ a) = primᵗ notᵖ (toPlainTm a)
  toPlainTm (strmˢ e)      = strmᵗ (toPlain e)

  -- spelled out rather than `map`ped, so the recursion is structural
  toPlainTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
             → List (STm Γ Δᵍ Δ Θ t)
             → List (Tm (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t))
  toPlainTms []       = []
  toPlainTms (m ∷ ms) = toPlainTm m ∷ toPlainTms ms

-- THE ELABORATION PROPER, AND THE ONE THING IT ADDS TO THE WALK IS THE
-- FRAME.  A closed simul program elaborates to a closed plain one, so
-- the token the walk stands under is bound and discharged here and
-- nowhere else; every consumer sees an ordinary `Exp` at an empty value
-- telescope and carries no side condition about a token being in scope.
--
-- ONE MINT FOR THE WHOLE PROGRAM IS THE CLAIM, and it is the mirror's.
-- `mintᵉ` draws once per subscription of the node it stands at, and it
-- stands at the root, so every source beneath reads the same token for
-- one subscription of the program and a fresh one for the next — which
-- is what a subscribe frame is.  A resubscribe through `deferᵉ` re-runs
-- the body and not this binder, so an inner's frame is its outer's,
-- which is the sharing the grouping compares and the reason the token
-- could not have been bound per source.
--
-- THE MIRROR'S CONSTANT IS COARSER THAN THIS AND THE TWO STILL AGREE,
-- because the token's identity is READ BY NOBODY.  `SUBSCRIBE_FRAME`
-- is one module-level symbol shared by every run the process performs,
-- where this draws one per subscription; nothing on either side ever
-- compares a stamp against a literal, and every comparison that does
-- happen is between two stamps of the SAME run, which the two agree on
-- exactly.  So the difference is reachable by no program, and the
-- binder is the tighter of the two rather than a divergence.
elaborate : ∀ {n} {Γ : Ctx n} {Δᵍ Δ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ [] t
          → Exp (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) [] (emitᵗ t)
elaborate e = mintᵉ (toPlain e)
