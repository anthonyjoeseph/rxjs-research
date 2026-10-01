module SExp.Elaborate where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; map; foldr)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin)
open import Data.Vec using (lookup)
open import Data.Vec.Properties using (lookup-zipWith)
open import Relation.Binary.PropositionalEquality using (subst; refl)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; listᵗ; obs; _×ᵗ_; boolᵗ; natᵗ; uniqᵗ; input; ofᵉ; μᵉ; varᵉ; deferᵉ; mintᵉ;
  mapᵉ; scanᵉ; FlatOp; mergeᶠ; flattenᵉ; batchSyncᵉ; unitᵗ; _+ᵗ_;
  varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ;
  foldᵗ; ifᵗ; primᵗ; strmᵗ; letᵗ; revᵗ; appendᵗ; renTm; renExp; ext∈; add; sub; mul;
  eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import SExp.InstEmit using (instEventᵗ; closeReasonᵗ; emitKindᵗ; eventsᵛ; instantᵛ; sourceᵛ; kindᵛ;
                               eventCaseᵛ; splitEventsᵛ; reassembleᵛ; instEmitᵛ;
                               initᵛ; valueᵛ; closeᵛ; completeᵛ;
                               machineEmitᵗ)
open import SExp.Syntax using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeˢ; mapˢ; scanˢ; flattenˢ; μˢ;
  varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ; caseˢ;
  foldˢ; ifˢ; primˢ; strmˢ; plainᵗ; plainᶜ; emitᵗ; emitᶜ; Kinds; scriptedᵏ; sharedᵏ; slotTy;
  plainᵏ)

------------------------------------------------------------------
-- The per-former plumbing the elaboration is a composition of.
------------------------------------------------------------------

-- EVERY FORMER IS A BODY NOW, AND THE ONE LEAF LEFT IS AN OPERATOR
-- RATHER THAN A FACT.  The elaboration compiles the author's palette
-- into the plain tree, so a gap here is a capability plain rxjs has and
-- `Rx.Exp` does not — a former to add, carrying a name and a ledger
-- row, rather than a paragraph saying the body cannot be written.

-- AND THE BODIES ARE AIMED AT THE TYPESCRIPT, NOT AT THE SPEC (Anthony:
-- "we are not worried about correctness, just a basic mirroring of what
-- the typescript side is already doing").  Each one transcribes the
-- pipeline its twin runs out of stock rxjs, operator for operator;
-- where the palette is short of what the twin uses, the body takes the
-- nearest thing the palette does reach and its own header says which
-- reading that loses.  QuickCheck and the oracle are what settle those,
-- and neither is a claim this module makes.

-- MINTING IS NOT ONE OF THE GAPS, AND WHAT IT COSTS IS PLACEMENT
-- RATHER THAN A FORMER.  A source coming alive owes an `init` naming a
-- token nothing has used, and the term language has no former at
-- `uniqᵗ` at all — a term that made a token would be a literal, and a
-- program that could write a token could forge a collision.  A token is
-- drawn from a BINDER, and a binder reads as one token per subscription
-- while a source owes one per time it comes alive; those are the same
-- arity, since coming alive IS being subscribed, and a mint standing at
-- an INNER's head is subscribed once per outer value, so the binder
-- reaches a per-delivery token too.

-- NEITHER IS READING THE RUNNING INSTANT, AND WHICH INSTANT IS WANTED
-- IS WHY.  Downstream of a source the instant is not missing at all:
-- the incoming emit IS an InstEmit, a term can project its instant
-- field, and a step that stamps its output with the instant it was
-- handed is an ordinary `Tm`.  A former with NO input has nothing to
-- read it off — but the two sources want the SUBSCRIBE FRAME's instant
-- and no other, since a cold's whole emission leaves in one burst, and
-- a frame is exactly what one token bound above the walk names.

-- THE TWO ARMS OF A NESTED SUM THAT THIS ELABORATION NAMES, AND THEY
-- ARE HERE RATHER THAN BESIDE THE ENCODING BECAUSE ONE ELABORATION IS
-- THEIR ONLY CONSUMER.  `SExp.InstEmit` owes the constructors, which
-- every operator needs; which REASON a source closes for and which
-- KIND of emit a subscribe burst is are this walk's vocabulary.
exhaustedᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Tm Γ Δᵍ Δ Θ closeReasonᵗ
exhaustedᵛ = inrᵗ (inrᵗ unit̂)

subscribeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Tm Γ Δᵍ Δ Θ emitKindᵗ
subscribeᵛ = inlᵗ unit̂

-- A FLATTENER OVER A SOURCE OF OBSERVABLES, which is what rxjs's
-- `mergeAll`, `switchAll` and `exhaustAll` are: `flattenᵉ` over a map
-- making every element a lane and none an echo.
flatAllᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → FlatOp → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
flatAllᵉ op e = flattenᵉ op (mapᵉ (pairᵗ (inlᵗ unit̂) (inrᵗ (varᵗ (here refl)))) e)

-- the arrival kind: the tag an input's per-arrival emit carries
deliveryᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ} → Tm Γ Δᵍ Δ Θ emitKindᵗ
deliveryᵛ = inrᵗ (inlᵗ unit̂)

-- A COLD SOURCE IS ONE INSTEMIT PER VALUE, ALL UNDER THE FRAME TOKEN.
-- Everything this former emits leaves in the subscribe burst — the
-- `init` naming the source on the first emit, the author's values one
-- per emit, the exhausted `close` and the `complete` on the last — so
-- the one instant it has to name is the frame's, and a source that
-- INHERITED a later cascade's would be naming something it can never
-- be handed.
--
-- ONE VALUE PER EMIT BECAUSE A FLATTENER ELEMENT HOLDS ONE LANE.  An
-- emit carrying k inners is one element whose lane is their merge, so
-- one emit for an `of` of k observables nests a flattener plain rxjs
-- does not have, and the evaluator's cost is multiplicative in that
-- nesting (`typecheck-performance-numbers.md`).  The twin's `of` is one
-- emit; batching cannot tell the two apart, since both are one instant.
--
-- THE SOURCE TOKEN IS MINTED AT THIS NODE AND THE INSTANT IS NOT, AND
-- the difference is the arity.  A source is a fresh identity per
-- subscription, which is `mintᵉ`'s own arity, so it is bound here; the
-- frame is one identity for every source alive in the same frame, so it
-- is bound once above the whole walk and read here.  Two colds side by
-- side therefore get two sources and one instant, which is what the
-- spec's grouping compares.
-- THE INPUT SOURCE, WRAPPED HERE RATHER THAN ASSUMED ON THE TABLE.
-- The slot stands at the author's bare payload, so this is the term
-- that builds every InstEmit an input contributes: one `init` naming
-- the source, then one emit per ARRIVAL carrying that arrival's
-- values.  Nothing else in the elaboration writes an input's InstEmit,
-- which is what makes a well-formedness claim about inputs a lemma
-- about this definition instead of a hypothesis about the table.
--
-- THE AMBIENT INSTANT IS RECOVERED BY GROUPING, NOT BY READING A
-- CLOCK (Anthony).  A fold over a flat stream cannot tell which values
-- shared an arrival, so wrapping each separately would split a cold's
-- subscribe burst into as many instants as it has values.
-- `batchSyncᵉ` already draws that boundary -- it emits `(head , rest)`,
-- the whole synchronous group under one value -- so a group IS an
-- instant and no arm has to ask which kind it is; an isolated
-- asynchronous arrival is the same shape at `rest ≡ []`.  Nothing here
-- senses synchrony, which is the property the machine was always
-- GIVEN and a timing-based repair would have re-derived.
--
-- AND THE PER-ARRIVAL TOKEN COMES FROM THE MINT'S PLACEMENT, WHICH IS
-- THE ARITY THAT LOOKED MISSING.  `mintᵉ` draws once per subscription
-- of the node it stands at.  The OUTER mint stands at this node, so it
-- draws one SOURCE token per subscription of the input -- a source's
-- own arity.  The INNER mint stands at the head of a merging flattener's
-- inner, which is subscribed once per outer value, so it draws one
-- INSTANT token per arrival.  Two arities, one former, and the
-- difference is where the binder sits.
--
-- DEAD ROUTE: bracket the frame with `batchSyncᵉ` and let the GROUPING
--   stand in for the id.  It brackets without NAMING, so two groups
--   can never be joined and nothing downstream can compare instants.
--   The route above is not that one: the group TRIGGERS a mint, and
--   naming is restored by the token the mint binds.  What survives of
--   the old objection -- two sources grouping separately -- is a
--   semantics question and not a blocker, since two independent
--   arrivals in one turn are two arrivals.

-- WHAT IS DELIBERATELY ABSENT: the `close` at `exhausted`.  The
-- TypeScript mirror mints one off its script's `isLast`, and
-- `batchSyncᵉ` hands over no such bit.  An input that must be seen to
-- complete is owed a separate reading of the script, not a repair of
-- this term.
inputᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} (i : Fin n)
       → Tm Γ Δᵍ Δ Θ uniqᵗ
       → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (lookup Γ i))
inputᵖ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} i frame =
  mintᵉ (flatAllᵉ (mergeᶠ nothing) (ofᵉ (strmᵗ announce ∷ strmᵗ deliveries ∷ [])))
  where
  a : Ty
  a = lookup Γ i

  -- under the SOURCE binder
  Θ¹ : List Ty
  Θ¹ = uniqᵗ ∷ Θ

  -- under the SOURCE binder, the group, and the INSTANT binder
  Θ² : List Ty
  Θ² = uniqᵗ ∷ (a ×ᵗ listᵗ a) ∷ Θ¹

  ↑ : ∀ {r} → Tm Γ Δᵍ Δ Θ r → Tm Γ Δᵍ Δ Θ¹ r
  ↑ = renTm (λ x → x) (λ x → x) there

  src : Tm Γ Δᵍ Δ Θ¹ uniqᵗ
  src = varᵗ (here refl)

  -- the registration announcement: one `init`, in the subscribe frame,
  -- tagged `subscribe` so it owes and pays nothing.
  announce : Exp Γ Δᵍ Δ Θ¹ (machineEmitᵗ a)
  announce =
    ofᵉ (instEmitᵛ (consᵗ (initᵛ src) nilᵗ) (↑ frame) src subscribeᵛ ∷ [])

  -- inside the INSTANT binder: the token, then the group, then the
  -- source token, then Θ
  inst : Tm Γ Δᵍ Δ Θ² uniqᵗ
  inst = varᵗ (here refl)

  grp : Tm Γ Δᵍ Δ Θ² (a ×ᵗ listᵗ a)
  grp = varᵗ (there (here refl))

  srcᵍ : Tm Γ Δᵍ Δ Θ² uniqᵗ
  srcᵍ = varᵗ (there (there (here refl)))

  -- head first, then the tail in arrival order (the `revᵗ` is what
  -- makes a cons-fold rebuild the list rather than reverse it)
  evs : Tm Γ Δᵍ Δ Θ² (listᵗ (instEventᵗ uniqᵗ a))
  evs = consᵗ (valueᵛ (fstᵗ grp))
              (foldᵗ (revᵗ (sndᵗ grp)) nilᵗ
                     (consᵗ (valueᵛ (varᵗ (here refl)))
                            (varᵗ (there (here refl)))))

  -- one arrival: mint its instant, emit its whole group under it
  stamp : Tm Γ Δᵍ Δ ((a ×ᵗ listᵗ a) ∷ Θ¹) (obs (machineEmitᵗ a))
  stamp = strmᵗ (mintᵉ (ofᵉ (instEmitᵛ evs inst srcᵍ deliveryᵛ ∷ [])))

  deliveries : Exp Γ Δᵍ Δ Θ¹ (machineEmitᵗ a)
  deliveries = flatAllᵉ (mergeᶠ nothing) (mapᵉ stamp (batchSyncᵉ (input i)))

ofᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
    → Tm Γ Δᵍ Δ Θ uniqᵗ
    → List (Tm Γ Δᵍ Δ Θ (plainᵗ t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
ofᵖ {Θ = Θ} {t = t} frame ts = mintᵉ (ofᵉ (emits (initᵛ src ∷ []) (map ↑ ts)))
  where
  ↑ : ∀ {r} → Tm _ _ _ Θ r → Tm _ _ _ (uniqᵗ ∷ Θ) r
  ↑ = renTm (λ x → x) (λ x → x) there

  src : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  src = varᵗ (here refl)

  frame↑ : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  frame↑ = ↑ frame

  E : Ty
  E = instEventᵗ uniqᵗ (plainᵗ t)

  emit : List (Tm _ _ _ (uniqᵗ ∷ Θ) E) → Tm _ _ _ (uniqᵗ ∷ Θ) (emitᵗ t)
  emit evs = instEmitᵛ (foldr consᵗ nilᵗ evs) frame↑ src subscribeᵛ

  ending : List (Tm _ _ _ (uniqᵗ ∷ Θ) E)
  ending = closeᵛ src exhaustedᵛ ∷ completeᵛ ∷ []

  -- the events owed before the next value, then the values left
  emits : List (Tm _ _ _ (uniqᵗ ∷ Θ) E) → List (Tm _ _ _ (uniqᵗ ∷ Θ) (plainᵗ t))
        → List (Tm _ _ _ (uniqᵗ ∷ Θ) (emitᵗ t))
  emits pre []           = emit (pre ++ ending) ∷ []
  emits pre (v ∷ [])     = emit (pre ++ valueᵛ v ∷ ending) ∷ []
  emits pre (v ∷ w ∷ vs) = emit (pre ++ valueᵛ v ∷ []) ∷ emits [] (w ∷ vs)

-- THE EMPTY SRXJS SOURCE IS NOT THE EMPTY PLAIN ONE, and the gap is
-- one InstEmit rather than one event: it still brackets a subscribe
-- frame, so it emits an `init` and a `complete` where `emptyᵉ` emits
-- nothing at all.  It is `ofᵖ` at no values, which is what the mirror
-- writes too.
emptyᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
       → Tm Γ Δᵍ Δ Θ uniqᵗ → Exp Γ Δᵍ Δ Θ (emitᵗ t)
emptyᵖ frame = ofᵖ frame []

-- THE TWO FORMERS OF THIS LEG THAT WERE NEVER BLOCKED, AND WRITING
-- THEM IS WHAT SAYS SO.  Neither adds an event, mints anything or can
-- end the stream, so everything either needs is in the emit it was
-- handed: the payloads come out of the InstEmit, the author's step runs
-- over them, and what goes back in is the same InstEmit with new
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

-- THE FOUR LIST ROUTINES THE CUT IS WRITTEN OUT OF, AND THEY ARE HERE
-- BECAUSE THE TERM LANGUAGE HAS NO LIBRARY.  `Tm` has one eliminator
-- over lists and no application, so `take`, `length`, and a multiset
-- delete are each a fold with a pair-shaped accumulator rather than a
-- call.  The mirror spells the same four inline as ordinary JavaScript,
-- which is why nothing about them is a finding.

takeListᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
          → Tm Γ Δᵍ Δ Θ natᵗ → Tm Γ Δᵍ Δ Θ (listᵗ a)
          → Tm Γ Δᵍ Δ Θ (listᵗ a)
takeListᵛ {Θ = Θ} {a = a} m xs = revᵗ (sndᵗ (foldᵗ xs (pairᵗ m nilᵗ) body))
  where
  A : Ty
  A = natᵗ ×ᵗ listᵗ a

  acc : Tm _ _ _ (a ∷ A ∷ Θ) A
  acc = varᵗ (there (here refl))

  body : Tm _ _ _ (a ∷ A ∷ Θ) A
  body = ifᵗ (primᵗ ltᵖ (pairᵗ (nat̂ 0) (fstᵗ acc)))
             (pairᵗ (primᵗ sub (pairᵗ (fstᵗ acc) (nat̂ 1)))
                    (consᵗ (varᵗ (here refl)) (sndᵗ acc)))
             acc

lengthᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
        → Tm Γ Δᵍ Δ Θ (listᵗ a) → Tm Γ Δᵍ Δ Θ natᵗ
lengthᵛ xs = foldᵗ xs (nat̂ 0)
                   (primᵗ add (pairᵗ (varᵗ (there (here refl))) (nat̂ 1)))

-- the open registrations are a MULTISET, so a `close` retires ONE
-- occurrence: two subscriptions of one source are two entries and the
-- first close may not take both.
removeOneᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ}
           → Tm Γ Δᵍ Δ Θ uniqᵗ → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ)
           → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ)
removeOneᵛ {Θ = Θ} u xs = revᵗ (sndᵗ (foldᵗ xs (pairᵗ (bool̂ false) nilᵗ) body))
  where
  A : Ty
  A = boolᵗ ×ᵗ listᵗ uniqᵗ

  u↑ : Tm _ _ _ (uniqᵗ ∷ A ∷ Θ) uniqᵗ
  u↑ = renTm (λ x → x) (λ x → x) (λ x → there (there x)) u

  acc : Tm _ _ _ (uniqᵗ ∷ A ∷ Θ) A
  acc = varᵗ (there (here refl))

  keep : Tm _ _ _ (uniqᵗ ∷ A ∷ Θ) A
  keep = pairᵗ (fstᵗ acc) (consᵗ (varᵗ (here refl)) (sndᵗ acc))

  body : Tm _ _ _ (uniqᵗ ∷ A ∷ Θ) A
  body = ifᵗ (primᵗ notᵖ (fstᵗ acc))
             (ifᵗ (primᵗ eqᵘ (pairᵗ (varᵗ (here refl)) u↑))
                  (pairᵗ (bool̂ true) (sndᵗ acc))
                  keep)
             keep

-- the open registrations after one emit's bookkeeping: `init` enlists,
-- `close` retires, everything else passes.  The mirror's `openAfter`,
-- minus its plumbing-kind filter, which this walk never reaches because
-- the elaboration mints no plumbing emits.
openAfterᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ b}
           → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ uniqᵗ b))
           → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ) → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ)
openAfterᵛ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {b = b} evs os = foldᵗ evs os body
  where
  E : Ty
  E = instEventᵗ uniqᵗ b

  acc : ∀ {x} → Tm Γ Δᵍ Δ (x ∷ E ∷ listᵗ uniqᵗ ∷ Θ) (listᵗ uniqᵗ)
  acc = varᵗ (there (there (here refl)))

  body : Tm _ _ _ (E ∷ listᵗ uniqᵗ ∷ Θ) (listᵗ uniqᵗ)
  body = eventCaseᵛ (varᵗ (here refl))
           (appendᵗ acc (consᵗ (varᵗ (here refl)) nilᵗ))
           acc
           (removeOneᵛ (fstᵗ (varᵗ (here refl))) acc)
           acc
           acc

-- one `close` per surviving registration, which is what the cut owes
-- the sources it is about to stop.
--
-- WHAT IS NOT MIRRORED IS THE PER-VICTIM REASON, AND IT IS A REASON AND
-- NOT A SOURCE.  The twin decides `cut` against `cutPending` by reading
-- a ledger of which registrations were already paid or born in the
-- cutting instant; this writes `cut` throughout.  The victims are the
-- same list either way, so what a program can see of the difference is
-- one field of one event.
cutClosesᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ b}
           → Tm Γ Δᵍ Δ Θ (listᵗ uniqᵗ)
           → Tm Γ Δᵍ Δ Θ (listᵗ (instEventᵗ uniqᵗ b))
cutClosesᵛ os = revᵗ (foldᵗ os nilᵗ
  (consᵗ (closeᵛ (varᵗ (here refl)) (inlᵗ unit̂)) (varᵗ (there (here refl)))))

-- THE PIPELINE THE MIRROR WRITES, MINUS ITS ENDING.  A scan carrying
-- the quota, the open registrations, whether the cut has happened and
-- the emit this delivery produced; then a projection pulling that emit
-- back out of the state.  Counting the author's values and truncating
-- their list is a pure step's work, and the state carries the answer
-- and the emit together because the palette reads a value and nothing
-- beside it.
--
-- WHAT IS NOT MIRRORED IS THE ENDING, AND IT IS THE ONE PIECE THAT IS
-- NOT A STEP'S WORK.  rxjs ends on `takeWhile(p, true)`, whose
-- predicate reads the scan's own state; the plain palette can only end
-- at an emit INDEX fixed at subscription, and a cut over the author's
-- VALUES is not one, since how many InstEmits it takes to fill a quota
-- over their payloads is a property of the run.  So the emit that fills
-- the quota carries the closes and the completion, and every emit after
-- it passes through carrying its bookkeeping and no values — where the
-- twin has unsubscribed and the stream is over.
--
-- AND THE BEHAVIOUR THE CUT MUST MIRROR IS MEASURED RATHER THAN
-- INFERRED (Anthony: "just run it in js").  Real rxjs `take` was run
-- against a four-item synchronous source, against a `mergeAll` of two
-- inner bursts, and at zero.  It emits the nth value and completes
-- AFTER it; it cuts mid-burst, so an inner's remaining values are
-- dropped rather than waited for; and at ZERO it never subscribes its
-- source at all, which is the fact a count-down silently gets wrong.
--
-- THE SEED'S EMIT COMPONENT IS UNOBSERVABLE, exactly as `scanᵖ`'s is: a
-- scan emits the result of its FIRST application and never the seed, so
-- the tokens below are read by nothing and claim no freshness.  One
-- `mintᵉ` supplies the inhabitant `uniqᵗ` has no literal for.
-- DEAD ROUTE: cut with `takeᵉ` over a count the scan computes.  Nothing
--   converts a budget over values into the emit index a
--   subscription-time count has to name.
takeᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
      → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ (emitᵗ t) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
takeᵖ {Θ = Θ} {t = t} k e = mintᵉ (mapᵉ outᵛ counted)
  where
  -- the quota left, whether the cut has happened, the open
  -- registrations, and the emit this delivery produced
  S : Ty
  S = natᵗ ×ᵗ (boolᵗ ×ᵗ (listᵗ uniqᵗ ×ᵗ emitᵗ t))

  -- the step's argument: the carried state and the arriving emit
  P : Ty
  P = S ×ᵗ emitᵗ t

  -- the split of one emit: bookkeeping retagged, payloads, completion
  SP : Ty
  SP = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ (plainᵗ t) ×ᵗ boolᵗ)

  k' : Tm _ _ _ (uniqᵗ ∷ Θ) natᵗ
  k' = renTm (λ x → x) (λ x → x) there k

  e' : Exp _ _ _ (uniqᵗ ∷ Θ) (emitᵗ t)
  e' = renExp (λ x → x) (λ x → x) there e

  tok : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  tok = varᵗ (here refl)

  seed : Tm _ _ _ (uniqᵗ ∷ Θ) S
  seed = pairᵗ k' (pairᵗ (bool̂ false)
                         (pairᵗ nilᵗ (instEmitᵛ nilᵗ tok tok subscribeᵛ)))

  -- inside the two `letᵗ`s: the taken payloads, the split, the step's
  -- argument, the mint's token, then Θ
  inner : Tm _ _ _ (listᵗ (plainᵗ t) ∷ SP ∷ P ∷ uniqᵗ ∷ Θ) S
  inner = ifᵗ cut?
              (pairᵗ (nat̂ 0)
                     (pairᵗ (bool̂ true)
                            (pairᵗ nilᵗ
                                   (reassembleᵛ env
                                                (appendᵗ book (cutClosesᵛ open'))
                                                taken (bool̂ true)))))
              (pairᵗ (primᵗ sub (pairᵗ rem (lengthᵛ taken)))
                     (pairᵗ done
                            (pairᵗ open' (reassembleᵛ env book taken fin))))
    where
    taken = varᵗ (here refl)
    split = varᵗ (there (here refl))
    st    = fstᵗ (varᵗ (there (there (here refl))))
    env   = sndᵗ (varᵗ (there (there (here refl))))
    book  = fstᵗ split
    fin   = sndᵗ (sndᵗ split)
    rem   = fstᵗ st
    done  = fstᵗ (sndᵗ st)
    open' = openAfterᵛ book (fstᵗ (sndᵗ (sndᵗ st)))

    -- the closes are minted ONCE: the quota is spent from the emit that
    -- fills it onwards, so the equality alone would re-cut on every
    -- emit after it.
    cut? = ifᵗ done (bool̂ false) (primᵗ eqᵖ (pairᵗ (lengthᵛ taken) rem))

  -- inside the first `letᵗ`: the split, the step's argument, the
  -- mint's token, then Θ
  body : Tm _ _ _ (SP ∷ P ∷ uniqᵗ ∷ Θ) S
  body = letᵗ (takeListᵛ (fstᵗ st) (fstᵗ (sndᵗ (varᵗ (here refl))))) st inner
    where
    st = fstᵗ (varᵗ (there (here refl)))

  step : Tm _ _ _ (P ∷ uniqᵗ ∷ Θ) S
  step = letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (sndᵗ (varᵗ (here refl)))))
              (fstᵗ (varᵗ (here refl))) body

  outᵛ : Fn _ _ _ (uniqᵗ ∷ Θ) S (emitᵗ t)
  outᵛ = sndᵗ (sndᵗ (sndᵗ (varᵗ (here refl))))

  counted : Exp _ _ _ (uniqᵗ ∷ Θ) S
  counted = scanᵉ step seed e'

-- ONE OUTER EMIT AS ONE FLATTENER ELEMENT: an echo carrying the emit's
-- bookkeeping and its echoed values, beside a lane merging the inners it
-- carried.  The flattener is `flattenᵉ` itself, at the author's policy,
-- because the author wrote `flattenˢ`; nothing here chooses one.
--
-- THE INSTEMIT APPEARS TWICE IN THE ARGUMENT, WHICH IS EASY TO READ
-- PAST.  `emitᵗ` unfolds through `plainᵗ`'s observable clause, so an
-- inner lane is an observable of INSTEMITS: the argument is an InstEmit
-- stream whose payloads may hold InstEmit streams.  Both layers are
-- already stamped when they arrive, which is why nothing here mints —
-- the inner's bookkeeping rides the inner's own emits, and only the
-- OUTER's has to be placed.
--
-- AND IT IS PLACED ON THE ECHO, WHICH NO POLICY SEES.  A lane is what a
-- concurrency limit COUNTS, what a switch CUTS and what an exhaust
-- DROPS, so bookkeeping riding a lane would queue behind a running inner
-- at a saturated limit and vanish with a dropped one; the echo leaves as
-- the element arrives, before its lane is handled, which is the twin's
-- one ordered channel.  For the same reason an emit carrying no inner
-- has NO lane rather than an empty one: under a switch an empty lane
-- still cancels the live one.
--
-- THE LANE IS PER EMIT AND NOT PER INNER: an emit carrying two inners
-- hands the flattener one lane, their merge.
elemᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
      → Fn Γ Δᵍ Δ Θ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))
                    ((unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t)))
elemᵛ {Θ = Θ} {t = t} =
  letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (varᵗ (here refl))))
       (pairᵗ (inlᵗ unit̂) (inlᵗ unit̂)) body
  where
  L : Ty
  L = unitᵗ +ᵗ obs (emitᵗ t)

  P : Ty
  P = (unitᵗ +ᵗ plainᵗ t) ×ᵗ L

  SP : Ty
  SP = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ P ×ᵗ boolᵗ)

  -- one payload's echo consed onto the accumulated ones, reversed:
  -- the payload, then the accumulator
  echoStep : Tm _ _ _ (P ∷ listᵗ (plainᵗ t) ∷ SP ∷ emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)) ∷ Θ)
                (listᵗ (plainᵗ t))
  echoStep = caseᵗ (fstᵗ (varᵗ (here refl)))
                   (varᵗ (there (there (here refl))))
                   (consᵗ (varᵗ (here refl)) (varᵗ (there (there (here refl)))))

  -- one payload's lane merged in FRONT of the accumulated one, over the
  -- payloads reversed, so the first inner leads: the payload, then the
  -- accumulator
  laneStep : Tm _ _ _ (P ∷ L ∷ SP ∷ emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)) ∷ Θ) L
  laneStep = caseᵗ (sndᵗ (varᵗ (here refl)))
                   (varᵗ (there (there (here refl))))
                   (caseᵗ (varᵗ (there (there (here refl))))
                          (inrᵗ (varᵗ (there (here refl))))
                          (inrᵗ (strmᵗ (flatAllᵉ (mergeᶠ nothing)
                                  (ofᵉ (varᵗ (there (here refl)) ∷ varᵗ (here refl) ∷ []))))))

  -- inside the `letᵗ`: the split, the former's argument, then Θ
  body : Tm _ _ _ (SP ∷ emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)) ∷ Θ)
            ((unitᵗ +ᵗ emitᵗ t) ×ᵗ L)
  body = pairᵗ (inrᵗ (reassembleᵛ env (fstᵗ split) echoes (sndᵗ (sndᵗ split))))
               (foldᵗ (revᵗ vals) (inlᵗ unit̂) laneStep)
    where
    split  = varᵗ (here refl)
    env    = varᵗ (there (here refl))
    vals   = fstᵗ (sndᵗ split)
    echoes = revᵗ (foldᵗ vals nilᵗ echoStep)

-- A SUBSCRIBE BURST TAKES THE INSTANT OF WHATEVER SUBSCRIBED IT.  An
-- emit of kind `subscribe` was stamped with the frame it was BUILT in,
-- which is the root's; when the subscription happened inside a later
-- cascade, the burst belongs to that cascade, and `at`/`as` name it.
-- The twin's join grafts such a burst onto its carrier for the same
-- reason.
restampᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
         → Tm Γ Δᵍ Δ Θ uniqᵗ → Tm Γ Δᵍ Δ Θ emitKindᵗ
         → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a)
restampᵛ at as e =
  ifᵗ (caseᵗ (kindᵛ e) (bool̂ true) (bool̂ false))
      (instEmitᵛ (eventsᵛ e) at (sourceᵛ e) as)
      e

-- A LANE IS SUBSCRIBED IN THE LAST INSTANT THE FLATTENER PUT OUT: the
-- echo of the outer emit that carried it, or the lane emit whose
-- completion freed its slot.  So a scan over the output carries that
-- instant and its kind, and every subscribe burst behind it takes them.
-- Inside the root frame everything is the frame and nothing moves.
flattenᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty} → FlatOp
         → Tm Γ Δᵍ Δ Θ uniqᵗ
         → Exp Γ Δᵍ Δ Θ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
flattenᵖ {Θ = Θ} {t = t} op frame e =
  mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ step seed (flattenᵉ op (mapᵉ elemᵛ e)))
  where
  -- the last instant and kind put out, and the emit put out
  S : Ty
  S = (uniqᵗ ×ᵗ emitKindᵗ) ×ᵗ emitᵗ t

  seed : Tm _ _ _ Θ S
  seed = pairᵗ (pairᵗ frame subscribeᵛ) (instEmitᵛ nilᵗ frame frame subscribeᵛ)

  step : Tm _ _ _ ((S ×ᵗ emitᵗ t) ∷ Θ) S
  step = letᵗ (restampᵛ (fstᵗ (fstᵗ (fstᵗ arg))) (sndᵗ (fstᵗ (fstᵗ arg))) (sndᵗ arg))
              (fstᵗ arg)
              (pairᵗ (pairᵗ (instantᵛ (varᵗ (here refl))) (kindᵛ (varᵗ (here refl))))
                     (varᵗ (here refl)))
    where
    arg = varᵗ (here refl)

------------------------------------------------------------------
-- The elaboration: one simul program down into one plain program.
------------------------------------------------------------------

-- THE ONE PLACE THE INSTEMIT IS WRITTEN, WHICH IS WHAT MAKES THE
-- PALETTE ARGUMENT A PROOF RATHER THAN A CONVENTION.  A simul program
-- names no token, so every instant and every source appearing in an
-- elaborated program is put there here; and since the evaluator runs
-- only the plain tree, the elaboration is also the sole route by which
-- a shipped operator's protocol behaviour reaches a run.  Anything an
-- author could do to an InstEmit, they did by choosing a former.

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

-- THE WALK IS PARAMETERISED BY THE SLOT KINDS, AND BY NOTHING ELSE NEW.
-- `κ` says how each slot is SUPPLIED, which is the one thing the input
-- arm has to split on and the one thing an author's tree does not
-- record (SExp.Syntax).  It rides as a module parameter rather than an
-- argument so that the ~40 recursive calls below read exactly as they
-- did; `Γ` joins it there because the walk never changes slots.
module _ {n} {Γ : Ctx n} (κ : Kinds n) where

 mutual

   toInstEmit : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
           → SExp Γ Δᵍ Δ Θ t
           → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (emitᵗ t)
   -- AN INPUT IS THE ONE SOURCE THIS BODY WRITES, AND IT IS A TRANSPORT
   -- BECAUSE THE SLOT ALREADY CARRIES INSTEMITS.  The shape on the table
   -- is a slot carrying PLAIN values that the elaboration wraps instead
   -- -- a sync bracket for a cold, a bare stamp for a hot -- which moves
   -- the InstEmit's construction OUT of the machine and into the term
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
   -- already stands at the InstEmit, so nothing is wrapped here and the
   -- program's own elaboration mints over whatever the slot hands it.  A
   -- `shared` def is then a program at the InstEmit that was itself
   -- elaborated, so it arrives already minted and the mint above it is a
   -- second layer.  Run at a def that is an elaborated source, the
   -- second layer costs nothing a consumer can see: the program
   -- evaluates, the input delivers, and the decoded emit is a single
   -- coherent InstEmit.  What the def DOES move is the ambient token,
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
   -- THE ONE ARM THAT READS `κ`, and the only place in the walk that
   -- cares how a slot is supplied.  Both arms land at `emitᵗ (lookup Γ
   -- i)`: a SCRIPTED slot stands at `plainᵗ`, so `inputᵖ` wrapping it
   -- gives `machineEmitᵗ (plainᵗ _)`, which IS that type; a SHARED one
   -- stands at `emitᵗ` already, so the reference is `input i` and
   -- nothing is wrapped a second time.
   toInstEmit {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (inputˢ i)
     with lookup κ i | lookup-zipWith slotTy i Γ κ
   ... | scriptedᵏ | eq =
         subst (λ u → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ)
                          (machineEmitᵗ u))
               eq (inputᵖ i (frameᵛ Θ))
   ... | sharedᵏ   | eq =
         mapᵉ (restampᵛ (renTm (λ x → x) (λ x → x) there (frameᵛ Θ)) subscribeᵛ
                        (varᵗ (here refl)))
              (subst (λ u → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) u)
                     eq (input i))
   toInstEmit {Θ = Θ} (ofˢ ts)    = ofᵖ (frameᵛ Θ) (toInstEmitTms ts)
   toInstEmit {Θ = Θ} emptyˢ      = emptyᵖ (frameᵛ Θ)
   toInstEmit (takeˢ k e)         = takeᵖ (toInstEmitTm k) (toInstEmit e)
   toInstEmit (mapˢ f e)          = mapᵖ (toInstEmitTm f) (toInstEmit e)
   toInstEmit (scanˢ f z e)       = scanᵖ (toInstEmitTm f) (toInstEmitTm z) (toInstEmit e)
   toInstEmit {Θ = Θ} (flattenˢ op e) = flattenᵖ op (frameᵛ Θ) (toInstEmit e)
   toInstEmit (μˢ e)              = μᵉ (toInstEmit e)
   toInstEmit (varˢ x)            = varᵉ (∈-map⁺ emitᵗ x)
   toInstEmit {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (deferˢ {t = t} e) =
     deferᵉ (mintᵉ (mapᵉ (restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)))
       (renExp (λ x → x) (λ x → x) there
         (subst (λ ζ → Exp (plainᵏ Γ κ) [] ζ (plainᶜ⁺ Θ) (emitᵗ t))
                (map-++ emitᵗ Δᵍ Δ) (toInstEmit e)))))

   toInstEmitTm : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
             → STm Γ Δᵍ Δ Θ t
             → Tm (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t)
   toInstEmitTm (varˢᵗ x)      = varᵗ (∈-++⁺ˡ (∈-map⁺ plainᵗ x))
   toInstEmitTm unitˢ          = unit̂
   toInstEmitTm (boolˢ b)      = bool̂ b
   toInstEmitTm (natˢ k)       = nat̂ k
   toInstEmitTm (pairˢ a b)    = pairᵗ (toInstEmitTm a) (toInstEmitTm b)
   toInstEmitTm (fstˢ p)       = fstᵗ (toInstEmitTm p)
   toInstEmitTm (sndˢ p)       = sndᵗ (toInstEmitTm p)
   toInstEmitTm nilˢ           = nilᵗ
   toInstEmitTm (consˢ h t)    = consᵗ (toInstEmitTm h) (toInstEmitTm t)
   toInstEmitTm (inlˢ a)       = inlᵗ (toInstEmitTm a)
   toInstEmitTm (inrˢ b)       = inrᵗ (toInstEmitTm b)
   toInstEmitTm (caseˢ s l r)  = caseᵗ (toInstEmitTm s) (toInstEmitTm l) (toInstEmitTm r)
   toInstEmitTm (foldˢ l z f)  = foldᵗ (toInstEmitTm l) (toInstEmitTm z) (toInstEmitTm f)
   toInstEmitTm (ifˢ c a b)    = ifᵗ (toInstEmitTm c) (toInstEmitTm a) (toInstEmitTm b)
   toInstEmitTm (primˢ add a)  = primᵗ add  (toInstEmitTm a)
   toInstEmitTm (primˢ sub a)  = primᵗ sub  (toInstEmitTm a)
   toInstEmitTm (primˢ mul a)  = primᵗ mul  (toInstEmitTm a)
   toInstEmitTm (primˢ eqᵖ a)  = primᵗ eqᵖ  (toInstEmitTm a)
   toInstEmitTm (primˢ ltᵖ a)  = primᵗ ltᵖ  (toInstEmitTm a)
   toInstEmitTm (primˢ eqᵘ a)  = primᵗ eqᵘ  (toInstEmitTm a)
   toInstEmitTm (primˢ notᵖ a) = primᵗ notᵖ (toInstEmitTm a)
   toInstEmitTm (strmˢ e)      = strmᵗ (toInstEmit e)

   -- spelled out rather than `map`ped, so the recursion is structural
   toInstEmitTms : ∀ {Δᵍ Δ Θ : List Ty} {t : Ty}
              → List (STm Γ Δᵍ Δ Θ t)
              → List (Tm (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ) (plainᵗ t))
   toInstEmitTms []       = []
   toInstEmitTms (m ∷ ms) = toInstEmitTm m ∷ toInstEmitTms ms
