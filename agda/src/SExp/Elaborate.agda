module SExp.Elaborate where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_; map; foldr)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing)
open import Data.Fin using (Fin; _↑ʳ_)
open import Data.Vec using (lookup; zipWith)
open import Data.Vec.Properties using (lookup-zipWith; lookup-++ʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; refl; trans)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; listᵗ; obs; _×ᵗ_; boolᵗ; uniqᵗ; input; ofᵉ; emptyᵉ; μᵉ; varᵉ; deferᵉ;
  mintᵉ; mapᵉ; scanᵉ; FlatOp; mergeᶠ; flattenᵉ; batchSyncᵉ; unitᵗ; _+ᵗ_; varᵗ; unit̂; bool̂;
  nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ; consᵗ; inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; primᵗ; strmᵗ; letᵗ;
  revᵗ; appendᵗ; renTm; renExp; ext∈; add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ; takeWhileᵉ)
open import SExp.InstEmit using (instEventᵗ; closeReasonᵗ; emitKindᵗ; eventsᵛ; instantᵛ; sourceᵛ; kindᵛ;
                               eventCaseᵛ; splitEventsᵛ; reassembleᵛ; instEmitᵛ;
                               initᵛ; valueᵛ; closeᵛ; completeᵛ;
                               machineEmitᵗ; splitAccᵗ)
open import SExp.Syntax using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeWhileˢ; mapˢ; scanˢ; flattenˢ; μˢ;
  varˢ; deferˢ; varˢᵗ; unitˢ; boolˢ; natˢ; pairˢ; fstˢ; sndˢ; nilˢ; consˢ; inlˢ; inrˢ; caseˢ;
  foldˢ; ifˢ; primˢ; strmˢ; plainᵗ; plainᶜ; emitᵗ; emitᶜ; Kinds; hotᵏ; coldᵏ; sharedᵏ; slotTy;
  rawTy; plainᵏ)

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

-- the subscribe frame: the `init` and the frame's values, under the
-- frame, tagged `subscribe`.  A later arrival: mint its instant and
-- emit its value under it.
inputStampᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {a : Ty}
            → Tm Γ Δᵍ Δ Θ uniqᵗ
            → Fn Γ Δᵍ Δ (uniqᵗ ∷ Θ) ((unitᵗ +ᵗ a) ×ᵗ listᵗ (unitᵗ +ᵗ a)) (obs (machineEmitᵗ a))
inputStampᵖ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {a = a} frame = stamp
  where
  m : Ty
  m = unitᵗ +ᵗ a

  -- under the SOURCE binder and the group
  Θᵍ : List Ty
  Θᵍ = (m ×ᵗ listᵗ m) ∷ uniqᵗ ∷ Θ

  grp : Tm Γ Δᵍ Δ Θᵍ (m ×ᵗ listᵗ m)
  grp = varᵗ (here refl)

  src : Tm Γ Δᵍ Δ Θᵍ uniqᵗ
  src = varᵗ (there (here refl))

  frameᵍ : Tm Γ Δᵍ Δ Θᵍ uniqᵗ
  frameᵍ = renTm (λ x → x) (λ x → x) (λ x → there (there x)) frame

  -- the tail in arrival order (the `revᵗ` is what makes a cons-fold
  -- rebuild the list rather than reverse it); a marker in it is
  -- dropped, and only a group's head can be one
  rest : Tm Γ Δᵍ Δ Θᵍ (listᵗ (instEventᵗ uniqᵗ a))
  rest = foldᵗ (revᵗ (sndᵗ grp)) nilᵗ
           (caseᵗ (varᵗ (here refl))
                  (varᵗ (there (there (here refl))))
                  (consᵗ (valueᵛ (varᵗ (here refl))) (varᵗ (there (there (here refl))))))

  ↑ : ∀ {s r} → Tm Γ Δᵍ Δ Θᵍ r → Tm Γ Δᵍ Δ (s ∷ Θᵍ) r
  ↑ = renTm (λ x → x) (λ x → x) there

  ↑² : ∀ {s s′ r} → Tm Γ Δᵍ Δ Θᵍ r → Tm Γ Δᵍ Δ (s′ ∷ s ∷ Θᵍ) r
  ↑² = renTm (λ x → x) (λ x → x) (λ x → there (there x))

  stamp : Tm Γ Δᵍ Δ Θᵍ (obs (machineEmitᵗ a))
  stamp = caseᵗ (fstᵗ grp)
    (strmᵗ (ofᵉ (instEmitᵛ (consᵗ (initᵛ (↑ src)) (↑ rest)) (↑ frameᵍ) (↑ src) subscribeᵛ ∷ [])))
    (strmᵗ (mintᵉ (ofᵉ (instEmitᵛ (consᵗ (valueᵛ (varᵗ (there (here refl)))) (↑² rest))
                                 (varᵗ (here refl)) (↑² src) deliveryᵛ ∷ []))))

-- the marker first, so the subscribe frame's group always exists and
-- always leads with it; the input's own values behind it
inputMarkedᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} (i : Fin n) → Exp Γ Δᵍ Δ Θ (unitᵗ +ᵗ lookup Γ i)
inputMarkedᵖ i = flatAllᵉ (mergeᶠ nothing)
  (ofᵉ (strmᵗ (ofᵉ (inlᵗ unit̂ ∷ [])) ∷
        strmᵗ (mapᵉ (inrᵗ (varᵗ (here refl))) (input i)) ∷ []))

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
-- that builds every InstEmit an input contributes: one carrying the
-- `init` and the subscribe frame's values, then one emit per later
-- ARRIVAL carrying that arrival's value.  Nothing else in the elaboration writes an input's InstEmit,
-- which is what makes a well-formedness claim about inputs a lemma
-- about this definition instead of a hypothesis about the table.
--
-- THE AMBIENT INSTANT IS RECOVERED BY GROUPING, NOT BY READING A
-- CLOCK (Anthony).  A fold over a flat stream cannot tell which values
-- shared an arrival, so wrapping each separately would split a cold's
-- subscribe burst into as many instants as it has values.
-- `batchSyncᵉ` already draws that boundary -- it emits `(head , rest)`,
-- the whole synchronous group under one value -- so a group IS an
-- instant.  Nothing here senses synchrony, which is the property the
-- machine was always GIVEN and a timing-based repair would have
-- re-derived.

-- THE SUBSCRIBE FRAME'S GROUP IS THE FRAME'S INSTANT, NOT A NEW ONE.
-- One `subscribe()` call is one batch (README), so a cold's synchronous
-- values share the instant of whatever subscribed it, and the emit
-- says so by carrying the frame, tagged `subscribe` so an enclosing
-- flattener re-instants it.  The group alone cannot say which one it
-- is -- a one-value frame and a later arrival are both `(v , [])` --
-- so a marker merged in AHEAD of the input makes the frame's group
-- always exist and always lead with the marker, and no later group
-- can.  The `init` rides the same emit, which is why there is no
-- separate announcement.
--
-- AND THE PER-ARRIVAL TOKEN COMES FROM THE MINT'S PLACEMENT, WHICH IS
-- THE ARITY THAT LOOKED MISSING.  `mintᵉ` draws once per subscription
-- of the node it stands at.  The OUTER mint stands at this node, so it
-- draws one SOURCE token per subscription of the input -- a source's
-- own arity.  The INNER mint stands at the head of a merging flattener's
-- inner, which is subscribed once per outer value, so it draws one
-- INSTANT token per later arrival.  Two arities, one former, and the
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

-- SO A HOT SCRIPT IS WRAPPED ONCE, IN THE TABLE, and not per
-- reference: `SExp.Pipeline` puts this term in a share, so every
-- subscriber of a hot slot reads one instant per arrival.  A cold
-- script re-runs per subscription, so its reference is wrapped where
-- it is read.

-- WHAT IS DELIBERATELY ABSENT: the `close` at `exhausted`.  The
-- TypeScript mirror mints one off its script's `isLast`, and
-- `batchSyncᵉ` hands over no such bit.  An input that must be seen to
-- complete is owed a separate reading of the script, not a repair of
-- this term.
inputᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} (i : Fin n)
       → Tm Γ Δᵍ Δ Θ uniqᵗ
       → Exp Γ Δᵍ Δ Θ (machineEmitᵗ (lookup Γ i))
inputᵖ i frame = mintᵉ (flatAllᵉ (mergeᶠ nothing) (mapᵉ (inputStampᵖ frame) (batchSyncᵉ (inputMarkedᵖ i))))

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
mapStepᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t : Ty}
         → Fn Γ Δᵍ Δ Θ (plainᵗ s) (plainᵗ t) → Fn Γ Δᵍ Δ Θ (emitᵗ s) (emitᵗ t)
mapStepᵖ {Θ = Θ} {s = s} {t = t} f = step
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

mapᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t : Ty}
     → Fn Γ Δᵍ Δ Θ (plainᵗ s) (plainᵗ t)
     → Exp Γ Δᵍ Δ Θ (emitᵗ s) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
mapᵖ f e = mapᵉ (mapStepᵖ f) e

-- the carried value: the author's state, and the emit built for the
-- delivery that produced it
ScanAᵗ : Ty → Ty
ScanAᵗ t = plainᵗ t ×ᵗ emitᵗ t

scanStepᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t : Ty}
          → Fn Γ Δᵍ Δ Θ (plainᵗ t ×ᵗ plainᵗ s) (plainᵗ t)
          → Fn Γ Δᵍ Δ (uniqᵗ ∷ Θ) (ScanAᵗ t ×ᵗ emitᵗ s) (ScanAᵗ t)
scanStepᵖ {Θ = Θ} {s = s} {t = t} f = step
  where
  A : Ty
  A = ScanAᵗ t

  -- the step's argument: the carried value and the arriving emit
  P : Ty
  P = A ×ᵗ emitᵗ s

  -- shift the author's step under the mint binder
  f' : Fn _ _ _ (uniqᵗ ∷ Θ) (plainᵗ t ×ᵗ plainᵗ s) (plainᵗ t)
  f' = renTm (λ x → x) (λ x → x) (ext∈ there) f

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
  mintᵉ (mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ (scanStepᵖ f) seed e'))
  where
  -- the token bound by the enclosing mint, read by nothing
  tok : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  tok = varᵗ (here refl)

  -- shift the incoming arguments under the mint binder
  z' : Tm _ _ _ (uniqᵗ ∷ Θ) (plainᵗ t)
  z' = renTm (λ x → x) (λ x → x) there z

  e' : Exp _ _ _ (uniqᵗ ∷ Θ) (emitᵗ s)
  e' = renExp (λ x → x) (λ x → x) there e

  seed : Tm _ _ _ (uniqᵗ ∷ Θ) (ScanAᵗ t)
  seed = pairᵗ z' (instEmitᵛ nilᵗ tok tok (inlᵗ unit̂))

-- THE LIST ROUTINES THE CUT IS WRITTEN OUT OF, AND THEY ARE HERE
-- BECAUSE THE TERM LANGUAGE HAS NO LIBRARY.  `Tm` has one eliminator
-- over lists and no application, so `takeWhile` and a multiset delete
-- are each a fold with a pair-shaped accumulator rather than a
-- call.  The mirror spells the same routines inline as ordinary JavaScript,
-- which is why nothing about them is a finding.

-- the prefix up to and including the first element failing the
-- predicate, and whether one did
takeWhileListᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
               → Tm Γ Δᵍ Δ (a ∷ Θ) boolᵗ → Tm Γ Δᵍ Δ Θ (listᵗ a)
               → Tm Γ Δᵍ Δ Θ (listᵗ a ×ᵗ boolᵗ)
takeWhileListᵛ {Θ = Θ} {a = a} p xs =
  letᵗ (foldᵗ xs (pairᵗ (bool̂ false) nilᵗ) body) (pairᵗ nilᵗ (bool̂ false))
       (pairᵗ (revᵗ (sndᵗ (varᵗ (here refl)))) (fstᵗ (varᵗ (here refl))))
  where
  A : Ty
  A = boolᵗ ×ᵗ listᵗ a

  acc : Tm _ _ _ (a ∷ A ∷ Θ) A
  acc = varᵗ (there (here refl))

  p↑ : Tm _ _ _ (a ∷ A ∷ Θ) boolᵗ
  p↑ = renTm (λ x → x) (λ x → x) (ext∈ there) p

  body : Tm _ _ _ (a ∷ A ∷ Θ) A
  body = ifᵗ (fstᵗ acc) acc
             (pairᵗ (primᵗ notᵖ p↑) (consᵗ (varᵗ (here refl)) (sndᵗ acc)))

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

-- THE PIPELINE THE MIRROR WRITES, OPERATOR FOR OPERATOR, FOR THE
-- CUTTING OPERATOR.  A scan carrying a budget, whether the cut has
-- happened, the open registrations and the emit this delivery produced;
-- an inclusive `takeWhileᵉ` ending on the state whose cut has happened;
-- then a projection pulling the emit back out of the state.  Cutting the
-- author's values out of one emit's list is a pure step's work, and the
-- state carries the answer and the emit together because the palette
-- reads a value and nothing beside it.  The step's own decision is the
-- CUTTER, handed the budget and one emit's payloads, which returns the
-- payloads let through, whether they end the stream, and the budget
-- left.
--
-- THE SEED'S EMIT COMPONENT IS UNOBSERVABLE, exactly as `scanᵖ`'s is: a
-- scan emits the result of its FIRST application and never the seed, so
-- the tokens below are read by nothing and claim no freshness.  One
-- `mintᵉ` supplies the inhabitant `uniqᵗ` has no literal for.
CutS : Ty → Ty → Ty
CutS B t = B ×ᵗ (boolᵗ ×ᵗ (listᵗ uniqᵗ ×ᵗ emitᵗ t))

CutSP : Ty → Ty
CutSP t = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ (plainᵗ t) ×ᵗ boolᵗ)

-- where a cutter runs: one emit's split, the step's argument, the mint's
-- token, then Θ
CutCtx : Ty → Ty → List Ty → List Ty
CutCtx B t Θ = CutSP t ∷ (CutS B t ×ᵗ emitᵗ t) ∷ uniqᵗ ∷ Θ

-- what a cutter is: handed the budget and one emit's payloads, the
-- payloads let through, whether they end the stream, and the budget left
Cutter : ∀ {n} → Ctx n → List Ty → List Ty → List Ty → Ty → Ty → Set
Cutter Γ Δᵍ Δ Θ B t = Tm Γ Δᵍ Δ (CutCtx B t Θ) B → Tm Γ Δᵍ Δ (CutCtx B t Θ) (listᵗ (plainᵗ t))
                    → Tm Γ Δᵍ Δ (CutCtx B t Θ) (listᵗ (plainᵗ t) ×ᵗ (boolᵗ ×ᵗ B))

cutStepᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t B : Ty}
         → Cutter Γ Δᵍ Δ Θ B t → Fn Γ Δᵍ Δ (uniqᵗ ∷ Θ) (CutS B t ×ᵗ emitᵗ t) (CutS B t)
cutStepᵖ {Θ = Θ} {t = t} {B = B} cutter = step
  where
  S : Ty
  S = CutS B t

  P : Ty
  P = S ×ᵗ emitᵗ t

  SP : Ty
  SP = CutSP t

  R : Ty
  R = listᵗ (plainᵗ t) ×ᵗ (boolᵗ ×ᵗ B)

  -- inside the two `letᵗ`s: the cutter's answer, the split, the step's
  -- argument, the mint's token, then Θ
  inner : Tm _ _ _ (R ∷ SP ∷ P ∷ uniqᵗ ∷ Θ) S
  inner = ifᵗ cut?
              (pairᵗ left
                     (pairᵗ (bool̂ true)
                            (pairᵗ nilᵗ
                                   (reassembleᵛ env
                                                (appendᵗ book (cutClosesᵛ open'))
                                                taken (bool̂ true)))))
              (pairᵗ left
                     (pairᵗ (bool̂ false)
                            (pairᵗ open' (reassembleᵛ env book taken fin))))
    where
    answer = varᵗ (here refl)
    taken  = fstᵗ answer
    cut?   = fstᵗ (sndᵗ answer)
    left   = sndᵗ (sndᵗ answer)
    split  = varᵗ (there (here refl))
    st     = fstᵗ (varᵗ (there (there (here refl))))
    env    = sndᵗ (varᵗ (there (there (here refl))))
    book   = fstᵗ split
    fin    = sndᵗ (sndᵗ split)
    open'  = openAfterᵛ book (fstᵗ (sndᵗ (sndᵗ st)))

  -- inside the first `letᵗ`: the split, the step's argument, the
  -- mint's token, then Θ
  body : Tm _ _ _ (SP ∷ P ∷ uniqᵗ ∷ Θ) S
  body = letᵗ (cutter (fstᵗ st) (fstᵗ (sndᵗ (varᵗ (here refl))))) st inner
    where
    st = fstᵗ (varᵗ (there (here refl)))

  step : Tm _ _ _ (P ∷ uniqᵗ ∷ Θ) S
  step = letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (sndᵗ (varᵗ (here refl)))))
              (fstᵗ (varᵗ (here refl))) body

cutOutᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t B : Ty} → Fn Γ Δᵍ Δ Θ (CutS B t) (emitᵗ t)
cutOutᵛ = sndᵗ (sndᵗ (sndᵗ (varᵗ (here refl))))

-- open until the state whose cut has happened, which still leaves
cutOpenᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t B : Ty} → Fn Γ Δᵍ Δ Θ (CutS B t) boolᵗ
cutOpenᵛ = primᵗ notᵖ (fstᵗ (sndᵗ (varᵗ (here refl))))

cutᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t B : Ty}
     → Tm Γ Δᵍ Δ (uniqᵗ ∷ Θ) B → Cutter Γ Δᵍ Δ Θ B t
     → Exp Γ Δᵍ Δ Θ (emitᵗ t) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
cutᵖ {Θ = Θ} {t = t} {B = B} b₀ cutter e =
  mintᵉ (mapᵉ cutOutᵛ (takeWhileᵉ cutOpenᵛ (scanᵉ (cutStepᵖ cutter) seed e')))
  where
  e' : Exp _ _ _ (uniqᵗ ∷ Θ) (emitᵗ t)
  e' = renExp (λ x → x) (λ x → x) there e

  tok : Tm _ _ _ (uniqᵗ ∷ Θ) uniqᵗ
  tok = varᵗ (here refl)

  seed : Tm _ _ _ (uniqᵗ ∷ Θ) (CutS B t)
  seed = pairᵗ b₀ (pairᵗ (bool̂ false)
                         (pairᵗ nilᵗ (instEmitᵛ nilᵗ tok tok subscribeᵛ)))

whileCutᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → Fn Γ Δᵍ Δ Θ (plainᵗ t) boolᵗ → Cutter Γ Δᵍ Δ Θ unitᵗ t
whileCutᵖ {Θ = Θ} {t = t} f _ vs = pairᵗ (fstᵗ (takeWhileListᵛ f↑ vs)) (pairᵗ (sndᵗ (takeWhileListᵛ f↑ vs)) unit̂)
  where
  f↑ : Tm _ _ _ (plainᵗ t ∷ CutCtx unitᵗ t Θ) boolᵗ
  f↑ = renTm (λ x → x) (λ x → x) (ext∈ (λ x → there (there (there x)))) f

-- rxjs `takeWhile(p, true)`: the payloads up to and including the first
-- the author's predicate fails, and that failure cuts.  No budget, and
-- nothing to decide at subscribe: rxjs's `takeWhile` always subscribes
-- its source.
takeWhileᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
           → Fn Γ Δᵍ Δ Θ (plainᵗ t) boolᵗ
           → Exp Γ Δᵍ Δ Θ (emitᵗ t) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
takeWhileᵖ f e = cutᵖ unit̂ (whileCutᵖ f) e

-- insert one variable ABOVE everything in scope: what a term owes for
-- each binder a `caseᵗ`, `foldᵗ` or `letᵗ` wrapped around it adds.
upᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s r} → Tm Γ Δᵍ Δ Θ r → Tm Γ Δᵍ Δ (s ∷ Θ) r
upᵛ = renTm (λ x → x) (λ x → x) there

-- one payload's echo, if it has one, onto the echoes after it
echoOntoᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a}
          → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ a)
echoOntoᵛ e vs = caseᵗ e (upᵛ vs) (consᵗ (varᵗ (here refl)) (upᵛ vs))

nullᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a} → Tm Γ Δᵍ Δ Θ (listᵗ a) → Tm Γ Δᵍ Δ Θ boolᵗ
nullᵛ vs = foldᵗ vs (bool̂ true) (bool̂ false)

-- echoes leaving between two inners: an emit of their own, under the
-- outer emit's instant, source and kind and carrying none of its
-- bookkeeping, which the first echo already put out
segᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a b}
     → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a) → Tm Γ Δᵍ Δ Θ (listᵗ b) → Tm Γ Δᵍ Δ Θ (machineEmitᵗ b)
segᵛ env vs = reassembleᵛ env nilᵗ vs (bool̂ false)

mergeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a} → List (Tm Γ Δᵍ Δ Θ (obs a)) → Tm Γ Δᵍ Δ Θ (obs a)
mergeᵛ os = strmᵗ (flatAllᵉ (mergeᶠ nothing) (ofᵉ os))

-- an inner, then the echoes after it as an `of` of their own, then the
-- lane after those, merged in that order.  With no echoes between, the
-- inner leads the lane bare, and a lone inner IS its lane.
leadᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ a b}
      → Tm Γ Δᵍ Δ Θ (obs (machineEmitᵗ b)) → Tm Γ Δᵍ Δ Θ (machineEmitᵗ a)
      → Tm Γ Δᵍ Δ Θ (listᵗ b) → Tm Γ Δᵍ Δ Θ (unitᵗ +ᵗ obs (machineEmitᵗ b))
      → Tm Γ Δᵍ Δ Θ (obs (machineEmitᵗ b))
leadᵛ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {b = b} o env vs l =
  caseᵗ l (ifᵗ (nullᵛ (upᵛ vs)) (upᵛ o) (mergeᵛ (upᵛ o ∷ seg ∷ [])))
          (ifᵗ (nullᵛ (upᵛ vs)) (mergeᵛ (upᵛ o ∷ varᵗ (here refl) ∷ []))
                                (mergeᵛ (upᵛ o ∷ seg ∷ varᵗ (here refl) ∷ [])))
  where
  seg : ∀ {s} → Tm Γ Δᵍ Δ (s ∷ Θ) (obs (machineEmitᵗ b))
  seg = strmᵗ (ofᵉ (segᵛ (upᵛ env) (upᵛ vs) ∷ []))

-- `elemᵛ` below, inside its `letᵗ`: the split, the former's argument,
-- then Θ.  NAMED
-- because a lemma transporting the split's result through it has to
-- say what it is transported through
elemBodyᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → Tm Γ Δᵍ Δ (splitAccᵗ uniqᵗ (plainᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))) (plainᵗ t)
                       ∷ emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)) ∷ Θ)
                      ((unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t)))
elemBodyᵛ {Θ = Θ} {t = t} =
  letᵗ (foldᵗ (revᵗ (fstᵗ (sndᵗ split))) (pairᵗ nilᵗ (inlᵗ unit̂)) laneStep)
       (pairᵗ (inlᵗ unit̂) (inlᵗ unit̂))
       (pairᵗ (inrᵗ (reassembleᵛ (upᵛ arg) (fstᵗ (upᵛ split)) (fstᵗ out) (sndᵗ (sndᵗ (upᵛ split)))))
              (sndᵗ out))
  where
  L : Ty
  L = unitᵗ +ᵗ obs (emitᵗ t)

  P : Ty
  P = (unitᵗ +ᵗ plainᵗ t) ×ᵗ L

  E : Ty
  E = emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))

  SP : Ty
  SP = splitAccᵗ uniqᵗ P (plainᵗ t)

  split = varᵗ (here refl)
  arg   = varᵗ (there (here refl))
  out   = varᵗ (here refl)

  -- the echoes waiting for an inner, then the lane they lead
  A : Ty
  A = listᵗ (plainᵗ t) ×ᵗ L

  -- one payload over the payloads reversed: an echo waits, and an inner
  -- leads the echoes waiting and the lane after them.  The payload, then
  -- the accumulator
  laneStep : Tm _ _ _ (P ∷ A ∷ SP ∷ E ∷ Θ) A
  laneStep = caseᵗ (sndᵗ p)
                   (pairᵗ (echoOntoᵛ (fstᵗ (upᵛ p)) (fstᵗ (upᵛ acc))) (sndᵗ (upᵛ acc)))
                   (pairᵗ (echoOntoᵛ (fstᵗ (upᵛ p)) nilᵗ)
                          (inrᵗ (leadᵛ (varᵗ (here refl)) (upᵛ env) (fstᵗ (upᵛ acc)) (sndᵗ (upᵛ acc)))))
    where
    p   = varᵗ (here refl)
    acc = varᵗ (there (here refl))
    env = varᵗ (there (there (there (here refl))))

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
-- THE ECHO IS CUT AT EACH INNER, BECAUSE THE PLAIN RUN INTERLEAVES THEM.
-- A payload echoes before its inner is subscribed, so a payload after an
-- inner echoes after that inner's synchronous emits.  The echo carries
-- the values up to the first inner; each later run of them rides the
-- lane between the inners it falls between.
--
-- THE LANE IS PER EMIT, WHICH IS RIGHT ONLY WHERE NO POLICY TELLS ONE
-- LANE FROM TWO: an unbounded merge, or an outer that never carries two
-- inners in one emit.  `flattenᵖ` takes `explodeᵛ` everywhere else.
elemᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
      → Fn Γ Δᵍ Δ Θ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))
                    ((unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t)))
elemᵛ {t = t} =
  letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (varᵗ (here refl))))
       (pairᵗ (inlᵗ unit̂) (inlᵗ unit̂)) elemBodyᵛ

-- ONE OUTER EMIT AS A RUN OF FLATTENER ELEMENTS, ONE PER INNER: the
-- first carries the echo up to the first inner beside that inner, each
-- later inner rides an element of its own whose echo is the values
-- falling after the inner before it, and values after the last inner
-- ride one element with no lane.
--
-- THE LANE IS PER INNER, BECAUSE THE POLICY IS.  A switch over a
-- synchronous pair keeps only the second inner live, and an exhaust
-- drops the second while the first is open; one lane merging both would
-- keep both.  The twin's join accepts each payload's inner on its own
-- for the same reason.
--
-- AND THE ECHO IS CUT ONLY AT AN INNER.  Between two inners one outer
-- emit is one emit out, whatever it carried; an echo per payload
-- multiplies emits through every flattener nested above, and the timed
-- translation nests several per author flattener.
explodeᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
         → Fn Γ Δᵍ Δ Θ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t)))
                       (obs ((unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t))))
explodeᵛ {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} {t = t} =
  letᵗ (splitEventsᵛ {b = plainᵗ t} (eventsᵛ (varᵗ (here refl)))) (strmᵗ emptyᵉ) body
  where
  L : Ty
  L = unitᵗ +ᵗ obs (emitᵗ t)

  P : Ty
  P = (unitᵗ +ᵗ plainᵗ t) ×ᵗ L

  Elem : Ty
  Elem = (unitᵗ +ᵗ emitᵗ t) ×ᵗ L

  E : Ty
  E = emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))

  SP : Ty
  SP = listᵗ (instEventᵗ uniqᵗ (plainᵗ t)) ×ᵗ (listᵗ P ×ᵗ boolᵗ)

  -- the echoes waiting for an inner, the inner they follow still
  -- unplaced, and whether a run follows it
  Acc : Ty
  Acc = listᵗ (plainᵗ t) ×ᵗ (L ×ᵗ (boolᵗ ×ᵗ obs Elem))

  -- one element, then the run if there is one
  before : ∀ {Θ′} → Tm Γ Δᵍ Δ Θ′ Elem → Tm Γ Δᵍ Δ Θ′ (boolᵗ ×ᵗ obs Elem) → Tm Γ Δᵍ Δ Θ′ (obs Elem)
  before x run = ifᵗ (fstᵗ run) (mergeᵛ (strmᵗ (ofᵉ (x ∷ [])) ∷ sndᵗ run ∷ []))
                                (strmᵗ (ofᵉ (x ∷ [])))

  -- echoes as an element's echo: none, or an emit of their own
  segEchoᵛ : ∀ {Θ′} → Tm Γ Δᵍ Δ Θ′ E → Tm Γ Δᵍ Δ Θ′ (listᵗ (plainᵗ t)) → Tm Γ Δᵍ Δ Θ′ (unitᵗ +ᵗ emitᵗ t)
  segEchoᵛ env vs = ifᵗ (nullᵛ vs) (inlᵗ unit̂) (inrᵗ (segᵛ env vs))

  -- the unplaced inner, its echo the values waiting, onto the run;
  -- values no inner follows ride an element of their own
  pushᵛ : ∀ {Θ′} → Tm Γ Δᵍ Δ Θ′ E → Tm Γ Δᵍ Δ Θ′ Acc → Tm Γ Δᵍ Δ Θ′ (boolᵗ ×ᵗ obs Elem)
  pushᵛ env acc =
    caseᵗ (fstᵗ (sndᵗ acc))
          (ifᵗ (nullᵛ (fstᵗ (upᵛ acc))) (sndᵗ (sndᵗ (upᵛ acc)))
               (pairᵗ (bool̂ true) (before (pairᵗ (segEchoᵛ (upᵛ env) (fstᵗ (upᵛ acc))) (inlᵗ unit̂))
                                          (sndᵗ (sndᵗ (upᵛ acc))))))
          (pairᵗ (bool̂ true) (before (pairᵗ (segEchoᵛ (upᵛ env) (fstᵗ (upᵛ acc))) (inrᵗ (varᵗ (here refl))))
                                     (sndᵗ (sndᵗ (upᵛ acc)))))

  -- one payload over the payloads reversed: an echo waits, and an inner
  -- pushes the unplaced one and takes its place.  The payload, then the
  -- accumulator
  laneStep : Tm Γ Δᵍ Δ (P ∷ Acc ∷ SP ∷ E ∷ Θ) Acc
  laneStep = caseᵗ (sndᵗ p)
                   (pairᵗ (echoOntoᵛ (fstᵗ (upᵛ p)) (fstᵗ (upᵛ acc))) (sndᵗ (upᵛ acc)))
                   (pairᵗ (echoOntoᵛ (fstᵗ (upᵛ p)) nilᵗ)
                          (pairᵗ (inrᵗ (varᵗ (here refl))) (pushᵛ (upᵛ env) (upᵛ acc))))
    where
    p   = varᵗ (here refl)
    acc = varᵗ (there (here refl))
    env = varᵗ (there (there (there (here refl))))

  -- inside the `letᵗ`: the split, the former's argument, then Θ
  body : Tm Γ Δᵍ Δ (SP ∷ E ∷ Θ) (obs Elem)
  body = letᵗ (foldᵗ (revᵗ (fstᵗ (sndᵗ split)))
                     (pairᵗ nilᵗ (pairᵗ (inlᵗ unit̂) (pairᵗ (bool̂ false) (strmᵗ emptyᵉ)))) laneStep)
              (strmᵗ emptyᵉ)
              (before first (sndᵗ (sndᵗ acc)))
    where
    split = varᵗ (here refl)
    env   = varᵗ (there (here refl))
    acc   = varᵗ (here refl)
    first = pairᵗ (inrᵗ (reassembleᵛ (upᵛ env) (fstᵗ (upᵛ split)) (fstᵗ acc) (sndᵗ (sndᵗ (upᵛ split)))))
                  (fstᵗ (sndᵗ acc))

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

-- WHETHER A FLATTENER NEEDS ONE ELEMENT PER INNER: only where its
-- policy tells one lane from two, over an outer that can carry two
-- inners in one emit.  An unbounded merge runs a merged lane exactly as
-- it runs its parts, and an `ofˢ` under maps emits one value per emit.
-- The split costs a subscription per emit, and every subscribing frame
-- on the way down is replayed, so it is paid only where it is owed.
oneInnerˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty} → SExp Γ Δᵍ Δ Θ t → Bool
oneInnerˢ (ofˢ _)    = true
oneInnerˢ (mapˢ _ e) = oneInnerˢ e
oneInnerˢ _          = false

perInnerˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty} → FlatOp → SExp Γ Δᵍ Δ Θ t → Bool
perInnerˢ (mergeᶠ nothing) e = false
perInnerˢ _                e = not (oneInnerˢ e)

-- A LANE IS SUBSCRIBED IN THE LAST INSTANT THE FLATTENER PUT OUT: the
-- echo of the outer emit that carried it, or the lane emit whose
-- completion freed its slot.  So a scan over the output carries that
-- instant and its kind, and every subscribe burst behind it takes them.
-- Inside the root frame everything is the frame and nothing moves.
-- the last instant and kind put out, and the emit put out
FlatSᵗ : Ty → Ty
FlatSᵗ t = (uniqᵗ ×ᵗ emitKindᵗ) ×ᵗ emitᵗ t

flatStepᵛ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty} → Fn Γ Δᵍ Δ Θ (FlatSᵗ t ×ᵗ emitᵗ t) (FlatSᵗ t)
flatStepᵛ = letᵗ (restampᵛ (fstᵗ (fstᵗ (fstᵗ arg))) (sndᵗ (fstᵗ (fstᵗ arg))) (sndᵗ arg))
                 (fstᵗ arg)
                 (pairᵗ (pairᵗ (instantᵛ (varᵗ (here refl))) (kindᵛ (varᵗ (here refl))))
                        (varᵗ (here refl)))
  where
  arg = varᵗ (here refl)

flattenᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty} → FlatOp → Bool
         → Tm Γ Δᵍ Δ Θ uniqᵗ
         → Exp Γ Δᵍ Δ Θ (emitᵗ ((unitᵗ +ᵗ t) ×ᵗ (unitᵗ +ᵗ obs t))) → Exp Γ Δᵍ Δ Θ (emitᵗ t)
flattenᵖ {Θ = Θ} {t = t} op perInner frame e =
  mapᵉ (sndᵗ (varᵗ (here refl))) (scanᵉ flatStepᵛ seed (flattenᵉ op (elems perInner)))
  where
  elems : Bool → Exp _ _ _ Θ ((unitᵗ +ᵗ emitᵗ t) ×ᵗ (unitᵗ +ᵗ obs (emitᵗ t)))
  elems true  = flatAllᵉ (mergeᶠ nothing) (mapᵉ explodeᵛ e)
  elems false = mapᵉ elemᵛ e

  seed : Tm _ _ _ Θ (FlatSᵗ t)
  seed = pairᵗ (pairᵗ frame subscribeᵛ) (instEmitᵛ nilᵗ frame frame subscribeᵛ)

-- what a deferred body runs as: its begin marker, then the body, each
-- delivery restamped under the instant its arrival minted
deferBodyᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {u : Ty}
           → Exp Γ Δᵍ Δ Θ (machineEmitᵗ u) → Exp Γ Δᵍ Δ Θ (machineEmitᵗ u)
deferBodyᵖ b =
  mintᵉ (mapᵉ (restampᵛ (varᵗ (there (here refl))) deliveryᵛ (varᵗ (here refl)))
    (flatAllᵉ (mergeᶠ nothing) (ofᵉ (
      strmᵗ (ofᵉ (instEmitᵛ nilᵗ (varᵗ (here refl)) (varᵗ (here refl)) deliveryᵛ ∷ [])) ∷
      strmᵗ (renExp (λ x → x) (λ x → x) there b) ∷ []))))

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

-- the author's slot i is the STAMPED half's slot `n ↑ʳ i`
stampedSlot : ∀ {n} (Γ : Ctx n) (κ : Kinds n) (i : Fin n)
            → lookup (plainᵏ Γ κ) (n ↑ʳ i) ≡ slotTy (lookup Γ i) (lookup κ i)
stampedSlot {n} Γ κ i =
  trans (lookup-++ʳ (zipWith rawTy Γ κ) (zipWith slotTy Γ κ) i) (lookup-zipWith slotTy i Γ κ)

-- A SLOT ALREADY AT THE INSTEMIT, READ: the share wrapped it once, so
-- the reference only hands its subscribe-kind emits this program's
-- frame.
readStampedᵖ : ∀ {m} {Γ : Ctx m} {Δᵍ Δ Θ : List Ty} {u : Ty} (j : Fin m)
             → lookup Γ j ≡ machineEmitᵗ u → Tm Γ Δᵍ Δ Θ uniqᵗ
             → Exp Γ Δᵍ Δ Θ (machineEmitᵗ u)
readStampedᵖ {Γ = Γ} {Δᵍ} {Δ} {Θ} j eq frame =
  mapᵉ (restampᵛ (renTm (λ x → x) (λ x → x) there frame) subscribeᵛ (varᵗ (here refl)))
       (subst (Exp Γ Δᵍ Δ Θ) eq (input j))

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
   -- cares how a slot is supplied.  Every arm reads the STAMPED half's
   -- slot `n ↑ʳ i` and lands at `emitᵗ (lookup Γ i)`: a COLD slot stands
   -- at `plainᵗ`, so `inputᵖ` wrapping it gives `machineEmitᵗ (plainᵗ
   -- _)`, which IS that type; a HOT or SHARED one stands at `emitᵗ`
   -- already, wrapped once by the share every reference reads, so
   -- nothing is wrapped a second time and its subscribe-kind emits take
   -- this program's frame.
   toInstEmit {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (inputˢ i)
     with lookup κ i | stampedSlot Γ κ i
   ... | coldᵏ   | eq =
         subst (λ u → Exp (plainᵏ Γ κ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ⁺ Θ)
                          (machineEmitᵗ u))
               eq (inputᵖ (n ↑ʳ i) (frameᵛ Θ))
   ... | hotᵏ    | eq = readStampedᵖ (n ↑ʳ i) eq (frameᵛ Θ)
   ... | sharedᵏ | eq = readStampedᵖ (n ↑ʳ i) eq (frameᵛ Θ)
   toInstEmit {Θ = Θ} (ofˢ ts)    = ofᵖ (frameᵛ Θ) (toInstEmitTms ts)
   toInstEmit {Θ = Θ} emptyˢ      = emptyᵖ (frameᵛ Θ)
   toInstEmit (takeWhileˢ f e)    = takeWhileᵖ (toInstEmitTm f) (toInstEmit e)
   toInstEmit (mapˢ f e)          = mapᵖ (toInstEmitTm f) (toInstEmit e)
   toInstEmit (scanˢ f z e)       = scanᵖ (toInstEmitTm f) (toInstEmitTm z) (toInstEmit e)
   toInstEmit {Θ = Θ} (flattenˢ op e) = flattenᵖ op (perInnerˢ op e) (frameᵛ Θ) (toInstEmit e)
   toInstEmit (μˢ e)              = μᵉ (toInstEmit e)
   toInstEmit (varˢ x)            = varᵉ (∈-map⁺ emitᵗ x)
   -- A DEFERRED HOP IS A NEW INSTANT, AND IT SAYS SO BEFORE ANYTHING
   -- ELSE.  The hop's first emit is an empty one under its own token, so
   -- a reader learns that the previous instant is over even when the
   -- body puts out nothing -- an unproductive `μ` looping through a
   -- defer is the case where nothing else ever would.  It LEADS the
   -- body rather than trailing it because a trailer is followed by
   -- whatever the body's completion subscribes, in this same instant.
   toInstEmit {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (deferˢ {t = t} e) =
     deferᵉ (deferBodyᵖ (subst (λ ζ → Exp (plainᵏ Γ κ) [] ζ (plainᶜ⁺ Θ) (emitᵗ t))
                              (map-++ emitᵗ Δᵍ Δ) (toInstEmit e)))

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
