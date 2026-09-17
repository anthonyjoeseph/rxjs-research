module Rx.Elaborate where

open import Data.List using (List; []; _∷_)
open import Data.List.Properties using (map-++)
open import Data.List.Membership.Propositional.Properties using (∈-map⁺)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ)
open import Data.Vec.Properties using (lookup-map)
open import Relation.Binary.PropositionalEquality using (subst)

open import Rx.Exp using (Ty; Ctx; Exp; Tm; Fn; natᵗ; listᵗ; obs; _×ᵗ_;
                          input; μᵉ; varᵉ; deferᵉ;
                          varᵗ; unit̂; bool̂; nat̂; pairᵗ; fstᵗ; sndᵗ; nilᵗ;
                          consᵗ; inlᵗ; inrᵗ; caseᵗ; foldᵗ; ifᵗ; primᵗ; strmᵗ;
                          add; sub; mul; eqᵖ; ltᵖ; eqᵘ; notᵖ)
open import Rx.SExp using (SExp; STm; inputˢ; ofˢ; emptyˢ; takeˢ; liftˢ;
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
--
-- MINTING IS THE FIRST KIND AND IT IS THE HARD ONE.  A source coming
-- alive owes an `init` naming a token nothing has used, and `uniq̂` is a
-- literal — the one term that makes a token and the one the simul
-- palette deliberately does not reach, since a program that could write
-- a token could forge a collision.  So `ofᵖ` and `emptyᵖ` are blocked
-- outright, and the three flatteners are blocked on the registrations
-- they bring alive rather than on their values.
--
-- READING THE RUNNING INSTANT IS THE SECOND, AND IT IS NARROWER THAN
-- THE ELABORATION'S OWN HEADER ONCE CLAIMED.  Downstream of a source
-- the instant is not missing at all: the incoming emit IS an envelope,
-- a term can project its instant field, and a step that stamps its
-- output with the instant it was handed is an ordinary `Tm`.  Only a
-- former with NO input — the two sources — has nothing to read it off.
-- The finding is that the two gaps coincide exactly, at the sources,
-- which is also where the TypeScript mirror reaches for its driver.
--
-- `liftᵖ` AND THE FLATTENERS ARE A THIRD THING, AND SAYING SO IS THE
-- POINT: they are not blocked, they are unwritten.  A lift's whole job
-- is to unwrap, run the author's step over the value list, and rewrap
-- under the instant it was given, and every part of that is a fold, a
-- case and a pair; a flattener's values come out of `mergeAllᵉ` over
-- the observables its envelopes carry.  Each is a large term and none
-- of them needs a capability that is missing.
--
-- `takeᵖ` IS THE ONE GENUINE SURPRISE, AND IT IS NEITHER KIND.  The
-- author's operator and the plain one agree on everything that was in
-- doubt — both cut naively on values, mid-batch, and both owe the
-- closing envelope at the cut.  What they do not share is the LEVEL:
-- elaboration puts the author's values inside the envelope, so a plain
-- `takeᵉ` over an enveloped stream counts batches.
-- Counting is a lift's business and ENDING is not: no former in the
-- plain tree stops a stream on a condition read out of the values, and
-- the cut also owes a `close` the lift could otherwise have written,
-- since by then it has an instant in hand.

postulate
  -- a source coming alive owes an `init` naming a token nothing has
  -- used, and the author's values owe an instant to be stamped with.
  -- THE FIRST OF THOSE TWO IS AVAILABLE AND THE SECOND IS NOT, SO WHAT
  -- BLOCKS THIS IS THE READ ALONE.  `mintᵉ` binds an unforgeable token
  -- drawn at the scheduler's own source key, once per subscription,
  -- which is exactly the arity a SOURCE wants.  An INSTANT has a
  -- different arity, and that is the finding: the machine mints a
  -- source per cold and threads the instant IN, as an argument to
  -- subscribe handed down by the subscriber.  So a source INHERITS its
  -- instant, and it must, because the spec groups by comparing instant
  -- ids -- two colds coming alive in one frame have to carry the SAME
  -- id or the batch they belong to is split.  A fresh mint per source
  -- is the one answer that is certainly wrong.
  -- DEAD ROUTE: bracket the subscribe frame with `batchSyncᵉ` and let
  --   the grouping stand in for the id.  It brackets a frame without
  --   NAMING one, and the bracket is per node, so two colds subscribed
  --   in one frame group separately and nothing joins the two groups --
  --   which is the whole of what the id was doing.  The former is
  --   necessary here and is not sufficient.
  -- DEAD ROUTE: build both inline, out of `uniq̂` and a counter carried
  --   in a lift's state.  `uniq̂` is a literal, so a program that writes
  --   one can write one already in use — which is the forgery the palette
  --   exists to rule out — and a lift's state advances per EMIT, so it
  --   cannot tell two emits of one cascade from two cascades.  Both
  --   quantities are properties of the RUN, and the run is the
  --   scheduler's.
  ofᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
      → List (Tm Γ Δᵍ Δ Θ (plainᵗ t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- the empty srxjs source is not the empty plain one: it still brackets
  -- a subscribe frame, so it emits an envelope carrying `init` and
  -- `complete` where `emptyᵉ` emits nothing at all.
  -- DEAD ROUTE: `emptyᵉ`, which has no emit to hang the frame on; and
  --   `ofᵖ []`, which is the same mint blocked one entry up.
  emptyᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
         → Exp Γ Δᵍ Δ Θ (emitᵗ t)

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
  -- DEAD ROUTE: count in a lift and cut with `takeᵉ`.  The counting and
  --   truncation halves are both a lift's work; the ENDING half is not,
  --   since a lift cannot change how many emits pass through it, so
  --   nothing converts a budget over values into the emit index a
  --   subscription-time count has to name.
  takeᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
        → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ (emitᵗ t) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- NOT BLOCKED, ONLY UNWRITTEN, and the difference is the leg's whole
  -- finding.  The body unwraps the envelope, runs the author's step over
  -- the value list and rewraps under the instant it was HANDED, which is
  -- a fold, a case and a pair; the instant is missing only at a source.
  -- TWIN: `scanᵉ`
  liftᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {s t u : Ty}
        → Fn Γ Δᵍ Δ Θ (plainᵗ u ×ᵗ listᵗ (plainᵗ s))
                      (plainᵗ u ×ᵗ listᵗ (plainᵗ t))
        → Tm Γ Δᵍ Δ Θ (plainᵗ u)
        → Exp Γ Δᵍ Δ Θ (emitᵗ s) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- the VALUES need nothing new: a lift projects each envelope to the
  -- observables it carries, and the plain flattener runs them, their own
  -- emits being envelopes already.  What waits is the join's protocol
  -- traffic — a registration coming alive is a mint.
  -- AND THE MINT BINDER DOES NOT REACH IT, WHICH IS WHY THIS STAYS
  -- BLOCKED WHILE THE SOURCES DO NOT.  A mint draws ONE token, at the
  -- scheduler's own source key, ONCE per subscription — the arity a
  -- source wants.  A flattener brings registrations alive as the outer
  -- stream hands it observables, so the count is dynamic and the key is
  -- the registration one, a chain per subscribing path; neither is what
  -- a binder fixed at subscribe time can supply.
  -- DEAD ROUTE: elaborate the handoff and init events in the projecting
  --   lift, which has the outer emit's instant but no token to name the
  --   inner source with.
  mergeAllᵖ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → Maybe ℕ → Exp Γ Δᵍ Δ Θ (emitᵗ (obs t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

  -- the two cutting flatteners, blocked where `mergeAllᵖ` is and also on
  -- the `close` a switch owes the registration it drops.
  -- DEAD ROUTE: the projecting lift again — it sees the emit that causes
  --   the switch, and not the source being cut.
  switchAllᵖ exhaustAllᵖ :
              ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → Exp Γ Δᵍ Δ Θ (emitᵗ (obs t)) → Exp Γ Δᵍ Δ Θ (emitᵗ t)

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

mutual

  toPlain : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
          → SExp Γ Δᵍ Δ Θ t
          → Exp (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ Θ) (emitᵗ t)
  toPlain {Γ = Γ} (inputˢ i)  = subst (Exp _ _ _ _) (lookup-map i emitᵗ Γ)
                                      (input i)
  toPlain (ofˢ ts)            = ofᵖ (toPlainTms ts)
  toPlain emptyˢ              = emptyᵖ
  toPlain (takeˢ k e)         = takeᵖ (toPlainTm k) (toPlain e)
  toPlain (liftˢ f i e)       = liftᵖ (toPlainTm f) (toPlainTm i) (toPlain e)
  toPlain (mergeAllˢ k e)     = mergeAllᵖ k (toPlain e)
  toPlain (switchAllˢ e)      = switchAllᵖ (toPlain e)
  toPlain (exhaustAllˢ e)     = exhaustAllᵖ (toPlain e)
  toPlain (μˢ e)              = μᵉ (toPlain e)
  toPlain (varˢ x)            = varᵉ (∈-map⁺ emitᵗ x)
  toPlain {Γ = Γ} {Δᵍ = Δᵍ} {Δ = Δ} {Θ = Θ} (deferˢ {t = t} e) =
    deferᵉ (subst (λ ζ → Exp (emitᵛ Γ) [] ζ (plainᶜ Θ) (emitᵗ t))
                  (map-++ emitᵗ Δᵍ Δ) (toPlain e))

  toPlainTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ : List Ty} {t : Ty}
            → STm Γ Δᵍ Δ Θ t
            → Tm (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ Θ) (plainᵗ t)
  toPlainTm (varˢᵗ x)      = varᵗ (∈-map⁺ plainᵗ x)
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
             → List (Tm (emitᵛ Γ) (emitᶜ Δᵍ) (emitᶜ Δ) (plainᶜ Θ) (plainᵗ t))
  toPlainTms []       = []
  toPlainTms (m ∷ ms) = toPlainTm m ∷ toPlainTms ms
