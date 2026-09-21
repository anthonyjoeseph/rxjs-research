module Rx.SExp where

open import Data.Nat     using (ℕ)
open import Data.Bool    using (Bool)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec     using (Vec; lookup; zipWith) renaming (map to mapⱽ)
open import Data.Fin     using (Fin)
open import Data.Maybe   using (Maybe)

open import Rx.Exp      using (Ty; Ctx; unitᵗ; boolᵗ; natᵗ; uniqᵗ; _×ᵗ_; _+ᵗ_;
                               listᵗ; obs; PrimOp)
open import Rx.Envelope using (machineEmitᵗ)

------------------------------------------------------------------
-- The SIMUL tree: what an srxjs author writes.
------------------------------------------------------------------

-- A SECOND SYNTAX WHOSE FORMERS ARE THE SHIPPED OPERATORS, AND WHOSE
-- INDEX IS THE AUTHOR'S PAYLOAD.  `Rx.Exp` is the whole of what the
-- evaluator runs and is deliberately larger than anything anyone should
-- compose: it can build an emit by hand, and once the envelope is an
-- ordinary type of the object language it can build one of those too.
-- The theorem is not about that language.  It is about programs made of
-- the operators this development ships, so those operators are a
-- SYNTAX, and being outside it is a scope error rather than a side
-- condition anything has to carry.
--
-- WHAT KEEPS THE ENVELOPE HONEST IS THE PALETTE AND NOT A PREDICATE.
-- No former below reaches the term that makes a token, so no simul
-- program can name an instant or a source, let alone forge one that
-- collides; the elaboration is the only thing that writes those fields
-- and the evaluator is the only thing that mints their values.  That is
-- why the author's payload index here is a plain `Ty` with no envelope
-- anywhere in it, while the elaboration's result stands at the envelope
-- — the wrapper appears exactly once, at the boundary between the two
-- trees, instead of being threaded through a program's own types.
--
-- THE PALETTE IS THE TYPESCRIPT ONE, NAME FOR NAME, which is what makes
-- the two implementations comparable at all rather than merely
-- analogous.  `share` is absent from both for the same reason: a shared
-- observable is a BINDING and not an expression, so it lives in the
-- slot telescope and is referenced with `inputˢ`.  The two pure-function
-- formers are `mapˢ` and `scanˢ` for the reason their plain
-- counterparts are two: rxjs ships two operators and neither derives
-- from the other, so one former over a step returning a LIST would be
-- an operator the palette is supposed to mirror and does not have.

mutual

  data SExp {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    inputˢ      : (i : Fin n) → SExp Γ Δᵍ Δ Θ (lookup Γ i)
    ofˢ         : ∀ {t} → List (STm Γ Δᵍ Δ Θ t) → SExp Γ Δᵍ Δ Θ t
    emptyˢ      : ∀ {t} → SExp Γ Δᵍ Δ Θ t
    takeˢ       : ∀ {t} → STm Γ Δᵍ Δ Θ natᵗ → SExp Γ Δᵍ Δ Θ t → SExp Γ Δᵍ Δ Θ t
    mapˢ        : ∀ {s t} → SFn Γ Δᵍ Δ Θ s t → SExp Γ Δᵍ Δ Θ s → SExp Γ Δᵍ Δ Θ t
    scanˢ       : ∀ {s t} → SFn Γ Δᵍ Δ Θ (t ×ᵗ s) t
                → STm Γ Δᵍ Δ Θ t → SExp Γ Δᵍ Δ Θ s → SExp Γ Δᵍ Δ Θ t
    mergeAllˢ   : ∀ {t} → Maybe ℕ → SExp Γ Δᵍ Δ Θ (obs t) → SExp Γ Δᵍ Δ Θ t
    switchAllˢ exhaustAllˢ :
                  ∀ {t} → SExp Γ Δᵍ Δ Θ (obs t) → SExp Γ Δᵍ Δ Θ t
    μˢ          : ∀ {t} → SExp Γ (t ∷ Δᵍ) Δ Θ t → SExp Γ Δᵍ Δ Θ t
    varˢ        : ∀ {t} → t ∈ Δ → SExp Γ Δᵍ Δ Θ t
    deferˢ      : ∀ {t} → SExp Γ [] (Δᵍ ++ Δ) Θ t → SExp Γ Δᵍ Δ Θ t

  -- The author's TERM language is the plain one with its observable
  -- former re-pointed at the simul tree.  Everything else is copied
  -- rather than shared because the two trees' observables are different
  -- objects: a `Tm`'s `strmᵗ` holds a program the evaluator runs, and an
  -- author's holds a program that has not been elaborated yet.
  data STm {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    varˢᵗ  : ∀ {t} → t ∈ Θ → STm Γ Δᵍ Δ Θ t
    unitˢ  : STm Γ Δᵍ Δ Θ unitᵗ
    boolˢ  : Bool → STm Γ Δᵍ Δ Θ boolᵗ
    natˢ   : ℕ → STm Γ Δᵍ Δ Θ natᵗ
    pairˢ  : ∀ {s t} → STm Γ Δᵍ Δ Θ s → STm Γ Δᵍ Δ Θ t → STm Γ Δᵍ Δ Θ (s ×ᵗ t)
    fstˢ   : ∀ {s t} → STm Γ Δᵍ Δ Θ (s ×ᵗ t) → STm Γ Δᵍ Δ Θ s
    sndˢ   : ∀ {s t} → STm Γ Δᵍ Δ Θ (s ×ᵗ t) → STm Γ Δᵍ Δ Θ t
    nilˢ   : ∀ {t} → STm Γ Δᵍ Δ Θ (listᵗ t)
    consˢ  : ∀ {t} → STm Γ Δᵍ Δ Θ t → STm Γ Δᵍ Δ Θ (listᵗ t)
           → STm Γ Δᵍ Δ Θ (listᵗ t)
    inlˢ   : ∀ {s t} → STm Γ Δᵍ Δ Θ s → STm Γ Δᵍ Δ Θ (s +ᵗ t)
    inrˢ   : ∀ {s t} → STm Γ Δᵍ Δ Θ t → STm Γ Δᵍ Δ Θ (s +ᵗ t)
    caseˢ  : ∀ {s t u} → STm Γ Δᵍ Δ Θ (s +ᵗ t)
           → STm Γ Δᵍ Δ (s ∷ Θ) u → STm Γ Δᵍ Δ (t ∷ Θ) u → STm Γ Δᵍ Δ Θ u
    foldˢ  : ∀ {s u} → STm Γ Δᵍ Δ Θ (listᵗ s) → STm Γ Δᵍ Δ Θ u
           → STm Γ Δᵍ Δ (s ∷ u ∷ Θ) u → STm Γ Δᵍ Δ Θ u
    ifˢ    : ∀ {t} → STm Γ Δᵍ Δ Θ boolᵗ → STm Γ Δᵍ Δ Θ t → STm Γ Δᵍ Δ Θ t
           → STm Γ Δᵍ Δ Θ t
    primˢ  : ∀ {s t} → PrimOp s t → STm Γ Δᵍ Δ Θ s → STm Γ Δᵍ Δ Θ t
    strmˢ  : ∀ {t} → SExp Γ Δᵍ Δ Θ t → STm Γ Δᵍ Δ Θ (obs t)

  SFn : ∀ {n} → Ctx n → List Ty → List Ty → List Ty → Ty → Ty → Set
  SFn Γ Δᵍ Δ Θ s t = STm Γ Δᵍ Δ (s ∷ Θ) t

------------------------------------------------------------------
-- The type translation the elaboration runs over.
------------------------------------------------------------------

-- AN AUTHOR'S TYPE AND THE TYPE ITS ELABORATION STANDS AT DIFFER IN
-- EXACTLY ONE PLACE, and it is not the outermost one.  A simul program
-- at `t` elaborates to a plain program at the machine envelope over
-- `t`, so the wrapper at the top is applied by the elaboration's own
-- signature; what this walk is for is the wrappers UNDERNEATH, since a
-- nested observable is a value the author wrote at `obs t` and the
-- elaborated program carries at `obs (machineEmitᵗ (plainᵗ t))`.
-- Everything else is structural, which is what makes the two languages
-- share their values everywhere no observable occurs.
plainᵗ : Ty → Ty
plainᵗ unitᵗ    = unitᵗ
plainᵗ boolᵗ    = boolᵗ
plainᵗ natᵗ     = natᵗ
plainᵗ uniqᵗ    = uniqᵗ
plainᵗ (s ×ᵗ t)  = plainᵗ s ×ᵗ plainᵗ t
plainᵗ (s +ᵗ t)   = plainᵗ s +ᵗ plainᵗ t
plainᵗ (listᵗ t)  = listᵗ (plainᵗ t)
plainᵗ (obs t)    = obs (machineEmitᵗ (plainᵗ t))

plainᶜ : List Ty → List Ty
plainᶜ ts = map plainᵗ ts

-- WHAT A STREAM NAME STANDS AT IS WHAT ITS SUBTREE ELABORATES TO, AND
-- THAT IS NOT WHAT A VALUE NAME STANDS AT.  A μ-bound name in a simul
-- program is a STREAM at the author's payload, so the program it
-- elaborates to binds one at the envelope over the translated payload;
-- a `Θ` name is an ordinary value and carries no envelope anywhere.
-- One translation cannot serve both, so the elaboration's four contexts
-- split two and two: the two stream telescopes walk with `emitᶜ` and
-- the value telescope with `plainᶜ`.
emitᵗ : Ty → Ty
emitᵗ t = machineEmitᵗ (plainᵗ t)

emitᶜ : List Ty → List Ty
emitᶜ ts = map emitᵗ ts

------------------------------------------------------------------
-- How a slot is SUPPLIED, which the author does not see.
------------------------------------------------------------------

-- A SLOT'S KIND IS A PROPERTY OF THE TABLE AND NOT OF THE PROGRAM,
-- which is why it is not an index of `SExp`.  An author writes
-- `inputˢ i` without caring whether slot i is fed by a script or
-- defined by another srxjs program; the ELABORATION cares, because the
-- two arrive in different shapes, so the kinds are an argument to
-- `toPlain` and nothing above it changes.
data Kind : Set where
  scriptedᵏ : Kind   -- an external source: bare payloads, `inputᵖ` wraps them
  sharedᵏ   : Kind   -- another srxjs program: already elaborated

Kinds : ℕ → Set
Kinds n = Vec Kind n

-- WHAT A SLOT STANDS AT, NOW PER SLOT RATHER THAN UNIFORMLY.
--
-- A SCRIPTED SLOT STANDS AT THE PAYLOAD, and it has to: a script is
-- arbitrary, so standing it at the envelope would let a table name an
-- instant past the counter and reach the output through `input`
-- untouched -- exactly how `evaluate-accepted` was refuted.  `inputᵖ`
-- wrapping it is what makes a claim about inputs a lemma about the
-- elaboration rather than a hypothesis about the table.
--
-- THE TYPESCRIPT MIRROR IS WHAT SETTLES IT RATHER THAN THE PROOF'S
-- CONVENIENCE.  `input-source.ts`'s `makeInputSource` takes an
-- `ObservableInput<Val>` -- bare payloads and waits -- and returns an
-- `Observable<InstEmit<Val>>`.  It is the only door into a pipeline, so
-- srxjs cannot BE handed a malformed input stream; a slot at the
-- envelope models a system that can, which is the model being wrong
-- about the artifact rather than the artifact being unproven.
--
-- WHAT UNBLOCKED THE WRAPPING WAS THE GROUPING AND NOT A NEW FORMER.
-- The standing argument was that a fold over a flat stream cannot tell
-- which payloads shared an arrival, so wrapping each separately would
-- split a cold's subscribe burst into as many instants as it has
-- values -- and that the AMBIENT INSTANT needed to repair it was
-- unreachable.  A synchrony-sensing operator is the wrong answer
-- twice: rxjs has none, so the palette would stop mirroring, and it
-- would re-derive by timing what this side is GIVEN.  `batchSyncᵉ`
-- already draws the boundary, so a group IS an instant and the mint
-- has something to key on.  See `inputᵖ` for the placement that gives
-- one token per arrival.
--
-- A SHARED SLOT STANDS AT THE ENVELOPE, and the same objection does
-- not reach it, because its content is not a script.  A shared
-- definition is an srxjs program, so it has ALREADY been elaborated
-- and already carries the envelopes `inputᵖ` would otherwise build --
-- which is why the reference to it is a transport and not a second
-- wrapping.  Wrapping it twice is what refuted `mapᵉ laneᵛ ∘
-- elaborate` as a reading, over an empty inner and so structurally.
slotTy : Ty → Kind → Ty
slotTy t scriptedᵏ = plainᵗ t
slotTy t sharedᵏ   = emitᵗ t

-- the context an elaborated program stands in: the author's types,
-- read through the kinds
plainᵏ : ∀ {n} → Ctx n → Kinds n → Ctx n
plainᵏ Γ κ = zipWith slotTy Γ κ
