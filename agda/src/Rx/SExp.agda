module Rx.SExp where

open import Data.Nat     using (ℕ)
open import Data.Bool    using (Bool)
open import Data.List    using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Vec     using (Vec; lookup) renaming (map to mapⱽ)
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
-- slot telescope and is referenced with `inputˢ`.  `mapˢ` and `scanˢ`
-- are likewise absent as formers because they are definitions over
-- `liftˢ`, exactly as their plain counterparts are over `liftᵉ`.

mutual

  data SExp {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    inputˢ      : (i : Fin n) → SExp Γ Δᵍ Δ Θ (lookup Γ i)
    ofˢ         : ∀ {t} → List (STm Γ Δᵍ Δ Θ t) → SExp Γ Δᵍ Δ Θ t
    emptyˢ      : ∀ {t} → SExp Γ Δᵍ Δ Θ t
    takeˢ       : ∀ {t} → STm Γ Δᵍ Δ Θ natᵗ → SExp Γ Δᵍ Δ Θ t → SExp Γ Δᵍ Δ Θ t
    liftˢ       : ∀ {s t u} → SFn Γ Δᵍ Δ Θ (u ×ᵗ s) (u ×ᵗ listᵗ t)
                → STm Γ Δᵍ Δ Θ u → SExp Γ Δᵍ Δ Θ s → SExp Γ Δᵍ Δ Θ t
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

-- AND AN INPUT IS A STREAM TOO, WHICH IS WHY THE INPUT VECTOR WALKS
-- WITH THE STREAM TRANSLATION AND NOT THE VALUE ONE.  The TypeScript
-- mirror settles it: an input source there is built by the driver,
-- which is what mints its source token and stamps its instant, so what
-- reaches the pipeline is already an `InstEmit`.
--
-- SO THE BOUNDARY IS ASSUMED HERE AND NOT PERFORMED, AND THAT IS NOW A
-- CHOICE RATHER THAN A NECESSITY (Anthony).  This walk once carried the
-- argument that reading inputs as bare payloads would oblige the
-- elaboration to WRAP each one, wrapping being an operation no program
-- could perform.  A program can perform it: the envelope's source is a
-- token `mintᵉ` binds, and the rest of the stamp is a fold over the
-- arriving values -- one `liftᵉ` per input, seeded once per
-- subscription.  What the seed still wants is the AMBIENT INSTANT, so
-- that a cold source's synchronous burst INHERITS the subscriber's
-- rather than minting, and that one capability is what is missing.
--
-- The choice is not cosmetic and is the elaboration's to make: wrapping
-- here leaves the slots at plain `Γ` and PROVES that a simul program
-- holds no bare payload in a stream position, where this vector only
-- ASSUMES it.

-- AND THE OBSTACLE TO WRAPPING WITH A FOLD IS NOT THE STAMP BUT THE
-- GROUPING, WHICH IS WHY A SYNCHRONY-SENSING OPERATOR IS THE WRONG
-- ANSWER (Anthony).  A fold over a flat stream of payloads cannot tell
-- which of them shared an instant, so wrapping each one separately
-- would split a cold source's subscribe burst into as many instants as
-- it has values.  The operator that recovers the boundary by TIMING --
-- collect while a flag says synchronous, release on the first
-- asynchronous turn -- is the standard rxjs repair and it re-derives
-- something this side is GIVEN: the evaluator's cold arms read the
-- split off `ObservableInput`'s own constructor, where the synchronous
-- values are a bound field and the rest are a separate list, and the
-- burst they build carries the whole field under ONE stamp.  Nothing
-- here has ever had to sense synchrony, so nothing should acquire the
-- machinery to.
--
-- What that leaves is a question about the PAYLOAD TYPE rather than
-- about a former: a source whose deliveries are already grouped -- one
-- delivery's values carried as a list -- is wrappable by an ordinary
-- fold, since a group IS an instant and no arm has to ask which kind it
-- is.  That is the shape the subscribe burst already has; it is not
-- visible in the type.
emitᵛ : ∀ {n} → Ctx n → Ctx n
emitᵛ Γ = mapⱽ emitᵗ Γ
