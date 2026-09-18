module Rx.Exp where

open import Data.Nat     using (ℕ; _+_; _∸_; _*_; _≡ᵇ_; _<ᵇ_)
open import Data.Bool    using (Bool; true; false; not; _∧_; if_then_else_)
open import Data.List    using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻; ∈-++⁺ˡ; ∈-++⁺ʳ)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Vec     using (Vec; lookup)
open import Data.Fin     using (Fin; toℕ)
open import Data.Maybe   using (Maybe)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit    using (⊤; tt)
open import Data.Sum     using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)


------------------------------------------------------------------
-- Types (sums included, for Either/error and sentinel patterns)
------------------------------------------------------------------

data Ty : Set where
  unitᵗ boolᵗ natᵗ : Ty
  uniqᵗ : Ty
  _×ᵗ_ _+ᵗ_ : Ty → Ty → Ty
  listᵗ : Ty → Ty
  obs : Ty → Ty

Ctx : ℕ → Set
Ctx n = Vec Ty n

-- A type is DATA when no `obs` occurs anywhere inside it.  An observable
-- value is a CLOSURE — an arbitrary expression paired with an environment
-- for its free token variables — so a value at a non-data type smuggles
-- unbounded syntax in from outside the program.  Nested occurrences
-- count: `natᵗ ×ᵗ obs natᵗ` is reachable with `mapᵉ (sndᵗ …)`, so the
-- check has to be hereditary.  This is the side condition on scripted
-- slots (Rx.Evaluator.Slot).
isData : Ty → Bool
isData unitᵗ    = true
isData boolᵗ    = true
isData natᵗ     = true
isData uniqᵗ    = true
isData (s ×ᵗ t) = if isData s then isData t else false
isData (s +ᵗ t) = if isData s then isData t else false
isData (listᵗ t) = isData t
isData (obs _)  = false

-- concrete now (the JSON bridge fixes exactly this set): the binary ops
-- take a pair; sub is ℕ monus; eq/lt compare nats
data PrimOp : Ty → Ty → Set where
  add sub mul : PrimOp (natᵗ ×ᵗ natᵗ) natᵗ
  eqᵖ ltᵖ     : PrimOp (natᵗ ×ᵗ natᵗ) boolᵗ
  eqᵘ         : PrimOp (uniqᵗ ×ᵗ uniqᵗ) boolᵗ
  notᵖ        : PrimOp boolᵗ boolᵗ


------------------------------------------------------------------
-- Syntax.  Contexts: Γ inputs, Δᵍ guarded μ-vars, Δ usable μ-vars,
-- Θ value vars.  μᵉ binds into Δᵍ; deferᵉ is the sole gate moving
-- Δᵍ into scope — synchronous self-reference is a type error.
------------------------------------------------------------------

mutual

  data Exp {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    input      : (i : Fin n) → Exp Γ Δᵍ Δ Θ (lookup Γ i)
    ofᵉ        : ∀ {t} → List (Tm Γ Δᵍ Δ Θ t) → Exp Γ Δᵍ Δ Θ t
    emptyᵉ     : ∀ {t} → Exp Γ Δᵍ Δ Θ t
    takeᵉ      : ∀ {t} → Tm Γ Δᵍ Δ Θ natᵗ → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ t
                 -- count is a term: evaluated once, at subscription time
    batchSyncᵉ : ∀ {t} → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ (t ×ᵗ listᵗ t)
                 -- THE ONE PLAIN OPERATOR THAT CAN SEE SYNCHRONY, AND IT
                 -- SEES EXACTLY ONE BIT OF IT.  The subscribe frame's
                 -- values leave as ONE group; every value arriving after
                 -- that leaves as its own singleton.  The result is
                 -- NONEMPTY by construction -- head and tail, so no new
                 -- `Ty` is needed -- because an empty subscribe burst
                 -- emits nothing at all rather than an empty group,
                 -- which is what the TypeScript `captureSync` does when
                 -- its burst array comes back empty.
                 --
                 -- WHAT IT CANNOT DO IS THE REASON IT EXISTS.  Cutting a
                 -- batch of genuinely simultaneous emissions means
                 -- knowing when NOT to cut -- whether more is still owed
                 -- this instant -- and that is forward-looking knowledge
                 -- no operator reading its own input can have.  This one
                 -- knows a single bit, whether its subscribe call has
                 -- returned.  It learns nothing about where a value came
                 -- from and nothing about parents, siblings or children,
                 -- so it can separate a cold's initial burst from the
                 -- rest and NOTHING FURTHER.  Recovering a true instant
                 -- is `batchSimultaneous`'s job and needs the
                 -- registration counts; that this operator cannot reach
                 -- it is why that one has to be proven rather than
                 -- assumed.
    mapᵉ       : ∀ {s t} → Fn Γ Δᵍ Δ Θ s t → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
    scanᵉ      : ∀ {s t} → Fn Γ Δᵍ Δ Θ (t ×ᵗ s) t
               → Tm Γ Δᵍ Δ Θ t → Exp Γ Δᵍ Δ Θ s → Exp Γ Δᵍ Δ Θ t
                 -- THE PURE-FUNCTION FORMERS, AND THERE ARE TWO OF THEM
                 -- BECAUSE RXJS HAS TWO.  Each is ONE value in and ONE
                 -- value out, `scanᵉ` threading the carried state that is
                 -- also what it emits — which is `map` and `scan`
                 -- exactly, operator for operator, with no notion of a
                 -- frame anywhere in either.  The step is a `Tm`, so it
                 -- is pure, total and first-order.
                 --
                 -- NEITHER IS DERIVABLE FROM THE OTHER, WHICH IS WHY
                 -- RXJS CARRIES BOTH.  A scan's accumulator IS its
                 -- output, so changing the value's type needs a seed at
                 -- the new type, and `Tm` has no generic inhabitant to
                 -- default one to; a map carries no state, so it cannot
                 -- stand in for a scan either.
                 --
                 -- ZERO-OR-MORE OUT IS NOT THEIR JOB, AND THAT IS NOT A
                 -- GAP.  A step that could emit a LIST would be a
                 -- flatten fused into a map, and rxjs has no such
                 -- operator for a reason — flattening is ambiguous, which
                 -- is why `mergeAll`, `switchAll` and `exhaustAll` are
                 -- three operators and not one.  So filter is
                 -- `mergeAllᵉ` over a step returning `strmᵗ (ofᵉ [ x ])`
                 -- or `strmᵗ emptyᵉ`, and duplicate is the same with a
                 -- two-element `ofᵉ`: `mergeMap(x => p(x) ? of(x) :
                 -- EMPTY)`, which is how a plain rxjs program writes it.
                 --
                 -- AND THE INNER SUBSCRIPTION THAT COSTS IS THE POINT
                 -- RATHER THAN A PRICE — the spec is built around
                 -- `mergeMap(of)` merging its synchronous bursts, so a
                 -- former invented to avoid that hop would be avoiding
                 -- the thing under test.
                 --
                 -- WHAT THEY ABSORB IS DECIDED BY WHETHER AN OPERATOR
                 -- READS THE PROTOCOL'S OWN BOOKKEEPING, and that test
                 -- was run in TypeScript against real rxjs before it was
                 -- written here.
                 -- `takeᵉ` is NOT absorbed, because it reads the open
                 -- registrations and the cut ledger and mints a close per
                 -- victim, so absorbing it would put source ids and close
                 -- reasons into the value language.  The flatteners cannot
                 -- follow it in for a different reason: their payloads are
                 -- literal syntax that must be RUN, and `Tm` has no
                 -- eliminator for that.
                 --
                 -- THE REST OF THE PALETTE HAS BEEN PUT TO THE SAME TEST,
                 -- and the verdicts are a column of `scripts/formers.tsv`
                 -- rather than a sentence each here, so that a former added
                 -- later inherits the obligation to have one.  The sources
                 -- pass it trivially in the other direction — they produce
                 -- without reading anything and subscribe nothing — while
                 -- `deferᵉ` fails it the way `takeᵉ` does, since what it
                 -- moves is the SUBSCRIPTION, which is protocol and not
                 -- value.  `μᵉ` and `varᵉ` are not operators at all and the
                 -- test does not apply: they are the binding structure the
                 -- operators sit inside.
               -- NOTE: share is NOT an Exp primitive — share identity is a
               -- binding, not an expression.  Shared observables live in the
               -- slot telescope (Rx.Evaluator.Slot) and are referenced with
               -- `input`, exactly like scripted inputs
    mergeAllᵉ   : ∀ {t} → Maybe ℕ → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
                 -- ONE higher-order primitive, carrying rxjs's own
                 -- `concurrent` argument.  `nothing` is Infinity, which is
                 -- plain `mergeAll`; `just 1` is `concatAll`; `just k` for k ≥ 2
                 -- is the bounded `mergeMap(f , k)` that has no name of its
                 -- own in rxjs and that nothing in this development could
                 -- previously express.  The limit is a `Maybe ℕ` and NOT a
                 -- `Tm`, unlike `takeᵉ`'s count: rxjs fixes `concurrent` when
                 -- the pipeline is BUILT, not when it is subscribed, so a
                 -- limit that varied per subscription would be a capability
                 -- the real operator does not have.  `just 0` is degenerate
                 -- but well defined — the queue grows and nothing is ever
                 -- subscribed — and is left representable rather than ruled
                 -- out by a side condition, which would have to be threaded
                 -- through every well-formedness face to buy the exclusion
                 -- of one program already indistinguishable from `emptyᵉ` on
                 -- its outputs.
    switchAllᵉ exhaustAllᵉ :
                 ∀ {t} → Exp Γ Δᵍ Δ Θ (obs t) → Exp Γ Δᵍ Δ Θ t
    μᵉ         : ∀ {t} → Exp Γ (t ∷ Δᵍ) Δ Θ t → Exp Γ Δᵍ Δ Θ t
    varᵉ       : ∀ {t} → t ∈ Δ → Exp Γ Δᵍ Δ Θ t
    deferᵉ     : ∀ {t} → Exp Γ [] (Δᵍ ++ Δ) Θ t → Exp Γ Δᵍ Δ Θ t
                 -- subscribe at tick k ⇒ body subscribed at k+1, fresh ids
    mintᵉ      : ∀ {t} → Exp Γ Δᵍ Δ (uniqᵗ ∷ Θ) t → Exp Γ Δᵍ Δ Θ t
                 -- A FRESH SOURCE TOKEN, BOUND AND NEVER WRITTEN.  A source
                 -- coming alive owes an `init` naming a token nothing has
                 -- used, and the elaboration of the srxjs sources is the only
                 -- thing that writes one.  So the capability is a BINDER and
                 -- not a term former: a term former at `uniqᵗ` would be a
                 -- LITERAL, and a program that can write one can write one
                 -- already in use, which is the forgery the palette exists to
                 -- rule out.  `Tm` has no such former, and the evaluator
                 -- never needs one because it closes bodies by ENVIRONMENT
                 -- rather than by substitution — nothing reifies a value back
                 -- into a term, so nothing owes a term at `uniqᵗ`.
                 -- Minting belongs to
                 -- the run, so the token arrives from the scheduler's own
                 -- ledger at the key `deferᵉ` already draws from — one per
                 -- SUBSCRIPTION, and nesting is how a body needing two gets
                 -- two.  Binding it into Θ is what lets the body PLACE it; the
                 -- only eliminator `uniqᵗ` has is equality, so placing is very
                 -- nearly all a body can do with it.
                 --
                 -- IT IS NOT IN THE SIMUL TREE AND MUST NOT BE.  The palette
                 -- argument is that no former an author composes reaches the
                 -- term that makes a token.  A binder only the elaboration
                 -- emits leaves that argument standing; the same binder in
                 -- `SExp` would hand every author a token to collide with.

  data Tm {n} (Γ : Ctx n) (Δᵍ Δ Θ : List Ty) : Ty → Set where
    varᵗ  : ∀ {t} → t ∈ Θ → Tm Γ Δᵍ Δ Θ t
    unit̂  : Tm Γ Δᵍ Δ Θ unitᵗ
    bool̂  : Bool → Tm Γ Δᵍ Δ Θ boolᵗ
    nat̂   : ℕ → Tm Γ Δᵍ Δ Θ natᵗ
    pairᵗ : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s ×ᵗ t)
    fstᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ s
    sndᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ (s ×ᵗ t) → Tm Γ Δᵍ Δ Θ t
    nilᵗ  : ∀ {t} → Tm Γ Δᵍ Δ Θ (listᵗ t)
    consᵗ : ∀ {t} → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (listᵗ t)
          → Tm Γ Δᵍ Δ Θ (listᵗ t)
    inlᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    inrᵗ  : ∀ {s t} → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
    caseᵗ : ∀ {s t u} → Tm Γ Δᵍ Δ Θ (s +ᵗ t)
          → Tm Γ Δᵍ Δ (s ∷ Θ) u → Tm Γ Δᵍ Δ (t ∷ Θ) u → Tm Γ Δᵍ Δ Θ u
    foldᵗ : ∀ {s u} → Tm Γ Δᵍ Δ Θ (listᵗ s) → Tm Γ Δᵍ Δ Θ u
          → Tm Γ Δᵍ Δ (s ∷ u ∷ Θ) u → Tm Γ Δᵍ Δ Θ u
    ifᵗ   : ∀ {t} → Tm Γ Δᵍ Δ Θ boolᵗ → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ t
          → Tm Γ Δᵍ Δ Θ t
    primᵗ : ∀ {s t} → PrimOp s t → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ t
    strmᵗ : ∀ {t} → Exp Γ Δᵍ Δ Θ t → Tm Γ Δᵍ Δ Θ (obs t)

  Fn : ∀ {n} → Ctx n → List Ty → List Ty → List Ty → Ty → Ty → Set
  Fn Γ Δᵍ Δ Θ s t = Tm Γ Δᵍ Δ (s ∷ Θ) t

Closed : ∀ {n} → Ctx n → Ty → Set
Closed Γ t = Exp Γ [] [] [] t

------------------------------------------------------------------
-- Val: an observable value is a CLOSURE, and that is what keeps a
-- token out of the term language
------------------------------------------------------------------

-- THE `obs` ARM USED TO READ AN OBSERVABLE VALUE AS A CLOSED
-- EXPRESSION, AND THAT IS WHAT PUT A NUMERAL IN THE TERM LANGUAGE.
-- Closing an expression is the evaluator's job, and the only closing
-- move a first-order evaluator has is SUBSTITUTION -- which obliges
-- every bindable value to be DENOTABLE by a closed term, at every type,
-- the provenance token included.  A token a term can denote is a token
-- a program can forge, so the two requirements are one requirement with
-- opposite signs, and the literal was the sign flip.
--
-- CARRYING THE ENVIRONMENT INSTEAD BUYS THE WHOLE QUESTION.  An
-- observable value is a CLOSURE -- the expression together with the
-- environment its free binders stand in -- so nothing is ever
-- substituted and no value is ever denoted.  The token stays a runtime
-- quantity the scheduler mints and the term language cannot write.
--
-- AND THE ENVIRONMENT IS ITS OWN DATATYPE BECAUSE THE ARM CANNOT BE
-- WRITTEN BY RECURSION ON `Ty`.  A closure's environment is indexed by
-- the binder telescope its body stands under, and those types are not
-- smaller than `obs t`, so an equation reaching for `All (Val Γ) Θ`
-- would ask for `Val` at types the recursion has no access to.  As a
-- DATATYPE mutual with the recursion the same occurrence is strictly
-- positive and costs nothing -- and it costs nothing in the sense that
-- matters: every other arm still COMPUTES, so a value at a data type is
-- still the bare `ℕ`, `Bool` or pair it always was.
mutual

  Val : ∀ {n} → Ctx n → Ty → Set
  Val Γ unitᵗ    = ⊤
  Val Γ boolᵗ    = Bool
  Val Γ natᵗ     = ℕ
  Val Γ uniqᵗ    = ℕ
  Val Γ (s ×ᵗ t) = Val Γ s × Val Γ t
  Val Γ (s +ᵗ t) = Val Γ s ⊎ Val Γ t
  Val Γ (listᵗ t) = List (Val Γ t)
  Val Γ (obs t)  = Σ (List Ty) (λ Θ → Exp Γ [] [] Θ t × Env Γ Θ)

  data Env {n} (Γ : Ctx n) : List Ty → Set where
    []ᵉ  : Env Γ []
    _∷ᵉ_ : ∀ {s Θ} → Val Γ s → Env Γ Θ → Env Γ (s ∷ Θ)

infixr 5 _∷ᵉ_

-- decidable type equality (the evaluator admits a chain only past a Ty
-- match, so no payload is ever read at the wrong type)
_≟ᵗ_ : (s t : Ty) → Dec (s ≡ t)
unitᵗ ≟ᵗ unitᵗ = yes refl
boolᵗ ≟ᵗ boolᵗ = yes refl
natᵗ  ≟ᵗ natᵗ  = yes refl
uniqᵗ ≟ᵗ uniqᵗ = yes refl
(a ×ᵗ b) ≟ᵗ (c ×ᵗ d) with a ≟ᵗ c | b ≟ᵗ d
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬p    = no λ { refl → ¬p refl }
(a +ᵗ b) ≟ᵗ (c +ᵗ d) with a ≟ᵗ c | b ≟ᵗ d
... | yes refl | yes refl = yes refl
... | no ¬p    | _        = no λ { refl → ¬p refl }
... | _        | no ¬p    = no λ { refl → ¬p refl }
listᵗ a ≟ᵗ listᵗ c with a ≟ᵗ c
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
obs a ≟ᵗ obs c with a ≟ᵗ c
... | yes refl = yes refl
... | no ¬p    = no λ { refl → ¬p refl }
unitᵗ    ≟ᵗ boolᵗ    = no λ ()
unitᵗ    ≟ᵗ natᵗ     = no λ ()
unitᵗ    ≟ᵗ (_ ×ᵗ _) = no λ ()
unitᵗ    ≟ᵗ (_ +ᵗ _) = no λ ()
unitᵗ    ≟ᵗ obs _    = no λ ()
boolᵗ    ≟ᵗ unitᵗ    = no λ ()
boolᵗ    ≟ᵗ natᵗ     = no λ ()
boolᵗ    ≟ᵗ (_ ×ᵗ _) = no λ ()
boolᵗ    ≟ᵗ (_ +ᵗ _) = no λ ()
boolᵗ    ≟ᵗ obs _    = no λ ()
natᵗ     ≟ᵗ unitᵗ    = no λ ()
natᵗ     ≟ᵗ boolᵗ    = no λ ()
natᵗ     ≟ᵗ (_ ×ᵗ _) = no λ ()
natᵗ     ≟ᵗ (_ +ᵗ _) = no λ ()
natᵗ     ≟ᵗ obs _    = no λ ()
(_ ×ᵗ _) ≟ᵗ unitᵗ    = no λ ()
(_ ×ᵗ _) ≟ᵗ boolᵗ    = no λ ()
(_ ×ᵗ _) ≟ᵗ natᵗ     = no λ ()
(_ ×ᵗ _) ≟ᵗ (_ +ᵗ _) = no λ ()
(_ ×ᵗ _) ≟ᵗ obs _    = no λ ()
(_ +ᵗ _) ≟ᵗ unitᵗ    = no λ ()
(_ +ᵗ _) ≟ᵗ boolᵗ    = no λ ()
(_ +ᵗ _) ≟ᵗ natᵗ     = no λ ()
(_ +ᵗ _) ≟ᵗ (_ ×ᵗ _) = no λ ()
(_ +ᵗ _) ≟ᵗ obs _    = no λ ()
obs _    ≟ᵗ unitᵗ    = no λ ()
obs _    ≟ᵗ boolᵗ    = no λ ()
obs _    ≟ᵗ natᵗ     = no λ ()
obs _    ≟ᵗ (_ ×ᵗ _) = no λ ()
obs _    ≟ᵗ (_ +ᵗ _) = no λ ()
unitᵗ    ≟ᵗ listᵗ _  = no λ ()
boolᵗ    ≟ᵗ listᵗ _  = no λ ()
natᵗ     ≟ᵗ listᵗ _  = no λ ()
(_ ×ᵗ _) ≟ᵗ listᵗ _  = no λ ()
(_ +ᵗ _) ≟ᵗ listᵗ _  = no λ ()
obs _    ≟ᵗ listᵗ _  = no λ ()
listᵗ _  ≟ᵗ unitᵗ    = no λ ()
listᵗ _  ≟ᵗ boolᵗ    = no λ ()
listᵗ _  ≟ᵗ natᵗ     = no λ ()
listᵗ _  ≟ᵗ (_ ×ᵗ _) = no λ ()
listᵗ _  ≟ᵗ (_ +ᵗ _) = no λ ()
listᵗ _  ≟ᵗ obs _    = no λ ()
uniqᵗ    ≟ᵗ unitᵗ    = no λ ()
uniqᵗ    ≟ᵗ boolᵗ    = no λ ()
uniqᵗ    ≟ᵗ natᵗ     = no λ ()
uniqᵗ    ≟ᵗ (_ ×ᵗ _) = no λ ()
uniqᵗ    ≟ᵗ (_ +ᵗ _) = no λ ()
uniqᵗ    ≟ᵗ listᵗ _  = no λ ()
uniqᵗ    ≟ᵗ obs _    = no λ ()
unitᵗ    ≟ᵗ uniqᵗ    = no λ ()
boolᵗ    ≟ᵗ uniqᵗ    = no λ ()
natᵗ     ≟ᵗ uniqᵗ    = no λ ()
(_ ×ᵗ _) ≟ᵗ uniqᵗ    = no λ ()
(_ +ᵗ _) ≟ᵗ uniqᵗ    = no λ ()
listᵗ _  ≟ᵗ uniqᵗ    = no λ ()
obs _    ≟ᵗ uniqᵗ    = no λ ()

-- one Θ value-environment lookup, indexed by the de Bruijn membership proof
lookupEnv : ∀ {n} {Γ : Ctx n} {Θ t} → Env Γ Θ → t ∈ Θ → Val Γ t
lookupEnv (v ∷ᵉ _)  (here refl) = v
lookupEnv (_ ∷ᵉ vs) (there p)   = lookupEnv vs p

------------------------------------------------------------------
-- Renaming: re-index a term into wider μ-var (Δᵍ, Δ) and value-var (Θ)
-- contexts. A membership map per context; extended under binders; the
-- deferᵉ clause moves Δᵍ into Δ, so its Δ-renaming is the ++-congruence.
------------------------------------------------------------------

Ren∈ : List Ty → List Ty → Set
Ren∈ xs ys = ∀ {u} → u ∈ xs → u ∈ ys

ext∈ : ∀ {xs ys s} → Ren∈ xs ys → Ren∈ (s ∷ xs) (s ∷ ys)
ext∈ ρ (here refl) = here refl
ext∈ ρ (there x)   = there (ρ x)

++Ren : ∀ {A A′ B B′} → Ren∈ A A′ → Ren∈ B B′ → Ren∈ (A ++ B) (A′ ++ B′)
++Ren {A} {A′} ρa ρb x with ∈-++⁻ A x
... | inj₁ y = ∈-++⁺ˡ (ρa y)
... | inj₂ z = ∈-++⁺ʳ A′ (ρb z)

mutual
  renExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
         → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
         → Exp Γ Δᵍ Δ Θ t → Exp Γ Δᵍ′ Δ′ Θ′ t
  renExp ρg ρd ρt (input i)      = input i
  renExp ρg ρd ρt (ofᵉ ts)       = ofᵉ (renTms ρg ρd ρt ts)
  renExp ρg ρd ρt emptyᵉ         = emptyᵉ
  renExp ρg ρd ρt (takeᵉ n e)    = takeᵉ (renTm ρg ρd ρt n) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (batchSyncᵉ e) = batchSyncᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (mapᵉ f e)     = mapᵉ (renTm ρg ρd (ext∈ ρt) f) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (scanᵉ f i e)  = scanᵉ (renTm ρg ρd (ext∈ ρt) f) (renTm ρg ρd ρt i) (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (mergeAllᵉ lim e) = mergeAllᵉ lim (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (switchAllᵉ e) = switchAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (exhaustAllᵉ e) = exhaustAllᵉ (renExp ρg ρd ρt e)
  renExp ρg ρd ρt (μᵉ e)         = μᵉ (renExp (ext∈ ρg) ρd ρt e)
  renExp ρg ρd ρt (varᵉ x)       = varᵉ (ρd x)
  renExp ρg ρd ρt (deferᵉ e)     = deferᵉ (renExp (λ ()) (++Ren ρg ρd) ρt e)
  renExp ρg ρd ρt (mintᵉ e)      = mintᵉ (renExp ρg ρd (ext∈ ρt) e)

  renTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
        → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
        → Tm Γ Δᵍ Δ Θ t → Tm Γ Δᵍ′ Δ′ Θ′ t
  renTm ρg ρd ρt (varᵗ x)     = varᵗ (ρt x)
  renTm ρg ρd ρt unit̂         = unit̂
  renTm ρg ρd ρt (bool̂ b)     = bool̂ b
  renTm ρg ρd ρt (nat̂ n)      = nat̂ n
  renTm ρg ρd ρt (foldᵗ l z f) =
    foldᵗ (renTm ρg ρd ρt l) (renTm ρg ρd ρt z)
          (renTm ρg ρd (ext∈ (ext∈ ρt)) f)
  renTm ρg ρd ρt nilᵗ         = nilᵗ
  renTm ρg ρd ρt (consᵗ a as) = consᵗ (renTm ρg ρd ρt a) (renTm ρg ρd ρt as)
  renTm ρg ρd ρt (pairᵗ a b)  = pairᵗ (renTm ρg ρd ρt a) (renTm ρg ρd ρt b)
  renTm ρg ρd ρt (fstᵗ p)     = fstᵗ (renTm ρg ρd ρt p)
  renTm ρg ρd ρt (sndᵗ p)     = sndᵗ (renTm ρg ρd ρt p)
  renTm ρg ρd ρt (inlᵗ a)     = inlᵗ (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (inrᵗ a)     = inrᵗ (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (caseᵗ s l r) = caseᵗ (renTm ρg ρd ρt s) (renTm ρg ρd (ext∈ ρt) l) (renTm ρg ρd (ext∈ ρt) r)
  renTm ρg ρd ρt (ifᵗ c a b)  = ifᵗ (renTm ρg ρd ρt c) (renTm ρg ρd ρt a) (renTm ρg ρd ρt b)
  renTm ρg ρd ρt (primᵗ op a) = primᵗ op (renTm ρg ρd ρt a)
  renTm ρg ρd ρt (strmᵗ e)    = strmᵗ (renExp ρg ρd ρt e)

  renTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δᵍ′ Δ Δ′ Θ Θ′ t}
         → Ren∈ Δᵍ Δᵍ′ → Ren∈ Δ Δ′ → Ren∈ Θ Θ′
         → List (Tm Γ Δᵍ Δ Θ t) → List (Tm Γ Δᵍ′ Δ′ Θ′ t)
  renTms ρg ρd ρt []       = []
  renTms ρg ρd ρt (x ∷ xs) = renTm ρg ρd ρt x ∷ renTms ρg ρd ρt xs

-- weaken a closed term into any context (source contexts empty)
wkTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → Tm Γ [] [] [] t → Tm Γ Δᵍ Δ Θ t
wkTm = renTm (λ ()) (λ ()) (λ ())

------------------------------------------------------------------
-- `letᵗ` and the list helpers the encodings above are written with.
------------------------------------------------------------------

-- THE TERM LANGUAGE HAS NO APPLICATION, AND THAT IS WHAT SHAPES EVERY
-- ENCODING HERE.  A `Fn` is a `Tm` under one extra binder, and the only
-- substitution here carries VALUES, so a step cannot simply be applied
-- to a term: the argument has to be handed over by a former that BINDS.
-- `foldᵗ` over a ONE-ELEMENT list is that former, which is why `letᵗ`
-- below is a definition and not a new constructor — a constructor would
-- have cost a clause in every walk, which is exactly the price this
-- whole leg is collecting back.  The seed is explicit because `Tm` has
-- no generic inhabitant to default it to, and every caller here has a
-- real one in hand.
letᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ s u}
     → Tm Γ Δᵍ Δ Θ s → Tm Γ Δᵍ Δ Θ u → Tm Γ Δᵍ Δ (s ∷ Θ) u → Tm Γ Δᵍ Δ Θ u
letᵗ m d b = foldᵗ (consᵗ m nilᵗ) d (renTm (λ x → x) (λ x → x) (ext∈ there) b)

-- `foldᵗ` is a LEFT fold, so a list built by consing comes out reversed
-- and every encoding below pays one reversing pass.
revᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
     → Tm Γ Δᵍ Δ Θ (listᵗ t) → Tm Γ Δᵍ Δ Θ (listᵗ t)
revᵗ l = foldᵗ l nilᵗ (consᵗ (varᵗ (here refl)) (varᵗ (there (here refl))))

-- append, which is `revᵗ` seeded with the second list rather than with
-- nothing: consing the reverse of the first onto it puts it back in
-- order.  So the two are one encoding and the reversing pass `foldᵗ`
-- costs is paid once either way.
appendᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t}
        → Tm Γ Δᵍ Δ Θ (listᵗ t) → Tm Γ Δᵍ Δ Θ (listᵗ t) → Tm Γ Δᵍ Δ Θ (listᵗ t)
appendᵗ xs ys = foldᵗ (revᵗ xs) ys (consᵗ (varᵗ (here refl))
                                          (varᵗ (there (here refl))))


------------------------------------------------------------------
-- unfoldμ: substitute the (closed) `μᵉ body` for the μ-var this μ binds.
-- The var starts alone in Δᵍ and is READ only as a varᵉ (in Δ), reachable
-- only past a deferᵉ that moved Δᵍ into Δ. So we eliminate it, tracking
-- whether it currently sits in Δᵍ (elimG) or has migrated into Δ (elimD),
-- and drop it from that context. The deferᵉ shuffle needs two context
-- identities — proofs, left as postulates per the behavior/proof split.
------------------------------------------------------------------

-- remove the pointed element from a context
_⊟_ : ∀ {A : Set} (xs : List A) {x : A} → x ∈ xs → List A
(_ ∷ xs) ⊟ here _  = xs
(y ∷ xs) ⊟ there p = y ∷ (xs ⊟ p)

-- proven (not postulated): a postulate here would be an abstract proof,
-- and subst on it would BLOCK evaluation — these must reduce to refl on
-- concrete indices for a μ-program to compute
⊟-++ˡ : ∀ {Δᵍ Δ : List Ty} {t} (x : t ∈ Δᵍ)
      → (Δᵍ ++ Δ) ⊟ (∈-++⁺ˡ {ys = Δ} x) ≡ (Δᵍ ⊟ x) ++ Δ
⊟-++ˡ (here refl) = refl
⊟-++ˡ (there {x = g} x) = cong (g ∷_) (⊟-++ˡ x)

⊟-++ʳ : ∀ {Δᵍ Δ : List Ty} {t} (x : t ∈ Δ)
      → (Δᵍ ++ Δ) ⊟ (∈-++⁺ʳ Δᵍ x) ≡ Δᵍ ++ (Δ ⊟ x)
⊟-++ʳ {Δᵍ = []}     x = refl
⊟-++ʳ {Δᵍ = g ∷ _}  x = cong (g ∷_) (⊟-++ʳ x)

-- compare two positions: inj₁ ⟺ the same position (types coincide);
-- inj₂ ⟺ y sits at this position once x is removed
compare∈ : ∀ {A : Set} {t u : A} {xs} (x : t ∈ xs) (y : u ∈ xs)
         → (t ≡ u) ⊎ (u ∈ (xs ⊟ x))
compare∈ (here refl) (here refl) = inj₁ refl
compare∈ (here refl) (there y)   = inj₂ y
compare∈ (there x)   (here refl) = inj₂ (here refl)
compare∈ (there x)   (there y)   with compare∈ x y
... | inj₁ eq = inj₁ eq
... | inj₂ y′ = inj₂ (there y′)

mutual
  elimGExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
           → Exp Γ [] [] Θsub t → Exp Γ Δᵍ Δ (Θloc ++ Θsub) u
           → Exp Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u
  elimGExp Θl x cl (input i)      = input i
  elimGExp Θl x cl (ofᵉ ts)       = ofᵉ (elimGTms Θl x cl ts)
  elimGExp Θl x cl emptyᵉ         = emptyᵉ
  elimGExp Θl x cl (takeᵉ n e)    = takeᵉ (elimGTm Θl x cl n) (elimGExp Θl x cl e)
  elimGExp Θl x cl (batchSyncᵉ e) = batchSyncᵉ (elimGExp Θl x cl e)
  elimGExp Θl x cl (mapᵉ f e)     =
    mapᵉ (elimGTm (_ ∷ Θl) x cl f) (elimGExp Θl x cl e)
  elimGExp Θl x cl (scanᵉ f i e)  =
    scanᵉ (elimGTm (_ ∷ Θl) x cl f) (elimGTm Θl x cl i) (elimGExp Θl x cl e)
  elimGExp Θl x cl (mergeAllᵉ lim e) = mergeAllᵉ lim (elimGExp Θl x cl e)
  elimGExp Θl x cl (switchAllᵉ e) = switchAllᵉ (elimGExp Θl x cl e)
  elimGExp Θl x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimGExp Θl x cl e)
  elimGExp Θl x cl (μᵉ e)         = μᵉ (elimGExp Θl (there x) cl e)
  elimGExp Θl x cl (varᵉ y)       = varᵉ y
  elimGExp Θl x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ˡ x) (elimDExp Θl (∈-++⁺ˡ x) cl e))
  elimGExp Θl x cl (mintᵉ e)      = mintᵉ (elimGExp (uniqᵗ ∷ Θl) x cl e)

  elimGTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
          → Exp Γ [] [] Θsub t → Tm Γ Δᵍ Δ (Θloc ++ Θsub) u
          → Tm Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u
  elimGTm Θl x cl (varᵗ y)     = varᵗ y
  elimGTm Θl x cl unit̂         = unit̂
  elimGTm Θl x cl (bool̂ b)     = bool̂ b
  elimGTm Θl x cl (nat̂ n)      = nat̂ n
  elimGTm Θl x cl nilᵗ         = nilᵗ
  elimGTm Θl x cl (consᵗ a as) = consᵗ (elimGTm Θl x cl a) (elimGTm Θl x cl as)
  elimGTm Θl x cl (pairᵗ a b)  = pairᵗ (elimGTm Θl x cl a) (elimGTm Θl x cl b)
  elimGTm Θl x cl (fstᵗ p)     = fstᵗ (elimGTm Θl x cl p)
  elimGTm Θl x cl (sndᵗ p)     = sndᵗ (elimGTm Θl x cl p)
  elimGTm Θl x cl (inlᵗ a)     = inlᵗ (elimGTm Θl x cl a)
  elimGTm Θl x cl (inrᵗ a)     = inrᵗ (elimGTm Θl x cl a)
  elimGTm Θl x cl (foldᵗ l z f) =
    foldᵗ (elimGTm Θl x cl l) (elimGTm Θl x cl z)
          (elimGTm (_ ∷ _ ∷ Θl) x cl f)
  elimGTm Θl x cl (caseᵗ s l r) =
    caseᵗ (elimGTm Θl x cl s) (elimGTm (_ ∷ Θl) x cl l) (elimGTm (_ ∷ Θl) x cl r)
  elimGTm Θl x cl (ifᵗ c a b)  =
    ifᵗ (elimGTm Θl x cl c) (elimGTm Θl x cl a) (elimGTm Θl x cl b)
  elimGTm Θl x cl (primᵗ op a) = primᵗ op (elimGTm Θl x cl a)
  elimGTm Θl x cl (strmᵗ e)    = strmᵗ (elimGExp Θl x cl e)

  elimGTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δᵍ)
           → Exp Γ [] [] Θsub t → List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
           → List (Tm Γ (Δᵍ ⊟ x) Δ (Θloc ++ Θsub) u)
  elimGTms Θl x cl []       = []
  elimGTms Θl x cl (y ∷ ys) = elimGTm Θl x cl y ∷ elimGTms Θl x cl ys

  elimDExp : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
           → Exp Γ [] [] Θsub t → Exp Γ Δᵍ Δ (Θloc ++ Θsub) u
           → Exp Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u
  elimDExp Θl x cl (input i)      = input i
  elimDExp Θl x cl (ofᵉ ts)       = ofᵉ (elimDTms Θl x cl ts)
  elimDExp Θl x cl emptyᵉ         = emptyᵉ
  elimDExp Θl x cl (takeᵉ n e)    = takeᵉ (elimDTm Θl x cl n) (elimDExp Θl x cl e)
  elimDExp Θl x cl (batchSyncᵉ e) = batchSyncᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (mapᵉ f e)     =
    mapᵉ (elimDTm (_ ∷ Θl) x cl f) (elimDExp Θl x cl e)
  elimDExp Θl x cl (scanᵉ f i e)  =
    scanᵉ (elimDTm (_ ∷ Θl) x cl f) (elimDTm Θl x cl i) (elimDExp Θl x cl e)
  elimDExp Θl x cl (mergeAllᵉ lim e) = mergeAllᵉ lim (elimDExp Θl x cl e)
  elimDExp Θl x cl (switchAllᵉ e) = switchAllᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (exhaustAllᵉ e) = exhaustAllᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (μᵉ e)         = μᵉ (elimDExp Θl x cl e)
  elimDExp Θl x cl (varᵉ y)       with compare∈ x y
  ... | inj₁ refl = renExp (λ ()) (λ ()) (∈-++⁺ʳ Θl) cl
  ... | inj₂ y′   = varᵉ y′
  elimDExp Θl x cl (deferᵉ e)     =
    deferᵉ (subst (λ ζ → Exp _ [] ζ _ _) (⊟-++ʳ x) (elimDExp Θl (∈-++⁺ʳ _ x) cl e))
  elimDExp Θl x cl (mintᵉ e)      = mintᵉ (elimDExp (uniqᵗ ∷ Θl) x cl e)

  elimDTm : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
          → Exp Γ [] [] Θsub t → Tm Γ Δᵍ Δ (Θloc ++ Θsub) u
          → Tm Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u
  elimDTm Θl x cl (varᵗ y)     = varᵗ y
  elimDTm Θl x cl unit̂         = unit̂
  elimDTm Θl x cl (bool̂ b)     = bool̂ b
  elimDTm Θl x cl (nat̂ n)      = nat̂ n
  elimDTm Θl x cl nilᵗ         = nilᵗ
  elimDTm Θl x cl (consᵗ a as) = consᵗ (elimDTm Θl x cl a) (elimDTm Θl x cl as)
  elimDTm Θl x cl (pairᵗ a b)  = pairᵗ (elimDTm Θl x cl a) (elimDTm Θl x cl b)
  elimDTm Θl x cl (fstᵗ p)     = fstᵗ (elimDTm Θl x cl p)
  elimDTm Θl x cl (sndᵗ p)     = sndᵗ (elimDTm Θl x cl p)
  elimDTm Θl x cl (inlᵗ a)     = inlᵗ (elimDTm Θl x cl a)
  elimDTm Θl x cl (inrᵗ a)     = inrᵗ (elimDTm Θl x cl a)
  elimDTm Θl x cl (foldᵗ l z f) =
    foldᵗ (elimDTm Θl x cl l) (elimDTm Θl x cl z)
          (elimDTm (_ ∷ _ ∷ Θl) x cl f)
  elimDTm Θl x cl (caseᵗ s l r) =
    caseᵗ (elimDTm Θl x cl s) (elimDTm (_ ∷ Θl) x cl l) (elimDTm (_ ∷ Θl) x cl r)
  elimDTm Θl x cl (ifᵗ c a b)  =
    ifᵗ (elimDTm Θl x cl c) (elimDTm Θl x cl a) (elimDTm Θl x cl b)
  elimDTm Θl x cl (primᵗ op a) = primᵗ op (elimDTm Θl x cl a)
  elimDTm Θl x cl (strmᵗ e)    = strmᵗ (elimDExp Θl x cl e)

  elimDTms : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θsub u t} (Θloc : List Ty) (x : t ∈ Δ)
           → Exp Γ [] [] Θsub t → List (Tm Γ Δᵍ Δ (Θloc ++ Θsub) u)
           → List (Tm Γ Δᵍ (Δ ⊟ x) (Θloc ++ Θsub) u)
  elimDTms Θl x cl []       = []
  elimDTms Θl x cl (y ∷ ys) = elimDTm Θl x cl y ∷ elimDTms Θl x cl ys

unfoldμ : ∀ {n} {Γ : Ctx n} {Θ t} → Exp Γ (t ∷ []) [] Θ t → Exp Γ [] [] Θ t
unfoldμ body = elimGExp [] (here refl) (μᵉ body) body


-- the first-order evaluator, in a Θ value-environment.  A `strmᵗ` is
-- evaluated by PAIRING its body with the environment in hand rather
-- than by substituting that environment into it — which is the whole
-- point of the family: nothing is ever reified, so no value needs a
-- term denoting it, so a token needs no intro form.
evalWith : ∀ {n} {Γ : Ctx n} {Θ t} → Tm Γ [] [] Θ t → Env Γ Θ → Val Γ t

-- THE FOLD'S ACCUMULATOR LOOP, HOISTED OUT OF THE ARM THAT USES IT.  A
-- `where` helper is invisible outside its clause, so no lemma could be
-- STATED about it — and the substitution face needs exactly one: that
-- folding under a substituted step agrees with folding under the
-- composed environment.  Naming it costs a forward declaration and buys
-- the statement.
foldVals : ∀ {n} {Γ : Ctx n} {Θ s u}
         → Tm Γ [] [] (s ∷ u ∷ Θ) u → Env Γ Θ
         → List (Val Γ s) → Val Γ u → Val Γ u

evalWith (varᵗ x)      env = lookupEnv env x
evalWith unit̂          env = tt
evalWith (bool̂ b)      env = b
evalWith (nat̂ n)       env = n
evalWith nilᵗ          env = []
evalWith (consᵗ a as)  env = evalWith a env ∷ evalWith as env
evalWith (pairᵗ a b)   env = evalWith a env , evalWith b env
evalWith (fstᵗ p)      env = proj₁ (evalWith p env)
evalWith (sndᵗ p)      env = proj₂ (evalWith p env)
evalWith (inlᵗ a)      env = inj₁ (evalWith a env)
evalWith (inrᵗ a)      env = inj₂ (evalWith a env)
evalWith (foldᵗ l z f) env = foldVals f env (evalWith l env) (evalWith z env)
evalWith (caseᵗ sc l r) env with evalWith sc env
... | inj₁ x = evalWith l (x ∷ᵉ env)
... | inj₂ y = evalWith r (y ∷ᵉ env)
evalWith (ifᵗ c t e)   env = if evalWith c env then evalWith t env else evalWith e env
evalWith (primᵗ add arg)  env = let (a , b) = evalWith arg env in a + b
evalWith (primᵗ sub arg)  env = let (a , b) = evalWith arg env in a ∸ b
evalWith (primᵗ mul arg)  env = let (a , b) = evalWith arg env in a * b
evalWith (primᵗ eqᵖ arg)  env = let (a , b) = evalWith arg env in a ≡ᵇ b
evalWith (primᵗ eqᵘ arg)  env = let (a , b) = evalWith arg env in a ≡ᵇ b
evalWith (primᵗ ltᵖ arg)  env = let (a , b) = evalWith arg env in a <ᵇ b
evalWith (primᵗ notᵖ arg) env = not (evalWith arg env)
-- THE CLAUSE THE WHOLE FAMILY EXISTS FOR: the body is PAIRED with the
-- environment rather than substituted into, so nothing is reified and
-- no value is ever denoted by a term.
evalWith (strmᵗ e)     env = _ , e , env

foldVals f env []       acc = acc
foldVals f env (x ∷ xs) acc = foldVals f env xs (evalWith f (x ∷ᵉ acc ∷ᵉ env))

evalTm  : ∀ {n} {Γ : Ctx n} {t} → Tm Γ [] [] [] t → Val Γ t
evalTm t = evalWith t []ᵉ

applyFn : ∀ {n} {Γ : Ctx n} {s t} → Fn Γ [] [] [] s t → Val Γ s → Val Γ t
applyFn fn v = evalWith fn (v ∷ᵉ []ᵉ)

-- A STEP FUNCTION AS A VALUE, WHICH IN A LANGUAGE WHOSE `Ty` HAS NO
-- ARROW IS THE ONLY THING ONE CAN BE.  `Val Γ (obs u)` pairs a body
-- with an environment because an observable is carried as data; a
-- frame's step is carried the same way for the same reason, since the
-- operator that installed it was itself reached under a token
-- telescope and its body is not closed.  There is no `Ty` for this and
-- there is not meant to be: nothing in the term language holds a step,
-- only the machine does.
FnClo : ∀ {n} → Ctx n → Ty → Ty → Set
FnClo Γ s t = Σ (List Ty) (λ Θ → Fn Γ [] [] Θ s t × Env Γ Θ)

applyClo : ∀ {n} {Γ : Ctx n} {s t} → FnClo Γ s t → Val Γ s → Val Γ t
applyClo (_ , fn , ρ) v = evalWith fn (v ∷ᵉ ρ)

------------------------------------------------------------------
-- STRATIFICATION of the slot telescope: every `input j` an
-- expression mentions has j < k.  A shared slot's def carries this
-- as a side condition (Rx.Slots.shared), so the telescope is a real
-- JS `const` telescope — a def can read only strictly-earlier
-- bindings, exactly what the TS generator already builds and what a
-- JS const can reference without a TDZ error.  It exists so that a
-- per-slot measure is computable by recursion on the slot index:
-- slot k reads only slots j < k.
--
-- deferᵉ is NOT cut: a deferred subtree
-- subscribes later, but its `input` references are just as real
-- when it does.  The check is about which slots a def can EVER
-- reach, not about when.
------------------------------------------------------------------
mutual
  inputsBelowᵉ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → Exp Γ Δᵍ Δ Θ t → Bool
  inputsBelowᵉ k (input i)       = toℕ i <ᵇ k
  inputsBelowᵉ k (ofᵉ ts)        = inputsBelowᵗˢ k ts
  inputsBelowᵉ k emptyᵉ          = true
  inputsBelowᵉ k (takeᵉ c e)     = inputsBelowᵗ k c ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (batchSyncᵉ e)  = inputsBelowᵉ k e
  inputsBelowᵉ k (mapᵉ f e)      = inputsBelowᵗ k f ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (scanᵉ f z e)   =
    inputsBelowᵗ k f ∧ inputsBelowᵗ k z ∧ inputsBelowᵉ k e
  inputsBelowᵉ k (mergeAllᵉ lim e) = inputsBelowᵉ k e
  inputsBelowᵉ k (switchAllᵉ e)  = inputsBelowᵉ k e
  inputsBelowᵉ k (exhaustAllᵉ e) = inputsBelowᵉ k e
  inputsBelowᵉ k (μᵉ e)          = inputsBelowᵉ k e
  inputsBelowᵉ k (varᵉ x)        = true
  inputsBelowᵉ k (deferᵉ e)      = inputsBelowᵉ k e
  inputsBelowᵉ k (mintᵉ e)       = inputsBelowᵉ k e

  inputsBelowᵗ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → Tm Γ Δᵍ Δ Θ t → Bool
  inputsBelowᵗ k (varᵗ x)      = true
  inputsBelowᵗ k unit̂          = true
  inputsBelowᵗ k (bool̂ _)      = true
  inputsBelowᵗ k (nat̂ _)       = true
  inputsBelowᵗ k (foldᵗ l z f) =
    inputsBelowᵗ k l ∧ inputsBelowᵗ k z ∧ inputsBelowᵗ k f
  inputsBelowᵗ k nilᵗ          = true
  inputsBelowᵗ k (consᵗ a as)  = inputsBelowᵗ k a ∧ inputsBelowᵗ k as
  inputsBelowᵗ k (pairᵗ a b)   = inputsBelowᵗ k a ∧ inputsBelowᵗ k b
  inputsBelowᵗ k (fstᵗ p)      = inputsBelowᵗ k p
  inputsBelowᵗ k (sndᵗ p)      = inputsBelowᵗ k p
  inputsBelowᵗ k (inlᵗ a)      = inputsBelowᵗ k a
  inputsBelowᵗ k (inrᵗ a)      = inputsBelowᵗ k a
  inputsBelowᵗ k (caseᵗ s l r) =
    inputsBelowᵗ k s ∧ inputsBelowᵗ k l ∧ inputsBelowᵗ k r
  inputsBelowᵗ k (ifᵗ c a b)   =
    inputsBelowᵗ k c ∧ inputsBelowᵗ k a ∧ inputsBelowᵗ k b
  inputsBelowᵗ k (primᵗ _ a)   = inputsBelowᵗ k a
  inputsBelowᵗ k (strmᵗ e)     = inputsBelowᵉ k e

  inputsBelowᵗˢ : ∀ {n} {Γ : Ctx n} {Δᵍ Δ Θ t} → ℕ → List (Tm Γ Δᵍ Δ Θ t) → Bool
  inputsBelowᵗˢ k []       = true
  inputsBelowᵗˢ k (y ∷ ys) = inputsBelowᵗ k y ∧ inputsBelowᵗˢ k ys
