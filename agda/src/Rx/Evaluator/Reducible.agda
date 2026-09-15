------------------------------------------------------------------
-- REDUCIBILITY: THE DESCENT THE TYPE FUNDS, WHERE THE RANK STOOD.
------------------------------------------------------------------

-- WHAT THIS REPLACES AND WHY THE REPLACEMENT IS FREE.  The builder
-- justifies its recursion with a RANK — a lexicographic triple carried
-- into every call, decreasing at three edges and inert at the rest.
-- Every open obligation on that face is one of the rank's own decrease
-- steps, which is why they are refuted rather than merely hard: the
-- quantity is being asked to fall across an unfolding that does not
-- move it.  A Girard-Tait candidate spends no such quantity.  It
-- recurses on the TYPE, which the flatteners move strictly downward
-- (`obs (obs u)` to `obs u`) and the term-structural formers do not
-- move at all — so the cases that cost the rank a decrease proof cost
-- this nothing, and the cases the rank passed through untouched are
-- exactly the ones the type leaves alone.
--
-- WHY IT IS A FUNCTION AND NOT A FAMILY.  A relation relating an
-- expression to its subscription derivation may not mention that
-- derivation's own type in a negative position, so the candidate
-- cannot be an inductive family over the domain relation.  Defined by
-- recursion on `Ty` it never needs to be: `Red (obs u)` mentions
-- `Red u` at a strictly smaller type and `subscribeE⇓` only positively.
--
-- WHY THE STATE IS QUANTIFIED RATHER THAN CONSTRAINED.  `subscribeE⇓`
-- takes the scheduler and the evaluator state as plain indices with no
-- precondition, and the entry invariants the builder carries appear
-- nowhere in its conclusion — they are the rank's bookkeeping and are
-- discarded from the result.  So the candidate can demand
-- subscribability in EVERY state, which is what lets a flattener's hop
-- subscribe its inner in whatever state the outer delivery reached.
module Rx.Evaluator.Reducible where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)

open import Rx.Prim using (Id; Source; Tick; InstEmit; InstEvent; init; value; close;
  handoff; complete)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Ctx; Closed; Val)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; sharedPlumb; spentBurst)
open import Rx.Evaluator.Domain using (subscribeE⇓)

-- An emitted EVENT carries a payload only in the `value` arm; every
-- other arm is protocol traffic and constrains nothing.
EvSat : ∀ {A : Set} → (A → Set) → InstEvent A → Set
EvSat P (init _)    = ⊤
EvSat P (value v)   = P v
EvSat P (close _ _) = ⊤
EvSat P (handoff _) = ⊤
EvSat P complete    = ⊤

-- …and a STREAM satisfies a predicate when every value it ever carries
-- does.  Taking the predicate as a parameter is what keeps `Red`'s
-- recursion structural: the recursive occurrence is `Red u` applied at
-- a strictly smaller type, not a call at the type being defined.
StreamSat : ∀ {A : Set} → (A → Set) → List (InstEmit A) → Set
StreamSat P = All (λ em → All (EvSat P) (InstEmit.events em))

-- THE CANDIDATE.  At a data type it is trivial, because nothing about
-- a number can fail to be reducible; at an observable it is the pair
-- the whole argument turns on — a subscription derivation in every
-- state, and the guarantee that everything that derivation emits is
-- itself reducible at the element type.
Red : ∀ {n} {Γ : Ctx n} (t : Ty) → Val Γ t → Set
Red unitᵗ    _        = ⊤
Red boolᵗ    _        = ⊤
Red natᵗ     _        = ⊤
Red (s ×ᵗ t) (a , b)  = Red s a × Red t b
Red (s +ᵗ t) (inj₁ a) = Red s a
Red (s +ᵗ t) (inj₂ b) = Red t b
Red {Γ = Γ} (obs u) b =
  ∀ {t} {e : Closed Γ t} {lo} (κ : Path Γ lo u t) (id : Id) (now : Tick)
    (sched : Sched Γ) (st : EvalSt e) →
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    subscribeE⇓ {e = e} b κ id now sched st r × StreamSat (Red u) (proj₁ r)

-- WHY A SHARE'S FAN-OUT COSTS THE CANDIDATE NOTHING, WHICH IS THE ONE
-- THING ABOUT `connect` THAT WAS NOT OBVIOUS.  A shared slot subscribes
-- its def ONCE and attaches every later reader to that one connection,
-- so the natural fear is that reducibility must be maintained as an
-- INVARIANT ON STORED STATE — everything a share is holding for its
-- next attacher would have to be reducible, and every step would owe
-- that invariant's preservation.  Nothing of the kind is owed, because
-- the fan-out carries NO PAYLOAD: a late reader's arm emits a bare
-- registration, a spent slot's arm emits a registration and its close,
-- and the only arm carrying values is the one that subscribes the def —
-- whose values are the def's, which is the induction hypothesis.  The
-- semantic fact underneath is that this share does not replay, so there
-- is nothing stored for the invariant to be about.

-- A SPENT SLOT'S BURST is registration traffic and a completion, so
-- every predicate holds of it for want of anything to hold of.
StreamSat-spent : ∀ {A : Set} {P : A → Set} (src : Source) (id : Id)
                → StreamSat P (spentBurst {A} src id)
StreamSat-spent src id = (tt ∷ᵃ tt ∷ᵃ tt ∷ᵃ []ᵃ) ∷ᵃ []ᵃ

-- AND THE FAN-OUT RETAGS ITS EMITS WITHOUT TOUCHING THEIR EVENTS, so
-- whatever held of the def's burst still holds of what the readers see.
StreamSat-plumb : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} (str : Stream Γ u)
                → StreamSat P str → StreamSat P (sharedPlumb str)
StreamSat-plumb []       []ᵃ        = []ᵃ
StreamSat-plumb (x ∷ xs) (p ∷ᵃ ps) = p ∷ᵃ StreamSat-plumb xs ps

-- THE FUNDAMENTAL LEMMA, WHICH IS THE WHOLE OF WHAT IS OWED.  Every
-- closed expression is reducible, and the builder's subscribe cluster
-- is its consumer rather than its competitor: the clauses that cluster
-- writes are the cases this induction has to take, and the rank they
-- used to thread is what the type's own descent replaces.  Stated
-- unconditionally because nothing narrows it — a slot telescope
-- carries its stratification in the slot record, so a scheduler that
-- typechecks is already one this can be instantiated at.
postulate
  reducible : ∀ {n} {Γ : Ctx n} {t} (b : Closed Γ t) → Red {Γ = Γ} (obs t) b
