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

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (Maybe)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)

open import Relation.Binary.PropositionalEquality using (refl)

open import Rx.Prim using (Id; Tick; InstEmit; InstEvent; init; value; close; handoff; complete)
open import Rx.Exp using (Ty; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_; obs; Ctx; Closed; Val;
  Exp; Tm; evalTm; input; ofᵉ; emptyᵉ; mapᵉ; takeᵉ; scanᵉ; mergeAllᵉ; switchAllᵉ;
  exhaustAllᵉ; μᵉ; varᵉ; deferᵉ)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; _↠_; map-f;
  take-f; scan-f; take-st; scan-st; installNode; oneShotBurst)
open import Rx.Evaluator.Domain using (subscribeE⇓; pushBurst⇓; subs-of;
  subs-empty; subs-map; subs-take-zero; subs-take-suc; subs-scan; subs-defer)

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
--
-- RECOVERY: git show 64c568e2:agda/src/Rx/Evaluator/Reducible.agda restores
--   `StreamSat-spent` and `StreamSat-plumb`, the two arms of that
--   argument discharged — the first at the spent slot's fixed burst,
--   the second across the plumbing retag.  They are three lines each
--   and belong in the body that replaces the leaf below, which is the
--   consumer they were written ahead of.

-- PUSHING A BURST THROUGH A FRAME, WITH THE CANDIDATE CARRIED ACROSS.
-- The three transformer arms all have the same two-step shape — run the
-- source, then push what it emitted through this frame — so the second
-- step is one obligation stated once rather than three.
RedPush : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
        → Id → Tick → Frame Γ s u → Path Γ lo u t
        → Stream Γ s → Sched Γ → EvalSt e → Set
RedPush {Γ = Γ} {e = e} {u = u} id now f κ burst sched st =
  Σ (Stream Γ u × Sched Γ × EvalSt e) λ r →
    pushBurst⇓ {e = e} id now f κ burst sched st r × StreamSat (Red u) (proj₁ r)

postulate
  -- THE FUNDAMENTAL THEOREM ONE LEVEL DOWN, AT TERMS.  `Tm` and `Exp`
  -- are one mutual datatype and `strmᵗ` embeds an expression into a
  -- term, so this and the body below are mutually structural; it is
  -- stated separately because the arm that spends it is the only one
  -- that needs a value rather than a subscription.
  --
  -- PROBED: `Probed.Reducible-Arms` at an observable-typed term, where
  --   the claim IS an expression's own reducibility and the body
  --   delivers it; and at a numeral, which is DEGENERATE and is there
  --   to say the data half asserts nothing.  No binding term reached.
  red-tm : ∀ {n} {Γ : Ctx n} {u} (tm : Tm Γ [] [] [] u) → Red u (evalTm tm)

  -- THE SLOT ARM.  Five of its six sub-arms emit a fixed protocol
  -- burst and thread the state on untouched; the sixth is a share's
  -- connect, whose def is an arbitrary term and whose candidate is the
  -- one this development quantifies over state to obtain.
  --
  -- PROBED: `Probed.Reducible-Arms` at three of the five scripted
  --   sub-arms -- below the floor, live above it, and a cold script
  --   whose synchronous values ride out.  The satisfaction half is
  --   UNREACHABLE here and that is a property of the statement: a
  --   scripted slot's own side condition makes its element type data,
  --   so the candidate over its values is trivial by construction.
  --   The share's connect is not reached; nor is the spent hot arm,
  --   nor a cold with an asynchronous tail.
  red-input : ∀ {n} {Γ : Ctx n} (i : Fin n)
            → Red {Γ = Γ} (obs (lookup Γ i)) (input i)

  red-push : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo}
             (id : Id) (now : Tick) (f : Frame Γ s u) (κ : Path Γ lo u t)
             {burst : Stream Γ s} → StreamSat (Red s) burst
           → (sched : Sched Γ) (st : EvalSt e)
           → RedPush {e = e} id now f κ burst sched st
  -- PROBED: `Probed.Reducible-Arms` through a mapping frame whose
  --   function returns an OBSERVABLE -- the one row in that file where
  --   the satisfaction half is a real claim, since what the pushed
  --   value must satisfy is another expression's reducibility rather
  --   than a protocol event.  No scan, take or flattening frame
  --   reached, and no burst of more than one emit.

  -- THE FLATTENERS, where the type genuinely descends.  Each takes the
  -- outer's own candidate at `obs (obs u)`, which is where the inners
  -- arrive already reducible at `obs u`.
  --
  -- PROBED: `Probed.Reducible-Arms` reaches all three at an outer that
  --   emits no inner at all, so the node install, the outer's own
  --   subscription and the push back through the frame are shown to
  --   compose.  Nothing downstream of the HOP is reached: the queue
  --   never fills, the switch never kills, the exhaust never refuses,
  --   and the concurrency limit is untouched at every value.
  red-merge-all : ∀ {n} {Γ : Ctx n} {u} (lim : Maybe ℕ) (b : Closed Γ (obs u))
                → Red {Γ = Γ} (obs (obs u)) b → Red {Γ = Γ} (obs u) (mergeAllᵉ lim b)

  red-switch-all : ∀ {n} {Γ : Ctx n} {u} (b : Closed Γ (obs u))
                 → Red {Γ = Γ} (obs (obs u)) b → Red {Γ = Γ} (obs u) (switchAllᵉ b)

  red-exhaust-all : ∀ {n} {Γ : Ctx n} {u} (b : Closed Γ (obs u))
                  → Red {Γ = Γ} (obs (obs u)) b → Red {Γ = Γ} (obs u) (exhaustAllᵉ b)

  -- THE μ PEEL.  The unfolding is no subterm, so the body below cannot
  -- reach it; it sits at the SAME type, so this is a fixpoint at one
  -- type rather than a descent.
  --
  -- PROBED: `Probed.Reducible-Arms` at a body with no self-reference,
  --   which exercises the PEEL -- the unfolding subscribed in the
  --   caller's own state -- and says nothing about the fixpoint.
  red-μ : ∀ {n} {Γ : Ctx n} {u} (body : Exp Γ (u ∷ []) [] [] u)
        → Red {Γ = Γ} (obs u) (μᵉ body)

-- Every protocol event carries no payload, so a burst's values are the
-- only thing to check and a burst with none is satisfied outright.
satEvents : ∀ {A : Set} {P : A → Set} {vals : List A} {rest : List (InstEvent A)}
          → All P vals → All (EvSat P) rest
          → All (EvSat P) (map value vals ++ rest)
satEvents []       ar = ar
satEvents (p ∷ ps) ar = p ∷ satEvents ps ar

satOneShot : ∀ {n} {Γ : Ctx n} {u} {P : Val Γ u → Set} {vals}
             (id : Id) (sched : Sched Γ)
           → All P vals → StreamSat P (proj₁ (oneShotBurst vals id sched))
satOneShot id sched ps = (tt ∷ satEvents ps (tt ∷ tt ∷ [])) ∷ []

redTms : ∀ {n} {Γ : Ctx n} {u} (ts : List (Tm Γ [] [] [] u))
       → All (Red u) (map (λ tm → evalTm tm) ts)
redTms []       = []
redTms (x ∷ xs) = red-tm x ∷ redTms xs

-- THE BODY, AND THE ONE THING IT IS EVIDENCE FOR.  Its recursion is
-- structural in the TERM at every arm that has one, and every
-- recursive call is made at a schedule and a state the caller has
-- already moved — a fresh node installed, a counter bumped, a path
-- extended.  That those calls are free is exactly what the candidate's
-- quantification over every state buys, and writing the arms is the
-- only way to find out.
reducible : ∀ {n} {Γ : Ctx n} {t} (b : Closed Γ t) → Red {Γ = Γ} (obs t) b
reducible (input i) κ id now sched st = red-input i κ id now sched st
reducible (ofᵉ ts) κ id now sched st = _ , subs-of refl , satOneShot id sched (redTms ts)
reducible emptyᵉ κ id now sched st = _ , subs-empty refl , satOneShot id sched []
reducible (mapᵉ f b) κ id now sched st =
  let ((burst , sched₁ , st₁) , d , sat) = reducible b (map-f f ↠ κ) id now sched st
      (r , p , sat′) = red-push id now (map-f f) κ sat sched₁ st₁
  in r , subs-map d p , sat′
reducible (takeᵉ c b) κ id now sched st with evalTm c in ceq
... | zero  = _ , subs-take-zero ceq refl , satOneShot id sched []
... | suc k =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducible b (take-f nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (take-st (suc k)) st)
      (r , p , sat′) = red-push id now (take-f nid) κ sat sched₂ st₁
  in r , subs-take-suc ceq refl d p , sat′
reducible (scanᵉ f z b) κ id now sched st =
  let nid = Sched.nextNode sched
      ((burst , sched₂ , st₁) , d , sat) =
        reducible b (scan-f f nid ↠ κ) id now
          (record sched { nextNode = suc nid })
          (installNode nid (scan-st (evalTm z)) st)
      (r , p , sat′) = red-push id now (scan-f f nid) κ sat sched₂ st₁
  in r , subs-scan refl d p , sat′
reducible (mergeAllᵉ lim b) =
  red-merge-all lim b (λ {t} {e} {lo} κ → reducible b {t} {e} {lo} κ)
reducible (switchAllᵉ b) =
  red-switch-all b (λ {t} {e} {lo} κ → reducible b {t} {e} {lo} κ)
reducible (exhaustAllᵉ b) =
  red-exhaust-all b (λ {t} {e} {lo} κ → reducible b {t} {e} {lo} κ)
reducible (μᵉ body) κ id now sched st = red-μ body κ id now sched st
reducible (varᵉ ())
reducible (deferᵉ body) κ id now sched st =
  _ , subs-defer refl refl refl , (tt ∷ []) ∷ []
