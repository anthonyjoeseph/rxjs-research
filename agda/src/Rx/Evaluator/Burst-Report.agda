------------------------------------------------------------------
-- WHAT A SUBSCRIBE HANDS BACK ABOUT ITS OWN BURST.
------------------------------------------------------------------

-- THE HOP'S PREMISE, MADE SUPPLIABLE AT EVERY CALL RATHER THAN AT THE
-- ROOT.  The push cycle is handed a burst and has to know its
-- observables are shallower than the rank the subscribe entered at.
-- That is a claim about what a run PRODUCED, so it is stated over the
-- relation and not over any function — which is what keeps it out of
-- the builder's cycle, since a statement about a derivation needs no
-- builder to exist before it can be written.
--
-- AND IT IS AN ASSEMBLY HERE RATHER THAN A LEAF, WHICH IS WHAT SPLITS
-- THE CLAIM INTO THE PIECES ACTUALLY AT RISK.  Written as one postulate
-- it asserted the whole induction at once, and nothing said which of its
-- sixteen arms carried the content.  Walked as a body, most of them turn
-- out to be shape: a burst holding no `value` event satisfies the
-- predicate at every triple, and a one-shot's events are its values plus
-- bookkeeping.  What is left are the leaves below — the two that must
-- read a VALUE's depth against the rank, and the three that must follow
-- the run into another family.
--
-- AND THE ENVIRONMENT IS NOT DECORATION: IT IS WHAT THE CLAIM IS
-- DENOMINATED IN AT A SLOT REFERENCE.  A reference is one symbol
-- standing for a definition of any nesting, and a connect plumbs the
-- DEFINITION's burst out through that reference's own entry — so a
-- reading that prices the SYMBOL promises less than the burst delivers,
-- at the ordinary run rather than at some case a run avoids.
-- `Rx.Slot-Depth.slotDepth` prices it at the definition's own reading
-- instead, and under that the connect re-seeds at a rank the caller's
-- entry already dominates.
--
-- AND IT IS A PARAMETER RATHER THAN A READING OF THE SCHEDULE IN HAND,
-- WHICH IS WHAT KEEPS EVERY PREMISE A CONSTANT.  Read off `sched`, the
-- claim would be denominated afresh at each of the builder's recursive
-- calls and every one of them would owe a transport; fixed by the caller
-- the premises do not move, and the schedules only have to AGREE.
module Rx.Evaluator.Burst-Report where

open import Data.Bool using (Bool; true; false; if_then_else_; T)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; map; _++_)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; <⇒≤; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (Id; Source; Tick; InstEvent; InstEmit; init; value; close;
  handoff; complete; exhausted; subscribe; _at_from_as_)
open import Rx.Exp using (Ty; Ctx; Closed; Val; Tm; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_;
  obs; input; isData; evalTm; evalWith; Fn; applyFn)
open import Rx.Obs-Depth using (depᵗ; depᵗˢ; depᵛ)
open import Rx.Obs-Depth.Substitution using (AllData; []ᵈ; _∷ᵈ_; ≤pred⇒<;
  dep-eval-strict)
open import Rx.Slots using (Slots)
open import Rx.Slot-Depth using (slotDepth)
open import Rx.Strat-Order using (Tri)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; oneShotBurst;
  spentBurst; splitEvents; retagEvents; NodeId; NodeState; scan-st; take-st;
  mergeAll-st; switch-st; exhaust-st; takeVals; takeDispatch; scanVals; thruWrap;
  map-f; scan-f; take-f; from-inner; thru-outer; lookupNode)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  subscribeSharedSlot⇓; sharedConnect⇓; slot-spent; slot-join; slot-connect;
  stepFrame⇓; push-nil; push-cons;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all;
  subs-exhaust-all; subs-μ; subs-defer; sub-all; innerReact⇓; thruWalk⇓;
  step-map; step-scan; step-scan-nil; step-take; step-from-inner;
  step-thru-outer)
open import Rx.Evaluator.Doorless using (EntryOK; ValOK; HandedOK; BurstOK; EventOK;
  split-handed; inner-ok; under-ok; μ-entry)

------------------------------------------------------------------
-- THE SHAPES THAT CARRY NOTHING.  Several of the burst shapes a
-- subscribe produces hold no `value` event at all, so the predicate
-- holds of them at every triple and the arms returning one are closed
-- by construction rather than by an argument.
------------------------------------------------------------------

-- a spent source's burst: an init, a close and a complete
spent-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
           (src : Source) (id : Id)
         → BurstOK {Γ = Γ} {s = u} η (spentBurst src id) τ
spent-ok η τ src id = (tt ∷ᵃ tt ∷ᵃ tt ∷ᵃ []ᵃ) ∷ᵃ []ᵃ

-- a registration that joins something already live: one init, nothing
-- else, since the values it will see are the FUTURE ones
init-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
          (src : Source) (id : Id)
        → BurstOK {Γ = Γ} {s = u} η
            (((init src ∷ []) at id from src as subscribe) ∷ []) τ
init-ok η τ src id = (tt ∷ᵃ []ᵃ) ∷ᵃ []ᵃ

------------------------------------------------------------------
-- THE ONE-SHOT, WHICH IS ITS VALUES AND NOTHING ELSE.  Every remaining
-- event of the emit is bookkeeping, so the whole burst reduces to the
-- values' own property — and that is the only place a `value` can
-- enter a burst without another family having produced it.
------------------------------------------------------------------

private
  tail-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
            (src : Source) (vs : List (Val Γ u))
          → HandedOK η vs τ
          → All (EventOK η τ) (map value vs ++ close src exhausted ∷ complete ∷ [])
  tail-ok η τ src []       []ᵃ       = tt ∷ᵃ tt ∷ᵃ []ᵃ
  tail-ok η τ src (v ∷ vs) (p ∷ᵃ ps) = p ∷ᵃ tail-ok η τ src vs ps

  head-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
            (src : Source) (vs : List (Val Γ u))
          → HandedOK η vs τ → All (EventOK η τ) (init src ∷ map value vs)
  head-ok η τ src vs ps = tt ∷ᵃ values-ok vs ps
    where
    values-ok : ∀ ws → HandedOK η ws τ → All (EventOK η τ) (map value ws)
    values-ok []       []ᵃ       = []ᵃ
    values-ok (w ∷ ws) (q ∷ᵃ qs) = q ∷ᵃ values-ok ws qs

oneshot-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
             (vs : List (Val Γ u)) (id : Id) (sched : Sched Γ)
             {burst : Stream Γ u} {sched₁ : Sched Γ}
           → oneShotBurst vs id sched ≡ (burst , sched₁)
           → HandedOK η vs τ
           → BurstOK η burst τ
oneshot-ok η τ vs id sched refl ps =
  (tt ∷ᵃ tail-ok η τ _ vs ps) ∷ᵃ []ᵃ

-- and the cold source's, which has the same values under a different
-- tail: the async half is still owed, so nothing closes here
anchored-ok : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
              (vs : List (Val Γ u)) (id : Id) (src : Source)
            → HandedOK η vs τ
            → BurstOK η (((init src ∷ map value vs)
                           at id from src as subscribe) ∷ []) τ
anchored-ok η τ vs id src ps = head-ok η τ src vs ps ∷ᵃ []ᵃ

------------------------------------------------------------------
-- THE LEAVES.  What the walk cannot close, split by WHY: two that must
-- price a value's own depth against the rank, three that must follow
-- the run into a family this module does not walk.
------------------------------------------------------------------

-- A SCRIPTED SLOT'S PAYLOAD IS DATA, AND DATA IS UNCONDITIONALLY UNDER
-- EVERY RANK.  `ValOK` reads a rank only at `obs`, and the slot's own
-- side condition says the element type has no `obs` in it — so this is
-- an induction on the TYPE with nothing arithmetic in it at all, and it
-- is a leaf only because that induction has not been written.
--
-- PROBED: `Probed.Burst-Handed` — a flat type, a product and a sum, over
--   lists of two so the fold is spent.  Not reached: a data type nested
--   under a sum under a product.
postulate
  data-handed : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) (τ : Tri)
                (vs : List (Val Γ u)) → T (isData u) → HandedOK η vs τ

-- AND THE ONE PLACE A TERM BECOMES A VALUE, WHICH IS WHERE THE CLAIM IS
-- ACTUALLY ARITHMETIC.  `ofᵉ` evaluates its terms and emits them, so a
-- payload at `obs` is an expression the term WROTE, and the entry
-- invariant prices the whole list at `depᵗˢ`.  What is owed is that
-- evaluating a term does not deepen it past its own reading — which is
-- the substitution shelf's subject, and the reason that shelf exists.
--
-- AND WHAT IS LEFT AS A LEAF IS THE SILENT TERM, WHOSE READING IS
-- NOUGHT.  A term reading nothing wrote no `strmᵗ`, and the only other
-- way to hold an observable is to read one from a binder — which under
-- a data environment carries none.  So its value carries no observable
-- at all and the predicate holds at EVERY rank, the rank nought
-- included, which is the one case the drop cannot reach: there is
-- nothing to drop below.  It is a leaf because the induction saying so
-- is over the type and the term together rather than over either
-- alone.
--
-- AND IT IS STATED OPEN, WHICH IS WHAT THE FRAME WALK ASKS FOR RATHER
-- THAN A GENERALITY FOR ITS OWN SAKE.  A map frame applies a template
-- to one value, so the term it evaluates is open at exactly one binder
-- and the closed form is this one at the empty environment.  The data
-- hypothesis is what keeps that binder from being the observable the
-- statement says the term does not hold.
--
-- PROBED: `Probed.Burst-Handed` — at a flat payload, at a sum whose
--   other arm is an observable, which is the shape that could fail it
--   (the TYPE reaches an observable while the value takes the other
--   arm, so the reading has to select on the injection rather than on
--   the type), and at a term reading a data binder.  NOT reached: a
--   binder at a compound data type.
postulate
  eval-silent : ∀ {n} {Γ : Ctx n} {Θ u} {τ : Tri} (η : Fin n → ℕ)
                → AllData Θ → (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ)
                → depᵗ η tm ≡ 0 → ValOK η u τ (evalWith tm env)

private
  -- a value read under the rank satisfies the entry predicate at every
  -- type: the rank enters only at `obs`, and the join a compound is
  -- read by dominates each component's own reading
  valOK-below : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {U q r sz} (u : Ty)
                (v : Val Γ u) → depᵛ η u v < r → ValOK η u (U , q , r , sz) v
  valOK-below η unitᵗ    _        lt = tt
  valOK-below η boolᵗ    _        lt = tt
  valOK-below η natᵗ     _        lt = tt
  valOK-below η (s ×ᵗ t) (a , b)  lt =
      valOK-below η s a (≤-trans (s≤s (m≤m⊔n (depᵛ η s a) (depᵛ η t b))) lt)
    , valOK-below η t b (≤-trans (s≤s (m≤n⊔m (depᵛ η s a) (depᵛ η t b))) lt)
  valOK-below η (s +ᵗ t) (inj₁ a) lt = valOK-below η s a lt
  valOK-below η (s +ᵗ t) (inj₂ b) lt = valOK-below η t b lt
  valOK-below η (obs t)  _        lt = lt

  -- one element: the term's own reading bounds its value's, strictly
  -- wherever there is anything to be strict about.  Open at a data
  -- environment, since a frame's template is open at exactly one
  -- binder and a source's terms are this at the empty one
  handed-open : ∀ {n} {Γ : Ctx n} {Θ u} {U q r sz} (η : Fin n → ℕ)
                (dd : AllData Θ) (tm : Tm Γ [] [] Θ u)
                (env : All (Val Γ) Θ) → depᵗ η tm ≤ r
              → ValOK η u (U , q , r , sz) (evalWith tm env)
  handed-open {u = u} η dd tm env le with depᵗ η tm in eq
  ... | zero  = eval-silent η dd tm env eq
  ... | suc k = valOK-below η u (evalWith tm env)
                  (≤-trans (≤pred⇒< (subst (0 <_) (sym eq) (s≤s z≤n))
                                    (dep-eval-strict η dd tm env))
                           (subst (_≤ _) (sym eq) le))

of-handed : ∀ {n} {Γ : Ctx n} {u} {U q r sz} (η : Fin n → ℕ)
            (ts : List (Tm Γ [] [] [] u))
          → depᵗˢ η ts ≤ r
          → HandedOK η (map (λ tm → evalTm tm) ts) (U , q , r , sz)
of-handed η []        dep = []ᵃ
of-handed η (tm ∷ ts) dep =
    handed-open η []ᵈ tm []ᵃ (≤-trans (m≤m⊔n (depᵗ η tm) (depᵗˢ η ts)) dep)
  ∷ᵃ of-handed η ts (≤-trans (m≤n⊔m (depᵗ η tm) (depᵗˢ η ts)) dep)

-- THE LIST'S OWN READING, WHICH IS WHAT AN ENTRY POINT PAYS WITH.
-- Every builder quantifies over the rank, so a site ENTERING the
-- recursion is free to NAME one, and a rank set above the values it
-- already holds satisfies the premise outright — no hypothesis, no
-- field, and nothing carried in from the caller.  Only a site INSIDE
-- the descent is denied that, because there the rank is the quantity
-- the recursion is spending; the three entry points — the root, an
-- arrival, and the drain of a merge's queue — are outside it.
depᵛˢ : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) (u : Ty) → List (Val Γ u) → ℕ
depᵛˢ η u []       = 0
depᵛˢ η u (v ∷ vs) = depᵛ η u v ⊔ depᵛˢ η u vs

handed-below : ∀ {n} {Γ : Ctx n} {U q r sz} (η : Fin n → ℕ) (u : Ty)
               (vs : List (Val Γ u)) → depᵛˢ η u vs < r
             → HandedOK η vs (U , q , r , sz)
handed-below η u []       lt = []ᵃ
handed-below η u (v ∷ vs) lt =
    valOK-below η u v (≤-trans (s≤s (m≤m⊔n (depᵛ η u v) (depᵛˢ η u vs))) lt)
  ∷ᵃ handed-below η u vs
       (≤-trans (s≤s (m≤n⊔m (depᵛ η u v) (depᵛˢ η u vs))) lt)

-- WHAT A PUSH CYCLE HANDS ON.  The cycle steps one frame per emit and
-- the frame REWRITES the payload, so the burst coming out is not the
-- burst going in and the property has to be re-established rather than
-- transported.  Stated over the relation for the same reason the parent
-- is: it is a claim about what a run produced.
--
-- AND IT IS A BODY OVER ONE LEAF, WHICH IS WHERE THE CONTENT TURNED
-- OUT TO BE.  The cycle's relation has two constructors and the empty
-- one closes by construction; the other emits one concatenation, and
-- three of its four segments carry nothing -- the split's bookkeeping
-- half and the retagged events both DROP `value`, so the predicate
-- holds of them whatever the frame did, and a terminal `complete` is
-- ⊤.  What is left is the segment the frame WROTE, which is the leaf
-- below.  Walking it is what says the risk sits at the frame step and
-- not at the cycle.
private
  -- the bookkeeping half of a split holds no `value` at all, so the
  -- predicate holds of it at every triple and at whatever type the
  -- retag is pinned to by the call
  split-book : ∀ {n} {Γ : Ctx n} {s u} {τ : Tri} (η : Fin n → ℕ)
             → (es : List (InstEvent (Val Γ s)))
             → All (EventOK {u = u} η τ)
                 (proj₁ (proj₂ (splitEvents {A = Val Γ u} es)))
  split-book η []               = []ᵃ
  split-book η (value _   ∷ es) = split-book η es
  split-book η (init _    ∷ es) = tt ∷ᵃ split-book η es
  split-book η (close _ _ ∷ es) = tt ∷ᵃ split-book η es
  split-book η (handoff _ ∷ es) = tt ∷ᵃ split-book η es
  split-book η (complete  ∷ es) = split-book η es

  -- and the retag, which drops `value` for the same reason
  retag-book : ∀ {n} {Γ : Ctx n} {A : Set} {u} {τ : Tri} (η : Fin n → ℕ)
             → (es : List (InstEvent A))
             → All (EventOK {Γ = Γ} {u = u} η τ) (retagEvents es)
  retag-book η []               = []ᵃ
  retag-book η (value _   ∷ es) = retag-book η es
  retag-book η (init _    ∷ es) = tt ∷ᵃ retag-book η es
  retag-book η (close _ _ ∷ es) = tt ∷ᵃ retag-book η es
  retag-book η (handoff _ ∷ es) = tt ∷ᵃ retag-book η es
  retag-book η (complete  ∷ es) = tt ∷ᵃ retag-book η es

  -- the handed values read back as the events they are delivered as
  handed-events : ∀ {n} {Γ : Ctx n} {u} {τ : Tri} (η : Fin n → ℕ)
                → (vs : List (Val Γ u)) → HandedOK η vs τ
                → All (EventOK η τ) (map value vs)
  handed-events η []       []ᵃ        = []ᵃ
  handed-events η (v ∷ vs) (p ∷ᵃ ps) = p ∷ᵃ handed-events η vs ps

  -- the terminal marker, which carries no payload either way
  fin-events : ∀ {n} {Γ : Ctx n} {u} {τ : Tri} (η : Fin n → ℕ) (b : Bool)
             → All (EventOK {Γ = Γ} {u = u} η τ)
                 (if b then complete ∷ [] else [])
  fin-events η true  = tt ∷ᵃ []ᵃ
  fin-events η false = []ᵃ

-- WHAT THE ENTRY INVARIANT SAYS ABOUT THE FRAME ITSELF, which is the
-- one thing the step needs and the cycle did not carry.  Two of the
-- five heads hold a template, and the reading of the expression the
-- subscribe entered at is a JOIN over that template and the inner --
-- so the caller already has this and hands it down rather than
-- proving it.  The other three hold no term at all.
FrameOK : ∀ {n} {Γ : Ctx n} {s u} (η : Fin n → ℕ) → Frame Γ s u → Tri → Set
FrameOK η (map-f fn)          (_ , _ , r , _) = depᵗ η fn ≤ r
FrameOK η (scan-f fn nid)     (_ , _ , r , _) = depᵗ η fn ≤ r
FrameOK η (take-f nid)        _           = ⊤
FrameOK η (from-inner _ _ _)  _           = ⊤
FrameOK η (thru-outer _ _)    _           = ⊤

private
  -- a take hands on a PREFIX of what it was given, so any property of
  -- the values survives it whatever the budget was
  take-vals-ok : ∀ {n} {Γ : Ctx n} {s} {τ : Tri} (η : Fin n → ℕ)
                 (k : ℕ) (vs : List (Val Γ s)) → HandedOK η vs τ
               → HandedOK η (proj₁ (takeVals k vs)) τ
  take-vals-ok η zero          vs        _          = []ᵃ
  take-vals-ok η (suc k)       []        _          = []ᵃ
  take-vals-ok η (suc zero)    (v ∷ _)  (p ∷ᵃ _)   = p ∷ᵃ []ᵃ
  take-vals-ok η (suc (suc k)) (v ∷ vs) (p ∷ᵃ ps) =
    p ∷ᵃ take-vals-ok η (suc k) vs ps

  -- and the dispatch around it: every arm either hands that prefix on
  -- or hands nothing on, and the cut only changes the bookkeeping
  take-arm : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s} {τ : Tri}
             (η : Fin n → ℕ) (nid : NodeId) (vs : List (Val Γ s))
             (fin : Bool) (sched : Sched Γ) (st : EvalSt e)
             (ns : Maybe (NodeState Γ)) → HandedOK η vs τ
           → HandedOK η
               (proj₁ (takeDispatch {e = e} nid vs fin sched st ns)) τ
  take-arm η nid vs fin sched st (just (take-st k)) ps
    with proj₂ (proj₂ (takeVals k vs))
  ... | true  = take-vals-ok η k vs ps
  ... | false = take-vals-ok η k vs ps
  take-arm η nid vs fin sched st nothing                    ps = []ᵃ
  take-arm η nid vs fin sched st (just (scan-st _))         ps = []ᵃ
  take-arm η nid vs fin sched st (just (mergeAll-st _ _ _ _)) ps = []ᵃ
  take-arm η nid vs fin sched st (just (switch-st _ _))     ps = []ᵃ
  take-arm η nid vs fin sched st (just (exhaust-st _ _))    ps = []ᵃ

-- THE MAP AT A DATA PAYLOAD, WHICH IS THE ONE-VALUE DROP AND NOTHING
-- MORE.  `applyFn` is evaluation at a one-binder environment, so the
-- arm is the source's own reading generalised from the empty
-- environment to that binder -- and the data hypothesis is what stops
-- the binder being the observable the drop assumes is not there.
map-data : ∀ {n} {Γ : Ctx n} {s u} {τ : Tri} (η : Fin n → ℕ)
           → isData s ≡ true → (fn : Fn Γ [] [] [] s u)
             (vs : List (Val Γ s)) → depᵗ η fn ≤ proj₁ (proj₂ (proj₂ τ))
           → HandedOK η vs τ → HandedOK η (map (applyFn fn) vs) τ
map-data {τ = _ , _ , _} η ds fn []       le []ᵃ        = []ᵃ
map-data {τ = _ , _ , _} η ds fn (v ∷ vs) le (_ ∷ᵃ ps) =
    handed-open η (ds ∷ᵈ []ᵈ) fn (v ∷ᵃ []ᵃ) le
  ∷ᵃ map-data η ds fn vs le ps

-- AND THE MAP AT A PAYLOAD THAT IS NOT DATA, WHICH IS WHERE THE
-- MEASURE RUNS OUT.  The bound on the frame is a JOIN and the run is a
-- SUM: evaluation at an environment holding an observable costs the
-- template's reading PLUS the environment's, so a template wrapping
-- its own argument hands back a value deeper than either side and no
-- premise about the FRAME can close it -- the argument is the other
-- addend.  Repairing it is a change to the reading every tier is
-- denominated in, which is why the arm is a leaf and not a weakening.
--
-- REFUTED: `Refuted.Template-Passes` — the crossing at the shelf's own
--   statement, which is where it was found first: a template that
--   merely passes its argument through reifies it under a `strmᵗ` the
--   template never wrote, so the emission is as deep as whatever was
--   handed in.  Its rows are the witness for this arm too, since the
--   quantity that fails here is the one it reads.
--
-- RECOVERY: git show 9b538b5b:agda/src/Rx/Obs-Depth/Substitution.agda
--   restores the shelf that prices this crossing — the open form and
--   the environment reading it is denominated in, which are what a
--   repaired map clause would be proven against.
postulate
  map-open : ∀ {n} {Γ : Ctx n} {s u} {τ : Tri} (η : Fin n → ℕ)
           → isData s ≡ false → (fn : Fn Γ [] [] [] s u)
             (vs : List (Val Γ s)) → depᵗ η fn ≤ proj₁ (proj₂ (proj₂ τ))
           → HandedOK η vs τ → HandedOK η (map (applyFn fn) vs) τ

-- AND THE FOLD, WHICH THE SAME REPAIR DOES NOT REACH.  A scan re-enters
-- its own template with the accumulator it last produced, so the
-- reading climbs once per delivery and the outputs of ONE frame,
-- entered under ONE bound, grow with the LENGTH of the burst.  No
-- static reading of the syntax carries a length, so this is not the map
-- arm's gap at another head: it is a question about whether the depth
-- component can be read off the program at all.
--
-- REFUTED: `Refuted.Scan-Deepens` — the fold whose template re-wraps its
--   accumulator, at the constructor this arm stands over.
postulate
  scan-handed : ∀ {n} {Γ : Ctx n} {s u} {τ : Tri} (η : Fin n → ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s))
    {outs : List (Val Γ u)} {ac′ : Val Γ u} →
    depᵗ η fn ≤ proj₁ (proj₂ (proj₂ τ)) → HandedOK η vs τ →
    scanVals fn ac vs ≡ (outs , ac′) → HandedOK η outs τ

-- AND THE TWO HEADS THAT LEAVE THIS MODULE.  An `*All` frame does not
-- rewrite a payload: it SUBSCRIBES one, or it delivers what an inner
-- subscription produced — so what is owed is the same claim about
-- another family's run, and the rank it has to be made at is the one
-- that family entered at rather than this frame's.
postulate
  inner-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s lo} {τ : Tri}
    (η : Fin n → ℕ) {op allNid inst} {κ : Path Γ lo s t} {id now}
    {vs : List (Val Γ s)} {sched : Sched Γ} {st : EvalSt e} {fin}
    {vals : List (Val Γ s)} {evs : List (InstEvent (Val Γ t))} {fin′}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    HandedOK η vs τ →
    innerReact⇓ {e = e} op allNid inst κ id now vs sched st fin
      (vals , evs , fin′ , sched′ , st′) →
    HandedOK η vals τ

  thru-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
    (η : Fin n → ℕ) {op nid} {κ : Path Γ lo u t} {id now}
    {vs : List (Val Γ (obs u))} {sched : Sched Γ} {st : EvalSt e}
    (fin : Bool)
    (res : List (Val Γ u) × List (InstEvent (Val Γ t)) × Sched Γ × EvalSt e) →
    HandedOK η vs τ →
    thruWalk⇓ {e = e} op nid κ id now vs sched st res →
    HandedOK η (proj₁ (thruWrap {e = e} op nid fin res)) τ

-- WHAT THE FRAME WROTE, WHICH IS THE ONE SEGMENT AT RISK.  A step is
-- handed the emit's own values and returns the values it delivers
-- onward, and the six heads it can take do genuinely different things:
-- one returns nothing, one filters what it was given, two REWRITE the
-- payload through a template, and two follow the run into another
-- family.  So this is where the claim has to be split next, and the
-- split is what the arms above say it is.
--
-- DEAD ROUTE: bounding the output rank instead of restricting the
--   payload -- state the cycle as carrying `τ` in and a larger `τ` out.
--   It is STRUCTURALLY DEAD at the walk below rather than here: the
--   entry invariant that feeds this is fixed by the caller at one
--   `slotDepth sl`, and the walk re-enters at that same rank through
--   every recursive arm, so a rank that grows per frame has nowhere to
--   be recorded and the `subs-μ` arm, which re-enters at the unfolded
--   body, would have to grow it without bound.
--
-- RECOVERY: git show 80e527f9:agda/src/Verify-Rank-Sufficient/Push-Carried.agda
--   restores the predecessor's proof of exactly this over the machine,
--   with the five frame clauses worked out; what does not transport is
--   the denomination, since the statement it carries is the
--   unenvironmented one the two retired witnesses killed.
step-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u}
  {κ : Path Γ lo u t} {vs : List (Val Γ s)} {c : Bool}
  {sched : Sched Γ} {st : EvalSt e}
  {vals : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))} {fin : Bool}
  {sched′ : Sched Γ} {st′ : EvalSt e} →
  FrameOK η fr τ → HandedOK η vs τ →
  stepFrame⇓ {e = e} id now fr κ vs c sched st
    (vals , evs , fin , sched′ , st′) →
  HandedOK η vals τ
step-handed {s = s} {τ = _ , _ , _} η {fr = map-f fn} le ps step-map
  with isData s in ds
... | true  = map-data η ds fn _ le ps
... | false = map-open η ds fn _ le ps
step-handed {τ = _ , _ , _} η {fr = scan-f fn nid} le ps (step-scan _ eq) =
  scan-handed η fn _ _ le ps eq
step-handed η le ps step-scan-nil = []ᵃ
step-handed η {fr = take-f nid} le ps
             (step-take {vals = vs} {fin = fin} {sched = sched} {st = st}) =
  take-arm η nid vs fin sched st (lookupNode nid (EvalSt.nodes st)) ps
step-handed η le ps (step-from-inner r)  = inner-handed η ps r
step-handed η le ps
            (step-thru-outer {fin = fin} {vs = vs} {bs = bs}
                             {sched′ = sched′} {st′ = st′} w) =
  thru-handed η fin (vs , bs , sched′ , st′) ps w

push-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
  {bs : Stream Γ s} {sched : Sched Γ} {st : EvalSt e}
  {burst : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} →
  FrameOK η fr τ → BurstOK η bs τ →
  pushBurst⇓ {e = e} id now fr κ bs sched st (burst , sched′ , st′) →
  BurstOK η burst τ
push-carries η fok ok push-nil = []ᵃ
push-carries {u = u} {τ = τ} η fok (okem ∷ᵃ okrest)
             (push-cons {em = em} {evs = evs} {fin′ = fin′} sp step rest) =
    ++⁺ (subst (All (EventOK η τ))
               (cong (λ z → proj₁ (proj₂ z)) sp)
               (split-book {u = u} η (InstEmit.events em)))
        (++⁺ (retag-book η evs)
             (++⁺ (handed-events η _
                     (step-handed η fok
                       (subst (λ ws → HandedOK η ws τ) (cong proj₁ sp)
                              (split-handed η (InstEmit.events em) okem))
                       step))
                  (fin-events η fin′)))
  ∷ᵃ push-carries η fok okrest rest

-- AND THE SHARED SLOT, WHICH IS A WALK AFTER ALL — OVER THREE
-- CONSTRUCTORS OF WHICH TWO CARRY NOTHING.  A slot the run has already
-- spent hands back the spent burst and a slot joining something already
-- live hands back one init, so both close by the bookkeeping lemmas
-- above at every triple.  What is left is the CONNECT, which is the only
-- arm that re-enters the subscribe, and so the only one where the two
-- readings can differ.
postulate
  -- THE CONNECT, WHERE THE SLOT'S OWN READING MEETS THE CALLER'S.  The
  -- fan-out re-enters at `slotDepth sl i` rather than at the rank the
  -- caller fixed, so the burst comes back reported against a triple this
  -- statement's premise does not mention.  `Rx.Evaluator.Doorless.
  -- connect-entry` already proves the re-entry invariant holds at the
  -- slot's own triple, and `depᵉ (slotDepth sl) (input i)` IS
  -- `slotDepth sl i`, so the caller's premise already dominates that
  -- rank — what is missing between them is that `BurstOK` may be WIDENED
  -- along that domination, which nothing in the tree yet states.  That
  -- widening is the same relating the queued observable needs, which is
  -- why this arm is where the record's field is owed.
  --
  -- AND IT IS ORDERED BEHIND THE BUILDER AGREEMENT, WHICH IS WHAT STOPS
  -- IT BEING WALKED TODAY.  The recursion itself is available: both of
  -- `sharedConnect⇓`'s constructors prepend bookkeeping to a
  -- `sharedPlumb` of a burst some `subscribeE⇓` produced, and that
  -- derivation is a structural subterm — so this is a CLAUSE of the walk
  -- below and not a family it cannot perform.  What it cannot supply is
  -- `connect-entry`'s premise: the constructor carries the equation
  -- against the SCHEDULE's table and `connect-entry` wants it against
  -- `sl`, so the clause needs `Sched.slots sched ≡ sl` at a schedule
  -- another clause built — which is what widening a builder's RETURN
  -- type is for.
  --
  -- REFUTED: `Refuted.Carried-Derived` — the reading with no environment
  --   at all, at that run.  It is this arm the witness stands at: a
  --   reference is one symbol standing for a definition of any nesting, so
  --   a reading that prices the SYMBOL promises less than the connect
  --   delivers.
  connect-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
    (sl : Slots Γ) {i : Fin n} {d : Closed Γ (lookup Γ i)}
    {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
    {id : Id} {now : Tick}
    {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ (lookup Γ i)}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    EntryOK {Γ = Γ} (slotDepth sl) (input i) τ →
    sharedConnect⇓ {e = e} i d κ below id now sched st
      (burst , sched′ , st′) →
    BurstOK (slotDepth sl) burst τ

slot-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {lo} {τ : Tri}
  (sl : Slots Γ) {i : Fin n} {d : Closed Γ (lookup Γ i)}
  {κ : Path Γ lo (lookup Γ i) t} {below : toℕ i < lo}
  {id : Id} {now : Tick}
  {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ (lookup Γ i)}
  {sched′ : Sched Γ} {st′ : EvalSt e} →
  EntryOK {Γ = Γ} (slotDepth sl) (input i) τ →
  subscribeSharedSlot⇓ {e = e} i d κ below id now sched st
    (burst , sched′ , st′) →
  BurstOK (slotDepth sl) burst τ
slot-carries {τ = τ} sl ok (slot-spent _)       = spent-ok (slotDepth sl) τ _ _
slot-carries {τ = τ} sl ok (slot-join _ _)      = init-ok (slotDepth sl) τ _ _
slot-carries         sl ok (slot-connect _ _ c) = connect-carries sl ok c

------------------------------------------------------------------
-- THE WALK.
------------------------------------------------------------------

-- STRUCTURAL SCC: burst-carries all-carries
mutual

 all-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
   (sl : Slots Γ) {op ns} {b : Closed Γ (obs u)} {κ : Path Γ lo u t}
   {id : Id} {now : Tick} {sched : Sched Γ} {st : EvalSt e}
   {burst : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} →
   EntryOK (slotDepth sl) b τ →
   subscribeAll⇓ {e = e} op ns b κ id now sched st (burst , sched′ , st′) →
   BurstOK (slotDepth sl) burst τ
 all-carries sl ok (sub-all _ d p) = push-carries _ tt (burst-carries sl ok d) p

 burst-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {u lo} {τ : Tri}
   (sl : Slots Γ) {b : Closed Γ u} {κ : Path Γ lo u t} {id : Id} {now : Tick}
   {sched : Sched Γ} {st : EvalSt e} {burst : Stream Γ u}
   {sched′ : Sched Γ} {st′ : EvalSt e} →
   EntryOK (slotDepth sl) b τ →
   subscribeE⇓ {e = e} b κ id now sched st (burst , sched′ , st′) →
   BurstOK (slotDepth sl) burst τ
 burst-carries {τ = τ} sl ok (subs-floor _)           = spent-ok _ τ _ _
 burst-carries {τ = τ} sl ok (subs-hot-done _ _ _)    = spent-ok _ τ _ _
 burst-carries {τ = τ} sl ok (subs-hot-live _ _ _)    = init-ok _ τ _ _
 burst-carries {τ = τ} sl ok (subs-defer _ _ _)       = init-ok _ τ _ _
 burst-carries {τ = τ} sl ok (subs-shared _ s)        = slot-carries sl ok s
 burst-carries {τ = τ} sl ok (subs-empty eq)          = oneshot-ok _ τ [] _ _ eq []ᵃ
 burst-carries {τ = τ} sl ok (subs-take-zero _ eq)    = oneshot-ok _ τ [] _ _ eq []ᵃ
 burst-carries {τ = U , q , r , sz} sl (_ , dep) (subs-of eq) =
   oneshot-ok _ (U , q , r , sz) _ _ _ eq (of-handed (slotDepth sl) _ dep)
 burst-carries {τ = τ} sl ok (subs-cold-sync {ok = okd} _ _ eq) =
   oneshot-ok _ τ _ _ _ eq (data-handed _ τ _ okd)
 burst-carries {τ = τ} sl ok (subs-cold-async {ok = okd} _ _ _ _) =
   anchored-ok _ τ _ _ _ (data-handed _ τ _ okd)
 burst-carries {τ = _ , _ , _} sl ok (subs-map d p) =
   push-carries _ (≤-trans (m≤m⊔n _ _) (proj₂ ok))
     (burst-carries sl (inner-ok ok) d) p
 burst-carries sl ok (subs-merge-all a)   = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-switch-all a)  = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-exhaust-all a) = all-carries sl (under-ok ok) a
 burst-carries sl (sz≤ , r≤) (subs-μ {body = body} d) =
   burst-carries sl
     ( ≤-trans (<⇒≤ (unfoldμ-shrinks body)) sz≤
     , μ-entry (slotDepth sl) body r≤ ) d
 burst-carries sl ok (subs-take-suc _ _ d p) =
   push-carries _ tt (burst-carries sl (inner-ok ok) d) p
 burst-carries {τ = _ , _ , _} sl ok (subs-scan _ d p) =
   push-carries _ (≤-trans (m≤m⊔n _ _) (≤-trans (m≤m⊔n _ _) (proj₂ ok)))
     (burst-carries sl (inner-ok ok) d) p
