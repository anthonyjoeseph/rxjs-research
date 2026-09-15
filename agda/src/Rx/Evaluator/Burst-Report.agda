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
open import Data.List using (List; []; _∷_; map; _++_; length)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _+_; _*_; _⊔_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; <⇒≤; m≤m⊔n; m≤n⊔m; ⊔-lub;
  ⊔-identityʳ; ≤-reflexive)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (Id; Source; Tick; InstEvent; InstEmit; init; value; close;
  handoff; complete; exhausted; subscribe; _at_from_as_)
open import Rx.Exp using (Ty; Ctx; Closed; Val; Tm; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_;
  obs; input; isData; evalTm; evalWith; Fn; applyFn; reify)
open import Rx.Obs-Depth using (depᵉ; depᵗ; depᵗˢ; depᵛ; bindᵃᵉ; bindˢᵗ)
open import Rx.Obs-Depth.Substitution using (dep-eval; envDepth)
open import Rx.Evaluator.Scan-Climb using (Rate; scan-climbs)
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
  split-handed; inner-ok; under-ok; entry-inner; μ-entry)

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
private
  -- a value read under the rank satisfies the entry predicate at every
  -- type: the rank enters only at `obs`, and the join a compound is
  -- read by dominates each component's own reading
  valOK-below : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {U r sz} (u : Ty)
                (v : Val Γ u) → depᵛ η u v < r → ValOK η u (U , r , sz) v
  valOK-below η unitᵗ    _        lt = tt
  valOK-below η boolᵗ    _        lt = tt
  valOK-below η natᵗ     _        lt = tt
  valOK-below η (s ×ᵗ t) (a , b)  lt =
      valOK-below η s a (≤-trans (s≤s (m≤m⊔n (depᵛ η s a) (depᵛ η t b))) lt)
    , valOK-below η t b (≤-trans (s≤s (m≤n⊔m (depᵛ η s a) (depᵛ η t b))) lt)
  valOK-below η (s +ᵗ t) (inj₁ a) lt = valOK-below η s a lt
  valOK-below η (s +ᵗ t) (inj₂ b) lt = valOK-below η t b lt
  valOK-below η (obs t)  _        lt = lt

  -- AND THE SAME PREDICATE READ THROUGH `reify`, WHICH IS THE FORM
  -- EVERYTHING ARITHMETIC HERE ARRIVES IN.  `ValOK` is strict at an
  -- observable and vacuous everywhere else; `reify` writes one `strmᵗ`
  -- at an observable and nothing anywhere else.  So one weak
  -- inequality about the reification says exactly what the predicate
  -- says, at every type at once, and the strictness is a reduction
  -- rather than a premise anybody has to carry.
  valOK-reify : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {U r sz} (u : Ty)
                (v : Val Γ u) → depᵗ η 0 (reify v) ≤ r
              → ValOK η u (U , r , sz) v
  valOK-reify η unitᵗ    _        le = tt
  valOK-reify η boolᵗ    _        le = tt
  valOK-reify η natᵗ     _        le = tt
  valOK-reify η (s ×ᵗ t) (a , b)  le =
      valOK-reify η s a (≤-trans (m≤m⊔n _ _) le)
    , valOK-reify η t b (≤-trans (m≤n⊔m _ _) le)
  valOK-reify η (s +ᵗ t) (inj₁ a) le = valOK-reify η s a le
  valOK-reify η (s +ᵗ t) (inj₂ b) le = valOK-reify η t b le
  valOK-reify η (obs t)  _        le = le

  -- and back, which is what makes a value admissible as an ENVIRONMENT
  valOK⇒reify : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {U r sz} (u : Ty)
                (v : Val Γ u) → ValOK η u (U , r , sz) v
              → depᵗ η 0 (reify v) ≤ r
  valOK⇒reify η unitᵗ    _        ok = z≤n
  valOK⇒reify η boolᵗ    _        ok = z≤n
  valOK⇒reify η natᵗ     _        ok = z≤n
  valOK⇒reify η (s ×ᵗ t) (a , b)  (p , q) =
    ⊔-lub (valOK⇒reify η s a p) (valOK⇒reify η t b q)
  valOK⇒reify η (s +ᵗ t) (inj₁ a) ok = valOK⇒reify η s a ok
  valOK⇒reify η (s +ᵗ t) (inj₂ b) ok = valOK⇒reify η t b ok
  valOK⇒reify η (obs t)  _        ok = ok

  -- a rank only ever rises along a frame, and the predicate follows it
  valOK-mono : ∀ {n} {Γ : Ctx n} (η : Fin n → ℕ) {U q sz U′ r sz′} (u : Ty)
               (v : Val Γ u) → q ≤ r → ValOK η u (U , q , sz) v
             → ValOK η u (U′ , r , sz′) v
  valOK-mono η u v qr ok = valOK-reify η u v (≤-trans (valOK⇒reify η u v ok) qr)

  handed-mono : ∀ {n} {Γ : Ctx n} {u} (η : Fin n → ℕ) {U q sz U′ r sz′}
                (vs : List (Val Γ u)) → q ≤ r → HandedOK η vs (U , q , sz)
              → HandedOK η vs (U′ , r , sz′)
  handed-mono η []       qr []ᵃ       = []ᵃ
  handed-mono {u = u} η (v ∷ vs) qr (p ∷ᵃ ps) =
    valOK-mono η u v qr p ∷ᵃ handed-mono η vs qr ps

  -- ONE ELEMENT, AND IT IS NOW A BODY RATHER THAN THREE LEAVES.  The
  -- term's own reading bounds its value's, at the bound its
  -- environment satisfies — which is the whole of the substitution
  -- shelf's subject, and unconditional in what the binders hold.  The
  -- data hypothesis the three predecessors carried was never about the
  -- mathematics: it was how a reading with no bound argument excluded
  -- the case it could not price.
  handed-open : ∀ {n} {Γ : Ctx n} {Θ u} {U r sz} (η : Fin n → ℕ)
                (tm : Tm Γ [] [] Θ u) (env : All (Val Γ) Θ) (m : ℕ)
              → envDepth η env ≤ m → depᵗ η m tm ≤ r
              → ValOK η u (U , r , sz) (evalWith tm env)
  handed-open {u = u} η tm env m h le =
    valOK-reify η u (evalWith tm env)
      (≤-trans (dep-eval η tm env m h) le)

of-handed : ∀ {n} {Γ : Ctx n} {u} {U r sz} (η : Fin n → ℕ)
            (ts : List (Tm Γ [] [] [] u))
          → depᵗˢ η 0 ts ≤ r
          → HandedOK η (map (λ tm → evalTm tm) ts) (U , r , sz)
of-handed η []        dep = []ᵃ
of-handed η (tm ∷ ts) dep =
    handed-open η tm []ᵃ 0 ≤-refl
      (≤-trans (m≤m⊔n (depᵗ η 0 tm) (depᵗˢ η 0 ts)) dep)
  ∷ᵃ of-handed η ts (≤-trans (m≤n⊔m (depᵗ η 0 tm) (depᵗˢ η 0 ts)) dep)

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

handed-below : ∀ {n} {Γ : Ctx n} {U r sz} (η : Fin n → ℕ) (u : Ty)
               (vs : List (Val Γ u)) → depᵛˢ η u vs < r
             → HandedOK η vs (U , r , sz)
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
-- subscribe entered at prices that template AT THE BOUND ITS SOURCE
-- EMITS UNDER -- so the caller already has this and hands it down
-- rather than proving it.  The other three hold no term at all, and
-- what they owe instead is that the rank did not fall.
--
-- IT RELATES TWO RANKS AND NOT ONE, AND THAT IS THE WHOLE REPAIR.  A
-- frame is handed what its source emitted and delivers onward what it
-- wrote, and those are two different depths whenever the template
-- WRAPS -- so a predicate denominated at a single rank asserts that a
-- template which deepens its argument does not, which is false at a
-- template as small as one that re-emits what it was given.  The
-- source's rank is the bound the template is READ at; the frame's is
-- the bound its output is CLAIMED under; and the reading's own
-- composing clause is what makes the caller able to supply both.
FrameOK : ∀ {n} {Γ : Ctx n} {s u} (η : Fin n → ℕ) → Frame Γ s u → Tri → Tri → Set
FrameOK η (map-f fn)          (_ , q , _) (_ , r , _) = depᵗ η q fn ≤ r
FrameOK η (scan-f fn nid)     (_ , q , _) (_ , r , _) = depᵗ η q fn ≤ r
FrameOK η (take-f nid)        (_ , q , _) (_ , r , _) = q ≤ r
FrameOK η (from-inner _ _ _)  (_ , q , _) (_ , r , _) = q ≤ r
FrameOK η (thru-outer _ _)    (_ , q , _) (_ , r , _) = q ≤ r

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

-- THE MAP, WHICH IS ONE EVALUATION PER VALUE AND NO ARITHMETIC AT ALL.
-- `applyFn` is evaluation at a one-binder environment, so what the
-- template hands back is priced by the template READ AT the bound that
-- binder satisfies -- and the binder holds exactly what the source
-- emitted, whose bound is the frame's incoming rank.  There is no
-- case split on whether the payload is data: a binder carrying an
-- observable is PRICED here rather than excluded, which is what the
-- bound argument bought and what three of this arm's predecessors
-- existed to work around.
map-handed : ∀ {n} {Γ : Ctx n} {s u} {U q sz U′ r sz′} (η : Fin n → ℕ)
             (fn : Fn Γ [] [] [] s u) (vs : List (Val Γ s))
           → depᵗ η q fn ≤ r → HandedOK η vs (U , q , sz)
           → HandedOK η (map (applyFn fn) vs) (U′ , r , sz′)
map-handed η fn []       le []ᵃ       = []ᵃ
map-handed {s = s} η fn (v ∷ vs) le (p ∷ᵃ ps) =
    handed-open η fn (v ∷ᵃ []ᵃ) _
      (≤-trans (≤-reflexive (⊔-identityʳ (depᵗ η 0 (reify v))))
               (valOK⇒reify η s v p))
      le
  ∷ᵃ map-handed η fn vs le ps

-- AND WHAT THE FOLD STILL OWES ONCE ITS ITERATION IS PRICED, WHICH IS
-- A RESERVATION AND TWO UNKNOWNS.  The climb itself is no longer a
-- claim -- `scan-climbs` proves the outputs sit one RATE per delivery
-- above where the fold started -- so what is left is whether the rank
-- the frame was ENTERED at can afford that, and the leaf below says it
-- can by producing the figure the whole burst fits under.
--
-- THE FIGURE HIDES TWO DIFFERENT GAPS, AND ONLY ONE OF THEM IS THE
-- TIER'S QUESTION.  One is the LENGTH: a rate per delivery needs a
-- count of deliveries, and every rank in this development is read off
-- the program, where there is no count to read.  The other is the
-- SEED, and it is a store question rather than an arithmetic one -- the
-- accumulator a fold re-enters with is whatever its node last stored,
-- and no premise here says anything about what that reads.  Both are
-- pinned by the same witness, which is why they share a leaf: the
-- figure has to dominate the seed AND leave a rate per element under
-- the rank.
--
-- AND THE Σ IS PINNED FROM BELOW, WHICH IS WHAT KEEPS IT FROM BEING
-- SATISFIABLE BY ENLARGEMENT.  Its first two conjuncts grow easier as
-- the figure rises and the third grows harder, so the witness cannot be
-- inflated into a proof -- the statement is exactly as strong as the
-- rank is generous.
--
-- AND THE COUNT IS OWED AT THE FOLD ALONE, WHICH NARROWS EVERY SEARCH
-- FOR ITS CARRIER.  Of the expression formers, `scanᵉ` is the only one
-- whose output at a delivery is built from its own output at the
-- delivery before; every other is a fixed transformation of what it
-- was handed, so an instant it produces is no wider than the instant it
-- consumed.  The one other self-reference is `μᵉ`, and that one is
-- settled rather than open: an occurrence of the bound var is
-- reachable only past a `deferᵉ`, which ends the instant, so
-- `unfoldμ-shrinks` proves an unfolding measures exactly what the body
-- did.  Recursion buys more instants, never a wider one.  So whatever
-- carries the count has to hold what a FOLD accumulates, and a census
-- of everything that grows with a run looks in more places than an
-- instant's width can come from.
--
-- REFUTED: `Refuted.Scan-Deepens` — the rate, proven over every burst
--   length, which is why the figure below carries one at all.
-- REFUTED: `Refuted.Scan-Reachable` — the same template RUN, which
--   kills the escape of restricting the claim to reachable
--   configurations, and whose positive figure is in this leaf's own
--   currency: a bound in the reading PLUS the length holds there, while
--   the reading alone does not.
-- REFUTED: `Refuted.Scan-Length` — this statement, at an ordinary
--   five-element burst of plain numbers.  The length reservation is
--   asked of `r` by the conclusion and related to nothing by the
--   premises, so the leaf is false as written and no figure repairs it.
-- REFUTED: `Refuted.Burst-Length` — and the premise that would carry
--   the count, killed at the only channel able to hold one.  A count is
--   readable where the walk seeds a frame's rank, but that site builds
--   a derivation while this leaf is owed over one, and the single
--   length-shaped component between them is outgrown by one instant of
--   a doubling cascade.  So restating this with the count as a premise
--   moves tracked debt into a hypothesis nothing can discharge; what
--   the leaf is owed is a quantity read off the RUN, which is a change
--   to what the entry carries rather than to what this states.
postulate
  scan-fits : ∀ {n} {Γ : Ctx n} {s u} {U q sz r} (η : Fin n → ℕ)
    (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s))
    → depᵗ η q fn ≤ r → HandedOK η vs (U , q , sz)
    → Σ ℕ (λ a → (depᵗ η 0 (reify ac) ≤ a)
               × All (λ v → depᵗ η 0 (reify v) ≤ a) vs
               × (a + length vs * Rate η fn < r))

private
  -- a payload read under a figure the rank exceeds, which is the shape
  -- every length-carrying bound arrives in: the climb is stated through
  -- `reify` because the fold's own induction has to be, and a value
  -- never reads deeper than its reification
  handed-reify : ∀ {n} {Γ : Ctx n} {U r sz} (η : Fin n → ℕ) (u : Ty)
                 (vs : List (Val Γ u)) (a : ℕ) → a < r
               → All (λ v → depᵗ η 0 (reify v) ≤ a) vs
               → HandedOK η vs (U , r , sz)
  handed-reify η u []       a lt []ᵃ       = []ᵃ
  handed-reify η u (v ∷ vs) a lt (p ∷ᵃ ps) =
      valOK-reify η u v (≤-trans p (<⇒≤ lt))
    ∷ᵃ handed-reify η u vs a lt ps

-- AND THE FOLD'S ARM IS A BODY OVER THAT LEAF, ON THE MAP ARM'S OWN
-- PATTERN.  `scan-climbs` performs the iteration -- every output is one
-- of the accumulators the fold wrote, and each sits one RATE above the
-- last -- so what a delivery costs is discharged here and no longer
-- asserted.  What the leaf keeps is the reservation, and it is the
-- first statement in this tier to name the burst's LENGTH: the rank has
-- to have been entered high enough to pay a rate per delivery, and
-- `entryTri` reads a figure off the program, which has no length in it.
scan-handed : ∀ {n} {Γ : Ctx n} {s u} {U q sz U′ r sz′} (η : Fin n → ℕ)
  (fn : Fn Γ [] [] [] (u ×ᵗ s) u) (ac : Val Γ u) (vs : List (Val Γ s))
  {outs : List (Val Γ u)} {ac′ : Val Γ u} →
  depᵗ η q fn ≤ r → HandedOK η vs (U , q , sz) →
  scanVals fn ac vs ≡ (outs , ac′) → HandedOK η outs (U′ , r , sz′)
scan-handed {u = u} η fn ac vs le ps eq
  with scan-fits η fn ac vs le ps
... | a , ac≤ , vs≤ , fits rewrite sym (cong proj₁ eq) =
  handed-reify η u _ _ fits (scan-climbs η fn ac vs a ac≤ vs≤)

-- AND THE TWO HEADS THAT LEAVE THIS MODULE.  An `*All` frame does not
-- rewrite a payload: it SUBSCRIBES one, or it delivers what an inner
-- subscription produced — so what is owed is the same claim about
-- another family's run, and the rank it has to be made at is the one
-- that family entered at rather than this frame's.
--
-- PROBED: `Probed.Frame-Heads` — the inner head at the pass-through arm
--   and at the completion side reaching no node, over a payload of two;
--   the thru head at the empty walk and at a walk of one over each of
--   the three ops, with the input an observable read strictly under the
--   rank and the wrap's flag both ways.  Not reached, and it is where
--   either could fail: every arm that MINTS a value, since each one
--   runs a subscription — so no row here has a conclusion its own
--   hypothesis did not already carry.
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
step-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τᵢ τ : Tri}
  (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u}
  {κ : Path Γ lo u t} {vs : List (Val Γ s)} {c : Bool}
  {sched : Sched Γ} {st : EvalSt e}
  {vals : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))} {fin : Bool}
  {sched′ : Sched Γ} {st′ : EvalSt e} →
  FrameOK η fr τᵢ τ → HandedOK η vs τᵢ →
  stepFrame⇓ {e = e} id now fr κ vs c sched st
    (vals , evs , fin , sched′ , st′) →
  HandedOK η vals τ
step-handed {τᵢ = _ , _ , _} {_ , _ , _} η {fr = map-f fn} le ps step-map =
  map-handed η fn _ le ps
step-handed {τᵢ = _ , _ , _} {_ , _ , _} η {fr = scan-f fn nid} le ps
            (step-scan _ eq) =
  scan-handed η fn _ _ le ps eq
step-handed η le ps step-scan-nil = []ᵃ
step-handed {τᵢ = _ , _ , _} {_ , _ , _} η {fr = take-f nid} le ps
             (step-take {vals = vs} {fin = fin} {sched = sched} {st = st}) =
  handed-mono η _ le
    (take-arm η nid vs fin sched st (lookupNode nid (EvalSt.nodes st)) ps)
step-handed {τᵢ = _ , _ , _} {_ , _ , _} η {fr = from-inner _ _ _} le ps
            (step-from-inner r) =
  handed-mono η _ le (inner-handed η ps r)
step-handed {e = e} {τᵢ = Uᵢ , q , szᵢ} {U , r , sz} η
            {fr = thru-outer op nid}
            {κ = κ} {sched = sched} {st = st} le ps
            (step-thru-outer {id = id} {now = now} {vals = vals} {fin = fin}
                             {vs = vs} {bs = bs}
                             {sched′ = sched′} {st′ = st′} w) =
  handed-mono η {Uᵢ} {q} {szᵢ} {U} {r} {sz}
    (proj₁ (thruWrap {e = e} op nid fin (vs , bs , sched′ , st′)))
    le
    (thru-handed {τ = Uᵢ , q , szᵢ} η {op = op} {nid = nid} {κ = κ}
       {id = id} {now = now} {vs = vals} {sched = sched} {st = st}
       fin (vs , bs , sched′ , st′) ps w)

push-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τᵢ τ : Tri}
  (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
  {bs : Stream Γ s} {sched : Sched Γ} {st : EvalSt e}
  {burst : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} →
  FrameOK η fr τᵢ τ → BurstOK η bs τᵢ →
  pushBurst⇓ {e = e} id now fr κ bs sched st (burst , sched′ , st′) →
  BurstOK η burst τ
push-carries η fok ok push-nil = []ᵃ
push-carries {u = u} {τᵢ = τᵢ} {τ = τ} η fok (okem ∷ᵃ okrest)
             (push-cons {em = em} {evs = evs} {fin′ = fin′} sp step rest) =
    ++⁺ (subst (All (EventOK η τ))
               (cong (λ z → proj₁ (proj₂ z)) sp)
               (split-book {u = u} η (InstEmit.events em)))
        (++⁺ (retag-book η evs)
             (++⁺ (handed-events η _
                     (step-handed η fok
                       (subst (λ ws → HandedOK η ws τᵢ) (cong proj₁ sp)
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
 all-carries {τ = U , r , sz} sl ok (sub-all _ d p) =
   push-carries {τᵢ = U , r , sz} _ ≤-refl (burst-carries sl ok d) p

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
 burst-carries {τ = U , r , sz} sl (_ , dep) (subs-of eq) =
   oneshot-ok _ (U , r , sz) _ _ _ eq (of-handed (slotDepth sl) _ dep)
 burst-carries {τ = τ} sl ok (subs-cold-sync {ok = okd} _ _ eq) =
   oneshot-ok _ τ _ _ _ eq (data-handed _ τ _ okd)
 burst-carries {τ = τ} sl ok (subs-cold-async {ok = okd} _ _ _ _) =
   anchored-ok _ τ _ _ _ (data-handed _ τ _ okd)
 burst-carries {τ = U , r , sz} sl ok (subs-map {f = f} {b = b} d p) =
   push-carries {τᵢ = U , bindᵃᵉ (slotDepth sl) 0 b , sz}
     _ (≤-trans (m≤m⊔n (depᵗ (slotDepth sl) (bindᵃᵉ (slotDepth sl) 0 b) f)
                       (depᵉ (slotDepth sl) 0 b))
                (proj₂ ok))
     (burst-carries sl
       (entry-inner (proj₁ ok) , m≤m⊔n (depᵉ (slotDepth sl) 0 b) 0) d) p
 burst-carries sl ok (subs-merge-all a)   = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-switch-all a)  = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-exhaust-all a) = all-carries sl (under-ok ok) a
 burst-carries sl (sz≤ , r≤) (subs-μ {body = body} d) =
   burst-carries sl
     ( ≤-trans (<⇒≤ (unfoldμ-shrinks body)) sz≤
     , μ-entry (slotDepth sl) body r≤ ) d
 burst-carries {τ = U , r , sz} sl ok (subs-take-suc _ _ d p) =
   push-carries {τᵢ = U , r , sz} _ ≤-refl
     (burst-carries sl (inner-ok ok) d) p
 burst-carries {τ = U , r , sz} sl ok
               (subs-scan {f = f} {seed = seed} {b = b} _ d p) =
   push-carries {τᵢ = U , bindˢᵗ (slotDepth sl) 0 seed b , sz}
     _ (≤-trans (m≤m⊔n (depᵗ (slotDepth sl) (bindˢᵗ (slotDepth sl) 0 seed b) f)
                       (depᵗ (slotDepth sl) 0 seed))
                (≤-trans (m≤m⊔n (depᵗ (slotDepth sl)
                                   (bindˢᵗ (slotDepth sl) 0 seed b) f
                                 ⊔ depᵗ (slotDepth sl) 0 seed)
                                (depᵉ (slotDepth sl) 0 b))
                         (proj₂ ok)))
     (burst-carries sl
       (entry-inner (proj₁ ok)
       , ≤-trans (m≤m⊔n (depᵉ (slotDepth sl) 0 b) 0)
                 (m≤m⊔n (bindᵃᵉ (slotDepth sl) 0 b)
                        (depᵗ (slotDepth sl) 0 seed))) d) p
