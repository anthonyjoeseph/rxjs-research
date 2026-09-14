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
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; <⇒≤; m≤m⊔n; m≤n⊔m)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Data.Vec using (lookup)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)

open import Rx.Prim using (Id; Source; Tick; InstEvent; InstEmit; init; value; close;
  handoff; complete; exhausted; subscribe; _at_from_as_)
open import Rx.Exp using (Ty; Ctx; Closed; Val; Tm; unitᵗ; boolᵗ; natᵗ; _×ᵗ_; _+ᵗ_;
  obs; input; isData; evalTm)
open import Rx.Obs-Depth using (depᵗ; depᵗˢ; depᵛ)
open import Rx.Obs-Depth.Substitution using ([]ᵈ; ≤pred⇒<; dep-eval-strict)
open import Rx.Slots using (Slots)
open import Rx.Slot-Depth using (slotDepth)
open import Rx.Strat-Order using (Tri)
open import Rx.Sync-Size using (unfoldμ-shrinks)
open import Rx.Evaluator using (Stream; Sched; EvalSt; Path; Frame; oneShotBurst;
  spentBurst; splitEvents; retagEvents)
open import Rx.Evaluator.Domain using (subscribeE⇓; subscribeAll⇓; pushBurst⇓;
  subscribeSharedSlot⇓; stepFrame⇓; push-nil; push-cons;
  subs-floor; subs-shared; subs-hot-done; subs-hot-live; subs-cold-sync;
  subs-cold-async; subs-of; subs-empty; subs-map; subs-take-zero;
  subs-take-suc; subs-scan; subs-merge-all; subs-switch-all;
  subs-exhaust-all; subs-μ; subs-defer; sub-all)
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
-- NOUGHT.  A closed term reading nothing wrote no `strmᵗ`, and the only
-- other way to hold an observable is to read one from a binder — of
-- which a closed term has none.  So its value carries no observable at
-- all and the predicate holds at EVERY rank, the rank nought included,
-- which is the one case the drop cannot reach: there is nothing to drop
-- below.  It is a leaf because the induction saying so is over the type
-- and the term together, the same split `dep-fn-pos` names.
--
-- PROBED: `Probed.Burst-Handed` — at a flat payload, and at a sum whose
--   other arm is an observable, which is the shape that could fail it:
--   the TYPE reaches an observable while the value takes the other arm,
--   so the reading has to select on the injection rather than on the
--   type.  NOT reached: a silent term at a binding head, since a closed
--   term has no binder to read.
postulate
  eval-silent : ∀ {n} {Γ : Ctx n} {u} {τ : Tri} (η : Fin n → ℕ)
                (tm : Tm Γ [] [] [] u)
              → depᵗ η tm ≡ 0 → ValOK η u τ (evalTm tm)

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

  -- one element: the term's own reading bounds its value's, strictly
  -- wherever there is anything to be strict about
  handed-one : ∀ {n} {Γ : Ctx n} {u} {U r sz} (η : Fin n → ℕ)
               (tm : Tm Γ [] [] [] u) → depᵗ η tm ≤ r
             → ValOK η u (U , r , sz) (evalTm tm)
  handed-one {u = u} η tm le with depᵗ η tm in eq
  ... | zero  = eval-silent η tm eq
  ... | suc k = valOK-below η u (evalTm tm)
                  (≤-trans (≤pred⇒< (subst (0 <_) (sym eq) (s≤s z≤n))
                                    (dep-eval-strict η []ᵈ tm []ᵃ))
                           (subst (_≤ _) (sym eq) le))

of-handed : ∀ {n} {Γ : Ctx n} {u} {U r sz} (η : Fin n → ℕ)
            (ts : List (Tm Γ [] [] [] u))
          → depᵗˢ η ts ≤ r
          → HandedOK η (map (λ tm → evalTm tm) ts) (U , r , sz)
of-handed η []        dep = []ᵃ
of-handed η (tm ∷ ts) dep =
    handed-one η tm (≤-trans (m≤m⊔n (depᵗ η tm) (depᵗˢ η ts)) dep)
  ∷ᵃ of-handed η ts (≤-trans (m≤n⊔m (depᵗ η tm) (depᵗˢ η ts)) dep)

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

-- WHAT THE FRAME WROTE, WHICH IS THE ONE SEGMENT AT RISK.  A step is
-- handed the emit's own values and returns the values it delivers
-- onward, and the six heads it can take do genuinely different things:
-- one returns nothing, one filters what it was given, two REWRITE the
-- payload through a template, and two follow the run into another
-- family.  So this is where the claim has to be split next, and the
-- split is what the arms below say it is.
--
-- AND IT IS FALSE AT TWO OF THOSE HEADS, WHICH IS THE CYCLE'S OWN
-- FINDING LOCALISED RATHER THAN A NEW ONE.  The map arm is
-- `map (applyFn fn) vals`, and `applyFn` is
-- `evalWith` at a one-value environment, so what bounds its reading is
-- `dep-eval-open`: `depᵗ fn + m`, a SUM.  The measure the entry
-- invariant is denominated in reads a map as `depᵗ f ⊔ depᵉ e`, a JOIN.
-- So a frame whose body wraps its own argument under a stream
-- constructor hands back a value deeper than either side, and no
-- premise bounding the FRAME can close the gap -- the argument is the
-- other addend.
--
-- AND THE DATA RESTRICTION IS NOT AVAILABLE, WHICH IS WHAT MAKES THIS
-- THE MEASURE'S FINDING RATHER THAN THIS STATEMENT'S.  Every statement
-- of the substitution shelf carries `isData s ≡ true`, and that is why:
-- at a data argument the environment reads nought, the sum collapses
-- onto `depᵗ fn`, and the join is exact.  But the map constructor is
-- typed at an ARBITRARY payload, so a map over a stream of streams is
-- ordinary syntax and an ordinary rxjs pipeline, and restricting this
-- arm to data would be restricting the language rather than the lemma.
-- What is left is that the measure's own map clause under-counts: it
-- JOINS where the run ADDS, and the gap is unbounded rather than off by
-- one.  Repairing it is a change to the reading every tier is
-- denominated in, which is why it is not made in passing.
--
-- REFUTED: `Refuted.Template-Passes` — the same crossing at the shelf's
--   own statement, which is where it was found first: a template that
--   merely passes its argument through reifies it under a `strmᵗ` the
--   template never wrote, so the emission is as deep as whatever was
--   handed in.  Its rows are the witness for this arm too, since the
--   quantity that fails here is the one it reads.
--
-- DEAD ROUTE: bounding the output rank instead of restricting the
--   payload -- state the cycle as carrying `τ` in and a larger `τ` out.
--   It is STRUCTURALLY DEAD at the walk above rather than here: the
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
postulate
  step-handed : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
    (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u}
    {κ : Path Γ lo u t} {vs : List (Val Γ s)} {c : Bool}
    {sched : Sched Γ} {st : EvalSt e}
    {vals : List (Val Γ u)} {evs : List (InstEvent (Val Γ t))} {fin : Bool}
    {sched′ : Sched Γ} {st′ : EvalSt e} →
    HandedOK η vs τ →
    stepFrame⇓ {e = e} id now fr κ vs c sched st
      (vals , evs , fin , sched′ , st′) →
    HandedOK η vals τ

push-carries : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} {s u lo} {τ : Tri}
  (η : Fin n → ℕ) {id : Id} {now : Tick} {fr : Frame Γ s u} {κ : Path Γ lo u t}
  {bs : Stream Γ s} {sched : Sched Γ} {st : EvalSt e}
  {burst : Stream Γ u} {sched′ : Sched Γ} {st′ : EvalSt e} →
  BurstOK η bs τ →
  pushBurst⇓ {e = e} id now fr κ bs sched st (burst , sched′ , st′) →
  BurstOK η burst τ
push-carries η ok push-nil = []ᵃ
push-carries {u = u} {τ = τ} η (okem ∷ᵃ okrest)
             (push-cons {em = em} {evs = evs} {fin′ = fin′} sp step rest) =
    ++⁺ (subst (All (EventOK η τ))
               (cong (λ z → proj₁ (proj₂ z)) sp)
               (split-book {u = u} η (InstEmit.events em)))
        (++⁺ (retag-book η evs)
             (++⁺ (handed-events η _
                     (step-handed η
                       (subst (λ ws → HandedOK η ws τ) (cong proj₁ sp)
                              (split-handed η (InstEmit.events em) okem))
                       step))
                  (fin-events η fin′)))
  ∷ᵃ push-carries η okrest rest

-- AND THE ONE FAMILY THIS MODULE DOES NOT WALK: the shared slot, whose
-- connect re-enters the subscribe at the SLOT'S own reading rather than
-- at the caller's, and so needs the two schedules' tables related where
-- this walk carries only the one the caller fixed.  That is the same
-- relating the queued observable needs, which is why the arm is a leaf
-- rather than a clause and why it is where the record's field is owed.
--
-- REFUTED: `Refuted.Carried-Derived` — the reading with no environment
--   at all, at that run.  It is this arm the witness stands at: a
--   reference is one symbol standing for a definition of any nesting, so
--   a reading that prices the SYMBOL promises less than the connect
--   delivers.
postulate
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
 all-carries sl ok (sub-all _ d p) = push-carries _ (burst-carries sl ok d) p

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
 burst-carries sl ok (subs-map d p) =
   push-carries _ (burst-carries sl (inner-ok ok) d) p
 burst-carries sl ok (subs-merge-all a)   = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-switch-all a)  = all-carries sl (under-ok ok) a
 burst-carries sl ok (subs-exhaust-all a) = all-carries sl (under-ok ok) a
 burst-carries sl (sz≤ , r≤) (subs-μ {body = body} d) =
   burst-carries sl
     ( ≤-trans (<⇒≤ (unfoldμ-shrinks body)) sz≤
     , μ-entry (slotDepth sl) body r≤ ) d
 burst-carries sl ok (subs-take-suc _ _ d p) =
   push-carries _ (burst-carries sl (inner-ok ok) d) p
 burst-carries sl ok (subs-scan _ d p) =
   push-carries _ (burst-carries sl (inner-ok ok) d) p
