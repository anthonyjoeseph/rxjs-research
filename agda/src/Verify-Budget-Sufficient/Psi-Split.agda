------------------------------------------------------------------
-- THE Ψ LEDGER AND ITS ZIPS — the fnCap halves of the walk's own
-- bound predicates, split out so the size halves can ride the LEVEL
-- while the Ψ halves ride the walk CONSTANT.
--
-- WHY THIS IS ITS OWN MODULE, AND IT IS A PLACEMENT FACT RATHER THAN
-- A MATHEMATICAL ONE.  Every ingredient here is a bound predicate or
-- an `all`-zip from the measures and the size face; nothing in the
-- file knows anything about a walk, a cascade or a subscribe.  What
-- forces the module is the CONSUMER set: both the level-walk face and
-- the wet/nodry face need these zips, and the level walk is UPSTREAM
-- of the wet one, so the lowest module reaching both is neither of
-- them.  The apparatus has now moved twice for exactly this reason —
-- first out of the bridge module when its consumer turned out to sit
-- below it, and now out of the burst face for the same reason one
-- level further down.  Sited here it cannot happen a third time: this
-- module imports only the measures and the size face, which is as far
-- down as the ingredients go.
--
-- THE SHAPE, and it is the whole design.  Each combined predicate is
-- a conjunction of a B-indexed conjunct and a Ψ-indexed one.  The
-- Ψ-indexed conjunct MENTIONS NO LEVEL, so it needs no reconciliation
-- when a subscribe reports growth: it is carried across the level
-- change untouched, and the B-indexed half is re-supplied at the new
-- level from the size receipt the caps face already produced.  That
-- is what `INV?-reindex` and `burstB?-reindex` below do, and it is why
-- a walk-face statement can take its caps receipts as hypotheses at
-- the caller's level and still conclude the wet facts there.
------------------------------------------------------------------

module Verify-Budget-Sufficient.Psi-Split where

open import Data.Bool    using (Bool; true; false; T; if_then_else_; _∧_; _∨_; not)
open import Data.Nat     using (ℕ; zero; suc; pred; _+_; _*_; _^_; _≤_; s≤s; _≤ᵇ_; _≡ᵇ_; _⊔_)
open import Data.Nat.Properties
  using (≤-trans; ≤-refl; ≤-reflexive; *-identityʳ; ≤⇒≤ᵇ; ≤ᵇ⇒≤; m≤m+n; m≤n+m; m≤n⊔m;
         m≤m⊔n; n≤1+n)
open import Data.List    using (List; []; _∷_; _++_; map; length)
open import Data.Bool.ListAction using (all; any)
open import Data.Maybe   using (Maybe; just; nothing)
open import Data.Unit    using (⊤; tt)
open import Data.List.Relation.Unary.All using (All)
  renaming ([] to []ᵃ; _∷_ to _∷ᵃ_)
open import Relation.Nullary using (yes; no)
open import Data.Fin     using (Fin; toℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import Rx.Prim using (Gas; gs; g0; Id; Tick; Source; InstEvent;
                           value; init; close; handoff; complete;
                           CloseReason; cut; cutPending; exhausted; dried;
                           gasPad; gasTower; towerℕ;
                           InstEmit; _at_from_as_; EmitKind; delivery)
open import Rx.Exp  using (Ty; Ctx; Closed; Val; obs; Fn; applyFn; _×ᵗ_; _≟ᵗ_; sizeᵉ; syncSizeᵉ;
                          sizeᵗ; sizeᵛ)
open import Rx.Evaluator
open import Verify-Budget-Sufficient.Caps-Face

valΨ? : ∀ {n} {Γ : Ctx n} → ℕ → (u : Ty) → Val Γ u → Bool
valΨ? Ψ u v = fnCapᵛ u v ≤ᵇ Ψ

valsΨ? : ∀ {n} {Γ : Ctx n} {s} → ℕ → List (Val Γ s) → Bool
valsΨ? {s = s} Ψ = all (valΨ? Ψ s)

eventΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → InstEvent (Val Γ u) → Bool
eventΨ? {u = u} Ψ (value v) = valΨ? Ψ u v
eventΨ? Ψ (init _)    = true
eventΨ? Ψ (close _ _) = true
eventΨ? Ψ (handoff _) = true
eventΨ? Ψ complete    = true

eventsΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → List (InstEvent (Val Γ u)) → Bool
eventsΨ? Ψ = all (eventΨ? Ψ)

burstΨ? : ∀ {n} {Γ : Ctx n} {u} → ℕ → Stream Γ u → Bool
burstΨ? Ψ = all (λ em → all (eventΨ? Ψ) (InstEmit.events em))

frameBΨ? : ∀ {n} {Γ : Ctx n} {s u} → ℕ → Frame Γ s u → Bool
frameBΨ? Ψ (map-f fn)         = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (scan-f fn _)      = (caseWᵗ fn ⊔ fnCapᵗ fn) ≤ᵇ Ψ
frameBΨ? Ψ (take-f _)         = true
frameBΨ? Ψ (from-inner _ _ _) = true
frameBΨ? Ψ (thru-outer _ _)   = true

pathBΨ? : ∀ {n} {Γ : Ctx n} {s t} → ℕ → Path Γ s t → Bool
pathBΨ? Ψ root           = true
pathBΨ? Ψ (share-sink i) = true
pathBΨ? Ψ (f ↠ p)        = frameBΨ? Ψ f ∧ pathBΨ? Ψ p

regsBΨ? : ∀ {n} {Γ : Ctx n} {t} → ℕ
        → List (RegId × Source × Chain Γ t) → Bool
regsBΨ? Ψ = all (λ en → pathBΨ? Ψ (proj₂ (proj₂ (proj₂ en))))

------------------------------------------------------------------

------------------------------------------------------------------
-- THE RECOMBINATION LEMMAS (the INJECTIONS).  The size-only half from
-- the caps face plus the Ψ-only half directly above reunite into the
-- real combined predicate that the invariant reads — one ∧-intro per
-- clause.  Note that the path's size predicate carries a LENGTH
-- conjunct the combined one does not, so the zip discards it.
------------------------------------------------------------------

frameB?-of-parts : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B Ψ : ℕ} →
  frameSz? B f ≡ true → frameBΨ? Ψ f ≡ true → frameB? B Ψ f ≡ true
frameB?-of-parts (map-f fn)         hb hΨ = ∧-intro hb hΨ
frameB?-of-parts (scan-f fn _)      hb hΨ = ∧-intro hb hΨ
frameB?-of-parts (take-f _)         hb hΨ = refl
frameB?-of-parts (from-inner _ _ _) hb hΨ = refl
frameB?-of-parts (thru-outer _ _)   hb hΨ = refl

pathB?-of-parts : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) {B Ψ : ℕ} →
  pathSz? B p ≡ true → pathBΨ? Ψ p ≡ true → pathB? B Ψ p ≡ true
pathB?-of-parts root           hsz hΨ = refl
pathB?-of-parts (share-sink i) hsz hΨ = refl
pathB?-of-parts (f ↠ p) {B} {Ψ} hsz hΨ
  with ∧-true (frameSz? B f) _ hsz
... | hf , hrest with ∧-true (suc (pathLen p) ≤ᵇ B) (pathSz? B p) hrest
... | _ , hp with ∧-true (frameBΨ? Ψ f) (pathBΨ? Ψ p) hΨ
... | hfΨ , hpΨ = ∧-intro (frameB?-of-parts f hf hfΨ) (pathB?-of-parts p hp hpΨ)

regsB?-of-parts : ∀ {n} {Γ : Ctx n} {t}
  (rs : List (RegId × Source × Chain Γ t)) {B Ψ : ℕ} →
  regsSz? B rs ≡ true → regsBΨ? Ψ rs ≡ true → regsB? B Ψ rs ≡ true
regsB?-of-parts rs hsz hΨ =
  all-zip _ _ _ (λ en psz pΨ → pathB?-of-parts (proj₂ (proj₂ (proj₂ en))) psz pΨ)
                rs hsz hΨ

------------------------------------------------------------------
-- THE SAME ZIP FOR EVENTS AND BURSTS.  The two flavours ARE the
-- combined event/burst predicate at the caps' own size, pointwise.
------------------------------------------------------------------

eventB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (ev : InstEvent (Val Γ u)) →
  eventCaps? c′ sl ev ≡ true → eventΨ? Ψ ev ≡ true →
  eventB? (Caps.cSize c′) Ψ ev ≡ true
eventB?-halves c′ sl Ψ (value v) hc hp = ∧-intro (proj₁ (∧-true _ _ hc)) hp
eventB?-halves c′ sl Ψ (init _)    _ _ = refl
eventB?-halves c′ sl Ψ (close _ _) _ _ = refl
eventB?-halves c′ sl Ψ (handoff _) _ _ = refl
eventB?-halves c′ sl Ψ complete    _ _ = refl

eventsB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (es : List (InstEvent (Val Γ u))) →
  all (eventCaps? c′ sl) es ≡ true → eventsΨ? Ψ es ≡ true →
  all (eventB? (Caps.cSize c′) Ψ) es ≡ true
eventsB?-halves c′ sl Ψ []       _  _  = refl
eventsB?-halves c′ sl Ψ (e ∷ es) hc hp =
  ∧-intro (eventB?-halves c′ sl Ψ e (proj₁ (∧-true _ _ hc)) (proj₁ (∧-true _ _ hp)))
          (eventsB?-halves c′ sl Ψ es (proj₂ (∧-true _ _ hc)) (proj₂ (∧-true _ _ hp)))

burstB?-halves : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ) (Ψ : ℕ)
  (str : Stream Γ u) →
  burstCaps? c′ sl str ≡ true → burstΨ? Ψ str ≡ true →
  burstB? (Caps.cSize c′) Ψ str ≡ true
burstB?-halves c′ sl Ψ []         _  _  = refl
burstB?-halves c′ sl Ψ (em ∷ ems) hc hp =
  ∧-intro (eventsB?-halves c′ sl Ψ (InstEmit.events em)
            (proj₁ (∧-true _ _ hc)) (proj₁ (∧-true _ _ hp)))
          (burstB?-halves c′ sl Ψ ems (proj₂ (∧-true _ _ hc)) (proj₂ (∧-true _ _ hp)))

------------------------------------------------------------------
-- THE LEDGER GLUE (regP?-∧ / chP?-∧) — pointwise conjunctions over the registry and
-- chain lists, so the caller supplies the two flavours separately.
------------------------------------------------------------------

------------------------------------------------------------------
-- THE LEDGER GLUE — pointwise conjunctions over the registry and
-- chain lists, so the caller supplies the two flavours separately.
------------------------------------------------------------------

regP?-∧ : ∀ {n} {Γ : Ctx n} {t} (P Q : ∀ {u} → Path Γ u t → Bool)
  (rs : List (RegId × Source × Chain Γ t)) →
  regP? P rs ≡ true → regP? Q rs ≡ true →
  regP? (λ {v} p → P {v} p ∧ Q p) rs ≡ true
regP?-∧ P Q []       h₁ h₂ = refl
regP?-∧ P Q (r ∷ rs) h₁ h₂
  with ∧-true (P (proj₂ (proj₂ (proj₂ r)))) (regP? P rs) h₁
     | ∧-true (Q (proj₂ (proj₂ (proj₂ r)))) (regP? Q rs) h₂
... | a₁ , b₁ | a₂ , b₂ = ∧-intro (∧-intro a₁ a₂) (regP?-∧ P Q rs b₁ b₂)

chP?-∧ : ∀ {n} {Γ : Ctx n} {s t} (P Q : ∀ {u} → Path Γ u t → Bool)
  (ps : List (RegId × Path Γ s t)) →
  chP? P ps ≡ true → chP? Q ps ≡ true →
  chP? (λ {v} p → P {v} p ∧ Q p) ps ≡ true
chP?-∧ P Q []       h₁ h₂ = refl
chP?-∧ P Q (r ∷ rs) h₁ h₂
  with ∧-true (P (proj₂ r)) (chP? P rs) h₁
     | ∧-true (Q (proj₂ r)) (chP? Q rs) h₂
... | a₁ , b₁ | a₂ , b₂ = ∧-intro (∧-intro a₁ a₂) (chP?-∧ P Q rs b₁ b₂)

------------------------------------------------------------------
-- THE PROJECTIONS — the other direction, and the half that makes
-- re-indexing possible at all.  A combined receipt at ANY level
-- yields the Ψ half, because the Ψ half does not mention the level;
-- so a level change is discharged by projecting out the Ψ half and
-- zipping it back against a size receipt at the new level.  The
-- injections above are the zip; these are the split.
------------------------------------------------------------------

frameBΨ?-of : ∀ {n} {Γ : Ctx n} {s u} (f : Frame Γ s u) {B Ψ : ℕ} →
  frameB? B Ψ f ≡ true → frameBΨ? Ψ f ≡ true
frameBΨ?-of (map-f fn)         h = proj₂ (∧-true _ _ h)
frameBΨ?-of (scan-f fn _)      h = proj₂ (∧-true _ _ h)
frameBΨ?-of (take-f _)         h = refl
frameBΨ?-of (from-inner _ _ _) h = refl
frameBΨ?-of (thru-outer _ _)   h = refl

pathBΨ?-of : ∀ {n} {Γ : Ctx n} {s t} (p : Path Γ s t) {B Ψ : ℕ} →
  pathB? B Ψ p ≡ true → pathBΨ? Ψ p ≡ true
pathBΨ?-of root           h = refl
pathBΨ?-of (share-sink i) h = refl
pathBΨ?-of (f ↠ p) {B} {Ψ} h
  with ∧-true (frameB? B Ψ f) (pathB? B Ψ p) h
... | hf , hp = ∧-intro (frameBΨ?-of f hf) (pathBΨ?-of p hp)

regsBΨ?-of : ∀ {n} {Γ : Ctx n} {t}
  (rs : List (RegId × Source × Chain Γ t)) {B Ψ : ℕ} →
  regsB? B Ψ rs ≡ true → regsBΨ? Ψ rs ≡ true
regsBΨ?-of rs h =
  all-impl _ _ (λ en → pathBΨ?-of (proj₂ (proj₂ (proj₂ en)))) rs h

eventΨ?-of : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (ev : InstEvent (Val Γ u)) →
  eventB? B Ψ ev ≡ true → eventΨ? Ψ ev ≡ true
eventΨ?-of {u = u} B Ψ (value v)   h = proj₂ (∧-true (sizeᵛ u v ≤ᵇ B) _ h)
eventΨ?-of B Ψ (init _)    h = refl
eventΨ?-of B Ψ (close _ _) h = refl
eventΨ?-of B Ψ (handoff _) h = refl
eventΨ?-of B Ψ complete    h = refl

eventsΨ?-of : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ)
  (es : List (InstEvent (Val Γ u))) →
  all (eventB? B Ψ) es ≡ true → eventsΨ? Ψ es ≡ true
eventsΨ?-of B Ψ []       h = refl
eventsΨ?-of B Ψ (e ∷ es) h =
  ∧-intro (eventΨ?-of B Ψ e (proj₁ (∧-true _ _ h)))
          (eventsΨ?-of B Ψ es (proj₂ (∧-true _ _ h)))

burstΨ?-of : ∀ {n} {Γ : Ctx n} {u} (B Ψ : ℕ) (str : Stream Γ u) →
  burstB? B Ψ str ≡ true → burstΨ? Ψ str ≡ true
burstΨ?-of B Ψ []         h = refl
burstΨ?-of B Ψ (em ∷ ems) h =
  ∧-intro (eventsΨ?-of B Ψ (InstEmit.events em) (proj₁ (∧-true _ _ h)))
          (burstΨ?-of B Ψ ems (proj₂ (∧-true _ _ h)))

------------------------------------------------------------------
-- RE-INDEXING — the two composites the level walk spends, each a
-- projection followed by the matching zip.
--
-- THIS IS WHAT A LEVEL CHANGE COSTS, and the point is that it costs
-- only a SIZE receipt.  A face that reports growth hands back its
-- caps receipt at the new level; the wet facts arrive from the
-- recursive call at the OLD one; and these two lemmas are the whole
-- reconciliation.  Nothing here is a widening — the new level's
-- bound need not dominate the old one, because the size half is not
-- transported at all but re-supplied.
------------------------------------------------------------------

burstB?-reindex : ∀ {n} {Γ : Ctx n} {u} (c′ : Caps) (sl : Slots Γ)
  (B Ψ : ℕ) (str : Stream Γ u) →
  burstB? B Ψ str ≡ true → burstCaps? c′ sl str ≡ true →
  burstB? (Caps.cSize c′) Ψ str ≡ true
burstB?-reindex c′ sl B Ψ str hb hc =
  burstB?-halves c′ sl Ψ str hc (burstΨ?-of B Ψ str hb)

INV?-of-parts : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  stBounded? B sched st ≡ true →
  fnCapBounded? Ψ sched st ≡ true →
  (length (EvalSt.registry st) ≤ᵇ B) ≡ true →
  regsB? B Ψ (EvalSt.registry st) ≡ true →
  (slotsSize (Sched.slots sched) ≤ᵇ B) ≡ true →
  (slotsFnCap (Sched.slots sched) ≤ᵇ Ψ) ≡ true →
  INV? Ψ B sched st ≡ true
INV?-of-parts Ψ B sched st h₁ h₂ h₃ h₄ h₅ h₆ =
  ∧-intro h₁ (∧-intro h₂ (∧-intro h₃ (∧-intro h₄ (∧-intro h₅ h₆))))

INV?-reindex : ∀ {n} {Γ : Ctx n} {t} {e : Closed Γ t} (Ψ B B′ : ℕ)
  (sched : Sched Γ) (st : EvalSt e) →
  INV? Ψ B sched st ≡ true →
  stBounded? B′ sched st ≡ true →
  (length (EvalSt.registry st) ≤ᵇ B′) ≡ true →
  regsSz? B′ (EvalSt.registry st) ≡ true →
  (slotsSize (Sched.slots sched) ≤ᵇ B′) ≡ true →
  INV? Ψ B′ sched st ≡ true
INV?-reindex Ψ B B′ sched st inv hsb hrl hrsz hss
  with INV-parts Ψ B sched st inv
... | _ , hfc , _ , hregs , _ , hsfc =
  INV?-of-parts Ψ B′ sched st hsb hfc hrl
    (regsB?-of-parts (EvalSt.registry st) hrsz
      (regsBΨ?-of (EvalSt.registry st) hregs))
    hss hsfc

------------------------------------------------------------------
-- THE PER-EMIT PLUMBING, Ψ FLAVOUR — the `all`-facts a wet push face's
-- cons clause needs about `pushBurst`'s emit shape (back events ++
-- retagged step events ++ mapped values ++ an optional terminator),
-- stated at the Ψ predicate above.  The B and hop flavours of the same
-- family sit with the push faces that spend them; these sit HERE, with
-- the predicate, because two faces need them at once — the level walk's
-- map push and the burst face's inner walk — and this module is below
-- both.
--
-- Two of the four are UNCONDITIONAL, and that is a fact about the
-- reassembly rather than about Ψ: splitEvents puts only bookkeeping in
-- its back list, and a terminator carries no value.  There is no
-- RETAG flavour here, and that is deliberate: map's stepFrame emits
-- `[]` literally, so its retag layer reduces away and never needs a
-- lemma; scan's is the first face that will, and it can be written
-- then rather than parked here now.
------------------------------------------------------------------

splitEvents-vals-Ψ : ∀ {n} {Γ : Ctx n} {u} {A : Set} (Ψ : ℕ)
  (events : List (InstEvent (Val Γ u))) →
  all (eventΨ? Ψ) events ≡ true →
  valsΨ? Ψ (proj₁ (splitEvents {A = A} events)) ≡ true
splitEvents-vals-Ψ Ψ [] _ = refl
splitEvents-vals-Ψ {u = u} {A = A} Ψ (value v ∷ es) h =
  ∧-intro (proj₁ (∧-true (valΨ? Ψ u v) (all (eventΨ? Ψ) es) h))
          (splitEvents-vals-Ψ {A = A} Ψ es
            (proj₂ (∧-true (valΨ? Ψ u v) (all (eventΨ? Ψ) es) h)))
splitEvents-vals-Ψ {A = A} Ψ (init _ ∷ es) h =
  splitEvents-vals-Ψ {A = A} Ψ es h
splitEvents-vals-Ψ {A = A} Ψ (close _ _ ∷ es) h =
  splitEvents-vals-Ψ {A = A} Ψ es h
splitEvents-vals-Ψ {A = A} Ψ (handoff _ ∷ es) h =
  splitEvents-vals-Ψ {A = A} Ψ es h
splitEvents-vals-Ψ {A = A} Ψ (complete ∷ es) h =
  splitEvents-vals-Ψ {A = A} Ψ es h

splitEvents-bk-Ψ : ∀ {n} {Γ : Ctx n} {u t} (Ψ : ℕ)
  (events : List (InstEvent (Val Γ u))) →
  eventsΨ? {u = t} Ψ (proj₁ (proj₂ (splitEvents {A = Val Γ t} events))) ≡ true
splitEvents-bk-Ψ Ψ [] = refl
splitEvents-bk-Ψ {t = t} Ψ (value _ ∷ es) =
  splitEvents-bk-Ψ {t = t} Ψ es
splitEvents-bk-Ψ {t = t} Ψ (init _ ∷ es) =
  ∧-intro refl (splitEvents-bk-Ψ {t = t} Ψ es)
splitEvents-bk-Ψ {t = t} Ψ (close _ _ ∷ es) =
  ∧-intro refl (splitEvents-bk-Ψ {t = t} Ψ es)
splitEvents-bk-Ψ {t = t} Ψ (handoff _ ∷ es) =
  ∧-intro refl (splitEvents-bk-Ψ {t = t} Ψ es)
splitEvents-bk-Ψ {t = t} Ψ (complete ∷ es) =
  splitEvents-bk-Ψ {t = t} Ψ es

mapValue-Ψ : ∀ {n} {Γ : Ctx n} {u} (Ψ : ℕ) (vs : List (Val Γ u)) →
  valsΨ? Ψ vs ≡ true → all (eventΨ? Ψ) (map value vs) ≡ true
mapValue-Ψ Ψ []       h = refl
mapValue-Ψ {u = u} Ψ (v ∷ vs) h =
  ∧-intro (proj₁ (∧-true (valΨ? Ψ u v) (valsΨ? Ψ vs) h))
          (mapValue-Ψ Ψ vs (proj₂ (∧-true (valΨ? Ψ u v) (valsΨ? Ψ vs) h)))

finList-Ψ : ∀ {n} {Γ : Ctx n} {u} (Ψ : ℕ) (b : Bool) →
  all (eventΨ? {n = n} {Γ = Γ} {u = u} Ψ)
      (if b then complete ∷ [] else []) ≡ true
finList-Ψ Ψ true  = refl
finList-Ψ Ψ false = refl

-- All ↔ all FOR THE Ψ PREDICATE.  The scan ledgers in .Wet are stated
-- over `All` and `_≤_` while every burst predicate here is a `Bool` and
-- `≡ true`, so a face that spends one inside the other crosses this pair
-- twice.  They sit HERE, with the predicate, because two faces need them
-- at once — .Burst-Walk's stepFrame-level scan leaf and the level walk's
-- scan push — and this module is below both.  (.Wet's allB-* pair is the
-- same bridge for `valB?`, which carries the SIZE half alongside; these
-- see only Ψ, which is the whole point of the split.)
allΨ-to : ∀ {n} {Γ : Ctx n} {s} (Ψ : ℕ) (vs : List (Val Γ s)) →
  valsΨ? Ψ vs ≡ true → All (λ v → fnCapᵛ s v ≤ Ψ) vs
allΨ-to Ψ []       h = []ᵃ
allΨ-to Ψ (v ∷ vs) h =
  ≤ᵇ⇒≤ _ _ (T-to (proj₁ (∧-true _ _ h))) ∷ᵃ allΨ-to Ψ vs (proj₂ (∧-true _ _ h))

allΨ-of : ∀ {n} {Γ : Ctx n} {s} (Ψ : ℕ) (vs : List (Val Γ s)) →
  All (λ v → fnCapᵛ s v ≤ Ψ) vs → valsΨ? Ψ vs ≡ true
allΨ-of Ψ []       h          = refl
allΨ-of Ψ (v ∷ vs) (p ∷ᵃ ps) = ∧-intro (T⇒≡true _ (≤⇒≤ᵇ p)) (allΨ-of Ψ vs ps)
