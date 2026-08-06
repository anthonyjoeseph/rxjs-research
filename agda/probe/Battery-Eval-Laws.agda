-- BATTERY-EVAL-LAWS (2026-08-06).  Concrete instance probes for three
-- postulates from Rx.Evaluator-Theorems and Rx.Provenance-Theorems:
--
--   μ-unfold       evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins
--   fuel-coherent  Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)
--   id-inheritance ids (evaluate fuel e ins) ⊆ᵢ horizon fuel
--
-- CLASSIFICATION KEY applied to every row below:
--   LOAD-BEARING: the row exercises the mechanism the claim is about; it
--     could fail if the claim were false at this instance.
--   DEGENERATE: passes trivially (empty list, 0≤n, or program too small
--     to reach the behaviour).  Kept for documentation; a non-degenerate
--     sibling is always added.
--
-- What would make a LOAD-BEARING row fail:
--   μ-unfold: if subscribeE (budgetAt (μᵉ e) ...) and subscribeE
--     (budgetAt (unfoldμ e) ...) produce different outputs because the
--     different cap budgets change when a μᵉ unfolds to g0 vs gs on one
--     side only.
--   fuel-coherent: if evaluate fuel₁ produced emits from drain steps that
--     evaluate fuel₁ does not produce (i.e. drain step k appears in
--     fuel₁ output but not fuel₂ output — prefix violated).
--   id-inheritance: if the evaluator assigned an instant id > fuel to
--     some emit.
--
-- A FAILED refl check (TYPE ERROR) means the postulate is FALSE at that
-- instance.  STOP immediately and report the two sides.
module Battery-Eval-Laws where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Relation.Unary.All  using (All)
  renaming ([] to []ₐ; _∷_ to _∷ₐ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Fuel; Id; InstEmit; _at_from_as_;
                                EmitKind; subscribe; delivery;
                                CloseReason; exhausted; InstEvent; init; close; complete)
open import Rx.Exp       using (Ty; Ctx; natᵗ; Closed; Exp;
                                emptyᵉ; ofᵉ; nat̂; μᵉ; deferᵉ; varᵉ; unfoldμ)
open import Rx.Evaluator using (Slot; Slots; evaluate)
open import Rx.Provenance-Theorems using (_⊆ᵢ_; ids; horizon)

-- Empty context and matching slots
Γ₀ : Ctx 0
Γ₀ = []ᵛ

noSlots : Slots Γ₀
noSlots ()

-- The canonical self-referential body: deferᵉ (varᵉ (here refl)).
-- μᵉ μbody₁ is the simplest infinite-loop observable in an empty context.
-- unfoldμ μbody₁ = deferᵉ (μᵉ μbody₁) definitionally.
-- At fuel=n with noSlots, the deferred body fires at each tick, so drain
-- processes n steps, producing n+1 total InstEmits (1 subscribe + n deliveries).
-- This is the canonical non-degenerate program for all three postulates.
μbody₁ : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
μbody₁ = deferᵉ (varᵉ (here refl))

-------------------------------------------------------------------
-- §1  μ-UNFOLD: evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins
--
-- SUSPICIOUS mechanism (from defer-shift's comment): unfolding may
-- re-mint ids.  The coordinator's concern: if evaluate uses
-- `budgetAt (μᵉ e) ins id` on the LHS but `budgetAt (unfoldμ e) ins id`
-- on the RHS, the cap budgets differ (sizeᵉ (μᵉ e) ≠ sizeᵉ (unfoldμ e)
-- for self-referential bodies).  A budget difference at the
-- subscribeE(μᵉ) boundary causes one side to unfold and the other to
-- emit dryBurst.
--
-- MECHANISM ACTUALLY EXERCISED HERE: fuel=1 with μbody₁.
--   LHS: subscribeE (budgetAt (μᵉ μbody₁) noSlots 0) (μᵉ μbody₁) ...
--        μᵉ clause fires, unfolds to deferᵉ(μᵉ μbody₁), mints src=0,
--        drain step 1 fires (tick-1 arrival), re-subscribes to μᵉ μbody₁
--        using budgetAt (μᵉ μbody₁) noSlots 1 inside cascade.
--   RHS: subscribeE (budgetAt (deferᵉ (μᵉ μbody₁)) noSlots 0) (deferᵉ ...) ...
--        deferᵉ clause fires directly, mints src=0,
--        drain step 1 fires (same tick-1 arrival), re-subscribes to μᵉ μbody₁
--        using budgetAt (deferᵉ (μᵉ μbody₁)) noSlots 1 inside cascade.
--   Both cap budgets are gasPad-large (>>8 gs levels) so the μᵉ unfolds
--   exactly once on both sides; deferᵉ ignores gas entirely.  The output
--   list is the same concrete term on both sides.
--
-- WHAT WOULD MAKE THIS FAIL:
--   If the cap budget difference caused one side to hit g0 (dryBurst)
--   while the other side unfolded normally.  That would require
--   capsBase (μᵉ μbody₁) noSlots = 0 and capsBase (unfoldμ μbody₁) noSlots > 0,
--   or vice versa.  Since both sizes are ≥ 3, both budgets have at least
--   8 gs levels; the difference cannot be decisive at either site.
--
-- ROWS:
--   (a) DEGENERATE: body has no self-reference; unfoldμ = id; drain idle.
--   (b) LOAD-BEARING: self-referential body, fuel=1; drain step fires.
-------------------------------------------------------------------

-- (a) DEGENERATE rows — no self-reference, no unfolding fires

_ : evaluate {t = natᵗ} 0 (μᵉ (emptyᵉ {Γ = Γ₀})) noSlots
    ≡ evaluate 0 emptyᵉ noSlots
_ = refl

_ : evaluate {t = natᵗ} 5 (μᵉ (emptyᵉ {Γ = Γ₀})) noSlots
    ≡ evaluate 5 emptyᵉ noSlots
_ = refl

-- (b) LOAD-BEARING: μbody₁ = deferᵉ (varᵉ (here refl)).
-- unfoldμ μbody₁ = deferᵉ (μᵉ μbody₁) definitionally.
-- drain step 1 fires because deferᵉ queues (tick=1, μᵉ μbody₁) in live.
-- If the cap budget asymmetry caused different unfolding depth,
-- the two sides would mint different sources and this refl would fail.

_ : evaluate {t = natᵗ} 1 (μᵉ μbody₁) noSlots
    ≡ evaluate 1 (unfoldμ μbody₁) noSlots
_ = refl

-- Fuel=2: two drain steps fire on both sides.
-- A refutation here would show 4 emits on one side, fewer on the other.

_ : evaluate {t = natᵗ} 2 (μᵉ μbody₁) noSlots
    ≡ evaluate 2 (unfoldμ μbody₁) noSlots
_ = refl

-- Concrete verification: the outputs at fuel=1 and fuel=2 by refl.
-- If these fail, the error shows the actual normalized form.
-- (The concrete list is derived by hand: each drain step k produces one
-- delivery InstEmit with events [close (k-1) exhausted, init k] at
-- instant k from source k-1.)

_ : evaluate {t = natᵗ} 1 (μᵉ μbody₁) noSlots
    ≡ ((init 0 ∷ [])
         at 0 from 0 as subscribe) ∷
      ((close 0 exhausted ∷ init 1 ∷ [])
         at 1 from 0 as delivery) ∷ []
_ = refl

-------------------------------------------------------------------
-- §2  FUEL-COHERENT: Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)
--     when f₁ ≤ f₂
--
-- WHAT WOULD MAKE A ROW FAIL:
--   A drain step that appears in evaluate f₁ but NOT in evaluate f₂,
--   i.e. a step that is somehow truncated at higher fuel.
--   Equivalently: the stream is NOT prefix-closed in fuel, meaning
--   going from f₁ to f₂ removes or reorders some earlier emits.
--
-- ROWS:
--   (a) DEGENERATE: emptyᵉ / ofᵉ with no-arrival; equality at all fuels.
--   (b) LOAD-BEARING: μbody₁ — evaluate 1 is 2 emits, evaluate 3 is 4.
--       Prefix claim: evaluate 1 is a proper INITIAL SEGMENT of evaluate 3.
--       Evidence: we check both sides are the concrete lists that exhibit
--       the proper prefix relationship, rather than constructing a Prefix
--       term (which requires stdlib machinery not currently imported).
-------------------------------------------------------------------

-- (a) DEGENERATE: fuel doesn't matter for no-arrival programs

_ : evaluate {t = natᵗ} 0 (emptyᵉ {Γ = Γ₀}) noSlots
    ≡ evaluate 1 emptyᵉ noSlots
_ = refl

_ : evaluate {t = natᵗ} 0 (ofᵉ {Γ = Γ₀} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots
    ≡ evaluate 3 (ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots
_ = refl

-- (b) LOAD-BEARING: μbody₁ with self-referential unfolding.
-- evaluate 1 produces 2 emits; evaluate 3 produces 4 emits.
-- evaluate 1's output is a prefix (proper initial segment) of evaluate 3's.

-- Step 1: Verify evaluate 1 produces exactly 2 InstEmits (fuel=1 is not vacuous).
_ : length (evaluate {t = natᵗ} 1 (μᵉ μbody₁) noSlots) ≡ 2
_ = refl

-- Step 2: Verify evaluate 3 produces strictly more (4 InstEmits).
-- If this fails alongside step 1, fuel-coherent is not obviously false —
-- but the claim is non-trivial only when evaluate 3 ≠ evaluate 1.
_ : length (evaluate {t = natᵗ} 3 (μᵉ μbody₁) noSlots) ≡ 4
_ = refl

-- Step 3: Verify evaluate 3's list begins with evaluate 1's list.
-- evaluate 3 = evaluate 1 ++ [em₂, em₃].
-- A refl failure here means fuel-coherent fails at this instance.
_ : evaluate {t = natᵗ} 3 (μᵉ μbody₁) noSlots
    ≡ ((init 0 ∷ [])
         at 0 from 0 as subscribe) ∷
      ((close 0 exhausted ∷ init 1 ∷ [])
         at 1 from 0 as delivery) ∷
      ((close 1 exhausted ∷ init 2 ∷ [])
         at 2 from 1 as delivery) ∷
      ((close 2 exhausted ∷ init 3 ∷ [])
         at 3 from 2 as delivery) ∷ []
_ = refl

-------------------------------------------------------------------
-- §3  ID-INHERITANCE: ids (evaluate fuel e ins) ⊆ᵢ horizon fuel
--
-- ids = map InstEmit.instant.  horizon fuel = [0 .. fuel].
-- Instant ids are assigned by: instant=0 for the subscribe frame,
-- instant=k for the k-th drain step (nextId increments with each step).
--
-- WHAT WOULD MAKE A ROW FAIL:
--   An emit whose instant field is GREATER THAN fuel.
--   Concretely: drain step k assigns instant=nextId, and nextId = k+1
--   after k steps.  But nextId at drain step k is k (1-indexed drain,
--   drain starts with nextId=1), so evaluate fuel can produce instants
--   0..fuel.  A bug assigning nextId=fuel+1 or higher would refute this.
--
-- ROWS:
--   (a) DEGENERATE: no-arrival programs, all instants=0, single-element list.
--   (b) LOAD-BEARING: μbody₁ at fuel=3, 4 distinct instants [0,1,2,3].
--       The ⊆ᵢ proof requires showing each of 0, 1, 2, 3 is in [0,1,2,3].
--       Compared to the degenerate [0] ⊆ [0] case, this exercises ⊆ᵢ
--       with non-trivial membership checks (the `there` constructor).
-------------------------------------------------------------------

-- (a) DEGENERATE: ids=[0], horizon=[0..fuel], [0]⊆ trivially

-- NOTE: ids from Rx.Provenance-Theorems has phantom implicits that Agda
-- cannot infer from an opaque `evaluate` application.  We inline as
-- map InstEmit.instant (definitionally equal: ids = map InstEmit.instant).

_ : map InstEmit.instant (evaluate {t = natᵗ} 0 (emptyᵉ {Γ = Γ₀}) noSlots) ≡ (0 ∷ [])
_ = refl

_ : map InstEmit.instant (evaluate {t = natᵗ} 0 (ofᵉ {Γ = Γ₀} (nat̂ 5 ∷ [])) noSlots) ≡ (0 ∷ [])
_ = refl

-- (b) LOAD-BEARING: μbody₁ at fuel=3 produces instants [0,1,2,3].
-- The id-inheritance claim requires all four to be in horizon 3 = [0,1,2,3].
-- This is the first non-trivial instance: 4-element ⊆ᵢ 4-element list,
-- requiring three `there` constructors for the last three elements.

-- Step 1: Verify ids are exactly [0,1,2,3] — this is the "both sides" check.
-- A refl failure here means the evaluator assigned wrong instant ids, directly
-- refuting id-inheritance (would show the actual id list in the error).
_ : map InstEmit.instant (evaluate {t = natᵗ} 3 (μᵉ μbody₁) noSlots)
    ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

-- Step 2: Verify horizon 3 = [0,1,2,3].
_ : horizon 3 ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
_ = refl

-- Step 3: The ⊆ᵢ proof: each of 0,1,2,3 is in [0,1,2,3].
-- (here refl) proves x ∈ (x ∷ _).  (there p) proves x ∈ (_ ∷ ys) given p : x ∈ ys.
-- A failed proof term here would be caught by the typechecker.
id-inheritance-fuel3 : (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ⊆ᵢ (0 ∷ 1 ∷ 2 ∷ 3 ∷ [])
id-inheritance-fuel3 =
  here refl ∷ₐ
  there (here refl) ∷ₐ
  there (there (here refl)) ∷ₐ
  there (there (there (here refl))) ∷ₐ
  []ₐ

-- Wider horizon: [0,1,2,3] ⊆ [0..5].  Non-trivial because [0..5] is wider
-- than the id list, so the proof cannot just use (here refl) everywhere.
_ : horizon 5 ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

id-inheritance-fuel3-in-5 : (0 ∷ 1 ∷ 2 ∷ 3 ∷ []) ⊆ᵢ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
id-inheritance-fuel3-in-5 =
  here refl ∷ₐ
  there (here refl) ∷ₐ
  there (there (here refl)) ∷ₐ
  there (there (there (here refl))) ∷ₐ
  []ₐ
