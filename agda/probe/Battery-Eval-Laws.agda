-- BATTERY-EVAL-LAWS (2026-08-06).  Concrete instance probes for three
-- postulates from Rx.Evaluator-Theorems and Rx.Provenance-Theorems:
--
--   μ-unfold       evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins
--   fuel-coherent  Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)
--   id-inheritance ids (evaluate fuel e ins) ⊆ᵢ horizon fuel
--
-- All checks: refl (equality checks) or explicit proof terms.
-- A FAILED check (refl rejected) means the postulate is FALSE at that
-- instance — STOP and report immediately.
--
-- Shape of this file: "battery" = one probe per concrete shape, not a
-- general theorem.  The point is to confirm none of these are vacuous
-- and that the easiest instances hold.
--
-- Note on fuel-coherent: we test the strictly STRONGER equality form
-- (evaluate f₁ ≡ evaluate f₂) for no-arrival programs, which implies
-- Prefix.  Arrival programs (with hot/cold slots) can exhibit genuine
-- prefix-but-not-equality, but their Prefix proofs need scripted slot
-- machinery.  Those cases are noted below as out of scope.
module Battery-Eval-Laws where

open import Data.Nat  using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; map)
open import Data.Vec  using () renaming ([] to []ᵛ; _∷_ to _∷ᵛ_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any  using (here; there)
open import Data.List.Relation.Unary.All  using (All)
  renaming ([] to []ₐ; _∷_ to _∷ₐ_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Rx.Prim      using (Fuel; Id; InstEmit)
open import Rx.Exp       using (Ty; Ctx; natᵗ; Closed; Exp;
                                emptyᵉ; ofᵉ; nat̂; μᵉ; deferᵉ; varᵉ; unfoldμ)
open import Rx.Evaluator using (Slot; Slots; evaluate)
open import Rx.Provenance-Theorems using (_⊆ᵢ_; ids; horizon)

-- Empty context and matching slots
Γ₀ : Ctx 0
Γ₀ = []ᵛ

noSlots : Slots Γ₀
noSlots ()

-------------------------------------------------------------------
-- §1  μ-UNFOLD: evaluate fuel (μᵉ e) ins ≡ evaluate fuel (unfoldμ e) ins
--
-- WHY REFL WORKS here.  Both sides call subscribeE on the same
-- expression structure (unfoldμ e) with the same sched-init (which does
-- NOT depend on e).  The only difference is the gas value, and every
-- expression we probe (emptyᵉ, ofᵉ, deferᵉ) IGNORES gas entirely, so
-- the outputs are definitionally equal.
-------------------------------------------------------------------

-- Case (a): body = emptyᵉ (no μ-var).
-- unfoldμ emptyᵉ = emptyᵉ definitionally (no var to replace).
-- Both sides normalise to the same oneShotBurst at instant 0.

_ : evaluate {t = natᵗ} 0 (μᵉ (emptyᵉ {Γ = Γ₀})) noSlots
    ≡ evaluate 0 emptyᵉ noSlots
_ = refl

_ : evaluate {t = natᵗ} 5 (μᵉ (emptyᵉ {Γ = Γ₀})) noSlots
    ≡ evaluate 5 emptyᵉ noSlots
_ = refl

-- Case (b): body = ofᵉ ts (no μ-var).
-- unfoldμ (ofᵉ ts) = ofᵉ ts (ofᵉ clause of elimGExp is identity).
-- ofᵉ clause ignores gas.

_ : evaluate {t = natᵗ} 0 (μᵉ (ofᵉ (nat̂ 5 ∷ []))) noSlots
    ≡ evaluate 0 (ofᵉ (nat̂ 5 ∷ [])) noSlots
_ = refl

_ : evaluate {t = natᵗ} 0 (μᵉ (ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ []))) noSlots
    ≡ evaluate 0 (ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots
_ = refl

-- Case (c): body = deferᵉ (varᵉ (here refl)) — the μ-var appears once,
-- inside a deferᵉ gate.  unfoldμ substitutes (μᵉ body) for the var,
-- yielding deferᵉ (μᵉ body).
--
-- At fuel=0: drain runs 0 steps, so the deferred body never fires.
-- Both sides subscribe to a deferᵉ with the SAME sched₀, mint the same
-- nid/src/ord, and produce the same burst (init src at instant 0).
-- The body queued in live differs syntactically but is never processed.

μbody₁ : Exp Γ₀ (natᵗ ∷ []) [] [] natᵗ
μbody₁ = deferᵉ (varᵉ (here refl))

-- unfoldμ reduces definitionally to deferᵉ (μᵉ (deferᵉ (varᵉ (here refl))))
_ : evaluate {t = natᵗ} 0 (μᵉ μbody₁) noSlots
    ≡ evaluate 0 (deferᵉ (μᵉ (deferᵉ (varᵉ (here refl))))) noSlots
_ = refl

-- the same thing via unfoldμ directly
_ : evaluate {t = natᵗ} 0 (μᵉ μbody₁) noSlots
    ≡ evaluate 0 (unfoldμ μbody₁) noSlots
_ = refl

-------------------------------------------------------------------
-- §2  FUEL-COHERENT: Prefix _≡_ (evaluate f₁ e ins) (evaluate f₂ e ins)
--
-- For no-arrival programs (emptyᵉ, ofᵉ ts), drain sees an empty live
-- queue regardless of fuel, so evaluate is EQUAL at all fuel levels.
-- This is strictly stronger than Prefix.
--
-- Arrival programs (programs with hot/cold scripted slots) can exhibit
-- genuinely different prefixes at different fuel levels.  Probing those
-- requires constructing explicit Prefix terms over the scripted-slot
-- machinery; that is out of scope for this battery.
-------------------------------------------------------------------

_ : evaluate {t = natᵗ} 0 (emptyᵉ {Γ = Γ₀}) noSlots
    ≡ evaluate 1 emptyᵉ noSlots
_ = refl

_ : evaluate {t = natᵗ} 0 (emptyᵉ {Γ = Γ₀}) noSlots
    ≡ evaluate 5 emptyᵉ noSlots
_ = refl

_ : evaluate {t = natᵗ} 0 (ofᵉ {Γ = Γ₀} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots
    ≡ evaluate 3 (ofᵉ (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots
_ = refl

_ : evaluate {t = natᵗ} 1 (ofᵉ {Γ = Γ₀} (nat̂ 5 ∷ [])) noSlots
    ≡ evaluate 10 (ofᵉ (nat̂ 5 ∷ [])) noSlots
_ = refl

-------------------------------------------------------------------
-- §3  ID-INHERITANCE: ids (evaluate fuel e ins) ⊆ᵢ horizon fuel
--
-- horizon fuel = upTo (suc fuel) = [0 .. fuel].
-- Instant IDs are assigned by: instant=0 for the subscribe frame,
-- instant=k for the k-th drain step.
-- For no-arrival programs, only instant=0 appears.
-- The proof is All (λ x → x ∈ horizon fuel) [0] = (0 ∈ horizon fuel).
-- 0 ∈ upTo (suc fuel) = here refl for all fuel ≥ 0.
--
-- NOTE ON META STRATEGY: `ids (evaluate ...) ⊆ᵢ horizon fuel` has
-- implicit arguments in `here` that Agda cannot resolve from the
-- opaque type.  Instead we prove two subgoals by refl:
--   (A) ids (evaluate ...) ≡ (0 ∷ [])          — the concrete ids
--   (B) horizon fuel ≡ (0 ∷ rest)               — horizon starts with 0
-- then the full ⊆ᵢ follows by `subst` + membership on concrete lists.
-- For the probe, checks (A) and (B) confirm the postulate is not
-- vacuous at these instances; full ⊆ᵢ compositions are left as notes.
-------------------------------------------------------------------

-- (A) ids of the evaluator output normalise to [0] for no-arrival programs
--
-- NOTE: `ids` from Rx.Provenance-Theorems carries phantom implicits {n}{Γ}{t}
-- that Agda cannot resolve when the argument is an opaque `evaluate` application.
-- Since ids = map InstEmit.instant by definition, we inline it here to avoid
-- the meta; this is definitionally equivalent.

_ : map InstEmit.instant (evaluate {t = natᵗ} 0 (emptyᵉ {Γ = Γ₀}) noSlots) ≡ (0 ∷ [])
_ = refl

_ : map InstEmit.instant (evaluate {t = natᵗ} 0 (ofᵉ {Γ = Γ₀} (nat̂ 5 ∷ [])) noSlots) ≡ (0 ∷ [])
_ = refl

_ : map InstEmit.instant (evaluate {t = natᵗ} 5 (emptyᵉ {Γ = Γ₀}) noSlots) ≡ (0 ∷ [])
_ = refl

_ : map InstEmit.instant (evaluate {t = natᵗ} 0 (ofᵉ {Γ = Γ₀} (nat̂ 3 ∷ nat̂ 7 ∷ [])) noSlots) ≡ (0 ∷ [])
_ = refl

-- (B) horizon includes 0 at all fuel levels (horizon n = 0 ∷ rest)
-- upTo (suc n) always starts with 0

_ : horizon 0 ≡ (0 ∷ [])
_ = refl

_ : horizon 5 ≡ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
_ = refl

-- (C) the ⊆ᵢ proof at a concrete known list, confirming the proof term
-- shape: `here refl ∷ₐ []ₐ` works when both sides are known concrete lists

id-subset-concrete : (0 ∷ []) ⊆ᵢ (0 ∷ [])
id-subset-concrete = here refl ∷ₐ []ₐ

id-subset-wider : (0 ∷ []) ⊆ᵢ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ [])
id-subset-wider = here refl ∷ₐ []ₐ
